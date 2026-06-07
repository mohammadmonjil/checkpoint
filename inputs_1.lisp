
(include-book "model")
(include-book "invariants")
(include-book "equivalence")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: Compressed Input Generation 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ------------------------------------------------------------------
;; High-level algorithm for compressed input generation
;;
;; Goal:
;;   Transform an implementation-level input sequence containing
;;   checkpointing and recovery protocol actions into a spec-level
;;   input sequence that preserves only the behavior relevant to the
;;   abstract computation.
;;
;; Overall pipeline:
;;
;;   1. Run the implementation from the initial state to obtain the
;;      full execution trace.
;;
;;   2. Scan the input sequence to locate each recovery input.  For
;;      each recovery input, identify:
;;        - the checkpoint-start index of the snapshot that will be
;;          used for that recovery,
;;        - the recovery-start index itself, and
;;        - the snapshot id (sid) being recovered.
;;
;;   3. For each (checkpoint-start, recovery-start, sid) segment:
;;        a. Scan forward from checkpoint-start until checkpointing
;;           for sid is complete, building cut metadata:
;;             - inputs-before-cut
;;             - buffered inputs-after-cut
;;        b. Scan forward from recovery-start until recovery is done,
;;           building recovery metadata:
;;             - inputs-during-recovery
;;        c. Build one compressed segment input by concatenating:
;;             - inputs-before-cut
;;             - replayed buffered inputs-after-cut in recovery replay order
;;             - preserved inputs-during-recovery
;;
;;   4. Replace each original checkpoint-to-recovery region by its
;;      compressed segment.  This stitching is done from right to left,
;;      so later recoveries naturally overwrite earlier recoveries that
;;      depend on the same checkpoint.
;;
;;   5. For untouched regions copied directly from the original input
;;      sequence, convert implementation-only inputs into spec no-ops
;;      (:nop).  In particular, receives of marker or recovery messages
;;      must not remain as spec receives.
;;
;; Result:
;;   A spec-compliant input sequence containing only meaningful normal
;;   actions and normal receives, with checkpoint/recovery protocol
;;   traffic removed or turned into no-ops.
;; ------------------------------------------------------------------


;; ------------------------------------------------------------------
;; Subsection A: Recovery-segment discovery
;;
;; This block identifies the recovery episodes in the implementation
;; run.  For each recovery input, it determines which checkpoint that
;; recovery rolls back to and packages the information into a recovery-
;; segment record.
;;
;; Main idea:
;;   - look at the pre-state of a recovery input,
;;   - extract the most recent snapshot id used by that process,
;;   - find the matching start-checkpoint input that created that sid,
;;   - return a record describing the segment.
;;
;; These records are later used to drive the cut scan, the recovery
;; scan, and the final compressed-segment generation.
;; ------------------------------------------------------------------

(defmacro rs-checkpoint-start (r)
  `(g :checkpoint-start ,r))

(defmacro rs-recovery-start (r)
  `(g :recovery-start ,r))

(defmacro rs-sid (r)
  `(g :sid ,r))


(defun latest-snapshot-id-for-proc (st i)
  ;; Return the most recent snapshot-id stored for process i.
  ;; This is the snapshot that recovery will use.
  (let* ((procs (procs st))
         (p     (g i procs)))
    (car (snapshot-ids p))))

(defun snapshot-count-for-proc (st i)
  ;; Return how many snapshot-ids process i currently has.
  ;; If this is 1, we treat it as the initial snapshot only.
  (let* ((procs (procs st))
         (p     (g i procs)))
    (len (snapshot-ids p))))

(defun recover-input-p (input)
  ;; Check whether INPUT is a recovery input.
  (equal (ttype input) :recover))

(defun checkpoint-start-match-p (input st sid)
  ;; Check whether this input/state position corresponds to the
  ;; start-checkpoint step that created SID.
  ;;
  ;; We match:
  ;;   1. input type is :start-checkpoint
  ;;   2. pid of the input matches the pid inside SID
  ;;   3. (pid, counter-at-that-state) = SID
  ;;
  ;; This works because snapshot ids are created as (list pid counter).
  (let* ((i     (pid input))
         (procs (procs st))
         (p     (g i procs)))
    (and (equal (ttype input) :start-checkpoint)
         (equal i (car sid))
         (equal sid
                (list i
                      (counter p))))))

(defun find-checkpoint-start-left (inputs trace idx sid)
  ;; Scan left from input/trace index IDX down to 0 to find the
  ;; checkpoint-start position whose created snapshot-id matches SID.
  ;;
  ;; INPUTS[k] is checked together with TRACE[k], where TRACE[k]
  ;; is the pre-state for INPUTS[k].
  (let ((input (nth idx inputs))
        (st    (nth idx trace)))
    (if (checkpoint-start-match-p input st sid)
        idx
      (if (zp idx)
          0
        (find-checkpoint-start-left
         inputs trace (- idx 1) sid)))))

(defun recovery-segment-for-index (inputs trace x)
  ;; Assume INPUTS[x] is a :recover input.
  ;;
  ;; Build a record with fields:
  ;;   :checkpoint-start
  ;;   :recovery-start
  ;;   :sid
  ;;
  ;; where:
  ;;   checkpoint-start = input index of the matching start-checkpoint
  ;;                    = 0 if recovery before a checkpoint input
  ;;                    meaning recovers back to initial state
  ;;   recovery-start   = input index x of the recover input
  ;;   sid              = snapshot id used by that recovery
  (let* ((input            (nth x inputs))
         (i                (pid input))
         (pre-state        (nth x trace))
         (sid              (latest-snapshot-id-for-proc pre-state i))
         (snap-count       (snapshot-count-for-proc pre-state i))
         (checkpoint-start
          (if (equal snap-count 1)
              0
            (find-checkpoint-start-left inputs trace (- x 1) sid))))
    (>_ :checkpoint-start checkpoint-start
        :recovery-start x
        :sid sid)))

(defun collect-recovery-segments-aux (full-inputs trace inputs idx)
  ;; Scan INPUTS from left to right.
  ;;
  ;; For every recover input encountered, collect a record with fields:
  ;;   :checkpoint-start
  ;;   :recovery-start
  ;;   :sid
  (if (endp inputs)
      nil
    (if (recover-input-p (first inputs))
        (cons (recovery-segment-for-index full-inputs trace idx)
              (collect-recovery-segments-aux
               full-inputs trace (rest inputs) (+ 1 idx)))
      (collect-recovery-segments-aux
       full-inputs trace (rest inputs) (+ 1 idx)))))

(defun collect-recovery-segments-from-trace (inputs trace)
  ;; INPUTS and TRACE must be aligned so that:
  ;;   TRACE[x]   = pre-state of INPUTS[x]
  ;;   TRACE[x+1] = post-state of INPUTS[x]
  ;;
  ;; Extracts all recovery segments as records.
  (collect-recovery-segments-aux inputs trace inputs 0))

(defun collect-recovery-segments (st inputs)
  ;; Wrapper that first executes the implementation to get the trace,
  ;; then extracts all recovery segments as records.
  (let ((trace (run-imp-trace st inputs)))
    (collect-recovery-segments-from-trace inputs trace)))


;; ------------------------------------------------------------------
;; Subsection B: Cut metadata and checkpoint-side compression
;;
;; This block defines the metadata used while scanning from a checkpoint
;; start until the corresponding checkpoint is complete.
;;
;; The cut metadata records:
;;   - sid                     = snapshot being tracked
;;   - proc-ids                = all process ids
;;   - cut-not-taken           = processes that have not yet taken their cut
;;   - waiting-marker-from     = per-process list of senders whose marker
;;                               has not yet arrived
;;   - inputs-before-cut       = inputs that occur before the receiver
;;                               (or process) has taken its cut
;;   - inputs-after-cut        = buffered normal receives that must later
;;                               be replayed during recovery
;;
;; Intuition:
;;   - before a process takes its cut, normal behavior is preserved
;;     immediately;
;;   - after a process has taken its cut, only those receives that are
;;     still on channels waiting for a marker are buffered for replay;
;;   - once checkpointing completes, the cut metadata contains exactly
;;     the prefix and buffered replay information needed to reconstruct
;;     the recovered computation.
;; ------------------------------------------------------------------

(defmacro cm-sid (m)
  `(g :sid ,m))

(defun cm-proc-ids (m)
  (g :proc-ids m))

(defun cm-cut-not-taken (m)
  (g :cut-not-taken m))

(defun cm-waiting-marker-from (m)
  (g :waiting-marker-from m))

(defun cm-inputs-before-cut (m)
  (g :inputs-before-cut m))

(defun cm-inputs-after-cut (m)
  (g :inputs-after-cut m))

(defun cm-waiting-marker-for (m i)
  (g i (cm-waiting-marker-from m)))

(defun cm-set-waiting-marker-for (m i xs)
  (s :waiting-marker-from
     (s i xs (cm-waiting-marker-from m))
     m))

(defun cm-cut-not-taken-p (m i)
  (memberp i (cm-cut-not-taken m)))

(defun cm-remove-cut-not-taken (m i)
  (s :cut-not-taken
     (remove1-equal i (cm-cut-not-taken m))
     m))

(defun cm-add-before-cut (m input)
  (s :inputs-before-cut
     (append (cm-inputs-before-cut m) (list input))
     m))

(defun cm-after-cut-get (m i j)
  (let* ((rec-i (g i (cm-inputs-after-cut m))))
    (g j rec-i)))

(defun cm-after-cut-append (m i j input)
  (let* ((all   (cm-inputs-after-cut m))
         (rec-i (g i all))
         (old   (g j rec-i))
         (rec-i (s j (append old (list input)) rec-i))
         (all   (s i rec-i all)))
    (s :inputs-after-cut all m)))

(defun cut-done-p (m)
  (if (equal (cm-sid m) :init)
      t
    (endp (cm-cut-not-taken m))))

(defun make-inputs-after-cut-for-proc (nbrs)
  (if (endp nbrs)
      nil
    (s (first nbrs)
       nil
       (make-inputs-after-cut-for-proc (rest nbrs)))))

(defun make-inputs-after-cut (proc-ids procs)
  (if (endp proc-ids)
      nil
      (let* ((i         (first proc-ids))
	     (p (g i procs))
             (nbrs      (nbrs-from p))
             (entry-i   (make-inputs-after-cut-for-proc nbrs))
             (rest-recs (make-inputs-after-cut (rest proc-ids) procs)))
      (s i entry-i rest-recs))))

(defun make-empty-waiting-marker-from (proc-ids)
  (if (endp proc-ids)
      nil
    (s (first proc-ids)
       nil
       (make-empty-waiting-marker-from (rest proc-ids)))))

(defun make-cut-meta (sid initiator st)
  (let* ((procs    (procs st))
         (proc-ids (proc-ids st))
	 (p        (g initiator procs))
         (nbrs     (nbrs-from p))
         (m        nil)
         (m        (s :inputs-after-cut
                      (make-inputs-after-cut proc-ids procs)
                      m))
         (m        (s :inputs-before-cut nil m))
         (m        (s :waiting-marker-from
                      (s initiator
                         nbrs
                         (make-empty-waiting-marker-from proc-ids))
                      m))
         (m        (s :cut-not-taken
                      (remove1-equal initiator proc-ids)
                      m))
         (m        (s :proc-ids proc-ids m))
         (m        (s :sid sid m)))
    m))

;; ------------------------------------------------------------------
;; Cut-phase step processing
;;
;; These functions implement the checkpoint-side scan one input at a
;; time.  They inspect each implementation input together with the
;; corresponding pre-state from the trace and update the cut metadata.
;;
;; Cases:
;;   - :normal
;;       preserve it only if the process has not yet taken its cut.
;;
;;   - :receive carrying :marker
;;       update cut-taken / waiting-marker-from information if sid matches.
;;       ignore the input is sid not matches (situation while multiple
;;       checkpointing is happening concurrently)
;;
;;   - :receive carrying :normal
;;       preserve it immediately if the receiver has not taken its cut;
;;       otherwise buffer it only if that channel is still waiting for
;;       a marker.
;;
;;   - protocol-only traffic that does not contribute to the spec
;;       leaves the metadata unchanged.
;; ------------------------------------------------------------------

(defun process-cut-normal (input m)
  (let ((i (pid input)))
    (if (cm-cut-not-taken-p m i)
        (cm-add-before-cut m input)
      m)))

(defun process-cut-marker-receive (i j st m)
  (let* ((procs (procs st)))
    (if (cm-cut-not-taken-p m i)
        ;; first marker for i: i now takes its cut
        (let* ((p    (g i procs))
	       (nbrs (nbrs-from p))
               (ws   (remove1-equal j nbrs))
               (m    (cm-remove-cut-not-taken m i)))
          (cm-set-waiting-marker-for m i ws))
      ;; later marker for i: just remove sender j from waiting set
      (cm-set-waiting-marker-for
       m i
       (remove1-equal j (cm-waiting-marker-for m i))))))


(defun process-cut-normal-receive (input i j m)
  (if (cm-cut-not-taken-p m i)
      (cm-add-before-cut m input)
    (if (memberp j (cm-waiting-marker-for m i))
        (cm-after-cut-append m i j input)
      m)))


(defun current-msg-for-receive (input st)
  ;; Replace SRC with your actual sender accessor for receive inputs.
  (let* ((i        (pid input))
         (j        (sender input))
         (channels (channels st)))
    (get-msg-from-channel j i channels)))

(defun process-cut-receive (input st m)
  ;; Handle one :receive input during the cut-building phase.
  ;; if for the receive marker, sid do not match that input is dropped too
  (let* ((i   (pid input))
         (j   (sender input))   ;; replace SRC with your sender accessor
         (msg (current-msg-for-receive input st))
         (sid (cm-sid m)))
    (cond
     ((and (equal (msg-type msg) :marker)
           (equal (sid msg) sid))
      (process-cut-marker-receive i j st m))

     ((equal (msg-type msg) :normal)
      (process-cut-normal-receive input i j m))

     (t
      m))))

(defun process-cut-step (input st m)
  ;; Process one implementation input while scanning from cp-start
  ;; until checkpoint completion.
  (cond
   ((equal (ttype input) :start-checkpoint)
    ;; Usually only the initiator's start-checkpoint matters here.
    ;; Since make-cut-meta already accounts for the initiator having
    ;; taken its cut, we do nothing.
    ;; If this is checkpointing input for a new sid we drop that too
    m)

   ((equal (ttype input) :normal)
    (process-cut-normal input m))

   ((equal (ttype input) :receive)
    (process-cut-receive input st m))

   (t
    m)))


(defmacro cut-result-idx (r)
  `(g :cut-done-index ,r))

(defmacro cut-result-meta (r)
  `(g :cut-meta ,r))

(defmacro recovery-result-idx (r)
  `(g :recovery-done-index ,r))

(defmacro recovery-result-meta (r)
  `(g :recovery-meta ,r))

;; ------------------------------------------------------------------
;; Cut-phase scan
;;
;; Starting from checkpoint-start, scan the aligned input suffix and
;; trace until checkpointing for the current sid is complete.
;;
;; Return:
;;   - :cut-done-index   = first index at which checkpointing is done
;;   - :cut-meta         = final cut metadata
;;
;; For sid = :init, cut-done is immediate, since there is no actual
;; checkpoint protocol to complete.
;; ------------------------------------------------------------------

(defun scan-until-cut-done-aux (inputs trace idx m)
  ;; Scan left-to-right until checkpoint completion.
  ;; TRACE[idx] is the pre-state of INPUTS[idx].
  ;; Returns a record with fields:
  ;;   :cut-done-index
  ;;   :cut-meta
  (if (or (endp inputs)
          (cut-done-p m))
      (>_ :cut-done-index idx
          :cut-meta m)
    (let* ((input (first inputs))
           (st    (nth idx trace))
           (m     (process-cut-step input st m)))
      (scan-until-cut-done-aux (rest inputs)
                               trace
                               (+ 1 idx)
                               m))))

(defun scan-until-cut-done (inputs trace cp-start sid initiator)
  ;; Start scanning at cp-start with freshly initialized cut meta-state.
  ;; Returns a record with fields:
  ;;   :cut-done-index
  ;;   :cut-meta
  (let* ((st (nth cp-start trace))
         (m0 (make-cut-meta sid initiator st)))
    (scan-until-cut-done-aux (nthcdr cp-start inputs)
                             trace
                             cp-start
                             m0)))

;; ------------------------------------------------------------------
;; Subsection C: Recovery metadata and recovery-side compression
;;
;; This block defines the metadata used while scanning from recovery-
;; start until recovery is complete.
;;
;; The recovery metadata records:
;;   - sid                      = snapshot being recovered
;;   - proc-ids                 = all process ids
;;   - recovery-started-procs   = processes that have already started
;;                                recovery
;;   - waiting-recovery-from    = per-process list of senders whose
;;                                recovery message has not yet arrived
;;   - inputs-during-recovery   = normal/spec-relevant inputs that
;;                                survive after rollback
;;
;; Intuition:
;;   - once a process starts recovery, later normal actions for that
;;     process may contribute to the recovered computation;
;;   - a normal receive(i,j) can contribute only after process i has
;;     started recovery and is no longer waiting for j's recovery
;;     message;
;;   - recovery is complete when all processes have started recovery
;;     and all waiting-recovery sets are empty.
;; ------------------------------------------------------------------

(defmacro rm-sid (m)
  `(g :sid ,m))

(defmacro rm-proc-ids (m)
  `(g :proc-ids ,m))

(defmacro rm-recovery-started-procs (m)
  `(g :recovery-started-procs ,m))

(defmacro rm-waiting-recovery-from (m)
  `(g :waiting-recovery-from ,m))

(defmacro rm-inputs-during-recovery (m)
  `(g :inputs-during-recovery ,m))


(defun rm-recovery-started-p (m i)
  (memberp i (rm-recovery-started-procs m)))

(defun rm-add-recovery-started-proc (m i)
  (s :recovery-started-procs
     (add-to-set-equal1 i (rm-recovery-started-procs m))
     m))

(defun rm-waiting-recovery-for (m i)
  (g i (rm-waiting-recovery-from m)))

(defun rm-set-waiting-recovery-for (m i xs)
  (s :waiting-recovery-from
     (s i xs (rm-waiting-recovery-from m))
     m))

(defun rm-add-input-during-recovery (m input)
  (s :inputs-during-recovery
     (append (rm-inputs-during-recovery m) (list input))
     m))


(defun make-empty-waiting-recovery-from (proc-ids)
  (if (endp proc-ids)
      nil
    (s (first proc-ids)
       nil
       (make-empty-waiting-recovery-from (rest proc-ids)))))


(defun all-waiting-recovery-empty-p (proc-ids m)
  (if (endp proc-ids)
      t
    (and (endp (rm-waiting-recovery-for m (first proc-ids)))
         (all-waiting-recovery-empty-p (rest proc-ids) m))))

(defun recovery-done-p (m)
  (and (subsetp-equal (rm-proc-ids m)
                      (rm-recovery-started-procs m))
       (all-waiting-recovery-empty-p (rm-proc-ids m) m)))


(defun make-recovery-meta (sid initiator st)
  ;; Initialize recovery meta-state at recovery-start.
  ;; The initiator has already taken the :recover step.
  (let* ((procs                  (procs st))
         (proc-ids               (proc-ids st))
	 (p                      (g initiator procs))
         (initiator-nbrs         (nbrs-from p))
         (empty-waiting          (make-empty-waiting-recovery-from proc-ids))
         (waiting-recovery-from  (s initiator
                                    initiator-nbrs
                                    empty-waiting))
         (recovery-started-procs (list initiator))
         (m                      nil)
         (m                      (s :inputs-during-recovery nil m))
         (m                      (s :waiting-recovery-from
                                    waiting-recovery-from
                                    m))
         (m                      (s :recovery-started-procs
                                    recovery-started-procs
                                    m))
         (m                      (s :proc-ids proc-ids m))
         (m                      (s :sid sid m)))
    m))

;; ------------------------------------------------------------------
;; Recovery-phase step processing
;;
;; These functions implement the recovery-side scan one input at a
;; time.  They inspect each implementation input together with the
;; corresponding trace pre-state and update the recovery metadata.
;;
;; Cases:
;;   - :receive carrying :recovery
;;       mark the receiver as having started recovery and update its
;;       waiting-recovery-from set.
;;
;;   - :receive carrying :normal
;;       preserve it only if the receiver has already started recovery
;;       and is no longer waiting for the sender's recovery message.
;;
;;   - :normal
;;       preserve it only after the process has started recovery.
;;
;;   - other protocol inputs
;;       do not contribute directly to the spec input sequence.
;; ------------------------------------------------------------------

(defun rm-handle-first-recovery-receive (m i j st)
  ;; Process i receives its first recovery message from j.
  (let* ((procs (procs st))
	 (p     (g i procs))
         (nbrs  (nbrs-from p))
         (ws    (remove1-equal j nbrs))
         (m     (rm-add-recovery-started-proc m i))
         (m     (rm-set-waiting-recovery-for m i ws)))
    m))

(defun rm-handle-later-recovery-receive (m i j)
  ;; Process i has already started recovery and receives another
  ;; recovery message from j.
  (let* ((ws (remove1-equal j (rm-waiting-recovery-for m i)))
         (m  (rm-set-waiting-recovery-for m i ws)))
    m))

(defun process-recovery-recovery-receive (i j st m)
  ;; Handle a :receive(i,j) that consumes a :recovery message.
  (if (rm-recovery-started-p m i)
      (rm-handle-later-recovery-receive m i j)
    (rm-handle-first-recovery-receive m i j st)))

(defun process-recovery-normal-receive (input i j m)
  ;; Keep ordinary receive(i,j) only if:
  ;;   1. i has already started recovery, and
  ;;   2. i is no longer waiting for j's recovery message.
  (if (not (rm-recovery-started-p m i))
      m
    (if (memberp j (rm-waiting-recovery-for m i))
        m
      (rm-add-input-during-recovery m input))))

(defun process-recovery-receive (input st m)
  ;; Handle one :receive input during recovery scan.
  (let* ((i   (pid input))
         (j   (sender input))
         (msg (current-msg-for-receive input st)))
    (cond
     ((and (equal (msg-type msg) :recovery)
           (equal (sid msg) (rm-sid m)))
      (process-recovery-recovery-receive i j st m))

     ((equal (msg-type msg) :normal)
      (process-recovery-normal-receive input i j m))

     (t
      m))))

(defun process-recovery-normal (input m)
  ;; Keep :normal(i) only after i has started recovery.
  (let ((i (pid input)))
    (if (rm-recovery-started-p m i)
        (rm-add-input-during-recovery m input)
      m)))

(defun process-recovery-step (input st m)
  ;; No new :recover input is expected here, by legal-inputp.
  ;; Checkpointing input is not expected here, by legal-inputp
  (cond
   ((equal (ttype input) :receive)
    (process-recovery-receive input st m))

   ((equal (ttype input) :normal)
    (process-recovery-normal input m))

   (t
    m)))

;; ------------------------------------------------------------------
;; Recovery-phase scan
;;
;; Starting from recovery-start, scan the aligned input suffix and
;; trace until recovery for the current sid is complete.
;;
;; Return:
;;   - :recovery-done-index = first index at which recovery is done
;;   - :recovery-meta       = final recovery metadata
;;
;; The resulting recovery metadata contains exactly the normal inputs
;; that should remain after the rollback/replay has been accounted for.
;; ------------------------------------------------------------------

(defun scan-until-recovery-done-aux (inputs trace idx m)
  ;; Scan left-to-right from absolute index IDX until recovery is done.
  ;; TRACE[idx] is the pre-state of INPUTS[idx].
  ;; Returns a record with fields:
  ;;   :recovery-done-index
  ;;   :recovery-meta
  (if (or (endp inputs)
          (recovery-done-p m))
      (>_ :recovery-done-index idx
          :recovery-meta m)
    (let* ((input (first inputs))
           (st    (nth idx trace))
           (m     (process-recovery-step input st m)))
      (scan-until-recovery-done-aux (rest inputs)
                                    trace
                                    (+ 1 idx)
                                    m))))

(defun scan-until-recovery (inputs trace recovery-start sid initiator)
  ;; INPUTS[recovery-start] is the initiating :recover input.
  ;; Returns a record with fields:
  ;;   :recovery-done-index
  ;;   :recovery-meta
  (let* ((st (nth recovery-start trace))
         (m0 (make-recovery-meta sid initiator st)))
    (scan-until-recovery-done-aux (nthcdr recovery-start inputs)
                                  trace
                                  recovery-start
                                  m0)))


;; ------------------------------------------------------------------
;; Subsection D: Build one compressed segment input
;;
;; Once cut metadata and recovery metadata have been computed for one
;; recovery segment, the compressed input for that segment is built in
;; three pieces:
;;
;;   1. inputs-before-cut
;;        ordinary behavior that occurred before each process took its
;;        checkpoint cut;
;;
;;   2. replayed inputs-after-cut
;;        buffered receives replayed in the same order that the
;;        implementation recovery uses to replay channel snapshots;
;;
;;   3. inputs-during-recovery
;;        normal behavior that survives after rollback has started.
;;
;; The concatenation of these three pieces is the spec-level input
;; sequence corresponding to one checkpoint-recovery segment.
;; ------------------------------------------------------------------

(defun replay-inputs-for-one-proc (i nbrs-from-i cm-meta)
  ;; Collect buffered receive inputs for process i, in nbrs-from order.
  (if (endp nbrs-from-i)
      nil
    (append (cm-after-cut-get cm-meta i (first nbrs-from-i))
            (replay-inputs-for-one-proc i
                                        (rest nbrs-from-i)
                                        cm-meta))))

(defun replay-inputs-from-cut-meta-aux (proc-ids procs cm-meta)
  ;; Collect all buffered receive inputs in replay order.
  ;; Outer order: processes in PROC-IDS
  ;; Inner order: nbrs-from order for each process
  (if (endp proc-ids)
      nil
      (let* ((i            (first proc-ids))
	     (p            (g i procs))
           (nbrs-from-i  (nbrs-from p)))
      (append (replay-inputs-for-one-proc i
                                          nbrs-from-i
                                          cm-meta)
              (replay-inputs-from-cut-meta-aux (rest proc-ids)
                                               procs
                                               cm-meta)))))

(defun replay-inputs-from-cut-meta (st cm-meta)
  (let* ((proc-ids (cm-proc-ids cm-meta))
         (procs    (procs st)))
    (replay-inputs-from-cut-meta-aux proc-ids
                                     procs
                                     cm-meta)))

(defun generate-segment-inputs (st cm-meta rm-meta)
  ;; Final compressed input sequence for one checkpoint-recovery segment:
  ;;   1. inputs-before-cut
  ;;   2. replayed buffered inputs from cut-meta
  ;;   3. preserved inputs during recovery
  (append (cm-inputs-before-cut cm-meta)
          (append (replay-inputs-from-cut-meta st cm-meta)
                  (rm-inputs-during-recovery rm-meta))))


;; ------------------------------------------------------------------
;; Subsection E: Generate compressed segment records
;;
;; For each discovered recovery-segment record
;;   (:checkpoint-start, :recovery-start, :sid),
;; compute:
;;   - the cut metadata,
;;   - the recovery metadata,
;;   - the compressed segment input sequence, and
;;   - the index at which the covered recovery finishes.
;;
;; The output is a list of records with fields:
;;   :checkpoint-start-index
;;   :recovery-done-index
;;   :compressed-seg
;;
;; These records are the units used by the final stitching phase.
;; ------------------------------------------------------------------

(defmacro cis-recovery-done-index (r)
  `(g :recovery-done-index ,r))

(defmacro cis-checkpoint-start-index (r)
  `(g :checkpoint-start-index ,r))

(defmacro cis-compressed-seg (r)
  `(g :compressed-seg ,r))

(defun generate-compressed-input-segments (inputs trace cp-rc-sid-record-list)
  ;; For each recovery-segment record with fields:
  ;;   :checkpoint-start
  ;;   :recovery-start
  ;;   :sid
  ;;
  ;; compute:
  ;;   :recovery-done-index
  ;;   :compressed-seg
  ;;
  ;; Returns a list of such records.
  (if (endp cp-rc-sid-record-list)
      nil
    (let* ((cp-rc-sid-record   (first cp-rc-sid-record-list))
           (cp-start          (rs-checkpoint-start cp-rc-sid-record))
           (recovery-start    (rs-recovery-start cp-rc-sid-record))
           (sid               (rs-sid cp-rc-sid-record))
           (initiator-rc      (pid (nth recovery-start inputs)))
           ;; If sid = :init, there may be no actual checkpoint input.
           ;; In that case, use the recovery initiator as a harmless
           ;; initiator for the cut meta, and cut-done-p will make the
           ;; cut phase finish immediately.
           (initiator-cp      (if (equal sid :init)
                                  initiator-rc
                                (pid (nth cp-start inputs))))
           (cut-result        (scan-until-cut-done inputs
                                                   trace
                                                   cp-start
                                                   sid
                                                   initiator-cp))
           (cut-meta          (cut-result-meta cut-result))
           (recovery-result   (scan-until-recovery inputs
                                                   trace
                                                   recovery-start
                                                   sid
                                                   initiator-rc))
           (recovery-done     (recovery-result-idx recovery-result))
           (recovery-meta     (recovery-result-meta recovery-result))
           ;; Use the state at cp-start for replay-order information.
           (st-cp             (nth cp-start trace))
           (compressed-seg    (generate-segment-inputs st-cp
                                                       cut-meta
                                                       recovery-meta))
           (result-rec        (>_ :recovery-done-index recovery-done
                                  :compressed-seg compressed-seg
				  :checkpoint-start-index cp-start)))
      (cons result-rec
            (generate-compressed-input-segments inputs
                                                trace
                                                (rest cp-rc-sid-record-list))))))




;; ------------------------------------------------------------------
;; Subsection F: Convert untouched original inputs into spec-compatible
;; form and stitch compressed segments left to right
;;
;; The compressed segment inputs are already built to be spec-level
;; inputs.  However, untouched portions copied directly from the
;; original implementation input sequence may still contain protocol-
;; only actions.
;;
;; This block has two responsibilities:
;;
;;   1. Convert untouched original inputs into spec-compatible form:
;;        - keep :normal as-is,
;;        - keep :receive only when the consumed message is :normal,
;;        - turn implementation-only inputs into :nop.
;;
;;      In particular, receives of marker or recovery messages must
;;      not be preserved as spec receives.
;;
;;   2. Build the final transformed input sequence by stitching
;;      compressed segments from left to right.
;;
;;      Since multiple recovery segments may be associated with the
;;      same checkpoint-start index, we first keep only the last
;;      compressed segment for each checkpoint-start.  This ensures
;;      that if several recoveries roll back to the same checkpoint,
;;      only the final one is used in the stitched result.
;;
;;      After this filtering step, stitching proceeds left to right:
;;        - copy untouched inputs from the current index up to the
;;          next checkpoint-start,
;;        - insert the compressed segment,
;;        - continue from that segment's recovery-done index.
;;
;; Result:
;;   The final output is a spec-compatible input sequence in which
;;   untouched regions are converted to spec-level inputs or :nop,
;;   and each retained checkpoint/recovery region is replaced by its
;;   compressed segment input.
;; ------------------------------------------------------------------

(defun make-nop-input (input)
  (update input :ttype :nop))

(defun spec-compatible-input (input st)
  ;; Convert any implementation-only input into a spec no-op.
  ;; Keep:
  ;;   :normal
  ;;   :receive only when the consumed msg is :normal
  ;; Convert to :nop:
  ;;   :start-checkpoint, :recover, :crash
  ;;   :receive when the consumed msg is :marker or :recovery
  (cond
   ((equal (ttype input) :normal)
    input)

   ((equal (ttype input) :receive)
    (let ((msg (current-msg-for-receive input st)))
      (if (equal (msg-type msg) :normal)
          input
        (make-nop-input input))))

   (t
    (make-nop-input input))))

(defun take-input-range-aux (inputs trace idx stop)
  ;; INPUTS is assumed to be aligned with absolute index IDX.
  ;; Collect spec-compatible inputs from absolute index IDX up to STOP-1.
  (if (or (endp inputs)
          (>= idx stop))
      nil
    (let* ((input (first inputs))
           (st    (nth idx trace))
           (input (spec-compatible-input input st)))
      (cons input
            (take-input-range-aux (rest inputs)
                                  trace
                                  (+ 1 idx)
                                  stop)))))

(defun take-input-range (inputs trace start stop)
  ;; Collect spec-compatible inputs from absolute index START up to STOP-1.
  (take-input-range-aux (nthcdr start inputs)
                        trace
                        start
                        stop))

(defun cis-record-has-checkpoint-start-p (cp-start seg-records)
  ;; Check whether some compressed-segment record in SEG-RECORDS
  ;; has checkpoint-start-index = CP-START.
  (if (endp seg-records)
      nil
    (or (equal cp-start
               (cis-checkpoint-start-index (first seg-records)))
        (cis-record-has-checkpoint-start-p cp-start
                                           (rest seg-records)))))

(defun keep-last-segments-by-checkpoint-start (seg-records)
  ;; If multiple segment records share the same checkpoint-start index,
  ;; keep only the last one. Later recoveries from the same checkpoint
  ;; override earlier ones before stitching.
  (if (endp seg-records)
      nil
    (let* ((seg       (first seg-records))
           (rest-kept (keep-last-segments-by-checkpoint-start
                       (rest seg-records)))
           (cp-start  (cis-checkpoint-start-index seg)))
      (if (cis-record-has-checkpoint-start-p cp-start rest-kept)
          rest-kept
        (cons seg rest-kept)))))

(defun stitch-compressed-inputs (inputs trace compressed-seg-records idx)
  ;; Build final transformed input list starting from absolute index IDX,
  ;; moving left to right.
  ;;
  ;; Each retained segment record contributes:
  ;;   - spec-compatible untouched inputs from IDX to checkpoint-start-1,
  ;;   - then the compressed segment itself,
  ;;   - then continue from recovery-done-index.
  ;;
  ;; recovery-done-index is treated as the first index after the region
  ;; covered by that checkpoint/recovery segment.
  (if (endp compressed-seg-records)
      (take-input-range inputs trace idx (len inputs))
    (let* ((seg-record     (first compressed-seg-records))
           (cp-start       (cis-checkpoint-start-index seg-record))
           (recovery-done  (cis-recovery-done-index seg-record))
           (compressed-seg (cis-compressed-seg seg-record)))
      (append (take-input-range inputs trace idx cp-start)
              (append compressed-seg
                      (stitch-compressed-inputs inputs
                                                trace
                                                (rest compressed-seg-records)
                                                recovery-done))))))

(defun spec-input-generation (inputs)
  (let* ((st0                        (make-initial-state))
         (trace                      (run-imp-trace st0 inputs))
         (cp-rc-sid-record-list      (collect-recovery-segments-from-trace
                                      inputs trace))
         (compressed-seg-records-raw (generate-compressed-input-segments
                                      inputs trace cp-rc-sid-record-list))
         (compressed-seg-records     (keep-last-segments-by-checkpoint-start
                                      compressed-seg-records-raw)))
    (stitch-compressed-inputs inputs
                              trace
                              compressed-seg-records
                              0)))


(defun spec-input-generation-from-state (st inputs)
  (let* ((trace                      (run-imp-trace st inputs))
         (cp-rc-sid-record-list      (collect-recovery-segments-from-trace
                                      inputs trace))
         (compressed-seg-records-raw (generate-compressed-input-segments
                                      inputs trace cp-rc-sid-record-list))
         (compressed-seg-records     (keep-last-segments-by-checkpoint-start
                                      compressed-seg-records-raw)))
    (stitch-compressed-inputs inputs
                              trace
                              compressed-seg-records
                              0)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: CP Start - Recovery Done Segment Predicate 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This section defines a predicate for recognizing one complete
;; checkpoint/recovery segment in an implementation input sequence.
;;
;; The input segment is viewed relative to a starting implementation
;; state ST, and is intended to capture a region that:
;;
;;   - starts with a checkpoint-start input,
;;   - contains exactly one recovery associated with that checkpoint,
;;   - and ends exactly when that recovery is complete.
;;
;; The definition is expressed using the executable functions already
;; available in the model, such as:
;; ------------------------------------------------------------------

;; ------------------------------------------------------------------
;; Predicate for one checkpoint-start ... recovery-done segment
;;
;; INPUT-SEG is viewed as a suffix beginning at implementation state ST.
;;
;; The segment must:
;;   - be legal from that state,
;;   - begin with :start-checkpoint,
;;   - contain exactly one recovery,
;;   - have that recovery tied to the snapshot id created by the
;;     first checkpoint-start,
;;   - have that recovery point back to checkpoint-start index 0,
;;   - and end exactly when that recovery is done.
;;
;; We define this using the executable scan functions already present
;; in the development:
;;
;;   - run-imp-trace
;;   - collect-recovery-segments-from-trace
;;   - scan-until-recovery
;;
;; Important indexing convention:
;;   recovery-result-idx is treated as the first index after the
;;   covered checkpoint/recovery region. Therefore, to say that the
;;   whole INPUT-SEG is exactly one such segment, we require:
;;
;;      recovery-result-idx = (len input-seg)
;; ------------------------------------------------------------------

(defun cp-start-rc-done-segment-p (st input-seg)
  (let* ((trace   (run-imp-trace st input-seg))

         ;; Extract recovery-segment records from the aligned trace.
         ;; Since this predicate is for the simpler case, we require
         ;; exactly one such record.
         (records (collect-recovery-segments-from-trace input-seg trace)))
    (and 
         ;; The entire segment must be legally executable from ST.
         (legal-input-sequencep st input-seg)

         ;; The segment must be nonempty and begin with a checkpoint start.
         (consp input-seg)
         (equal (ttype (first input-seg)) :start-checkpoint)

         ;; The segment must contain exactly one recovery.
         (consp records)
         (endp (rest records))

         (let* ((rec  (first records))
                (i    (pid (first input-seg)))

                ;; SID0 is the snapshot id created by the checkpoint-start
                ;; at segment index 0. Since ST is the pre-state of the
                ;; first input, the relevant counter is read from ST.
                (sid0 (list i
                            (counter (g i (procs st)))))

                ;; Extract the unique recovery information from the record.
                (x1   (rs-recovery-start rec))
                (j    (pid (nth x1 input-seg)))

                ;; Scan from that recovery-start until recovery is done.
                (recovery-result
                 (scan-until-recovery input-seg
                                      trace
                                      x1
                                      sid0
                                      j))

                ;; x2 is the first index after the recovery-complete region.
                (x2   (recovery-result-idx recovery-result)))
           (and
            ;; The unique recovery must use the snapshot id created
            ;; by the checkpoint-start at segment index 0.
            (equal (rs-sid rec) sid0)

            ;; The unique recovery must point back to checkpoint-start
            ;; at segment-relative index 0.
            (equal (rs-checkpoint-start rec) 0)

            ;; The unique recovery must finish exactly at the end of
            ;; INPUT-SEG.
            (equal x2 (len input-seg)))))))


;start target: rep-correctness-of-cp-start-rc-done-segment-general
;; State-parametric version.
;;
;; This is the cleaner theorem if INPUT-SEG is viewed as a segment
;; beginning from an arbitrary implementation state ST.



(defthm snapshot-local-state-of-step-rcv-first-marker
  (implies
   (and
    (equal (msg-type
            (get-msg-from-channel j i (channels st)))
           :marker)

    (equal (sid
            (get-msg-from-channel j i (channels st)))
           sid)

    ;; This is first marker for SID at process i.
    (not
     (memberp sid
              (snapshot-ids
               (g i (procs st))))))

   (equal
    (snapshot-local-snap-shot
     (snapshot-entry
      sid
      (g i
         (procs
          (step-rcv st i j)))))
    (local-state
     (g i
        (procs st))))))


(defthm memberp-of-remove1-equal-implies-memberp
  (implies
   (memberp x (remove1-equal y xs))
   (memberp x xs)))

(defthm local-state-of-start-checkpoint-helper
  (equal
   (local-state
    (g i
       (start-checkpoint-helper procs k)))
   (local-state
    (g i procs)))
  :hints
  (("Goal"
    :cases ((equal i k)))))


(defthm local-state-of-step-checkpoint
  (equal
   (local-state
    (g i
       (procs
        (step-checkpoint st k))))
   (local-state
    (g i
       (procs st))))
  :hints
  (("Goal"
    :in-theory
    (disable start-checkpoint-helper))))

(defthm run-spec-of-append-singleton
  (equal
   (run-spec st (append xs (list input)))
   (spec-step
    (run-spec st xs)
    input)))

(defthm local-state-of-update-proc-for-normal-msg-core
  (equal
   (local-state
    (update-proc-for-normal-msg-core p j msg))
   (update-local-state-rcv
    (local-state p)
    msg
    j)))



(defthm local-state-of-handle-first-marker-msg-different-proc
  (implies
   (not (equal k i))
   (equal
    (local-state
     (g k
        (procs
         (handle-first-marker-msg st i j msg))))
    (local-state
     (g k
        (procs st))))))


(defthm local-state-of-handle-non-first-marker-msg-different-proc
  (implies
   (not (equal k i))
   (equal
    (local-state
     (g k
        (procs
         (handle-non-first-marker-msg st i j msg))))
    (local-state
     (g k
        (procs st))))))

(defthm local-state-of-handle-marker-msg-different-proc
  (implies
   (not (equal k i))
   (equal
    (local-state
     (g k
        (procs
         (handle-marker-msg st i j msg))))
    (local-state
     (g k
        (procs st))))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Local-state preservation for marker handling
;;
;; Goal:
;;   Marker handling may update snapshot metadata and channels, but it
;;   must not change any process local state.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Updating snapshot tables does not change local-state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm local-state-of-set-snapshot-entry
  (equal
   (local-state
    (set-snapshot-entry sid entry p))
   (local-state p)))



(defthm local-state-of-install-snapshot-entry
  (equal
   (local-state
    (install-snapshot-entry sid entry p))
   (local-state p)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Marker-specific process updates do not change local-state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm local-state-of-update-proc-for-first-marker-msg
  (equal
   (local-state
    (update-proc-for-first-marker-msg p sid j))
   (local-state p)))



(defthm local-state-of-update-proc-for-non-first-marker-msg
  (equal
   (local-state
    (update-proc-for-non-first-marker-msg p sid j))
   (local-state p)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Updating one process in the process table preserves local-state
;;    of every process if the replacement process has the same local-state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm local-state-of-set-proc-when-new-proc-local-state-same
  (implies
   (equal
    (local-state new-p)
    (local-state
     (g i procs)))
   (equal
    (local-state
     (g k
        (s i new-p procs)))
    (local-state
     (g k procs))))
  :hints
  (("Goal"
    :cases ((equal k i)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. First-marker handler preserves every process local-state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm local-state-of-handle-first-marker-msg
  (equal
   (local-state
    (g k
       (procs
        (handle-first-marker-msg st i j msg))))
   (local-state
    (g k
       (procs st)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Non-first-marker handler preserves every process local-state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm local-state-of-handle-non-first-marker-msg
  (equal
   (local-state
    (g k
       (procs
        (handle-non-first-marker-msg st i j msg))))
   (local-state
    (g k
       (procs st)))))


(defthm local-state-of-handle-marker-msg
  (equal
   (local-state
    (g k
       (procs
        (handle-marker-msg st i j msg))))
   (local-state
    (g k
       (procs st)))))

(defthm not-proc-status-recovering-when-not-any-proc-recovering-p
  (implies
   (and
    (not (any-proc-recovering-p ids procs))
    (memberp i ids))
   (not
    (equal
     (proc-status (g i procs))
     :recovering))))

(defthm not-proc-status-recovering-when-no-process-recovering
  (implies
   (and
    (not (any-process-recovering-p st))
    (memberp i (proc-ids st)))
   (not
    (equal
     (proc-status (g i (procs st)))
     :recovering))))


(defthm not-equal-when-memberp-and-not-memberp-same-list
  (implies
   (and
    (memberp x xs)
    (not (memberp y xs)))
   (not (equal x y)))
  :hints
  (("Goal"
    :cases ((equal x y)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Updating a different process does not change i's local state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm local-state-of-g-of-s-different-proc
  (implies
   (not (equal i k))
   (equal
    (local-state
     (g i
        (s k new-p procs)))
    (local-state
     (g i procs)))))


(defun cut-scan-spec-imp-local-match-p
    (i  m imp-st spec-start-st)
   (equal
    (local-state
     (g i
        (procs
         (run-spec spec-start-st
                   (cm-inputs-before-cut m)))))
    (local-state
     (g i
        (procs imp-st)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Process i stays before its first marker for the whole segment
;;
;; This says i is in CUT-NOT-TAKEN at the beginning, after every step,
;; and therefore also at the end of the segment.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cut-scan-proc-stays-cut-not-taken-step-p (i input st m)
  (let ((m-next (process-cut-step input st m)))
    (and
     (memberp i (cm-cut-not-taken m))
     (memberp i (cm-cut-not-taken m-next)))))


(defun cut-scan-proc-stays-cut-not-taken-p (i inputs st m)
  (if (endp inputs)
      (memberp i (cm-cut-not-taken m))
    (let* ((input  (first inputs))
           (m-next (process-cut-step input st m))
           (st-next (system-step st input)))
      (and
       (cut-scan-proc-stays-cut-not-taken-step-p i input st m)
       (cut-scan-proc-stays-cut-not-taken-p
        i
        (rest inputs)
        st-next
        m-next)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; No recovery behavior inside this before-first-marker segment
;;
;; This matches the side conditions of
;; CUT-SCAN-SPEC-IMP-LOCAL-MATCH-BEFORE-FIRST-MARKER-STEP.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cut-scan-no-recovery-step-p (input st)
  (and
   (not (any-process-recovering-p st))
   (not (equal (ttype input) :recover))
   (implies
    (equal (ttype input) :receive)
    (not
     (equal
      (msg-type
       (get-msg-from-channel
        (sender input)
        (pid input)
        (channels st)))
      :recovery)))))

(defun cut-scan-no-recovery-segment-p (inputs st)
  (if (endp inputs)
      t
    (let* ((input   (first inputs))
           (st-next (system-step st input)))
      (and
       (cut-scan-no-recovery-step-p input st)
       (cut-scan-no-recovery-segment-p
        (rest inputs)
        st-next)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Channel-head match over the whole segment
;;
;; For now this is an explicit hypothesis.  Later, prove this from
;; implementation/spec channel equivalence.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun cut-scan-channel-msg-match-p
    (j i m imp-st spec-start-st)
  ;; If the implementation head message on channel j -> i is normal,
  ;; then the corresponding spec head message agrees with it.
  ;;
  ;; We do not require INPUT to be a receive here.  This predicate is a
  ;; pure channel-head condition, and later it can be derived from channel
  ;; equivalence.
  (let ((spec-st (run-spec spec-start-st
                           (cm-inputs-before-cut m))))
    (implies
     (equal
      (msg-type
       (get-msg-from-channel j i (channels imp-st)))
      :normal)
     (equal
      (get-msg-from-channel j i (channels spec-st))
      (get-msg-from-channel j i (channels imp-st))))))


(defun cut-scan-channel-msg-match-segment-p
    (inputs st m spec-start-st)
  (if (endp inputs)
      t
    (let* ((input   (first inputs))
           (m-next  (process-cut-step input st m))
           (st-next (system-step st input)))
      (and
       (cut-scan-channel-msg-match-p
        (sender input)
        (pid input)
        m
        st
        spec-start-st)
       (cut-scan-channel-msg-match-segment-p
        (rest inputs)
        st-next
        m-next
        spec-start-st)))))



(defthm cut-scan-spec-imp-local-match-before-first-marker-step
  (implies
   (and
    ;; Local-state invariant before this cut-scan step.
    (cut-scan-spec-imp-local-match-p
     i m st-cur spec-start-st)

    ;; Process i remains before the cut during this step.
    (cut-scan-proc-stays-cut-not-taken-step-p
     i input st-cur m)

    ;; Current input is legal in the implementation state.
    (legal-inputp st-cur input)

    ;; If the relevant implementation channel head is normal, then the
    ;; spec and implementation channel heads match.
    ;; No :receive condition is needed here because this is a pure
    ;; channel-head condition.
    (cut-scan-channel-msg-match-p
     (sender input)
     (pid input)
     m
     st-cur
     spec-start-st)

    ;; No recovery behavior in this one-step before-first-marker segment.
    (cut-scan-no-recovery-step-p input st-cur)

    ;; st-next is the implementation state after INPUT.
    (equal st-next
           (system-step st-cur input))

    ;; m-next is the cut metadata after processing INPUT.
    (equal m-next
           (process-cut-step input st-cur m)))

   ;; Local-state invariant after this cut-scan step.
   (cut-scan-spec-imp-local-match-p
    i m-next st-next spec-start-st))

  :hints
  (("Goal"
    :cases
    ((equal i (pid input))
     (equal
      (msg-type
       (get-msg-from-channel
        (sender input)
        (pid input)
        (channels st-cur)))
      :normal))
    :in-theory
    (disable
     step-checkpoint
     step-recover
     start-checkpoint-helper
     start-recovery-helper
     recovery-local-state-after-replay

     handle-marker-msg
     handle-first-marker-msg
     handle-non-first-marker-msg
     update-proc-for-first-marker-msg
     update-proc-for-non-first-marker-msg

     handle-recovery-msg
     handle-first-recovery-msg
     handle-non-first-recovery-msg
     update-proc-for-first-recovery-msg
     update-proc-for-non-first-recovery-msg))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;start target: cut-scan-local-match-over-input-segment

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Segment scan for cut metadata
;;
;; This runs PROCESS-CUT-STEP over an input segment while advancing the
;; implementation state in parallel.  It is the segment-level version of
;; one cut-scan step.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun process-cut-segment (inputs st m)
  (if (endp inputs)
      m
    (let* ((input (first inputs))
           (m-next (process-cut-step input st m))
           (st-next (system-step st input)))
      (process-cut-segment (rest inputs)
                           st-next
                           m-next))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Segment-level local-state match before first marker
;;
;; If process i stays in CUT-NOT-TAKEN throughout the input segment, there is no
;; recovery behavior in the segment, and the needed normal channel-head matches
;; hold at each step, then the local-state match is preserved after running the
;; whole segment.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm cut-scan-spec-imp-local-match-over-input-segment
  (implies
   (and
    ;; Local-state invariant at the beginning of the segment.
    (cut-scan-spec-imp-local-match-p
     i m st spec-start-st)

    ;; Process i remains before its first marker throughout the segment.
    (cut-scan-proc-stays-cut-not-taken-p
     i inputs st m)

    ;; Every input is legal along the implementation run.
    (legal-input-sequencep st inputs)

    ;; At each step, if the relevant implementation channel head is normal,
    ;; then the corresponding spec/imp channel heads match.
    (cut-scan-channel-msg-match-segment-p
     inputs st m spec-start-st)

    ;; No recovery behavior occurs anywhere in this segment.
    (cut-scan-no-recovery-segment-p
     inputs st))

   ;; Local-state invariant after the whole segment.
   (cut-scan-spec-imp-local-match-p
    i
    (process-cut-segment inputs st m)
    (run-imp st inputs)
    spec-start-st))

  :hints
  (("Goal"
    :induct
    (process-cut-segment inputs st m)
    :in-theory
    (disable
      cut-scan-spec-imp-local-match-p
      cut-scan-channel-msg-match-p
      cut-scan-no-recovery-step-p
      cut-scan-proc-stays-cut-not-taken-step-p
      legal-inputp
      system-step
      process-cut-step))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Process i takes the cut during this one step
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cut-scan-proc-takes-cut-step-p (i input st m)
  (and
   (memberp i (cm-cut-not-taken m))
   (not
    (memberp i
             (cm-cut-not-taken
              (process-cut-step input st m))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Spec local state matches the saved local snapshot for sid at process i
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cut-scan-spec-snapshot-local-match-p
    (i sid m imp-st spec-start-st)
  (equal
   (local-state
    (g i
       (procs
        (run-spec spec-start-st
                  (cm-inputs-before-cut m)))))
   (snapshot-local-snap-shot
    (snapshot-entry sid
                    (g i (procs imp-st))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; When process i takes the cut, its saved snapshot local state matches spec
;;
;; Intuition:
;;   - Before this step, i is still before the cut.
;;   - Therefore the spec state obtained by running cm-inputs-before-cut
;;     matches i's current implementation local state.
;;   - This step is the first marker receive for i.
;;   - handle-first-marker-msg saves i's current implementation local state
;;     into the snapshot entry for sid.
;;   - Therefore the spec local state matches the saved snapshot local state.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm local-snap-shot-of-update-proc-for-first-marker-msg
  (equal
   (g :local-snap-shot
      (g sid
         (g :snapshots
            (update-proc-for-first-marker-msg p sid j))))
   (g :local-state p)))

(defthm cut-scan-spec-local-match-implies-snapshot-local-match-when-cut-taken-step
  (implies
   (and
    ;; Before this step, spec-prefix local state matches implementation local state.
    (cut-scan-spec-imp-local-match-p
     i m st-cur spec-start-st)

    ;; Process i takes the cut during this step.
    (cut-scan-proc-takes-cut-step-p
     i input st-cur m)

    ;; The step is legal.
    (legal-inputp st-cur input)

    ;; This cut-taking step is a receive at process i.
    (equal (ttype input) :receive)
    (equal (pid input) i)

    ;; The received message is the marker that causes the cut.
    (equal msg
           (get-msg-from-channel
            (sender input)
            i
            (channels st-cur)))
    (equal (msg-type msg) :marker)

    ;; First-marker case: i did not already know this snapshot id.
    ;; This is the implementation condition that makes handle-marker-msg call
    ;; handle-first-marker-msg, which saves the current local state.
    (not
     (memberp (sid msg)
              (snapshot-ids
               (g i (procs st-cur)))))

    ;; The marker sid is known somewhere, usually from good-state/legal channel
    ;; invariants. Keep it explicit here if ACL2 needs it to open the handler.
    (some-proc-has-snapshot-id-p
     (sid msg)
     (proc-ids st-cur)
     (procs st-cur))

    ;; Name the post-state.
    (equal st-next
           (system-step st-cur input)))

   ;; After the step, the saved local snapshot for this sid matches the
   ;; spec local state at the cut prefix.
   (cut-scan-spec-snapshot-local-match-p
    i
    (sid msg)
    m
    st-next
    spec-start-st))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (cut-scan-proc-takes-cut-step-p
      cut-scan-spec-snapshot-local-match-p
      cut-scan-spec-imp-local-match-p
      system-step
      step-rcv
      handle-marker-msg
      handle-first-marker-msg)

     (step-checkpoint
      step-recover
      start-checkpoint-helper
      start-recovery-helper
      recovery-local-state-after-replay

      handle-non-first-marker-msg
      update-proc-for-first-marker-msg
      update-proc-for-non-first-marker-msg

      handle-recovery-msg
      handle-first-recovery-msg
      handle-non-first-recovery-msg
      update-proc-for-first-recovery-msg
      update-proc-for-non-first-recovery-msg)))))



(defthm nbrs-from-of-system-step-start-checkpoint
  (implies
   (equal (g :ttype input) :start-checkpoint)
   (equal
    (g :nbrs-from
       (g i (g :procs (system-step st input))))
    (g :nbrs-from
       (g i (g :procs st)))))
  :hints
  (("Goal"
    :in-theory
    (disable start-checkpoint-helper))))


(defthm nbrs-from-of-g-of-step-rcv
  (equal
   (nbrs-from
    (g k (procs (step-rcv st i j))))
   (nbrs-from
    (g k (procs st))))
  :hints
  (("Goal"
    :in-theory
    (e/d
     (step-rcv
      handle-normal-msg
      handle-normal-msg-core
      ignore-normal-msg
      handle-marker-msg
      handle-first-marker-msg
      handle-non-first-marker-msg
      handle-recovery-msg
      handle-first-recovery-msg
      handle-non-first-recovery-msg)

     (remove-message-from-channel
      send-msg-all-outgoing-channels
      update-proc-for-normal-msg-core
      update-proc-for-first-marker-msg
      update-proc-for-non-first-marker-msg
      update-proc-for-first-recovery-msg
      update-proc-for-non-first-recovery-msg)))))


(defthm nbrs-from-of-g-of-step-normal
  (equal
   (nbrs-from
    (g k (procs (step-normal st i))))
   (nbrs-from
    (g k (procs st))))
  :hints
  (("Goal"
    :in-theory
    (e/d (step-normal)
         (send-compute-message)))))


(defthm nbrs-from-of-g-of-step-checkpoint
  (equal
   (nbrs-from
    (g k (procs (step-checkpoint st i))))
   (nbrs-from
    (g k (procs st))))
  :hints
  (("Goal"
    :in-theory
    (e/d (step-checkpoint)
         (start-checkpoint-helper
          send-msg-all-outgoing-channels
          create-marker-message)))))


(defthm nbrs-from-of-g-of-step-crash
  (equal
   (nbrs-from
    (g k (procs (step-crash st i))))
   (nbrs-from
    (g k (procs st))))
  :hints
  (("Goal"
    :in-theory
    (enable step-crash))))


(defthm nbrs-from-of-g-of-step-recover
  (equal
   (nbrs-from
    (g k (procs (step-recover st i))))
   (nbrs-from
    (g k (procs st))))
  :hints
  (("Goal"
    :in-theory
    (e/d (step-recover)
         (start-recovery-helper
          send-msg-all-outgoing-channels
          create-recovery-message
          recovery-local-state-after-replay)))))



(defthm nbrs-from-of-g-of-system-step
  (equal
   (nbrs-from
    (g k (procs (system-step st input))))
   (nbrs-from
    (g k (procs st))))
  :hints
  (("Goal"
    :in-theory
    (e/d (system-step)
         (step-rcv
          step-normal
          step-checkpoint
          step-crash
          step-recover)))))




(defthm incoming-channels-equivalent-for-proc-p-of-system-step-start-checkpoint-left
  (implies
   (and
    (equal (g :ttype input) :start-checkpoint)

    (incoming-channels-equivalent-for-proc-p
     srcs
     dst
     (g :channels st)
     spec-channels))

   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (g :channels (system-step st input))
    spec-channels))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (system-step
      step-checkpoint)

     (send-msg-all-outgoing-channels
      create-marker-message
      incoming-channels-equivalent-for-proc-p)))))

(defthm msg-type-of-get-msg-from-channel-marker-implies-not-normal
  (implies
   (equal
    (msg-type
     (get-msg-from-channel j k channels))
    :marker)

   (not
    (equal
     (msg-type
      (get-msg-from-channel j k channels))
     :normal))))


(defthm g-msg-type-of-get-msg-from-channel-marker-implies-msg-type-not-normal
  (implies
   (equal
    (g :msg-type
       (get-msg-from-channel j k channels))
    :marker)
   (not
    (equal
     (msg-type
      (get-msg-from-channel j k channels))
     :normal))))

(defthm incoming-channels-equivalent-for-proc-p-of-remove-message-from-channel-left-marker
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst channels spec-channels)

    (consp
     (channel-state j k channels))

    (equal
     (g :msg-type
        (get-msg-from-channel j k channels))
     :marker))

   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (remove-message-from-channel j k channels)
    spec-channels)))

(defthm incoming-channels-equivalent-for-proc-p-of-step-rcv-marker-left
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs
     dst
     (g :channels st)
     spec-channels)

    (consp
     (channel-state j k (g :channels st)))

    (equal
     (msg-type
      (get-msg-from-channel j k (g :channels st)))
     :marker))

   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (g :channels (step-rcv st k j))
    spec-channels))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (step-rcv
      handle-marker-msg
      handle-first-marker-msg
      handle-non-first-marker-msg)

     (incoming-channels-equivalent-for-proc-p
      get-msg-from-channel
      incoming-channels-equivalent-for-proc-p-of-remove-message-from-channel-left
      incoming-channels-equivalent-for-proc-p-of-send-marker-left
      remove-message-from-channel
      send-msg-all-outgoing-channels
      create-marker-message)))))

(defthm consp-of-channel-state-when-get-msg-from-channel-has-marker-type
  (implies
   (equal
    (g :msg-type
       (get-msg-from-channel j k channels))
    :marker)
   (consp
    (channel-state j k channels))))


(defthm consp-channel-state-when-get-msg-from-channel-marker
  (implies
   (equal
    (g :msg-type
       (get-msg-from-channel j k channels))
    :marker)
   (consp
    (channel-state j k channels))))

(defthm replay-inputs-for-one-proc-of-s-cut-not-taken
  (equal
   (replay-inputs-for-one-proc
    i nbrs
    (s :cut-not-taken cut-not-taken m))
   (replay-inputs-for-one-proc
    i nbrs m)))

(defthm replay-inputs-for-one-proc-of-s-waiting-marker-from
  (equal
   (replay-inputs-for-one-proc
    i nbrs
    (s :waiting-marker-from waiting-marker-from m))
   (replay-inputs-for-one-proc
    i nbrs m)))

(defthm replay-inputs-for-one-proc-of-first-marker-cut-meta-update
  (equal
   (replay-inputs-for-one-proc
    i nbrs
    (s :cut-not-taken
       cut-not-taken
       (s :waiting-marker-from
          waiting-marker-from
          m)))
   (replay-inputs-for-one-proc
    i nbrs m)))


(defthm step-rcv-when-head-msg-type-is-unknown
  (implies
   (and
    (not
     (equal
      (g :msg-type
         (get-msg-from-channel j k (g :channels st)))
      :normal))

    (not
     (equal
      (g :msg-type
         (get-msg-from-channel j k (g :channels st)))
      :marker))

    (not
     (equal
      (g :msg-type
         (get-msg-from-channel j k (g :channels st)))
      :recovery)))

   (equal
    (step-rcv st k j)
    st)))


(defthm cut-scan-no-recovery-step-p-receive-implies-input-head-not-recovery
  (implies
   (and
    (cut-scan-no-recovery-step-p input st)
    (equal (g :ttype input) :receive))

   (not
    (equal
     (g :msg-type
        (get-msg-from-channel
         (g :sender input)
         (g :pid input)
         (g :channels st)))
     :recovery))))


(defthm step-rcv-input-when-head-msg-type-is-unknown
  (implies
   (and
    ;; This is a receive input.
    (equal (g :ttype input) :receive)

    ;; The selected channel head is not normal.
    (not
     (equal
      (g :msg-type
         (get-msg-from-channel
          (g :sender input)
          (g :pid input)
          (g :channels st)))
      :normal))

    ;; The selected channel head is not marker.
    (not
     (equal
      (g :msg-type
         (get-msg-from-channel
          (g :sender input)
          (g :pid input)
          (g :channels st)))
      :marker))

    ;; No recovery receive in this cut-scan step.
    (cut-scan-no-recovery-step-p input st))

   ;; Therefore step-rcv takes the unknown-message branch and leaves st unchanged.
   (equal
    (step-rcv st
              (g :pid input)
              (g :sender input))
    st))

  :hints
  (("Goal"
    :in-theory
    (disable
     step-rcv))))

(defthm incoming-channels-equivalent-for-proc-p-of-remove-message-from-channel-left-different-dst
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)

    ;; We remove from rm-src -> rm-dst, but incoming equivalence is for dst.
    ;; If rm-dst is different from dst, no incoming channel into dst changes.
    (not (equal rm-dst dst)))

   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (remove-message-from-channel rm-src rm-dst imp-channels)
    spec-channels)))


(defthm incoming-channels-equivalent-for-proc-p-of-step-rcv-normal-different-dst-left
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst
     (g :channels st)
     spec-channels)
    (not (equal k dst)))

   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (g :channels (step-rcv st k j))
    spec-channels))

  :hints
  (("Goal"
    :in-theory
    (disable
     incoming-channels-equivalent-for-proc-p
     remove-message-from-channel))))



;start support: replay for i ignores inputs-after-cut updates for other procs

(defthm replay-inputs-for-one-proc-of-s-inputs-after-cut-different-proc
  (implies
   (not (equal k i))
   (equal
    (replay-inputs-for-one-proc
     i nbrs
     (s :inputs-after-cut
        (s k new-row (g :inputs-after-cut m))
        m))
    (replay-inputs-for-one-proc
     i nbrs m))))

;end support: replay for i ignores inputs-after-cut updates for other procs


(defthm replay-inputs-for-one-proc-of-s-inputs-before-cut
  (equal
   (replay-inputs-for-one-proc
    i nbrs
    (s :inputs-before-cut inputs-before-cut m))
   (replay-inputs-for-one-proc
    i nbrs m)))


(defthm waiting-marker-row-of-s-different-proc
  (implies
   (not (equal k i))
   (equal
    (g i
       (s k new-waiting-row waiting-marker-from))
    (g i waiting-marker-from))))



(defthm incoming-channels-equivalent-for-proc-p-of-remove1-equal-srcs
  (implies
   (incoming-channels-equivalent-for-proc-p
    srcs dst imp-channels spec-channels)
   (incoming-channels-equivalent-for-proc-p
    (remove1-equal x srcs)
    dst imp-channels spec-channels)))


(defthm incoming-channels-equivalent-for-proc-p-of-step-rcv-marker-left-shrink-srcs
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs
     dst
     (g :channels st)
     spec-channels)

    (consp
     (g j (g k (g :channels st))))

    (equal
     (msg-type
      (get-msg-from-channel j k (g :channels st)))
     :marker))

   (incoming-channels-equivalent-for-proc-p
    (remove1-equal j srcs)
    dst
    (g :channels (step-rcv st k j))
    spec-channels))

  :hints
  (("Goal"
    :in-theory
    (disable
     step-rcv
     get-msg-from-channel
     incoming-channels-equivalent-for-proc-p
     remove1-equal))))

(defthm incoming-channels-equivalent-for-proc-p-of-step-rcv-marker-left-waiting-update
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     (g i waiting-marker-from)
     i
     (g :channels st)
     spec-channels)

    (consp
     (g j (g k (g :channels st))))

    (equal
     (msg-type
      (get-msg-from-channel j k (g :channels st)))
     :marker))

   (incoming-channels-equivalent-for-proc-p
    (g i
       (s k
          (remove1-equal j
                         (g k waiting-marker-from))
          waiting-marker-from))
    i
    (g :channels (step-rcv st k j))
    spec-channels))

  :hints
  (("Goal"
    :cases ((equal k i))

    :use
    ((:instance
      incoming-channels-equivalent-for-proc-p-of-step-rcv-marker-left
      (srcs (g i waiting-marker-from))
      (dst i)
      (st st)
      (j j)
      (k k)
      (spec-channels spec-channels))

     (:instance
      incoming-channels-equivalent-for-proc-p-of-step-rcv-marker-left-shrink-srcs
      (srcs (g i waiting-marker-from))
      (dst i)
      (st st)
      (j j)
      (k k)
      (spec-channels spec-channels)))

    :in-theory
    (disable
     step-rcv
     get-msg-from-channel
     incoming-channels-equivalent-for-proc-p
     remove1-equal
     incoming-channels-equivalent-for-proc-p-of-step-rcv-marker-left
     incoming-channels-equivalent-for-proc-p-of-step-rcv-marker-left-shrink-srcs))))


(defthm g-waiting-marker-for-of-cm-after-cut-append
  (equal
   (g i
      (g :waiting-marker-from
         (cm-after-cut-append m k j input)))
   (g i
      (g :waiting-marker-from m))))


(defthm replay-inputs-for-one-proc-of-cm-after-cut-append-different-proc
  (implies
   (not (equal k i))
   (equal
    (replay-inputs-for-one-proc
     i nbrs
     (cm-after-cut-append m k j input))
    (replay-inputs-for-one-proc
     i nbrs m))))


;; (defthm run-spec-of-append
;;   (equal
;;    (run-spec st (append xs ys))
;;    (run-spec (run-spec st xs) ys)))



(defun receive-input-listp (xs)
  (if (endp xs)
      t
    (and
     (equal (g :ttype (car xs)) :receive)
     (receive-input-listp (cdr xs)))))

  
; ------------------------------------------------------------
; After-cut well-formedness:
; For process DST, every entry stored under source SRC in
; :inputs-after-cut contains only receive inputs from SRC -> DST.
; ------------------------------------------------------------

(defun receive-inputs-from-to-p (src dst xs)
  (if (endp xs)
      t
    (and
     (equal (g :ttype  (car xs)) :receive)
     (equal (g :sender (car xs)) src)
     (equal (g :pid    (car xs)) dst)
     (receive-inputs-from-to-p src dst (cdr xs)))))


(defun after-cut-row-well-formed-p (dst srcs row)
  (if (endp srcs)
      t
    (and
     (receive-inputs-from-to-p
      (car srcs)
      dst
      (g (car srcs) row))
     (after-cut-row-well-formed-p
      dst
      (cdr srcs)
      row))))


(defun after-cut-for-proc-well-formed-p (i nbrs m)
  (after-cut-row-well-formed-p
   i
   nbrs
   (g i (g :inputs-after-cut m))))


; ------------------------------------------------------------
; Main one-channel theorem:
; For a fixed incoming channel SRC -> I, replaying after
; CM-AFTER-CUT-APPEND gives the same channel SRC -> I as
; replaying old inputs and then INPUT at the end.
; ------------------------------------------------------------



; Support: channel SRC -> DST depends only on receive inputs
; from SRC -> DST.
; ------------------------------------------------------------

(defun no-receive-from-channel-p (src dst xs)
  (if (endp xs)
      t
    (and
     (or
      (not (equal (g :ttype  (car xs)) :receive))
      (not (equal (g :sender (car xs)) src))
      (not (equal (g :pid    (car xs)) dst)))
     (no-receive-from-channel-p src dst (cdr xs)))))

(defthm channel-state-of-run-spec-suffix-no-receive-from-channel
  (implies
   (and
    (receive-input-listp suffix)
    (no-receive-from-channel-p src dst suffix))

   (equal
    (channel-state
     src dst
     (g :channels (run-spec st suffix)))

    (channel-state
     src dst
     (g :channels st)))))

; If SUFFIX contains only receive inputs and none of them receives
; from SRC -> DST, then appending SUFFIX after PREFIX does not change
; channel SRC -> DST.

(defthm channel-state-of-run-spec-append-suffix-no-receive-from-channel
  (implies
   (and
    (receive-input-listp suffix)
    (no-receive-from-channel-p src dst suffix))

   (equal
    (channel-state
     src dst
     (g :channels
        (run-spec st
                  (append prefix suffix))))

    (channel-state
     src dst
     (g :channels
        (run-spec st prefix))))))


; If PREFIX contains no receive from SRC -> DST, then running PREFIX
; before SUFFIX does not change the final channel SRC -> DST.
;
; This is the exchanged version of:
;   append prefix suffix  vs prefix
;
; Now:
					;   append prefix suffix  vs suffix

(defthm g-channel-of-spec-step-receive-not-from-channel
  (implies
   (and
    (equal (g :ttype input) :receive)
    (or
     (not (equal (g :sender input) src))
     (not (equal (g :pid input) dst))))
   (equal
    (g src
       (g dst
          (g :channels (spec-step st input))))
    (g src
       (g dst
          (g :channels st))))))

(defthm g-channel-of-run-spec-same-when-same-initial-channel
  (implies
   (and
    (receive-input-listp xs)
    (equal
     (g src (g dst (g :channels st1)))
     (g src (g dst (g :channels st2)))))
   (equal
    (g src
       (g dst
          (g :channels (run-spec st1 xs))))
    (g src
       (g dst
          (g :channels (run-spec st2 xs)))))))



(defthm g-channel-of-run-spec-cons-receive-not-from-channel
  (implies
   (and
    ;; The first input is a receive.
    (equal (g :ttype input) :receive)

    ;; But it is not a receive from SRC -> DST.
    (or
     (not (equal (g :sender input) src))
     (not (equal (g :pid input) dst)))

    ;; The rest of the list is receive-only, so its effect on SRC -> DST
    ;; depends only on the initial SRC -> DST channel.
    (receive-input-listp rest))

   (equal
    (g src
       (g dst
          (g :channels
             (run-spec st
                       (cons input rest)))))

    (g src
       (g dst
          (g :channels
             (run-spec st rest))))))

  :hints
  (("Goal"
    :use
    ((:instance
      g-channel-of-spec-step-receive-not-from-channel
      (input input)
      (src src)
      (dst dst)
      (st st))

     (:instance
      g-channel-of-run-spec-same-when-same-initial-channel
      (src src)
      (dst dst)
      (st1 (spec-step st input))
      (st2 st)
      (xs rest)))

    :in-theory
    (e/d
     (run-spec
      receive-input-listp)

     (spec-step
      spec-step-rcv
      g-channel-of-spec-step-receive-not-from-channel
      g-channel-of-run-spec-same-when-same-initial-channel)))))


(defthm receive-input-listp-of-append
  (implies
   (and
    (receive-input-listp xs)
    (receive-input-listp ys))
   (receive-input-listp
    (append xs ys))))

(defthm channel-state-of-run-spec-append-prefix-no-receive-from-channel
  (implies
   (and
    (receive-input-listp prefix)
    (no-receive-from-channel-p src dst prefix)
    (receive-input-listp suffix))

   (equal
    (channel-state
     src dst
     (g :channels
        (run-spec st
                  (append prefix suffix))))

    (channel-state
     src dst
     (g :channels
        (run-spec st suffix)))))

  :hints
  (("Goal"
    :in-theory
    (disable
     run-spec
      spec-step
      spec-step-rcv))))

(defthm replay-inputs-for-one-proc-receive-list-and-no-receive-from-channel
  (implies
   (and
    (after-cut-row-well-formed-p
     dst nbrs
     (g dst (g :inputs-after-cut m)))

    (not (memberp src nbrs)))

   (and
    (receive-input-listp
     (replay-inputs-for-one-proc dst nbrs m))

    (no-receive-from-channel-p
     src dst
     (replay-inputs-for-one-proc dst nbrs m)))))


(defthm receive-input-listp-when-receive-inputs-from-to-p
  (implies
   (receive-inputs-from-to-p other-src dst xs)
   (receive-input-listp xs)))

(defthm no-receive-from-channel-p-when-receive-inputs-from-to-p-different-src
  (implies
   (and
    (receive-inputs-from-to-p other-src dst xs)
    (not (equal src other-src)))
   (no-receive-from-channel-p src dst xs)))


(defthm memberp-cdr-and-not-memberp-car-cdr-implies-not-equal
  (implies
   (and
    (memberp src (cdr nbrs))
    (not (memberp (car nbrs) (cdr nbrs))))
   (not (equal src (car nbrs)))))

(defthm after-cut-meta-row-entry-receive-list-and-no-receive-from-channel
  (implies
   (and
    (memberp row-src srcs)
    (not (equal src row-src))
    (after-cut-row-well-formed-p
     dst
     srcs
     (g dst (g :inputs-after-cut m))))

   (and
    (receive-input-listp
     (g row-src
        (g dst (g :inputs-after-cut m))))

    (no-receive-from-channel-p
     src
     dst
     (g row-src
        (g dst (g :inputs-after-cut m)))))))




(defthm channel-state-of-run-spec-replay-inputs-for-one-proc-is-row-only
  (implies
   (and
    (memberp src nbrs)
    (uniquep nbrs)
    (after-cut-row-well-formed-p
     dst nbrs
     (g dst (g :inputs-after-cut m))))

   (equal
    (channel-state
     src dst
     (g :channels
        (run-spec
         spec-start-st
         (replay-inputs-for-one-proc dst nbrs m))))

    (channel-state
     src dst
     (g :channels
        (run-spec
         spec-start-st
         (cm-after-cut-get m dst src))))))

  :hints
  (("Goal"
    :cases ((equal src (car nbrs)))
    :in-theory


    (disable
     run-spec
      spec-step
      spec-step-rcv))))




(defthm cm-after-cut-get-of-cm-after-cut-append-different-src
  (implies
   (not (equal src j))
   (equal
    (cm-after-cut-get
     (cm-after-cut-append m dst j input)
     dst
     src)
    (cm-after-cut-get m dst src))))


(defthm receive-inputs-from-to-p-of-append-singleton
  (implies
   (and
    (receive-inputs-from-to-p src dst xs)

    ;; The new input is exactly a receive from SRC to DST.
    (equal (g :ttype input) :receive)
    (equal (g :sender input) src)
    (equal (g :pid input) dst))

   (receive-inputs-from-to-p
    src dst
    (append xs (list input)))))
  
(defthm receive-inputs-from-to-p-when-after-cut-row-well-formed-p
  (implies
   (and
    (after-cut-row-well-formed-p dst srcs row)
    (memberp src srcs))

   (receive-inputs-from-to-p
    src dst
    (g src row))))


(defthm inputs-after-cut-row-of-cm-after-cut-append-same-dst
  (equal
   (g dst
      (g :inputs-after-cut
         (cm-after-cut-append m dst j input)))

   (s j
      (append
       (g j
          (g dst
             (g :inputs-after-cut m)))
       (list input))
      (g dst
         (g :inputs-after-cut m)))))


(defthm after-cut-row-well-formed-p-of-cm-after-cut-append
  (implies
   (and
    (after-cut-row-well-formed-p
     dst nbrs
     (g dst (g :inputs-after-cut m)))

    (memberp j nbrs)
    (uniquep nbrs)

    (equal (g :ttype input) :receive)
    (equal (g :pid input) dst)
    (equal (g :sender input) j))

   (after-cut-row-well-formed-p
    dst
    nbrs
    (g dst
       (g :inputs-after-cut
          (cm-after-cut-append m dst j input))))))




(defthm g-channel-of-run-spec-replay-inputs-for-one-proc-of-cm-after-cut-append-different-src
  (implies
   (and
    (not (equal src (g :sender input)))

    (equal (g :ttype input) :receive)

    (memberp (g :sender input) nbrs)
    (memberp src nbrs)
    (uniquep nbrs)

    (after-cut-row-well-formed-p
     (g :pid input)
     nbrs
     (g (g :pid input)
        (g :inputs-after-cut m))))

   (equal
    (g src
       (g (g :pid input)
          (g :channels
             (run-spec
              spec-start-st
              (replay-inputs-for-one-proc
               (g :pid input)
               nbrs
               (cm-after-cut-append
                m
                (g :pid input)
                (g :sender input)
                input))))))

    (g src
       (g (g :pid input)
          (g :channels
             (run-spec
              spec-start-st
              (replay-inputs-for-one-proc
               (g :pid input)
               nbrs
               m)))))))

  :hints
  (("Goal"
    :use
    ((:instance
      channel-state-of-run-spec-replay-inputs-for-one-proc-is-row-only
      (src src)
      (dst (g :pid input))
      (nbrs nbrs)
      (m (cm-after-cut-append
          m
          (g :pid input)
          (g :sender input)
          input))
      (spec-start-st spec-start-st))

     (:instance
      channel-state-of-run-spec-replay-inputs-for-one-proc-is-row-only
      (src src)
      (dst (g :pid input))
      (nbrs nbrs)
      (m m)
      (spec-start-st spec-start-st))

     (:instance
      cm-after-cut-get-of-cm-after-cut-append-different-src
      (src src)
      (j (g :sender input))
      (dst (g :pid input))
      (m m)
      (input input))

     (:instance
      after-cut-row-well-formed-p-of-cm-after-cut-append
      (dst (g :pid input))
      (nbrs nbrs)
      (m m)
      (j (g :sender input))
      (input input)))

    :in-theory
    (disable
     replay-inputs-for-one-proc
     run-spec
     spec-step
     spec-step-rcv
     cm-after-cut-append
     cm-after-cut-get
     channel-state-of-run-spec-replay-inputs-for-one-proc-is-row-only
     cm-after-cut-get-of-cm-after-cut-append-different-src
     after-cut-row-well-formed-p-of-cm-after-cut-append))))

(defthm cm-after-cut-get-of-cm-after-cut-append-same-src
  (equal
   (cm-after-cut-get
    (cm-after-cut-append m dst src input)
    dst
    src)
   (append
    (cm-after-cut-get m dst src)
    (list input))))


(defthm g-channel-of-run-spec-append-singleton-same-when-prefix-channel-same
  (implies
   (and
    (equal
     (g src
        (g dst
           (g :channels
              (run-spec st prefix1))))
     (g src
        (g dst
           (g :channels
              (run-spec st prefix2)))))

    (equal (g :ttype input) :receive))

   (equal
    (g src
       (g dst
          (g :channels
             (run-spec st
                       (append prefix1 (list input))))))
    (g src
       (g dst
          (g :channels
             (run-spec st
                       (append prefix2 (list input)))))))))


(defthm g-channel-of-run-spec-replay-inputs-for-one-proc-of-cm-after-cut-append-same-src
  (implies
   (and
    (equal (g :ttype input) :receive)

    (memberp (g :sender input) nbrs)
    (uniquep nbrs)

    (after-cut-row-well-formed-p
     (g :pid input)
     nbrs
     (g (g :pid input)
        (g :inputs-after-cut m))))

   (equal
    (g
     (g :sender input)
     (g
      (g :pid input)
      (g
       :channels
       (run-spec
        spec-start-st
        (replay-inputs-for-one-proc
         (g :pid input)
         nbrs
         (cm-after-cut-append
          m
          (g :pid input)
          (g :sender input)
          input))))))

    (g
     (g :sender input)
     (g
      (g :pid input)
      (g
       :channels
       (run-spec
        spec-start-st
        (append
         (replay-inputs-for-one-proc
          (g :pid input)
          nbrs
          m)
         (list input))))))))

  :hints
  (("Goal"
    :use
    ((:instance
      channel-state-of-run-spec-replay-inputs-for-one-proc-is-row-only
      (src (g :sender input))
      (dst (g :pid input))
      (nbrs nbrs)
      (m (cm-after-cut-append
          m
          (g :pid input)
          (g :sender input)
          input))
      (spec-start-st spec-start-st))

     (:instance
      after-cut-row-well-formed-p-of-cm-after-cut-append
      (dst (g :pid input))
      (nbrs nbrs)
      (m m)
      (j (g :sender input))
      (input input))

     (:instance
      channel-state-of-run-spec-replay-inputs-for-one-proc-is-row-only
      (src (g :sender input))
      (dst (g :pid input))
      (nbrs nbrs)
      (m m)
      (spec-start-st spec-start-st))

     (:instance
      cm-after-cut-get-of-cm-after-cut-append-same-src
      (m m)
      (dst (g :pid input))
      (src (g :sender input))
      (input input))

     (:instance
      g-channel-of-run-spec-append-singleton-same-when-prefix-channel-same
      (src (g :sender input))
      (dst (g :pid input))
      (st spec-start-st)
      (prefix1
       (replay-inputs-for-one-proc
        (g :pid input)
        nbrs
        m))
      (prefix2
       (cm-after-cut-get
        m
        (g :pid input)
        (g :sender input)))
      (input input)))

    :in-theory
    (disable
     replay-inputs-for-one-proc
     run-spec
     spec-step
     spec-step-rcv
     cm-after-cut-append
     cm-after-cut-get
     channel-state-of-run-spec-replay-inputs-for-one-proc-is-row-only
     after-cut-row-well-formed-p-of-cm-after-cut-append
     cm-after-cut-get-of-cm-after-cut-append-same-src
     g-channel-of-run-spec-append-singleton-same-when-prefix-channel-same))))





(defthm channel-state-of-run-spec-replay-inputs-for-one-proc-of-cm-after-cut-append
  (implies
   (and
    (equal (g :ttype input) :receive)
    (equal (g :pid input) i)
    (equal (g :sender input) j)
    (memberp j nbrs)
    (memberp src nbrs)
    (uniquep nbrs)
    (after-cut-for-proc-well-formed-p i nbrs m))

   (equal
    ;; Channel SRC -> I after grouped replay with updated cut-meta.
    (channel-state
     src
     i
     (g :channels
        (run-spec
         spec-start-st
         (replay-inputs-for-one-proc
          i
          nbrs
          (cm-after-cut-append m i j input)))))

    ;; Channel SRC -> I after old replay followed by INPUT.
    (channel-state
     src
     i
     (g :channels
        (run-spec
         spec-start-st
         (append
          (replay-inputs-for-one-proc i nbrs m)
          (list input)))))))

  :hints
  (("Goal"
    :cases ((equal src j))
    :in-theory

    (disable
     run-spec
     RUN-SPEC-OF-APPEND-SINGLETON
     channel-state-of-run-spec-replay-inputs-for-one-proc-is-row-only
     cm-after-cut-append
      spec-step
      spec-step-rcv))))



(defun incoming-channels-equal-p (srcs dst channels1 channels2)
  (if (endp srcs)
      t
    (and
     (equal
      (channel-state (car srcs) dst channels1)
      (channel-state (car srcs) dst channels2))
     (incoming-channels-equal-p
      (cdr srcs)
      dst
      channels1
      channels2))))



(defthm incoming-channels-equivalent-for-proc-p-right-replace-when-incoming-channels-equal-p
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels old-spec-channels)

    (incoming-channels-equal-p
     srcs dst new-spec-channels old-spec-channels))

   (incoming-channels-equivalent-for-proc-p
    srcs dst imp-channels new-spec-channels)))


(defthm incoming-channels-equivalent-for-proc-p-left-replace-when-incoming-channels-equal-p
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst old-imp-channels spec-channels)

    (incoming-channels-equal-p
     srcs dst new-imp-channels old-imp-channels))

   (incoming-channels-equivalent-for-proc-p
    srcs dst new-imp-channels spec-channels)))



(defthm channels-of-spec-step-receive-normal
  (implies
   (and
    (equal (g :ttype input) :receive)
    (equal (g :pid input) i)
    (equal (g :sender input) j)

    (equal
     (g :msg-type
        (get-msg-from-channel j i (g :channels spec-st)))
     :normal))

   (equal
    (g :channels
       (spec-step spec-st input))
    (remove-message-from-channel
     j i
     (g :channels spec-st)))))

(defthm channels-of-run-spec-append-singleton-receive-normal
  (implies
   (and
    (equal (g :ttype input) :receive)
    (equal (g :pid input) i)
    (equal (g :sender input) j)

    (equal
     (g :msg-type
        (get-msg-from-channel
         j i
         (g :channels
            (run-spec spec-start-st old-inputs))))
     :normal))

   (equal
    (g :channels
       (run-spec
        spec-start-st
        (append old-inputs (list input))))
    (remove-message-from-channel
     j i
     (g :channels
        (run-spec spec-start-st old-inputs))))))






(defun replay-cm-after-cut-one-src-inv-p
    (src i j nbrs m input)
  (and
   ;; INPUT is receive j -> i.
   (equal (g :ttype input) :receive)
   (equal (g :pid input) i)
   (equal (g :sender input) j)

   ;; j is the source whose after-cut list is updated.
   (memberp j nbrs)

   ;; This particular SRC is one of the replayed incoming sources.
   (memberp src nbrs)

   ;; Replay row invariants.
   (uniquep nbrs)
   (after-cut-for-proc-well-formed-p i nbrs m)))


(defun replay-cm-after-cut-all-srcs-inv-p
    (srcs i j nbrs m input)
  (if (endp srcs)
      t
    (and
     (replay-cm-after-cut-one-src-inv-p
      (car srcs) i j nbrs m input)
     (replay-cm-after-cut-all-srcs-inv-p
      (cdr srcs) i j nbrs m input))))


(defthm replay-cm-after-cut-one-src-inv-implies-channel-state-equal
  (implies
   (replay-cm-after-cut-one-src-inv-p
    src i j nbrs m input)

   (equal
    ;; Channel SRC -> I after grouped replay with updated cut-meta.
    (channel-state
     src
     i
     (g :channels
        (run-spec
         spec-start-st
         (replay-inputs-for-one-proc
          i
          nbrs
          (cm-after-cut-append m i j input)))))

    ;; Channel SRC -> I after old replay followed by INPUT.
    (channel-state
     src
     i
     (g :channels
        (run-spec
         spec-start-st
         (append
          (replay-inputs-for-one-proc i nbrs m)
          (list input)))))))
  :hints
  (("Goal"
    :in-theory (disable run-spec
			replay-inputs-for-one-proc
			cm-after-cut-append))))





(defthm replay-cm-after-cut-all-srcs-inv-implies-incoming-channels-equal-p
  (implies
   (replay-cm-after-cut-all-srcs-inv-p
    srcs i j nbrs m input)

   (incoming-channels-equal-p
    srcs
    i
    (g :channels
       (run-spec
        spec-start-st
        (replay-inputs-for-one-proc
         i
         nbrs
         (cm-after-cut-append m i j input))))
    (g :channels
       (run-spec
        spec-start-st
        (append
         (replay-inputs-for-one-proc i nbrs m)
         (list input))))))

  :hints
  (("Goal"
    :induct
    (replay-cm-after-cut-all-srcs-inv-p
     srcs i j nbrs m input)

    :in-theory
    (disable
     replay-cm-after-cut-one-src-inv-p
     append
     replay-inputs-for-one-proc
     run-spec
     cm-after-cut-append
     RUN-SPEC-OF-APPEND-SINGLETON
     ))))








(defthm incoming-channels-equal-p-of-equal-right
  (implies
   (and
    (incoming-channels-equal-p srcs dst channels1 old-channels2)
    (equal new-channels2 old-channels2))

   (incoming-channels-equal-p
    srcs dst channels1 new-channels2)))





(defthm incoming-channels-equal-p-of-cm-after-cut-append-and-remove-message
  (implies
   (and
    ;; The all-source replay invariant gives equality between:
    ;;   updated replay
    ;; and
    ;;   old replay ++ INPUT.
    (replay-cm-after-cut-all-srcs-inv-p
     srcs i j nbrs m input)

    ;; The old replay has a normal message at j -> i,
    ;; so running INPUT consumes/removes that message.
    (equal
     (g :msg-type
        (get-msg-from-channel
         j i
         (g :channels
            (run-spec
             spec-start-st
             (replay-inputs-for-one-proc i nbrs m)))))
     :normal))

   (incoming-channels-equal-p
    srcs
    i

    ;; Updated replay channels.
    (g :channels
       (run-spec
        spec-start-st
        (replay-inputs-for-one-proc
         i
         nbrs
         (cm-after-cut-append m i j input))))

    ;; Old replay channels after consuming/removing j -> i.
    (remove-message-from-channel
     j i
     (g :channels
        (run-spec
         spec-start-st
         (replay-inputs-for-one-proc i nbrs m))))))

  :hints
  (("Goal"
    :use
    ((:instance
      replay-cm-after-cut-all-srcs-inv-implies-incoming-channels-equal-p
      (srcs srcs)
      (i i)
      (j j)
      (nbrs nbrs)
      (m m)
      (input input)
      (spec-start-st spec-start-st))

     (:instance
      channels-of-run-spec-append-singleton-receive-normal
      (spec-start-st spec-start-st)
      (old-inputs (replay-inputs-for-one-proc i nbrs m))
      (input input)
      (i i)
      (j j))

     (:instance
      incoming-channels-equal-p-of-equal-right
      (srcs srcs)
      (dst i)
      (channels1
       (g :channels
          (run-spec
           spec-start-st
           (replay-inputs-for-one-proc
            i
            nbrs
            (cm-after-cut-append m i j input)))))
      (old-channels2
       (g :channels
          (run-spec
           spec-start-st
           (append
            (replay-inputs-for-one-proc i nbrs m)
            (list input)))))
      (new-channels2
       (remove-message-from-channel
        j i
        (g :channels
           (run-spec
            spec-start-st
            (replay-inputs-for-one-proc i nbrs m)))))))

    :in-theory
    (disable
     replay-cm-after-cut-all-srcs-inv-implies-incoming-channels-equal-p
     channels-of-run-spec-append-singleton-receive-normal
     incoming-channels-equal-p-of-equal-right
     replay-inputs-for-one-proc
     run-spec
     run-spec-of-append-singleton
     RUN-SPEC-OF-APPEND-SINGLETON
     cm-after-cut-append
     remove-message-from-channel
     spec-step
     spec-step-rcv))))







(defthm replay-cm-after-cut-all-srcs-inv-p-from-subset
  (implies
   (and
    ;; INPUT is receive j -> i.
    (equal (g :ttype input) :receive)
    (equal (g :pid input) i)
    (equal (g :sender input) j)

    ;; Every source in SRCS is one of the replayed neighbors.
    (subset srcs nbrs)

    ;; j is also one of the replayed neighbors.
    (memberp j nbrs)

    ;; Replay row invariants.
    (uniquep nbrs)
    (after-cut-for-proc-well-formed-p i nbrs m))

   (replay-cm-after-cut-all-srcs-inv-p
    srcs i j nbrs m input)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main bridge:
;;
;; Old incoming equivalence + implementation normal head
;; implies old replay/spec head is also normal.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm spec-channel-head-normal-when-imp-channel-head-normal-and-equivalent
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)

    (equal
     (g :msg-type (car imp-msgs))
     :normal))

   (equal
    (g :msg-type (car spec-msgs))
    :normal)))

(defthm consp-spec-channel-when-imp-head-normal-and-channel-equivalent
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)

    (consp imp-msgs)

    (equal
     (g :msg-type (car imp-msgs))
     :normal))

   (consp spec-msgs)))

(defthm spec-head-normal-when-imp-head-normal-and-channel-equivalent
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)

    (consp imp-msgs)

    (equal
     (g :msg-type (car imp-msgs))
     :normal))

   (equal
    (g :msg-type (car spec-msgs))
    :normal)))

(defthm spec-head-normal-when-incoming-equivalent-and-imp-head-normal
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     open-srcs i imp-channels spec-channels)

    (memberp j open-srcs)

    (consp
     (g j (g i imp-channels)))

    (equal
     (g :msg-type
        (car (g j (g i imp-channels))))
     :normal))

   (equal
    (g :msg-type
       (car (g j (g i spec-channels))))
    :normal)))


(defthm consp-spec-channel-when-incoming-equivalent-and-imp-head-normal
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     open-srcs i imp-channels spec-channels)

    (memberp j open-srcs)

    (consp
     (g j (g i imp-channels)))

    (equal
     (g :msg-type
        (car (g j (g i imp-channels))))
     :normal))

   (consp
    (g j (g i spec-channels)))))

(defthm spec-replay-head-normal-when-incoming-equivalent-and-imp-head-normal
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     open-srcs
     i
     (g :channels st)
     (g :channels
        (run-spec
         spec-start-st
         (replay-inputs-for-one-proc i nbrs m))))

    (memberp j open-srcs)

    (equal
     (g :msg-type
        (get-msg-from-channel j i (g :channels st)))
     :normal))

   (equal
    (g :msg-type
       (get-msg-from-channel
        j i
        (g :channels
           (run-spec
            spec-start-st
            (replay-inputs-for-one-proc i nbrs m)))))
    :normal))

  :hints
  (("Goal"

    :in-theory
    (e/d
     (get-msg-from-channel)

     (incoming-channels-equivalent-for-proc-p
      imp-spec-channel-msgs-equivalent-p
      run-spec
      replay-inputs-for-one-proc)))))






(defthm imp-spec-channel-msgs-equivalent-p-of-cdr-when-imp-head-normal
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
    (consp imp-msgs)
    (equal (g :msg-type (car imp-msgs)) :normal))
   (imp-spec-channel-msgs-equivalent-p
    (cdr imp-msgs)
    (cdr spec-msgs))))


(defthm imp-spec-channel-msgs-equivalent-p-when-incoming-channels-equivalent-for-proc-p
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)
    (memberp src srcs))

   (imp-spec-channel-msgs-equivalent-p
    (g src (g dst imp-channels))
    (g src (g dst spec-channels)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic uniqueness/member helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm uniquep-of-cdr
  (implies
   (uniquep xs)
   (uniquep (cdr xs)))
  :hints
  (("Goal"
    :in-theory (enable uniquep))))


(defthm not-memberp-car-cdr-when-uniquep
  (implies
   (and
    (consp xs)
    (uniquep xs))
   (not (memberp (car xs) (cdr xs))))
  :hints
  (("Goal"
    :in-theory (enable uniquep memberp))))


(defthm memberp-cdr-when-memberp-and-not-equal-car
  (implies
   (and
    (memberp x xs)
    (not (equal x (car xs))))
   (memberp x (cdr xs)))
  :hints
  (("Goal"
    :in-theory (enable memberp))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; If J is not in SRCS, changing channel J -> DST does not affect
;; incoming-channel equivalence for SRCS.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm incoming-channels-equivalent-for-proc-p-of-update-non-member-src
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)

    (not (memberp j srcs)))

   (incoming-channels-equivalent-for-proc-p
    srcs
    dst

    (s dst
       (s j new-imp-msgs
          (g dst imp-channels))
       imp-channels)

    (s dst
       (s j new-spec-msgs
          (g dst spec-channels))
       spec-channels)))

  :hints
  (("Goal"
    :induct
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)

    :in-theory
    (enable
     incoming-channels-equivalent-for-proc-p
     memberp))))


(defthm incoming-channels-equivalent-for-proc-p-of-update-one-src-unique
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)

    (uniquep srcs)
    (memberp j srcs)

    (imp-spec-channel-msgs-equivalent-p
     new-imp-msgs
     new-spec-msgs))

   (incoming-channels-equivalent-for-proc-p
    srcs
    dst

    (s dst
       (s j new-imp-msgs
          (g dst imp-channels))
       imp-channels)

    (s dst
       (s j new-spec-msgs
          (g dst spec-channels))
       spec-channels))))


(defthm not-imp-spec-channel-msgs-equivalent-p-with-nil-spec-when-imp-head-normal
  (implies
   (and
    (consp imp-msgs)
    (equal
     (g :msg-type (car imp-msgs))
     :normal))

   (equal
    (imp-spec-channel-msgs-equivalent-p imp-msgs nil)
    nil)))

(defthm incoming-channels-equivalent-for-proc-p-of-remove-message-from-channel-both-normal
  (implies
   (and
    ;; Old incoming-channel equivalence.
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)

    ;; We remove channel j -> dst.
    (memberp j srcs)
    (uniquep srcs)
    ;; The implementation side has a normal head message.
    ;; (consp
    ;;  (g j (g dst imp-channels)))

   (equal
     (g :msg-type
        (get-msg-from-channel j dst imp-channels))
     :normal))

   ;; Remove the head from both implementation and spec channels.
   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (remove-message-from-channel j dst imp-channels)
    (remove-message-from-channel j dst spec-channels)))
  :hints
  (("Goal"
    :in-theory (disable imp-spec-channel-msgs-equivalent-p)
    :cases ((equal j (car srcs))))))


 (defthm memberp-when-memberp-and-subset
  (implies
   (and
    (memberp x xs)
    (subset xs ys))
   (memberp x ys)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Support:
;; If J is in OPEN-SRCS and OPEN-SRCS is a subset of NBRS, then J is in NBRS.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm memberp-when-memberp-and-subset
  (implies
   (and
    (memberp x xs)
    (subset xs ys))
   (memberp x ys))
  :hints
  (("Goal"
    :in-theory (enable subset memberp))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main theorem for Subgoal 3''
;;
;; Recovering case, normal message received from an open channel.
;;
;; The channel proof does not actually use :RECOVERING or
;; WAITING-RECOVERY-FROM.  They are kept here so the theorem matches the
;; parent subgoal exactly.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm incoming-channels-equivalent-for-proc-p-of-remove-normal-recovering-open-channel
  (implies
   (and
    ;; Old incoming equivalence:
    ;; implementation channels match old replay-spec channels.
    (incoming-channels-equivalent-for-proc-p
     open-srcs
     (g :pid input)
     (g :channels st)
     (g :channels
        (run-spec
         spec-start-st
         (replay-inputs-for-one-proc
          (g :pid input)
          nbrs
          m))))

    ;; The consumed source is open.
    (memberp (g :sender input) open-srcs)

    ;; INPUT is a receive from sender -> pid.
    (equal (g :ttype input) :receive)

    ;; Replay/open-source assumptions.
    (subset open-srcs nbrs)
    (uniquep nbrs)
    (uniquep open-srcs)

    (after-cut-row-well-formed-p
     (g :pid input)
     nbrs
     (g (g :pid input)
        (g :inputs-after-cut m)))

    ;; Implementation channel head is a normal message.
    (consp
     (g (g :sender input)
        (g (g :pid input)
           (g :channels st))))

    (equal
     (g :msg-type
        (car
         (g (g :sender input)
            (g (g :pid input)
               (g :channels st)))))
     :normal))

   ;; Goal:
   ;; after implementation removes the normal message, it is equivalent
   ;; to spec replay with CM-AFTER-CUT-APPEND.
   (incoming-channels-equivalent-for-proc-p
    open-srcs
    (g :pid input)

    (remove-message-from-channel
     (g :sender input)
     (g :pid input)
     (g :channels st))

    (g :channels
       (run-spec
        spec-start-st
        (replay-inputs-for-one-proc
         (g :pid input)
         nbrs
         (cm-after-cut-append
          m
          (g :pid input)
          (g :sender input)
          input))))))

  :hints
  (("Goal"
    :use
    (;; Derive sender is in NBRS from sender in OPEN-SRCS and subset.
     (:instance
      memberp-when-memberp-and-subset
      (x (g :sender input))
      (xs open-srcs)
      (ys nbrs))

     ;; Build the all-source replay invariant needed by the replay/remove
     ;; equality theorem.
     (:instance
      replay-cm-after-cut-all-srcs-inv-p-from-subset
      (srcs open-srcs)
      (i (g :pid input))
      (j (g :sender input))
      (nbrs nbrs)
      (m m)
      (input input))

     ;; Old imp/spec incoming equivalence plus normal imp head gives
     ;; normal spec/replay head.
     (:instance
      spec-replay-head-normal-when-incoming-equivalent-and-imp-head-normal
      (open-srcs open-srcs)
      (i (g :pid input))
      (j (g :sender input))
      (st st)
      (spec-start-st spec-start-st)
      (nbrs nbrs)
      (m m))

     ;; Remove the normal message from both old imp/spec channel maps.
     (:instance
      incoming-channels-equivalent-for-proc-p-of-remove-message-from-channel-both-normal
      (srcs open-srcs)
      (dst (g :pid input))
      (j (g :sender input))
      (imp-channels (g :channels st))
      (spec-channels
       (g :channels
          (run-spec
           spec-start-st
           (replay-inputs-for-one-proc
            (g :pid input)
            nbrs
            m)))))

     ;; Updated CM-AFTER-CUT replay equals old replay after removing
     ;; sender -> pid.
     (:instance
      incoming-channels-equal-p-of-cm-after-cut-append-and-remove-message
      (srcs open-srcs)
      (i (g :pid input))
      (j (g :sender input))
      (nbrs nbrs)
      (m m)
      (input input)
      (spec-start-st spec-start-st))

     ;; Replace old removed spec channels by updated CM-AFTER-CUT replay.
     (:instance
      incoming-channels-equivalent-for-proc-p-right-replace-when-incoming-channels-equal-p
      (srcs open-srcs)
      (dst (g :pid input))

      (imp-channels
       (remove-message-from-channel
        (g :sender input)
        (g :pid input)
        (g :channels st)))

      (old-spec-channels
       (remove-message-from-channel
        (g :sender input)
        (g :pid input)
        (g :channels
           (run-spec
            spec-start-st
            (replay-inputs-for-one-proc
             (g :pid input)
             nbrs
             m)))))

      (new-spec-channels
       (g :channels
          (run-spec
           spec-start-st
           (replay-inputs-for-one-proc
            (g :pid input)
            nbrs
            (cm-after-cut-append
             m
             (g :pid input)
             (g :sender input)
             input)))))))

    :in-theory
    (e/d
     ;; Enable these only to normalize the hypotheses into the forms
     ;; expected by your proved lemmas.
     (get-msg-from-channel
      after-cut-for-proc-well-formed-p)

     ;; Keep the big functions closed.
     (incoming-channels-equivalent-for-proc-p
      incoming-channels-equal-p
      replay-inputs-for-one-proc
      run-spec
      run-spec-of-append-singleton
      RUN-SPEC-OF-APPEND-SINGLETON
      cm-after-cut-append
      remove-message-from-channel
      spec-step
      spec-step-rcv

      memberp-when-memberp-and-subset
      replay-cm-after-cut-all-srcs-inv-p-from-subset
      spec-replay-head-normal-when-incoming-equivalent-and-imp-head-normal
      incoming-channels-equivalent-for-proc-p-of-remove-message-from-channel-both-normal
      incoming-channels-equal-p-of-cm-after-cut-append-and-remove-message
      incoming-channels-equivalent-for-proc-p-right-replace-when-incoming-channels-equal-p)))))




(defthm incoming-channels-equivalent-for-proc-p-of-step-rcv-normal-same-open-channel
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     open-srcs
     i
     (g :channels st)
     (g :channels
        (run-spec
         spec-start-st
         (replay-inputs-for-one-proc i nbrs m))))

    (memberp j open-srcs)

    (equal (g :ttype input) :receive)
    (equal (g :pid input) i)
    (equal (g :sender input) j)
    (memberp j nbrs)
    (subset open-srcs nbrs)
    (uniquep nbrs)
    (uniquep open-srcs)
    (after-cut-for-proc-well-formed-p i nbrs m)

    (equal
     (g :msg-type
        (get-msg-from-channel j i (g :channels st)))
     :normal))

   (incoming-channels-equivalent-for-proc-p
    open-srcs
    i
    (g :channels (step-rcv st i j))
    (g :channels
       (run-spec
        spec-start-st
        (replay-inputs-for-one-proc
         i
         nbrs
         (cm-after-cut-append m i j input))))))

 :hints
  ( ("Goal"
    :in-theory
    (disable
     incoming-channels-equivalent-for-proc-p
      cm-after-cut-append
       remove-message-from-channel
      run-spec
     ; replay-inputs-for-one-proc
      cut-scan-no-recovery-step-p))))


(defun waiting-marker-from-rows-uniquep-p (ids m)
  (if (endp ids)
      t
    (and
     (uniquep
      (g (car ids)
         (g :waiting-marker-from m)))
     (waiting-marker-from-rows-uniquep-p
      (cdr ids)
      m))))


(defthm uniquep-of-waiting-marker-row-when-waiting-marker-from-rows-uniquep-p
  (implies
   (and
    (waiting-marker-from-rows-uniquep-p ids m)
    (memberp i ids))
   (uniquep
    (g i
       (g :waiting-marker-from m)))))


(defun nbrs-from-rows-uniquep-p (ids procs)
  (if (endp ids)
      t
    (and
     (uniquep
      (g :nbrs-from
         (g (car ids) procs)))
     (nbrs-from-rows-uniquep-p
      (cdr ids)
      procs))))


(defthm uniquep-of-nbrs-from-row-when-nbrs-from-rows-uniquep-p
  (implies
   (and
    (nbrs-from-rows-uniquep-p ids procs)
    (memberp i ids))
   (uniquep
    (g :nbrs-from
       (g i procs)))))


(defun waiting-marker-from-subset-of-nbrs-from-p (ids m procs)
  (if (endp ids)
      t
    (and
     (subset
      (g (car ids)
         (g :waiting-marker-from m))
      (g :nbrs-from
         (g (car ids) procs)))
     (waiting-marker-from-subset-of-nbrs-from-p
      (cdr ids)
      m
      procs))))

(defthm subset-of-waiting-marker-from-row-when-waiting-marker-from-subset-of-nbrs-from-p
  (implies
   (and
    (waiting-marker-from-subset-of-nbrs-from-p ids m procs)
    (memberp i ids))
   (subset
    (g i
       (g :waiting-marker-from m))
    (g :nbrs-from
       (g i procs)))))


(defun after-cut-for-all-procs-well-formed-p (ids procs m)
  (if (endp ids)
      t
    (and
     (after-cut-for-proc-well-formed-p
      (car ids)
      (g :nbrs-from
         (g (car ids) procs))
      m)
     (after-cut-for-all-procs-well-formed-p
      (cdr ids)
      procs
      m))))


(defthm memberp-pid-in-proc-ids-m-when-same-proc-ids
  (implies
   (and
    (equal (g :proc-ids m)
           (g :proc-ids st))
    (memberp i (g :proc-ids st)))
   (memberp i (g :proc-ids m))))


(defthm after-cut-for-proc-well-formed-p-when-after-cut-for-all-procs-well-formed-p
  (implies
   (and
    (after-cut-for-all-procs-well-formed-p ids procs m)
    (memberp i ids))
   (after-cut-for-proc-well-formed-p
    i
    (g :nbrs-from
       (g i procs))
    m)))

(defthm legal-inputp-receive-implies-pid-in-proc-ids
  (implies
   (and
    (legal-inputp st input)
    (equal (g :ttype input) :receive))
   (memberp (g :pid input)
            (g :proc-ids st))))



(defthm incoming-channels-equivalent-for-proc-p-of-step-rcv-normal-not-open-channel
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     open-srcs
     i
     (g :channels st)
     spec-channels)

    ;; The implementation receives a normal message on j -> k.
    (equal
     (g :msg-type
        (get-msg-from-channel j k (g :channels st)))
     :normal)

    ;; The changed channel j -> k is irrelevant to the row being compared.
    ;; Either it is for a different destination, or j is not one of i's
    ;; open incoming sources.

   (not (memberp j open-srcs)))

   (incoming-channels-equivalent-for-proc-p
    open-srcs
    i
    (g :channels (step-rcv st k j))
    spec-channels)))


(defthm incoming-channels-equivalent-for-proc-p-of-step-rcv-normal-different-dst
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     open-srcs
     i
     (g :channels st)
     spec-channels)

    (equal
     (g :msg-type
        (get-msg-from-channel j k (g :channels st)))
     :normal)

    (not (equal k i)))

   (incoming-channels-equivalent-for-proc-p
    open-srcs
    i
    (g :channels (step-rcv st k j))
    spec-channels)))


(defthm cut-scan-open-incoming-channels-equivalent-after-cut-receive-step
  (implies
   (and
    ;; Only channels still waiting for marker must match.
    (incoming-channels-equivalent-for-proc-p
     (g i (g :waiting-marker-from m))
     i
     (g :channels st-cur)
     (g
      :channels
      (run-spec
       spec-start-st
       (replay-inputs-for-one-proc
        i
        (g :nbrs-from (g i (g :procs st-cur)))
        m))))

    ;; i has already taken the cut.
    (not (memberp i (g :cut-not-taken m)))
    ;; i is still recording at least one incoming channel.
    (consp (g i (g :waiting-marker-from m)))

    (waiting-marker-from-rows-uniquep-p
     (g :proc-ids st-cur)
     m)

    (nbrs-from-rows-uniquep-p
     (g :proc-ids st-cur)
     (g :procs st-cur))

    (waiting-marker-from-subset-of-nbrs-from-p
     (g :proc-ids st-cur)
     m
     (g :procs st-cur))

    (after-cut-for-all-procs-well-formed-p
     (g :proc-ids st-cur)
     (g :procs st-cur)
     m)
    ;; Receive step.
    (equal (g :ttype input) :receive)
    (legal-inputp st-cur input)
    (cut-scan-no-recovery-step-p input st-cur))

   ;; After the receive, only the updated still-open channels must match.
   (incoming-channels-equivalent-for-proc-p
    (g i
       (g :waiting-marker-from
          (process-cut-receive input st-cur m)))
    i
    (g :channels (system-step st-cur input))
    (g
     :channels
     (run-spec
      spec-start-st
      (replay-inputs-for-one-proc
       i
       (g :nbrs-from (g i (g :procs st-cur)))
       (process-cut-receive input st-cur m))))))

  :hints
  (("Subgoal 1"
    :cases ((equal (g :pid input) i)))
   ("Subgoal 2'"
    :cases ((equal (g :pid input) i)))
   ("Goal"
    :in-theory
    (e/d
     (process-cut-receive
      process-cut-normal-receive
      process-cut-marker-receive
      current-msg-for-receive
      system-step)

     (incoming-channels-equivalent-for-proc-p
      cm-after-cut-append
      step-rcv
      run-spec
      replay-inputs-for-one-proc
      legal-inputp
      get-msg-from-channel
      cut-scan-no-recovery-step-p)))))






(defun cut-scan-replay-open-incoming-channels-equivalent-for-proc-p
    (i m st-cur spec-start-st)
  (incoming-channels-equivalent-for-proc-p
   ;; Only channels still waiting for marker are tracked.
   (cm-waiting-marker-for m i)

   i

   ;; Current implementation channels.
   (g :channels st-cur)

   ;; Spec after replaying all after-cut inputs collected so far.
   (g :channels
      (run-spec
       spec-start-st
       (replay-inputs-for-one-proc
        i
        (g :nbrs-from (g i (g :procs st-cur)))
        m)))))


(defun cut-scan-after-cut-segment-inputp (input)
  (or (equal (g :ttype input) :normal)
      (equal (g :ttype input) :receive)
      (equal (g :ttype input) :start-checkpoint)))
 

(defthm cut-scan-replay-open-incoming-channels-equivalent-after-cut-step
  (implies
   (and
    ;; Only open incoming channels into i match before this step.
    (cut-scan-replay-open-incoming-channels-equivalent-for-proc-p
     i m st-cur spec-start-st)

    ;; i has already taken its cut.
    (not (memberp i (cm-cut-not-taken m)))

    ;; i is still recording at least one incoming channel.
    ;; Needed by cut-scan-open-incoming-channels-equivalent-after-cut-receive-step.
    (consp
     (g i
        (g :waiting-marker-from m)))

    ;; Each waiting-marker row has no duplicate sources.
    (waiting-marker-from-rows-uniquep-p
     (g :proc-ids st-cur)
     m)

    ;; Each neighbor row has no duplicate sources.
    (nbrs-from-rows-uniquep-p
     (g :proc-ids st-cur)
     (g :procs st-cur))

    ;; Waiting-marker rows are subsets of the corresponding nbrs-from rows.
    (waiting-marker-from-subset-of-nbrs-from-p
     (g :proc-ids st-cur)
     m
     (g :procs st-cur))

    ;; The after-cut input rows are well-formed for every process.
    (after-cut-for-all-procs-well-formed-p
     (g :proc-ids st-cur)
     (g :procs st-cur)
     m)

    ;; Current implementation input is legal.
    (legal-inputp st-cur input)

    (equal (g :ttype input) :receive)

    ;; No recovery behavior during this cut-scan step.
    (cut-scan-no-recovery-step-p input st-cur)

    ;; Name the next implementation state.
    (equal st-next
           (system-step st-cur input))

    ;; Name the next cut metadata.
    (equal m-next
           (process-cut-step input st-cur m)))

   ;; Only the updated open incoming channels into i must match.
   (cut-scan-replay-open-incoming-channels-equivalent-for-proc-p
    i m-next st-next spec-start-st))

  :hints
  (("Goal''"
    :by
    (:instance cut-scan-open-incoming-channels-equivalent-after-cut-receive-step
               (i i)
               (m m)
               (st-cur st-cur)
               (spec-start-st spec-start-st)
              (input input)))
   ("Goal"
    :in-theory
    (e/d
     (cut-scan-replay-open-incoming-channels-equivalent-for-proc-p
      process-cut-step)

     (system-step
      spec-step
      step-rcv
      spec-step-rcv
      step-normal
      spec-step-normal
      step-crash
      step-recover

      process-cut-receive
      process-cut-normal
      process-cut-normal-receive
      process-cut-marker-receive
      current-msg-for-receive

      handle-normal-msg
      handle-normal-msg-core
      handle-marker-msg
      handle-recovery-msg

      cut-scan-open-incoming-channels-equivalent-after-cut-receive-step

      incoming-channels-equivalent-for-proc-p
      imp-spec-channel-msgs-equivalent-p
      run-spec
      run-imp
      legal-inputp
      cut-scan-no-recovery-step-p)))))



(defthm cut-scan-replay-open-incoming-channels-equivalent-after-cut-step
  (implies
   (and
    ;; Only open incoming channels into i match before this step.
    (cut-scan-replay-open-incoming-channels-equivalent-for-proc-p
     i m st-cur spec-start-st)

    ;; i has already taken its cut.
    (not (memberp i (cm-cut-not-taken m)))

    ;; Current implementation input is legal.
    (legal-inputp st-cur input)

    ;; No recovery behavior during this cut-scan step.
    (cut-scan-no-recovery-step-p input st-cur)

    ;; Name the next implementation state.
    (equal st-next
           (system-step st-cur input))

    ;; Name the next cut metadata.
    (equal m-next
           (process-cut-step input st-cur m)))

   ;; Only the updated open incoming channels into i must match.
   (cut-scan-replay-open-incoming-channels-equivalent-for-proc-p
    i m-next st-next spec-start-st))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (cut-scan-replay-open-incoming-channels-equivalent-for-proc-p)

     (system-step
      spec-step
      step-rcv
      spec-step-rcv
      step-normal
      spec-step-normal
      step-crash
      step-recover

      process-cut-receive
      process-cut-normal
      process-cut-normal-receive
      process-cut-marker-receive
      current-msg-for-receive

      handle-normal-msg
      handle-normal-msg-core
      handle-marker-msg
      handle-recovery-msg

      incoming-channels-equivalent-for-proc-p
      imp-spec-channel-msgs-equivalent-p
      run-spec
      run-imp
      legal-inputp
      cut-scan-no-recovery-step-p)))))

;; (defun cut-scan-procs-equivalent-p (m st-cur spec-start-st)
;;   (procs-equivalent-p
;;    (proc-ids st-cur)
;;    (procs st-cur)
;;    (procs
;;     (run-spec spec-start-st
;;               (cm-inputs-before-cut m)))))


;; (defun cut-scan-incoming-channels-equivalent-for-proc-p
;;     (i m st-cur spec-start-st)
;;   (incoming-channels-equivalent-for-proc-p
;;    (nbrs-from (g i (procs st-cur)))
;;    i
;;    (channels st-cur)
;;    (channels
;;     (run-spec spec-start-st
;;               (cm-inputs-before-cut m)))))


;; (defthm cut-scan-procs-equivalent-before-cut-step
;;   (implies
;;    (and
;;     ;; Process equivalence before this step.
;;     (cut-scan-procs-equivalent-p
;;      m st-cur spec-start-st)

;;     ;; Needed for receive steps:
;;     ;; implementation/spec channel heads must match.
;;     (cut-scan-incoming-channels-equivalent-for-proc-p
;;      (pid input) m st-cur spec-start-st)

;;     ;; The process of the current input remains before cut.
;;     (cut-scan-proc-stays-cut-not-taken-step-p
;;      (pid input) input st-cur m)

;;     ;; Current input is legal.
;;     (legal-inputp st-cur input)

;;     ;; No recovery behavior in this step.
;;     (cut-scan-no-recovery-step-p input st-cur)

;;     ;; Next implementation state.
;;     (equal st-next
;;            (system-step st-cur input))

;;     ;; Next cut metadata.
;;     (equal m-next
;;            (process-cut-step input st-cur m)))

;;    ;; Process equivalence after this step.
;;    (cut-scan-procs-equivalent-p
;;     m-next st-next spec-start-st))

;;   :hints
;; (("Goal"
;;   :in-theory
;;   (e/d
;;    (
;;     ;; Enable only the wrapper predicates you want ACL2 to unfold.
;;     cut-scan-procs-equivalent-p
;;     cut-scan-incoming-channels-equivalent-for-proc-p
;;     )

;;    (
;;     ;; Do not expand big transition functions.
;;     system-step
;;     spec-step
;;     step-rcv
;;     spec-step-rcv
;;     step-normal
;;     spec-step-normal
;;     step-checkpoint
;;     step-crash
;;     step-recover

;;     ;; Do not expand cut-scan bookkeeping unless you specifically need it.
;;     ;process-cut-step
;;     process-cut-receive
;;     process-cut-normal
;;     process-cut-normal-receive
;;     process-cut-marker-receive
;;     current-msg-for-receive

;;     ;; Do not expand low-level handlers.
;;     handle-normal-msg
;;     handle-normal-msg-core
;;     handle-marker-msg
;;     handle-recovery-msg

;;     ;; Do not expand recursive equivalence predicates.
;;     procs-equivalent-p
;;     proc-equivalent-p
;;     incoming-channels-equivalent-for-proc-p
;;     imp-spec-channel-msgs-equivalent-p

;;     ;; Do not expand large invariant/legal predicates.
;;     good-state-p
;;     good-spec-state-p
;;     good-procs-p
;;     good-channels-p
;;     legal-inputp
;;     cut-scan-no-recovery-step-p
;;     cut-scan-proc-stays-cut-not-taken-step-p

;;     ;; Usually keep run functions disabled and use run-spec append lemmas.
;;     run-spec
;;     run-imp)))))

;; (defthm cut-scan-incoming-channels-equivalent-before-cut-step
;;   (implies
;;    (and
;;     ;; Process equivalence is needed for normal sends,
;;     ;; because generated messages depend on local state.
;;     (cut-scan-procs-equivalent-p
;;      m st-cur spec-start-st)

;;     ;; Incoming channels into i match before this step.
;;     (cut-scan-incoming-channels-equivalent-for-proc-p
;;      i m st-cur spec-start-st)

;;     ;; Process i remains before cut through this step.
;;     (cut-scan-proc-stays-cut-not-taken-step-p
;;      i input st-cur m)

;;     ;; Current input is legal.
;;     (legal-inputp st-cur input)

;;     ;; No recovery behavior in this step.
;;     (cut-scan-no-recovery-step-p input st-cur)

;;     ;; Next implementation state.
;;     (equal st-next
;;            (system-step st-cur input))

;;     ;; Next cut metadata.
;;     (equal m-next
;;            (process-cut-step input st-cur m)))

;;    ;; Incoming channels into i still match after this step.
;;    (cut-scan-incoming-channels-equivalent-for-proc-p
;;     i m-next st-next spec-start-st))
;;   :hints
;; (("Goal"
;;   :in-theory
;;   (e/d
;;    (
;;     ;; Enable only the wrapper predicates you want ACL2 to unfold.
;;     cut-scan-procs-equivalent-p
;;     cut-scan-incoming-channels-equivalent-for-proc-p
;;     )

;;    (
;;     ;; Do not expand big transition functions.
;;     system-step
;;     spec-step
;;     step-rcv
;;     spec-step-rcv
;;     step-normal
;;     spec-step-normal
;;     step-checkpoint
;;     step-crash
;;     step-recover

;;     ;; Do not expand cut-scan bookkeeping unless you specifically need it.
;;     process-cut-step
;;     process-cut-receive
;;     process-cut-normal
;;     process-cut-normal-receive
;;     process-cut-marker-receive
;;     current-msg-for-receive

;;     ;; Do not expand low-level handlers.
;;     handle-normal-msg
;;     handle-normal-msg-core
;;     handle-marker-msg
;;     handle-recovery-msg

;;     ;; Do not expand recursive equivalence predicates.
;;     procs-equivalent-p
;;     proc-equivalent-p
;;     incoming-channels-equivalent-for-proc-p
;;     imp-spec-channel-msgs-equivalent-p

;;     ;; Do not expand large invariant/legal predicates.
;;     good-state-p
;;     good-spec-state-p
;;     good-procs-p
;;     good-channels-p
;;     legal-inputp
;;     cut-scan-no-recovery-step-p
;;     cut-scan-proc-stays-cut-not-taken-step-p

;;     ;; Usually keep run functions disabled and use run-spec append lemmas.
;;     run-spec
;;     run-imp)))))


;; ;; (defthm cut-scan-incoming-channels-equivalent-for-proc-before-cut-step
;; ;;   (implies
;; ;;    (and
;; ;;     ;; before step, incoming channels into i match
;; ;;     (cut-scan-incoming-channels-equivalent-for-proc-p
;; ;;      i m st-cur spec-start-st)

;; ;;     ;; process i remains before cut through this step
;; ;;     (cut-scan-proc-stays-cut-not-taken-step-p
;; ;;      i input st-cur m)

;; ;;     ;; legal implementation input
;; ;;     (legal-inputp st-cur input)

;; ;;     ;; no recovery step
;; ;;     (cut-scan-no-recovery-step-p input st-cur)

;; ;;     ;; next states
;; ;;     (equal st-next
;; ;;            (system-step st-cur input))
;; ;;     (equal m-next
;; ;;            (process-cut-step input st-cur m)))

;; ;;    ;; after step, incoming channels into i still match
;; ;;    (cut-scan-incoming-channels-equivalent-for-proc-p
;; ;;     i m-next st-next spec-start-st)))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;; Useful consequence:
;; ;; If i stays in CUT-NOT-TAKEN throughout the segment, then i is still in
;; ;; CUT-NOT-TAKEN in the final cut metadata.
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; (defthm memberp-cut-not-taken-of-process-cut-segment
;; ;;   (implies
;; ;;    (cut-scan-proc-stays-cut-not-taken-p i inputs st m)
;; ;;    (memberp i
;; ;;             (cm-cut-not-taken
;; ;;              (process-cut-segment inputs st m))))
;; ;;   :hints
;;   (("Goal"
;;     :induct (process-cut-segment inputs st m)
;;     :in-theory
;;     (enable
;;      process-cut-segment
;;      cut-scan-proc-stays-cut-not-taken-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Explicit local-state equality form
;;
;; This is often easier to use later than the implication-style predicate.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm cut-scan-local-state-match-at-end-of-segment
;;   (implies
;;    (and
;;     (cut-scan-spec-imp-local-match-before-first-marker-p
;;      i m st spec-start-st)

;;     (legal-input-sequencep st inputs)

;;     (cut-scan-proc-stays-cut-not-taken-p
;;      i inputs st m)

;;     (cut-scan-no-recovery-segment-p inputs st)

;;     (cut-scan-channel-msg-match-segment-p
;;      inputs st m spec-start-st))

;;    (equal
;;     (local-state
;;      (g i
;;         (procs
;;          (run-spec
;;           spec-start-st
;;           (cm-inputs-before-cut
;;            (process-cut-segment inputs st m))))))
;;     (local-state
;;      (g i
;;         (procs
;;          (run-imp st inputs))))))

;;   :hints
;;   (("Goal"
;;     :use
;;     ((:instance
;;       cut-scan-spec-imp-local-match-before-first-marker-segment)
;;      (:instance
;;       memberp-cut-not-taken-of-process-cut-segment))
;;     :in-theory
;;     (enable cut-scan-spec-imp-local-match-before-first-marker-p))))

;end target: cut-scan-local-match-over-input-segment


;; (defun cut-not-taken-transition-index-for-proc-aux
;;     (inputs trace idx i m)
;;   ;; Return the first index IDX where process I changes from
;;   ;; cut-not-taken to not cut-not-taken.
;;   ;; Return NIL if no such transition is found.
;;   (if (or (endp inputs)
;;           (cut-done-p m))
;;       nil
;;     (let* ((input      (first inputs))
;;            (st         (nth idx trace))
;;            (before-p   (cm-cut-not-taken-p m i))
;;            (m-next     (process-cut-step input st m))
;;            (after-p    (cm-cut-not-taken-p m-next i)))
;;       (if (and before-p
;;                (not after-p))
;;           idx
;;         (cut-not-taken-transition-index-for-proc-aux
;;          (rest inputs)
;;          trace
;;          (+ 1 idx)
;;          i
;;          m-next)))))


;; (defun cut-not-taken-transition-index-for-proc
;;     (inputs trace cp-start sid initiator i)
;;   ;; Return the index where I leaves cut-not-taken.
;;   ;; Return NIL if I is not found or no transition is found.
;;   (let* ((st0 (nth cp-start trace))
;;          (m0  (make-cut-meta sid initiator st0)))
;;     (if (not (memberp i (cm-proc-ids m0)))
;;         nil
;;       (if (not (cm-cut-not-taken-p m0 i))
;;           cp-start
;;         (cut-not-taken-transition-index-for-proc-aux
;;          (nthcdr cp-start inputs)
;;          trace
;;          cp-start
;;          i
;;          m0)))))


;; (defun segment-cut-not-taken-transition-index-for-proc
;;     (st input-seg i)
;;   (let* ((trace     (run-imp-trace st input-seg))
;;          (cp-start  0)
;;          (initiator (pid (first input-seg)))
;;          (sid       (list initiator
;;                           (counter
;;                            (g initiator
;;                               (procs st))))))
;;     (cut-not-taken-transition-index-for-proc
;;      input-seg
;;      trace
;;      cp-start
;;      sid
;;      initiator
;;      i)))




;; ;start target: local-state-match-at-cut-transition-index

;; (defun cut-meta-before-index-aux (inputs trace idx stop m)
;;   ;; Scan cut metadata up to, but not including, absolute index STOP.
;;   ;; So the returned meta is the cut meta just before INPUTS[STOP].
;;   (if (or (endp inputs)
;;           (>= idx stop)
;;           (cut-done-p m))
;;       m
;;     (let* ((input (first inputs))
;;            (st    (nth idx trace))
;;            (m     (process-cut-step input st m)))
;;       (cut-meta-before-index-aux
;;        (rest inputs)
;;        trace
;;        (+ 1 idx)
;;        stop
;;        m))))


;; (defun cut-meta-before-index
;;     (inputs trace cp-start sid initiator stop)
;;   (let* ((st0 (nth cp-start trace))
;;          (m0  (make-cut-meta sid initiator st0)))
;;     (cut-meta-before-index-aux
;;      (nthcdr cp-start inputs)
;;      trace
;;      cp-start
;;      stop
;;      m0)))


;; (defun segment-cut-meta-before-transition-for-proc
;;     (st input-seg i)
;;   (let* ((trace     (run-imp-trace st input-seg))
;;          (cp-start  0)
;;          (initiator (pid (first input-seg)))
;;          (sid       (list initiator
;;                           (counter
;;                            (g initiator
;;                               (procs st)))))
;;          (idx       (segment-cut-not-taken-transition-index-for-proc
;;                      st input-seg i)))
;;     (if idx
;;         (cut-meta-before-index
;;          input-seg
;;          trace
;;          cp-start
;;          sid
;;          initiator
;;          idx)
;;       nil)))


;; (defthm local-state-match-at-cut-transition-index-for-proc
;;   (implies
;;    (and
;;     (good-state-p st)
;;     (cp-start-rc-done-segment-p st input-seg)
;;     (memberp i (proc-ids st))

;;     ;; The transition index exists.
;;     (segment-cut-not-taken-transition-index-for-proc
;;      st input-seg i))

;;    (let* ((trace (run-imp-trace st input-seg))
;;           (idx   (segment-cut-not-taken-transition-index-for-proc
;;                   st input-seg i))
;;           (m     (segment-cut-meta-before-transition-for-proc
;;                   st input-seg i)))

;;      ;; Running the spec on the inputs accumulated before i takes its cut
;;      ;; gives the same local-state for i as the implementation pre-state
;;      ;; at i's cut-transition index.
;;      (equal
;;       (local-state
;;        (g i
;;           (procs
;;            (run-spec
;;             (rep st)
;;             (cm-inputs-before-cut m)))))
;;       (local-state
;;        (g i
;;           (procs
;;            (nth idx trace)))))))

;;   :hints
;;   (("Goal"
;;     :in-theory
;;     (disable
;;      run-spec
;;      run-imp-trace
;;      system-step
;;      spec-step
;;      process-cut-step
;;      process-cut-receive
;;      process-cut-marker-receive
;;      process-cut-normal-receive
;;      process-cut-normal
;;      step-checkpoint
;;      step-recover
;;      start-checkpoint-helper
;;      start-recovery-helper
;;      handle-marker-msg
;;      handle-first-marker-msg
;;      handle-non-first-marker-msg
;;      update-proc-for-first-marker-msg
;;      update-proc-for-non-first-marker-msg
;;      handle-recovery-msg
;;      handle-first-recovery-msg
;;      handle-non-first-recovery-msg
;;      update-proc-for-first-recovery-msg
;;      update-proc-for-non-first-recovery-msg))))

;; ;end target: local-state-match-at-cut-transition-index
