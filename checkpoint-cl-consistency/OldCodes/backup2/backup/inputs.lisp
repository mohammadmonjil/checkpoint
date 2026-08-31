
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

(defun cut-scan-spec-imp-local-match-before-first-marker-p
    (i  m imp-st spec-start-st)
  (implies
   (memberp i (cm-cut-not-taken m))
   (equal
    (local-state
     (g i
        (procs
         (run-spec spec-start-st
                   (cm-inputs-before-cut m)))))
    (local-state
     (g i
        (procs imp-st))))))


(defun cut-scan-channel-msg-match-p
    (j i m imp-st spec-start-st)
  ;; If receiver i has not taken its cut, then the next message
  ;; seen on channel j -> i agrees between the spec state and
  ;; the implementation state.
  (let ((spec-st (run-spec spec-start-st
                           (cm-inputs-before-cut m))))
    (implies
     (memberp i (cm-cut-not-taken m))
     (equal
      (get-msg-from-channel j i (channels spec-st))
      (get-msg-from-channel j i (channels imp-st))))))





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
    (cut-scan-spec-imp-local-match-before-first-marker-p
     i m st-cur spec-start-st)
    (legal-inputp st-cur input)
    (not (any-process-recovering-p st-cur))
    ;; For receive steps, the spec state and implementation state must
    ;; agree on the message that will be consumed.
    (cut-scan-channel-msg-match-p
     (sender input)
     (pid input)
     m
     st-cur
     spec-start-st)
    ;; st-next is the implementation state after INPUT.
    (equal st-next
           (system-step st-cur input))
    ;; m-next is the cut metadata after processing INPUT.
    (equal m-next
           (process-cut-step input st-cur m))
    ;; We only prove the invariant while process i has still not
    ;; taken its cut after this step.
    (memberp i (cm-cut-not-taken m-next))
    (not (equal (ttype input) :recover))
    ;; Recovery-message receives are also outside this invariant.
    ;; process-cut-step ignores them, but system-step executes recovery behavior.
    (implies
     (equal (ttype input) :receive)
     (not
      (equal
       (msg-type
        (get-msg-from-channel
         (sender input)
         (pid input)
         (channels st-cur)))
       :recovery))))

   ;; Local-state invariant after this cut-scan step.
   (cut-scan-spec-imp-local-match-before-first-marker-p
    i m-next st-next spec-start-st))

  :hints
  (("Goal"
    :cases ((equal i (pid input)))
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
;; Main segment lemma
;;
;; If local-state matches at the beginning of the segment, and process i
;; stays in CUT-NOT-TAKEN throughout the segment, then local-state still
;; matches at the end of the segment.
;;
;; This is exactly the segment-level induction wrapper around the proved
;; one-step lemma:
;;
;;   CUT-SCAN-SPEC-IMP-LOCAL-MATCH-BEFORE-FIRST-MARKER-STEP
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm cut-scan-spec-imp-local-match-before-first-marker-segment
  (implies
   (and
    ;; Initial local-state match.
    (cut-scan-spec-imp-local-match-before-first-marker-p
     i m st spec-start-st)

    ;; Input segment is legal in the implementation.
    (legal-input-sequencep st inputs)

    ;; Process i never takes its cut in this segment.
    (cut-scan-proc-stays-cut-not-taken-p
     i inputs st m)

    ;; Recovery behavior is outside this before-first-marker segment.
    (cut-scan-no-recovery-segment-p inputs st)

    ;; Channel-head agreement for receive steps.
    ;; Later this should come from channel equivalence.
    (cut-scan-channel-msg-match-segment-p
     inputs st m spec-start-st))

   ;; Final local-state match after the whole segment.
   (cut-scan-spec-imp-local-match-before-first-marker-p
    i
    (process-cut-segment inputs st m)
    (run-imp st inputs)
    spec-start-st))

  :hints
  (("Goal"
    :induct (process-cut-segment inputs st m)
    :in-theory
    (disable
     ;process-cut-segment
     ;cut-scan-proc-stays-cut-not-taken-p
     cut-scan-no-recovery-step-p
     cut-scan-no-recovery-segment-p
     cut-scan-channel-msg-match-segment-p
     legal-input-sequencep
     run-imp))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Useful consequence:
;; If i stays in CUT-NOT-TAKEN throughout the segment, then i is still in
;; CUT-NOT-TAKEN in the final cut metadata.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm memberp-cut-not-taken-of-process-cut-segment
;;   (implies
;;    (cut-scan-proc-stays-cut-not-taken-p i inputs st m)
;;    (memberp i
;;             (cm-cut-not-taken
;;              (process-cut-segment inputs st m))))
;;   :hints
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
