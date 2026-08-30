
(in-package "ACL2")
(include-book "model")
(include-book "good_state_invariants")	
(include-book "channel_equivalence")
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


(defun current-msg-for-receive (input st)
  (let* ((i        (pid input))
         (j        (sender input))
         (channels (channels st)))
    (get-msg-from-channel j i channels)))

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


(defun spec-compatible-input-sequence (st inputs)
  ;; Convert each implementation input using the implementation
  ;; state immediately before that input executes.
  (declare
   (xargs :measure (acl2-count inputs)))

  (if (endp inputs)
      nil

    (let* ((input   (first inputs))
           (st-next (system-step st input)))

      (cons
       (spec-compatible-input input st)

       (spec-compatible-input-sequence
        st-next
        (rest inputs))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unified cut scan
;;
;; This is a drop-in replacement for the existing cut-metadata/scan block.
;; Existing names are preserved.  The only new global metadata field is:
;;
;;   :after-cut-input-sequence
;;
;; It contains every ordinary input whose process had already taken its cut,
;; in the original global execution order.
;;
;; The older :inputs-after-cut field is preserved unchanged.  It remains the
;; channel-wise table of receives recorded while an incoming channel is open.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ------------------------------------------------------------------
;; Existing metadata accessors
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

;; Existing channel-wise table:
;;   process i -> incoming neighbor j -> receive-input list.
(defun cm-inputs-after-cut (m)
  (g :inputs-after-cut m))

;; Existing channel-wise table of the actual normal messages consumed by
;; the receive inputs in :inputs-after-cut.
(defun cm-after-cut-msgs (m)
  (g :after-cut-msgs m))

;; ------------------------------------------------------------------
;; New accessor: global post-cut ordinary-input sequence
;; ------------------------------------------------------------------

(defun cm-after-cut-input-sequence (m)
  (g :after-cut-input-sequence m))

;; Optional alias with the words in the opposite order.
(defun cm-inputs-after-cut-sequence (m)
  (cm-after-cut-input-sequence m))

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
     (append
      (cm-inputs-before-cut m)
      (list input))
     m))

(defun cm-add-after-cut-input-sequence (m input)
  (s :after-cut-input-sequence
     (append
      (cm-after-cut-input-sequence m)
      (list input))
     m))

(defun cm-before-cut-input-sequence (m)
  `(g :before-cut-input-sequence ,m))


(defun cm-add-before-cut-input-sequence (m input)
  (s :before-cut-input-sequence
     (append
      (cm-before-cut-input-sequence m)
      (list input))
     m))

;; ------------------------------------------------------------------
;; Existing channel-wise after-cut input operations
;; ------------------------------------------------------------------

(defun cm-after-cut-get (m i j)
  (let ((rec-i (g i (cm-inputs-after-cut m))))
    (g j rec-i)))

(defun cm-after-cut-append (m i j input)
  (let* ((all   (cm-inputs-after-cut m))
         (rec-i (g i all))
         (old   (g j rec-i))
         (rec-i
          (s j
             (append old (list input))
             rec-i))
         (all   (s i rec-i all)))
    (s :inputs-after-cut all m)))

;; ------------------------------------------------------------------
;; Existing channel-wise after-cut message operations
;; ------------------------------------------------------------------

(defun cm-after-cut-msg-get (m i j)
  (let ((rec-i (g i (cm-after-cut-msgs m))))
    (g j rec-i)))

(defun cm-after-cut-msg-append (m i j msg)
  (let* ((all   (cm-after-cut-msgs m))
         (rec-i (g i all))
         (old   (g j rec-i))
         (rec-i
          (s j
             (append old (list msg))
             rec-i))
         (all   (s i rec-i all)))
    (s :after-cut-msgs all m)))

;; ------------------------------------------------------------------
;; Metadata construction
;; ------------------------------------------------------------------

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
           (p         (g i procs))
           (nbrs      (nbrs-from p))
           (entry-i   (make-inputs-after-cut-for-proc nbrs))
           (rest-recs (make-inputs-after-cut (rest proc-ids) procs)))
      (s i entry-i rest-recs))))

(defun make-after-cut-msgs-for-proc (nbrs)
  (if (endp nbrs)
      nil
    (s (first nbrs)
       nil
       (make-after-cut-msgs-for-proc (rest nbrs)))))

(defun make-after-cut-msgs (proc-ids procs)
  (if (endp proc-ids)
      nil
    (let* ((i         (first proc-ids))
           (p         (g i procs))
           (nbrs      (nbrs-from p))
           (entry-i   (make-after-cut-msgs-for-proc nbrs))
           (rest-recs (make-after-cut-msgs (rest proc-ids) procs)))
      (s i entry-i rest-recs))))

(defun make-empty-waiting-marker-from (proc-ids)
  (if (endp proc-ids)
      nil
    (s (first proc-ids)
       nil
       (make-empty-waiting-marker-from (rest proc-ids)))))

;; (defun make-cut-meta (sid initiator st)
;;   ;; Preserve the old convention: the initiator is already treated as having
;;   ;; taken its cut when this metadata is created.  Therefore the matching
;;   ;; :start-checkpoint input itself remains a protocol step and is ignored by
;;   ;; process-cut-step.
;;   (let* ((procs    (procs st))
;;          (proc-ids (proc-ids st))
;;          (p        (g initiator procs))
;;          (nbrs     (nbrs-from p))
;;          (m        nil)
;;          ;; New global post-cut sequence.
;;          (m        (s :after-cut-input-sequence nil m))
;; 	 (m        (s :before-cut-input-sequence nil m))
	 
;;          ;; Existing channel-wise data.
;;          (m        (s :after-cut-msgs
;;                       (make-after-cut-msgs proc-ids procs)
;;                       m))
;;          (m        (s :inputs-after-cut
;;                       (make-inputs-after-cut proc-ids procs)
;;                       m))
;;          (m        (s :inputs-before-cut nil m))
;;          (m        (s :waiting-marker-from
;;                       (s initiator
;;                          nbrs
;;                          (make-empty-waiting-marker-from proc-ids))
;;                       m))
;;          (m        (s :cut-not-taken
;;                       (remove1-equal initiator proc-ids)
;;                       m))
;;          (m        (s :proc-ids proc-ids m))
;;          (m        (s :sid sid m)))
;;     m))


(defun make-cut-meta (sid initiator st)
  ;; Initial cut metadata before processing the target
  ;; :start-checkpoint input.
  ;;
  ;; No process has taken its cut yet.  In particular, the initiator
  ;; remains in :cut-not-taken.  PROCESS-CUT-STEP will recognize the
  ;; matching :start-checkpoint input, remove the initiator from
  ;; :cut-not-taken, and initialize its waiting-marker-from entry.
  (declare (ignore initiator))
  (let* ((procs    (procs st))
         (proc-ids (proc-ids st))
         (m        nil)

         ;; Global input sequences.
         (m        (s :after-cut-input-sequence nil m))
         (m        (s :before-cut-input-sequence nil m))

         ;; Existing channel-wise data.
         (m        (s :after-cut-msgs
                      (make-after-cut-msgs proc-ids procs)
                      m))

         (m        (s :inputs-after-cut
                      (make-inputs-after-cut proc-ids procs)
                      m))

         (m        (s :inputs-before-cut nil m))

         ;; No process has taken its cut yet, so nobody is
         ;; waiting for checkpoint markers yet.
         (m        (s :waiting-marker-from
                      (make-empty-waiting-marker-from proc-ids)
                      m))

         ;; Initially every process has not taken its cut.
         (m        (s :cut-not-taken
                      proc-ids
                      m))

         (m        (s :proc-ids proc-ids m))
         (m        (s :sid sid m)))

    m))

;; ------------------------------------------------------------------
;; Full checkpoint-completion predicate
;; ------------------------------------------------------------------

(defun all-waiting-marker-empty-p (ids m)
  (if (endp ids)
      t
    (and (endp (cm-waiting-marker-for m (first ids)))
         (all-waiting-marker-empty-p (rest ids) m))))

(defun checkpoint-collection-complete-p (m)
  (if (equal (cm-sid m) :init)
      t
    (and (endp (cm-cut-not-taken m))
         (all-waiting-marker-empty-p
          (cm-proc-ids m)
          m))))

;; Keep the old name available.  It now denotes full checkpoint collection
;; completion, rather than only "all local cuts have occurred."
(defun cut-done-p (m)
  (checkpoint-collection-complete-p m))

;; ------------------------------------------------------------------
;; One-step processing
;; ------------------------------------------------------------------

;; (defun process-cut-normal (input m)
;;   ;; Every ordinary local step belongs to exactly one global list.
;;   (let ((i (pid input)))
;;     (if (cm-cut-not-taken-p m i)
;;         (cm-add-before-cut m input)
;;       (cm-add-after-cut-input-sequence m input))))

(defun process-cut-marker-receive (i j st m)
  (let ((procs (procs st)))
    (if (cm-cut-not-taken-p m i)
        ;; First marker for i: i takes its cut.  The channel j -> i is
        ;; closed immediately, while the other incoming channels remain open.
        (let* ((p    (g i procs))
               (nbrs (nbrs-from p))
               (ws   (remove1-equal j nbrs))
               (m    (cm-remove-cut-not-taken m i)))
          (cm-set-waiting-marker-for m i ws))
      ;; Later marker for i: close only j -> i.
      (cm-set-waiting-marker-for
       m i
       (remove1-equal j
                      (cm-waiting-marker-for m i))))))


;; (defun process-cut-normal-receive (input i j msg m)
;;   (if (cm-cut-not-taken-p m i)

;;       ;; Receive occurs before process i takes its cut.
;;       (cm-add-before-cut m input)

;;     ;; Receive occurs after process i takes its cut.
;;     (let
;;         ((old-result
;;           (if
;;               ;; The incoming channel j -> i is still open.
;;               (memberp j
;;                        (cm-waiting-marker-for m i))

;;               ;; Preserve the original metadata updates exactly.
;;               (cm-after-cut-msg-append
;;                (cm-after-cut-append
;;                 m i j input)
;;                i j msg)

;;             ;; The marker from j has already arrived, so this receive
;;             ;; is not added to the channel-wise snapshot rows.
;;             m)))

;;       ;; Add the input to the new global post-cut sequence only after
;;       ;; all original metadata updates have finished.
;;       (cm-add-after-cut-input-sequence
;;        old-result
;;        input))))


(defun process-cut-normal (input m)
  ;; Preserve only the existing local-state replay metadata here.
  (let ((i (pid input)))
    (if (cm-cut-not-taken-p m i)
        (cm-add-before-cut m input)
      m)))


(defun process-cut-normal-receive (input i j msg m)
  (if (cm-cut-not-taken-p m i)

      ;; Preserve the existing local-state replay metadata.
      (cm-add-before-cut m input)

    ;; Preserve only the channel-wise snapshot metadata here.
    (if (memberp j
                 (cm-waiting-marker-for m i))

        (cm-after-cut-msg-append
         (cm-after-cut-append
          m i j input)
         i j msg)

	m)))


(defun process-cut-receive (input st m)
  (let* ((i   (pid input))
         (j   (sender input))
         (msg (current-msg-for-receive input st))
         (sid (cm-sid m)))
    (cond
     ;; Matching checkpoint marker: update cut/open-channel metadata only.
     ((and (equal (msg-type msg) :marker)
           (equal (sid msg) sid))
      (process-cut-marker-receive i j st m))

     ;; An actual ordinary receive is classified as pre or post.
     ((equal (msg-type msg) :normal)
      (process-cut-normal-receive input i j msg m))

     ;; Recovery messages, markers for another SID, and empty receives are
     ;; protocol/nonordinary steps for this scan.
     (t m))))



(defun process-cut-checkpoint (input st m)
  (let* ((i          (pid input))
         (procs      (procs st))
         (p          (g i procs))
         (input-sid  (list i
                           (counter p)))
         (target-sid (cm-sid m)))

    (if (equal input-sid target-sid)

        ;; This is the :start-checkpoint that begins TARGET-SID.
        ;; The initiator now takes its cut.
        (let* ((m (cm-remove-cut-not-taken m i))
               (m (s :waiting-marker-from
                     (s i
                        (nbrs-from p)
                        (g :waiting-marker-from m))
                     m)))
          m)

      ;; A :start-checkpoint for some other checkpoint.
      ;; It does not affect this cut scan.
	m)))


;; (defun process-cut-step (input st m)
;;   ;; Existing name and argument order are unchanged.
;;   (cond
;;    ((equal (ttype input) :start-checkpoint)
;;     ;; make-cut-meta already accounts for the initiator's local cut.
;;     m)

;;    ((equal (ttype input) :normal)
;;     (process-cut-normal input m))

;;    ((equal (ttype input) :receive)
;;     (process-cut-receive input st m))

;;    (t m)))


(defun process-cut-step (input st m)
  (let* ((m-core
          (cond
           ((equal (ttype input) :start-checkpoint)
            (process-cut-checkpoint input st m))

           ((equal (ttype input) :normal)
            (process-cut-normal input m))

           ((equal (ttype input) :receive)
            (process-cut-receive input st m))

           (t
            m)))

         (i (pid input)))

    (if (cm-cut-not-taken-p m-core i)

        (cm-add-before-cut-input-sequence
         m-core input)

      (cm-add-after-cut-input-sequence
       m-core input))))


;; (defun process-cut-step (input st m)
;;   (let* ((spec-input
;;           (spec-compatible-input input st))

;;          (m-core
;;           (cond
;;            ((equal (ttype input) :start-checkpoint)
;;             m)

;;            ((equal (ttype input) :normal)
;;             (process-cut-normal input m))

;;            ((equal (ttype input) :receive)
;;             (process-cut-receive input st m))

;;            (t
;;             m)))

;;          (i (pid input)))

;;     (if (cm-cut-not-taken-p m-core i)

;;         (cm-add-before-cut-input-sequence
;;          m-core spec-input)

;;       (cm-add-after-cut-input-sequence
;;        m-core spec-input))))


;; (defun process-cut-step (input st m)
;;   (let*
;;       (;; Conversion uses the implementation state before INPUT.
;;        (spec-input
;;         (spec-compatible-input input st))

;;        ;; First perform all original cut and channel metadata updates.
;;        (m-core
;;         (cond
;;          ((equal (ttype input) :start-checkpoint)
;;           m)

;;          ((equal (ttype input) :normal)
;;           (process-cut-normal input m))

;;          ((equal (ttype input) :receive)
;;           (process-cut-receive input st m))

;;          (t
;;           m)))

;;        (i (pid input)))

;;     ;; Store every compatible input exactly once in one global sequence.
;;     ;; Use M-CORE so an input that causes the process to take its cut
;;     ;; is placed in the after-cut sequence.
;;     (if (cm-cut-not-taken-p m-core i)

;;         (cm-add-before-cut-input-sequence
;;          m-core
;;          spec-input)

;;       (cm-add-after-cut-input-sequence
;;        m-core
;;        spec-input))))

;; Existing recursive segment function; old lemmas can continue to use it.
(defun process-cut-segment (inputs st m)
  (declare (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      m
    (let* ((input   (first inputs))
           (m-next  (process-cut-step input st m))
           (st-next (system-step st input)))
      (process-cut-segment (rest inputs)
                           st-next
                           m-next))))

;; ------------------------------------------------------------------
;; Existing scan result names
;; ------------------------------------------------------------------

(defmacro cut-result-idx (r)
  `(g :cut-done-index ,r))

(defmacro cut-result-meta (r)
  `(g :cut-meta ,r))

;; ------------------------------------------------------------------
;; Existing scan names, now scanning through full checkpoint completion
;; ---------------------------------------------------------------
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
  (declare (xargs :measure (acl2-count inputs)))
  (if (or (endp inputs)
          (checkpoint-collection-complete-p m))
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
  ;; Existing name and argument order are unchanged.
  (let* ((st (nth cp-start trace))
         (m0 (make-cut-meta sid initiator st)))
    (scan-until-cut-done-aux (nthcdr cp-start inputs)
                             trace
                             cp-start
                             m0)))




(defmacro recovery-result-idx (r)
  `(g :recovery-done-index ,r))

(defmacro recovery-result-meta (r)
  `(g :recovery-meta ,r))


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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Collect saved snapshot messages in the same order as replay inputs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun collect-snapshot-msgs-for-one-proc (i nbrs-from-i cm-meta)
  ;; Collect saved channel-snapshot messages for process i,
  ;; in the same sender order as replay-inputs-for-one-proc.
  (if (endp nbrs-from-i)
      nil
    (append (cm-after-cut-msg-get cm-meta i (first nbrs-from-i))
            (collect-snapshot-msgs-for-one-proc
             i
             (rest nbrs-from-i)
             cm-meta))))

(defun collect-snapshot-msgs-from-cut-meta-aux (proc-ids procs cm-meta)
  ;; Collect all saved snapshot messages in replay order.
  ;; Outer order: PROC-IDS.
  ;; Inner order: nbrs-from order for each process.
  (if (endp proc-ids)
      nil
    (let* ((i           (first proc-ids))
           (p           (g i procs))
           (nbrs-from-i (nbrs-from p)))
      (append (collect-snapshot-msgs-for-one-proc
               i
               nbrs-from-i
               cm-meta)
              (collect-snapshot-msgs-from-cut-meta-aux
               (rest proc-ids)
               procs
               cm-meta)))))

(defun collect-snapshot-msgs-from-cut-meta (st cm-meta)
  (let* ((proc-ids (cm-proc-ids cm-meta))
         (procs    (procs st)))
    (collect-snapshot-msgs-from-cut-meta-aux
     proc-ids
     procs
     cm-meta)))

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


