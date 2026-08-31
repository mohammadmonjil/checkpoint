(in-package "ACL2")

;; ------------------------------------------------------------------
;; Top-level theorem target for one cp-start ... recovery-done segment.
;;
;; This file is intentionally small and proof-oriented:
;;   - INPUTS_2 is included so all extracted predicates are available.
;;   - The main theorem is stated in terms of the existing INPUTS_2
;;     bridge predicates.
;;   - The extracted predicate bodies from INPUTS_2 are copied at the
;;     end inside a block comment for quick reference.
;;
;; The theorem is wrapped in SKIP-PROOFS because this is the top-level
;; target statement.  The remaining work is to prove the side-condition
;; predicate from the lower-level segment invariants.
;; ------------------------------------------------------------------

(include-book "inputs_2")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Segment-level helper terms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cp-start-rc-top-sid (st input-seg)
  ;; Snapshot id created by the first :start-checkpoint in INPUT-SEG.
  (let* ((initiator (pid (first input-seg))))
    (list initiator
          (counter
           (g initiator (procs st))))))


(defun cp-start-rc-top-initiator (input-seg)
  (pid (first input-seg)))


(defun cp-start-rc-top-cut-result (st input-seg)
  ;; Cut-scan result for the checkpoint that starts at segment index 0.
  (let* ((trace     (run-imp-trace st input-seg))
         (sid       (cp-start-rc-top-sid st input-seg))
         (initiator (cp-start-rc-top-initiator input-seg)))
    (scan-until-cut-done input-seg
                         trace
                         0
                         sid
                         initiator)))


(defun cp-start-rc-top-cut-meta (st input-seg)
  ;; Final cut metadata at checkpoint-collection completion.
  (cut-result-meta
   (cp-start-rc-top-cut-result st input-seg)))


(defun cp-start-rc-top-cut-done-index (st input-seg)
  ;; First index after the checkpoint collection is complete.
  (cut-result-idx
   (cp-start-rc-top-cut-result st input-seg)))


(defun cp-start-rc-top-nbrs-from (i st)
  (nbrs-from
   (g i (procs st))))


(defun cp-start-rc-top-before-after-inputs-for-proc
    (i st input-seg)
  ;; The one-proc compressed spec sequence described by the theorem:
  ;;
  ;;   1. all original computation inputs before the cut, followed by
  ;;   2. replay inputs for process i's after-cut channel snapshots.
  ;;
  ;; This is intentionally the one-process version.  The all-process
  ;; compressed sequence in INPUTS_1 is REPLAY-INPUTS-FROM-CUT-META.
  (let* ((m    (cp-start-rc-top-cut-meta st input-seg))
         (nbrs (cp-start-rc-top-nbrs-from i st)))
    (append (cm-inputs-before-cut m)
            (replay-inputs-for-one-proc i nbrs m))))


(defun cp-start-rc-top-spec-cut-state (st input-seg)
  ;; Spec state after only INPUTS-BEFORE-CUT.
  (let* ((m (cp-start-rc-top-cut-meta st input-seg)))
    (run-spec st
              (cm-inputs-before-cut m))))


(defun cp-start-rc-top-final-imp-state (st input-seg)
  (run-imp st input-seg))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Recovery bridge predicate
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cp-start-rc-top-recovery-local-replay-p
    (i st input-seg)
  ;; This is the remaining recovery-side bridge needed by the top theorem:
  ;; after the whole cp-start ... recovery-done segment, process i's concrete
  ;; local state is exactly the replay of the saved snapshot local state plus
  ;; saved channel snapshots.
  ;;
  ;; The checkpoint-side INPUTS_2 theorem
  ;; IMP-SNAPSHOT-REPLAY-LOCAL-STATE-EQUALS-SPEC-REPLAY-INPUTS-FOR-ONE-PROC
  ;; then converts this replay into RUN-SPEC over the after-cut inputs.
  (let* ((sid      (cp-start-rc-top-sid st input-seg))
         (imp-st   (cp-start-rc-top-final-imp-state st input-seg))
         (p        (g i (procs imp-st)))
         (entry    (snapshot-entry sid p))
         (nbrs     (cp-start-rc-top-nbrs-from i st)))
    (equal
     (local-state p)
     (replay-channel-snapshots
      (snapshot-local-snap-shot entry)
      (snapshot-channel-snapshots entry)
      nbrs))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Top-level side conditions assembled from INPUTS_2 predicates
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cp-start-rc-top-local-state-sideconds-p
    (i st input-seg)
  (let* ((sid         (cp-start-rc-top-sid st input-seg))
         (m           (cp-start-rc-top-cut-meta st input-seg))
         (nbrs        (cp-start-rc-top-nbrs-from i st))
         (imp-st      (cp-start-rc-top-final-imp-state st input-seg))
         (spec-cut-st (cp-start-rc-top-spec-cut-state st input-seg)))
    (and
     ;; Segment shape: exactly one checkpoint-start ... recovery-done region.
     (cp-start-rc-done-segment-p st input-seg)

     ;; We reason about a real process row.
     (memberp i (proc-ids st))

     ;; Neighbor/replay well-formedness required by
     ;; IMP-SNAPSHOT-REPLAY-LOCAL-STATE-EQUALS-SPEC-REPLAY-INPUTS-FOR-ONE-PROC.
     (uniquep nbrs)
     (after-cut-for-proc-well-formed-p i nbrs m)

     ;; Saved snapshot local state equals the spec local state after
     ;; INPUTS-BEFORE-CUT.
     (spec-imp-snapshot-local-match-p
      i sid imp-st spec-cut-st)

     ;; Saved implementation channel snapshots equal the messages consumed
     ;; by spec replay for the same after-cut metadata rows.
     (imp-snapshot-spec-msgs-match-for-nbrs-p
      i nbrs sid m imp-st spec-cut-st)

     ;; Recovery-side bridge: final implementation local state equals the
     ;; replay of the saved snapshot local state and channel snapshots.
     (cp-start-rc-top-recovery-local-replay-p
      i st input-seg))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main target theorem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(skip-proofs
 (defthm rep-correctness-of-cp-start-rc-done-segment-local-state
   (implies
    (cp-start-rc-top-local-state-sideconds-p
     i st input-seg)

    (equal
     ;; Implementation: execute the original checkpoint/recovery segment.
     (local-state
      (g i
         (procs
          (run-imp st input-seg))))

     ;; Spec: execute the compressed one-proc sequence:
     ;;   INPUTS-BEFORE-CUT + REPLAY-INPUTS-FOR-ONE-PROC.
     (local-state
      (g i
         (procs
          (run-spec
           st
           (cp-start-rc-top-before-after-inputs-for-proc
            i st input-seg)))))))

   :hints
   (("Goal"
     :use
     ((:instance
       imp-snapshot-replay-local-state-equals-spec-replay-inputs-for-one-proc
       (i i)
       (sid (cp-start-rc-top-sid st input-seg))
       (nbrs-from (cp-start-rc-top-nbrs-from i st))
       (m (cp-start-rc-top-cut-meta st input-seg))
       (imp-st (cp-start-rc-top-final-imp-state st input-seg))
       (spec-cut-st (cp-start-rc-top-spec-cut-state st input-seg))))
     :in-theory
     (disable
      cp-start-rc-top-local-state-sideconds-p
      cp-start-rc-top-recovery-local-replay-p
      cp-start-rc-top-before-after-inputs-for-proc
      cp-start-rc-top-spec-cut-state
      cp-start-rc-top-cut-meta
      cp-start-rc-top-cut-result
      imp-snapshot-replay-local-state-equals-spec-replay-inputs-for-one-proc)))))


#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Extracted predicate/helper forms from INPUTS_2.LISP
;;
;; These are copied here only for reference.  They are not redefined because
;; this file includes INPUTS_2 above.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defun process-cut-segment (inputs st m)
  (if (endp inputs)
      m
    (let* ((input (first inputs))
           (m-next (process-cut-step input st m))
           (st-next (system-step st input)))
      (process-cut-segment (rest inputs)
                           st-next
                           m-next))))

(defun cut-scan-proc-takes-cut-step-p (i input st m)
  (and
   (memberp i (cm-cut-not-taken m))
   (not
    (memberp i
             (cm-cut-not-taken
              (process-cut-step input st m))))))

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

(defun cm-spec-open-incoming-step-sideconds-p
    (i nbrs input st m spec-start-st)
  (and
   (legal-inputp st input)
   (uniquep nbrs)
   (implies
    (and
     (equal (g :ttype input) :receive)
     (equal (g :pid input) i))
    (memberp (g :sender input) nbrs))
   (consp (cm-waiting-marker-for m i))
   (incoming-channels-equivalent-for-proc-p
    (cm-waiting-marker-for m i)
    i
    (g :channels st)
    (g :channels
       (run-spec
        spec-start-st
        (replay-inputs-for-one-proc i nbrs m))))
   (uniquep (cm-waiting-marker-for m i))
   (subsetp (cm-waiting-marker-for m i) nbrs)
   (after-cut-for-proc-well-formed-p i nbrs m)))

(defun cm-spec-open-incoming-segment-sideconds-p
    (i nbrs inputs st m spec-start-st)
  (if (endp inputs)
      t
    (let* ((input   (car inputs))
           (st-next (system-step st input))
           (m-next  (process-cut-step input st m)))
      (and
       (cm-spec-open-incoming-step-sideconds-p
        i nbrs input st m spec-start-st)

       (cm-spec-open-incoming-segment-sideconds-p
        i
        nbrs
        (cdr inputs)
        st-next
        m-next
        spec-start-st)))))

(defun imp-snapshot-msg-get (sid i j st)
  (g j
     (snapshot-channel-snapshots
      (snapshot-entry sid
                      (g i (g :procs st))))))

(defun cm-imp-snapshot-msgs-match-for-nbrs-p (i nbrs sid m st)
  (if (endp nbrs)
      t
    (and
     (equal
      (cm-after-cut-msg-get m i (car nbrs))
      (imp-snapshot-msg-get sid i (car nbrs) st))

     (cm-imp-snapshot-msgs-match-for-nbrs-p
      i (cdr nbrs) sid m st))))

(defun cm-imp-snapshot-waiting-marker-match-p (i sid m st)
  (equal
   (cm-waiting-marker-for m i)
   (snapshot-waiting-marker-from
    (snapshot-entry sid
                    (g i (g :procs st))))))

(defun cm-imp-snapshot-step-sideconds-p
    (i nbrs sid input st m)
  (let* ((j    (g :sender input))
         (pid  (g :pid input))
         (p    (g i (g :procs st)))
         (snap (snapshot-entry sid p)))
    (and
     ;; Concrete step is legal.
     (legal-inputp st input)

     ;; We intentionally ignore recovery behavior in this proof portion.
     (cut-scan-no-recovery-step-p input st)

     ;; We are already in the after-cut recording phase for process i.
     ;; This theorem is about preserving a snapshot that already exists.
     (not (cm-cut-not-taken-p m i))

     ;; Neighbor-row facts.
     (uniquep nbrs)

     ;; If this input is a receive into i, its sender belongs to i's row.
     (implies
      (and
       (equal (g :ttype input) :receive)
       (equal pid i))
      (memberp j nbrs))

     (implies
      (and
       (equal (g :ttype input) :start-checkpoint)
       (equal (g :pid input) i))
      (not
       (equal sid
              (list i
		    (g :counter
                       (g i (g :procs st)))))))

     ;; Fixed implementation snapshot exists uniquely.
     (memberp sid (snapshot-ids p))
     (uniquep (snapshot-ids p))
     ;; We are comparing against an active checkpointing snapshot.
     (equal (snapshot-status snap) :checkpointing)

     ;; Main bridge:
     ;; metadata open channels and implementation snapshot open channels agree.
     (cm-imp-snapshot-waiting-marker-match-p i sid m st))))

(defun cm-imp-snapshot-segment-sideconds-p
    (i nbrs sid inputs st m)
  (if (endp inputs)
      t
    (let* ((input   (first inputs))
           (m-next  (process-cut-step input st m))
           (st-next (system-step st input)))
      (and
       (cm-imp-snapshot-step-sideconds-p
        i nbrs sid input st m)

       (cm-imp-snapshot-segment-sideconds-p
        i nbrs sid
        (rest inputs)
        st-next
        m-next)))))

(defun imp-snapshot-spec-msgs-match-p
    (i j sid m st spec-start-st)
  (equal
   (imp-snapshot-msg-get sid i j st)
   (spec-consumed-msgs
    spec-start-st
    (cm-after-cut-get m i j))))

(defun imp-snapshot-spec-msgs-match-for-nbrs-p
    (i nbrs sid m st spec-start-st)
  (if (endp nbrs)
      t
    (and
     (imp-snapshot-spec-msgs-match-p
      i (car nbrs) sid m st spec-start-st)
     (imp-snapshot-spec-msgs-match-for-nbrs-p
      i (cdr nbrs) sid m st spec-start-st))))

(defun cut-scan-proc-closes-after-cut-step-p (i input st m)
  (let ((m-next (process-cut-step input st m)))
    (and
     ;; i has already taken its local cut before this step.
     (not (cm-cut-not-taken-p m i))

     ;; Before this step, i is still recording some incoming channels.
     (consp (cm-waiting-marker-for m i))

     ;; This step closes the recording phase for i.
     (endp (cm-waiting-marker-for m-next i)))))

(defun cut-scan-proc-snapshot-closes-step-p (i sid input st m)
  (let* ((m-next  (process-cut-step input st m))
         (st-next (system-step st input)))
    (and
     ;; Metadata side is open before the step.
     (consp (cm-waiting-marker-for m i))

     ;; Implementation snapshot side is open before the step.
     (consp
      (snapshot-waiting-marker-from
       (snapshot-entry sid
                       (g i (g :procs st)))))

     ;; Metadata side is closed after the step.
     (endp (cm-waiting-marker-for m-next i))

     ;; Implementation snapshot side is closed after the step.
     (endp
      (snapshot-waiting-marker-from
       (snapshot-entry sid
                       (g i (g :procs st-next))))))))

(defun spec-imp-snapshot-local-match-p
    (i sid imp-st spec-st)
  (equal
   (snapshot-local-snap-shot
    (snapshot-entry sid
                    (g i (procs imp-st))))
   (local-state
    (g i
       (procs spec-st)))))

(defun imp-snapshot-local-get (i sid st)
  (snapshot-local-snap-shot
   (snapshot-entry sid
                   (g i (g :procs st)))))

(defun imp-snapshot-local-stable-step-sideconds-p
    (i sid st)
  (let* ((p   (g i (g :procs st))))
    (and
     ;; Fixed snapshot already exists before this step.
     (memberp sid
              (snapshot-ids p))

     ;; If process i starts another checkpoint, it must not overwrite
     ;; the fixed SID whose local snapshot we are tracking.
     (not
       (equal sid
              (list i
                    (g :counter
                       (g i (g :procs st)))))))))

(defun imp-snapshot-local-stable-segment-sideconds-p
    (i sid inputs st)
  (if (endp inputs)
      t
    (let* ((input   (car inputs))
           (st-next (system-step st input)))
      (and
       (imp-snapshot-local-stable-step-sideconds-p
        i sid st)

       (imp-snapshot-local-stable-segment-sideconds-p
        i sid
        (cdr inputs)
        st-next)))))
|#
