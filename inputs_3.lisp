
(include-book "model")
(include-book "invariants")
(include-book "equivalence")
;; (include-book "inputs_1") ; optional local input examples

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Cut-scan proof support book
;;
;; Purpose:
;;   This book collects the predicates and bridge lemmas used to connect
;;   implementation checkpoint/cut scanning with the replayed specification.
;;
;; Main proof idea:
;;   1. Before a process sees its first marker, CM-INPUTS-BEFORE-CUT replay
;;      preserves the process local-state match.
;;   2. When the first marker is received, the saved snapshot local state is
;;      exactly that matched implementation local state.
;;   3. After the cut, the still-open incoming channels are compared against
;;      RUN-SPEC over REPLAY-INPUTS-FOR-ONE-PROC.
;;   4. A normal receive on an open channel is handled by appending that input
;;      to the appropriate after-cut row and proving the replay consumes the
;;      same normal message.
;;
;; Cleanup notes:
;;   - Duplicate event names were removed/commented with NOTE markers.
;;   - Large transition functions are generally kept disabled in proof hints;
;;     smaller bridge lemmas are used to expose only the needed effects.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
;; available in the model.  The key scanners used below are
;; RUN-IMP-TRACE, COLLECT-RECOVERY-SEGMENTS-FROM-TRACE, and
;; SCAN-UNTIL-RECOVERY.

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic local-state/snapshot lemmas
;;
;; These lemmas isolate facts about local-state preservation and first-marker
;; snapshot installation.  Keeping them small makes the later cut-scan proof
;; avoid expanding the full receive/checkpoint transition repeatedly.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Before-first-marker local-state invariant
;;
;; CUT-SCAN-SPEC-IMP-LOCAL-MATCH-P says that replaying the inputs collected
;; before the cut gives the same local state for process I as the current
;; implementation state.  The step and segment theorems below preserve this
;; while I remains in CUT-NOT-TAKEN.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Cut-taking step and saved local snapshot
;;
;; When I leaves CUT-NOT-TAKEN, the receive must be the first marker for the
;; snapshot id.  The theorem in this block connects the pre-cut spec/local
;; match to the local state stored in I's snapshot entry.
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Neighbor-row preservation
;;
;; These lemmas show that the :NBRS-FROM rows are stable across the concrete
;; system transitions used in the cut-scan argument.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; After-cut replay well-formedness
;;
;; After a process has taken its cut, only normal RECEIVE inputs on still-open
;; incoming channels are stored in :INPUTS-AFTER-CUT.  The row predicates below
;; state that every stored input under source SRC is exactly a receive SRC -> DST.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lifting per-channel replay equality to incoming-channel equivalence
;;
;; The low-level replay lemmas prove equality for a fixed SRC -> I channel.
;; INCOMING-CHANNELS-EQUAL-P packages those per-source equalities so they can be
;; used to replace the spec or implementation channel map in the recursive
;; INCOMING-CHANNELS-EQUIVALENT-FOR-PROC-P predicate.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Replay invariant for CM-AFTER-CUT-APPEND
;;
;; These predicates collect the recurring side conditions needed to prove that
;; updating one after-cut row is equivalent to replaying the old grouped inputs
;; and then executing the new receive input at the end.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


;; NOTE: Removed an earlier duplicate of MEMBERP-WHEN-MEMBERP-AND-SUBSET.
;; The kept version below includes the explicit SUBSET/MEMBERP enable hint.


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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Row invariants used by the open-channel preservation theorem
;;
;; The final after-cut receive theorem needs uniqueness of waiting-marker rows,
;; uniqueness of neighbor rows, subset facts, and after-cut row well-formedness.
;; These small access lemmas expose the row-level facts from all-process
;; invariants.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


(defthm replay-inputs-for-one-proc-of-s-msgs-after-cut
  (equal
   (replay-inputs-for-one-proc
    i nbrs
    (s :msgs-after-cut msgs-after-cut m))
   (replay-inputs-for-one-proc
    i nbrs m)))

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
          (process-cut-step input st-cur m)))
    i
    (g :channels (system-step st-cur input))
    (g
     :channels
     (run-spec
      spec-start-st
      (replay-inputs-for-one-proc
       i
       (g :nbrs-from (g i (g :procs st-cur)))
       (process-cut-step input st-cur m))))))

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


(defthm cut-scan-open-incoming-channels-equivalent-after-cut-start-checkpoint-step
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

    ;; Start-checkpoint step.
    (equal (g :ttype input) :start-checkpoint)
    (legal-inputp st-cur input))

   ;; After start-checkpoint, open incoming equivalence for i is preserved.
   (incoming-channels-equivalent-for-proc-p
    (g i
       (g :waiting-marker-from
          (process-cut-step input st-cur m)))
    i
    (g :channels (system-step st-cur input))
    (g
     :channels
     (run-spec
      spec-start-st
      (replay-inputs-for-one-proc
       i
       (g :nbrs-from (g i (g :procs st-cur)))
       (process-cut-step input st-cur m))))))

  :hints
  (("Goal"
    :use
    ((:instance
      incoming-channels-equivalent-for-proc-p-of-system-step-start-checkpoint-left
      (srcs (g i (g :waiting-marker-from m)))
      (dst i)
      (st st-cur)
      (input input)
      (spec-channels
       (g
        :channels
        (run-spec
         spec-start-st
         (replay-inputs-for-one-proc
          i
          (g :nbrs-from (g i (g :procs st-cur)))
          m))))))
    :in-theory
    (e/d
     (process-cut-step
      ;; enable the start-checkpoint cut-meta function here
      ;; if PROCESS-CUT-STEP calls a named helper
      ;; such as PROCESS-CUT-START-CHECKPOINT.
      system-step

      replay-inputs-for-one-proc-of-s-cut-not-taken
      replay-inputs-for-one-proc-of-s-waiting-marker-from
      replay-inputs-for-one-proc-of-first-marker-cut-meta-update
      replay-inputs-for-one-proc-of-s-inputs-before-cut)

     (incoming-channels-equivalent-for-proc-p
     ; incoming-channels-equivalent-for-proc-p-of-system-step-start-checkpoint-left
      step-checkpoint
      start-checkpoint-helper
      send-msg-all-outgoing-channels
      create-marker-message
      run-spec
      replay-inputs-for-one-proc
      legal-inputp)))))




(defun spec-consumed-msgs (st inputs)
  (if (endp inputs)
      nil
    (let* ((input (car inputs))
           (msg   (get-msg-from-channel
                   (g :sender input)
                   (g :pid input)
                   (g :channels st)))
           (st1   (spec-step st input)))
      (if (equal (g :ttype input) :receive)
          (cons msg
                (spec-consumed-msgs st1 (cdr inputs)))
          (spec-consumed-msgs st1 (cdr inputs))))))


(defun channel-snapshot-msgs-match-p (i j m spec-start-st)
  (equal
   (cm-after-cut-msg-get m i j)
   (spec-consumed-msgs
    spec-start-st
    (cm-after-cut-get m i j))))

(defun channel-snapshot-msgs-match-for-nbrs-p
    (i nbrs m spec-start-st)
  (if (endp nbrs)
      t
    (and
     (channel-snapshot-msgs-match-p
      i (car nbrs) m spec-start-st)
     (channel-snapshot-msgs-match-for-nbrs-p
      i (cdr nbrs) m spec-start-st))))


(defthm spec-consumed-msgs-of-append
  (equal
   (spec-consumed-msgs st (append xs ys))
   (append
    (spec-consumed-msgs st xs)
    (spec-consumed-msgs
     (run-spec st xs)
     ys))))

(defthm channel-snapshot-msgs-match-p-of-normal-receive-append-step
  (implies
   (and
    ;; We are appending a receive from j -> i.
    (equal (g :ttype input) :receive)
    (equal (g :pid input) i)
    (equal (g :sender input) j)

    ;; This is the actual implementation message recorded.
    (equal msg
           (get-msg-from-channel j i (g :channels st-cur)))

    (equal (g :msg-type msg) :normal)

    ;; Old per-channel snapshot/spec-consumption match.
    (channel-snapshot-msgs-match-p
     i j m spec-start-st)

    ;; Spec head equals implementation head.
    (equal
     (get-msg-from-channel
      j i
      (g :channels
         (run-spec spec-start-st
                   (cm-after-cut-get m i j))))
     msg))

   ;; Match is preserved after appending the receive input
   ;; and the corresponding consumed message.
   (channel-snapshot-msgs-match-p
    i j
    (cm-after-cut-msg-append
     (cm-after-cut-append m i j input)
     i j msg)
    spec-start-st)))



(defthm channel-snapshot-msgs-match-p-of-normal-receive-append-step-different-src
  (implies
   (and
    (not (equal src j))

    (channel-snapshot-msgs-match-p
     i src m spec-start-st))

   (channel-snapshot-msgs-match-p
    i src
    (cm-after-cut-msg-append
     (cm-after-cut-append m i j input)
     i j msg)
    spec-start-st)))



(defthm channel-snapshot-msgs-match-for-nbrs-p-of-normal-receive-append-step
  (implies
   (and
    ;; Old invariant over all neighbors.
    (channel-snapshot-msgs-match-for-nbrs-p
     i nbrs m spec-start-st)

    ;; We append to bucket j -> i.
    (memberp j nbrs)
    (uniquep nbrs)

    (equal (g :ttype input) :receive)
    (equal (g :pid input) i)
    (equal (g :sender input) j)

    ;; Implementation message being recorded.
    (equal msg
           (get-msg-from-channel j i (g :channels st-cur)))
    (equal (g :msg-type msg) :normal)

    ;; Spec head equals implementation head.
    (equal
     (get-msg-from-channel
      j i
      (g :channels
         (run-spec spec-start-st
                   (cm-after-cut-get m i j))))
     msg))

   (channel-snapshot-msgs-match-for-nbrs-p
    i nbrs
    (cm-after-cut-msg-append
     (cm-after-cut-append m i j input)
     i j msg)
    spec-start-st))

  :hints
  (("Subgoal *1/2"
    :cases ((equal (car nbrs) j))	    )
   ("Goal"
    :induct
    (channel-snapshot-msgs-match-for-nbrs-p
     i nbrs m spec-start-st)
    :in-theory
    (disable
     get-msg-from-channel
     channel-snapshot-msgs-match-p 
      cm-after-cut-append
      cm-after-cut-msg-append
      cm-after-cut-get
      cm-after-cut-msg-get
      spec-consumed-msgs
      run-spec))))



(defthm channel-snapshot-msgs-match-for-nbrs-p-of-process-cut-normal-receive-open
  (implies
   (and
    ;; Old invariant for all incoming neighbors of i.
    (channel-snapshot-msgs-match-for-nbrs-p
     i nbrs m spec-start-st)

    ;; This is a receive input j -> i.
    (equal (g :ttype input) :receive)
    (equal (g :pid input) i)
    (equal (g :sender input) j)

    ;; i has already taken the cut.
    (not (cm-cut-not-taken-p m i))

    ;; j is still open / marker from j has not arrived yet.
    (memberp j (cm-waiting-marker-for m i))

    ;; j belongs to i's neighbor list.
    (memberp j nbrs)
    (uniquep nbrs)

    ;; msg is the actual implementation head.
    (equal msg
           (get-msg-from-channel j i (g :channels st-cur)))

    ;; This branch is for normal-message receive.
    (equal (g :msg-type msg) :normal)

    ;; Spec head agrees with implementation head.
    ;; Later this should come from open incoming-channel equivalence.
    (equal
     (get-msg-from-channel
      j i
      (g :channels
         (run-spec spec-start-st
                   (cm-after-cut-get m i j))))
     msg))

   ;; After process-cut-normal-receive, the message/input match still holds.
   (channel-snapshot-msgs-match-for-nbrs-p
    i nbrs
    (process-cut-normal-receive input i j msg m)
    spec-start-st))

  :hints
  (("Goal"
    :in-theory
     (disable
      get-msg-from-channel
      cm-after-cut-append
      cm-after-cut-msg-append
      cm-after-cut-get
      cm-after-cut-msg-get
      spec-consumed-msgs
      run-spec))))


(defthm channel-snapshot-msgs-match-for-nbrs-p-of-process-cut-marker-receive
  (equal
   (channel-snapshot-msgs-match-for-nbrs-p
    k nbrs
    (process-cut-marker-receive i j st m)
    spec-start-st)
   (channel-snapshot-msgs-match-for-nbrs-p
    k nbrs m spec-start-st)))

(defthm channel-snapshot-msgs-match-for-nbrs-p-of-normal-receive-before-cut
  (implies
   (and
    (channel-snapshot-msgs-match-for-nbrs-p
     pid nbrs m spec-start-st)

    ;; Receiver pid has not taken the cut yet.
    (memberp pid (g :cut-not-taken m)))

   (channel-snapshot-msgs-match-for-nbrs-p
    pid
    nbrs
    (process-cut-normal-receive input pid sender msg m)
    spec-start-st)))

(defthm channel-snapshot-msgs-match-for-nbrs-p-of-normal-receive-sender-not-waiting
  (implies
   (and
    (channel-snapshot-msgs-match-for-nbrs-p
     pid nbrs m spec-start-st)

    ;; Channel sender -> pid is no longer open for snapshot recording.
    (not (memberp sender
                  (g pid (g :waiting-marker-from m)))))

   (channel-snapshot-msgs-match-for-nbrs-p
    pid
    nbrs
    (process-cut-normal-receive input pid sender msg m)
    spec-start-st)))

(defthm channel-snapshot-msgs-match-for-nbrs-p-of-s-inputs-before-cut
  (equal
   (channel-snapshot-msgs-match-for-nbrs-p
    pid nbrs
    (s :inputs-before-cut xs m)
    spec-start-st)
   (channel-snapshot-msgs-match-for-nbrs-p
    pid nbrs
    m
    spec-start-st)))



(defthm channel-snapshot-msgs-match-for-nbrs-p-of-process-cut-normal-receive
  (implies
   (and
    (channel-snapshot-msgs-match-for-nbrs-p
     pid nbrs m spec-start-st)

    (equal (g :ttype input) :receive)
    (equal (g :pid input) pid)
    (equal (g :sender input) sender)

    (memberp sender nbrs)
    (uniquep nbrs)

    (equal
     (get-msg-from-channel
      sender
      pid
      (g :channels
         (run-spec spec-start-st
                   (cm-after-cut-get m pid sender))))
     (get-msg-from-channel
      sender
      pid
      (g :channels st-cur)))

    (equal
     (g :msg-type
        (get-msg-from-channel sender pid (g :channels st-cur)))
     :normal))

   (channel-snapshot-msgs-match-for-nbrs-p
    pid nbrs
    (process-cut-normal-receive
     input
     pid
     sender
     (get-msg-from-channel sender pid (g :channels st-cur))
     m)
    spec-start-st))

  :hints
  (("Goal"
    :in-theory
    (disable
     channel-snapshot-msgs-match-for-nbrs-p
      cm-after-cut-msg-append
      cm-after-cut-append
      get-msg-from-channel
      cm-after-cut-get
      run-spec))))

(defthm channel-snapshot-msgs-match-for-nbrs-p-of-process-cut-receive
  (implies
   (and
    ;; Old invariant for all incoming neighbors of receiver i.
    (channel-snapshot-msgs-match-for-nbrs-p
     i nbrs m spec-start-st)

    ;; INPUT is receive j -> i.
    (equal (g :ttype input) :receive)
    (equal (g :pid input) i)
    (equal (g :sender input) j)

    ;; MSG is the implementation channel head used by process-cut-receive.
    (equal msg
           (current-msg-for-receive input st-cur))

    ;; Neighbor facts needed only in normal append branch.
    (memberp j nbrs)
    (uniquep nbrs)

    ;; If this is the normal/open-channel branch, spec head equals imp head.
    (implies
     (and
      (equal (g :msg-type msg) :normal)
      (not (cm-cut-not-taken-p m i))
      (memberp j (cm-waiting-marker-for m i)))
     (equal
      (get-msg-from-channel
       j i
       (g :channels
          (run-spec spec-start-st
                    (cm-after-cut-get m i j))))
      msg)))

   (channel-snapshot-msgs-match-for-nbrs-p
    i nbrs
    (process-cut-receive input st-cur m)
    spec-start-st))

  :hints
  (("Goal"

    :in-theory
    (disable
     channel-snapshot-msgs-match-for-nbrs-p
      get-msg-from-channel
      process-cut-normal-receive
      process-cut-marker-receive
      cm-after-cut-get
      run-spec
      spec-consumed-msgs))))


(defthm channel-snapshot-msgs-match-for-nbrs-p-of-process-cut-step
  (implies
   (and
    (channel-snapshot-msgs-match-for-nbrs-p
     i nbrs m spec-start-st)

    ;; If the step is a receive, it is receive j -> i.
    (implies (equal (g :ttype input) :receive)
             (equal (g :pid input) i))
    (implies (equal (g :ttype input) :receive)
             (equal (g :sender input) j))
    (implies (equal (g :ttype input) :receive)
             (equal msg
                    (current-msg-for-receive input st-cur)))

    ;; Neighbor facts only matter in the receive/append branch.
    (memberp j nbrs)
    (uniquep nbrs)

    ;; Only required in the normal/open-channel receive branch.
    (implies
     (and
      (equal (g :ttype input) :receive)
      (equal (g :msg-type msg) :normal)
      (not (cm-cut-not-taken-p m i))
      (memberp j (cm-waiting-marker-for m i)))
     (equal
      (get-msg-from-channel
       j i
       (g :channels
          (run-spec spec-start-st
                    (cm-after-cut-get m i j))))
      msg)))

   (channel-snapshot-msgs-match-for-nbrs-p
    i nbrs
    (process-cut-step input st-cur m)
    spec-start-st))

  :hints
  (("Goal"
    :cases ((equal (g :ttype input) :receive))
    :in-theory
    (e/d
     (process-cut-step)
     (channel-snapshot-msgs-match-for-nbrs-p
      process-cut-receive
      process-cut-normal-receive
      process-cut-marker-receive
      current-msg-for-receive
      get-msg-from-channel
      cm-after-cut-get
      run-spec
      spec-consumed-msgs)))))




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


(defthm channel-snapshot-of-record-msg-in-snapshots-same
  (implies
   (and
    (memberp sid snapshot-ids)
    (uniquep snapshot-ids)

    (equal (g :status (g sid snapshots))
           :checkpointing)

    (memberp j
             (g :waiting-marker-from
                (g sid snapshots))))

   (equal
    (g j
       (g :channel-snapshots
          (g sid
             (record-msg-in-snapshots
              snapshots snapshot-ids j msg))))
    (append
     (g j
        (g :channel-snapshots
           (g sid snapshots)))
     (list msg)))))

(defthm channel-snapshot-of-record-msg-in-snapshots-different-channel
  (implies
   (not (equal k j))
   (equal
    (g k
       (g :channel-snapshots
          (g sid
             (record-msg-in-snapshots
              snapshots snapshot-ids j msg))))
    (g k
       (g :channel-snapshots
          (g sid snapshots))))))


(defthm msg-type-of-get-msg-from-empty-channel-not-normal
  (implies
   (not (g sender
           (g pid channels)))
   (not
    (equal
     (g :msg-type
        (get-msg-from-channel sender pid channels))
     :normal))))


(defthm cm-imp-snapshot-msgs-match-for-nbrs-p-ignore-local-state-and-channels
  (equal
   (cm-imp-snapshot-msgs-match-for-nbrs-p
    i nbrs sid m
    (s :procs
       (s i
          (s :snapshots snapshots
             (s :local-state local-state
                (g i (g :procs st))))
          (g :procs st))
       (s :channels channels st)))
   (cm-imp-snapshot-msgs-match-for-nbrs-p
    i nbrs sid m
    (s :procs
       (s i
          (s :snapshots snapshots
             (g i (g :procs st)))
          (g :procs st))
       st))))


(defthm cm-imp-snapshot-msgs-match-for-nbrs-p-of-msg-append-and-record-not-memberp
  (implies
   (and
    (cm-imp-snapshot-msgs-match-for-nbrs-p
     i nbrs sid m st)

    ;; The updated source j is not in the list we are checking.
    (not (memberp j nbrs)))

   (cm-imp-snapshot-msgs-match-for-nbrs-p
    i nbrs sid

    ;; Metadata update on j -> i.
    (cm-after-cut-msg-append m i j msg)

    ;; Implementation snapshot update on j -> i.
    (s :procs
       (s i
          (s :snapshots
             (record-msg-in-snapshots
              (g :snapshots (g i (g :procs st)))
              (g :snapshot-ids (g i (g :procs st)))
              j
              msg)
             (g i (g :procs st)))
          (g :procs st))
       st))))

(defthm msgs-after-cut-of-cm-after-cut-msg-append-same
  (equal
   (g j
      (g i
         (g :msgs-after-cut
            (cm-after-cut-msg-append m i j msg))))
   (append
    (g j
       (g i
          (g :msgs-after-cut m)))
    (list msg))))

(defthm msgs-after-cut-of-cm-after-cut-msg-append-different
  (implies
   (not (equal k j))
   (equal
    (g k
       (g i
          (g :msgs-after-cut
             (cm-after-cut-msg-append m i j msg))))
    (g k
       (g i
          (g :msgs-after-cut m))))))

(defthm cm-imp-snapshot-msgs-match-for-nbrs-p-of-msg-append-and-record
  (implies
   (and
    ;; Old equality between metadata msgs and implementation snapshot msgs.
    (cm-imp-snapshot-msgs-match-for-nbrs-p
     i nbrs sid m st)

    ;; We update channel j -> i.
    (memberp j nbrs)
    (uniquep nbrs)

    ;; Snapshot sid exists uniquely for process i.
    (memberp sid
             (g :snapshot-ids
                (g i (g :procs st))))

    (uniquep
     (g :snapshot-ids
        (g i (g :procs st))))

    ;; Snapshot sid is actively recording.
    (equal
     (g :status
        (g sid
           (g :snapshots
              (g i (g :procs st)))))
     :checkpointing)

    ;; Snapshot sid is still recording channel j -> i.
    (memberp
     j
     (g :waiting-marker-from
        (g sid
           (g :snapshots
              (g i (g :procs st)))))))

   (cm-imp-snapshot-msgs-match-for-nbrs-p
    i
    nbrs
    sid

    ;; Metadata after appending msg.
    (cm-after-cut-msg-append m i j msg)

    ;; Implementation snapshot after recording msg.
    (s :procs
       (s i
          (s :snapshots
             (record-msg-in-snapshots
              (g :snapshots
                 (g i (g :procs st)))
              (g :snapshot-ids
                 (g i (g :procs st)))
              j
              msg)
             (g i (g :procs st)))
          (g :procs st))
       st)))

  :hints
  (("Goal"
    :induct
    (cm-imp-snapshot-msgs-match-for-nbrs-p
     i nbrs sid m st)
    :in-theory
    (e/d
     (cm-imp-snapshot-msgs-match-for-nbrs-p
      ;cm-after-cut-msg-append
      )
     (cm-after-cut-msg-append
      record-msg-in-snapshots)))))

(defthm cm-imp-snapshot-msgs-match-for-nbrs-p-of-msg-append-after-input-append
  (equal
   (cm-imp-snapshot-msgs-match-for-nbrs-p
    i nbrs sid
    (cm-after-cut-msg-append
     (cm-after-cut-append m dst src input)
     dst2 src2 msg)
    st)
   (cm-imp-snapshot-msgs-match-for-nbrs-p
    i nbrs sid
    (cm-after-cut-msg-append
     m dst2 src2 msg)
    st)))

(defthm cm-imp-snapshot-msgs-match-for-nbrs-p-of-handle-normal-msg
  (implies
   (and
    ;; Old meta/implementation snapshot equality.
    (cm-imp-snapshot-msgs-match-for-nbrs-p
     i nbrs sid m st-cur)

    ;; Receive j -> i.
    (equal (g :ttype input) :receive)
    (equal (g :pid input) i)
    (equal (g :sender input) j)

    ;; Message being handled.
    (equal msg
           (get-msg-from-channel j i (g :channels st-cur)))
    (equal (g :msg-type msg) :normal)

    ;; Metadata records this message.
    (not (cm-cut-not-taken-p m i))
    (memberp j (cm-waiting-marker-for m i))

    ;; Implementation snapshot also records this message.
    (memberp sid
             (g :snapshot-ids
                (g i (g :procs st-cur))))

    (uniquep
     (g :snapshot-ids
        (g i (g :procs st-cur))))

    (equal
     (g :status
        (g sid
           (g :snapshots
              (g i (g :procs st-cur)))))
     :checkpointing)

    (memberp
     j
     (g :waiting-marker-from
        (g sid
           (g :snapshots
              (g i (g :procs st-cur))))))

    ;; Avoid the recovery-ignore branch.
    (not
     (and
      (equal (g :proc-status
                (g i (g :procs st-cur)))
             :recovering)
      (memberp j
               (g :waiting-recovery-from
                  (g i (g :procs st-cur))))))

    ;; Neighbor facts.
    (memberp j nbrs)
    (uniquep nbrs))

   (cm-imp-snapshot-msgs-match-for-nbrs-p
    i nbrs sid

    ;; Metadata after recording.
    (cm-after-cut-msg-append
     (cm-after-cut-append m i j input)
     i j msg)

    ;; Implementation after handling normal message.
    (handle-normal-msg st-cur i j msg)))

  :hints
  (("Goal"

    :in-theory
    (e/d
     (handle-normal-msg)
     ( cm-after-cut-msg-append
       cm-after-cut-append

     get-msg-from-channel
      get-msg-from-channel)))))


(defthm cm-imp-snapshot-msgs-match-for-nbrs-p-of-normal-open-receive
  (implies
   (and
    ;; Old meta/implementation snapshot-message equality.
    (cm-imp-snapshot-msgs-match-for-nbrs-p
     i nbrs sid m st-cur)

    ;; Receive j -> i.
    (equal (g :ttype input) :receive)
    (equal (g :pid input) i)
    (equal (g :sender input) j)

    ;; The received message.
    (equal msg
           (get-msg-from-channel j i (g :channels st-cur)))
    (equal (g :msg-type msg) :normal)

    ;; This is the open snapshot-recording branch in metadata.
    (not (cm-cut-not-taken-p m i))
    (memberp j (cm-waiting-marker-for m i))

    ;; Same branch is open in implementation snapshot.
    (memberp sid
             (snapshot-ids (g i (g :procs st-cur))))
    (equal
     (snapshot-status
      (snapshot-entry sid (g i (g :procs st-cur))))
     :checkpointing)
    (memberp
     j
     (snapshot-waiting-marker-from
      (snapshot-entry sid (g i (g :procs st-cur)))))

    ;; Avoid the ignore-normal-msg branch.
    (not
     (and
      (equal (proc-status (g i (g :procs st-cur))) :recovering)
      (memberp j
               (waiting-recovery-from
                (g i (g :procs st-cur))))))

    ;; Neighbor facts.
    (uniquep
     (g :snapshot-ids
	(g i (g :procs st-cur))))
    (memberp j nbrs)
    (uniquep nbrs))

   (cm-imp-snapshot-msgs-match-for-nbrs-p
    i nbrs sid

    ;; Metadata after recording msg.
    (cm-after-cut-msg-append
     (cm-after-cut-append m i j input)
     i j msg)

    ;; Implementation after receiving msg.
    (step-rcv st-cur i j)))

  :hints
  (("Goal"
    :in-theory
    (disable
     handle-normal-msg
     cm-imp-snapshot-msgs-match-for-nbrs-p-of-msg-append-after-input-append
     cm-after-cut-msg-append
     cm-after-cut-append
     get-msg-from-channel))))






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


(defthm imp-snapshot-spec-msgs-match-p-from-cm-bridges
  (implies
   (and
    ;; metadata = implementation snapshot
    (equal
     (cm-after-cut-msg-get m i j)
     (imp-snapshot-msg-get sid i j st))

    ;; metadata = spec consumed msgs
    (channel-snapshot-msgs-match-p
     i j m spec-start-st))

   ;; therefore implementation snapshot = spec consumed msgs
   (imp-snapshot-spec-msgs-match-p
    i j sid m st spec-start-st)))


(defthm imp-snapshot-spec-msgs-match-for-nbrs-p-from-cm-bridges
  (implies
   (and
    ;; For every neighbor:
    ;; metadata msgs = implementation snapshot msgs
    (cm-imp-snapshot-msgs-match-for-nbrs-p
     i nbrs sid m st)

    ;; For every neighbor:
    ;; metadata msgs = spec consumed msgs
    (channel-snapshot-msgs-match-for-nbrs-p
     i nbrs m spec-start-st))

   ;; Therefore:
   ;; implementation snapshot msgs = spec consumed msgs
   (imp-snapshot-spec-msgs-match-for-nbrs-p
    i nbrs sid m st spec-start-st)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final wrapper: open incoming channels after I has taken the cut
;;
;; Only channels still waiting for a marker are compared.  A normal receive on
;; one of those channels appends the receive input to the after-cut metadata and
;; the replay-side channel equality lemmas show the spec consumes the same head
;; normal message.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defun cut-scan-replay-open-incoming-channels-equivalent-for-proc-p
;;     (i m st-cur spec-start-st)
;;   (incoming-channels-equivalent-for-proc-p
;;    ;; Only channels still waiting for marker are tracked.
;;    (cm-waiting-marker-for m i)

;;    i

;;    ;; Current implementation channels.
;;    (g :channels st-cur)

;;    ;; Spec after replaying all after-cut inputs collected so far.
;;    (g :channels
;;       (run-spec
;;        spec-start-st
;;        (replay-inputs-for-one-proc
;;         i
;;         (g :nbrs-from (g i (g :procs st-cur)))
;;         m)))))


;; (defun cut-scan-after-cut-segment-inputp (input)
;;   (or (equal (g :ttype input) :normal)
;;       (equal (g :ttype input) :receive)
;;       (equal (g :ttype input) :start-checkpoint)))


;; (defthm cut-scan-replay-open-incoming-channels-equivalent-after-cut-step
;;   (implies
;;    (and
;;     ;; Only open incoming channels into i match before this step.
;;     (cut-scan-replay-open-incoming-channels-equivalent-for-proc-p
;;      i m st-cur spec-start-st)

;;     ;; i has already taken its cut.
;;     (not (memberp i (cm-cut-not-taken m)))

;;     ;; i is still recording at least one incoming channel.
;;     ;; Needed by cut-scan-open-incoming-channels-equivalent-after-cut-receive-step.
;;     (consp
;;      (g i
;;         (g :waiting-marker-from m)))

;;     ;; Each waiting-marker row has no duplicate sources.
;;     (waiting-marker-from-rows-uniquep-p
;;      (g :proc-ids st-cur)
;;      m)

;;     ;; Each neighbor row has no duplicate sources.
;;     (nbrs-from-rows-uniquep-p
;;      (g :proc-ids st-cur)
;;      (g :procs st-cur))

;;     ;; Waiting-marker rows are subsets of the corresponding nbrs-from rows.
;;     (waiting-marker-from-subset-of-nbrs-from-p
;;      (g :proc-ids st-cur)
;;      m
;;      (g :procs st-cur))

;;     ;; The after-cut input rows are well-formed for every process.
;;     (after-cut-for-all-procs-well-formed-p
;;      (g :proc-ids st-cur)
;;      (g :procs st-cur)
;;      m)

;;     ;; Current implementation input is legal.
;;     (legal-inputp st-cur input)

;;     (equal (g :ttype input) :receive)

;;     ;; No recovery behavior during this cut-scan step.
;;     (cut-scan-no-recovery-step-p input st-cur)

;;     ;; Name the next implementation state.
;;     (equal st-next
;;            (system-step st-cur input))

;;     ;; Name the next cut metadata.
;;     (equal m-next
;;            (process-cut-step input st-cur m)))

;;    ;; Only the updated open incoming channels into i must match.
;;    (cut-scan-replay-open-incoming-channels-equivalent-for-proc-p
;;     i m-next st-next spec-start-st))

;;   :hints
;;   (("Goal''"
;;     :by
;;     (:instance cut-scan-open-incoming-channels-equivalent-after-cut-receive-step
;;                (i i)
;;                (m m)
;;                (st-cur st-cur)
;;                (spec-start-st spec-start-st)
;;               (input input)))
;;    ("Goal"
;;     :in-theory
;;     (e/d
;;      (cut-scan-replay-open-incoming-channels-equivalent-for-proc-p
;;       process-cut-step)

;;      (system-step
;;       spec-step
;;       step-rcv
;;       spec-step-rcv
;;       step-normal
;;       spec-step-normal
;;       step-crash
;;       step-recover

;;       process-cut-receive
;;       process-cut-normal
;;       process-cut-normal-receive
;;       process-cut-marker-receive
;;       current-msg-for-receive

;;       handle-normal-msg
;;       handle-normal-msg-core
;;       handle-marker-msg
;;       handle-recovery-msg

;;       cut-scan-open-incoming-channels-equivalent-after-cut-receive-step

;;       incoming-channels-equivalent-for-proc-p
;;       imp-spec-channel-msgs-equivalent-p
;;       run-spec
;;       run-imp
;;       legal-inputp
;;       cut-scan-no-recovery-step-p)))))


;; NOTE: Removed a second draft theorem named
;; CUT-SCAN-REPLAY-OPEN-INCOMING-CHANNELS-EQUIVALENT-AFTER-CUT-STEP.
;; ACL2 event names must be unique.  The kept theorem above is the
;; receive-step version with the needed open-channel and well-formedness
;; hypotheses.

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
