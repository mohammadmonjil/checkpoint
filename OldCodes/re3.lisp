(in-package "ACL2")

(include-book "model")
(include-book "scan")
(include-book "good_state_invariants")
(include-book "channel_equivalence")
(include-book "basic")
(include-book "cfinvariants")
(include-book "rec")
(include-book "cut_inv")
(include-book "lemmas_meta_data_commute")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof roadmap
;;
;; The book establishes checkpoint-segment reordering in four layers:
;;
;;   1. Segment wrappers expose one unified cut scan and its before/after
;;      classification without duplicating scanner logic.
;;   2. A local post-cut/pre-cut predicate is shown to imply a semantic
;;      two-input swappability contract.
;;   3. Independent adjacent inputs are proved to commute componentwise:
;;      application-visible process state, concrete channels, and the
;;      checkpoint-control projection.
;;   4. The component results are assembled into CL-STATE-EQUIVALENT-P, and
;;      a separate preservation library shows that subsequent checkpoint-body
;;      steps respect that equivalence.
;;
;; Comments distinguish exact equality from observational equivalence.  Exact
;; equality is used for PROC-IDS and CHANNELS; process protocol bookkeeping is
;; compared only through the fields its corresponding relation observes.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Complete isolated checkpoint segment using the unified cut scan
;;
;; A valid segment:
;;   1. is nonempty;
;;   2. starts with :start-checkpoint;
;;   3. has no later recovery, crash, or unknown input;
;;   4. starts outside an active  recovery;
;;   5. is legal from the supplied implementation state;
;;   6. does not consume a recovery message through a generic receive;
;;   7. first reaches full checkpoint completion after its final input.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; ------------------------------------------------------------------
;; Exclude receives that consume recovery messages
;; ------------------------------------------------------------------

;; A :receive input does not identify the message type directly.
;; Its behavior is determined by the head message on:
;;
;;     sender(input) -> pid(input)
(defun cl-recovery-receive-input-p (input st)
  (and
   (equal (ttype input) :receive)
   (let ((msg (current-msg-for-receive input st)))
     (and
      msg
      (equal (msg-type msg) :recovery)))))

;; Lift the single-input test to an entire execution.  The recursive call
;; deliberately checks the tail in the state produced by the head input:
;; whether a later :receive is a recovery receive depends on the channel
;; contents at that later execution point, not on the initial state.
(defun cl-no-recovery-receive-sequencep (st inputs)
  (declare
   (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      t
    (let ((input (first inputs)))
      (and
       (not
        (cl-recovery-receive-input-p input st))

       (cl-no-recovery-receive-sequencep
        (system-step st input)
        (rest inputs))))))



;; ------------------------------------------------------------------
;; Segment identity and unified-scan wrappers
;; ------------------------------------------------------------------

;; The first input is the distinguished checkpoint start, so its PID is the
;; process whose cut this segment is intended to complete.
(defun cl-checkpoint-segment-initiator (input-seg)
  (pid (first input-seg)))

;; The implementation creates the SID using the initiator's counter
;; immediately before the :start-checkpoint input executes.
(defun cl-checkpoint-segment-sid (st input-seg)
  (let* ((i (cl-checkpoint-segment-initiator input-seg))
         (p (g i (procs st))))
    (list i (counter p))))

;; RUN-IMP-TRACE supplies the state at every input boundary.  Keeping this
;; wrapper named by the segment abstraction prevents later definitions from
;; depending directly on the trace representation.
(defun cl-checkpoint-segment-trace (st input-seg)
  (run-imp-trace st input-seg))

;; Run the single, authoritative cut scanner over the complete segment.
;; The returned object contains both the cut metadata and the end-exclusive
;; index at which checkpoint collection first becomes complete.
(defun cl-checkpoint-segment-result (st input-seg)
  (let* ((initiator
          (cl-checkpoint-segment-initiator input-seg))

         (sid
          (cl-checkpoint-segment-sid st input-seg))

         (trace
          (cl-checkpoint-segment-trace st input-seg)))

    ;; The checkpoint-start input is at index 0.
    (scan-until-cut-done
     input-seg
     trace
     0
     sid
     initiator)))

;; The scanner's metadata records the global before/after partition as well
;; as its per-channel refinement.  All accessors below read this one object;
;; no second classification of the input sequence is performed.
(defun cl-checkpoint-segment-meta (st input-seg)
  (cut-result-meta
   (cl-checkpoint-segment-result st input-seg)))

;; End-exclusive completion position returned by the unified scan.
(defun cl-checkpoint-segment-completion-index (st input-seg)
  (cut-result-idx
   (cl-checkpoint-segment-result st input-seg)))

;; Boolean view of the scanner's checkpoint-collection status.
(defun cl-checkpoint-segment-completep (st input-seg)
  (checkpoint-collection-complete-p
   (cl-checkpoint-segment-meta st input-seg)))

;; The scan index is end-exclusive. NTH at the completion index gives
;; the implementation state after the input that completed collection.
(defun cl-checkpoint-segment-completion-state (st input-seg)
  (nth
   (cl-checkpoint-segment-completion-index st input-seg)
   (cl-checkpoint-segment-trace st input-seg)))

;; Ordinary operational endpoint, retained separately from the state at the
;; first completion index so later theorems can compare the two explicitly.
(defun cl-checkpoint-segment-end-state (st input-seg)
  (run-imp st input-seg))

;; ------------------------------------------------------------------
;; Unified metadata accessors
;; ------------------------------------------------------------------

;; Global prerecording sequence, preserving original execution order.
;; (defun cl-checkpoint-segment-before-cut-inputs (st input-seg)
;;   (cm-inputs-before-cut
;;    (cl-checkpoint-segment-meta st input-seg)))

(defun cl-checkpoint-segment-before-cut-inputs (st input-seg)
  (cm-before-cut-input-sequence
   (cl-checkpoint-segment-meta st input-seg)))

;; Global postrecording sequence, preserving original execution order.
(defun cl-checkpoint-segment-after-cut-inputs (st input-seg)
  (cm-after-cut-input-sequence
   (cl-checkpoint-segment-meta st input-seg)))


;; Chandy-Lamport paper-style reordered ordinary input sequence.
(defun cl-checkpoint-segment-reordered-inputs (st input-seg)
  (append
   (cl-checkpoint-segment-before-cut-inputs
    st input-seg)

   (cl-checkpoint-segment-after-cut-inputs
    st input-seg)))

;; ------------------------------------------------------------------
;; Main complete-segment predicate
;; ------------------------------------------------------------------

;; This predicate is the public contract for the reordering theorem.  It
;; couples syntactic shape, dynamic legality, recovery exclusion, and the
;; unified scanner's completion result.  In particular, the final index
;; equality says that completion occurs at the segment boundary rather than
;; somewhere in a proper prefix.
(defun cl-checkpoint-complete-segment-p (st input-seg)
  (and
   ;; The segment has a first input.
   (consp input-seg)

   ;; The first input starts the target checkpoint.
   (equal
    (ttype (first input-seg))
    :start-checkpoint)

   ;; Every later input is :nop, :normal, :start-checkpoint or :receive.
   ;; This excludes:
   ;;   :recover
   ;;   :crash
   ;;   unknown input types
   (cl-checkpoint-body-inputs-p
    (rest input-seg))
   
   (good-state-p st)
   ;; Every input is legal in the state where it executes.
   (legal-input-sequencep
    st input-seg)

   ;; We begin completely outside recovery.
   (recovery-free-state-p st)

   ;; The scanner has witnessed completion of the target checkpoint.
   (cl-checkpoint-segment-completep
    st input-seg)

   ;; The scan index is end-exclusive. Equality with the segment length
   ;; means completion was not reached before the final input.
   (equal
    (cl-checkpoint-segment-completion-index
     st input-seg)

    (len input-seg))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Local two-input independence contract
;;
;; Global reordering is reduced to adjacent transpositions.  The predicate
;; below states exactly when one such transposition is semantically safe:
;; the inputs belong to different processes, both orders are legal, and
;; neither order enters the recovery semantics.  Subsequent commutation
;; theorems consume this common contract for processes, channels, and
;; checkpoint-control state.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun cl-two-imp-inputs-swappable-p
    (st input-1 input-2)

  (let* ((st-1 (system-step st input-1))
         (st-2 (system-step st input-2)))

    (and

     ;; Preserve each process's local input order.
     (not
      (equal
       (pid input-1)
       (pid input-2)))

     ;; Both inputs are valid checkpoint-segment body inputs.
     ;; This includes checkpoint starts for other SIDs.
     (cl-checkpoint-body-input-p input-1)
     (cl-checkpoint-body-input-p input-2)

     ;; Both execution orders are legal.
     (legal-inputp st input-1)
     (legal-inputp st-1 input-2)

     (legal-inputp st input-2)
     (legal-inputp st-2 input-1)

     ;; Neither execution order performs recovery activity.
     (no-recovery-step-p input-1 st)
     (no-recovery-step-p input-2 st-1)

     (no-recovery-step-p input-2 st)
     (no-recovery-step-p input-1 st-2))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; State equivalence used by the implementation reordering proof
;;
;; Two implementation states are equivalent when they have:
;;   1. the same process identifiers;
;;   2. exactly the same channel state;
;;   3. pointwise equality of application-visible process fields; and
;;   4. pointwise equality of checkpoint-control fields.
;;
;; PROCS-EQUIVALENT-P observes LOCAL-STATE, NBRS-TO, and NBRS-FROM.
;; CL-CHECKPOINT-CONTROL-EQUIVALENT-P observes COUNTER and SNAPSHOT-IDS.
;; The remaining implementation bookkeeping may differ.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cl-state-equivalent-p (st-1 st-2)

  (and
   (equal
    (proc-ids st-1)
    (proc-ids st-2))

   (equal
    (channels st-1)
    (channels st-2))

   ;; Existing pointwise visible-process relation.
   (procs-equivalent-p
    (proc-ids st-1)
    (procs st-1)
    (procs st-2))

   ;; Existing pointwise checkpoint-control relation.
   (cl-checkpoint-control-equivalent-p
    (proc-ids st-1)
   (procs st-1)
   (procs st-2))))

;; Process-side adjacent-swap theorem.  SYSTEM-STEP has sixteen possible
;; body-input type pairs; the case split reduces each to the channel/update
;; algebra above.  Literal process records need not agree because snapshots
;; and protocol bookkeeping may be recorded in different orders.  The
;; application-visible fields observed by PROCS-EQUIVALENT-P do agree.
(defthm
  cl-two-imp-inputs-commute-under-procs-equivalence

  (implies
   (cl-two-imp-inputs-swappable-p
    st
    input-1
    input-2)

   (procs-equivalent-p
    (proc-ids st)

    ;; INPUT-1 followed by INPUT-2.
    (procs
     (system-step
      (system-step st input-1)
      input-2))

    ;; INPUT-2 followed by INPUT-1.
    (procs
     (system-step
      (system-step st input-2)
      input-1))))

 ; :otf-flg t

  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel
     remove-message-from-channel
     start-checkpoint-helper
     create-marker-message
     update-proc-for-normal-msg-core)

    :cases
    ((equal (ttype input-1) :nop)
     (equal (ttype input-1) :normal)
     (equal (ttype input-1) :receive)
     (equal (ttype input-1) :start-checkpoint)

     (equal (ttype input-2) :nop)
     (equal (ttype input-2) :normal)
     (equal (ttype input-2) :receive)
     (equal (ttype input-2) :start-checkpoint)))))









;; ------------------------------------------------------------
;; INPUT-J is legal before moving it to the left of INPUT-I.
;;
;; We know INPUT-I ; INPUT-J is legal in the original execution.
;; INPUT-I is post-cut, while INPUT-J is still pre-cut immediately
;; before it executes.
;;
;; The marker-in-transit invariant rules out the only problematic
;; dependency: INPUT-I cannot be responsible for creating the
;; message that makes a pre-cut INPUT-J receive legal.
;; ------------------------------------------------------------

(defthm cl-post-pre-input-j-legal-before-input-i
  (let*
      ((m-after-i
        (process-cut-step
         input-i
         st
         m)))

    (implies
     (and
      (cut-markers-in-transit-p
       m
       st)

      (cut-meta-imp-consistent-p
       m
       st)
      ;; We begin completely outside recovery.
      (recovery-free-state-p st)
      
      (good-cut-meta-p m)

      (good-state-p st)

      (legal-input-sequencep
       st
       (list input-i input-j))

      (cl-checkpoint-body-input-p
       input-i)

      (cl-checkpoint-body-input-p
       input-j)

      ;; (no-recovery-step-p
      ;;  input-i
      ;;  st)

      ;; (no-recovery-step-p
      ;;  input-j
      ;;  (system-step st input-i))

      ;; INPUT-I is post-cut.
      (not
       (cm-cut-not-taken-p
        m
        (pid input-i)))

      ;; INPUT-J is still pre-cut after INPUT-I.
      (cm-cut-not-taken-p
       m-after-i
       (pid input-j)))

     (legal-inputp
      st
      input-j)))
  :rule-classes
  ((:rewrite
    :match-free :all))

  :hints
  (("Goal"
    :cases
    ((equal (ttype input-i) :nop)
     (equal (ttype input-i) :normal)
     (equal (ttype input-i) :receive)
     (equal (ttype input-i) :start-checkpoint)

     (equal (ttype input-j) :nop)
     (equal (ttype input-j) :normal)
     (equal (ttype input-j) :receive)
     (equal (ttype input-j) :start-checkpoint))

    :in-theory
    (disable
     good-state-p
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     recovery-free-state-p
     good-cut-meta-p
    ; legal-inputp
     process-cut-step
     system-step
     step-normal
     step-rcv
     step-checkpoint
     get-msg-from-channel
     cm-cut-not-taken-p))
   ("Subgoal 7''"
    :cases
    ((equal
    (sender input-j)
    (pid input-i))))
      ("Subgoal 2.1"
    :cases
    ((equal
    (sender input-j)
    (pid input-i))))))




;; ------------------------------------------------------------
;; SWAPPED-ORDER LEGALITY OF INPUT-I
;;
;; Original execution:
;;
;;        ST --INPUT-I--> ... --INPUT-J-->
;;
;; is legal.
;;
;; INPUT-I belongs to a process that is already POST-cut,
;; while INPUT-J is still PRE-cut after INPUT-I.
;;
;; To swap the two inputs, we must show that INPUT-I is still
;; legal after executing INPUT-J first:
;;
;;        ST --INPUT-J--> ...
;;                         ^
;;                         INPUT-I must be legal here.
;; ------------------------------------------------------------

(defthm
  cl-post-pre-input-i-legal-after-input-j

  (implies
   (and
    ;; Cut invariants at ST.
    (cut-markers-in-transit-p
     m st)

    (cut-meta-imp-consistent-p
     m st)

    (good-cut-meta-p m)

    (good-state-p st)
    ;; We begin completely outside recovery.
    (recovery-free-state-p st)
    ;; Original two-input execution is legal.
    (legal-input-sequencep
     st
     (list input-i input-j))

    ;; Both inputs are checkpoint-body inputs.
    (cl-checkpoint-body-input-p
     input-i)

    (cl-checkpoint-body-input-p
     input-j)

    ;; ;; No recovery activity occurs in this two-step segment.
    ;; (no-recovery-step-p
    ;;  input-i
    ;;  st)

    ;; (no-recovery-step-p
    ;;  input-j
    ;;  (system-step st input-i))

    ;; INPUT-I is already POST-cut.
    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))

    ;; INPUT-J is still PRE-cut after INPUT-I.
    (cm-cut-not-taken-p
     (process-cut-step
      input-i
      st
      m)
     (pid input-j)))

   ;; After moving INPUT-J first, INPUT-I remains legal.
   (legal-inputp
    (system-step st input-j)
    input-i))
    :rule-classes
  ((:rewrite
    :match-free :all))

  :hints
  (("Goal"
    :cases
    ((equal (ttype input-i) :nop)
     (equal (ttype input-i) :normal)
     (equal (ttype input-i) :receive)
     (equal (ttype input-i) :start-checkpoint)

     (equal (ttype input-j) :nop)
     (equal (ttype input-j) :normal)
     (equal (ttype input-j) :receive)
     (equal (ttype input-j) :start-checkpoint))

    :in-theory
    (disable
     good-state-p
     recovery-free-state-p
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     no-recovery-step-p
     good-cut-meta-p
    ; legal-inputp
     process-cut-step
     system-step
     step-normal
     step-rcv
     step-checkpoint
     get-msg-from-channel
     cm-cut-not-taken-p))))




;; ------------------------------------------------------------
;; A POST process and a PRE process cannot be the same process.
;;
;; INPUT-I is already post-cut in M.
;;
;; INPUT-J is still pre-cut after PROCESS-CUT-STEP.  Since
;; PROCESS-CUT-STEP never adds a process back into
;; :CUT-NOT-TAKEN, INPUT-J was also pre-cut in M.
;;
;; Therefore PID(INPUT-I) and PID(INPUT-J) must be different.
;; ------------------------------------------------------------

(defthm
  post-pre-process-cut-step-implies-pids-different

  (implies
   (and
    ;; INPUT-I is POST in M.
    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))

    ;; INPUT-J is PRE after INPUT-I.
    (cm-cut-not-taken-p
     (process-cut-step input-i st m)
     (pid input-j)))

   (not
    (equal
     (pid input-i)
     (pid input-j))))
    :rule-classes
  ((:rewrite
    :match-free :all)))



;; ;; ------------------------------------------------------------
;; ;; A POST-CUT input followed by a PRE-CUT input is swappable
;; ;; in the implementation.
;; ;;
;; ;; M and ST describe the implementation immediately before
;; ;; INPUT-I.
;; ;;
;; ;; INPUT-I belongs to a process that has already taken the cut.
;; ;; INPUT-J belongs to a process that is still pre-cut after
;; ;; INPUT-I executes.
;; ;;
;; ;; The marker-in-transit invariant is the key fact used when
;; ;; moving a PRE-CUT receive backward across INPUT-I: if INPUT-I
;; ;; could have created the message needed by INPUT-J, the target
;; ;; marker separating the cut would already be ahead of that
;; ;; message on the relevant channel.
;; ;;
;; ;; The consistency and well-formedness invariants provide the
;; ;; metadata/implementation facts needed to interpret the cut
;; ;; status correctly.
;; ;; ------------------------------------------------------------


;; ------------------------------------------------------------
;; Starting condition for a local POST ; PRE swap.
;;
;; ST and M describe the implementation and cut metadata
;; immediately before INPUT-1 executes.
;;
;; INPUT-1 is already POST-cut.
;; INPUT-2 is still PRE-cut after INPUT-1 executes.
;;
;; The state satisfies the implementation/cut invariants,
;; begins recovery-free, and INPUT-1 ; INPUT-2 is the actual
;; legal checkpoint-body execution.
;; ------------------------------------------------------------

(defun cl-post-pre-swap-start-p
    (st m input-1 input-2)

  (let*
      ((m-after-1
        (process-cut-step
         input-1
         st
         m)))

    (and
     ;; Cut / implementation invariants.
     (cut-markers-in-transit-p
      m st)

     (cut-meta-imp-consistent-p
      m st)

     (good-cut-meta-p m)

     (good-state-p st)

     ;; We are outside recovery.
     (recovery-free-state-p st)

     ;; INPUT-1 ; INPUT-2 is the actual legal order.
     (legal-input-sequencep
      st
      (list input-1 input-2))

     ;; Both are checkpoint-body inputs.
     (cl-checkpoint-body-input-p
      input-1)

     (cl-checkpoint-body-input-p
      input-2)

     ;; INPUT-1 is POST-cut.
     (not
      (cm-cut-not-taken-p
       m
       (pid input-1)))

     ;; INPUT-2 is still PRE-cut immediately before it executes.
     (cm-cut-not-taken-p
     m-after-1
     (pid input-2)))))

;; Bridge from the cut-oriented hypothesis used by the global reordering
;; argument to the semantic independence contract used by the local
;; commutation library.  This is where the good-state, cut-consistency,
;; marker-in-transit, legality, and recovery-free assumptions are consumed.
(defthm cl-post-pre-two-imp-inputs-swappable-p
  (implies
   (cl-post-pre-swap-start-p
    st m input-1 input-2)

   (cl-two-imp-inputs-swappable-p
    st input-1 input-2))
  
  :hints
  (("Goal"
    :in-theory
    (disable
     process-cut-step
     recovery-free-state-p
     good-state-p
     legal-input-sequencep
     legal-inputp
     cm-cut-not-taken-p
     any-process-recovering-p
     append
     any-snapshot-checkpointing-p
     no-recovery-step-p
     system-step
     cl-checkpoint-body-input-p
     cut-markers-in-transit-p
     recovery-free-state-p)))
  :rule-classes
  ((:rewrite
    :match-free :all)))









;; Raw-channel adjacent-swap theorem.  Unlike the projection lemmas above,
;; this conclusion is exact equality: NOP is inert, normal sends commute by
;; source, legal receives remove fixed FIFO heads, and checkpoint starts
;; broadcast from distinct sources.
(defthm cl-two-imp-inputs-commute-channels
  (implies
   (cl-two-imp-inputs-swappable-p
    st input-1 input-2)

   (equal
    (channels
     (system-step
      (system-step st input-1)
      input-2))

    (channels
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    ;; Split the proof according to the implementation input types and use
    ;; the exact commutation facts established in the channel library.
    :in-theory
    (disable get-msg-from-channel
             remove-message-from-channel
	     start-checkpoint-helper
	     create-marker-message
	     update-proc-for-normal-msg-core
	    ; step-normal
	     )

    :cases
    ((equal (ttype input-1) :nop)
     (equal (ttype input-1) :normal)
     (equal (ttype input-1) :receive)
     (equal (ttype input-1) :start-checkpoint)

     (equal (ttype input-2) :nop)
     (equal (ttype input-2) :normal)
     (equal (ttype input-2) :receive)
     (equal (ttype input-2) :start-checkpoint)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Checkpoint-control commutation by input-type pair
;;
;; CL-CHECKPOINT-CONTROL-EQUIVALENT-P observes each process's COUNTER and
;; SNAPSHOT-IDS.  Unlike the visible-process and channel components, these
;; fields are intentionally modified by :start-checkpoint and marker
;; receives.  We therefore prove the interesting type pairs separately,
;; retain both orientations where a mixed pair is asymmetric syntactically,
;; and finish with one exhaustive dispatcher theorem.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;; A post-cut input and the following still-pre-cut input cannot belong to
;; the same process: PROCESS-CUT-STEP never makes an already-taken cut revert.
(defthm
  cl-post-pre-swap-start-implies-pids-different

  (implies
   (cl-post-pre-swap-start-p
    st m input-1 input-2)

   (not
    (equal
     (pid input-1)
     (pid input-2))))

  :hints
  (("Goal"
    :in-theory
     (disable
      process-cut-step
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-input-sequencep
      legal-inputp
      cl-checkpoint-body-input-p
      cm-cut-not-taken-p
      system-step))))




;; Exhaustive checkpoint-control dispatcher.  The body-input recognizers
;; restrict each input to NOP, NORMAL, RECEIVE, or START-CHECKPOINT; the case
;; lemmas above discharge all sixteen ordered pairs.  This theorem is the
;; checkpoint-control component consumed by the local state-equivalence
;; theorem immediately below.
(defthm
  cl-post-pre-two-imp-inputs-commute-checkpoint-control

    (implies
     (and 
   (cl-post-pre-swap-start-p
    st m input-1 input-2)
    (cl-checkpoint-body-input-p input-1)
    (cl-checkpoint-body-input-p input-2))


   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (run-imp
      st
      (list input-1 input-2)))

    (procs
     (run-imp
      st
      (list input-2 input-1)))))

 :otf-flg t

  :hints
  (("Goal"
    :in-theory
    (disable
     cl-post-pre-swap-start-p
     system-step
      step-rcv
      step-normal
      step-checkpoint
      process-cut-step
     ; recovery-free-state-p
      good-state-p
      good-cut-meta-p
      cut-meta-imp-consistent-p
     ; legal-input-sequencep
      legal-inputp
      cm-cut-not-taken-p
      ;cl-checkpoint-body-input-p
      cut-markers-in-transit-p
     ; cl-checkpoint-control-equivalent-p
      ))))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Local swap theorem under implementation-state equivalence
;;
;; The process, channel, and checkpoint-control results established above
;; are assembled here.  Thus, exchanging one adjacent post-cut/pre-cut pair
;; preserves every component observed by CL-STATE-EQUIVALENT-P.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  cl-post-pre-two-imp-inputs-commute-under-state-equivalence

  (implies
   (cl-post-pre-swap-start-p
    st m input-1 input-2)

   (cl-state-equivalent-p
    (run-imp
     st
     (list input-1 input-2))

    (run-imp
     st
     (list input-2 input-1))))

  :hints
  (("Goal"
    :use
    ((:instance
      cl-post-pre-two-imp-inputs-swappable-p)

     (:instance
      cl-two-imp-inputs-commute-under-procs-equivalence)

     (:instance
      cl-two-imp-inputs-commute-channels)

     (:instance
      cl-post-pre-two-imp-inputs-commute-checkpoint-control))

    :in-theory
    (disable
     cl-post-pre-swap-start-p
      cl-post-pre-two-imp-inputs-swappable-p
      system-step
      procs-equivalent-p
      cl-checkpoint-control-equivalent-p
      cl-checkpoint-body-input-p
      legal-inputp
      no-recovery-step-p
      recovery-free-state-p)))
      :rule-classes nil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Single-step preservation support library
;;
;; The final theorem in this book starts from two already equivalent
;; implementation states and executes the same checkpoint-body input in
;; both.  The lemmas below are grouped by the obligations generated by the
;; four clauses of CL-STATE-EQUIVALENT-P:
;;
;;   * recovery-free execution excludes impossible receive branches;
;;   * visible-process equivalence ignores checkpoint bookkeeping;
;;   * checkpoint-control equivalence ignores non-control bookkeeping and
;;     exposes COUNTER and SNAPSHOT-IDS at a selected member process.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main single-step preservation theorem
;;
;; Applying the same legal checkpoint-body input to two recovery-free,
;; CL-state-equivalent implementation states preserves CL state equivalence.
;; The proof covers :NOP, :NORMAL, :RECEIVE, and :START-CHECKPOINT through
;; CL-CHECKPOINT-BODY-INPUT-P and uses the support library above to abstract
;; from implementation-only snapshot and recovery bookkeeping.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  cl-state-equivalent-p-preserved-by-checkpoint-body-step

  (implies
   (and
    (cl-state-equivalent-p
     st-1
     st-2)

    (cl-checkpoint-body-input-p
     input)

    (recovery-free-state-p
     st-1)

    (recovery-free-state-p
     st-2)

    (legal-inputp
     st-1
     input)

    (legal-inputp
     st-2
     input))

   (cl-state-equivalent-p
    (system-step st-1 input)
    (system-step st-2 input))))



;; ------------------------------------------------------------
;; Equivalent states remain equivalent after executing the
;; same legal, recovery-free checkpoint-body postfix.
;; ------------------------------------------------------------

(defthm
  cl-state-equivalent-p-preserved-by-checkpoint-body-inputs

  (implies
   (and
    (cl-state-equivalent-p
     st-1
     st-2)

    (good-state-p st-1)
    (good-state-p st-2)

    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)

    (cl-checkpoint-body-inputs-p
     inputs)

    (legal-input-sequencep
     st-1
     inputs)

    (legal-input-sequencep
     st-2
     inputs))

   (cl-state-equivalent-p
    (run-imp st-1 inputs)
    (run-imp st-2 inputs)))

  :hints
  (("Goal"
    :in-theory
    (disable
     system-step
     legal-inputp
     good-state-p
     recovery-free-state-p
     cl-checkpoint-body-input-p
     cl-state-equivalent-p))))



(defthm cl-state-equivalent-p-reflexive
  (cl-state-equivalent-p st st))









(defthm
  cl-state-equivalent-p-preserves-legal-postfix

  (implies
   (and
    ;; States immediately after the original and swapped pairs.
    (cl-state-equivalent-p
     st-original
     st-after-swap)

    ;; State equivalence does not compare recovery status directly.
    (recovery-free-state-p
     st-original)

    (recovery-free-state-p
     st-after-swap)

    ;;Both are good states
    (good-state-p st-original)

    (good-state-p st-after-swap)

    ;; POSTFIX contains no :recover, :crash, or unknown inputs.
    (cl-checkpoint-body-inputs-p
     postfix)

    ;; The known original execution is legal.
    (legal-input-sequencep
     st-original
     postfix))

   ;; Therefore, the same postfix is legal after the swap.
   (legal-input-sequencep
    st-after-swap
    postfix))
  :hints (("Goal"
	  ; :induct (legal-input-sequencep st-after-swap postfix)
	   :in-theory (disable legal-inputp
			       cl-state-equivalent-p
			       recovery-free-state-p
			       good-state-p
			       system-step
			       cl-checkpoint-body-input-p)))
  :rule-classes
  ((:rewrite
    :match-free :all)))









(defthm
  cl-one-post-pre-swap-with-prefix-and-postfix

  (let*
      (;; State immediately before the adjacent pair.
       (swap-st
        (run-imp st prefix))

       ;; States immediately after the two possible pair orders.
       (original-pair-st
        (run-imp
         swap-st
         (list input-post input-pre)))

       (swapped-pair-st
        (run-imp
         swap-st
         (list input-pre input-post)))

       ;; Complete original and swapped sequences.
       (original-inputs
        (append (append prefix (list input-post input-pre)) postfix))
	 
       (swapped-inputs
        (append (append prefix (list input-pre input-post)) postfix)))

    (implies
     (and
      ;; Only the original complete execution is assumed legal.
      (legal-input-sequencep
       st
       original-inputs)

      ;; The adjacent pair is a valid post/pre inversion at SWAP-ST.
      ;; M-AT-SWAP is the metadata immediately before the pair.
      (cl-post-pre-swap-start-p
       swap-st
       m-at-swap
       input-post
       input-pre)

      ;; Required for propagating equivalence through POSTFIX.
      (cl-checkpoint-body-inputs-p
       postfix)

      ;; These are temporarily explicit because the postfix
      ;; theorems currently require them.
      (good-state-p original-pair-st)
      (good-state-p swapped-pair-st)

      (recovery-free-state-p original-pair-st)
      (recovery-free-state-p swapped-pair-st))
    ;; Both complete executions end in equivalent states.
    (cl-state-equivalent-p
       (run-imp st original-inputs)
       (run-imp st swapped-inputs))))
  :hints
(("Goal"
  :do-not-induct t

  :use
  ((:instance
    cl-post-pre-two-imp-inputs-commute-under-state-equivalence
    (st
     (run-imp st prefix))
    (m
     m-at-swap)
    (input-1
     input-post)
    (input-2
     input-pre))

   (:instance
    legal-input-sequencep-of-append-implies-second
    (st
     st)
    (inputs-1
     (append
      prefix
      (list input-post input-pre)))
    (inputs-2
     postfix))

   (:instance
    cl-state-equivalent-p-preserved-by-postfix

    (st-original
     (run-imp
      (run-imp st prefix)
      (list input-post input-pre)))

    (st-after-swap
     (run-imp
      (run-imp st prefix)
      (list input-pre input-post)))

    (postfix
     postfix)))

  :in-theory
  (e/d
   (run-imp-of-append)

   (append
    run-imp
    recovery-free-state-p
    good-state-p
    cl-checkpoint-body-inputs-p
    cl-post-pre-swap-start-p
    legal-input-sequencep
    cl-state-equivalent-p

;    cl-post-pre-two-imp-inputs-commute-under-state-equivalence
    legal-input-sequencep-of-append-implies-second
    cl-state-equivalent-p-preserved-by-postfix)))))











(defthm
  cl-one-post-pre-swap-with-prefix-and-postfix-final

  (let*
      (;; State immediately before the adjacent pair.
       (swap-st
        (run-imp st prefix))

       ;; Complete original and swapped sequences.
       (original-inputs
        (append
         (append prefix
                 (list input-post input-pre))
         postfix))

       (swapped-inputs
        (append
         (append prefix
                 (list input-pre input-post))
         postfix)))

    (implies
     (and
      ;; Only the original complete execution is assumed legal.
      (legal-input-sequencep
       st
       original-inputs)

      ;; The adjacent pair is a valid POST/PRE inversion.
      (cl-post-pre-swap-start-p
       swap-st
       m-at-swap
       input-post
       input-pre)

      ;; The common suffix contains only checkpoint-body inputs.
      (cl-checkpoint-body-inputs-p
       postfix))

     ;; Both complete executions end in equivalent states.
     (cl-state-equivalent-p
      (run-imp st original-inputs)
      (run-imp st swapped-inputs))))

  :hints
  (("Goal"
    :do-not-induct t

    :use
    (;; Local POST/PRE swap preserves state equivalence.
     (:instance
      cl-post-pre-two-imp-inputs-commute-under-state-equivalence
      (st
       (run-imp st prefix))
      (m
       m-at-swap)
      (input-1
       input-post)
      (input-2
       input-pre))

     ;; The swap-start condition also guarantees that both
     ;; pair-result states are good and recovery-free.
     (:instance
      cl-post-pre-swap-start-implies-pair-states-good-and-recovery-free
      (st
       (run-imp st prefix))
      (m
       m-at-swap)
      (input-1
       input-post)
      (input-2
       input-pre))

     ;; Legality of the entire original execution gives legality
     ;; of POSTFIX from the original pair-result state.
     (:instance
      legal-input-sequencep-of-append-implies-second
      (st
       st)
      (inputs-1
       (append
        prefix
        (list input-post input-pre)))
      (inputs-2
       postfix))

     ;; Propagate pair-state equivalence through the common POSTFIX.
     (:instance
      cl-state-equivalent-p-preserved-by-postfix

      (st-original
       (run-imp
        (run-imp st prefix)
        (list input-post input-pre)))

      (st-after-swap
       (run-imp
        (run-imp st prefix)
        (list input-pre input-post)))

      (postfix
       postfix)))

    :in-theory
    (e/d
     (run-imp-of-append)

     (append
      run-imp
      recovery-free-state-p
      good-state-p
      cl-checkpoint-body-inputs-p
      cl-post-pre-swap-start-p
      legal-input-sequencep
      cl-state-equivalent-p

      cl-post-pre-swap-start-implies-pair-states-good-and-recovery-free
      legal-input-sequencep-of-append-implies-second
      cl-state-equivalent-p-preserved-by-postfix)))))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DYNAMIC INVERSION COUNT
;;
;; INPUTS is executed from left to right using the current ST and M.
;;
;; NUMBER-OF-AFTER-CUT-INPUTS-SEEN records how many earlier inputs were
;; classified as after-cut.
;;
;; Whenever a before-cut input is encountered, it forms one inversion with
;; every earlier after-cut input. Therefore, the accumulator is added to
;; the result.
;;
;; Initial call:
;;
;;     (inversion-count st m inputs 0)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; COUNT BEFORE-CUT INPUTS IN AN EXECUTION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun number-of-before-cut-inputs
    (st m inputs)

  (declare
   (xargs
    :measure
    (acl2-count inputs)))

  (if (endp inputs)

      0

    (let* ((input
            (first inputs))

           ;; Classify INPUT before executing it.
           (before-cut-input-p
            (cm-cut-not-taken-p
             m
             (g :pid input)))

           (next-st
            (system-step
             st
             input))

           (next-m
            (process-cut-step
             input
             st
             m)))

      (if before-cut-input-p

          (+
           1

           (number-of-before-cut-inputs
            next-st
            next-m
            (rest inputs)))

        (number-of-before-cut-inputs
         next-st
         next-m
         (rest inputs))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; COUNT AFTER-CUT / BEFORE-CUT INVERSIONS
;;
;; If the first input is after-cut, every before-cut input in the suffix
;; forms an inversion with it.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun inversion-count
    (st m inputs)

  (declare
   (xargs
    :measure
    (acl2-count inputs)))

  (if (endp inputs)

      0

    (let* ((input
            (first inputs))

           ;; Classify INPUT before executing it.
           (before-cut-input-p
            (cm-cut-not-taken-p
             m
             (g :pid input)))

           (next-st
            (system-step
             st
             input))

           (next-m
            (process-cut-step
             input
             st
             m))

           (suffix
            (rest inputs)))

      (+
       ;; If INPUT is after-cut, count all later before-cut inputs.
       (if before-cut-input-p
           0
         (number-of-before-cut-inputs
          next-st
          next-m
          suffix))

       ;; Count inversions whose first input occurs in the suffix.
       (inversion-count
        next-st
        next-m
        suffix)))))


(defthm
  natp-of-inversion-count

  (natp
   (inversion-count
    st
    m
    inputs))

  :hints
  (("Goal"
    :induct
    (inversion-count
     st
     m
     inputs))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SWAP THE FIRST ADJACENT POST/PRE PAIR
;;
;; The returned sequence is explicitly constructed using APPEND so that its
;; form matches CL-ONE-POST-PRE-SWAP-WITH-PREFIX-AND-POSTFIX-FINAL.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun swap-first-after-before
    (st m inputs)

  (declare
   (xargs
    :measure
    (acl2-count inputs)))

  ;; Fewer than two inputs means no adjacent pair exists.
  (if (or
       (endp inputs)
       (endp (rest inputs)))

      inputs

    (let* ((input-post
            (first inputs))

           (input-pre
            (second inputs))

           (postfix
            (rest
             (rest inputs))))

      (if
       (cl-post-pre-swap-start-p
        st
        m
        input-post
        input-pre)

       (append
        (list input-pre input-post)
        postfix)
       (append
        (list input-post)

        (swap-first-after-before
         (system-step
          st
          input-post)

         (process-cut-step
          input-post
          st
          m)

         (rest inputs)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; REPEATEDLY REORDER THE COMPLETE RAW INPUT SEQUENCE
;;
;; Every iteration:
;;
;;   1. Calculates the inversion count by executing the current sequence
;;      from the supplied initial ST and M.
;;
;;   2. Exchanges the first adjacent pair satisfying
;;      CL-POST-PRE-SWAP-START-P.
;;
;;   3. Restarts from the same initial ST and M on the complete updated
;;      input sequence.
;;
;; The explicit decrease test makes the recursive measure visible to ACL2.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun reorder-inputs
    (st m inputs)

  (declare
   (xargs
    :measure
    (inversion-count
     st m inputs)

    :hints
    (("Goal"
      :in-theory
      (disable
       inversion-count
       swap-first-after-before)))))

  (let ((current-count
         (inversion-count
          st m inputs)))

    (if (zp current-count)

        inputs

      (let* ((next-inputs
              (swap-first-after-before
               st m inputs))

             (next-count
              (inversion-count
               st m next-inputs)))

        (if (< next-count current-count)

            (reorder-inputs
             st m next-inputs)

          inputs)))))




(defthm
  front-post-pre-swap-start-implies-swapped-postfix-legal

  (implies
   (and
    (consp inputs)
    (consp (rest inputs))

    (cl-post-pre-swap-start-p
     st
     m
     (first inputs)
     (second inputs))

    (legal-input-sequencep
     st inputs)

    (cl-checkpoint-body-inputs-p
     inputs))

   (legal-input-sequencep

    ;; State after executing the swapped pair.
    (run-imp
     st
     (list
      (second inputs)
      (first inputs)))

    ;; Common postfix.
    (rest
     (rest inputs))))

  :hints
  (("Goal"
    :do-not-induct t

    :use
    (;; The original and swapped pair-result states are equivalent.
     (:instance
      front-post-pre-swap-start-implies-state-equivalent

      (st st)
      (m m)
      (inputs inputs))

     ;; Both pair-result states are good and recovery-free.
     (:instance
      cl-post-pre-swap-start-implies-pair-states-good-and-recovery-free

      (st st)
      (m m)

      (input-1
       (first inputs))

      (input-2
       (second inputs)))

     ;; Original complete legality gives postfix legality after
     ;; executing the original pair.
     (:instance
      legal-input-sequencep-of-append-implies-second

      (st st)

      (inputs-1
       (list
        (first inputs)
        (second inputs)))

      (inputs-2
       (rest
        (rest inputs))))

     ;; Transfer postfix legality to the swapped pair-result state.
     (:instance
      cl-state-equivalent-p-preserves-legal-postfix

      (st-original
       (run-imp
        st
        (list
         (first inputs)
         (second inputs))))

      (st-after-swap
       (run-imp
        st
        (list
         (second inputs)
         (first inputs))))

      (postfix
       (rest
        (rest inputs)))))

    :in-theory
    (e/d
     (;; Extract the body-input property of CDDR INPUTS.
      cl-checkpoint-body-inputs-p)

     (;; Keep semantic definitions closed.
      cl-post-pre-swap-start-p
      cl-state-equivalent-p
      good-state-p
      recovery-free-state-p
      legal-input-sequencep
      legal-inputp
      run-imp
      system-step
      process-cut-step

      ;; These rules are instantiated explicitly above.
      front-post-pre-swap-start-implies-state-equivalent
      cl-post-pre-swap-start-implies-pair-states-good-and-recovery-free
      legal-input-sequencep-of-append-implies-second
      cl-state-equivalent-p-preserves-legal-postfix)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LEGALITY OF A SELECTED PAIR AT THE FRONT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  front-post-pre-swap-preserves-legal-input-sequencep

  (implies
   (and
    (consp inputs)
    (consp (rest inputs))

    (cl-post-pre-swap-start-p
     st
     m
     (first inputs)
     (second inputs))

    (legal-input-sequencep
     st inputs)

    (cl-checkpoint-body-inputs-p
     inputs))

   (legal-input-sequencep
    st
    (append
     (list
      (second inputs)
      (first inputs))

     (rest
      (rest inputs)))))

    :hints
  (("Goal"
    :do-not-induct t

    :use
    (;; Legality of the swapped two-input prefix.
     (:instance
      front-post-pre-swap-start-implies-swapped-pair-legal

      (st st)
      (m m)
      (inputs inputs))

     ;; Legality of the postfix from the state reached after
     ;; executing the swapped pair.
     (:instance
      front-post-pre-swap-start-implies-swapped-postfix-legal

      (st st)
      (m m)
      (inputs inputs))

     ;; Combine the legal swapped pair and legal postfix.
     (:instance
      legal-input-sequencep-of-append-if

      (st st)

      (inputs-1
       (list
        (second inputs)
        (first inputs)))

      (inputs-2
       (rest
        (rest inputs)))))

    :in-theory
    (disable
     cl-checkpoint-body-inputs-p
     legal-input-sequencep
     cl-post-pre-swap-start-p
     run-imp

     front-post-pre-swap-start-implies-swapped-pair-legal
     front-post-pre-swap-start-implies-swapped-postfix-legal
     legal-input-sequencep-of-append-if)))
    :rule-classes
  ((:rewrite
    :match-free :all)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; THE COMPLETE ONE-SWAP SCAN PRESERVES LEGALITY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  legal-input-sequencep-of-swap-first-after-before

  (implies
   (and
    (legal-input-sequencep
     st inputs)

    (cl-checkpoint-body-inputs-p
     inputs))

   (legal-input-sequencep
    st
    (swap-first-after-before
     st m inputs))))


(defthm
  swap-first-after-before-preserves-run

  (implies
   (and
    (legal-input-sequencep
     st inputs)

    (cl-checkpoint-body-inputs-p
     inputs))

   (cl-state-equivalent-p

    (run-imp
     st inputs)

    (run-imp
     st
     (swap-first-after-before
      st m inputs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TRANSITIVITY OF VISIBLE-PROCESS EQUIVALENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  cl-procs-equivalent-p-transitive

  (implies
   (and
    (procs-equivalent-p
     ids
     procs-1
     procs-2)

    (procs-equivalent-p
     ids
     procs-2
     procs-3))

   (procs-equivalent-p
    ids
    procs-1
    procs-3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TRANSITIVITY OF CHECKPOINT-CONTROL EQUIVALENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  cl-checkpoint-control-equivalent-p-transitive

  (implies
   (and
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2)

    (cl-checkpoint-control-equivalent-p
     ids
     procs-2
     procs-3))

   (cl-checkpoint-control-equivalent-p
    ids
    procs-1
    procs-3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TRANSITIVITY OF CL-STATE-EQUIVALENT-P
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  cl-state-equivalent-p-transitive

  (implies
   (and
    (cl-state-equivalent-p
     st-1
     st-2)

    (cl-state-equivalent-p
     st-2
     st-3))

   (cl-state-equivalent-p
    st-1
    st-3))
      :rule-classes
  ((:rewrite
    :match-free :all)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MAIN REORDER THEOREM
;;
;; Repeatedly exchanging dynamically selected after-cut / before-cut pairs
;; preserves the final implementation state up to CL-STATE-EQUIVALENT-P.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  reorder-inputs-preserves-run

  (implies
   (and
    (true-listp inputs)

    (cut-markers-in-transit-p
     m st)

    (cut-meta-imp-consistent-p
     m st)

    (good-cut-meta-p
     m)

    (good-state-p
     st)

    (recovery-free-state-p
     st)

    (legal-input-sequencep
     st inputs)

    (cl-checkpoint-body-inputs-p
     inputs))

   (cl-state-equivalent-p
    (run-imp
     st inputs)
    (run-imp
     st
     (reorder-inputs
      st m inputs)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; COLLECT THE BEFORE-CUT INPUTS
;;
;; Each input is classified using the current cut metadata.  ST and M are
;; then advanced before the remaining inputs are examined.
;;
;; The relative order of all before-cut inputs is preserved.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun before-cut-inputs (st m inputs)
  (declare
   (xargs
    :measure
    (acl2-count inputs)))

  (if (endp inputs)

      nil

    (let* ((input
            (first inputs))

           ;; Classify INPUT before advancing the metadata.
           (before-cut-p
            (cm-cut-not-taken-p
             m
             (pid input)))

           (next-st
            (system-step
             st
             input))

           (next-m
            (process-cut-step
             input
             st
             m))

           (remaining-before-cut-inputs
            (before-cut-inputs
             next-st
             next-m
             (rest inputs))))

      (if before-cut-p

          (cons
           input
           remaining-before-cut-inputs)

        remaining-before-cut-inputs))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; COLLECT THE AFTER-CUT INPUTS
;;
;; An input is after-cut when its process has already taken the cut in the
;; metadata immediately before that input executes.
;;
;; The relative order of all after-cut inputs is preserved.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun after-cut-inputs (st m inputs)
  (declare
   (xargs
    :measure
    (acl2-count inputs)))

  (if (endp inputs)

      nil

    (let* ((input
            (first inputs))

           ;; Classify INPUT before advancing the metadata.
           (before-cut-p
            (cm-cut-not-taken-p
             m
             (pid input)))

           (next-st
            (system-step
             st
             input))

           (next-m
            (process-cut-step
             input
             st
             m))

           (remaining-after-cut-inputs
            (after-cut-inputs
             next-st
             next-m
             (rest inputs))))

      (if before-cut-p

          remaining-after-cut-inputs

        (cons
         input
         remaining-after-cut-inputs)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CROSS-STATE PRESERVATION OF CUT-META CONSISTENCY
;;
;; PROCESS-CUT-STEP computed using ST-1 is equal to the one computed
;; using the equivalent state ST-2. Therefore, the ordinary preservation
;; theorem for ST-2 establishes consistency with SYSTEM-STEP of ST-2.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  cut-meta-imp-consistent-p-preserved-by-equivalent-state-step

  (implies
   (and
    (cl-state-equivalent-p
     st-1 st-2)

    (cut-markers-in-transit-p
     m st-1)

    (cut-markers-in-transit-p
     m st-2)

    (cut-meta-imp-consistent-p
     m st-1)

    (cut-meta-imp-consistent-p
     m st-2)

    (good-cut-meta-p m)

    (good-state-p st-1)

    (good-state-p st-2)

    (recovery-free-state-p st-1)

    (recovery-free-state-p st-2)

    (legal-inputp st-1 input)

    (legal-inputp st-2 input)

    (cl-checkpoint-body-input-p input))

   (cut-meta-imp-consistent-p

    ;; Metadata computed from ST-1.
    (process-cut-step
     input st-1 m)

    ;; Implementation state computed from ST-2.
    (system-step
     st-2 input))))




(defthm
  number-of-before-cut-inputs-equal-for-equivalent-states

  (implies
   (and
    (cl-state-equivalent-p
     st-1 st-2)

    ;; The same metadata agrees with both states.
    (cut-markers-in-transit-p
     m st-1)

    (cut-markers-in-transit-p
     m st-2)

    (cut-meta-imp-consistent-p
     m st-1)

    (cut-meta-imp-consistent-p
     m st-2)

    (good-cut-meta-p m)

    (good-state-p st-1)
    (good-state-p st-2)

    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)

    (true-listp postfix)

    (legal-input-sequencep
     st-1 postfix)

    (legal-input-sequencep
     st-2 postfix)

    (cl-checkpoint-body-inputs-p
     postfix))

   (equal
    (number-of-before-cut-inputs
     st-1 m postfix)

    (number-of-before-cut-inputs
     st-2 m postfix))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Now we start proving commutivity of process-cut-step under swap-start condition. This
;; means, meta-data produced while scanning a (after-before) pair is equal to the meta-data
;; produced by swapping the pair. We first prove supporting lemmas, then prove lemma.
;; We prove it under checkpoint-body-input-p of before-after inputs, lets us exclude
;; one :recover input which is not applicable in our proof scope.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PROCESS-CUT-STEP COMMUTES FOR ONE POST-CUT / BEFORE-CUT SWAP
;;
;; Original order:
;;
;;     INPUT-POST, INPUT-PRE
;;
;; Swapped order:
;;
;;     INPUT-PRE, INPUT-POST
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  cl-post-pre-two-process-cut-steps-commute

    (implies
     (and
      (cl-post-pre-swap-start-p
       st
       m
       input-post
       input-pre)
      (cl-checkpoint-body-input-p input-post)
      (cl-checkpoint-body-input-p input-pre))

   (equal

    ;; Metadata after the original POST/PRE order.
    (process-cut-step
     input-pre

     (system-step
      st
      input-post)

     (process-cut-step
      input-post
      st
      m))

    ;; Metadata after the swapped PRE/POST order.
    (process-cut-step
     input-post

     (system-step
      st
      input-pre)

     (process-cut-step
      input-pre
      st
      m)))))




(defthm
  number-of-before-cut-inputs-after-post-pre-pair-commutes

  (let* (;; Original order: POST, PRE.
         (st-after-post
          (system-step st input-post))

         (m-after-post
          (process-cut-step
           input-post st m))

         (st-after-post-pre
          (system-step
           st-after-post
           input-pre))

         (m-after-post-pre
          (process-cut-step
           input-pre
           st-after-post
           m-after-post))

         ;; Swapped order: PRE, POST.
         (st-after-pre
          (system-step st input-pre))

         (m-after-pre
          (process-cut-step
           input-pre st m))

         (st-after-pre-post
          (system-step
           st-after-pre
           input-post))

         (m-after-pre-post
          (process-cut-step
           input-post
           st-after-pre
           m-after-pre)))

    (implies
     (and
      (cl-post-pre-swap-start-p
       st m input-post input-pre)

      (true-listp postfix)

      (legal-input-sequencep
       st
       (append
        (list input-post input-pre)
        postfix))

      (cl-checkpoint-body-inputs-p
       (append
        (list input-post input-pre)
        postfix)))

     (equal
      ;; Suffix count after PRE, POST.
      (number-of-before-cut-inputs
       st-after-pre-post
       m-after-pre-post
       postfix)

      ;; Suffix count after POST, PRE.
      (number-of-before-cut-inputs
       st-after-post-pre
       m-after-post-pre
       postfix)))))
 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ONE SWAP PRESERVES THE NUMBER OF BEFORE-CUT INPUTS
;;
;; SWAP-FIRST-AFTER-BEFORE only changes the order of one after-cut and one
;; before-cut input. It neither creates nor removes a before-cut input.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  number-of-before-cut-inputs-of-swap-first-after-before

  (implies
   (and
    (true-listp inputs)

    (cut-markers-in-transit-p
     m st)

    (cut-meta-imp-consistent-p
     m st)

    (good-cut-meta-p
     m)

    (good-state-p
     st)

    (recovery-free-state-p
     st)

    (legal-input-sequencep
     st inputs)

    (cl-checkpoint-body-inputs-p
     inputs))

   (equal
    (number-of-before-cut-inputs
     st
     m
     (swap-first-after-before
      st m inputs))

    (number-of-before-cut-inputs
     st m inputs))))





(defthm
  positive-inversion-count-implies-swap-decreases

  (implies
   (and
    (not
     (zp
      (inversion-count st m inputs)))

    (true-listp inputs)

    (cut-markers-in-transit-p m st)

    (cut-meta-imp-consistent-p m st)

    (good-cut-meta-p m)

    (good-state-p st)

    (recovery-free-state-p st)

    (legal-input-sequencep
     st inputs)

    (cl-checkpoint-body-inputs-p
     inputs))

   (<
    (inversion-count
     st m
     (swap-first-after-before
      st m inputs))

    (inversion-count
     st m inputs))))





(defthm
  cut-partition-of-swap-first-after-before

  (implies
   (and
    (true-listp inputs)

    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)

    (legal-input-sequencep
     st inputs)

    (cl-checkpoint-body-inputs-p
     inputs))

   (equal
    (append
     (before-cut-inputs
      st
      m
      (swap-first-after-before
       st m inputs))

     (after-cut-inputs
      st
      m
      (swap-first-after-before
       st m inputs)))

    (append
     (before-cut-inputs
      st m inputs)

     (after-cut-inputs
      st m inputs)))))



(defthm
  reorder-inputs-returns-before-append-after

  (implies
   (and
    (true-listp inputs)

    (cut-markers-in-transit-p m st)

    (cut-meta-imp-consistent-p m st)

    (good-cut-meta-p m)

    (good-state-p st)

    (recovery-free-state-p st)

    (legal-input-sequencep
     st inputs)

    (cl-checkpoint-body-inputs-p
     inputs))

   (equal
    (reorder-inputs
     st m inputs)

    (append
     (before-cut-inputs
      st m inputs)

     (after-cut-inputs
      st m inputs)))))
