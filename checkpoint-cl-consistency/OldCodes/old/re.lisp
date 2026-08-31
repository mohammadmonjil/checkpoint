(in-package "ACL2")

(include-book "model")
(include-book "scan")
(include-book "good_state_invariants")
(include-book "channel_equivalence")
(include-book "basic")
(include-book "cfinvariants")
(include-book "rec")
(include-book "good_meta_invariants")

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

;; Original channel-wise table:
;;
;; receiver i -> sender j -> open-channel post-cut receive inputs.
(defun cl-checkpoint-segment-channel-after-cut-inputs
    (st input-seg)
  (cm-inputs-after-cut
   (cl-checkpoint-segment-meta st input-seg)))

;; Point accessor for the receiver-I / sender-J entry of the table above.
(defun cl-checkpoint-segment-channel-after-cut-input-get
    (st input-seg i j)
  (cm-after-cut-get
   (cl-checkpoint-segment-meta st input-seg)
   i
   j))

;; Original channel-wise table of actual normal messages consumed by
;; the open-channel post-cut receive inputs.
(defun cl-checkpoint-segment-after-cut-msgs (st input-seg)
  (cm-after-cut-msgs
   (cl-checkpoint-segment-meta st input-seg)))

;; Point accessor for the normal messages attributed to channel J -> I.
(defun cl-checkpoint-segment-after-cut-msg-get
    (st input-seg i j)
  (cm-after-cut-msg-get
   (cl-checkpoint-segment-meta st input-seg)
   i
   j))

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
;; Channel algebra for independent implementation steps
;;
;; Channels are stored as a nested receiver/sender record.  The lemmas in
;; this section expose the small algebraic facts needed by the case split on
;; two input types.  They are intentionally stated below SYSTEM-STEP so the
;; main commutation proofs do not repeatedly expand the entire transition
;; relation.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Updates to rows belonging to distinct senders commute, even when their
;; destination keys happen to be equal.
(defthm cl-channel-updates-different-senders-commute
  (implies
   (not (equal i1 i2))

   (equal
    (>channel
     i2 dst2 val2
     (>channel
      i1 dst1 val1
      channels))

    (>channel
     i1 dst1 val1
     (>channel
      i2 dst2 val2
      channels))))

  :hints
  (("Goal"
    :cases
    ((equal dst1 dst2)))))

;; A compute-message send from I2 cannot disturb a separately installed
;; channel value whose sender is I1.  This one-sided transport rule is used
;; to normalize nested channel updates before applying commutativity.
(defthm cl-send-compute-message-preserves-other-sender-update
  (implies
   (not (equal i1 i2))

   (equal
    (send-compute-message
     local2
     i2
     nbrs2
     (s dst
        (s i1 val
           (g dst channels))
        channels))

    (s dst
       (s i1 val
          (g dst
             (send-compute-message
              local2
              i2
              nbrs2
              channels)))
       (send-compute-message
        local2
        i2
        nbrs2
        channels)))))

;; Two normal compute sends from different processes may be exchanged
;; without changing the concrete channel table.
(defthm cl-send-compute-message-different-senders-commute
  (implies
   (not (equal i1 i2))

   (equal
    (send-compute-message
     local2
     i2
     nbrs2
     (send-compute-message
      local1
      i1
      nbrs1
      channels))

    (send-compute-message
     local1
     i1
     nbrs1
     (send-compute-message
      local2
      i2
      nbrs2
      channels)))))

;; Normal application execution changes process and channel contents but not
;; the universe or order of process identifiers.
(defthm proc-ids-of-step-normal
  (equal
   (proc-ids
   (step-normal st i))
   (proc-ids st)))

;; Starting a checkpoint at I2 commutes with replacing the distinct process
;; slot I1.  This isolates the process-table part of mixed normal/start cases.
(defthm cl-start-checkpoint-helper-commutes-with-other-proc-update
  (implies
   (not (equal i1 i2))

   (equal
    (start-checkpoint-helper
     (s i1 p1 procs)
     i2)

    (s i1
       p1
       (start-checkpoint-helper
        procs
        i2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Projection lemmas for marker traffic
;;
;; The concrete implementation carries checkpoint markers in its channels,
;; whereas the specification projection retains only application messages.
;; The following lifting chain proves marker invisibility at the channel,
;; row, and whole-table levels, then combines it with a normal compute send.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Projecting one concrete channel erases a marker appended by broadcast.
(defthm cl-project-channel-msgs-marker-send-invisible
  (implies
   (equal (msg-type msg) :marker)

   (equal
    (project-channel-msgs-to-spec
     (channel-state
      src
      dst
      (send-msg-all-outgoing-channels
       msg i nbrs channels)))

    (project-channel-msgs-to-spec
     (channel-state
      src
      dst
     channels)))))

;; Lift marker invisibility from one channel to one destination row.
(defthm cl-project-channel-row-marker-send-invisible
  (implies
   (equal (msg-type msg) :marker)

   (equal
    (project-channel-row-to-spec
     srcs
     dst
     (send-msg-all-outgoing-channels
      msg i nbrs channels))

    (project-channel-row-to-spec
     srcs
     dst
     channels))))

;; Lift marker invisibility once more to the complete projected channel map.
(defthm cl-project-channels-marker-send-invisible
  (implies
   (equal (msg-type msg) :marker)

   (equal
    (project-channels-to-spec-aux
     dsts
     srcs
     (send-msg-all-outgoing-channels
      msg i nbrs channels))

    (project-channels-to-spec-aux
     dsts
     srcs
     channels))))

;; A broadcast sent by I2 leaves every channel whose sender is I1 unchanged.
(defthm channel-state-of-send-msg-all-other-sender
  (implies
   (not (equal i1 i2))

   (equal
    (channel-state
     i1
     dst
     (send-msg-all-outgoing-channels
      msg i2 nbrs2 channels))

    (channel-state
     i1
     dst
     channels))))

;; Consequently, a broadcast by I2 commutes with an explicit update to an
;; I1-originating channel when I1 and I2 are distinct.
(defthm send-msg-all-outgoing-commutes-with-other-sender-update
  (implies
   (not (equal i1 i2))

   (equal
    (send-msg-all-outgoing-channels
     msg
     i2
     nbrs2
     (>channel i1 dst val channels))

    (>channel
     i1
     dst
     val
     (send-msg-all-outgoing-channels
      msg
      i2
      nbrs2
      channels)))))

;; A normal send from I1 followed by a marker broadcast from I2 has the same
;; projected destination row as the normal send alone.
(defthm cl-project-channel-row-send-compute-marker-invisible
  (implies
   (and
    (not (equal i1 i2))
    (equal (msg-type msg) :marker))

   (equal
    (project-channel-row-to-spec
     srcs dst
     (send-compute-message
      local i1 nbrs1
      (send-msg-all-outgoing-channels
       msg i2 nbrs2 channels)))

    (project-channel-row-to-spec
     srcs dst
     (send-compute-message
      local i1 nbrs1 channels)))))

;; Whole-table version of the preceding row lemma.  Keeping this as a named
;; lifting fact prevents recursive projection definitions from leaking into
;; the mixed normal/start commutation proof.
(defthm cl-project-send-compute-marker-invisible
 (implies
    (and
    (not (equal i1 i2))
    (equal (msg-type msg) :marker))

   (equal
    (project-channels-to-spec-aux
     dsts
     srcs
     (send-compute-message
      local
      i1
      nbrs1
      (send-msg-all-outgoing-channels
       msg i2 nbrs2 channels)))

    (project-channels-to-spec-aux
     dsts
     srcs
     (send-compute-message
      local
      i1
      nbrs1
      channels))))
  :hints (("Goal"
	   :in-theory (disable send-msg-all-outgoing-channels
			       send-compute-message))))

;; At the specification-channel level, a normal send and a marker broadcast
;; by different processes commute.  Projection is essential here because
;; marker traffic is intentionally absent from the specification.
(defthm cl-project-channels-normal-send-marker-send-commute
  (implies
   (and
    (not (equal i1 i2))
    (equal (msg-type msg) :marker))

   (equal
    ;; Normal send from I1 first, then marker sends from I2.
    (project-channels-to-spec-aux
     ids
     ids
     (send-msg-all-outgoing-channels
      msg
      i2
      nbrs2
      (send-compute-message
       local1
       i1
       nbrs1
       channels)))

    ;; Marker sends from I2 first, then normal send from I1.
    (project-channels-to-spec-aux
     ids
     ids
     (send-compute-message
      local1
      i1
      nbrs1
      (send-msg-all-outgoing-channels
       msg
       i2
       nbrs2
       channels))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FIFO-head and receive-removal facts
;;
;; Sends append to a FIFO while receives remove its head.  These lemmas make
;; the append/remove reasoning explicit, including the nonempty side
;; conditions that ensure an append cannot change the message consumed by a
;; legal receive.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Appending an element to a nonempty list preserves its existing head.
(defthm car-of-snoc-when-consp
  (implies
   (consp x)
   (equal
    (car (snoc x e))
    (car x))))

;; Hence a compute send cannot change the message currently available on a
;; nonempty channel, whether or not that channel is one of the send targets.
(defthm get-msg-from-channel-of-send-compute-message-when-consp
  (implies
   (consp
    (channel-state src dst channels))

   (equal
    (get-msg-from-channel
     src
     dst
     (send-compute-message
      local i nbrs channels))

    (get-msg-from-channel
     src
     dst
     channels))))

;; Removing the old head and appending compute traffic commute on a nonempty
;; channel.  This is the concrete channel equality needed for normal/receive.
(defthm remove-message-from-channel-of-send-compute-message
  (implies
   (consp
    (channel-state sender receiver channels))

   (equal
    (remove-message-from-channel
     sender
     receiver
     (send-compute-message
      local
      normal-i
      nbrs
      channels))

    (send-compute-message
     local
     normal-i
     nbrs
     (remove-message-from-channel
      sender
      receiver
      channels)))))

;; Broadcasting can only append; it cannot make an existing channel empty.
(defthm channel-consp-after-send-msg-all-outgoing
  (implies
   (consp (channel-state src dst channels))

   (consp
    (channel-state
     src
     dst
     (send-msg-all-outgoing-channels
      msg i nbrs channels)))))

;; A marker or recovery broadcast also preserves the head of every channel
;; that was already nonempty.
(defthm get-msg-from-channel-of-send-msg-all-outgoing-when-consp
  (implies
   (consp
    (channel-state
     src
     dst
     channels))

   (equal
    (get-msg-from-channel
     src
     dst
     (send-msg-all-outgoing-channels
      msg
      i
      nbrs
      channels))

    (get-msg-from-channel
     src
     dst
     channels))))

;; Boolean/non-NIL form of nonemptiness preservation, useful after ACL2 has
;; simplified a CONSP fact into a truth test on CHANNEL-STATE.
(defthm channel-nonempty-after-send-msg-all-outgoing
  (implies
   (consp
    (channel-state src dst channels))

   (channel-state
    src
    dst
    (send-msg-all-outgoing-channels
     msg i nbrs channels))))

;; Receiving at destination DST commutes with a broadcast originating from a
;; different process I, provided the received channel already has a head.
(defthm remove-message-from-channel-of-send-msg-all-outgoing-when-consp
    (implies
     (and
      (not (equal dst i))
      (consp (channel-state src dst channels)))

   (equal
    (remove-message-from-channel
     src
     dst
     (send-msg-all-outgoing-channels
      msg i nbrs channels))

    (send-msg-all-outgoing-channels
     msg
     i
     nbrs
     (remove-message-from-channel
      src dst channels)))))

;; A receive removal at DST1 cannot affect the head observed at DST2.
(defthm get-msg-from-channel-of-remove-message-different-dst
  (implies
   (not (equal dst1 dst2))

   (equal
    (get-msg-from-channel
     src2
     dst2
     (remove-message-from-channel
      src1
      dst1
      channels))

    (get-msg-from-channel
     src2
     dst2
     channels))))

;; Two receives addressed to distinct processes modify distinct destination
;; rows and therefore commute exactly.
(defthm remove-message-from-channel-different-dsts-commute
  (implies
   (not (equal dst1 dst2))

   (equal
    (remove-message-from-channel
     src1
     dst1
     (remove-message-from-channel
      src2
      dst2
      channels))

    (remove-message-from-channel
     src2
     dst2
     (remove-message-from-channel
      src1
      dst1
      channels)))))

;; The process-table helper used by two independent checkpoint starts is
;; itself commutative at distinct process identifiers.
(defthm start-checkpoint-helper-different-pids-commute
  (implies
   (not (equal i1 i2))

   (equal
    (start-checkpoint-helper
     (start-checkpoint-helper procs i1)
     i2)

    (start-checkpoint-helper
     (start-checkpoint-helper procs i2)
     i1))))


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
;; PROCESS-CUT-STEP cannot make a process become pre-cut.
;;
;; If I is still in :cut-not-taken after the metadata step,
;; then I must already have been in :cut-not-taken before it.
;;
;; Equivalently, once a process has taken the target cut,
;; later PROCESS-CUT-STEP calls never put it back into the
;; pre-cut set.
;; ------------------------------------------------------------

(defthm
  cm-cut-not-taken-p-after-process-cut-step-implies-before

  (implies
   (cm-cut-not-taken-p
    (process-cut-step
     input
     st
     m)
    i)

   (cm-cut-not-taken-p
    m
    i)))

;; Executing a NOP leaves the state unchanged, so it cannot alter whether the
;; next input is legal.  The biconditional form rewrites legality in either
;; direction during adjacent-swap proofs.
(defthm
  legal-inputp-after-nop-step-iff

  (implies
   (equal
    (ttype input-i)
    :nop)

   (equal
    (legal-inputp
     (system-step st input-i)
     input-j)

    (legal-inputp
     st
     input-j))))

;; NOP itself is always an admissible implementation input.
(defthm legal-inputp-when-nop
  (implies
   (equal
    (ttype input)
    :nop)

   (legal-inputp
    st
    input)))

;; ------------------------------------------------------------
;; SYSTEM-STEP does not change the set of process IDs.
;;
;; Individual implementation steps may change process state,
;; channels, snapshots, etc., but they do not add or remove
;; processes from the distributed system.
;; ------------------------------------------------------------


(defthm
  legal-normal-input-after-step-implies-before

  (implies
   (and
    (equal
     (ttype input-j)
     :normal)

    (legal-inputp
     (system-step st input-i)
     input-j))

   (legal-inputp
    st
    input-j)))


;; ------------------------------------------------------------
;; A NORMAL input does not change the set of processes that
;; have not yet taken the cut.
;;
;; PROCESS-CUT-NORMAL may record the input in metadata, and
;; PROCESS-CUT-STEP may add it to the global before/after-cut
;; sequence, but none of those updates modify :CUT-NOT-TAKEN.
;; ------------------------------------------------------------

(defthm
  cm-cut-not-taken-p-of-process-cut-step-when-normal

  (implies
   (equal
    (ttype input)
    :normal)

   (equal
    (cm-cut-not-taken-p
     (process-cut-step
      input
      st
      m)
     i)

    (cm-cut-not-taken-p
     m
     i))))



;; ------------------------------------------------------------
;; If INPUT-I is a NORMAL step, it only sends messages from
;;
;;     PID(INPUT-I)
;;
;; Therefore a channel whose source is some different process
;; SRC is unchanged by INPUT-I.
;;
;; This is exactly the easy branch needed later when
;;
;;     SENDER(INPUT-J) != PID(INPUT-I).
;; ------------------------------------------------------------

(defthm
  channel-state-after-normal-step-when-src-different

  (implies
   (and
    (equal
     (ttype input)
     :normal)

    (not
     (equal
      src
      (pid input))))

   (equal
    (channel-state
     src
     dst
     (channels
      (system-step st input)))

    (channel-state
     src
     dst
     (channels st)))))


;; ------------------------------------------------------------
;; If SRC has already taken the cut and DST has not,
;; and SRC is an incoming neighbor of DST, then the
;; SRC -> DST channel is already nonempty.
;;
;; GOOD-STATE-P converts
;;
;;   SRC in NBRS-FROM(DST)
;;
;; into
;;
;;   DST in NBRS-TO(SRC).
;;
;; Then CUT-MARKERS-IN-TRANSIT-P says the checkpoint marker
;; is already somewhere in SRC -> DST, so the channel is CONSP.
;; ------------------------------------------------------------


;; ------------------------------------------------------------
;; Convert the incoming-neighbor view into the outgoing-neighbor
;; view.
;;
;; If SRC is an incoming neighbor of DST, then under GOOD-STATE-P
;; the topology consistency invariant says that DST is an outgoing
;; neighbor of SRC.
;;
;; This is the exact orientation needed by the
;; CUT-MARKERS-IN-TRANSIT invariant.
;; ------------------------------------------------------------

(defthm nbrs-from-src-dst-implies-nbrs-to-src-dst
  (implies
   (and
    (good-state-p st)

    (memberp src
             (proc-ids st))

    (memberp dst
             (proc-ids st))

    (memberp
     src
     (nbrs-from
      (g dst
         (procs st)))))

   (memberp
    dst
    (nbrs-to
     (g src
        (procs st)))))

  :hints
  (("Goal"
    :in-theory
    (enable
     nbrs-from-implies-nbrs-to-when-good-state-p))))

;; Convert topology plus the marker-in-transit invariant into the concrete
;; FIFO fact required by receive commutation: the channel from an already
;; post-cut sender to a still-pre-cut receiver has a message at its head.
(defthm
  cut-markers-in-transit-p-implies-channel-consp-from-nbrs-from

  (implies
   (and
    (cut-markers-in-transit-p
     m
     st)

    (good-state-p st)

    (memberp src
             (proc-ids st))

    (memberp dst
             (proc-ids st))

    (memberp
     src
     (nbrs-from
      (g dst
         (procs st))))

    ;; SRC is already post-cut.
    (not
     (cm-cut-not-taken-p
      m
      src))

    ;; DST is still pre-cut.
    (cm-cut-not-taken-p
     m
     dst))

   (consp
    (channel-state
     src
     dst
     (channels st))))
  :hints
  (("Goal"
    :in-theory (disable cut-markers-in-transit-p
			good-state-p
			cm-cut-not-taken)))
    :rule-classes
  ((:rewrite
    :match-free :all)))



;; ------------------------------------------------------------
;; INPUT-I is already post-cut.
;;
;; INPUT-J is still pre-cut after processing INPUT-I.
;;
;; Since PROCESS-CUT-STEP never puts a process back into
;; :CUT-NOT-TAKEN, INPUT-J was also pre-cut before INPUT-I.
;;
;; Therefore INPUT-I and INPUT-J cannot belong to the same
;; process: one is post-cut and the other is pre-cut.
;; ------------------------------------------------------------

(defthm
  post-pre-after-process-cut-step-implies-different-pids

  (implies
   (and
    ;; INPUT-I is already post-cut.
    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))

    ;; INPUT-J is pre-cut after INPUT-I.
    (cm-cut-not-taken-p
     (process-cut-step
      input-i
      st
      m)
     (pid input-j)))

   (not
    (equal
     (pid input-i)
     (pid input-j)))))


;; ------------------------------------------------------------
;; A RECEIVE by process I can affect channels in two ways:
;;
;;   1. it removes a message from SENDER(INPUT) -> I;
;;
;;   2. for certain received protocol messages, I may send
;;      messages on its outgoing channels I -> K.
;;
;; Therefore a channel SRC -> DST is definitely unchanged when
;; both:
;;
;;      SRC != I
;;      DST != I
;;
;; The first condition protects against messages sent by I.
;; The second condition protects against the consumed channel.
;; ------------------------------------------------------------

(defthm
  channel-state-after-receive-step-when-src-and-dst-different

  (implies
   (and
    (equal
     (ttype input)
     :receive)

    (not
     (equal
      src
      (pid input)))

    (not
     (equal
      dst
      (pid input))))

   (equal
    (channel-state
     src
     dst
     (channels
      (system-step st input)))

    (channel-state
     src
     dst
     (channels st)))))


;; ------------------------------------------------------------
;; INPUT-I is a RECEIVE by a post-cut process.
;; INPUT-J is a RECEIVE by a process that is still pre-cut.
;;
;; We want to show that INPUT-J's receive channel was already
;; nonempty before INPUT-I executes.
;;
;; Split on whether INPUT-I is the sender of INPUT-J's channel.
;;
;; Case 1:
;;   SENDER(INPUT-J) != PID(INPUT-I)
;;
;;   We already know PID(INPUT-J) != PID(INPUT-I) from the
;;   POST/PRE statuses.  Therefore both the source and the
;;   destination of INPUT-J's channel differ from PID(INPUT-I).
;;   The previous channel-preservation lemma applies.
;;
;; Case 2:
;;   SENDER(INPUT-J) = PID(INPUT-I)
;;
;;   INPUT-I is post-cut and INPUT-J is pre-cut.  Since
;;   SENDER(INPUT-J) is an incoming neighbor of PID(INPUT-J),
;;   GOOD-STATE-P converts that to the corresponding NBRS-TO
;;   relation.  CUT-MARKERS-IN-TRANSIT-P then says that the
;;   channel already contains the target marker, hence it is
;;   nonempty.
;; ------------------------------------------------------------

(defthm
  receive-channel-consp-before-post-cut-receive-step

  (implies
   (and
    (cut-markers-in-transit-p m st)

    (good-state-p st)

    (equal
     (ttype input-i)
     :receive)

    (equal
     (ttype input-j)
     :receive)

    ;; INPUT-J is a valid receive topology-wise in ST.
    (memberp
     (pid input-j)
     (proc-ids st))

    (memberp
     (sender input-j)
     (proc-ids st))

    (memberp
     (sender input-j)
     (nbrs-from
      (g (pid input-j)
         (procs st))))

    ;; INPUT-J's channel is nonempty after INPUT-I.
    (consp
     (channel-state
      (sender input-j)
      (pid input-j)
      (channels
       (system-step st input-i))))

    ;; INPUT-I is already post-cut.
    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))

    ;; INPUT-J is still pre-cut after INPUT-I.
    (cm-cut-not-taken-p
     (process-cut-step
      input-i
      st
      m)
     (pid input-j)))

   ;; Therefore INPUT-J's channel was already nonempty.
   (consp
    (channel-state
     (sender input-j)
     (pid input-j)
     (channels st))))

  :hints
  (("Goal"

    ;; Is INPUT-I the source of INPUT-J's receive channel?
    :cases
    ((equal
      (sender input-j)
      (pid input-i))))))


;; ------------------------------------------------------------
;; SEND-MSG-ALL-OUTGOING-CHANNELS only changes channels
;; whose source is I.
;;
;; Therefore, if SRC is different from I, the channel
;;
;;     SRC -> DST
;;
;; is unchanged.
;; ------------------------------------------------------------

(defthm
  channel-state-of-send-msg-all-outgoing-channels-when-src-different

  (implies
   (not
    (equal src i))

   (equal
    (channel-state
     src
     dst
     (send-msg-all-outgoing-channels
      msg
      i
      nbrs
      channels))

    (channel-state
     src
     dst
     channels)))

  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg
     i
     nbrs
     channels))))


;; ------------------------------------------------------------
;; A START-CHECKPOINT step sends marker messages only from
;; PID(INPUT) to its outgoing neighbors.
;;
;; Therefore, any channel whose source SRC is different from
;; PID(INPUT) is unchanged by the checkpoint-start step.
;; ------------------------------------------------------------

(defthm
  channel-state-after-start-checkpoint-step-when-src-different

  (implies
   (and
    (equal
     (ttype input)
     :start-checkpoint)

    (not
     (equal
      src
      (pid input))))

   (equal
    (channel-state
     src
     dst
     (channels
      (system-step st input)))

    (channel-state
     src
     dst
     (channels st)))))


;; ------------------------------------------------------------
;; INPUT-I is a START-CHECKPOINT step by a process that is
;; already post-cut with respect to the target cut M.
;;
;; INPUT-J is a RECEIVE by a process that is still pre-cut.
;;
;; We show that INPUT-J's receive channel was already nonempty
;; before INPUT-I.
;;
;; Case 1:
;;   SENDER(INPUT-J) != PID(INPUT-I)
;;
;;   START-CHECKPOINT only sends messages from PID(INPUT-I),
;;   so INPUT-J's channel is unchanged.
;;
;; Case 2:
;;   SENDER(INPUT-J) = PID(INPUT-I)
;;
;;   INPUT-I is post-cut and INPUT-J is pre-cut.  The
;;   marker-in-transit invariant therefore guarantees that
;;   the target marker is already in this channel, so the
;;   channel was already nonempty.
;; ------------------------------------------------------------

(defthm
  receive-channel-consp-before-post-cut-start-checkpoint-step

  (implies
   (and
    (cut-markers-in-transit-p
     m st)

    (good-state-p st)

    (equal
     (ttype input-i)
     :start-checkpoint)

    (equal
     (ttype input-j)
     :receive)

    (memberp
     (pid input-j)
     (proc-ids st))

    (memberp
     (sender input-j)
     (proc-ids st))

    (memberp
     (sender input-j)
     (nbrs-from
      (g (pid input-j)
         (procs st))))

    ;; INPUT-J's channel is nonempty after INPUT-I.
    (consp
     (channel-state
      (sender input-j)
      (pid input-j)
      (channels
       (system-step st input-i))))

    ;; INPUT-I is already post-cut.
    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))

    ;; INPUT-J remains pre-cut after INPUT-I.
    (cm-cut-not-taken-p
     (process-cut-step
      input-i
      st
      m)
     (pid input-j)))

   ;; Hence INPUT-J's receive channel was already nonempty.
   (consp
    (channel-state
     (sender input-j)
     (pid input-j)
     (channels st))))

  :hints
  (("Goal"

    ;; Split according to whether INPUT-I is the source of
    ;; INPUT-J's receive channel.
    :cases
    ((equal
      (sender input-j)
      (pid input-i))))))



;; ------------------------------------------------------------
;; A NOP step does not change any channel.
;;
;; Therefore every channel SRC -> DST is exactly the same
;; before and after executing a :NOP input.
;; ------------------------------------------------------------

(defthm
  channel-state-after-nop-step

  (implies
   (equal
    (ttype input)
    :nop)

   (equal
    (channel-state
     src
     dst
     (channels
      (system-step st input)))

    (channel-state
     src
     dst
     (channels st)))))

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
;; If a sequence of inputs is legal from ST, then its first
;; input is legal in ST.
;;
;; This is the first obligation in the recursive definition of
;; LEGAL-INPUT-SEQUENCEP.
;; ------------------------------------------------------------

(defthm legal-input-sequencep-implies-first-legal
  (implies
   (and
    (consp inputs)
    (legal-input-sequencep st inputs))

   (legal-inputp
    st
    (first inputs))))

;; ------------------------------------------------------------
;; If the two-input sequence (INPUT-I INPUT-J) is legal from ST,
;; then INPUT-I is legal in ST.
;; ------------------------------------------------------------

(defthm legal-input-sequencep-of-two-implies-first-legal
  (implies
   (legal-input-sequencep
    st
    (list input-i input-j))

   (legal-inputp
    st
    input-i))
    :rule-classes
  ((:rewrite
    :match-free :all))
  :hints (("Goal"
	   :in-theory (disable legal-inputp))))


;; ------------------------------------------------------------
;; If the two-input sequence (INPUT-I INPUT-J) is legal from ST,
;; then after executing INPUT-I, INPUT-J is legal.
;;
;; This is the second obligation in the recursive definition of
;; LEGAL-INPUT-SEQUENCEP for a two-element list.
;; ------------------------------------------------------------

(defthm legal-input-sequencep-of-two-implies-second-legal
  (implies
   (legal-input-sequencep
    st
    (list input-i input-j))

   (legal-inputp
    (system-step st input-i)
    input-j))
    :rule-classes
  ((:rewrite
    :match-free :all))
  :hints (("Goal"
	   :in-theory (disable legal-inputp
			       system-step))))









;; ------------------------------------------------------------
;; SEND-COMPUTE-MESSAGE never makes a nonempty channel empty.
;;
;; It either:
;;
;;   - leaves the channels unchanged,
;;   - recursively considers another outgoing neighbor, or
;;   - appends a compute message to one channel.
;;
;; Appending with SNOC preserves nonemptiness.
;; ------------------------------------------------------------

(defthm channel-consp-preserved-by-send-compute-message
  (implies
   (consp
    (channel-state
     src
     dst
     channels))

   (consp
    (channel-state
     src
     dst
     (send-compute-message
      local-state
      i
      nbrs
      channels)))))

;; ------------------------------------------------------------
;; A NORMAL step never removes messages from any channel.
;;
;; It may append a newly computed message to some outgoing
;; channels of PID(INPUT), but appending preserves nonemptiness.
;;
;; Therefore, if SRC -> DST is nonempty before the NORMAL step,
;; it is still nonempty afterwards.
;; ------------------------------------------------------------

(defthm
  channel-consp-preserved-by-normal-step

  (implies
   (and
    (equal
     (ttype input)
     :normal)

    (consp
     (channel-state
      src
      dst
      (channels st))))

   (consp
    (channel-state
     src
     dst
     (channels
      (system-step st input))))))





;; A START-CHECKPOINT step cannot make an already nonempty
;; channel empty.
;;
;; START-CHECKPOINT sends marker messages on outgoing channels.
;; This may append to some channels, but it never removes a
;; message from any channel.
;;
;; Therefore, if SRC -> DST is nonempty before the step, it
;; remains nonempty afterward.
;; ------------------------------------------------------------

(defthm
  channel-consp-preserved-by-start-checkpoint-step

  (implies
   (and
    (equal
     (ttype input)
     :start-checkpoint)

    (consp
     (channel-state
      src
      dst
      (channels st))))

   (consp
    (channel-state
     src
     dst
     (channels
      (system-step st input))))))


;; ------------------------------------------------------------
;; A RECEIVE step at process PID(INPUT) cannot make a
;; nonempty channel SRC -> DST empty when DST is a different
;; process.
;;
;; A RECEIVE may:
;;
;;   - remove one message from SENDER(INPUT) -> PID(INPUT);
;;   - send marker/recovery messages from PID(INPUT) to
;;     outgoing neighbors.
;;
;; If DST != PID(INPUT), the target SRC -> DST channel is not
;; the channel from which the receive removes a message.
;;
;; Any protocol send can only append to SRC -> DST, so an
;; already nonempty channel remains nonempty.
;; ------------------------------------------------------------

(defthm
  channel-consp-preserved-by-receive-step-when-dst-different

  (implies
   (and
    (equal
     (ttype input)
     :receive)

    (not
     (equal
      dst
      (pid input)))

    (consp
     (channel-state
      src
      dst
      (channels st))))

   (consp
    (channel-state
     src
     dst
     (channels
      (system-step st input))))))




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









;; ------------------------------------------------------------
;; A normal-message send by I1 commutes exactly with sending
;; MSG on all outgoing channels of a different process I2.
;;
;; SEND-COMPUTE-MESSAGE only updates channels sourced by I1.
;; SEND-MSG-ALL-OUTGOING-CHANNELS only updates channels sourced
;; by I2.
;;
;; Since I1 != I2, the channel updates commute exactly.
;; ------------------------------------------------------------

(defthm
  send-compute-message-send-msg-all-outgoing-different-senders-commute

  (implies
   (not
    (equal i1 i2))

   (equal
    (send-msg-all-outgoing-channels
     msg
     i2
     nbrs2
     (send-compute-message
      local1
      i1
      nbrs1
      channels))

    (send-compute-message
     local1
     i1
     nbrs1
     (send-msg-all-outgoing-channels
      msg
      i2
      nbrs2
      channels))))

  :hints
  (("Goal"
    :induct
    (send-compute-message
     local1
     i1
     nbrs1
     channels)

    :in-theory
    (disable
     send-msg-all-outgoing-channels))))


;; ------------------------------------------------------------
;; Sending messages from another source I2 cannot affect the
;; final I1 -> DST channel produced by I1's own outgoing sends.
;;
;; The I2 send changes only channels sourced by I2.
;; Since I1 != I2, I1's starting row is unchanged; therefore
;; running the same I1 outgoing sends produces the same
;; I1 -> DST channel.
;; ------------------------------------------------------------

(defthm
  channel-state-of-send-msg-all-after-other-sender

  (implies
   (not
    (equal i1 i2))

   (equal
    (channel-state
     i1
     dst
     (send-msg-all-outgoing-channels
      msg1
      i1
      nbrs1
      (send-msg-all-outgoing-channels
       msg2
       i2
       nbrs2
       channels)))

    (channel-state
     i1
     dst
     (send-msg-all-outgoing-channels
      msg1
      i1
      nbrs1
      channels)))))

;; ------------------------------------------------------------
;; Sending messages from two different source processes
;; commutes exactly at the raw channel level.
;;
;; Each SEND-MSG-ALL-OUTGOING-CHANNELS only updates channels
;; whose source is its own process ID.
;;
;; Therefore, when I1 != I2, the two sets of channel updates
;; are disjoint by source and commute.
;; ------------------------------------------------------------

(defthm
  send-msg-all-outgoing-different-senders-commute

  (implies
   (not
    (equal i1 i2))

   (equal
    (send-msg-all-outgoing-channels
     msg2
     i2
     nbrs2
     (send-msg-all-outgoing-channels
      msg1
      i1
      nbrs1
      channels))

    (send-msg-all-outgoing-channels
     msg1
     i1
     nbrs1
     (send-msg-all-outgoing-channels
      msg2
      i2
      nbrs2
      channels)))))



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

;; A NOP is operational identity.  This closes every case in which either
;; side of the adjacent transposition is :nop.
(defthm system-step-when-nop
  (implies
   (equal
    (ttype input)
    :nop)

   (equal
    (system-step st input)
    st)))


;; The pointwise checkpoint-control relation is reflexive; it is the terminal
;; fact for cases whose two process tables simplify to the same term.
(defthm cl-checkpoint-control-equivalent-p-reflexive
  (cl-checkpoint-control-equivalent-p
   ids
   procs
   procs))


;; Receive/receive base case under the abstract swappability contract.  Legal
;; receives at different PIDs may update snapshot metadata, but their
;; observed counter/SID lists remain pointwise equivalent after swapping.
(defthm
  cl-checkpoint-control-receive-receive-commute

  (implies
   (and
    (equal (ttype input-1) :receive)
    (equal (ttype input-2) :receive)

    (cl-two-imp-inputs-swappable-p
     st input-1 input-2))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel
     remove-message-from-channel))))


;; Specialize the abstract receive/receive result to a post-cut/pre-cut pair
;; by deriving CL-TWO-IMP-INPUTS-SWAPPABLE-P from the cut invariants.
(defthm
  cl-post-pre-receive-receive-checkpoint-control

  (implies
   (and
    (equal (ttype input-1) :receive)
    (equal (ttype input-2) :receive)

    (cl-post-pre-swap-start-p
     st m input-1 input-2))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :use
    ((:instance
      cl-post-pre-two-imp-inputs-swappable-p)

     (:instance
      cl-checkpoint-control-receive-receive-commute))

    :in-theory
    (disable
     cl-post-pre-swap-start-p
     cl-post-pre-two-imp-inputs-swappable-p
     cl-two-imp-inputs-swappable-p
     cl-checkpoint-control-receive-receive-commute
     cl-checkpoint-control-equivalent-p
     system-step))))



;; Two normal inputs do not modify checkpoint counters or snapshot-ID lists,
;; so checkpoint-control equivalence holds without a swappability hypothesis.
(defthm
  cl-checkpoint-control-normal-normal-commute

  (implies
   (and
    (equal (ttype input-1) :normal)
    (equal (ttype input-2) :normal))

   (cl-checkpoint-control-equivalent-p
    ids

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1)))))



;; Mixed normal/receive base case, with normal first in the original order.
;; The swappability contract guarantees the receive consumes the same FIFO
;; head in both executions.
(defthm
  cl-checkpoint-control-normal-receive-commute

  (implies
   (and
    (equal (ttype input-1) :normal)
    (equal (ttype input-2) :receive)

    (cl-two-imp-inputs-swappable-p
     st input-1 input-2))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel))))


;; Cut-oriented wrapper for the normal/receive base case.
(defthm
  cl-post-pre-normal-receive-checkpoint-control

  (implies
   (and
    (equal (ttype input-1) :normal)
    (equal (ttype input-2) :receive)

    (cl-post-pre-swap-start-p
     st m input-1 input-2))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :use
    ((:instance
      cl-post-pre-two-imp-inputs-swappable-p)

     (:instance
      cl-checkpoint-control-normal-receive-commute)))))






;; Reverse mixed orientation: receive first, then normal.  This is stated as
;; a separate theorem so ACL2 need not synthesize argument permutations
;; during the final type dispatch.
(defthm
  cl-checkpoint-control-normal-receive-commute2

  (implies
   (and
    (equal (ttype input-1) :receive)
    (equal (ttype input-2) :normal)

    (cl-two-imp-inputs-swappable-p
     st input-1 input-2))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel))))



;; Cut-oriented wrapper for the receive/normal orientation.
(defthm
  cl-post-pre-normal-receive-checkpoint-control2

  (implies
   (and
    (equal (ttype input-1) :receive)
    (equal (ttype input-2) :normal)

    (cl-post-pre-swap-start-p
     st m input-1 input-2))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :use
    ((:instance
      cl-post-pre-two-imp-inputs-swappable-p)

     (:instance
      cl-checkpoint-control-normal-receive-commute2)))))




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


;; Symmetric spelling of PID disequality, registered only for explicit use.
;; It avoids depending on ACL2 to orient EQUAL in mixed start/normal proofs.
(defthm
  cl-post-pre-swap-start-implies-reversed-pids-different

  (implies
   (cl-post-pre-swap-start-p
    st m input-1 input-2)

   (not
    (equal
     (pid input-2)
     (pid input-1))))

  :hints
  (("Goal"
    :use
    ((:instance
      cl-post-pre-swap-start-implies-pids-different
      (st st)
      (m m)
      (input-1 input-1)
      (input-2 input-2)))

    :cases
    ((equal
      (pid input-2)
      (pid input-1)))

    :in-theory
    (disable
     cl-post-pre-swap-start-p
     cl-post-pre-swap-start-implies-pids-different)))

:rule-classes nil)


;; Exact process-table commutation for checkpoint-start followed by a normal
;; step at a different PID.  Equality is stronger than the control relation
;; and lets the wrapper below close by reflexivity.
(defthm
  cl-start-checkpoint-normal-procs-commute

  (implies
   (and
    (equal (ttype input-1) :start-checkpoint)
    (equal (ttype input-2) :normal)

    (not
     (equal
      (pid input-1)
      (pid input-2))))

   (equal
    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (system-step)

     (start-checkpoint-helper
      create-marker-message
      send-compute-message)))))




;; Normal/start is the reverse syntactic orientation of the exact theorem
;; above; PID disequality from the post/pre predicate supplies its side case.
(defthm
  cl-post-pre-normal-start-checkpoint-checkpoint-control

  (implies
   (and
    (equal (ttype input-1) :normal)
    (equal (ttype input-2) :start-checkpoint)

    (cl-post-pre-swap-start-p
     st m input-1 input-2))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :use
    ((:instance
      cl-post-pre-swap-start-implies-reversed-pids-different
      (st st)
      (m m)
      (input-1 input-1)
      (input-2 input-2))

     (:instance
      cl-start-checkpoint-normal-procs-commute
      (st st)
      (input-1 input-2)
      (input-2 input-1)))

    :in-theory
    (disable
     cl-post-pre-swap-start-p
     cl-post-pre-swap-start-implies-pids-different
    ; cl-post-pre-swap-start-implies-reversed-pids-different
     cl-start-checkpoint-normal-procs-commute
     system-step
     cl-checkpoint-control-equivalent-p))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generic update rules for the checkpoint-control relation
;;
;; The difficult receive/start expansions eventually reduce to replacing a
;; single process record.  These congruence lemmas let those proofs reason
;; only about COUNTER and SNAPSHOT-IDS rather than recursively rebuilding the
;; complete process table.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If two replacement records agree on the observed control fields, placing
;; them into the same process table at the same key yields equivalent tables.
(defthm
  cl-checkpoint-control-equivalent-p-of-single-proc-update

  (implies
   (and
    (equal
     (counter p1)
     (counter p2))

    (equal
     (snapshot-ids p1)
     (snapshot-ids p2)))

   (cl-checkpoint-control-equivalent-p
    ids
    (s i p1 procs)
    (s i p2 procs)))

  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids procs procs)

    :in-theory
    (enable
     cl-checkpoint-control-equivalent-p))

   ("Subgoal *1/2"
    :cases
    ((equal
      (car ids)
      i)))))


;; If two tables are already control-equivalent, installing the same process
;; record at the same key on both sides preserves the relation.
(defthm
  cl-checkpoint-control-equivalent-p-preserved-by-same-proc-update

  (implies
   (cl-checkpoint-control-equivalent-p
    ids procs-1 procs-2)

   (cl-checkpoint-control-equivalent-p
    ids
    (s i p procs-1)
    (s i p procs-2)))

  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids procs-1 procs-2)

    :in-theory
    (enable
     cl-checkpoint-control-equivalent-p))

   ("Subgoal *1/2"
    :cases
    ((equal
      (car ids)
      i)))))


;; Core start/receive theorem.  The steps target distinct PIDs, both inputs
;; are legal in the common state, and recovery is absent.  The conclusion is
;; deliberately the control relation: marker handling may reorder hidden
;; snapshot contents while preserving counters and the snapshot-ID frontier.
(defthm
  cl-start-checkpoint-receive-checkpoint-control

  (implies
   (and
    (equal
     (ttype input-1)
     :start-checkpoint)

    (equal
     (ttype input-2)
     :receive)

    (not
     (equal
      (pid input-1)
      (pid input-2)))

    (legal-inputp
     st
     input-1)

    (legal-inputp
     st
     input-2)

    (recovery-free-state-p st))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1)))))


;; Symmetry is kept as an explicit non-rewrite theorem.  Using it by instance
;; is predictable and avoids rewrite loops on a symmetric relation.
(defthm
  cl-checkpoint-control-equivalent-p-symmetric

  (implies
   (cl-checkpoint-control-equivalent-p
    ids
    procs-1
    procs-2)

   (cl-checkpoint-control-equivalent-p
    ids
    procs-2
    procs-1))

  :hints
  (("Goal"
    :in-theory
    (enable
     cl-checkpoint-control-equivalent-p)))

  :rule-classes nil)



;; Receive/start wrapper.  Apply the core start/receive theorem in the
;; opposite order, then use symmetry to restore the requested conclusion.
(defthm
  cl-post-pre-receive-start-checkpoint-checkpoint-control

  (implies
   (and
    (cl-post-pre-swap-start-p
     st m input-1 input-2)

    (equal (ttype input-1) :receive)

    (equal
     (ttype input-2)
     :start-checkpoint))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :cases
    ((equal
      (pid input-2)
      (pid input-1)))

    :use
    ((:instance
      cl-post-pre-two-imp-inputs-swappable-p)

     (:instance
      cl-start-checkpoint-receive-checkpoint-control
      (input-1 input-2)
      (input-2 input-1))

     (:instance
      cl-checkpoint-control-equivalent-p-symmetric

      (ids (proc-ids st))

      (procs-1
       (procs
        (system-step
         (system-step st input-2)
         input-1)))

      (procs-2
       (procs
        (system-step
         (system-step st input-1)
         input-2)))))

    :in-theory
    (e/d
     (cl-post-pre-swap-start-p
      cl-two-imp-inputs-swappable-p)

     (cl-post-pre-two-imp-inputs-swappable-p
      cl-start-checkpoint-receive-checkpoint-control
     ; cl-checkpoint-control-equivalent-p-symmetric
      cl-checkpoint-control-equivalent-p
      system-step
      process-cut-step
      legal-input-sequencep
      legal-inputp
      no-recovery-step-p
      recovery-free-state-p
      cl-checkpoint-body-input-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p)))))



;; Start/receive wrapper in the same orientation as the core theorem.
(defthm
  cl-post-pre-start-checkpoint-receive-checkpoint-control

  (implies
   (and
    (cl-post-pre-swap-start-p
     st m input-1 input-2)

    (equal
     (ttype input-1)
     :start-checkpoint)

    (equal
     (ttype input-2)
     :receive))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :use
    ((:instance
      cl-post-pre-two-imp-inputs-swappable-p)

     (:instance
      cl-start-checkpoint-receive-checkpoint-control))

    :in-theory
    (e/d
     (cl-post-pre-swap-start-p
      cl-two-imp-inputs-swappable-p)

     (cl-post-pre-two-imp-inputs-swappable-p
      cl-start-checkpoint-receive-checkpoint-control
      cl-checkpoint-control-equivalent-p

      system-step
      process-cut-step
      legal-input-sequencep
      legal-inputp
      no-recovery-step-p
      recovery-free-state-p
      cl-checkpoint-body-input-p

      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p)))))



;; Start/normal post-pre case.  The stronger exact process commutation theorem
;; immediately implies checkpoint-control equivalence.
(defthm
  cl-post-pre-start-checkpoint-normal-checkpoint-control

  (implies
   (and
    (cl-post-pre-swap-start-p
     st m input-1 input-2)

    (equal
     (ttype input-1)
     :start-checkpoint)

    (equal
     (ttype input-2)
     :normal))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :use
    ((:instance
      cl-post-pre-two-imp-inputs-swappable-p)

     (:instance
      cl-start-checkpoint-normal-procs-commute))

    :in-theory
    (e/d
     (cl-two-imp-inputs-swappable-p)

     (cl-post-pre-swap-start-p
      cl-post-pre-two-imp-inputs-swappable-p
      cl-start-checkpoint-normal-procs-commute
      cl-checkpoint-control-equivalent-p
      system-step)))))



;; Two starts at distinct PIDs commute exactly in the process table: each
;; START-CHECKPOINT-HELPER updates only its designated process slot.
(defthm
  procs-start-checkpoint-start-checkpoint-different-pids-commute

  (implies
   (and
    (equal
     (ttype input-1)
     :start-checkpoint)

    (equal
     (ttype input-2)
     :start-checkpoint)

    (not
     (equal
      (pid input-1)
      (pid input-2))))

   (equal
    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :in-theory
    (enable
     system-step
     step-checkpoint))))


;; Cut-oriented control-equivalence wrapper for the start/start equality.
(defthm
  cl-post-pre-start-checkpoint-start-checkpoint-checkpoint-control

  (implies
   (and
    (cl-post-pre-swap-start-p
     st m input-1 input-2)

    (equal
     (ttype input-1)
     :start-checkpoint)

    (equal
     (ttype input-2)
     :start-checkpoint))

   (cl-checkpoint-control-equivalent-p
    (proc-ids st)

    (procs
     (system-step
      (system-step st input-1)
      input-2))

    (procs
     (system-step
      (system-step st input-2)
      input-1))))

  :hints
  (("Goal"
    :use
    ((:instance
      cl-post-pre-two-imp-inputs-swappable-p)

     (:instance
      procs-start-checkpoint-start-checkpoint-different-pids-commute))

    :in-theory
    (e/d
     (cl-two-imp-inputs-swappable-p)

     (cl-post-pre-swap-start-p
      cl-post-pre-two-imp-inputs-swappable-p
      procs-start-checkpoint-start-checkpoint-different-pids-commute
      cl-checkpoint-control-equivalent-p
      system-step)))))


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

;; A nonempty channel in a recovery-free state cannot have a recovery
;; message at its head.  This removes the recovery-message receive branch.
(defthm
  cl-no-recovery-msgs-in-state-channels-implies-head-not-recovery

  (implies
   (and
    (no-recovery-msgs-in-channels-p
     (proc-ids st)
     (proc-ids st)
     (channels st))

    (memberp
     src
     (proc-ids st))

    (memberp
     dst
     (proc-ids st))

    (consp
     (channel-state
      src
      dst
      (channels st))))

   (not
    (equal
     (msg-type
      (first
       (channel-state
        src
        dst
        (channels st))))
     :recovery)))

  :hints
  (("Goal"
    :use
    ((:instance
      no-recovery-msgs-in-channels-p-implies-get-msg-not-recovery

      (srcs
       (proc-ids st))

      (dsts
       (proc-ids st))

      (channels
       (channels st))

      (src src)
      (dst dst)))

    :in-theory
    (e/d
     (get-msg-from-channel)

     (no-recovery-msgs-in-channels-p-implies-get-msg-not-recovery)))))


;; LOCAL-STATE is not part of checkpoint control, so independent local-state
;; updates preserve checkpoint-control equivalence.
(defthm
  cl-checkpoint-control-equivalent-p-preserved-by-local-state-updates

  (implies
   (cl-checkpoint-control-equivalent-p
    ids
    procs-1
    procs-2)

   (cl-checkpoint-control-equivalent-p
    ids

    (s i
       (s :local-state
          new-local-1
          (g i procs-1))
       procs-1)

    (s i
       (s :local-state
          new-local-2
          (g i procs-2))
       procs-2)))

  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2)

    :in-theory
    (enable
     cl-checkpoint-control-equivalent-p))

   ("Subgoal *1/2"
    :cases
    ((equal
      (car ids)
      i)))))


;; A normal receive may record different snapshot bookkeeping on the two
;; sides, but visible-process equivalence is preserved when it installs the
;; same application-visible local state.
(defthm
  procs-equivalent-p-preserved-by-same-local-state-and-snapshots-update

  (implies
   (procs-equivalent-p
    ids
    procs-1
    procs-2)

   (procs-equivalent-p
    ids

    (s i
       (s :snapshots snapshots-1
          (s :local-state new-local
             (g i procs-1)))
       procs-1)

    (s i
       (s :snapshots snapshots-2
          (s :local-state new-local
             (g i procs-2)))
       procs-2)))

  :hints
  (("Goal"
    :induct
    (procs-equivalent-p
     ids
     procs-1
     procs-2))

   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))



;; Both LOCAL-STATE and SNAPSHOTS are invisible to checkpoint control.
;; Consequently, they may be updated independently on the two sides.
(defthm
  cl-checkpoint-control-equivalent-p-preserved-by-local-state-and-snapshots-updates

  (implies
   (cl-checkpoint-control-equivalent-p
    ids
    procs-1
    procs-2)

   (cl-checkpoint-control-equivalent-p
    ids

    (s i
       (s :snapshots snapshots-1
          (s :local-state new-local-1
             (g i procs-1)))
       procs-1)

    (s i
       (s :snapshots snapshots-2
          (s :local-state new-local-2
             (g i procs-2)))
       procs-2)))

  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2))

   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))



;; SNAPSHOTS and SNAPSHOT-IDS are invisible to PROCS-EQUIVALENT-P, whose
;; observations are limited to the three application-visible process fields.
(defthm
  procs-equivalent-p-preserved-by-snapshots-and-snapshot-ids-updates

  (implies
   (procs-equivalent-p
    ids
    procs-1
    procs-2)

   (procs-equivalent-p
    ids

    (s i
       (s :snapshots snapshots-1
          (s :snapshot-ids snapshot-ids-1
             (g i procs-1)))
       procs-1)

    (s i
       (s :snapshots snapshots-2
          (s :snapshot-ids snapshot-ids-2
             (g i procs-2)))
       procs-2)))

  :hints
  (("Goal"
    :induct
    (procs-equivalent-p
     ids
     procs-1
     procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))


;; If no listed process is recovering, a listed process cannot individually
;; have :RECOVERING status.  This closes inconsistent receive branches.
(defthm
  no-any-proc-recovering-p-implies-member-not-recovering

  (implies
   (and
    (not
     (any-proc-recovering-p
      ids
      procs))

    (memberp i ids))

   (not
    (equal
     (proc-status
      (g i procs))
     :recovering))))


;; Generic checkpoint-control update rule.  Replacing process I preserves
;; the list relation whenever agreement of I's old control fields implies
;; agreement of the replacement processes' control fields.
(defthm
  cl-checkpoint-control-equivalent-p-preserved-by-related-proc-updates

  (implies
   (and
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2)

    (implies
     (and
      (equal
       (counter (g i procs-1))
       (counter (g i procs-2)))

      (equal
       (snapshot-ids (g i procs-1))
       (snapshot-ids (g i procs-2))))

     (and
      (equal
       (counter new-p-1)
       (counter new-p-2))

      (equal
       (snapshot-ids new-p-1)
       (snapshot-ids new-p-2)))))

   (cl-checkpoint-control-equivalent-p
    ids
    (s i new-p-1 procs-1)
    (s i new-p-2 procs-2)))

  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2)

    :in-theory
    (enable
     cl-checkpoint-control-equivalent-p))

   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))


;; Pointwise projection of SNAPSHOT-IDS from checkpoint-control equivalence.
;; This rules out branches that classify the same marker as first on one side
;; and non-first on the other.
(defthm
  cl-checkpoint-control-equivalent-p-implies-snapshot-ids-equal

  (implies
   (and
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2)

    (memberp i ids))

   (equal
    (snapshot-ids
     (g i procs-1))

    (snapshot-ids
     (g i procs-2))))

  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2)

    :in-theory
    (enable
     cl-checkpoint-control-equivalent-p
     memberp))

   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))


;; Process-level field abstraction.  Updating any field other than the three
;; fields observed by PROC-EQUIVALENT-P has no effect on that relation, and
;; the hidden values installed on the two sides need not be equal.
(defthm
  proc-equivalent-p-ignores-non-visible-field-updates

  (implies
   (and
    (not (equal field :local-state))
    (not (equal field :nbrs-to))
    (not (equal field :nbrs-from)))

   (equal
    (proc-equivalent-p
     (s field value-1 p-1)
     (s field value-2 p-2))

    (proc-equivalent-p
     p-1
     p-2)))

  :hints
  (("Goal"
    :in-theory
    (enable proc-equivalent-p))))


;; Lift the preceding field abstraction pointwise over the process table.
(defthm
  procs-equivalent-p-ignores-non-visible-field-updates

  (implies
   (and
    (procs-equivalent-p
     ids
     procs-1
     procs-2)

    (not (equal field :local-state))
    (not (equal field :nbrs-to))
    (not (equal field :nbrs-from)))

   (procs-equivalent-p
    ids

    (s i
       (s field value-1
          (g i procs-1))
       procs-1)

    (s i
       (s field value-2
          (g i procs-2))
       procs-2)))

  :hints
  (("Goal"
    :induct
    (procs-equivalent-p
     ids
     procs-1
     procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))


;; Pointwise projection of COUNTER from checkpoint-control equivalence.  It
;; ensures that both executions create the same checkpoint SID and marker.
(defthm
  cl-checkpoint-control-equivalent-p-implies-counter-equal

  (implies
   (and
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2)

    (memberp i ids))

   (equal
    (counter
     (g i procs-1))

    (counter
     (g i procs-2))))

  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2))

   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))



;; Most general visible-process replacement rule used by the preservation
;; proof.  NEW-P-1 and NEW-P-2 may contain arbitrary, asymmetric checkpoint
;; bookkeeping as long as each preserves the visible fields of its original.
(defthm
  procs-equivalent-p-preserved-by-invisible-proc-replacements

  (implies
   (and
    (procs-equivalent-p
     ids
     procs-1
     procs-2)

    ;; NEW-P-1 preserves the visible fields of its original.
    (equal
     (local-state new-p-1)
     (local-state (g i procs-1)))

    (equal
     (nbrs-to new-p-1)
     (nbrs-to (g i procs-1)))

    (equal
     (nbrs-from new-p-1)
     (nbrs-from (g i procs-1)))

    ;; NEW-P-2 preserves the visible fields of its original.
    (equal
     (local-state new-p-2)
     (local-state (g i procs-2)))

    (equal
     (nbrs-to new-p-2)
     (nbrs-to (g i procs-2)))

    (equal
     (nbrs-from new-p-2)
     (nbrs-from (g i procs-2))))

   (procs-equivalent-p
    ids
    (s i new-p-1 procs-1)
    (s i new-p-2 procs-2)))

  :hints
  (("Goal"
    :induct
    (procs-equivalent-p
     ids
     procs-1
     procs-2))

   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))



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







;; ------------------------------------------------------------
;; Equivalent process tables have identical incoming-neighbor
;; lists for every process identifier in IDS.
;;
;; This is needed for transferring the legality of a :RECEIVE
;; input from one equivalent state to the other.
;; ------------------------------------------------------------

(defthm
  cl-procs-equivalent-p-implies-nbrs-from-equal

  (implies
   (and
    (procs-equivalent-p
     ids
     procs-1
     procs-2)

    (memberp i ids))

   (equal
    (g :nbrs-from
       (g i procs-1))

    (g :nbrs-from
       (g i procs-2)))))




(defthm
  cl-state-equivalent-p-preserves-legal-body-inputp

  (implies
   (and
    (cl-state-equivalent-p
     st-original
     st-after-swap)

    (recovery-free-state-p
     st-original)

    (recovery-free-state-p
     st-after-swap)

    (cl-checkpoint-body-input-p
     input)

    (legal-inputp
     st-original
     input))

   (legal-inputp
    st-after-swap
    input)))




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
  cl-state-equivalent-p-preserved-by-postfix

  (implies
   (and
    (cl-state-equivalent-p
     st-original
     st-after-swap)

    (recovery-free-state-p st-original)
    (recovery-free-state-p st-after-swap)

    (good-state-p st-original)
    (good-state-p st-after-swap)

    (cl-checkpoint-body-inputs-p postfix)

    (legal-input-sequencep
     st-original
     postfix))

   (cl-state-equivalent-p
    (run-imp st-original postfix)
    (run-imp st-after-swap postfix)))
  :hints (("Goal"
	  ; :induct (legal-input-sequencep st-after-swap postfix)
	   :in-theory (disable 
			       cl-state-equivalent-p
			       recovery-free-state-p
			       good-state-p
			       run-imp
			       cl-checkpoint-body-inputs-p))))






;; ------------------------------------------------------------
;; Legality of a concatenated execution implies legality of
;; its suffix from the state reached after its prefix.
;;
;; If
;;
;;     INPUTS-1 ++ INPUTS-2
;;
;; is legal from ST, then INPUTS-2 is legal from the state
;; obtained after executing INPUTS-1.
;;
;; There are no free variables in this rewrite rule:
;; ST, INPUTS-1, and INPUTS-2 all occur in the conclusion.
;; ------------------------------------------------------------

(defthm
  legal-input-sequencep-of-append-implies-second

  (implies
   (legal-input-sequencep
    st
    (append inputs-1 inputs-2))

   (legal-input-sequencep
    (run-imp st inputs-1)
    inputs-2)))






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










;; ------------------------------------------------------------
;; A swappable pair is legal in its original order.
;; ------------------------------------------------------------

(defthm
  cl-two-imp-inputs-swappable-p-implies-original-order-legal

  (implies
   (cl-two-imp-inputs-swappable-p
    st input-1 input-2)

   (legal-input-sequencep
    st
    (list input-1 input-2)))
  :hints
  (("Goal"
    :in-theory
    (disable cl-checkpoint-body-input-p
	     legal-inputp
	     system-step))))


;; ------------------------------------------------------------
;; A swappable pair is also legal in the exchanged order.
;; ------------------------------------------------------------

(defthm
  cl-two-imp-inputs-swappable-p-implies-swapped-order-legal

  (implies
   (cl-two-imp-inputs-swappable-p
    st input-1 input-2)

   (legal-input-sequencep
    st
    (list input-2 input-1)))
    :hints
  (("Goal"
    :in-theory
    (disable cl-checkpoint-body-input-p
	     legal-inputp
	     system-step))))





;; ------------------------------------------------------------
;; The local POST/PRE swap condition is strong enough to
;; establish all state-quality assumptions needed after the
;; adjacent pair, in both execution orders.
;;
;; In particular:
;;
;;   * SWAP-ST is initially good and recovery-free;
;;   * both orders are legal;
;;   * both orders perform only non-recovery steps.
;;
;; Hence both resulting pair states are good and recovery-free.
;; ------------------------------------------------------------

(defthm
  cl-post-pre-swap-start-implies-good-state

  (implies
   (cl-post-pre-swap-start-p
    st m input-1 input-2)
   (good-state-p st))
  :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :in-theory
    (disable good-state-p))))


(defthm
  cl-post-pre-swap-start-implies-recovery-free-state

  (implies
   (cl-post-pre-swap-start-p
    st m input-1 input-2)
   (recovery-free-state-p st))
  :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :in-theory
     (disable
   ;  cl-post-pre-swap-start-p
     good-state-p
     cut-markers-in-transit-p
     legal-input-sequencep
     cm-cut-not-taken
     process-cut-step
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cl-checkpoint-body-input-p
     recovery-free-state-p))))



(defthm
  cl-post-pre-swap-start-implies-cp-inputs

  (implies
   (cl-post-pre-swap-start-p
    st m input-1 input-2)
   (cl-checkpoint-body-inputs-p (list input-1 input-2)))
  :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :in-theory
     (disable
     good-state-p
     cut-markers-in-transit-p
     legal-input-sequencep
     cm-cut-not-taken
     process-cut-step
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cl-checkpoint-body-input-p
     recovery-free-state-p))))



(defthm
  cl-post-pre-swap-start-implies-cp-inputs-2

  (implies
   (cl-post-pre-swap-start-p
    st m input-1 input-2)
   (cl-checkpoint-body-inputs-p (list input-2 input-1)))
  :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :in-theory
     (disable
     good-state-p
     cut-markers-in-transit-p
     legal-input-sequencep
     cm-cut-not-taken
     process-cut-step
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cl-checkpoint-body-input-p
     recovery-free-state-p))))


(defthm
  cl-post-pre-swap-start-implies-pair-states-good-and-recovery-free

  (implies
   (cl-post-pre-swap-start-p
    st m input-1 input-2)

   (and
    ;; Original order.
    (good-state-p
     (run-imp
      st
      (list input-1 input-2)))

    (recovery-free-state-p
     (run-imp
      st
      (list input-1 input-2)))

    ;; Swapped order.
    (good-state-p
     (run-imp
      st
      (list input-2 input-1)))

    (recovery-free-state-p
     (run-imp
      st
      (list input-2 input-1)))))
  :hints
  (("Goal"
       ; :use ((:instance cl-post-pre-two-imp-inputs-swappable-p ))
    :in-theory

    (disable
     cl-post-pre-swap-start-p
     good-state-p
     cut-markers-in-transit-p
     legal-input-sequencep
     cm-cut-not-taken
     process-cut-step
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cl-checkpoint-body-input-p
     run-imp
     recovery-free-state-p))))



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





;; ------------------------------------------------------------
;; Metadata commutativity for one adjacent POST/PRE swap.
;;
;; ST and M describe the implementation state and scan metadata
;; immediately before INPUT-POST executes in the original order.
;;
;; The theorem says that processing:
;;
;;     INPUT-POST ; INPUT-PRE
;;
;; and:
;;
;;     INPUT-PRE ; INPUT-POST
;;
;; produces exactly the same cut metadata after both inputs.
;; ------------------------------------------------------------

;; (defthm
;;   cl-post-pre-two-process-cut-steps-commute

;;   (let*
;;       (;; --------------------------------------------------
;;        ;; Original order: INPUT-POST ; INPUT-PRE
;;        ;; --------------------------------------------------

;;        (m-after-post
;;         (process-cut-step
;;          input-post
;;          st
;;          m))

;;        (st-after-post
;;         (system-step
;;          st
;;          input-post))

;;        (m-after-post-pre
;;         (process-cut-step
;;          input-pre
;;          st-after-post
;;          m-after-post))

;;        ;; --------------------------------------------------
;;        ;; Swapped order: INPUT-PRE ; INPUT-POST
;;        ;; --------------------------------------------------

;;        (m-after-pre
;;         (process-cut-step
;;          input-pre
;;          st
;;          m))

;;        (st-after-pre
;;         (system-step
;;          st
;;          input-pre))

;;        (m-after-pre-post
;;         (process-cut-step
;;          input-post
;;          st-after-pre
;;          m-after-pre)))

;;     (implies
;;      (cl-post-pre-swap-start-p
;;       st
;;       m
;;       input-post
;;       input-pre)

;;      (equal
;;       m-after-post-pre
;;       m-after-pre-post)))
;;   :hints
;;   (("Goal"
;;     :in-theory
;;     (disable good-state-p
;; 	     cut-meta-imp))))
