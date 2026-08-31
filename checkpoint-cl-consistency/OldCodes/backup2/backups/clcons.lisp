(in-package "ACL2")

(include-book "model")
(include-book "spec_input_gen")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Complete isolated checkpoint segment using the unified cut scan
;;
;; A valid segment:
;;   1. is nonempty;
;;   2. starts with :start-checkpoint;
;;   3. has no later checkpoint, recovery, crash, or unknown input;
;;   4. starts outside an active checkpoint or recovery;
;;   5. is legal from the supplied implementation state;
;;   6. does not consume a recovery message through a generic receive;
;;   7. first reaches full checkpoint completion after its final input.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ------------------------------------------------------------------
;; Inputs allowed after the initial :start-checkpoint
;; ------------------------------------------------------------------

(defun cl-checkpoint-body-input-p (input)
  (let ((tp (ttype input)))
    (or (equal tp :nop)
        (equal tp :normal)
        (equal tp :receive))))

(defun cl-checkpoint-body-inputs-p (inputs)
  (declare
   (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      t
    (and
     (cl-checkpoint-body-input-p (first inputs))
     (cl-checkpoint-body-inputs-p (rest inputs)))))

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

(defun cl-checkpoint-segment-initiator (input-seg)
  (pid (first input-seg)))

;; The implementation creates the SID using the initiator's counter
;; immediately before the :start-checkpoint input executes.
(defun cl-checkpoint-segment-sid (st input-seg)
  (let* ((i (cl-checkpoint-segment-initiator input-seg))
         (p (g i (procs st))))
    (list i (counter p))))

(defun cl-checkpoint-segment-trace (st input-seg)
  (run-imp-trace st input-seg))

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

(defun cl-checkpoint-segment-meta (st input-seg)
  (cut-result-meta
   (cl-checkpoint-segment-result st input-seg)))

(defun cl-checkpoint-segment-completion-index (st input-seg)
  (cut-result-idx
   (cl-checkpoint-segment-result st input-seg)))

(defun cl-checkpoint-segment-completep (st input-seg)
  (checkpoint-collection-complete-p
   (cl-checkpoint-segment-meta st input-seg)))

;; The scan index is end-exclusive. NTH at the completion index gives
;; the implementation state after the input that completed collection.
(defun cl-checkpoint-segment-completion-state (st input-seg)
  (nth
   (cl-checkpoint-segment-completion-index st input-seg)
   (cl-checkpoint-segment-trace st input-seg)))

(defun cl-checkpoint-segment-end-state (st input-seg)
  (run-imp st input-seg))

;; ------------------------------------------------------------------
;; Unified metadata accessors
;; ------------------------------------------------------------------

;; Global prerecording sequence, preserving original execution order.
(defun cl-checkpoint-segment-before-cut-inputs (st input-seg)
  (cm-inputs-before-cut
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

(defun cl-checkpoint-complete-segment-p (st input-seg)
  (and
   ;; The segment has a first input.
   (consp input-seg)

   ;; No older checkpoint or recovery phase is active initially.
   (not
    (any-snapshot-checkpointing-p st))

   (not
    (any-process-recovering-p st))

   ;; The first input starts the target checkpoint.
   (equal
    (ttype (first input-seg))
    :start-checkpoint)

   ;; Every later input is :nop, :normal, or :receive.
   ;; This excludes:
   ;;   :start-checkpoint
   ;;   :recover
   ;;   :crash
   ;;   unknown input types
   (cl-checkpoint-body-inputs-p
    (rest input-seg))

   ;; Every input is legal in the state where it executes.
   (legal-input-sequencep
    st input-seg)

   ;; No generic :receive consumes a recovery message.
   (cl-no-recovery-receive-sequencep
    st input-seg)

   ;; Full checkpoint collection completes:
   ;;   - every process has taken its cut;
   ;;   - every incoming marker has been received.
   (cl-checkpoint-segment-completep
    st input-seg)

   ;; The scan index is end-exclusive. Equality with the segment length
   ;; means completion was not reached before the final input.
   (equal
    (cl-checkpoint-segment-completion-index
     st input-seg)

    (len input-seg))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Channel-state invariant for one process
;;
;; For every incoming channel j -> i:
;;
;;   channel in the specification cut state
;;
;;       =
;;
;;   messages already recorded in i's channel snapshot
;;       ++
;;   normal messages still pending before the target marker
;;
;; Before process i takes its cut, the recorded-snapshot component is NIL.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; ------------------------------------------------------------------
;; Recognize the marker for the target checkpoint
;; ------------------------------------------------------------------

(defun cl-target-marker-p (msg target-sid)
  (and
   (equal (msg-type msg) :marker)
   (equal (sid msg) target-sid)))


;; ------------------------------------------------------------------
;; Normal-message prefix before the target marker
;; ------------------------------------------------------------------

;; Return the normal messages at the front of a physical channel that
;; occur before the marker for TARGET-SID.
;;
;; Examples:
;;
;;   (m1 m2 marker m3)  ->  (m1 m2)
;;   (m1 m2)            ->  (m1 m2)
;;   (marker m1 m2)     ->  NIL
;;
;; Under the isolated-checkpoint assumptions, an unrelated protocol
;; message should not occur before the target marker. If one does occur,
;; this function conservatively stops there.
(defun cl-normal-msg-prefix-before-marker
    (target-sid channel)
  ;; (declare
  ;;  (xargs :measure (acl2-count channel)))

  (if (endp channel)
      nil

    (let ((msg (first channel)))
      (cond
       ;; Stop immediately before the target marker.
       ((cl-target-marker-p msg target-sid)
        nil)

       ;; Preserve ordinary messages in FIFO order.
       ((equal (msg-type msg) :normal)
        (cons
         msg
         (cl-normal-msg-prefix-before-marker
          target-sid
          (rest channel))))

       ;; A different protocol message is not part of this pending
       ;; normal-message prefix.
       (t nil)))))


;; ------------------------------------------------------------------
;; Actual implementation channel-snapshot accessor
;; ------------------------------------------------------------------

;; Read the messages that the implementation has recorded for channel
;; j -> i in process i's snapshot entry for TARGET-SID.
;;
;; This accessor assumes that the target snapshot entry exists.
(defun cl-imp-recorded-channel-snapshot-msgs
    (i j target-sid imp-st)
  (let* ((p
          (g i (procs imp-st)))

         (entry
          (snapshot-entry target-sid p))

         (channel-snaps
          (snapshot-channel-snapshots entry)))

    (g j channel-snaps)))


;; ------------------------------------------------------------------
;; Snapshot component used by the invariant
;; ------------------------------------------------------------------

;; Before process i takes its cut, there is no recorded channel snapshot
;; for the target checkpoint. Therefore, the snapshot component of the
;; invariant is NIL.
;;
;; After process i takes its cut, use the actual recorded messages from
;; the implementation snapshot.
(defun cl-imp-channel-snapshot-part
    (i j target-sid m imp-st)
  (if (cm-cut-not-taken-p m i)
      nil

    (cl-imp-recorded-channel-snapshot-msgs
     i
     j
     target-sid
     imp-st)))


;; ------------------------------------------------------------------
;; Pending component used by the invariant
;; ------------------------------------------------------------------

;; The pending portion consists of normal messages that still belong to
;; the target distributed snapshot but have not yet been recorded by i.
;;
;; Before i takes its cut:
;;   no messages have been recorded, so the relevant pending prefix is
;;   the normal-message prefix before the target marker.
;;
;; After i takes its cut but before receiving j's marker:
;;   j remains in i's waiting-marker row, so the remaining normal prefix
;;   before the marker is still pending.
;;
;; After i receives j's marker:
;;   channel j -> i is closed for this snapshot, so the pending portion
;;   is NIL. Messages remaining in the physical channel are post-marker
;;   messages and do not belong to this snapshot.
(defun cl-imp-channel-pending-msgs
    (i j target-sid m imp-st)
  (if
      (or
       ;; Process i has not yet taken its cut.
       (cm-cut-not-taken-p m i)

       ;; Process i has taken its cut, but channel j -> i is open.
       (memberp
        j
        (cm-waiting-marker-for m i)))

      (cl-normal-msg-prefix-before-marker
       target-sid
       (channel-state
        j
        i
        (channels imp-st)))

    ;; The marker from j has already been consumed.
    nil))


;; ------------------------------------------------------------------
;; Channel invariant for one incoming channel j -> i
;; ------------------------------------------------------------------

(defun cl-spec-channel-snapshot-pending-match-p
    (i j target-sid m imp-st spec-cut-st)
  (equal
   ;; Channel j -> i at the specification cut.
   (channel-state
    j
    i
    (channels spec-cut-st))

   ;; Messages already recorded by i, followed by messages that are
   ;; still pending before j's marker.
   (append
    (cl-imp-channel-snapshot-part
     i
     j
     target-sid
     m
     imp-st)

    (cl-imp-channel-pending-msgs
     i
     j
     target-sid
     m
     imp-st))))


;; ------------------------------------------------------------------
;; Channel invariant over a list of incoming neighbors
;; ------------------------------------------------------------------

(defun cl-spec-channel-snapshot-pending-match-for-nbrs-p
    (i nbrs target-sid m imp-st spec-cut-st)

  (if (endp nbrs)
      t

    (and
     ;; Check the channel from the first incoming neighbor to i.
     (cl-spec-channel-snapshot-pending-match-p
      i
      (first nbrs)
      target-sid
      m
      imp-st
      spec-cut-st)

     ;; Check the remaining incoming channels.
     (cl-spec-channel-snapshot-pending-match-for-nbrs-p
      i
      (rest nbrs)
      target-sid
      m
      imp-st
      spec-cut-st))))


;; ------------------------------------------------------------------
;; Main invariant for one process i
;; ------------------------------------------------------------------

(defun cl-cut-channel-invariant-for-proc-p
    (i target-sid m imp-st spec-start-st)
  (let* (;; The incoming neighbors of process i.
         (p
          (g i (procs imp-st)))

         (nbrs
          (nbrs-from p))

         ;; Execute exactly the global prerecording inputs.
         ;;
         ;; This produces the specification state at the distributed
         ;; snapshot boundary represented by the current cut metadata.
         (spec-cut-st
          (run-spec
           spec-start-st
           (cm-inputs-before-cut m))))

    ;; Compare every incoming channel j -> i.
    (cl-spec-channel-snapshot-pending-match-for-nbrs-p
     i
     nbrs
     target-sid
     m
     imp-st
     spec-cut-st)))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; One-step preservation of the channel invariant for process i
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm cl-cut-channel-invariant-for-proc-p-preserved-by-one-step
  (implies
   (and
    ;; The channel equation currently holds for every channel j -> i.
    (cl-cut-channel-invariant-for-proc-p
     i
     target-sid
     m
     imp-st
     spec-start-st)

    ;; The target SID agrees with the scan metadata.
    (equal
     (cm-sid m)
     target-sid)

    ;; Process i belongs to the system.
    (memberp
     i
     (proc-ids imp-st))

    ;; The current input belongs to the checkpoint body. The initial
    ;; :start-checkpoint input is handled by a separate initialization
    ;; theorem.
    (cl-checkpoint-body-input-p input)

    ;; The implementation transition is legal.
    (legal-inputp imp-st input)

    ;; Recovery behavior is excluded from this checkpoint segment.
    (not
     (any-process-recovering-p imp-st))

    (cut-scan-no-recovery-step-p
     input
     imp-st)

    ;; The executing process is valid.
    (memberp
     (pid input)
     (proc-ids imp-st))

    ;; For a receive, the sender is a valid incoming neighbor.
    (implies
     (equal (ttype input) :receive)

     (and
      (memberp
       (sender input)
       (proc-ids imp-st))

      (memberp
       (sender input)
       (nbrs-from
        (g (pid input)
           (procs imp-st))))

      ;; The receive consumes either an ordinary message or the marker
      ;; belonging to this checkpoint.
      (let ((msg
             (current-msg-for-receive
              input
              imp-st)))
        (or
         (equal
          (msg-type msg)
          :normal)

         (and
          (equal
           (msg-type msg)
           :marker)

          (equal
           (sid msg)
           target-sid))))))

    ;; Metadata rows have the expected topology.
    (waiting-marker-from-rows-uniquep-p
     (proc-ids imp-st)
     m)

    (nbrs-from-rows-uniquep-p
     (proc-ids imp-st)
     (procs imp-st))

    (waiting-marker-from-subset-of-nbrs-from-p
     (proc-ids imp-st)
     m
     (procs imp-st))

    ;; This auxiliary invariant captures the FIFO position of the target
    ;; markers. In particular:
    ;;
    ;;   - before sender j takes its cut, channel j -> i contains only
    ;;     ordinary messages relevant to the current boundary;
    ;;
    ;;   - after sender j takes its cut, but while channel j -> i remains
    ;;     open, its target marker occurs after the pending normal prefix;
    ;;
    ;;   - after i receives the marker, the pending component is NIL.
    (cl-cut-channel-marker-order-for-proc-p
     i
     target-sid
     m
     imp-st)

    ;; Once i has taken its cut, the scan metadata and the actual
    ;; implementation snapshot agree about the open incoming channels.
    (implies
     (not
      (cm-cut-not-taken-p m i))

     (let* ((p
             (g i
                (procs imp-st)))

            (entry
             (snapshot-entry
              target-sid
              p)))

       (and
        (memberp
         target-sid
         (snapshot-ids p))

        (equal
         (cm-waiting-marker-for m i)

         (snapshot-waiting-marker-from
          entry))

        ;; While at least one incoming channel is open, normal receives
        ;; must still be recorded in the target snapshot.
        (implies
         (consp
          (cm-waiting-marker-for m i))

         (equal
          (snapshot-status entry)
          :checkpointing))))))

   ;; The channel equation remains true after executing one
   ;; implementation step and performing the corresponding metadata
   ;; update.
   (cl-cut-channel-invariant-for-proc-p
    i
    target-sid

    (process-cut-step
     input
     imp-st
     m)

    (system-step
     imp-st
     input)

    spec-start-st)))
