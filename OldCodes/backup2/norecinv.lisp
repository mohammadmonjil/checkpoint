(in-package "ACL2")
(include-book "model")
(include-book "good_state_invariants")




(defun no-recovery-step-p (input st)
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

(defun no-recovery-segment-p (inputs st)
  (if (endp inputs)
      t
    (let* ((input   (first inputs))
           (st-next (system-step st input)))
      (and
       (no-recovery-step-p input st)
       (no-recovery-segment-p
        (rest inputs)
        st-next)))))



;; ------------------------------------------------------------
;; Read :PROC-STATUS after updating FIELD of process I.
;;
;; If K is not I, process K is unchanged.
;;
;; If K is I:
;;   - when FIELD = :PROC-STATUS, the new status is VALUE;
;;   - otherwise, :PROC-STATUS is unchanged.
;; ------------------------------------------------------------

(defthm proc-status-of-g-after-proc-field-update
  (equal
   (g :proc-status
      (g k
         (s i
            (s field
               value
               (g i procs))
            procs)))

   (if (equal k i)
       (if (equal field :proc-status)
           value
         (g :proc-status
            (g i procs)))
     (g :proc-status
        (g k procs))))

  :hints
  (("Goal"
    :cases
    ((equal k i)
     (equal field :proc-status)))))


;; ------------------------------------------------------------
;; Updating one field of one process cannot introduce a
;; recovering process provided that:
;;
;;   - nobody was recovering before the update, and
;;
;;   - if the updated field is :PROC-STATUS, its new value
;;     is not :RECOVERING.
;;
;; If FIELD is anything other than :PROC-STATUS, the process
;; status is unchanged.
;; ------------------------------------------------------------

(defthm
  any-proc-recovering-p-preserved-by-non-recovering-proc-update

  (implies
   (and
    (not
     (any-proc-recovering-p
      ids
      procs))

    (or
     (not
      (equal field
             :proc-status))

     (not
      (equal value
             :recovering))))

   (not
    (any-proc-recovering-p
     ids
     (s i
        (s field
           value
           (g i procs))
        procs)))))



;; ------------------------------------------------------------
;; Reading :PROC-STATUS after replacing process I.
;;
;; If K = I, we read the status from the replacement P.
;; Otherwise, process K is unchanged.
;; ------------------------------------------------------------

(defthm proc-status-of-g-of-set-proc
  (equal
   (g :proc-status
      (g k
         (s i p procs)))

   (if (equal k i)
       (g :proc-status p)
     (g :proc-status
        (g k procs))))

  :hints
  (("Goal"
    :cases
    ((equal k i)))))


;;-----------------------------------------------------------
;; Replacing process I does not affect whether any process
;; is recovering, provided the replacement has the same
;; :PROC-STATUS as the old process.
;; ------------------------------------------------------------

(defthm
  any-proc-recovering-p-of-set-proc-same-status

  (implies
   (equal
    (g :proc-status p)
    (g :proc-status
       (g i procs)))

   (equal
    (any-proc-recovering-p
     ids
     (s i p procs))

    (any-proc-recovering-p
     ids
     procs))))

;; ------------------------------------------------------------
;; A step classified as NO-RECOVERY-STEP-P cannot introduce
;; a recovering process.
;;
;; If no process is recovering before the step, and the step
;; does not perform any recovery action, then no process is
;; recovering afterward.
;; ------------------------------------------------------------

(defthm no-recovery-step-p-preserves-no-proc-recovering
  (implies
   (no-recovery-step-p
     input
     st)

   (not
    (any-proc-recovering-p
     (proc-ids st)
     (procs
      (system-step st input))))))


;; ------------------------------------------------------------
;; No recovery message occurs in a single channel.
;; ------------------------------------------------------------

(defun no-recovery-msgs-in-channel-p (channel)
  (declare
   (xargs :measure (acl2-count channel)))

  (if (endp channel)
      t

    (and
     (not
      (equal
       (msg-type (first channel))
       :recovery))

     (no-recovery-msgs-in-channel-p
      (rest channel)))))


;; ------------------------------------------------------------
;; No recovery message occurs in any SRC -> DST channel for
;; the given destination list.
;; ------------------------------------------------------------

(defun no-recovery-msgs-for-dsts-p
    (src dsts channels)

  (declare
   (xargs :measure (acl2-count dsts)))

  (if (endp dsts)
      t

    (and
     (no-recovery-msgs-in-channel-p
      (channel-state
       src
       (first dsts)
       channels))

     (no-recovery-msgs-for-dsts-p
      src
      (rest dsts)
      channels))))


;; ------------------------------------------------------------
;; No recovery message occurs anywhere in the channel table.
;; ------------------------------------------------------------

(defun no-recovery-msgs-in-channels-p
    (srcs dsts channels)

  (declare
   (xargs :measure (acl2-count srcs)))

  (if (endp srcs)
      t

    (and
     (no-recovery-msgs-for-dsts-p
      (first srcs)
      dsts
      channels)

     (no-recovery-msgs-in-channels-p
      (rest srcs)
      dsts
      channels))))

;; ------------------------------------------------------------
;; The implementation is completely outside recovery:
;;
;;   1. no process is currently recovering;
;;   2. no recovery message remains anywhere in the channels.
;;
;; This is the invariant we actually need during a checkpoint
;; segment.
;; ------------------------------------------------------------

(defun recovery-free-state-p (st)
  (let ((ids (proc-ids st)))
    (and
     (not
      (any-proc-recovering-p
       ids
       (procs st)))

     (no-recovery-msgs-in-channels-p
      ids
      ids
      (channels st)))))


(defun cl-checkpoint-body-input-p (input)
  (let ((tp (ttype input)))
    (or (equal tp :nop)
        (equal tp :normal)
        (equal tp :receive)
        (equal tp :start-checkpoint))))


(defun cl-checkpoint-body-inputs-p (inputs)
  (declare
   (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      t
    (and
     (cl-checkpoint-body-input-p (first inputs))
     (cl-checkpoint-body-inputs-p (rest inputs)))))




;; ------------------------------------------------------------
;; Appending a non-recovery message to a recovery-free channel
;; preserves the fact that the channel contains no recovery
;; messages.
;;
;; This is the basic fact needed for NORMAL computation sends.
;; ------------------------------------------------------------

(defthm no-recovery-msgs-in-channel-p-of-snoc
  (implies
   (and
    (no-recovery-msgs-in-channel-p
     channel)

    (not
     (equal
      (msg-type msg)
      :recovery)))

   (no-recovery-msgs-in-channel-p
    (snoc channel msg)))

  :hints
  (("Goal"
    :induct
    (snoc channel msg))))


;; ------------------------------------------------------------
;; A compute message can safely be appended to a recovery-free
;; channel.
;;
;; CREATE-COMPUTE-MESSAGE always creates a :NORMAL message,
;; hence never a :RECOVERY message.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-in-channel-p-of-snoc-compute-message

  (implies
   (no-recovery-msgs-in-channel-p
    channel)

   (no-recovery-msgs-in-channel-p
    (snoc
     channel
     (create-compute-message
      local-state
      nbr)))))



;; ------------------------------------------------------------
;; Replacing one channel SRC -> DST by NEW-CHANNEL preserves
;; recovery-freedom for the destination scan, provided the
;; replacement channel itself contains no recovery messages.
;;
;; The channel table update has the same shape used throughout
;; the model:
;;
;;   (s dst
;;      (s src new-channel
;;         (g dst channels))
;;      channels)
;;
;; If SCAN-SRC = SRC and the current destination is DST, the
;; predicate sees NEW-CHANNEL.
;;
;; Every other channel is unchanged.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-for-dsts-p-of-set-channel

  (implies
   (and
    (no-recovery-msgs-for-dsts-p
     scan-src
     dsts
     channels)

    (no-recovery-msgs-in-channel-p
     new-channel))

   (no-recovery-msgs-for-dsts-p
    scan-src
    dsts
    (s dst
       (s src
          new-channel
          (g dst channels))
       channels)))

  :hints
  (("Goal"
   ; :induct dsts

    :cases
    ((equal scan-src src)
     ;(equal (first dsts) dst)
     ))))


;; ------------------------------------------------------------
;; Updating one channel by appending a COMPUTE message
;; preserves NO-RECOVERY-MSGS-FOR-DSTS-P.
;;
;; There are two relevant cases:
;;
;;   SCAN-SRC != I
;;      The updated channel belongs to another source row,
;;      so this row is unchanged.
;;
;;   SCAN-SRC = I
;;      If DST is one of the destinations being checked, the
;;      old I -> DST channel is recovery-free by the original
;;      row predicate.  Appending a COMPUTE message preserves
;;      that property because a COMPUTE message is :NORMAL.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-for-dsts-p-of-compute-channel-update

  (implies
   (no-recovery-msgs-for-dsts-p
    scan-src
    dsts
    channels)

   (no-recovery-msgs-for-dsts-p
    scan-src
    dsts
    (s dst
       (s i
          (snoc
           (g i
              (g dst channels))
           (create-compute-message
            local-state
            dst))
          (g dst channels))
       channels)))

  :hints
  (("Goal"
    :cases
    ((equal scan-src i)
     (equal (first dsts) dst))

    :in-theory
    (enable
     no-recovery-msgs-for-dsts-p))))
;; ------------------------------------------------------------
;; SEND-COMPUTE-MESSAGE preserves the absence of recovery
;; messages for one fixed source row.
;;
;; SEND-COMPUTE-MESSAGE walks through NBRS.  Whenever it sends
;; a message, it updates exactly one channel:
;;
;;      I -> (FIRST NBRS)
;;
;; by appending CREATE-COMPUTE-MESSAGE.
;;
;; We already proved:
;;
;;   1. appending a compute message preserves
;;      NO-RECOVERY-MSGS-IN-CHANNEL-P;
;;
;;   2. replacing one channel by a recovery-free channel
;;      preserves NO-RECOVERY-MSGS-FOR-DSTS-P.
;;
;; Therefore each recursive SEND-COMPUTE-MESSAGE update
;; preserves the whole row property.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-for-dsts-p-preserved-by-send-compute-message

  (implies
   (no-recovery-msgs-for-dsts-p
    scan-src
    dsts
    channels)

   (no-recovery-msgs-for-dsts-p
    scan-src
    dsts
    (send-compute-message
     local-state
     i
     nbrs
     channels)))

  :hints
  (("Goal"
    :induct
    (send-compute-message
     local-state
     i
     nbrs
     channels))))
;; ------------------------------------------------------------
;; SEND-COMPUTE-MESSAGE preserves recovery-free channels.
;;
;; The function may append compute messages to some outgoing
;; channels of process I.
;;
;; Every compute message is a :NORMAL message, so each append
;; preserves NO-RECOVERY-MSGS-IN-CHANNEL-P.
;;
;; Therefore, if there are no recovery messages anywhere
;; before SEND-COMPUTE-MESSAGE, there are still none afterward.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-in-channels-p-preserved-by-send-compute-message

  (implies
   (no-recovery-msgs-in-channels-p
    srcs
    dsts
    channels)

   (no-recovery-msgs-in-channels-p
    srcs
    dsts
    (send-compute-message
     local-state
     i
     nbrs
     channels)))

  :hints
  (("Goal"
    :induct
    (no-recovery-msgs-in-channels-p
    srcs
    dsts
    channels))))






;; ------------------------------------------------------------
;; Appending any non-recovery message to one channel preserves
;; NO-RECOVERY-MSGS-FOR-DSTS-P.
;;
;; This is generic enough for both:
;;
;;   - compute messages (:NORMAL)
;;   - checkpoint messages (:MARKER)
;;
;; and avoids proving separate row-update lemmas for each
;; message constructor.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-for-dsts-p-of-snoc-non-recovery-msg

  (implies
   (and
    (no-recovery-msgs-for-dsts-p
     scan-src
     dsts
     channels)

    (not
     (equal
      (msg-type msg)
      :recovery)))

   (no-recovery-msgs-for-dsts-p
    scan-src
    dsts
    (s dst
       (s src
          (snoc
           (channel-state
            src
            dst
            channels)
           msg)
          (g dst channels))
       channels)))

  :hints
  (("Goal"

    :cases
    ((equal scan-src src)
     (equal (first dsts) dst)))))


;; ------------------------------------------------------------
;; A checkpoint marker is not a recovery message.
;; ------------------------------------------------------------

(defthm create-marker-message-not-recovery
  (not
   (equal
    (msg-type
     (create-marker-message
      local-state
      sid))
    :recovery)))


;; ------------------------------------------------------------
;; SEND-MSG-ALL-OUTGOING-CHANNELS preserves recovery-freedom
;; for one fixed source row, provided the message being sent
;; is not a recovery message.
;;
;; At each recursive step, the function only appends MSG to
;; one channel:
;;
;;      SRC -> (FIRST DSTS-TO-SEND)
;;
;; The previously proved single-channel lemma handles that
;; update; the induction hypothesis handles the remaining
;; outgoing neighbors.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-for-dsts-p-preserved-by-send-msg-all-outgoing-channels

  (implies
   (and
    (no-recovery-msgs-for-dsts-p
     scan-src
     dsts
     channels)

    (not
     (equal
      (msg-type msg)
      :recovery)))

   (no-recovery-msgs-for-dsts-p
    scan-src
    dsts
    (send-msg-all-outgoing-channels
     msg
     src
     nbrs
     channels)))

  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg
     src
     nbrs
     channels))))


;; ------------------------------------------------------------
;; Sending a non-recovery message to all outgoing neighbors
;; preserves the absence of recovery messages in the entire
;; channel table.
;;
;; The row-level preservation theorem handles each SRC in the
;; outer scan.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-in-channels-p-preserved-by-send-msg-all-outgoing-channels

  (implies
   (and
    (no-recovery-msgs-in-channels-p
     srcs
     dsts
     channels)

    (not
     (equal
      (msg-type msg)
      :recovery)))

   (no-recovery-msgs-in-channels-p
    srcs
    dsts
    (send-msg-all-outgoing-channels
     msg
     src
     nbrs
     channels)))

  :hints
  (("Goal"

    :in-theory
    (disable
     no-recovery-msgs-for-dsts-p-preserved-by-send-msg-all-outgoing-channels))))



;; ------------------------------------------------------------
;; If a nonempty channel contains no recovery messages, then
;; the message currently returned from that channel is not a
;; recovery message.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-in-channel-p-implies-get-msg-not-recovery

  (implies
   (and
    (no-recovery-msgs-in-channel-p channel)
    (consp channel))

   (not
    (equal
     (msg-type
      (first channel))
     :recovery))))


;; ------------------------------------------------------------
;; If all channels from SRC to destinations in DSTS contain
;; no recovery messages, then the current message on SRC -> DST
;; is not a recovery message for any DST in DSTS.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-for-dsts-p-implies-get-msg-not-recovery

  (implies
   (and
    (no-recovery-msgs-for-dsts-p
     src
     dsts
     channels)

    (memberp dst dsts)

    (consp
     (channel-state
      src dst channels)))

   (not
    (equal
     (msg-type
      (get-msg-from-channel
       src dst channels))
     :recovery))))


;; ------------------------------------------------------------
;; Lift the one-source-row result over all source processes.
;;
;; Keep SRCS and DSTS separate so induction only changes SRCS.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-in-channels-p-implies-get-msg-not-recovery

  (implies
   (and
    (no-recovery-msgs-in-channels-p
     srcs
     dsts
     channels)

    (memberp src srcs)
    (memberp dst dsts)

    (consp
     (channel-state
      src dst channels)))

   (not
    (equal
     (msg-type
      (get-msg-from-channel
       src dst channels))
     :recovery)))

  :hints
  (("Goal"
 

    :in-theory
    (disable

     get-msg-from-channel))))


;; ------------------------------------------------------------
;; Removing the first message from a recovery-free channel
;; cannot introduce a recovery message.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-in-channel-p-of-cdr

  (implies
   (no-recovery-msgs-in-channel-p channel)

   (no-recovery-msgs-in-channel-p
    (cdr channel)))


;; ------------------------------------------------------------
;; Removing the head message from SENDER -> RECEIVER preserves
;; recovery-freedom for one fixed source row.
;;
;; If SCAN-SRC is not SENDER, the row is unchanged.
;;
;; If SCAN-SRC = SENDER, then when the destination scan reaches
;; RECEIVER, the original channel is recovery-free, and CDR of
;; a recovery-free channel is also recovery-free.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-for-dsts-p-preserved-by-remove-message-from-channel

  (implies
   (no-recovery-msgs-for-dsts-p
    scan-src
    dsts
    channels)

   (no-recovery-msgs-for-dsts-p
    scan-src
    dsts
    (remove-message-from-channel
     sender
     receiver
     channels)))

  :hints
  (("Goal"
    :cases
    ((equal scan-src sender)
     (equal (first dsts) receiver)))))
;; ------------------------------------------------------------
;; Removing the head message from one channel cannot introduce
;; a recovery message anywhere in the channel table.
;; ------------------------------------------------------------

(defthm
  no-recovery-msgs-in-channels-p-preserved-by-remove-message-from-channel

  (implies
   (no-recovery-msgs-in-channels-p
    srcs
    dsts
    channels)

   (no-recovery-msgs-in-channels-p
    srcs
    dsts
    (remove-message-from-channel
     sender
     receiver
     channels)))
  :hints (("Goal"
	   :in-theory (disable remove-message-from-channel))))
;; ------------------------------------------------------------
;; A checkpoint-body step cannot start recovery from a
;; recovery-free state.
;;
;; Allowed body inputs are:
;;
;;   :NOP
;;   :NORMAL
;;   :RECEIVE
;;   :START-CHECKPOINT
;;
;; None of these creates a recovery message from nothing.
;; Since there is no recovery message in any channel initially,
;; a :RECEIVE cannot consume a recovery message either.
;;
;; Hence no process becomes :RECOVERING and no recovery message
;; appears.
;; ------------------------------------------------------------

(defthm recovery-free-state-p-preserved-by-checkpoint-body-step
  (implies
   (and
    (recovery-free-state-p st)

    (good-state-p st)

    (legal-inputp st input)

    (cl-checkpoint-body-input-p input))

   (recovery-free-state-p
    (system-step st input)))
  :hints (("Goal"
	   :in-theory (disable create-marker-message
			       get-msg-from-channel
			       remove-message-from-channel))))





;; ------------------------------------------------------------
;; In a recovery-free state, every legal checkpoint-body input
;; is automatically a NO-RECOVERY step.
;;
;; RECOVERY-FREE-STATE-P gives:
;;
;;   1. no process is currently recovering;
;;   2. no channel contains a recovery message.
;;
;; CL-CHECKPOINT-BODY-INPUT-P restricts INPUT to:
;;
;;   :NOP
;;   :NORMAL
;;   :RECEIVE
;;   :START-CHECKPOINT
;;
;; For RECEIVE, LEGAL-INPUTP gives valid sender/receiver IDs
;; and a nonempty channel.  Recovery-freedom then implies that
;; GET-MSG-FROM-CHANNEL cannot return a :RECOVERY message.
;; ------------------------------------------------------------

(defthm
  recovery-free-checkpoint-body-implies-no-recovery-step

  (implies
   (and
    (recovery-free-state-p st)

    (legal-inputp st input)

    (cl-checkpoint-body-input-p input))

   (no-recovery-step-p
    input st))

  :hints
  (("Goal"

    :cases
    ((equal (ttype input) :nop)
     (equal (ttype input) :normal)
     (equal (ttype input) :receive)
     (equal (ttype input) :start-checkpoint))

    :in-theory
    (disable
     get-msg-from-channel)))))
