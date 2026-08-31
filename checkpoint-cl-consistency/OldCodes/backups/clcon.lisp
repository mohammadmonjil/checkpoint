(in-package "ACL2")

(include-book "model")
(include-book "spec_input_gen")
(include-book "good_state_invariants")
(include-book "channel_equivalence")
(include-book "segment_lemmas")

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
;; Ordinary specification input executable in ST
;;
;; The reordered specification execution contains:
;;   - :nop
;;   - :normal
;;   - :receive of a normal message
;;
;; Marker and recovery receives are excluded.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun spec-legal-inputp (st input)
  (let* ((tp       (ttype input))
         (i        (pid input))
         (j        (sender input))
         (ids      (proc-ids st))
         (procs    (procs st))
         (channels (channels st)))
    (cond
     ;; NOP is always legal.
     ((equal tp :nop)
      t)

     ;; A normal step requires a valid process.
     ((equal tp :normal)
      (memberp i ids))

     ;; A specification receive must consume a normal message
     ;; from a valid incoming channel.
     ((equal tp :receive)
      (and
       (memberp i ids)

       (memberp j ids)

       (memberp
        j
        (nbrs-from
         (g i procs)))

       (consp
        (channel-state
         j
         i
         channels))

       (equal
        (msg-type
         (get-msg-from-channel
          j
          i
          channels))
        :normal)))

     ;; Protocol inputs are not specification inputs.
     (t nil))))


(defun spec-legal-input-sequencep (st inputs)
  (declare
   (xargs :measure (acl2-count inputs)))

  (if (endp inputs)
      t

    (and
     (spec-legal-inputp
      st
      (first inputs))

     (spec-legal-input-sequencep
      (spec-step
       st
       (first inputs))
      (rest inputs)))))




(defun checkpoint-prefix-input-type-p (input)
     (or
      (equal
       (ttype  input)
       :start-checkpoint)

      (cl-checkpoint-body-input-p input)))


(defun checkpoint-prefix-input-types-p (inputs)
  (declare
   (xargs :measure (acl2-count inputs)))

  (if (endp inputs)
      t

    (and
      (checkpoint-prefix-input-type-p
       (first inputs))

     (checkpoint-prefix-input-types-p
      (rest inputs)))))



(defun spec-compatible-input-sequence-induct
    (imp-st spec-st inputs)

  (if (endp inputs)

      ;; Makes both state arguments relevant to ACL2.
      (cons imp-st spec-st)

    (spec-compatible-input-sequence-induct
     (system-step imp-st (first inputs))

     (spec-step
      spec-st
      (spec-compatible-input
       (first inputs)
       imp-st))

     (rest inputs))))





(defun marker-for-sid-in-channel-p (target-sid channel)
  (declare
   (xargs :measure (acl2-count channel)))

  (if (endp channel)
      nil

    (or
     (and
      (equal
       (msg-type (first channel))
       :marker)

      (equal
       (sid (first channel))
       target-sid))

     (marker-for-sid-in-channel-p
      target-sid
      (rest channel)))))



(defun cut-frontier-markers-for-dsts-p
    (src dsts target-sid m channels)

  (declare
   (xargs :measure (acl2-count dsts)))

  ;; If SRC has not taken its cut yet,
  ;; there is no frontier obligation from SRC.
  (if (cm-cut-not-taken-p m src)
      t
    ;; SRC has taken its cut.
    ;; Check each destination that has not yet taken its cut.
    (if (endp dsts)
        t
      (let ((dst (first dsts)))
        (and
         ;; If DST has not taken its cut,
         ;; the marker must still be on SRC -> DST.
         (if (cm-cut-not-taken-p m dst)
             (marker-for-sid-in-channel-p
              target-sid
              (channel-state
               src
               dst
               channels))
           ;; DST has already taken its cut,
           ;; so no frontier requirement exists.
           t)

         (cut-frontier-markers-for-dsts-p
          src
          (rest dsts)
          target-sid
          m
          channels))))))


(defun cut-frontier-markers-for-srcs-p
    (srcs target-sid m procs channels)

  (declare
   (xargs :measure (acl2-count srcs)))

  (if (endp srcs)
      t

    (let ((src (first srcs)))

      (and
       (cut-frontier-markers-for-dsts-p
        src
        (nbrs-to
         (g src procs))
        target-sid
        m
        channels)

       (cut-frontier-markers-for-srcs-p
        (rest srcs)
        target-sid
        m
        procs
        channels)))))



(defun cut-frontier-markers-p (m st)
  (cut-frontier-markers-for-srcs-p
   (proc-ids st)
   (cm-sid m)
   m
   (procs st)
   (channels st)))



(defthm not-memberp-after-remove1-equal-when-uniquep
  (implies
   (uniquep xs)

   (not
    (memberp
     x
     (remove1-equal x xs)))))

(defthm good-state-p-implies-uniquep-proc-ids
  (implies
   (good-state-p st)

   (uniquep
    (proc-ids st))))

(defthm
  snapshot-counters-good-for-procs-p-implies-proc-good

  (implies
   (and
    (snapshot-counters-good-for-procs-p
     ids
     procs)

    (memberp i ids))

   (proc-snapshot-counter-good-p
    i
    (g i procs))))


(defthm
  good-state-p-implies-proc-snapshot-counter-good-p

  (implies
   (and
    (good-state-p st)

    (memberp i
             (proc-ids st)))

   (proc-snapshot-counter-good-p
    i
    (g i
       (procs st)))))


(defthm
  own-checkpoint-sids-before-counter-p-implies-current-sid-not-member

  (implies
   (own-checkpoint-sids-before-counter-p
    i
    ctr
    sids)

   (not
    (memberp
     (list i ctr)
     sids))))

(defthm
  good-state-p-implies-current-sid-fresh

  (implies
   (and
    (good-state-p st)

    (memberp i
             (proc-ids st)))

   (not
    (memberp
     (list
      i
      (counter
       (g i
          (procs st))))

     (snapshot-ids
      (g i
         (procs st)))))))


(defthm marker-for-sid-in-channel-p-of-snoc-marker
  (implies
   (equal
    (msg-type msg)
    :marker)

   (marker-for-sid-in-channel-p
    (sid msg)
    (snoc channel msg))))


(defthm
  marker-for-sid-after-send-msg-all-outgoing-channels

  (implies
   (and
    (memberp dst nbrs)

    (equal
     (msg-type msg)
     :marker)

    (equal
     (sid msg)
     target-sid))

   (marker-for-sid-in-channel-p
    target-sid

    (channel-state
     src
     dst
     (send-msg-all-outgoing-channels
      msg
      src
      nbrs
      channels)))))


(defthm initiator-not-cut-not-taken-of-make-cut-meta
  (implies
   (uniquep
    (proc-ids st))

   (not
    (cm-cut-not-taken-p
     (make-cut-meta sid initiator st)
     initiator))))

(defthm
  cut-frontier-markers-for-dsts-p-of-s-after-cut-input-sequence

  (equal
   (cut-frontier-markers-for-dsts-p
    src
    dsts
    target-sid
    (s :after-cut-input-sequence val m)
    channels)

   (cut-frontier-markers-for-dsts-p
    src
    dsts
    target-sid
    m
    channels)))


(defthm cm-sid-of-cm-add-after-cut-input-sequence
  (equal
   (cm-sid
    (cm-add-after-cut-input-sequence m input))
   (cm-sid m)))


(defthm sid-of-make-cut-meta
  (equal
   (cm-sid
    (make-cut-meta sid i st))
   sid))


(defthm nbrs-to-of-start-checkpoint-helper
  (equal
   (g :nbrs-to
      (g src
         (start-checkpoint-helper procs i)))
   (g :nbrs-to
      (g src procs))))


(defthm cut-frontier-markers-for-srcs-p-of-start-checkpoint-helper
  (equal
   (cut-frontier-markers-for-srcs-p
    srcs
    target-sid
    m
    (start-checkpoint-helper procs i)
    channels)

   (cut-frontier-markers-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :in-theory (disable cut-frontier-markers-for-dsts-p
			start-checkpoint-helper))))



(defthm
  cut-frontier-markers-for-srcs-p-of-cm-add-after-cut-input-sequence

  (equal
   (cut-frontier-markers-for-srcs-p
    srcs
    target-sid
    (cm-add-after-cut-input-sequence m input)
    procs
    channels)

   (cut-frontier-markers-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)))


(defthm memberp-car-when-subset
  (implies
   (and
    (consp xs)
    (subset xs ys))
   (memberp (car xs) ys))

  :hints
  (("Goal"
    :in-theory
    (enable subset))))



(defthm
  cut-frontier-markers-for-dsts-p-after-send-msg-all-outgoing-channels-gen

  (implies
   (and
    (subset dsts nbrs)
    (equal (msg-type msg) :marker)
    (equal (sid msg) target-sid))

   (cut-frontier-markers-for-dsts-p
    src
    dsts
    target-sid
    m
    (send-msg-all-outgoing-channels
     msg
     src
     nbrs
     channels)))

  :hints
  (("Goal"
    :in-theory
    (disable  marker-for-sid-in-channel-p
	      cm-cut-not-taken-p))))


(defthm
  cut-frontier-markers-for-dsts-p-after-send-msg-all-outgoing-channels

  (implies
   (and
    (equal (msg-type msg) :marker)
    (equal (sid msg) target-sid))

   (cut-frontier-markers-for-dsts-p
    src
    dsts
    target-sid
    m
    (send-msg-all-outgoing-channels
     msg
     src
     dsts
     channels)))
  :hints (("Goal"
	   :in-theory (disable send-msg-all-outgoing-channels))))



(defthm cut-frontier-markers-for-srcs-p-helper
  (implies
   (and
    (subset
     srcs
     (cons initiator
           (g :cut-not-taken m)))

    (cut-frontier-markers-for-dsts-p
     initiator
     (g :nbrs-to
        (g initiator procs))
     target-sid
     m
     channels))

   (cut-frontier-markers-for-srcs-p
    srcs target-sid m procs channels)))

(defthm subset-cons-remove1-equal
  (subset
   xs
   (cons a
         (remove1-equal a xs))))


(defthm proc-ids-subset-initiator-and-cut-not-taken-after-make-cut-meta
  (subset
   (g :proc-ids st)

   (cons
    initiator
    (g :cut-not-taken
       (make-cut-meta
        target-sid
        initiator
        st)))))


(defthm
  cut-frontier-markers-for-srcs-p-after-make-cut-meta-and-send-marker

  (implies
   (and
    (equal (msg-type msg) :marker)
    (equal (sid msg) target-sid))

   (cut-frontier-markers-for-srcs-p
    (g :proc-ids st)
    target-sid

    (make-cut-meta
     target-sid
     initiator
     st)

    (g :procs st)

    (send-msg-all-outgoing-channels
     msg
     initiator
     (g :nbrs-to
        (g initiator
           (g :procs st)))
     (g :channels st))))
  :hints
  (("Goal"
    :use
    ((:instance
      cut-frontier-markers-for-srcs-p-helper
      (srcs
       (g :proc-ids st))
      (m
       (make-cut-meta
        target-sid
        initiator
        st))
      (procs
       (g :procs st))

      (channels
       (send-msg-all-outgoing-channels
        msg
        initiator
        (g :nbrs-to
           (g initiator
              (g :procs st)))
        (g :channels st))))

     (:instance
      cut-frontier-markers-for-dsts-p-after-send-msg-all-outgoing-channels

      (src initiator)

      (dsts
       (g :nbrs-to
          (g initiator
             (g :procs st))))

      (m
       (make-cut-meta
        target-sid
        initiator
        st))

      (channels
       (g :channels st)))

     (:instance
      proc-ids-subset-initiator-and-cut-not-taken-after-make-cut-meta
      (initiator initiator)
      (target-sid target-sid)
      (st st))))))



(defthm
  cut-frontier-markers-p-after-start-checkpoint

  (implies
   (and
    (good-state-p st)

    (legal-inputp st input)

    (equal
     (ttype input)
     :start-checkpoint)

    (not
     (any-snapshot-checkpointing-p st))

    (not
     (any-process-recovering-p st)))

   (let*
       ((i
         (pid input))

        (target-sid
         (list
          i
          (counter
           (g i (procs st)))))

        (m0
         (make-cut-meta
          target-sid
          i
          st)))

     (cut-frontier-markers-p
      (process-cut-step
       input
       st
       m0)

      (system-step
       st
       input))))
  :hints (("Goal"
	   :in-theory (disable good-state-p
			       start-checkpoint-helper
			       create-marker-message
			       make-cut-meta
			       cm-add-after-cut-input-sequence
			      ; legal-inputp
			       ))))













































(defthm cl-checkpoint-body-inputs-p-of-append
  (equal
   (cl-checkpoint-body-inputs-p
    (append xs ys))

   (and
    (cl-checkpoint-body-inputs-p xs)
    (cl-checkpoint-body-inputs-p ys)))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (cl-checkpoint-body-inputs-p)
     (cl-checkpoint-body-input-p)))))

(defthm cl-checkpoint-body-inputs-p-of-two-inputs
  (equal
   (cl-checkpoint-body-inputs-p
    (list input-1 input-2))

   (and
    (cl-checkpoint-body-input-p input-1)
    (cl-checkpoint-body-input-p input-2)))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (cl-checkpoint-body-inputs-p)
     (cl-checkpoint-body-input-p)))))


(defthm
  cl-checkpoint-body-input-p-implies-checkpoint-prefix-input-type-p

  (implies
   (cl-checkpoint-body-input-p input)

   (checkpoint-prefix-input-type-p input)))


(defthm
  checkpoint-prefix-input-types-p-when-first-start-and-rest-body

  (implies
   (and
    (equal
     (ttype (first prefix-inputs))
     :start-checkpoint)

    (cl-checkpoint-body-inputs-p
     (rest prefix-inputs)))

   (checkpoint-prefix-input-types-p
    prefix-inputs)))


  
(defthm cut-scan-no-recovery-segment-p-of-append
  (equal
   (cut-scan-no-recovery-segment-p
    (append xs ys)
    st)

   (and
    (cut-scan-no-recovery-segment-p
     xs
     st)

    (cut-scan-no-recovery-segment-p
     ys
     (run-imp st xs))))

  :hints
  (("Goal"
    :in-theory
    (disable
     system-step
     cut-scan-no-recovery-step-p))))


(defthm cut-scan-no-recovery-segment-p-of-two-inputs
  (equal
   (cut-scan-no-recovery-segment-p
    (list input-1 input-2)
    st)

   (and
    (cut-scan-no-recovery-step-p
     input-1
     st)

    (cut-scan-no-recovery-step-p
     input-2
     (system-step st input-1))))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (cut-scan-no-recovery-segment-p)

     (cut-scan-no-recovery-step-p
      system-step)))))


(defthm cut-scan-no-recovery-step-p-of-input-1-after-prefix
  (implies
   (cut-scan-no-recovery-segment-p
    (append prefix-inputs
            (list input-1 input-2))
    st)

   (cut-scan-no-recovery-step-p
    input-1
    (run-imp st prefix-inputs)))

  :hints
  (("Goal"
    :in-theory
    (disable
     cut-scan-no-recovery-segment-p
     cut-scan-no-recovery-step-p
     system-step))))


(defthm cut-scan-no-recovery-step-p-of-input-2-after-prefix
  (implies
   (cut-scan-no-recovery-segment-p
    (append prefix-inputs
            (list input-1 input-2))
    st)

   (cut-scan-no-recovery-step-p
    input-2
    (system-step
     (run-imp st prefix-inputs)
     input-1)))

  :hints
  (("Goal"
    :in-theory
    (disable
     cut-scan-no-recovery-segment-p
     cut-scan-no-recovery-step-p
     system-step))))


(defthm cut-scan-no-recovery-step-p-of-input-2-after-prefix
  (implies
   (cut-scan-no-recovery-segment-p
    (append prefix-inputs
            (list input-1 input-2))
    st)

   (cut-scan-no-recovery-step-p
    input-2
    (system-step
     (run-imp st prefix-inputs)
     input-1)))

  :hints
  (("Goal"

    :in-theory
    (disable
     cut-scan-no-recovery-segment-p
     cut-scan-no-recovery-step-p
     system-step))))




(defthm legal-input-sequencep-of-append
  (equal
   (legal-input-sequencep
    st
    (append xs ys))

   (and
    (legal-input-sequencep
     st xs)

    (legal-input-sequencep
     (run-imp st xs)
     ys)))

  :hints
  (("Goal"
    :in-theory
    (disable
     system-step
     legal-inputp))))



(defthm legal-inputp-of-input-1-from-legal-two-input-suffix
  (implies
   (legal-input-sequencep
    st
    (list input-1 input-2))

   (legal-inputp
    st
    input-1))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (legal-input-sequencep)

     (legal-inputp
      system-step)))))

(defthm legal-inputp-of-input-1-after-prefix
  (implies
   (legal-input-sequencep
    st
    (append prefix-inputs
            (list input-1 input-2)))

   (legal-inputp
    (run-imp st prefix-inputs)
    input-1))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (legal-input-sequencep)

     (
      legal-inputp
      run-imp
      system-step)))))

(defthm legal-inputp-of-input-2-after-prefix-input-2
  (implies
   (legal-input-sequencep
    st
    (append prefix-inputs
            (list input-1 input-2)))

   (legal-inputp
    (system-step
     (run-imp st prefix-inputs)
     input-1)
    input-2))

  :hints
  (("Goal"
:in-theory
     (disable
      legal-inputp
      system-step))))


(defthm pid-of-spec-compatible-input
  (equal
   (pid
    (spec-compatible-input input st))
   (pid input)))

(defthm ttype-of-spec-compatible-input-when-normal
  (implies
   (equal (ttype input) :normal)

   (equal
    (ttype (spec-compatible-input input st))
    :normal)))

(defthm ttype-of-spec-compatible-input-when-normal-receive
  (implies
   (and
    (equal (ttype input) :receive)

    (equal
     (msg-type
      (current-msg-for-receive input st))
     :normal))

   (equal
    (ttype (spec-compatible-input input st))
    :receive)))

(defthm ttype-of-spec-compatible-input-when-non-normal-receive
  (implies
   (and
    (equal (ttype input) :receive)

    (not
     (equal
      (msg-type
       (current-msg-for-receive input st))
      :normal)))

   (equal
    (ttype (spec-compatible-input input st))
    :nop)))

(defthm ttype-of-spec-compatible-input-when-not-normal-or-receive
  (implies
   (and
    (not (equal (ttype input) :normal))
    (not (equal (ttype input) :receive)))

   (equal
    (ttype (spec-compatible-input input st))
    :nop)))

(defthm proc-ids-of-step-rcv

   (equal
    (proc-ids
     (step-rcv st i j))
    (proc-ids st)))

(defthm proc-ids-of-step-normal

   (equal
    (proc-ids
     (step-normal st i ))
    (proc-ids st)))

(defthm proc-ids-of-step-normal

   (equal
    (proc-ids
     (step-normal st i ))
    (proc-ids st)))

(defthm proc-ids-of-handle-normal-msg
  (equal
   (g :proc-ids
      (handle-normal-msg st i j msg))
   (g :proc-ids st)))


(defthm
  imp-spec-equivalent-p-after-spec-compatible-input-one-step

  (implies
   (and
    (good-state-p imp-st)

    (good-spec-state-p spec-st)

    (imp-spec-equivalent-p
     imp-st
     spec-st)

    (legal-inputp
     imp-st
     input)

    (checkpoint-prefix-input-type-p input)

    (cut-scan-no-recovery-step-p
     input
     imp-st))

   (imp-spec-equivalent-p
    (system-step
     imp-st
     input)

    (spec-step
     spec-st
     (spec-compatible-input
      input
      imp-st))))
    :hints
  (("Goal"
    :cases
    ((equal (ttype input)
            :nop)
     (equal (ttype input)
            :start-checkpoint)
     (equal (ttype input)
            :normal)
     (equal (ttype input)
            :receive))
    :in-theory
    (disable
     imp-spec-equivalent-p
     good-state-p
     step-checkpoint
     step-normal
     handle-normal-msg-core
     handle-marker-msg
     ;step-rcv
     spec-step-rcv
     spec-step-normal
     get-msg-from-channel

     good-spec-state-p))
("Subgoal 1.2'"
 :use
 ((:instance
   imp-spec-equivalent-p-of-step-rcv-marker

   (i
    (pid input))

   (j
    (sender input)))

  (:instance
   consp-of-channel-state-when-get-msg-from-channel-has-marker-type
   (j
    (sender input))

   (k
    (pid input))

   (channels
    (channels imp-st)))))))

(defthm nbrs-from-of-spec-proc-when-procs-equivalent-p
  (implies
   (and
    (procs-equivalent-p
     ids
     imp-procs
     spec-procs)

    (memberp i ids))

   (equal
    (nbrs-from
     (g i spec-procs))

    (nbrs-from
     (g i imp-procs)))))

(defthm nbrs-from-of-spec-proc-when-imp-spec-equivalent-p
  (implies
   (and
    (imp-spec-equivalent-p
     imp-st
     spec-st)

    (memberp
     i
     (proc-ids spec-st)))

   (equal
    (nbrs-from
     (g i (procs spec-st)))

    (nbrs-from
     (g i (procs imp-st))))))

(defthm spec-channel-consp-when-imp-spec-channels-equivalent-p
  (implies
   (and
    (imp-spec-channels-equivalent-p
     ids imp-st spec-st)

    (memberp dst ids)

    (memberp
     src
     (nbrs-from
      (g dst (procs imp-st))))

    (equal
     (msg-type
      (get-msg-from-channel
       src dst
       (channels imp-st)))
     :normal))

   (consp
    (channel-state
     src dst
     (channels spec-st)))))

(defthm spec-channel-head-normal-when-imp-spec-channels-equivalent-p
  (implies
   (and
    (imp-spec-channels-equivalent-p
     ids imp-st spec-st)

    (memberp dst ids)

    (memberp
     src
     (nbrs-from
      (g dst (procs imp-st))))
    (equal
     (msg-type
      (get-msg-from-channel
       src dst
       (channels imp-st)))
     :normal))

   (equal
    (msg-type
     (get-msg-from-channel
      src dst
      (channels spec-st)))
    :normal)))


(defthm
  spec-compatible-input-one-step-is-spec-legal

  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)

    (imp-spec-equivalent-p
     imp-st
     spec-st)

    (legal-inputp
     imp-st
     input)

    (checkpoint-prefix-input-type-p input)
    (cut-scan-no-recovery-step-p
     input
     imp-st))

   (spec-legal-inputp
    spec-st
    (spec-compatible-input
     input
     imp-st)))

  :hints
  (("Goal"
    :in-theory
    (disable
     imp-spec-equivalent-p
     good-state-p
     good-spec-state-p
     get-msg-from-channel))

   ("Subgoal 2"
    :in-theory
    (e/d
     (imp-spec-equivalent-p)

     (good-state-p
      good-spec-state-p
      get-msg-from-channel
      imp-spec-channels-equivalent-p)))))


(defthm checkpoint-prefix-input-types-p-when-start-and-body-append
  (implies
   (and
    (equal
     (ttype (first prefix-inputs))
     :start-checkpoint)

    (cl-checkpoint-body-inputs-p
     (append
      (rest prefix-inputs)
      (list input-i input-j))))

   (checkpoint-prefix-input-types-p
    prefix-inputs)))

(defthm
  spec-compatible-input-sequence-is-spec-legal

  (implies
   (and
    (good-state-p
     imp-start-st)

    (good-spec-state-p
     spec-start-st)

    (imp-spec-equivalent-p
     imp-start-st
     spec-start-st)

    (legal-input-sequencep
     imp-start-st
     prefix-inputs)

    ;; Every input satisfies the input-type hypothesis
    ;; of the one-step theorem.
    (checkpoint-prefix-input-types-p
     prefix-inputs)

    ;; Every step satisfies the no-recovery hypothesis
    ;; of the one-step theorem.
    (cut-scan-no-recovery-segment-p
     prefix-inputs
     imp-start-st))

   (spec-legal-input-sequencep
    spec-start-st

    (spec-compatible-input-sequence
     imp-start-st
     prefix-inputs)))

  :hints
  (("Goal"
    :induct
    (spec-compatible-input-sequence-induct
     imp-start-st
     spec-start-st
     prefix-inputs)

    :in-theory
    (disable
     good-state-p
      good-spec-state-p
      imp-spec-equivalent-p

      legal-inputp
      spec-legal-inputp

      cl-checkpoint-body-input-p
      cut-scan-no-recovery-step-p

      checkpoint-prefix-input-type-p
      spec-compatible-input
      system-step
      spec-step))))



(defthm
  imp-spec-equivalent-p-after-spec-compatible-input-sequence

  (implies
   (and
    (good-state-p imp-st)

    (good-spec-state-p spec-st)

    (imp-spec-equivalent-p
     imp-st
     spec-st)

    (legal-input-sequencep
     imp-st
     inputs)

    (checkpoint-prefix-input-types-p
     inputs)

    (cut-scan-no-recovery-segment-p
     inputs
     imp-st))

   (imp-spec-equivalent-p
    (run-imp
     imp-st
     inputs)

    (run-spec
     spec-st
     (spec-compatible-input-sequence
      imp-st
      inputs))))

  :hints
  (("Goal"
    :induct
    (spec-compatible-input-sequence-induct
     imp-st
     spec-st
     inputs)

    :in-theory
    (disable
     good-state-p
      good-spec-state-p
      imp-spec-equivalent-p
      legal-inputp
      cut-scan-no-recovery-step-p
      system-step
      checkpoint-prefix-input-type-p
      spec-step
      spec-compatible-input))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Two specification inputs are swappable
;;
;; This predicate states only the operational conditions required for
;; commutativity. It does not classify either input as pre-cut or post-cut.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cl-two-spec-inputs-swappable-p
    (st input-1 input-2)
  (let* ((st-after-input-1
          (spec-step st input-1))

         (st-after-input-2
          (spec-step st input-2)))

    (and
     ;; Process and channel structures are well formed.
     (good-spec-state-p st)

     ;; Events of one process must retain their original local order.
     (not
      (equal
       (pid input-1)
       (pid input-2)))

     ;; Both inputs are executable before either input occurs.
     ;;
     ;; For a receive, this rules out the case where the other input
     ;; creates the message being consumed.
     (spec-legal-inputp
      st
      input-1)

     (spec-legal-inputp
      st
      input-2)

     ;; Both inputs remain executable in the opposite execution order.
     (spec-legal-inputp
      st-after-input-1
      input-2)

     (spec-legal-inputp
      st-after-input-2
      input-1))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bottom two-step commutativity theorem
;;
;; No implementation state or cut metadata appears here.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm channel-state-of->channel-different-sender
  (implies
   (not (equal i-1 i-2))

   (equal
    (channel-state
     i-2 j-2
     (>channel i-1 j-1 val channels))

    (channel-state
     i-2 j-2
     channels)))

  :hints
  (("Goal"
    :cases
    ((equal j-1 j-2)))))

(defthm channel-updates-commute-for-different-senders
  (implies
   (not (equal i-1 i-2))

   (equal
    (>channel
     i-2 j-2 val-2
     (>channel
      i-1 j-1 val-1
      channels))

    (>channel
     i-1 j-1 val-1
     (>channel
      i-2 j-2 val-2
      channels))))

  :hints
  (("Goal"
    :cases
    ((equal j-1 j-2)))))

(defthm send-compute-message-of->channel-different-sender
  (implies
   (not (equal i-1 i-2))

   (equal
    (send-compute-message
     local-2
     i-2
     nbrs-2
     (>channel
      i-1 j-1 val channels))

    (>channel
     i-1 j-1 val
     (send-compute-message
      local-2
      i-2
      nbrs-2
      channels)))))

(defthm send-compute-message-commutes-for-different-processes
  (implies
   (not (equal i-1 i-2))

   (equal
    ;; Process i-1 sends first, then process i-2.
    (send-compute-message
     local-2
     i-2
     nbrs-2
     (send-compute-message
      local-1
      i-1
      nbrs-1
      channels))

    ;; Process i-2 sends first, then process i-1.
    (send-compute-message
     local-1
     i-1
     nbrs-1
     (send-compute-message
      local-2
      i-2
      nbrs-2
      channels)))))


(defthm car-of-snoc-when-consp
  (implies
   (consp xs)

   (equal
    (car (snoc xs x))
    (car xs))))

(defthm channel-head-of-send-compute-message
  (implies
   (consp
    (channel-state src dst channels))

   (equal
    (car
     (channel-state
      src
      dst
      (send-compute-message
       local i nbrs channels)))

    (car
     (channel-state
      src
      dst
      channels)))))



(defthm get-msg-from-channel-of-send-compute-message
  (implies
   ;; The incoming channel sender -> receiver is nonempty.
   (consp
    (channel-state sender receiver channels))

   (equal
    ;; get-msg-from-channel takes receiver first, sender second.
    (get-msg-from-channel
     
     sender
     receiver
     (send-compute-message
      local
      i
      nbrs
      channels))

    (get-msg-from-channel
     
     sender
     receiver
     channels))))

(defthm remove-message-from-channel-of-send-compute-message
  (implies
   ;; The channel SENDER -> RECEIVER already contains a message.
   (consp
    (channel-state sender receiver channels))

   (equal
    ;; First perform the normal send, then remove the received message.
    (remove-message-from-channel
     sender
     receiver
     (send-compute-message
      local
      normal-i
      nbrs
      channels))

    ;; First remove the received message, then perform the normal send.
    (send-compute-message
     local
     normal-i
     nbrs
     (remove-message-from-channel
      sender
      receiver
      channels)))))


(defthm remove-message-from-channel-commutes-for-different-receivers
  (implies
   (not (equal receiver-1 receiver-2))

   (equal
    (remove-message-from-channel
     sender-2
     receiver-2
     (remove-message-from-channel
      sender-1
      receiver-1
      channels))

    (remove-message-from-channel
     sender-1
     receiver-1
     (remove-message-from-channel
      sender-2
      receiver-2
      channels)))))

(defthm get-msg-from-channel-of-remove-message-from-channel-different-pid
  (implies
   (not (equal pid-1 pid-2))

   (equal
    ;; Read the message for PID-1 after removing a message for PID-2.
    (get-msg-from-channel
     sender-1
     pid-1
     (remove-message-from-channel
      sender-2
      pid-2
      channels))

    ;; Removing from PID-2's incoming channel does not affect PID-1.
    (get-msg-from-channel
     sender-1
     pid-1
     channels))))

(defthm cl-two-spec-inputs-commute
  (implies
   (cl-two-spec-inputs-swappable-p
    st
    input-1
    input-2)

   (equal
    ;; INPUT-1 ; INPUT-2
    (spec-step
     (spec-step st input-1)
     input-2)

    ;; INPUT-2 ; INPUT-1
    (spec-step
     (spec-step st input-2)
     input-1)))

  :hints
  (("Goal"
    ;; Split the proof according to the input types.
    :in-theory (disable get-msg-from-channel remove-message-from-channel)
    :cases
    ((equal (ttype input-1) :nop)
     (equal (ttype input-1) :normal)
     (equal (ttype input-1) :receive)

     (equal (ttype input-2) :nop)
     (equal (ttype input-2) :normal)
     (equal (ttype input-2) :receive)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Two-input RUN-SPEC form
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defthm cl-run-spec-two-inputs-commute
  (implies
   (cl-two-spec-inputs-swappable-p
    st
    input-1
    input-2)

   (equal
    (run-spec
     st
     (list input-1 input-2))

    (run-spec
     st
     (list input-2 input-1))))
  :hints
  (("Goal"
    ;; Split the proof according to the input types.
    :in-theory (disable spec-step))))

(defthm run-spec-swapped-first-two-inputs
  (implies
   (cl-two-spec-inputs-swappable-p
    st input-1 input-2)

   (equal
    (run-spec
     st
     (cons input-1
           (cons input-2 post)))

    (run-spec
     st
     (cons input-2
           (cons input-1 post))))))


(defthm run-spec-adjacent-inputs-commute
  (implies
   (cl-two-spec-inputs-swappable-p
    (run-spec st pre)
    input-1
    input-2)

   (equal
    ;; PRE ; INPUT-1 ; INPUT-2 ; POST
    (run-spec
     st
     (append
      pre
      (cons input-1
            (cons input-2 post))))

    ;; PRE ; INPUT-2 ; INPUT-1 ; POST
    (run-spec
     st
     (append
      pre
      (cons input-2
            (cons input-1 post)))))))






(defthm
  cm-cut-not-taken-p-after-process-cut-step-implies-before

  (implies
   (cm-cut-not-taken-p
    (process-cut-step input st m)
    i)

   (cm-cut-not-taken-p m i)))



(defthm post-pre-inputs-have-different-pids

  (implies
   (and
    ;; INPUT-1 belongs to a process that has already taken its cut.
    (not
     (cm-cut-not-taken-p
      pre-m
      (pid input-1)))

    ;; INPUT-2 belongs to a process that remains pre-cut
    ;; after INPUT-1.
    (cm-cut-not-taken-p
     (process-cut-step
      input-1
      pre-imp-st
      pre-m)
     (pid input-2)))

   (not
    (equal
     (pid input-1)
     (pid input-2)))))


(defthm
  legal-input-sequencep-append-two-implies-input-1-legal

  (implies
   (legal-input-sequencep
    st
    (append prefix-inputs
            (list input-1 input-2)))

   (legal-inputp
    (run-imp st prefix-inputs)
    input-1))

  :hints
  (("Goal"

    :in-theory
    (disable system-step))))


(defthm
  legal-input-sequencep-append-two-implies-input-2-legal

  (implies
   (legal-input-sequencep
    st
    (append prefix-inputs
            (list input-1 input-2)))

   (legal-inputp
    (system-step
     (run-imp st prefix-inputs)
     input-1)
    input-2))

  :hints
  (("Goal"
    :in-theory
    (disable system-step))))





(defthm
  cl-spec-compatible-input-i-is-spec-legal-after-prefix

  (implies
   (and
    (good-state-p
     imp-start-st)

    (good-spec-state-p
     spec-start-st)

    (imp-spec-equivalent-p
     imp-start-st
     spec-start-st)

    ;; The prefix starts the checkpoint.
    (equal
     (ttype (first prefix-inputs))
     :start-checkpoint)

    (cl-checkpoint-body-inputs-p
     (rest prefix-inputs))

    ;; The prefix is legal and contains no recovery step.
    (legal-input-sequencep
     imp-start-st
     prefix-inputs)

    (cut-scan-no-recovery-segment-p
     prefix-inputs
     imp-start-st)

    ;; INPUT-I has an allowed type and is a no-recovery step.
    (cl-checkpoint-body-input-p
     input-i)

    (cut-scan-no-recovery-step-p
     input-i
     (run-imp
      imp-start-st
      prefix-inputs))

    ;; This is the exact legality hypothesis available in Subgoal 4.
    (legal-input-sequencep
     (run-imp
      imp-start-st
      prefix-inputs)

     (list input-i input-j)))

   (spec-legal-inputp
    (run-spec
     spec-start-st
     (spec-compatible-input-sequence
      imp-start-st
      prefix-inputs))

    (spec-compatible-input
     input-i
     (run-imp
      imp-start-st
      prefix-inputs))))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (checkpoint-prefix-input-type-p)

     (good-state-p
      good-spec-state-p
      imp-spec-equivalent-p

      legal-inputp
      legal-input-sequencep
      spec-legal-inputp

      checkpoint-prefix-input-types-p
      cut-scan-no-recovery-step-p
      cut-scan-no-recovery-segment-p

      run-imp
      run-spec
      spec-compatible-input
      spec-compatible-input-sequence
      system-step)))))


(defthm proc-ids-of-system-step
  (equal
   (proc-ids
    (system-step st input))
   (proc-ids st)))


(defthm proc-ids-of-spec-step
  (equal
   (proc-ids
    (spec-step st input))
   (proc-ids st)))


(defthm proc-ids-of-run-imp
  (equal
   (proc-ids
    (run-imp st inputs))
   (proc-ids st))

  :hints
  (("Goal"
    :induct
    (run-imp st inputs))))


(defthm proc-ids-of-run-spec
  (equal
   (proc-ids
    (run-spec st inputs))
   (proc-ids st))

  :hints
  (("Goal"
    :induct
    (run-spec st inputs))))


(defthm normal-second-input-pid-in-proc-ids
  (implies
   (and
    (legal-input-sequencep
     st
     (list input-i input-j))

    (equal
     (ttype input-j)
     :normal))

   (memberp
    (pid input-j)
    (proc-ids st))))


(defthm receive-second-input-pid-in-proc-ids
  (implies
   (and
    (legal-input-sequencep
     st
     (list input-i input-j))

    (equal
     (ttype input-j)
     :receive))

   (memberp
    (pid input-j)
    (proc-ids st))))



(defthm receive-second-input-sender-in-proc-ids
  (implies
   (and
    (legal-input-sequencep
     st
     (list input-i input-j))

    (equal
     (ttype input-j)
     :receive))

   (memberp
    (sender input-j)
    (proc-ids st))))


(defthm normal-second-input-pid-in-run-spec-proc-ids
  (implies
   (and
    (imp-spec-equivalent-p
     imp-start-st
     spec-start-st)

    (legal-input-sequencep
     (run-imp
      imp-start-st
      prefix-inputs)
     (list input-i input-j))

    (equal
     (ttype input-j)
     :normal))
    (memberp
    (pid input-j)

    (proc-ids
      spec-start-st)))

  :hints
  (("Goal"
    :use
    ((:instance
      normal-second-input-pid-in-proc-ids

      (st
       (run-imp
        imp-start-st
        prefix-inputs)))

     (:instance
      proc-ids-equal-when-imp-spec-equivalent-p

      (imp-st imp-start-st)
      (spec-st spec-start-st)))

    :in-theory
    (disable
     imp-spec-equivalent-p
     legal-input-sequencep
     run-imp
     run-spec))))



(defthm receive-second-input-pid-in-run-spec-proc-ids
  (implies
   (and
    (imp-spec-equivalent-p
     imp-start-st
     spec-start-st)

    (legal-input-sequencep
     (run-imp
      imp-start-st
      prefix-inputs)
     (list input-i input-j))

    (equal
     (ttype input-j)
     :receive))

    (memberp
    (pid input-j)

    (proc-ids
      spec-start-st)))

  :hints
  (("Goal"
    :use
    ((:instance
      receive-second-input-pid-in-proc-ids

      (st
       (run-imp
        imp-start-st
        prefix-inputs)))

     (:instance
      proc-ids-equal-when-imp-spec-equivalent-p

      (imp-st imp-start-st)
      (spec-st spec-start-st)))

    :in-theory
    (disable
     imp-spec-equivalent-p
     legal-input-sequencep
     run-imp
     run-spec))))


(defthm receive-second-input-sender-in-run-spec-proc-ids
  (implies
   (and
    (imp-spec-equivalent-p
     imp-start-st
     spec-start-st)

    (legal-input-sequencep
     (run-imp
      imp-start-st
      prefix-inputs)
     (list input-i input-j))

    (equal
     (ttype input-j)
     :receive))

   (memberp
    (sender input-j)
    (proc-ids spec-start-st)))

  :hints
  (("Goal"
    :use
    ((:instance
      receive-second-input-sender-in-proc-ids

      (st
       (run-imp
        imp-start-st
        prefix-inputs)))

     (:instance
      proc-ids-equal-when-imp-spec-equivalent-p

      (imp-st imp-start-st)
      (spec-st spec-start-st)))

    :in-theory
    (disable
     imp-spec-equivalent-p
     legal-input-sequencep
     run-imp
     run-spec))))

;; (defthm receive-second-input-sender-in-run-spec-proc-ids
;;   (implies
;;    (and
;;     (imp-spec-equivalent-p
;;      imp-start-st
;;      spec-start-st)

;;     (legal-input-sequencep
;;      (run-imp
;;       imp-start-st
;;       prefix-inputs)
;;      (list input-i input-j))

;;     (equal
;;      (ttype input-j)
;;      :receive))

;;     (memberp
;;     (sender input-j)

;;     (proc-ids
;;       spec-start-st)))

;;   :hints
;;   (("Goal"
;;     :use
;;     ((:instance
;;       receive-second-input-sender-in-proc-ids

;;       (st
;;        (run-imp
;;         imp-start-st
;;         prefix-inputs)))

;;      (:instance
;;       proc-ids-equal-when-imp-spec-equivalent-p

;;       (imp-st imp-start-st)
;;       (spec-st spec-start-st)))

;;     :in-theory
;;     (disable
;;      imp-spec-equivalent-p
;;      legal-input-sequencep
;;      run-imp
;;      run-spec))))



(defthm receive-second-input-sender-in-nbrs-from
  (implies
   (and
    (legal-inputp
     st
     input-j)

    (equal
     (ttype input-j)
     :receive))

   (memberp
    (sender input-j)

    (nbrs-from
     (g (pid input-j)
        (procs st))))))

(defthm nbrs-from-of-g-of-run-imp
  (equal
   (nbrs-from
    (g k
       (procs
        (run-imp st inputs))))

   (nbrs-from
    (g k
       (procs st)))))



(defthm nbrs-from-of-g-of-run-spec
  (equal
   (nbrs-from
    (g k
       (procs
        (run-spec st inputs))))

   (nbrs-from
    (g k
       (procs st)))))



(defthm nbrs-from-of-g-of-system-step
  (equal
   (nbrs-from
    (g k
       (procs
        (system-step st input))))

   (nbrs-from
    (g k
       (procs st)))))


(defthm receive-second-input-sender-in-nbrs-from-2
  (implies
   (and
    (legal-input-sequencep
     st
     (list input-i input-j))

    (equal
     (ttype input-j)
     :receive))

   (memberp
    (sender input-j)

    (nbrs-from
     (g (pid input-j)
        (procs st)))))

    :hints
  (("Goal"
    :in-theory
    (disable
     legal-inputp
     system-step
     run-imp))
   ("Goal'"
    :use
    ((:instance
      receive-second-input-sender-in-nbrs-from
      (st
       (system-step st input-i))
      (input-j input-j)))
    )))


(defthm receive-second-input-sender-in-nbrs-from-before-run-imp
  (implies
   (and
    (legal-input-sequencep
     (run-imp st inputs)
     (list input-i input-j))

    (equal
     (ttype input-j)
     :receive))

   (memberp
    (sender input-j)

    (nbrs-from
     (g (pid input-j)
        (procs st)))))

  :hints
  (("Goal"
    :use
    ((:instance
      receive-second-input-sender-in-nbrs-from-2

      (st
       (run-imp st inputs))

      (input-i input-i)
      (input-j input-j))

     (:instance
      nbrs-from-of-g-of-run-imp

      (st st)
      (inputs inputs)
      (k (pid input-j))))

    :in-theory
    (disable
     receive-second-input-sender-in-nbrs-from-2
     nbrs-from-of-g-of-run-imp
     legal-input-sequencep
     run-imp))))



(defthm channel-consp-before-nop-step
  (implies
    (equal
     (ttype input-i)
     :nop)

    (equal
     (g (sender input-j)
        (g (pid input-j)
           (channels
            (system-step st input-i))))

    (g (sender input-j)
       (g (pid input-j)
          (channels st))))))

(defthm normal-channel-head-before-nop-step
  (implies
    (equal
     (ttype input-i)
     :nop)

   (equal
     (msg-type
      (get-msg-from-channel
        (sender input-j)
          (pid input-j)
             (channels
              (system-step st input-i))))
    (msg-type
     (get-msg-from-channel
      (sender input-j)
         (pid input-j)
            (channels st))))))





(defthm spec-channel-head-normal-when-imp-spec-equivalent-p
  (implies
   (and
    ;; Bind IMP-ST first.
    (equal
     (msg-type
      (get-msg-from-channel
       src
       dst
       (channels imp-st)))
     :normal)

    (imp-spec-equivalent-p
     imp-st
     spec-st)

    (memberp
     dst
     (proc-ids imp-st))

    (memberp
     src
     (nbrs-from
      (g dst
         (procs imp-st)))))

   (equal
    (msg-type
     (get-msg-from-channel
      src
      dst
      (channels spec-st)))
    :normal))

  :rule-classes
  ((:rewrite
    :match-free :once))

  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel
     imp-spec-channels-equivalent-p))))

(defthm spec-channel-consp-when-imp-spec-equivalent-p
  (implies
   (and
    ;; This exact fact is present in the checkpoint.
    ;; ACL2 uses it to bind IMP-ST.
    (equal
     (msg-type
      (get-msg-from-channel
       src
       dst
       (channels imp-st)))
     :normal)

    ;; IMP-ST is now fully instantiated.
    (imp-spec-equivalent-p
     imp-st
     spec-st)

    (memberp
     dst
     (proc-ids imp-st))

    (memberp
     src
     (nbrs-from
      (g dst
         (procs imp-st)))))

   (consp
    (channel-state
     src
     dst
     (channels spec-st))))

  :rule-classes
  ((:rewrite
    :match-free :once))

  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel
     imp-spec-channels-equivalent-p))))


(defthm checkpoint-prefix-input-types-p-from-start-and-body
  (implies
   (and
    (consp prefix-inputs)

    (equal
     (ttype (first prefix-inputs))
     :start-checkpoint)

    (cl-checkpoint-body-inputs-p
     (rest prefix-inputs)))

   (checkpoint-prefix-input-types-p
    prefix-inputs)))






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






(defthm marker-for-sid-in-channel-p-implies-consp
  (implies
   (marker-for-sid-in-channel-p
    target-sid
    channel)

   (consp channel))

  :rule-classes
  ((:rewrite
    :match-free :once)))

(defthm
  cut-frontier-markers-for-dsts-p-implies-marker

  (implies
   (and
    (cut-frontier-markers-for-dsts-p
     src
     dsts
     target-sid
     m
     channels)

    (memberp dst dsts)

    ;; SRC has taken its cut.
    (not
     (cm-cut-not-taken-p m src))

    ;; DST has not taken its cut.
    (cm-cut-not-taken-p m dst))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     channels))))


(defthm cut-frontier-markers-for-srcs-p-implies-marker
  (implies
   (and
    (cut-frontier-markers-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    (memberp src srcs)

    (memberp
     dst
     (nbrs-to
      (g src procs)))

    (not
     (cm-cut-not-taken-p m src))

    (cm-cut-not-taken-p m dst))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src dst channels))))




(defthm cut-frontier-markers-p-implies-channel-consp
  (implies
   (and
    (cut-frontier-markers-p
     m
     st)

    (memberp
     src
     (proc-ids st))

    (memberp
     dst
     (nbrs-to
      (g src
         (procs st))))

    (not
     (cm-cut-not-taken-p
      m
      src))

    (cm-cut-not-taken-p
     m
     dst))

   (consp
    (channel-state
     src
     dst
     (channels st))))

  :rule-classes
  ((:rewrite
    :match-free :once))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-frontier-markers-for-srcs-p-implies-marker

      (srcs
       (proc-ids st))

      (target-sid
       (sid m))

      (procs
       (procs st))

      (channels
       (channels st)))

     (:instance
      marker-for-sid-in-channel-p-implies-consp

      (target-sid
       (sid m))

      (channel
       (channel-state
        src
        dst
        (channels st))))))))


(defthm
  normal-channel-head-after-normal-step-implies-before

  (implies
   (and
    (equal
     (ttype input)
     :normal)

    (consp
     (channel-state
      src
      dst
      (channels st)))

    (equal
     (msg-type
      (get-msg-from-channel
       src
       dst
       (channels
        (system-step st input))))
     :normal))

   (equal
    (msg-type
     (get-msg-from-channel
      src
      dst
      (channels st)))
    :normal))

  :hints
  (("Goal"
    :in-theory
    (disable
     NBRS-FROM-OF-SPEC-PROC-WHEN-PROCS-EQUIVALENT-P
     get-msg-from-channel))))



(defthm
  get-msg-from-channel-of-send-compute-message-different-sender

  (implies
   (not
    (equal i sender))

   (equal
    (get-msg-from-channel
     sender
     receiver
     (send-compute-message
      local
      i
      nbrs
      channels))

    (get-msg-from-channel
     sender
     receiver
     channels))))




(defthm
  normal-channel-head-before-post-cut-normal-step

  (implies
   (and
    ;; Metadata and implementation channels correspond.
    (cut-frontier-markers-p
     m
     st)

    (equal
     (ttype input-i)
     :normal)

    ;; INPUT-I belongs to a process that has taken its cut.
    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))

    ;; INPUT-J belongs to a process that has not taken its cut.
    (cm-cut-not-taken-p
     m
     (pid input-j))

    ;; INPUT-J identifies a valid incoming channel.
    (memberp
     (sender input-j)
     (proc-ids st))

    (memberp
     (pid input-j)
     (nbrs-to
      (g (sender input-j)
         (procs st))))

    ;; After INPUT-I, the channel consumed by INPUT-J
    ;; has a normal message at its head.
    (equal
     (msg-type
      (get-msg-from-channel
       (sender input-j)
       (pid input-j)
       (channels
        (system-step st input-i))))
     :normal))

   ;; Therefore, that normal message was already at the
   ;; channel head before INPUT-I.
   (equal
    (msg-type
     (get-msg-from-channel
      (sender input-j)
      (pid input-j)
      (channels st)))
    :normal))
  :otf-flg t
    :rule-classes
  ((:rewrite
    :match-free :once))
  
  :hints (("Goal"
	   :cases
	   ((equal
	     (pid input-i)
	     (sender input-j)))
	   :in-theory (disable cut-frontier-markers-p
			       get-msg-from-channel
			       NBRS-FROM-OF-SPEC-PROC-WHEN-PROCS-EQUIVALENT-P
			      ; system-step 
			       cm-cut-not-taken-p))))
  



    ;; (memberp
    ;;  (sender input-j)
    ;;  (proc-ids st))

    ;; (memberp
    ;;  (pid input-j)
    ;;  (nbrs-to
    ;;   (g (sender input-j)
    ;;      (procs st))))

(defthm
  legal-receive-after-step-implies-sender-in-nbrs-from-before-step

  (implies
   (and
    (equal
     (ttype input-j)
     :receive)

    (legal-inputp
     (system-step st input-i)
     input-j))

   (memberp
    (sender input-j)

    (nbrs-from
     (g (pid input-j)
        (procs st)))))

  :hints
  (("Goal"
    :in-theory
    (e/d
     (legal-inputp)

     (system-step)))))


(defthm
  legal-receive-after-step-pid-in-proc-ids-before-step

  (implies
   (and
    (equal
     (ttype input-j)
     :receive)

    (legal-inputp
     (system-step st input-i)
     input-j))

   (memberp
    (pid input-j)
    (proc-ids st))))


(defthm
  legal-receive-after-step-sender-in-proc-ids-before-step

  (implies
   (and
    (equal
     (ttype input-j)
     :receive)

    (legal-inputp
     (system-step st input-i)
     input-j))

   (memberp
    (sender input-j)
    (proc-ids st))))



(defthm
  legal-receive-after-step-implies-nbrs-to-before-step

  (implies
   (and
    (good-state-p st)

    (equal
     (ttype input-j)
     :receive)

    (legal-inputp
     (system-step st input-i)
     input-j))

   (memberp
    (pid input-j)
    (nbrs-to
     (g (sender input-j)
        (procs st)))))

  :hints
  (("Goal"
    :use
    ((:instance
      nbrs-from-implies-nbrs-to-when-good-state-p

      (i
       (pid input-j))

      (j
       (sender input-j))))

    :in-theory
    (disable
     good-state-p
     legal-inputp
     system-step))))




(defthm
  normal-channel-head-before-post-cut-normal-step-2

  (implies
   (and
    (cut-frontier-markers-p
     m
     st)

    (equal
     (ttype input-i)
     :normal)

    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))

    (equal
     (ttype input-j)
     :receive)

    (cm-cut-not-taken-p
     m
     (pid input-j))

    (good-state-p st)

    (legal-inputp
     st
     input-i)

    (legal-inputp
     (system-step st input-i)
     input-j)

    (equal
     (msg-type
      (get-msg-from-channel
       (sender input-j)
       (pid input-j)
       (channels
        (system-step st input-i))))
     :normal))

   (equal
    (msg-type
     (get-msg-from-channel
      (sender input-j)
      (pid input-j)
      (channels st)))
    :normal))

  :rule-classes
  ((:rewrite :match-free :once))
  :hints
  (("Goal"
    :in-theory
    (disable
     good-state-p
     legal-inputp
     system-step
     cut-frontier-markers-p
     get-msg-from-channel
     cm-cut-not-taken-p))))


(defthm
  normal-channel-head-before-post-cut-normal-step-3

  (implies
   (and
    (cut-frontier-markers-p m st)

    (equal
     (ttype input-i)
     :normal)

    (equal
     (ttype input-j)
     :receive)

    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))

    (cm-cut-not-taken-p
     m
     (pid input-j))

    (good-state-p st)

    ;; Exact shape available in Subgoal 2.1.
    (legal-input-sequencep
     st
     (list input-i input-j))

    (equal
     (msg-type
      (get-msg-from-channel
       (sender input-j)
       (pid input-j)
       (channels
        (system-step st input-i))))
     :normal))

   (equal
    (msg-type
     (get-msg-from-channel
      (sender input-j)
      (pid input-j)
      (channels st)))
    :normal))

  :rule-classes
((:rewrite :match-free :all))
  :hints
  (("Goal"
    :use
    ((:instance
      normal-channel-head-before-post-cut-normal-step-2))

    :in-theory
    (enable
     legal-input-sequencep))))



(defthm
  normal-head-after-send-marker-all-implies-before

  (implies
   (and
    (equal
     (msg-type msg)
     :marker)

    (equal
     (msg-type
      (get-msg-from-channel
       src
       dst
       (send-msg-all-outgoing-channels
        msg
        i
        nbrs
        channels)))
     :normal))

   (equal
    (msg-type
     (get-msg-from-channel
      src
      dst
      channels))
    :normal)))



(defthm
  normal-head-before-marker-broadcast-after-different-receive

  (implies
   (and
    ;; The broadcast message is a marker.
    (equal
     (msg-type msg)
     :marker)

    ;; INPUT-I removes from a different receiver than INPUT-J.
    (not
     (equal receiver-i
            receiver-j))

    ;; After removal + marker broadcast, J sees NORMAL.
    (equal
     (msg-type
      (get-msg-from-channel
       sender-j
       receiver-j

       (send-msg-all-outgoing-channels
        msg
        sender-i
        nbrs

        (remove-message-from-channel
         sender-i-recv
         receiver-i
         channels))))
     :normal))

   ;; Therefore J already saw NORMAL in the original channels.
   (equal
    (msg-type
     (get-msg-from-channel
      sender-j
      receiver-j
      channels))
    :normal))

  ;:rule-classes 

  :hints
  (("Goal"

    :use
    (
     ;; Move backward across the marker broadcast.
     (:instance
      normal-head-after-send-marker-all-implies-before

      (msg msg)
      (i sender-i)
      (nbrs nbrs)

      (src sender-j)
      (dst receiver-j)

      (channels
       (remove-message-from-channel
        sender-i-recv
        receiver-i
        channels)))

     ;; Move backward across the receive's channel removal.
     (:instance
      get-msg-from-channel-of-remove-message-from-channel-different-pid

      (sender-1 sender-j)
      (pid-1 receiver-j)

      (sender-2 sender-i-recv)
      (pid-2 receiver-i)

      (channels channels)))

    :in-theory
    (disable
     normal-head-after-send-marker-all-implies-before
     get-msg-from-channel-of-remove-message-from-channel-different-pid
     get-msg-from-channel
     remove-message-from-channel
     send-msg-all-outgoing-channels))))



(defthm
  normal-channel-head-before-receive-at-different-pid

  (implies
   (and
    (equal
     (ttype input-i)
     :receive)

    ;; Excludes recovery-message receive behavior.
    (cut-scan-no-recovery-step-p
     input-i
     st)

    ;; INPUT-I receives at a different process from INPUT-J.
    (not
     (equal
      (pid input-i)
      (pid input-j)))

    ;; After INPUT-I, INPUT-J's channel has a normal head.
    (equal
     (msg-type
      (get-msg-from-channel
       (sender input-j)
       (pid input-j)
       (channels
        (system-step st input-i))))
     :normal))

   ;; Then it already had a normal head before INPUT-I.
   (equal
    (msg-type
     (get-msg-from-channel
      (sender input-j)
      (pid input-j)
      (channels st)))
    :normal))
  :otf-flg t
  :hints (("Goal"
	   :in-theory (disable get-msg-from-channel
			       remove-message-from-channel
			       handle-first-marker-msg
			       ;; step-rcv
			       ;; step-normal
			       NBRS-FROM-OF-SPEC-PROC-WHEN-PROCS-EQUIVALENT-P
			       cut-scan-no-recovery-step-p))))





(defthm
  cl-post-pre-spec-compatible-input-j-legal-before-input-i

  (let*
      ((pre-imp-st
        (run-imp
         imp-start-st
         prefix-inputs))

       (pre-m
        (process-cut-segment
         prefix-inputs
         imp-start-st
         (make-cut-meta
          (list
           (pid (first prefix-inputs))

           (counter
            (g (pid (first prefix-inputs))
               (procs imp-start-st))))

          (pid (first prefix-inputs))
          imp-start-st)))

       (imp-after-i
        (system-step
         pre-imp-st
         input-i))
       
       (m-after-i
        (process-cut-step
         input-i
         pre-imp-st
         pre-m))

       (pre-spec-st
        (run-spec
         spec-start-st

         (spec-compatible-input-sequence
          imp-start-st
          prefix-inputs))))

    (implies
     (and
      (cut-frontier-markers-p pre-m pre-imp-st)
      (good-state-p
       (run-imp imp-start-st prefix-inputs))
      (good-state-p
       imp-start-st)

      (good-spec-state-p
       spec-start-st)

      (imp-spec-equivalent-p
       imp-start-st
       spec-start-st)

      (consp
       prefix-inputs)

      (equal
       (ttype (first prefix-inputs))
       :start-checkpoint)

      (not
       (any-snapshot-checkpointing-p
        imp-start-st))

      (not
       (any-process-recovering-p
        imp-start-st))

      (cut-scan-no-recovery-segment-p
       prefix-inputs
       imp-start-st)

      (cut-scan-no-recovery-step-p
       input-i
       pre-imp-st)

      (cut-scan-no-recovery-step-p
       input-j
       imp-after-i)

      (cl-checkpoint-body-inputs-p
       (rest prefix-inputs))

      (cl-checkpoint-body-input-p
       input-i)

      (cl-checkpoint-body-input-p
       input-j)

      (legal-input-sequencep
       imp-start-st
       prefix-inputs)

      (legal-input-sequencep
       pre-imp-st
       (list input-i input-j))

      ;; INPUT-I is post-cut.
      (not
       (cm-cut-not-taken-p
        pre-m
        (pid input-i)))

      ;; INPUT-J is still pre-cut after INPUT-I.
      (cm-cut-not-taken-p
       m-after-i
       (pid input-j)))

     (spec-legal-inputp
      pre-spec-st

      (spec-compatible-input
       input-j
       imp-after-i))))

  ;; :rule-classes nil
  :otf-flg t
  :hints
  ( ("Goal"
    :in-theory
    (disable
     good-state-p
     good-spec-state-p
     imp-spec-equivalent-p
     legal-inputp
     legal-input-sequencep
    ; spec-legal-inputp

     process-cut-segment
     process-cut-step
     make-cut-meta
     cut-scan-no-recovery-segment-p
     cut-scan-no-recovery-step-p
    ; cl-checkpoint-body-input-p
     cl-checkpoint-body-inputs-p

     any-snapshot-checkpointing-p
     any-process-recovering-p
     get-msg-from-channel
     cm-cut-not-taken-p
     run-imp
     run-spec
     system-step
					; spec-compatible-input
     cut-frontier-markers-p
     spec-compatible-input-sequence))

    ("Subgoal 6.1"

 :use
 (
  ;; ------------------------------------------------------------
  ;; 1. INPUT-I and INPUT-J belong to different processes.
  ;; ------------------------------------------------------------
  (:instance
   post-pre-inputs-have-different-pids

   (pre-m
    (process-cut-segment
     prefix-inputs
     imp-start-st
     (make-cut-meta
      (list
       (pid (first prefix-inputs))
       (counter
        (g (pid (first prefix-inputs))
           (procs imp-start-st))))
      (pid (first prefix-inputs))
      imp-start-st)))

   (pre-imp-st
    (run-imp
     imp-start-st
     prefix-inputs))

   (input-1 input-i)
   (input-2 input-j))


  ;; ------------------------------------------------------------
  ;; 2. Move J's NORMAL head backward across INPUT-I's receive.
  ;; ------------------------------------------------------------
  (:instance
   normal-channel-head-before-receive-at-different-pid

   (st
    (run-imp
     imp-start-st
     prefix-inputs))

   (input-i input-i)
   (input-j input-j))


  ;; ------------------------------------------------------------
  ;; 3. PREFIX has the required checkpoint input shape.
  ;; ------------------------------------------------------------
  (:instance
   checkpoint-prefix-input-types-p-from-start-and-body

   (prefix-inputs
    prefix-inputs))


  ;; ------------------------------------------------------------
  ;; 4. IMP/SPEC equivalence after PREFIX.
  ;; ------------------------------------------------------------
  (:instance
   imp-spec-equivalent-p-after-spec-compatible-input-sequence

   (imp-st
    imp-start-st)

   (spec-st
    spec-start-st)

   (inputs
    prefix-inputs))


  ;; ------------------------------------------------------------
  ;; 5. PID(INPUT-J) is valid in the pre-prefix IMP state.
  ;; ------------------------------------------------------------
  (:instance
   receive-second-input-pid-in-proc-ids

   (st
    (run-imp
     imp-start-st
     prefix-inputs))

   (input-i
    input-i)

   (input-j
    input-j))


  ;; ------------------------------------------------------------
  ;; 6. SENDER(INPUT-J) is an incoming neighbor of PID(INPUT-J).
  ;; ------------------------------------------------------------
  (:instance
   receive-second-input-sender-in-nbrs-from-2

   (st
    (run-imp
     imp-start-st
     prefix-inputs))

   (input-i
    input-i)

   (input-j
    input-j))


  ;; ------------------------------------------------------------
  ;; 7. Transfer the NORMAL head from IMP to SPEC.
  ;; ------------------------------------------------------------
  (:instance
   spec-channel-head-normal-when-imp-spec-equivalent-p

   (imp-st
    (run-imp
     imp-start-st
     prefix-inputs))

   (spec-st
    (run-spec
     spec-start-st
     (spec-compatible-input-sequence
      imp-start-st
      prefix-inputs)))

   (src
    (sender input-j))

   (dst
    (pid input-j))))

 :in-theory
 (disable
  post-pre-inputs-have-different-pids
  normal-channel-head-before-receive-at-different-pid

  checkpoint-prefix-input-types-p-from-start-and-body
  imp-spec-equivalent-p-after-spec-compatible-input-sequence

  receive-second-input-pid-in-proc-ids
  receive-second-input-sender-in-nbrs-from-2

  spec-channel-head-normal-when-imp-spec-equivalent-p

  good-state-p
  good-spec-state-p
  imp-spec-equivalent-p

  legal-input-sequencep

  cut-frontier-markers-p
  cut-scan-no-recovery-step-p

  cm-cut-not-taken-p

  get-msg-from-channel
  run-imp
  run-spec
  system-step

  process-cut-step
  process-cut-segment
  make-cut-meta

  spec-compatible-input-sequence))


    ("Subgoal 6.2"

 :use
 (
  ;; 1. INPUT-I and INPUT-J have different PIDs.
  (:instance
   post-pre-inputs-have-different-pids

   (pre-m
    (process-cut-segment
     prefix-inputs
     imp-start-st
     (make-cut-meta
      (list
       (pid (first prefix-inputs))
       (counter
        (g (pid (first prefix-inputs))
           (procs imp-start-st))))
      (pid (first prefix-inputs))
      imp-start-st)))

   (pre-imp-st
    (run-imp
     imp-start-st
     prefix-inputs))

   (input-1 input-i)
   (input-2 input-j))


  ;; 2. Move J's normal head backward across INPUT-I's receive.
  (:instance
   normal-channel-head-before-receive-at-different-pid

   (st
    (run-imp
     imp-start-st
     prefix-inputs))

   (input-i input-i)
   (input-j input-j))


  ;; 3. Prefix has valid checkpoint-input shape.
  (:instance
   checkpoint-prefix-input-types-p-from-start-and-body

   (prefix-inputs
    prefix-inputs))


  ;; 4. IMP/SPEC equivalence after the prefix.
  (:instance
   imp-spec-equivalent-p-after-spec-compatible-input-sequence

   (imp-st
    imp-start-st)

   (spec-st
    spec-start-st)

   (inputs
    prefix-inputs))


  ;; 5. PID(INPUT-J) is valid in PRE-IMP-ST.
  (:instance
   receive-second-input-pid-in-proc-ids

   (st
    (run-imp
     imp-start-st
     prefix-inputs))

   (input-i
    input-i)

   (input-j
    input-j))


  ;; 6. SENDER(INPUT-J) is an incoming neighbor of PID(INPUT-J).
  (:instance
   receive-second-input-sender-in-nbrs-from-2

   (st
    (run-imp
     imp-start-st
     prefix-inputs))

   (input-i
    input-i)

   (input-j
    input-j))


  ;; 7. Transfer nonemptiness from IMP channel to SPEC channel.
  (:instance
   spec-channel-consp-when-imp-spec-equivalent-p

   (imp-st
    (run-imp
     imp-start-st
     prefix-inputs))

   (spec-st
    (run-spec
     spec-start-st
     (spec-compatible-input-sequence
      imp-start-st
      prefix-inputs)))

   (src
    (sender input-j))

   (dst
    (pid input-j))))

 :in-theory
 (disable
  post-pre-inputs-have-different-pids
  normal-channel-head-before-receive-at-different-pid

  checkpoint-prefix-input-types-p-from-start-and-body
  imp-spec-equivalent-p-after-spec-compatible-input-sequence

  receive-second-input-pid-in-proc-ids
  receive-second-input-sender-in-nbrs-from-2

  spec-channel-consp-when-imp-spec-equivalent-p

  good-state-p
  good-spec-state-p
  imp-spec-equivalent-p

  legal-input-sequencep

  cut-frontier-markers-p
  cut-scan-no-recovery-step-p

  cm-cut-not-taken-p

  get-msg-from-channel
  run-imp
  run-spec
  system-step

  process-cut-step
  process-cut-segment
  make-cut-meta

  spec-compatible-input-sequence))
    

    ("Subgoal 2.2"

 :use
 (
  ;; Good state after PREFIX.
  (:instance
   good-state-p-of-run-imp-when-legal-input-sequencep
   (st imp-start-st)
   (inputs prefix-inputs))

  ;; PREFIX has the required input-type shape.
  (:instance
   checkpoint-prefix-input-types-p-from-start-and-body
   (prefix-inputs prefix-inputs))

  ;; IMP/SPEC equivalence after PREFIX.
  (:instance
   imp-spec-equivalent-p-after-spec-compatible-input-sequence
   (imp-st imp-start-st)
   (spec-st spec-start-st)
   (inputs prefix-inputs))

  ;; PID(INPUT-J) is a valid process in PRE-IMP-ST.
  (:instance
   receive-second-input-pid-in-proc-ids
   (st
    (run-imp
     imp-start-st
     prefix-inputs))
   (input-i input-i)
   (input-j input-j))

  ;; SENDER(INPUT-J) is an incoming neighbor of PID(INPUT-J)
  ;; in PRE-IMP-ST.
  (:instance
   receive-second-input-sender-in-nbrs-from-2
   (st
    (run-imp
     imp-start-st
     prefix-inputs))
   (input-i input-i)
   (input-j input-j))

  ;; Move the normal head backwards across the post-cut normal step.
  (:instance
   normal-channel-head-before-post-cut-normal-step-3

   (m
    (process-cut-segment
     prefix-inputs
     imp-start-st
     (make-cut-meta
      (list
       (pid (first prefix-inputs))
       (counter
        (g (pid (first prefix-inputs))
           (procs imp-start-st))))
      (pid (first prefix-inputs))
      imp-start-st)))

   (st
    (run-imp
     imp-start-st
     prefix-inputs))

   (input-i input-i)
   (input-j input-j))

  ;; Transfer nonemptiness to the corresponding SPEC channel.
  (:instance
   spec-channel-consp-when-imp-spec-equivalent-p

   (imp-st
    (run-imp
     imp-start-st
     prefix-inputs))

   (spec-st
    (run-spec
     spec-start-st
     (spec-compatible-input-sequence
      imp-start-st
      prefix-inputs)))

   (src
    (sender input-j))

   (dst
    (pid input-j))))

 :in-theory
 (disable
  good-state-p-of-run-imp-when-legal-input-sequencep
  checkpoint-prefix-input-types-p-from-start-and-body
  imp-spec-equivalent-p-after-spec-compatible-input-sequence
  receive-second-input-pid-in-proc-ids
  receive-second-input-sender-in-nbrs-from-2
  normal-channel-head-before-post-cut-normal-step-3
  spec-channel-consp-when-imp-spec-equivalent-p

  good-state-p
  good-spec-state-p
  imp-spec-equivalent-p
  legal-input-sequencep
  cut-frontier-markers-p
  get-msg-from-channel
  run-imp
  run-spec
  system-step
  process-cut-segment
  spec-compatible-input-sequence))

    ("Subgoal 2.1"

 :use
 (
  (:instance
   good-state-p-of-run-imp-when-legal-input-sequencep
   (st imp-start-st)
   (inputs prefix-inputs))

  (:instance
   checkpoint-prefix-input-types-p-from-start-and-body
   (prefix-inputs prefix-inputs))

  (:instance
   imp-spec-equivalent-p-after-spec-compatible-input-sequence
   (imp-st imp-start-st)
   (spec-st spec-start-st)
   (inputs prefix-inputs))

  (:instance
   receive-second-input-pid-in-proc-ids
   (st
    (run-imp imp-start-st prefix-inputs))
   (input-i input-i)
   (input-j input-j))

  (:instance
   receive-second-input-sender-in-nbrs-from-2
   (st
    (run-imp imp-start-st prefix-inputs))
   (input-i input-i)
   (input-j input-j))

  (:instance
   normal-channel-head-before-post-cut-normal-step-3

   (m
    (process-cut-segment
     prefix-inputs
     imp-start-st
     (make-cut-meta
      (list
       (pid (first prefix-inputs))
       (counter
        (g (pid (first prefix-inputs))
           (procs imp-start-st))))
      (pid (first prefix-inputs))
      imp-start-st)))

   (st
    (run-imp
     imp-start-st
     prefix-inputs))

   (input-i input-i)
   (input-j input-j))

  (:instance
   spec-channel-head-normal-when-imp-spec-equivalent-p

   (imp-st
    (run-imp
     imp-start-st
     prefix-inputs))

   (spec-st
    (run-spec
     spec-start-st
     (spec-compatible-input-sequence
      imp-start-st
      prefix-inputs)))

   (src
    (sender input-j))

   (dst
    (pid input-j))))

 :in-theory
 (disable
  normal-channel-head-before-post-cut-normal-step-3
  spec-channel-head-normal-when-imp-spec-equivalent-p
  receive-second-input-pid-in-proc-ids
  receive-second-input-sender-in-nbrs-from-2
  imp-spec-equivalent-p-after-spec-compatible-input-sequence
  checkpoint-prefix-input-types-p-from-start-and-body

  good-state-p
  good-spec-state-p
  imp-spec-equivalent-p
  legal-input-sequencep
  cut-frontier-markers-p
  get-msg-from-channel
  run-imp
  run-spec
  system-step
  process-cut-segment
  spec-compatible-input-sequence))
    
    ))


(defthm
  channel-consp-preserved-by-send-compute-message

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
      local
      i
      nbrs
      channels)))))


(defthm
  spec-legal-inputp-preserved-by-different-pid-step

  (implies
   (and
    (spec-legal-inputp st input-1)

    (spec-legal-inputp st input-2)

    (not
     (equal
      (pid input-1)
      (pid input-2))))

   (spec-legal-inputp
    (spec-step st input-2)
    input-1))

  :hints
  (("Goal"
    :cases
    ((equal (ttype input-1) :nop)
     (equal (ttype input-1) :normal)
     (equal (ttype input-1) :receive)

     (equal (ttype input-2) :nop)
     (equal (ttype input-2) :normal)
     (equal (ttype input-2) :receive))

    :in-theory
    (disable
      NBRS-FROM-OF-SPEC-PROC-WHEN-PROCS-EQUIVALENT-P
      get-msg-from-channel
      remove-message-from-channel))))






(defthm
  cl-post-pre-spec-compatible-inputs-swappable-after-prefix

  (let*
      (;; The checkpoint represented by this segment.
       (initiator
        (cl-checkpoint-segment-initiator
         prefix-inputs))

       (target-sid
        (cl-checkpoint-segment-sid
         imp-start-st
         prefix-inputs))

       ;; Initial metadata corresponds to the checkpoint started by
       ;; the first input.
       (m0
        (make-cut-meta
         target-sid
         initiator
         imp-start-st))

       ;; Implementation state and cut metadata generated by exactly
       ;; the same execution prefix.
       (pre-imp-st
        (run-imp
         imp-start-st
         prefix-inputs))

       (pre-m
        (process-cut-segment
         prefix-inputs
         imp-start-st
         m0))

       ;; State and metadata after the first input of the pair.
       (imp-after-i
        (system-step
         pre-imp-st
         input-i))

       (m-after-i
        (process-cut-step
         input-i
         pre-imp-st
         pre-m))

       ;; Specification state corresponding to the same prefix.
       (spec-prefix
        (spec-compatible-input-sequence
         imp-start-st
         prefix-inputs))

       (pre-spec-st
        (run-spec
         spec-start-st
         spec-prefix))

       ;; Each input is converted using its actual implementation
       ;; pre-state in the original execution.
       (spec-input-i
        (spec-compatible-input
         input-i
         pre-imp-st))

       (spec-input-j
        (spec-compatible-input
         input-j
         imp-after-i)))

    (implies
     (and
      ;; Initial implementation/specification relationship.
      (good-state-p imp-start-st)

      (good-spec-state-p spec-start-st)

      (cut-frontier-markers-p pre-m pre-imp-st)
      
      (imp-spec-equivalent-p
       imp-start-st
       spec-start-st)

      ;; PREFIX-INPUTS begins the isolated checkpoint execution.
      (consp prefix-inputs)

      (equal
       (ttype (first prefix-inputs))
       :start-checkpoint)

      (not
       (any-snapshot-checkpointing-p
        imp-start-st))

      (not
       (any-process-recovering-p
        imp-start-st))


      (cut-scan-no-recovery-segment-p
       (append
	prefix-inputs
	(list input-i input-j))
       imp-start-st)

      ;; The remainder of the prefix and the adjacent pair contain
      ;; only checkpoint-body inputs.
      (cl-checkpoint-body-inputs-p
       (append
        (rest prefix-inputs)
        (list input-i input-j)))

      ;; The actual prefix followed by INPUT-I ; INPUT-J is legal.
      (legal-input-sequencep
       imp-start-st
       (append
        prefix-inputs
        (list input-i input-j)))

      (not
       (cm-cut-not-taken-p
	pre-m
	(pid input-i)))

      ;; INPUT-J occurs before its process takes the cut.
      ;; M-AFTER-I is the metadata immediately before INPUT-J.
      (cm-cut-not-taken-p
       m-after-i
       (pid input-j)))

     ;; Therefore, the projected POST_i ; PRE_j pair is swappable.
     (cl-two-spec-inputs-swappable-p
      pre-spec-st
      spec-input-i
      spec-input-j)))
    :hints
  (("Goal"
    ;; Split the proof according to the input types.
    
    :in-theory (disable process-cut-step
			process-cut-segment
			good-state-p
			good-spec-state-p
			imp-spec-equivalent-p
			legal-input-sequencep
			spec-legal-inputp
			cl-no-recovery-receive-sequencep
			cm-cut-not-taken-p
			any-process-recovering-p
			append
			spec-compatible-input
			any-snapshot-checkpointing-p
			cut-scan-no-recovery-step-p
			legal-inputp
			step-normal
			system-step
			spec-step
			make-cut-meta
			CL-CHECKPOINT-BODY-INPUT-P
			cut-frontier-markers-p
			;legal-input-sequencep-of-append
			))))








;; (defthm cl-generated-meta-reordering-preserves-run-spec
;;   (implies
;;    (and
;;     (good-state-p imp-start-st)
;;     (good-spec-state-p spec-start-st)

;;     (imp-spec-equivalent-p
;;      imp-start-st
;;      spec-start-st)

;;     (cl-checkpoint-complete-segment-p
;;      imp-start-st
;;      inputs))

;;    (let* ((trace
;;            (run-imp-trace imp-start-st inputs))

;;           (sid
;;            (cl-checkpoint-segment-sid
;;             imp-start-st inputs))

;;           (initiator
;;            (cl-checkpoint-segment-initiator
;;             inputs))

;;           (cut-result
;;            (scan-until-cut-done
;;             inputs
;;             trace
;;             0
;;             sid
;;             initiator))

;;           (m-final
;;            (cut-result-meta cut-result)))

;;      (equal
;;       (run-spec
;;        spec-start-st
;;        (spec-compatible-input-sequence
;;         imp-start-st
;;         inputs))

;;       (run-spec
;;        spec-start-st
;;        (append
;;         (cm-inputs-before-cut m-final)
;;         (cm-after-cut-input-sequence m-final)))))))











