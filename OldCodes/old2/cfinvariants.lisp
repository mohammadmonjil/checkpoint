(in-package "ACL2")
(include-book "model")
(include-book "scan")
(include-book "cut_inv")
(include-book "basic")



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


(defun cut-marker-in-transit-for-outgoing-nbrs-p
    (src outgoing-nbrs target-sid m channels)

  (declare
   (xargs :measure (acl2-count outgoing-nbrs)))

  ;; If SRC has not taken its cut yet, it has not sent
  ;; the target checkpoint marker, so there is no
  ;; in-transit marker obligation from SRC.
  (if (cm-cut-not-taken-p m src)
      t

    ;; SRC has taken its cut.
    (if (endp outgoing-nbrs)
        t

      (let ((out-nbr (first outgoing-nbrs)))

        (and
         ;; If OUT-NBR has not taken its cut yet, then the
         ;; target checkpoint marker sent by SRC must still
         ;; be in transit on channel SRC -> OUT-NBR.
         (if (cm-cut-not-taken-p m out-nbr)

             (marker-for-sid-in-channel-p
              target-sid
              (channel-state
               src
               out-nbr
               channels))

           ;; OUT-NBR has already taken its cut, so there is
           ;; no longer an in-transit obligation.
           t)

         (cut-marker-in-transit-for-outgoing-nbrs-p
          src
          (rest outgoing-nbrs)
          target-sid
          m
          channels))))))


(defun cut-markers-in-transit-for-srcs-p
    (srcs target-sid m procs channels)

  (declare
   (xargs :measure (acl2-count srcs)))

  (if (endp srcs)
      t

    (let ((src (first srcs)))

      (and
       ;; Check every outgoing channel of SRC.
       (cut-marker-in-transit-for-outgoing-nbrs-p
        src
        (nbrs-to
         (g src procs))
        target-sid
        m
        channels)

       ;; Check the remaining source processes.
       (cut-markers-in-transit-for-srcs-p
        (rest srcs)
        target-sid
        m
        procs
        channels)))))


(defun cut-markers-in-transit-p (m st)
  ;; Global invariant:
  ;;
  ;; For every SRC that has taken the target cut and every
  ;; outgoing neighbor DST that has not yet taken the cut,
  ;; the target checkpoint marker is still present somewhere
  ;; on channel SRC -> DST.
  (cut-markers-in-transit-for-srcs-p
   (proc-ids st)
   (cm-sid m)
   m
   (procs st)
   (channels st)))

;; ------------------------------------------------------------
;; Base case for the invariant.
;;
;; If every source process in SRCS is still in :cut-not-taken,
;; then none of them has sent the target checkpoint marker yet.
;; Therefore there are no outgoing marker-in-transit obligations
;; to check, and the invariant holds trivially.
;;
;; This lemma is especially useful at checkpoint initialization
;; and for the processes other than the one that has just taken
;; the cut.
;; ------------------------------------------------------------



(defthm
  cut-markers-in-transit-for-srcs-p-when-all-cut-not-taken

  (implies
   (subset
    srcs
    (cm-cut-not-taken m))

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)))

;; ------------------------------------------------------------
;; Initial marker-in-transit invariant.
;;
;; MAKE-CUT-META initially places every process in
;; :cut-not-taken.  Hence no process has yet created an outgoing
;; target-marker obligation, so CUT-MARKERS-IN-TRANSIT-P holds
;; immediately for the initial cut metadata.
;; ------------------------------------------------------------



(defthm cut-markers-in-transit-p-of-make-cut-meta
  (cut-markers-in-transit-p
   (make-cut-meta
    target-sid
    initiator
    st)
   st))






(defthm cut-marker-in-transit-for-outgoing-nbrs-p-of-before-cut-input-sequence-update
  (equal
   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    (s :before-cut-input-sequence val m)
    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    channels)))


(defthm cut-markers-in-transit-for-srcs-p-of-before-cut-input-sequence-update
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    (s :before-cut-input-sequence val m)
    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)))


(defthm cut-marker-in-transit-for-outgoing-nbrs-p-of-after-cut-input-sequence-update
  (equal
   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    (s :after-cut-input-sequence val m)
    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    channels)))


(defthm cut-markers-in-transit-for-srcs-p-of-after-cut-input-sequence-update
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    (s :after-cut-input-sequence val m)
    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)))


;; (defthm
;;   cut-marker-in-transit-for-outgoing-nbrs-p-of-inputs-before-cut-update

;;   (equal
;;    (cut-marker-in-transit-for-outgoing-nbrs-p
;;     src
;;     outgoing-nbrs
;;     target-sid
;;     (s :inputs-before-cut val m)
;;     channels)

;;    (cut-marker-in-transit-for-outgoing-nbrs-p
;;     src
;;     outgoing-nbrs
;;     target-sid
;;     m
;;     channels)))


;; (defthm
;;   cut-markers-in-transit-for-srcs-p-of-inputs-before-cut-update

;;   (equal
;;    (cut-markers-in-transit-for-srcs-p
;;     srcs
;;     target-sid
;;     (s :inputs-before-cut val m)
;;     procs
;;     channels)

;;    (cut-markers-in-transit-for-srcs-p
;;     srcs
;;     target-sid
;;     m
;;     procs
;;     channels)))


(defthm cut-markers-in-transit-for-srcs-p-of-local-state-update
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (s :local-state val
          (g i procs))
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)))



(defthm marker-for-sid-in-channel-p-of-snoc
  (implies
   (marker-for-sid-in-channel-p
    target-sid
    channel)

   (marker-for-sid-in-channel-p
    target-sid
    (snoc channel msg))))

;; ------------------------------------------------------------
;; Ordinary sends cannot destroy an existing target marker.
;;
;; SEND-COMPUTE-MESSAGE only appends a normal message to a
;; channel.  If TARGET-SID was already represented by a marker
;; somewhere in SRC -> DST, appending another message leaves that
;; marker in the channel.
;; ------------------------------------------------------------



(defthm marker-for-sid-in-channel-p-preserved-by-send-compute-message
  (implies
   (marker-for-sid-in-channel-p
    target-sid
    (channel-state src dst channels))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     (send-compute-message
      local-state
      i
      nbrs
      channels)))))


(defthm cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-send-compute-message
  (implies
   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    (send-compute-message
     local-state
     i
     nbrs
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src
     outgoing-nbrs
     target-sid
     m
     channels))))

;; ------------------------------------------------------------
;; Lift ordinary-send preservation to the global source list.
;;
;; Since SEND-COMPUTE-MESSAGE only appends a message and never
;; removes an existing target marker, every marker-in-transit
;; obligation that held before the send still holds afterward.
;; ------------------------------------------------------------



(defthm cut-markers-in-transit-for-srcs-p-preserved-by-send-compute-message
  (implies
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    (send-compute-message
     local-state
     i
     nbrs
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels))))

;; ------------------------------------------------------------
;; START-CHECKPOINT-HELPER is invisible to this invariant.
;;
;; The invariant reads PROCS only to obtain each process's
;; outgoing neighbors.  START-CHECKPOINT-HELPER changes snapshot
;; and checkpoint-related process state but preserves NBRS-TO.
;; Hence it does not change any marker-in-transit obligation.
;; ------------------------------------------------------------


(defthm cut-markers-in-transit-for-srcs-p-of-start-checkpoint-helper
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (start-checkpoint-helper procs i)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    :in-theory
    (disable start-checkpoint-helper))))

(defthm marker-for-sid-in-channel-p-preserved-by-send-msg-all-outgoing
  (implies
   (marker-for-sid-in-channel-p
    target-sid
    (channel-state src dst channels))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     (send-msg-all-outgoing-channels
      msg
      i
      nbrs
      channels))))

  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg i nbrs channels))))

(defthm cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-send-msg-all-outgoing
  (implies
   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    (send-msg-all-outgoing-channels
     msg
     i
     nbrs
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src outgoing-nbrs target-sid m channels))))

;; ------------------------------------------------------------
;; Broadcasting a message preserves all already-existing target
;; marker obligations.
;;
;; SEND-MSG-ALL-OUTGOING-CHANNELS only appends messages to
;; outgoing channels.  Thus an existing target marker cannot be
;; removed by the broadcast.
;;
;; Note that this theorem is preservation only.  The separate
;; TARGET-MARKER-PRESENT-AFTER-SEND-TO-ALL-OUTGOING-NBRS theorem
;; is what establishes a newly-created marker obligation.
;; ------------------------------------------------------------



(defthm cut-markers-in-transit-for-srcs-p-preserved-by-send-msg-all-outgoing
  (implies
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    (send-msg-all-outgoing-channels
     msg
     i
     nbrs
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs target-sid m procs channels))))


(defthm cut-markers-in-transit-for-srcs-p-of-proc-status-update
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (s :proc-status val
          (g i procs))
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)))

;; ------------------------------------------------------------
;; Normal-message process updates are invisible to the invariant.
;;
;; UPDATE-PROC-FOR-NORMAL-MSG-CORE changes local process state,
;; but it does not change the process's outgoing-neighbor list.
;; Since the invariant uses PROCS only through NBRS-TO, the
;; process update itself cannot affect marker-in-transit facts.
;; ------------------------------------------------------------



(defthm cut-markers-in-transit-for-srcs-p-of-update-proc-for-normal-msg-core
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (update-proc-for-normal-msg-core
        (g i procs)
        j
        msg)
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)
    :in-theory
    (disable update-proc-for-normal-msg-core))))


;; (defthm
;;   cut-marker-in-transit-for-outgoing-nbrs-p-of-inputs-after-cut-update

;;   (equal
;;    (cut-marker-in-transit-for-outgoing-nbrs-p
;;     src
;;     outgoing-nbrs
;;     target-sid
;;     (s :inputs-after-cut val m)
;;     channels)

;;    (cut-marker-in-transit-for-outgoing-nbrs-p
;;     src
;;     outgoing-nbrs
;;     target-sid
;;     m
;;     channels))

;;   :hints
;;   (("Goal"
;;     :induct
;;     (cut-marker-in-transit-for-outgoing-nbrs-p
;;      src
;;      outgoing-nbrs
;;      target-sid
;;      m
;;      channels))))


;; (defthm cut-markers-in-transit-for-srcs-p-of-cm-after-cut-append
;;   (equal
;;    (cut-markers-in-transit-for-srcs-p
;;     srcs target-sid
;;     (cm-after-cut-append m i j input)
;;     procs channels)

;;    (cut-markers-in-transit-for-srcs-p
;;     srcs target-sid
;;     m
;;     procs channels)))

;; (defthm
;;   cut-marker-in-transit-for-outgoing-nbrs-p-of-after-cut-msgs-update

;;   (equal
;;    (cut-marker-in-transit-for-outgoing-nbrs-p
;;     src
;;     outgoing-nbrs
;;     target-sid
;;     (s :after-cut-msgs val m)
;;     channels)

;;    (cut-marker-in-transit-for-outgoing-nbrs-p
;;     src
;;     outgoing-nbrs
;;     target-sid
;;     m
;;     channels))

;;   :hints
;;   (("Goal"
;;     :induct
;;     (cut-marker-in-transit-for-outgoing-nbrs-p
;;      src
;;      outgoing-nbrs
;;      target-sid
;;      m
;;      channels))))


;; (defthm cut-markers-in-transit-for-srcs-p-of-cm-after-cut-msg-append
;;   (equal
;;    (cut-markers-in-transit-for-srcs-p
;;     srcs target-sid
;;     (cm-after-cut-msg-append m i j msg)
;;     procs channels)

;;    (cut-markers-in-transit-for-srcs-p
;;     srcs target-sid
;;     m
;;     procs channels)))

;; (defthm sid-of-cm-after-cut-append
;;   (equal
;;    (g :sid
;;       (cm-after-cut-append m i j input))
;;    (g :sid m)))

;; (defthm sid-of-cm-after-cut-msg-append
;;   (equal
;;    (g :sid
;;       (cm-after-cut-msg-append m i j msg))
;;    (g :sid m)))


;; (defthm cut-not-taken-of-cm-after-cut-append
;;   (equal
;;    (g :cut-not-taken
;;       (cm-after-cut-append m i j input))
;;    (g :cut-not-taken m)))


;; (defthm cut-not-taken-of-cm-after-cut-msg-append
;;   (equal
;;    (g :cut-not-taken
;;       (cm-after-cut-msg-append m i j msg))
;;    (g :cut-not-taken m)))




(defthm
  marker-for-sid-in-channel-p-preserved-by-remove-normal-message

  (implies
   (and

    (equal
     (msg-type
      (get-msg-from-channel j i channels))
     :normal)

    (marker-for-sid-in-channel-p
     target-sid
     (channel-state src dst channels)))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     (remove-message-from-channel
      j i channels))))

  :hints
  (("Goal"
    :cases
    ((equal src j)
     (equal dst i))
    :in-theory
    (disable 
             remove-message-from-channel))))


(defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-remove-normal-message

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src
     outgoing-nbrs
     target-sid
     m
     channels)

    ;; (consp
    ;;  (channel-state j i channels))

    (equal
     (msg-type
      (get-msg-from-channel j i channels))
     :normal))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src
     outgoing-nbrs
     target-sid
     m
     channels))))



(defthm
  cut-markers-in-transit-for-srcs-p-preserved-by-remove-normal-message

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    (equal
     (msg-type
      (get-msg-from-channel j i channels))
     :normal))

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :in-theory (disable remove-message-from-channel)
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels))))

;; ------------------------------------------------------------
;; Metadata/implementation consistency: cut already taken.
;;
;; If metadata says process I is no longer in :cut-not-taken,
;; then the implementation must already contain TARGET-SID in
;; I's snapshot IDs.
;;
;; This lemma removes impossible proof branches where metadata
;; says "cut taken" but the implementation says otherwise.
;; ------------------------------------------------------------



(defthm
  cut-meta-imp-procs-consistent-p-cut-taken-implies-has-snapshot

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (memberp i ids)

    (not
     (cm-cut-not-taken-p m i)))

   (memberp
    target-sid
    (snapshot-ids (g i procs)))))


(defthm marker-for-sid-in-channel-p-of-cdr-when-head-not-marker
  (implies
   (and
    (consp channel)

    (not
     (equal (msg-type (car channel))
            :marker))

    (marker-for-sid-in-channel-p
     target-sid
     channel))

   (marker-for-sid-in-channel-p
    target-sid
    (cdr channel))))

;; ------------------------------------------------------------
;; Removing a non-marker head preserves a target marker.
;;
;; The interesting case is when the removed message is from the
;; same channel being checked.  Because the removed head is not a
;; marker, any target marker already present must occur later in
;; the channel and therefore remains after the head is removed.
;; ------------------------------------------------------------


(defthm
  marker-for-sid-in-channel-p-preserved-by-remove-non-marker-message

  (implies
   (and
    (consp
     (channel-state j i channels))

    (not
     (equal
      (msg-type
       (get-msg-from-channel j i channels))
      :marker))

    (marker-for-sid-in-channel-p
     target-sid
     (channel-state src dst channels)))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     (remove-message-from-channel
      j i channels)))))

(defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-remove-non-marker-message

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src outgoing-nbrs target-sid m channels)

    (consp
     (channel-state j i channels))

    (not
     (equal
      (msg-type
       (get-msg-from-channel j i channels))
      :marker)))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src outgoing-nbrs target-sid m channels))))


(defthm
  cut-markers-in-transit-for-srcs-p-of-first-recovery-proc-update

  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (update-proc-for-first-recovery-msg
        (g i procs)
        sid
        j)
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs target-sid m procs channels)
    :in-theory
    (disable update-proc-for-first-recovery-msg))))


(defthm get-msg-recovery-implies-not-marker
  (implies
   (equal
    (msg-type
     (get-msg-from-channel j i channels))
    :recovery)
   (not
    (equal
     (msg-type
      (get-msg-from-channel j i channels))
     :marker))))

(defthm recovery-msg-implies-channel-consp
  (implies
   (equal
    (msg-type
     (get-msg-from-channel j i channels))
    :recovery)

   (consp
    (channel-state j i channels))))

;; ------------------------------------------------------------
;; Global lift of non-marker removal preservation.
;;
;; This handles RECEIVE cases such as normal and recovery
;; messages: consuming a non-marker message cannot remove the
;; checkpoint marker required by the invariant.
;; ------------------------------------------------------------




  (defthm
  cut-markers-in-transit-for-srcs-p-preserved-by-remove-non-marker-message

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    (consp
     (channel-state j i channels))

    (not
     (equal
      (msg-type
       (get-msg-from-channel j i channels))
      :marker)))

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    :in-theory
    (disable remove-message-from-channel
             get-msg-from-channel))))
  


  (defthm
  cut-markers-in-transit-for-srcs-p-of-non-first-recovery-proc-update

  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (update-proc-for-non-first-recovery-msg
        (g i procs)
        j)
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    :in-theory
    (disable
     update-proc-for-non-first-recovery-msg))))


(defthm
  cut-markers-in-transit-for-srcs-p-of-first-marker-proc-update

  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (update-proc-for-first-marker-msg
        (g i procs)
        sid
        j)
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs target-sid m procs channels)
    :in-theory
    (disable update-proc-for-first-marker-msg))))


(defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-of-waiting-marker-from-update
  (equal
   (cut-marker-in-transit-for-outgoing-nbrs-p
    src outgoing-nbrs target-sid
    (s :waiting-marker-from val m)
    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src outgoing-nbrs target-sid
    m
    channels)))

(defthm
  cut-markers-in-transit-for-srcs-p-of-waiting-marker-from-update
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs target-sid
    (s :waiting-marker-from val m)
    procs channels)

   (cut-markers-in-transit-for-srcs-p
    srcs target-sid
    m
    procs channels)))




;; ------------------------------------------------------------
;; I takes its cut by receiving a marker from J.
;;
;; This lemma considers some OTHER process P and checks that
;; P's existing outgoing-marker obligations are preserved.
;;
;; Before the step:
;;   - I is in :cut-not-taken.
;;   - P is different from I.
;;
;; During the step:
;;   - I is removed from :cut-not-taken.
;;   - the received message is removed from channel J -> I.
;;
;; The removed message may be the target marker.
;; This is safe for P because, after I takes the cut, P no
;; longer has any marker-in-transit obligation whose destination
;; is I.
;;
;; All other outgoing channels of P are unchanged.
;;
;; P != I is essential.  I is the newly-cut process, so I gets
;; NEW outgoing marker obligations.  Those are established later
;; when I sends the marker to all of its outgoing neighbors.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; Preserve obligations of an OLD source when I takes the cut.
;;
;; I consumes a message from J and is removed from
;; :cut-not-taken.  For any source process P different from I,
;; its old outgoing-marker obligations remain valid.
;;
;; If the consumed message is the target marker on P -> I, that
;; removal is safe because after I takes the cut there is no
;; longer an obligation whose destination is I.
;;
;; P != I is essential: I is the newly-cut source and gains new
;; outgoing obligations, which are established by the broadcast.
;; ------------------------------------------------------------


(defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-preserved-when-i-takes-cut

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p
     nbrs
     target-sid
     m
     channels)

    ;; I has not taken the cut yet.
    (memberp i
             (cm-cut-not-taken m))

    ;; Removing I once really removes it.
    (uniquep
     (cm-cut-not-taken m))

    ;; P is not the process taking the cut now.
    (not (equal p i)))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    nbrs
    target-sid

    ;; I takes the cut.
    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))
       m)

    ;; I consumed the message received from J.
    (remove-message-from-channel
     j
     i
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p nbrs target-sid m channels)

    :in-theory
    (disable remove-message-from-channel))))



;; ------------------------------------------------------------
;; Source-level preservation when I takes its cut.
;;
;; I takes its cut by receiving a message from J.
;;
;; PIDS contains processes other than I.  For every process P
;; in PIDS, the outgoing-neighbor-level lemma says that P's outgoing
;; marker obligations are preserved when:
;;
;;   - I is removed from :cut-not-taken, and
;;   - the received message is removed from J -> I.
;;
;; We exclude I from PIDS because I is the newly-cut process.
;; I gets NEW outgoing marker obligations, which will be handled
;; separately by the marker broadcast from I.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; Source-list lift for the "I takes the cut" transition.
;;
;; PIDS intentionally excludes I.  Every process in PIDS is an
;; old source whose obligations survive both:
;;   1. removing I from :cut-not-taken, and
;;   2. consuming the message on J -> I.
;;
;; I itself is handled separately because taking the cut creates
;; new outgoing obligations for I.
;; ------------------------------------------------------------


(defthm
  cut-markers-in-transit-for-srcs-p-preserved-when-i-takes-cut

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     m
     procs
     channels)

    ;; I has not taken the cut before this step.
    (memberp i
             (cm-cut-not-taken m))

    (uniquep
     (cm-cut-not-taken m))

    ;; PIDS contains only the processes other than I.
    (not (memberp i pids)))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    ;; I now takes the cut.
    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))
       m)

    procs

    ;; I consumes the message received from J.
    (remove-message-from-channel
     j
     i
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     m
     procs
     channels)

    :in-theory
    (disable remove-message-from-channel
	     cm-cut-not-taken))))






(defthm marker-for-sid-in-channel-p-of-snoc-marker
  (implies
   (equal (msg-type msg) :marker)

   (marker-for-sid-in-channel-p
    (sid msg)
    (snoc channel msg))))

;; ------------------------------------------------------------
;; Marker broadcast CREATES the required marker.
;;
;; Unlike the generic send-preservation lemmas, this theorem does
;; not assume the target marker already exists.  If MSG is the
;; target marker and OUT-NBR is one of I's outgoing neighbors,
;; then after SEND-MSG-ALL-OUTGOING-CHANNELS the target marker is
;; present on channel I -> OUT-NBR.
;; ------------------------------------------------------------




(defthm
  target-marker-present-after-send-to-all-outgoing-nbrs

  (implies
   (and
    (memberp out-nbr outgoing-nbrs)

    (equal (msg-type msg)
           :marker)

    (equal (sid msg)
           target-sid))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     i
     out-nbr
     (send-msg-all-outgoing-channels
      msg
      i
      outgoing-nbrs
      channels))))

  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg i outgoing-nbrs channels))))




;; ------------------------------------------------------------
;; I has just taken the cut.
;;
;; Before this step I was in :cut-not-taken, so there were no
;; outgoing marker obligations for I.
;;
;; After removing I from :cut-not-taken, I becomes a cut process.
;; Therefore, for every outgoing neighbor that is still in
;; :cut-not-taken, a target marker must now be present on
;; channel I -> OUT-NBR.
;;
;; SEND-MSG-ALL-OUTGOING-CHANNELS establishes exactly these new
;; obligations by sending the target marker to every outgoing
;; neighbor of I.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; Establish I's NEW outgoing obligations when I takes the cut.
;;
;; Before the step I is in :cut-not-taken, so I has no outgoing
;; marker obligations.  After removing I from :cut-not-taken,
;; every outgoing neighbor that is still pre-cut requires a
;; target marker on I -> OUT-NBR.
;;
;; The outgoing marker broadcast establishes exactly those new
;; obligations.
;; ------------------------------------------------------------


(defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-when-i-takes-cut

  (implies
   (and
    ;; I has not taken the cut before this step.
    (memberp i
             (cm-cut-not-taken m))

    ;; Removing I once makes I definitely cut.
    (uniquep
     (cm-cut-not-taken m))

    ;; The message being broadcast is the target marker.
    (equal (msg-type msg)
           :marker)

    (equal (sid msg)
           target-sid))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    i
    outgoing-nbrs
    target-sid

    ;; I now takes the cut.
    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))
       m)

    ;; I broadcasts the target marker.
    (send-msg-all-outgoing-channels
     msg
     i
     outgoing-nbrs
     channels))))



(defthm
  cut-markers-in-transit-for-srcs-p-from-i-and-rest

  (implies
   (and
    (uniquep pids)

    (memberp i pids)

    ;; I's own outgoing obligations.
    (cut-marker-in-transit-for-outgoing-nbrs-p
     i
     (nbrs-to (g i procs))
     target-sid
     m
     channels)

    ;; Obligations for every other process.
    (cut-markers-in-transit-for-srcs-p
     (remove1-equal i pids)
     target-sid
     m
     procs
     channels))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    channels)))


;; Removing one PID from the list of source processes cannot
;; create any new marker obligation.  Therefore, if the
;; invariant holds for all PIDS, it also holds after removing I.

(defthm
  cut-markers-in-transit-for-srcs-p-of-remove1-equal

  (implies
   (cut-markers-in-transit-for-srcs-p
    pids target-sid m procs channels)

   (cut-markers-in-transit-for-srcs-p
    (remove1-equal i pids)
    target-sid
    m
    procs
    channels)))


;; If:
;;
;;   1. I occurs in PIDS,
;;   2. I's own outgoing-marker obligation holds, and
;;   3. the invariant holds for every PID other than I,
;;
;; then the invariant holds for the complete PIDS list.
;;
;; UNIQUEP is important because REMOVE1-EQUAL I PIDS must
;; represent exactly "all the other PIDs".

(defthm
  cut-markers-in-transit-for-srcs-p-from-i-and-other-pids

  (implies
   (and
    (uniquep pids)

    (memberp i pids)

    ;; I itself.
    (cut-marker-in-transit-for-outgoing-nbrs-p
     i
     (nbrs-to (g i procs))
     target-sid
     m
     channels)

    ;; Every process other than I.
    (cut-markers-in-transit-for-srcs-p
     (remove1-equal i pids)
     target-sid
     m
     procs
     channels))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    channels)))

;; ------------------------------------------------------------
;; Complete first-target-marker transition.
;;
;; This combines the two essential pieces:
;;
;;   - all old source processes keep their existing obligations
;;     when I takes the cut and consumes J -> I; and
;;
;;   - I, the newly-cut source, obtains its new outgoing
;;     obligations because it broadcasts the target marker.
;;
;; This is the main semantic lemma for a process taking its cut
;; upon receiving the first target checkpoint marker.
;; ------------------------------------------------------------



(defthm
  cut-markers-in-transit-for-srcs-p-after-i-takes-cut-and-sends-marker

  (implies
   (and
    ;; Old invariant.
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     m
     procs
     channels)

    ;; I has not taken the cut before this step.
    (memberp i
             (cm-cut-not-taken m))

    (uniquep
     (cm-cut-not-taken m))

    (uniquep pids)

    ;; The broadcast message is the target marker.
    (equal (msg-type msg) :marker)

    (equal (sid msg) target-sid))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    ;; I takes the cut.
    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))
       m)

    procs

    ;; First consume J -> I, then I broadcasts the marker.
    (send-msg-all-outgoing-channels
     msg
     i
     (nbrs-to (g i procs))
     (remove-message-from-channel
      j i channels))))

  :hints
  (("Goal"
    :in-theory (disable remove-message-from-channel
			cm-cut-not-taken)
    :cases ((memberp i pids)))))


(defthm cm-cut-not-taken-of-cut-not-taken-update
  (equal
   (cm-cut-not-taken
    (s :cut-not-taken val m))
   val))



(defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-of-cut-update-over-waiting-and-after-cut

  (equal
   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid

    (s :cut-not-taken
       cut-not-taken
       (s :waiting-marker-from
          waiting
          (s :after-cut-input-sequence
             after-cut
             m)))

    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid

    (s :cut-not-taken
       cut-not-taken
       m)

    channels))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p
     outgoing-nbrs
     target-sid
     (s :cut-not-taken cut-not-taken m)
     channels))))



(defthm
  cut-markers-in-transit-for-srcs-p-of-cut-update-over-waiting-and-after-cut

  (equal
   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    (s :cut-not-taken
       cut-not-taken
       (s :waiting-marker-from
          waiting
          (s :after-cut-input-sequence
             after-cut
             m)))

    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    (s :cut-not-taken
       cut-not-taken
       m)

    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     (s :cut-not-taken cut-not-taken m)
     procs
     channels))))

;; ------------------------------------------------------------
;; Metadata/implementation consistency: cut not yet taken.
;;
;; If metadata says I is still in :cut-not-taken, then the
;; implementation cannot already contain TARGET-SID in I's
;; snapshot IDs.
;;
;; This is the converse consistency fact used to eliminate
;; impossible marker-receive branches.
;; ------------------------------------------------------------



(defthm
  cut-meta-imp-procs-consistent-p-cut-not-taken-implies-no-snapshot

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (memberp i ids)

    (cm-cut-not-taken-p m i))

   (not
    (memberp
     target-sid
     (snapshot-ids
      (g i procs))))))

(defthm cm-cut-not-taken-of-waiting-marker-from-update
  (equal
   (cm-cut-not-taken
    (s :waiting-marker-from val m))
   (cm-cut-not-taken m)))



;; ------------------------------------------------------------
;; I has already taken the cut.
;;
;; Therefore no process has an in-transit marker obligation
;; whose destination is I.
;;
;; Hence removing any message from J -> I is safe for the
;; marker-in-transit invariant.  In this branch the removed
;; message is the target marker, but that does not matter:
;; destination I is already cut.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; Later target-marker receive.
;;
;; If I has already taken the cut, no source has an outstanding
;; marker-in-transit obligation whose destination is I.
;; Therefore consuming any message on J -> I, including the
;; target marker itself, cannot violate this invariant.
;; ------------------------------------------------------------


(defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-remove-message-when-i-already-cut

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p
     outgoing-nbrs
     target-sid
     m
     channels)

    (not
     (memberp i
              (cm-cut-not-taken m))))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid
    m
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p outgoing-nbrs target-sid m channels)

    :in-theory
    (disable remove-message-from-channel))))

;; ------------------------------------------------------------
;; Global lift for a later marker received by an already-cut I.
;;
;; Since destination I is already closed with respect to the cut,
;; removing the message from J -> I preserves every source's
;; remaining marker-in-transit obligations.
;; ------------------------------------------------------------



(defthm
  cut-markers-in-transit-for-srcs-p-preserved-by-remove-message-when-i-already-cut

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     m
     procs
     channels)

    (not
     (memberp i
              (cm-cut-not-taken m))))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids target-sid m procs channels)

    :in-theory
    (disable remove-message-from-channel))))

(defthm
  cut-markers-in-transit-for-srcs-p-of-snapshots-update

  (equal
   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    (s i
       (s :snapshots val
          (g i procs))
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids target-sid m procs channels))))

;; ------------------------------------------------------------
;; Removing a marker for a DIFFERENT checkpoint is safe.
;;
;; A RECEIVE may consume a marker whose SID is not TARGET-SID.
;; Such a message is irrelevant to the target cut.  Any marker
;; for TARGET-SID already present in the channel remains after
;; this non-target marker is removed.
;; ------------------------------------------------------------




(defthm
  marker-for-sid-in-channel-p-preserved-by-remove-non-target-marker

  (implies
   (and
    (consp
     (channel-state j i channels))

    ;; The consumed message is not the marker for TARGET-SID.
    (not
     (and
      (equal
       (msg-type
        (get-msg-from-channel j i channels))
       :marker)

      (equal
       (sid
        (get-msg-from-channel j i channels))
       target-sid)))

    (marker-for-sid-in-channel-p
     target-sid
     (channel-state p q channels)))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     p q
     (remove-message-from-channel
      j i channels))))

  :hints
  (("Goal"
    :cases
    ((equal p j)
     (equal q i))
    :in-theory
    (disable remove-message-from-channel))))


(defthm
  different-sid-marker-implies-not-target-marker

  (implies
   (and
    (equal
     (msg-type msg)
     :marker)

    (not
     (equal
      (sid msg)
      target-sid)))

   (not
    (and
     (equal
      (msg-type msg)
      :marker)

     (equal
      (sid msg)
      target-sid)))))

(defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-remove-non-target-marker

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p outgoing-nbrs target-sid m channels)

    (consp
     (channel-state j i channels))

    (not
     (and
      (equal
       (msg-type
        (get-msg-from-channel j i channels))
       :marker)

      (equal
       (sid
        (get-msg-from-channel j i channels))
       target-sid))))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid
    m
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p outgoing-nbrs target-sid m channels))))

;; ------------------------------------------------------------
;; Global preservation when a different-SID marker is consumed.
;;
;; The target cut metadata does not change in this case, and the
;; removed marker belongs to another checkpoint.  Therefore all
;; target-marker obligations survive the receive.
;; ------------------------------------------------------------



(defthm
  cut-markers-in-transit-for-srcs-p-preserved-by-remove-non-target-marker

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     pids target-sid m procs channels)

    (consp
     (channel-state j i channels))

    (not
     (and
      (equal
       (msg-type
        (get-msg-from-channel j i channels))
       :marker)

      (equal
       (sid
        (get-msg-from-channel j i channels))
       target-sid))))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :in-theory (disable remove-message-from-channel
			get-msg-from-channel)
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids target-sid m procs channels))))


;; ------------------------------------------------------------
;; START-RECOVERY-HELPER changes recovery-related process fields,
;; but it does not change any process's outgoing-neighbor list.
;;
;; The marker-in-transit invariant only uses PROCS to obtain
;; (nbrs-to (g src procs)).
;;
;; Therefore START-RECOVERY-HELPER is invisible to this invariant.
;; ------------------------------------------------------------

(defthm
  cut-markers-in-transit-for-srcs-p-of-start-recovery-helper

  (equal
   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    (start-recovery-helper procs i)
    channels)

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     m
     procs
     channels)

    :in-theory
    (disable start-recovery-helper))))






;; ------------------------------------------------------------
;; I initiates the target checkpoint.
;;
;; Before the step every PID is in :cut-not-taken, so no
;; process has outgoing marker obligations.
;;
;; I is then removed from :cut-not-taken.  This creates new
;; outgoing marker obligations only for I.
;;
;; SEND-MSG-ALL-OUTGOING-CHANNELS sends the target marker to
;; every outgoing neighbor of I, establishing those new
;; obligations.  Every other PID remains in :cut-not-taken,
;; so it still has no outgoing obligations.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; Initiator starts the target checkpoint.
;;
;; Before the start step, PIDS is exactly :cut-not-taken, so no
;; process has an outgoing marker obligation.
;;
;; I is removed from :cut-not-taken, making I the only newly-cut
;; source.  The marker broadcast from I establishes I's required
;; markers to every still-pre-cut outgoing neighbor.  Every other
;; PID remains pre-cut and therefore has no source obligation.
;;
;; This is the main semantic lemma for the :START-CHECKPOINT
;; branch.
;; ------------------------------------------------------------


(defthm
  cut-markers-in-transit-for-srcs-p-after-i-starts-checkpoint

  (implies
   (and
    (equal
     (cm-cut-not-taken m)
     pids)

    (uniquep pids)

    (memberp i pids)

    (equal (msg-type msg)
           :marker)

    (equal (sid msg)
           target-sid))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))
       m)

    procs

    (send-msg-all-outgoing-channels
     msg
     i
     (nbrs-to (g i procs))
     channels)))

  :hints
  (("Goal"
    :in-theory (disable cm-cut-not-taken)
    :cases ((memberp i pids)))))

(defthm cm-cut-not-taken-of-before-cut-input-sequence-update
  (equal
   (cm-cut-not-taken
    (s :before-cut-input-sequence val m))
   (cm-cut-not-taken m)))



(defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-of-cut-update-over-waiting-and-before-cut

  (equal
   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid

    (s :cut-not-taken
       cut-not-taken
       (s :waiting-marker-from
          waiting
          (s :before-cut-input-sequence
             before-cut
             m)))

    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid

    (s :cut-not-taken
       cut-not-taken
       m)

    channels))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p
     outgoing-nbrs
     target-sid
     (s :cut-not-taken cut-not-taken m)
     channels))))


(defthm
  cut-markers-in-transit-for-srcs-p-of-cut-update-over-waiting-and-before-cut

  (equal
   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    (s :cut-not-taken
       cut-not-taken
       (s :waiting-marker-from
          waiting
          (s :before-cut-input-sequence
             before-cut
             m)))

    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    (s :cut-not-taken
       cut-not-taken
       m)

    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     (s :cut-not-taken cut-not-taken m)
     procs
     channels))))


(defthm cm-cut-not-taken-of-after-cut-input-sequence-update
  (equal
   (cm-cut-not-taken
    (s :after-cut-input-sequence val m))
   (cm-cut-not-taken m))
  :hints
  (("Goal"
    :in-theory
    (enable cm-cut-not-taken))))

;; ============================================================
;; MAIN ONE-STEP PRESERVATION THEOREM
;;
;; If:
;;   - the marker-in-transit invariant holds before the step,
;;   - cut metadata is consistent with the implementation,
;;   - the implementation state and cut metadata are well formed,
;;   - and INPUT is legal,
;;
;; then processing the same INPUT in both:
;;
;;     PROCESS-CUT-STEP   -- metadata evolution
;;     SYSTEM-STEP        -- implementation evolution
;;
;; preserves CUT-MARKERS-IN-TRANSIT-P.
;;
;; The supporting lemmas above cover the semantic cases:
;;   * ordinary sends and receives,
;;   * recovery traffic,
;;   * non-target checkpoint markers,
;;   * later target-marker receives,
;;   * first target-marker receives where a process takes its cut,
;;   * and the initiator's START-CHECKPOINT step.
;;
;; This theorem is the step-level invariant needed to lift the
;; property to an entire input segment by induction.
;; ============================================================






(defthm cut-markers-in-transit-p-preserved-by-step
  (implies
   (and
    (cut-markers-in-transit-p
     m
     st)

    (cut-meta-imp-consistent-p
     m
     st)

    (good-state-p st)
    (good-cut-meta-p m)
    (legal-inputp
     st
     input))

   (cut-markers-in-transit-p
    (process-cut-step
     input
     st
     m)

    (system-step
     st
     input)))
  :hints (("Goal"
	   :in-theory (disable record-msg-in-snapshots
			       update-proc-for-first-marker-msg
			       
			      update-proc-for-first-recovery-msg
			      update-proc-for-non-first-recovery-msg
			      start-recovery-helper
			       start-checkpoint-helper
			       create-marker-message
			       create-recovery-message
			       remove-message-from-channel
			       get-msg-from-channel
			       update-proc-for-normal-msg-core
			       cm-cut-not-taken
			     ;  cm-after-cut-append
					; cm-after-cut-msg-append
			       ))))





;; ------------------------------------------------------------
;; Marker-in-transit preservation over an entire input segment.
;;
;; PROCESS-CUT-SEGMENT processes each input through the cut
;; metadata scanner, while RUN-IMP executes the same input
;; sequence in the implementation.
;;
;; The one-step theorem preserves CUT-MARKERS-IN-TRANSIT-P.
;; To apply it repeatedly, the induction also relies on the
;; segment/step preservation of:
;;
;;   - CUT-META-IMP-CONSISTENT-P
;;   - GOOD-CUT-META-P
;;   - GOOD-STATE-P
;;
;; LEGAL-INPUT-SEQUENCEP guarantees that each input is legal
;; at the implementation state where that input is executed.
;; ------------------------------------------------------------

(defthm cut-markers-in-transit-p-preserved-by-segment
  (implies
   (and
    (cut-markers-in-transit-p m st)

    (cut-meta-imp-consistent-p m st)

    (good-state-p st)

    (good-cut-meta-p m)

    (legal-input-sequencep st inputs))

   (cut-markers-in-transit-p
    (process-cut-segment inputs st m)
    (run-imp st inputs)))

  :hints
  (("Goal"
    :induct
    (process-cut-segment
     inputs
     st
     m)

    :in-theory
    (disable
     good-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cut-markers-in-transit-p
     process-cut-step
     system-step
     legal-inputp))))







(defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-implies-marker

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src
     outgoing-nbrs
     target-sid
     m
     channels)

    (memberp dst outgoing-nbrs)

    ;; SRC is post-cut.
    (not
     (cm-cut-not-taken-p m src))

    ;; DST is pre-cut.
    (cm-cut-not-taken-p m dst))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     channels)))
  :rule-classes
((:rewrite
  :match-free :all)))


(defthm
  cut-markers-in-transit-for-srcs-p-implies-marker

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
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
     src
     dst
     channels)))
    :rule-classes
((:rewrite
  :match-free :all)))


;; ------------------------------------------------------------
;; Global marker consequence of CUT-MARKERS-IN-TRANSIT-P.
;;
;; If SRC has taken the cut, DST is still pre-cut, and DST is
;; an outgoing neighbor of SRC, then the target marker is
;; present somewhere on SRC -> DST.
;;
;; This is just the global wrapper around
;; CUT-MARKERS-IN-TRANSIT-FOR-SRCS-P-IMPLIES-MARKER.
;; ------------------------------------------------------------

(defthm
  cut-markers-in-transit-p-implies-marker

  (implies
   (and
    (cut-markers-in-transit-p
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

   (marker-for-sid-in-channel-p
    (cm-sid m)
    (channel-state
     src
     dst
     (channels st))))
    :rule-classes
((:rewrite
  :match-free :all)))


(defthm marker-for-sid-in-channel-p-implies-consp
  (implies
   (marker-for-sid-in-channel-p
    target-sid
    channel)

   (consp channel))
      :rule-classes
((:rewrite
  :match-free :all)))

;; ------------------------------------------------------------
;; If SRC is post-cut and DST is still pre-cut, the target
;; marker must be somewhere on SRC -> DST.  Therefore that
;; channel was already nonempty.
;; ------------------------------------------------------------
(defthm
  cut-markers-in-transit-for-srcs-p-implies-channel-consp

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
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

   (consp
    (channel-state
     src
     dst
     channels)))
  :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :in-theory
    (disable
     cm-cut-not-taken-p))))



;; ------------------------------------------------------------
;; Global version of the FOR-SRCS channel-nonempty theorem.
;;
;; CUT-MARKERS-IN-TRANSIT-P expands to
;;
;;   CUT-MARKERS-IN-TRANSIT-FOR-SRCS-P
;;      (PROC-IDS ST)
;;      (CM-SID M)
;;      M
;;      (PROCS ST)
;;      (CHANNELS ST)
;;
;; Therefore, if SRC is one of the processes, DST is an
;; outgoing neighbor of SRC, SRC is post-cut, and DST is
;; still pre-cut, then SRC -> DST must already contain the
;; target marker and hence must be nonempty.
;; ------------------------------------------------------------

(defthm
  cut-markers-in-transit-p-implies-channel-consp

  (implies
   (and
    (cut-markers-in-transit-p
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

    ;; SRC has already taken the cut.
    (not
     (cm-cut-not-taken-p
      m
      src))

    ;; DST has not yet taken the cut.
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
    :match-free :all)))
