(in-package "ACL2")
(include-book "model")
(include-book "invariants")


(defun proc-equivalent-p (imp-p spec-p)
  ;; Spec process keeps only the application-visible process fields.
  (and
   (equal (local-state imp-p)
          (local-state spec-p))
   (equal (nbrs-to imp-p)
          (nbrs-to spec-p))
   (equal (nbrs-from imp-p)
          (nbrs-from spec-p))))


(defun procs-equivalent-p (ids imp-procs spec-procs)
  ;; Check process equivalence for every process id.
  (if (endp ids)
      t
    (and
     (proc-equivalent-p
      (g (first ids) imp-procs)
      (g (first ids) spec-procs))
     (procs-equivalent-p
      (rest ids)
      imp-procs
      spec-procs))))


(defun imp-spec-channel-msgs-equivalent-p (imp-msgs spec-msgs)
  ;; SPEC-MSGS should be exactly the normal-message projection of IMP-MSGS.
  ;;
  ;; While scanning the implementation channel:
  ;;   - marker/recovery/non-normal messages are skipped;
  ;;   - normal messages must match the current head of the spec channel;
  ;;   - the spec-channel pointer advances only when a normal msg is matched.
  (if (endp imp-msgs)
      (endp spec-msgs)
    (let ((msg (first imp-msgs)))
      (if (equal (msg-type msg) :normal)
          (and
           (consp spec-msgs)
           (equal msg (first spec-msgs))
           (imp-spec-channel-msgs-equivalent-p
            (rest imp-msgs)
            (rest spec-msgs)))
        (imp-spec-channel-msgs-equivalent-p
         (rest imp-msgs)
         spec-msgs)))))


(defun incoming-channels-equivalent-for-proc-p
    (srcs dst imp-channels spec-channels)
  ;; Check every incoming channel src -> dst.
  (if (endp srcs)
      t
    (and
     (imp-spec-channel-msgs-equivalent-p
      (channel-state (first srcs) dst imp-channels)
      (channel-state (first srcs) dst spec-channels))
     (incoming-channels-equivalent-for-proc-p
      (rest srcs)
      dst
      imp-channels
      spec-channels))))


(defun imp-spec-channels-equivalent-p-aux
    (dsts imp-procs imp-channels spec-channels)
  ;; For each destination process, check all of its incoming channels.
  (if (endp dsts)
      t
    (let* ((dst       (first dsts))
           (imp-p     (g dst imp-procs))
           (srcs      (nbrs-from imp-p)))
      (and
       (incoming-channels-equivalent-for-proc-p
        srcs
        dst
        imp-channels
        spec-channels)
       (imp-spec-channels-equivalent-p-aux
        (rest dsts)
        imp-procs
        imp-channels
        spec-channels)))))


(defun imp-spec-channels-equivalent-p (ids imp-st spec-st)
  (imp-spec-channels-equivalent-p-aux
   ids
   (procs imp-st)
   (channels imp-st)
   (channels spec-st)))


(defun imp-spec-equivalent-p (imp-st spec-st)
  ;; Full implementation/spec equivalence:
  ;;   1. same process ids;
  ;;   2. same visible process fields;
  ;;   3. spec channels are the normal-message projection of imp channels.
  (let ((ids (proc-ids imp-st)))
    (and
     (equal (proc-ids imp-st)
            (proc-ids spec-st))
     (procs-equivalent-p
      ids
      (procs imp-st)
      (procs spec-st))
     (imp-spec-channels-equivalent-p
      ids
      imp-st
      spec-st))))

;end definitions: imp-spec-equivalence




(defthm proc-ids-equal-when-imp-spec-equivalent-p
  (implies
   (imp-spec-equivalent-p imp-st spec-st)
   (equal (proc-ids imp-st)
          (proc-ids spec-st))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Process equivalence preservation under normal local-state update
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm proc-equivalent-p-implies-local-state-equal
  (implies
   (proc-equivalent-p imp-p spec-p)
   (equal
    (local-state imp-p)
    (local-state spec-p))))

;; (defthm proc-equivalent-p-of-update-local-state
;;   (implies
;;    (and
;;     (proc-equivalent-p imp-p spec-p)
;;     (equal new-imp-local new-spec-local))
;;    (proc-equivalent-p
;;     (s :local-state new-imp-local imp-p)
;;     (s :local-state new-spec-local spec-p))))


(defthm proc-equivalent-p-of-same-local-state-update
  (implies
   (proc-equivalent-p imp-p spec-p)
   (proc-equivalent-p
    (s :local-state new-local imp-p)
    (s :local-state new-local spec-p))))


(defthm procs-equivalent-p-of-same-local-state-update
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids
    (s i
       (s :local-state new-local
          (g i imp-procs))
       imp-procs)
    (s i
       (s :local-state new-local
          (g i spec-procs))
       spec-procs))))

(defthm procs-equivalent-p-of-normal-local-state-update
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids

    ;; Updated implementation process table.
    (s i
       (s :local-state
          (update-local-state-normal
           (local-state
            (g i imp-procs)))
          (g i imp-procs))
       imp-procs)

    ;; Updated spec process table.
    (s i
       (s :local-state
          (update-local-state-normal
           (local-state
            (g i spec-procs)))
          (g i spec-procs))
       spec-procs))))


(defun send-compute-message-pair-induct
    (local sender nbrs imp-channels spec-channels)
  (if (endp nbrs)
      (list imp-channels spec-channels)
    (if (message-to-send? local (first nbrs))
        (let* ((nbr           (first nbrs))
               (msg           (create-compute-message local nbr))

               ;; Update implementation channel sender -> nbr.
               (imp-channel   (channel-state sender nbr imp-channels))
               (imp-channel   (snoc imp-channel msg))
               (imp-channels  (>channel sender nbr imp-channel imp-channels))

               ;; Update spec channel sender -> nbr in the same way.
               (spec-channel  (channel-state sender nbr spec-channels))
               (spec-channel  (snoc spec-channel msg))
               (spec-channels (>channel sender nbr spec-channel spec-channels)))
          (send-compute-message-pair-induct
           local
           sender
           (rest nbrs)
           imp-channels
           spec-channels))
      (send-compute-message-pair-induct
       local
       sender
       (rest nbrs)
       imp-channels
       spec-channels))))


(defthm imp-spec-channel-msgs-equivalent-p-of-snoc-create-compute-message
  (implies
   (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
   (imp-spec-channel-msgs-equivalent-p
    (snoc imp-msgs
          (create-compute-message local nbr))
    (snoc spec-msgs
          (create-compute-message local nbr)))))


(defthm imp-spec-channel-msgs-equivalent-p-of-send-compute-message
  (implies
   (imp-spec-channel-msgs-equivalent-p
    (channel-state src dst imp-channels)
    (channel-state src dst spec-channels))

   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (send-compute-message local sender nbrs imp-channels))
    (channel-state
     src dst
     (send-compute-message local sender nbrs spec-channels))))

  :hints
  (("Goal"
    :induct
    (send-compute-message-pair-induct
     local sender nbrs imp-channels spec-channels))))


(defthm incoming-channels-equivalent-for-proc-p-of-send-compute-message-same
  (implies
   (incoming-channels-equivalent-for-proc-p
    srcs dst imp-channels spec-channels)
   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (send-compute-message local sender nbrs imp-channels)
    (send-compute-message local sender nbrs spec-channels))))


(defthm imp-spec-channels-equivalent-p-aux-of-send-compute-message-same
  (implies
   (imp-spec-channels-equivalent-p-aux
    ids imp-procs imp-channels spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (send-compute-message local sender nbrs imp-channels)
    (send-compute-message local sender nbrs spec-channels))))



(defthm imp-spec-channels-equivalent-p-aux-of-local-state-update-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (s i
       (s :local-state new-local (g i procs))
       procs)
    imp-channels
    spec-channels)

   (imp-spec-channels-equivalent-p-aux
    ids
    procs
    imp-channels
    spec-channels)))




;; Projection facts from process equivalence
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defthm local-state-of-spec-proc-when-procs-equivalent-p
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (equal
    (local-state (g i spec-procs))
    (local-state (g i imp-procs)))))


(defthm nbrs-to-of-spec-proc-when-procs-equivalent-p
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (equal
    (nbrs-to (g i spec-procs))
    (nbrs-to (g i imp-procs)))))
 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Normal step preserves implementation/spec equivalence
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-equivalent-p-of-step-normal
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)
    (memberp i (proc-ids imp-st)))
   (imp-spec-equivalent-p
    (step-normal imp-st i)
    (spec-step-normal spec-st i)))
  :hints
  (("Goal"
    :in-theory
    (disable
      good-state-p
      good-spec-state-p
      good-proc-p
      good-spec-proc-p
      send-compute-message))))





(defthm proc-equivalent-p-of-start-checkpoint-helper-left-same-proc
  (implies
   (proc-equivalent-p (g i imp-procs)
                      (g i spec-procs))
   (proc-equivalent-p
    (g i (start-checkpoint-helper imp-procs i))
    (g i spec-procs))))

(defthm proc-equivalent-p-of-start-checkpoint-helper-left-diff-proc
  (implies
   (and
    (not (equal k i))
    (proc-equivalent-p (g k imp-procs)
                       (g k spec-procs)))
   (proc-equivalent-p
    (g k (start-checkpoint-helper imp-procs i))
    (g k spec-procs))))

(defthm procs-equivalent-p-of-start-checkpoint-helper-left
  (implies
   (procs-equivalent-p ids imp-procs spec-procs)
   (procs-equivalent-p
    ids
    (start-checkpoint-helper imp-procs i)
    spec-procs))
  :hints
  (("Goal"
    :induct (procs-equivalent-p ids imp-procs spec-procs)
    :in-theory
    (disable proc-equivalent-p start-checkpoint-helper))

   ("Subgoal *1/2"
    :cases ((equal (car ids) i)))))




(defthm imp-spec-channel-msgs-equivalent-p-of-snoc-create-marker-message-left
  (implies
   (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
   (imp-spec-channel-msgs-equivalent-p
    (snoc imp-msgs
          (create-marker-message local sid))
    spec-msgs)))

(defthm imp-spec-channel-msgs-equivalent-p-of-send-marker-one-channel
  (implies
   (imp-spec-channel-msgs-equivalent-p
    (channel-state src dst imp-channels)
    (channel-state src dst spec-channels))
   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (send-msg-all-outgoing-channels
      (create-marker-message local sid)
      sender
      nbrs
      imp-channels))
    (channel-state
     src dst
     spec-channels)))
  :hints
  (("Goal"
    :in-theory
    (disable create-marker-message))))


(defthm incoming-channels-equivalent-for-proc-p-of-send-marker-left
  (implies
   (incoming-channels-equivalent-for-proc-p
    srcs dst imp-channels spec-channels)
   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (send-msg-all-outgoing-channels
     (create-marker-message local sid)
     sender
     nbrs
     imp-channels)
    spec-channels))
  :hints
  (("Goal"
    :induct
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)
    :in-theory
    (disable create-marker-message send-msg-all-outgoing-channels))))


(defthm imp-spec-channels-equivalent-p-aux-of-send-marker-left
  (implies
   (imp-spec-channels-equivalent-p-aux
    ids imp-procs imp-channels spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (send-msg-all-outgoing-channels
     (create-marker-message local sid)
     sender
     nbrs
     imp-channels)
    spec-channels))
  :hints
  (("Goal"
    ;; :induct
    ;; (imp-spec-channels-equivalent-p-aux
    ;;  ids imp-procs imp-channels spec-channels)
    :in-theory
    (disable create-marker-message))))


(defthm imp-spec-channels-equivalent-p-aux-of-start-checkpoint-helper-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (start-checkpoint-helper imp-procs i)
    imp-channels
    spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    imp-channels
    spec-channels))
  :hints (("Goal"
	   :in-theory (disable start-checkpoint-helper))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Main theorem:
;;    step-checkpoint on implementation, no change on spec.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-equivalent-p-of-step-checkpoint
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)
    (memberp i (proc-ids imp-st)))
   (imp-spec-equivalent-p
    (step-checkpoint imp-st i)
    spec-st))
  :hints
  (("Goal"
    :in-theory
    (disable
     good-state-p
      good-spec-state-p
      good-proc-p
      good-spec-proc-p
      send-msg-all-outgoing-channels
      create-marker-message
      start-checkpoint-helper))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; step-recover: only channel equivalence is preserved
;;
;; We do NOT prove full imp-spec-equivalent-p here, because recovery changes
;; implementation local-state/proc-status, while the spec state does not step.
;;
;; What should remain true:
;;   spec channels are still the normal-message projection of imp channels.
;; Recovery messages are non-normal, so adding them to implementation channels
;; does not change the projected spec channels.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Snoc of recovery message on implementation side preserves
;;    message-list equivalence
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-channel-msgs-equivalent-p-of-snoc-create-recovery-message-left
  (implies
   (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
   (imp-spec-channel-msgs-equivalent-p
    (snoc imp-msgs
          (create-recovery-message local sid))
    spec-msgs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Sending recovery messages on implementation channels only preserves
;;    one channel-message equivalence
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-channel-msgs-equivalent-p-of-send-recovery-message-left
  (implies
   (imp-spec-channel-msgs-equivalent-p
    (channel-state src dst imp-channels)
    (channel-state src dst spec-channels))
   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (send-msg-all-outgoing-channels
      (create-recovery-message local sid)
      sender
      nbrs
      imp-channels))
    (channel-state src dst spec-channels)))
  :hints
  (("Goal"
    :in-theory
    (disable create-recovery-message))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Lift to incoming-channel equivalence for one destination process
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm incoming-channels-equivalent-for-proc-p-of-send-recovery-message-left
  (implies
   (incoming-channels-equivalent-for-proc-p
    srcs dst imp-channels spec-channels)
   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (send-msg-all-outgoing-channels
     (create-recovery-message local sid)
     sender
     nbrs
     imp-channels)
    spec-channels))
    :hints
  (("Goal"
    :in-theory
    (disable create-recovery-message))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Lift to all channels
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-channels-equivalent-p-aux-of-send-recovery-message-left
  (implies
   (imp-spec-channels-equivalent-p-aux
    ids imp-procs imp-channels spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (send-msg-all-outgoing-channels
     (create-recovery-message local sid)
     sender
     nbrs
     imp-channels)
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    :in-theory
    (disable create-recovery-message))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. start-recovery-helper changes recovery metadata/local-state, but not
;;    nbrs-from.  Channel equivalence only uses nbrs-from from imp-procs.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm nbrs-from-of-start-recovery-helper
  (equal
   (nbrs-from
    (g k
       (start-recovery-helper procs i)))
   (nbrs-from
    (g k procs))))

(defthm imp-spec-channels-equivalent-p-aux-of-start-recovery-helper-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (start-recovery-helper imp-procs i)
    imp-channels
    spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    imp-channels
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    :in-theory
    (disable start-recovery-helper))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Main theorem:
;;    step-recover on implementation preserves only channel equivalence
;;    with unchanged spec state.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-channels-equivalent-p-of-step-recover
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)
    (memberp i (proc-ids imp-st)))
   (imp-spec-channels-equivalent-p
    (proc-ids imp-st)
    (step-recover imp-st i)
    spec-st))
  :hints
  (("Goal"
    :in-theory
    (disable
     good-state-p
      good-spec-state-p
      good-proc-p
      good-spec-proc-p
      send-msg-all-outgoing-channels
      create-recovery-message
      start-recovery-helper))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; proc-ids preservation for marker-message handling
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; proc-ids preservation for marker-message handling
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm proc-ids-of-handle-first-marker-msg
  (equal
   (proc-ids
    (handle-first-marker-msg st i j msg))
   (proc-ids st)))


(defthm proc-ids-of-handle-non-first-marker-msg
  (equal
   (proc-ids
    (handle-non-first-marker-msg st i j msg))
   (proc-ids st)))



(defthm proc-ids-of-handle-marker-msg
  (equal
   (proc-ids
    (handle-marker-msg st i j msg))
   (proc-ids st)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Non-first marker preserves visible process equivalence
;;
;; Non-first marker handling only updates snapshot metadata:
;;   :snapshots / snapshot entry status / waiting-marker-from
;;
;; It does not change:
;;   :local-state
;;   :nbrs-to
;;   :nbrs-from
;;
;; So process equivalence with the spec process is preserved.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm proc-equivalent-p-of-update-proc-for-non-first-marker-msg-left
  (implies
   (proc-equivalent-p imp-p spec-p)
   (proc-equivalent-p
    (update-proc-for-non-first-marker-msg imp-p sid j)
    spec-p)))


(defthm procs-equivalent-p-of-set-non-first-marker-proc-left
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids
    (s i
       (update-proc-for-non-first-marker-msg
        (g i imp-procs)
        sid
        j)
       imp-procs)
    spec-procs))
  :hints
  (("Goal"
    :induct (procs-equivalent-p ids imp-procs spec-procs)
    :in-theory
    (disable update-proc-for-non-first-marker-msg proc-equivalent-p))
   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))


(defthm procs-equivalent-p-of-handle-non-first-marker-msg-left
  (implies
   (and
    (procs-equivalent-p ids
                        (procs imp-st)
                        (procs spec-st))
    (memberp i ids))
   (procs-equivalent-p
    ids
    (procs
     (handle-non-first-marker-msg imp-st i j msg))
    (procs spec-st))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Channel equivalence preservation for handle-non-first-marker-msg
;;
;; Non-first marker handling:
;;   1. updates only snapshot metadata in process i;
;;   2. removes the marker message from channel j -> i.
;;
;; Since marker messages are non-normal, removing that marker from the
;; implementation channel does not change the normal-message projection.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;; 1. update-proc-for-non-first-marker-msg preserves nbrs-from
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm nbrs-from-of-set-snapshot-entry
;;   (equal
;;    (nbrs-from
;;     (set-snapshot-entry sid entry p))
;;    (nbrs-from p))
;;   :hints
;;   (("Goal"
;;     :in-theory
;;     (enable set-snapshot-entry))))


;; (defthm nbrs-from-of-update-proc-for-non-first-marker-msg
;;   (equal
;;    (nbrs-from
;;     (update-proc-for-non-first-marker-msg p sid j))
;;    (nbrs-from p))
;;   :hints
;;   (("Goal"
;;     :in-theory
;;     (enable update-proc-for-non-first-marker-msg
;;             nbrs-from-of-set-snapshot-entry))))


;; (defthm nbrs-from-of-procs-handle-non-first-marker-msg
;;   (equal
;;    (nbrs-from
;;     (g k
;;        (procs
;;         (handle-non-first-marker-msg st i j msg))))
;;    (nbrs-from
;;     (g k
;;        (procs st))))
;;   :hints
;;   (("Goal"
;;     :cases ((equal k i))
;;     :in-theory
;;     (enable handle-non-first-marker-msg
;;             nbrs-from-of-update-proc-for-non-first-marker-msg))))


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;; 2. Changing procs by handle-non-first-marker-msg does not affect
;; ;;    imp/spec channel equivalence, because the equivalence predicate
;; ;;    only reads nbrs-from from imp-procs.
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-channels-equivalent-p-aux-of-handle-non-first-marker-msg-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs
     (handle-non-first-marker-msg st i j msg))
    imp-channels
    spec-channels)

   (imp-spec-channels-equivalent-p-aux
    ids
    (procs st)
    imp-channels
    spec-channels)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Main non-first-marker channel theorem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Channel part of non-first marker handling
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm channels-of-handle-non-first-marker-msg
  (equal
   (channels
    (handle-non-first-marker-msg st i j msg))
   (remove-message-from-channel j i (channels st))))

(defthm imp-spec-channel-msgs-equivalent-p-of-cdr-left-when-head-non-normal
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
    (consp imp-msgs)
    (not (equal (msg-type (first imp-msgs)) :normal)))
   (imp-spec-channel-msgs-equivalent-p
    (rest imp-msgs)
    spec-msgs)))



(defthm imp-spec-channel-msgs-equivalent-p-of-remove-message-from-channel-left
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p
     (channel-state src dst imp-channels)
     (channel-state src dst spec-channels))
    ;; The channel being removed from is nonempty.
    (consp
     (channel-state rm-src rm-dst imp-channels))

    ;; The removed message is non-normal.
    (not
     (equal
      (msg-type
       (get-msg-from-channel rm-src rm-dst imp-channels))
      :normal)))

   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (remove-message-from-channel rm-src rm-dst imp-channels))
    (channel-state src dst spec-channels)))

  :hints
  (("Goal"
    :cases ((and (equal src rm-src)
                 (equal dst rm-dst))))))


(defthm incoming-channels-equivalent-for-proc-p-of-remove-message-from-channel-left
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)

    (consp
     (channel-state rm-src rm-dst imp-channels))

    (not
     (equal
      (msg-type
       (get-msg-from-channel rm-src rm-dst imp-channels))
      :normal)))

   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (remove-message-from-channel rm-src rm-dst imp-channels)
    spec-channels)))


(defthm imp-spec-channels-equivalent-p-aux-of-remove-message-from-channel-left
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)

    (consp
     (channel-state rm-src rm-dst imp-channels))

    (not
     (equal
      (msg-type
       (get-msg-from-channel rm-src rm-dst imp-channels))
      :normal)))

   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (remove-message-from-channel rm-src rm-dst imp-channels)
    spec-channels))

  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    :in-theory
    (disable
     remove-message-from-channel
     incoming-channels-equivalent-for-proc-p))))

  
(defthm imp-spec-channels-equivalent-p-aux-of-channels-handle-non-first-marker-msg-left
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids
     imp-procs
     (channels imp-st)
     spec-channels)
    ;; The channel j -> i has a head message.
    (consp
     (channel-state j i (channels imp-st)))
    ;; The consumed message is that head message.
    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    ;; The head message is a marker, hence non-normal.
    (equal
     (msg-type msg)
     :marker))

   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (channels
     (handle-non-first-marker-msg imp-st i j msg))
    spec-channels))

  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel
     remove-message-from-channel) )))




(defthm proc-equivalent-p-of-update-proc-for-first-marker-msg-left
  (implies
   (proc-equivalent-p imp-p spec-p)
   (proc-equivalent-p
    (update-proc-for-first-marker-msg imp-p sid j)
    spec-p)))


(defthm procs-equivalent-p-of-set-first-marker-proc-left
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids
    (s i
       (update-proc-for-first-marker-msg
        (g i imp-procs)
        sid
        j)
       imp-procs)
    spec-procs))
  :hints
  (("Goal"
    :induct (procs-equivalent-p ids imp-procs spec-procs)
    :in-theory
    (disable update-proc-for-first-marker-msg))
   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))



(defthm procs-equivalent-p-of-handle-first-marker-msg-left
  (implies
   (and
    (procs-equivalent-p ids
                        (procs imp-st)
                        (procs spec-st))
    (memberp i ids))
   (procs-equivalent-p
    ids
    (procs
     (handle-first-marker-msg imp-st i j msg))
    (procs spec-st)))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-first-marker-msg))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; First-marker channel equivalence preservation
;;
;; handle-first-marker-msg does two channel operations:
;;   1. remove the marker from j -> i
;;   2. forward the same marker msg on i's outgoing channels
;;
;; Both preserve imp/spec channel equivalence because marker messages are
;; non-normal and are ignored by imp-spec-channel-msgs-equivalent-p.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Sending any non-normal message on implementation channels only
;;    preserves one channel-message equivalence.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-channel-msgs-equivalent-p-of-snoc-non-normal-left
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
    (not (equal (msg-type msg) :normal)))
   (imp-spec-channel-msgs-equivalent-p
    (snoc imp-msgs msg)
    spec-msgs)))


(defthm imp-spec-channel-msgs-equivalent-p-of-send-non-normal-msg-left
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p
     (channel-state src dst imp-channels)
     (channel-state src dst spec-channels))
    (not (equal (msg-type msg) :normal)))
   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (send-msg-all-outgoing-channels
      msg
      sender
      nbrs
      imp-channels))
    (channel-state src dst spec-channels))))

(defthm incoming-channels-equivalent-for-proc-p-of-send-non-normal-msg-left
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)
    (not (equal (msg-type msg) :normal)))
   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (send-msg-all-outgoing-channels
     msg
     sender
     nbrs
     imp-channels)
    spec-channels)))


(defthm imp-spec-channels-equivalent-p-aux-of-send-non-normal-msg-left
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    (not (equal (msg-type msg) :normal)))
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (send-msg-all-outgoing-channels
     msg
     sender
     nbrs
     imp-channels)
    spec-channels)))



(defthm nbrs-from-of-install-snapshot-entry
  (equal
   (nbrs-from
    (install-snapshot-entry sid entry p))
   (nbrs-from p)))


(defthm nbrs-from-of-update-proc-for-first-marker-msg
  (equal
   (nbrs-from
    (update-proc-for-first-marker-msg p sid j))
   (nbrs-from p)))


(defthm nbrs-from-of-procs-handle-first-marker-msg
  (equal
   (nbrs-from
    (g k
       (procs
        (handle-first-marker-msg st i j msg))))
   (nbrs-from
    (g k
       (procs st))))
  :hints
  (("Goal"
    :cases ((equal k i)))))


(defthm imp-spec-channels-equivalent-p-aux-of-handle-first-marker-msg-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs
     (handle-first-marker-msg st i j msg))
    imp-channels
    spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs st)
    imp-channels
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids
     (procs st)
     imp-channels
     spec-channels)
    :in-theory
    (disable update-proc-for-first-marker-msg))))


(defthm channels-of-handle-first-marker-msg
  (equal
   (channels
    (handle-first-marker-msg st i j msg))
   (send-msg-all-outgoing-channels
    msg
    i
    (nbrs-to (g i (procs st)))
    (remove-message-from-channel j i (channels st)))))



(defthm imp-spec-equivalent-p-of-step-rcv-marker
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)

    (memberp i (proc-ids imp-st))
    (memberp j (proc-ids imp-st))

    ;; The implementation receive consumes a marker.
    (consp (channel-state j i (channels imp-st)))
    (equal
     (msg-type
      (get-msg-from-channel j i (channels imp-st)))
     :marker))
   (imp-spec-equivalent-p
    (step-rcv imp-st i j)
    spec-st))
  :hints
  (("Goal"
    :in-theory
    ( disable
      good-state-p
      good-spec-state-p
      good-proc-p
      good-spec-proc-p
      handle-first-marker-msg
      handle-non-first-marker-msg
      send-msg-all-outgoing-channels
      remove-message-from-channel
      create-marker-message
      get-msg-from-channel
      procs-equivalent-p
      imp-spec-channels-equivalent-p-aux))))
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm imp-spec-equivalent-p-of-step-when-legal-inputp
;;   (implies
;;    (and
;;     (good-state-p imp-st)
;;     (good-spec-state-p spec-st)
;;     (imp-spec-equivalent-p imp-st spec-st)
;;     (legal-inputp imp-st input))
;;    (imp-spec-equivalent-p
;;     (system-step imp-st input)
;;     (spec-step spec-st input)))
;;   :hints
;;   (("Goal"
;;     :cases
;;     ((equal (ttype input) :receive)
;;      (equal (ttype input) :normal)
;;      (equal (ttype input) :start-checkpoint)
;;      (equal (ttype input) :crash)
;;      (equal (ttype input) :recover)
;;      (equal (ttype input) :nop))
;;     :in-theory
;;     (e/d
;;      (legal-inputp
;;       system-step
;;       spec-step)

;;      (good-state-p
;;       good-spec-state-p
;;       imp-spec-equivalent-p
;;       step-rcv
;;       step-normal
;;       step-checkpoint
;;       step-crash
;;       step-recover
;;       spec-step-rcv
;;       spec-step-normal)))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; First-recovery-message channel equivalence preservation
;;
;; handle-first-recovery-msg does two channel operations:
;;   1. remove the recovery message from j -> i
;;   2. forward the same recovery message on i's outgoing channels
;;
;; Recovery messages are non-normal, so both operations preserve the
;; normal-message projection used by imp/spec channel equivalence.
;;
;; We prove ONLY channel equivalence here.  We do not prove full
;; imp-spec-equivalent-p, because first recovery may change implementation
;; local-state / proc-status / waiting-recovery-from.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. handle-first-recovery-msg preserves proc-ids
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm proc-ids-of-handle-first-recovery-msg
  (equal
   (proc-ids
    (handle-first-recovery-msg st i j msg))
   (proc-ids st)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. handle-first-recovery-msg may update process i, but it does not change
;;    nbrs-from for any process.  Channel equivalence only reads nbrs-from
;;    from the implementation process table.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm nbrs-from-of-procs-handle-first-recovery-msg
  (equal
   (nbrs-from
    (g k
       (procs
        (handle-first-recovery-msg st i j msg))))
   (nbrs-from
    (g k
       (procs st))))
  :hints
  (("Goal"
    :cases ((equal k i))
    :in-theory
    (disable
     replay-channel-snapshots
     replay-msgs-on-channel
     remove-from-list))))


(defthm imp-spec-channels-equivalent-p-aux-of-handle-first-recovery-msg-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs
     (handle-first-recovery-msg st i j msg))
    imp-channels
    spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs st)
    imp-channels
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids
     (procs st)
     imp-channels
     spec-channels)
    :in-theory
    (disable
     handle-first-recovery-msg
     replay-channel-snapshots
     replay-msgs-on-channel))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Channel part of handle-first-recovery-msg
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm channels-of-handle-first-recovery-msg
  (equal
   (channels
    (handle-first-recovery-msg st i j msg))
   (send-msg-all-outgoing-channels
    msg
    i
    (nbrs-to (g i (procs st)))
    (remove-message-from-channel j i (channels st)))))
    

(defthm imp-spec-channels-equivalent-p-aux-of-channels-handle-first-recovery-msg-left
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids
     imp-procs
     (channels imp-st)
     spec-channels)

    ;; The channel j -> i has a head message.
    (consp
     (channel-state j i (channels imp-st)))

    ;; The consumed message is that head message.
    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    ;; The head message is a recovery message, hence non-normal.
    (equal
     (msg-type msg)
     :recovery))

   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (channels
     (handle-first-recovery-msg imp-st i j msg))
    spec-channels))

  :hints
  (("Goal"
    :in-theory
    (disable
     handle-first-recovery-msg
     send-msg-all-outgoing-channels
     remove-message-from-channel
     get-msg-from-channel))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Main handler theorem:
;;    first recovery handling preserves only channel equivalence.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-channels-equivalent-p-of-handle-first-recovery-msg
  (implies
   (and
    (imp-spec-channels-equivalent-p
     ids
     imp-st
     spec-st)

    ;; The channel j -> i has a recovery message at the head.
    (consp
     (channel-state j i (channels imp-st)))

    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    (equal
     (msg-type msg)
     :recovery))

   (imp-spec-channels-equivalent-p
    ids
    (handle-first-recovery-msg imp-st i j msg)
    spec-st))

  :hints
  (("Goal"
    :in-theory
    (disable
     handle-first-recovery-msg
     send-msg-all-outgoing-channels
     remove-message-from-channel
     get-msg-from-channel
     imp-spec-channels-equivalent-p-aux))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Optional receive-level theorem:
;;    if step-rcv dispatches to the first-recovery case, then the receive
;;    step preserves only channel equivalence.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-channels-equivalent-p-of-step-rcv-first-recovery
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)

    (memberp i (proc-ids imp-st))
    (memberp j (proc-ids imp-st))

    ;; First recovery message means receiver i is still normal.
    (equal
     (proc-status (g i (procs imp-st)))
     :normal)

    ;; The implementation receive consumes a recovery message.
    (consp
     (channel-state j i (channels imp-st)))

    (equal
     (msg-type
      (get-msg-from-channel j i (channels imp-st)))
     :recovery))

   (imp-spec-channels-equivalent-p
    (proc-ids imp-st)
    (step-rcv imp-st i j)
    spec-st))

  :hints
  (("Goal"
    :in-theory
    (disable
     good-state-p
     good-spec-state-p
     good-proc-p
     good-spec-proc-p
    ; step-rcv
    ; handle-recovery-msg
     handle-first-recovery-msg
     send-msg-all-outgoing-channels
     remove-message-from-channel
     get-msg-from-channel
     replay-channel-snapshots
     replay-msgs-on-channel
     imp-spec-channels-equivalent-p-aux))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Non-first-recovery-message full equivalence preservation
;;
;; Non-first recovery uses the helper:
;;
;;   update-proc-for-non-first-recovery-msg
;;
;; This helper only changes recovery bookkeeping:
;;   :proc-status
;;   :waiting-recovery-from
;;
;; It does not change:
;;   :local-state
;;   :nbrs-to
;;   :nbrs-from
;;
;; So process equivalence is preserved.
;;
;; The handler also removes one recovery message from channel j -> i.
;; Since recovery messages are non-normal, removing it preserves the
;; normal-message projection used by imp/spec channel equivalence.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Helper preserves visible process equivalence
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm proc-equivalent-p-of-update-proc-for-non-first-recovery-msg-left
  (implies
   (proc-equivalent-p imp-p spec-p)
   (proc-equivalent-p
    (update-proc-for-non-first-recovery-msg imp-p j)
    spec-p))
  :hints
  (("Goal"
    :in-theory
    (disable remove-from-list))))


(defthm procs-equivalent-p-of-set-non-first-recovery-proc-left
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids
    (s i
       (update-proc-for-non-first-recovery-msg
        (g i imp-procs)
        j)
       imp-procs)
    spec-procs))
  :hints
  (("Goal"
    :induct (procs-equivalent-p ids imp-procs spec-procs)
    :in-theory
    (disable
     update-proc-for-non-first-recovery-msg
     proc-equivalent-p))
   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))


(defthm procs-equivalent-p-of-handle-non-first-recovery-msg-left
  (implies
   (and
    (procs-equivalent-p ids
                        (procs imp-st)
                        (procs spec-st))
    (memberp i ids))
   (procs-equivalent-p
    ids
    (procs
     (handle-non-first-recovery-msg imp-st i j msg))
    (procs spec-st)))
  :hints
  (("Goal"
    :in-theory
    (disable
     update-proc-for-non-first-recovery-msg
     proc-equivalent-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Helper preserves nbrs-from.
;;
;; Channel equivalence only reads nbrs-from from implementation procs,
;; so changing recovery bookkeeping cannot affect which channels are checked.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm nbrs-from-of-update-proc-for-non-first-recovery-msg
  (equal
   (nbrs-from
    (update-proc-for-non-first-recovery-msg p j))
   (nbrs-from p))
  :hints
  (("Goal"
    :in-theory
    (disable remove-from-list))))


(defthm nbrs-from-of-procs-handle-non-first-recovery-msg
  (equal
   (nbrs-from
    (g k
       (procs
        (handle-non-first-recovery-msg st i j msg))))
   (nbrs-from
    (g k
       (procs st))))
  :hints
  (("Goal"
    :cases ((equal k i))
    :in-theory
    (disable
     update-proc-for-non-first-recovery-msg
     remove-from-list))))


(defthm imp-spec-channels-equivalent-p-aux-of-handle-non-first-recovery-msg-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs
     (handle-non-first-recovery-msg st i j msg))
    imp-channels
    spec-channels)

   (imp-spec-channels-equivalent-p-aux
    ids
    (procs st)
    imp-channels
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids
     (procs st)
     imp-channels
     spec-channels)
    :in-theory
    (disable
     handle-non-first-recovery-msg
     update-proc-for-non-first-recovery-msg
     remove-from-list))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3. Handler preserves proc-ids
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm proc-ids-of-handle-non-first-recovery-msg
  (equal
   (proc-ids
    (handle-non-first-recovery-msg st i j msg))
   (proc-ids st)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Channel part of handle-non-first-recovery-msg
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm channels-of-handle-non-first-recovery-msg
  (equal
   (channels
    (handle-non-first-recovery-msg st i j msg))
   (remove-message-from-channel j i (channels st))))


(defthm imp-spec-channels-equivalent-p-aux-of-channels-handle-non-first-recovery-msg-left
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids
     imp-procs
     (channels imp-st)
     spec-channels)

    ;; The channel j -> i has a head message.
    (consp
     (channel-state j i (channels imp-st)))

    ;; The consumed message is that head message.
    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    ;; The head message is recovery, hence non-normal.
    (equal
     (msg-type msg)
     :recovery))

   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (channels
     (handle-non-first-recovery-msg imp-st i j msg))
    spec-channels))

  :hints
  (("Goal"
    :in-theory
    (disable
     handle-non-first-recovery-msg
     get-msg-from-channel
     remove-message-from-channel))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Main handler theorem:
;;    non-first recovery preserves FULL imp/spec equivalence.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-equivalent-p-of-handle-non-first-recovery-msg
  (implies
   (and
    (imp-spec-equivalent-p imp-st spec-st)

    ;; Needed because only process i is updated.
    (memberp i (proc-ids imp-st))

    ;; The channel j -> i has a recovery message at the head.
    (consp
     (channel-state j i (channels imp-st)))

    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    (equal
     (msg-type msg)
     :recovery))

   (imp-spec-equivalent-p
    (handle-non-first-recovery-msg imp-st i j msg)
    spec-st))

  :hints
  (("Goal"
    :in-theory
    (disable
     handle-non-first-recovery-msg
     update-proc-for-non-first-recovery-msg
     get-msg-from-channel
     remove-message-from-channel
     imp-spec-channels-equivalent-p-aux
     procs-equivalent-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 6. Receive-level theorem:
;;    step-rcv dispatches to non-first recovery when the received message
;;    is :recovery and receiver i is already not :normal.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm imp-spec-equivalent-p-of-step-rcv-non-first-recovery
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)

    (memberp i (proc-ids imp-st))
    (memberp j (proc-ids imp-st))

    ;; Non-first recovery means receiver i is already not normal.
    (not
     (equal
      (proc-status (g i (procs imp-st)))
      :normal))

    ;; The implementation receive consumes a recovery message.
    (consp
     (channel-state j i (channels imp-st)))

    (equal
     (msg-type
      (get-msg-from-channel j i (channels imp-st)))
     :recovery))

   (imp-spec-equivalent-p
    (step-rcv imp-st i j)
    spec-st))

  :hints
  (("Goal"
    :in-theory
    (disable
     good-state-p
     good-spec-state-p
     good-proc-p
     good-spec-proc-p
     handle-non-first-recovery-msg
     update-proc-for-non-first-recovery-msg
     get-msg-from-channel
     remove-message-from-channel
     remove-from-list
     imp-spec-channels-equivalent-p-aux
     procs-equivalent-p))))








(defthm proc-ids-of-handle-normal-msg-core
  (equal
   (proc-ids
    (handle-normal-msg-core st i j msg))
   (proc-ids st)))





(defthm proc-equivalent-p-of-update-proc-for-normal-msg-core-left-right
  (implies
   (proc-equivalent-p imp-p spec-p)
   (proc-equivalent-p
    (update-proc-for-normal-msg-core imp-p j msg)
    (update spec-p
            :local-state
            (update-local-state-rcv
             (local-state spec-p)
             msg
             j))))
  :hints
  (("Goal"
    :in-theory
    (disable record-msg-in-snapshots))))


(defthm procs-equivalent-p-of-set-normal-msg-core-left-right
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids
    (s i
       (update-proc-for-normal-msg-core
        (g i imp-procs)
        j
        msg)
       imp-procs)
    (s i
       (update (g i spec-procs)
               :local-state
               (update-local-state-rcv
                (local-state (g i spec-procs))
                msg
                j))
       spec-procs)))
  :hints
  (("Goal"
    :induct (procs-equivalent-p ids imp-procs spec-procs)
    :in-theory
    (disable
     update-proc-for-normal-msg-core
     LOCAL-STATE-OF-SPEC-PROC-WHEN-PROCS-EQUIVALENT-P
     proc-equivalent-p))
   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))




(defthm procs-equivalent-p-of-handle-normal-msg-core-and-spec-step-rcv
  (implies
   (and
    (procs-equivalent-p ids
                        (procs imp-st)
                        (procs spec-st))
    (memberp i ids)

    ;; The spec receive must use the same normal application message.
    (equal
     msg
     (get-msg-from-channel j i (channels spec-st))))

   (procs-equivalent-p
    ids
    (procs
     (handle-normal-msg-core imp-st i j msg))
    (procs
     (spec-step-rcv spec-st i j))))

  :hints
  (("Goal"
    :in-theory
    (disable
      LOCAL-STATE-OF-SPEC-PROC-WHEN-PROCS-EQUIVALENT-P
     update-proc-for-normal-msg-core
     procs-equivalent-p))))

(defthm proc-ids-of-spec-step-rcv
  (equal
   (proc-ids
    (spec-step-rcv st i j))
   (proc-ids st)))


(defthm imp-spec-channel-msgs-equivalent-p-when-incoming-channels-equivalent-for-proc-p
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)
    (memberp src srcs))
   (imp-spec-channel-msgs-equivalent-p
    (channel-state src dst imp-channels)
    (channel-state src dst spec-channels))))


(defthm imp-spec-channel-msgs-equivalent-p-when-imp-spec-channels-equivalent-p-aux
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    (memberp dst ids)
    (memberp src (nbrs-from (g dst imp-procs))))
   (imp-spec-channel-msgs-equivalent-p
    (channel-state src dst imp-channels)
    (channel-state src dst spec-channels))))

(defthm first-spec-msg-when-left-head-normal-and-msgs-equivalent
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
    (consp imp-msgs)
    (equal (msg-type (first imp-msgs)) :normal))
   (equal (first spec-msgs)
          (first imp-msgs))))



(defthm get-msg-from-channel-equal-when-imp-spec-channels-equivalent-p-aux
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids
     imp-procs
     imp-channels
     spec-channels)

    ;; dst must be one of the destinations checked by ids.
    (memberp dst ids)

    ;; src -> dst must be one of dst's checked incoming channels.
    (memberp src
             (nbrs-from
              (g dst imp-procs)))

    ;; Implementation channel has a head message.
    (consp
     (channel-state src dst imp-channels))

    ;; Implementation head message is visible to spec.
    (equal
     (msg-type
      (get-msg-from-channel src dst imp-channels))
     :normal))

   (equal
    (get-msg-from-channel src dst spec-channels)
    (get-msg-from-channel src dst imp-channels)))

  :hints
  (("Goal"
    :use
    ((:instance
      imp-spec-channel-msgs-equivalent-p-when-imp-spec-channels-equivalent-p-aux
      (ids ids)
      (imp-procs imp-procs)
      (imp-channels imp-channels)
      (spec-channels spec-channels)
      (src src)
      (dst dst))

     (:instance
      first-spec-msg-when-left-head-normal-and-msgs-equivalent
      (imp-msgs
       (channel-state src dst imp-channels))
      (spec-msgs
       (channel-state src dst spec-channels))))

    :in-theory
    (e/d
     (get-msg-from-channel)
     (imp-spec-channel-msgs-equivalent-p
      imp-spec-channel-msgs-equivalent-p-when-imp-spec-channels-equivalent-p-aux
      first-spec-msg-when-left-head-normal-and-msgs-equivalent
      imp-spec-channels-equivalent-p-aux
      incoming-channels-equivalent-for-proc-p)))))


(defthm nbrs-from-of-procs-handle-normal-msg-core
  (equal
   (nbrs-from
    (g k
       (procs
        (handle-normal-msg-core st i j msg))))
   (nbrs-from
    (g k
       (procs st))))
  :hints
  (("Goal"
    :cases ((equal k i))
    :in-theory
    (disable
     update-proc-for-normal-msg-core
     record-msg-in-snapshots
     remove-message-from-channel))))



(defthm imp-spec-channels-equivalent-p-aux-of-handle-normal-msg-core-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs
     (handle-normal-msg-core st i j msg))
    imp-channels
    spec-channels)

   (imp-spec-channels-equivalent-p-aux
    ids
    (procs st)
    imp-channels
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids
     (procs st)
     imp-channels
     spec-channels)
    :in-theory
    (disable
     handle-normal-msg-core
     update-proc-for-normal-msg-core
     record-msg-in-snapshots
     remove-message-from-channel))))




(defthm imp-spec-channel-msgs-equivalent-p-of-cdr-both-when-left-head-normal
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
    (consp imp-msgs)
    (equal (msg-type (first imp-msgs)) :normal))
   (imp-spec-channel-msgs-equivalent-p
    (rest imp-msgs)
    (rest spec-msgs))))

(defthm imp-spec-channel-msgs-equivalent-p-of-remove-message-from-channel-both
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p
     (channel-state src dst imp-channels)
     (channel-state src dst spec-channels))

    ;; The removed implementation channel is nonempty.
    (consp
     (channel-state rm-src rm-dst imp-channels))

    ;; The removed implementation head is normal.
    (equal
     (msg-type
      (get-msg-from-channel rm-src rm-dst imp-channels))
     :normal))

   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (remove-message-from-channel rm-src rm-dst imp-channels))
    (channel-state
     src dst
     (remove-message-from-channel rm-src rm-dst spec-channels)))))


(defthm incoming-channels-equivalent-for-proc-p-of-remove-message-from-channel-both
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)

    (consp
     (channel-state rm-src rm-dst imp-channels))

    (equal
     (msg-type
      (get-msg-from-channel rm-src rm-dst imp-channels))
     :normal))

   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (remove-message-from-channel rm-src rm-dst imp-channels)
    (remove-message-from-channel rm-src rm-dst spec-channels))))



(defthm imp-spec-channels-equivalent-p-aux-of-remove-message-from-channel-both
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)

    (consp
     (channel-state rm-src rm-dst imp-channels))

    (equal
     (msg-type
      (get-msg-from-channel rm-src rm-dst imp-channels))
     :normal))

   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (remove-message-from-channel rm-src rm-dst imp-channels)
    (remove-message-from-channel rm-src rm-dst spec-channels)))

  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    :in-theory
    (disable
     remove-message-from-channel
     get-msg-from-channel
     incoming-channels-equivalent-for-proc-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Channel fields of normal receive handlers.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm channels-of-handle-normal-msg-core
  (equal
   (channels
    (handle-normal-msg-core st i j msg))
   (remove-message-from-channel j i (channels st))))


(defthm channels-of-spec-step-rcv
  (equal
   (channels
    (spec-step-rcv st i j))
   (remove-message-from-channel j i (channels st))))

(defthm imp-spec-equivalent-p-of-handle-normal-msg-core
  (implies
   (and
    (imp-spec-equivalent-p imp-st spec-st)

    ;; Process i must be checked by process equivalence.
    (memberp i (proc-ids imp-st))

    ;; j -> i must be a checked incoming channel, so the spec receives
    ;; the same normal message as the implementation.
    (memberp j (nbrs-from (g i (procs imp-st))))

    ;; Implementation consumes msg from channel j -> i.
    (consp
     (channel-state j i (channels imp-st)))

    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    (equal
     (msg-type msg)
     :normal))

   (imp-spec-equivalent-p
    (handle-normal-msg-core imp-st i j msg)
    (spec-step-rcv spec-st i j)))

  :hints
  (("Goal"
    :in-theory
    (disable
     handle-normal-msg-core
     spec-step-rcv
     LOCAL-STATE-OF-SPEC-PROC-WHEN-PROCS-EQUIVALENT-P
     update-proc-for-normal-msg-core
     get-msg-from-channel
     remove-message-from-channel
     imp-spec-channels-equivalent-p-aux
     ;procs-equivalent-p
     ))))
