;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Non-first recovery-message preservation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This section handles the case where process i receives a recovery message
;; while it is already in recovery mode.  The handler only removes sender j
;; from i's waiting-recovery-from list.  If that list becomes empty, i returns
;; to :normal; otherwise, i stays :recovering.

;start support: non-first-recovery-process-field-preservation
;; Field-level facts about update-proc-for-non-first-recovery-msg.
;; These lemmas say exactly which fields are unchanged and which field is
;; changed.  They keep ACL2 from opening the updater repeatedly in later proofs.

(defthm nbrs-from-of-update-proc-for-non-first-recovery-msg
  (equal (g :nbrs-from
            (update-proc-for-non-first-recovery-msg p j))
         (g :nbrs-from p)))

(defthm nbrs-to-of-update-proc-for-non-first-recovery-msg
  (equal (g :nbrs-to
            (update-proc-for-non-first-recovery-msg p j))
         (g :nbrs-to p)))

(defthm waiting-recovery-from-of-update-proc-for-non-first-recovery-msg
  (equal (g :waiting-recovery-from
            (update-proc-for-non-first-recovery-msg p j))
         (remove-from-list (g :waiting-recovery-from p) j)))

(defthm snapshot-ids-of-update-proc-for-non-first-recovery-msg
  (equal (g :snapshot-ids
            (update-proc-for-non-first-recovery-msg p j))
         (g :snapshot-ids p)))

(defthm counter-of-update-proc-for-non-first-recovery-msg
  (equal (g :counter
            (update-proc-for-non-first-recovery-msg p j))
         (g :counter p)))

(defthm local-state-of-update-proc-for-non-first-recovery-msg
  (equal (g :local-state
            (update-proc-for-non-first-recovery-msg p j))
         (g :local-state p)))

;; The only status change is controlled by the remaining wait list.
;; If all expected recovery messages have arrived, the process becomes normal;
;; otherwise it remains recovering.
(defthm proc-status-of-update-proc-for-non-first-recovery-msg
  (equal (g :proc-status
            (update-proc-for-non-first-recovery-msg p j))
         (if (endp (remove-from-list (g :waiting-recovery-from p) j))
             :normal
             :recovering)))

;; Removing an element from a list cannot introduce a new element outside ys.
;; This is used to preserve:
;;   waiting-recovery-from subset nbrs-from.
(defthm subset-of-remove-from-list-when-subset
  (implies
   (subset xs ys)
   (subset (remove-from-list xs a)
           ys)))

;end support: non-first-recovery-process-field-preservation


;start support: non-first-recovery-process-wellformedness
;; Lift the field-level facts to the full process invariant.
;; Since snapshot ids, snapshots, local state, counter, and neighbors are
;; unchanged, the main thing to preserve is that the shortened wait list is
;; still a subset of nbrs-from.

(defthm good-snapshots-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (good-snapshots-p snapshot-ids p nbrs-from ids)
   (good-snapshots-p
    snapshot-ids
    (update-proc-for-non-first-recovery-msg p j)
    nbrs-from
    ids)))

(defthm good-proc-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (good-proc-p p ids)
   (good-proc-p
    (update-proc-for-non-first-recovery-msg p j)
    ids))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-recovery-msg))))

;end support: non-first-recovery-process-wellformedness


;start support: non-first-recovery-updated-procs-field-compatibility
;; Facts about reading fields from the process table after updating one process.
;; These are needed because channel well-formedness depends on process metadata,
;; especially outgoing neighbors and known snapshot ids.

(defthm nbrs-to-of-g-of-s-update-proc-for-non-first-recovery-msg
  (equal
   (g :nbrs-to
      (g x
         (s k
            (update-proc-for-non-first-recovery-msg
             (g k procs)
             j)
            procs)))
   (g :nbrs-to
      (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))

(defthm snapshot-ids-of-g-of-s-update-proc-for-non-first-recovery-msg
  (equal
   (g :snapshot-ids
      (g x
         (s k
            (update-proc-for-non-first-recovery-msg
             (g k procs)
             j)
            procs)))
   (g :snapshot-ids
      (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))

;end support: non-first-recovery-updated-procs-field-compatibility


;start support: non-first-recovery-message-goodness-preservation
;; Updating a process for a non-first recovery message does not change any
;; process's snapshot-id list.  Therefore, any message that was good before the
;; update is still good after the update.

(defthm some-proc-has-snapshot-id-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (some-proc-has-snapshot-id-p sid ids procs)
   (some-proc-has-snapshot-id-p
    sid
    ids
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-recovery-msg))))

(defthm good-msg-list-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (good-msg-list-p msgs ids procs)
   (good-msg-list-p
    msgs
    ids
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-recovery-msg))))

;end support: non-first-recovery-message-goodness-preservation


;start support: non-first-recovery-channel-table-preservation
;; Lift message-goodness preservation to channel rows and then to the whole
;; channel table.  The channel contents are not changed by these lemmas; only
;; the process table used to interpret channel/message well-formedness changes.

(defthm good-channel-row-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (good-channel-row-p src dsts channels ids procs)
   (good-channel-row-p
    src
    dsts
    channels
    ids
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :induct (good-channel-row-p src dsts channels ids procs)
    :in-theory
    (disable update-proc-for-non-first-recovery-msg))))

(defthm good-channels-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (good-channels-p srcs dsts channels ids procs)
   (good-channels-p
    srcs
    dsts
    channels
    ids
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :induct (good-channels-p srcs dsts channels ids procs)
    :in-theory (disable update-proc-for-non-first-recovery-msg))))

;end support: non-first-recovery-channel-table-preservation


;start target: good-state-p-of-handle-non-first-recovery-msg
;; Target theorem for the non-first recovery-message handler.
;; Assumptions identify a valid channel j -> i, say that msg is the head of
;; that channel, and require that i is not :normal.  Therefore this handler uses
;; the non-first recovery case rather than the first recovery case.
;;
;; Proof idea:
;; 1. remove-message-from-channel preserves good-channels-p;
;; 2. update-proc-for-non-first-recovery-msg preserves good-proc-p for i;
;; 3. the same update does not invalidate channel/message well-formedness.

(defthm good-state-p-of-handle-non-first-recovery-msg
  (implies
   (and (good-state-p st)

        ;; Valid receiver and sender.
        (memberp i (proc-ids st))
        (memberp j (proc-ids st))
        (memberp j (nbrs-from (g i (procs st))))

        ;; msg is the first message on channel j -> i.
        (equal msg
               (get-msg-from-channel j i (channels st)))

        ;; This is really a recovery message.
        (equal (msg-type msg) :recovery)

        ;; Non-first recovery-message case:
        ;; receiver is already recovering or crashed, but not normal.
        (not (equal (proc-status (g i (procs st))) :normal)))
   (good-state-p
    (handle-non-first-recovery-msg st i j msg)))
  :hints
  (("Goal"
    :in-theory (disable good-proc-p
                        remove-message-from-channel
                        get-msg-from-channel
                        update-proc-for-non-first-recovery-msg))))

;end target: good-state-p-of-handle-non-first-recovery-msg


;start target: good-state-p-of-handle-recovery-msg
;; Dispatcher theorem for handle-recovery-msg.
;; The handler splits into two cases based on receiver i's current status:
;;
;;   1. If i is :normal, this is the first recovery message for i.
;;      Then the sid carried by msg must already be in i's snapshot-ids.
;;
;;   2. If i is not :normal, this is the non-first recovery case.
;;      The theorem above handles that branch.
;;
;; The extra implication in the hypotheses is exactly the invariant needed for
;; the first branch:
;;   Any recovery message on channel j -> i must carry a sid that receiver i
;;   already knows when i is still normal.

(defthm good-state-p-of-handle-recovery-msg
  (implies
   (and (good-state-p st)

        ;; Valid receiver and sender.
        (memberp i (proc-ids st))
        (memberp j (proc-ids st))
        (memberp j (nbrs-from (g i (procs st))))

        ;; msg is the first message on channel j -> i.
        (equal msg
               (get-msg-from-channel j i (channels st)))

        ;; This is really a recovery message.
        (equal (msg-type msg) :recovery)

        ;; First-recovery side condition:
        ;; if i is still normal, then the recovery sid must already be known
        ;; by i.  Non-first recovery does not need this extra assumption.
        (implies
         (equal (proc-status (g i (procs st))) :normal)
         (memberp (sid msg)
                  (snapshot-ids (g i (procs st))))))
   (good-state-p
    (handle-recovery-msg st i j msg)))
  :hints
  (("Goal"
    :in-theory
    (disable good-state-p
             good-proc-p
             handle-first-recovery-msg
             handle-non-first-recovery-msg
             remove-message-from-channel
             get-msg-from-channel
             update-proc-for-first-recovery-msg
             update-proc-for-non-first-recovery-msg))))

;end target: good-state-p-of-handle-recovery-msg
