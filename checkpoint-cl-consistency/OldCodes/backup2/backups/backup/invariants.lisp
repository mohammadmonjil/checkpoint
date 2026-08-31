(include-book "model")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: Good State Predicate 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This section defines structural well-formedness predicates for the
;; implementation state.
;;
;; The goal of good-state-p is not to encode the full protocol
;; correctness argument, but to ensure that the system state has the
;; expected shape required by the step functions and later proofs.
;;
;; In particular, these predicates check that:
;;
;;   - the list of process ids is well formed,
;;   - each process record contains valid protocol fields,
;;   - process status values are legal,
;;   - snapshot ids and snapshot entries are well formed,
;;   - waiting lists refer only to valid neighbor processes,
;;   - every live channel contains a proper list of valid messages, and
;;   - every saved channel snapshot contains only normal messages.
;;
;; Thus, good-state-p serves as the main structural invariant used for
;; preservation lemmas, such as showing that each protocol step maps
;; good states to good states.
;; ------------------------------------------------------------------


;; ------------------------------------------------------------------
;; Basic status and snapshot-id predicates
;;
;; These predicates define the legal values for process status,
;; snapshot status, and snapshot ids.
;;
;; Snapshot ids are either:
;;   - :init, for the initial installed snapshot, or
;;   - a pair (pid counter), where pid is a valid process id and
;;     counter is a natural number.
;; ------------------------------------------------------------------

(defun good-proc-status-p (x)
  (or (equal x :normal)
      (equal x :crashed)
      (equal x :recovering)))

(defun good-snapshot-status-p (x)
  (or (equal x :checkpointing)
      (equal x :done)))

(defun good-snapshot-id-p (sid ids)
  (or (equal sid :init)
      (and (consp sid)
           (consp (cdr sid))
           (endp (cddr sid))
           (memberp (car sid) ids)
           (natp (cadr sid)))))


;; ------------------------------------------------------------------
;; Message predicates
;;
;; Live channels may contain three kinds of messages:
;;   - :normal
;;   - :marker
;;   - :recovery
;;
;; For marker and recovery messages, the sid carried in the message
;; must already be known by at least one process in the system.
;; This matches the protocol behavior: a process installs a snapshot
;; id before sending marker or recovery messages carrying that id.
;; ------------------------------------------------------------------


(defun some-proc-has-snapshot-id-p (sid ids procs)
  (if (endp ids)
      nil
    (let* ((i (first ids))
           (p (g i procs)))
      (or (memberp sid (snapshot-ids p))
          (some-proc-has-snapshot-id-p sid (rest ids) procs)))))

(defun good-msg-p (msg ids procs)
  (let ((tp (msg-type msg)))
    (cond ((equal tp :normal)
           t)
          ((equal tp :marker)
           (some-proc-has-snapshot-id-p (sid msg) ids procs))
          ((equal tp :recovery)
           (some-proc-has-snapshot-id-p (sid msg) ids procs))
          (t nil))))

(defun good-msg-list-p (msgs ids procs)
  (if (endp msgs)
      t
    (and (good-msg-p (first msgs) ids procs)
         (good-msg-list-p (rest msgs) ids procs))))



(defthm good-msg-p-of-create-marker-message
  (implies (some-proc-has-snapshot-id-p sid ids procs)
           (good-msg-p (create-marker-message local-state sid)
                       ids
                       procs)))

(defthm good-msg-p-of-create-recovery-message
  (implies (some-proc-has-snapshot-id-p sid ids procs)
           (good-msg-p (create-recovery-message local-state sid)
                       ids
                       procs)))

;; ------------------------------------------------------------------
;; Saved-channel-snapshot message predicates
;;
;; A snapshot entry stores channel snapshots that represent recorded
;; in-transit application messages. These should contain only normal
;; messages, because marker and recovery messages are protocol-control
;; traffic and are never recorded into snapshot channel histories.
;; ------------------------------------------------------------------

(defun good-normal-msg-p (msg)
  (equal (msg-type msg) :normal))

(defthm good-normal-msg-p-of-create-compute-message
  (good-normal-msg-p (create-compute-message local-state nbr)))

(defun good-normal-msg-list-p (msgs)
  (if (endp msgs)
      t
    (and (good-normal-msg-p (first msgs))
         (good-normal-msg-list-p (rest msgs)))))

(defun good-channel-snapshot-record-p (nbrs-from-i cs)
  (if (endp nbrs-from-i)
      t
    (and (good-normal-msg-list-p (g (first nbrs-from-i) cs))
         (good-channel-snapshot-record-p (rest nbrs-from-i) cs))))


;; ------------------------------------------------------------------
;; Snapshot-entry and snapshot-table predicates
;;
;; These predicates check that each snapshot entry has:
;;   - a legal snapshot status,
;;   - a waiting-marker-from list that refers only to valid incoming
;;     neighbors of the process, and
;;   - a channel-snapshot record containing only normal messages.
;;
;; The snapshot-table predicate checks every snapshot id currently
;; stored in the process.
;; ------------------------------------------------------------------

(defun good-snapshot-entry-p (entry nbrs-from-i)
  (and (good-snapshot-status-p (snapshot-status entry))
       (true-listp (snapshot-waiting-marker-from entry))
       (subset (snapshot-waiting-marker-from entry) nbrs-from-i)
       (good-channel-snapshot-record-p nbrs-from-i
                                       (snapshot-channel-snapshots entry))))

(defun good-snapshots-p (snapshot-ids p nbrs-from-i ids)
  (if (endp snapshot-ids)
      t
    (let* ((sid   (first snapshot-ids))
           (entry (snapshot-entry sid p)))
      (and (good-snapshot-id-p sid ids)
           (good-snapshot-entry-p entry nbrs-from-i)
           (good-snapshots-p (rest snapshot-ids)
                             p
                             nbrs-from-i
                             ids)))))


;; ------------------------------------------------------------------
;; Process predicate
;;
;; A process is good if:
;;   - its incoming and outgoing neighbor lists are true lists and
;;     refer only to valid process ids,
;;   - its process status is legal,
;;   - its counter is a natural number,
;;   - its waiting-recovery-from list refers only to incoming neighbors,
;;   - its snapshot-id list is a true list, has no duplicates, and
;;     contains :init, and
;;   - all of its snapshot entries are good.
;;
;; The local-state field is left abstract, since the application-level
;; local-state semantics are intentionally stubbed in this model.
;; ------------------------------------------------------------------

(defun good-proc-p ( p ids)
  (let* ((nbrs-in  (nbrs-from p))
         (nbrs-out (nbrs-to p)))
    (and (true-listp nbrs-in)
         (true-listp nbrs-out)
         (subset nbrs-in ids)
         (subset nbrs-out ids)

         (good-proc-status-p (proc-status p))
         (natp (counter p))

         (true-listp (waiting-recovery-from p))
         (subset (waiting-recovery-from p) nbrs-in)

         (true-listp (snapshot-ids p))
         (uniquep (snapshot-ids p))
         (memberp :init (snapshot-ids p))

         (good-snapshots-p (snapshot-ids p) p nbrs-in ids))))

(defun good-procs-p (ids procs all-ids)
  (if (endp ids)
      t
    (let* ((i (first ids))
           (p (g i procs)))
      (and (good-proc-p  p  all-ids)
           (good-procs-p (rest ids) procs all-ids)))))


;; ------------------------------------------------------------------
;; Channel predicates
;;
;; These predicates check the live communication channels.
;;
;; The channel table is treated as a 2D record where channel-state i j
;; gives the channel from process i to process j. Each such channel
;; must contain a proper list of good messages.
;; ------------------------------------------------------------------

(defun good-channel-p (src dst channels ids procs)
  (let ((p (g src procs)))
    (if (memberp dst (nbrs-to p))
        (good-msg-list-p (channel-state src dst channels) ids procs)
      (equal (channel-state src dst channels) nil))))

(defun good-channel-row-p (src dsts channels ids procs)
  (if (endp dsts)
      t
    (and (good-channel-p src (first dsts) channels ids procs)
         (good-channel-row-p src (rest dsts) channels ids procs))))

(defun good-channels-p (srcs dsts channels ids procs)
  (if (endp srcs)
      t
    (and (good-channel-row-p (first srcs) dsts channels ids procs)
         (good-channels-p (rest srcs) dsts channels ids procs))))

;; ------------------------------------------------------------------
;; Top-level state predicate
;;
;; A state is good if:
;;   - proc-ids is a true list with no duplicates,
;;   - all process records indexed by those ids are good, and
;;   - all live channels between those process ids are good.
;; ------------------------------------------------------------------

(defun good-state-p (st)
  (let* ((ids      (proc-ids st))
         (procs    (procs st))
         (channels (channels st)))
    (and (true-listp ids)
         (uniquep ids)
         (good-procs-p ids procs ids)
         (good-channels-p ids ids channels ids procs))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Initial-state proof support
;;
;; The lemmas in this block show that the concrete initial constructors
;; produce a structurally good implementation state.  The proof is split
;; into process-table preservation, channel-table preservation, and the
;; final top-level good-state-p theorem.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-normal-msg-list-p-of-nil
  (good-normal-msg-list-p nil))

(defthm good-msg-list-p-of-nil
  (good-msg-list-p nil ids procs))

(defthm good-channel-snapshot-record-p-of-nil
  (good-channel-snapshot-record-p nbrs-from-i nil))

(defthm good-snapshot-entry-p-of-make-init-snapshot-entry
  (good-snapshot-entry-p (make-init-snapshot-entry init-local-state)
                         nbrs-from-i))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;; 2. One installed initial process is good
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-proc-p-of-install-initial-snapshot-on-make-one-proc
  (good-proc-p
   (install-initial-snapshot (make-one-proc i all-ids))
   all-ids))


(defthm g-of-make-procs-aux
  (implies (and (memberp i ids)
                (uniquep ids))
           (equal (g i (make-procs-aux ids all-ids))
                  (make-one-proc i all-ids))))

(defthm g-of-s-diff
  (implies (not (equal k1 k2))
           (equal (g k1 (s k2 v r))
                  (g k1 r))))

(defthm g-of-install-initial-snapshots-when-not-member
  (implies (not (memberp k ids))
           (equal (g k (install-initial-snapshots ids procs))
                  (g k procs))))

(defthm g-of-install-initial-snapshots
  (implies (and (memberp i ids)
                (uniquep ids))
           (equal (g i (install-initial-snapshots ids procs))
                  (install-initial-snapshot (g i procs)))))


(defthm g-of-install-initial-snapshots-of-make-procs-aux
  (implies (and (memberp i ids)
                (uniquep ids))
           (equal (g i
                     (install-initial-snapshots ids
                                                (make-procs-aux ids all-ids)))
                  (install-initial-snapshot
                   (make-one-proc i all-ids)))))


(defthm good-proc-p-of-g-of-install-initial-snapshots-of-make-procs-aux
  (implies (and (memberp i ids)
                (uniquep ids))
           (good-proc-p
            (g i
               (install-initial-snapshots ids
                                          (make-procs-aux ids all-ids)))
            all-ids)))


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;; 3. All installed initial processes are good
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-procs-p-of-install-initial-snapshots-of-make-procs-aux
  (implies (uniquep ids)
           (good-procs-p ids
                         (install-initial-snapshots ids
                                                    (make-procs-aux ids all-ids))
                         all-ids)))



;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;; 4. Initial channels are good
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm good-channel-row-p-preserved-by-adding-fresh-dst
  (implies (and (good-channel-row-p src dsts channels ids procs)
                (not (memberp new-dst dsts)))
           (good-channel-row-p src dsts
                               (s new-dst row channels)
                               ids procs)))

(defthm good-channels-p-of-cons-new-dst
  (implies (and (good-channels-p srcs dsts channels ids procs)
                (not (memberp dst dsts))
		(uniquep dsts)
		(uniquep srcs))
           (good-channels-p srcs
                            (cons dst dsts)
                            (s dst (make-channel-row srcs) channels)
                            ids
                            procs)))

(defthm good-channels-p-of-make-channels-aux
    (implies (and (uniquep dsts)
		  (uniquep srcs))
           (good-channels-p srcs
                            dsts
                            (make-channels-aux srcs dsts)
                            ids
                            procs)))
  


(defthm good-channels-p-of-make-channels
    (implies (uniquep ids)
	     (good-channels-p ids ids (make-channels ids) ids procs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 4. Initial State is a good state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm initial-state-is-good-state
    (good-state-p (make-initial-state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NOP step preservation
;;
;; A :nop input does not modify the state, so good-state-p is preserved
;; directly by the definition of system-step.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-preserved-by-nop
  (implies (and (good-state-p st)
                (equal (ttype input) :nop))
           (good-state-p (system-step st input))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Crash step preservation
;;
;; A crash step only changes one process's :proc-status field to :crashed.
;; Since :crashed is an allowed process status, the process table remains
;; good.  Channel predicates are also preserved because they do not depend
;; on the process status field.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Updating only :proc-status does not change the snapshot table.

(defthm good-snapshots-p-of-set-proc-status-crashed
  (implies (good-snapshots-p snapshot-ids
                             p
                             nbrs-from
                             ids)
           (good-snapshots-p snapshot-ids
                             (s :proc-status :crashed p)
                             nbrs-from
                             ids)))

;; A good process remains good after changing its status to :crashed.

(defthm good-proc-p-of-set-proc-status-crashed
  (implies (good-proc-p p ids)
           (good-proc-p (s :proc-status :crashed p)
                        ids)))


(defthm good-proc-p-of-crashed-g-when-good-procs-p
  (implies (and (good-procs-p ids procs all-ids)
                (memberp i ids))
           (good-proc-p (s :proc-status
                           :crashed
                           (g i procs))
                        all-ids)))


  
(defthm good-proc-p-of-g-when-good-procs-p
  (implies (and (good-procs-p ids procs all-ids)
                (memberp i ids))
           (good-proc-p (g i procs)
                        all-ids)))

(defthm g-of-crash-updated-procs
  (equal (g k
            (s i
               (s :proc-status :crashed (g i procs))
               procs))
         (if (equal k i)
             (s :proc-status :crashed (g i procs))
           (g k procs))))

;; Lift the single-process crash update to the whole process table.

(defthm good-procs-p-of-crash-update
  (implies (and (true-listp ids)
                (uniquep ids)
                (true-listp all-ids)
                (uniquep all-ids)	
                (good-procs-p ids procs all-ids))
           (good-procs-p ids
                         (s i
                            (s :proc-status
                               :crashed
                               (g i procs))
                            procs)
                         all-ids)))

;; Channel well-formedness is unaffected by changing process status.

(defthm good-msg-list-p-of-crash-update
  (implies (good-msg-list-p msgs ids procs)
           (good-msg-list-p msgs ids
                            (s i
                               (s :proc-status :crashed (g i procs))
                               procs))))


(defthm good-channel-p-of-crash-update
  (implies (good-channel-p src dst channels ids procs)
           (good-channel-p src dst channels ids
                           (s i
                              (s :proc-status :crashed (g i procs))
                              procs))))



(defthm good-channel-row-p-of-crash-update
  (implies (good-channel-row-p src dsts channels ids procs)
           (good-channel-row-p src dsts channels ids
                               (s i
                                  (s :proc-status :crashed (g i procs))
                                  procs))))
  
(defthm good-channels-p-of-crash-update
  (implies (good-channels-p srcs dsts channels ids procs)
           (good-channels-p srcs dsts channels ids
                            (s i
                               (s :proc-status :crashed (g i procs))
                               procs))))



(defthm good-state-p-of-system-step-crash
  (implies (and (good-state-p st)
                (equal (ttype input) :crash))
           (good-state-p (system-step st input))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Normal step preservation
;;
;; A normal step has two effects:
;;   1. it may append compute messages to outgoing channels, and
;;   2. it updates the local state of the executing process.
;;
;; The following lemmas prove these two effects preserve the structural
;; good-state-p invariant.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Updating :local-state does not affect snapshot well-formedness.

(defthm good-snapshots-p-of-set-proc-update-normal
  (implies (good-snapshots-p snapshot-ids
                             p
                             nbrs-from
                             ids)
           (good-snapshots-p snapshot-ids
                             (s :local-state val p)
                             nbrs-from
                             ids)))

;; A good process remains good after a local-state update.

(defthm good-proc-p-of-set-proc-update-normal
  (implies (good-proc-p p ids)
           (good-proc-p (s :local-state val p)
                        ids)))


(defthm good-proc-p-of-update-normal-g-when-good-procs-p
  (implies (and (good-procs-p ids procs all-ids)
                (memberp i ids))
           (good-proc-p (s :local-state val
                           (g i procs))
                        all-ids)))


  
(defthm good-proc-p-of-g-when-good-procs-p-update-normal
  (implies (and (good-procs-p ids procs all-ids)
                (memberp i ids))
           (good-proc-p (g i procs)
                        all-ids)))

(defthm g-of-update-normal-updated-procs
  (equal (g k
            (s i
               (s :local-state val (g i procs))
               procs))
         (if (equal k i)
             (s :local-state val (g i procs))
           (g k procs))))


;; Lift the local-state update to the whole process table.

(defthm good-procs-p-of-normal-update
  (implies (and (true-listp ids)
                (uniquep ids)
                (true-listp all-ids)
                (uniquep all-ids)	
                (good-procs-p ids procs all-ids))
           (good-procs-p ids
                         (s i
                            (s :local-state
                               val
                               (g i procs))
                            procs)
                         all-ids)))


;; Channel predicates do not depend on process local-state.

(defthm good-msg-list-p-of-normal-update
  (implies (good-msg-list-p msgs ids procs)
           (good-msg-list-p msgs ids
                            (s i
                               (s :local-state val (g i procs))
                               procs))))


(defthm good-channel-p-of-normal-update
  (implies (good-channel-p src dst channels ids procs)
           (good-channel-p src dst channels ids
                           (s i
                              (s :local-state val (g i procs))
                              procs))))



(defthm good-channel-row-p-of-normal-update
  (implies (good-channel-row-p src dsts channels ids procs)
           (good-channel-row-p src dsts channels ids
                               (s i
                                  (s  :local-state val (g i procs))
                                  procs))))

(defthm good-channels-p-of-normal-update
  (implies (good-channels-p srcs dsts channels ids procs)
           (good-channels-p srcs dsts channels ids
                            (s i
                               (s :local-state val (g i procs))
                               procs))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Compute-message preservation lemmas
;;
;; Compute messages are normal messages, so appending them to a good
;; message list preserves good-msg-list-p.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-msg-p-of-create-compute-message
  (good-msg-p (create-compute-message local-state nbr)
              ids
              procs))


(defthm good-msg-list-p-of-snoc-create-compute-message
  (implies (good-msg-list-p msgs ids procs)
           (good-msg-list-p
            (snoc msgs (create-compute-message local-state nbr))
            ids
            procs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Channel lookup/update lemmas
;;
;; These lemmas reason about the 2D channel table.  A send update changes
;; only one channel entry, namely source i and destination j.  All other
;; source/destination lookups remain unchanged.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm channel-lookup-after-send-compute-message-when-dst-not-in-nbrs
  (implies (not (memberp dst nbrs))
           (equal (g src
                     (g dst
                        (send-compute-message local-state i nbrs channels)))
                  (g src
                     (g dst channels)))))
  

;; Updating a different destination row preserves the checked channel.

(defthm good-msg-list-p-preserved-by-setting-different-dst
    (implies (and (memberp dst dsts)
		  (not (memberp dst2 dsts))
                (good-msg-list-p (g src (g dst channels))
                                 ids procs))
           (good-msg-list-p
            (g src
               (g dst
                  (s dst2 row channels)))
            ids procs)))

;; Updating a different source entry inside the same row preserves the checked channel.

(defthm good-msg-list-p-preserved-by-setting-different-src
  (implies (and (not (equal src src2))
                (good-msg-list-p (g src (g dst channels))
                                 ids procs))
           (good-msg-list-p
            (g src
               (g dst
                  (s dst
                     (s src2 val (g dst channels))
                     channels)))
            ids procs)))

;; General row-entry update: if the new value is good, the lookup remains good.

(defthm good-msg-list-p-of-setting-channel-src-entry-val
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (good-msg-list-p val ids procs))
   (good-msg-list-p
    (g src
       (s i
          val
          (g dst channels)))
    ids procs))
  :hints (("Goal"
           :cases ((equal i src)))))

;; General 2D channel update: if the new channel value is good, the checked lookup remains good.

(defthm good-msg-list-p-of-setting-channel-dst-entry-val
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
	
        (good-msg-list-p val ids procs))
   (good-msg-list-p
    (g src
       (g dst
          (s j
             (s i val (g j channels))
             channels)))
    ids procs))
  :hints (("Goal"
           :cases ((equal dst j)))))



(defthm g-of-s-different-src
  (implies (not (equal src i))
           (equal (g src (s i val row))
                  (g src row))))

(defthm g-g-of-s-different-dst
  (implies (not (equal dst j))
           (equal (g src
                     (g dst
                        (s j row channels)))
                  (g src
                     (g dst channels)))))


(defthm channel-lookup-of-setting-different-channel
  (implies (or (not (equal dst j))
               (not (equal src i)))
           (equal
            (g src
               (g dst
                  (s j
                     (s i val (g j channels))
                     channels)))
            (g src
               (g dst channels))))
  :hints (("Goal"
           :do-not '(generalize fertilize)
           :cases ((equal dst j)))))


(defthm good-msg-list-p-of-setting-different-channel
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (or (not (equal dst j))
            (not (equal src i))))
   (good-msg-list-p
    (g src
       (g dst
          (s j
             (s i val (g j channels))
             channels)))
    ids procs)))


(defthm good-msg-list-p-of-setting-channel-combined
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (or (not (equal dst j))
            (not (equal src i))
            (good-msg-list-p val ids procs)))
   (good-msg-list-p
    (g src
       (g dst
          (s j
             (s i val (g j channels))
             channels)))
    ids procs))
  :hints (("Goal"
           :do-not '(generalize fertilize)
           :cases ((equal dst j)
                   (equal src i)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; One-send update preservation
;;
;; A single compute send appends one compute message to channel i -> j.
;; If the checked channel is the updated one, the snoc lemma is used.
;; Otherwise, the channel lookup is unchanged.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-msg-list-p-of-snoc-create-compute-message-same-channel
  (implies
   (and (equal src i)
        (equal dst j)
        (good-msg-list-p (g src (g dst channels))
                         ids procs))
   (good-msg-list-p
    (snoc (g i (g j channels))
          (create-compute-message local-state j))
    ids procs)))

;; Case helper: either the checked channel is different, or the new snoc value is good.

(defthm one-compute-send-update-disjunct
  (implies
   (good-msg-list-p (g src (g dst channels))
                    ids procs)
   (or (not (equal dst j))
       (not (equal src i))
       (good-msg-list-p
        (snoc (g i (g j channels))
              (create-compute-message local-state j))
        ids procs))))


;; A single compute-send update preserves good-msg-list-p for any checked channel.

(defthm good-msg-list-p-of-one-compute-send-update
  (implies
   (good-msg-list-p (g src (g dst channels))
                    ids procs)
   (good-msg-list-p
    (g src
       (g dst
          (s j
             (s i
                (snoc (g i (g j channels))
                      (create-compute-message local-state j))
                (g j channels))
             channels)))
    ids procs))
  :hints (("Goal"
           :do-not '(generalize fertilize)
           :use ((:instance good-msg-list-p-of-setting-channel-combined
                            (src src)
                            (dst dst)
                            (i i)
                            (j j)
                            (channels channels)
                            (ids ids)
                            (procs procs)
                            (val (snoc (g i (g j channels))
                                       (create-compute-message local-state j))))
                 (:instance one-compute-send-update-disjunct
                            (src src)
                            (dst dst)
                            (i i)
                            (j j)
                            (channels channels)
                            (ids ids)
                            (procs procs)
                            (local-state local-state))))))


;; Repeated compute sends preserve good-msg-list-p by induction over nbrs.

(defthm good-msg-list-p-of-channel-after-send-compute-message
  (implies
   (good-msg-list-p (g src (g dst channels)) ids procs)
   (good-msg-list-p
    (g src
       (g dst
          (send-compute-message local-state i nbrs channels)))
    ids procs)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Nil-channel preservation
;;
;; For non-neighbor channels, good-channel-p requires the channel to be nil.
;; These lemmas show that send-compute-message does not make such channels
;; non-nil when sends are restricted to valid outgoing neighbors.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm not-memberp-when-subset-and-not-memberp
  (implies (and (subset xs ys)
                (not (memberp a ys)))
           (not (memberp a xs))))



;; If dst is not among the destinations being processed, its row is unchanged.

(defthm channel-nil-after-send-compute-message-when-dst-not-in-nbrs-2
    (implies (and (not (memberp dst  nbrs-to))
		  (subset nbrs nbrs-to )
                (not (g src (g dst channels))))
           (not (g src
                   (g dst
                      (send-compute-message local-state i nbrs channels))))))


;; If src is not the sending process, channels from src are unchanged.

(defthm channel-lookup-after-send-compute-message-when-src-not-i
  (implies (not (equal src i))
           (equal (g src
                     (g dst
                        (send-compute-message local-state i nbrs channels)))
                  (g src
                     (g dst channels)))))


(defthm channel-nil-after-send-compute-message-when-src-not-i
  (implies (and (not (equal src i))
                (not (g src (g dst channels))))
           (not
            (g src
               (g dst
                  (send-compute-message local-state i nbrs channels))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Channel preservation under normal sends
;;
;; First prove preservation for one channel, then lift it to a row, and
;; finally to the full channel table.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Single-channel preservation under send-compute-message.

(defthm good-channel-p-of-send-compute-message
  (implies (and (good-channel-p src dst channels ids procs)
                (subset nbrs (nbrs-to (g i procs))))
           (good-channel-p
            src
            dst
            (send-compute-message local-state i nbrs channels)
            ids
            procs))
  :hints (("Goal'"
           :cases ((equal src i)))))


;; Row-level preservation: every destination in a row remains good.

(defthm good-channel-row-p-of-send-compute-message
  (implies (and (good-channel-row-p src dsts channels ids procs)
                (subset nbrs (nbrs-to (g i procs))))
           (good-channel-row-p
            src
            dsts
            (send-compute-message local-state i nbrs channels)
            ids
            procs))
    :hints (("Goal"
           :induct (good-channel-row-p src dsts channels ids procs))))


;; Full channel-table preservation: every source row remains good.

(defthm good-channels-p-of-send-compute-message
  (implies (and (good-channels-p srcs dsts channels ids procs)
                (subset nbrs (nbrs-to (g i procs))))
           (good-channels-p
            srcs
            dsts
            (send-compute-message local-state i nbrs channels)
            ids
            procs))
      :hints (("Goal"
           :induct (good-channels-p srcs dsts channels ids procs))))

(defthm memberp-of-cons-right
  (implies (memberp e xs)
           (memberp e (cons a xs))))

(defthm subset-of-cons
  (implies (subset xs ys)
           (subset xs (cons a ys))))

(defthm subset-reflexive
    (subset x x))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Normal system-step preservation
;;
;; Combine process-table preservation, channel-table preservation, and
;; the definition of system-step for :normal inputs.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-system-step-normal
  (implies (and (good-state-p st)
                (equal (ttype input) :normal))
           (good-state-p (system-step st input))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Checkpoint system-step preservation
;;
;; Combine process-table preservation, channel-table preservation, and
;; the definition of system-step for :normal inputs.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm g-of-s-nil-nil
  (equal (g k (s j nil nil))
         nil)
  :hints (("Goal"
           :cases ((equal k j)))))

(defthm good-normal-msg-list-p-of-g-of-s-nil-nil
  (good-normal-msg-list-p (g k (s j nil nil))))

;;Make-snapshot-entry produces a good-snapshot-entry
(defthm good-snapshot-entry-p-of-make-snapshot-entry
  (implies (and (true-listp waiting-marker-from)
                (subset waiting-marker-from nbrs-from-i))
           (good-snapshot-entry-p
            (make-snapshot-entry local-snap-shot
                                 waiting-marker-from
                                 j)
            nbrs-from-i)))


;;Adding a good snapshot id preserves good-snapshots-p
(defthm good-snapshots-p-of-add-snapshot-id
  (implies
   (and (good-snapshot-id-p sid ids)
        (good-snapshot-entry-p entry nbrs-from-i)
        (good-snapshots-p snapshot-ids
                          (install-snapshot-entry sid entry p)
                          nbrs-from-i
                          ids))
   (good-snapshots-p (add-snapshot-id sid snapshot-ids)
                     (install-snapshot-entry sid entry p)
                     nbrs-from-i
                     ids)))



;; (defthm good-snapshots-p-of-install-snapshot-entry
;;   (implies
;;    (and (good-snapshots-p (snapshot-ids p)
;;                           p
;;                           nbrs-from-i
;;                           ids)
;;         (good-snapshot-id-p sid ids)
;;         (good-snapshot-entry-p entry nbrs-from-i))
;;    (good-snapshots-p
;;     (snapshot-ids (install-snapshot-entry sid entry p))
;;     (install-snapshot-entry sid entry p)
;;     nbrs-from-i
;;     ids))
;;   :hints (("Goal"
;; 	   :in-theory)))
  
;; (defthm good-state-p-of-system-step-start-checkpoint
;;   (implies (and (good-state-p st)
;;                 (equal (ttype input) :start-checkpoint))
;;            (good-state-p (system-step st input))))

