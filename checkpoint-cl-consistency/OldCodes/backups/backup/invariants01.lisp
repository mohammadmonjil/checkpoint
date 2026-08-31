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

(defun good-snapshot-ids-p (snapshot-ids ids)
  (if (endp snapshot-ids)
      t
    (and (good-snapshot-id-p (first snapshot-ids) ids)
         (good-snapshot-ids-p (rest snapshot-ids) ids))))

(defun good-snapshot-ids-list-p (snapshot-ids ids)
  (and (true-listp snapshot-ids)
       (uniquep snapshot-ids)
       (memberp :init snapshot-ids)
       (good-snapshot-ids-p snapshot-ids ids)))

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
  (declare (irrelevant ids))
  (if (endp snapshot-ids)
      t
    (let* ((sid   (first snapshot-ids))
           (entry (snapshot-entry sid p)))
      (and
           ;(good-snapshot-id-p sid ids)
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
	 (good-snapshot-ids-list-p (snapshot-ids p) ids)
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


(defthm good-snapshots-p-of-set-snapshot-entry-general
  (implies
   (and (good-snapshots-p snapshot-ids
                          p
                          nbrs-from-i
                          ids)
        (good-snapshot-entry-p entry nbrs-from-i))
   (good-snapshots-p
    snapshot-ids
    (s :snapshots
       (s sid entry (snapshots p))
       p)
    nbrs-from-i
    ids))
  :hints (("Goal"

           :in-theory (disable good-snapshot-entry-p))

          ("Subgoal *1/4''"
           :cases ((equal sid (car snapshot-ids))))))






(defthm good-snapshots-p-of-set-snapshot-ids-field
  (implies
   (good-snapshots-p snapshot-ids
                     p
                     nbrs-from-i
                     ids)
   (good-snapshots-p snapshot-ids
                     (s :snapshot-ids new-snapshot-ids p)
                     nbrs-from-i
                     ids)))



(defthm good-snapshots-p-of-set-snapshot-entry-after-set-snapshot-ids
  (implies
   (and (good-snapshots-p snapshot-ids
                          p
                          nbrs-from-i
                          ids)
        (good-snapshot-entry-p entry nbrs-from-i))
   (good-snapshots-p
    snapshot-ids
    (s :snapshots
       (s sid entry (g :snapshots p))
       (s :snapshot-ids new-snapshot-ids p))
    nbrs-from-i
    ids))
  :hints
  (("Goal"
    :use ((:instance good-snapshots-p-of-set-snapshot-ids-field
                     (snapshot-ids snapshot-ids)
                     (p p)
                     (new-snapshot-ids new-snapshot-ids)
                     (nbrs-from-i nbrs-from-i)
                     (ids ids))

          (:instance good-snapshots-p-of-set-snapshot-entry-general
                     (snapshot-ids snapshot-ids)
                     (p (s :snapshot-ids new-snapshot-ids p))
                     (sid sid)
                     (entry entry)
                     (nbrs-from-i nbrs-from-i)
                     (ids ids)))
    :in-theory (disable good-snapshot-entry-p))))




(defthm good-snapshots-p-of-install-snapshot-entry
  (implies
   (and (good-snapshots-p (snapshot-ids p)
                          p
                          nbrs-from-i
                          ids)
        (good-snapshot-entry-p entry nbrs-from-i))
   (good-snapshots-p
    (snapshot-ids (install-snapshot-entry sid entry p))
    (install-snapshot-entry sid entry p)
    nbrs-from-i
    ids))
  :hints (("Goal"
	   :in-theory (disable good-snapshot-entry-p))))



(defthm good-snapshots-p-of-set-counter
  (implies (good-snapshots-p snapshot-ids
                             p
                             nbrs-from-i
                             ids)
           (good-snapshots-p snapshot-ids
                             (s :counter val p)
                             nbrs-from-i
                             ids)))


(defthm good-proc-p-of-increment-counter
  (implies (good-proc-p p ids)
           (good-proc-p
            (s :counter
               (+ 1 (counter p))
               p)
            ids)))


(defthm good-proc-p-of-install-snapshot-entry-and-increment-counter
  (implies
   (and (good-proc-p p ids)
        (good-snapshot-id-p sid ids)
        (good-snapshot-entry-p entry (nbrs-from p)))
   (good-proc-p
    (s :counter
       (+ 1 (counter p))
       (install-snapshot-entry sid entry p))
    ids)))





(defthm good-proc-p-of-install-make-snapshot-entry-and-increment-counter
  (implies
   (and (good-proc-p p ids)
        (good-snapshot-id-p sid ids)
        (true-listp waiting-marker-from)
        (subset waiting-marker-from (nbrs-from p)))
   (good-proc-p
    (s :counter
       (+ 1 (counter p))
       (install-snapshot-entry
        sid
        (make-snapshot-entry local-snap-shot
                             waiting-marker-from
                             j)
        p))
    ids))
  :hints
  (("Goal"
    :in-theory (disable good-proc-p
                        make-snapshot-entry
                        install-snapshot-entry
                        good-snapshot-entry-p))))




(defthm good-procs-p-of-set-good-proc
  (implies (and (good-procs-p ids procs all-ids)
                (good-proc-p new-p all-ids))
           (good-procs-p ids
                         (s i new-p procs)
                         all-ids))
  :hints (("Goal"
           :induct (good-procs-p ids procs all-ids))
          ("Subgoal *1/2"
           :cases ((equal i (car ids))))))





(defthm good-procs-p-of-set-proc-if-new-proc-good-when-member
  (implies (and (good-procs-p ids procs all-ids)
                (implies (memberp i ids)
                         (good-proc-p new-p all-ids)))
           (good-procs-p ids
                         (s i new-p procs)
                         all-ids))
  :hints (("Goal"
           :induct (good-procs-p ids procs all-ids))
          ("Subgoal *1/2"
           :cases ((equal i (car ids))))))



(defthm good-proc-p-of-start-checkpoint-updated-proc
  (implies (and (good-proc-p p ids)
                (memberp i ids)
		)
           (good-proc-p
            (s :counter
               (+ 1 (counter p))
               (install-snapshot-entry
                (list i (counter p))
                (make-snapshot-entry (local-state p)
                                     (nbrs-from p)
                                     nil)
                p))
            ids)))



(defthm good-proc-p-of-start-checkpoint-updated-proc-when-good-procs-p
  (implies (and (good-procs-p ids procs ids)
                (memberp i ids))
           (good-proc-p
            (s :counter
               (+ 1 (counter (g i procs)))
               (install-snapshot-entry
                (list i (counter (g i procs)))
                (make-snapshot-entry (local-state (g i procs))
                                     (nbrs-from (g i procs))
                                     nil)
                (g i procs)))
            ids))
  :hints (("Goal"
           :in-theory (disable good-proc-p
                               make-snapshot-entry
                               install-snapshot-entry))))




(defthm good-procs-p-of-start-checkpoint-proc-update
  (implies
   (and (good-procs-p ids procs ids)
        (true-listp ids)
        (uniquep ids))
   (good-procs-p
    ids
    (s i
       (s :counter
          (+ 1 (counter (g i procs)))
          (install-snapshot-entry
           (list i (counter (g i procs)))
           (make-snapshot-entry (local-state (g i procs))
                                (nbrs-from (g i procs))
                                nil)
           (g i procs)))
       procs)
    ids))
  :hints (("Goal"
           :do-not '(generalize fertilize)
           :use ((:instance good-procs-p-of-set-proc-if-new-proc-good-when-member
                            (ids ids)
                            (procs procs)
                            (all-ids ids)
                            (i i)
                            (new-p
                             (s :counter
                                (+ 1 (counter (g i procs)))
                                (install-snapshot-entry
                                 (list i (counter (g i procs)))
                                 (make-snapshot-entry
                                  (local-state (g i procs))
                                  (nbrs-from (g i procs))
                                  nil)
                                 (g i procs)))))

                 (:instance good-proc-p-of-start-checkpoint-updated-proc-when-good-procs-p
                            (ids ids)
                            (procs procs)
                            (i i)))
           :in-theory (disable good-proc-p
                               good-procs-p
                               make-snapshot-entry
                               install-snapshot-entry
                               good-snapshot-entry-p))))













;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generic send-msg-all-outgoing-channels preservation
;;
;; This is the generalized version of the send-compute-message proof.
;; Instead of using create-compute-message, we assume directly that MSG
;; is a good message.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;START;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-msg-list-p-of-snoc-good-msg
  (implies (and (good-msg-list-p msgs ids procs)
                (good-msg-p msg ids procs))
           (good-msg-list-p (snoc msgs msg)
                            ids
                            procs))
  :hints (("Goal"
           :induct (snoc msgs msg))))


(defthm one-generic-send-update-disjunct
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (good-msg-p msg ids procs))
   (or (not (equal dst j))
       (not (equal src i))
       (good-msg-list-p
        (snoc (g i (g j channels)) msg)
        ids procs))))


(defthm good-msg-list-p-of-one-generic-send-update
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (good-msg-p msg ids procs))
   (good-msg-list-p
    (g src
       (g dst
          (s j
             (s i
                (snoc (g i (g j channels)) msg)
                (g j channels))
             channels)))
    ids procs))
  :hints
  (("Goal"
    :do-not '(generalize fertilize)
    :use ((:instance good-msg-list-p-of-setting-channel-combined
                     (src src)
                     (dst dst)
                     (i i)
                     (j j)
                     (channels channels)
                     (ids ids)
                     (procs procs)
                     (val (snoc (g i (g j channels)) msg)))

          (:instance one-generic-send-update-disjunct
                     (src src)
                     (dst dst)
                     (i i)
                     (j j)
                     (channels channels)
                     (ids ids)
                     (procs procs)
                     (msg msg))))))


(defthm good-msg-list-p-of-channel-after-send-msg-all-outgoing-channels
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (good-msg-p msg ids procs))
   (good-msg-list-p
    (g src
       (g dst
          (send-msg-all-outgoing-channels msg i nbrs channels)))
    ids procs))
  :hints (("Goal"
           :induct (send-msg-all-outgoing-channels msg i nbrs channels))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lookup/nil preservation for channels that should not be modified
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm channel-lookup-after-send-msg-all-outgoing-channels-when-src-not-i
  (implies
   (not (equal src i))
   (equal
    (g src
       (g dst
          (send-msg-all-outgoing-channels msg i nbrs channels)))
    (g src
       (g dst channels))))
  :hints (("Goal"
           :induct (send-msg-all-outgoing-channels msg i nbrs channels))))


(defthm channel-lookup-after-send-msg-all-outgoing-channels-when-dst-not-in-nbrs
  (implies
   (not (memberp dst nbrs))
   (equal
    (g src
       (g dst
          (send-msg-all-outgoing-channels msg i nbrs channels)))
    (g src
       (g dst channels))))
  :hints (("Goal"
           :induct (send-msg-all-outgoing-channels msg i nbrs channels))))


(defthm channel-nil-after-send-msg-all-outgoing-channels-when-dst-not-in-nbrs-to
  (implies
   (and (not (memberp dst nbrs-to))
        (subset nbrs nbrs-to)
        (not (g src (g dst channels))))
   (not
    (g src
       (g dst
          (send-msg-all-outgoing-channels msg i nbrs channels)))))
  :hints
  (("Goal"
    :use ((:instance not-memberp-when-subset-and-not-memberp
                     (xs nbrs)
                     (ys nbrs-to)
                     (a dst))

          (:instance channel-lookup-after-send-msg-all-outgoing-channels-when-dst-not-in-nbrs
                     (src src)
                     (dst dst)
                     (msg msg)
                     (i i)
                     (nbrs nbrs)
                     (channels channels))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lift to good-channel-p, good-channel-row-p, and good-channels-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-channel-p-of-send-msg-all-outgoing-channels
  (implies
   (and (good-channel-p src dst channels ids procs)
        (good-msg-p msg ids procs)
        (subset nbrs (nbrs-to (g i procs))))
   (good-channel-p
    src
    dst
    (send-msg-all-outgoing-channels msg i nbrs channels)
    ids
    procs))
  :hints (("Goal"
           :cases ((equal src i)))))


(defthm good-channel-row-p-of-send-msg-all-outgoing-channels
  (implies
   (and (good-channel-row-p src dsts channels ids procs)
        (good-msg-p msg ids procs)
        (subset nbrs (nbrs-to (g i procs))))
   (good-channel-row-p
    src
    dsts
    (send-msg-all-outgoing-channels msg i nbrs channels)
    ids
    procs))
  :hints (("Goal"
           :induct (good-channel-row-p src dsts channels ids procs))))


(defthm good-channels-p-of-send-msg-all-outgoing-channels
  (implies
   (and (good-channels-p srcs dsts channels ids procs)
        (good-msg-p msg ids procs)
        (subset nbrs (nbrs-to (g i procs))))
   (good-channels-p
    srcs
    dsts
    (send-msg-all-outgoing-channels msg i nbrs channels)
    ids
    procs))
  :hints (("Goal"
           :induct (good-channels-p srcs dsts channels ids procs))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-channels-p-of-send-msg-all-outgoing-channels
  (implies
   (and (good-channels-p srcs dsts channels ids procs)
        (good-msg-p msg ids procs)
        (subset nbrs (nbrs-to (g i procs))))
   (good-channels-p
    srcs
    dsts
    (send-msg-all-outgoing-channels msg i nbrs channels)
    ids
    procs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generic send-msg-all-outgoing-channels preservation
;;
;; This is the generalized version of the send-compute-message proof.
;; Instead of using create-compute-message, we assume directly that MSG
;; is a good message.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;END;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;






(defthm some-proc-has-snapshot-id-p-after-install-snapshot-entry
  (implies (memberp i ids)
           (some-proc-has-snapshot-id-p
            sid
            ids
            (s i
               (install-snapshot-entry sid entry (g i procs))
               procs)))
  :hints (("Goal"
           :induct (some-proc-has-snapshot-id-p sid ids procs))
          ("Subgoal *1/2"
           :cases ((equal i (car ids))))))


(defthm good-msg-p-of-create-marker-message-after-install-snapshot-entry
  (implies (memberp i ids)
           (good-msg-p
            (create-marker-message local-state sid)
            ids
            (s i
               (install-snapshot-entry sid entry (g i procs))
               procs)))
  :hints (("Goal"
           :use ((:instance good-msg-p-of-create-marker-message
                            (local-state local-state)
                            (sid sid)
                            (ids ids)
                            (procs
                             (s i
                                (install-snapshot-entry sid entry (g i procs))
                                procs))))
           :in-theory (disable good-msg-p-of-create-marker-message))))



(defthm memberp-sid-of-counter-after-install-snapshot-entry
  (memberp sid
           (snapshot-ids
            (s :counter val
               (install-snapshot-entry sid entry p)))))


(defthm some-proc-has-snapshot-id-p-after-checkpoint-proc-update
  (implies (memberp i ids)
           (some-proc-has-snapshot-id-p
            sid
            ids
            (s i
               (s :counter val
                  (install-snapshot-entry sid entry (g i procs)))
               procs)))
  :hints (("Goal"
           :induct (some-proc-has-snapshot-id-p sid ids procs))
          ("Subgoal *1/2"
           :cases ((equal i (car ids))))))


(defthm good-msg-p-of-create-marker-message-after-checkpoint-proc-update
  (implies (memberp i ids)
           (good-msg-p
            (create-marker-message local-state sid)
            ids
            (s i
               (s :counter val
                  (install-snapshot-entry sid entry (g i procs)))
               procs)))
  :hints (("Goal"
           :use ((:instance good-msg-p-of-create-marker-message
                            (local-state local-state)
                            (sid sid)
                            (ids ids)
                            (procs
                             (s i
                                (s :counter val
                                   (install-snapshot-entry sid entry (g i procs)))
                                procs))))
           :in-theory (disable good-msg-p-of-create-marker-message))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm good-marker-msg-for-start-checkpoint-updated-procs
  (implies (memberp i ids)
           (good-msg-p
            (create-marker-message
             (local-state (g i procs))
             (list i (counter (g i procs))))
            ids
            (s i
               (s :counter
                  (+ 1 (counter (g i procs)))
                  (install-snapshot-entry
                   (list i (counter (g i procs)))
                   (make-snapshot-entry
                    (local-state (g i procs))
                    (nbrs-from (g i procs))
                    nil)
                   (g i procs)))
               procs)))
  :hints
  (("Goal"
    :use ((:instance good-msg-p-of-create-marker-message-after-checkpoint-proc-update
                     (local-state (local-state (g i procs)))
                     (sid (list i (counter (g i procs))))
                     (ids ids)
                     (i i)
                     (val (+ 1 (counter (g i procs))))
                     (entry (make-snapshot-entry
                             (local-state (g i procs))
                             (nbrs-from (g i procs))
                             nil))
                     (procs procs)))
    :in-theory (disable good-msg-p-of-create-marker-message-after-checkpoint-proc-update))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;









Goal'
(IMPLIES
 (AND (TRUE-LISTP (G :PROC-IDS ST))
      (UNIQUEP (G :PROC-IDS ST))
      (GOOD-PROCS-P (G :PROC-IDS ST)
                    (G :PROCS ST)
                    (G :PROC-IDS ST))
      (GOOD-CHANNELS-P (G :PROC-IDS ST)
                       (G :PROC-IDS ST)
                       (G :CHANNELS ST)
                       (G :PROC-IDS ST)
                       (G :PROCS ST))
      (EQUAL (G :TTYPE INPUT)
             :START-CHECKPOINT)
      (MEMBERP (G :PID INPUT)
               (G :PROC-IDS ST)))
 (GOOD-CHANNELS-P
  (G :PROC-IDS ST)
  (G :PROC-IDS ST)
  (SEND-MSG-ALL-OUTGOING-CHANNELS
       (CREATE-MARKER-MESSAGE
            (G :LOCAL-STATE (G (G :PID INPUT) (G :PROCS ST)))
            (LIST (G :PID INPUT)
                  (G :COUNTER (G (G :PID INPUT) (G :PROCS ST)))))
       (G :PID INPUT)
       (G :NBRS-TO (G (G :PID INPUT) (G :PROCS ST)))
       (G :CHANNELS ST))
  (G :PROC-IDS ST)
  (S
   (G :PID INPUT)
   (S
    :COUNTER
    (+ 1
       (G :COUNTER (G (G :PID INPUT) (G :PROCS ST))))
    (INSTALL-SNAPSHOT-ENTRY
       (LIST (G :PID INPUT)
             (G :COUNTER (G (G :PID INPUT) (G :PROCS ST))))
       (MAKE-SNAPSHOT-ENTRY (G :LOCAL-STATE (G (G :PID INPUT) (G :PROCS ST)))
                            (G :NBRS-FROM (G (G :PID INPUT) (G :PROCS ST)))
                            NIL)
       (G (G :PID INPUT) (G :PROCS ST))))
   (G :PROCS ST))))


Goal'
(IMPLIES
 (AND (TRUE-LISTP ids)
      (UNIQUEP ids)
      (GOOD-PROCS-P ids
                    procs
                    ids)

      (GOOD-CHANNELS-P ids
                       ids
                       channels
                       ids
                       procs )

      (EQUAL (G :TTYPE INPUT)
             :START-CHECKPOINT)
      
      (MEMBERP i ids))


 (GOOD-CHANNELS-P
  ids
  ids
  (SEND-MSG-ALL-OUTGOING-CHANNELS
   (CREATE-MARKER-MESSAGE
    (G :LOCAL-STATE (G i procs))
    (LIST i
          (G :COUNTER (G i procs))))
   i
   nbrs
   channels)

  ids

  (S i
     (S  :COUNTER
	 (+ 1
	    (G :COUNTER (G i procs)
	       (INSTALL-SNAPSHOT-ENTRY
		(LIST i (G :COUNTER (G i procs)))
		(MAKE-SNAPSHOT-ENTRY (G :LOCAL-STATE (G i procs)))
	        (G :NBRS-FROM (G i procs))
		NIL)
	       (G i procs)))
	 procs )))


(defthm good-channels-p-of-start-checkpoint-channel-update
  (implies
   (and (true-listp ids)
        (uniquep ids)
        (good-procs-p ids procs ids)
        (good-channels-p ids ids channels ids procs)
        (memberp i ids))

   (good-channels-p
    ids
    ids

    ;; updated channels after sending marker
    (send-msg-all-outgoing-channels
     (create-marker-message
      (local-state (g i procs))
      (list i (counter (g i procs))))
     i
     (nbrs-to (g i procs))
     channels)

    ids

    ;; updated procs after installing snapshot and incrementing counter
    (s i
       (s :counter
          (+ 1 (counter (g i procs)))
          (install-snapshot-entry
           (list i (counter (g i procs)))
           (make-snapshot-entry
            (local-state (g i procs))
            (nbrs-from (g i procs))
            nil)
           (g i procs)))
       procs))))


(defthm good-state-p-of-system-step-start-checkpoint
  (implies (and (good-state-p st)
                (equal (ttype input) :start-checkpoint)
		(memberp (pid input) (proc-ids st)))
           (good-state-p (system-step st input)))
  :hints
  (("Goal"
    :in-theory (disable good-proc-p
                        make-snapshot-entry
                        install-snapshot-entry
			create-marker-message))

   ("Subgoal 2"
    :use (:instance good-procs-p-of-start-checkpoint-proc-update
                    (ids   (g :proc-ids st))
                    (procs (g :procs st))
                    (i     (g :pid input)))
    :in-theory (disable good-proc-p
                        good-procs-p
                        make-snapshot-entry
                        install-snapshot-entry))))


;; (defthm good-state-p-of-system-step-start-checkpoint
;;   (implies (and (good-state-p st)
;;                 (equal (ttype input) :start-checkpoint))
;;            (good-state-p (system-step st input)))
;;   :hints (("Goal"
;;            :in-theory (disable good-proc-p make-snapshot-entry install-snapshot-entry))))

;; (defthm good-state-p-of-system-step-start-checkpoint
;;   (implies (and (good-state-p st)
;;                 (equal (ttype input) :start-checkpoint))
;;            (good-state-p (system-step st input))))





(defthm good-msg-p-of-create-marker-message
  (implies (some-proc-has-snapshot-id-p sid ids procs)
           (good-msg-p (create-marker-message local-state sid)
                       ids
                       procs)))



(defthm good-channels-p-of-send-msg-all-outgoing-channels
  (implies
   (and (good-channels-p srcs dsts channels ids procs)
        (good-msg-p msg ids procs)
        (subset nbrs (nbrs-to (g i procs))))
   (good-channels-p
    srcs
    dsts
    (send-msg-all-outgoing-channels msg i nbrs channels)
    ids
    procs)))







(defun f2 (procs input)
  (let* ((i     (pid input))
         (p     (g i procs))
         (sid   (list i (counter p)))
         (entry (make-snapshot-entry
                 (local-state p)
                 (nbrs-from p)
                 nil))
         (p-new (s :counter
                   (+ 1 (counter p))
                   (install-snapshot-entry sid entry p))))
    (s i p-new procs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; f2 preserves old snapshot ids
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm memberp-of-add-snapshot-id-preserve
  (implies (memberp old-sid ids)
           (memberp old-sid
                    (add-snapshot-id new-sid ids)))
  :hints (("Goal"
           :in-theory (enable add-snapshot-id))))

(defthm snapshot-ids-of-install-snapshot-entry
  (equal (snapshot-ids
          (install-snapshot-entry sid entry p))
         (add-snapshot-id sid (snapshot-ids p)))
  :hints (("Goal"
           :in-theory (enable install-snapshot-entry))))

(defthm snapshot-ids-of-set-counter
  (equal (snapshot-ids (s :counter val p))
         (snapshot-ids p)))

(defthm memberp-snapshot-id-of-g-f2-preserve
  (implies
   (memberp old-sid
            (snapshot-ids (g k procs)))
   (memberp old-sid
            (snapshot-ids (g k (f2 procs input)))))
  :hints
  (("Goal"
    :in-theory (enable f2)
    :cases ((equal k (pid input))))))



(defthm some-proc-has-snapshot-id-p-of-f2-preserve
  (implies
   (some-proc-has-snapshot-id-p sid ids procs)
   (some-proc-has-snapshot-id-p sid ids (f2 procs input)))
  :hints
  (("Goal"
    :induct (some-proc-has-snapshot-id-p sid ids procs))
   ("Subgoal *1/2"
    :use ((:instance memberp-snapshot-id-of-g-f2-preserve
                     (old-sid sid)
                     (k (car ids))
                     (procs procs)
                     (input input))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; f2 preserves goodness of one existing message
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-msg-p-of-f2-procs
  (implies
   (good-msg-p msg ids procs)
   (good-msg-p msg ids (f2 procs input)))
  :hints
  (("Goal"
    :in-theory (enable good-msg-p)
    :use ((:instance some-proc-has-snapshot-id-p-of-f2-preserve
                     (sid (sid msg))
                     (ids ids)
                     (procs procs)
                     (input input)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; f2 preserves goodness of an existing message list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-msg-list-p-of-f2-procs
  (implies
   (good-msg-list-p msgs ids procs)
   (good-msg-list-p msgs ids (f2 procs input)))
  :hints
  (("Goal"
    :induct (good-msg-list-p msgs ids procs)
    :in-theory (disable f2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; f2 does not change nbrs-to
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm nbrs-to-of-install-snapshot-entry
  (equal (nbrs-to (install-snapshot-entry sid entry p))
         (nbrs-to p))
  :hints (("Goal"
           :in-theory (enable install-snapshot-entry))))

(defthm nbrs-to-of-set-counter
  (equal (nbrs-to (s :counter val p))
         (nbrs-to p)))

(defthm nbrs-to-of-g-of-f2
  (equal (nbrs-to (g src (f2 procs input)))
         (nbrs-to (g src procs)))
  :hints
  (("Goal"
    :in-theory (enable f2)
    :cases ((equal src (pid input))))))



(defthm good-channel-p-of-f2-procs
  (implies
   (good-channel-p src dst channels ids procs)
   (good-channel-p src dst channels ids (f2 procs input)))
  :hints
  (("Goal"
    :in-theory (e/d (good-channel-p)
                    (f2
                     good-msg-list-p-of-f2-procs
                     nbrs-to-of-g-of-f2))
    :use ((:instance good-msg-list-p-of-f2-procs
                     (msgs (g src (g dst channels)))
                     (ids ids)
                     (procs procs)
                     (input input))

          (:instance nbrs-to-of-g-of-f2
                     (src src)
                     (procs procs)
                     (input input))))))



(defthm good-channel-row-p-of-f2-procs
  (implies
   (good-channel-row-p src dsts channels ids procs)
   (good-channel-row-p src dsts channels ids (f2 procs input)))
  :hints
  (("Goal"
    :induct (good-channel-row-p src dsts channels ids procs)
    :in-theory (disable f2
                        good-channel-p-of-f2-procs))))



(defthm good-channels-p-of-f2-procs
  (implies
   (good-channels-p srcs dsts channels ids procs)
   (good-channels-p srcs dsts channels ids (f2 procs input)))
    :hints
  (("Goal"
    :induct (good-channels-p src dsts channels ids procs)
    :in-theory (disable f2))))





(defthm good-msg-p-of-create-marker-message
  (implies (some-proc-has-snapshot-id-p sid ids procs)
           (good-msg-p (create-marker-message local-state sid)
                       ids
                       procs)))



(defthm good-channels-p-of-send-msg-all-outgoing-channels
  (implies
   (and (good-channels-p srcs dsts channels ids procs)
        (good-msg-p msg ids procs)
        (subset nbrs (nbrs-to (g i procs))))
   (good-channels-p
    srcs
    dsts
    (send-msg-all-outgoing-channels msg i nbrs channels)
    ids
    procs)))



(defthm good-channels-p-of-send-msg-all-outgoing-channels
  (implies
   (and (good-channels-p srcs dsts channels ids procs_1)
        (good-msg-p msg ids procs_2)
	(same-set-of-neibors procs_1 procs_2 ids)
	(snapshot-ids subset procs_1 procs_2)
        (subset nbrs (nbrs-to (g i procs))))
   (good-channels-p
    srcs
    dsts
    (send-msg-all-outgoing-channels msg i nbrs channels)
    ids
    procs_2)))







Goal'
(IMPLIES
 (AND (TRUE-LISTP (G :PROC-IDS ST))
      (UNIQUEP (G :PROC-IDS ST))
      (GOOD-PROCS-P (G :PROC-IDS ST)
                    (G :PROCS ST)
                    (G :PROC-IDS ST))
      (GOOD-CHANNELS-P (G :PROC-IDS ST)
                       (G :PROC-IDS ST)
                       (G :CHANNELS ST)
                       (G :PROC-IDS ST)
                       (G :PROCS ST))
      (EQUAL (G :TTYPE INPUT)
             :START-CHECKPOINT)
      (MEMBERP (G :PID INPUT)
               (G :PROC-IDS ST)))
 (GOOD-CHANNELS-P
  (G :PROC-IDS ST)
  (G :PROC-IDS ST)
  (SEND-MSG-ALL-OUTGOING-CHANNELS
       (CREATE-MARKER-MESSAGE
            (G :LOCAL-STATE (G (G :PID INPUT) (G :PROCS ST)))
            (LIST (G :PID INPUT)
                  (G :COUNTER (G (G :PID INPUT) (G :PROCS ST)))))
       (G :PID INPUT)
       (G :NBRS-TO (G (G :PID INPUT) (G :PROCS ST)))
       (G :CHANNELS ST))
  (G :PROC-IDS ST)
  (S
   (G :PID INPUT)
   (S
    :COUNTER
    (+ 1
       (G :COUNTER (G (G :PID INPUT) (G :PROCS ST))))
    (INSTALL-SNAPSHOT-ENTRY
       (LIST (G :PID INPUT)
             (G :COUNTER (G (G :PID INPUT) (G :PROCS ST))))
       (MAKE-SNAPSHOT-ENTRY (G :LOCAL-STATE (G (G :PID INPUT) (G :PROCS ST)))
                            (G :NBRS-FROM (G (G :PID INPUT) (G :PROCS ST)))
                            NIL)
       (G (G :PID INPUT) (G :PROCS ST))))
   (G :PROCS ST))))
