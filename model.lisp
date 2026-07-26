(in-package "ACL2")

;;   distributed-checkpointingh.lisp
;;   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

;; Author: Sandip Ray
;; Date: Tue May  6 09:10:58 2025

;; In this book, we formalize a version of the Chandy-Lamport distributed snapshot
;; protocol using ACL2.  The goal is to have a formalization of correctness in a
;; generic form applicable to *any* reasonable snapshot algorithm.  In order to be
;; able to show that the protocol is correct using this correctness criterion we
;; need to augment the protocol in certain ways which might be thought of as
;; "completion" of the protocol.

;; Effort Breakdown:

;; - I spent two hour on May 8, creating an abstract
;;   structure for the distribued protocol.  The key reason
;;   for the time it took was an initial simplification I
;;   was trying to make, which was to associate incoming
;;   channel with each process.  However, that seemed wrong
;;   eventually, since a process as to have incoming
;;   channels corresponding to multiple processes, which
;;   ultimately made me change the channel into a 2-D array
;;   indexed by process indices i and j (indicating a
;;   channel from i to j).


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Generic functions and their properties                    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I define memberp and subset below, merely because I hate the fact that the
;; Lisp member function does not return a Boolean.  

(defun memberp (e l)
  (cond ((endp l) nil)
        ((equal e (first l)) t)
        (t (memberp e (rest l)))))


(defun subset (x y) 
  (cond ((endp x) t)
        (t (and (memberp (first x) y)
                (subset (rest x) y)))))


(defun uniquep (x)
  (if (endp x) t
    (and (not (memberp (first x) (rest x)))
         (uniquep (rest x)))))


(defun rev1 (x)
  (if (endp x)
      nil
    (append (rev1 (rest x))
            (list (first x)))))


(defun add-to-set-equal1 (x xs)
  (if (memberp x xs)
      xs
    (cons x xs)))

;; The function snoc adds an element at the "end" of a list.  The reason for
;; the name should be rather obvious.

(defun snoc (x e) 
  (if (endp x) (list e)
    (cons (first x) (snoc (rest x) e))))


;;the following function removes all occurences of item e from a list x

(defun remove-from-list (x e)
  (if (endp x)
      nil
    (if (equal e (first x))
        (remove-from-list (rest x) e)
      (cons (first x)
            (remove-from-list (rest x) e)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2: Auxiliary macros and functions for access and updates
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; I use the records book, principally so that I don't have to deal with
;; hypothesis on "well-formedness" of the state structure.  I hate to write
;; such hypothesis and carry along with the invariants that such structure is
;; preserved.  In this section I also build the macros I'm going to use for
;; access and updates to the different state components.

(include-book "misc/records" :dir :system)

;; The system state is given by (1) the state of all the processes, (2) the
;; state of the stable storage corresponding to all the processes, and (3) the
;; state of the communication channels.  For this level of formalization I don't
;; care that much whether the channel is a message passing interface or shared
;; memory.  I'll just call everything the channel.

;; I may add more components to the state.  If I do, I will
;; add them here.

(defmacro procs     (s) `(g :procs ,s))
(defmacro channels  (s) `(g :channels ,s))
(defmacro proc-ids  (s) `(g :proc-ids ,s)) ;list of process-ids

;; A process will have a local state, some outgoing
;; channels, and some incoming channels.  I feel that when
;; we start modeling the protocol we will need to put more
;; stuff, like a place for its stable snapshot.  But for
;; now, this is sufficient.  The way I am modeling channels
;; is as a 2D array (or record).  chans[i][j] (which I model
;; as (g i (g j chans)) gives me th channel from index i to
;; index j.

(defmacro local-state           (p) `(g :local-state ,p))
(defmacro channel-state (i j chans) `(g ,i (g ,j ,chans)))

;; Neighbor lists are STORED in each process record.
(defmacro nbrs-to               (p) `(g :nbrs-to ,p))
(defmacro nbrs-from             (p) `(g :nbrs-from ,p))

;; For a distributed system with checkpointing, the input
;; will need to specify which transition etc.

(defmacro pid   (input) `(g :pid ,input))
(defmacro ttype (input) `(g :ttype ,input))
(defmacro sender (input) `(g :sender ,input))

;; We also need to write an "update" macro.  That will be really important in
;; order for us to succinctly model the protocol.

(defun update-macro (upds result)
  (declare (xargs :guard (keyword-value-listp upds)))
  (if (endp upds) result
    (update-macro (cddr upds)
                  (list 's (car upds) (cadr upds) result))))

(defmacro update (old &rest updates)
  (declare (xargs :guard (keyword-value-listp updates)))
  (update-macro updates old))

(defmacro >st (&rest upds) `(update st ,@upds))
(defmacro >p  (&rest upds) `(update p  ,@upds))
(defmacro >_ (&rest upds) `(update nil ,@upds))

;; (defmacro >channel (i j val channels) `(s ,i (s ,j ,val ,channels) ,channels))

(defmacro >channel (i j val channels)
  `(s ,j
      (s ,i ,val (g ,j ,channels))
      ,channels))

(defmacro append-to-record-list (key val record)
  `(let* ((existing (g ,key ,record))
          (updated (append existing (list ,val))))
     (s ,key updated ,record)))

;; Each process can be in :normal, :crashed or :recovering state. We keep checkpointing 
;; separate from process status. Checkpointing status is kept in the snapshot records

(defmacro proc-status           (p) `(g :proc-status ,p))
(defmacro waiting-recovery-from (p) `(g :waiting-recovery-from ,p))
(defmacro counter               (p) `(g :counter ,p))

;; ------------------------------------------------------------------
;; Snapshot bookkeeping: accessors, entry structure, and update helpers
;;
;; This block defines the basic interface for managing per-process
;; snapshot state.  Each process keeps:
;;   (1) a list of snapshot ids currently known to it, and
;;   (2) a table mapping each snapshot id to its corresponding
;;       snapshot entry.
;;
;; A snapshot entry stores all information associated with one
;; checkpoint instance:
;;   - :status               = current progress of the snapshot
;;                             (e.g., :checkpointing or :done)
;;   - :local-snap-shot      = saved local state of the process
;;   - :channel-snapshots    = recorded in-transit messages for
;;                             incoming channels
;;   - :waiting-marker-from  = incoming neighbors from which a
;;                             marker is still expected
;;
;; The macros below provide convenient access to snapshot-related
;; fields in process records, message records, and snapshot entries.
;; The functions then build and maintain this snapshot structure:
;;   - make-snapshot-entry      creates a fresh entry for a new snapshot
;;   - add-snapshot-id          adds a snapshot id if not already present
;;   - set-snapshot-entry       stores an entry under a given snapshot id
;;   - install-snapshot-entry   updates both the id list and snapshot table
;;   - update-snapshot-entry    edits an existing snapshot entry in place
;;
;; In short, this block organizes how snapshot metadata is represented,
;; created, looked up, and updated during checkpointing and recovery.
;; ------------------------------------------------------------------

;; Get the list of snapshot ids currently tracked by a process.
(defmacro snapshot-ids          (p) `(g :snapshot-ids ,p))

;; Get the snapshot table/map from a process record.
(defmacro snapshots             (p) `(g :snapshots ,p))

;; Look up the snapshot entry for snapshot id sid in process p.
(defmacro snapshot-entry    (sid p) `(g ,sid (snapshots ,p)))


;; Extract snapshot id from a message record. applicable for marker & recovery msgs
(defmacro sid (msg) `(g :sid ,msg))

;;msg type, :normal, :marker, :recovery
(defmacro msg-type (msg) `(g :msg-type ,msg))


;; Read the status field from a snapshot entry.
(defmacro snapshot-status (entry)
  `(g :status ,entry))

;; Read the saved local snapshot from a snapshot entry.
(defmacro snapshot-local-snap-shot (entry)
  `(g :local-snap-shot ,entry))

;; Read the per-channel snapshot record from a snapshot entry.
(defmacro snapshot-channel-snapshots (entry)
  `(g :channel-snapshots ,entry))


;; Read the list of incoming channels still waiting for a marker.
(defmacro snapshot-waiting-marker-from (entry)
  `(g :waiting-marker-from ,entry))

;; Convenience macro to update fields of a local variable named entry.
(defmacro >entry (&rest upds)
  `(update entry ,@upds))


;; Create a fresh snapshot entry.
;; local-snap-shot      = saved local state
;; waiting-marker-from  = incoming channels still waiting for marker arrival
;; j                    = channel that delivered the first marker;
;;                        if j is nil, initialize with no channel entry yet
;;                        which is applicable for the process who started checkpointing
(defun make-snapshot-entry (local-snap-shot waiting-marker-from j)
  (let ((cs (if j
                (s j nil nil)   ;; explicit empty snapshot for channel j
              nil)))
    (>_ :status :checkpointing
        :local-snap-shot local-snap-shot
        :channel-snapshots cs
        :waiting-marker-from waiting-marker-from)))

;; Add sid to the snapshot-id list if it is not already present.
(defun add-snapshot-id (sid ids)
  (if (memberp sid ids)
      ids
    (cons  sid ids)))

;; Store a snapshot entry under sid in process p.
(defun set-snapshot-entry (sid entry p)
  (let* ((snaps (snapshots p))
         (snaps (s sid entry snaps)))
    (s :snapshots snaps p)))

;; Install a new snapshot entry and register its sid in the process.
(defun install-snapshot-entry (sid entry p)
  (let* ((snapshot-ids   (add-snapshot-id sid (snapshot-ids p)))
         (snapshots (snapshots p))
         (snapshots (s sid entry snapshots)))
    (update p
            :snapshot-ids snapshot-ids
            :snapshots snapshots)))

;; Update selected fields of the snapshot entry for sid in process p.
(defmacro update-snapshot-entry (sid p &rest upds)
  `(let* ((entry (snapshot-entry ,sid ,p))
          (entry (update entry ,@upds)))
     (set-snapshot-entry ,sid entry ,p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: Stubbed Functions and other constraints
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I am defining the neighbors of the process of index i in
;; procs.  I will likely need to have some conditions, like
;; the neighbors graph is connected.  And I will add that to
;; the constraints in the function.  The idea of the
;; neighbors is to think about which processes I can send
;; the message to. If some process is in the nbrs list for
;; me then I will send a message to it, and append it to its
;; incoming channel.  By modeling this way I avoid having
;; the deal with outgoing and incoming channels separately. 

;; (encapsulate
;;  (((make-nbrs-to * *) => *)
;;   ((make-nbrs-from * *) => *))
 
;;   (local (defun make-nbrs-to (i proc-ids) (declare (ignore i proc-ids)) nil))
;;   (local (defun make-nbrs-from (i proc-ids) (declare (ignore i proc-ids)) nil)))


;; The following protocol-dependent operations could have been introduced
;; with defstub, but we use encapsulate instead so that their argument
;; structure is explicit and easy to inspect.
;;
;; These functions represent the abstract application behavior that is
;; layered underneath the checkpointing/recovery protocol.  During normal
;; execution, a process evolves in two conceptually different ways:
;;
;;   1. Local computation without receiving a message.
;;   2. State update caused by receiving a message from a neighbor.
;;
;; For that reason we keep two separate local-state update functions:
;;
;;   - update-local-state-normal:
;;       models an internal/local transition of the process during an
;;       ordinary step when no message is being received. But a process
;;       may send a send a msg.
;;
;;   - update-local-state-rcv:
;;       models the state transition caused by consuming a message from
;;       neighbor nbr.
;;
;; In addition, a process may choose to send messages to only some of its
;; outgoing neighbors during a normal step.  The predicate
;; message-to-send? determines whether a message should be sent on a given
;; outgoing channel, and create-compute-message constructs that ordinary
;; application-level message.
;;
;; The checkpointing protocol itself also introduces two special control
;; messages:
;;
;;   - create-marker-message:
;;       constructs the marker used to propagate snapshot initiation.
;;
;;   - create-recovery-message:
;;       constructs the recovery message used to coordinate rollback.
;;

(encapsulate
 (((update-local-state-rcv * * *) => *)
  ((update-local-state-normal *) => *)
  ((message-to-send? * *) => *)
  ((create-compute-message * *) => *))

 (local
  (defun update-local-state-rcv (local-state msg nbr)
    (declare (ignore local-state msg nbr))
    nil))

 (local
  (defun update-local-state-normal (local-state)
    (declare (ignore local-state))
    nil))

 (local
  (defun message-to-send? (local-state nbr)
    (declare (ignore local-state nbr))
    nil))

 (local
  (defun create-compute-message (local-state nbr)
    (declare (ignore local-state nbr))
    (>_ :msg-type :normal)))

 (defthm msg-type-of-create-compute-message
   (equal (msg-type (create-compute-message local-state nbr))
          :normal)))


(defun create-marker-message (local-state sid)
  (declare (ignore local-state))
  (>_ :msg-type :marker
      :sid sid))

(defun create-recovery-message (local-state sid)
  (declare (ignore local-state))
  (>_ :msg-type :recovery
      :sid sid))

(defthm msg-type-of-create-marker-message
  (equal (msg-type (create-marker-message local-state sid))
         :marker))

(defthm sid-of-create-marker-message
  (equal (sid (create-marker-message local-state sid))
         sid))

(defthm msg-type-of-create-recovery-message
  (equal (msg-type (create-recovery-message local-state sid))
         :recovery))

(defthm sid-of-create-recovery-message
  (equal (sid (create-recovery-message local-state sid))
         sid))

;; ------------------------------------------------------------------
;; Channel update and marker-handling logic
;;
;; This block contains the core operations used to propagate and process
;; snapshot marker messages.
;;
;; First, we define basic channel manipulation utilities:
;;   - remove-message-from-channel removes the head message from an
;;     incoming channel after that message has been consumed.
;;   - send-msg-all-outgoing-channels appends the same message to all
;;     outgoing channels in a given neighbor list.
;;
;; Next, we define the handling of marker messages for the checkpoint
;; protocol.  A marker message for snapshot id sid can arrive at a
;; process either as the first marker seen for that snapshot, or as a
;; later marker on another incoming channel.
;;
;;   - handle-first-marker-msg:
;;       This is the case where process i sees sid for the first time.
;;       The process records its current local state as the snapshot,
;;       initializes the set of incoming channels still waiting for a
;;       marker, removes j from that set because j has already delivered
;;       the first marker, installs the new snapshot entry, forwards the
;;       marker on all outgoing channels, and removes the received marker
;;       from channel j -> i.
;;
;;   - handle-non-first-marker-msg:
;;       This handles later marker arrivals for an already known snapshot.
;;       The process simply marks channel j as having delivered its marker,
;;       updates the waiting-marker-from set, and changes the snapshot
;;       status to :done once markers have been received on all incoming
;;       channels.  It also removes the marker message from channel j -> i.
;;
;;   - handle-marker-msg:
;;       This dispatcher checks whether sid is already present in the
;;       process's snapshot-id list.  If not, the marker is treated as
;;       the first one for that snapshot; otherwise it is treated as a
;;       subsequent marker.
;;
;; So the organization is:
;;   channel utilities -> first-marker handling -> later-marker handling
;;   -> dispatch based on whether the snapshot id is already known.
;; ------------------------------------------------------------------

;; Remove the first msg from a incoming channel and return channels
(defun remove-message-from-channel (nbr i channels)
    (let* ((channel (channel-state nbr i channels))
           (channel (if channel (cdr channel) nil))
           (channels (>channel nbr i  channel channels)))
      channels))


; Send msg along all outgoing channels in nbrs.
(defun send-msg-all-outgoing-channels (msg i nbrs channels)
  (cond ((endp nbrs) channels)
        (t
         (let* ((nbr      (first nbrs))
                (channels (send-msg-all-outgoing-channels msg i (rest nbrs) channels))
                (channel  (channel-state i nbr channels))
                (channel  (snoc channel msg))
                (channels (>channel i nbr channel channels)))
           channels))))

(defun update-proc-for-first-marker-msg (p sid j)
  (let* ((nbrs-from           (nbrs-from p))
         (local-state         (local-state p))
         ;; For this snapshot id, wait for markers from all incoming
         ;; channels except j, because j already delivered the first marker.
         (waiting-marker-from (remove-from-list nbrs-from j))
         ;; Create and install the fresh snapshot entry.
         (entry               (make-snapshot-entry local-state
                                                   waiting-marker-from
                                                   j)))
    (install-snapshot-entry sid entry p)))

(defun handle-first-marker-msg (st i j msg)
  (let* ((procs    (procs st))
         (p        (g i procs))
         (nbrs-to  (nbrs-to p))
         (channels (channels st))
         (sid      (sid msg))

         ;; Remove marker from incoming channel j -> i.
         (channels (remove-message-from-channel j i channels))

         ;; Update process i for the first marker of sid.
         (p        (update-proc-for-first-marker-msg p sid j))

         ;; Forward the marker on all outgoing channels of i.
         (channels (send-msg-all-outgoing-channels msg i nbrs-to channels))

         ;; Write updated process and channels back.
         (procs    (s i p procs)))
    (>st :procs procs
         :channels channels)))

(defun update-proc-for-non-first-marker-msg (p sid j)
  (let* ((entry               (snapshot-entry sid p))

         ;; Marker for channel j -> i has arrived, so stop waiting for j.
         (waiting-marker-from (snapshot-waiting-marker-from entry))
         (waiting-marker-from (remove-from-list waiting-marker-from j))

         ;; Snapshot is complete if no incoming markers remain.
         (status              (if (endp waiting-marker-from)
                                  :done
                                (snapshot-status entry)))

         ;; Update the snapshot entry for sid.
         (entry               (update entry
                                      :waiting-marker-from waiting-marker-from
                                      :status status)))
    (set-snapshot-entry sid entry p)))

(defun handle-non-first-marker-msg (st i j msg)
  (let* ((sid      (sid msg))
         (procs    (procs st))
         (p        (g i procs))
         (channels (channels st))

         ;; Update process i for a later marker of sid.
         (p        (update-proc-for-non-first-marker-msg p sid j))

         ;; Remove marker message itself from incoming channel j -> i.
         (channels (remove-message-from-channel j i channels))

         ;; Write updated process and channels back.
         (procs    (s i p procs)))
    (>st :procs procs
         :channels channels)))

(defun handle-marker-msg (st i j msg)
  (let* ((sid (sid msg))
         (procs (procs st))
         (p (g i procs))
         (snapshot-ids (snapshot-ids p)))
    (if (memberp sid snapshot-ids)
        (handle-non-first-marker-msg st i j msg)
      (handle-first-marker-msg st i j msg))))


;; ------------------------------------------------------------------
;; Recovery replay and recovery-message handling
;;
;; This block defines how a process restores its state during recovery
;; and how recovery messages are propagated through the system.
;;
;; The first two functions implement replay of the recorded snapshot
;; history.  When a process rolls back to a saved local snapshot, it
;; must also re-apply the in-transit messages that were recorded for
;; that snapshot.
;;
;;   - replay-msgs-on-channel:
;;       replays the saved messages of one incoming channel, in their
;;       original order, by repeatedly applying update-local-state-rcv.
;;
;;   - replay-channel-snapshots:
;;       extends this replay across all incoming neighbors by fetching
;;       each channel's recorded message list from the snapshot entry
;;       and replaying them one channel at a time.
;;
;; The next functions handle recovery control messages.
;;
;;   - handle-first-recovery-msg:
;;       this is the first recovery message seen by process i.  The
;;       process restores its saved local snapshot for sid, replays the
;;       recorded incoming-channel messages, forwards the recovery
;;       message to all outgoing neighbors, removes the received message
;;       from channel j -> i, and enters :recovering mode.  It then
;;       waits for recovery messages from all other incoming neighbors.
;;
;;   - handle-non-first-recovery-msg:
;;       this handles later recovery messages while the process is
;;       already recovering.  In this case, no further rollback or
;;       replay is needed.  The process simply records that neighbor j
;;       has responded, removes the received message, and returns to
;;       :normal once all expected recovery messages have arrived.
;;
;;   - handle-recovery-msg:
;;       dispatches between the two cases above.  If the process is in
;;       :normal state, this must be the first recovery message;
;;       otherwise it is treated as a later one.
;;
;; So the organization is:
;;   replay saved snapshot traffic -> handle first recovery message ->
;;   handle later recovery messages -> dispatch by recovery status.
;; ---------------------------------------------------------------






;; (defun replay-msgs-on-channel (local-state msgs j)
;;   (cond ((endp msgs)
;;          local-state)
;;         (t
;;          (replay-msgs-on-channel
;;           (update-local-state-rcv local-state (first msgs) j)
;;           (rest msgs)
;;           j))))


(defun replay-msgs-on-channel (local-state msgs j)
  (cond ((endp msgs)
         local-state)

        ;; Match spec-step-rcv behavior:
        ;; if the receive finds no message, local state is unchanged.
        ((not (first msgs))
         (replay-msgs-on-channel
          local-state
          (rest msgs)
          j))

        (t
         (replay-msgs-on-channel
          (update-local-state-rcv local-state (first msgs) j)
          (rest msgs)
          j))))


(defun replay-channel-snapshots (local-state channel-snaps nbrs-from)
  (cond ((endp nbrs-from)
         local-state)
        (t
         (let* ((ch          (first nbrs-from))
                (msgs        (g ch channel-snaps))
                (local-state (replay-msgs-on-channel local-state msgs ch)))
           (replay-channel-snapshots local-state
                                     channel-snaps
                                     (rest nbrs-from))))))

(defun update-proc-for-first-recovery-msg (p sid j)
  (let* ((nbrs-from     (nbrs-from p))
         (entry         (snapshot-entry sid p))
         (local-state   (snapshot-local-snap-shot entry))
         (channel-snaps (snapshot-channel-snapshots entry))
         (local-state   (replay-channel-snapshots local-state
                                                  channel-snaps
                                                  nbrs-from))
         (waiting       (remove-from-list nbrs-from j)))
    (update p
            :local-state local-state
            :proc-status :recovering
            :waiting-recovery-from waiting)))

(defun handle-first-recovery-msg (st i j msg)
  (let* ((sid           (sid msg))
         (procs         (procs st))
         (channels      (channels st))
         (p             (g i procs))
         (nbrs-to       (nbrs-to p))

         ;; update channels
         (channels      (remove-message-from-channel j i channels))
         (channels      (send-msg-all-outgoing-channels msg i nbrs-to channels))

         ;; update process
         (p             (update-proc-for-first-recovery-msg p sid j))
         (procs         (s i p procs)))
    (>st :procs procs
         :channels channels)))

(defun update-proc-for-non-first-recovery-msg (p j)
  (let* ((waiting     (waiting-recovery-from p))
         (waiting     (remove-from-list waiting j))
         (proc-status (if (endp waiting)
                          :normal
                        :recovering)))
    (update p
            :proc-status proc-status
            :waiting-recovery-from waiting)))

(defun handle-non-first-recovery-msg (st i j msg)
  (declare (ignore msg))
  (let* ((procs    (procs st))
         (channels (channels st))
         (p        (g i procs))
         (channels (remove-message-from-channel j i channels))
         (p        (update-proc-for-non-first-recovery-msg p j))
         (procs    (s i p procs)))
    (>st :procs procs
         :channels channels)))

;; (defun handle-non-first-recovery-msg (st i j msg)
;;   (declare (ignore msg))
;;   (let* ((procs         (procs st))
;;          (channels      (channels st))
;;          (p             (g i procs))
;;          (waiting       (waiting-recovery-from p))
;;          (waiting       (remove-from-list waiting j))
;;          (proc-status   (if (endp waiting)
;;                             :normal
;;                           :recovering))
;;          (channels      (remove-message-from-channel j i channels))
;;          (p             (update p
;;                                 :proc-status proc-status
;;                                 :waiting-recovery-from waiting))
;;          (procs         (s i p procs)))
;;     (>st :procs procs
;;          :channels channels)))


(defun handle-recovery-msg (st i j msg)
  (let* ((procs       (procs st))
         (p           (g i procs))
         (proc-status (proc-status p)))
    (if (equal proc-status :normal)
        (handle-first-recovery-msg st i j msg)
	(handle-non-first-recovery-msg st i j msg))))

;; ------------------------------------------------------------------
;; Normal-message processing and snapshot recording
;;
;; This block defines how ordinary application messages are handled,
;; especially when checkpointing is in progress.
;;
;; The key issue is that, while a snapshot is still open, some incoming
;; messages may need to be recorded as part of the channel snapshot.
;; In particular, if a snapshot is currently :checkpointing and process i
;; is still waiting for the marker from channel j, then a normal message
;; arriving on j is considered in-transit for that snapshot and must be
;; appended to the saved message list for channel j.
;;
;;   - record-msg-in-snapshots:
;;       scans all snapshot ids currently tracked by the process and,
;;       for each active snapshot that is still waiting for marker j,
;;       records msg in that snapshot's per-channel message history.
;;
;; Once this recording rule is defined, ordinary message handling splits
;; into two cases.
;;
;;   - handle-normal-msg-core:
;;       this is the standard case.  The process consumes the message,
;;       updates its local state, records the message in any still-open
;;       snapshots where it counts as in-transit, removes the message
;;       from the incoming channel, and writes the updated process state
;;       back into the system state.
;;
;;   - ignore-normal-msg:
;;       this is used during recovery when process i is still waiting for
;;       a recovery message from sender j.  In that case, ordinary
;;       application messages from j are ignored and simply removed from
;;       the channel.
;;
;;   - handle-normal-msg:
;;       dispatches between the two behaviors above.  If the receiver is
;;       recovering and still waiting for j, the message is ignored;
;;       otherwise it is handled normally.
;; ------------------------------------------------------------------

(defun record-msg-in-snapshots (snapshots snapshot-ids j msg)
  (cond ((endp snapshot-ids)
         snapshots)
        (t
         (let* ((sid       (first snapshot-ids))
                (rest-ids  (rest snapshot-ids))
                (snapshots (record-msg-in-snapshots snapshots rest-ids j msg))
                (entry     (g sid snapshots))
                (status    (snapshot-status entry))
                (waiting   (snapshot-waiting-marker-from entry)))
           (if (and (equal status :checkpointing)
                    (memberp j waiting))
               (let* ((cs        (snapshot-channel-snapshots entry))
                      (cs        (append-to-record-list j msg cs))
                      (entry     (update entry :channel-snapshots cs))
                      (snapshots (s sid entry snapshots)))
                 snapshots)
               snapshots)))))

(defun update-proc-for-normal-msg-core (p j msg)
  (let* ((local-state  (local-state p))
         (local-state  (update-local-state-rcv local-state msg j))
         (snapshot-ids (snapshot-ids p))
         (snapshots    (snapshots p))
         (snapshots    (record-msg-in-snapshots snapshots
                                                snapshot-ids
                                                j
                                                msg)))
    (update p
            :local-state local-state
            :snapshots snapshots)))

(defun handle-normal-msg-core (st i j msg)
  (let* ((procs    (procs st))
         (channels (channels st))
         (p        (g i procs))
         ;; update receiver process local state and active snapshots
         (p        (update-proc-for-normal-msg-core p j msg))
         ;; remove consumed normal message from incoming channel j -> i
         (channels (remove-message-from-channel j i channels))
         ;; write updated process and channels back
         (procs    (s i p procs)))
    (>st :procs procs
         :channels channels)))

(defun ignore-normal-msg (st i j msg)
  (declare (ignore msg))
  (let* ((channels (channels st))
         (channels (remove-message-from-channel j i channels)))
    (>st :procs (procs st)
         :channels channels)))

(defun handle-normal-msg (st i j msg)
  (let* ((procs   (procs st))
         (p       (g i procs))
         (status  (proc-status p))
         (waiting (waiting-recovery-from p)))
    (if (and (equal status :recovering)
             (memberp j waiting))
        (ignore-normal-msg st i j msg)
	(handle-normal-msg-core st i j msg))))


;; ------------------------------------------------------------------
;; Receiving one message from an incoming channel
;;
;; This block provides the entry point for a receive step.
;;
;;   - get-msg-from-channel:
;;       reads the head message from the incoming channel nbr -> i
;;       without yet modifying the channel state.
;;
;;   - step-rcv:
;;       performs one receive transition for process i from sender j.
;;       It first fetches the message at the head of channel j -> i,
;;       examines its type, and then dispatches to the corresponding
;;       handler:
;;         :normal    -> ordinary application-message handling
;;         :marker    -> checkpoint marker handling
;;         :recovery  -> recovery-message handling
;;
;; Thus, this section separates message inspection from message-specific
;; processing, and serves as the main dispatcher for all receive events.
;; ------------------------------------------------------------------

(defun get-msg-from-channel (nbr i channels)
  (let ((channel (channel-state nbr i channels)))
    (if (consp channel)
        (first channel)
      nil)))

;; (defun step-rcv (st i j)
;;   (let* (
;;          (channels (channels st))
;; 	 (msg (get-msg-from-channel j i channels))
;; 	 (msg-type (msg-type msg)))
;; 	 (case msg-type
;; 	   (:normal   (handle-normal-msg st i j msg))
;; 	   (:marker   (handle-marker-msg st i j msg))
;; 	   (:recovery (handle-recovery-msg st i j msg))
;; 	   )))


(defun step-rcv (st i j)
  (let* ((channels (channels st))
         (msg      (get-msg-from-channel j i channels)))
    (if (not msg)
        st
      (let ((msg-type (msg-type msg)))
        (case msg-type
          (:normal   (handle-normal-msg st i j msg))
          (:marker   (handle-marker-msg st i j msg))
          (:recovery (handle-recovery-msg st i j msg))
          (otherwise st))))))

;; (defun step-rcv (st i j)
;;   (let* ((channels (channels st))
;;          (msg      (get-msg-from-channel j i channels))
;;          (msg-type (msg-type msg)))
;;     (case msg-type
;;       (:normal   (handle-normal-msg st i j msg))
;;       (:marker   (handle-marker-msg st i j msg))
;;       (:recovery (handle-recovery-msg st i j msg))
;;       (otherwise st))))

;; ------------------------------------------------------------------
;; Normal computation step and application-level message sending
;;
;; This block models ordinary process behavior outside the special
;; checkpointing and recovery control flow.
;;
;; A normal step has two parts:
;;   (1) the process may send ordinary application messages to some of
;;       its outgoing neighbors, and
;;   (2) it updates its own local state by taking an internal step.
;;
;; The messages sent here are "compute messages," meaning ordinary
;; application messages, as opposed to the marker and recovery messages
;; introduced by the checkpointing protocol itself.
;; ------------------------------------------------------------------


(defun send-compute-message (local-state i nbrs channels)
  (cond
   ((endp nbrs)
    channels)

   ((message-to-send? local-state (first nbrs))
    (let* ((nbr      (first nbrs))
           (channel  (channel-state i nbr channels))
           (msg      (create-compute-message local-state nbr))
           (channel  (snoc channel msg))
           (channels (>channel i nbr channel channels)))
      (send-compute-message local-state
                            i
                            (rest nbrs)
                            channels)))

   (t
    (send-compute-message local-state
                          i
                          (rest nbrs)
                          channels))))

(defun step-normal (st i)
(let* ((procs (procs st))
       (channels (channels st))
       (p (g i procs))
       (nbrs-to (nbrs-to p))
       (local (local-state p))
       (channels (send-compute-message local i nbrs-to channels))
       (local (update-local-state-normal local))
       (p     (>p  :local-state local))
       (procs (s i p procs))
       (st (>st :procs procs
         	:channels channels)))
       st))
 
;; ------------------------------------------------------------------
;; Start a new checkpoint at process i.
;;
;; A fresh snapshot id is created from the process id and its local
;; counter.  The current local state is saved as the local snapshot,
;; and the new snapshot entry is initialized to wait for marker
;; messages from all incoming neighbors.  The snapshot entry is then
;; installed in the process state, the counter is incremented for
;; future checkpoints, and a marker message for this snapshot is sent
;; on all outgoing channels.
;; ------------------------------------------------------------------

(defun start-checkpoint-helper (procs i)
  (let* ((p     (g i procs))
         (sid   (list i (counter p)))
         (entry (make-snapshot-entry
                 (local-state p)
                 (nbrs-from p)
                 nil))
         (p-new (s :counter
                   (+ 1 (counter p))
                   (install-snapshot-entry sid entry p))))
    (s i p-new procs)))

(defun step-checkpoint (st i)
  (let* ((procs       (procs st))
         (channels    (channels st))

         ;; Important: use the old process record here, before
         ;; start-checkpoint-procs increments the counter.
         (p           (g i procs))
         (sid         (list i (counter p)))
         (local-state (local-state p))
         (nbrs-to     (nbrs-to p))

         ;; First update the process table.
         (procs       (start-checkpoint-helper procs i))

         ;; Then send marker messages using the same sid.
         (msg         (create-marker-message local-state sid))
         (channels    (send-msg-all-outgoing-channels msg i nbrs-to channels))

         (st          (>st :procs procs
                           :channels channels)))
    st))


; Crash process i by setting its process status to :crashed.
(defun step-crash (st i)
  (let* ((procs (procs st))
         (p     (g i procs))
         (p     (update p :proc-status :crashed))
         (procs (s i p procs)))
    (>st :procs procs
         :channels (channels st))))

;; ------------------------------------------------------------------
;; Recover process i from its most recent completed snapshot.
;;
;; The process selects its latest saved snapshot id, restores the saved
;; local state from that snapshot, and replays the recorded in-transit
;; messages from all incoming channels.  It then creates a recovery
;; message for that snapshot and sends it on all outgoing channels.
;; Finally, the process enters :recovering mode and records that it is
;; waiting for recovery messages from all incoming neighbors.
;; ------------------------------------------------------------------

(defun recovery-local-state-after-replay (p)
  (let* ((nbrs-from     (nbrs-from p))
         (sid           (car (snapshot-ids p)))
         (entry         (snapshot-entry sid p))
         (local-state   (snapshot-local-snap-shot entry))
         (channel-snaps (snapshot-channel-snapshots entry)))
    (replay-channel-snapshots local-state
                              channel-snaps
                              nbrs-from)))

(defun start-recovery-helper (procs i)
  (let* ((p           (g i procs))
         (nbrs-from   (nbrs-from p))
         (local-state (recovery-local-state-after-replay p))
         (p-new       (update p
                              :local-state local-state
                              :proc-status :recovering
                              :waiting-recovery-from nbrs-from)))
    (s i p-new procs)))

(defun step-recover (st i)
  (let* ((procs         (procs st))
         (channels      (channels st))

         ;; Use old process record before updating procs.
         (p             (g i procs))
         (nbrs-to       (nbrs-to p))
         (sid           (car (snapshot-ids p)))
         (local-state   (recovery-local-state-after-replay p))

         ;; First update the process table.
         (procs         (start-recovery-helper procs i))

         ;; Then send recovery message using the same sid.
         (msg           (create-recovery-message local-state sid))
         (channels      (send-msg-all-outgoing-channels msg i nbrs-to channels))

         (st            (>st :procs procs
                             :channels channels)))
    st))


(defstub complete-this () => *)

(defun system-step (st input)
  (let* (
	 (i (pid input))
         (j (sender input))
         (ttype (ttype input)))
    (case ttype
      (:receive          (step-rcv st i j))
      (:normal           (step-normal st i))
      (:start-checkpoint (step-checkpoint st i))
      (:crash            (step-crash st i))
      (:recover          (step-recover st i))
      (:nop               st)
      (t st))))


;; ------------------------------------------------------------------
;; Specification-level step functions.
;;
;; These functions define the simpler specification semantics used for
;; comparison with the full checkpointing system. 
;;
;; - spec-step-rcv processes one received message by updating the local
;;   state of process i and removing the message from channel j -> i.
;;
;; - spec-step-normal performs one normal process step by sending any
;;   compute messages on outgoing channels and then updating the local
;;   state of process i.
;; ------------------------------------------------------------------

(defun spec-step-rcv (st i j)
  (let* ((channels (channels st))
         (msg      (get-msg-from-channel j i channels)))
    (if (not msg)
        st
      (let* ((procs       (procs st))
             (p           (g i procs))
             (local-state (local-state p))
             (local-state (update-local-state-rcv local-state msg j))
             (p           (update p :local-state local-state))
             (channels    (remove-message-from-channel j i channels))
             (procs       (s i p procs)))
        (>st :procs procs
             :channels channels)))))

;; (defun spec-step-rcv (st i j)
;;   (let* ((channels    (channels st))
;;          (msg         (get-msg-from-channel j i channels))
;;          (procs       (procs st))
;;          (p           (g i procs))
;;          (local-state (local-state p))
;;          (local-state (update-local-state-rcv local-state msg j))
;;          (p           (update p :local-state local-state))
;;          (channels    (remove-message-from-channel j i channels))
;;          (procs       (s i p procs)))
;;     (>st :procs procs
;;          :channels channels)))

(defun spec-step-normal (st i)
(let* ((procs (procs st))
       (channels (channels st))
       (p (g i procs))
       (nbrs-to (nbrs-to p))
       (local (local-state p))
       (channels (send-compute-message local i nbrs-to channels)) 
       (local (update-local-state-normal local))
       (p     (>p  :local-state local))
       (procs (s i p procs))
       (st (>st :procs procs
         	:channels channels)))
       st))

(defun spec-step (st input)
  (let* ((i     (pid input))
         (j     (sender input))
         (ttype (ttype input)))
    (case ttype
      (:receive   (spec-step-rcv st i j))
      (:normal    (spec-step-normal st i))
      (t st))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  run function
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun run-imp (st inputs)
  (if (endp inputs)
      st
    (run-imp
     (system-step st (first inputs))
     (rest inputs))))

(defun run-imp-trace (st inputs)
  (if (endp inputs)
      (list st)
    (cons st
          (run-imp-trace
           (system-step st (first inputs))
           (rest inputs)))))

(defun run-spec (st inputs)
  (if (endp inputs)
      st
    (run-spec
     (spec-step st (first inputs))
     (rest inputs))))

(defun run-spec-trace (st inputs)
  (if (endp inputs)
      (list st)
    (cons st
          (run-spec-trace
           (spec-step st (first inputs))
           (rest inputs)))))



;; ------------------------------------------------------------------
;; Predicates for global checkpointing/recovery status and input legality.
;;
;; This block defines a small hierarchy of predicates that inspect the
;; distributed system state at different levels.
;;
;; First, it checks whether a single process has any snapshot whose
;; status is still :checkpointing. It then lifts that check to the
;; whole system by scanning all process ids and asking whether any
;; process still has an unfinished snapshot. In parallel, it also
;; defines predicates that scan the process table to determine whether
;; any process is currently in :recovering status.
;;
;; These system-level predicates are then used to define legal-inputp,
;; which enforces simple protocol restrictions on the allowed next input.
;;
;; In particular:
;;   - a :crash input is illegal while the system is checkpointing
;;     or recovering,
;;   - a :start-checkpoint input is illegal while any process is
;;     recovering, and
;;   - a :recover input is illegal while any snapshot is still
;;     checkpointing.
;;
;; These restrictions rule out overlapping protocol phases that would
;; interfere with the intended checkpoint/recovery behavior.
;; ------------------------------------------------------------------

(defun any-checkpointing-snapshot-in-ids-p (snapshot-ids p)
  (cond ((endp snapshot-ids)
         nil)
        (t
         (let* ((sid   (first snapshot-ids))
                (entry (snapshot-entry sid p)))
           (or (equal (snapshot-status entry) :checkpointing)
               (any-checkpointing-snapshot-in-ids-p (rest snapshot-ids) p))))))

(defun proc-has-checkpointing-snapshot-p (p)
  (any-checkpointing-snapshot-in-ids-p (snapshot-ids p) p))

(defun any-proc-checkpointing-p (proc-ids procs)
  (cond ((endp proc-ids)
         nil)
        (t
         (let* ((pid (first proc-ids))
                (p   (g pid procs)))
           (or (proc-has-checkpointing-snapshot-p p)
               (any-proc-checkpointing-p (rest proc-ids) procs))))))

(defun any-snapshot-checkpointing-p (st)
  (let* ((ids   (proc-ids st))
         (procs (procs st)))
    (any-proc-checkpointing-p ids procs)))

(defun any-proc-recovering-p (proc-ids procs)
  (cond ((endp proc-ids)
         nil)
        (t
         (let* ((pid (first proc-ids))
                (p   (g pid procs)))
           (or (equal (proc-status p) :recovering)
               (any-proc-recovering-p (rest proc-ids) procs))))))

(defun any-process-recovering-p (st)
  (let* ((ids   (proc-ids st))
         (procs (procs st)))
    (any-proc-recovering-p ids procs)))


(defun some-proc-has-snapshot-id-p (sid ids procs)
  (if (endp ids)
      nil
    (let* ((i (first ids))
           (p (g i procs)))
      (or (memberp sid (snapshot-ids p))
          (some-proc-has-snapshot-id-p sid (rest ids) procs)))))

(defun all-procs-have-snapshot-id-p (sid ids procs)
  (if (endp ids)
      t
    (let* ((i (first ids))
           (p (g i procs)))
      (and (memberp sid (snapshot-ids p))
           (all-procs-have-snapshot-id-p sid (rest ids) procs)))))
 


(defun legal-inputp (st input)
  (let* ((tp    (ttype input))
         (i     (pid input))
         (j     (sender input))
         (ids   (proc-ids st))
         (procs (procs st)))
    (cond
     ((equal tp :nop)
      t)

     ;; Normal computation requires a valid process id.
     ((equal tp :normal)
      (memberp i ids))

     ;; A receive is legal only if:
     ;;   - receiver i is a valid process,
     ;;   - sender j is a valid process,
     ;;   - j is an incoming neighbor of i,
     ((equal tp :receive)
      (and
       (memberp i ids)
       (memberp j ids)
       (memberp j (nbrs-from (g i procs)))))

     ;; A checkpoint can start during normal execution or during another
     ;; checkpoint, but not while any process is recovering.
     ((equal tp :start-checkpoint)
      (and
       (memberp i ids)
       (not (any-process-recovering-p st))))

     ;; A crash is illegal during checkpointing or recovery.
     ((equal tp :crash)
      (and
       (memberp i ids)
       (not (any-process-recovering-p st))
       (not (any-snapshot-checkpointing-p st))))

     ;; A recovery is illegal during checkpointing or recovery.
     ;; In addition, the recovery sid must be known by every process,
     ;; because recovery messages may be forwarded.
     ((equal tp :recover)
      (and
       (memberp i ids)
      (not (any-process-recovering-p st))
      (not (any-snapshot-checkpointing-p st))
       (all-procs-have-snapshot-id-p
        (car (snapshot-ids (g i procs)))
        ids
        procs)
       )
      )

     ;; Unknown input types are not legal.
     (t
      nil))))



(defun legal-input-sequencep (st inputs)
  (declare (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      t
    (and (legal-inputp st (first inputs))
         (legal-input-sequencep
          (system-step st (first inputs))
          (rest inputs)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: Initial State Formation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Abstract process-id constructor

(encapsulate
 (((make-proc-ids) => *))

 (local
  (defun make-proc-ids ()
    '(0 1 2)))

 (defthm make-proc-ids-true-listp
   (true-listp (make-proc-ids)))

 (defthm make-proc-ids-uniquep
   (uniquep (make-proc-ids))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract neighbor constructors
;;
;; These construct the initial incoming/outgoing neighbor lists from a
;; process id and the full global process-id list.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate
 (((make-nbrs-to * *) => *)
  ((make-nbrs-from * *) => *))

 (local
  (defun make-nbrs-to (i proc-ids)
    (declare (ignore i proc-ids))
    nil))

 (local
  (defun make-nbrs-from (i proc-ids)
    (declare (ignore i proc-ids))
    nil))

 ;; Basic shape facts.
 (defthm make-nbrs-to-true-listp
   (true-listp (make-nbrs-to i proc-ids)))

 (defthm make-nbrs-from-true-listp
   (true-listp (make-nbrs-from i proc-ids)))

 (defthm make-nbrs-to-subset-of-proc-ids
   (subset (make-nbrs-to i proc-ids)
           proc-ids))

 (defthm make-nbrs-from-subset-of-proc-ids
   (subset (make-nbrs-from i proc-ids)
           proc-ids))

 ;; Direction 1:
 ;; If j is in i's incoming-neighbor list,
 ;; then i is in j's outgoing-neighbor list.
 (defthm make-nbrs-from-implies-make-nbrs-to
   (implies
    (and
     (memberp i proc-ids)
     (memberp j proc-ids)
     (memberp j (make-nbrs-from i proc-ids)))
    (memberp i (make-nbrs-to j proc-ids))))

 ;; Direction 2:
 ;; If i is in j's outgoing-neighbor list,
 ;; then j is in i's incoming-neighbor list.
 (defthm make-nbrs-to-implies-make-nbrs-from
   (implies
    (and
     (memberp i proc-ids)
     (memberp j proc-ids)
     (memberp i (make-nbrs-to j proc-ids)))
    (memberp j (make-nbrs-from i proc-ids)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract initial local-state constructor
;;
;; The application-specific local state remains abstract.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 (((make-init-local-state *) => *))

 (local
  (defun make-init-local-state (i)
    (declare (ignore i))
    nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Concrete construction of the initial process table
;;
;; Each process record stores:
;;   :local-state
;;   :nbrs-to
;;   :nbrs-from
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-one-proc (i all-ids)
  (>_ :local-state (make-init-local-state i)
      :nbrs-to     (make-nbrs-to i all-ids)
      :nbrs-from   (make-nbrs-from i all-ids)))

(defun make-procs-aux (ids all-ids)
  (if (endp ids)
      nil
    (let* ((i     (first ids))
           (p     (make-one-proc i all-ids))
           (procs (make-procs-aux (rest ids) all-ids)))
      (s i p procs))))

(defun make-procs (ids)
  (make-procs-aux ids ids))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Concrete construction of the initial channel table
;;
;; Channel table is a 2-D record:
;;   channel-state src dst channels
;;
;; Initially, every channel is empty (nil).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-channel-row (srcs)
  (if (endp srcs)
      nil
    (s (first srcs)
       nil
       (make-channel-row (rest srcs)))))

(defun make-channels-aux ( srcs dsts)
  (if (endp dsts)
      nil
    (s (first dsts)
       (make-channel-row srcs)
       (make-channels-aux srcs (rest dsts)))))

(defun make-channels (ids)
  (make-channels-aux ids ids))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Initial snapshot installation
;;
;; Snapshot id for the initial snapshot is :init.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-init-snapshot-entry (init-local-state)
  (>_ :status :done
      :local-snap-shot init-local-state
      :channel-snapshots nil
      :waiting-marker-from nil))

(defun install-initial-snapshot (p)
  (let* ((init-local   (local-state p))
         (entry        (make-init-snapshot-entry init-local))
         (snapshot-ids (add-snapshot-id :init nil))
         (snaps        (s :init entry nil)))
    (update p
            :proc-status :normal
            :waiting-recovery-from nil
            :counter 0
            :snapshot-ids snapshot-ids
            :snapshots snaps)))

(defun install-initial-snapshots (ids procs)
  (if (endp ids)
      procs
    (let* ((i     (first ids))
           (p     (g i procs))
           (p     (install-initial-snapshot p))
           (procs (s i p procs)))
      (install-initial-snapshots (rest ids) procs))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Initial implementation state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-initial-state ()
  (let* ((ids      (make-proc-ids))
         (procs    (make-procs ids))
         (channels (make-channels ids))
         (procs    (install-initial-snapshots ids procs)))
    (>_ :proc-ids ids
        :procs procs
        :channels channels)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Initial spec state
;;
;; Spec processes need only local-state / nbrs fields, so make-procs is
;; already sufficient here.  No initial snapshot installation is needed.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-initial-spec-state ()
  (let* ((ids      (make-proc-ids))
         (procs    (make-procs ids))
         (channels (make-channels ids)))
    (>_ :proc-ids ids
        :procs procs
        :channels channels)))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Channel projection for REP
;;
;; Implementation channels may contain:
;;   :normal
;;   :marker
;;   :recovery
;;
;; The spec should only see normal/application messages.
;; Therefore REP must project each implementation channel by removing
;; marker/recovery protocol messages and keeping only normal messages.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




(defun project-channel-msgs-to-spec (msgs)
  ;; Remove protocol messages from one implementation channel.
  ;; Keep only normal messages, preserving their order.
  (if (endp msgs)
      nil
    (if (equal (msg-type (first msgs)) :normal)
        (cons (first msgs)
              (project-channel-msgs-to-spec (rest msgs)))
      (project-channel-msgs-to-spec (rest msgs)))))


(defun project-channel-row-to-spec (srcs dst imp-channels)
  ;; Build one destination row of the spec channel table.
  ;;
  ;; For fixed DST, project every SRC -> DST channel.
  ;; Since channel-state src dst channels = (g src (g dst channels)),
  ;; the row stored under DST maps SRC keys to message lists.
  (if (endp srcs)
      nil
    (let* ((src       (first srcs))
           (msgs      (channel-state src dst imp-channels))
           (spec-msgs (project-channel-msgs-to-spec msgs))
           (row-rest  (project-channel-row-to-spec
                       (rest srcs)
                       dst
                       imp-channels)))
      (s src spec-msgs row-rest))))


(defun project-channels-to-spec-aux (dsts srcs imp-channels)
  ;; Build the full spec channel table.
  ;;
  ;; Outer keys are destination process ids.
  ;; Inner keys are source process ids.
  (if (endp dsts)
      nil
    (let* ((dst       (first dsts))
           (row       (project-channel-row-to-spec
                       srcs
                       dst
                       imp-channels))
           (rest-rows (project-channels-to-spec-aux
                       (rest dsts)
                       srcs
                       imp-channels)))
      (s dst row rest-rows))))


(defun project-channels-to-spec (ids imp-channels)
  ;; Project all channels over the known process ids.
  (project-channels-to-spec-aux ids ids imp-channels))


(defun map-proc-to-spec-proc (imp-p)
  ;; Project one implementation process record into a spec process record.
  ;; Keep only the fields needed by the spec.
  (>_ :local-state (local-state imp-p)
      :nbrs-to (nbrs-to imp-p)
      :nbrs-from (nbrs-from imp-p)))

(defun map-procs-to-spec-procs (ids imp-procs)
  ;; Build the full spec process table by projecting each
  ;; implementation process into its spec-level form.
  (if (endp ids)
      nil
    (let* ((i          (first ids))
           (imp-p      (g i imp-procs))
           (spec-p     (map-proc-to-spec-proc imp-p))
           (spec-procs (map-procs-to-spec-procs (rest ids) imp-procs)))
      (s i spec-p spec-procs))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Updated REP
;;
;; REP now:
;;   - preserves proc-ids,
;;   - projects each implementation process to spec process fields,
;;   - projects channels by removing marker/recovery messages.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rep (imp-st)
  (let* ((ids          (proc-ids imp-st))
         (imp-procs    (procs imp-st))
         (imp-channels (channels imp-st)))
    (>_ :proc-ids ids
        :procs
        (map-procs-to-spec-procs ids imp-procs)
        :channels
        (project-channels-to-spec ids imp-channels))))
