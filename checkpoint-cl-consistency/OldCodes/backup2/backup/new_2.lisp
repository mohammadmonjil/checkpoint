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

(defmacro proc-status           (p) `(g :proc-status ,p))

(defmacro waiting-recovery-from (p) `(g :waiting-recovery-from ,p))

(defmacro counter               (p) `(g :counter ,p))
 
;; Get the list of snapshot ids currently tracked by a process.
(defmacro snapshot-ids          (p) `(g :snapshot-ids ,p))

;; Get the snapshot table/map from a process record.
(defmacro snapshots             (p) `(g :snapshots ,p))

;; Look up the snapshot entry for snapshot id sid in process p.
(defmacro snapshot-entry    (sid p) `(g ,sid (snapshots ,p)))

(defmacro channel-state (i j chans) `(g ,i (g ,j ,chans)))


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

(defmacro >channel (i j val channels) `(s ,i (s ,j ,val ,channels) ,channels))

(defmacro append-to-record-list (key val record)
  `(let* ((existing (g ,key ,record))
          (updated (append existing (list ,val))))
     (s ,key updated ,record)))



;; Extract snapshot id from a message record.
(defmacro sid (msg)
  `(g :sid ,msg))
;;msg type
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
;; j                    = channel that already delivered the first marker;
;;                        if j is nil, initialize with no channel entry yet
(defun make-snapshot-entry (local-snap-shot waiting-marker-from j)
  (let ((cs (if j
                (append-to-record-list j nil nil)
              nil)))
    (>_ :status :checkpointing
        :local-snap-shot local-snap-shot
        :channel-snapshots cs
        :waiting-marker-from waiting-marker-from)))

;; Add sid to the snapshot-id list if it is not already present.
(defun add-snapshot-id (sid ids)
  (if (memberp sid ids)
      ids
    (snoc ids sid)))

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

(encapsulate
 (((nbrs-to * *) => *)
  ((nbrs-from * *) => *))
 
  (local (defun nbrs-to (i procs) (declare (ignore i procs)) nil))
  (local (defun nbrs-from (i procs) (declare (ignore i procs)) nil)))


;; The following can I guess just be defined as defstub.
;; But I did it as encapsulate, so that I can look up the
;; arguments and see what they are.

;; There are two things that a process does during normal
;; activity.  It computes the next local state and sends
;; messages (sometimes).  I permit a process to send
;; messages to a subset of neighbors.  My
;; send-compute-message function does that work.  

(encapsulate
 (((update-local-state-rcv * * *) => *)
  ((update-local-state-normal *) => *)
  ((message-to-send? * *) => *)
  ((create-compute-message * *) => *)
  ((create-marker-message * *) => *)
  ((create-recovery-message * *) => *))
 
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
    nil))
  
  (local
  (defun create-marker-message  (local-state sid)
    (declare (ignore local-state sid))
    nil))

  (local
  (defun create-recovery-message (local-state sid)
    (declare (ignore local-state sid))
    nil))
     )


;; Remove the first msg from a incoming channel and return channels
(defun remove-message-from-channel (i nbr channels)
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

(defun handle-first-marker-msg (st i j msg)
  (let* ((procs               (procs st))
         (p                   (g i procs))
         (nbrs-from           (nbrs-from i procs))
         (nbrs-to             (nbrs-to i procs))
         (local-state         (local-state p))
         (channels            (channels st))
         (sid                 (sid msg))

         ;; remove received marker from channel j -> i
         (channels            (remove-message-from-channel j i channels))

         ;; for this snapshot-id, wait for markers from all incoming channels except j
         (waiting-marker-from (remove-from-list nbrs-from j))

         ;; create and install fresh snapshot entry for sid
         (entry               (make-snapshot-entry local-state waiting-marker-from j))
         (p                   (install-snapshot-entry sid entry p))

         ;; send marker for this sid on all outgoing channels
         (channels            (send-msg-all-outgoing-channels msg i nbrs-to channels))

         (procs               (s i p procs))
         (st                  (>st :procs procs
                                   :channels channels)))
    st))


(defun handle-non-first-marker-msg (st i j msg)
  (let* ((sid                 (sid msg))
         (procs               (procs st))
         (p                   (g i procs))
         (entry               (snapshot-entry sid p))

         ;; marker for channel j -> i has arrived, so stop waiting for j
         (waiting-marker-from (snapshot-waiting-marker-from entry))
         (waiting-marker-from (remove-from-list waiting-marker-from j))

         ;; snapshot is complete if no incoming markers remain
         (status              (if (endp waiting-marker-from)
                                  :done
                                (snapshot-status entry)))

         (entry               (update entry
                                      :waiting-marker-from waiting-marker-from
                                      :status status))
         (p                   (set-snapshot-entry sid entry p))

         ;; remove marker message itself from incoming channel j -> i
         (channels            (channels st))
         (channels            (remove-message-from-channel j i channels))
         (procs               (s i p procs))
         (st                  (>st :procs procs
                                   :channels channels)))
    st))



(defun handle-marker-msg (st i j msg)
  (let* ((sid (sid msg))
         (procs (procs st))
         (p (g i procs))
         (snapshot-ids (snapshot-ids p)))
    (if (memberp sid snapshot-ids)
        (handle-non-first-marker-msg st i j msg)
      (handle-first-marker-msg st i j msg))))


; Replay the recorded messages of one incoming channel in original order.
; msgs is the list of messages saved for channel j in the snapshot.
; Each message is applied to local-state using update-local-state.
(defun replay-msgs-on-channel (local-state msgs j)
  (cond ((endp msgs)
         local-state)
        (t
         (replay-msgs-on-channel
          (update-local-state-rcv local-state (first msgs) j)
          (rest msgs)
          j))))

; Replay the recorded channel snapshots for all incoming neighbors.
; For each incoming channel in nbrs-from, fetch its saved message list
; from channel-snaps and replay those messages into local-state.
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


; Handle the first recovery message received by process i.
; The recovery message carries a snapshot id sid.
; Process i restores its saved local snapshot for sid, replays the
; recorded in-transit messages from all incoming channels, forwards
; the same recovery message to all outgoing neighbors, removes the
; received recovery message from channel j->i, and enters recovering mode.
; It initializes :waiting-recovery-from to all incoming neighbors except j,
; since j has already delivered its recovery message.

(defun handle-first-recovery-msg (st i j msg)
  (let* ((sid           (sid msg))
         (procs         (procs st))
         (channels      (channels st))
         (p             (g i procs))
         (nbrs-from     (nbrs-from i procs))
         (nbrs-to       (nbrs-to i procs))
         (entry         (snapshot-entry sid p))
         (local-state   (snapshot-local-snap-shot entry))
         (channel-snaps (snapshot-channel-snapshots entry))
         (local-state   (replay-channel-snapshots local-state
                                                  channel-snaps
                                                  nbrs-from))
         (waiting       (remove-from-list nbrs-from j))
         (channels      (remove-message-from-channel j i channels))
         (channels      (send-msg-all-outgoing-channels msg i nbrs-to channels))
         (p             (update p
                                :local-state local-state
                                :proc-status :recovering
                                :waiting-recovery-from waiting))
         (procs         (s i p procs)))
    (>st :procs procs
         :channels channels)))


; Handle a non-first recovery message received by process i.
; Since process i is already in recovering mode, there is no need to
; restore the snapshot or replay saved messages again.
; We simply remove the received message from channel j->i, mark that
; channel j has responded by removing it from :waiting-recovery-from,
; and if no channels remain, return the process to normal mode.
(defun handle-non-first-recovery-msg (st i j msg)
  (declare (ignore msg))
  (let* ((procs         (procs st))
         (channels      (channels st))
         (p             (g i procs))
         (waiting       (waiting-recovery-from p))
         (waiting       (remove-from-list waiting j))
         (proc-status   (if (endp waiting)
                            :normal
                          :recovering))
         (channels      (remove-message-from-channel j i channels))
         (p             (update p
                                :proc-status proc-status
                                :waiting-recovery-from waiting))
         (procs         (s i p procs)))
    (>st :procs procs
         :channels channels)))


(defun handle-recovery-msg (st i j msg)
  (let* ((procs       (procs st))
         (p           (g i procs))
         (proc-status (proc-status p)))
    (if (equal proc-status :normal)
        (handle-first-recovery-msg st i j msg)
	(handle-non-first-recovery-msg st i j msg))))

; Record a newly received normal message msg from channel j in every
; active snapshot that is still waiting for a marker on j.
; For each snapshot id in snapshot-ids:
;   - if the snapshot status is :checkpointing, and
;   - if j is still in its waiting-marker-from list,
; then append msg to the saved message list for channel j in that snapshot.
; Otherwise leave that snapshot unchanged.

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



; Process a normal application message in the usual way:
; update local state, record the message in any active snapshots,
; remove the message from the channel, and update the state.
(defun handle-normal-msg-core (st i j msg)
  (let* ((procs        (procs st))
         (p            (g i procs))
         (local-state  (local-state p))
         (local-state  (update-local-state-rcv local-state msg j))
         (snapshot-ids (snapshot-ids p))
         (snapshots    (snapshots p))
         (snapshots    (record-msg-in-snapshots snapshots snapshot-ids j msg))
         (p            (update p
                               :local-state local-state
                               :snapshots snapshots))
         (channels     (channels st))
         (channels     (remove-message-from-channel i j channels))
         (procs        (s i p procs)))
    (>st :procs procs
         :channels channels)))

; Ignore a normal message by simply removing it from the channel.
; This is used when the receiver is recovering and is still waiting
; for a recovery message from the sender j.
(defun ignore-normal-msg (st i j msg)
  (declare (ignore msg))
  (let* ((channels (channels st))
         (channels (remove-message-from-channel i j channels)))
    (>st :procs (procs st)
         :channels channels)))

; Handle a normal message.
; If process i is recovering and is still waiting for recovery from j,
; then ignore the message.  Otherwise process it as a normal message.
(defun handle-normal-msg (st i j msg)
  (let* ((procs   (procs st))
         (p       (g i procs))
         (status  (proc-status p))
         (waiting (waiting-recovery-from p)))
    (if (and (equal status :recovering)
             (memberp j waiting))
        (ignore-normal-msg st i j msg)
	(handle-normal-msg-core st i j msg))))




;; Get the first msg from a incoming channel
(defun get-msg-from-channel (i nbr channels)
  (let* ((channel (channel-state nbr i channels))
	 (msg (first channel)))
    msg))

(defun step-rcv (st i j)
  (let* (
         (channels (channels st))
	 (msg (get-msg-from-channel i j channels))
	 (msg-type (msg-type msg)))
	 (case msg-type
	   (:normal   (handle-normal-msg st i j msg))
	   (:marker   (handle-marker-msg st i j msg))
	   (:recovery (handle-recovery-msg st i j msg))
	   )))


;; I am now define what it means to send a message. I am
;; calling it compute-message as opposeed to the recovery or
;; marker messages involved in the Chandy-Lamport protocol.

(defun send-compute-message (local-state i nbrs channels)
  (cond ((endp nbrs) channels)
        ((message-to-send? local-state (first nbrs))
         (let*
             ((nbr (first nbrs))
              (channel (channel-state i nbr channels))
              (msg (create-compute-message local-state nbr))
              (channel (snoc channel msg))
              (channels (>channel i nbr channel channels)))
           channels))
        (t (send-compute-message local-state i (rest nbrs) channels))))


(defun step-normal (st i)
(let* ((procs (procs st))
       (channels (channels st))
       (p (g i procs))
       (nbrs-to (nbrs-to i procs))
       (local (local-state p))
       (channels (send-compute-message local i nbrs-to channels)) ;; send compute messages along outgoing channels
       (local (update-local-state-normal local))
       (p     (>p  :local-state local))
       (procs (s i p procs))
       (st (>st :procs procs
         	:channels channels)))
       st))
 
; Initiate a new checkpoint at process i.
; Create a fresh snapshot id from process i and its local counter,
; save the current local state in a new snapshot entry, initialize
; waiting-marker-from to all incoming neighbors, increment the local
; counter, and send a marker message on all outgoing channels.

(defun step-checkpoint (st i)
  (let* ((procs               (procs st))
         (channels            (channels st))
         (p                   (g i procs))
         (nbrs-to             (nbrs-to i procs))
         (nbrs-from           (nbrs-from i procs))
         (local-state         (local-state p))
         (ctr                 (counter p))

         ;; snapshot id = (process-id counter)
         (sid                 (list i ctr))

         ;; initiator waits for markers from all incoming channels
         (waiting-marker-from nbrs-from)

         ;; install snapshot entry for this sid
         (entry               (make-snapshot-entry local-state waiting-marker-from nil))
         (p                   (install-snapshot-entry sid entry p))

         ;; increment counter for future snapshots
         (p                   (update p :counter (+ 1 ctr)))

         ;; send marker on all outgoing channels
         (msg                 (create-marker-message local-state sid))
         (channels            (send-msg-all-outgoing-channels msg i nbrs-to channels))

         (procs               (s i p procs))
         (st                  (>st :procs procs
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

; Recover process i from the most recent completed snapshot.
; We assume that all snapshot ids in (snapshot-ids p) are completed
; when recovery is initiated.  This function chooses the last snapshot
; id, restores the saved local snapshot, replays the recorded incoming-
; channel messages from that snapshot, creates a recovery message, sends
; it on all outgoing channels, and moves the process into recovering mode.
(defun step-recover (st i)
  (let* ((procs         (procs st))
         (channels      (channels st))
         (p             (g i procs))
         (nbrs-from     (nbrs-from i procs))
         (nbrs-to       (nbrs-to i procs))

         ;; choose the most recent snapshot id
         (sid           (car (last (snapshot-ids p))))

         ;; restore saved snapshot state
         (entry         (snapshot-entry sid p))
         (local-state   (snapshot-local-snap-shot entry))
         (channel-snaps (snapshot-channel-snapshots entry))

         ;; replay recorded in-transit messages
         (local-state   (replay-channel-snapshots local-state
                                                  channel-snaps
                                                  nbrs-from))

         ;; create and send recovery message on all outgoing channels
         (msg           (create-recovery-message local-state sid))
         (channels      (send-msg-all-outgoing-channels msg i nbrs-to channels))

         ;; enter recovering mode and wait for recovery from all inputs
         (p             (update p
                                :local-state local-state
                                :proc-status :recovering
                                :waiting-recovery-from nbrs-from))
         (procs         (s i p procs)))
    (>st :procs procs
         :channels channels)))

(defstub complete-this () => *)




(defun checkpointing-distributed-system-step (st input)
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
      (t st))))


;; Return t if any snapshot id in snapshot-ids has status :checkpointing.
;; This scans the snapshot entries of a single process.
(defun any-checkpointing-snapshot-in-ids-p (snapshot-ids p)
  (cond ((endp snapshot-ids)
         nil)
        (t
         (let* ((sid   (first snapshot-ids))
                (entry (snapshot-entry sid p)))
           (or (equal (snapshot-status entry) :checkpointing)
               (any-checkpointing-snapshot-in-ids-p (rest snapshot-ids) p))))))

;; Return t if process p has at least one snapshot currently in
;; :checkpointing mode.
(defun proc-has-checkpointing-snapshot-p (p)
  (any-checkpointing-snapshot-in-ids-p (snapshot-ids p) p))

;; Return t if any process in proc-ids has a snapshot in
;; :checkpointing mode.
(defun any-proc-checkpointing-p (proc-ids procs)
  (cond ((endp proc-ids)
         nil)
        (t
         (let* ((pid (first proc-ids))
                (p   (g pid procs)))
           (or (proc-has-checkpointing-snapshot-p p)
               (any-proc-checkpointing-p (rest proc-ids) procs))))))

;; Return t if there exists any snapshot in any process that is still
;; in :checkpointing mode.
(defun any-snapshot-checkpointing-p (st)
  (let* ((ids   (proc-ids st))
         (procs (procs st)))
    (any-proc-checkpointing-p ids procs)))

;; Return t if any process in proc-ids is currently in :recovering status.
(defun any-proc-recovering-p (proc-ids procs)
  (cond ((endp proc-ids)
         nil)
        (t
         (let* ((pid (first proc-ids))
                (p   (g pid procs)))
           (or (equal (proc-status p) :recovering)
               (any-proc-recovering-p (rest proc-ids) procs))))))

;; Return t if there exists any process in the system whose
;; process status is :recovering.
(defun any-process-recovering-p (st)
  (let* ((ids   (proc-ids st))
         (procs (procs st)))
    (any-proc-recovering-p ids procs)))


; Check whether input is legal in state st.
; Restriction 1:
; During recovery or checkpointing, :crash is not allowed.

(defun legal-inputp (st input)
  (let ((ttype (ttype input)))
    (cond ((and (or (any-process-recovering-p st)
                    (any-snapshot-checkpointing-p st))
                (equal ttype :crash))
           nil)
          (t
           t))))



(defun spec-step-rcv (st i j)
  (let* ((channels    (channels st))
         (msg         (get-msg-from-channel i j channels))
         (procs       (procs st))
         (p           (g i procs))
         (local-state (local-state p))
         (local-state (update-local-state-rcv local-state msg j))
         (p           (update p :local-state local-state))
         (channels    (remove-message-from-channel i j channels))
         (procs       (s i p procs)))
    (>st :procs procs
         :channels channels)))


(defun spec-step-normal (st i)
(let* ((procs (procs st))
       (channels (channels st))
       (p (g i procs))
       (nbrs-to (nbrs-to i procs))
       (local (local-state p))
       (channels (send-compute-message local i nbrs-to channels)) ;; send compute messages along outgoing channels
       (local (update-local-state-normal local))
       (p     (>p  :local-state local))
       (procs (s i p procs))
       (st (>st :procs procs
         	:channels channels)))
       st))


;; List of past system states, with most recent state at the front.
(defmacro past-states (s)
  `(g :past-states ,s))

;; Read the fallback index from the input.
(defmacro index (input)
  `(g :index ,input))

;; Remove the history field from st before saving it into history.
(defun strip-past-states (st)
  (s :past-states nil st))

;; Save the current state into the history list.
;; The saved copy has its own :past-states field cleared.
(defun save-state-in-history (st)
  (let* ((hist (past-states st))
         (base (strip-past-states st))
         (hist (cons base hist)))
    (update st :past-states hist)))

;; Return the nth state in lst.
;; Index 0 means the most recently saved state.
(defun nth-state (n lst)
  (cond ((endp lst)
         nil)
        ((zp n)
         (first lst))
        (t
         (nth-state (- n 1) (rest lst)))))

;; Fall back to a previously saved state from history.
;; If the requested index is out of range, leave the state unchanged.
(defun spec-step-fall-back (st input)
  (let* ((n    (index input))
         (hist (past-states st))
         (old  (nth-state n hist)))
    (cond (old old)
          (t   st))))

(defun spec-checkpointing-distributed-system-step (st input)
  (let* ((st    (save-state-in-history st))
         (i     (pid input))
         (j     (sender input))
         (ttype (ttype input)))
    (case ttype
      (:receive   (spec-step-rcv st i j))
      (:normal    (spec-step-normal st i))
      (:fall-back (spec-step-fall-back st input))
      (t st))))
