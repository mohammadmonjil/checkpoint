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
      x
      (if (equal e (first x))
	  (remove-from-list (rest x) e)
	  (list (first x) (remove-from-list  (rest x) e)))))

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

;; A process will have a local state, some outgoing
;; channels, and some incoming channels.  I feel that when
;; we start modeling the protocol we will need to put more
;; stuff, like a place for its stable snapshot.  But for
;; now, this is sufficient.  The way I am modeling channels
;; is as a 2D array (or record).  chans[i][j] (which I model
;; as (g i (g j chans)) gives me th channel from index i to
;; index j.

(defmacro local-state        (p) `(g :local-state ,p))
(defmacro channel-state (i j chans) `(g ,i (g ,j ,chans)))
;; (ld "cl.lisp") 
;;msg type
(defmacro msg-type (msg) `(g :msg-type ,msg))

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


(defmacro sid (msg)
  `(g :sid ,msg)))

(defmacro counter (p)
  `(g :counter ,p))
 
(defmacro snapshot-ids (p)
  `(g :snapshot-ids ,p))

(defmacro snapshots (p)
  `(g :snapshots ,p))

(defmacro snapshot-entry (sid p)
  `(g ,sid (snapshots ,p)))

(defmacro snapshot-status (entry)
  `(g :status ,entry))

(defmacro snapshot-local-snap-shot (entry)
  `(g :local-snap-shot ,entry))

(defmacro snapshot-channel-snapshots (entry)
  `(g :channel-snapshots ,entry))

(defmacro snapshot-recording-from (entry)
  `(g :recording-from ,entry))

(defmacro >entry (&rest upds)
  `(update entry ,@upds))

(defun make-snapshot-entry (local-snap-shot recording-from j)
  (>_ :status :checkpointing
      :local-snap-shot local-snap-shot
      :channel-snapshots (append-to-record-list j nil nil)
      :recording-from recording-from))

(defun add-snapshot-id (sid ids)
  (if (memberp sid ids)
      ids
    (snoc ids sid)))

(defun set-snapshot-entry (sid entry p)
  (let* ((snaps (snapshots p))
         (snaps (s sid entry snaps)))
    (s :snapshots snaps p)))

(defun install-snapshot-entry (sid entry p)
  (let* ((snapshot-ids   (add-snapshot-id sid (snapshot-ids p)))
         (snapshots (snapshots p))
         (snapshots (s sid entry snapshots)))
    (update p
            :snapshot-ids snapshot-ids
            :snapshots snapshots)))

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
 (((update-local-state * * *) => *)
  ;;what arguments to put in update-local-state?
  ;;Probably current state, normal-msg, nbr from which the msg was received
  
  ((message-to-send? * *) => *)
  ((create-compute-message * *) => *)
  ((create-marker-message * *) => *)
  ((create-recovery-message * *) => *))
 
 (local
  (defun update-local-state (local-state msg nbr)
    (declare (ignore local-state msg nbr))
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
  (defun create-marker-message (local-state nbr)
    (declare (ignore local-state nbr))
    nil))

  (local
  (defun create-recovery-message (local-state nbr)
    (declare (ignore local-state nbr))
    nil))
     )


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


(defun send-marker-message (msg i nbrs channels)
  (cond ((endp nbrs) channels)
        ( t
         (let*
             ((nbr (first nbrs))
              (channels (send-marker-message msg i (rest nbrs) channels))
              (channel (channel-state i nbr channels))
              (channel (snoc channel msg))
              (channels (>channel i nbr channel channels)))
           channels))))

;; Also, I need to receive messages and remove them from the
;; channels.

(defun find-incoming-channels (i nbrs channels)
  (if (endp nbrs)
      nil
    (cons (channel-state i (first nbrs) channels)
          (find-incoming-channels i (rest nbrs) channels))))


;; Get the first msg from a incoming channel
(defun get-msg-from-channel (i nbr channels)
  (let* ((channel (channel-state nbr i channels))
         (channel (if channel (cdr channel) nil))
	 (msg (first channel)))
    msg))

;; Remove the first msg from a incoming channel and return channels
(defun remove-message-from-incoming-channel (i nbr channels)
    (let* ((channel (channel-state nbr i channels))
           (channel (if channel (cdr channel) nil))
           (channels (>channel nbr i  channel channels)))
      channels))

;; record-msg-from a incoming-channel and return channel-snapshots
(defun record-msg-from-incoming-channel-return-channel-snapshot (i nbr channel-snapshots channels)
(let* ((channel (channel-state nbr i channels))
       (msg (first channel))
       (channel-snapshots (append-to-record-list nbr msg channel-snapshots))) 
  channel-snapshots))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 4: Transition function
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For defining a transition of distributed system, i is the
;; index of the process that takes a step.
;; if checkpoint started, we need to record the messages



;; helper functions for step-rcv. Normal and marker msgs need to be handled
;; differently. Based on the process status (normal/checkpointing) different
;; things needed to be done

(defun handle-normal-msg (st i nbr msg status)
  (case status

    (:normal-op
     ;; A normal msg received before checkpointing, so just update local-state of the process,
     ;; remove the msg from the channel
     (let* ((procs (procs st))
            (channels (channels st))
            (p (g i procs))
	    (local (local-state p))
	    (local (update-local-state local msg nbr))
            (channels (remove-message-from-incoming-channel i nbr channels))
	    (p (>p :local-state local))
            (procs (s i p procs))
            (st (>st :procs procs
                     :channels channels)))
       st))

     (:checkpointing
      ;;A normal msg received after checkpointing, so save the msg in the channel snapshot's jth entry
      
     (let* ((procs (procs st))
            (channels (channels st))
            (p (g i procs))
	    (channel-snapshots (channel-snapshots p))
	    (recording-from (recording-from p))
	    (channel-snapshots
	     (if (memberp nbr recording-from)
		 ( record-msg-from-incoming-channel-return-channel-snapshot
		  i nbr channel-snapshots channels)
		 channel-snapshots))    
            (channels (remove-message-from-incoming-channel i nbr channels))
	    (p (>p :channel-snapshots channel-snapshots))
	    ;; update local-state?
            (procs (s i p procs))
            (st (>st :procs procs
                     :channels channels)))
       st))))


(defun handle-non-first-marker-msg (st i j msg)
  (let* ((sid            (sid msg))          ; snapshot id carried by this marker
         (procs          (procs st))         ; current process table
         (p              (g i procs))        ; state of receiving process i

         ;; Look up the snapshot entry for this snapshot id at process i
         (entry          (snapshot-entry sid p))

         ;; Process i was recording channel j -> i for this snapshot.
         ;; Since the marker for sid has now arrived on that channel,
         ;; stop recording that channel by removing j from recording-from.
         (recording-from (snapshot-recording-from entry))
         (recording-from (remove-from-list recording-from j))

         ;; If no incoming channels remain to be recorded for this snapshot,
         ;; then the snapshot is complete at this process.
         (status         (if (endp recording-from)
                             :done
                           (snapshot-status entry)))

         ;; Write the updated per-snapshot fields back into the entry.
         (entry          (update entry
                                 :recording-from recording-from
                                 :status status))

         ;; Store the updated snapshot entry back into process i.
         (p              (set-snapshot-entry sid entry p))

         ;; Remove the marker message itself from incoming channel j -> i.
         (channels       (channels st))
         (channels       (remove-message-from-incoming-channel i j channels))
         (procs          (s i p procs))
         (st             (>st :procs procs
                              :channels channels)))
    st))

(defun handle-first-marker-msg (st i j  msg)
  (let* ((procs          (procs st))
         (p              (g i procs))
         (nbrs-from      (nbrs-from i procs))
         (nbrs-to        (nbrs-to i procs))
         (local-state    (local-state p))
         (channels       (channels st))
         (sid            (sid msg))

         ;; remove received marker from channel j -> i
         (channels       (remove-message-from-incoming-channel i j channels))

         ;; for this snapshot-id, start recording all incoming channels except j
         (recording-from (remove-from-list nbrs-from j))

         ;; create and install fresh snapshot entry for sid
         (entry          (make-snapshot-entry local-state recording-from j))
         (p              (install-snapshot-entry sid entry p))

         ;; send marker for this sid on all outgoing channels
         (channels       (send-marker-message msg i nbrs-to channels))

         (procs          (s i p procs))
         (st             (>st :procs procs
                              :channels channels)))
    st))


(defun handle-marker-msg (st i j msg)
 (let* ((sid (sid msg))
	(procs (procs st))
        (p (g i procs))
	(snapshot-ids (snapshot-ids p))))
 (if (memberp sid snapshot-ids)
     (handle-non-first-marker-msg st i j msg)
     (handle-first-marker-msg st i j msg)))




(defun step-rcv (st i j)
  (let* ((procs (procs st))
         (channels (channels st))
	 (msg (get-msg-from-channel i j channels))
	 (msg-type (msg-type msg)))
	 (case msg-type
	   (:normal  (handle-normal-msg st i j msg))
	   (:marker  (handle-marker-msg st i j msg)))))

;; Do we need to update local state when sending a message

(defun step-snd (st i)
(let* ((procs (procs st))
       (channels (channels st))
       (p (g i procs))
       (nbrs-to (nbrs-to i procs))
       (local (local-state p))
       (channels (send-compute-message local i nbrs-to channels)) ;; send compute messages along outgoing channels
       (procs (s i p procs))
       (st (>st :procs procs
         	:channels channels)))
       st))

(defun step-start-checkpoint (st i)
  (let* ((procs (procs st))
         (channels (channels st))
         (p (g i procs))
         (nbrs-to (nbrs-to i procs))
	 (nbrs-from (nbrs-from i procs))
         (recording-from nbrs-from) ;;start recording on all incoming channels
         (local-state (local-state p))
	 (p (>p :local-snap-shot local-state
		:status "checkpointing"
		:recording-from recording-from)) 
         (channels (send-marker-message local-state i nbrs-to channels))
         (procs (s i p procs))
         (st (>st :procs procs
                  :channels channels)))
    st))


;; This is just a placeholder for what you need to do.
(defstub complete-this () => *)

(defun checkpointing-distributed-system-step (st input)
  (let* ((i (pid input))
	 (j (sender input))
         (ttype (ttype input)))
    (case ttype
      (:receive (step-rcv st i j))
      (:normal (step-snd st i))
      (:start-checkpoint (step-start-checkpoint st i))
      (:crash (complete-this))
      (:recover (complete-this))
      (t st))))
         
            
;; a process i sending a normal msg to another process j : should it not be a function of local-state of process i?
;; start-checkpointing and crash should be output input
;; recover should be initiated after the a process is crashed and by the crashed process

;;In a normal transition, we are doing step-snd, what we will do here? send a msg to other processes? Based on current state?
;; 
