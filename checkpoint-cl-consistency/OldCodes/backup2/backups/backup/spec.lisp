
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
    nil))
  
     )



;; Remove the first msg from a incoming channel and return channels
(defun remove-message-from-channel (i nbr channels)
    (let* ((channel (channel-state nbr i channels))
           (channel (if channel (cdr channel) nil))
           (channels (>channel nbr i  channel channels)))
      channels))



;; Get the first msg from a incoming channel
(defun get-msg-from-channel (i nbr channels)
  (let* ((channel (channel-state nbr i channels))
	 (msg (first channel)))
    msg))


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

;; (defun spec-checkpointing-distributed-system-step (st input)
;;   (let* ((i     (pid input))
;;          (j     (sender input))
;;          (ttype (ttype input)))
;;     (case ttype
;;       (:fall-back (spec-step-fall-back st input))
;;       (t
;;        (let* ((st (save-state-in-history st)))
;;          (case ttype
;;            (:receive (spec-step-rcv st i j))
;;            (:normal  (spec-step-normal st i))
;;            (t st)))))))
