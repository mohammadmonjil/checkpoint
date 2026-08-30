(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unified cut scan
;;
;; This is a drop-in replacement for the existing cut-metadata/scan block.
;; Existing names are preserved.  The only new global metadata field is:
;;
;;   :after-cut-input-sequence
;;
;; It contains every ordinary input whose process had already taken its cut,
;; in the original global execution order.
;;
;; The older :inputs-after-cut field is preserved unchanged.  It remains the
;; channel-wise table of receives recorded while an incoming channel is open.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ------------------------------------------------------------------
;; Existing metadata accessors
;; ------------------------------------------------------------------

(defmacro cm-sid (m)
  `(g :sid ,m))

(defun cm-proc-ids (m)
  (g :proc-ids m))

(defun cm-cut-not-taken (m)
  (g :cut-not-taken m))

(defun cm-waiting-marker-from (m)
  (g :waiting-marker-from m))

(defun cm-inputs-before-cut (m)
  (g :inputs-before-cut m))

;; Existing channel-wise table:
;;   process i -> incoming neighbor j -> receive-input list.
(defun cm-inputs-after-cut (m)
  (g :inputs-after-cut m))

;; Existing channel-wise table of the actual normal messages consumed by
;; the receive inputs in :inputs-after-cut.
(defun cm-after-cut-msgs (m)
  (g :after-cut-msgs m))

;; ------------------------------------------------------------------
;; New accessor: global post-cut ordinary-input sequence
;; ------------------------------------------------------------------

(defun cm-after-cut-input-sequence (m)
  (g :after-cut-input-sequence m))

;; Optional alias with the words in the opposite order.
(defun cm-inputs-after-cut-sequence (m)
  (cm-after-cut-input-sequence m))

(defun cm-waiting-marker-for (m i)
  (g i (cm-waiting-marker-from m)))

(defun cm-set-waiting-marker-for (m i xs)
  (s :waiting-marker-from
     (s i xs (cm-waiting-marker-from m))
     m))

(defun cm-cut-not-taken-p (m i)
  (memberp i (cm-cut-not-taken m)))

(defun cm-remove-cut-not-taken (m i)
  (s :cut-not-taken
     (remove1-equal i (cm-cut-not-taken m))
     m))

(defun cm-add-before-cut (m input)
  (s :inputs-before-cut
     (snoc (cm-inputs-before-cut m) input)
     m))

;; New update helper.  SNOC preserves the original global execution order.
(defun cm-add-after-cut-input-sequence (m input)
  (s :after-cut-input-sequence
     (snoc (cm-after-cut-input-sequence m) input)
     m))

;; ------------------------------------------------------------------
;; Existing channel-wise after-cut input operations
;; ------------------------------------------------------------------

(defun cm-after-cut-get (m i j)
  (let ((rec-i (g i (cm-inputs-after-cut m))))
    (g j rec-i)))

(defun cm-after-cut-append (m i j input)
  (let* ((all   (cm-inputs-after-cut m))
         (rec-i (g i all))
         (old   (g j rec-i))
         (rec-i (s j (snoc old input) rec-i))
         (all   (s i rec-i all)))
    (s :inputs-after-cut all m)))

;; ------------------------------------------------------------------
;; Existing channel-wise after-cut message operations
;; ------------------------------------------------------------------

(defun cm-after-cut-msg-get (m i j)
  (let ((rec-i (g i (cm-after-cut-msgs m))))
    (g j rec-i)))

(defun cm-after-cut-msg-append (m i j msg)
  (let* ((all   (cm-after-cut-msgs m))
         (rec-i (g i all))
         (old   (g j rec-i))
         (rec-i (s j (snoc old msg) rec-i))
         (all   (s i rec-i all)))
    (s :after-cut-msgs all m)))

;; ------------------------------------------------------------------
;; Metadata construction
;; ------------------------------------------------------------------

(defun make-inputs-after-cut-for-proc (nbrs)
  (if (endp nbrs)
      nil
    (s (first nbrs)
       nil
       (make-inputs-after-cut-for-proc (rest nbrs)))))

(defun make-inputs-after-cut (proc-ids procs)
  (if (endp proc-ids)
      nil
    (let* ((i         (first proc-ids))
           (p         (g i procs))
           (nbrs      (nbrs-from p))
           (entry-i   (make-inputs-after-cut-for-proc nbrs))
           (rest-recs (make-inputs-after-cut (rest proc-ids) procs)))
      (s i entry-i rest-recs))))

(defun make-after-cut-msgs-for-proc (nbrs)
  (if (endp nbrs)
      nil
    (s (first nbrs)
       nil
       (make-after-cut-msgs-for-proc (rest nbrs)))))

(defun make-after-cut-msgs (proc-ids procs)
  (if (endp proc-ids)
      nil
    (let* ((i         (first proc-ids))
           (p         (g i procs))
           (nbrs      (nbrs-from p))
           (entry-i   (make-after-cut-msgs-for-proc nbrs))
           (rest-recs (make-after-cut-msgs (rest proc-ids) procs)))
      (s i entry-i rest-recs))))

(defun make-empty-waiting-marker-from (proc-ids)
  (if (endp proc-ids)
      nil
    (s (first proc-ids)
       nil
       (make-empty-waiting-marker-from (rest proc-ids)))))

(defun make-cut-meta (sid initiator st)
  ;; Preserve the old convention: the initiator is already treated as having
  ;; taken its cut when this metadata is created.  Therefore the matching
  ;; :start-checkpoint input itself remains a protocol step and is ignored by
  ;; process-cut-step.
  (let* ((procs    (procs st))
         (proc-ids (proc-ids st))
         (p        (g initiator procs))
         (nbrs     (nbrs-from p))
         (m        nil)
         ;; New global post-cut sequence.
         (m        (s :after-cut-input-sequence nil m))
         ;; Existing channel-wise data.
         (m        (s :after-cut-msgs
                      (make-after-cut-msgs proc-ids procs)
                      m))
         (m        (s :inputs-after-cut
                      (make-inputs-after-cut proc-ids procs)
                      m))
         (m        (s :inputs-before-cut nil m))
         (m        (s :waiting-marker-from
                      (s initiator
                         nbrs
                         (make-empty-waiting-marker-from proc-ids))
                      m))
         (m        (s :cut-not-taken
                      (remove1-equal initiator proc-ids)
                      m))
         (m        (s :proc-ids proc-ids m))
         (m        (s :sid sid m)))
    m))

;; ------------------------------------------------------------------
;; Full checkpoint-completion predicate
;; ------------------------------------------------------------------

(defun all-waiting-marker-empty-p (ids m)
  (if (endp ids)
      t
    (and (endp (cm-waiting-marker-for m (first ids)))
         (all-waiting-marker-empty-p (rest ids) m))))

(defun checkpoint-collection-complete-p (m)
  (if (equal (cm-sid m) :init)
      t
    (and (endp (cm-cut-not-taken m))
         (all-waiting-marker-empty-p
          (cm-proc-ids m)
          m))))

;; Keep the old name available.  It now denotes full checkpoint collection
;; completion, rather than only "all local cuts have occurred."
(defun cut-done-p (m)
  (checkpoint-collection-complete-p m))

;; ------------------------------------------------------------------
;; One-step processing
;; ------------------------------------------------------------------

(defun process-cut-normal (input m)
  ;; Every ordinary local step belongs to exactly one global list.
  (let ((i (pid input)))
    (if (cm-cut-not-taken-p m i)
        (cm-add-before-cut m input)
      (cm-add-after-cut-input-sequence m input))))

(defun process-cut-marker-receive (i j st m)
  (let ((procs (procs st)))
    (if (cm-cut-not-taken-p m i)
        ;; First marker for i: i takes its cut.  The channel j -> i is
        ;; closed immediately, while the other incoming channels remain open.
        (let* ((p    (g i procs))
               (nbrs (nbrs-from p))
               (ws   (remove1-equal j nbrs))
               (m    (cm-remove-cut-not-taken m i)))
          (cm-set-waiting-marker-for m i ws))
      ;; Later marker for i: close only j -> i.
      (cm-set-waiting-marker-for
       m i
       (remove1-equal j
                      (cm-waiting-marker-for m i))))))

(defun process-cut-normal-receive (input i j msg m)
  (if (cm-cut-not-taken-p m i)
      ;; The receive is prerecording for i.
      (cm-add-before-cut m input)

    ;; Every normal receive after i's cut belongs to the new global post-cut
    ;; sequence, even if j's marker has already arrived.
    (let ((m (cm-add-after-cut-input-sequence m input)))
      (if (memberp j (cm-waiting-marker-for m i))
          ;; While j -> i is still open, preserve the old channel-wise rows
          ;; used by the recovery/replay lemmas.
          (let ((m (cm-after-cut-append m i j input)))
            (cm-after-cut-msg-append m i j msg))
        m))))

(defun current-msg-for-receive (input st)
  (let* ((i        (pid input))
         (j        (sender input))
         (channels (channels st)))
    (get-msg-from-channel j i channels)))

(defun process-cut-receive (input st m)
  (let* ((i   (pid input))
         (j   (sender input))
         (msg (current-msg-for-receive input st))
         (sid (cm-sid m)))
    (cond
     ;; Matching checkpoint marker: update cut/open-channel metadata only.
     ((and (equal (msg-type msg) :marker)
           (equal (sid msg) sid))
      (process-cut-marker-receive i j st m))

     ;; An actual ordinary receive is classified as pre or post.
     ((equal (msg-type msg) :normal)
      (process-cut-normal-receive input i j msg m))

     ;; Recovery messages, markers for another SID, and empty receives are
     ;; protocol/nonordinary steps for this scan.
     (t m))))

(defun process-cut-step (input st m)
  ;; Existing name and argument order are unchanged.
  (cond
   ((equal (ttype input) :start-checkpoint)
    ;; make-cut-meta already accounts for the initiator's local cut.
    m)

   ((equal (ttype input) :normal)
    (process-cut-normal input m))

   ((equal (ttype input) :receive)
    (process-cut-receive input st m))

   (t m)))

;; Existing recursive segment function; old lemmas can continue to use it.
(defun process-cut-segment (inputs st m)
  (declare (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      m
    (let* ((input   (first inputs))
           (m-next  (process-cut-step input st m))
           (st-next (system-step st input)))
      (process-cut-segment (rest inputs)
                           st-next
                           m-next))))

;; ------------------------------------------------------------------
;; Existing scan result names
;; ------------------------------------------------------------------

(defmacro cut-result-idx (r)
  `(g :cut-done-index ,r))

(defmacro cut-result-meta (r)
  `(g :cut-meta ,r))

;; ------------------------------------------------------------------
;; Existing scan names, now scanning through full checkpoint completion
;; ------------------------------------------------------------------

(defun scan-until-cut-done-aux (inputs trace idx m)
  (declare (xargs :measure (acl2-count inputs)))
  (if (or (endp inputs)
          (checkpoint-collection-complete-p m))
      (>_ :cut-done-index idx
          :cut-meta m)
    (let* ((input (first inputs))
           (st    (nth idx trace))
           (m     (process-cut-step input st m)))
      (scan-until-cut-done-aux (rest inputs)
                               trace
                               (+ 1 idx)
                               m))))

(defun scan-until-cut-done (inputs trace cp-start sid initiator)
  ;; Existing name and argument order are unchanged.
  (let* ((st (nth cp-start trace))
         (m0 (make-cut-meta sid initiator st)))
    (scan-until-cut-done-aux (nthcdr cp-start inputs)
                             trace
                             cp-start
                             m0)))
