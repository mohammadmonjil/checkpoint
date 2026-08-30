
(in-package "ACL2")
(include-book "model")
(include-book "good_state_invariants")	
(include-book "channel_equivalence")


(defun current-msg-for-receive (input st)
  (let* ((i        (pid input))
         (j        (sender input))
         (channels (channels st)))
    (get-msg-from-channel j i channels)))

;; (defun make-nop-input (input)
;;   (update input :ttype :nop))



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

;; (defun cm-inputs-before-cut (m)
;;   (g :inputs-before-cut m))

;; ;; Existing channel-wise table:
;; ;;   process i -> incoming neighbor j -> receive-input list.
;; (defun cm-inputs-after-cut (m)
;;   (g :inputs-after-cut m))

;; ;; Existing channel-wise table of the actual normal messages consumed by
;; ;; the receive inputs in :inputs-after-cut.
;; (defun cm-after-cut-msgs (m)
;;   (g :after-cut-msgs m))

;; ------------------------------------------------------------------
;; New accessor: global post-cut ordinary-input sequence
;; ------------------------------------------------------------------

(defun cm-after-cut-input-sequence (m)
  (g :after-cut-input-sequence m))


(defun cm-before-cut-input-sequence (m)
  (g :before-cut-input-sequence m))


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


(defun cm-add-after-cut-input-sequence (m input)
  (s :after-cut-input-sequence
     (append
      (cm-after-cut-input-sequence m)
      (list input))
     m))


(defun cm-add-before-cut-input-sequence (m input)
  (s :before-cut-input-sequence
     (append
      (cm-before-cut-input-sequence m)
      (list input))
     m))




(defun make-empty-waiting-marker-from (proc-ids)
  (if (endp proc-ids)
      nil
    (s (first proc-ids)
       nil
       (make-empty-waiting-marker-from (rest proc-ids)))))



(defun make-cut-meta (sid initiator st)
  ;; Initial cut metadata before processing the target
  ;; :start-checkpoint input.
  ;;
  ;; No process has taken its cut yet.  In particular, the initiator
  ;; remains in :cut-not-taken.  PROCESS-CUT-STEP will recognize the
  ;; matching :start-checkpoint input, remove the initiator from
  ;; :cut-not-taken, and initialize its waiting-marker-from entry.
  (declare (ignore initiator))
  (let* (
         (proc-ids (proc-ids st))
         (m        nil)

         ;; Global input sequences.
         (m        (s :after-cut-input-sequence nil m))
         (m        (s :before-cut-input-sequence nil m))

         ;; No process has taken its cut yet, so nobody is
         ;; waiting for checkpoint markers yet.
         (m        (s :waiting-marker-from
                      (make-empty-waiting-marker-from proc-ids)
                      m))

         ;; Initially every process has not taken its cut.
         (m        (s :cut-not-taken
                      proc-ids
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

;; (defun process-cut-normal (input m)
;;   ;; Every ordinary local step belongs to exactly one global list.
;;   (let ((i (pid input)))
;;     (if (cm-cut-not-taken-p m i)
;;         (cm-add-before-cut m input)
;;       (cm-add-after-cut-input-sequence m input))))

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
      m)

     ;; Recovery messages, markers for another SID, and empty receives are
     ;; protocol/nonordinary steps for this scan.
     (t m))))



(defun process-cut-checkpoint (input st m)
  (let* ((i          (pid input))
         (procs      (procs st))
         (p          (g i procs))
         (input-sid  (list i
                           (counter p)))
         (target-sid (cm-sid m)))

    (if (equal input-sid target-sid)

        ;; This is the :start-checkpoint that begins TARGET-SID.
        ;; The initiator now takes its cut.
        (let* ((m (cm-remove-cut-not-taken m i))
               (m (s :waiting-marker-from
                     (s i
                        (nbrs-from p)
                        (g :waiting-marker-from m))
                     m)))
          m)

      ;; A :start-checkpoint for some other checkpoint.
      ;; It does not affect this cut scan.
	m)))


(defun process-cut-step (input st m)

  (let*
      ((i
        (pid input))

       ;; Classify INPUT before performing its cut update.
       (m
        (if
            (cm-cut-not-taken-p m i)

            (cm-add-before-cut-input-sequence
             m input)

          (cm-add-after-cut-input-sequence
           m input))))

    ;; Now perform the input-specific metadata update.
    (cond
     ((equal (ttype input) :start-checkpoint)
      (process-cut-checkpoint input st m))

     ((equal (ttype input) :normal)
       m)

     ((equal (ttype input) :receive)
      (process-cut-receive input st m))

     (t
      m))))



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
;; ---------------------------------------------------------------
;; ------------------------------------------------------------------
;; Cut-phase scan
;;
;; Starting from checkpoint-start, scan the aligned input suffix and
;; trace until checkpointing for the current sid is complete.
;;
;; Return:
;;   - :cut-done-index   = first index at which checkpointing is done
;;   - :cut-meta         = final cut metadata
;;
;; For sid = :init, cut-done is immediate, since there is no actual
;; checkpoint protocol to complete.
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


