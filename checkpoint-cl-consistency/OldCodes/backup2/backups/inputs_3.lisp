(in-package "ACL2")

(include-book "model")
(include-book "invariants")
(include-book "equivalence")
(include-book "inputs_1")
(include-book "inputs_2")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Top-level cp-start / recovery segment helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cp-start-rc-segment-initiator (input-seg)
  (pid (first input-seg)))


(defun cp-start-rc-segment-sid (st input-seg)
  ;; SID created by the checkpoint-start input at the beginning
  ;; of this cp-start ... rc-done segment.
  (let* ((i (cp-start-rc-segment-initiator input-seg)))
    (list i
          (counter
           (g i (procs st))))))


(defun cp-start-rc-initial-cut-meta (st input-seg)
  ;; Initial cut metadata immediately associated with this checkpoint SID.
  (let* ((sid       (cp-start-rc-segment-sid st input-seg))
         (initiator (cp-start-rc-segment-initiator input-seg)))
    (make-cut-meta sid initiator st)))


(defun cp-start-rc-cut-result (st input-seg)
  ;; Global scan until checkpoint collection is complete for all processes.
  ;; This is useful only for bounding per-process indices x and y.
  (let* ((trace     (run-imp-trace st input-seg))
         (sid       (cp-start-rc-segment-sid st input-seg))
         (initiator (cp-start-rc-segment-initiator input-seg)))
    (scan-until-cut-done input-seg
                         trace
                         0
                         sid
                         initiator)))


(defun cp-start-rc-cut-done-index (st input-seg)
  (cut-result-idx
   (cp-start-rc-cut-result st input-seg)))


(defun cp-start-rc-cut-meta (st input-seg)
  (cut-result-meta
   (cp-start-rc-cut-result st input-seg)))


(defun cp-start-cut-done-prefix-p (st input-seg)
  (let* ((xcut (cp-start-rc-cut-done-index st input-seg))
         (mcut (cp-start-rc-cut-meta st input-seg)))
    (and
     (cp-start-rc-done-segment-p st input-seg)

     ;; xcut is the global checkpoint-completion boundary.
     (natp xcut)
     (<= xcut (len input-seg))

     ;; Metadata at xcut says checkpoint collection is complete.
     (checkpoint-collection-complete-p mcut))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; State/meta before and after an input index
;;
;; Index convention:
;;
;;   before-cut-index x:
;;      after executing inputs 0 ... x-1
;;
;;   input at index x:
;;      (nth x input-seg)
;;
;;   after-cut-index x:
;;      after executing input x
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cp-start-rc-state-before-cut-index (st input-seg x)
  (run-imp st
           (take x input-seg)))


(defun cp-start-rc-meta-before-cut-index (st input-seg x)
  (process-cut-segment
   (take x input-seg)
   st
   (cp-start-rc-initial-cut-meta st input-seg)))


(defun cp-start-rc-state-after-cut-index (st input-seg x)
  (system-step
   (cp-start-rc-state-before-cut-index st input-seg x)
   (nth x input-seg)))


(defun cp-start-rc-meta-after-cut-index (st input-seg x)
  (process-cut-step
   (nth x input-seg)
   (cp-start-rc-state-before-cut-index st input-seg x)
   (cp-start-rc-meta-before-cut-index st input-seg x)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Per-process segment slices
;;
;; x = index where process i takes its cut
;; y = first state-boundary index where process i is cut-complete
;;
;; Therefore:
;;
;;   before-cut inputs:
;;      inputs[0 ... x-1]
;;
;;   cut-step input:
;;      inputs[x]
;;
;;   after-cut inputs:
;;      inputs[x+1 ... y-1]
;;
;; If y = x+1, then process i became complete immediately after the cut-step.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cp-start-rc-proc-before-cut-inputs (x input-seg)
  (take x input-seg))


(defun cp-start-rc-proc-cut-input (x input-seg)
  (nth x input-seg))


(defun cp-start-rc-proc-after-cut-inputs (x y input-seg)
  ;; Excludes the cut-step at x.
  ;; Ends just before boundary y.
  (take (nfix (- y (+ 1 x)))
        (nthcdr (+ 1 x) input-seg)))


(defun cp-start-rc-proc-cut-through-complete-inputs (x y input-seg)
  ;; Includes the cut-step at x.
  ;; Ends just before boundary y.
  (take (nfix (- y x))
        (nthcdr x input-seg)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Per-process before-cut segment
;;
;; This says:
;;   - i is not the checkpoint initiator;
;;   - x is a real input index before global cut completion;
;;   - before input x, process i has not taken its cut;
;;   - immediately before input x, i is still in cut-not-taken.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cp-start-rc-proc-before-cut-segment-p
    (i x st input-seg)
  (let* ((m0         (cp-start-rc-initial-cut-meta st input-seg))
         (pre-inputs (cp-start-rc-proc-before-cut-inputs x input-seg))
         (m-x        (cp-start-rc-meta-before-cut-index st input-seg x)))
    (and
     (cp-start-rc-done-segment-p st input-seg)

     (natp x)
     (< x (len input-seg))

     ;; Non-initiator case.
     ;; The initiator is cut-taken in the initial metadata.
     (not (equal i
                 (cp-start-rc-segment-initiator input-seg)))

     ;; Process i must take its cut during the checkpoint-collection prefix.
     (< x (cp-start-rc-cut-done-index st input-seg))

     ;; Process i stays cut-not-taken throughout the prefix before x.
     (cut-scan-proc-stays-cut-not-taken-p
      i pre-inputs st m0)

     ;; Immediately before x, i is still cut-not-taken.
     (cm-cut-not-taken-p m-x i))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Exact cut-step for process i
;;
;; This says input x is the first input where i leaves cut-not-taken.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cp-start-rc-proc-cut-step-p
    (i x st input-seg)
  (let* ((st-x    (cp-start-rc-state-before-cut-index st input-seg x))
         (m-x     (cp-start-rc-meta-before-cut-index st input-seg x))
         (input-x (cp-start-rc-proc-cut-input x input-seg)))
    (and
     (cp-start-rc-proc-before-cut-segment-p
      i x st input-seg)

     (cut-scan-proc-takes-cut-step-p
      i input-x st-x m-x))))


(defun proc-takes-cut-at-index-in-cp-start-rc-segment-p
    (i x st input-seg)
  (cp-start-rc-proc-cut-step-p i x st input-seg))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Per-process cut completion
;;
;; i is complete iff:
;;   - i already took its local cut;
;;   - i is no longer waiting for markers from any incoming channel.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proc-cut-complete-p (i m)
  (and
   (not (cm-cut-not-taken-p m i))
   (endp (cm-waiting-marker-for m i))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Structural after-cut segment predicate
;;
;; This is the induction-friendly predicate.
;;
;; It walks over the post-cut input list.
;;
;; Base case:
;;   no more inputs; process i must be complete.
;;
;; Step case:
;;   before each input:
;;      - i already took cut;
;;      - i is still waiting for at least one marker;
;;      - spec-side one-process side conditions hold;
;;      - implementation snapshot one-process side conditions hold.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proc-after-cut-until-complete-segment-p
    (i nbrs sid inputs st m spec-start-st)
  (if (endp inputs)
      (proc-cut-complete-p i m)
    (let* ((input   (car inputs))
           (st-next (system-step st input))
           (m-next  (process-cut-step input st m)))
      (and
       ;; i has already taken cut before every step in this segment.
       (not (cm-cut-not-taken-p m i))

       ;; Since there is still an input in this suffix,
       ;; i has not yet completed marker collection.
       (consp (cm-waiting-marker-for m i))

       ;; Existing spec-side one-process side conditions.
       (cm-spec-open-incoming-step-sideconds-p
        i nbrs input st m spec-start-st)

       ;; Existing implementation snapshot side conditions.
       (cm-imp-snapshot-step-sideconds-p
        i nbrs sid input st m)

       ;; Continue through the suffix.
       (proc-after-cut-until-complete-segment-p
        i nbrs sid
        (cdr inputs)
        st-next
        m-next
        spec-start-st)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; State/meta helpers for the after-cut segment
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cp-start-rc-proc-after-cut-initial-state
    (x st input-seg)
  (cp-start-rc-state-after-cut-index st input-seg x))


(defun cp-start-rc-proc-after-cut-initial-meta
    (x st input-seg)
  (cp-start-rc-meta-after-cut-index st input-seg x))


(defun cp-start-rc-proc-after-cut-final-state
    (x y st input-seg)
  (run-imp
   (cp-start-rc-proc-after-cut-initial-state x st input-seg)
   (cp-start-rc-proc-after-cut-inputs x y input-seg)))


(defun cp-start-rc-proc-after-cut-final-meta
    (x y st input-seg)
  (process-cut-segment
   (cp-start-rc-proc-after-cut-inputs x y input-seg)
   (cp-start-rc-proc-after-cut-initial-state x st input-seg)
   (cp-start-rc-proc-after-cut-initial-meta x st input-seg)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; After-cut segment for process i inside cp-start-rc
;;
;; x = cut-step index for i
;; y = first boundary where i is complete
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cp-start-rc-proc-after-cut-segment-p
    (i nbrs sid x y st input-seg spec-start-st)
  (let* ((m-after-cut
          (cp-start-rc-proc-after-cut-initial-meta x st input-seg))
         (post-inputs
          (cp-start-rc-proc-after-cut-inputs x y input-seg))
         (st-after-cut
          (cp-start-rc-proc-after-cut-initial-state x st input-seg))
         (m-final
          (cp-start-rc-proc-after-cut-final-meta x y st input-seg)))
    (and
     ;; x is where i takes cut.
     (cp-start-rc-proc-cut-step-p
      i x st input-seg)

     ;; y is a valid boundary after x.
     (natp y)
     (<= (+ 1 x) y)
     (<= y (len input-seg))

     ;; Process-local completion occurs no later than global cut completion.
     (<= y (cp-start-rc-cut-done-index st input-seg))

     ;; Use the checkpoint SID from the segment.
     (equal sid
            (cp-start-rc-segment-sid st input-seg))

     ;; Immediately after x, process i has taken the cut.
     (not (cm-cut-not-taken-p m-after-cut i))

     ;; Structural post-cut segment side condition.
     (proc-after-cut-until-complete-segment-p
      i nbrs sid
      post-inputs
      st-after-cut
      m-after-cut
      spec-start-st)

     ;; Final sanity check.
     (proc-cut-complete-p i m-final))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Full per-process cut-complete segment
;;
;; This combines:
;;
;;   1. checkpoint-start through before i's cut;
;;   2. exact cut-step for i;
;;   3. after-cut marker-recording suffix until i is complete.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun cp-start-rc-proc-cut-complete-segment-p
    (i nbrs sid x y st input-seg spec-start-st)
  (and
   (cp-start-rc-proc-before-cut-segment-p
    i x st input-seg)

   (cp-start-rc-proc-cut-step-p
    i x st input-seg)

   (cp-start-rc-proc-after-cut-segment-p
    i nbrs sid x y st input-seg spec-start-st)))
