(in-package "ACL2")
(include-book "model")
(include-book "good_state_invariants")
(include-book "scan")
(include-book "basic")


(defun cut-meta-imp-procs-consistent-p
    (ids target-sid m imp-procs)

  (declare
   (xargs :measure (acl2-count ids)))

  (if (endp ids)

      t

    (let* ((i       (first ids))
           (p       (g i imp-procs))
           (has-sid (memberp target-sid
                             (snapshot-ids p))))

      (and

       ;; --------------------------------------------------
       ;; CUT STATUS
       ;;
       ;; Metadata says i has not taken the cut exactly when
       ;; the implementation does not yet contain TARGET-SID.
       ;; --------------------------------------------------
       (equal
        (cm-cut-not-taken-p m i)
        (not has-sid))


       ;; --------------------------------------------------
       ;; WAITING-MARKER-FROM
       ;; --------------------------------------------------
       (if has-sid

           ;; Once i has taken the cut, the scanner metadata
           ;; must exactly mirror the implementation snapshot.
           (equal
            (g i
               (g :waiting-marker-from m))

            (snapshot-waiting-marker-from
             (snapshot-entry
              target-sid
              p)))

         ;; Before i takes the cut, it must not yet have an
         ;; open-channel row in the cut metadata.
         (endp
          (g i
             (g :waiting-marker-from m))))


       (cut-meta-imp-procs-consistent-p
        (rest ids)
        target-sid
        m
        imp-procs)))))



(defun cut-meta-imp-initiator-consistent-p (m imp-st)
  (let* ((target-sid     (cm-sid m))
         (initiator      (first target-sid))
         (target-counter (second target-sid))
         (proc-ids       (proc-ids imp-st))
         (p              (g initiator
                            (procs imp-st))))

    (and
     (memberp initiator proc-ids)

     (if (cm-cut-not-taken-p m initiator)

         ;; Target checkpoint has not started.
         (and
          (equal (counter p)
                 target-counter)

          ;; Before the initiator starts the target checkpoint,
          ;; nobody can have taken this target cut.
          (equal (cm-cut-not-taken m)
                 (g :proc-ids m)))

       ;; Target checkpoint has started.
       ;; The initiator's current counter is now beyond
       ;; the counter stored in TARGET-SID.
       (< target-counter
          (counter p))))))



(defun cut-meta-imp-proc-ids-consistent-p (m imp-st)
  (equal
   (g :proc-ids m)
   (proc-ids imp-st)))




(defun cut-meta-imp-consistent-p (m imp-st)

  (and

   ;; Metadata and implementation describe the same processes.
   (cut-meta-imp-proc-ids-consistent-p
    m
    imp-st)

   ;; The SID initiator/counter agrees with implementation state.
   (cut-meta-imp-initiator-consistent-p
    m
    imp-st)

   ;; Per-process cut status and waiting-marker state agree.
   (cut-meta-imp-procs-consistent-p
    (g :proc-ids m)
    (cm-sid m)
    m
    (procs imp-st))))





(defun target-sid-absent-from-procs-p
    (ids target-sid procs)

  (declare
   (xargs :measure (acl2-count ids)))

  (if (endp ids)

      t

    (let* ((i (first ids))
           (p (g i procs)))

      (and
       (not
        (memberp
         target-sid
         (snapshot-ids p)))

       (target-sid-absent-from-procs-p
        (rest ids)
        target-sid
        procs)))))




(defthm
  cut-meta-imp-proc-ids-consistent-p-of-make-cut-meta

  (cut-meta-imp-proc-ids-consistent-p
   (make-cut-meta sid initiator st)
   st))


(defthm
  cut-meta-imp-initiator-consistent-p-of-make-cut-meta

  (implies
   (and
    (memberp
     initiator
     (proc-ids st))

    (equal
     sid
     (list
      initiator
      (counter
       (g initiator
          (procs st))))))

   (cut-meta-imp-initiator-consistent-p
    (make-cut-meta sid initiator st)
    st)))


(defthm
  cut-meta-imp-procs-consistent-p-of-make-cut-meta-gen

  (implies
   (and
    (subset
     ids
     (proc-ids st))

    (target-sid-absent-from-procs-p
     ids
     sid
     (procs st)))

   (cut-meta-imp-procs-consistent-p
    ids
    sid
    (make-cut-meta sid initiator st)
    (procs st))))



(defthm
  cut-meta-imp-procs-consistent-p-of-make-cut-meta

  (implies
   (target-sid-absent-from-procs-p
    (proc-ids st)
    sid
    (procs st))

   (cut-meta-imp-procs-consistent-p
    (proc-ids st)
    sid
    (make-cut-meta sid initiator st)
    (procs st)))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-procs-consistent-p-of-make-cut-meta-gen
      (ids (proc-ids st)))))))




(defthm
  cut-meta-imp-consistent-p-of-make-cut-meta

  (implies
   (and
    ;; INITIATOR is a real process.
    (memberp
     initiator
     (proc-ids st))

    ;; SID is exactly the checkpoint that INITIATOR
    ;; would start in ST.
    (equal
     sid
     (list
      initiator
      (counter
       (g initiator
          (procs st)))))

    ;; This checkpoint has not started yet.
    (target-sid-absent-from-procs-p
     (proc-ids st)
     sid
     (procs st)))

   (cut-meta-imp-consistent-p
    (make-cut-meta
     sid
     initiator
     st)

    st))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-proc-ids-consistent-p-of-make-cut-meta)

     (:instance
      cut-meta-imp-initiator-consistent-p-of-make-cut-meta)

     (:instance
      cut-meta-imp-procs-consistent-p-of-make-cut-meta))

    :in-theory
    (enable
     cut-meta-imp-consistent-p))))



(defun good-cut-meta-sid-p (m)
  (let ((sid (cm-sid m)))
    (and
     (true-listp sid)
     (equal (len sid) 2)

     ;; SID = (initiator counter)
     (memberp
      (first sid)
      (cm-proc-ids m))

     (natp
      (second sid)))))


(defun good-cut-meta-cut-not-taken-p (m)
  (and
   (true-listp
    (cm-cut-not-taken m))

   (uniquep
    (cm-cut-not-taken m))

   (subset
    (cm-cut-not-taken m)
    (cm-proc-ids m))))


(defun good-cut-meta-waiting-for-procs-p (ids m)
  (declare
   (xargs :measure (acl2-count ids)))

  (if (endp ids)

      t

    (let* ((i       (first ids))
           (waiting (g i
                       (g :waiting-marker-from m))))

      (and
       ;; A waiting row is a proper, duplicate-free process list.
       (true-listp waiting)

       (uniquep waiting)

       ;; It cannot mention a process outside this metadata universe.
       (subset
        waiting
        (cm-proc-ids m))

       ;; A process that has not taken its cut should not yet
       ;; be waiting for checkpoint markers.
       (implies
        (cm-cut-not-taken-p m i)
        (endp waiting))

       (good-cut-meta-waiting-for-procs-p
        (rest ids)
        m)))))


(defun good-cut-meta-global-input-sequences-p (m)
  (and
   (true-listp
    (g :before-cut-input-sequence m))

   (true-listp
    (g :after-cut-input-sequence m))))



(defun good-cut-meta-p (m)
  (and
   ;; Process universe.
   (true-listp
    (cm-proc-ids m))

   (uniquep
    (cm-proc-ids m))

   ;; Target checkpoint identifier.
   (good-cut-meta-sid-p m)

   ;; Cut-status set.
   (good-cut-meta-cut-not-taken-p m)

   ;; Per-process waiting-marker rows.
   (good-cut-meta-waiting-for-procs-p
    (cm-proc-ids m)
    m)

   ;; Global stored input sequences.
   (good-cut-meta-global-input-sequences-p m)))




;; ------------------------------------------------------------
;; GOOD-CUT-META-P is invariant under one metadata-processing
;; step, provided the implementation state and metadata are
;; mutually consistent and the concrete input is legal.
;;
;; GOOD-STATE-P supplies the structural facts about process
;; neighbor lists needed when PROCESS-CUT-STEP initializes a new
;; waiting-marker row.
;; ------------------------------------------------------------

;; ============================================================
;; FRAME LEMMAS FOR THE TWO GLOBAL INPUT-SEQUENCE FIELDS
;;
;; The waiting-marker invariant reads only:
;;
;;   :proc-ids
;;   :cut-not-taken
;;   :waiting-marker-from
;;
;; Consequently, changing either global input sequence cannot
;; affect the waiting-marker invariant.
;; ============================================================


(defthm
  good-cut-meta-waiting-for-procs-p-of-s-before-cut-input-sequence

  (equal
   (good-cut-meta-waiting-for-procs-p
    ids
    (s :before-cut-input-sequence xs m))

   (good-cut-meta-waiting-for-procs-p
    ids
    m)))


(defthm
  good-cut-meta-waiting-for-procs-p-of-s-after-cut-input-sequence

  (equal
   (good-cut-meta-waiting-for-procs-p
    ids
    (s :after-cut-input-sequence xs m))

   (good-cut-meta-waiting-for-procs-p
    ids
    m)))


;; ============================================================
;; Updating a stored input sequence does not affect the
;; correspondence between the cut-control metadata and the
;; implementation process state.
;; ============================================================


(defthm
  cut-meta-imp-procs-consistent-p-of-s-before-cut-input-sequence

  (equal
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    (s :before-cut-input-sequence xs m)
    procs)

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    procs)))


(defthm
  cut-meta-imp-procs-consistent-p-of-s-after-cut-input-sequence

  (equal
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    (s :after-cut-input-sequence xs m)
    procs)

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    procs)))


;; ============================================================
;; APPEND-ONE preserves TRUE-LISTP.
;; ============================================================


(defthm
  true-listp-of-append-one

  (implies
   (true-listp xs)

   (true-listp
    (append xs
            (list x)))))


;; ============================================================
;; Adding one input to either global sequence preserves the
;; structural invariant for the two stored sequences.
;; ============================================================


(defthm
  good-cut-meta-global-input-sequences-p-of-add-before

  (implies
   (good-cut-meta-global-input-sequences-p m)

   (good-cut-meta-global-input-sequences-p
    (cm-add-before-cut-input-sequence
     m
     input)))

  :hints
  (("Goal"
    :in-theory
    (enable
     good-cut-meta-global-input-sequences-p
     cm-add-before-cut-input-sequence
     cm-before-cut-input-sequence
     cm-after-cut-input-sequence))))


(defthm
  good-cut-meta-global-input-sequences-p-of-add-after

  (implies
   (good-cut-meta-global-input-sequences-p m)

   (good-cut-meta-global-input-sequences-p
    (cm-add-after-cut-input-sequence
     m
     input)))

  :hints
  (("Goal"
    :in-theory
    (enable
     good-cut-meta-global-input-sequences-p
     cm-add-after-cut-input-sequence
     cm-before-cut-input-sequence
     cm-after-cut-input-sequence))))


;; ============================================================
;; Extract the structural properties of an incoming-neighbor
;; list from GOOD-PROCS-P.
;; ============================================================


(defthm
  cl-good-procs-p-implies-good-proc-p

  (implies
   (and
    (good-procs-p ids procs all-ids)
    (memberp i ids))

   (good-proc-p
    (g i procs)
    all-ids)))


(defthm
  good-procs-p-implies-good-nbrs-from

  (implies
   (and
    (good-procs-p
     ids
     procs
     all-ids)

    (memberp i ids))

   (and
    (true-listp
     (g :nbrs-from
        (g i procs)))

    (uniquep
     (g :nbrs-from
        (g i procs)))

    (subset
     (g :nbrs-from
        (g i procs))
     all-ids))))


;; ============================================================
;; Closing one already-open incoming channel preserves the
;; waiting-marker invariant.
;; ============================================================


(defthm
  good-cut-meta-waiting-for-procs-p-of-remove-waiting-marker

  (implies
   (good-cut-meta-waiting-for-procs-p
    ids
    m)

   (good-cut-meta-waiting-for-procs-p
    ids

    (s :waiting-marker-from
       (s i
          (remove1-equal
           j
           (g i
              (g :waiting-marker-from m)))

          (g :waiting-marker-from m))

       m)))

  :hints
  (("Goal"
    :induct
    (good-cut-meta-waiting-for-procs-p
     ids
     m))

   ("Subgoal *1/2"
    :cases
    ((equal i
            (car ids))))))


;; ============================================================
;; A first target-marker receive:
;;
;;   1. removes I from :cut-not-taken;
;;   2. installs the still-open incoming channels for I;
;;   3. preserves the global waiting-marker invariant.
;; ============================================================


(defthm
  good-cut-meta-waiting-for-procs-p-of-first-marker-update

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p
     ids
     m)

    (uniquep
     (g :cut-not-taken m))

    (true-listp nbrs)

    (uniquep nbrs)

    (subset
     nbrs
     (g :proc-ids m)))

   (good-cut-meta-waiting-for-procs-p
    ids

    (s :cut-not-taken
       (remove1-equal
        i
        (g :cut-not-taken m))

       (s :waiting-marker-from
          (s i
             (remove1-equal j nbrs)
             (g :waiting-marker-from m))

          (s :before-cut-input-sequence
             new-before
             m)))))

  :hints
  (("Goal"
    :induct
    (good-cut-meta-waiting-for-procs-p
     ids
     m))

   ("Subgoal *1/2"
    :cases
    ((equal i
            (car ids))))))



;; ============================================================
;; Starting the target checkpoint:
;;
;;   1. removes the initiator from :cut-not-taken;
;;   2. installs all of its incoming channels as initially open;
;;   3. preserves the global waiting-marker invariant.
;; ============================================================


(defthm
  good-cut-meta-waiting-for-procs-p-of-start-checkpoint-update

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p
     ids
     m)

    (uniquep
     (g :cut-not-taken m))

    (true-listp nbrs)

    (uniquep nbrs)

    (subset
     nbrs
     (g :proc-ids m)))

   (good-cut-meta-waiting-for-procs-p
    ids

    (s :cut-not-taken
       (remove1-equal
        i
        (g :cut-not-taken m))

       (s :waiting-marker-from
          (s i
             nbrs
             (g :waiting-marker-from m))

          (s :before-cut-input-sequence
             new-before
             m)))))

  :hints
  (("Goal"
    :induct
    (good-cut-meta-waiting-for-procs-p
     ids
     m))

   ("Subgoal *1/2"
    :cases
    ((equal i
            (car ids))))))



;; ============================================================
;; LATER TARGET MARKER
;;
;; Process I has already taken its cut. The input is therefore
;; appended to the global after-cut sequence. The marker then
;; removes sender J from I's waiting-marker row.
;; ============================================================

(defthm
  good-cut-meta-waiting-for-procs-p-of-later-marker

  (implies
   (good-cut-meta-waiting-for-procs-p
    ids
    m)

   (good-cut-meta-waiting-for-procs-p
    ids

    (s :waiting-marker-from
       (s i
          (remove1-equal
           j
           (g i
              (g :waiting-marker-from m)))

          (g :waiting-marker-from m))

       (s :after-cut-input-sequence
          new-after
          m))))

  :hints
  (("Goal"
    :induct
    (good-cut-meta-waiting-for-procs-p
     ids
     m))

   ("Subgoal *1/2"
    :cases
    ((equal i
            (car ids))))))


;; ============================================================
;; TARGET START-CHECKPOINT
;;
;; Initially every process is in :cut-not-taken. The target
;; initiator takes its cut and installs its incoming-neighbor
;; list as its waiting-marker row.
;; ============================================================

(defthm
  good-cut-meta-waiting-for-procs-p-of-initial-start-checkpoint

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p
     (g :proc-ids m)
     m)

    (uniquep
     (g :proc-ids m))

    (equal
     (g :cut-not-taken m)
     (g :proc-ids m))

    (good-procs-p
     (g :proc-ids m)
     procs
     (g :proc-ids m))

    (memberp
     i
     (g :proc-ids m)))

   (good-cut-meta-waiting-for-procs-p
    (g :proc-ids m)

    (s :cut-not-taken
       (remove1-equal
        i
        (g :proc-ids m))

       (s :waiting-marker-from
          (s i
             (g :nbrs-from
                (g i procs))

             (g :waiting-marker-from m))

          (s :before-cut-input-sequence
             new-before
             m)))))

  :hints
  (("Goal"
    :use
    ((:instance
      good-cut-meta-waiting-for-procs-p-of-start-checkpoint-update

      (ids
       (g :proc-ids m))

      (nbrs
       (g :nbrs-from
          (g i procs))))))

   ("Goal"
    :in-theory
    (enable
     good-procs-p-implies-good-nbrs-from))))



;; ============================================================
;; FIRST TARGET MARKER
;;
;; Initially every process is in :cut-not-taken. Process I
;; takes its cut when receiving the first target marker from J.
;; All other incoming channels remain open.
;; ============================================================

(defthm
  good-cut-meta-waiting-for-procs-p-of-initial-first-marker

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p
     (g :proc-ids m)
     m)

    (uniquep
     (g :proc-ids m))

    (equal
     (g :cut-not-taken m)
     (g :proc-ids m))

    (good-procs-p
     (g :proc-ids m)
     procs
     (g :proc-ids m))

    (memberp
     i
     (g :proc-ids m)))

   (good-cut-meta-waiting-for-procs-p
    (g :proc-ids m)

    (s :cut-not-taken
       (remove1-equal
        i
        (g :proc-ids m))

       (s :waiting-marker-from
          (s i
             (remove1-equal
              j
              (g :nbrs-from
                 (g i procs)))

             (g :waiting-marker-from m))

          (s :before-cut-input-sequence
             new-before
             m)))))

  :hints
  (("Goal"
    :use
    ((:instance
      good-cut-meta-waiting-for-procs-p-of-first-marker-update

      (ids
       (g :proc-ids m))

      (nbrs
       (g :nbrs-from
          (g i procs))))))

   ("Goal"
    :in-theory
    (enable
     good-procs-p-implies-good-nbrs-from))))



(defthm
  good-cut-meta-p-preserved-by-process-cut-step

  (implies
   (and
    (good-cut-meta-p m)

    (cut-meta-imp-consistent-p
     m
     st)

    (good-state-p st)

    (legal-inputp
     st
     input))

   (good-cut-meta-p
    (process-cut-step
     input
     st
     m)))
  :otf-flg t
  :hints
  (("Goal"
    :in-theory
    (disable
     cut-meta-imp-procs-consistent-p
     snapshot-counters-good-for-procs-p
     nbrs-from-to-consistent-p
     nbrs-to-from-consistent-p
     good-channels-p))))


;; (defthm proc-ids-of-step-normal
;;   (equal
;;    (proc-ids
;;     (step-normal st i))

;;    (proc-ids st)))

;; (defthm counter-of-g-of-procs-of-step-normal
;;   (equal
;;    (counter
;;     (g j
;;        (procs
;;         (step-normal st i))))

;;    (counter
;;     (g j
;;        (procs st)))))


;; (defthm
;;   cut-meta-imp-procs-consistent-p-of-step-normal

;;   (equal
;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid
;;     m
;;     (procs
;;      (step-normal st i)))

;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid
;;     m
;;     (procs st))))

;; (defthm
;;   target-counter-bound-preserved-by-start-checkpoint-helper

;;   (implies
;;    (< target-counter
;;       (counter
;;        (g initiator procs)))

;;    (< target-counter
;;       (counter
;;        (g initiator
;;           (start-checkpoint-helper
;;            procs
;;            i)))))

;;   :hints
;;   (("Goal"
;;     :cases
;;     ((equal i initiator)))))




;; (defun target-cut-proc-view (target-sid p)
;;   (let ((has-sid
;;          (memberp target-sid
;;                   (snapshot-ids p))))
;;     (list
;;      has-sid
;;      (if has-sid
;;          (snapshot-waiting-marker-from
;;           (snapshot-entry target-sid p))
;;        nil))))



;; (defthm
;;   cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same

;;   (implies
;;    (and
;;     (cut-meta-imp-procs-consistent-p
;;      ids
;;      target-sid
;;      m
;;      procs)

;;     (equal
;;      (target-cut-proc-view
;;       target-sid
;;       new-p)

;;      (target-cut-proc-view
;;       target-sid
;;       (g i procs))))

;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid
;;     m
;;     (s i new-p procs)))

;;   :hints
;;   (("Goal"
;;     :induct
;;     (len ids))

;;    ;; The LEN induction has only one nontrivial inductive step.
;;    ;; Split according to whether the current process is the
;;    ;; process being replaced.
;;    ("Subgoal *1/1"
;;     :cases
;;     ((equal i
;;             (car ids))))))

;; ;; Updating the counter does not affect the target-cut view.

;; (defthm target-cut-proc-view-of-counter-update
;;   (equal
;;    (target-cut-proc-view
;;     target-sid
;;     (s :counter new-counter p))

;;    (target-cut-proc-view
;;     target-sid
;;     p)))

;; ;; Installing an entry for another SID does not affect TARGET-SID.

;; (defthm
;;   target-cut-proc-view-of-install-snapshot-entry-other-sid

;;   (implies
;;    (not (equal target-sid new-sid))

;;    (equal
;;     (target-cut-proc-view
;;      target-sid
;;      (install-snapshot-entry
;;       new-sid
;;       entry
;;       p))

;;     (target-cut-proc-view
;;      target-sid
;;      p))))


;; ;; Starting another checkpoint preserves the updated process's
;; ;; view of TARGET-SID.

;; (defthm
;;   target-cut-proc-view-of-g-of-start-checkpoint-helper-other-sid

;;   (implies
;;    (not
;;     (equal
;;      target-sid
;;      (list i
;;            (counter (g i procs)))))

;;    (equal
;;     (target-cut-proc-view
;;      target-sid
;;      (g i
;;         (start-checkpoint-helper procs i)))

;;     (target-cut-proc-view
;;      target-sid
;;      (g i procs)))))


;; (defthm
;;   cut-meta-imp-procs-consistent-p-of-start-checkpoint-helper-other-sid

;;   (implies
;;    (and
;;     (cut-meta-imp-procs-consistent-p
;;      ids
;;      target-sid
;;      m
;;      procs)

;;     (not
;;      (equal
;;       target-sid
;;       (list i
;;             (counter (g i procs))))))

;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid
;;     m
;;     (start-checkpoint-helper procs i)))

;;   :hints
;;   (("Goal"
;;     :do-not-induct t

;;     :use
;;     ((:instance
;;       target-cut-proc-view-of-g-of-start-checkpoint-helper-other-sid)

;;      (:instance
;;       cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same

;;       (new-p
;;        (g i
;;           (start-checkpoint-helper procs i)))))

;;     :in-theory
;;     (e/d
;;      (start-checkpoint-helper)

;;      (cut-meta-imp-procs-consistent-p
;;       target-cut-proc-view)))))


;; (defthm
;;   counter-of-g-of-s-update-proc-for-normal-msg-core

;;   (equal
;;    (counter
;;     (g k
;;        (s i
;;           (update-proc-for-normal-msg-core
;;            (g i procs)
;;            j
;;            msg)
;;           procs)))

;;    (counter
;;     (g k procs)))

;;   :hints
;;   (("Goal"
;;     :cases
;;     ((equal k i)))))



;; (defthm
;;   snapshot-waiting-marker-from-of-record-msg-in-snapshots

;;   (equal
;;    (snapshot-waiting-marker-from
;;     (g target-sid
;;        (record-msg-in-snapshots
;;         snapshots snapshot-ids j msg)))

;;    (snapshot-waiting-marker-from
;;     (g target-sid snapshots)))

;;   :hints
;;   (("Goal"
;;     :induct
;;     (record-msg-in-snapshots
;;      snapshots snapshot-ids j msg))

;;    ("Subgoal *1/2"
;;     :cases
;;     ((equal target-sid
;;             (car snapshot-ids))))))




;; (defthm
;;   target-cut-proc-view-of-update-proc-for-normal-msg-core

;;   (equal
;;    (target-cut-proc-view
;;     target-sid
;;     (update-proc-for-normal-msg-core p j msg))

;;    (target-cut-proc-view
;;     target-sid
;;     p)))



;; (defthm
;;   cut-meta-imp-procs-consistent-p-of-update-proc-for-normal-msg-core

;;   (implies
;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid
;;     m
;;     procs)

;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid
;;     m
;;     (s i
;;        (update-proc-for-normal-msg-core
;;         (g i procs)
;;         j
;;         msg)
;;        procs)))

;;   :hints
;;   (("Goal"
;;     :use
;;     ((:instance
;;       cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same

;;       (new-p
;;        (update-proc-for-normal-msg-core
;;         (g i procs)
;;         j
;;         msg)))))))



;; (defthm
;;   cut-meta-imp-procs-consistent-p-implies-cut-status

;;   (implies
;;    (and
;;     (cut-meta-imp-procs-consistent-p
;;      ids target-sid m procs)

;;     (memberp i ids))

;;    (equal
;;     (cm-cut-not-taken-p m i)

;;     (not
;;      (memberp
;;       target-sid
;;       (snapshot-ids
;;        (g i procs)))))))


;; (defthm
;;   cm-cut-not-taken-p-of-s-before-cut-input-sequence

;;   (equal
;;    (cm-cut-not-taken-p
;;     (s :before-cut-input-sequence xs m)
;;     i)

;;    (cm-cut-not-taken-p
;;     m
;;     i)))

;; (defthm
;;   cm-cut-not-taken-p-of-s-after-cut-input-sequence

;;   (equal
;;    (cm-cut-not-taken-p
;;     (s :after-cut-input-sequence xs m)
;;     i)

;;    (cm-cut-not-taken-p
;;     m
;;     i)))



;; (defthm
;;   target-cut-proc-view-of-update-proc-for-first-marker-msg-other-sid

;;   (implies
;;    (not (equal target-sid sid))

;;    (equal
;;     (target-cut-proc-view
;;      target-sid
;;      (update-proc-for-first-marker-msg p sid j))

;;     (target-cut-proc-view
;;      target-sid
;;      p))))

;; (defthm
;;   target-cut-proc-view-of-update-proc-for-non-first-marker-msg-other-sid

;;   (implies
;;    (not (equal target-sid sid))

;;    (equal
;;     (target-cut-proc-view
;;      target-sid
;;      (update-proc-for-non-first-marker-msg p sid j))

;;     (target-cut-proc-view
;;      target-sid
;;      p))))





;; (defthm
;;   target-cut-proc-view-of-update-proc-for-first-marker-msg-same-sid

;;   (implies
;;    (and
;;     (true-listp
;;      (nbrs-from p))

;;     (uniquep
;;      (nbrs-from p)))

;;    (equal
;;     (target-cut-proc-view
;;      sid
;;      (update-proc-for-first-marker-msg
;;       p sid j))

;;     (list
;;      t

;;      (remove1-equal
;;       j
;;       (nbrs-from p)))))

;;   :hints
;;   (("Goal"
;;     :in-theory
;;     (enable
;;      target-cut-proc-view
;;      update-proc-for-first-marker-msg
;;      install-snapshot-entry
;;      add-snapshot-id
;;      make-snapshot-entry))))


;; ;; REMOVE-FROM-LIST removes every occurrence.  On a proper,
;; ;; duplicate-free list, this equals REMOVE1-EQUAL.

;; (defthm remove-from-list-when-not-memberp-and-true-listp
;;   (implies
;;    (and
;;     (true-listp xs)
;;     (not (memberp x xs)))

;;    (equal
;;     (remove-from-list xs x)
;;     xs)))

;; (defthm
;;   remove-from-list-equals-remove1-equal-when-true-listp-and-uniquep

;;   (implies
;;    (and
;;     (true-listp xs)
;;     (uniquep xs))

;;    (equal
;;     (remove-from-list xs x)
;;     (remove1-equal x xs))))




;; ;; ============================================================
;; ;; Generic synchronized first-cut update.
;; ;;
;; ;; NEW-P has taken TARGET-SID and its target waiting row is
;; ;; NEW-WAIT.  Metadata performs the corresponding updates.
;; ;; ============================================================

;; (defthm
;;   cut-meta-imp-procs-consistent-p-of-first-target-view-update

;;   (implies
;;    (and
;;     (cut-meta-imp-procs-consistent-p
;;      ids target-sid m procs)

;;     (true-listp
;;      (cm-cut-not-taken m))

;;     (uniquep
;;      (cm-cut-not-taken m))

;;     (cm-cut-not-taken-p m i)

;;     (equal
;;      (target-cut-proc-view
;;       target-sid
;;       new-p)

;;      (list t new-wait)))

;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid

;;     (s :cut-not-taken
;;        (remove1-equal
;;         i
;;         (cm-cut-not-taken m))

;;        (s :waiting-marker-from
;;           (s i
;;              new-wait
;;              (cm-waiting-marker-from m))

;;           m))

;;     (s i new-p procs)))

;;   :hints
;;   (("Goal"
;;     :induct
;;     (len ids))

;;    ("Subgoal *1/1"
;;     :cases
;;     ((equal i
;;             (car ids))))))


;; (defthm
;;   cut-meta-imp-procs-consistent-p-of-first-target-marker

;;   (implies
;;    (and
;;     (cut-meta-imp-procs-consistent-p
;;      ids target-sid m procs)

;;     (true-listp
;;      (cm-cut-not-taken m))

;;     (uniquep
;;      (cm-cut-not-taken m))

;;     (cm-cut-not-taken-p m i)

;;     (true-listp
;;      (nbrs-from (g i procs)))

;;     (uniquep
;;      (nbrs-from (g i procs))))

;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid

;;     (s :cut-not-taken
;;        (remove1-equal
;;         i
;;         (cm-cut-not-taken m))

;;        (s :waiting-marker-from
;;           (s i
;;              (remove1-equal
;;               j
;;               (nbrs-from (g i procs)))

;;              (cm-waiting-marker-from m))

;;           m))

;;     (s i
;;        (update-proc-for-first-marker-msg
;;         (g i procs)
;;         target-sid
;;         j)

;;        procs)))

;;   :hints
;;   (("Goal"
;;     :do-not-induct t

;;     :use
;;     ((:instance
;;       target-cut-proc-view-of-update-proc-for-first-marker-msg-same-sid

;;       (p
;;        (g i procs))

;;       (sid
;;        target-sid))

;;      (:instance
;;       cut-meta-imp-procs-consistent-p-of-first-target-view-update

;;       (new-p
;;        (update-proc-for-first-marker-msg
;;         (g i procs)
;;         target-sid
;;         j))

;;       (new-wait
;;        (remove1-equal
;;         j
;;         (nbrs-from (g i procs))))))

;;     :in-theory
;;     (disable
;;      cut-meta-imp-procs-consistent-p
;;      target-cut-proc-view
;;      update-proc-for-first-marker-msg
;;      cut-meta-imp-procs-consistent-p-of-first-target-view-update))))





;; ;; The first-marker and target-start updates place the BEFORE
;; ;; sequence update underneath the cut and waiting-row updates.

;; (defthm
;;   cut-meta-imp-procs-consistent-p-ignores-before-sequence-under-cut-update

;;   (equal
;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid

;;     (s :cut-not-taken
;;        cut-not-taken

;;        (s :waiting-marker-from
;;           waiting-marker-from

;;           (s :before-cut-input-sequence
;;              before-sequence
;;              m)))

;;     procs)

;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid

;;     (s :cut-not-taken
;;        cut-not-taken

;;        (s :waiting-marker-from
;;           waiting-marker-from
;;           m))

;;     procs))

;;   :hints
;;   (("Goal"
;;     :induct
;;     (len ids)

;;     :in-theory
;;     (enable
;;      cut-meta-imp-procs-consistent-p))))



;; ;; A later-marker update places the AFTER sequence update
;; ;; underneath the waiting-row update.

;; (defthm
;;   cut-meta-imp-procs-consistent-p-ignores-after-sequence-under-waiting-update

;;   (equal
;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid

;;     (s :waiting-marker-from
;;        waiting-marker-from

;;        (s :after-cut-input-sequence
;;           after-sequence
;;           m))

;;     procs)

;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid

;;     (s :waiting-marker-from
;;        waiting-marker-from
;;        m)

;;     procs))

;;   :hints
;;   (("Goal"
;;     :induct
;;     (len ids)

;;     :in-theory
;;     (enable
;;      cut-meta-imp-procs-consistent-p))))




;; (defthm
;;   cut-meta-imp-procs-consistent-p-of-first-target-marker-from-good-procs

;;   (implies
;;    (and
;;     ;; Existing metadata/implementation consistency.
;;     (cut-meta-imp-procs-consistent-p
;;      ids
;;      target-sid
;;      m
;;      procs)

;;     ;; I is one of the processes governed by the invariant.
;;     (memberp i ids)

;;     ;; The implementation has not yet taken TARGET-SID at I.
;;     (not
;;      (memberp
;;       target-sid
;;       (snapshot-ids
;;        (g i procs))))

;;     ;; Structural properties of the metadata cut set.
;;     (true-listp
;;      (cm-cut-not-taken m))

;;     (uniquep
;;      (cm-cut-not-taken m))

;;     ;; Supplies properness and uniqueness of I's incoming
;;     ;; neighbor list.
;;     (good-procs-p
;;      ids
;;      procs
;;      ids))

;;    ;; The first target marker updates metadata and the
;;    ;; implementation process in corresponding ways.
;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid

;;     (s :cut-not-taken
;;        (remove1-equal
;;         i
;;         (cm-cut-not-taken m))

;;        (s :waiting-marker-from
;;           (s i
;;              (remove1-equal
;;               j
;;               (nbrs-from (g i procs)))

;;              (cm-waiting-marker-from m))

;;           m))

;;     (s i
;;        (update-proc-for-first-marker-msg
;;         (g i procs)
;;         target-sid
;;         j)

;;        procs)))

;;   :hints
;;   (("Goal"
;;     :do-not-induct t

;;     :use
;;     ((:instance
;;       cut-meta-imp-procs-consistent-p-implies-cut-status)

;;      (:instance
;;       good-procs-p-implies-good-nbrs-from
;;       (all-ids ids))

;;      (:instance
;;       cut-meta-imp-procs-consistent-p-of-first-target-marker))

;;     :in-theory
;;     (disable
;;      cut-meta-imp-procs-consistent-p
;;      good-procs-p
;;      update-proc-for-first-marker-msg
;;      cut-meta-imp-procs-consistent-p-of-first-target-marker))))



(defthm cut-meta-imp-consistent-p-preserved-by-step
  (implies
   (and
    (cut-meta-imp-consistent-p m st)
    (good-state-p st)
    (good-cut-meta-p m)
    (legal-inputp st input))

   (cut-meta-imp-consistent-p
    (process-cut-step input st m)
    (system-step st input)))
  :hints
  (("Goal"
    :in-theory
    (disable step-normal
	     start-checkpoint-helper
	     cm-cut-not-taken-p
	     get-msg-from-channel
	     update-proc-for-first-marker-msg
	     update-proc-for-normal-msg-core
	          cm-cut-not-taken
		  good-state-p
		  good-cut-meta-p
		  cut-markers-in-transit-p
		  cut-meta-imp-consistent-p
		  recovery-free-state-p
		  get-msg-from-channel
		  remove-message-from-channel
		  legal-input-sequencep
		  current-msg-for-receive
		  legal-inputp
		  cm-cut-not-taken-p
		  cm-remove-cut-not-taken
		  cm-waiting-marker-for
		  cm-set-waiting-marker-for
		  cm-remove-cut-not-taken
		  cm-add-after-cut-input-sequence
		  cm-add-before-cut-input-sequence
		  cm-after-cut-input-sequence
		  cm-before-cut-input-sequence
		  cm-waiting-marker-from
		  ))))

;; ------------------------------------------------------------
;; GOOD-CUT-META and CUT-META/IMPLEMENTATION CONSISTENCY
;; are preserved together over an entire legal input segment.
;;
;; The induction carries both invariants simultaneously because
;; each one-step preservation theorem may rely on the other at
;; the current state.
;;
;; GOOD-STATE-P is also preserved along the implementation run
;; and supplies the implementation well-formedness needed at
;; every recursive step.
;; ------------------------------------------------------------


;; ------------------------------------------------------------
;; GOOD-CUT-META preservation over a complete input segment.
;; ------------------------------------------------------------

(defthm
  good-cut-meta-p-over-process-cut-segment

  (implies
   (and
    (good-cut-meta-p m)

    (cut-meta-imp-consistent-p
     m
     st)

    (good-state-p st)

    (legal-input-sequencep
     st
     inputs))

   (good-cut-meta-p
    (process-cut-segment
     inputs
     st
     m))))



;; ------------------------------------------------------------
;; Metadata/implementation consistency over a complete segment.
;;
;; PROCESS-CUT-SEGMENT collects metadata over INPUTS while
;; RUN-IMP executes the same concrete inputs.  If they agree at
;; the beginning and the required invariants hold, they agree
;; again at the end of the segment.
;; ------------------------------------------------------------

(defthm
  cut-meta-imp-consistent-p-over-process-cut-segment

  (implies
   (and
    (cut-meta-imp-consistent-p
     m
     st)

    (good-cut-meta-p m)

    (good-state-p st)

    (legal-input-sequencep
     st
     inputs))

   (cut-meta-imp-consistent-p
    (process-cut-segment
     inputs
     st
     m)

    (run-imp
     st
     inputs))))
