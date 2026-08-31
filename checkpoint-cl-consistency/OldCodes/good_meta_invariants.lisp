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

;;----------------------------------------
;; Metadata/implementation consistency is preserved by one step.
;;
;; PROCESS-CUT-STEP updates the cut metadata according to INPUT,
;; while SYSTEM-STEP performs the corresponding implementation
;; transition.
;;
;; If the metadata and implementation agree before a legal step,
;; then they should continue to agree afterward:
;;
;;   - :cut-not-taken matches presence/absence of TARGET-SID
;;     in each implementation process,
;;
;;   - metadata waiting-marker rows match the corresponding
;;     implementation snapshot waiting-marker rows,
;;
;;   - the metadata and implementation process universes agree,
;;
;;   - and the target SID remains consistent with the initiator's
;;     checkpoint counter.
;;
;; We leave the proof until the consistency definition is stable,
;; since the reorder development may require strengthening or
;; changing exactly what correspondence is maintained.
;; ------------------------------------------------------------

;; (defthm
;;   cut-meta-imp-procs-consistent-p-of-s-inputs-before-cut

;;   (equal
;;    (cut-meta-imp-procs-consistent-p
;;     ids target-sid
;;     (s :inputs-before-cut value m)
;;     procs)

;;    (cut-meta-imp-procs-consistent-p
;;     ids target-sid
;;     m
;;     procs))

;;   :hints
;;   (("Goal"
;;     :induct
;;     (cut-meta-imp-procs-consistent-p
;;      ids target-sid m procs))

;;     :in-theory
;;     (enable
;;      cut-meta-imp-procs-consistent-p)))



;; (defthm
;;   cut-meta-imp-procs-consistent-p-of-local-state-update-before-cut

;;   (implies
;;    (and
;;     (cut-meta-imp-procs-consistent-p
;;      ids target-sid m procs)

;;     (memberp i
;;              (g :cut-not-taken m)))

;;    (cut-meta-imp-procs-consistent-p
;;     ids
;;     target-sid
;;     m

;;     (s i
;;        (s :local-state
;;           new-local
;;           (g i procs))
;;        procs)))

;;   :hints
;;   (("Goal"
;;     :induct
;;     (cut-meta-imp-procs-consistent-p
;;      ids target-sid m procs))

;;    ("Subgoal *1/2"
;;     :cases
;;     ((equal i (car ids))))))


;; ============================================================

(defun target-cut-proc-view (target-sid p)
  (let ((has-sid
         (memberp target-sid
                  (snapshot-ids p))))
    (list
     has-sid
     (if has-sid
         (snapshot-waiting-marker-from
          (snapshot-entry target-sid p))
       nil))))



(defthm
  cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs)

    (equal
     (target-cut-proc-view
      target-sid
      new-p)

     (target-cut-proc-view
      target-sid
      (g i procs))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (s i new-p procs)))

  :hints
  (("Goal"
    :induct
    (len ids)

    :in-theory
    (enable
     cut-meta-imp-procs-consistent-p
     target-cut-proc-view))

   ;; The LEN induction has only one nontrivial inductive step.
   ;; Split according to whether the current process is the
   ;; process being replaced.
   ("Subgoal *1/1"
    :cases
    ((equal i
            (car ids))))))



(defthm
  target-cut-proc-view-of-unobserved-field-update

  (implies
   (and
    (not (equal field :snapshot-ids))
    (not (equal field :snapshots)))

   (equal
    (target-cut-proc-view
     target-sid
     (s field value p))

    (target-cut-proc-view
     target-sid
     p)))

  :hints
  (("Goal"
    :in-theory
    (enable target-cut-proc-view))))


(defthm
  cut-meta-imp-procs-consistent-p-of-unobserved-proc-field-update

  (implies
   (and
    (not (equal field :snapshot-ids))
    (not (equal field :snapshots)))

   (equal
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     (s i
        (s field value (g i procs))
        procs))

    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs)))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same
      (new-p
       (s field value (g i procs))))))))


;; ============================================================
;; NORMAL-MESSAGE RECORDING DOES NOT CHANGE THE TARGET VIEW
;; ============================================================

(defthm
  snapshot-waiting-marker-from-of-record-msg-in-snapshots

  (equal
   (snapshot-waiting-marker-from
    (g target-sid
       (record-msg-in-snapshots
        snapshots snapshot-ids j msg)))

   (snapshot-waiting-marker-from
    (g target-sid snapshots)))

  :hints
  (("Goal"
    :induct
    (record-msg-in-snapshots
     snapshots snapshot-ids j msg))

   ("Subgoal *1/2"
    :cases
    ((equal target-sid
            (car snapshot-ids))))))


(defthm
  target-cut-proc-view-of-update-proc-for-normal-msg-core

  (equal
   (target-cut-proc-view
    target-sid
    (update-proc-for-normal-msg-core p j msg))

   (target-cut-proc-view
    target-sid
    p))

  :hints
  (("Goal"
    :in-theory
    (enable
     target-cut-proc-view
     update-proc-for-normal-msg-core))))


(defthm
  cut-meta-imp-procs-consistent-p-of-update-proc-for-normal-msg-core

  (implies
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    procs)

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (s i
       (update-proc-for-normal-msg-core
        (g i procs)
        j
        msg)
       procs)))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same

      (new-p
       (update-proc-for-normal-msg-core
        (g i procs)
        j
        msg))))

    :in-theory
    (disable
     cut-meta-imp-procs-consistent-p
     target-cut-proc-view
     update-proc-for-normal-msg-core
     record-msg-in-snapshots))))

;; ============================================================
;; RECOVERY UPDATES DO NOT CHANGE SNAPSHOT CONTROL
;; ============================================================

(defthm
  target-cut-proc-view-of-update-proc-for-first-recovery-msg

  (equal
   (target-cut-proc-view
    target-sid
    (update-proc-for-first-recovery-msg p sid j))

   (target-cut-proc-view
    target-sid
    p))

  :hints
  (("Goal"
    :in-theory
    (enable
     target-cut-proc-view
     update-proc-for-first-recovery-msg))))


(defthm
  target-cut-proc-view-of-update-proc-for-non-first-recovery-msg

  (equal
   (target-cut-proc-view
    target-sid
    (update-proc-for-non-first-recovery-msg p j))

   (target-cut-proc-view
    target-sid
    p))

  :hints
  (("Goal"
    :in-theory
    (enable
     target-cut-proc-view
     update-proc-for-non-first-recovery-msg))))


(defthm
  target-cut-proc-view-of-g-of-start-recovery-helper

  (equal
   (target-cut-proc-view
    target-sid
    (g k (start-recovery-helper procs i)))

   (target-cut-proc-view
    target-sid
    (g k procs)))

  :hints
  (("Goal"
    :cases
    ((equal k i))

    :in-theory
    (enable
     target-cut-proc-view
     start-recovery-helper))))

(defthm
  cut-meta-imp-procs-consistent-p-of-start-recovery-helper

  (implies
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    procs)

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (start-recovery-helper procs i)))

  :hints
  (("Goal"
    :use
    ((:instance
      target-cut-proc-view-of-g-of-start-recovery-helper

      (k i))

     (:instance
      cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same

      (new-p
       (g i
          (start-recovery-helper procs i)))))

    ;; Expand only enough to show that START-RECOVERY-HELPER
    ;; replaces process I with its updated process record.
    :in-theory
    (e/d
     (start-recovery-helper)

     (cut-meta-imp-procs-consistent-p
      target-cut-proc-view
      recovery-local-state-after-replay
      replay-channel-snapshots
      replay-msgs-on-channel)))))

;; ============================================================
;; OTHER-SID CHECKPOINT AND MARKER UPDATES
;; ============================================================

(defthm
  memberp-of-add-snapshot-id-when-different

  (implies
   (not (equal target-sid sid))

   (equal
    (memberp target-sid
             (add-snapshot-id sid snapshot-ids))

    (memberp target-sid snapshot-ids)))

  :hints
  (("Goal"
    :in-theory
    (enable add-snapshot-id))))


(defthm
  target-cut-proc-view-of-install-other-snapshot

  (implies
   (not (equal target-sid sid))

   (equal
    (target-cut-proc-view
     target-sid
     (install-snapshot-entry sid entry p))

    (target-cut-proc-view
     target-sid
     p)))

  :hints
  (("Goal"
    :in-theory
    (enable
     target-cut-proc-view
     install-snapshot-entry))))


(defthm
  target-cut-proc-view-of-update-proc-for-first-marker-msg-other-sid

  (implies
   (not (equal target-sid sid))

   (equal
    (target-cut-proc-view
     target-sid
     (update-proc-for-first-marker-msg p sid j))

    (target-cut-proc-view
     target-sid
     p)))

  :hints
  (("Goal"
    :in-theory
    (enable update-proc-for-first-marker-msg))))


(defthm
  target-cut-proc-view-of-update-proc-for-non-first-marker-msg-other-sid

  (implies
   (not (equal target-sid sid))

   (equal
    (target-cut-proc-view
     target-sid
     (update-proc-for-non-first-marker-msg p sid j))

    (target-cut-proc-view
     target-sid
     p)))

  :hints
  (("Goal"
    :in-theory
    (enable
     target-cut-proc-view
     update-proc-for-non-first-marker-msg
     set-snapshot-entry))))


(defthm
  target-cut-proc-view-of-g-of-start-checkpoint-helper-other-sid

  (implies
   (not
    (equal
     target-sid
     (list i
           (counter (g i procs)))))

   (equal
    (target-cut-proc-view
     target-sid
     (g k (start-checkpoint-helper procs i)))

    (target-cut-proc-view
     target-sid
     (g k procs))))

  :hints
  (("Goal"
    :cases
    ((equal k i))

    :in-theory
    (enable start-checkpoint-helper))))


(defthm
  cut-meta-imp-procs-consistent-p-of-start-checkpoint-helper-other-sid

  (implies
   (and
    ;; The checkpoint being started is not TARGET-SID.
    (not
     (equal
      target-sid
      (list i
            (counter (g i procs)))))

    ;; Existing target-cut consistency.
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (start-checkpoint-helper procs i)))

  :hints
  (("Goal"
    :use
    ((:instance
      target-cut-proc-view-of-g-of-start-checkpoint-helper-other-sid

      (k i))

     (:instance
      cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same

      (new-p
       (g i
          (start-checkpoint-helper procs i)))))

    ;; Expose only that START-CHECKPOINT-HELPER replaces
    ;; process I. Its internal snapshot construction remains closed.
    :in-theory
    (e/d
     (start-checkpoint-helper)

     (cut-meta-imp-procs-consistent-p
      target-cut-proc-view
      install-snapshot-entry
      make-snapshot-entry
      add-snapshot-id)))))


;; ============================================================
;; REMOVE-FROM-LIST / REMOVE1-EQUAL BRIDGE
;; ============================================================

(defthm
  remove-from-list-equals-remove1-equal-when-uniquep

  (implies
   (uniquep xs)

   (equal
    (remove-from-list xs x)
    (remove1-equal x xs)))

  :hints
  (("Goal"
    :induct xs)))


;; ============================================================
;; SYNCHRONIZED TARGET-SID CONTROL UPDATES
;; ============================================================

(defthm
  memberp-of-remove1-equal-when-different

  (implies
   (not (equal x y))

   (equal
    (memberp x
             (remove1-equal y xs))

    (memberp x xs))))

(defthm
  not-memberp-of-remove1-equal-when-uniquep

  (implies
   (and
    (uniquep xs)
    (memberp x xs))

   (not
    (memberp x
             (remove1-equal x xs)))))


;; ============================================================
;; Induction scheme for a single-process synchronized update.
;;
;; At every position in IDS, distinguish whether the current
;; process is the process I being updated.
;; ============================================================

(defun cut-meta-target-start-induct (ids i branch)
  (declare
   (xargs :measure (acl2-count ids)))

  (if (endp ids)

      branch

    (if (equal i (car ids))

        (cut-meta-target-start-induct
         (cdr ids)
         i
         t)

      (cut-meta-target-start-induct
       (cdr ids)
       i
       nil))))

;; ============================================================
;; Total read-after-write rule.
;;
;; Unlike separate same-key and different-key lemmas, this rule
;; works before ACL2 knows whether K1 and K2 are equal.
;; ============================================================

(defthm cl-g-of-s-as-if
  (equal
   (g k1 (s k2 value record))

   (if (equal k1 k2)
       value
     (g k1 record)))

  :hints
  (("Goal"
    :cases
    ((equal k1 k2)))))


;; ============================================================
;; Membership after removing one element from a unique list.
;;
;; If K is I, K is absent after the removal.
;; Otherwise, K's membership is unchanged.
;; ============================================================

(defthm memberp-of-remove1-equal-under-uniquep
  (implies
   (uniquep xs)

   (equal
    (memberp k
             (remove1-equal i xs))

    (if (equal k i)
        nil
      (memberp k xs))))

  :hints
  (("Goal"
    :cases
    ((equal k i)))))


(defthm
  cut-meta-imp-procs-consistent-p-of-target-start

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (uniquep
     (cm-cut-not-taken m))

    (cm-cut-not-taken-p m i)

    (equal
     target-sid
     (list i
           (counter (g i procs)))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))

       (s :waiting-marker-from
          (s i
             (nbrs-from (g i procs))
             (cm-waiting-marker-from m))
          m))

    (start-checkpoint-helper procs i)))

  :hints
  (("Goal"
    :induct (len ids)

    :in-theory
    (enable
     cut-meta-imp-procs-consistent-p
     cm-cut-not-taken-p
     cm-cut-not-taken
     cm-waiting-marker-from
     start-checkpoint-helper
     install-snapshot-entry
     add-snapshot-id))))



(defthm
  cut-meta-imp-procs-consistent-p-of-target-start

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs)

    ;; REMOVE1-EQUAL must completely remove I.
    (uniquep
     (cm-cut-not-taken m))

    ;; Before this step, I has not taken the target cut.
    (cm-cut-not-taken-p m i)

    ;; This is exactly the target checkpoint.
    (equal
     target-sid
     (list i
           (counter (g i procs)))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))

       (s :waiting-marker-from
          (s i
             (nbrs-from (g i procs))
             (cm-waiting-marker-from m))
          m))

    (start-checkpoint-helper procs i)))

  :hints
  (("Goal"
    :induct
    (len ids)

    :in-theory
    (enable
     cut-meta-imp-procs-consistent-p
     cm-cut-not-taken-p
     cm-cut-not-taken
     cm-waiting-marker-from
     start-checkpoint-helper
     install-snapshot-entry
     add-snapshot-id))

   ("Subgoal *1/1.2.2"
    :cases
    ((equal i
            (car ids))))))




;; ============================================================
;; FIRST-MARKER IMPLEMENTATION FACTS
;;
;; Installing the first marker snapshot:
;;
;;   1. makes SID a known snapshot identifier;
;;   2. initializes its waiting row to all incoming neighbors
;;      except the marker sender.
;; ============================================================

(defthm memberp-own-sid-after-update-proc-for-first-marker-msg
  (memberp
   sid
   (snapshot-ids
    (update-proc-for-first-marker-msg
     p sid j)))

  :hints
  (("Goal"
    :in-theory
    (enable
     update-proc-for-first-marker-msg
     install-snapshot-entry
     add-snapshot-id
     memberp))))


(defthm
  snapshot-waiting-marker-from-after-update-proc-for-first-marker-msg

  (equal
   (snapshot-waiting-marker-from
    (snapshot-entry
     sid
     (update-proc-for-first-marker-msg
      p sid j)))

   (remove-from-list
    (nbrs-from p)
    j))

  :hints
  (("Goal"
    :in-theory
    (enable
     update-proc-for-first-marker-msg
     install-snapshot-entry
     make-snapshot-entry))))



(defthm remove-from-list-when-not-memberp
  (implies
   (and
    (true-listp xs)
    (not (memberp x xs)))

   (equal
    (remove-from-list xs x)
    xs))

  :hints
  (("Goal"
    :induct
    (remove-from-list xs x)

    :in-theory
    (enable
     memberp
     remove-from-list))))




;; REMOVE-FROM-LIST removes every occurrence, whereas
;; REMOVE1-EQUAL removes only the first. They agree on a
;; proper duplicate-free list.

(defthm remove-from-list-equals-remove1-equal-when-uniquep
  (implies
   (and
    (true-listp xs)
    (uniquep xs))

   (equal
    (remove-from-list xs x)
    (remove1-equal x xs)))

  :hints
  (("Goal"
    :induct
    (remove-from-list xs x)

    :in-theory
    (enable
     memberp
     uniquep
     remove-from-list
     remove1-equal))))



(defthm
  cut-meta-imp-procs-consistent-p-of-first-target-marker

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (true-listp
     (cm-cut-not-taken m))

    (uniquep
     (cm-cut-not-taken m))

    (cm-cut-not-taken-p m i)

    (true-listp
     (nbrs-from (g i procs)))

    (uniquep
     (nbrs-from (g i procs))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))

       (s :waiting-marker-from
          (s i
             (remove1-equal
              j
              (nbrs-from (g i procs)))
             (cm-waiting-marker-from m))
          m))

    (s i
       (update-proc-for-first-marker-msg
        (g i procs)
        target-sid
        j)
       procs)))

  :hints
  (("Goal"
    :induct (len ids)

    :in-theory
    (e/d
     (cut-meta-imp-procs-consistent-p
      cm-cut-not-taken-p
      cm-cut-not-taken
      cm-waiting-marker-from)

     ;; Keep the implementation update opaque during the
     ;; recursive lifting proof. The two observable facts above
     ;; are sufficient.
     (update-proc-for-first-marker-msg
      install-snapshot-entry
      make-snapshot-entry
      add-snapshot-id
      remove-from-list)))))



(defthm true-listp-of-remove-from-list
  (true-listp
   (remove-from-list xs x)))



(defthm remove-from-list-is-nil-when-not-consp
  (implies
   (not
    (consp
     (remove-from-list xs x)))

   (not
    (remove-from-list xs x))))



(defthm
  cut-meta-imp-procs-consistent-p-of-later-target-marker

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    ;; I has already taken the target cut.
    (not
     (cm-cut-not-taken-p m i))

    ;; Needed to relate REMOVE1-EQUAL in metadata to
    ;; REMOVE-FROM-LIST in the implementation.
    (true-listp
     (cm-waiting-marker-for m i))

    (uniquep
     (cm-waiting-marker-for m i)))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (cm-set-waiting-marker-for
     m
     i
     (remove1-equal
      j
      (cm-waiting-marker-for m i)))

    (s i
       (update-proc-for-non-first-marker-msg
        (g i procs)
        target-sid
        j)
       procs)))

  ;; Keep your existing induction hint here.
  )






;; ============================================================
;; BEFORE TARGET START, A TARGET MARKER CANNOT BE RECEIVED
;; ============================================================

(defthm
  gm-cut-not-taken-implies-no-target-snapshot

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (memberp i ids)

    (cm-cut-not-taken-p m i))

   (not
    (memberp
     target-sid
     (snapshot-ids (g i procs))))))


(defthm
  gm-all-cut-not-taken-implies-target-sid-absent

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (subset ids
            (cm-cut-not-taken m)))

   (target-sid-absent-from-procs-p
    ids target-sid procs))

  :hints
  (("Goal"
    :induct
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    :in-theory
    (enable target-sid-absent-from-procs-p))))


(defthm
  target-sid-absent-implies-not-some-proc-has-sid

  (implies
   (target-sid-absent-from-procs-p
    ids target-sid procs)

   (not
    (some-proc-has-snapshot-id-p
     target-sid ids procs)))

  :hints
  (("Goal"
    :induct
    (target-sid-absent-from-procs-p
     ids target-sid procs))))


(defthm
  target-marker-receive-impossible-before-target-start

  (implies
   (and
    (cut-meta-imp-consistent-p m st)
    (good-state-p st)
    (legal-inputp st input)

    (cm-cut-not-taken-p
     m
     (first (cm-sid m)))

    (equal (ttype input) :receive)

    (equal
     (msg-type
      (current-msg-for-receive input st))
     :marker)

    (equal
     (sid
      (current-msg-for-receive input st))
     (cm-sid m)))

   nil)

  :rule-classes nil

  :hints
  (("Goal"
    :use
    ((:instance
      gm-all-cut-not-taken-implies-target-sid-absent
      (ids (cm-proc-ids m))
      (target-sid (cm-sid m))
      (procs (procs st)))

     (:instance
      target-sid-absent-implies-not-some-proc-has-sid
      (ids (cm-proc-ids m))
      (target-sid (cm-sid m))
      (procs (procs st)))

     (:instance
      good-state-p-implies-marker-head-sid-known-somewhere
      (i (pid input))
      (j (sender input))))

    :in-theory
    (enable
     cut-meta-imp-consistent-p
     cut-meta-imp-proc-ids-consistent-p
     cut-meta-imp-initiator-consistent-p
     legal-inputp
     current-msg-for-receive))))


;; ============================================================
;; START-CHECKPOINT-HELPER changes only I's counter, increasing
;; it by one.
;; ============================================================

(defthm counter-of-g-of-start-checkpoint-helper
  (equal
   (counter
    (g k
       (start-checkpoint-helper procs i)))

   (if (equal k i)
       (+ 1
          (counter (g i procs)))
     (counter (g k procs))))

  :hints
  (("Goal"
    :cases
    ((equal k i))

    :in-theory
    (e/d
     (start-checkpoint-helper)

     (install-snapshot-entry
      make-snapshot-entry
      add-snapshot-id)))))


;; ============================================================
;; Target checkpoint start after INPUT has already been added
;; to the global before-cut sequence.
;; ============================================================

(defthm
  cut-meta-imp-procs-consistent-p-of-target-start-after-before-sequence

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (true-listp
     (cm-cut-not-taken m))

    (uniquep
     (cm-cut-not-taken m))

    (cm-cut-not-taken-p m i)

    (equal
     target-sid
     (list i
           (counter (g i procs)))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))

       (s :waiting-marker-from
          (s i
             (nbrs-from (g i procs))
             (cm-waiting-marker-from m))

          (s :before-cut-input-sequence
             new-before
             m)))

    (start-checkpoint-helper procs i)))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-procs-consistent-p-of-target-start

      (m
       (s :before-cut-input-sequence
          new-before
          m))))

    :in-theory
    (e/d
     (cm-cut-not-taken
      cm-cut-not-taken-p
      cm-waiting-marker-from)

     (cut-meta-imp-procs-consistent-p
      start-checkpoint-helper)))))


(defthm gm-true-listp-len-two-reconstruction
  (implies
   (and
    (true-listp x)
    (equal (len x) 2))
   (equal
    (list (car x) (cadr x))
    x)))

(defthm good-cut-meta-p-implies-sid-reconstruction
  (implies
   (good-cut-meta-p m)
   (equal
    (list
     (car (cm-sid m))
     (cadr (cm-sid m)))
    (cm-sid m))))

(defthm gm-cut-taken-implies-target-snapshot
  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (memberp i ids)

    (not
     (cm-cut-not-taken-p m i)))

   (memberp
    target-sid
    (snapshot-ids
     (g i procs)))))

(defthm
  good-cut-meta-waiting-for-procs-p-implies-row-uniquep

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p ids m)
    (memberp i ids))

   (uniquep
    (cm-waiting-marker-for m i))))

(defthm
  good-cut-meta-p-implies-waiting-marker-row-uniquep

  (implies
   (and
    (good-cut-meta-p m)
    (memberp i (cm-proc-ids m)))

   (uniquep
    (cm-waiting-marker-for m i)))

  :hints
  (("Goal"
    :use
    ((:instance
      good-cut-meta-waiting-for-procs-p-implies-row-uniquep
      (ids (cm-proc-ids m))))
    :in-theory
    (enable good-cut-meta-p))))


(defthm good-cut-meta-sid-p-implies-canonical-sid
  (implies
   (good-cut-meta-sid-p m)

   (equal
    (list
     (first (cm-sid m))
     (second (cm-sid m)))
    (cm-sid m))))


(defthm
  cut-meta-imp-procs-consistent-p-implies-cut-status

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (memberp i ids))

   (equal
    (cm-cut-not-taken-p m i)

    (not
     (memberp
      target-sid
      (snapshot-ids
       (g i procs)))))))

(defthm
  good-cut-meta-waiting-for-procs-p-implies-true-listp-row

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p ids m)
    (memberp i ids))

   (true-listp
    (cm-waiting-marker-for m i))))

(defthm
  good-cut-meta-waiting-for-procs-p-implies-uniquep-row

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p ids m)
    (memberp i ids))

   (uniquep
    (cm-waiting-marker-for m i))))


(defthm
  cut-meta-imp-procs-consistent-p-of-first-target-marker-after-before-sequence

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (true-listp
     (cm-cut-not-taken m))

    (uniquep
     (cm-cut-not-taken m))

    (cm-cut-not-taken-p m i)

    (true-listp
     (nbrs-from (g i procs)))

    (uniquep
     (nbrs-from (g i procs))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))

       (s :waiting-marker-from
          (s i
             (remove1-equal
              j
              (nbrs-from (g i procs)))

             (cm-waiting-marker-from m))

          (s :before-cut-input-sequence
             new-before
             m)))

    (s i
       (update-proc-for-first-marker-msg
        (g i procs)
        target-sid
        j)
       procs)))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-procs-consistent-p-of-first-target-marker
      (m
       (s :before-cut-input-sequence
          new-before
          m))))

    :in-theory
    (disable
     cut-meta-imp-procs-consistent-p-of-first-target-marker))))


(defthm
  cut-meta-imp-procs-consistent-p-of-later-target-marker-after-after-sequence

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (not
     (cm-cut-not-taken-p m i))

    (true-listp
     (cm-waiting-marker-for m i))

    (uniquep
     (cm-waiting-marker-for m i)))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (s :waiting-marker-from
       (s i
          (remove1-equal
           j
           (cm-waiting-marker-for m i))

          (cm-waiting-marker-from m))

       (s :after-cut-input-sequence
          new-after
          m))

    (s i
       (update-proc-for-non-first-marker-msg
        (g i procs)
        target-sid
        j)
       procs)))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-procs-consistent-p-of-later-target-marker
      (m
       (s :after-cut-input-sequence
          new-after
          m))))

    :in-theory
    (disable
     cut-meta-imp-procs-consistent-p-of-later-target-marker))))


(defthm
  cut-meta-imp-procs-consistent-p-of-initial-target-start-after-before-sequence

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     (cm-proc-ids m)
     target-sid
     m
     procs)

    (true-listp
     (cm-proc-ids m))

    (uniquep
     (cm-proc-ids m))

    (equal
     (cm-cut-not-taken m)
     (cm-proc-ids m))

    (memberp
     i
     (cm-proc-ids m))

    (equal
     target-sid
     (list i
           (counter (g i procs)))))

   (cut-meta-imp-procs-consistent-p
    (cm-proc-ids m)
    target-sid

    (s :cut-not-taken
       (remove1-equal
        i
        (cm-proc-ids m))

       (s :waiting-marker-from
          (s i
             (nbrs-from (g i procs))
             (cm-waiting-marker-from m))

          (s :before-cut-input-sequence
             new-before
             m)))

    (start-checkpoint-helper procs i)))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-procs-consistent-p-of-target-start-after-before-sequence
      (ids (cm-proc-ids m))))

    :in-theory
    (disable
     cut-meta-imp-procs-consistent-p-of-target-start-after-before-sequence))))



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

  :otf-flg t

:hints
(("Goal"
  :do-not-induct t

  ;; :use
  ;; ((:instance
  ;;   target-marker-receive-impossible-before-target-start
  ;;   (m m)
  ;;   (st st)
  ;;   (input input))

  ;;  (:instance
  ;;   cut-meta-imp-procs-consistent-p-of-initial-target-start-after-before-sequence
  ;;   (target-sid (cm-sid m))
  ;;   (procs (procs st))
  ;;   (i (pid input))
  ;;   (new-before
  ;;    (append
  ;;     (cm-before-cut-input-sequence m)
  ;;     (list input))))

  ;;  (:instance
  ;;   cut-meta-imp-procs-consistent-p-of-first-target-marker-after-before-sequence
  ;;   (ids (cm-proc-ids m))
  ;;   (target-sid (cm-sid m))
  ;;   (procs (procs st))
  ;;   (i (pid input))
  ;;   (j (sender input))
  ;;   (new-before
  ;;    (append
  ;;     (cm-before-cut-input-sequence m)
  ;;     (list input))))

  ;;  (:instance
  ;;   cut-meta-imp-procs-consistent-p-of-later-target-marker-after-after-sequence
  ;;   (ids (cm-proc-ids m))
  ;;   (target-sid (cm-sid m))
  ;;   (procs (procs st))
  ;;   (i (pid input))
  ;;   (j (sender input))
  ;;   (new-after
  ;;    (append
  ;;     (cm-after-cut-input-sequence m)
  ;;     (list input)))))

  :in-theory
  (disable
   ;; Keep recursive invariants abstract.
   cut-meta-imp-procs-consistent-p
   snapshot-counters-good-for-procs-p
   good-procs-p
   nbrs-from-to-consistent-p
   nbrs-to-from-consistent-p
   good-channels-p
   good-cut-meta-waiting-for-procs-p

   ;; Preserve GOOD-CUT-META-SID-P so the canonical-SID
   ;; consequence can rewrite the impossible SID branches.
   good-cut-meta-sid-p

   ;; Keep concrete process transformations abstract.
   start-checkpoint-helper
   start-recovery-helper
   update-proc-for-first-marker-msg
   update-proc-for-non-first-marker-msg
   update-proc-for-first-recovery-msg
   update-proc-for-non-first-recovery-msg
   update-proc-for-normal-msg-core
   record-msg-in-snapshots
   install-snapshot-entry
   add-snapshot-id))))
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
