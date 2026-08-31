(in-package "ACL2")

;; This block belongs after GOOD-CUT-META-P-PRESERVED-BY-PROCESS-CUT-STEP
;; and before CUT-META-IMP-CONSISTENT-P-PRESERVED-BY-STEP.

;; ============================================================
;; TARGET-CUT PROCESS VIEW
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
   (equal
    (target-cut-proc-view target-sid new-p)
    (target-cut-proc-view target-sid (g i procs)))

   (equal
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     (s i new-p procs))

    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs)))

  :hints
  (("Goal"
    :induct
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs))

   ("Subgoal *1/2"
    :cases
    ((equal i (car ids))))))


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

  (equal
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (s i
       (update-proc-for-normal-msg-core
        (g i procs)
        j
        msg)
       procs))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    procs))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same
      (new-p
       (update-proc-for-normal-msg-core
        (g i procs)
        j
        msg)))))))


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

  (equal
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (start-recovery-helper procs i))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    procs))

  :hints
  (("Goal"
    :induct
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs))))


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
   (not
    (equal
     target-sid
     (list i
           (counter (g i procs)))))

   (equal
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     (start-checkpoint-helper procs i))

    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs)))

  :hints
  (("Goal"
    :induct
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs))))


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
  cut-meta-imp-procs-consistent-p-of-target-start

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (cm-cut-not-taken-p m i)

    (equal
     target-sid
     (list i
           (counter (g i procs)))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (s :cut-not-taken
       (remove1-equal i
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
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    :in-theory
    (enable
     start-checkpoint-helper
     install-snapshot-entry
     add-snapshot-id))

   ("Subgoal *1/2"
    :cases
    ((equal i (car ids))))))


(defthm
  cut-meta-imp-procs-consistent-p-of-first-target-marker

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (cm-cut-not-taken-p m i)

    (uniquep
     (nbrs-from (g i procs))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (s :cut-not-taken
       (remove1-equal i
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
    :induct
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    :in-theory
    (enable
     update-proc-for-first-marker-msg
     install-snapshot-entry
     add-snapshot-id))

   ("Subgoal *1/2"
    :cases
    ((equal i (car ids))))))


(defthm
  cut-meta-imp-procs-consistent-p-of-later-target-marker

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (not
     (cm-cut-not-taken-p m i))

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

  :hints
  (("Goal"
    :induct
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    :in-theory
    (enable
     cm-set-waiting-marker-for
     cm-waiting-marker-for
     update-proc-for-non-first-marker-msg
     set-snapshot-entry))

   ("Subgoal *1/2"
    :cases
    ((equal i (car ids))))))


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

