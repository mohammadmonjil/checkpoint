(in-package "ACL2")
(include-book "model")
(include-book "spec_input_gen")


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
          (equal (g :cut-not-taken m)
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
    (g :after-cut-input-sequence m))

   (true-listp
    (g :inputs-before-cut m))))


(defun good-cm-inputs-after-cut-for-srcs-p
    (i srcs m)

  (declare
   (xargs :measure (acl2-count srcs)))

  (if (endp srcs)
      t

    (let ((j (first srcs)))

      (and
       ;; The stored after-cut inputs for channel j -> i
       ;; must form a proper list.
       (true-listp
        (cm-after-cut-get i j m))

       (good-cm-inputs-after-cut-for-srcs-p
        i
        (rest srcs)
        m)))))


(defun good-cm-inputs-after-cut-p
    (ids m)

  (declare
   (xargs :measure (acl2-count ids)))

  (if (endp ids)
      t

    (let ((i (first ids)))

      (and
       (good-cm-inputs-after-cut-for-srcs-p
        i
        (cm-proc-ids m)
        m)

       (good-cm-inputs-after-cut-p
        (rest ids)
        m)))))

(defun good-cm-after-cut-msgs-for-srcs-p
    (i srcs m)

  (declare
   (xargs :measure (acl2-count srcs)))

  (if (endp srcs)
      t

    (let ((j (first srcs)))

      (and
       ;; Messages recorded from channel j -> i
       ;; must form a proper list.
       (true-listp
        (cm-after-cut-msg-get i j m))

       (good-cm-after-cut-msgs-for-srcs-p
        i
        (rest srcs)
        m)))))

(defun good-cm-after-cut-msgs-p
    (ids m)

  (declare
   (xargs :measure (acl2-count ids)))

  (if (endp ids)
      t

    (let ((i (first ids)))

      (and
       (good-cm-after-cut-msgs-for-srcs-p
        i
        (cm-proc-ids m)
        m)

       (good-cm-after-cut-msgs-p
        (rest ids)
        m)))))


(defun good-cm-after-cut-pairs-for-srcs-p
    (i srcs m)

  (declare
   (xargs :measure (acl2-count srcs)))

  (if (endp srcs)
      t

    (let ((j (first srcs)))

      (and
       (equal
        (len (cm-after-cut-get i j m))
        (len (cm-after-cut-msg-get i j m)))

       (good-cm-after-cut-pairs-for-srcs-p
        i
        (rest srcs)
        m)))))


(defun good-cm-after-cut-pairs-p
    (ids m)

  (declare
   (xargs :measure (acl2-count ids)))

  (if (endp ids)
      t

    (let ((i (first ids)))

      (and
       (good-cm-after-cut-pairs-for-srcs-p
        i
        (cm-proc-ids m)
        m)

       (good-cm-after-cut-pairs-p
        (rest ids)
        m)))))


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
   (good-cut-meta-global-input-sequences-p m)

   (good-cm-inputs-after-cut-p
    (cm-proc-ids m)
    m)

   (good-cm-after-cut-msgs-p
    (cm-proc-ids m)
    m)

   (good-cm-after-cut-pairs-p
    (cm-proc-ids m)
    m)))
