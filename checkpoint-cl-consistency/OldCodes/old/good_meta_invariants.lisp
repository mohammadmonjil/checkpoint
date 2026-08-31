(in-package "ACL2")
(include-book "model")
(include-book "good_state_invariants")
(include-book "spec_input_gen")
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
       ;; The stored inputs for channel j -> i form a proper list.
       (true-listp
        (cm-after-cut-get m i j))

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


;; ------------------------------------------------------------
;; Check that every channel-wise after-cut message sequence
;; for receiver I is a proper list.
;; ------------------------------------------------------------

(defun good-cm-after-cut-msgs-for-srcs-p
    (i srcs m)

  (declare
   (xargs :measure (acl2-count srcs)))

  (if (endp srcs)
      t

    (let ((j (first srcs)))

      (and
       ;; Messages recorded from channel j -> i form a proper list.
       (true-listp
        (cm-after-cut-msg-get m i j))

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

;; ------------------------------------------------------------
;; Check that every channel has one recorded message for each
;; corresponding recorded after-cut receive input.
;; ------------------------------------------------------------

(defun good-cm-after-cut-pairs-for-srcs-p
    (i srcs m)

  (declare
   (xargs :measure (acl2-count srcs)))

  (if (endp srcs)
      t

    (let ((j (first srcs)))

      (and
       ;; Input and message sequences for channel j -> i correspond.
       (equal
        (len (cm-after-cut-get m i j))
        (len (cm-after-cut-msg-get m i j)))

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





;; ------------------------------------------------------------
;; GOOD-CUT-META-P is invariant under one metadata-processing
;; step, provided the implementation state and metadata are
;; mutually consistent and the concrete input is legal.
;;
;; GOOD-STATE-P supplies the structural facts about process
;; neighbor lists needed when PROCESS-CUT-STEP initializes a new
;; waiting-marker row.
;; ------------------------------------------------------------

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



;; ------------------------------------------------------------
;; The global before-cut sequence is independent of the
;; channel-wise :inputs-after-cut table.
;; ------------------------------------------------------------

(defthm
  good-cm-inputs-after-cut-for-srcs-p-of-s-before-cut-input-sequence

  (equal
   (good-cm-inputs-after-cut-for-srcs-p
    i
    srcs
    (s :before-cut-input-sequence xs m))

   (good-cm-inputs-after-cut-for-srcs-p
    i
    srcs
    m)))


;; ------------------------------------------------------------
;; Consequently, adding an input to the global before-cut
;; sequence preserves the complete channel-wise invariant.
;; ------------------------------------------------------------

(defthm
  good-cm-inputs-after-cut-p-of-s-before-cut-input-sequence

  (equal
   (good-cm-inputs-after-cut-p
    ids
    (s :before-cut-input-sequence xs m))

   (good-cm-inputs-after-cut-p
    ids
    m)))


;; ------------------------------------------------------------
;; Updating the global before-cut sequence does not change any
;; channel-wise after-cut message sequence.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-msgs-for-srcs-p-of-s-before-cut-input-sequence

  (equal
   (good-cm-after-cut-msgs-for-srcs-p
    i
    srcs
    (s :before-cut-input-sequence xs m))

   (good-cm-after-cut-msgs-for-srcs-p
    i
    srcs
    m)))

;; ------------------------------------------------------------
;; Therefore, the complete after-cut message invariant is
;; unchanged by updating the global before-cut sequence.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-msgs-p-of-s-before-cut-input-sequence

  (equal
   (good-cm-after-cut-msgs-p
    ids
    (s :before-cut-input-sequence xs m))

   (good-cm-after-cut-msgs-p
    ids
    m)))



;; ------------------------------------------------------------
;; Updating the global before-cut sequence does not change the
;; channel-wise input/message correspondence.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-pairs-for-srcs-p-of-s-before-cut-input-sequence

  (equal
   (good-cm-after-cut-pairs-for-srcs-p
    i
    srcs
    (s :before-cut-input-sequence xs m))

   (good-cm-after-cut-pairs-for-srcs-p
    i
    srcs
    m)))

;; ------------------------------------------------------------
;; Therefore, the complete input/message pairing invariant is
;; preserved by updating the global before-cut sequence.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-pairs-p-of-s-before-cut-input-sequence

  (equal
   (good-cm-after-cut-pairs-p
    ids
    (s :before-cut-input-sequence xs m))

   (good-cm-after-cut-pairs-p
    ids
    m)))


;; ------------------------------------------------------------
;; The global after-cut sequence is independent of the
;; channel-wise :inputs-after-cut table.
;; ------------------------------------------------------------

(defthm
  good-cm-inputs-after-cut-for-srcs-p-of-s-after-cut-input-sequence

  (equal
   (good-cm-inputs-after-cut-for-srcs-p
    i
    srcs
    (s :after-cut-input-sequence xs m))

   (good-cm-inputs-after-cut-for-srcs-p
    i
    srcs
    m)))

;; ------------------------------------------------------------
;; Updating the global after-cut sequence preserves the
;; complete channel-wise after-cut input invariant.
;; ------------------------------------------------------------

(defthm
  good-cm-inputs-after-cut-p-of-s-after-cut-input-sequence

  (equal
   (good-cm-inputs-after-cut-p
    ids
    (s :after-cut-input-sequence xs m))

   (good-cm-inputs-after-cut-p
    ids
    m)))




;; ------------------------------------------------------------
;; Updating the global after-cut input sequence does not change
;; any channel-wise recorded message sequence.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-msgs-for-srcs-p-of-s-after-cut-input-sequence

  (equal
   (good-cm-after-cut-msgs-for-srcs-p
    i
    srcs
    (s :after-cut-input-sequence xs m))

   (good-cm-after-cut-msgs-for-srcs-p
    i
    srcs
    m)))


;; ------------------------------------------------------------
;; Therefore, the complete after-cut message invariant is
;; preserved by updating the global after-cut input sequence.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-msgs-p-of-s-after-cut-input-sequence

  (equal
   (good-cm-after-cut-msgs-p
    ids
    (s :after-cut-input-sequence xs m))

   (good-cm-after-cut-msgs-p
    ids
    m)))


;; ------------------------------------------------------------
;; Updating the global after-cut input sequence does not change
;; the channel-wise input/message correspondence.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-pairs-for-srcs-p-of-s-after-cut-input-sequence

  (equal
   (good-cm-after-cut-pairs-for-srcs-p
    i
    srcs
    (s :after-cut-input-sequence xs m))

   (good-cm-after-cut-pairs-for-srcs-p
    i
    srcs
    m)))


;; ------------------------------------------------------------
;; Therefore, the complete input/message pairing invariant is
;; preserved by updating the global after-cut input sequence.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-pairs-p-of-s-after-cut-input-sequence

  (equal
   (good-cm-after-cut-pairs-p
    ids
    (s :after-cut-input-sequence xs m))

   (good-cm-after-cut-pairs-p
    ids
    m)))


;; ------------------------------------------------------------
;; Updating the ordinary pre-cut input list does not change
;; cut status or any waiting-marker row.
;; ------------------------------------------------------------

(defthm
  good-cut-meta-waiting-for-procs-p-of-s-inputs-before-cut

  (equal
   (good-cut-meta-waiting-for-procs-p
    ids
    (s :inputs-before-cut xs m))

   (good-cut-meta-waiting-for-procs-p
    ids
    m)))


;; ------------------------------------------------------------
;; The global pre-cut input list is independent of the
;; channel-wise :inputs-after-cut table.
;; ------------------------------------------------------------

(defthm
  good-cm-inputs-after-cut-for-srcs-p-of-s-inputs-before-cut

  (equal
   (good-cm-inputs-after-cut-for-srcs-p
    i
    srcs
    (s :inputs-before-cut xs m))

   (good-cm-inputs-after-cut-for-srcs-p
    i
    srcs
    m)))

;; ------------------------------------------------------------
;; Therefore, updating the global pre-cut input list preserves
;; the complete channel-wise after-cut input invariant.
;; ------------------------------------------------------------

(defthm
  good-cm-inputs-after-cut-p-of-s-inputs-before-cut

  (equal
   (good-cm-inputs-after-cut-p
    ids
    (s :inputs-before-cut xs m))

   (good-cm-inputs-after-cut-p
    ids
    m)))


;; ------------------------------------------------------------
;; The global pre-cut input list is independent of the
;; channel-wise after-cut message table.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-msgs-for-srcs-p-of-s-inputs-before-cut

  (equal
   (good-cm-after-cut-msgs-for-srcs-p
    i
    srcs
    (s :inputs-before-cut xs m))

   (good-cm-after-cut-msgs-for-srcs-p
    i
    srcs
    m)))


;; ------------------------------------------------------------
;; Therefore, updating the global pre-cut input list preserves
;; the complete after-cut message invariant.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-msgs-p-of-s-inputs-before-cut

  (equal
   (good-cm-after-cut-msgs-p
    ids
    (s :inputs-before-cut xs m))

   (good-cm-after-cut-msgs-p
    ids
    m)))


;; ------------------------------------------------------------
;; The global pre-cut input list is independent of the
;; channel-wise input/message correspondence.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-pairs-for-srcs-p-of-s-inputs-before-cut

  (equal
   (good-cm-after-cut-pairs-for-srcs-p
    i
    srcs
    (s :inputs-before-cut xs m))

   (good-cm-after-cut-pairs-for-srcs-p
    i
    srcs
    m)))


;; ------------------------------------------------------------
;; Therefore, updating the global pre-cut input list preserves
;; the complete input/message pairing invariant.
;; ------------------------------------------------------------

(defthm
  good-cm-after-cut-pairs-p-of-s-inputs-before-cut

  (equal
   (good-cm-after-cut-pairs-p
    ids
    (s :inputs-before-cut xs m))

   (good-cm-after-cut-pairs-p
    ids
    m)))


(defthm
  good-cut-meta-waiting-for-procs-p-of-first-marker-update

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p ids m)

    ;; Removing I must remove its only occurrence from
    ;; the not-yet-cut set.
    (uniquep
     (g :cut-not-taken m))

    ;; The new waiting row is the receiver's incoming-neighbor
    ;; row with the marker sender removed.
    (true-listp nbrs)
    (uniquep nbrs)
    (subset nbrs
            (g :proc-ids m)))

   (good-cut-meta-waiting-for-procs-p
    ids
    (s :cut-not-taken
       (remove1-equal i
                      (g :cut-not-taken m))

       (s :waiting-marker-from
          (s i
             (remove1-equal j nbrs)
             (g :waiting-marker-from m))

          ;; This field is invisible to the target predicate.
          (s :before-cut-input-sequence
             new-before
             m)))))

  :hints
  (("Goal"
    :induct
    (good-cut-meta-waiting-for-procs-p ids m))

   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))


(defthm cl-good-procs-p-implies-good-proc-p
  (implies
   (and
    (good-procs-p ids procs all-ids)
    (memberp i ids))
   (good-proc-p
    (g i procs)
    all-ids)))

(defthm good-procs-p-implies-true-listp-nbrs-from
  (implies
   (and
    (good-procs-p ids procs all-ids)
    (memberp i ids))
   (true-listp
    (g :nbrs-from
       (g i procs)))))


(defthm good-procs-p-implies-uniquep-nbrs-from
  (implies
   (and
    (good-procs-p ids procs all-ids)
    (memberp i ids))
   (uniquep
    (g :nbrs-from
       (g i procs)))))

(defthm good-procs-p-implies-subset-nbrs-from
  (implies
   (and
    (good-procs-p ids procs all-ids)
    (memberp i ids))
   (subset
    (g :nbrs-from
       (g i procs))
    all-ids)))




;; ------------------------------------------------------------------
;; GOOD-CM-INPUTS-AFTER-CUT-P depends only on:
;;
;;   :PROC-IDS
;;   :INPUTS-AFTER-CUT
;;
;; Updating any other metadata field therefore preserves it.
;; ------------------------------------------------------------------

(defthm cm-proc-ids-of-s-different-field
  (implies
   (not (equal key :proc-ids))
   (equal
    (cm-proc-ids
     (s key value m))
    (cm-proc-ids m))))


(defthm cm-after-cut-get-of-s-different-field
  (implies
   (not (equal key :inputs-after-cut))
   (equal
    (cm-after-cut-get
     (s key value m)
     dst
     src)
    (cm-after-cut-get
     m
     dst
     src))))


;; First lift the field-level result through the source-list scanner.
(defthm
  good-cm-inputs-after-cut-for-srcs-p-of-s-different-field

  (implies
   (and
    (not (equal key :proc-ids))
    (not (equal key :inputs-after-cut)))

   (equal
    (good-cm-inputs-after-cut-for-srcs-p
     dst
     srcs
     (s key value m))

    (good-cm-inputs-after-cut-for-srcs-p
     dst
     srcs
     m))))


;; Then lift it through the outer destination-list scanner.
(defthm
  good-cm-inputs-after-cut-p-of-s-different-field

  (implies
   (and
    (not (equal key :proc-ids))
    (not (equal key :inputs-after-cut)))

   (equal
    (good-cm-inputs-after-cut-p
     ids
     (s key value m))

    (good-cm-inputs-after-cut-p
     ids
     m))))

(defthm
  good-cm-inputs-after-cut-p-of-s-cut-not-taken

  (equal
   (good-cm-inputs-after-cut-p
    ids
    (s :cut-not-taken value m))

   (good-cm-inputs-after-cut-p
    ids
    m)))


(defthm
  good-cm-inputs-after-cut-p-of-s-waiting-marker-from

  (equal
   (good-cm-inputs-after-cut-p
    ids
    (s :waiting-marker-from value m))

   (good-cm-inputs-after-cut-p
    ids
    m)))


;; ------------------------------------------------------------------
;; Updating an unrelated metadata field does not change an
;; individual after-cut message row.
;; ------------------------------------------------------------------

(defthm cm-after-cut-msg-get-of-s-different-field
  (implies
   (not (equal key :after-cut-msgs))
   (equal
    (cm-after-cut-msg-get
     (s key value m)
     dst
     src)

    (cm-after-cut-msg-get
     m
     dst
     src))))


;; ------------------------------------------------------------------
;; Lift the field-level result through the source-list scanner.
;; ------------------------------------------------------------------

(defthm
  good-cm-after-cut-msgs-for-srcs-p-of-s-different-field

  (implies
   (not (equal key :after-cut-msgs))

   (equal
    (good-cm-after-cut-msgs-for-srcs-p
     dst
     srcs
     (s key value m))

    (good-cm-after-cut-msgs-for-srcs-p
     dst
     srcs
     m))))


;; ------------------------------------------------------------------
;; Lift the result through the outer destination-list scanner.
;;
;; The outer predicate also obtains its source list from :PROC-IDS,
;; so both relevant fields must remain unchanged.
;; ------------------------------------------------------------------

(defthm
  good-cm-after-cut-msgs-p-of-s-different-field

  (implies
   (and
    (not (equal key :proc-ids))
    (not (equal key :after-cut-msgs)))

   (equal
    (good-cm-after-cut-msgs-p
     ids
     (s key value m))

    (good-cm-after-cut-msgs-p
     ids
     m))))


;; ------------------------------------------------------------------
;; Preserve the per-destination pair invariant across an update to
;; any field other than the two per-channel tables.
;; ------------------------------------------------------------------

(defthm
  good-cm-after-cut-pairs-for-srcs-p-of-s-different-field

  (implies
   (and
    (not (equal key :inputs-after-cut))
    (not (equal key :after-cut-msgs)))

   (equal
    (good-cm-after-cut-pairs-for-srcs-p
     dst
     srcs
     (s key value m))

    (good-cm-after-cut-pairs-for-srcs-p
     dst
     srcs
     m))))

;; ------------------------------------------------------------------
;; Preserve the complete pair invariant.
;;
;; The outer scanner additionally reads :PROC-IDS to determine the
;; source list used for each destination.
;; ------------------------------------------------------------------

(defthm
  good-cm-after-cut-pairs-p-of-s-different-field

  (implies
   (and
    (not (equal key :proc-ids))
    (not (equal key :inputs-after-cut))
    (not (equal key :after-cut-msgs)))

   (equal
    (good-cm-after-cut-pairs-p
     ids
     (s key value m))

    (good-cm-after-cut-pairs-p
     ids
     m))))



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
    ((equal i (car ids))))))


(defthm
  s-waiting-marker-from-over-s-after-cut-input-sequence

  (equal
   (s :waiting-marker-from waiting
      (s :after-cut-input-sequence after m))

   (s :after-cut-input-sequence after
      (s :waiting-marker-from waiting m)))
  :rule-classes nil)


(defthm
  good-cut-meta-waiting-for-procs-p-of-waiting-over-after-cut-sequence

  (equal
   (good-cut-meta-waiting-for-procs-p
    ids
    (s :waiting-marker-from waiting
       (s :after-cut-input-sequence after m)))

   (good-cut-meta-waiting-for-procs-p
    ids
    (s :waiting-marker-from waiting m))))
   

(defthm
  good-cut-meta-waiting-for-procs-p-of-s-different-field

  (implies
   (and
    (not (equal key :proc-ids))
    (not (equal key :cut-not-taken))
    (not (equal key :waiting-marker-from)))

   (equal
    (good-cut-meta-waiting-for-procs-p
     ids
     (s key value m))

    (good-cut-meta-waiting-for-procs-p
     ids
     m))))


(defthm
  good-cm-inputs-after-cut-for-srcs-p-of-append-one

  (implies
   (good-cm-inputs-after-cut-for-srcs-p
    scan-dst
    srcs
    m)

   (good-cm-inputs-after-cut-for-srcs-p
    scan-dst
    srcs

    (s :inputs-after-cut
       (s dst
          (s src
             (append
              (g src
                 (g dst
                    (g :inputs-after-cut m)))
              (list new-input))

             (g dst
                (g :inputs-after-cut m)))

          (g :inputs-after-cut m))

       ;; This field is irrelevant to the inner predicate.
       (s :after-cut-input-sequence
          new-after
          m))))

  :hints
  (("Goal"
    :cases
    ((equal scan-dst dst)
     (equal src (car srcs))))))


(defthm
  good-cm-after-cut-msgs-for-srcs-p-of-append-one

  (implies
   (good-cm-after-cut-msgs-for-srcs-p
    scan-dst
    srcs
    m)

   (good-cm-after-cut-msgs-for-srcs-p
    scan-dst
    srcs

    (s :after-cut-msgs
       (s dst
          (s src
             (append
              (g src
                 (g dst
                    (g :after-cut-msgs m)))
              (list new-msg))

             (g dst
                (g :after-cut-msgs m)))

          (g :after-cut-msgs m))

       ;; These two fields are irrelevant to this predicate.
       (s :inputs-after-cut
          new-inputs
          (s :after-cut-input-sequence
             new-after
             m)))))

  :hints
  (("Goal"
    :cases
    ((equal scan-dst dst)
     (equal src (car srcs))))))


(defthm
  good-cm-after-cut-msgs-p-of-append-one

  (implies
   (good-cm-after-cut-msgs-p
    ids
    m)

   (good-cm-after-cut-msgs-p
    ids

    (s :after-cut-msgs
       (s dst
          (s src
             (append
              (g src
                 (g dst
                    (g :after-cut-msgs m)))
              (list new-msg))

             (g dst
                (g :after-cut-msgs m)))

          (g :after-cut-msgs m))

       (s :inputs-after-cut
          new-inputs
          (s :after-cut-input-sequence
             new-after
             m))))))

(defthm
  good-cm-inputs-after-cut-p-of-append-one

  (implies
   (good-cm-inputs-after-cut-p
    ids
    m)

   (good-cm-inputs-after-cut-p
    ids

    (s :inputs-after-cut
       (s dst
          (s src
             (append
              (g src
                 (g dst
                    (g :inputs-after-cut m)))
              (list new-input))

             (g dst
                (g :inputs-after-cut m)))

          (g :inputs-after-cut m))

       (s :after-cut-input-sequence
          new-after
          m)))))




(defthm cl-len-of-append-one
  (equal
   (len (append xs (list x)))
   (+ 1 (len xs))))

(defthm
  good-cm-after-cut-pairs-for-srcs-p-of-append-one-pair

  (implies
   (good-cm-after-cut-pairs-for-srcs-p
    scan-dst
    srcs
    m)

   (good-cm-after-cut-pairs-for-srcs-p
    scan-dst
    srcs

    (s :after-cut-msgs
       (s dst
          (s src
             (append
              (g src
                 (g dst
                    (g :after-cut-msgs m)))
              (list new-msg))

             (g dst
                (g :after-cut-msgs m)))

          (g :after-cut-msgs m))

       (s :inputs-after-cut
          (s dst
             (s src
                (append
                 (g src
                    (g dst
                       (g :inputs-after-cut m)))
                 (list new-input))

                (g dst
                   (g :inputs-after-cut m)))

             (g :inputs-after-cut m))

          (s :after-cut-input-sequence
             new-after
             m)))))

  :hints
  (("Goal"
    :cases
    ((equal scan-dst dst)
     (equal src (car srcs))))))


(defthm
  good-cm-after-cut-pairs-p-of-append-one-pair

  (implies
   (good-cm-after-cut-pairs-p
    ids
    m)

   (good-cm-after-cut-pairs-p
    ids

    (s :after-cut-msgs
       (s dst
          (s src
             (append
              (g src
                 (g dst
                    (g :after-cut-msgs m)))
              (list new-msg))

             (g dst
                (g :after-cut-msgs m)))

          (g :after-cut-msgs m))

       (s :inputs-after-cut
          (s dst
             (s src
                (append
                 (g src
                    (g dst
                       (g :inputs-after-cut m)))
                 (list new-input))

                (g dst
                   (g :inputs-after-cut m)))

             (g :inputs-after-cut m))

          (s :after-cut-input-sequence
             new-after
             m))))))




(defthm
  good-cut-meta-waiting-for-procs-p-of-start-checkpoint-update

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p
     ids
     m)

    ;; Ensures that removing I eliminates its only occurrence.
    (uniquep
     (g :cut-not-taken m))

    ;; Structural properties required for the new waiting row.
    (true-listp nbrs)
    (uniquep nbrs)
    (subset nbrs
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

          ;; Irrelevant to the waiting-row predicate, but included
          ;; so that the theorem matches PROCESS-CUT-STEP exactly.
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
    ((equal i (car ids))))))


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

    (memberp i
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
          (g i procs))))

     (:instance
      good-procs-p-implies-good-nbrs-from

      (ids
       (g :proc-ids m))
      (all-ids
       (g :proc-ids m)))))))


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

    (memberp i
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
          (g i procs)))
      )

     (:instance
      good-procs-p-implies-good-nbrs-from

      (ids
       (g :proc-ids m))
      (all-ids
       (g :proc-ids m)))))))


(defthm good-cut-meta-p-preserved-by-process-cut-step
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
  :hints
  (("Goal"
    :in-theory
    (disable
     cut-meta-imp-procs-consistent-p
     snapshot-counters-good-for-procs-p
    ; good-procs-p
     nbrs-from-to-consistent-p
     nbrs-to-from-consistent-p
     good-channels-p

     good-cm-inputs-after-cut-p
     good-cm-after-cut-msgs-p
     good-cm-after-cut-pairs-p))))


;; ------------------------------------------------------------
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

(defthm
  cut-meta-imp-procs-consistent-p-of-s-inputs-before-cut

  (equal
   (cut-meta-imp-procs-consistent-p
    ids target-sid
    (s :inputs-before-cut value m)
    procs)

   (cut-meta-imp-procs-consistent-p
    ids target-sid
    m
    procs))

  :hints
  (("Goal"
    :induct
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs))

    :in-theory
    (enable
     cut-meta-imp-procs-consistent-p)))



(defthm
  cut-meta-imp-procs-consistent-p-of-local-state-update-before-cut

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (memberp i
             (g :cut-not-taken m)))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m

    (s i
       (s :local-state
          new-local
          (g i procs))
       procs)))

  :hints
  (("Goal"
    :induct
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs))

   ("Subgoal *1/2"
    :cases
    ((equal i (car ids))))))


(defthm cut-meta-imp-consistent-p-preserved-by-step
  (implies
   (and
    (cut-meta-imp-consistent-p
     m
     st)

    (good-state-p st)

    (good-cut-meta-p m)

    (legal-inputp
     st
     input))

   (cut-meta-imp-consistent-p
    (process-cut-step
     input
     st
     m)

    (system-step
     st
     input))))




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
