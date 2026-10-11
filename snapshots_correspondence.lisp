(in-package "ACL2")
(include-book "snapshot_local_inv")



;; Snapshot correspondence states the desired result for a completed
;; checkpoint: recorded channel messages and local states match the
;; corresponding channels and processes in the before-cut state.
;; M identifies the target snapshot and tracks cuts and pending markers.
;; IMP-ST is the implementation state containing the recorded snapshot.
;; The before-cut state is reconstructed by running the inputs classified
;; as before-cut, in their original order, from the starting state.
;;
;; During collection, the channel invariant states that before-cut normal
;; messages equal APPEND of recorded messages and messages still to be
;; recorded. Completion makes the second list empty, giving correspondence.

;; For the channel from INCOMING-NBR to I, compare the before-cut normal
;; messages with the messages recorded for the target snapshot in M.
(defun one-channel-snapshot-correspondence
    (incoming-nbr i m imp-st before-cut-st)
  (equal
   (normal-channel-msgs incoming-nbr i before-cut-st)

   (recorded-channel-msgs incoming-nbr i m imp-st)))


;; Require channel correspondence for every neighbor in INCOMING-NBRS.
;; An empty neighbor list has no channel equalities to check.
(defun incoming-channels-snapshot-correspondence
    (incoming-nbrs i m imp-st before-cut-st)
  (declare
   (xargs :measure (acl2-count incoming-nbrs)))
  (if (endp incoming-nbrs)
      t
    (and
     (one-channel-snapshot-correspondence
      (first incoming-nbrs)
      i
      m
      imp-st
      before-cut-st)

     (incoming-channels-snapshot-correspondence
      (rest incoming-nbrs)
      i
      m
      imp-st
      before-cut-st))))

;; Check exactly the incoming channels listed by process I in IMP-ST.
(defun one-process-channel-snapshot-correspondence
    (i m imp-st before-cut-st)
  (incoming-channels-snapshot-correspondence
   (nbrs-from
    (g i (procs imp-st)))
   i
   m
   imp-st
   before-cut-st))


;; Lift channel correspondence to every process in the supplied ID list.
(defun processes-channel-snapshot-correspondence
    (ids m imp-st before-st)
  (if (endp ids)
      t
    (and
     (one-process-channel-snapshot-correspondence
      (first ids) m imp-st before-st)
     (processes-channel-snapshot-correspondence
      (rest ids) m imp-st before-st))))


;; Require channel correspondence for every implementation process.
(defun all-processes-channel-snapshot-correspondence
    (m imp-st before-st)
  (processes-channel-snapshot-correspondence
   (proc-ids imp-st) m imp-st before-st))




;; Compare I's before-cut local state with the local state stored in its
;; snapshot entry for the SID selected by M.
(defun one-process-local-snapshot-correspondence
    (i m imp-st before-st)
  (let ((imp-proc (g i (procs imp-st)))
        (before-proc (g i (procs before-st))))
      (equal (local-state before-proc)
             (g :local-snap-shot
                (snapshot-entry (cm-sid m) imp-proc)))))



;; Require local-state correspondence for each process in IDS.
(defun processes-local-snapshot-correspondence
    (ids m imp-st before-st)
  (if (endp ids)
      t
    (and
     (one-process-local-snapshot-correspondence
      (first ids) m imp-st before-st)
     (processes-local-snapshot-correspondence
      (rest ids) m imp-st before-st))))

;; Check recorded local states for all implementation process IDs.
(defun all-processes-local-snapshot-correspondence
    (m imp-st before-st)
  (processes-local-snapshot-correspondence
   (proc-ids imp-st) m imp-st before-st))



;; Once I has taken its cut and received all target markers, the
;; invariant's remaining-message list is empty. The recorded list must be
;; a true list so that APPEND of that list and NIL equals the list itself.

(defthm one-channel-snapshot-correspondence-when-cut-complete
  (implies
   (and
    (memberp i (proc-ids imp-st))
    (not (cm-cut-not-taken-p m i))
    (endp (cm-waiting-marker-for m i))
    (true-listp
     (recorded-channel-msgs incoming-nbr i m imp-st))
    (one-channel-snapshot-invariant-p
     incoming-nbr i m imp-st before-cut-st))
   (one-channel-snapshot-correspondence
    incoming-nbr i m imp-st before-cut-st))
  :hints
  (("Goal"
    :in-theory
    (disable
     normal-channel-msgs
      recorded-channel-msgs
      normal-msgs-before-target-marker))))





;; The snapshot-record recognizer checks each incoming channel row.
;; Extract its true-list property for any listed incoming neighbor.
(defthm true-listp-of-channel-snapshot-record-when-good
  (implies
   (and
    (good-channel-snapshot-record-p nbrs-from-i cs)
    (memberp incoming-nbr nbrs-from-i))
   (true-listp (g incoming-nbr cs))))


;; Derive the recorded-list typing needed by the completed-cut theorem.
;; Before I takes its cut, its recorded list is NIL. Afterward, metadata
;; consistency places the target SID in I's snapshot IDs, and GOOD-STATE-P
;; supplies the well-formed snapshot entry and channel row.
(defthm true-listp-of-recorded-channel-msgs-when-good-state-and-consistent
  (implies
   (and
    (good-state-p imp-st)
    (cut-meta-imp-consistent-p m imp-st)
    (memberp i (proc-ids imp-st))
    (memberp incoming-nbr (nbrs-from (g i (procs imp-st)))))
   (true-listp (recorded-channel-msgs incoming-nbr i m imp-st)))
  :hints
  (("Goal"
    :do-not-induct t
    :cases ((cm-cut-not-taken-p m i))
    :use
    ((:instance good-proc-p-of-g-when-good-procs-p
      (ids (proc-ids imp-st))
      (procs (procs imp-st))
      (all-ids (proc-ids imp-st)))
     (:instance
      cut-meta-imp-consistent-p-implies-target-sid-present-when-cut-taken)
     (:instance good-proc-p-implies-good-snapshot-entry-p-for-member
      (p (g i (procs imp-st)))
      (ids (proc-ids imp-st))
      (sid (cm-sid m)))
     (:instance true-listp-of-channel-snapshot-record-when-good
      (nbrs-from-i (nbrs-from (g i (procs imp-st))))
      (cs
       (snapshot-channel-snapshots
        (snapshot-entry (cm-sid m) (g i (procs imp-st)))))))
    :in-theory
    (disable
     good-proc-p-of-g-when-good-procs-p
      cut-meta-imp-consistent-p-implies-target-sid-present-when-cut-taken
      good-proc-p-implies-good-snapshot-entry-p-for-member
      true-listp-of-channel-snapshot-record-when-good
      good-procs-p good-proc-p
      good-channel-snapshot-record-p good-normal-msg-list-p
      good-snapshot-status-p
      all-initiators-stored-sids-have-smaller-counters-p
      nbrs-from-to-consistent-p nbrs-to-from-consistent-p
      good-channels-p
      cut-meta-imp-consistent-p
      cm-cut-not-taken))))


;; Completion treats SID :INIT as a special case. GOOD-CUT-META-P
;; excludes that case, so later lemmas can extract cuts and waiting rows
;; from the ordinary checkpoint-completion condition.
(defthm good-cut-meta-p-implies-sid-not-init
  (implies
   (good-cut-meta-p m)
   (not (equal (cm-sid m) :init))))


;; If every waiting row in IDS is empty, extract the empty row for I.
(defthm all-waiting-marker-empty-p-implies-empty-row
  (implies
   (and
    (all-waiting-marker-empty-p ids m)
    (memberp i ids))
   (endp (cm-waiting-marker-for m i))))


;; Translate global checkpoint completion into I's two completion facts:
;; its cut is taken and its waiting-marker row is empty. Consistency aligns
;; the metadata process IDs with the implementation process IDs.
(defthm checkpoint-collection-complete-p-implies-process-cut-complete
  (implies
   (and
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m imp-st)
    (checkpoint-collection-complete-p m)
    (memberp i (proc-ids imp-st)))
   (and
    (not (cm-cut-not-taken-p m i))
    (endp (cm-waiting-marker-for m i))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance good-cut-meta-p-implies-sid-not-init)
     (:instance all-waiting-marker-empty-p-implies-empty-row
      (ids (cm-proc-ids m))))
    :in-theory
    (disable
     good-cut-meta-p
      good-cut-meta-p-implies-sid-not-init
      all-waiting-marker-empty-p
      all-waiting-marker-empty-p-implies-empty-row
      cut-meta-imp-initiator-consistent-p
      cut-meta-imp-procs-consistent-p
      cm-proc-ids cm-cut-not-taken cm-waiting-marker-for))))


;; Combine process completion and recorded-list typing with the channel
;; invariant. This version obtains the explicit cut and waiting-row facts
;; from completion of the entire target checkpoint.
(defthm
  one-channel-snapshot-correspondence-when-checkpoint-collection-complete
  (implies
   (and
    (good-state-p imp-st)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m imp-st)
    (checkpoint-collection-complete-p m)
    (memberp i (proc-ids imp-st))
    (memberp incoming-nbr (nbrs-from (g i (procs imp-st))))
    (one-channel-snapshot-invariant-p
     incoming-nbr i m imp-st before-st))
   (one-channel-snapshot-correspondence
    incoming-nbr i m imp-st before-st))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance
      checkpoint-collection-complete-p-implies-process-cut-complete)
     (:instance
      true-listp-of-recorded-channel-msgs-when-good-state-and-consistent)
     (:instance
      one-channel-snapshot-correspondence-when-cut-complete
      (before-cut-st before-st)))
    :in-theory
    (disable
     checkpoint-collection-complete-p-implies-process-cut-complete
     true-listp-of-recorded-channel-msgs-when-good-state-and-consistent
     one-channel-snapshot-correspondence-when-cut-complete
     good-state-p good-cut-meta-p cut-meta-imp-consistent-p
     checkpoint-collection-complete-p
     one-channel-snapshot-invariant-p
     one-channel-snapshot-correspondence
     recorded-channel-msgs
     cm-cut-not-taken-p cm-waiting-marker-for))))


;; Lift the one-channel result by induction over INCOMING-NBRS. The subset
;; premise ensures that each listed neighbor is an incoming neighbor of I.
(defthm
  incoming-channels-snapshot-correspondence-when-checkpoint-collection-complete
  (implies
   (and
    (good-state-p imp-st)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m imp-st)
    (checkpoint-collection-complete-p m)
    (memberp i (proc-ids imp-st))
    (subset incoming-nbrs (nbrs-from (g i (procs imp-st))))
    (incoming-channels-snapshot-invariant-p
     incoming-nbrs i m imp-st before-st))
   (incoming-channels-snapshot-correspondence
    incoming-nbrs i m imp-st before-st))
  :hints
  (("Goal"
    :induct
    (incoming-channels-snapshot-invariant-p
     incoming-nbrs i m imp-st before-st)
    :in-theory
    (disable
     good-state-p good-cut-meta-p cut-meta-imp-consistent-p
      checkpoint-collection-complete-p
      one-channel-snapshot-invariant-p
      one-channel-snapshot-correspondence
      recorded-channel-msgs))))


;; Instantiate the neighbor-list result with I's full incoming-neighbor
;; list to obtain correspondence for all of I's incoming channels.
(defthm
  one-process-channel-snapshot-correspondence-when-checkpoint-collection-complete
  (implies
   (and
    (good-state-p imp-st)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m imp-st)
    (checkpoint-collection-complete-p m)
    (memberp i (proc-ids imp-st))
    (one-process-channel-snapshot-invariant-p
     i m imp-st before-st))
   (one-process-channel-snapshot-correspondence
    i m imp-st before-st))
  :hints
  (("Goal"
    :use
    ((:instance
      incoming-channels-snapshot-correspondence-when-checkpoint-collection-complete
      (incoming-nbrs (nbrs-from (g i (procs imp-st))))))
    :in-theory
    (disable
     incoming-channels-snapshot-correspondence-when-checkpoint-collection-complete
      incoming-channels-snapshot-invariant-p
      incoming-channels-snapshot-correspondence
      good-state-p good-cut-meta-p cut-meta-imp-consistent-p
      checkpoint-collection-complete-p))))


;; Induct over IDS and apply the one-process channel result at each step.
;; The subset premise supplies implementation membership for each process.
(defthm
  processes-channel-snapshot-correspondence-when-checkpoint-collection-complete
  (implies
   (and
    (good-state-p imp-st)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m imp-st)
    (checkpoint-collection-complete-p m)
    (subset ids (proc-ids imp-st))
    (processes-channel-snapshot-invariant-p ids m imp-st before-st))
   (processes-channel-snapshot-correspondence ids m imp-st before-st))
  :hints
  (("Goal"
    :induct
    (processes-channel-snapshot-invariant-p ids m imp-st before-st)
    :in-theory
    (disable
     good-state-p good-cut-meta-p cut-meta-imp-consistent-p
      checkpoint-collection-complete-p
      one-process-channel-snapshot-invariant-p
      one-process-channel-snapshot-correspondence))))


;; Use the full implementation process list. At checkpoint completion,
;; the channel invariant therefore gives correspondence for every channel.
(defthm
  all-processes-channel-snapshot-correspondence-when-checkpoint-collection-complete
  (implies
   (and
    (good-state-p imp-st)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m imp-st)
    (checkpoint-collection-complete-p m)
    (all-processes-channel-snapshot-invariant-p m imp-st before-st))
   (all-processes-channel-snapshot-correspondence m imp-st before-st))
  :hints
  (("Goal"
    :use
    ((:instance
      processes-channel-snapshot-correspondence-when-checkpoint-collection-complete
      (ids (proc-ids imp-st))))
    :in-theory
    (disable
     processes-channel-snapshot-correspondence-when-checkpoint-collection-complete
      processes-channel-snapshot-invariant-p
      processes-channel-snapshot-correspondence
      good-state-p good-cut-meta-p cut-meta-imp-consistent-p
      checkpoint-collection-complete-p))))






;; The local invariant compares before-cut local state with current local
;; state before I's cut, and with stored local state after its cut.
;; Completion selects the stored-state branch and gives correspondence.
(defthm
  one-process-local-snapshot-correspondence-when-checkpoint-collection-complete
  (implies
   (and
    (good-state-p imp-st)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m imp-st)
    (checkpoint-collection-complete-p m)
    (memberp i (proc-ids imp-st))
    (one-process-local-snapshot-invariant-p i m imp-st before-st))
   (one-process-local-snapshot-correspondence i m imp-st before-st))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance
      checkpoint-collection-complete-p-implies-process-cut-complete))
    :in-theory
    (disable
     checkpoint-collection-complete-p-implies-process-cut-complete
      good-state-p good-cut-meta-p cut-meta-imp-consistent-p
      checkpoint-collection-complete-p
      cm-cut-not-taken-p cm-waiting-marker-for))))


;; Lift completed local-state correspondence by induction over IDS,
;; using its subset premise to establish each process's membership.
(defthm
  processes-local-snapshot-correspondence-when-checkpoint-collection-complete
  (implies
   (and
    (good-state-p imp-st)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m imp-st)
    (checkpoint-collection-complete-p m)
    (subset ids (proc-ids imp-st))
    (processes-local-snapshot-invariant-p ids m imp-st before-st))
   (processes-local-snapshot-correspondence ids m imp-st before-st))
  :hints
  (("Goal"
    :induct
    (processes-local-snapshot-invariant-p ids m imp-st before-st)
    :in-theory
    (disable
     one-process-local-snapshot-invariant-p
      one-process-local-snapshot-correspondence
      good-state-p good-cut-meta-p cut-meta-imp-consistent-p
      checkpoint-collection-complete-p
      cm-cut-not-taken-p cm-waiting-marker-for))))


;; Instantiate the process-list result with all implementation process IDs
;; to obtain correspondence for the complete collection of local states.
(defthm
  all-processes-local-snapshot-correspondence-when-checkpoint-collection-complete
  (implies
   (and
    (good-state-p imp-st)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m imp-st)
    (checkpoint-collection-complete-p m)
    (all-processes-local-snapshot-invariant-p m imp-st before-st))
   (all-processes-local-snapshot-correspondence m imp-st before-st))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance
      processes-local-snapshot-correspondence-when-checkpoint-collection-complete
      (ids (proc-ids imp-st))))
    :in-theory
    (disable
     processes-local-snapshot-correspondence-when-checkpoint-collection-complete
      processes-local-snapshot-invariant-p
      processes-local-snapshot-correspondence
      good-state-p good-cut-meta-p cut-meta-imp-consistent-p
      checkpoint-collection-complete-p))))








































;; Connect the completed-checkpoint results to a checkpoint segment.
;; The argument follows the segment construction in GLOBAL_REORDER:
;; relate the segment scanner to PROCESS-CUT-SEGMENT, establish all initial
;; invariants for a fresh snapshot ID, preserve them through the inputs,
;; and apply correspondence when the final metadata reports completion.
;; Helper facts remain local to this encapsulate; the final combined
;; theorem and its channel and local-state corollaries are exported.
(encapsulate ()

;; Fresh metadata has no classified inputs yet, so its before-cut history
;; is empty.
(local-defthm snapshot-cm-before-cut-input-sequence-of-make-cut-meta
  (equal
   (cm-before-cut-input-sequence
    (make-cut-meta
     sid initiator st))
   nil))

;; The after-cut history is also empty before processing the segment.
(local-defthm snapshot-cm-after-cut-input-sequence-of-make-cut-meta
  (equal
   (cm-after-cut-input-sequence
    (make-cut-meta
     sid initiator st))
   nil))

;; The scanner may stop at checkpoint completion, whereas PROCESS-CUT-SEGMENT
;; processes the entire list. If completion occurs at the segment end, both
;; computations process the same inputs and produce the same metadata.
(local-defthm snapshot-scan-until-checkpoint-done-equals-process-cut-segment
  (implies
   (checkpoint-completes-at-segment-end-p
    input-seg st m)
   (equal
    (scan-until-checkpoint-done input-seg st m)
    (process-cut-segment input-seg st m)))
  :hints
  (("Goal"
    :induct
    (scan-until-checkpoint-done input-seg st m)
    :in-theory
    (disable
     process-cut-step
     system-step
     checkpoint-collection-complete-p))))

;; Apply the scanner equality to the segment's initial metadata. This lets
;; history-preservation theorems describe the final segment metadata.
(local-defthm snapshot-checkpoint-segment-meta-equals-process-cut-segment
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (equal
    (checkpoint-segment-meta st input-seg)
    (process-cut-segment
     input-seg
     st
     (checkpoint-segment-initial-meta st input-seg))))
  :hints
  (("Goal"
    :in-theory
    (disable
     checkpoint-segment-initial-meta
     checkpoint-segment-completep
     checkpoint-completes-at-segment-end-p
     scan-until-checkpoint-done
     process-cut-segment
     process-cut-step
     system-step
     checkpoint-collection-complete-p
     good-state-p
     legal-input-sequencep
     recovery-free-state-p
     cl-checkpoint-body-inputs-p))))

;; Extract the stored-SID counter condition for a particular initiator
;; from the condition imposed on every listed initiator.
(local-defthm snapshot-all-initiators-smaller-counters-when-memberp
  (implies
   (and
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators ids procs)
    (memberp initiator initiators))
   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator ids procs))
  :hints
  (("Goal"
    :induct
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators ids procs)
    :in-theory
    (disable
     all-stored-sids-for-initiator-have-smaller-counters-p))))

;; Stored SIDs for this initiator use strictly smaller counters. Therefore
;; the SID formed with its current counter is absent from all listed processes.
(local-defthm snapshot-all-stored-smaller-counters-implies-current-sid-absent
  (implies
   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator ids procs)
   (target-sid-absent-from-procs-p
    ids
    (list initiator
          (counter (g initiator procs)))
    procs))
  :hints
  (("Goal"
    :induct
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator ids procs)
    :in-theory
    (disable
     stored-sids-for-initiator-have-smaller-counters-p))))

;; GOOD-STATE-P supplies the stored-SID counter condition. For a valid
;; initiator, the next checkpoint SID is consequently fresh throughout ST.
(local-defthm snapshot-good-state-p-implies-current-sid-absent
  (implies
   (and
    (good-state-p st)
    (memberp initiator (proc-ids st)))
   (target-sid-absent-from-procs-p
    (proc-ids st)
    (list initiator
          (counter
           (g initiator (procs st))))
    (procs st)))
  :hints
  (("Goal"
    :expand
    ((good-state-p st))
    :in-theory
    (disable
     good-state-p
     all-initiators-stored-sids-have-smaller-counters-p
     all-stored-sids-for-initiator-have-smaller-counters-p
     target-sid-absent-from-procs-p))))

;; The metadata constructor retains the target SID supplied by its caller.
(local-defthm snapshot-cm-sid-of-make-cut-meta
  (equal
   (cm-sid
    (make-cut-meta sid initiator st))
   sid))

;; Initial metadata uses the implementation's process ID list.
(local-defthm snapshot-proc-ids-of-make-cut-meta
  (equal
   (g :proc-ids
      (make-cut-meta sid initiator st))
   (proc-ids st)))

;; Initially every implementation process still has to take its cut.
(local-defthm snapshot-cut-not-taken-of-make-cut-meta
  (equal
   (g :cut-not-taken
      (make-cut-meta sid initiator st))
   (proc-ids st)))

;; The segment begins with a legal checkpoint-start input, so its initiator
;; is a process in the starting state.
(local-defthm snapshot-checkpoint-complete-segment-p-implies-initiator-memberp
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (memberp
    (checkpoint-segment-initiator input-seg)
    (proc-ids st))))

;; Constructing metadata for the segment's fresh SID and valid initiator
;; makes that metadata consistent with the starting implementation state.
(local-defthm snapshot-checkpoint-complete-segment-p-implies-initial-meta-consistent
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (cut-meta-imp-consistent-p
    (checkpoint-segment-initial-meta st input-seg)
    st))
    :hints
    (("Goal"
      :use (snapshot-checkpoint-complete-segment-p-implies-initiator-memberp)
    :in-theory
    (disable
     make-cut-meta
     checkpoint-segment-completep
     checkpoint-completes-at-segment-end-p
     scan-until-checkpoint-done
     process-cut-segment
     process-cut-step
     system-step
     checkpoint-collection-complete-p
     good-state-p
     legal-input-sequencep
     recovery-free-state-p
     cl-checkpoint-body-inputs-p))))

;; Extract process membership from legality of the leading checkpoint-start
;; input, without requiring the full checkpoint-segment predicate.
(local-defthm snapshot-legal-start-checkpoint-sequence-implies-first-pid-memberp
  (implies
   (and
    (consp inputs)
    (legal-input-sequencep st inputs)
    (equal
     (ttype (first inputs))
     :start-checkpoint))

   (memberp
    (pid (first inputs))
    (proc-ids st))))

;; A listed process in a well-formed process table has a natural-number
;; counter, as required for the segment's checkpoint SID.
(local-defthm snapshot-good-procs-p-and-memberp-implies-counter-natp
  (implies
   (and
    (good-procs-p ids procs all-ids)
    (memberp i ids))
   (natp
    (counter
     (g i procs)))))

;; Every lookup in the initial waiting-marker table returns NIL. The
;; induction distinguishes the newly inserted process ID from other IDs.
(local-defthm snapshot-g-of-make-empty-waiting-marker-from
  (equal
   (g i
      (make-empty-waiting-marker-from ids))
   nil)

  :rule-classes nil

  :hints
  (("Goal"
    :induct
    (make-empty-waiting-marker-from ids))

   ("Subgoal *1/2''"
    :cases
    ((equal i (car ids)))

    :use
    (:instance
     g-of-s-diff
     (k1 i)
     (k2 (car ids))
     (v nil)
     (r
      (make-empty-waiting-marker-from
       (cdr ids)))))))

;; An empty waiting-marker table satisfies the waiting-row part of metadata
;; well-formedness for any supplied process list.
(local-defthm snapshot-good-cut-meta-waiting-for-procs-p-when-table-empty
  (implies
   (equal
    (g :waiting-marker-from m)
    (make-empty-waiting-marker-from all-ids))

   (good-cut-meta-waiting-for-procs-p
    ids m))

  :rule-classes nil

  :hints
  (("Goal"
    :induct
    (good-cut-meta-waiting-for-procs-p
     ids m)

    :in-theory
    (disable
     make-empty-waiting-marker-from
     cm-cut-not-taken-p
     cm-cut-not-taken
     cm-proc-ids))

   ("Subgoal *1/6''"
    :use
    (:instance
     snapshot-g-of-make-empty-waiting-marker-from
     (i (car ids))
     (ids all-ids)))

   ("Subgoal *1/5''"
    :use
    (:instance
     snapshot-g-of-make-empty-waiting-marker-from
     (i (car ids))
     (ids all-ids)))

   ("Subgoal *1/4''"
    :use
    (:instance
     snapshot-g-of-make-empty-waiting-marker-from
     (i (car ids))
     (ids all-ids)))

   ("Subgoal *1/3''"
    :use
    (:instance
     snapshot-g-of-make-empty-waiting-marker-from
     (i (car ids))
     (ids all-ids)))))

;; Combine the segment's valid initiator and counter with the initial empty
;; waiting rows to establish well-formedness of its initial metadata.
(local-defthm snapshot-checkpoint-start-end-segment-p-implies-initial-meta-good
  (implies
   (checkpoint-start-end-segment-p st input-seg)

   (good-cut-meta-p
    (checkpoint-segment-initial-meta
     st input-seg)))

  :rule-classes nil

  :hints
  (("Goal"
    :use
    ((:instance
      snapshot-good-cut-meta-waiting-for-procs-p-when-table-empty
      (ids (proc-ids st))
      (all-ids (proc-ids st))
      (m
       (checkpoint-segment-initial-meta
        st input-seg))))

    :in-theory
    (disable
     good-proc-p
     legal-input-sequencep
     recovery-free-state-p
     cl-checkpoint-body-inputs-p
     scan-until-checkpoint-done
     process-cut-segment
     process-cut-step
     system-step))))

;; Specialize the constructor's empty-history facts to the segment's
;; initial metadata, for both the before-cut and after-cut histories.
(local-defthm snapshot-checkpoint-segment-initial-meta-input-sequences-empty
  (and
   (equal
    (cm-before-cut-input-sequence
     (checkpoint-segment-initial-meta st input-seg))
    nil)

   (equal
    (cm-after-cut-input-sequence
     (checkpoint-segment-initial-meta st input-seg))
    nil))

  :rule-classes nil

  :hints
  (("Goal"
    :use
    ((:instance
      snapshot-cm-before-cut-input-sequence-of-make-cut-meta
      (sid
       (checkpoint-segment-sid st input-seg))
      (initiator
       (checkpoint-segment-initiator input-seg)))

     (:instance
      snapshot-cm-after-cut-input-sequence-of-make-cut-meta
      (sid
       (checkpoint-segment-sid st input-seg))
      (initiator
       (checkpoint-segment-initiator input-seg))))

    :expand
    ((checkpoint-segment-initial-meta
      st input-seg))

    :in-theory
    (disable
     checkpoint-segment-initial-meta
     checkpoint-segment-sid
     checkpoint-segment-initiator
     make-cut-meta
     cm-before-cut-input-sequence
     cm-after-cut-input-sequence))))

;; Relate the freshness predicate to the predicate that searches for
;; a process storing the target SID. Freshness rules out such a process.
(local-defthm snapshot-absent-sid-not-known-by-any-process
  (implies
   (target-sid-absent-from-procs-p ids target-sid procs)
   (not (some-proc-has-snapshot-id-p target-sid ids procs)))
  :hints
  (("Goal"
    :induct (target-sid-absent-from-procs-p ids target-sid procs))))

;; Well-formed marker messages require the SID to be known by a process.
;; If no process stores the target SID, a good message list cannot contain
;; a marker for it.
(local-defthm snapshot-no-target-marker-in-good-message-list
  (implies
   (and
    (good-msg-list-p msgs ids procs)
    (target-sid-absent-from-procs-p ids target-sid procs))
   (not (marker-for-sid-in-channel-p target-sid msgs)))
  :hints
  (("Goal"
    :induct (good-msg-list-p msgs ids procs)
    :in-theory
    (disable target-sid-absent-from-procs-p
             some-proc-has-snapshot-id-p))))

;; The process recognizer restricts incoming neighbors to valid process
;; IDs. Extract that membership fact for neighbor J of process I.
(local-defthm snapshot-incoming-neighbor-is-a-process
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st))
    (memberp j (nbrs-from (g i (procs st)))))
   (memberp j (proc-ids st)))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance good-proc-p-of-g-when-good-procs-p
      (ids (proc-ids st))
      (procs (procs st))
      (all-ids (proc-ids st)))
     (:instance memberp-when-subset
      (a j)
      (xs (nbrs-from (g i (procs st))))
      (ys (proc-ids st))))
    :expand
    ((good-state-p st)
     (good-proc-p (g i (procs st)) (proc-ids st)))
    :in-theory
    (disable good-state-p good-proc-p good-procs-p
             good-snapshots-p good-snapshot-ids-list-p
             good-channels-p
             nbrs-from-to-consistent-p nbrs-to-from-consistent-p
             all-initiators-stored-sids-have-smaller-counters-p))))

;; Apply marker absence to a well-formed incoming channel. This rules out
;; target markers already being in transit before the fresh checkpoint starts.
(local-defthm snapshot-no-fresh-target-marker-on-incoming-channel
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st))
    (memberp j (nbrs-from (g i (procs st))))
    (target-sid-absent-from-procs-p
     (proc-ids st) target-sid (procs st)))
   (not
    (marker-for-sid-in-channel-p
     target-sid (channel-state j i (channels st)))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    (snapshot-incoming-neighbor-is-a-process
     (:instance good-msg-list-p-of-channel-state-when-good-state-p-nbrs-from)
     (:instance snapshot-no-target-marker-in-good-message-list
      (msgs (channel-state j i (channels st)))
      (ids (proc-ids st))
      (procs (procs st))))
    :in-theory
    (disable good-state-p good-msg-list-p
             target-sid-absent-from-procs-p
             marker-for-sid-in-channel-p
             snapshot-incoming-neighbor-is-a-process
             good-msg-list-p-of-channel-state-when-good-state-p-nbrs-from
             snapshot-no-target-marker-in-good-message-list))))

;; Without a target marker, the normal-message prefix before that marker
;; is the entire normal-message projection. This also holds with an
;; improper terminal atom, since both projections produce a proper list.
(local-defthm snapshot-normal-prefix-is-entire-projection-when-marker-absent
  (implies
   (not (marker-for-sid-in-channel-p target-sid channel))
   (equal
    (normal-msgs-before-target-marker target-sid channel)
    (project-channel-msgs-to-spec channel)))
  :hints
  (("Goal"
    :induct (channel-before-target-marker target-sid channel))))

;; Establish snapshot-message equality, cut-phase consistency, and uncut
;; channel agreement before the first input. Both execution states are ST,
;; no target messages have been recorded, and freshness excludes a target
;; marker that could truncate the initial normal-message projection.
(local-defthm snapshot-initial-one-channel-invariants
  (implies
   (and
    (good-state-p st)
    (target-sid-absent-from-procs-p
     (proc-ids st) target-sid (procs st))
    (memberp i (proc-ids st))
    (memberp j (nbrs-from (g i (procs st)))))
   (let ((m (make-cut-meta target-sid initiator st)))
     (and
      (one-channel-snapshot-invariant-p j i m st st)
      (one-channel-cut-phase-consistent-p j i m st)
      (one-uncut-incoming-channel-agrees-p j i m st st))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    (snapshot-incoming-neighbor-is-a-process
     snapshot-no-fresh-target-marker-on-incoming-channel
     (:instance
      snapshot-normal-prefix-is-entire-projection-when-marker-absent
      (channel (channel-state j i (channels st))))
     (:instance at-most-one-target-marker-p-when-absent
      (channel (channel-state j i (channels st)))))
    :in-theory
    (disable good-state-p target-sid-absent-from-procs-p
             marker-for-sid-in-channel-p at-most-one-target-marker-p
             normal-msgs-before-target-marker
             project-channel-msgs-to-spec
             make-empty-waiting-marker-from))))

;; Lift the three initial channel facts by induction over a supplied subset
;; of I's incoming neighbors.
(local-defthm snapshot-initial-incoming-channel-invariants
  (implies
   (and
    (good-state-p st)
    (target-sid-absent-from-procs-p
     (proc-ids st) target-sid (procs st))
    (memberp i (proc-ids st))
    (subset incoming-nbrs (nbrs-from (g i (procs st)))))
   (let ((m (make-cut-meta target-sid initiator st)))
     (and
      (incoming-channels-snapshot-invariant-p
       incoming-nbrs i m st st)
      (incoming-channels-cut-phase-consistent-p
       incoming-nbrs i m st)
      (uncut-incoming-channels-agree-p
       incoming-nbrs i m st st))))
  :hints
  (("Goal"
    :induct
    (incoming-channels-snapshot-invariant-p
     incoming-nbrs i (make-cut-meta target-sid initiator st) st st)
    :in-theory
    (disable good-state-p target-sid-absent-from-procs-p
             make-cut-meta
             one-channel-snapshot-invariant-p
             one-channel-cut-phase-consistent-p
             one-uncut-incoming-channel-agrees-p))))

;; Process agreement is reflexive when both execution states are ST,
;; including the checkpoint-control information used by the agreement test.
(local-defthm snapshot-one-uncut-process-agrees-with-itself
  (one-uncut-process-agrees-p i m st st)
  :hints
  (("Goal"
    :expand ((proc-equivalent-p
              (g i (procs st)) (g i (procs st))))
    :in-theory (disable cl-checkpoint-control-view))))

;; Initial metadata leaves I uncut. The local invariant therefore compares
;; I's current local state with itself.
(local-defthm snapshot-initial-one-process-local-invariant
  (implies
   (memberp i (proc-ids st))
   (one-process-local-snapshot-invariant-p
    i (make-cut-meta target-sid initiator st) st st))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (disable make-empty-waiting-marker-from))))

;; Lift the initial channel and local facts across IDS. Together they give
;; before-state agreement, channel cut-phase consistency, and both snapshot
;; invariants for any subset of the starting process IDs.
(local-defthm snapshot-initial-process-invariants
  (implies
   (and
    (good-state-p st)
    (target-sid-absent-from-procs-p
     (proc-ids st) target-sid (procs st))
    (subset ids (proc-ids st)))
   (let ((m (make-cut-meta target-sid initiator st)))
     (and
      (before-imp-state-agree-aux-p ids m st st)
      (processes-channel-cut-phase-consistent-p ids m st)
      (processes-channel-snapshot-invariant-p ids m st st)
      (processes-local-snapshot-invariant-p ids m st st))))
  :hints
  (("Goal"
    :induct
    (before-imp-state-agree-aux-p
     ids (make-cut-meta target-sid initiator st) st st)
    :in-theory
    (disable good-state-p target-sid-absent-from-procs-p make-cut-meta
             incoming-channels-snapshot-invariant-p
             incoming-channels-cut-phase-consistent-p
             uncut-incoming-channels-agree-p
             one-uncut-process-agrees-p
             one-process-local-snapshot-invariant-p))))

;; Reconstructing the before-cut state from fresh metadata runs an empty
;; history and returns ST. The constructor form is kept explicit so the
;; equality also matches goals after initial segment metadata is expanded.
(local-defthm snapshot-before-state-of-make-cut-meta
  (equal
   (before-cut-state-from-meta
    st (make-cut-meta target-sid initiator st))
   st)
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance snapshot-cm-before-cut-input-sequence-of-make-cut-meta
      (sid target-sid)))
    :expand
    ((before-cut-state-from-meta
      st (make-cut-meta target-sid initiator st))
     (run-imp st nil))
    :in-theory
    (disable make-cut-meta cm-before-cut-input-sequence
             before-cut-state-from-meta run-imp system-step
             snapshot-cm-before-cut-input-sequence-of-make-cut-meta))))

;; Specialize the empty-history reconstruction to initial segment metadata.
(local-defthm snapshot-before-state-of-initial-segment-meta
  (equal
   (before-cut-state-from-meta
    st (checkpoint-segment-initial-meta st input-seg))
   st)
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance snapshot-before-state-of-make-cut-meta
      (target-sid (checkpoint-segment-sid st input-seg))
      (initiator (checkpoint-segment-initiator input-seg))))
    :expand
    ((checkpoint-segment-initial-meta st input-seg))
    :in-theory
    (disable checkpoint-segment-initial-meta make-cut-meta
             before-cut-state-from-meta run-imp system-step
             snapshot-before-state-of-make-cut-meta))))

;; Collect every initial fact needed by history preservation: good and
;; consistent metadata, the reconstructed before state ST, before-state
;; agreement, cut-phase consistency, and the channel and local invariants.
(local-defthm snapshot-checkpoint-segment-initial-invariants
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (let ((m (checkpoint-segment-initial-meta st input-seg)))
     (and
      (good-cut-meta-p m)
      (cut-meta-imp-consistent-p m st)
      (equal (before-cut-state-from-meta st m) st)
      (before-imp-state-agree-p m st st)
      (all-processes-channel-cut-phase-consistent-p m st)
      (all-processes-channel-snapshot-invariant-p m st st)
      (all-processes-local-snapshot-invariant-p m st st))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    (snapshot-checkpoint-complete-segment-p-implies-initiator-memberp
     snapshot-checkpoint-complete-segment-p-implies-initial-meta-consistent
     snapshot-checkpoint-start-end-segment-p-implies-initial-meta-good
     snapshot-before-state-of-initial-segment-meta
     (:instance snapshot-before-state-of-make-cut-meta
      (target-sid (checkpoint-segment-sid st input-seg))
      (initiator (checkpoint-segment-initiator input-seg)))
     (:instance snapshot-good-state-p-implies-current-sid-absent
      (initiator (checkpoint-segment-initiator input-seg)))
     (:instance snapshot-initial-process-invariants
      (ids (proc-ids st))
      (target-sid (checkpoint-segment-sid st input-seg))
      (initiator (checkpoint-segment-initiator input-seg))))
    :in-theory
    (disable good-state-p recovery-free-state-p legal-input-sequencep
             good-cut-meta-p cut-meta-imp-consistent-p
             cl-checkpoint-body-inputs-p checkpoint-segment-completep
             checkpoint-completes-at-segment-end-p
             before-cut-state-from-meta
             before-imp-state-agree-aux-p
             processes-channel-cut-phase-consistent-p
             processes-channel-snapshot-invariant-p
             processes-local-snapshot-invariant-p
             target-sid-absent-from-procs-p make-cut-meta
             snapshot-before-state-of-make-cut-meta
             snapshot-before-state-of-initial-segment-meta))))

;; The segment predicate classifies the tail as checkpoint-body inputs.
;; Its leading checkpoint-start input also belongs to that class, so
;; history preservation applies to the entire input segment.
(local-defthm snapshot-checkpoint-segment-inputs-are-body-inputs
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (cl-checkpoint-body-inputs-p input-seg))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory
    (disable good-state-p recovery-free-state-p legal-input-sequencep
             checkpoint-segment-completep
             checkpoint-completes-at-segment-end-p))))

;; Extract checkpoint collection completion from the segment predicate
;; for the metadata returned by the segment scanner.
(local-defthm snapshot-checkpoint-segment-final-meta-is-complete
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (checkpoint-collection-complete-p
    (checkpoint-segment-meta st input-seg)))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory
    (disable checkpoint-collection-complete-p checkpoint-segment-meta
             good-state-p recovery-free-state-p legal-input-sequencep
             cl-checkpoint-body-inputs-p
             checkpoint-completes-at-segment-end-p))))

;; The before-state reconstruction and the segment's before-cut execution
;; use the same classified input list. This equality connects their names.
(local-defthm snapshot-checkpoint-segment-before-state
  (equal
   (before-cut-state-from-meta st (checkpoint-segment-meta st input-seg))
   (run-imp st (checkpoint-segment-before-cut-inputs st input-seg)))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory
    (disable run-imp checkpoint-segment-meta cm-before-cut-input-sequence))))

;; Start from metadata and states satisfying the preservation hypotheses.
;; Preserve both snapshot invariants through INPUTS, and obtain final
;; state well-formedness and metadata consistency from their preservation
;; theorems. If the final metadata is complete, the completed-checkpoint
;; results yield channel and local-state correspondence with the before
;; state reconstructed from the final before-cut history.
(local-defthm snapshot-correspondence-after-complete-inputs-history
  (let ((before-st-cur
         (before-cut-state-from-meta imp-st-start m-cur)))
    (implies
     (and
      (good-state-p imp-st-cur)
      (good-state-p before-st-cur)
      (recovery-free-state-p imp-st-cur)
      (recovery-free-state-p before-st-cur)
      (good-cut-meta-p m-cur)
      (cut-meta-imp-consistent-p m-cur imp-st-cur)
      (cl-checkpoint-body-inputs-p inputs)
      (legal-input-sequencep imp-st-cur inputs)
      (before-imp-state-agree-p m-cur imp-st-cur before-st-cur)
      (all-processes-channel-cut-phase-consistent-p m-cur imp-st-cur)
      (all-processes-channel-snapshot-invariant-p
       m-cur imp-st-cur before-st-cur)
      (all-processes-local-snapshot-invariant-p
       m-cur imp-st-cur before-st-cur)
      (checkpoint-collection-complete-p
       (process-cut-segment inputs imp-st-cur m-cur)))
     (let* ((m-final (process-cut-segment inputs imp-st-cur m-cur))
            (imp-st-final (run-imp imp-st-cur inputs))
            (before-st-final
             (before-cut-state-from-meta imp-st-start m-final)))
       (and
        (all-processes-channel-snapshot-correspondence
         m-final imp-st-final before-st-final)
        (all-processes-local-snapshot-correspondence
         m-final imp-st-final before-st-final)))))
  :rule-classes nil
  :hints
  (("Goal"
    :do-not-induct t
    :use
    (all-processes-channel-snapshot-invariant-p-preserved-by-inputs-history
     all-processes-local-snapshot-invariant-p-preserved-by-inputs-history
     (:instance good-state-p-of-run-imp-when-legal-input-sequencep
      (st imp-st-cur))
     (:instance good-cut-meta-p-over-process-cut-segment
      (st imp-st-cur) (m m-cur))
     (:instance cut-meta-imp-consistent-p-over-process-cut-segment
      (st imp-st-cur) (m m-cur))
     (:instance
      all-processes-channel-snapshot-correspondence-when-checkpoint-collection-complete
      (m (process-cut-segment inputs imp-st-cur m-cur))
      (imp-st (run-imp imp-st-cur inputs))
      (before-st
       (before-cut-state-from-meta
        imp-st-start (process-cut-segment inputs imp-st-cur m-cur))))
     (:instance
      all-processes-local-snapshot-correspondence-when-checkpoint-collection-complete
      (m (process-cut-segment inputs imp-st-cur m-cur))
      (imp-st (run-imp imp-st-cur inputs))
      (before-st
       (before-cut-state-from-meta
        imp-st-start (process-cut-segment inputs imp-st-cur m-cur)))))
    :in-theory
    (disable all-processes-channel-snapshot-invariant-p-preserved-by-inputs-history
             all-processes-local-snapshot-invariant-p-preserved-by-inputs-history
             good-state-p-of-run-imp-when-legal-input-sequencep
             good-cut-meta-p-over-process-cut-segment
             cut-meta-imp-consistent-p-over-process-cut-segment
             all-processes-channel-snapshot-correspondence-when-checkpoint-collection-complete
             all-processes-local-snapshot-correspondence-when-checkpoint-collection-complete
             good-state-p recovery-free-state-p
             good-cut-meta-p cut-meta-imp-consistent-p
             cl-checkpoint-body-inputs-p legal-input-sequencep
             before-imp-state-agree-p
             all-processes-channel-cut-phase-consistent-p
             all-processes-channel-snapshot-invariant-p
             all-processes-local-snapshot-invariant-p
             all-processes-channel-snapshot-correspondence
             all-processes-local-snapshot-correspondence
             checkpoint-collection-complete-p
             before-cut-state-from-meta process-cut-segment run-imp))))

;; Main segment result: run the entire segment to collect its snapshot,
;; and run only its before-cut inputs to construct the cut state.
;; The final recorded channels and local states match that cut state.
;; Apply the history result using the initial invariants and the scanner
;; equalities; segment completion supplies the final completion premise.
(defthm checkpoint-start-end-segment-snapshot-correspondence
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (let* ((m-final (checkpoint-segment-meta st input-seg))
          (imp-st-final (run-imp st input-seg))
          (before-st-final
           (run-imp st (checkpoint-segment-before-cut-inputs st input-seg))))
     (and
      (all-processes-channel-snapshot-correspondence
       m-final imp-st-final before-st-final)
      (all-processes-local-snapshot-correspondence
       m-final imp-st-final before-st-final))))
  :rule-classes nil
  :hints
  (("Goal"
    :do-not-induct t
    :use
    (snapshot-checkpoint-segment-initial-invariants
     snapshot-checkpoint-segment-inputs-are-body-inputs
     snapshot-checkpoint-segment-meta-equals-process-cut-segment
     snapshot-checkpoint-segment-final-meta-is-complete
     snapshot-checkpoint-segment-before-state
     (:instance snapshot-correspondence-after-complete-inputs-history
      (inputs input-seg)
      (imp-st-start st)
      (imp-st-cur st)
      (m-cur (checkpoint-segment-initial-meta st input-seg))))
    :in-theory
    (disable good-state-p recovery-free-state-p legal-input-sequencep
             cl-checkpoint-body-inputs-p
             good-cut-meta-p cut-meta-imp-consistent-p
             before-imp-state-agree-p
             all-processes-channel-cut-phase-consistent-p
             all-processes-channel-snapshot-invariant-p
             all-processes-local-snapshot-invariant-p
             all-processes-channel-snapshot-correspondence
             all-processes-local-snapshot-correspondence
             checkpoint-segment-initial-meta checkpoint-segment-meta
             checkpoint-segment-before-cut-inputs checkpoint-segment-completep
             checkpoint-completes-at-segment-end-p
             checkpoint-collection-complete-p
             before-cut-state-from-meta process-cut-segment run-imp
             snapshot-checkpoint-segment-initial-invariants
             snapshot-checkpoint-segment-inputs-are-body-inputs
             snapshot-checkpoint-segment-meta-equals-process-cut-segment
             snapshot-checkpoint-segment-final-meta-is-complete
             snapshot-checkpoint-segment-before-state))))

;; Extract the channel-message part of the combined segment theorem.
(defthm checkpoint-start-end-segment-channel-snapshot-correspondence
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (all-processes-channel-snapshot-correspondence
    (checkpoint-segment-meta st input-seg)
    (run-imp st input-seg)
    (run-imp st (checkpoint-segment-before-cut-inputs st input-seg))))
  :hints
  (("Goal"
    :do-not-induct t
    :use (checkpoint-start-end-segment-snapshot-correspondence)
    :in-theory
    (disable checkpoint-start-end-segment-p
             all-processes-channel-snapshot-correspondence
             all-processes-local-snapshot-correspondence
             checkpoint-segment-meta checkpoint-segment-before-cut-inputs
             run-imp))))

;; Extract the recorded-local-state part of the combined segment theorem.
(defthm checkpoint-start-end-segment-local-snapshot-correspondence
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (all-processes-local-snapshot-correspondence
    (checkpoint-segment-meta st input-seg)
    (run-imp st input-seg)
    (run-imp st (checkpoint-segment-before-cut-inputs st input-seg))))
  :hints
  (("Goal"
    :do-not-induct t
    :use (checkpoint-start-end-segment-snapshot-correspondence)
    :in-theory
    (disable checkpoint-start-end-segment-p
             all-processes-channel-snapshot-correspondence
             all-processes-local-snapshot-correspondence
             checkpoint-segment-meta checkpoint-segment-before-cut-inputs
             run-imp))))

) ; end checkpoint-segment correspondence
