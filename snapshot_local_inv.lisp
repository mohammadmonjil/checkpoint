(in-package "ACL2")
(include-book "snapshot_channel_inv_preserved")

; Before the cut, compare current local states. After the cut, compare
; the before-cut local state with the local state recorded for CM-SID.
(defun one-process-local-snapshot-invariant-p
    (i m imp-st before-st)
  (let ((imp-proc (g i (procs imp-st)))
        (before-proc (g i (procs before-st))))
    (if (cm-cut-not-taken-p m i)
        (equal (local-state before-proc)
               (local-state imp-proc))
      (equal (local-state before-proc)
             (g :local-snap-shot
                (snapshot-entry (cm-sid m) imp-proc))))))

; Recording normal messages changes channel snapshots only.
(defthm local-snap-shot-of-record-msg-in-snapshots-for-target-sid
  (equal
   (g :local-snap-shot
      (g target-sid
         (record-msg-in-snapshots snapshots snapshot-ids j msg)))
   (g :local-snap-shot
      (g target-sid snapshots)))
  :hints
  (("Goal"
    :induct
    (record-msg-in-snapshots snapshots snapshot-ids j msg)
    :in-theory (enable record-msg-in-snapshots))))

; Load this event after the uncut-process preservation theorem and
; before-cut-state-from-meta-after-process-cut-step.
; ACL2 admission of these new events has not been checked here.
(defthm
  one-process-local-snapshot-invariant-p-preserved-by-one-step-history
  (let ((before-st-cur
         (before-cut-state-from-meta imp-st-start m-cur)))
    (implies
     (and
      (good-state-p imp-st-cur)
      (good-state-p before-st-cur)
      (recovery-free-state-p imp-st-cur)
      (recovery-free-state-p before-st-cur)
      (cl-checkpoint-body-input-p input)
      (legal-inputp imp-st-cur input)
      (good-cut-meta-p m-cur)
      (cut-meta-imp-consistent-p m-cur imp-st-cur)
      (memberp i (proc-ids imp-st-cur))
      (before-imp-state-agree-p
       m-cur imp-st-cur before-st-cur)
      (one-process-local-snapshot-invariant-p
       i m-cur imp-st-cur before-st-cur))
     (let* ((m-next
             (process-cut-step input imp-st-cur m-cur))
            (imp-st-next
             (system-step imp-st-cur input))
            (before-st-next
             (before-cut-state-from-meta imp-st-start m-next)))
       (one-process-local-snapshot-invariant-p
        i m-next imp-st-next before-st-next))))
  :hints
  (("Goal"
    :do-not-induct t
    :cases
    ((equal i (pid input))
     (cm-cut-not-taken-p m-cur i))
    :use
    ((:instance
      before-imp-state-agree-aux-p-implies-one-uncut-process-agrees-p
      (ids (proc-ids imp-st-cur))
      (m m-cur)
      (imp-st imp-st-cur)
      (before-st
       (before-cut-state-from-meta imp-st-start m-cur)))
     (:instance
      before-imp-state-agree-aux-p-implies-one-incoming-channel
      (ids (proc-ids imp-st-cur))
      (m m-cur)
      (imp-st imp-st-cur)
      (before-st
       (before-cut-state-from-meta imp-st-start m-cur))
      (i (pid input))
      (incoming-nbr (sender input)))
     (:instance
      one-uncut-process-agrees-p-preserved-by-one-step-history)
     (:instance
      before-cut-state-from-meta-after-process-cut-step
      (st imp-st-cur)
      (m m-cur)))
    :in-theory
    (disable
     good-state-p
      good-cut-meta-p
      cut-meta-imp-consistent-p
      recovery-free-state-p
      before-imp-state-agree-aux-p
      uncut-incoming-channels-agree-p
      channel-through-target-marker
      before-cut-state-from-meta
      before-cut-state-from-meta-after-process-cut-step
      one-uncut-process-agrees-p-preserved-by-one-step-history
      run-imp
      cm-cut-not-taken
      record-msg-in-snapshots
      send-compute-message
      send-msg-all-outgoing-channels
      remove-message-from-channel))))




(defun processes-local-snapshot-invariant-p
    (ids m imp-st before-st)
  (if (endp ids)
      t
    (and
     (one-process-local-snapshot-invariant-p
      (first ids) m imp-st before-st)
     (processes-local-snapshot-invariant-p
      (rest ids) m imp-st before-st))))

(defun all-processes-local-snapshot-invariant-p
    (m imp-st before-st)
  (processes-local-snapshot-invariant-p
   (proc-ids imp-st) m imp-st before-st))


(defthm processes-local-snapshot-invariant-p-preserved-aux
  (let ((before-st-cur
         (before-cut-state-from-meta imp-st-start m-cur)))
    (implies
     (and
      (good-state-p imp-st-cur)
      (good-state-p before-st-cur)
      (recovery-free-state-p imp-st-cur)
      (recovery-free-state-p before-st-cur)
      (cl-checkpoint-body-input-p input)
      (legal-inputp imp-st-cur input)
      (good-cut-meta-p m-cur)
      (cut-meta-imp-consistent-p m-cur imp-st-cur)
      (before-imp-state-agree-p
       m-cur imp-st-cur before-st-cur)
      (subset ids (proc-ids imp-st-cur))
      (processes-local-snapshot-invariant-p
       ids m-cur imp-st-cur before-st-cur))
     (let* ((m-next
             (process-cut-step input imp-st-cur m-cur))
            (imp-st-next
             (system-step imp-st-cur input))
            (before-st-next
             (before-cut-state-from-meta imp-st-start m-next)))
       (processes-local-snapshot-invariant-p
        ids m-next imp-st-next before-st-next))))
  :hints
  (("Goal"
    :induct
    (processes-local-snapshot-invariant-p
     ids m-cur imp-st-cur
     (before-cut-state-from-meta imp-st-start m-cur))
    :in-theory
    (disable
     one-process-local-snapshot-invariant-p
      good-state-p good-cut-meta-p cut-meta-imp-consistent-p
      recovery-free-state-p
      legal-inputp cl-checkpoint-body-input-p
      before-imp-state-agree-p
      before-cut-state-from-meta
      before-cut-state-from-meta-after-process-cut-step
      system-step process-cut-step run-imp))))


(defthm
  all-processes-local-snapshot-invariant-p-preserved-by-one-step-history
  (let ((before-st-cur
         (before-cut-state-from-meta imp-st-start m-cur)))
    (implies
     (and
      (good-state-p imp-st-cur)
      (good-state-p before-st-cur)
      (recovery-free-state-p imp-st-cur)
      (recovery-free-state-p before-st-cur)
      (cl-checkpoint-body-input-p input)
      (legal-inputp imp-st-cur input)
      (good-cut-meta-p m-cur)
      (cut-meta-imp-consistent-p m-cur imp-st-cur)
      (before-imp-state-agree-p
       m-cur imp-st-cur before-st-cur)
      (all-processes-local-snapshot-invariant-p
       m-cur imp-st-cur before-st-cur))
     (let* ((m-next
             (process-cut-step input imp-st-cur m-cur))
            (imp-st-next
             (system-step imp-st-cur input))
            (before-st-next
             (before-cut-state-from-meta imp-st-start m-next)))
       (all-processes-local-snapshot-invariant-p
        m-next imp-st-next before-st-next))))
  :hints
  (("Goal"
    :use
    ((:instance
      processes-local-snapshot-invariant-p-preserved-aux
      (ids (proc-ids imp-st-cur))))
    :in-theory
    (disable
     processes-local-snapshot-invariant-p-preserved-aux
      processes-local-snapshot-invariant-p
      one-process-local-snapshot-invariant-p
      good-state-p good-cut-meta-p cut-meta-imp-consistent-p
      recovery-free-state-p
      legal-inputp cl-checkpoint-body-input-p
      before-imp-state-agree-p
      before-cut-state-from-meta
      before-cut-state-from-meta-after-process-cut-step
      system-step process-cut-step run-imp))))




(defthm
  all-processes-local-snapshot-invariant-p-preserved-by-inputs-history
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
      (before-imp-state-agree-p
       m-cur imp-st-cur before-st-cur)
      (all-processes-channel-cut-phase-consistent-p
       m-cur imp-st-cur)
      (all-processes-local-snapshot-invariant-p
       m-cur imp-st-cur before-st-cur))

     (let* ((m-final
             (process-cut-segment inputs imp-st-cur m-cur))
            (imp-st-final
             (run-imp imp-st-cur inputs))
            (before-st-final
             (before-cut-state-from-meta imp-st-start m-final)))
       (all-processes-local-snapshot-invariant-p
        m-final imp-st-final before-st-final))))
  :hints
  (("Goal"
    :induct (process-cut-segment inputs imp-st-cur m-cur)
    :in-theory
    (disable
     all-processes-local-snapshot-invariant-p
      processes-local-snapshot-invariant-p
      one-process-local-snapshot-invariant-p
      before-imp-state-agree-p
      all-processes-channel-cut-phase-consistent-p
      before-cut-state-from-meta
      before-cut-state-from-meta-after-process-cut-step
      good-state-p
      recovery-free-state-p
      good-cut-meta-p
      cut-meta-imp-consistent-p
      legal-inputp
      cl-checkpoint-body-input-p
      process-cut-step
      system-step))))
