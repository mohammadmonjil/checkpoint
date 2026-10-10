; MIT License
;
; Copyright (c) 2026 Mohammad Bin Monjil and Sandip Ray
;
; Permission is hereby granted, free of charge, to any person obtaining a copy
; of this software and associated documentation files (the "Software"), to deal
; in the Software without restriction, including without limitation the rights
; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
; copies of the Software, and to permit persons to whom the Software is
; furnished to do so, subject to the following conditions:
;
; The above copyright notice and this permission notice shall be included in all
; copies or substantial portions of the Software.
;
; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
; SOFTWARE.


(in-package "ACL2")

(include-book "snap_ch_inv_preds_one_step")


(defthm legal-inputp-of-before-state-when-process-uncut
  (implies
   (and
    (before-imp-state-agree-p m imp-st before-st)
    (recovery-free-state-p before-st)
    (cl-checkpoint-body-input-p input)
    (legal-inputp imp-st input)
    (cm-cut-not-taken-p m (pid input)))
   (legal-inputp before-st input))
  :rule-classes ((:rewrite :match-free :all))
  :hints
  (("Goal"
    :do-not-induct t
    :cases ((equal (ttype input) :receive)
            (equal (ttype input) :start-checkpoint))
    :use
    ((:instance
      before-imp-state-agree-aux-p-implies-one-uncut-process-agrees-p
      (ids (proc-ids imp-st))
      (i (pid input)))
     (:instance
      before-imp-state-agree-aux-p-implies-one-incoming-channel
      (ids (proc-ids imp-st))
      (i (pid input))
      (incoming-nbr (sender input))))
    :in-theory
    (disable
     before-imp-state-agree-aux-p
      uncut-incoming-channels-agree-p
      channel-through-target-marker
      any-proc-recovering-p
      no-recovery-msgs-in-channels-p))))

; The before-cut execution advances exactly when the acting process was
; uncut before the implementation step.
(defthm before-cut-state-from-meta-after-process-cut-step
  (equal
   (before-cut-state-from-meta
    imp-st-start (process-cut-step input st m))
   (if (cm-cut-not-taken-p m (pid input))
       (system-step
        (before-cut-state-from-meta imp-st-start m) input)
     (before-cut-state-from-meta imp-st-start m)))
  :hints
  (("Goal"
    :do-not-induct t
    :cases ((cm-cut-not-taken-p m (pid input)))
    :in-theory
    (disable
     system-step run-imp))))

; Supply both reconstructed-state hypotheses needed by the next
; application of the one-step agreement theorem.
(defthm before-cut-state-well-formed-preserved-by-one-step
  (let ((before-st
         (before-cut-state-from-meta imp-st-start m)))
    (implies
     (and
      (good-state-p before-st)
      (recovery-free-state-p before-st)
      (cl-checkpoint-body-input-p input)
      (legal-inputp st input)
      (before-imp-state-agree-p m st before-st))
     (let ((before-st-next
            (before-cut-state-from-meta
             imp-st-start (process-cut-step input st m))))
       (and
        (good-state-p before-st-next)
        (recovery-free-state-p before-st-next)))))
  :hints
  (("Goal"
    :do-not-induct t
    :cases ((cm-cut-not-taken-p m (pid input)))
    :use
    ((:instance legal-inputp-of-before-state-when-process-uncut
      (imp-st st)
      (before-st (before-cut-state-from-meta imp-st-start m)))
     (:instance good-state-p-of-system-step-when-legal-inputp
      (st (before-cut-state-from-meta imp-st-start m)))
     (:instance recovery-free-state-p-preserved-by-checkpoint-body-step
      (st (before-cut-state-from-meta imp-st-start m))))
    :in-theory
     (disable
      before-cut-state-from-meta
      process-cut-step
      system-step
      run-imp
      legal-inputp
      cl-checkpoint-body-input-p
      good-state-p
      recovery-free-state-p
      before-imp-state-agree-p
      cm-cut-not-taken-p
      legal-inputp-of-before-state-when-process-uncut
      good-state-p-of-system-step-when-legal-inputp
      recovery-free-state-p-preserved-by-checkpoint-body-step))))

; Cut-phase consistency over a legal checkpoint-body input sequence.
(defthm
  all-processes-channel-cut-phase-consistent-p-preserved-by-inputs
  (implies
   (and
    (good-state-p st)
    (recovery-free-state-p st)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m st)
    (cl-checkpoint-body-inputs-p inputs)
    (legal-input-sequencep st inputs)
    (all-processes-channel-cut-phase-consistent-p m st))
   (all-processes-channel-cut-phase-consistent-p
    (process-cut-segment inputs st m)
    (run-imp st inputs)))
  :hints
  (("Goal"
    :induct (process-cut-segment inputs st m)
    :in-theory
    (disable
     all-processes-channel-cut-phase-consistent-p
      good-state-p
      recovery-free-state-p
      good-cut-meta-p
      cut-meta-imp-consistent-p
      legal-inputp
      cl-checkpoint-body-input-p
      process-cut-step
      system-step))))

; Before/implementation agreement over a legal checkpoint-body sequence.
; IMP-ST-START remains fixed during induction: it is the starting state
; used to reconstruct the before-cut history, not the current state.



(defthm before-imp-state-agree-p-preserved-by-inputs-history
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
       m-cur imp-st-cur))
     (let* ((m-final
             (process-cut-segment inputs imp-st-cur m-cur))
            (imp-st-final
             (run-imp imp-st-cur inputs))
            (before-st-final
             (before-cut-state-from-meta imp-st-start m-final)))
       (before-imp-state-agree-p
        m-final imp-st-final before-st-final))))
  :hints
  (("Goal"
    :induct (process-cut-segment inputs imp-st-cur m-cur)
    :in-theory
    (disable
     before-imp-state-agree-p
     before-cut-state-from-meta-after-process-cut-step
      all-processes-channel-cut-phase-consistent-p
      before-cut-state-from-meta
      good-state-p
      recovery-free-state-p
      good-cut-meta-p
      cut-meta-imp-consistent-p
      legal-inputp
      cl-checkpoint-body-input-p
      process-cut-step
      system-step))))




(defthm
  all-processes-channel-snapshot-invariant-p-preserved-by-inputs-history
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
      (all-processes-channel-snapshot-invariant-p
       m-cur imp-st-cur before-st-cur))
     (let* ((m-final
             (process-cut-segment inputs imp-st-cur m-cur))
            (imp-st-final
             (run-imp imp-st-cur inputs))
            (before-st-final
             (before-cut-state-from-meta imp-st-start m-final)))
       (all-processes-channel-snapshot-invariant-p
        m-final imp-st-final before-st-final))))
  :hints
  (("Goal"
    :induct (process-cut-segment inputs imp-st-cur m-cur)
    :in-theory
    (disable
     all-processes-channel-snapshot-invariant-p
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
