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

(include-book "snapshot_channel_inv_one_step")

;; We will prove preservation of the required conditions of the
;; channel snapshot invariant for one system-step and process-cut-step
;; We have two main conditions to prove
;;    1. before-imp-state-agree-p
;;    2. all-processes-channel-cut-phase-consistent-p

;; We start with second one
;; We will first prove the one-channel-cut-phase-consistent version
;; Then later lift it process level and then state level



(defthm one-channel-cut-phase-consistent-p-preserved-by-one-step
  (implies
   (and
    (good-state-p st)
    (recovery-free-state-p st)
    (cl-checkpoint-body-input-p input)
    (legal-inputp st input)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m st)

    (memberp i (proc-ids st))
    (memberp j (nbrs-from (g i (procs st))))

    (one-channel-cut-phase-consistent-p j i m st))

   (one-channel-cut-phase-consistent-p
    j i
    (process-cut-step input st m)
    (system-step st input))))
