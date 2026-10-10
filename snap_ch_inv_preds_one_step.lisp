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

(include-book "snap_ch_inv_one_step")

;; We will prove preservation of the required conditions of the
;; channel snapshot invariant for one system-step and process-cut-step
;; We have two main conditions to prove
;;    1. before-imp-state-agree-p
;;    2. all-processes-channel-cut-phase-consistent-p

;; We start with second one
;; We will first prove the one-channel-cut-phase-consistent version
;; Then later lift it process level and then state level



(defthm at-most-one-target-marker-p-of-snoc-compute-message
  (equal
   (at-most-one-target-marker-p
    target-sid
    (snoc channel
          (create-compute-message local-state nbr)))
   (at-most-one-target-marker-p target-sid channel)))

;;send-compute-msg does not at-most-one-target-marker-p
(defthm at-most-one-target-marker-p-of-send-compute-message
  (equal
   (at-most-one-target-marker-p
    target-sid
    (channel-state
     j i
     (send-compute-message
      local-state k nbrs channels)))
   (at-most-one-target-marker-p
    target-sid
    (channel-state j i channels))))


;;send-compute-msg does not change marker-for-sid-in-channel-p

(defthm marker-for-sid-in-channel-p-of-send-compute-message
  (equal
   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     j i
     (send-compute-message
      local-state k nbrs channels)))
   (marker-for-sid-in-channel-p
    target-sid
    (channel-state j i channels))))


(defthm recovery-free-state-p-implies-receive-head-not-recovery
  (implies
   (and
    (good-state-p st)
    (recovery-free-state-p st)
    (memberp (pid input) (proc-ids st))
    (memberp
     (sender input)
     (nbrs-from (g (pid input) (procs st))))
    (consp
     (channel-state
      (sender input) (pid input) (channels st))))
   (not
    (equal
     (msg-type
      (first
       (channel-state
        (sender input) (pid input) (channels st))))
     :recovery)))
  :hints
  (("Goal"
    :use
    ((:instance
      incoming-nbr-memberp-proc-ids-when-good-state-p
      (i (pid input))
      (incoming-nbr (sender input)))
     (:instance
      recovery-free-state-p-implies-get-msg-not-recovery
      (i (pid input))
      (incoming-nbr (sender input)))))))


(defthm at-most-one-target-marker-p-when-no-target-marker
  (implies
   (not (marker-for-sid-in-channel-p target-sid channel))
   (at-most-one-target-marker-p target-sid channel)))


(defthm target-marker-absent-after-remove-message
  (implies
   (not
    (marker-for-sid-in-channel-p
     target-sid (channel-state j i channels)))
   (not
    (marker-for-sid-in-channel-p
     target-sid
     (channel-state
      j i
      (remove-message-from-channel
       sender receiver channels))))))


(defthm at-most-one-target-marker-after-broadcast-from-absent
  (implies
   (and
    (uniquep nbrs)
    (not
     (marker-for-sid-in-channel-p
      target-sid (channel-state j i channels))))
   (at-most-one-target-marker-p
    target-sid
    (channel-state
     j i
     (send-msg-all-outgoing-channels
      msg source nbrs channels)))))


(defthm good-state-p-implies-uniquep-nbrs-to
  (implies
   (and (good-state-p st)
        (memberp k (proc-ids st)))
   (uniquep
    (nbrs-to (g k (procs st)))))
  :hints
  (("Goal"
    :use
    ((:instance
      good-proc-p-of-g-when-good-procs-p
      (ids (proc-ids st))
      (procs (procs st))
      (all-ids (proc-ids st))
      (i k))))))


(defthm marker-for-sid-in-channel-p-of-snoc-same-marker
  (implies
   (equal (msg-type msg) :marker)
   (marker-for-sid-in-channel-p
    (sid msg)
    (snoc channel msg))))

(defthm marker-present-after-target-broadcast-to-member
  (implies
   (and (memberp dst nbrs)
        (equal (msg-type msg) :marker)
        (equal (sid msg) target-sid))
   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src dst
     (send-msg-all-outgoing-channels
      msg src nbrs channels)))))



(defthm marker-absent-after-remove-message
  (implies
   (not (marker-for-sid-in-channel-p
         target-sid (channel-state j i channels)))
   (not (marker-for-sid-in-channel-p
         target-sid
         (channel-state
          j i
          (remove-message-from-channel src dst channels))))))

(defthm marker-presence-of-send-all-non-target
  (implies
   (not (target-marker-msg-p target-sid msg))
   (equal
    (marker-for-sid-in-channel-p
     target-sid
     (channel-state
      j i
      (send-msg-all-outgoing-channels msg send-src nbrs channels)))
    (marker-for-sid-in-channel-p
     target-sid (channel-state j i channels))))
  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg send-src nbrs channels))))

(defthm at-most-one-target-marker-p-when-absent
  (implies
   (not (marker-for-sid-in-channel-p target-sid channel))
   (at-most-one-target-marker-p target-sid channel))
  :hints
  (("Goal"
    :induct
    (at-most-one-target-marker-p target-sid channel))))



(defthm at-most-one-after-remove-and-forward-non-target
  (implies
   (and
    (not (target-marker-msg-p target-sid msg))
    (not (marker-for-sid-in-channel-p
          target-sid (channel-state j i channels))))
   (at-most-one-target-marker-p
    target-sid
    (channel-state
     j i
     (send-msg-all-outgoing-channels
      msg send-src nbrs
      (remove-message-from-channel src dst channels)))))
  :hints
  (("Goal"
    :use
    ((:instance marker-absent-after-remove-message
                (target-sid target-sid))
     (:instance marker-presence-of-send-all-non-target
                (target-sid target-sid)
                (channels
                 (remove-message-from-channel src dst channels)))
     (:instance at-most-one-target-marker-p-when-absent
                (target-sid target-sid)
                (channel
                 (channel-state
                  j i
                  (send-msg-all-outgoing-channels
                   msg send-src nbrs
                   (remove-message-from-channel
                    src dst channels))))))
    :in-theory
    (disable marker-absent-after-remove-message
             marker-presence-of-send-all-non-target
             at-most-one-target-marker-p-when-absent))))


(defthm at-most-one-target-marker-p-of-remove-message
  (implies
   (at-most-one-target-marker-p
    target-sid (channel-state j i channels))
   (at-most-one-target-marker-p
    target-sid
    (channel-state
     j i
     (remove-message-from-channel src dst channels)))))

(defthm at-most-one-target-marker-p-of-send-non-target
  (implies
   (not (target-marker-msg-p target-sid msg))
   (equal
    (at-most-one-target-marker-p
     target-sid
     (channel-state
      j i
      (send-msg-all-outgoing-channels
       msg send-src nbrs channels)))
    (at-most-one-target-marker-p
     target-sid (channel-state j i channels))))
  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg send-src nbrs channels))))


(defthm memberp-of-remove1-equal-when-different-iff
  (implies
   (not (equal x y))
   (equal (memberp x (remove1-equal y xs))
          (memberp x xs))))



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
    (system-step st input)))
  :hints
  (("Subgoal 2.2.2"
    :use
    ((:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x j)
                (y (g :pid input))
                (xs (cm-cut-not-taken m)))
     (:instance nbrs-from-implies-nbrs-to-when-good-state-p
                (st st) (i i) (j j))))

   ("Subgoal 6.2.1.1'"
    :use
    ((:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x i)
                (y (g :pid input))
                (xs (cm-cut-not-taken m)))))

   ("Subgoal 6.2.1.3"
    :use
    ((:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x i)
                (y (g :pid input))
                (xs (cm-cut-not-taken m)))
     (:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x j)
                (y (g :pid input))
                (xs (cm-cut-not-taken m)))
     (:instance nbrs-from-implies-nbrs-to-when-good-state-p
                (st st) (i i) (j j))
     (:instance marker-present-after-target-broadcast-to-member
                (target-sid (g :sid m))
                (msg
                 (create-marker-message
                  (g :local-state
                     (g (g :pid input) (g :procs st)))
                  (g :sid m)))
                (src (g :pid input))
                (dst i)
                (nbrs
                 (g :nbrs-to
                    (g (g :pid input) (g :procs st))))
                (channels (g :channels st)))))

   ("Subgoal 6.2.2.2"
    :use
    ((:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x j)
                (y (g :pid input))
                (xs (cm-cut-not-taken m)))
     (:instance nbrs-from-implies-nbrs-to-when-good-state-p
                (st st) (i i) (j j))
     (:instance marker-present-after-target-broadcast-to-member
                (target-sid (g :sid m))
                (msg
                 (create-marker-message
                  (g :local-state
                     (g (g :pid input) (g :procs st)))
                  (g :sid m)))
                (src (g :pid input))
                (dst i)
                (nbrs
                 (g :nbrs-to
                    (g (g :pid input) (g :procs st))))
                (channels (g :channels st)))))

   ("Subgoal 6.4'"
    :use
    ((:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x i)
                (y (g :pid input))
                (xs (cm-cut-not-taken m)))))

   ("Subgoal 12.2.3'"
    :cases ((equal i (g :pid input))))

   ("Subgoal 12.4.3'"
    :cases ((equal i (g :pid input))))

   ("Subgoal 14.2.2"
    :use
    ((:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x j)
                (y (g :pid input))
                (xs (cm-cut-not-taken m)))
     (:instance incoming-nbr-memberp-proc-ids-when-good-state-p
                (st st)
                (i i)
                (incoming-nbr j))
     (:instance nbrs-from-implies-nbrs-to-when-good-state-p
                (st st) (i i) (j j))
     (:instance marker-present-after-target-broadcast-to-member
                (target-sid (g :sid m))
                (msg
                 (car
                  (g (g :sender input)
                     (g (g :pid input) (g :channels st)))))
                (src (g :pid input))
                (dst i)
                (nbrs
                 (g :nbrs-to
                    (g (g :pid input) (g :procs st))))
                (channels
                 (remove-message-from-channel
                  (g :sender input)
                  (g :pid input)
                  (g :channels st))))))

   ("Subgoal 24.2.1'"
    :use
    ((:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x i)
                (y (g :pid input))
                (xs (cm-cut-not-taken m)))))

   ("Subgoal 24.2.3'"
    :use
    ((:instance incoming-nbr-memberp-proc-ids-when-good-state-p
                (i i)
                (incoming-nbr (pid input)))
     (:instance good-state-p-implies-uniquep-nbrs-to
                (k (pid input)))
     (:instance target-marker-absent-after-remove-message
                (target-sid (cm-sid m))
                (j (pid input))
                (i i)
                (sender (pid input))
                (receiver (pid input))
                (channels (channels st)))
     (:instance at-most-one-target-marker-after-broadcast-from-absent
                (target-sid (cm-sid m))
                (j (pid input))
                (i i)
                (msg
                 (first
                  (channel-state
                   (pid input) (pid input) (channels st))))
                (source (pid input))
                (nbrs
                 (nbrs-to (g (pid input) (procs st))))
                (channels
                 (remove-message-from-channel
                  (pid input) (pid input) (channels st))))))

   ("Subgoal 24.2.2'"
    :use
    ((:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x i)
                (y (g :pid input))
                (xs (cm-cut-not-taken m)))))

   ("Subgoal 24.2.4"
    :use
    ((:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x i)
                (y (pid input))
                (xs (cm-cut-not-taken m)))))

   ("Subgoal 24.2"
    :use
    ((:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x j)
                (y (pid input))
                (xs (cm-cut-not-taken m)))
     (:instance incoming-nbr-memberp-proc-ids-when-good-state-p
                (i i)
                (incoming-nbr j))
     (:instance memberp-of-remove1-equal-when-different
                (x j)
                (y (sender input))
                (xs (nbrs-from (g i (procs st)))))
     (:instance nbrs-from-implies-nbrs-to-when-good-state-p
                (i i)
                (j j))))

   ("Subgoal 24.4.5"
    :use
    ((:instance memberp-and-not-memberp-remove1-equal-implies-equal
                (x i)
                (y (pid input))
                (xs (cm-cut-not-taken m)))
     (:instance memberp-of-remove1-equal-when-different
                (x j)
                (y (sender input))
                (xs (nbrs-from (g i (procs st)))))))

   ("Goal"
    :in-theory
    (disable good-state-p
             good-cut-meta-p
             get-msg-from-channel
             remove-message-from-channel
             create-marker-message
             cut-meta-imp-consistent-p
             recovery-free-state-p
             cm-cut-not-taken
             make-snapshot-entry
             update-proc-for-first-marker-msg
             update-proc-for-non-first-marker-msg
             append-singleton-equal-snoc
             update-proc-for-normal-msg-core))))




(defthm incoming-channels-cut-phase-consistent-p-preserved-aux
  (implies
   (and
    (good-state-p st)
    (recovery-free-state-p st)
    (cl-checkpoint-body-input-p input)
    (legal-inputp st input)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m st)
    (memberp i (proc-ids st))
    (subset incoming-nbrs
                   (nbrs-from (g i (procs st))))
    (incoming-channels-cut-phase-consistent-p
     incoming-nbrs i m st))
   (incoming-channels-cut-phase-consistent-p
    incoming-nbrs
    i
    (process-cut-step input st m)
    (system-step st input)))
  :hints
  (("Goal"
    :induct
    (incoming-channels-cut-phase-consistent-p
     incoming-nbrs i m st)
    :in-theory
    (disable one-channel-cut-phase-consistent-p
             process-cut-step
             system-step
             good-state-p
             recovery-free-state-p
             good-cut-meta-p
             cut-meta-imp-consistent-p
             legal-inputp
             cl-checkpoint-body-input-p))))



(defthm incoming-channels-cut-phase-consistent-p-preserved-by-one-step
  (let ((incoming-nbrs
         (nbrs-from (g i (procs st)))))
    (implies
     (and
      (good-state-p st)
      (recovery-free-state-p st)
      (cl-checkpoint-body-input-p input)
      (legal-inputp st input)
      (good-cut-meta-p m)
      (cut-meta-imp-consistent-p m st)
      (memberp i (proc-ids st))
      (incoming-channels-cut-phase-consistent-p
       incoming-nbrs i m st))
     (incoming-channels-cut-phase-consistent-p
      incoming-nbrs
      i
      (process-cut-step input st m)
      (system-step st input))))
  :hints
  (("Goal"
    :use
    ((:instance
      incoming-channels-cut-phase-consistent-p-preserved-aux
      (incoming-nbrs
       (nbrs-from (g i (procs st))))))
    :in-theory
    (disable one-channel-cut-phase-consistent-p
             process-cut-step
             system-step
             good-state-p
             recovery-free-state-p
             good-cut-meta-p
             cut-meta-imp-consistent-p
             legal-inputp
             cl-checkpoint-body-input-p))))





(defthm processes-channel-cut-phase-consistent-p-preserved-by-one-step
  (implies
   (and
    (good-state-p st)
    (recovery-free-state-p st)
    (cl-checkpoint-body-input-p input)
    (legal-inputp st input)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m st)
    (subset ids (proc-ids st))
    (processes-channel-cut-phase-consistent-p ids m st))
   (processes-channel-cut-phase-consistent-p
    ids
    (process-cut-step input st m)
    (system-step st input)))
  :hints
  (("Goal"
    :induct
    (processes-channel-cut-phase-consistent-p ids m st)
    :in-theory
    (disable incoming-channels-cut-phase-consistent-p
             process-cut-step
             system-step
             good-state-p
             recovery-free-state-p
             good-cut-meta-p
             cut-meta-imp-consistent-p
             legal-inputp
             cl-checkpoint-body-input-p))))




(defthm all-processes-channel-cut-phase-consistent-p-preserved-by-one-step
  (implies
   (and
    (good-state-p st)
    (recovery-free-state-p st)
    (cl-checkpoint-body-input-p input)
    (legal-inputp st input)
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p m st)
    (all-processes-channel-cut-phase-consistent-p m st))
   (all-processes-channel-cut-phase-consistent-p
    (process-cut-step input st m)
    (system-step st input)))
  :hints
  (("Goal"
    :use
    ((:instance
      processes-channel-cut-phase-consistent-p-preserved-by-one-step
      (ids (proc-ids st))))
    :in-theory
    (disable incoming-channels-cut-phase-consistent-p
             process-cut-step
             system-step
             good-state-p
             recovery-free-state-p
             good-cut-meta-p
             cut-meta-imp-consistent-p
             legal-inputp
             cl-checkpoint-body-input-p))))






;;We will now prove preservation of before-imp-state-agrees-p
;;We start with one-uncut-incoming-channels-agree-p


(defthm channel-state-of-matching-send-compute-message-same-data
  (implies
   (equal (channel-state j i channels-1)
          (channel-state j i channels-2))
   (equal
    (channel-state
     j i
     (send-compute-message local-state k nbrs channels-1))
    (channel-state
     j i
     (send-compute-message local-state k nbrs channels-2))))
  :rule-classes nil
  :hints
  (("Goal"
    :induct
    (matching-send-compute-message-induct
     local-state k nbrs channels-1 channels-2))))


(defthm channel-state-of-matching-send-when-both-endpoints-uncut
  (implies
   (and
    (before-imp-state-agree-aux-p
     (proc-ids imp-st) m imp-st before-st)

    (memberp i (proc-ids imp-st))
    (memberp j (nbrs-from (g i (procs imp-st))))

    (memberp i (cm-cut-not-taken m))
    (memberp j (cm-cut-not-taken m)))

   (equal
    (channel-state
     j i
     (send-compute-message
      local-state k nbrs (channels before-st)))

    (channel-state
     j i
     (send-compute-message
      local-state k nbrs (channels imp-st)))))

  :rule-classes
  ((:rewrite :match-free :all))

  :hints
  (("Goal"
    :in-theory
    (disable
     send-compute-message
     before-imp-state-agree-aux-p
     one-uncut-incoming-channel-agrees-p
     before-imp-state-agree-aux-p-implies-one-incoming-channel
     one-uncut-incoming-channel-agrees-p-implies-channel-equal)

    :use
    ((:instance
      before-imp-state-agree-aux-p-implies-one-incoming-channel
      (ids (proc-ids imp-st))
      (incoming-nbr j))

     (:instance
      one-uncut-incoming-channel-agrees-p-implies-channel-equal
      (incoming-nbr j))

     (:instance
      channel-state-of-matching-send-compute-message-same-data
      (channels-1 (channels before-st))
      (channels-2 (channels imp-st)))))))





(defun matching-send-msg-all-induct
    (msg send-src nbrs channels-1 channels-2)
  (declare
   (irrelevant msg send-src channels-1 channels-2))
  (if (endp nbrs)
      t
    (matching-send-msg-all-induct
     msg send-src (rest nbrs)

     (>channel
      send-src (first nbrs)
      (snoc
       (channel-state send-src (first nbrs) channels-1)
       msg)
      channels-1)

     (>channel
      send-src (first nbrs)
      (snoc
       (channel-state send-src (first nbrs) channels-2)
       msg)
      channels-2))))




(defthm channel-state-of-matching-send-msg-all-same-data
  (implies
   (equal (channel-state j i channels-1)
          (channel-state j i channels-2))
   (equal
    (channel-state
     j i
     (send-msg-all-outgoing-channels
      msg send-src nbrs channels-1))
    (channel-state
     j i
     (send-msg-all-outgoing-channels
      msg send-src nbrs channels-2))))

  :rule-classes nil

  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg send-src nbrs channels-1))))



(defthm
  channel-state-of-matching-remove-then-broadcast-when-both-endpoints-uncut

  (implies
   (and
    (before-imp-state-agree-aux-p
     (proc-ids imp-st) m imp-st before-st)

    (memberp i (proc-ids imp-st))
    (memberp j (nbrs-from (g i (procs imp-st))))

    (memberp i (cm-cut-not-taken m))
    (memberp j (cm-cut-not-taken m)))

   (equal
    (channel-state
     j i
     (send-msg-all-outgoing-channels
      msg send-src nbrs
      (remove-message-from-channel
       sender receiver (channels before-st))))

    (channel-state
     j i
     (send-msg-all-outgoing-channels
      msg send-src nbrs
      (remove-message-from-channel
       sender receiver (channels imp-st))))))

  :rule-classes
  ((:rewrite :match-free :all))

  :hints
  (("Goal"
    :cases
    ((equal j sender)
     (equal i receiver))

    :in-theory
    (disable
     send-msg-all-outgoing-channels
     remove-message-from-channel
      before-imp-state-agree-aux-p
      one-uncut-incoming-channel-agrees-p
      before-imp-state-agree-aux-p-implies-one-incoming-channel
      one-uncut-incoming-channel-agrees-p-implies-channel-equal)

    :use
    ((:instance
      before-imp-state-agree-aux-p-implies-one-incoming-channel
      (ids (proc-ids imp-st))
      (incoming-nbr j))

     (:instance
      one-uncut-incoming-channel-agrees-p-implies-channel-equal
      (incoming-nbr j))

     (:instance
      channel-state-of-matching-send-msg-all-same-data
      (channels-1
       (remove-message-from-channel
        sender receiver (channels before-st)))
      (channels-2
       (remove-message-from-channel
        sender receiver (channels imp-st))))))))


(defthm counter-equal-when-before-imp-state-agree-and-process-uncut
  (implies
   (and
    (before-imp-state-agree-aux-p
     ids m imp-st before-st)
    (memberp i ids)
    (memberp i (cm-cut-not-taken m)))

   (equal
    (g :counter (g i (procs imp-st)))
    (g :counter (g i (procs before-st)))))

  :rule-classes
  ((:rewrite :match-free :all))

  :hints
  (("Goal"
    :use
    ((:instance
      before-imp-state-agree-aux-p-implies-one-uncut-process-agrees-p
      (ids ids))))))



(defthm matching-broadcast-channel-equality-when-both-uncut
  (implies
   (and
    (before-imp-state-agree-aux-p
     ids m imp-st before-st)

    (memberp i ids)
    (memberp j
             (g :nbrs-from (g i (g :procs imp-st))))

    (memberp i (cm-cut-not-taken m))
    (memberp j (cm-cut-not-taken m)))

   (iff
    (equal
     (g j
        (g i
           (send-msg-all-outgoing-channels
            msg send-src nbrs
            (g :channels before-st))))

     (g j
        (g i
           (send-msg-all-outgoing-channels
            msg send-src nbrs
            (g :channels imp-st)))))
    t))

  :rule-classes
  ((:rewrite :match-free :all))

  :hints
  (("Goal"
    :use
    ((:instance
      before-imp-state-agree-aux-p-implies-channel-equal-when-both-uncut
      (incoming-nbr j))

     (:instance
      channel-state-of-matching-send-msg-all-same-data
      (channels-1 (g :channels before-st))
      (channels-2 (g :channels imp-st)))))))







(defthm channel-through-target-marker-of-snoc-when-marker-present
  (implies
   (marker-for-sid-in-channel-p target-sid channel)
   (equal
    (channel-through-target-marker
     target-sid (snoc channel msg))
    (channel-through-target-marker
     target-sid channel))))


(defthm
  channel-through-target-marker-of-send-compute-message-when-marker-present

  (implies
   (marker-for-sid-in-channel-p
    target-sid (g j (g i channels)))

   (equal
    (channel-through-target-marker
     target-sid
     (g j
        (g i
           (send-compute-message
            local-state k nbrs channels))))

    (channel-through-target-marker
     target-sid
     (g j (g i channels)))))

  :hints
  (("Goal"
    :induct
    (send-compute-message local-state k nbrs channels))))




(defthm channel-state-of-send-msg-all-when-uniquep
  (implies
   (uniquep nbrs)
   (equal
    (g j
       (g i
          (send-msg-all-outgoing-channels
           msg j nbrs channels)))
    (if (memberp i nbrs)
        (snoc (g j (g i channels)) msg)
      (g j (g i channels)))))

  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels msg j nbrs channels))))

(defthm channel-through-target-marker-of-snoc-target-marker-when-absent
  (implies
   (and
    (not (marker-for-sid-in-channel-p target-sid channel))
    (target-marker-msg-p target-sid msg))
   (equal
    (channel-through-target-marker
     target-sid (snoc channel msg))
    (snoc channel msg))))


(defthm uniquep-start-nbrs-to-of-uncut-incoming-neighbor
  (implies
   (and
    (good-state-p st)

    (before-imp-state-agree-aux-p
     (g :proc-ids st) m st
     (run-imp start-st (g :before-cut-input-sequence m)))

    (memberp i (g :proc-ids st))
    (memberp k (g :nbrs-from (g i (g :procs st))))
    (memberp k (g :cut-not-taken m)))

   (uniquep
    (g :nbrs-to (g k (g :procs start-st)))))

  :rule-classes
  ((:rewrite :match-free :all))

  :hints
  (("Goal"
    :in-theory
    (disable
     good-state-p
      before-imp-state-agree-aux-p
      run-imp
      incoming-nbr-memberp-proc-ids-when-good-state-p
      good-state-p-implies-uniquep-nbrs-to
      nbrs-to-equal-of-uncut-process
      nbrs-to-of-run-imp)

    :use
    ((:instance
      incoming-nbr-memberp-proc-ids-when-good-state-p
      (incoming-nbr k))

     (:instance
      good-state-p-implies-uniquep-nbrs-to
      (st st)
      (k k))

     (:instance
      nbrs-to-equal-of-uncut-process
      (ids (g :proc-ids st))
      (m m)
      (imp-st st)
      (before-st
       (run-imp start-st (g :before-cut-input-sequence m)))
      (k k))

     (:instance
      nbrs-to-of-run-imp
      (st start-st)
      (inputs (g :before-cut-input-sequence m))
      (i k))))))

(defthm channel-through-target-marker-after-first-target-marker-broadcast
  (let* ((k (g :pid input))
         (msg
          (car
           (g (g :sender input)
              (g k (g :channels st)))))
         (next-channels
          (send-msg-all-outgoing-channels
           msg k
           (g :nbrs-to (g k (g :procs start-st)))
           (remove-message-from-channel
            (g :sender input) k (g :channels st)))))

    (implies
     (and
      (good-state-p st)
      (memberp k (g :proc-ids st))
      (memberp i (g :proc-ids st))
      (memberp j (g :nbrs-from (g i (g :procs st))))
      (not (equal i k))

      (before-imp-state-agree-aux-p
       (g :proc-ids st) m st
       (run-imp start-st (g :before-cut-input-sequence m)))

      (memberp k (cm-cut-not-taken m))
      (memberp j (cm-cut-not-taken m))
      (not
       (memberp j
                (remove1-equal k (cm-cut-not-taken m))))

      (not
       (marker-for-sid-in-channel-p
        (g :sid m) (g j (g i (g :channels st)))))
      (target-marker-msg-p (g :sid m) msg))

     (equal
      (channel-through-target-marker
       (g :sid m) (g j (g i next-channels)))
      (g j (g i next-channels)))))

  :hints
  (("Goal"
    :do-not-induct t

    :in-theory
    (disable
     good-state-p
      before-imp-state-agree-aux-p
      run-imp
      send-msg-all-outgoing-channels
      channel-through-target-marker)

    :use
    ((:instance
      memberp-and-not-memberp-remove1-equal-implies-equal
      (x j)
      (y (g :pid input))
      (xs (cm-cut-not-taken m)))

     (:instance
      uniquep-start-nbrs-to-of-uncut-incoming-neighbor
      (k (g :pid input)))

     (:instance
      nbrs-from-implies-nbrs-to-when-good-state-p
      (st st) (i i) (j j))

     (:instance
      good-state-p-implies-uniquep-nbrs-to
      (st st)
      (k (g :pid input)))

     (:instance
      nbrs-to-equal-of-uncut-process
      (ids (g :proc-ids st))
      (m m)
      (imp-st st)
      (before-st
       (run-imp start-st (g :before-cut-input-sequence m)))
      (k (g :pid input)))

     (:instance
      nbrs-to-of-run-imp
      (st start-st)
      (inputs (g :before-cut-input-sequence m))
      (i (g :pid input)))))))





(defthm marker-for-sid-in-channel-p-of-send-msg-all-when-present
  (implies
   (marker-for-sid-in-channel-p
    target-sid (g j (g i channels)))

   (marker-for-sid-in-channel-p
    target-sid
    (g j
       (g i
          (send-msg-all-outgoing-channels
           msg send-src nbrs channels)))))

  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg send-src nbrs channels))))


(defthm
  channel-through-target-marker-of-remove-then-broadcast-when-marker-present

  (implies
   (and
    (not (equal i receiver))
    (marker-for-sid-in-channel-p
     target-sid (g j (g i channels))))

   (equal
    (channel-through-target-marker
     target-sid
     (g j
        (g i
           (send-msg-all-outgoing-channels
            msg send-src nbrs
            (remove-message-from-channel
             sender receiver channels)))))

    (channel-through-target-marker
     target-sid
     (g j (g i channels)))))

  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg send-src nbrs channels))))





(defthm channel-through-target-marker-of-first-broadcast-equals-before-channel
  (let* ((before-st
          (run-imp start-st (g :before-cut-input-sequence m)))
         (nbrs
          (g :nbrs-to (g k (g :procs start-st))))
         (msg
          (create-marker-message local-state (g :sid m))))

    (implies
     (and
      (good-state-p st)
      (memberp k (g :proc-ids st))
      (memberp i (g :proc-ids st))
      (memberp j (g :nbrs-from (g i (g :procs st))))

      (before-imp-state-agree-aux-p
       (g :proc-ids st) m st before-st)

      (memberp i (cm-cut-not-taken m))
      (memberp j (cm-cut-not-taken m))
      (memberp k (cm-cut-not-taken m))
      (not
       (memberp j
                (remove1-equal k (cm-cut-not-taken m))))

      (not
       (marker-for-sid-in-channel-p
        (g :sid m) (g j (g i (g :channels st))))))

     (equal
      (channel-through-target-marker
       (g :sid m)
       (g j
          (g i
             (send-msg-all-outgoing-channels
              msg k nbrs (g :channels st)))))

      (g j
         (g i
            (send-msg-all-outgoing-channels
             msg k nbrs (g :channels before-st)))))))

  :hints
  (("Goal"
    :do-not-induct t

    :in-theory
    (disable
     good-state-p
      before-imp-state-agree-aux-p
      run-imp
      send-msg-all-outgoing-channels
      channel-through-target-marker
      before-imp-state-agree-aux-p-implies-channel-equal-when-both-uncut
      nbrs-from-implies-nbrs-to-when-good-state-p
      nbrs-to-equal-of-uncut-process
      nbrs-to-of-run-imp
      uniquep-start-nbrs-to-of-uncut-incoming-neighbor)

    :use
    ((:instance
      memberp-and-not-memberp-remove1-equal-implies-equal
      (x j)
      (y k)
      (xs (cm-cut-not-taken m)))

     (:instance
      before-imp-state-agree-aux-p-implies-channel-equal-when-both-uncut
      (ids (g :proc-ids st))
      (m m)
      (imp-st st)
      (before-st
       (run-imp start-st (g :before-cut-input-sequence m)))
      (incoming-nbr j))

     (:instance
      nbrs-from-implies-nbrs-to-when-good-state-p
      (st st) (i i) (j j))

     (:instance
      nbrs-to-equal-of-uncut-process
      (ids (g :proc-ids st))
      (m m)
      (imp-st st)
      (before-st
       (run-imp start-st (g :before-cut-input-sequence m)))
      (k k))

     (:instance
      nbrs-to-of-run-imp
      (st start-st)
      (inputs (g :before-cut-input-sequence m))
      (i k))

     (:instance
      uniquep-start-nbrs-to-of-uncut-incoming-neighbor
      (k k))))))



(defthm
  channel-through-target-marker-of-send-msg-all-when-marker-present

  (implies
   (marker-for-sid-in-channel-p
    target-sid (g j (g i channels)))

   (equal
    (channel-through-target-marker
     target-sid
     (g j
        (g i
           (send-msg-all-outgoing-channels
            msg send-src nbrs channels))))

    (channel-through-target-marker
     target-sid
     (g j (g i channels)))))

  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg send-src nbrs channels))))



(defthm
  one-uncut-incoming-channel-agrees-p-preserved-by-one-step-history

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
      (memberp incoming-nbr
               (nbrs-from (g i (procs imp-st-cur))))

      (before-imp-state-agree-p
       m-cur imp-st-cur before-st-cur)

      (one-channel-cut-phase-consistent-p
       incoming-nbr i m-cur imp-st-cur)

      (one-uncut-incoming-channel-agrees-p
       incoming-nbr i m-cur imp-st-cur before-st-cur))

     (let* ((m-next
             (process-cut-step input imp-st-cur m-cur))
            (imp-st-next
             (system-step imp-st-cur input))
            (before-st-next
             (before-cut-state-from-meta imp-st-start m-next)))

       (one-uncut-incoming-channel-agrees-p
        incoming-nbr i m-next imp-st-next before-st-next))))
  :hints (("Goal"
	   :do-not-induct t
	   :cases ((not (equal i (pid input))))
	   :in-theory (disable good-state-p
			       good-cut-meta-p
			       get-msg-from-channel
			       remove-message-from-channel
			       cut-meta-imp-consistent-p
			       recovery-free-state-p
					; run-imp
			       cm-cut-not-taken
			       make-snapshot-entry
			       create-marker-message
			       UPDATE-PROC-FOR-FIRST-MARKER-MSG
			       UPDATE-PROC-FOR-NON-FIRST-MARKER-MSG
			       APPEND-SINGLETON-EQUAL-SNOC
			       UPDATE-PROC-FOR-NORMAL-MSG-CORE))))






(defthm uncut-incoming-channels-agree-p-preserved-aux
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
      (subset incoming-nbrs
              (nbrs-from (g i (procs imp-st-cur))))

      (before-imp-state-agree-p
       m-cur imp-st-cur before-st-cur)

      (incoming-channels-cut-phase-consistent-p
       incoming-nbrs i m-cur imp-st-cur)

      (uncut-incoming-channels-agree-p
       incoming-nbrs i m-cur imp-st-cur before-st-cur))

     (let* ((m-next
             (process-cut-step input imp-st-cur m-cur))
            (imp-st-next
             (system-step imp-st-cur input))
            (before-st-next
             (before-cut-state-from-meta imp-st-start m-next)))

       (uncut-incoming-channels-agree-p
        incoming-nbrs i m-next imp-st-next before-st-next))))

  :hints
  (("Goal"
    :induct
    (uncut-incoming-channels-agree-p
     incoming-nbrs i m-cur imp-st-cur
     (before-cut-state-from-meta imp-st-start m-cur))

    :in-theory
    (disable
     one-uncut-incoming-channel-agrees-p
      one-channel-cut-phase-consistent-p
      good-state-p
      recovery-free-state-p
      good-cut-meta-p
      cut-meta-imp-consistent-p
      legal-inputp
      cl-checkpoint-body-input-p
      process-cut-step
      system-step
      before-imp-state-agree-p
      before-cut-state-from-meta))))




(defthm
  uncut-incoming-channels-agree-p-preserved-by-one-step-history

  (let* ((incoming-nbrs
          (nbrs-from (g i (procs imp-st-cur))))
         (before-st-cur
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

      (incoming-channels-cut-phase-consistent-p
       incoming-nbrs i m-cur imp-st-cur)

      (uncut-incoming-channels-agree-p
       incoming-nbrs i m-cur imp-st-cur before-st-cur))

     (let* ((m-next
             (process-cut-step input imp-st-cur m-cur))
            (imp-st-next
             (system-step imp-st-cur input))
            (before-st-next
             (before-cut-state-from-meta imp-st-start m-next)))

       (uncut-incoming-channels-agree-p
        incoming-nbrs i m-next imp-st-next before-st-next))))

  :hints
  (("Goal"
    :use
    ((:instance
      uncut-incoming-channels-agree-p-preserved-aux
      (incoming-nbrs
       (nbrs-from (g i (procs imp-st-cur))))))

    :in-theory
    (disable
     uncut-incoming-channels-agree-p-preserved-aux
     uncut-incoming-channels-agree-p
     incoming-channels-cut-phase-consistent-p
     good-state-p
     recovery-free-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     legal-inputp
     cl-checkpoint-body-input-p
     process-cut-step
     system-step
     before-imp-state-agree-p
     before-cut-state-from-meta))))





















(defthm cut-process-remains-cut-after-process-cut-step
  (implies
   (not (memberp i (cm-cut-not-taken m)))

   (not
    (memberp
     i
     (cm-cut-not-taken
      (process-cut-step input st m))))))



(defthm run-imp-of-snoc
  (equal
   (run-imp st (snoc inputs input))
   (system-step
    (run-imp st inputs)
    input))
  :hints
  (("Goal"
    :induct (run-imp st inputs)
    :in-theory
     (disable system-step))))



(defthm local-state-of-procs-update-local-state-and-snapshots
  (equal
   (g :local-state
      (g i
         (s k
            (s :snapshots new-snapshots
               (s :local-state new-local-state
                  (g k procs)))
            procs)))

   (if (equal i k)
       new-local-state
     (g :local-state (g i procs))))

  :hints
  (("Goal"
    :cases ((equal i k)))))


(defthm unchanged-field-of-procs-update-local-state-and-snapshots
  (implies
   (and (not (equal field :local-state))
        (not (equal field :snapshots)))

   (equal
    (g field
       (g i
          (s k
             (s :snapshots new-snapshots
                (s :local-state new-local-state
                   (g k procs)))
             procs)))

    (g field (g i procs))))

  :hints
  (("Goal"
    :cases ((equal i k)))))


(defthm unchanged-field-of-procs-update-two-fields
  (implies
   (and (not (equal field field-1))
        (not (equal field field-2)))

   (equal
    (g field
       (g i
          (s k
             (s field-1 value-1
                (s field-2 value-2
                   (g k procs)))
             procs)))

    (g field (g i procs))))

  :hints
  (("Goal"
    :cases ((equal i k)))))


(defthm snapshot-ids-of-procs-update-snapshots-and-snapshot-ids
  (equal
   (g :snapshot-ids
      (g i
         (s k
            (s :snapshots new-snapshots
               (s :snapshot-ids new-snapshot-ids
                  (g k procs)))
            procs)))

   (if (equal i k)
       new-snapshot-ids
     (g :snapshot-ids (g i procs))))

  :hints
  (("Goal"
    :cases ((equal i k)))))



(defthm counter-of-procs-update-counter
  (equal
   (g :counter
      (g i
         (s k
            (s :counter new-counter updated-proc)
            procs)))

   (if (equal i k)
       new-counter
     (g :counter (g i procs))))

  :hints
  (("Goal"
    :cases ((equal i k)))))


(defthm field-of-procs-update
  (equal
   (g field
      (g i (s k updated-proc procs)))

   (if (equal i k)
       (g field updated-proc)
     (g field (g i procs))))

  :hints
  (("Goal"
    :cases ((equal i k)))))



(defthm
  one-uncut-process-agrees-p-preserved-by-one-step-history

  (let ((before-st-cur
         (before-cut-state-from-meta
          imp-st-start m-cur)))

    (implies
     (and
      (good-state-p imp-st-cur)
      (good-state-p before-st-cur)

      (recovery-free-state-p imp-st-cur)
      (recovery-free-state-p before-st-cur)

      (cl-checkpoint-body-input-p input)
      (legal-inputp imp-st-cur input)

      (good-cut-meta-p m-cur)
      (cut-meta-imp-consistent-p
       m-cur imp-st-cur)

      (memberp i (proc-ids imp-st-cur))
      (one-uncut-process-agrees-p
        i m-cur imp-st-cur before-st-cur)
      (before-imp-state-agree-p
       m-cur imp-st-cur before-st-cur)

      )

     (let* ((m-next
             (process-cut-step
              input imp-st-cur m-cur))

            (imp-st-next
             (system-step imp-st-cur input))

            (before-st-next
             (before-cut-state-from-meta
              imp-st-start m-next)))

       (one-uncut-process-agrees-p
        i m-next imp-st-next before-st-next))))

  :hints
  (
   ("Goal"
     :use
     ((:instance  snapshot-ids-equal-when-before-imp-state-agree-and-process-uncut
		  (ids (proc-ids imp-st-cur))
		  (m m-cur)
		  (imp-st imp-st-cur)
		  (before-st
		   (run-imp imp-st-start
			    (g :before-cut-input-sequence m-cur)))
		  (i i))

      (:instance nbrs-to-equal-of-uncut-process
		 (ids (proc-ids imp-st-cur))
		 (m m-cur)
		 (imp-st imp-st-cur)
		 (before-st
		  (run-imp imp-st-start
			   (g :before-cut-input-sequence m-cur)))
		 (k i))
     (:instance local-state-equal-of-uncut-process
		(ids (proc-ids imp-st-cur))
		(m m-cur)
		(imp-st imp-st-cur)
		(before-st
		 (run-imp imp-st-start
			  (g :before-cut-input-sequence m-cur)))
		(k i)))
     
    :do-not-induct t
    :in-theory
    (disable
     good-state-p
      recovery-free-state-p
      good-cut-meta-p
      cut-meta-imp-consistent-p
      before-imp-state-agree-aux-p
      uncut-incoming-channels-agree-p
      one-uncut-incoming-channel-agrees-p
     ; proc-equivalent-p
     ; system-step
     ; process-cut-step
     ; cl-checkpoint-control-view
      cm-cut-not-taken
      BEFORE-IMP-STATE-AGREE-AUX-P-IMPLIES-ONE-UNCUT-PROCESS-AGREES-P))))





(defthm
  before-imp-state-agree-aux-p-preserved-by-one-step-history

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

      (subset ids (proc-ids imp-st-cur))

      ;; Retain the complete agreement for the pointwise lemmas.
      (before-imp-state-agree-p
       m-cur imp-st-cur before-st-cur)

      ;; Relations restricted to the induction list.
      (processes-channel-cut-phase-consistent-p
       ids m-cur imp-st-cur)

      (before-imp-state-agree-aux-p
       ids m-cur imp-st-cur before-st-cur))

     (let* ((m-next
             (process-cut-step input imp-st-cur m-cur))
            (imp-st-next
             (system-step imp-st-cur input))
            (before-st-next
             (before-cut-state-from-meta imp-st-start m-next)))

       (before-imp-state-agree-aux-p
        ids m-next imp-st-next before-st-next))))

  :hints
  (("Goal"
    :induct
    (before-imp-state-agree-aux-p
     ids m-cur imp-st-cur
     (before-cut-state-from-meta imp-st-start m-cur))

    :in-theory
    (disable
     one-uncut-process-agrees-p
      uncut-incoming-channels-agree-p
      incoming-channels-cut-phase-consistent-p
      before-imp-state-agree-p
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
  before-imp-state-agree-p-preserved-by-one-step-history

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

      (all-processes-channel-cut-phase-consistent-p
       m-cur imp-st-cur))

     (let* ((m-next
             (process-cut-step input imp-st-cur m-cur))
            (imp-st-next
             (system-step imp-st-cur input))
            (before-st-next
             (before-cut-state-from-meta imp-st-start m-next)))

       (before-imp-state-agree-p
        m-next imp-st-next before-st-next))))

  :hints
  (("Goal"
    :do-not-induct t

    :use
    ((:instance
      before-imp-state-agree-aux-p-preserved-by-one-step-history
      (ids (proc-ids imp-st-cur))))

    :in-theory
    (disable
     before-imp-state-agree-aux-p-preserved-by-one-step-history
      before-imp-state-agree-aux-p
      processes-channel-cut-phase-consistent-p
      good-state-p
      recovery-free-state-p
      good-cut-meta-p
      cut-meta-imp-consistent-p
      legal-inputp
      cl-checkpoint-body-input-p
      process-cut-step
      system-step
      run-imp))))
