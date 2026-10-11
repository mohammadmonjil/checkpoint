(in-package "ACL2")
(include-book "snapshots_correspondence")


(defthm imp-spec-equivalent-p-preserved-by-one-step
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)
    (recovery-free-state-p imp-st)
    (cl-checkpoint-body-input-p input)
    (legal-inputp imp-st input))
   (imp-spec-equivalent-p
    (system-step imp-st input)
    (spec-step
     spec-st
     (spec-compatible-input input imp-st)))))
