# Formalizing the Chandy–Lamport Checkpointing Algorithm in ACL2

This repository contains ACL2 scripts for the Chandy–Lamport distributed
checkpointing algorithm. The reordering result is described in the paper
*Formalizing the Chandy–Lamport Distributed Snapshot Reordering Theorem in
ACL2* by Mohammad Bin Monjil and Sandip Ray, submitted to the ACL2 Workshop
2026.

**The paper presents the reordering result. The snapshot-correspondence
proof and the checkpoint/recovery support described below are later work.**

## Reordering proof and supporting books

The reordering proof shows that before-cut inputs can be moved before
after-cut inputs while preserving state equivalence. It proceeds from a
local swap theorem to a global reordering theorem using an inversion-count
measure.

| File | Description |
| --- | --- |
| `model.lisp` | Contains the distributed system model: processes, FIFO channels, normal computation, checkpointing, crash and recovery actions, implementation and specification transitions, and execution functions. |
| `scan.lisp` | Defines the cut metadata and the scan that updates it alongside the implementation execution. The metadata tracks the target snapshot ID, processes that have not taken their cuts, pending markers, and before-cut and after-cut input sequences. |
| `basic.lisp` | Contains primitive list-processing lemmas and basic model properties, including preservation of process IDs and process topology. |
| `good_state_inv.lisp` | Defines structural well-formedness of implementation states, processes, channels, and snapshot records. Proves preservation under legal system transitions for all input types and under legal input sequences. |
| `channel_equivalence.lisp` | Defines equivalence between implementation and specification channels after removing protocol messages. Contains supporting channel and process equivalence lemmas. |
| `cut_meta_inv.lisp` | Defines structural well-formedness of cut metadata, consistency between the metadata and implementation state, and `cut-markers-in-transit-p`. Proves preservation under the corresponding metadata and implementation updates. |
| `recovery_inv.lisp` | Defines `recovery-free-state-p` and the allowable checkpoint-body inputs. Proves preservation of recovery freedom under legal checkpoint-body transitions and input sequences. |
| `local_swap.lisp` | Defines the checkpoint-start-to-completion segment predicate and the conditions for swapping two inputs. Proves the local swap theorem and supporting results for legality and state equivalence. |
| `global_reorder.lisp` | Defines the reordering procedure and its inversion-count measure. Proves the global reordering theorem and connects it to complete checkpoint segments. |

## Later work: snapshot correspondence

The snapshot-correspondence proof shows that, at the end of a complete
checkpoint segment, the recorded local states and channel messages match
the corresponding local states and normal channel messages obtained by
executing the segment's before-cut inputs. Together with the reordering
theorem, this identifies the recorded snapshot with the state at the
boundary between before-cut and after-cut inputs in the reordered execution.

| File | Description |
| --- | --- |
| `snap_ch_inv_one_step.lisp` | Defines the channel snapshot invariant, before-state agreement, and channel cut-phase consistency. Proves one-step preservation of the channel invariant and lifts it from individual channels to all processes. |
| `snap_ch_inv_preds_one_step.lisp` | Proves one-step preservation of before-state agreement and channel cut-phase consistency, the supporting conditions needed to preserve the channel snapshot invariant through an execution. |
| `snapshot_channel_invariants_multistep.lisp` | Proves preservation of before-state well-formedness and lifts the channel invariant, before-state agreement, and cut-phase consistency results to legal checkpoint-body input sequences using `run-imp` and `process-cut-segment`. |
| `snapshot_local_invariant.lisp` | Defines the local snapshot invariant and proves its preservation under one-step and multistep executions, for individual processes and all processes. |
| `snapshots_correspondence.lisp` | Defines channel and local-state snapshot correspondence. Shows that the invariants imply correspondence at checkpoint completion, establishes the initial invariants for a fresh checkpoint, and proves correspondence at the end of a complete checkpoint segment. |

The channel snapshot invariant states:

```text
normal messages in the before-cut channel
  = append(recorded messages, messages still to be recorded)
```

At checkpoint completion, no messages remain to be recorded, so the
recorded messages equal the before-cut channel's normal messages.

The local snapshot invariant compares a process's before-cut local state
with its current local state before its cut and with its recorded local
state after its cut. Completion ensures that every process has taken its
cut, giving local-state correspondence as well.

The combined segment-level theorem is
`checkpoint-start-end-segment-snapshot-correspondence`. Its conclusions
are also exported separately as:

- `checkpoint-start-end-segment-channel-snapshot-correspondence`
- `checkpoint-start-end-segment-local-snapshot-correspondence`

## Later work: checkpoint/recovery support

These books support reasoning about checkpoint/recovery executions and
specification input generation.

| File | Description |
| --- | --- |
| `spec_input_gen.lisp` | Constructs compressed specification input sequences from implementation executions. Identifies checkpoint/recovery regions, scans checkpoint and recovery progress, generates replay inputs, and stitches the resulting segments into a specification input sequence. |
| `segment_lemmas.lisp` | Defines checkpoint-start-to-recovery-completion segment predicates and supporting invariants. Contains lemmas relating cut scanning, recorded snapshots, and specification replay, including local-state and channel message matching. |

## Assumptions for checkpoint proofs

The reordering and snapshot-preservation proofs use two predicates:

- `cl-checkpoint-body-inputs-p` restricts inputs to `:start-checkpoint`,
  `:receive`, `:normal`, and `:nop`.
- `recovery-free-state-p` requires that no process is recovering and no
  channel contains a recovery message.

Together with input legality, these restrictions ensure that recovery
activity cannot begin during the checkpoint segment. The paper omits these
hypotheses from some displayed reordering events for brevity; the scripts
retain them.

