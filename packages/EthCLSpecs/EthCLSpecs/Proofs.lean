import EthCLSpecs.Proofs.BuilderIndex
import EthCLSpecs.Proofs.BuilderPendingPayments
import EthCLSpecs.Proofs.GetPtc
import EthCLSpecs.Proofs.InitializePtcWindow
import EthCLSpecs.Proofs.InitiateBuilderExit
import EthCLSpecs.Proofs.UpdateCheckpoints

/-!
# `EthCLSpecs.Proofs`: consensus-spec theorems (index)

Mathlib-free proofs about `EthCLSpecs` declarations, colocated with the specs
the way `SizzLean.Proofs` is colocated with `SizzLean`: same package, same
build. Each theorem is closed by whichever tactic its goal needs, `bv_decide`,
`decide`, `native_decide`, or plain case analysis. Always over the spec's own
types, never mathlib. A theorem that turns out to need mathlib moves to the standalone
`EthCLProofs` package instead (`docs/SPECS_ARCHITECTURE.md` §11), following the
`LeanPoseidonProofs` containment pattern. Mathlib never reaches this library,
the framework, the runner, or the conformance path.

Re-exports:

* `EthCLSpecs.Proofs.BuilderIndex`: the builder-index flag round-trip
  (`isBuilderIndex`, `toBuilderIndex`, `convertBuilderIndexToValidatorIndex`).
* `EthCLSpecs.Proofs.BuilderPendingPayments`: `processBuilderPendingPayments`'s
  withdrawal-queuing and payment-window-shift postcondition
  (`processBuilderPendingPayments_run`, plus
  `processBuilderPendingPayments_run_of_fits`).
* `EthCLSpecs.Proofs.GetPtc`: `getPtc`'s else-branch `ptcWindow` offset bound,
  for the `data.slot + 1 == state.slot` caller (`getPtcElseOffset`,
  `getPtcElseOffset_lt_next_slot`) and the `slot == curSlot` fork-choice replay callers
  (`getPtcElseOffset_lt_same_slot`).
* `EthCLSpecs.Proofs.InitializePtcWindow`: the seeded `ptcWindow`'s two
  regions (`initializePtcWindow`).
* `EthCLSpecs.Proofs.InitiateBuilderExit`: `initiateBuilderExit`'s exact
  in-range / out-of-range effect on the builders registry through `sszGet`
  (`initiateBuilderExit_run_inRange`, `initiateBuilderExit_run_outOfRange`),
  the conditional `UInt64` no-wrap bound on the withdrawability-delay sum
  (`epoch_add_minBuilderWithdrawabilityDelay_no_wrap`) and its function-level
  in-range corollary (`initiateBuilderExit_run_inRange_no_wrap`), and the two
  shipped preset/config pairs on which that bound holds unconditionally, with
  no epoch or slot hypothesis from the caller (`initiateBuilderExit_run_inRange_no_wrap_minimal`,
  `initiateBuilderExit_run_inRange_no_wrap_mainnet`).
* `EthCLSpecs.Proofs.UpdateCheckpoints`: `Gloas.updateCheckpoints` checkpoint
  monotonicity, the justified/finalized epoch never decreases. Its theorems sit
  in `EthCLSpecs.Proofs.Gloas`, since `updateCheckpoints` exists in both forks.
-/
