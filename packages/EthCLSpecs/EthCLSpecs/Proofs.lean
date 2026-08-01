import EthCLSpecs.Proofs.BuilderIndex
import EthCLSpecs.Proofs.GetPtc
import EthCLSpecs.Proofs.InitializePtcWindow
import EthCLSpecs.Proofs.InitiateBuilderExit

/-!
# `EthCLSpecs.Proofs`: consensus-spec theorems (index)

Mathlib-free proofs about `EthCLSpecs` declarations, colocated with the specs
the way `SizzLean.Proofs` is colocated with `SizzLean`: same package, same
build, `bv_decide` / `decide` / `native_decide` over the spec's own types, no
mathlib. A theorem that turns out to need mathlib moves to the standalone
`EthCLProofs` package instead (`docs/SPECS_ARCHITECTURE.md` §11), the
`LeanPoseidonProofs` containment pattern, so mathlib never reaches this
library, the framework, the runner, or the conformance path.

Re-exports:

* `EthCLSpecs.Proofs.BuilderIndex`: the builder-index flag round-trip
  (`isBuilderIndex`, `toBuilderIndex`, `convertBuilderIndexToValidatorIndex`).
* `EthCLSpecs.Proofs.GetPtc`: `getPtc`'s else-branch `ptcWindow` offset bound,
  for the `data.slot + 1 == state.slot` caller (`getPtcElseOffset`,
  `getPtcElseOffset_lt_next_slot`) and the `slot == curSlot` fork-choice replay callers
  (`getPtcElseOffset_lt_same_slot`).
* `EthCLSpecs.Proofs.InitializePtcWindow`: the seeded `ptcWindow`'s two
  regions (`initializePtcWindow`).
* `EthCLSpecs.Proofs.InitiateBuilderExit`: `initiateBuilderExit`'s exact
  in-range / out-of-range `sszGet`-observable effect
  (`initiateBuilderExit_run_inRange`, `initiateBuilderExit_run_outOfRange`),
  the conditional `UInt64` no-wrap bound on the withdrawability-delay sum
  (`epoch_add_minBuilderWithdrawabilityDelay_no_wrap`), and the function-level
  in-range corollary (`initiateBuilderExit_run_inRange_no_wrap`).
-/
