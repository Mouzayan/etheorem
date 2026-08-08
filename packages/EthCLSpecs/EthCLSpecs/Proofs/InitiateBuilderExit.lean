import EthCLSpecs.Gloas.Operations

/-!
# `EthCLSpecs.Proofs.InitiateBuilderExit`: `initiateBuilderExit`'s effect on the builder registry

`initiateBuilderExit_run_eq` is the whole-transition equation (the run equals the
source-level `sszModify` on `builders`). The in-range and out-of-range theorems
project that equation onto the builder registry through `sszGet`.

Postconditions on the registry are stated through `sszGet` (the *observable* read), never
through raw `State` equality. For an out-of-range write, the cached (`TreeBacked`) and
uncached flavours of `State` are only *observationally* equal, not structurally equal, so an
out-of-range run cannot be claimed as `state' = state`.

The out-of-range case is Lean-only behavior with no PySpec counterpart. Although
the pinned Gloas spec uses equivalent indexing syntax, the Python runtime rejects
an out-of-range index where Lean's `[i]!` write is a no-op. Likewise, Python rejects
an overflowing unsigned addition where Lean's `UInt64` addition wraps.

No-wrap for the withdrawability-delay sum is conditional for an arbitrary `[Config]`, and
unconditional for the two shipped Gloas preset/config pairs, with no epoch or slot hypothesis
from the caller.

The sole current caller derives the index from a successful `findIdx?`, so its calls are
expected to be in range. This caller-level fact is not proved in this file.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (HasherTag StateTransitionError)
open EthCLSpecs.Fulu (Preset Config BuilderIndex Epoch)
open EthCLSpecs.Fulu (minimal mainnet minimalConfig mainnetConfig)
open EthCLSpecs.Gloas (initiateBuilderExit State currentEpochOf)
open SizzLean.Repr
open SizzLean.Cache

/-- The concrete transition monad used by the Gloas runner (`Gloas/Interface.lean`). -/
abbrev InitiateBuilderExitRun [Preset] [HasherTag] [Config] :=
  EStateM StateTransitionError State

/-! ## `SSZList` read/write lemmas the `Box`-flavour split below reduces to

Generic facts about `sszModify`'s emitted `xs.set! i v` / `xs[j]!` pair, not specific to
`Builder` or to `initiateBuilderExit`. -/

/-- `SSZList.set!`'s size preservation. -/
private theorem sszList_size_set! {α : Type} {cap : Nat} :
    ∀ (xs : SSZList α cap) (i : Nat) (v : α), (xs.set! i v).size = xs.size := by
  intro xs i v
  simp [SSZList.size]

/-- The written element reads back exactly the written value, given the write was in range. -/
private theorem sszList_getElem!_set!_self {α : Type} [Inhabited α] {cap : Nat} :
    ∀ (xs : SSZList α cap) (i : Nat) (v : α), i < xs.size → (xs.set! i v)[i]! = v := by
  intro xs i v h
  rw [getElem!_pos (dom := fun (xs : SSZList α cap) i => i < xs.size)
    (h := by simpa [sszList_size_set!] using h)]
  show (xs.set! i v).val[i]'_ = v
  simp

/-- Every element other than the one written is untouched, regardless of whether that other
index `j` is itself in range. -/
private theorem sszList_getElem!_set!_ne {α : Type} [Inhabited α] {cap : Nat} :
    ∀ (xs : SSZList α cap) (i j : Nat) (v : α), i ≠ j → (xs.set! i v)[j]! = xs[j]! := by
  intro xs i j v hij
  by_cases hj : j < xs.size
  · rw [getElem!_pos (dom := fun (xs : SSZList α cap) i => i < xs.size)
          (h := by simpa [sszList_size_set!] using hj),
        getElem!_pos (dom := fun (xs : SSZList α cap) i => i < xs.size) (h := hj)]
    show (xs.set! i v).val[j]'_ = xs.val[j]'_
    exact Array.getElem_setIfInBounds_ne hj hij
  · rw [getElem!_neg (dom := fun (xs : SSZList α cap) i => i < xs.size)
          (h := by simpa [sszList_size_set!] using hj),
        getElem!_neg (dom := fun (xs : SSZList α cap) i => i < xs.size) (h := hj)]

/-- Out of range, the write is a no-op on the *whole* list, not merely at the target index: no
`[j]!` read at any `j` can tell the pre- and post-write lists apart, which is what
`initiateBuilderExit_run_outOfRange` needs. -/
private theorem sszList_set!_eq_of_out_of_range {α : Type} {cap : Nat} :
    ∀ (xs : SSZList α cap) (i : Nat) (v : α), ¬ i < xs.size → xs.set! i v = xs := by
  intro xs i v hi
  apply Subtype.ext
  exact Array.setIfInBounds_eq_of_size_le
    (by simpa [SSZList.size] using Nat.le_of_not_lt hi)

/-! ## The concrete-run theorems

`initiateBuilderExit_run_eq` is the whole-transition equation: the run equals `.ok ()` of the
source-level `sszModify` on `builders`. The in-range and out-of-range theorems are convenient
`sszGet` characterizations of that same result. `sszGet` on the post-state still needs the
cached/uncached `Box` split; both branches close by the same list lemmas. -/

/-- Exact whole-transition equation for `initiateBuilderExit`. The returned state
is the original state with only `builders[builderIndex.toNat]!` updated through
`sszModify`; every other top-level field is carried through. For an out-of-range
index the underlying list write is a no-op, although the cached representation
need not be structurally identical to the pre-state. -/
theorem initiateBuilderExit_run_eq [Preset] [HasherTag] [Config] :
    ∀ (state : State) (builderIndex : BuilderIndex),
      (initiateBuilderExit (StateTransition := InitiateBuilderExitRun) builderIndex).run state =
        .ok () (sszModify state builders[builderIndex.toNat]! as b =>
          { b with withdrawableEpoch :=
              currentEpochOf state + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay }) := by
  intro state builderIndex
  rfl

/-- **In range.** Running `initiateBuilderExit builderIndex` never rejects, and the exact effect
on the builder registry is: `builders[builderIndex.toNat]!.withdrawableEpoch` becomes
`currentEpochOf` read from the *pre*-state (the `do`-block's `← get` runs before the write) plus
`MIN_BUILDER_WITHDRAWABILITY_DELAY`, every other builder is unchanged, and the registry's
`.size` is unchanged. This does not characterize any other top-level `BeaconState` field. -/
theorem initiateBuilderExit_run_inRange [Preset] [HasherTag] [Config] :
    ∀ (state : State) (builderIndex : BuilderIndex),
      builderIndex.toNat < (sszGet state builders).size →
      ∃ state' : State,
        (initiateBuilderExit (StateTransition := InitiateBuilderExitRun) builderIndex).run state = .ok () state'
        ∧ sszGet state' builders[builderIndex.toNat]!
            = { sszGet state builders[builderIndex.toNat]! with
                withdrawableEpoch :=
                  currentEpochOf state + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay }
        ∧ (∀ j : Nat, j ≠ builderIndex.toNat →
              sszGet state' builders[j]! = sszGet state builders[j]!)
        ∧ (sszGet state' builders).size = (sszGet state builders).size := by
  intro state builderIndex hidx
  refine ⟨_, initiateBuilderExit_run_eq state builderIndex, ?_⟩
  rcases state with t | t <;>
    dsimp only [SSZ.Box.view, TreeBacked.addPendingMany] at hidx ⊢ <;>
    refine ⟨sszList_getElem!_set!_self _ _ _ hidx,
      fun j hj => sszList_getElem!_set!_ne _ _ _ _ (Ne.symm hj),
      sszList_size_set! _ _ _⟩

/-- **Out of range.** Running `initiateBuilderExit builderIndex` still never rejects (`[i]!` is
total), and now *every* `sszGet`-observable read of `builders`, at any index, agrees between the
pre- and post-state (`sszList_set!_eq_of_out_of_range`): the write is a genuine no-op at the
`SSZList` level, not merely at the written index. This is deliberately **not** stated as
`state' = state`, which is false for the cached flavour; see the module docstring. This case is
not expected to be exercised by the current caller `processBuilderExitRequest`; the caller-level
in-range fact is not proved in this file. -/
theorem initiateBuilderExit_run_outOfRange [Preset] [HasherTag] [Config] :
    ∀ (state : State) (builderIndex : BuilderIndex),
      ¬ builderIndex.toNat < (sszGet state builders).size →
      ∃ state' : State,
        (initiateBuilderExit (StateTransition := InitiateBuilderExitRun) builderIndex).run state = .ok () state'
        ∧ (∀ j : Nat, sszGet state' builders[j]! = sszGet state builders[j]!)
        ∧ (sszGet state' builders).size = (sszGet state builders).size := by
  intro state builderIndex hidx
  refine ⟨_, initiateBuilderExit_run_eq state builderIndex, fun j => ?_, ?_⟩ <;>
    rcases state with t | t <;>
    dsimp only [SSZ.Box.view, TreeBacked.addPendingMany] at hidx ⊢ <;>
    rw [sszList_set!_eq_of_out_of_range _ _ _ hidx]

/-! ## Generic conditional no-overflow

`Epoch` is an alias for `UInt64`, so `epoch + Const.minBuilderWithdrawabilityDelay` is
`UInt64` addition, mod `2 ^ 64`. No generic invariant relates the bounded `UInt64` current epoch
to the independently configurable withdrawal delay (a `[Config]` instance is free to set
`minBuilderWithdrawabilityDelay` arbitrarily), so the no-wrap fact is necessarily
**conditional**: the condition is a hypothesis a caller must otherwise establish (e.g. from a
slot/epoch bound on `mainnet`), not a run-time guard the function enforces itself. -/

/-- Core Lean's `UInt64.toNat_add` gives `(a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64`
unconditionally; under the stated bound, `Nat.mod_eq_of_lt` drops the `%` and the `UInt64` sum's
`.toNat` is exactly the `Nat` sum, no wraparound. -/
theorem epoch_add_minBuilderWithdrawabilityDelay_no_wrap [Config] {epoch : Epoch} :
    epoch.toNat + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay.toNat < 2 ^ 64 →
      (epoch + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay).toNat
        = epoch.toNat + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay.toNat := by
  intro h
  simp [UInt64.toNat_add, Nat.mod_eq_of_lt h]

/-- **Function-level corollary.** Chaining `initiateBuilderExit_run_inRange`'s written-field
equation with `epoch_add_minBuilderWithdrawabilityDelay_no_wrap`: under the epoch-bound
hypothesis (read from the *pre*-state's `currentEpochOf`, as in the unconditional in-range
theorem), the post-state builder's `withdrawableEpoch.toNat` is exactly the natural-number sum
`currentEpochOf(pre-state).toNat + MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat`, not a value that has
silently wrapped through `2 ^ 64`. -/
theorem initiateBuilderExit_run_inRange_no_wrap [Preset] [HasherTag] [Config] :
    ∀ (state : State) (builderIndex : BuilderIndex),
      builderIndex.toNat < (sszGet state builders).size →
      (currentEpochOf state).toNat
          + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay.toNat < 2 ^ 64 →
      ∃ state' : State,
        (initiateBuilderExit (StateTransition := InitiateBuilderExitRun) builderIndex).run state = .ok () state'
        ∧ (sszGet state' builders[builderIndex.toNat]!).withdrawableEpoch.toNat
            = (currentEpochOf state).toNat
              + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay.toNat := by
  intro state builderIndex hidx hbound
  obtain ⟨state', hrun, hview, -, -⟩ := initiateBuilderExit_run_inRange state builderIndex hidx
  exact ⟨state', hrun, by rw [hview]; exact epoch_add_minBuilderWithdrawabilityDelay_no_wrap hbound⟩

/-! ## Shipped preset/config pairs: unconditional

`initiateBuilderExit_run_inRange_no_wrap`'s `hbound` premise is conditional because a `[Config]`
instance is free, in general, to pick `minBuilderWithdrawabilityDelay` large enough to make
`currentEpochOf state + minBuilderWithdrawabilityDelay` overflow `2 ^ 64`. The two pairs the
repository actually ships (the minimal and mainnet preset/config pairs used by the shipped
Gloas interfaces) don't: `slotsPerEpoch` bounds `currentEpochOf state` well below `2 ^ 64` for
*any* `state.slot : UInt64`, so the sum with the concrete `minBuilderWithdrawabilityDelay` (`2`
on minimal, `8192` on mainnet) can never reach `2 ^ 64`.
Each corollary below discharges `hbound` from that arithmetic fact alone, no epoch or slot
hypothesis from the caller, and reuses `initiateBuilderExit_run_inRange_no_wrap` rather than
re-deriving the state transition. -/

/-- **Minimal preset/config (`minimal`, `minimalConfig`), unconditional.** `slotsPerEpoch = 8`,
`minBuilderWithdrawabilityDelay = 2`: `currentEpochOf state ≤ (2 ^ 64 - 1) / 8`, so the sum with
`2` is nowhere near `2 ^ 64`, for every `state`. -/
theorem initiateBuilderExit_run_inRange_no_wrap_minimal [HasherTag] :
    letI : Preset := minimal
    letI : Config := minimalConfig
    ∀ (state : State) (builderIndex : BuilderIndex),
      builderIndex.toNat < (sszGet state builders).size →
      ∃ state' : State,
        (initiateBuilderExit (StateTransition := InitiateBuilderExitRun) builderIndex).run state = .ok () state'
        ∧ (sszGet state' builders[builderIndex.toNat]!).withdrawableEpoch.toNat
            = (currentEpochOf state).toNat + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay.toNat := by
  letI : Preset := minimal
  letI : Config := minimalConfig
  intro state builderIndex hidx
  refine @initiateBuilderExit_run_inRange_no_wrap minimal _ minimalConfig state builderIndex hidx ?_
  have hslot := UInt64.toNat_lt (sszGet state slot)
  have hspe : (@Preset.slotsPerEpoch minimal : Nat) = 8 := rfl
  have hdelay : (@Config.minBuilderWithdrawabilityDelay minimalConfig).toNat = 2 := rfl
  simp only [currentEpochOf, EthCLSpecs.Gloas.computeEpochAtSlot,
    EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay, EthCLSpecs.Fulu.Const.slotsPerEpoch,
    UInt64.toNat_div, UInt64.toNat_ofNat', hspe, hdelay, Nat.reducePow, Nat.reduceMod]
  omega

/-- **Mainnet preset/config (`mainnet`, `mainnetConfig`), unconditional.** `slotsPerEpoch = 32`,
`minBuilderWithdrawabilityDelay = 8192`: `currentEpochOf state ≤ (2 ^ 64 - 1) / 32`, so the sum
with `8192` is nowhere near `2 ^ 64`, for every `state`. -/
theorem initiateBuilderExit_run_inRange_no_wrap_mainnet [HasherTag] :
    letI : Preset := mainnet
    letI : Config := mainnetConfig
    ∀ (state : State) (builderIndex : BuilderIndex),
      builderIndex.toNat < (sszGet state builders).size →
      ∃ state' : State,
        (initiateBuilderExit (StateTransition := InitiateBuilderExitRun) builderIndex).run state = .ok () state'
        ∧ (sszGet state' builders[builderIndex.toNat]!).withdrawableEpoch.toNat
            = (currentEpochOf state).toNat + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay.toNat := by
  letI : Preset := mainnet
  letI : Config := mainnetConfig
  intro state builderIndex hidx
  refine @initiateBuilderExit_run_inRange_no_wrap mainnet _ mainnetConfig state builderIndex hidx ?_
  have hslot := UInt64.toNat_lt (sszGet state slot)
  have hspe : (@Preset.slotsPerEpoch mainnet : Nat) = 32 := rfl
  have hdelay : (@Config.minBuilderWithdrawabilityDelay mainnetConfig).toNat = 8192 := rfl
  simp only [currentEpochOf, EthCLSpecs.Gloas.computeEpochAtSlot,
    EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay, EthCLSpecs.Fulu.Const.slotsPerEpoch,
    UInt64.toNat_div, UInt64.toNat_ofNat', hspe, hdelay, Nat.reducePow, Nat.reduceMod]
  omega

end EthCLSpecs.Proofs
