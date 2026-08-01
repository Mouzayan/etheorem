import EthCLSpecs.Gloas.Operations

/-!
# `EthCLSpecs.Proofs.InitiateBuilderExit`: `initiateBuilderExit`'s exact effect on the builder registry

`EthCLSpecs.Gloas.initiateBuilderExit` (`Gloas/Operations.lean`) is the EIP-8282
builder-exit mutator, called only from `processBuilderExitRequest`:

```
forkdef initiateBuilderExit (builderIndex : BuilderIndex) : StateTransition Unit := do
  let epoch := currentEpochOf (← get)
  modifyState fun state =>
    sszModify state builders[builderIndex.toNat]! as b =>
      { b with withdrawableEpoch := epoch + Const.minBuilderWithdrawabilityDelay }
```

It writes `builders[builderIndex.toNat]!.withdrawableEpoch`, through the infallible `[i]!`
index, to `currentEpochOf(pre-state) + MIN_BUILDER_WITHDRAWABILITY_DELAY`. Unlike
its validator-side sibling `initiateValidatorExit` (`Fulu/RegistryUpdates.lean`), it carries
no `assert` against `UInt64` overflow on that sum, so the sum silently wraps whenever it
would exceed `2 ^ 64 - 1`; see `epoch_add_minBuilderWithdrawabilityDelay_no_wrap` below for the
conditional (not unconditional) bound that rules the wrap out.

Every theorem here runs the concrete `EStateM StateTransitionError State` (`Run`), the monad
the fork's runner (`Gloas/Interface.lean`) actually instantiates `StateTransition` to, not the
`docs/SPECS_ARCHITECTURE.md`-aspirational pure `StateT`/`UncachedBox` pairing (that
configuration does not exist in the codebase yet). Postconditions are stated through `sszGet`
(the *observable* read), never through raw `State` equality: for an out-of-range write, the
cached (`TreeBacked`) and uncached flavours of `State` are only *observationally* equal, not
structurally equal, so `initiateBuilderExit_run_outOfRange` is phrased through `sszGet`, not
through a claimed `state' = state`.

The out-of-range case (`initiateBuilderExit_run_outOfRange`) is a Lean-only behavior with no
pyspec counterpart. The pinned Gloas spec (`initiate_builder_exit`,
`specs/gloas/beacon-chain.md`) indexes with the same `state.builders[builder_index]`
expression, but `remerkleable`'s `List.get`/`List.set` (`remerkleable/complex.py`, pinned
`eth-remerkleable` v0.1.31) raise `IndexError` on an out-of-range index, and the sum on the
following line raises on `UInt64` overflow the same way (see `epoch_add_…_no_wrap` above): both
are invalid transitions upstream, not silent no-ops. `initiateBuilderExit`'s only caller,
`processBuilderExitRequest`, only ever calls it with `builderIndex` derived from a successful
`findIdx?` over `state.builders` itself, so it is always in range in practice; the out-of-range
theorem characterizes Lean's `[i]!` total-indexing behavior on an input the real caller never
produces, not a divergence that can be triggered from a valid block.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec
open EthCLSpecs.Fulu (Preset Config BuilderIndex Epoch)
open EthCLSpecs.Gloas (initiateBuilderExit State currentEpochOf)

/-- `initiateBuilderExit` runs in the concrete transition monad used by the runner (`Gloas/Interface.lean`)
abstracted only over `[HasherTag]` (so this does not commit to `FastBox` vs `UncachedSSZ`, both
of which `HasherTag.H`-generic code can still be instantiated against). -/
abbrev Run [Preset] [HasherTag] [Config] :=
  EStateM StateTransitionError (State)

/-! ## `SSZList` read/write lemmas the `Box`-flavour split below reduces to

Generic facts about `sszModify`'s emitted `xs.set! i v` / `xs[j]!` pair, not specific to
`Builder` or to `initiateBuilderExit`. -/

/-- `SSZList.set!`'s size preservation. -/
private theorem sszList_size_set! {α : Type} {cap : Nat}
    (xs : SizzLean.Repr.SSZList α cap) (i : Nat) (v : α) :
    (xs.set! i v).size = xs.size := by
  simp [SizzLean.Repr.SSZList.size]

/-- The written element reads back exactly the written value, given the write was in range. -/
private theorem sszList_getElem!_set!_self {α : Type} [Inhabited α] {cap : Nat}
    (xs : SizzLean.Repr.SSZList α cap) (i : Nat) (v : α) (h : i < xs.size) :
    (xs.set! i v)[i]! = v := by
  rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.SSZList α cap) i => i < xs.size)
    (h := by simpa [sszList_size_set!] using h)]
  show (xs.set! i v).val[i]'_ = v
  simp

/-- Every element other than the one written is untouched, regardless of whether that other
index `j` is itself in range. -/
private theorem sszList_getElem!_set!_ne {α : Type} [Inhabited α] {cap : Nat}
    (xs : SizzLean.Repr.SSZList α cap) (i j : Nat) (v : α) (hij : i ≠ j) :
    (xs.set! i v)[j]! = xs[j]! := by
  by_cases hj : j < xs.size
  · rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.SSZList α cap) i => i < xs.size)
          (h := by simpa [sszList_size_set!] using hj),
        getElem!_pos (dom := fun (xs : SizzLean.Repr.SSZList α cap) i => i < xs.size) (h := hj)]
    show (xs.set! i v).val[j]'_ = xs.val[j]'_
    exact Array.getElem_setIfInBounds_ne hj hij
  · rw [getElem!_neg (dom := fun (xs : SizzLean.Repr.SSZList α cap) i => i < xs.size)
          (h := by simpa [sszList_size_set!] using hj),
        getElem!_neg (dom := fun (xs : SizzLean.Repr.SSZList α cap) i => i < xs.size) (h := hj)]

/-- Out of range, the write is a no-op on the *whole* list, not merely at the target index: no
`[j]!` read at any `j` can tell the pre- and post-write lists apart. This is strictly stronger
than "the `.view` field is unaffected", and is what `initiateBuilderExit_run_outOfRange` needs. -/
private theorem sszList_set!_eq_of_out_of_range {α : Type} {cap : Nat}
    (xs : SizzLean.Repr.SSZList α cap) (i : Nat) (v : α) (hi : ¬ i < xs.size) :
    xs.set! i v = xs := by
  apply Subtype.ext
  exact Array.setIfInBounds_eq_of_size_le
    (by simpa [SizzLean.Repr.SSZList.size] using Nat.le_of_not_lt hi)

/-! ## The concrete-run theorem

Both directions unfold `initiateBuilderExit` down to `EStateM`'s bare `Result.ok () state'` by
`rfl` (nothing in the `do`-block is opaque). `sszGet`'s read on the resulting `state'` is not
itself reducible by `rfl`, since it pattern-matches on `state`'s cached/uncached constructor;
`rcases state with t | t` splits on that, and both branches close by the same tactic. -/

/-- **In range.** Running `initiateBuilderExit builderIndex` never rejects, and the exact effect
on the builder registry is: `builders[builderIndex.toNat]!.withdrawableEpoch` becomes
`currentEpochOf` read from the *pre*-state (the `do`-block's `← get` runs before the write) plus
`MIN_BUILDER_WITHDRAWABILITY_DELAY`, every other builder is unchanged, and the registry's
`.size` is unchanged. This does not characterize any other top-level `BeaconState` field. -/
theorem initiateBuilderExit_run_inRange [Preset] [HasherTag] [Config]
    (state : State) (builderIndex : BuilderIndex)
    (hidx : builderIndex.toNat < (sszGet state builders).size) :
    ∃ state' : State,
      (initiateBuilderExit (StateTransition := Run) builderIndex).run state = .ok () state'
      ∧ sszGet state' builders[builderIndex.toNat]!
          = { sszGet state builders[builderIndex.toNat]! with
              withdrawableEpoch := currentEpochOf state + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay }
      ∧ (∀ j : Nat, j ≠ builderIndex.toNat → sszGet state' builders[j]! = sszGet state builders[j]!)
      ∧ (sszGet state' builders).size = (sszGet state builders).size := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rcases state with t | t <;>
      dsimp only [SizzLean.Cache.SSZ.Box.view, SizzLean.Cache.TreeBacked.addPendingMany] at hidx ⊢ <;>
      exact sszList_getElem!_set!_self _ _ _ hidx
  · intro j hj
    rcases state with t | t <;>
      dsimp only [SizzLean.Cache.SSZ.Box.view, SizzLean.Cache.TreeBacked.addPendingMany] at hidx ⊢ <;>
      exact sszList_getElem!_set!_ne _ _ _ _ (Ne.symm hj)
  · rcases state with t | t <;>
      dsimp only [SizzLean.Cache.SSZ.Box.view, SizzLean.Cache.TreeBacked.addPendingMany] at hidx ⊢ <;>
      exact sszList_size_set! _ _ _

/-- **Out of range.** Running `initiateBuilderExit builderIndex` still never rejects (`[i]!` is
total), and now *every* `sszGet`-observable read of `builders`, at any index, agrees between the
pre- and post-state (`sszList_set!_eq_of_out_of_range`): the write is a genuine no-op at the
`SSZList` level, not merely at the written index. This is deliberately **not** stated as
`state' = state`, which is false for the cached flavour; see the module docstring. This case has
no pyspec counterpart (the pinned spec raises `IndexError` here instead) and is never exercised
by the real caller `processBuilderExitRequest`; see the module docstring. -/
theorem initiateBuilderExit_run_outOfRange [Preset] [HasherTag] [Config]
    (state : State) (builderIndex : BuilderIndex)
    (hidx : ¬ builderIndex.toNat < (sszGet state builders).size) :
    ∃ state' : State,
      (initiateBuilderExit (StateTransition := Run) builderIndex).run state = .ok () state'
      ∧ (∀ j : Nat, sszGet state' builders[j]! = sszGet state builders[j]!)
      ∧ (sszGet state' builders).size = (sszGet state builders).size := by
  refine ⟨_, rfl, fun j => ?_, ?_⟩ <;>
    rcases state with t | t <;>
    dsimp only [SizzLean.Cache.SSZ.Box.view, SizzLean.Cache.TreeBacked.addPendingMany] at hidx ⊢ <;>
    rw [sszList_set!_eq_of_out_of_range _ _ _ hidx]

/-! ## No-overflow: conditional, matching `initiateValidatorExit`'s own `assert` shape

`Epoch` is `UInt64` (`Fulu/Types.lean`), so `epoch + Const.minBuilderWithdrawabilityDelay` is
`UInt64` addition, mod `2 ^ 64`. No generic invariant relates the bounded `UInt64` current epoch
to the independently configurable withdrawal delay (a `[Config]` instance is free to set
`minBuilderWithdrawabilityDelay` arbitrarily), so the no-wrap fact is necessarily
**conditional**, exactly the shape
`initiateValidatorExit`'s own `assert (exitEpoch.toNat + Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64)`
takes for the validator side; `initiateBuilderExit` carries no such `assert`, so the condition
is a hypothesis a caller must otherwise establish (e.g. from a slot/epoch bound on `mainnet`),
not a run-time guard the function enforces itself. -/

/-- Core Lean's `UInt64.toNat_add` gives `(a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64`
unconditionally; under the stated bound, `Nat.mod_eq_of_lt` drops the `%` and the `UInt64` sum's
`.toNat` is exactly the `Nat` sum, no wraparound. -/
theorem epoch_add_minBuilderWithdrawabilityDelay_no_wrap [Config] {epoch : Epoch}
    (h : epoch.toNat + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay.toNat < 2 ^ 64) :
    (epoch + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay).toNat
      = epoch.toNat + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay.toNat := by
  simp [UInt64.toNat_add, Nat.mod_eq_of_lt h]

/-- **Function-level corollary.** Chaining `initiateBuilderExit_run_inRange`'s written-field
equation with `epoch_add_minBuilderWithdrawabilityDelay_no_wrap`: under the epoch-bound
hypothesis (read from the *pre*-state's `currentEpochOf`, as in the unconditional in-range
theorem), the post-state builder's `withdrawableEpoch.toNat` is exactly the natural-number sum
`currentEpochOf(pre-state).toNat + MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat`, not a value that has
silently wrapped through `2 ^ 64`. -/
theorem initiateBuilderExit_run_inRange_no_wrap [Preset] [HasherTag] [Config]
    (state : State) (builderIndex : BuilderIndex)
    (hidx : builderIndex.toNat < (sszGet state builders).size)
    (hbound : (currentEpochOf state).toNat
      + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay.toNat < 2 ^ 64) :
    ∃ state' : State,
      (initiateBuilderExit (StateTransition := Run) builderIndex).run state = .ok () state'
      ∧ (sszGet state' builders[builderIndex.toNat]!).withdrawableEpoch.toNat
          = (currentEpochOf state).toNat + EthCLSpecs.Fulu.Const.minBuilderWithdrawabilityDelay.toNat := by
  obtain ⟨state', hrun, hview, -, -⟩ := initiateBuilderExit_run_inRange state builderIndex hidx
  exact ⟨state', hrun, by rw [hview]; exact epoch_add_minBuilderWithdrawabilityDelay_no_wrap hbound⟩

end EthCLSpecs.Proofs
