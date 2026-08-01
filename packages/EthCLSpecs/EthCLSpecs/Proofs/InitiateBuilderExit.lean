import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Fulu.RegistryUpdates

/-!
# `EthCLSpecs.Proofs.InitiateBuilderExit`: `initiateBuilderExit`'s exact effect

`EthCLSpecs.Gloas.initiateBuilderExit` (`Gloas/Operations.lean`) is the EIP-8282
builder-exit mutator, called only from `processBuilderExitRequest`:

```
forkdef initiateBuilderExit (builderIndex : BuilderIndex) : StateTransition Unit := do
  let epoch := currentEpochOf (← get)
  modifyState fun state =>
    sszModify state builders[builderIndex.toNat]! as b =>
      { b with withdrawableEpoch := epoch + Const.minBuilderWithdrawabilityDelay }
```

It writes exactly one field of exactly one builder, through the infallible `[i]!` index:
`withdrawableEpoch := currentEpochOf(pre-state) + MIN_BUILDER_WITHDRAWABILITY_DELAY`. Unlike
its validator-side sibling `initiateValidatorExit` (`Fulu/RegistryUpdates.lean`), it carries
no `assert` against `UInt64` overflow on that sum, so the sum silently wraps whenever it
would exceed `2 ^ 64 - 1`; see `epoch_add_minBuilderWithdrawabilityDelay_no_wrap` below for the
conditional (not unconditional) bound that rules the wrap out.

Every theorem here runs the concrete `EStateM StateTransitionError State` (`Run`), the monad
the fork's runner (`Gloas/Interface.lean`) actually instantiates `StateTransition` to, not the
`docs/SPECS_ARCHITECTURE.md`-aspirational pure `StateT`/`UncachedBox` pairing (that
configuration does not exist in the codebase yet). Postconditions are stated through `sszGet`
(the *observable* read, `.view.path`), never through raw `State` equality: `State` is
`SSZ.Box HasherTag.H BeaconState`, closed over a *cached* (`TreeBacked`) and an *uncached*
(`UncachedSSZ`) flavour, and the two are only *observationally* equal after an out-of-range
`[i]!` write. `SizzLean.Cache.Update`'s `sszUpdate` unconditionally records a `PendingWrite`
closure in the cached flavour's `pending` map even when the index is out of range (the closure
itself checks the bound and resolves to `none`, a commit-time no-op that leaves the Merkle root
unchanged); the `pending` map itself is a strictly new value, so the raw `Box` values differ
even though every `sszGet` read of the two post-states agrees. `initiateBuilderExit_run_outOfRange`
below is phrased accordingly, through `sszGet`, not through a claimed `state' = state`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec
open EthCLSpecs.Fulu (Preset Config BuilderIndex Epoch)
open EthCLSpecs.Gloas (initiateBuilderExit State currentEpochOf)

/-- `initiateBuilderExit` runs at everywhere in the runner (`Gloas/Interface.lean`)
abstracted only over `[HasherTag]` (so this does not commit to `FastBox` vs `UncachedSSZ`, both
of which `HasherTag.H`-generic code can still be instantiated against). -/
abbrev Run [Preset] [HasherTag] [Config] :=
  EStateM StateTransitionError (State)

/-! ## `SSZList` read/write lemmas the `Box`-flavour split below reduces to

None of these are specific to `Builder` or to `initiateBuilderExit`; they are the generic facts
`sszModify`'s emitted `xs.set! i v` / `xs[j]!` pair obeys, on top of core Lean's `Array` lemmas
for `setIfInBounds` (`Array.set!`'s definition) and the *default* `LawfulGetElem` instance that
`Init.GetElem` derives automatically from `SizzLean.Repr`'s `GetElem (SSZList α cap) …` instance
plus `Nat`'s decidable `<` (so `getElem!_pos` / `getElem!_neg`, stated generically for any
`LawfulGetElem`, already apply to `SSZList` with no `SSZList`-specific instance needed). -/

/-- `SSZList.set!`'s size preservation, spelled through `SSZList.size` (`sszUpdate`'s own
size-preservation proof obligation, restated as a usable rewrite rule). -/
private theorem sszList_size_set! {α : Type} {cap : Nat}
    (xs : SizzLean.Repr.SSZList α cap) (i : Nat) (v : α) :
    (xs.set! i v).size = xs.size := by
  simp [SizzLean.Repr.SSZList.size]

/-- The written element reads back exactly the written value, given the write was in range.
`getElem!_pos` first drops the `!` (an infallible read) down to a checked read at the supplied
proof; the remaining `.val[i]'_` goal is `Array.getElem_setIfInBounds_self` under `SSZList`'s
`Subtype` wrapper, which `simp` unwraps via `SSZList.set!`'s definition. -/
private theorem sszList_getElem!_set!_self {α : Type} [Inhabited α] {cap : Nat}
    (xs : SizzLean.Repr.SSZList α cap) (i : Nat) (v : α) (h : i < xs.size) :
    (xs.set! i v)[i]! = v := by
  rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.SSZList α cap) i => i < xs.size)
    (h := by simpa [sszList_size_set!] using h)]
  show (xs.set! i v).val[i]'_ = v
  simp

/-- Every element other than the one written is untouched, unconditionally on whether that
other index `j` is itself in range: in range, `Array.getElem_setIfInBounds_ne` distinguishes it
from the write at `i`; out of range, both sides are `getElem!_neg`'s `default` (same `.size` on
both sides, via `sszList_size_set!`). -/
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

/-- Out of range, `Array.set!`'s clamping (`setIfInBounds`) is a no-op on the *whole* list, not
merely at the target index: no `[j]!` read at any `j` (in range or not) can tell the pre- and
post-write lists apart. This is the fact `initiateBuilderExit_run_outOfRange` needs; it is
strictly stronger than "the `.view` field is unaffected" (`SSZList` equality, not just
per-element reads), even though the ambient `Box` itself is *not* a no-op in the cached
flavour (see the module docstring's `pending`-map note). -/
private theorem sszList_set!_eq_of_out_of_range {α : Type} {cap : Nat}
    (xs : SizzLean.Repr.SSZList α cap) (i : Nat) (v : α) (hi : ¬ i < xs.size) :
    xs.set! i v = xs := by
  apply Subtype.ext
  exact Array.setIfInBounds_eq_of_size_le
    (by simpa [SizzLean.Repr.SSZList.size] using Nat.le_of_not_lt hi)

/-! ## The concrete-run theorem

Both directions unfold `initiateBuilderExit` down to `EStateM`'s bare `Result.ok () state'` by
`rfl`: `get`, `modifyState` (`= modifyThe State`), and every layer of `MonadStateOf` /
`MonadState` between them are `@[inline]` / `abbrev` all the way to `EStateM.get` /
`EStateM.modifyGet`, so nothing is opaque and the `do`-block reduces without any hashing or
cache machinery running. What is *not* reducible by `rfl` is `sszGet`'s read on the resulting
`state'`, since `SSZ.Box.view` pattern-matches on `state`'s own `.cached` / `.uncached`
constructor: `rcases state with t | t` unsticks it, and the two branches close by the identical
tactic (the box-level dispatch never appears in a `sszGet`-observable postcondition; only the
Merkle-cache bookkeeping, invisible to `sszGet`, differs between them). -/

/-- **In range.** Running `initiateBuilderExit builderIndex` never rejects, and the only
`sszGet`-observable difference between the pre- and post-state is
`builders[builderIndex.toNat]!.withdrawableEpoch`, using `currentEpochOf` read from the
*pre*-state (the `do`-block's `← get` runs before the write, and nothing else can have changed
the state in between). Every other builder and the registry's `.size` are unchanged. -/
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
`state' = state`: in the cached flavour, `sszUpdate` still records a `PendingWrite` entry keyed
at `builderIndex`'s gindex in `TreeBacked.pending` (its bound check is deferred to commit time,
where it resolves to `none` and touches nothing), so the raw post-state `Box` value is a
genuinely different `pending` map, even though it is observationally, and root-wise, identical.
Claiming raw equality here would be a false theorem for the cached flavour; see the module
docstring. -/
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
`UInt64` addition, mod `2 ^ 64`. No bound on `[Config].minBuilderWithdrawabilityDelay` or on the
current epoch is universal (a `[Config]` instance is free to set
`minBuilderWithdrawabilityDelay` arbitrarily, and `currentEpochOf` grows without bound over a
chain's lifetime), so the no-wrap fact is necessarily **conditional**, exactly the shape
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
