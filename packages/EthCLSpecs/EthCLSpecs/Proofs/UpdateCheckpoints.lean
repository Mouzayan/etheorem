import EthCLSpecs.Gloas.ForkChoice

/-!
# `EthCLSpecs.Proofs.UpdateCheckpoints`: checkpoint monotonicity

`EthCLSpecs.Gloas.updateCheckpoints` replaces the Store's justified and finalized
checkpoints only when the corresponding candidate has a strictly greater epoch.
This file characterizes both branches exactly and proves that each invocation
preserves or advances both recorded epochs.

All current updates to these fields use this function; `getForkchoiceStore` initializes
the fields directly and is outside this claim. The separate Fulu declaration is also
out of scope.

`updateCheckpoints` is declared identically in both forks, so unlike the Gloas-only
subjects of the sibling proof modules these theorem names would collide with a Fulu
companion. They live in `EthCLSpecs.Proofs.Gloas`, mirroring the `EthCLSpecs.Gloas`
namespace the subject itself sits in, leaving `EthCLSpecs.Proofs.Fulu` free.

See `EthCLSpecs/docs/CONSENSUS_PROOF_CANDIDATES.md`, "Monotonicity properties".
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLSpecs.Gloas (Store updateCheckpoints Checkpoint)
open EthCLSpecs.Fulu (Preset)
open EthCLLib.Spec (MapKind HasherTag)

/-- The resulting justified checkpoint is either unchanged because `j` is not newer,
or exactly `j` because its epoch is strictly greater. -/
theorem updateCheckpoints_justifiedCheckpoint_eq_or_advances
    {map : MapKind} [Preset] [HasherTag] (store : Store map) (j f : Checkpoint) :
    ((updateCheckpoints store j f).justifiedCheckpoint = store.justifiedCheckpoint ∧
        j.epoch ≤ store.justifiedCheckpoint.epoch) ∨
    ((updateCheckpoints store j f).justifiedCheckpoint = j ∧
        store.justifiedCheckpoint.epoch < j.epoch) := by
  -- Decide both guards so `simp` can reduce the nested record updates
  -- and project the checkpoint field unaffected by the other update.
  by_cases h1 : j.epoch > store.justifiedCheckpoint.epoch
  · refine .inr ⟨?_, h1⟩
    by_cases h2 : f.epoch > store.finalizedCheckpoint.epoch <;> simp [updateCheckpoints, h1, h2]
  · refine .inl ⟨?_, UInt64.not_lt.mp h1⟩
    by_cases h2 : f.epoch > store.finalizedCheckpoint.epoch <;> simp [updateCheckpoints, h1, h2]

/-- The resulting finalized checkpoint is either unchanged because `f` is not newer,
or exactly `f` because its epoch is strictly greater. -/
theorem updateCheckpoints_finalizedCheckpoint_eq_or_advances
    {map : MapKind} [Preset] [HasherTag] (store : Store map) (j f : Checkpoint) :
    ((updateCheckpoints store j f).finalizedCheckpoint = store.finalizedCheckpoint ∧
        f.epoch ≤ store.finalizedCheckpoint.epoch) ∨
    ((updateCheckpoints store j f).finalizedCheckpoint = f ∧
        store.finalizedCheckpoint.epoch < f.epoch) := by
  -- Decide both guards so `simp` can reduce the nested record updates
  -- and project the checkpoint field unaffected by the other update.
  by_cases h2 : f.epoch > store.finalizedCheckpoint.epoch
  · refine .inr ⟨?_, h2⟩
    by_cases h1 : j.epoch > store.justifiedCheckpoint.epoch <;> simp [updateCheckpoints, h1, h2]
  · refine .inl ⟨?_, UInt64.not_lt.mp h2⟩
    by_cases h1 : j.epoch > store.justifiedCheckpoint.epoch <;> simp [updateCheckpoints, h1, h2]

/-- `updateCheckpoints` never lowers the Store's justified epoch. -/
theorem updateCheckpoints_justifiedEpoch_le
    {map : MapKind} [Preset] [HasherTag] (store : Store map) (j f : Checkpoint) :
    store.justifiedCheckpoint.epoch ≤ (updateCheckpoints store j f).justifiedCheckpoint.epoch := by
  rcases updateCheckpoints_justifiedCheckpoint_eq_or_advances store j f with ⟨h, _⟩ | ⟨h, hlt⟩
  · rw [h]; exact UInt64.le_refl _
  · rw [h]; exact UInt64.le_of_lt hlt

/-- `updateCheckpoints` never lowers the Store's finalized epoch. -/
theorem updateCheckpoints_finalizedEpoch_le
    {map : MapKind} [Preset] [HasherTag] (store : Store map) (j f : Checkpoint) :
    store.finalizedCheckpoint.epoch ≤ (updateCheckpoints store j f).finalizedCheckpoint.epoch := by
  rcases updateCheckpoints_finalizedCheckpoint_eq_or_advances store j f with ⟨h, _⟩ | ⟨h, hlt⟩
  · rw [h]; exact UInt64.le_refl _
  · rw [h]; exact UInt64.le_of_lt hlt

end EthCLSpecs.Proofs.Gloas
