import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Gloas.Run

/-!
# `EthCLSpecs.Proofs.Heze.ShouldExtendPayload`: Heze's FOCIL rejection gate

Heze's `shouldExtendPayload` follows the Gloas fork-choice decision flow but
inserts a FOCIL gate after payload verification and before the later timeliness,
data-availability, and proposer-boost logic.
This module proves that, once the common block/slot prefix succeeds, a verified
payload with a recorded `false` inclusion-list satisfaction verdict returns `false`
in the pure `HezeStoreRun`, leaving its runner state unchanged.

The theorem assumes the successful block lookup, current-slot calculation,
non-overflowing slot increment, and recorded verdict. It does not prove verdict
production or correctness, the payload/verdict pairing invariant, missing-record
behavior, inclusion-list construction or validation, or end-to-end canonicality
and liveness.

The theorem lives in `EthCLSpecs.Proofs.Heze` because `shouldExtendPayload` exists
in both Gloas and Heze.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag StoreTransitionError MapKind FcMap checkedAdd)
open EthCLSpecs.Fulu (Preset Config Root Slot)
open EthCLSpecs.Heze (Store shouldExtendPayload isPayloadInclusionListSatisfied isPayloadVerified
  getCurrentSlot BeaconBlock)

/-- Pure `StateT`/`Except` runner for Heze fork-choice proofs, mirroring
`GloasStoreRun`. A separate abbreviation is required because `Heze.Store` is a
distinct fork structure. The map backing remains abstract through `MapKind`. -/
abbrev HezeStoreRun [Preset] [HasherTag] (map : MapKind) : Type → Type :=
  StateT (Store map) (Except StoreTransitionError)

/-- A verified payload with a recorded `false` inclusion-list satisfaction verdict
is rejected by Heze's FOCIL gate once the preliminary block/slot checks succeed.
The result preserves the runner state and short-circuits the later inherited Gloas
logic.

`hVerified` is logically unnecessary for the Boolean conclusion: an unverified
payload is rejected earlier. It is retained to establish that the FOCIL gate is
the rejecting branch. The converse is not claimed: `shouldExtendPayload` can also
return `false` for an unverified payload or because of later Gloas logic. -/
theorem shouldExtendPayload_run_eq_false_of_recorded_unsatisfied
    {map : MapKind} [Preset] [HasherTag] [Config] [FcMap map]
    (store : Store map) (root : Root) (rootBlock : BeaconBlock)
    (hBlock : FcMap.lookup store.blocks root = some rootBlock)
    (hCurrentSlot :
      (getCurrentSlot (StoreTransition := HezeStoreRun map) store).run store
        = .ok (rootBlock.slot + 1, store))
    (hNoOverflow : ¬ (rootBlock.slot + 1 < rootBlock.slot))
    (hVerified : isPayloadVerified store root = true)
    (hUnsatisfied : FcMap.lookup store.payloadInclusionListSatisfaction root = some false) :
    (shouldExtendPayload (StoreTransition := HezeStoreRun map) store root).run store
      = .ok (false, store) := by
  simp [shouldExtendPayload, isPayloadInclusionListSatisfied, FcMap.getOrThrow,
    FcMap.getOrThrowKey, FcMap.getOrAssert, hBlock, checkedAdd, hNoOverflow, hVerified,
    hUnsatisfied, hCurrentSlot, Gloas.GloasRun.except_bind_ok]
  rfl

end EthCLSpecs.Proofs.Heze
