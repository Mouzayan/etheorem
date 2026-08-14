import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.Gloas.Run

/-!
# `EthCLSpecs.Proofs.Heze.ShouldExtendPayload`: Heze's FOCIL rejection gate

Public declarations live in `EthCLSpecs.Proofs.Heze`, since `shouldExtendPayload` exists
in both Gloas and Heze and this module's theorem is about the Heze override alone
(`EthCLSpecs/Proofs/Gloas/UpdateCheckpoints.lean` documents the same naming reason for
`updateCheckpoints`).

`[New in Heze:EIP7805]` adds one gate to Gloas's `should_extend_payload`: after the
ordinary `is_payload_verified` check, a payload whose recorded inclusion-list
satisfaction verdict is `false` is not extended, before any of the later timeliness,
data-availability, or proposer-boost reads run. This module proves that gate fires:
`shouldExtendPayload_run_eq_false_of_recorded_unsatisfied` shows that once the
preliminary block/slot checks succeed and the payload is verified, a `false` recorded
verdict alone determines the result, at the pure `HezeStoreRun` monad this file also
names (the store-side sibling of `GloasStoreRun` in `Proofs/Gloas/ForkChoiceRun.lean`, used
here rather than the `EStateM` pin configuration because the theorem's `.run store`
equation states non-mutation of the store directly, with no separate frame lemma
needed).

The preliminary preconditions the theorem still takes as hypotheses, rather than
proving: `store.blocks[root]` resolving to a concrete block, `getCurrentSlot store`
already equal to `rootBlock.slot + 1` (so the slot-equality assertion the
implementation opens with does not fire its own reject), and that addition not
overflowing. None of those are FOCIL-specific; they are the same guard Gloas's
`should_extend_payload` opens with, unconditional on the inclusion-list gate this
module is about.

Out of scope: how a `payloadInclusionListSatisfaction` verdict comes to be recorded
(`onExecutionPayloadEnvelope`'s write, and the invariant that it always accompanies a
`payloads` write), the missing-record `assert` branch this precondition rules out,
execution-engine correctness, inclusion-list ingestion and validation, PTC committee
selection, signature verification, transaction collection, block production, P2P
propagation, global fork-choice canonicality, and liveness. This module claims only
that the gate rejects when given an already-recorded `false` verdict, nothing about
where that verdict comes from or whether it is correct.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag StoreTransitionError MapKind FcMap checkedAdd)
open EthCLSpecs.Fulu (Preset Config Root Slot)
open EthCLSpecs.Heze (Store shouldExtendPayload isPayloadInclusionListSatisfied isPayloadVerified
  getCurrentSlot BeaconBlock)

/-- The Heze store machine's pure monad: `StateT` over `Except`, threading the Heze
fork-choice `Store` and rejecting with `StoreTransitionError`. The Heze-side sibling of
`GloasStoreRun` (`Proofs/Gloas/ForkChoiceRun.lean`): a separate abbrev because `Heze.Store` is
its own `forkstruct`, distinct from `Gloas.Store`, not a renaming of the same type.

Parameterized by the map backing rather than fixed to `treeMap`, for the same reason as
`GloasStoreRun`: the backing is a separate axis of the fast/pure duality from the
monad, and a theorem that does not read a map should not pin one. -/
abbrev HezeStoreRun [Preset] [HasherTag] (map : MapKind) : Type → Type :=
  StateT (Store map) (Except StoreTransitionError)

/-- **The FOCIL enforcement theorem.** A verified payload whose recorded inclusion-list
satisfaction verdict is `false` causes `should_extend_payload` to return exactly `false`,
with the runner state unchanged (the trailing `store` in the result, not some other
state): the FOCIL guard is the branch that decides the outcome, and it stops before any
later logic runs.

`hVerified` is not needed to derive the `false` result, `isPayloadInclusionListSatisfied`
itself returns `false` whenever the payload is unverified (its own `else` branch), so an
unverified payload already forces `false` before the FOCIL gate is even reached. The
hypothesis is kept anyway: it fixes which branch is doing the rejecting. Without it, this
theorem would be equally true of an unverified payload, and would say nothing about the
inclusion-list gate specifically. With it, the ordinary verification guard is recorded as
already having passed, so the `false` this theorem proves is the FOCIL gate's rejection,
not a restatement of the ordinary unverified-payload case Gloas already has.

This theorem does not evaluate, and says nothing about, the timeliness vote, the
data-availability vote, the proposer-boost root, or the parent block; those all sit past
the gate this theorem's hypotheses stop at. It also assumes the recorded verdict as given,
`hUnsatisfied` is a hypothesis, not a derived fact, so this theorem does not establish
that the verdict itself is correct, only that the gate honors it once recorded. -/
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
