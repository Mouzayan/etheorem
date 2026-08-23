import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.StoreRun

/-!
# `EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction`: Heze's FOCIL satisfaction-result write

`recordPayloadInclusionListSatisfaction` (`Heze/ForkChoice.lean:406-418`) is the
producer side of Heze's FOCIL satisfaction result. It takes an explicit
`Store`, records whether `payload` satisfies the inclusion-list transactions
selected for `state.slot - 1`, and returns a store whose
`payloadInclusionListSatisfaction` field is obtained by `FcMap.insert` of
that satisfaction result at `root`.
`onExecutionPayloadEnvelope` later installs that returned store, together
with the payload and warm block state, at the same root.

`recordPayloadInclusionListSatisfaction_run_eq` is the successful-run frame
equation at `ForkChoiceStoreRun (Store map)`. Under a successful transaction
collection, the recorder preserves the state returned by that collection
and returns the update with the collection's resulting runner state
unchanged by the recorder. Both Boolean results are covered: the
inserted value is `isInclusionListSatisfied payload ilTxs`. The returned
field is that `FcMap.insert` at `root`. Generic `[FcMap map]` has no
insert/lookup law, so no lookup corollary is stated.

The slot-0 `checkedSub` underflow and transaction-collection failures,
including the empty-committee and missing-timeliness-key paths, stay
outside the claim. A complete result covering those branches is what
would carry a `characterizes` tag.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedSub ExecutionEngine)
open EthCLSpecs.Heze (Preset Store State Root ExecutionPayload ExecutionRequests Transaction
  recordPayloadInclusionListSatisfaction getInclusionListTransactions isInclusionListSatisfied)

/-- If timely inclusion-list transaction collection succeeds, the recorder
returns the explicit store with `payloadInclusionListSatisfaction` updated by
`FcMap.insert` of `isInclusionListSatisfied payload ilTxs` at `root`, and
threads through the runner state that collection produced. The equation
covers both Boolean results. -/
theorem recordPayloadInclusionListSatisfaction_run_eq
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] :
    ∀ (store runnerStore postRunnerStore : Store map)
      (state : State) (root : Root)
      (payload : ExecutionPayload) (ilTxs : Array Transaction),
      sszGet state slot ≠ 0 →
      (getInclusionListTransactions
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store.inclusionListStore state (sszGet state slot - 1)
          (onlyTimely := true)).run runnerStore
        = .ok (ilTxs, postRunnerStore) →
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store state root payload).run runnerStore
        = .ok (
            { store with
              payloadInclusionListSatisfaction :=
                FcMap.insert store.payloadInclusionListSatisfaction root
                  (isInclusionListSatisfied payload ilTxs) },
            postRunnerStore) := by
  intro store runnerStore postRunnerStore state root payload ilTxs hslot htxs
  -- Targeted unfold of the recorder; residual goal is definitional.
  simp [recordPayloadInclusionListSatisfaction, checkedSub, hslot, htxs]
  rfl

end EthCLSpecs.Proofs.Heze
