import EthCLSpecs.Heze.ForkChoice
import EthCLSpecs.Proofs.StoreRun

/-!
# `EthCLSpecs.Proofs.Heze.RecordPayloadInclusionListSatisfaction`: Heze's FOCIL verdict write

`recordPayloadInclusionListSatisfaction` (`Heze/ForkChoice.lean:406-418`) is the
producer side of Heze's FOCIL verdict. It takes an explicit `Store`, records
whether `payload` satisfies the inclusion-list transactions selected for
`state.slot - 1`, stores that verdict under `root`, and returns the updated
`Store` as the monadic value. The runner state is left unchanged.
`onExecutionPayloadEnvelope` later installs that returned store, together
with the payload and warm block state, at the same root.

`recordPayloadInclusionListSatisfaction_run_eq` is the successful-run frame
equation at `ForkChoiceStoreRun (Store map)`. Both Boolean verdicts are
covered: the inserted value is `isInclusionListSatisfied payload ilTxs`. The
returned field is that `FcMap.insert` at `root`. Generic `[FcMap map]` has no
insert/lookup law, so no lookup corollary is stated.

The slot-0 `checkedSub` underflow and the `getInclusionListTransactions`
failures (empty committee, missing timeliness key) stay outside the claim.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLSpecs.Proofs (ForkChoiceStoreRun)
open EthCLLib.Spec (HasherTag MapKind FcMap checkedSub ExecutionEngine)
open EthCLSpecs.Heze (Preset Store State Root ExecutionPayload ExecutionRequests Transaction
  recordPayloadInclusionListSatisfaction getInclusionListTransactions isInclusionListSatisfied)

/-- Successful run of `recordPayloadInclusionListSatisfaction`: the explicit
store gains `FcMap.insert` of `isInclusionListSatisfied payload ilTxs` at
`root`, and the runner state is `runnerStore`. Both Boolean verdicts are this
same write. -/
@[characterizes EthCLSpecs.Heze.recordPayloadInclusionListSatisfaction]
theorem recordPayloadInclusionListSatisfaction_run_eq
    {map : MapKind} [Preset] [HasherTag] [FcMap map]
    [ExecutionEngine ExecutionPayload Transaction ExecutionRequests] :
    ∀ (store runnerStore : Store map) (state : State) (root : Root)
      (payload : ExecutionPayload) (ilTxs : Array Transaction),
      sszGet state slot ≠ 0 →
      (getInclusionListTransactions store.inclusionListStore state (sszGet state slot - 1)
        : ForkChoiceStoreRun (Store map) (Array Transaction)).run runnerStore
        = .ok (ilTxs, runnerStore) →
      (recordPayloadInclusionListSatisfaction
          (StoreTransition := ForkChoiceStoreRun (Store map))
          store state root payload).run runnerStore
        = .ok ({ store with
            payloadInclusionListSatisfaction :=
              FcMap.insert store.payloadInclusionListSatisfaction root
                (isInclusionListSatisfied payload ilTxs) }, runnerStore) := by
  intro store runnerStore state root payload ilTxs hslot htxs
  simp [recordPayloadInclusionListSatisfaction, checkedSub, hslot, htxs]
  rfl

end EthCLSpecs.Proofs.Heze
