import EthCLSpecs.Gloas.Transition

/-!
# `EthCLSpecs.Proofs.ProcessOperations`: deposit gate and successful-run characterization

Exact deposit-gate and successful-run characterization of Gloas
`processOperations` over the concrete `EStateM` runner. One theorem rejects a
non-empty in-block deposit list at the opening assert; the other characterizes a
successful `.run` exactly as empty deposits plus the six operation-family loops
succeeding in implementation order with threaded states. Handlers stay opaque.

`processOperations` is the operations coordinator within `processBlock`; these
theorems do not characterize the complete block-processing pipeline.

This module characterizes the coordinator's deposit gate and sequencing. It does
not establish complete correctness of operation processing: per-operation
handler postconditions sit outside its scope. Only the initial deposit assertion
is proved to preserve the pre-state on failure. Later handler failure states are
not characterized here; `EStateM` retains state changes made before a failure
rather than rolling them back.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (HasherTag CryptoBackend StateTransitionError SpecReject SSZList)
open scoped EthCLLib.Spec
open EthCLSpecs.Fulu (Preset Config)
open EthCLSpecs.Gloas (
  State BeaconBlockBody processOperations
  processProposerSlashing processAttesterSlashing processAttestation
  processVoluntaryExit processBlsToExecutionChange processPayloadAttestation)

/-- Concrete state-transition monad for Gloas `processOperations` theorems. -/
abbrev ProcessOperationsRun [Preset] [HasherTag] :=
  EStateM StateTransitionError State

/-- Left-to-right monadic fold of a body's operation list through its handler.
Definitionally `ForM.forM ops.val handler`, which is
`ops.val.foldlM (fun _ => handler) ⟨⟩`. This is the `forIn` expression Lean
emits for each `for op in ops do handler op` inside `processOperations` (the
`SSZList` instance delegates to `Array`, and an always-yielding body folds). -/
abbrev processOperationsForM [Preset] [HasherTag]
    {α : Type} {cap : Nat}
    (ops : SSZList α cap) (handler : α → ProcessOperationsRun Unit) :
    ProcessOperationsRun Unit :=
  ForM.forM ops.val handler

/-- Unit-returning `EStateM` actions absorb a trailing `pure ()`. -/
private theorem run_eq_bind_pure_unit [Preset] [HasherTag] :
    ∀ (x : ProcessOperationsRun Unit),
      (x >>= fun _ => pure PUnit.unit) = x := by
  intro x
  exact bind_pure_unit

/-- `(fun _ => a) <$> x` equals `x >>= fun _ => pure a` on `EStateM`. -/
private theorem map_const_eq_bind_pure [Preset] [HasherTag] :
    ∀ {α β : Type} (x : ProcessOperationsRun α) (a : β),
      (fun _ => a) <$> x = (x >>= fun _ => pure a) := by
  intro α β x a
  simp [Functor.map]

/-- The elaborated `forIn` body of `for op in ops do handler op` equals
`processOperationsForM`. -/
private theorem forIn_ops_eq_processOperationsForM [Preset] [HasherTag] :
    ∀ {α : Type} {cap : Nat} (ops : SSZList α cap)
      (handler : α → ProcessOperationsRun Unit),
      forIn ops PUnit.unit (fun op (_ : PUnit) => do
          handler op
          pure (ForInStep.yield PUnit.unit)) =
        processOperationsForM ops handler := by
  intro α cap ops handler
  -- `SSZList.ForIn` delegates to the underlying array.
  show forIn ops.val PUnit.unit
      (fun op (_ : PUnit) =>
        handler op >>= fun _ => pure (ForInStep.yield PUnit.unit)) =
    ForM.forM ops.val handler
  have hbody :
      (fun op (_ : PUnit) =>
        handler op >>= fun _ => pure (ForInStep.yield PUnit.unit)) =
      (fun a (_ : PUnit) =>
        (fun _ => ForInStep.yield PUnit.unit) <$> handler a) := by
    funext op _; rw [map_const_eq_bind_pure]
  rw [hbody, Array.forIn_yield_eq_foldlM
    (f := fun a (_ : PUnit) => handler a)
    (g := fun (_ : α) (_ : PUnit) (_ : PUnit) => PUnit.unit)]
  simp only [ForM.forM, Array.forM, map_const_eq_bind_pure, run_eq_bind_pure_unit]

/-- `processOperations` is the deposit assert followed by the six family folds. -/
private theorem processOperations_eq_seq [Preset] [HasherTag] [Config] [CryptoBackend] :
    ∀ (body : BeaconBlockBody),
      processOperations (StateTransition := ProcessOperationsRun) body = (do
        assert (body.deposits.size == 0)
        processOperationsForM body.proposerSlashings processProposerSlashing
        processOperationsForM body.attesterSlashings processAttesterSlashing
        processOperationsForM body.attestations processAttestation
        processOperationsForM body.voluntaryExits processVoluntaryExit
        processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange
        processOperationsForM body.payloadAttestations processPayloadAttestation) := by
  intro body
  unfold processOperations
  simp only [forIn_ops_eq_processOperationsForM, bind_pure_unit]

/-- Non-empty deposits make the opening `== 0` check false. -/
private theorem deposits_size_beq_zero_eq_false :
    ∀ {α : Type} {cap : Nat} (deposits : SSZList α cap),
      deposits.size ≠ 0 → (deposits.size == 0) = false := by
  intro α cap deposits hne
  exact beq_eq_false_iff_ne.2 hne

/-- Deposit-gate characterization: non-empty in-block deposits fail the opening
assertion immediately. The error is an `assert` constructor; its diagnostic
string is existential and unpinned in the statement. Only this initial gate is
claimed to preserve `pre`. Later handler failure states are not characterized
here; `EStateM` retains state changes made before a failure rather than rolling
them back. -/
theorem processOperations_nonempty_deposits_error [Preset] [HasherTag] [Config] [CryptoBackend] :
    ∀ (body : BeaconBlockBody) (pre : State),
      body.deposits.size ≠ 0 →
      ∃ descr : String,
        (processOperations (StateTransition := ProcessOperationsRun) body).run pre =
          .error (.assert descr) pre := by
  intro body pre hne
  rw [processOperations_eq_seq]
  have hfalse : (body.deposits.size == 0) = false :=
    deposits_size_beq_zero_eq_false body.deposits hne
  simp [hfalse, EStateM.run, Bind.bind, EStateM.bind, throw, throwThe,
    MonadExceptOf.throw, EStateM.throw, SpecReject.assert]

/-- Success of `x >>= f` on `ProcessOperationsRun Unit` unpacks to an intermediate
state where `x` succeeded and `f` continued from there. -/
private theorem run_bind_unit_ok_iff [Preset] [HasherTag] :
    ∀ (x : ProcessOperationsRun Unit) (f : Unit → ProcessOperationsRun Unit)
      (s post : State),
      (x >>= f).run s = .ok () post ↔
        ∃ s', x.run s = .ok () s' ∧ (f ()).run s' = .ok () post := by
  intro x f s post
  cases hx : x s with
  | ok u s' =>
    cases u
    simp [EStateM.run, Bind.bind, EStateM.bind, hx]
  | error e s' =>
    simp [EStateM.run, Bind.bind, EStateM.bind, hx]

/-- The six family folds as a single `ProcessOperationsRun` action. -/
private abbrev processOperationsLoops [Preset] [HasherTag] [Config] [CryptoBackend]
    (body : BeaconBlockBody) : ProcessOperationsRun Unit := do
  processOperationsForM body.proposerSlashings processProposerSlashing
  processOperationsForM body.attesterSlashings processAttesterSlashing
  processOperationsForM body.attestations processAttestation
  processOperationsForM body.voluntaryExits processVoluntaryExit
  processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange
  processOperationsForM body.payloadAttestations processPayloadAttestation

/-- `processOperationsLoops` is the six `processOperationsForM` steps in bind form. -/
private theorem processOperationsLoops_eq_binds [Preset] [HasherTag] [Config] [CryptoBackend] :
    ∀ (body : BeaconBlockBody),
      processOperationsLoops body =
        (processOperationsForM body.proposerSlashings processProposerSlashing >>= fun _ =>
         processOperationsForM body.attesterSlashings processAttesterSlashing >>= fun _ =>
         processOperationsForM body.attestations processAttestation >>= fun _ =>
         processOperationsForM body.voluntaryExits processVoluntaryExit >>= fun _ =>
         processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange >>= fun _ =>
         processOperationsForM body.payloadAttestations processPayloadAttestation) := by
  intro body
  rfl

/-- Unpack success of the six loops into the five intermediate states plus `post`. -/
private theorem processOperationsLoops_run_ok_iff [Preset] [HasherTag] [Config] [CryptoBackend] :
    ∀ (body : BeaconBlockBody) (pre post : State),
      (processOperationsLoops body).run pre = .ok () post ↔
        ∃ afterproposers afterattesters afterattestations afterexits afterchanges : State,
          (processOperationsForM body.proposerSlashings processProposerSlashing).run pre =
            .ok () afterproposers ∧
          (processOperationsForM body.attesterSlashings processAttesterSlashing).run
              afterproposers =
            .ok () afterattesters ∧
          (processOperationsForM body.attestations processAttestation).run
              afterattesters =
            .ok () afterattestations ∧
          (processOperationsForM body.voluntaryExits processVoluntaryExit).run
              afterattestations =
            .ok () afterexits ∧
          (processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange).run
              afterexits =
            .ok () afterchanges ∧
          (processOperationsForM body.payloadAttestations processPayloadAttestation).run
              afterchanges =
            .ok () post := by
  intro body pre post
  rw [processOperationsLoops_eq_binds]
  constructor
  · intro hok
    rw [run_bind_unit_ok_iff] at hok
    obtain ⟨afterproposers, h1, hrest1⟩ := hok
    rw [run_bind_unit_ok_iff] at hrest1
    obtain ⟨afterattesters, h2, hrest2⟩ := hrest1
    rw [run_bind_unit_ok_iff] at hrest2
    obtain ⟨afterattestations, h3, hrest3⟩ := hrest2
    rw [run_bind_unit_ok_iff] at hrest3
    obtain ⟨afterexits, h4, hrest4⟩ := hrest3
    rw [run_bind_unit_ok_iff] at hrest4
    obtain ⟨afterchanges, h5, h6⟩ := hrest4
    exact ⟨afterproposers, afterattesters, afterattestations, afterexits, afterchanges,
      h1, h2, h3, h4, h5, h6⟩
  · intro ⟨afterproposers, afterattesters, afterattestations, afterexits, afterchanges,
        h1, h2, h3, h4, h5, h6⟩
    rw [run_bind_unit_ok_iff]
    refine ⟨afterproposers, h1, ?_⟩
    rw [run_bind_unit_ok_iff]
    refine ⟨afterattesters, h2, ?_⟩
    rw [run_bind_unit_ok_iff]
    refine ⟨afterattestations, h3, ?_⟩
    rw [run_bind_unit_ok_iff]
    refine ⟨afterexits, h4, ?_⟩
    rw [run_bind_unit_ok_iff]
    exact ⟨afterchanges, h5, h6⟩

/-- After a successful deposit assert, `processOperations` is the six loops. -/
private theorem processOperations_run_eq_loops [Preset] [HasherTag] [Config] [CryptoBackend] :
    ∀ (body : BeaconBlockBody) (pre : State),
      (body.deposits.size == 0) = true →
      (processOperations (StateTransition := ProcessOperationsRun) body).run pre =
        (processOperationsLoops body).run pre := by
  intro body pre htrue
  rw [processOperations_eq_seq]
  simp [htrue, EStateM.run, Bind.bind, EStateM.bind, pure, EStateM.pure,
    processOperationsLoops]

/-- Exact success ↔: `processOperations` succeeds iff deposits are empty and the
six operation-family loops succeed sequentially, each from the preceding loop's
resulting state. Five existential intermediate states; `post` is the supplied
final state. Handlers stay opaque, so this is a coordinator sequencing
characterization rather than complete correctness of operation processing. -/
theorem processOperations_run_ok_iff [Preset] [HasherTag] [Config] [CryptoBackend] :
    ∀ (body : BeaconBlockBody) (pre post : State),
      (processOperations (StateTransition := ProcessOperationsRun) body).run pre =
          .ok () post ↔
        body.deposits.size = 0 ∧
        ∃ afterproposers afterattesters afterattestations afterexits afterchanges : State,
          (processOperationsForM body.proposerSlashings processProposerSlashing).run pre =
            .ok () afterproposers ∧
          (processOperationsForM body.attesterSlashings processAttesterSlashing).run
              afterproposers =
            .ok () afterattesters ∧
          (processOperationsForM body.attestations processAttestation).run
              afterattesters =
            .ok () afterattestations ∧
          (processOperationsForM body.voluntaryExits processVoluntaryExit).run
              afterattestations =
            .ok () afterexits ∧
          (processOperationsForM body.blsToExecutionChanges processBlsToExecutionChange).run
              afterexits =
            .ok () afterchanges ∧
          (processOperationsForM body.payloadAttestations processPayloadAttestation).run
              afterchanges =
            .ok () post := by
  intro body pre post
  constructor
  · intro hok
    cases hbeq : body.deposits.size == 0 with
    | false =>
      rw [processOperations_eq_seq] at hok
      simp [hbeq, EStateM.run, Bind.bind, EStateM.bind, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw, SpecReject.assert] at hok
    | true =>
      refine ⟨beq_iff_eq.mp hbeq, ?_⟩
      have hloops : (processOperationsLoops body).run pre = .ok () post := by
        rwa [← processOperations_run_eq_loops body pre hbeq]
      exact (processOperationsLoops_run_ok_iff body pre post).mp hloops
  · intro ⟨hsize, hloops⟩
    have htrue : (body.deposits.size == 0) = true := beq_iff_eq.mpr hsize
    have hok : (processOperationsLoops body).run pre = .ok () post :=
      (processOperationsLoops_run_ok_iff body pre post).mpr hloops
    rwa [processOperations_run_eq_loops body pre htrue]

end EthCLSpecs.Proofs
