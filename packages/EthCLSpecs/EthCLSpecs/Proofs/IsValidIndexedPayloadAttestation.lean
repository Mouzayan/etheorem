import EthCLSpecs.Gloas.Operations

/-!
# `EthCLSpecs.Proofs.IsValidIndexedPayloadAttestation`: a two-layer characterization

An exact backend-generic characterization of
`EthCLSpecs.Gloas.isValidIndexedPayloadAttestation` (`Gloas/Operations.lean:389-400`),
in two layers.

`isValidIndexedPayloadAttestation_eq_true_iff_checks` (Layer 1) unfolds the function's
`if` / `||` / `!` control flow into a plain conjunction, one conjunct per gate. The two
`Array.all`-based gates, the adjacent-pair non-strict sortedness check and the in-range
check, are stated exactly as the implementation's own literal booleans, so this direction
needs nothing beyond core `Bool` / `Nat` boolean-algebra rewrites: it is a case split over
the same three conditions the function itself branches on.

`indexedPayloadAttestation_adjacentNondecreasing_iff` and
`indexedPayloadAttestation_indicesInRange_iff` (Layer 2's bridge lemmas, named with
this file's declaration as an explicit prefix since each is a narrow, single-use
translation step rather than a general-purpose `Array` fact) turn those two literal
`Array.all` gates into named per-index propositions, using only core `Array` lemmas
(`Array.all_eq_true`, `Array.size_range`, `Array.getElem_range`,
`Array.getElem?_eq_getElem`, `Option.getD_some`, `decide_eq_true_eq`), no mathlib.
`indexedPayloadAttestation_adjacentNondecreasing_iff` states only what the
implementation checks: an adjacent, non-strict order between consecutive elements. It
does not claim uniqueness, full `List.Pairwise` sortedness, or anything about
`Array.qsort`.

`isValidIndexedPayloadAttestation_eq_true_iff` (Layer 2's public theorem) composes
Layer 1 with the two bridge lemmas into the semantic characterization: non-empty,
adjacent-non-decreasing, every index in range, and the configured `[CryptoBackend]`
returning `true` on the exact pubkey array / signing root / domain / epoch the
implementation computes. The fourth conjunct is a backend call, not a cryptographic
soundness claim; no `symbolic` / `verifyOff` specialization is drawn from it here.

`getDomain`, `computeEpochAtSlot`, and `Const.domainPtcAttester` above are all the
Gloas-local names as `isValidIndexedPayloadAttestation` itself resolves them:
`Gloas.EpochProcessing`'s `inherit getDomain` and `inherit computeEpochAtSlot` each
shadow the `Fulu` original inside the `Gloas` namespace with a re-elaborated,
Gloas-scoped copy, so this file opens and uses those copies directly rather than the
`Fulu` originals. No Fulu/Gloas equivalence theorem for either is needed or claimed.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

-- `sszGet` is `scoped syntax`, not a plain declaration (`open (sszGet)` fails
-- to parse it), so `EthCLLib.Spec` stays a full `open`; the `HasherTag` /
-- `CryptoBackend` / `blsFastAggregateVerify` / `computeSigningRoot` names it
-- also brings in are the only other `EthCLLib.Spec` names this file uses.
open EthCLLib.Spec
open EthCLSpecs.Fulu (Preset ValidatorIndex)
open EthCLSpecs.Fulu.Const (domainPtcAttester)
open EthCLSpecs.Gloas
  (State IndexedPayloadAttestation isValidIndexedPayloadAttestation getDomain computeEpochAtSlot)

/-! ## Layer 1: the literal characterization -/

/-- The exact, backend-generic characterization of `isValidIndexedPayloadAttestation`:
a direct unfold of its `if` / `||` / `!` control flow into a conjunction, one conjunct
per gate. The two `Array.all`-based gates (adjacent-pair sortedness, in-range) are
stated exactly as the implementation's own literal booleans; see
`indexedPayloadAttestation_adjacentNondecreasing_iff` /
`indexedPayloadAttestation_indicesInRange_iff` and
`isValidIndexedPayloadAttestation_eq_true_iff` below for the bridged, indexed form. -/
theorem isValidIndexedPayloadAttestation_eq_true_iff_checks [Preset] [HasherTag] [CryptoBackend]
    (state : State) (a : IndexedPayloadAttestation) :
    isValidIndexedPayloadAttestation state a = true ↔
      let idx := a.attestingIndices.toArray
      let validators := sszGet state validators
      idx.size ≠ 0 ∧
      (Array.range (idx.size - 1)).all
          (fun i => idx[i]?.getD default ≤ idx[i + 1]?.getD default) = true ∧
      idx.all (fun i => i.toNat < validators.size) = true ∧
      blsFastAggregateVerify (idx.map (fun i => (validators[i.toNat]!).pubkey))
        (computeSigningRoot a.data
          (getDomain state domainPtcAttester (computeEpochAtSlot a.data.slot)))
        a.signature = true := by
  unfold isValidIndexedPayloadAttestation
  dsimp only
  rcases Bool.eq_false_or_eq_true (a.attestingIndices.toArray.size == 0) with h1 | h1
  · simp_all
  · rcases Bool.eq_false_or_eq_true
      ((Array.range (a.attestingIndices.toArray.size - 1)).all
        (fun i => a.attestingIndices.toArray[i]?.getD default
          ≤ a.attestingIndices.toArray[i + 1]?.getD default))
      with h2 | h2
    · rcases Bool.eq_false_or_eq_true
        (a.attestingIndices.toArray.all (fun i => i.toNat < (sszGet state validators).size))
        with h3 | h3
      · simp_all
      · simp_all
        intro hforall
        obtain ⟨i, hi, hge⟩ := h3
        have := hforall i hi
        omega
    · simp_all

/-! ## Layer 2: core-only bridge lemmas, then the public semantic theorem -/

/-- Bridges the adjacent-pair, non-strict sortedness check
`isValidIndexedPayloadAttestation` performs (`Array.range` + `all` + `Option.getD`) into
an indexed inequality between consecutive elements. States exactly what the
implementation checks, an adjacent, non-strict order, no more: not uniqueness, not full
`List.Pairwise` sortedness, not `Array.qsort` correctness. -/
theorem indexedPayloadAttestation_adjacentNondecreasing_iff (idx : Array ValidatorIndex) :
    (Array.range (idx.size - 1)).all
        (fun i => idx[i]?.getD default ≤ idx[i + 1]?.getD default) = true ↔
      ∀ i (h : i + 1 < idx.size), idx[i]'(by omega) ≤ idx[i + 1]'h := by
  rw [Array.all_eq_true]
  constructor
  · intro h i hi
    have hi' : i < (Array.range (idx.size - 1)).size := by rw [Array.size_range]; omega
    have h' := h i hi'
    rw [Array.getElem_range hi'] at h'
    rwa [Array.getElem?_eq_getElem (show i < idx.size by omega),
      Array.getElem?_eq_getElem (show i + 1 < idx.size by omega), Option.getD_some,
      Option.getD_some, decide_eq_true_eq] at h'
  · intro h i hi
    have hi' : i < idx.size - 1 := by simpa [Array.size_range] using hi
    rw [Array.getElem_range hi]
    rw [Array.getElem?_eq_getElem (show i < idx.size by omega),
      Array.getElem?_eq_getElem (show i + 1 < idx.size by omega), Option.getD_some,
      Option.getD_some, decide_eq_true_eq]
    exact h i (by omega)

/-- Bridges the in-range check `isValidIndexedPayloadAttestation` performs
(`Array.all` over the raw elements) into a per-index bound. A direct application of
`Array.all_eq_true`, no `Array.range` plumbing needed since the check is already
elementwise. -/
theorem indexedPayloadAttestation_indicesInRange_iff [Preset] [HasherTag]
    (state : State) (idx : Array ValidatorIndex) :
    idx.all (fun i => i.toNat < (sszGet state validators).size) = true ↔
      ∀ i (h : i < idx.size), (idx[i]'h).toNat < (sszGet state validators).size := by
  simp only [Array.all_eq_true, decide_eq_true_eq]

/-- The public semantic characterization of `isValidIndexedPayloadAttestation`: non-empty,
adjacent-non-decreasing (in the literal, non-strict sense
`indexedPayloadAttestation_adjacentNondecreasing_iff` states, not full sortedness or
uniqueness), every index within the validator registry,
and the configured `[CryptoBackend]` returning `true` on the exact pubkey array, signing
root, `DOMAIN_PTC_ATTESTER` domain, and slot-derived epoch the implementation computes.
The fourth conjunct names a backend call; it is not a cryptographic soundness claim, and
no `symbolic` / `verifyOff` specialization is drawn here. -/
theorem isValidIndexedPayloadAttestation_eq_true_iff [Preset] [HasherTag] [CryptoBackend]
    (state : State) (a : IndexedPayloadAttestation) :
    isValidIndexedPayloadAttestation state a = true ↔
      let idx := a.attestingIndices.toArray
      let validators := sszGet state validators
      idx.size ≠ 0 ∧
      (∀ i (h : i + 1 < idx.size), idx[i]'(by omega) ≤ idx[i + 1]'h) ∧
      (∀ i (h : i < idx.size), (idx[i]'h).toNat < validators.size) ∧
      blsFastAggregateVerify (idx.map (fun i => (validators[i.toNat]!).pubkey))
        (computeSigningRoot a.data
          (getDomain state domainPtcAttester (computeEpochAtSlot a.data.slot)))
        a.signature = true := by
  rw [isValidIndexedPayloadAttestation_eq_true_iff_checks]
  simp only [indexedPayloadAttestation_adjacentNondecreasing_iff,
    indexedPayloadAttestation_indicesInRange_iff]

end EthCLSpecs.Proofs
