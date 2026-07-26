import EthCLSpecs.Gloas.Operations

/-!
# `EthCLSpecs.Proofs.IsValidIndexedPayloadAttestation`: a two-layer characterization

An exact backend-generic characterization of
`EthCLSpecs.Gloas.isValidIndexedPayloadAttestation` (`Gloas/Operations.lean:389-400`),
in two layers.

`isValidIndexedPayloadAttestation_eq_true_iff_checks` (Layer 1) restates the function's
`if` / `||` / `!` control flow as a plain conjunction, one conjunct per gate, with the
two `Array.all`-based gates (adjacent nondecreasing check, in-range) left exactly as the
implementation's own literal booleans.

`isValidIndexedPayloadAttestation_eq_true_iff` (Layer 2) bridges those two literal
gates into named per-index propositions and restates the characterization
semantically: non-empty, adjacent nondecreasing, every index in range, and the
configured `[CryptoBackend]` returning `true` on the exact pubkey array, signing root,
domain, and epoch the implementation computes. The sortedness conjunct is deliberately
adjacent and non-strict. It does not assert uniqueness, full `List.Pairwise` sortedness,
or `Array.qsort` correctness. The signature conjunct names a backend call, not a
cryptographic soundness claim. No mathlib.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs

open EthCLLib.Spec (CryptoBackend HasherTag blsFastAggregateVerify computeSigningRoot)
open scoped EthCLLib.Spec
open EthCLSpecs.Fulu (Preset ValidatorIndex)
open EthCLSpecs.Fulu.Const (domainPtcAttester)
open EthCLSpecs.Gloas
  (State IndexedPayloadAttestation isValidIndexedPayloadAttestation getDomain computeEpochAtSlot)

/-! ## Layer 1: the literal characterization -/

/-- Exact backend-generic characterization using the function's literal
`Array.all` validation gates. -/
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
  rcases Bool.eq_false_or_eq_true (a.attestingIndices.toArray.size == 0) with hempty | hempty
  · simp_all only [beq_iff_eq, Array.size_eq_zero_iff, List.size_toArray, List.length_nil, BEq.rfl,
      Nat.zero_le, Nat.sub_eq_zero_of_le, Nat.not_lt_zero, not_false_eq_true, getElem?_neg,
      Option.getD_none, Std.le_refl, decide_true, Array.size_range, Bool.true_or, ↓reduceIte,
      Bool.false_eq_true, ne_eq, not_true_eq_false, List.all_toArray', List.all_nil,
      List.map_toArray, List.map_nil, true_and, false_and]
  · rcases Bool.eq_false_or_eq_true
      ((Array.range (a.attestingIndices.toArray.size - 1)).all
        (fun i => a.attestingIndices.toArray[i]?.getD default
          ≤ a.attestingIndices.toArray[i + 1]?.getD default))
      with hsorted | hsorted
    · rcases Bool.eq_false_or_eq_true
        (a.attestingIndices.toArray.all (fun i => i.toNat < (sszGet state validators).size))
        with hbounds | hbounds
      · simp_all only [beq_eq_false_iff_ne, ne_eq, Array.size_eq_zero_iff, Array.size_range,
          Array.all_eq_true, decide_eq_true_eq, Bool.not_true, Bool.or_false, beq_iff_eq,
          ↓reduceIte, Bool.not_eq_eq_eq_not, Array.all_eq_false, decide_true, not_true_eq_false,
          exists_false, not_false_eq_true, implies_true, true_and]
      · simp_all only [beq_eq_false_iff_ne, ne_eq, Array.size_eq_zero_iff, Array.size_range,
          Array.all_eq_false, decide_eq_true_eq, Nat.not_lt, Bool.not_true, Bool.or_false,
          beq_iff_eq, ↓reduceIte, Bool.not_eq_eq_eq_not, Bool.false_eq_true, not_false_eq_true,
          Array.all_eq_true, true_and, false_iff, not_and, Bool.not_eq_true]
        intro hall
        obtain ⟨i, hi, hge⟩ := hbounds
        have hlt := hall i hi
        omega
    · simp_all only [beq_eq_false_iff_ne, ne_eq, Array.size_eq_zero_iff, Array.size_range,
        Bool.not_false, Bool.or_true, ↓reduceIte, Bool.false_eq_true, not_false_eq_true,
        Array.all_eq_true, decide_eq_true_eq, false_and, and_false]

/-! ## Layer 2: core-only bridge lemmas, then the public semantic theorem -/

/-- Bridges the adjacent nondecreasing check
`isValidIndexedPayloadAttestation` performs (`Array.range` + `all` + `Option.getD`) into
an indexed inequality between consecutive elements. -/
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
(`Array.all` over the raw elements) into a per-index bound. -/
theorem indexedPayloadAttestation_indicesInRange_iff [Preset] [HasherTag]
    (state : State) (idx : Array ValidatorIndex) :
    idx.all (fun i => i.toNat < (sszGet state validators).size) = true ↔
      ∀ i (h : i < idx.size), (idx[i]'h).toNat < (sszGet state validators).size := by
  simp only [Array.all_eq_true, decide_eq_true_eq]

/-- The public semantic characterization of
`isValidIndexedPayloadAttestation`: the indices are non-empty, adjacent
nondecreasing, and within the validator registry, and the configured
`[CryptoBackend]` returns `true` for the exact aggregate-verification call.
This does not assert uniqueness, full `List.Pairwise` sortedness, qsort
correctness, or cryptographic soundness of the backend. -/
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
