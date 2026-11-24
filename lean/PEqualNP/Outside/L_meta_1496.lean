import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1496_aux

theorem countStops (n : ℕ) (inputs : ℕ → List ℕ) (active : ℕ → Prop)
    (r : ℕ) (R stops I : Finset ℕ)
    (reach : ∀ k, k ∈ R ↔ Relation.ReflTransGen
      (fun k k' : ℕ => active k ∧ n + k' ∈ inputs k) r k)
    (stop : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, active k ∧ w ∈ inputs k) ∨
      (n ≤ w ∧ w - n ∈ R ∧ ¬ active (w - n)))
    (arity : ∀ k ∈ R, active k → (inputs k).length ≤ 2)
    (keep : ∀ k ∈ R, active k → k ∈ I) :
    stops.card ≤ I.card + 1 := by
  classical
  let A := R.filter active
  let W := A.image (fun k => n + k)
  let U := A.biUnion (fun k => (inputs k).toFinset)
  let B := insert (n + r) U
  have edgeMem (k : ℕ) (hk : k ∈ R) (ha : active k) (w : ℕ) (hw : w ∈ inputs k) :
      w ∈ B :=
    Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_filter.mpr ⟨hk, ha⟩, List.mem_toFinset.mpr hw⟩)
  have reachMem (k : ℕ) (h : Relation.ReflTransGen
      (fun k k' : ℕ => active k ∧ n + k' ∈ inputs k) r k) : n + k ∈ B := by
    cases h with
    | refl => exact Finset.mem_insert_self _ _
    | tail hpath edge =>
      exact edgeMem _ ((reach _).mpr hpath) edge.1 _ edge.2
  have covered : stops ∪ W ⊆ B := by
    intro w hw
    rcases Finset.mem_union.mp hw with hs | hw
    · rcases (stop w).mp hs with ⟨_, k, hk, ha, hin⟩ | ⟨hnw, hk, _⟩
      · exact edgeMem k hk ha w hin
      · have := reachMem (w - n) ((reach _).mp hk)
        rwa [Nat.add_sub_of_le hnw] at this
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
      exact reachMem k ((reach _).mp (Finset.mem_filter.mp hk).1)
  have separate : Disjoint stops W := by
    refine Finset.disjoint_left.mpr ?_
    intro w hs hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    have he : n + k - n = k := by omega
    rcases (stop (n + k)).mp hs with ⟨h, _⟩ | ⟨_, _, h⟩
    · omega
    · rw [he] at h
      exact h (Finset.mem_filter.mp hk).2
  have wcard : W.card = A.card :=
    Finset.card_image_of_injective _ fun _ _ h => Nat.add_left_cancel h
  have ucard : U.card ≤ 2 * A.card := by
    calc
      U.card ≤ ∑ k ∈ A, (inputs k).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ A, 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have info := Finset.mem_filter.mp hk
        exact (List.toFinset_card_le (inputs k)).trans (arity k info.1 info.2)
      _ = 2 * A.card := by simp [mul_comm]
  have count := (Finset.card_le_card covered).trans ((Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right ucard 1))
  rw [Finset.card_union_of_disjoint separate, wcard] at count
  have bound : A.card ≤ I.card :=
    Finset.card_le_card fun k hk =>
      let info := Finset.mem_filter.mp hk
      keep k info.1 info.2
  omega

-- The gate-arity assumption is the only property of IsAO2 used below.
theorem countCircuitStops :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.length ≤ 2) →
  ∀ (Z : Finset ℕ) (r : ℕ), r < C.gates.length →
  ∀ (R : Finset ℕ), (∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      n + k' ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) r k) →
  ∀ (stops : Finset ℕ), (∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or))) →
  ∀ I : Finset ℕ, (∀ k, k ∈ R → k ∉ Z →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or → k ∈ I) →
    stops.card ≤ I.card + 1 := by
  classical
  intro n C arity Z r _hr R reach stops stop I keep
  let inputs (k : ℕ) := (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs
  let active (k : ℕ) :=
    k ∉ Z ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
      PEqualNP.CircuitLowerBounds.GateOp.or
  refine countStops n inputs active r R stops I ?_ ?_ ?_ ?_
  · simpa only [active, inputs, and_assoc] using reach
  · intro w
    rw [stop w]
    simp only [inputs, active, not_and_or, not_not, and_assoc, ne_eq]
  · intro k _ _
    by_cases hk : k < C.gates.length
    · exact arity k hk
    · change (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.length ≤ 2
      rw [PEqualNP.MetaComplexity.NestedCover.gateAt,
        List.getD_eq_default _ _ (Nat.le_of_not_gt hk)]
      decide
  · exact fun k hk ha => keep k hk ha.1 ha.2

end PEqualNP.Outside.L_meta_1496_aux

theorem PEqualNP.Outside.L_meta_1496 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C →
  ∀ (Z : Finset ℕ) (r : ℕ), r < C.gates.length →
  ∀ (R : Finset ℕ), (∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      n + k' ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) r k) →
  ∀ (stops : Finset ℕ), (∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or))) →
  ∀ I : Finset ℕ, (∀ k, k ∈ R → k ∉ Z →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or → k ∈ I) →
    stops.card ≤ I.card + 1 := by
  intro n C hC
  apply PEqualNP.Outside.L_meta_1496_aux.countCircuitStops n C
  intro k hk
  have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C k ∈ C.gates := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  rw [hC.2.2 _ hmem]
