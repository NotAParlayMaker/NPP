import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_704

open PEqualNP.AndCount.AndCountCircuit

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T U : Finset (Fin n))

private lemma side_empty {k : ℕ} (B : Finset (Fin n)) (i : Fin k) (f : Fin k → Bool) :
    sideTrue U B ∅ i f = true ↔ ∃ v ∈ B, v ∈ U := by
  unfold sideTrue
  rw [decide_eq_true_eq]
  constructor
  · rintro (h | ⟨j, hj, _⟩)
    · exact h
    · exact (Finset.notMem_empty j hj).elim
  · exact Or.inl

private lemma gate_iff (i : Fin T.card) :
    (starCircuit G T).gateVal U i = true ↔
      T.orderEmbOfFin rfl i ∈ U ∧ ∃ w ∈ U, G.Adj (T.orderEmbOfFin rfl i) w := by
  have hsize : T.card = (T.card - 1) + 1 := by
    have := i.isLt
    omega
  change gateValFuel (starCircuit G T) U T.card i = true ↔ _
  rw [congrArg (fun d => gateValFuel (starCircuit G T) U d i) hsize]
  let f : Fin T.card → Bool := gateValFuel (starCircuit G T) U (T.card - 1)
  change (sideTrue U {T.orderEmbOfFin rfl i} ∅ i f &&
    sideTrue U (Finset.univ.filter (G.Adj (T.orderEmbOfFin rfl i))) ∅ i f) = true ↔ _
  rw [Bool.and_eq_true]
  refine (and_congr (side_empty U _ i f) (side_empty U _ i f)).trans ?_
  change ((∃ v ∈ {T.orderEmbOfFin rfl i}, v ∈ U) ∧
    ∃ w ∈ Finset.univ.filter (G.Adj (T.orderEmbOfFin rfl i)), w ∈ U) ↔ _
  simp [and_comm]

private lemma eval_iff :
    (starCircuit G T).eval U = true ↔
      ∃ a ∈ T, a ∈ U ∧ ∃ b ∈ U, G.Adj a b := by
  unfold eval
  rw [decide_eq_true_eq]
  change ((∃ v ∈ (∅ : Finset (Fin n)), v ∈ U) ∨
    ∃ j ∈ (Finset.univ : Finset (Fin T.card)), (starCircuit G T).gateVal U j = true) ↔ _
  simp only [Finset.notMem_empty, false_and, exists_false,
    false_or, Finset.mem_univ, true_and, gate_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, T.orderEmbOfFin_mem rfl i, hi⟩
  · rintro ⟨a, ha, h⟩
    have hr : a ∈ Set.range (T.orderEmbOfFin rfl) := by
      rwa [T.range_orderEmbOfFin rfl]
    obtain ⟨i, rfl⟩ := hr
    exact ⟨i, h⟩

end PEqualNP.Outside.L_meta_704

theorem PEqualNP.Outside.L_meta_704 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
    (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) →
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).WellFormed ∧
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).size = T.card ∧
      ∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ x : Fin n, x ∉ I → ∃ v ∈ I, G.Adj x v) →
        (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).eval I = false ∧
        ∀ x : Fin n, x ∉ I → (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).eval (insert x I) = true := by
  intro n G _ T cover
  refine ⟨?_, rfl, ?_⟩
  · intro i
    constructor <;> intro j hj <;> exact (Finset.notMem_empty j hj).elim
  · intro I independent maximal
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨a, _, ha, b, hb, hab⟩ := (PEqualNP.Outside.L_meta_704.eval_iff G T I).mp h
      exact independent a ha b hb hab
    · intro x hx
      obtain ⟨v, hv, hxv⟩ := maximal x hx
      apply (PEqualNP.Outside.L_meta_704.eval_iff G T (insert x I)).mpr
      have hx' := Finset.mem_insert_self x I
      have hv' := Finset.mem_insert_of_mem (b := x) hv
      rcases cover x v hxv with h | h
      · exact ⟨x, h, hx', v, hv', hxv⟩
      · exact ⟨v, h, hv', x, hx', G.adj_symm hxv⟩
