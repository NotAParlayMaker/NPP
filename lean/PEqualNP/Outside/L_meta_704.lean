import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta704

open PEqualNP.AndCount.AndCountCircuit

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private theorem gate_true (T U : Finset (Fin n)) (i : Fin T.card) (d : ℕ) (hd : 0 < d) :
    (starCircuit G T).gateValFuel U d i = true ↔
      T.orderEmbOfFin rfl i ∈ U ∧ ∃ v ∈ U, G.Adj (T.orderEmbOfFin rfl i) v := by
  cases d with
  | zero => omega
  | succ d =>
      simp only [gateValFuel, sideTrue, Bool.and_eq_true]
      rw [decide_eq_true_eq, decide_eq_true_eq]
      simp [starCircuit]
      constructor
      · rintro ⟨ha, hb⟩
        rcases ha with ha | ⟨j, hj, _⟩
        · rcases hb with ⟨v, huv, hv⟩ | ⟨j, hj, _⟩
          · exact ⟨ha, v, hv, huv⟩
          · exact (Finset.notMem_empty j hj).elim
        · exact (Finset.notMem_empty j hj).elim
      · rintro ⟨ha, v, hv, huv⟩
        exact ⟨Or.inl ha, Or.inl ⟨v, huv, hv⟩⟩

private theorem eval_true (T U : Finset (Fin n))
    (hT : ∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) :
    (starCircuit G T).eval U = true ↔ ∃ a ∈ U, ∃ b ∈ U, G.Adj a b := by
  have houtput : (starCircuit G T).eval U = true ↔
      ∃ i : Fin T.card, (starCircuit G T).gateVal U i = true := by
    unfold eval
    rw [decide_eq_true_eq]
    change ((∃ a ∈ (∅ : Finset (Fin n)), a ∈ U) ∨
      ∃ i ∈ (Finset.univ : Finset (Fin T.card)), (starCircuit G T).gateVal U i = true) ↔ _
    simp
  rw [houtput]
  have indexed (i : Fin T.card) := gate_true G T U i T.card (Nat.zero_lt_of_lt i.isLt)
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨ha, b, hb, hab⟩ := (indexed i).mp hi
    exact ⟨T.orderEmbOfFin rfl i, ha, b, hb, hab⟩
  · have witness (a b : Fin n) (haT : a ∈ T) (haU : a ∈ U) (hbU : b ∈ U) (hab : G.Adj a b) :
        ∃ i : Fin T.card, (starCircuit G T).gateVal U i = true := by
      have hrange : a ∈ Set.range (T.orderEmbOfFin (rfl : T.card = T.card)) := by
        rwa [Finset.range_orderEmbOfFin]
      obtain ⟨i, hi⟩ := hrange
      exact ⟨i, (indexed i).mpr ⟨hi ▸ haU, b, hbU, hi ▸ hab⟩⟩
    rintro ⟨a, ha, b, hb, hab⟩
    rcases hT a b hab with h | h
    · exact witness a b h ha hb hab
    · exact witness b a h hb ha (G.adj_symm hab)

end PEqualNP.Outside.LMeta704

theorem PEqualNP.Outside.L_meta_704 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
      (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) →
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).WellFormed ∧
      (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).size = T.card ∧
      ∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) →
        (∀ x : Fin n, x ∉ I → ∃ v ∈ I, G.Adj x v) →
        (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).eval I = false ∧
        ∀ x : Fin n, x ∉ I →
          (PEqualNP.AndCount.AndCountCircuit.starCircuit G T).eval (insert x I) = true := by
  intro n G _ T hT
  let C := PEqualNP.AndCount.AndCountCircuit.starCircuit G T
  refine ⟨?_, rfl, ?_⟩
  · intro i
    constructor <;> intro j hj <;>
      exact (Finset.notMem_empty j hj).elim
  intro I hInd hMax
  have heval := PEqualNP.Outside.LMeta704.eval_true G T I hT
  refine ⟨?_, ?_⟩
  · cases h : C.eval I with
    | false => rfl
    | true =>
      obtain ⟨a, ha, b, hb, hab⟩ := heval.mp h
      exact (hInd a ha b hb hab).elim
  · intro x hx
    obtain ⟨v, hv, hxv⟩ := hMax x hx
    apply (PEqualNP.Outside.LMeta704.eval_true G T (insert x I) hT).mpr
    exact ⟨x, Finset.mem_insert_self _ _, v, Finset.mem_insert_of_mem hv, hxv⟩
