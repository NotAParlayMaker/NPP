import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1745_5
  (buildFromCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A T : Finset (Fin n))
      (f : (Fin n → Bool) → Bool),
    (∃ u w, G.Adj u w) →
    (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) →
    (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) →
    ∃ s, s + 1 ≤ A.card + G.edgeSet.ncard + T.card ∧ HasCircuitSize n f s)
  (belowCoverBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (f : (Fin n → Bool) → Bool) (C : Circuit),
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
    (∀ u w, G.Adj u w → u ∉ A) →
    (∃ u w, G.Adj u w) →
    (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) →
    FanInTwo C → circuitFun n C = f →
    (∀ s, HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ A,
      let readers := C.gates.filter (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
      readers.length ≤ 3 ∧ (readers.length = 3 → ∀ g ∈ readers, g.op = GateOp.or)) →
    (∀ T : Finset (Fin n), (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) →
      C.size + 1 < A.card + G.edgeSet.ncard + T.card) →
    ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update x v false)) s) :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (f : (Fin n → Bool) → Bool) (C : Circuit),
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
    (∀ u w, G.Adj u w → u ∉ A) →
    (∃ u w, G.Adj u w) →
    (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) →
    FanInTwo C → circuitFun n C = f →
    (∀ s, HasCircuitSize n f s → C.size ≤ s) →
    (∀ v ∉ A,
      let readers := C.gates.filter (fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
      readers.length ≤ 3 ∧ (readers.length = 3 → ∀ g ∈ readers, g.op = GateOp.or)) →
    ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update x v false)) s := by
  classical
  intro n G A f C hdeg hgirth hfree hedge hsem hfan hfun hmin hread
  by_cases cheap : ∀ T : Finset (Fin n), (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) →
      C.size + 1 < A.card + G.edgeSet.ncard + T.card
  · exact belowCoverBound n G A f C hdeg hgirth hfree hedge hsem hfan hfun hmin hread cheap
  push Not at cheap
  obtain ⟨T, hcover, hbudget⟩ := cheap
  obtain ⟨i, j, hij⟩ := hedge
  have pick : ∃ v w, v ∈ T ∧ G.Adj v w := by
    rcases hcover i j hij with hi | hj
    · exact ⟨i, j, hi, hij⟩
    · exact ⟨j, i, hj, hij.symm⟩
  obtain ⟨v, w, hvT, hvw⟩ := pick
  have hvA := hfree v w hvw
  have hwA := hfree w v hvw.symm
  have alive : ∃ z, G.Adj w z ∧ z ≠ v := by
    by_contra! h
    have sub : G.neighborSet w ⊆ {v} := fun z hz => h z hz
    have := Set.ncard_le_ncard sub
    simp [hdeg w hwA] at this
  obtain ⟨z, hwz, hz⟩ := alive
  have edge' : (G.deleteIncidenceSet v).Adj w z :=
    SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hwz, hvw.ne.symm, hz⟩
  have cover' : ∀ i j, (G.deleteIncidenceSet v).Adj i j → i ∈ T.erase v ∨ j ∈ T.erase v := by
    intro i j h
    obtain ⟨hij, hi, hj⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
    simpa [Finset.mem_erase, hi, hj] using hcover i j hij
  have sem' : ∀ x : Fin n → Bool, f (Function.update x v false) = true ↔
      (∃ a ∈ A, x a = true) ∨
        ∃ i j, (G.deleteIncidenceSet v).Adj i j ∧ x i = true ∧ x j = true := by
    intro x
    rw [hsem]
    have upd (i : Fin n) : Function.update x v false i = true ↔ i ≠ v ∧ x i = true := by
      by_cases h : i = v <;> simp [h]
    simp only [upd, SimpleGraph.deleteIncidenceSet_adj]
    grind
  obtain ⟨s, hs, hsize⟩ := buildFromCover n (G.deleteIncidenceSet v) A (T.erase v) _
    ⟨w, z, edge'⟩ cover' sem'
  refine ⟨v, hvA, s, ?_, hsize⟩
  have removed := G.card_edgeFinset_deleteIncidenceSet v
  have enough := G.degree_le_card_edgeFinset v
  simp only [← SimpleGraph.card_edgeSet, Set.fintypeCard_eq_ncard,
    ← SimpleGraph.ncard_neighborSet] at removed enough
  rw [hdeg v hvA] at removed enough
  rw [removed, Finset.card_erase_of_mem hvT] at hs
  have pos := Finset.card_pos.mpr ⟨v, hvT⟩
  omega
