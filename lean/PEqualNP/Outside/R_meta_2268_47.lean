import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Extract a minimum-size circuit and an explicit Boolean 2-coloring, then split
-- into the heavy-reader / absorbing-gate case vs the all-sparse-OR-reader case.
theorem PEqualNP.Outside.R_meta_2268_47 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
        (f : (Fin n → Bool) → Bool) (side : Fin n → Bool) (C : Circuit),
      (∀ u v : Fin n, G.Adj u v → side u ≠ side v) →
      (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∀ u v : Fin n, G.Adj u v → u ∉ A) →
      (∃ u v : Fin n, G.Adj u v) →
      (∀ x : Fin n → Bool, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      FanInTwo C → circuitFun n C = f →
      (∀ s : ℕ, HasCircuitSize n f s → C.size ≤ s) →
      (∃ z : Fin n, z ∉ A ∧
        let rs := C.gates.filter fun g =>
          List.contains (g.inputs.take (bif g.op.eval [false] then 1 else 2)) z.val
        4 ≤ rs.length ∨ (rs.length = 3 ∧ ∃ g ∈ rs, g.op ≠ GateOp.or)) →
      ∃ u v : Fin n, u ∉ A ∧ v ∉ A ∧ u ≠ v ∧ ¬ G.Adj u v ∧
        ∃ t : ℕ, t + 8 ≤ C.size ∧
          HasCircuitSize n (fun x : Fin n → Bool =>
            f (Function.update (Function.update x u false) v false)) t) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
        (f : (Fin n → Bool) → Bool) (side : Fin n → Bool) (C : Circuit),
      (∀ u v : Fin n, G.Adj u v → side u ≠ side v) →
      (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∀ u v : Fin n, G.Adj u v → u ∉ A) →
      (∃ u v : Fin n, G.Adj u v) →
      (∀ x : Fin n → Bool, f x = true ↔ (∃ a ∈ A, x a = true) ∨
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      FanInTwo C → circuitFun n C = f →
      (∀ s : ℕ, HasCircuitSize n f s → C.size ≤ s) →
      (∀ z : Fin n, z ∉ A →
        let rs := C.gates.filter fun g =>
          List.contains (g.inputs.take (bif g.op.eval [false] then 1 else 2)) z.val
        rs.length ≤ 3 ∧ (rs.length = 3 → ∀ g ∈ rs, g.op = GateOp.or)) →
      ∃ u v : Fin n, u ∉ A ∧ v ∉ A ∧ u ≠ v ∧ ¬ G.Adj u v ∧
        ∃ t : ℕ, t + 8 ≤ C.size ∧
          HasCircuitSize n (fun x : Fin n → Bool =>
            f (Function.update (Function.update x u false) v false)) t) →
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  classical
  intro heavyCase sparseCase n G A f hCol hDeg hGirth hMarked hEdge hFun s hs
  exact Nonempty.elim hCol fun col => by
    let side : Fin n → Bool := fun v => decide ((col v).val = 1)
    have hSide : ∀ u v : Fin n, G.Adj u v → side u ≠ side v := by
      intro u v hadj heq
      have hne : col u ≠ col v := col.valid hadj
      have hlt_u : (col u).val < 2 := (col u).isLt
      have hlt_v : (col v).val < 2 := (col v).isLt
      by_cases hu1 : (col u).val = 1
      · have hsu : side u = true := decide_eq_true hu1
        have hsv : side v = true := heq.symm.trans hsu
        have hv1 : (col v).val = 1 := of_decide_eq_true hsv
        exact hne (Fin.ext (hu1.trans hv1.symm))
      · have hsu : side u = false := decide_eq_false hu1
        have hsv : side v = false := heq.symm.trans hsu
        have hv1 : (col v).val ≠ 1 := of_decide_eq_false hsv
        exact hne (Fin.ext (by omega))
    have hex : ∃ m : ℕ, HasCircuitSize n f m := ⟨s, hs⟩
    exact Exists.elim (Nat.find_spec hex) fun C hC => by
      have hFan : FanInTwo C := hC.1
      have hEval : circuitFun n C = f := funext hC.2.2
      have hMin : ∀ s' : ℕ, HasCircuitSize n f s' → C.size ≤ s' :=
        fun s' hs' => hC.2.1.trans (Nat.find_min' hex hs')
      have hCs : C.size ≤ s := hMin s hs
      let readers : Fin n → List Gate := fun z =>
        C.gates.filter fun g =>
          List.contains (g.inputs.take (bif g.op.eval [false] then 1 else 2)) z.val
      by_cases hHeavy : ∃ z : Fin n, z ∉ A ∧
          (4 ≤ (readers z).length ∨ ((readers z).length = 3 ∧ ∃ g ∈ readers z, g.op ≠ GateOp.or))
      · exact Exists.elim (heavyCase n G A f side C hSide hDeg hGirth hMarked hEdge hFun hFan hEval hMin hHeavy)
          fun u hu => Exists.elim hu fun v hv =>
            Exists.elim hv.2.2.2.2 fun t ht =>
              ⟨u, v, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, t, ht.1.trans hCs, ht.2⟩
      · have hSparse : ∀ z : Fin n, z ∉ A →
            (readers z).length ≤ 3 ∧ ((readers z).length = 3 → ∀ g ∈ readers z, g.op = GateOp.or) := by
          intro z hz
          refine ⟨?_, ?_⟩
          · by_contra hgt
            exact hHeavy ⟨z, hz, Or.inl (by omega)⟩
          · intro h3 g hg
            by_contra hne
            exact hHeavy ⟨z, hz, Or.inr ⟨h3, g, hg, hne⟩⟩
        exact Exists.elim (sparseCase n G A f side C hSide hDeg hGirth hMarked hEdge hFun hFan hEval hMin hSparse)
          fun u hu => Exists.elim hu fun v hv =>
            Exists.elim hv.2.2.2.2 fun t ht =>
              ⟨u, v, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, t, ht.1.trans hCs, ht.2⟩
