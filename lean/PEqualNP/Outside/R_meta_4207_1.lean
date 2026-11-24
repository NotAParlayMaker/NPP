import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4207_1
    (hmono :
      let f (x : Fin 9 → Bool) :=
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
          (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any
          fun e => x e.1 && x e.2
      ∀ C : Circuit, Monotone2 C → circuitFun 9 C = f → 16 ≤ C.size)
    (hnot :
      let f (x : Fin 9 → Bool) :=
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
          (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any
          fun e => x e.1 && x e.2
      let r (C : Circuit) (v : Fin 9) : Finset (Fin C.size) :=
        {i : Fin C.size | v.val ∈ (C.gates.get i).inputs}
      let clean (C : Circuit) := ∀ i : Fin C.size,
        let g := C.gates.get i
        (∀ w ∈ g.inputs, w < 9 + i.val) ∧ g.inputs.Nodup ∧
          (g.op = GateOp.not ∧ g.inputs.length = 1 ∨
            g.op ≠ GateOp.not ∧ g.inputs.length = 2)
      let low (C : Circuit) := ∀ v ∈ ([4, 6, 7] : List (Fin 9)),
        (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
          ∀ i ∈ r C v, (C.gates.get i).op = GateOp.or
      ∀ C : Circuit, IsMinimalCircuit 9 C → C.size = 15 → circuitFun 9 C = f →
        clean C → low C → (r C 4).card = 2 →
        (∃ g ∈ C.gates, g.op = GateOp.not) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 →     x3.size = (15 : ℕ) →       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 →         (∀ (x7 : Fin x3.size),             have x8 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x7;             (∀ x9 ∈ x8.inputs, x9 < (9 : ℕ) + ↑x7) ∧ x8.inputs.Nodup ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x8.inputs.length = (1 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x8.inputs.length = (2 : ℕ))) →           (∀ x8 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x8).Nonempty ∧ (x2 x3 x8).card ≤ (2 : ℕ) ∧ ∀ x10 ∈ x2 x3 x8, (x3.gates.get x10).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (x2 x3 (4 : Fin (9 : ℕ))).card = (2 : ℕ) → False := by
  classical
  dsimp only
  intro C hmin hsize hfun hclean hlow hcard
  let f (x : Fin 9 → Bool) :=
    ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
      (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any
      fun e => x e.1 && x e.2
  have hfun' : circuitFun 9 C = f := by
    rw [hfun]
    funext x
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  by_cases hn : ∃ g ∈ C.gates, g.op = GateOp.not
  · exact hnot C hmin hsize hfun' hclean hlow hcard hn
  · have hm : Monotone2 C := by
      intro g hg
      obtain ⟨hop, hfanin⟩ := hmin.1 g hg
      refine ⟨?_, hfanin⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hn ⟨g, hg, h⟩).elim
    have := hmono C hm hfun'
    omega
