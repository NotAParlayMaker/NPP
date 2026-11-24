import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Cut: the pin AND of at most two wires is itself a Monotone2 gate on the ten inputs, so the
-- 13 gates after it plus the pin form ONE Monotone2 circuit with at most 14 gates on ten inputs.
-- h1 is the link lemma for n = 10, s = 14 (desk step L-meta-3644, verbatim); h2 says the SAT
-- encoding for 14 gates is unsatisfiable on all 512 consistent rows (bit 9 = not bit 0).
theorem PEqualNP.Outside.R_meta_3622_314
    (h1 : ∀ (x1 : List ℕ) (x2 : ℕ → Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x4 ∈ x1, x4 < (1024 : ℕ)) → PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (14 : ℕ) → (∀ x7 ∈ x1, x3.eval (List.ofFn fun (x9 : Fin (10 : ℕ)) => x7.testBit ↑x9) = x2 x7) → PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) x2 x1))
    (h2 : ¬ PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ)
      (fun (r : ℕ) => r.testBit 0 && r.testBit 1 || r.testBit 1 && r.testBit 2 || r.testBit 2 && r.testBit 3 || r.testBit 3 && r.testBit 4 || r.testBit 4 && r.testBit 0 || r.testBit 0 && r.testBit 5 || r.testBit 1 && r.testBit 6 || r.testBit 2 && r.testBit 7 || r.testBit 3 && r.testBit 8 || r.testBit 5 && r.testBit 7 || r.testBit 6 && r.testBit 8 || r.testBit 8 && r.testBit 5)
      ((List.range 1024).filter (fun (r : ℕ) => r.testBit 9 != r.testBit 0)))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         (12 : ℕ) ≤ x3.size →           x3.size ≤ (13 : ℕ) →             List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => !x7.op.eval [Bool.true]) x3.gates = (0 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x3.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 C hfan hlo hhi hcnt
  by_contra hne
  apply h2
  refine h1 _ _ ⟨⟨GateOp.and, x1⟩ :: C.gates, C.output⟩ ?_ ?_ ?_ ?_
  · intro r hr
    rw [List.mem_filter, List.mem_range] at hr
    exact hr.1
  · intro g hg
    rcases List.mem_cons.mp hg with hg | hg
    · subst hg
      exact ⟨Or.inl rfl, hx1⟩
    · obtain ⟨hop, hlen⟩ := hfan g hg
      refine ⟨?_, hlen⟩
      have hz := (List.countP_eq_zero.mp hcnt) g hg
      rcases hop with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · exfalso
        apply hz
        rw [Set.mem_singleton_iff.mp hop]
        rfl
  · show C.gates.length + 1 ≤ 14
    have : C.gates.length ≤ 13 := hhi
    omega
  · intro r hr
    rw [List.mem_filter, List.mem_range] at hr
    obtain ⟨_, h9⟩ := hr
    have h9' : r.testBit 9 = !r.testBit 0 := by
      revert h9
      cases r.testBit 9 <;> cases r.testBit 0 <;> simp
    have hrow : (List.ofFn fun (i : Fin 10) => r.testBit ↑i) =
        List.ofFn (fun (i : Fin 9) => r.testBit ↑i) ++ [!r.testBit 0] := by
      simp [List.ofFn_succ, h9']
    have hk := fun h => hne ⟨fun (i : Fin 9) => r.testBit ↑i, h⟩
    rw [hrow]
    exact Classical.not_not.mp hk
