import Mathlib
import PEqualNP.Defs

-- Pin vertex 4 to false. The extra input becomes a copy of vertex 0. The edge
-- (0,4) forces a second use of vertex 4 when vertex 0 is on. Constant
-- propagation along that use saves an AND or OR, with inversions free.
theorem PEqualNP.Outside.R_meta_2679_314
    (pin : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      let run := fun (x : Fin 9 → Bool) => C.eval (List.ofFn x ++ [x 0 || x 4])
      let restricted := fun (x : Fin 8 → Bool) => run (Fin.insertNth 4 false x)
      (∃ x y : Fin 9 → Bool, x 0 = true ∧ y 0 = true ∧
        (∀ i, i ≠ 4 → x i = y i) ∧ run x ≠ run y) →
      (∃ x y, restricted x ≠ restricted y) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
        D.size < C.size ∧
        D.gates.countP (fun g => g.op.eval [true,true]) <
          C.gates.countP (fun g => g.op.eval [true,true]) ∧
        PEqualNP.MetaComplexity.circuitFun 8 D = restricted)
    (eight : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ 13 → PEqualNP.MetaComplexity.circuitFun 8 D = (fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) →
      13 ≤ D.gates.countP (fun g => g.op.eval [true,true])) :
    ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit),   x1.output ≤ (24 : ℕ) →     x2.output ≤ (24 : ℕ) →       (∀ x5 ∈ x1.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (24 : ℕ)) →         (∀ x6 ∈ x2.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (24 : ℕ)) →           x1.size + x2.size ≤ (13 : ℕ) →             PEqualNP.MetaComplexity.Monotone2 x1 →               PEqualNP.MetaComplexity.FanInTwo x2 →                 ¬∀ (x10 : Fin (9 : ℕ) → Bool),                     have x11 : List Bool := x1.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ))]);                     x2.eval (x11 ++ [!x11.getD x1.output Bool.false]) = (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  intro P D _ _ _ _ size mono fan correct
  let inv : PEqualNP.CircuitLowerBounds.Gate := ⟨.not, [P.output]⟩
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨P.gates ++ inv :: D.gates, D.output⟩
  have legal : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g h
    change g ∈ P.gates ++ inv :: D.gates at h
    rcases List.mem_append.mp h with hg | hg
    · obtain ⟨op, ar⟩ := mono g hg
      exact ⟨(show g.op = .and ∨ g.op = .or from op).elim Or.inl
        (fun eq => Or.inr (Or.inl eq)), ar⟩
    · rcases List.mem_cons.mp hg with rfl | hd
      · exact ⟨Or.inr (Or.inr rfl), by simp [inv]⟩
      · exact fan g hd
  let f := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  have eqv (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 4]) = f x := by
    change List.getD ((P.gates ++ inv :: D.gates).foldl _ (List.ofFn x ++ [x 0 || x 4])) D.output false = _
    rw [List.foldl_append]
    exact correct x
  let f8 := fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  have rel (x : Fin 8 → Bool) : f (Fin.insertNth 4 false x) = f8 x := by
    change (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && false || false && x 0 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) = _
    simp [f8, Bool.and_false, Bool.false_and]
  obtain ⟨S, sf, shorter, smaller, hs⟩ := pin C legal (by
    refine ⟨fun i => decide (i = 0), fun i => decide (i = 0 ∨ i = 4),
      by decide, by decide, ?_, ?_⟩
    · intro i hi
      simp [hi]
    · dsimp only
      rw [eqv,eqv]
      decide) (by
    refine ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), ?_⟩
    dsimp only
    rw [eqv,eqv,rel,rel]
    decide)
  have sizeC : C.size ≤ 14 := by
    change (P.gates ++ inv :: D.gates).length ≤ 14
    change P.gates.length + D.gates.length ≤ 13 at size
    simp only [List.length_append,List.length_cons]
    omega
  have low := eight S sf (by omega) (hs.trans (funext fun x => (eqv _).trans (rel x)))
  have bound : C.gates.countP (fun g => g.op.eval [true,true]) ≤ 13 := by
    change P.gates.length + D.gates.length ≤ 13 at size
    rw [show C.gates = P.gates ++ inv :: D.gates from rfl,
      List.countP_append, List.countP_cons]
    change P.gates.countP _ + D.gates.countP _ ≤ 13
    exact (Nat.add_le_add List.countP_le_length List.countP_le_length).trans size
  omega
