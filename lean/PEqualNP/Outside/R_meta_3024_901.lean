import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3024_901
    (many : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 15 →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
      2 ≤ C.gates.countP (fun g => g.op.eval [false]) →
      PEqualNP.MetaComplexity.circuitFun 9 C ≠ (fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)))
    (mono : ∀ i : Fin 11, ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [x 0 || x 2]
      C.eval (w ++ [!(w.getD i.val false)]) ≠ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) :
∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins hpins C fan size
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 2]
  let first : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, [0,2]⟩
  let second : PEqualNP.CircuitLowerBounds.Gate := ⟨.not, pins.map Fin.val⟩
  let full : PEqualNP.CircuitLowerBounds.Circuit := ⟨first :: second :: C.gates, C.output⟩
  have firstEval (x : Fin 9 → Bool) :
      first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 2) := by
    change ((List.ofFn x).getD 0 false || ((List.ofFn x).getD 2 false || false)) = (x 0 || x 2)
    simp [List.getD]
  have fullEval (x : Fin 9 → Bool) :
      full.eval (List.ofFn x) = C.eval (seed x ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval
        (pins.map fun i => (seed x).getD i.val false)]) := by
    change C.eval ((List.ofFn x ++ [_]) ++ [_]) = _
    simp only [firstEval]
    simp only [seed, second, List.map_map, Function.comp_def]
  by_cases extra : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · by_contra! agree
    have fullFan : PEqualNP.MetaComplexity.FanInTwo full := by
      intro g hg
      change g ∈ first :: second :: C.gates at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [first]
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by simp [second], by simpa [second] using hpins⟩
      · exact fan g hg
    have fullSize : full.size ≤ 15 := by
      change C.gates.length + 1 + 1 ≤ 15
      change C.gates.length ≤ 13 at size
      omega
    have keep (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k : Nat)
        (hk : k < w.length) :
        ((PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires w).getD k false = w.getD k false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change ((PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires (w ++ [_])).getD k false = _
        rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hk]
    have fullFirst (x : Fin 9 → Bool) :
        (full.wires (List.ofFn x)).getD 9 false = (x 0 || x 2) := by
      change ((PEqualNP.CircuitLowerBounds.Circuit.mk (second :: C.gates) 0).wires
        (List.ofFn x ++ [_])).getD 9 false = _
      rw [firstEval, keep _ _ _ (by simp)]
      simp [List.getD]
    have positive : 0 < C.gates.countP (fun g => g.op.eval [false]) := by
      rw [List.countP_pos_iff]
      obtain ⟨g,hg,hop⟩ := extra
      exact ⟨g,hg,by rw [hop]; rfl⟩
    have two : 2 ≤ full.gates.countP (fun g => g.op.eval [false]) := by
      simp only [full, List.countP_cons]
      change 2 ≤ (C.gates.countP (fun g => g.op.eval [false]) + 1) + 0
      omega
    apply many full fullFan fullSize fullFirst two
    funext x
    change full.eval (List.ofFn x) = _
    rw [fullEval]
    simpa only [seed, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using Classical.not_not.mp (agree x)
  · have monotone : PEqualNP.MetaComplexity.Monotone2 C := by
      intro g hg
      obtain ⟨ops,arity⟩ := fan g hg
      refine ⟨?_,arity⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops ⊢
      rcases ops with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (extra ⟨g,hg,h⟩)
    let i : Fin 11 := pins.headD 10
    obtain ⟨x,hx⟩ := mono i C monotone size
    refine ⟨x, ?_⟩
    have notValue : PEqualNP.CircuitLowerBounds.GateOp.not.eval
        (pins.map fun j => (seed x).getD j.val false) = !((seed x).getD i.val false) := by
      cases pins with
      | nil =>
        have length : (seed x).length = 10 := by simp [seed]
        change true = !((seed x).getD 10 false)
        rw [List.getD_eq_default _ _ (by omega)]
        rfl
      | cons j js => rfl
    change C.eval (seed x ++ [_]) ≠ _
    rw [notValue]
    simpa only [seed, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using hx
