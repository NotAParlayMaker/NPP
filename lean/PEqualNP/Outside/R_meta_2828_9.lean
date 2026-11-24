import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2828_9
    (h1 : ∀ (C : PEqualNP.MetaComplexity.BinaryCircuit) (b : Bool),
      (∀ g ∈ C.gates, ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      C.output = C.size + 10 →
      (∀ x : Fin 9 → Bool, (C.eval (List.ofFn x ++ [x 0 || x 1, false]) != b) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ C.size)
    (h2 : ∀ (C : PEqualNP.MetaComplexity.BinaryCircuit) (b : Bool),
      (∀ g ∈ C.gates, ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      11 ≤ C.output → C.output < C.size + 10 →
      (∀ x : Fin 9 → Bool, (C.eval (List.ofFn x ++ [x 0 || x 1, false]) != b) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      14 ≤ C.size) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C b hops hfun
  -- wires keep the input list as a prefix, and there is one new wire per gate
  have hpre : ∀ (gs : List PEqualNP.MetaComplexity.BinaryGate) (W : List Bool),
      (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) W).length
        = W.length + gs.length ∧
      ∀ i : ℕ, i < W.length →
        (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) W).getD
          i false = W.getD i false := by
    intro gs
    induction gs with
    | nil => intro W; simp
    | cons g gs ih =>
      intro W
      obtain ⟨ih1, ih2⟩ := ih (W ++ [g.op (W.getD g.left false) (W.getD g.right false)])
      refine ⟨?_, ?_⟩
      · simp only [List.foldl_cons]; rw [ih1]; simp; omega
      · intro i hi
        simp only [List.foldl_cons]
        rw [ih2 i (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  -- a circuit whose output is not a real gate wire reads an input, the OR wire, or false
  have hnot : ¬ (C.output < 11 ∨ C.size + 11 ≤ C.output) := by
    intro hout
    have hv : ∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 1, false]) =
          (List.ofFn x ++ [x 0 || x 1, false]).getD C.output false := by
      intro x
      obtain ⟨hl, hg⟩ := hpre C.gates (List.ofFn x ++ [x 0 || x 1, false])
      unfold PEqualNP.MetaComplexity.BinaryCircuit.eval
        PEqualNP.MetaComplexity.BinaryCircuit.wires
      rcases hout with h | h
      · exact hg _ (by simp; omega)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
          have h' : C.gates.length + 11 ≤ C.output := h
          rw [hl]; simp; omega)]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    have e0 := hfun (fun _ => false)
    have e1 := hfun (fun i => i == 5 || i == 7)
    have e2 := hfun (fun i => i == 3 || i == 4)
    rw [hv] at e0 e1 e2
    have hb : b = false := by
      revert e0
      cases b <;> generalize C.output = o <;> intro e0
      · rfl
      · exfalso; revert e0
        rcases Nat.lt_or_ge o 11 with ho | ho
        · interval_cases o <;> decide
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; decide
    subst hb
    revert e1 e2
    generalize C.output = o
    intro e1 e2
    rcases Nat.lt_or_ge o 11 with ho | ho
    · interval_cases o <;> revert e1 e2 <;> decide
    · revert e1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      decide
  -- what remains: the output is a gate wire; either the last gate or an earlier one
  rcases Nat.lt_or_ge C.output (C.size + 10) with h | h
  · exact h2 C b hops (by omega) h hfun
  · exact h1 C b hops (by omega) hfun
