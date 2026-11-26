import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18167

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def supported (x y z : List Bool) : Prop :=
  x.length = z.length ∧ y.length = z.length ∧ ∀ i,
    z.getD i false = true → x.getD i false = true ∨ y.getD i false = true

private theorem reading (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h, ite_eq_right (ne_of_lt h)]
  by_cases hEq : i = w.length
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right hEq, List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

private theorem append_supported {x y z : List Bool} {a b c : Bool}
    (h : supported x y z) (hn : c = true → a = true ∨ b = true) :
    supported (x ++ [a]) (y ++ [b]) (z ++ [c]) := by
  refine ⟨by simp [h.1], by simp [h.2.1], ?_⟩
  intro i hi
  rw [reading] at hi
  rw [reading, reading, h.1, h.2.1]
  split_ifs at hi ⊢
  · exact hn hi
  · exact h.2.2 _ hi

private theorem or_supported {x y z : List Bool} {g : Gate}
    (op : g.op = .or) (h : supported x y z) :
    g.op.eval (g.inputs.map (fun i => z.getD i false)) = true →
    g.op.eval (g.inputs.map (fun i => x.getD i false)) = true ∨
      g.op.eval (g.inputs.map (fun i => y.getD i false)) = true := by
  simp only [op, GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true]
  rintro ⟨i, hi, hz⟩
  rcases h.2.2 i hz with hx | hy
  · exact Or.inl ⟨i, hi, hx⟩
  · exact Or.inr ⟨i, hi, hy⟩

private def evaluate (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

private theorem evaluate_supported (gs : List Gate) {x y z : List Bool}
    (ops : ∀ g ∈ gs, g.op = .or) (h : supported x y z) :
    supported (evaluate gs x) (evaluate gs y) (evaluate gs z) := by
  induction gs generalizing x y z with
  | nil => exact h
  | cons g tail ih =>
    exact ih (fun j hj => ops j (List.mem_cons_of_mem _ hj))
      (append_supported h (or_supported (ops g (by simp)) h))

private def a (i : Fin 10) : Bool := decide (i = 0)
private def b (i : Fin 10) : Bool := decide (i = 1)
private def both (i : Fin 10) : Bool := a i || b i
private def target (x5 : Fin 10 → Bool) : Bool := (x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)))

private theorem initial : supported (List.ofFn a) (List.ofFn b) (List.ofFn both) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i h
  by_cases hi : i < 10
  · have al : i < (List.ofFn a).length := by simpa only [List.length_ofFn] using hi
    have bl : i < (List.ofFn b).length := by simpa only [List.length_ofFn] using hi
    have cl : i < (List.ofFn both).length := by simpa only [List.length_ofFn] using hi
    rw [List.getD_eq_getElem _ _ cl, List.getElem_ofFn] at h
    rw [List.getD_eq_getElem _ _ al, List.getD_eq_getElem _ _ bl,
        List.getElem_ofFn, List.getElem_ofFn]
    simpa only [both, Bool.or_eq_true] using h
  · rw [List.getD_eq_default _ _ (by simp; omega)] at h
    cases h

end PEqualNP.Outside.L_meta_18167

open PEqualNP.Outside.L_meta_18167 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_18167 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (18 : ℕ) → (¬∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ (x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) := by
  intro C fit _ noAnd
  have ops : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hg
    have notAnd : g.op ≠ .and := by
      intro h
      refine noAnd ⟨⟨i, hi⟩, ?_⟩
      exact congrArg Gate.op e |>.trans h
    have op := (fit g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, notAnd, false_or] using op
  change ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ target x
  by_contra! eq
  have ea : C.eval (List.ofFn a) = false := (eq a).trans (by decide +kernel)
  have eb : C.eval (List.ofFn b) = false := (eq b).trans (by decide +kernel)
  have et : C.eval (List.ofFn both) = true := (eq both).trans (by decide +kernel)
  have out : C.eval (List.ofFn a) = true ∨ C.eval (List.ofFn b) = true :=
    (evaluate_supported C.gates ops initial).2.2 C.output et
  rcases out with ha | hb
  · cases ea.symm.trans ha
  · cases eb.symm.trans hb
