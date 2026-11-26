import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18407

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

private def incident (p q : Fin 13) : Prop :=
  p - q = 0 ∨ p - q = 1 ∨ p - q = 3 ∨ p - q = 9

instance (p q : Fin 13) : Decidable (incident p q) := by
  unfold incident
  infer_instance

private def arcA : Finset (Fin 13) := {0, 1, 2, 5}
private def arcB : Finset (Fin 13) := {2, 4, 5, 6}

private def miss (arc : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun p : Fin 13 => decide (p ∈ arc)) ++
  (List.ofFn fun q : Fin 13 => decide (∀ p ∈ arc, ¬incident p q))

private def hit : List Bool :=
  (List.ofFn fun p : Fin 13 => decide (p = 0)) ++
  (List.ofFn fun q : Fin 13 => decide (q = 0))

private theorem inputSupport : supported (miss arcA) (miss arcB) hit := by
  have covering : ∀ i : Fin 26, hit.getD i.val false = true →
      (miss arcA).getD i.val false = true ∨ (miss arcB).getD i.val false = true := by
    decide +kernel
  refine ⟨by decide, by decide, ?_⟩
  intro i hi
  by_cases valid : i < 26
  · exact covering ⟨i, valid⟩ hi
  · rw [List.getD_eq_default _ _ (by simpa [hit] using Nat.le_of_not_lt valid)] at hi
    cases hi

end PEqualNP.Outside.L_meta_18407

open PEqualNP.Outside.L_meta_18407 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_18407 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → (∀ (x5 x6 : Fin (13 : ℕ)), x5 - x6 = (0 : Fin (13 : ℕ)) ∨ x5 - x6 = (1 : Fin (13 : ℕ)) ∨ x5 - x6 = (3 : Fin (13 : ℕ)) ∨ x5 - x6 = (9 : Fin (13 : ℕ)) → x1.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) → (∀ (x6 : Finset (Fin (13 : ℕ))), x6.card = (4 : ℕ) → (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x9 - x8 = (0 : Fin (13 : ℕ)) ∨ x9 - x8 = (1 : Fin (13 : ℕ)) ∨ x9 - x8 = (3 : Fin (13 : ℕ)) ∨ x9 - x8 = (9 : Fin (13 : ℕ))}.card ≤ (2 : ℕ)) → x1.eval ((List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x6, ¬(x10 - x9 = (0 : Fin (13 : ℕ)) ∨ x10 - x9 = (1 : Fin (13 : ℕ)) ∨ x10 - x9 = (3 : Fin (13 : ℕ)) ∨ x10 - x9 = (9 : Fin (13 : ℕ))))) = Bool.false) → (64 : ℕ) ≤ x1.size := by
  intro C fit noAnd _ good bad
  have ops : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hg
    have notAnd : g.op ≠ .and := by
      intro h
      exact noAnd ⟨⟨i, hi⟩, (congrArg Gate.op e).trans h⟩
    have op := (fit g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, notAnd, false_or] using op
  have et : C.eval hit = true := good 0 0 (Or.inl (by decide))
  have ea : C.eval (miss arcA) = false := bad arcA (by decide +kernel) (by decide +kernel)
  have eb : C.eval (miss arcB) = false := bad arcB (by decide +kernel) (by decide +kernel)
  have out : C.eval (miss arcA) = true ∨ C.eval (miss arcB) = true :=
    (evaluate_supported C.gates ops inputSupport).2.2 C.output et
  rcases out with ha | hb
  · cases ea.symm.trans ha
  · cases eb.symm.trans hb
