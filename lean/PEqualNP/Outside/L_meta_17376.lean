import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17376

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem boolLe (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

private def runs (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

private theorem appendMono (xs ys : List Bool) (a b : Bool)
    (hlen : xs.length = ys.length) (h : ∀ i, xs.getD i false ≤ ys.getD i false) (hab : a ≤ b) :
    ∀ i, (xs ++ [a]).getD i false ≤ (ys ++ [b]).getD i false := by
  intro i
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hi : i < xs.length
  · rw [List.getElem?_append_left hi, List.getElem?_append_left (by omega)]
    simpa [List.getD_eq_getElem?_getD] using h i
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hlen]
    cases i - ys.length with
    | zero => simpa using hab
    | succ k => simp

private theorem gateMono (g : Gate) (xs ys : List Bool)
    (hop : g.op = .and ∨ g.op = .or)
    (h : ∀ i, xs.getD i false ≤ ys.getD i false) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) ≤
      g.op.eval (g.inputs.map fun i => ys.getD i false) := by
  apply (boolLe _ _).mpr
  rcases hop with e | e
  · simp only [e, GateOp.eval, List.all_eq_true, List.mem_map]
    intro hxs y hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact (boolLe _ _).mp (h i) (hxs _ ⟨i, hi, rfl⟩)
  · simp only [e, GateOp.eval, List.any_eq_true, List.mem_map]
    intro hxs
    obtain ⟨x, ⟨i, hi, rfl⟩, hx⟩ := hxs
    exact ⟨_, ⟨i, hi, rfl⟩, (boolLe _ _).mp (h i) hx⟩

private theorem runMono (gs : List Gate) (xs ys : List Bool)
    (hlen : xs.length = ys.length) (h : ∀ i, xs.getD i false ≤ ys.getD i false)
    (ho : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    ∀ i, (runs gs xs).getD i false ≤ (runs gs ys).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    unfold runs
    rw [List.foldl_cons, List.foldl_cons]
    apply ih _ _ (by simp [hlen]) (appendMono _ _ _ _ hlen h (gateMono _ _ _ (ho _ (by simp)) h))
    exact fun g hg => ho g (List.mem_cons_of_mem _ hg)

private theorem circuitMono (n : ℕ) (C : Circuit) (hm : Monotone2 C) : Monotone (circuitFun n C) := by
  intro a b hab
  change (runs C.gates (List.ofFn a)).getD C.output false ≤ (runs C.gates (List.ofFn b)).getD C.output false
  apply runMono _ _ _ (by simp) _ _ _
  · intro i
    by_cases hi : i < n
    · simpa [List.getD_eq_getElem?_getD, hi] using hab ⟨i, hi⟩
    · simp [List.getD_eq_getElem?_getD, hi]
  · intro g hg
    simpa using (hm g hg).1

private theorem extreme {n : ℕ} (f g : (Fin n → Bool) → Bool)
    (hg : Monotone g)
    (h : ∀ x, (∀ i, x i = f x → f (Function.update x i (!(x i))) ≠ f x) → g x = f x) :
    ∀ x, g x = f x := by
  classical
  let active (x : Fin n → Bool) := Finset.univ.filter (fun i => x i = f x)
  have claim : ∀ m : ℕ, ∀ x, (active x).card = m → g x = f x := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro x hm
      by_cases hc : ∀ i, x i = f x → f (Function.update x i (!(x i))) ≠ f x
      · exact h x hc
      · obtain ⟨i, hi'⟩ := not_forall.mp hc
        have hi : x i = f x := (not_imp.mp hi').1
        let y := Function.update x i (!(x i))
        have hy : f y = f x := not_not.mp (not_imp.mp hi').2
        have hmem : i ∈ active x := by simp [active, hi]
        have hactive : active y = (active x).erase i := by
          ext j
          by_cases e : j = i
          · subst j
            have hn : y i ≠ f y := by
              rw [hy]
              simp only [y, Function.update_self]
              rw [hi]
              cases f x <;> decide
            simp [active, hn]
          · simp [active, y, hy, e]
        have hsmall : (active y).card < m := by
          rw [hactive, Finset.card_erase_of_mem hmem, ← hm]
          exact Nat.sub_lt (Finset.card_pos.mpr ⟨i, hmem⟩) (by decide)
        have good : g y = f x := (ih _ hsmall y rfl).trans hy
        cases fx : f x
        · have hxy : x ≤ y := by
            intro j
            by_cases e : j = i
            · subst j
              simp [y, hi, fx]
            · simp [y, Function.update_of_ne e]
          have u := hg hxy
          rw [good, fx] at u
          cases gx : g x
          · rfl
          · exact Bool.noConfusion ((boolLe _ _).mp u gx)
        · have hyx : y ≤ x := by
            intro j
            by_cases e : j = i
            · subst j
              simp [y, hi, fx]
            · simp [y, Function.update_of_ne e]
          have u := hg hyx
          rw [good, fx] at u
          exact (boolLe _ _).mp u rfl
  exact fun x => claim _ x rfl

end PEqualNP.Outside.L_meta_17376

open PEqualNP.Outside.L_meta_17376 in
theorem PEqualNP.Outside.L_meta_17376 : ∀ (x1 : ℕ) (x2 : (Fin x1 → Bool) → Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit), Monotone x2 → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x6 x7 = x2 x6 → x2 (Function.update x6 x7 !x6 x7) ≠ x2 x6) → PEqualNP.MetaComplexity.circuitFun x1 x3 x6 = x2 x6) → ∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x3 x7 = x2 x7 := by
  intro n f C _ hC h
  exact extreme f _ (circuitMono n C hC) h
