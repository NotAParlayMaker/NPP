import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18081

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem mono (gs : List Gate) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro i hi; exact h i hi
  | append_singleton gs g ih =>
    intro i hi
    have ih' := ih (fun g hg' => hg g (by simp [hg']))
    have l1 := run_length gs x
    have l2 := run_length gs y
    rw [run_snoc] at hi ⊢
    rcases Nat.lt_trichotomy i (x.length + gs.length) with hlt | heq | hgt
    · rw [getD_lt _ _ _ (by omega)] at hi ⊢; exact ih' i hi
    · have e1 : i = (run gs x).length := by omega
      have e2 : i = (run gs y).length := by omega
      have hi' : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) = true := by
        rw [← getD_at (run gs x) (g.op.eval (g.inputs.map fun i => (run gs x).getD i false)), ← e1]
        exact hi
      rw [e2, getD_at]
      rcases hg g (by simp) with ho | ho
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi' ⊢
        exact fun q hq => ih' q (hi' q hq)
      · rw [ho] at hi' ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi' ⊢
        obtain ⟨q, h1, h2⟩ := hi'
        exact ⟨q, h1, ih' q h2⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi


theorem mapRise {α : Type} (f g : α → Bool) (h : ∀ a, f a = true → g a = true)
    (l : List α) : ∀ i, (l.map f).getD i false = true → (l.map g).getD i false = true := by
  induction l with
  | nil => intro i h; simp at h
  | cons a l ih =>
    intro i
    cases i with
    | zero => exact h a
    | succ i => exact ih i

def inp (l : List (Fin 26)) (A B : Finset (Fin 13)) : List Bool :=
  l.map fun i => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ A) else decide (Fin.ofNat 13 i.val ∈ B)

theorem subsetEval (C : Circuit) (hm : Monotone2 C) (l : List (Fin 26))
    {A B D E : Finset (Fin 13)} (hA : A ⊆ D) (hB : B ⊆ E) :
    C.eval (inp l A B) = true → C.eval (inp l D E) = true := by
  apply mono C.gates (inp l A B) (inp l D E) (by simp [inp]) _ (fun g hg => by simpa using (hm g hg).1) C.output
  apply mapRise
  intro i hi
  by_cases h : i.val < 13
  · simp [h] at hi ⊢
    exact hA hi
  · simp [h] at hi ⊢
    exact hB hi

end PEqualNP.Outside.L_meta_18081

open PEqualNP.Outside.L_meta_18081

theorem PEqualNP.Outside.L_meta_18081 : ∀ (x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool) (x2 : List (Fin (26 : ℕ))) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x3 →     have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => List.map (fun (x7 : Fin (26 : ℕ)) => if ↑x7 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x6)) x2;     (∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 = Bool.true → x3.eval (x5 {x6} {x7}) = Bool.true) → (∀ (x7 : Finset (Fin (13 : ℕ))), x3.eval (x5 x7 {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, x1 x9 x8 = Bool.false}) = Bool.false) → ∀ (x8 x9 : Finset (Fin (13 : ℕ))), x3.eval (x5 x8 x9) = Bool.true ↔ ∃ x10 ∈ x8, ∃ x11 ∈ x9, x1 x10 x11 = Bool.true := by
  intro inc l C hmono encoded hpos hneg S T
  constructor
  · intro ht
    by_contra hn
    let Z : Finset (Fin 13) := {j | ∀ i ∈ S, inc i j = false}
    have sub : T ⊆ Z := by
      intro j hj
      simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      cases e : inc i j with
      | false => rfl
      | true => exact False.elim (hn ⟨i, hi, j, hj, e⟩)
    have bad : C.eval (inp l S Z) = false := hneg S
    have good : C.eval (inp l S Z) = true := subsetEval C hmono l (Finset.Subset.refl S) sub ht
    rw [bad] at good
    contradiction
  · rintro ⟨i, hi, j, hj, h⟩
    exact subsetEval C hmono l (Finset.singleton_subset_iff.mpr hi) (Finset.singleton_subset_iff.mpr hj) (hpos i j h)
