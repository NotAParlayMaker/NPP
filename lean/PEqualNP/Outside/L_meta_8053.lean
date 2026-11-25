import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8053

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

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



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


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8053

theorem PEqualNP.Outside.L_meta_8053 : have x1 : (Fin (42 : ℕ) → Bool) → List Bool := fun (x1 : Fin (42 : ℕ) → Bool) =>   have x2 : Fin (7 : ℕ) → ℕ → Bool := fun (x2 : Fin (7 : ℕ)) (x3 : ℕ) => x1 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x2 + x3) % (21 : ℕ)));   (List.ofFn x1 ++ List.ofFn fun (x3 : Fin (7 : ℕ)) => x2 x3 (5 : ℕ) || x2 x3 (17 : ℕ)) ++ List.ofFn fun (x3 : Fin (7 : ℕ)) => x2 x3 (5 : ℕ) || x2 x3 (17 : ℕ) || x2 x3 (20 : ℕ); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → Monotone fun (x4 : Fin (42 : ℕ) → Bool) => x2.eval (x1 x4) := by
  intro E C hC x y hxy
  have le : ∀ i, x i = true → y i = true := fun i h => Bool.le_iff_imp.1 (hxy i) h
  have f2 : ∀ {m : ℕ} (f g : Fin m → Bool), (∀ i, f i = true → g i = true) → ∀ i, (List.ofFn f).getD i false = true → (List.ofFn g).getD i false = true := by
    intro m f g h i hi
    by_cases hin : i < m
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin, dite_true, Option.getD_some] at hi ⊢
      exact h _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi
  have app : ∀ l l' k k' : List Bool, l.length = l'.length → (∀ i, l.getD i false = true → l'.getD i false = true) → (∀ i, k.getD i false = true → k'.getD i false = true) → ∀ i, (l ++ k).getD i false = true → (l' ++ k').getD i false = true := by
    intro l l' k k' hl h1 h2 i hi
    rcases Nat.lt_or_ge i l.length with h | h
    · rw [List.getD_append _ _ _ _ h] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact h1 i hi
    · rw [List.getD_append_right _ _ _ _ h] at hi
      rw [List.getD_append_right _ _ _ _ (by omega), ← hl]
      exact h2 _ hi
  refine Bool.le_iff_imp.2 fun h => ?_
  refine PEqualNP.Outside.L_meta_8053.mono C.gates (E x) (E y) (by simp [E]) ?_ (fun g hg => by simpa using (hC g hg).1) C.output h
  refine app _ _ _ _ (by simp) (app _ _ _ _ (by simp) (f2 _ _ le) (f2 _ _ fun i hi => ?_)) (f2 _ _ fun i hi => ?_)
  · simp only [Bool.or_eq_true] at hi ⊢
    exact hi.imp (le _) (le _)
  · simp only [Bool.or_eq_true] at hi ⊢
    exact hi.imp (Or.imp (le _) (le _)) (le _)
