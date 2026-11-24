import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2802_aux

open PEqualNP.CircuitLowerBounds

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

theorem pre (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl stepF w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (stepF w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [stepF]

theorem getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl stepF x).getD i false = x.getD i false := by
  obtain ⟨t, ht, _⟩ := pre gs x
  rw [ht]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def agree (p : ℕ → Bool) (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i < a.length, p i = false → a.getD i false = b.getD i false

theorem agree_all (p : ℕ → Bool) (a b : List Bool) (h : agree p a b) (i : ℕ) (hi : p i = false) :
    a.getD i false = b.getD i false := by
  by_cases hl : i < a.length
  · exact h.2 i hl hi
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by have := h.1; omega)]

theorem agree_step (p : ℕ → Bool) (a b : List Bool) (g : Gate) (h : agree p a b)
    (hg : ∀ i ∈ g.inputs, p i = false) : agree p (stepF a g) (stepF b g) := by
  have hv : (g.inputs.map fun i => a.getD i false) = (g.inputs.map fun i => b.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact agree_all p a b h i (hg i hi)
  have hl := h.1
  refine ⟨by simp [stepF, hl], ?_⟩
  intro i hi hpi
  have h1 := agree_all p a b h i hpi
  simp only [stepF, List.length_append, List.length_singleton] at hi
  simp only [stepF, hv, List.getD_eq_getElem?_getD, List.getElem?_append] at h1 ⊢
  simp only [List.getD_eq_getElem?_getD] at hv
  rw [← hl, hv]
  split
  · exact h1
  · rfl

theorem agree_fold (p : ℕ → Bool) (gs : List Gate) : ∀ (a b : List Bool), agree p a b →
    (∀ g ∈ gs, ∀ i ∈ g.inputs, p i = false) → agree p (gs.foldl stepF a) (gs.foldl stepF b) := by
  induction gs with
  | nil => intro a b h _; exact h
  | cons g gs ih =>
    intro a b h hg
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ (agree_step p a b g h (hg g (by simp))) (fun g2 hg2 => hg g2 (by simp [hg2]))

theorem indep (C : Circuit) (p : ℕ → Bool)
    (hS : ∀ k, p k = true → k ∉ C.output :: C.gates.flatMap Gate.inputs)
    (a b : List Bool) (h : agree p a b) : C.eval a = C.eval b := by
  simp only [Circuit.eval, wires_eq]
  apply agree_all p _ _ (agree_fold p C.gates a b h _)
  · by_contra hc
    exact hS C.output (by simpa using hc) (by simp)
  · intro g hg i hi
    by_contra hc
    exact hS i (by simpa using hc) (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, hi⟩))

def f (x1 : Fin 9 → Bool) : Bool :=
  x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))

def inp (x2 : Fin 9 → Bool) : List Bool :=
  List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]

def pt (i j : ℕ) : Fin 9 → Bool := fun k => k.val == i || k.val == j

theorem inp_eq (x : Fin 9 → Bool) :
    inp x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 0 || x 6] := by
  simp [inp, List.ofFn_succ]

theorem cnt (L : List ℕ) : List.countP (fun (x5 : ℕ) => Decidable.decide (x5 < (10 : ℕ))) L =
    L.count 0 + L.count 1 + L.count 2 + L.count 3 + L.count 4 + L.count 5 + L.count 6 +
      L.count 7 + L.count 8 + L.count 9 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain h | h : a < 10 ∨ 10 ≤ a := by omega
    · interval_cases a <;> simp [ih, List.count_cons] <;> omega
    · have h0 : ¬ a < 10 := by omega
      simp only [List.countP_cons, List.count_cons, ih, h0, decide_false, beq_iff_eq]
      simp only [if_neg (show ¬ a = 0 by omega), if_neg (show ¬ a = 1 by omega), if_neg (show ¬ a = 2 by omega), if_neg (show ¬ a = 3 by omega), if_neg (show ¬ a = 4 by omega), if_neg (show ¬ a = 5 by omega), if_neg (show ¬ a = 6 by omega), if_neg (show ¬ a = 7 by omega), if_neg (show ¬ a = 8 by omega), if_neg (show ¬ a = 9 by omega), Nat.add_zero, Bool.false_eq_true, if_false]

theorem dep (C : Circuit) (h : ∀ x, C.eval (inp x) = f x) (i j : ℕ)
    (hf : f (pt i j) ≠ f (pt j j)) (ha : agree (fun k => k == i) (inp (pt i j)) (inp (pt j j)))
    (ho : C.output ≠ i) : List.count i (C.gates.flatMap Gate.inputs) ≠ 0 := by
  intro hc
  apply hf
  rw [← h, ← h]
  apply indep C _ _ _ _ ha
  intro k hk
  have hk2 : k = i := by simpa using hk
  subst hk2
  simp only [List.mem_cons, not_or]
  exact ⟨fun e => ho e.symm, List.count_eq_zero.mp hc⟩

theorem outne (C : Circuit) (h : ∀ x, C.eval (inp x) = f x) (i : ℕ) (hi : i < 10)
    (hf : f (pt i i) ≠ (inp (pt i i)).getD i false) : C.output ≠ i := by
  intro e
  apply hf
  rw [← h]
  simp only [Circuit.eval, wires_eq, e]
  exact getD_lt _ _ _ (by simpa [inp] using hi)

theorem two (C : Circuit) (h : ∀ x, C.eval (inp x) = f x) (a b : ℕ) (x y : Fin 9 → Bool)
    (hf : f x ≠ f y) (ha : agree (fun k => k == a || k == b) (inp x) (inp y))
    (h1 : List.count a (C.output :: C.gates.flatMap Gate.inputs) = 0)
    (h2 : List.count b (C.output :: C.gates.flatMap Gate.inputs) = 0) : False := by
  apply hf
  rw [← h, ← h]
  apply indep C _ _ _ _ ha
  intro k hk
  have hk2 : k = a ∨ k = b := by simpa using hk
  rcases hk2 with e | e
  · subst e
    exact List.count_eq_zero.mp h1
  · subst e
    exact List.count_eq_zero.mp h2

theorem core : ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin (9 : ℕ) → Bool), x3.eval (inp x4) = f x4) → List.countP (fun (x5 : ℕ) => Decidable.decide (x5 < (10 : ℕ))) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates) ≤ (15 : ℕ) → ∃ (x6 : Fin (9 : ℕ)), x6 ≠ (0 : Fin (9 : ℕ)) ∧ x6 ≠ (6 : Fin (9 : ℕ)) ∧ x3.output ≠ ↑x6 ∧ List.count (↑x6) (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates) = (1 : ℕ) := by
  intro C h hc
  by_contra hno
  push_neg at hno
  rw [cnt] at hc
  have o1 := outne C h 1 (by omega) (by simp [inp_eq, f, pt])
  have o2 := outne C h 2 (by omega) (by simp [inp_eq, f, pt])
  have o3 := outne C h 3 (by omega) (by simp [inp_eq, f, pt])
  have o4 := outne C h 4 (by omega) (by simp [inp_eq, f, pt])
  have o5 := outne C h 5 (by omega) (by simp [inp_eq, f, pt])
  have o7 := outne C h 7 (by omega) (by simp [inp_eq, f, pt])
  have o8 := outne C h 8 (by omega) (by simp [inp_eq, f, pt])
  have d1 := dep C h 1 2 (by simp [f, pt]) (by rw [inp_eq, inp_eq]; exact ⟨rfl, by decide⟩) o1
  have d2 := dep C h 2 1 (by simp [f, pt]) (by rw [inp_eq, inp_eq]; exact ⟨rfl, by decide⟩) o2
  have d3 := dep C h 3 2 (by simp [f, pt]) (by rw [inp_eq, inp_eq]; exact ⟨rfl, by decide⟩) o3
  have d4 := dep C h 4 3 (by simp [f, pt]) (by rw [inp_eq, inp_eq]; exact ⟨rfl, by decide⟩) o4
  have d5 := dep C h 5 7 (by simp [f, pt]) (by rw [inp_eq, inp_eq]; exact ⟨rfl, by decide⟩) o5
  have d7 := dep C h 7 5 (by simp [f, pt]) (by rw [inp_eq, inp_eq]; exact ⟨rfl, by decide⟩) o7
  have d8 := dep C h 8 5 (by simp [f, pt]) (by rw [inp_eq, inp_eq]; exact ⟨rfl, by decide⟩) o8
  have n1 : List.count 1 (C.gates.flatMap Gate.inputs) ≠ 1 := hno 1 (by decide) (by decide) o1
  have n2 : List.count 2 (C.gates.flatMap Gate.inputs) ≠ 1 := hno 2 (by decide) (by decide) o2
  have n3 : List.count 3 (C.gates.flatMap Gate.inputs) ≠ 1 := hno 3 (by decide) (by decide) o3
  have n4 : List.count 4 (C.gates.flatMap Gate.inputs) ≠ 1 := hno 4 (by decide) (by decide) o4
  have n5 : List.count 5 (C.gates.flatMap Gate.inputs) ≠ 1 := hno 5 (by decide) (by decide) o5
  have n7 : List.count 7 (C.gates.flatMap Gate.inputs) ≠ 1 := hno 7 (by decide) (by decide) o7
  have n8 : List.count 8 (C.gates.flatMap Gate.inputs) ≠ 1 := hno 8 (by decide) (by decide) o8
  have c1 := List.count_le_count_cons (a := 1) (b := C.output) (l := C.gates.flatMap Gate.inputs)
  have c2 := List.count_le_count_cons (a := 2) (b := C.output) (l := C.gates.flatMap Gate.inputs)
  have c3 := List.count_le_count_cons (a := 3) (b := C.output) (l := C.gates.flatMap Gate.inputs)
  have c4 := List.count_le_count_cons (a := 4) (b := C.output) (l := C.gates.flatMap Gate.inputs)
  have c5 := List.count_le_count_cons (a := 5) (b := C.output) (l := C.gates.flatMap Gate.inputs)
  have c7 := List.count_le_count_cons (a := 7) (b := C.output) (l := C.gates.flatMap Gate.inputs)
  have c8 := List.count_le_count_cons (a := 8) (b := C.output) (l := C.gates.flatMap Gate.inputs)
  have hz : (List.count 0 (C.output :: C.gates.flatMap Gate.inputs) = 0 ∧
        List.count 6 (C.output :: C.gates.flatMap Gate.inputs) = 0) ∨
      (List.count 0 (C.output :: C.gates.flatMap Gate.inputs) = 0 ∧
        List.count 9 (C.output :: C.gates.flatMap Gate.inputs) = 0) ∨
      (List.count 6 (C.output :: C.gates.flatMap Gate.inputs) = 0 ∧
        List.count 9 (C.output :: C.gates.flatMap Gate.inputs) = 0) := by omega
  rcases hz with ⟨z1, z2⟩ | ⟨z1, z2⟩ | ⟨z1, z2⟩
  · exact two C h 0 6 (pt 0 5) (pt 6 5) (by simp [f, pt])
      (by rw [inp_eq, inp_eq]; exact ⟨rfl, by decide⟩) z1 z2
  · exact two C h 0 9 (pt 0 1) (pt 1 1) (by simp [f, pt])
      (by rw [inp_eq, inp_eq]; exact ⟨rfl, by decide⟩) z1 z2
  · exact two C h 6 9 (pt 6 1) (pt 1 1) (by simp [f, pt])
      (by rw [inp_eq, inp_eq]; exact ⟨rfl, by decide⟩) z1 z2

end PEqualNP.Outside.L_meta_2802_aux

theorem PEqualNP.Outside.L_meta_2802 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin (9 : ℕ) → Bool), x3.eval (x2 x4) = x1 x4) → List.countP (fun (x5 : ℕ) => Decidable.decide (x5 < (10 : ℕ))) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates) ≤ (15 : ℕ) → ∃ (x6 : Fin (9 : ℕ)), x6 ≠ (0 : Fin (9 : ℕ)) ∧ x6 ≠ (6 : Fin (9 : ℕ)) ∧ x3.output ≠ ↑x6 ∧ List.count (↑x6) (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates) = (1 : ℕ) := by
  exact PEqualNP.Outside.L_meta_2802_aux.core
