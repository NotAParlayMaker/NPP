import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_627

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_snoc_eq (w : List Bool) (b : Bool) (i : ℕ) (hi : i = w.length) :
    (w ++ [b]).getD i false = b := by
  subst hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_snoc_lt _ _ _ hi

-- The eight gates appended after a circuit whose wires are w, with L = w.length.
def tail8 (L o1 o2 u v : ℕ) : List Gate :=
  [⟨GateOp.or, [u, v]⟩, ⟨GateOp.and, [u, v]⟩, ⟨GateOp.not, [L + 1]⟩, ⟨GateOp.and, [L, L + 2]⟩,
   ⟨GateOp.not, [L + 3]⟩, ⟨GateOp.and, [o1, L + 4]⟩, ⟨GateOp.and, [o2, L + 3]⟩,
   ⟨GateOp.or, [L + 5, L + 6]⟩]

-- Reading a wire index o at a moment when the list has length L + k: it reads w at o when
-- o is below L, and false when o is at least L + k.
lemma read_old (w t : List Bool) (o : ℕ) (ho : o < w.length ∨ w.length + t.length ≤ o) :
    (w ++ t).getD o false = w.getD o false := by
  rcases ho with ho | ho
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ho]
  · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by omega)]

lemma tail8_val (w : List Bool) (o1 o2 u v : ℕ) (hu : u < w.length) (hv : v < w.length)
    (ho1 : o1 < w.length ∨ w.length + 5 ≤ o1) (ho2 : o2 < w.length ∨ w.length + 6 ≤ o2) :
    ((tail8 w.length o1 o2 u v).foldl step w).getD (w.length + 7) false =
      ((w.getD o1 false && !((w.getD u false || w.getD v false) &&
          !(w.getD u false && w.getD v false))) ||
        (w.getD o2 false && ((w.getD u false || w.getD v false) &&
          !(w.getD u false && w.getD v false)))) := by
  have gr : ∀ (t : List Bool) (k : ℕ), (w ++ t).getD (w.length + k) false = t.getD k false := by
    intro t k
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
  have gr0 : ∀ (t : List Bool), (w ++ t).getD w.length false = t.getD 0 false := by
    intro t; simpa using gr t 0
  have gu : ∀ t : List Bool, (w ++ t).getD u false = w.getD u false := fun t => read_old w t u (Or.inl hu)
  have gv : ∀ t : List Bool, (w ++ t).getD v false = w.getD v false := fun t => read_old w t v (Or.inl hv)
  have g1 : ∀ t : List Bool, t.length = 5 → (w ++ t).getD o1 false = w.getD o1 false := by
    intro t ht; exact read_old w t o1 (by omega)
  have g2 : ∀ t : List Bool, t.length = 6 → (w ++ t).getD o2 false = w.getD o2 false := by
    intro t ht; exact read_old w t o2 (by omega)
  simp only [tail8, List.foldl_cons, List.foldl_nil, step, List.map_cons, List.map_nil,
    List.append_assoc, List.cons_append, List.nil_append]
  simp only [gr, gr0, gu, gv, GateOp.eval, List.getD_cons_succ,
    List.getD_cons_zero, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id,
    List.headD_cons, Bool.and_true, Bool.or_false]
  rw [g1, g2]
  all_goals simp

end PEqualNP.Outside.L_meta_627

theorem PEqualNP.Outside.L_meta_627 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n), (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o1 false = F (Function.update x u (x v)) ∧ (C.wires (List.ofFn x)).getD o2 false = F (Function.update x u (!(x v)))) → PEqualNP.MetaComplexity.HasCircuitSize n F (s + 8) := by
  intro n s F u v ⟨C, hC, hs, o1, o2, ho⟩
  obtain ⟨L, hL⟩ : ∃ L, L = n + C.gates.length := ⟨_, rfl⟩
  obtain ⟨o1', ho1'⟩ : ∃ o, o = if o1 < L then o1 else L + 8 := ⟨_, rfl⟩
  obtain ⟨o2', ho2'⟩ : ∃ o, o = if o2 < L then o2 else L + 8 := ⟨_, rfl⟩
  refine ⟨⟨C.gates ++ PEqualNP.Outside.L_meta_627.tail8 L o1' o2' u v, L + 7⟩, ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hC g hg
    · simp only [PEqualNP.Outside.L_meta_627.tail8, List.mem_cons, List.mem_nil_iff, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, PEqualNP.Outside.L_meta_627.tail8,
      List.length_cons, List.length_nil] at hs ⊢
    omega
  · intro x
    have hw : (C.wires (List.ofFn x)).length = L := by
      rw [PEqualNP.Outside.L_meta_627.wires_eq, PEqualNP.Outside.L_meta_627.foldl_step_len]; simp [hL]
    have hin : ∀ i : Fin n, (C.wires (List.ofFn x)).getD i false = x i := by
      intro i
      rw [PEqualNP.Outside.L_meta_627.wires_eq, PEqualNP.Outside.L_meta_627.foldl_step_prefix _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    have go1 : (C.wires (List.ofFn x)).getD o1' false = F (Function.update x u (x v)) := by
      rw [← (ho x).1]
      by_cases h : o1 < L
      · rw [ho1', if_pos h]
      · rw [ho1', if_neg h, PEqualNP.Outside.L_meta_627.getD_ge _ _ (by omega), PEqualNP.Outside.L_meta_627.getD_ge _ _ (by omega)]
    have go2 : (C.wires (List.ofFn x)).getD o2' false = F (Function.update x u (!(x v))) := by
      rw [← (ho x).2]
      by_cases h : o2 < L
      · rw [ho2', if_pos h]
      · rw [ho2', if_neg h, PEqualNP.Outside.L_meta_627.getD_ge _ _ (by omega), PEqualNP.Outside.L_meta_627.getD_ge _ _ (by omega)]
    have key := PEqualNP.Outside.L_meta_627.tail8_val (C.wires (List.ofFn x)) o1' o2' u v (by omega) (by omega)
      (by by_cases h : o1 < L <;> simp only [ho1', h, if_true, if_false] <;> omega)
      (by by_cases h : o2 < L <;> simp only [ho2', h, if_true, if_false] <;> omega)
    rw [hw] at key
    show (List.foldl _ (List.ofFn x) (C.gates ++ PEqualNP.Outside.L_meta_627.tail8 L o1' o2' u v)).getD (L + 7) false = F x
    rw [List.foldl_append]
    change ((PEqualNP.Outside.L_meta_627.tail8 L o1' o2' ↑u ↑v).foldl PEqualNP.Outside.L_meta_627.step (C.wires (List.ofFn x))).getD (L + 7) false = F x
    rw [key, hin u, hin v, go1, go2]
    by_cases h : x u = x v
    · rw [Function.update_eq_self_iff.mpr h.symm, h]
      cases x v <;> simp
    · have h2 : Function.update x u (!(x v)) = x :=
        Function.update_eq_self_iff.mpr (by cases hu : x u <;> cases hv : x v <;> simp_all)
      rw [h2]
      cases hu : x u <;> cases hv : x v <;> simp_all
