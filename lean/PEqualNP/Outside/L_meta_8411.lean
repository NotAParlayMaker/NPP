import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8411_aux

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def Good (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
    ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

theorem fold_pre (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by simp only [List.foldl]; rw [ht, List.append_assoc]⟩

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl]; rw [ih]; simp; omega

theorem W_len (n : ℕ) (gs : List Gate) (x8 : Fin n → Bool) : (W gs (List.ofFn x8)).length = n + gs.length := by
  unfold W; rw [fold_len]; simp

theorem W_app (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_in (n : ℕ) (gs : List Gate) (x8 : Fin n → Bool) (i : Fin n) :
    (W gs (List.ofFn x8)).getD i.val false = x8 i := by
  unfold W
  obtain ⟨t, ht⟩ := fold_pre gs (List.ofFn x8)
  rw [ht, List.getD_append _ _ _ _ (by simp)]
  simp

theorem W_pre (n : ℕ) (gs : List Gate) (g : Gate) (x8 : Fin n → Bool) (i : ℕ) (hi : i < n + gs.length) :
    (W (gs ++ [g]) (List.ofFn x8)).getD i false = (W gs (List.ofFn x8)).getD i false := by
  rw [W_app, List.getD_append _ _ _ _ (by rw [W_len]; exact hi)]

theorem W_last (n : ℕ) (gs : List Gate) (g : Gate) (x8 : Fin n → Bool) :
    (W (gs ++ [g]) (List.ofFn x8)).getD (n + gs.length) false =
      g.op.eval (g.inputs.map fun i => (W gs (List.ofFn x8)).getD i false) := by
  rw [W_app, List.getD_append_right _ _ _ _ (by rw [W_len]), W_len, Nat.sub_self]
  simp

theorem Good_app (n : ℕ) (gs : List Gate) (g : Gate) (hg : Good n gs)
    (h1 : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (h2 : g.inputs.length ≤ 2)
    (h3 : ∀ i ∈ g.inputs, i < n + gs.length) : Good n (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hg.1 g' h
    · simp at h; subst h; exact ⟨h1, h2⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < gs.length
    · rw [List.getD_append _ _ _ _ hjl] at hi
      exact hg.2 j hjl i hi
    · have hj' : j = gs.length := by omega
      subst hj'
      rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self] at hi
      simp at hi
      exact h3 i hi

theorem chain (n : ℕ) (L : List (Fin n)) : ∀ (gs : List Gate) (w : ℕ), Good n gs → w < n + gs.length →
    ∃ gs' : List Gate, Good n gs' ∧ gs'.length = gs.length + L.length ∧ ∃ w' < n + gs'.length,
      (∀ x8 : Fin n → Bool, (W gs' (List.ofFn x8)).getD w' false = ((W gs (List.ofFn x8)).getD w false || L.any x8)) ∧
      ∀ x8 : Fin n → Bool, ∀ i < n + gs.length, (W gs' (List.ofFn x8)).getD i false = (W gs (List.ofFn x8)).getD i false := by
  induction L with
  | nil => intro gs w hg hw; exact ⟨gs, hg, by simp, w, hw, by simp, by simp⟩
  | cons l L ih =>
    intro gs w hg hw
    have hg1 : Good n (gs ++ [⟨GateOp.or, [w, l.val]⟩]) :=
      Good_app n gs _ hg (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
    obtain ⟨gs', hg', hl', w', hw', hv, hp⟩ := ih _ (n + gs.length) hg1 (by simp)
    refine ⟨gs', hg', by simp [hl']; omega, w', hw', ?_, ?_⟩
    · intro x8
      rw [hv x8, W_last]
      have hl := W_in n gs x8 l
      rw [List.getD_eq_getElem?_getD] at hl
      simp [GateOp.eval, Bool.or_assoc, hl]
    · intro x8 i hi
      rw [hp x8 i (by simp; omega), W_pre n gs _ x8 i hi]

theorem entry (n : ℕ) (e : Fin n × List (Fin n)) (gs : List Gate) (o : ℕ) (hg : Good n gs) (ho : o < n + gs.length) :
    ∃ (gs' : List Gate) (o' : ℕ), Good n gs' ∧ o' < n + gs'.length ∧ gs'.length ≤ gs.length + (e.2.length + 1) ∧
      ∀ x8 : Fin n → Bool, (W gs' (List.ofFn x8)).getD o' false = ((W gs (List.ofFn x8)).getD o false || (x8 e.1 && e.2.any x8)) := by
  obtain ⟨a, L⟩ := e
  cases L with
  | nil => exact ⟨gs, o, hg, ho, by simp, by simp⟩
  | cons l L =>
    obtain ⟨g1, hg1, hl1, w1, hw1, hv1, hp1⟩ := chain n L gs l.val hg (by omega)
    have hg2 : Good n (g1 ++ [(⟨GateOp.and, [w1, a.val]⟩ : Gate)]) :=
      Good_app n g1 _ hg1 (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
    have hg3 : Good n ((g1 ++ [(⟨GateOp.and, [w1, a.val]⟩ : Gate)]) ++ [⟨GateOp.or, [o, n + g1.length]⟩]) :=
      Good_app n _ _ hg2 (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> omega)
    refine ⟨_, n + (g1 ++ [(⟨GateOp.and, [w1, a.val]⟩ : Gate)]).length, hg3, by simp, by simp [hl1]; omega, ?_⟩
    intro x8
    rw [W_last]
    have e1 : (W (g1 ++ [(⟨GateOp.and, [w1, a.val]⟩ : Gate)]) (List.ofFn x8)).getD o false = (W gs (List.ofFn x8)).getD o false := by
      rw [W_pre n g1 _ x8 o (by omega), hp1 x8 o ho]
    have e2 : (W (g1 ++ [(⟨GateOp.and, [w1, a.val]⟩ : Gate)]) (List.ofFn x8)).getD (n + g1.length) false =
        ((x8 l || L.any x8) && x8 a) := by
      rw [W_last]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
      rw [hv1 x8, W_in, W_in, Bool.and_true]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
    rw [e1, e2]
    cases x8 a <;> simp

theorem main (n : ℕ) (x3 : List (Fin n × List (Fin n))) : ∀ (gs : List Gate) (o : ℕ), Good n gs → o < n + gs.length →
    ∃ (gs' : List Gate) (o' : ℕ), Good n gs' ∧ o' < n + gs'.length ∧
      gs'.length ≤ gs.length + (x3.map fun e => e.2.length + 1).sum ∧
      ∀ x8 : Fin n → Bool, (W gs' (List.ofFn x8)).getD o' false =
        ((W gs (List.ofFn x8)).getD o false || x3.any fun e => x8 e.1 && e.2.any x8) := by
  induction x3 with
  | nil => intro gs o hg ho; exact ⟨gs, o, hg, ho, by simp, by simp⟩
  | cons e r ih =>
    intro gs o hg ho
    obtain ⟨g1, o1, hg1, ho1, hl1, hv1⟩ := entry n e gs o hg ho
    obtain ⟨g2, o2, hg2, ho2, hl2, hv2⟩ := ih g1 o1 hg1 ho1
    refine ⟨g2, o2, hg2, ho2, by simp only [List.map_cons, List.sum_cons]; omega, ?_⟩
    intro x8
    rw [hv2 x8, hv1 x8]
    simp [Bool.or_assoc]

end PEqualNP.Outside.L_meta_8411_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_8411_aux in
theorem PEqualNP.Outside.L_meta_8411 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Fin x1 × List (Fin x1))), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x2.output < x1 + x2.size → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 ∧ x7.size ≤ x2.size + (List.map (fun (x8 : Fin x1 × List (Fin x1)) => x8.2.length + (1 : ℕ)) x3).sum ∧ ∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8) = (x2.eval (List.ofFn x8) || x3.any fun (x9 : Fin x1 × List (Fin x1)) => x8 x9.1 && x9.2.any x8) := by
  intro n C x3 hm hr ho
  have hG : Good n C.gates := by unfold Good; exact ⟨hm, hr⟩
  obtain ⟨gs, o, hg, -, hl, hv⟩ := main n x3 C.gates C.output hG ho
  refine ⟨⟨gs, o⟩, ?_, ?_, ?_, ?_⟩
  · exact hg.1
  · exact hg.2
  · exact hl
  · intro x8
    exact hv x8
