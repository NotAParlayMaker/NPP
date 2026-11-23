import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1101_aux

open PEqualNP.CircuitLowerBounds

def st (n m : ℕ) : List Gate :=
  [⟨GateOp.and, [n + 3 * m, m + 1]⟩, ⟨GateOp.or, [n + 3 * m, m + 1]⟩,
    ⟨GateOp.or, [n + 3 * m + 1, n + 3 * m + 2]⟩]

def G (n : ℕ) : ℕ → List Gate
  | 0 => [⟨GateOp.or, [0]⟩, ⟨GateOp.or, []⟩]
  | m + 1 => G n m ++ st n m

def stepf (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem G_len (n m : ℕ) : (G n m).length = 3 * m + 2 := by
  induction m with
  | zero => simp [G]
  | succ m ih => simp [G, st, ih]; omega

theorem G_ok (n m : ℕ) : ∀ g ∈ G n m, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction m with
  | zero => simp [G]
  | succ m ih =>
    intro g hg
    simp only [G, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih g hg
    · simp [st] at hg; rcases hg with rfl | rfl | rfl <;> simp

theorem gl (l r : List Bool) (i : ℕ) (h : i < l.length) : (l ++ r).getD i false = l.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gr (l r : List Bool) (k : ℕ) : (l ++ r).getD (l.length + k) false = r.getD k false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp

theorem stepeq (W : List Bool) (n m : ℕ) (hW : W.length = n + 3 * m + 2) :
    (st n m).foldl stepf W = W ++ [W.getD (n + 3 * m) false && W.getD (m + 1) false,
      W.getD (n + 3 * m) false || W.getD (m + 1) false,
      W.getD (n + 3 * m + 1) false || (W.getD (n + 3 * m) false && W.getD (m + 1) false)] := by
  simp only [st, List.foldl_cons, List.foldl_nil, stepf, List.map_cons, List.map_nil, GateOp.eval,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
  rw [gl W _ (n + 3 * m) (by omega), gl W _ (m + 1) (by omega),
    gl (W ++ _) _ (n + 3 * m + 1) (by simp; omega), gl W _ (n + 3 * m + 1) (by omega)]
  generalize W.getD (n + 3 * m) false = a
  generalize W.getD (m + 1) false = y
  generalize W.getD (n + 3 * m + 1) false = t
  rw [gl _ _ (n + 3 * m + 2) (by simp; omega)]
  have := gr W [a && y] 0
  rw [hW] at this
  simp only [Nat.add_zero, List.getD_cons_zero] at this
  rw [this]
  simp

theorem key (l : List Bool) (b : Bool) :
    (decide (2 ≤ l.count true) || (l.any id && b)) = decide (2 ≤ (l ++ [b]).count true) := by
  have hc : l.any id = decide (1 ≤ l.count true) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff, Nat.one_le_iff_ne_zero, Ne,
      List.count_eq_zero]
    simp
  rw [hc, List.count_append]
  generalize l.count true = c
  cases b <;> simp <;> omega

theorem key2 (l : List Bool) (b : Bool) : (l.any id || b) = (l ++ [b]).any id := by
  simp

theorem inv (x : List Bool) (m : ℕ) (hm : m < x.length) :
    ((G x.length m).foldl stepf x).length = x.length + 3 * m + 2 ∧
    (∀ i < x.length, ((G x.length m).foldl stepf x).getD i false = x.getD i false) ∧
    ((G x.length m).foldl stepf x).getD (x.length + 3 * m) false = (x.take (m + 1)).any id ∧
    ((G x.length m).foldl stepf x).getD (x.length + 3 * m + 1) false
      = decide (2 ≤ (x.take (m + 1)).count true) := by
  induction m with
  | zero =>
    have hW : (G x.length 0).foldl stepf x = x ++ [x.getD 0 false, false] := by
      simp [G, stepf, GateOp.eval]
    rw [hW]
    refine ⟨by simp, fun i hi => gl _ _ _ hi, ?_, ?_⟩
    · have := gr x [x.getD 0 false, false] 0
      simp only [Nat.add_zero] at this
      rw [Nat.mul_zero, Nat.add_zero, this]
      rcases x with _ | ⟨b, x⟩
      · simp at hm
      · simp
    · have := gr x [x.getD 0 false, false] 1
      rw [Nat.mul_zero, Nat.add_zero, this]
      rcases x with _ | ⟨b, x⟩
      · simp at hm
      · cases b <;> simp
  | succ m ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    have hx := h2 (m + 1) hm
    have hW := stepeq _ x.length m h1
    simp only [G, List.foldl_append]
    rw [hW]
    set W := (G x.length m).foldl stepf x
    have ht : x.take (m + 1 + 1) = x.take (m + 1) ++ [x[m + 1]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hm]; rfl
    have hxe : x.getD (m + 1) false = x[m + 1] := by simp [hm]
    rw [hx, hxe, h3, h4]
    refine ⟨by simp [h1]; omega, fun i hi => by rw [gl _ _ _ (by omega)]; exact h2 i hi, ?_, ?_⟩
    · have := gr W [(List.take (m + 1) x).any id && x[m + 1],
        (List.take (m + 1) x).any id || x[m + 1],
        decide (2 ≤ List.count true (List.take (m + 1) x)) ||
          ((List.take (m + 1) x).any id && x[m + 1])] 1
      rw [h1] at this
      rw [show x.length + 3 * (m + 1) = x.length + 3 * m + 2 + 1 by ring, this, ht]
      exact key2 _ _
    · have := gr W [(List.take (m + 1) x).any id && x[m + 1],
        (List.take (m + 1) x).any id || x[m + 1],
        decide (2 ≤ List.count true (List.take (m + 1) x)) ||
          ((List.take (m + 1) x).any id && x[m + 1])] 2
      rw [h1] at this
      rw [show x.length + 3 * (m + 1) + 1 = x.length + 3 * m + 2 + 2 by ring, this]
      rw [ht]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      exact key _ _

end PEqualNP.Outside.L_meta_1101_aux

open PEqualNP.Outside.L_meta_1101_aux in
theorem PEqualNP.Outside.L_meta_1101 : ∀ n : ℕ, 2 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.size ≤ 3 * n ∧ ∀ x : List Bool, x.length = n → (C.eval x = true ↔ 2 ≤ x.count true) := by
  intro n hn
  refine ⟨⟨G n (n - 1), n + 3 * (n - 1) + 1⟩, fun g hg => (G_ok n _ g hg).1,
    fun g hg => (G_ok n _ g hg).2, ?_, ?_⟩
  · show (G n (n - 1)).length ≤ 3 * n
    rw [G_len]; omega
  · intro x hx
    subst hx
    obtain ⟨-, -, -, h4⟩ := inv x (x.length - 1) (by omega)
    show ((G x.length (x.length - 1)).foldl stepf x).getD _ false = true ↔ _
    rw [h4, show x.length - 1 + 1 = x.length by omega, List.take_length]
    simp
