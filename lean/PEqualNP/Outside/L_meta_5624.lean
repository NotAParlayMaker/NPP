import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5624

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The argument. The graph joins left 0 to right 2 and 3, and left 1 and 2 to right 0 and 1.
-- Upper half: x0 (y2 + y3) + (x1 + x2) (y0 + y1), six gates.
-- Lower half: on the sixteen rows a monotone circuit must read each of the seven inputs
-- x0, x1, x2, y0, y1, y2, y3 (each has a row with value 1 and a row with value 0 that agree
-- outside that input, and monotonicity transports the 1). The backward cone of the output,
-- built top down, gains at most two wires per gate in it, so it has at most 1 + 2 g elements
-- when g of its elements are gates, and at least 7 + g. Hence g is at least 6.

-- The wire list as a fold (as in the checked file L_meta_5465).
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

-- The backward cone, built from the top gate down.
def dflt : Gate := ⟨GateOp.or, []⟩

def P (gs : List Gate) (t : ℕ) : Finset ℕ :=
  ((gs.getD t dflt).inputs.filter (fun i => decide (i < 8 + t))).toFinset

def rel (gs : List Gate) : ℕ → Finset ℕ → Finset ℕ
  | 0, S => S
  | t + 1, S => rel gs t (if 8 + t ∈ S then S ∪ P gs t else S)

theorem rel_zero (gs : List Gate) (S : Finset ℕ) : rel gs 0 S = S := rfl

theorem rel_succ (gs : List Gate) (t : ℕ) (S : Finset ℕ) :
    rel gs (t + 1) S = rel gs t (if 8 + t ∈ S then S ∪ P gs t else S) := rfl

theorem P_lt (gs : List Gate) (t i : ℕ) (h : i ∈ P gs t) : i < 8 + t := by
  simp only [P, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

theorem rel_sup (gs : List Gate) : ∀ (t : ℕ) (S : Finset ℕ), S ⊆ rel gs t S
  | 0, S => by rw [rel_zero]
  | t + 1, S => by
    rw [rel_succ]
    refine Finset.Subset.trans ?_ (rel_sup gs t _)
    split_ifs
    · exact Finset.subset_union_left
    · exact Finset.Subset.refl S

theorem rel_small (gs : List Gate) :
    ∀ (t : ℕ) (S : Finset ℕ) (x : ℕ), x ∈ rel gs t S → x ∈ S ∨ x < 8 + t
  | 0, S, x, h => by rw [rel_zero] at h; exact Or.inl h
  | t + 1, S, x, h => by
    rw [rel_succ] at h
    rcases rel_small gs t _ x h with h1 | h1
    · split_ifs at h1
      · rcases Finset.mem_union.mp h1 with h2 | h2
        · exact Or.inl h2
        · have := P_lt gs t x h2; right; omega
      · exact Or.inl h1
    · right; omega

theorem rel_closed (gs : List Gate) :
    ∀ (t : ℕ) (S : Finset ℕ) (j : ℕ), j < t → 8 + j ∈ rel gs t S → P gs j ⊆ rel gs t S
  | 0, S, j, hj, _ => absurd hj (by omega)
  | t + 1, S, j, hj, h => by
    rw [rel_succ] at h ⊢
    by_cases hjt : j < t
    · exact rel_closed gs t _ j hjt h
    · have hjt' : j = t := by omega
      subst hjt'
      rcases rel_small gs j _ _ h with h1 | h1
      · by_cases hS : 8 + j ∈ S
        · rw [if_pos hS] at h1 ⊢
          exact Finset.Subset.trans Finset.subset_union_right (rel_sup gs j _)
        · rw [if_neg hS] at h1; exact absurd h1 hS
      · omega

theorem rel_card (gs : List Gate) (hP : ∀ j, (P gs j).card ≤ 2) :
    ∀ (t : ℕ) (S : Finset ℕ), (rel gs t S).card ≤
      S.card + 2 * ((Finset.range t).filter (fun j => 8 + j ∈ rel gs t S)).card
  | 0, S => by rw [rel_zero]; omega
  | t + 1, S => by
    rw [rel_succ]
    have IH := rel_card gs hP t (if 8 + t ∈ S then S ∪ P gs t else S)
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hS : 8 + t ∈ S
    · have hin : 8 + t ∈ rel gs t (if 8 + t ∈ S then S ∪ P gs t else S) := by
        apply rel_sup
        rw [if_pos hS]
        exact Finset.mem_union_left _ hS
      rw [if_pos hin, Finset.card_insert_of_notMem (by simp)]
      rw [if_pos hS] at IH ⊢
      have h1 := Finset.card_union_le S (P gs t)
      have h2 := hP t
      omega
    · rw [if_neg hS] at IH ⊢
      split_ifs
      · rw [Finset.card_insert_of_notMem (by simp)]
        omega
      · exact IH

theorem P_card (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ j, (P gs j).card ≤ 2 := by
  intro j
  refine (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans ?_)
  by_cases hj : j < gs.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact (hm _ (List.getElem_mem hj)).2
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [dflt]

-- Monotone transport along a closed set of wires.
theorem agree (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (R : Finset ℕ) (hR : ∀ j, j < gs.length → 8 + j ∈ R → P gs j ⊆ R)
    (X Y : List Bool) (hX : X.length = 8) (hY : Y.length = 8)
    (hXY : ∀ i ∈ R, i < 8 → X.getD i false = true → Y.getD i false = true) :
    ∀ k, k ∈ R → (W gs X).getD k false = true → (W gs Y).getD k false = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk hv
  by_cases h1 : k < 8
  · rw [W_prefix gs X k (by omega)] at hv
    rw [W_prefix gs Y k (by omega)]
    exact hXY k hk h1 hv
  by_cases h2 : k < 8 + gs.length
  · obtain ⟨j, rfl⟩ : ∃ j, k = 8 + j := ⟨k - 8, by omega⟩
    have hj : j < gs.length := by omega
    have hgx := W_gate gs X j hj
    have hgy := W_gate gs Y j hj
    rw [hX] at hgx
    rw [hY] at hgy
    rw [hgx] at hv
    rw [hgy]
    obtain ⟨hop, _⟩ := hm _ (List.getElem_mem hj)
    have hcl : ∀ i ∈ (gs[j]).inputs, i < 8 + j → i ∈ R := by
      intro i hi hlt
      apply hR j hj hk
      simp only [P, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      rw [List.getD_eq_getElem _ _ hj]
      exact ⟨hi, hlt⟩
    have key : ∀ i ∈ (gs[j]).inputs,
        (if i < 8 + j then (W gs X).getD i false else false) = true →
        (if i < 8 + j then (W gs Y).getD i false else false) = true := by
      intro i hi h
      by_cases hlt : i < 8 + j
      · rw [if_pos hlt] at h ⊢
        exact ih i (by omega) (hcl i hi hlt) h
      · rw [if_neg hlt] at h
        exact absurd h (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop
    · rw [hop, eval_and_iff] at hv ⊢
      exact fun i hi => key i hi (hv i hi)
    · rw [hop, eval_or_iff] at hv ⊢
      obtain ⟨i, hi, h⟩ := hv
      exact ⟨i, hi, key i hi h⟩
  · rw [W_ge gs X k (by rw [hX]; omega)] at hv
    exact absurd hv (by simp)

-- Every input whose flip changes a forced value lies in the cone of the output.
theorem need (C : Circuit) (hC : Monotone2 C) (z : ℕ) (X Y : List Bool)
    (hX : X.length = 8) (hY : Y.length = 8)
    (hXY : ∀ i, i < 8 → i ≠ z → X.getD i false = true → Y.getD i false = true)
    (h1 : C.eval X = true) (h2 : C.eval Y = false) :
    z ∈ rel C.gates C.gates.length {C.output} := by
  by_contra hz
  have hR : ∀ j, j < C.gates.length → 8 + j ∈ rel C.gates C.gates.length {C.output} →
      P C.gates j ⊆ rel C.gates C.gates.length {C.output} :=
    fun j hj h => rel_closed C.gates C.gates.length {C.output} j hj h
  have hXY' : ∀ i ∈ rel C.gates C.gates.length {C.output}, i < 8 →
      X.getD i false = true → Y.getD i false = true := by
    intro i hi hi8 hx
    exact hXY i hi8 (fun h => hz (h ▸ hi)) hx
  have ho : C.output ∈ rel C.gates C.gates.length {C.output} :=
    rel_sup C.gates C.gates.length {C.output} (Finset.mem_singleton_self _)
  have h3 := agree C.gates hC _ hR X Y hX hY hXY' C.output ho h1
  rw [eval_W] at h2
  rw [h2] at h3
  exact absurd h3 (by simp)

theorem lower :
    ¬ RepSizeAtMost (fun u v : Fin 4 => (828 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  rintro ⟨C, hC, hs, hrep⟩
  have hz : ∀ z ∈ ({0, 1, 2, 4, 5, 6, 7} : Finset ℕ),
      z ∈ rel C.gates C.gates.length {C.output} := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact need C hC 0 (oneEach (0 : Fin 4) (2 : Fin 4)) (oneEach (1 : Fin 4) (2 : Fin 4))
        (by decide) (by decide) (by decide) ((hrep 0 2).trans (by decide)) ((hrep 1 2).trans (by decide))
    · exact need C hC 1 (oneEach (1 : Fin 4) (0 : Fin 4)) (oneEach (0 : Fin 4) (0 : Fin 4))
        (by decide) (by decide) (by decide) ((hrep 1 0).trans (by decide)) ((hrep 0 0).trans (by decide))
    · exact need C hC 2 (oneEach (2 : Fin 4) (0 : Fin 4)) (oneEach (0 : Fin 4) (0 : Fin 4))
        (by decide) (by decide) (by decide) ((hrep 2 0).trans (by decide)) ((hrep 0 0).trans (by decide))
    · exact need C hC 4 (oneEach (1 : Fin 4) (0 : Fin 4)) (oneEach (1 : Fin 4) (2 : Fin 4))
        (by decide) (by decide) (by decide) ((hrep 1 0).trans (by decide)) ((hrep 1 2).trans (by decide))
    · exact need C hC 5 (oneEach (1 : Fin 4) (1 : Fin 4)) (oneEach (1 : Fin 4) (2 : Fin 4))
        (by decide) (by decide) (by decide) ((hrep 1 1).trans (by decide)) ((hrep 1 2).trans (by decide))
    · exact need C hC 6 (oneEach (0 : Fin 4) (2 : Fin 4)) (oneEach (0 : Fin 4) (0 : Fin 4))
        (by decide) (by decide) (by decide) ((hrep 0 2).trans (by decide)) ((hrep 0 0).trans (by decide))
    · exact need C hC 7 (oneEach (0 : Fin 4) (3 : Fin 4)) (oneEach (0 : Fin 4) (0 : Fin 4))
        (by decide) (by decide) (by decide) ((hrep 0 3).trans (by decide)) ((hrep 0 0).trans (by decide))
  have hcard := rel_card C.gates (P_card C.gates hC) C.gates.length {C.output}
  rw [Finset.card_singleton] at hcard
  have hsub : ({0, 1, 2, 4, 5, 6, 7} : Finset ℕ) ∪
      ((Finset.range C.gates.length).filter
        (fun j => 8 + j ∈ rel C.gates C.gates.length {C.output})).image (fun j => 8 + j)
      ⊆ rel C.gates C.gates.length {C.output} := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hz x hx
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hj).2
  have hdisj : Disjoint ({0, 1, 2, 4, 5, 6, 7} : Finset ℕ)
      (((Finset.range C.gates.length).filter
        (fun j => 8 + j ∈ rel C.gates C.gates.length {C.output})).image (fun j => 8 + j)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    omega
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (add_right_injective 8)] at h1
  have h7 : ({0, 1, 2, 4, 5, 6, 7} : Finset ℕ).card = 7 := by decide
  have hG := Finset.card_filter_le (Finset.range C.gates.length)
    (fun j => 8 + j ∈ rel C.gates C.gates.length {C.output})
  rw [Finset.card_range] at hG
  have hs' : C.gates.length ≤ 5 := hs
  omega

-- The six-gate formula x0 (y2 + y3) + (x1 + x2) (y0 + y1); wires 0..3 left, 4..7 right.
def C0 : Circuit :=
  ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [9, 12]⟩], 13⟩

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (828 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  refine ⟨C0, ?_, by decide, by decide⟩
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_5624

theorem PEqualNP.Outside.L_meta_5624 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (828 : ℕ).testBit (4 * u.val + v.val)) 6 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (828 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨PEqualNP.Outside.L_meta_5624.upper, PEqualNP.Outside.L_meta_5624.lower⟩
