import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3787_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem step_len (W : List Bool) (g : Gate) : (step W g).length = W.length + 1 := by
  simp [step]

theorem fold_len (gs : List Gate) : ∀ W : List Bool, (gs.foldl step W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp
  | cons g gs ih =>
    intro W
    simp only [List.foldl_cons]
    rw [ih, step_len]
    simp
    omega

theorem step_prefix (W : List Bool) (g : Gate) (i : ℕ) (h : i < W.length) :
    (step W g).getD i false = W.getD i false := by
  unfold step
  rw [List.getD_append _ _ _ _ h]

theorem fold_prefix (gs : List Gate) : ∀ (W : List Bool) (i : ℕ), i < W.length →
    (gs.foldl step W).getD i false = W.getD i false := by
  induction gs with
  | nil => intro W i h; rfl
  | cons g gs ih =>
    intro W i h
    simp only [List.foldl_cons]
    rw [ih _ _ (by rw [step_len]; omega), step_prefix _ _ _ h]

theorem step_last (W : List Bool) (g : Gate) :
    (step W g).getD W.length false = g.op.eval (g.inputs.map fun i => W.getD i false) := by
  unfold step
  simp

def star : List Gate :=
  [⟨.or, [13, 14]⟩, ⟨.or, [26, 16]⟩, ⟨.or, [27, 22]⟩, ⟨.and, [0, 28]⟩,
   ⟨.or, [25, 13]⟩, ⟨.or, [30, 15]⟩, ⟨.or, [31, 21]⟩, ⟨.and, [1, 32]⟩,
   ⟨.or, [23, 24]⟩, ⟨.or, [34, 13]⟩, ⟨.or, [35, 19]⟩, ⟨.and, [3, 36]⟩,
   ⟨.or, [17, 18]⟩, ⟨.or, [38, 20]⟩, ⟨.or, [39, 13]⟩, ⟨.and, [9, 40]⟩,
   ⟨.or, [29, 33]⟩, ⟨.or, [42, 37]⟩, ⟨.or, [43, 41]⟩]

theorem star_len : star.length = 19 := rfl

theorem star_val (y : Fin 26 → Bool) :
    (star.foldl step (List.ofFn y)).getD 44 false =
      ((((y 0 && (((y 13 || y 14) || y 16) || y 22)) ||
        (y 1 && (((y 25 || y 13) || y 15) || y 21))) ||
        (y 3 && (((y 23 || y 24) || y 13) || y 19))) ||
        (y 9 && (((y 17 || y 18) || y 20) || y 13))) := by
  simp [star, step, List.ofFn_succ, GateOp.eval]

theorem star_iff (A B : Finset (Fin 13)) :
    ((((decide (0 ∈ A) && (((decide (0 ∈ B) || decide (1 ∈ B)) || decide (3 ∈ B)) || decide (9 ∈ B))) ||
      (decide (1 ∈ A) && (((decide (12 ∈ B) || decide (0 ∈ B)) || decide (2 ∈ B)) || decide (8 ∈ B)))) ||
      (decide (3 ∈ A) && (((decide (10 ∈ B) || decide (11 ∈ B)) || decide (0 ∈ B)) || decide (6 ∈ B)))) ||
      (decide (9 ∈ A) && (((decide (4 ∈ B) || decide (5 ∈ B)) || decide (7 ∈ B)) || decide (0 ∈ B)))) = true ↔
    ∃ p ∈ A, (p : ℕ) ∈ ([0, 1, 3, 9] : List ℕ) ∧
      ∃ l ∈ B, ((p : ℕ) + (l : ℕ)) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
  constructor
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with (((⟨hp, ((hl | hl) | hl) | hl⟩ | ⟨hp, ((hl | hl) | hl) | hl⟩) |
      ⟨hp, ((hl | hl) | hl) | hl⟩) | ⟨hp, ((hl | hl) | hl) | hl⟩) <;>
      exact ⟨_, hp, by decide, _, hl, by decide⟩
  · rintro ⟨p, hp, hpD, l, hl, hpl⟩
    fin_cases p <;> fin_cases l <;> simp_all (config := {decide := true})

def pts : List (Fin 26) :=
  [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

theorem pts_len : pts.length = 21 := rfl

def wmap (w : ℕ) : ℕ := if w < 21 then ((pts.getD w 0 : Fin 26) : ℕ) else w - 21 + 45

theorem wmap_lt (w : ℕ) (h : w < 21) : wmap w < 26 := by
  unfold wmap
  simp only [h, ↓reduceIte]
  exact (pts.getD w 0).isLt

theorem wmap_ge (w : ℕ) (h : ¬ w < 21) : wmap w = w - 21 + 45 := by
  unfold wmap
  simp only [h, ↓reduceIte]

def relGate (g : Gate) : Gate := ⟨g.op, g.inputs.map wmap⟩

def Rel (W W' : List Bool) : Prop :=
  21 ≤ W.length ∧ W'.length + 21 = W.length + 45 ∧ ∀ w : ℕ, W'.getD (wmap w) false = W.getD w false

theorem rel_step (W W' : List Bool) (g : Gate) (h : Rel W W') :
    Rel (step W g) (step W' (relGate g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate g).op.eval ((relGate g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap w < W'.length := by
      by_cases hc : w < 21
      · have := wmap_lt w hc; omega
      · rw [wmap_ge w hc]; omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap w = W'.length := by
      rw [wmap_ge w (by omega)]; omega
    rw [he, hw]
    simp
  · have hge : W'.length + 1 ≤ wmap w := by
      rw [wmap_ge w (by omega)]; omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (gs : List Gate) : ∀ W W' : List Bool, Rel W W' →
    Rel (gs.foldl step W) ((gs.map relGate).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step W W' g h)

theorem rel_init (y : Fin 26 → Bool) : Rel (pts.map y) (star.foldl step (List.ofFn y)) := by
  refine ⟨by simp [pts_len], by rw [fold_len, star_len]; simp [pts_len], ?_⟩
  intro w
  by_cases hc : w < 21
  · have hv := wmap_lt w hc
    rw [fold_prefix _ _ _ (by simp; omega)]
    interval_cases w <;> rfl
  · rw [wmap_ge w hc]
    rw [List.getD_eq_default _ _ (by rw [fold_len, star_len]; simp only [List.length_ofFn]; omega),
      List.getD_eq_default _ _ (by simp only [List.length_map, pts_len]; omega)]

def build (C : Circuit) : Circuit :=
  ⟨star ++ C.gates.map relGate ++ [⟨.or, [wmap C.output, 44]⟩], 45 + C.gates.length⟩

theorem build_eval (C : Circuit) (y : Fin 26 → Bool) :
    (build C).eval (List.ofFn y) = (C.eval (pts.map y) ||
      ((((y 0 && (((y 13 || y 14) || y 16) || y 22)) ||
        (y 1 && (((y 25 || y 13) || y 15) || y 21))) ||
        (y 3 && (((y 23 || y 24) || y 13) || y 19))) ||
        (y 9 && (((y 17 || y 18) || y 20) || y 13)))) := by
  have hR := rel_fold C.gates _ _ (rel_init y)
  set W1 := star.foldl step (List.ofFn y) with hW1
  set W2 := (C.gates.map relGate).foldl step W1 with hW2
  have hl1 : W1.length = 45 := by rw [hW1, fold_len, star_len]; simp
  have hl2 : W2.length = 45 + C.gates.length := by rw [hW2, fold_len, hl1]; simp
  have hw : (build C).wires (List.ofFn y) = step W2 ⟨.or, [wmap C.output, 44]⟩ := by
    rw [wires_eq]
    simp only [build, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  unfold Circuit.eval
  rw [hw]
  have ho : (build C).output = W2.length := by
    rw [hl2]
    rfl
  rw [ho, step_last]
  have h44 : W2.getD 44 false = W1.getD 44 false := by
    rw [hW2]; exact fold_prefix _ _ _ (by omega)
  have hout : W2.getD (wmap C.output) false = C.eval (pts.map y) := by
    rw [hW2]; exact hR.2.2 C.output
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id]
  rw [hout, h44, hW1, star_val]
  rfl

theorem build_mono (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (build C) := by
  intro g hg
  simp only [build, List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with (hg | ⟨g0, hg0, rfl⟩) | rfl
  · simp only [star, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · obtain ⟨h1, h2⟩ := hm g0 hg0
    exact ⟨h1, by simpa [relGate] using h2⟩
  · simp

theorem build_size (C : Circuit) : (build C).size ≤ C.size + 20 := by
  simp [build, Circuit.size, star_len]
  omega

end PEqualNP.Outside.L_meta_3787_aux

theorem PEqualNP.Outside.L_meta_3787 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.output < (21 : ℕ) + x1.size →       ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x4 ∧           x4.size ≤ x1.size + (20 : ℕ) ∧             have x5 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))];             have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);             have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x7 x8 : Fin (13 : ℕ)) => (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             ∀ (x8 x9 : Finset (Fin (13 : ℕ))), x4.eval (List.ofFn (x6 x8 x9)) = Bool.true ↔ x1.eval (List.map (x6 x8 x9) x5) = Bool.true ∨ ∃ x10 ∈ x8, ↑x10 ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x11 ∈ x9, x7 x10 x11 := by
  intro C hm _
  refine ⟨PEqualNP.Outside.L_meta_3787_aux.build C, PEqualNP.Outside.L_meta_3787_aux.build_mono C hm, PEqualNP.Outside.L_meta_3787_aux.build_size C, ?_⟩
  dsimp only
  intro A B
  rw [PEqualNP.Outside.L_meta_3787_aux.build_eval]
  rw [Bool.or_eq_true]
  apply or_congr_right
  rw [← PEqualNP.Outside.L_meta_3787_aux.star_iff A B]
  simp
  exact Iff.rfl
