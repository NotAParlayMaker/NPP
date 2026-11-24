import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4968

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]


def extra (B : ℕ) (u v : ℕ → ℕ) : ℕ → List Gate
  | 0 => [⟨GateOp.and, [u 0, v 0]⟩]
  | k + 1 => extra B u v k ++ [⟨GateOp.and, [u (k + 1), v (k + 1)]⟩, ⟨GateOp.or, [B + 2 * k, B + 2 * k + 1]⟩]

lemma extra_length (B : ℕ) (u v : ℕ → ℕ) (k : ℕ) : (extra B u v k).length = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [extra, ih]; omega

lemma extra_mono (B : ℕ) (u v : ℕ → ℕ) (k : ℕ) :
    ∀ g ∈ extra B u v k, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction k with
  | zero => intro g hg; simp [extra] at hg; subst hg; simp
  | succ k ih =>
    intro g hg
    simp only [extra, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact ih g hg
    · simp
    · simp

lemma extra_run (B : ℕ) (u v : ℕ → ℕ) (W : List Bool) (hW : W.length = B)
    (hu : ∀ j, u j < B) (hv : ∀ j, v j < B) (k : ℕ) :
    (run (extra B u v k) W).length = B + 2 * k + 1 ∧
      (∀ i < B, (run (extra B u v k) W).getD i false = W.getD i false) ∧
      ((run (extra B u v k) W).getD (B + 2 * k) false = true ↔
        ∃ j ≤ k, W.getD (u j) false = true ∧ W.getD (v j) false = true) := by
  induction k with
  | zero =>
    refine ⟨by simp [extra, run_length, hW], fun i hi => run_getD _ _ _ (by omega), ?_⟩
    change (step W _).getD (B + 2 * 0) false = true ↔ _
    rw [show B + 2 * 0 = W.length by omega, step_getD_last]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true]
    constructor
    · intro h; exact ⟨0, le_refl 0, h⟩
    · rintro ⟨j, hj, h⟩
      have : j = 0 := by omega
      subst this
      exact h
  | succ k ih =>
    obtain ⟨hl, hpre, hval⟩ := ih
    have hsplit : run (extra B u v (k + 1)) W =
        step (step (run (extra B u v k) W) ⟨GateOp.and, [u (k + 1), v (k + 1)]⟩)
          ⟨GateOp.or, [B + 2 * k, B + 2 * k + 1]⟩ := by
      simp only [extra]
      rw [run_append]
      rfl
    set R := run (extra B u v k) W with hR
    have hA : (step R ⟨GateOp.and, [u (k + 1), v (k + 1)]⟩).getD (B + 2 * k + 1) false =
        (W.getD (u (k + 1)) false && W.getD (v (k + 1)) false) := by
      rw [show B + 2 * k + 1 = R.length by omega, step_getD_last]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true]
      rw [hpre _ (hu _), hpre _ (hv _)]
    refine ⟨by rw [hsplit, step_length, step_length, hl]; omega, fun i hi => ?_, ?_⟩
    · rw [hsplit, step_getD _ _ _ (by rw [step_length]; omega), step_getD _ _ _ (by omega), hpre i hi]
    · rw [hsplit, show B + 2 * (k + 1) = (step R ⟨GateOp.and, [u (k + 1), v (k + 1)]⟩).length by
        rw [step_length]; omega, step_getD_last]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false, Bool.or_eq_true]
      rw [hA, step_getD _ _ _ (by omega), hval]
      simp only [Bool.and_eq_true]
      constructor
      · rintro (⟨j, hj, h⟩ | h)
        · exact ⟨j, by omega, h⟩
        · exact ⟨k + 1, le_refl _, h⟩
      · rintro ⟨j, hj, h⟩
        by_cases hjk : j ≤ k
        · exact Or.inl ⟨j, hjk, h⟩
        · have : j = k + 1 := by omega
          subst this
          exact Or.inr h

end PEqualNP.Outside.L_meta_4968

theorem PEqualNP.Outside.L_meta_4968 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (x2 + (1 : ℕ)) → Fin x1) (x5 : Fin (x2 + (1 : ℕ)) → ℕ), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin (x2 + (1 : ℕ))), x5 x7 < x1 + x3.size) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size = x3.size + (2 : ℕ) * x2 + (1 : ℕ) ∧ x8.output < x1 + x8.size ∧ (∀ (x9 : Fin x1 → Bool), ∀ x10 < x1 + x3.size, (x8.wires (List.ofFn x9)).getD x10 Bool.false = (x3.wires (List.ofFn x9)).getD x10 Bool.false) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin (x2 + (1 : ℕ))), x9 (x4 x10) = Bool.true ∧ (x3.wires (List.ofFn x9)).getD (x5 x10) Bool.false = Bool.true := by
  intro x1 x2 x3 x4 x5 hmono hx5
  let B := x1 + x3.gates.length
  let u : ℕ → ℕ := fun j => if h : j < x2 + 1 then (x4 ⟨j, h⟩ : ℕ) else 0
  let v : ℕ → ℕ := fun j => if h : j < x2 + 1 then x5 ⟨j, h⟩ else 0
  have hu : ∀ j, u j < B := by
    intro j
    simp only [u]
    split_ifs
    · have := (x4 ⟨j, by omega⟩).isLt
      omega
    · have := (x4 0).isLt
      omega
  have hv : ∀ j, v j < B := by
    intro j
    simp only [v]
    split_ifs with h
    · exact hx5 ⟨j, h⟩
    · have := (x4 0).isLt
      omega
  have hlen := PEqualNP.Outside.L_meta_4968.extra_length B u v x2
  refine ⟨⟨x3.gates ++ PEqualNP.Outside.L_meta_4968.extra B u v x2, B + 2 * x2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hmono g hg
    · exact PEqualNP.Outside.L_meta_4968.extra_mono B u v x2 g hg
  · change (x3.gates ++ _).length = x3.gates.length + 2 * x2 + 1
    rw [List.length_append, hlen]
    omega
  · change B + 2 * x2 < x1 + (x3.gates ++ _).length
    rw [List.length_append, hlen]
    omega
  · intro x9 x10 hx10
    have hW : (PEqualNP.Outside.L_meta_4968.run x3.gates (List.ofFn x9)).length = B := by
      rw [PEqualNP.Outside.L_meta_4968.run_length]
      simp [B]
    have h := (PEqualNP.Outside.L_meta_4968.extra_run B u v _ hW hu hv x2).2.1 x10 hx10
    change (PEqualNP.Outside.L_meta_4968.run (x3.gates ++ _) (List.ofFn x9)).getD x10 false = _
    rw [PEqualNP.Outside.L_meta_4968.run_append]
    exact h
  · intro x9
    have hW : (PEqualNP.Outside.L_meta_4968.run x3.gates (List.ofFn x9)).length = B := by
      rw [PEqualNP.Outside.L_meta_4968.run_length]
      simp [B]
    have h := (PEqualNP.Outside.L_meta_4968.extra_run B u v _ hW hu hv x2).2.2
    change (PEqualNP.Outside.L_meta_4968.run (x3.gates ++ _) (List.ofFn x9)).getD (B + 2 * x2) false = true ↔ _
    rw [PEqualNP.Outside.L_meta_4968.run_append, h]
    have hin : ∀ i : Fin x1,
        (PEqualNP.Outside.L_meta_4968.run x3.gates (List.ofFn x9)).getD i false = x9 i := by
      intro i
      rw [PEqualNP.Outside.L_meta_4968.run_getD _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    constructor
    · rintro ⟨j, hj, h1, h2⟩
      refine ⟨⟨j, by omega⟩, ?_, ?_⟩
      · have := hin (x4 ⟨j, by omega⟩)
        simp only [u, dif_pos (show j < x2 + 1 by omega)] at h1
        rw [← this]
        exact h1
      · simp only [v, dif_pos (show j < x2 + 1 by omega)] at h2
        exact h2
    · rintro ⟨k, h1, h2⟩
      refine ⟨k.val, by omega, ?_, ?_⟩
      · simp only [u, dif_pos k.isLt]
        rw [hin]
        exact h1
      · simp only [v, dif_pos k.isLt]
        exact h2
