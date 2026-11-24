import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2525

open PEqualNP.CircuitLowerBounds

lemma prefix_getD (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD j false
      = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hj]

lemma agree (gs : List Gate) (i : ℕ) (hi : ∀ g ∈ gs, i ∉ g.inputs) (w1 w2 : List Bool)
    (hl : w1.length = w2.length) (h : ∀ j, j ≠ i → w1.getD j false = w2.getD j false) :
    ∀ j, j ≠ i →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD j false
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD j
        false := by
  induction gs generalizing w1 w2 with
  | nil => exact h
  | cons g gs ih =>
    have hv : g.op.eval (g.inputs.map fun k => w1.getD k false)
        = g.op.eval (g.inputs.map fun k => w2.getD k false) := by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact h k (fun hki => hi g (by simp) (hki ▸ hk))
    apply ih (fun g' hg' => hi g' (by simp [hg']))
    · simp [hl]
    · intro j hj
      by_cases hjl : j < w1.length
      · rw [List.getD_append _ _ _ _ hjl, List.getD_append _ _ _ _ (hl ▸ hjl)]
        exact h j hj
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
          hl, hv]

lemma wire_first (C : Circuit) (g0 : Gate) (rest : List Gate) (hC : C.gates = g0 :: rest)
    (x : List Bool) :
    (C.wires x).getD x.length false = g0.op.eval (g0.inputs.map fun k => x.getD k false) := by
  unfold Circuit.wires
  rw [hC, List.foldl_cons, prefix_getD _ _ _ (by simp)]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma wire_input (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    (C.wires x).getD j false = x.getD j false := by
  unfold Circuit.wires
  exact prefix_getD _ _ _ hj

lemma flip_eq (C : Circuit) (g0 : Gate) (rest : List Gate) (hC : C.gates = g0 :: rest) (i : ℕ)
    (hi : ∀ g ∈ rest, i ∉ g.inputs) (ho : C.output ≠ i) (x y : List Bool)
    (hl : x.length = y.length) (hxy : ∀ j, j ≠ i → x.getD j false = y.getD j false)
    (hv : g0.op.eval (g0.inputs.map fun k => x.getD k false)
      = g0.op.eval (g0.inputs.map fun k => y.getD k false)) :
    C.eval x = C.eval y := by
  unfold Circuit.eval Circuit.wires
  rw [hC, List.foldl_cons, List.foldl_cons]
  apply agree rest i hi _ _ (by simp [hl]) _ _ ho
  intro j hj
  by_cases hjl : j < x.length
  · rw [List.getD_append _ _ _ _ hjl, List.getD_append _ _ _ _ (hl ▸ hjl)]
    exact hxy j hj
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
      hl, hv]

lemma ofFn_agree (x y : Fin 9 → Bool) (i : ℕ)
    (h : ∀ j : Fin 9, (j : ℕ) ≠ i → x j = y j) :
    ∀ j, j ≠ i → (List.ofFn x).getD j false = (List.ofFn y).getD j false := by
  intro j hj
  by_cases hj9 : j < 9
  · rw [List.getD_eq_getElem _ _ (by simpa using hj9), List.getD_eq_getElem _ _ (by simpa using hj9)]
    simp only [List.getElem_ofFn]
    exact h ⟨j, hj9⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_2525

theorem PEqualNP.Outside.L_meta_2525 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → (∃ x5 ∈ List.drop (1 : ℕ) x2.gates, (0 : ℕ) ∈ x5.inputs) ∧ ∃ x5 ∈ List.drop (1 : ℕ) x2.gates, (4 : ℕ) ∈ x5.inputs := by
  dsimp only
  intro C hw hf
  have e : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = _ := fun x => congrFun hf x
  rcases hg : C.gates with _ | ⟨g0, rest⟩
  · exfalso
    have h1 := hw (fun _ => true)
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires at h1
    rw [hg, List.foldl_nil, List.getD_eq_default _ _ (by simp)] at h1
    simp at h1
  · have w9 : ∀ x : Fin 9 → Bool,
        g0.op.eval (g0.inputs.map fun k => (List.ofFn x).getD k false) = (x 0 || x 4) := by
      intro x
      have := PEqualNP.Outside.L_meta_2525.wire_first C g0 rest hg (List.ofFn x)
      rw [List.length_ofFn] at this
      rw [← this]
      exact hw x
    simp only [List.drop_succ_cons, List.drop_zero]
    constructor
    · by_contra hno
      push Not at hno
      by_cases ho : C.output = 0
      · have hz := e (fun k => decide ((k : ℕ) = 0))
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval at hz
        rw [ho, PEqualNP.Outside.L_meta_2525.wire_input _ _ _ (by simp)] at hz
        revert hz
        decide
      · have hxy := PEqualNP.Outside.L_meta_2525.flip_eq C g0 rest hg 0 hno ho
          (List.ofFn fun k : Fin 9 => decide ((k : ℕ) = 0 ∨ (k : ℕ) = 1 ∨ (k : ℕ) = 4))
          (List.ofFn fun k : Fin 9 => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 4)) (by simp)
          (PEqualNP.Outside.L_meta_2525.ofFn_agree _ _ 0 (by intro j hj; simp [hj]))
          (by rw [w9, w9]; decide)
        rw [e, e] at hxy
        revert hxy
        decide
    · by_contra hno
      push Not at hno
      by_cases ho : C.output = 4
      · have hz := e (fun k => decide ((k : ℕ) = 4))
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval at hz
        rw [ho, PEqualNP.Outside.L_meta_2525.wire_input _ _ _ (by simp)] at hz
        revert hz
        decide
      · have hxy := PEqualNP.Outside.L_meta_2525.flip_eq C g0 rest hg 4 hno ho
          (List.ofFn fun k : Fin 9 => decide ((k : ℕ) = 0 ∨ (k : ℕ) = 3 ∨ (k : ℕ) = 4))
          (List.ofFn fun k : Fin 9 => decide ((k : ℕ) = 0 ∨ (k : ℕ) = 3)) (by simp)
          (PEqualNP.Outside.L_meta_2525.ofFn_agree _ _ 4 (by intro j hj; simp [hj]))
          (by rw [w9, w9]; decide)
        rw [e, e] at hxy
        revert hxy
        decide
