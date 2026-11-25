import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8053_aux

open PEqualNP.CircuitLowerBounds

theorem step (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w v : List Bool), w.length = v.length →
      (∀ i, w.getD i false = true → v.getD i false = true) →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
        = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).length ∧
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).getD i false = true := by
  induction gs with
  | nil => intro w v hl hm; exact ⟨hl, hm⟩
  | cons g gs ih =>
    intro w v hl hm
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · have hab : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
          g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
        rcases hg g (List.mem_cons_self) with h | h
        · rw [h]; simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
          rintro H x ⟨j, hj, rfl⟩
          exact hm j (H _ ⟨j, hj, rfl⟩)
        · rw [h]; simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
          rintro ⟨x, ⟨j, hj, rfl⟩, hx⟩
          exact ⟨_, ⟨j, hj, rfl⟩, hm j hx⟩
      intro i hi
      rcases lt_trichotomy i w.length with h1 | h1 | h1
      · rw [List.getD_append _ _ _ _ h1] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ h1)]
        exact hm i hi
      · subst h1
        rw [List.getD_append_right _ _ _ _ le_rfl] at hi
        rw [hl, List.getD_append_right _ _ _ _ le_rfl] at *
        simp at hi ⊢
        exact hab hi
      · rw [List.getD_eq_default] at hi
        · simp at hi
        · simp; omega

theorem base {n : ℕ} (x y : Fin n → Bool) (hxy : ∀ j, x j = true → y j = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases h : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, Option.getD] at hi ⊢
    simp_all
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    simp at hi


theorem app (a b c d : List Bool) (hl : a.length = b.length)
    (h1 : ∀ i, a.getD i false = true → b.getD i false = true)
    (h2 : ∀ i, c.getD i false = true → d.getD i false = true) :
    ∀ i, (a ++ c).getD i false = true → (b ++ d).getD i false = true := by
  intro i hi
  by_cases h : i < a.length
  · rw [List.getD_append _ _ _ _ h] at hi
    rw [List.getD_append _ _ _ _ (hl ▸ h)]
    exact h1 i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega)]
    rw [← hl]
    exact h2 _ hi

theorem ble (a b : Bool) (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> simp_all

end PEqualNP.Outside.L_meta_8053_aux

open PEqualNP.Outside.L_meta_8053_aux in
theorem PEqualNP.Outside.L_meta_8053 : have x1 : (Fin (42 : ℕ) → Bool) → List Bool := fun (x1 : Fin (42 : ℕ) → Bool) =>   have x2 : Fin (7 : ℕ) → ℕ → Bool := fun (x2 : Fin (7 : ℕ)) (x3 : ℕ) => x1 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x2 + x3) % (21 : ℕ)));   (List.ofFn x1 ++ List.ofFn fun (x3 : Fin (7 : ℕ)) => x2 x3 (5 : ℕ) || x2 x3 (17 : ℕ)) ++ List.ofFn fun (x3 : Fin (7 : ℕ)) => x2 x3 (5 : ℕ) || x2 x3 (17 : ℕ) || x2 x3 (20 : ℕ); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → Monotone fun (x4 : Fin (42 : ℕ) → Bool) => x2.eval (x1 x4) := by
  intro L C hC x y hxy
  have hm : ∀ j, x j = true → y j = true := by
    intro j hj
    have := hxy j
    rw [hj] at this
    revert this
    cases y j <;> simp
  have hb : ∀ i, (L x).getD i false = true → (L y).getD i false = true := by
    apply app
    · simp
    · apply app
      · simp
      · exact base x y hm
      · apply base
        intro j hj
        simp only [Bool.or_eq_true] at hj ⊢
        rcases hj with h | h
        · exact Or.inl (hm _ h)
        · exact Or.inr (hm _ h)
    · apply base
      intro j hj
      simp only [Bool.or_eq_true] at hj ⊢
      rcases hj with (h | h) | h
      · exact Or.inl (Or.inl (hm _ h))
      · exact Or.inl (Or.inr (hm _ h))
      · exact Or.inr (hm _ h)
  apply ble
  have hg : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  exact (step C.gates hg (L x) (L y) (by simp [L]) hb).2 C.output
