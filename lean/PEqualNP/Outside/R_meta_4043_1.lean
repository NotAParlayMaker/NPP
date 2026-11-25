import Mathlib
import PEqualNP.Defs

-- Cut by symmetry. The plane of order 3 is cyclic: translating every point and every line by the
-- same element of Fin 13 keeps incidence. Relabelling the input wires of a circuit by such a
-- translation keeps its size and its gate kinds, so the bound for a circuit right where vertex v is
-- false follows from the bound where point 0 is false (v a point) or line 0 is false (v a line).
theorem PEqualNP.Outside.R_meta_4043_1
    (h1 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      (∀ (x : Fin 26 → Bool), x 0 = false → (C.eval (List.ofFn x) = true ↔
        ∃ (a b : Fin 13), (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) ∧
          x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true)) → 58 ≤ C.size)
    (h2 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      (∀ (x : Fin 26 → Bool), x 13 = false → (C.eval (List.ofFn x) = true ↔
        ∃ (a b : Fin 13), (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) ∧
          x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true)) → 58 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (58 : ℕ) ≤ x1.size := by
  intro C v mono hf
  -- the incidence of the plane, and its invariance under translation
  let inc : Fin 13 → Fin 13 → Prop := fun a b => a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9
  have incShift : ∀ a b c : Fin 13, inc (a - c) (b - c) ↔ inc a b := by
    intro a b c
    simp only [inc, sub_add_eq_add_sub, sub_left_inj]
  -- translation of the 26 vertices by -c
  let tr : Fin 13 → Fin 26 → Fin 26 := fun c i =>
    if h : i.val < 13 then Fin.castAdd 13 (⟨i.val, h⟩ - c)
    else Fin.natAdd 13 (⟨i.val - 13, by omega⟩ - c)
  have trPoint : ∀ c a : Fin 13, tr c (Fin.castAdd 13 a) = Fin.castAdd 13 (a - c) := by
    intro c a
    have h : (Fin.castAdd 13 a).val < 13 := by simp
    simp only [tr, dite_eq_left h]
    rw [show (⟨(Fin.castAdd 13 a).val, h⟩ : Fin 13) = a from Fin.ext rfl]
  have trLine : ∀ c b : Fin 13, tr c (Fin.natAdd 13 b) = Fin.natAdd 13 (b - c) := by
    intro c b
    have h : ¬ (Fin.natAdd 13 b).val < 13 := by simp
    simp only [tr, dite_eq_right h]
    rw [show (⟨(Fin.natAdd 13 b).val - 13, by omega⟩ : Fin 13) = b from Fin.ext (by simp)]
  -- the value of the graph function does not change under the translation
  let F : (Fin 26 → Bool) → Prop := fun x => ∃ a b : Fin 13, inc a b ∧
    x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true
  have FShift : ∀ (c : Fin 13) (x : Fin 26 → Bool), F (fun i => x (tr c i)) ↔ F x := by
    intro c x
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      refine ⟨a - c, b - c, (incShift a b c).mpr hab, ?_, ?_⟩
      · simp only [trPoint] at ha
        exact ha
      · simp only [trLine] at hb
        exact hb
    · rintro ⟨a, b, hab, ha, hb⟩
      refine ⟨a + c, b + c, ?_, ?_, ?_⟩
      · have := (incShift (a + c) (b + c) c).mp
        simp only [add_sub_cancel_right] at this
        exact this hab
      · simp only [trPoint, add_sub_cancel_right]
        exact ha
      · simp only [trLine, add_sub_cancel_right]
        exact hb
  -- relabelling the input wires of a circuit
  let r : Fin 13 → ℕ → ℕ := fun c w => if h : w < 26 then (tr c ⟨w, h⟩).val else w
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let rg : Fin 13 → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun c g => { op := g.op, inputs := g.inputs.map (r c) }
  have rLow : ∀ c w, w < 26 → r c w < 26 := by
    intro c w hw
    simp only [r, dite_eq_left hw]
    exact (tr c ⟨w, hw⟩).isLt
  have rHigh : ∀ c w, ¬ w < 26 → r c w = w := by
    intro c w hw
    simp only [r, dite_eq_right hw]
  have snoc : ∀ (l : List Bool) (a : Bool) (i : ℕ), (l ++ [a]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then a else false := by
    intro l a i
    split_ifs with h h'
    · exact List.getD_append _ _ _ _ h
    · subst h'
      simp
    · rw [List.getD_eq_default]
      simp only [List.length_append, List.length_singleton]
      omega
  have sim : ∀ (c : Fin 13) (gs : List PEqualNP.CircuitLowerBounds.Gate) (v w : List Bool),
      v.length = w.length → 26 ≤ w.length → (∀ i, v.getD (r c i) false = w.getD i false) →
      ∀ i, ((gs.map (rg c)).foldl step v).getD (r c i) false = (gs.foldl step w).getD i false := by
    intro c gs
    induction gs with
    | nil => intro v w _ _ h i; exact h i
    | cons g gs ih =>
      intro v w hl h26 h
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hval : (rg c g).op.eval ((rg c g).inputs.map fun i => v.getD i false)
          = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [rg, List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact h j
      apply ih
      · simp [step, hl]
      · simp only [step, List.length_append, List.length_singleton]; omega
      · intro i
        simp only [step]
        rw [snoc, snoc, hval]
        by_cases hi : i < 26
        · have hr := rLow c i hi
          rw [ite_eq_left (by omega), ite_eq_left (by omega)]
          exact h i
        · rw [rHigh c i hi]
          have hi' := h i
          rw [rHigh c i hi] at hi'
          by_cases hlt : i < w.length
          · rw [ite_eq_left (by omega), ite_eq_left hlt]
            exact hi'
          · rw [ite_eq_right (by omega), ite_eq_right hlt]
            by_cases he : i = w.length
            · rw [ite_eq_left (by omega), ite_eq_left he]
            · rw [ite_eq_right (by omega), ite_eq_right he]
  have ofFnD : ∀ (y : Fin 26 → Bool) (i : ℕ) (h : i < 26), (List.ofFn y).getD i false = y ⟨i, h⟩ := by
    intro y i h
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  -- the relabelled circuit
  have relabel : ∀ c : Fin 13, ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧ D.size = C.size ∧
      ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (tr c i))) := by
    intro c
    refine ⟨⟨C.gates.map (rg c), r c C.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      have := mono g0 hg0
      simpa [rg] using this
    · show (C.gates.map (rg c)).length = C.gates.length
      exact List.length_map _
    · intro x
      show ((C.gates.map (rg c)).foldl step (List.ofFn x)).getD (r c C.output) false =
        (C.gates.foldl step (List.ofFn (fun i => x (tr c i)))).getD C.output false
      apply sim c C.gates
      · simp
      · simp
      · intro i
        by_cases hi : i < 26
        · simp only [r, dite_eq_left hi]
          rw [ofFnD x _ (tr c ⟨i, hi⟩).isLt, ofFnD _ i hi]
        · rw [rHigh c i hi, List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
  -- the two cases: v a point, v a line
  by_cases hv : v.val < 13
  · let c : Fin 13 := ⟨v.val, hv⟩
    have hvc : v = Fin.castAdd 13 c := Fin.ext rfl
    obtain ⟨D, monoD, sizeD, evalD⟩ := relabel c
    rw [← sizeD]
    apply h1 D monoD
    intro x hx
    rw [evalD]
    have hy : (fun i => x (tr c i)) v = false := by
      show x (tr c v) = false
      rw [hvc, trPoint, sub_self]
      have e : (Fin.castAdd 13 (0 : Fin 13) : Fin 26) = 0 := by decide
      rw [e]
      exact hx
    exact (hf _ hy).trans (FShift c x)
  · let c : Fin 13 := ⟨v.val - 13, by omega⟩
    have hvc : v = Fin.natAdd 13 c := Fin.ext (by simp [c]; omega)
    obtain ⟨D, monoD, sizeD, evalD⟩ := relabel c
    rw [← sizeD]
    apply h2 D monoD
    intro x hx
    rw [evalD]
    have hy : (fun i => x (tr c i)) v = false := by
      show x (tr c v) = false
      rw [hvc, trLine, sub_self]
      have e : (Fin.natAdd 13 (0 : Fin 13) : Fin 26) = 13 := by decide
      rw [e]
      exact hx
    exact (hf _ hy).trans (FShift c x)
