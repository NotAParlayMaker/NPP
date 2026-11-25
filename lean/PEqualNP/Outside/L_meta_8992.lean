import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8992_aux

open PEqualNP.CircuitLowerBounds

def fm (r B j : ℕ) : ℕ := if j < r then j else if j = r then B else j - 1

def rg (r B : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fm r B)⟩

theorem gN (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem gA (w : List Bool) (a : Bool) (i : ℕ) :
    (w ++ [a]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then a else false := by
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · exact gN _ _ (by simp; omega)

theorem gF (n : ℕ) (f : Fin n → Bool) (j : ℕ) :
    (List.ofFn f).getD j false = if h : j < n then f ⟨j, h⟩ else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]
  · exact gN _ _ (by simp; omega)

theorem key (r B : ℕ) (gs : List Gate) :
    ∀ w w' : List Bool, w.length + 1 = w'.length → r < w'.length → w.length + gs.length ≤ B →
      (∀ j, w.getD (fm r B j) false = w'.getD j false) →
      ∀ j, ((gs.map (rg r B)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
          (fm r B j) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD
          j false := by
  induction gs with
  | nil => intro w w' _ _ _ h j; exact h j
  | cons g gs ih =>
    intro w w' hl hr hB h
    simp only [List.map_cons, List.foldl_cons]
    have he : (rg r B g).op.eval ((rg r B g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    rw [he]
    simp only [List.length_cons] at hB
    apply ih
    · simp [hl]
    · simp; omega
    · simp; omega
    · intro j
      rw [gA, gA]
      have hj := h j
      have hz : w.getD B false = false := gN _ _ (by omega)
      unfold fm at hj ⊢
      split_ifs at hj ⊢ <;> first | omega | (subst_vars; simp_all)

end PEqualNP.Outside.L_meta_8992_aux

open PEqualNP.Outside.L_meta_8992_aux in
theorem PEqualNP.Outside.L_meta_8992 : ∀ (x1 : ℕ) (x2 : Fin (x1 + (1 : ℕ))) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x3.size ∧ ∀ (x6 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x5 x6 = PEqualNP.MetaComplexity.circuitFun (x1 + (1 : ℕ)) x3 (x2.insertNth Bool.false x6) := by
  intro x1 x2 x3 hm
  refine ⟨⟨x3.gates.map (rg x2.val (x1 + x3.gates.length)), fm x2.val (x1 + x3.gates.length) x3.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hm g0 hg0
    exact ⟨h1, by simpa [rg] using h2⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x6
    have hr := x2.isLt
    exact key x2.val (x1 + x3.gates.length) x3.gates (List.ofFn x6)
      (List.ofFn (x2.insertNth false x6)) (by simp) (by simp; omega) (by simp)
      (by
        intro j
        unfold fm
        split_ifs with h1 h2
        · have e : (⟨j, by omega⟩ : Fin (x1 + 1)) = x2.succAbove ⟨j, by omega⟩ := by
            rw [Fin.succAbove_of_castSucc_lt] <;> simp [Fin.lt_def, h1]
          have e2 := congrArg (x2.insertNth false x6) e
          rw [Fin.insertNth_apply_succAbove] at e2
          rw [gF, gF, dif_pos (by omega), dif_pos (by omega), e2]
        · subst h2
          rw [gN _ _ (by simp)]
          rw [gF, dif_pos hr]
          simp
        · by_cases hj : j < x1 + 1
          · have e : (⟨j, hj⟩ : Fin (x1 + 1)) = x2.succAbove ⟨j - 1, by omega⟩ := by
              rw [Fin.succAbove_of_le_castSucc] <;> simp [Fin.le_def, Fin.ext_iff] <;> omega
            have e2 := congrArg (x2.insertNth false x6) e
            rw [Fin.insertNth_apply_succAbove] at e2
            rw [gF, gF, dif_pos (by omega), dif_pos hj, e2]
          · rw [gN _ _ (by simp; omega), gN _ _ (by simp; omega)])
      x3.output
