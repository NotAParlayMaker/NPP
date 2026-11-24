import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2921_aux

open PEqualNP.CircuitLowerBounds

def sg (f : Fin 9 → Fin 9) (i : ℕ) : ℕ := if h : i < 9 then (f ⟨i, h⟩ : ℕ) else i

lemma getD_app (w : List Bool) (a : Bool) (i : ℕ) (h : i < w.length) :
    (w ++ [a]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_app2 (w v : List Bool) (a : Bool) (i : ℕ) (hl : w.length = v.length)
    (h : w.getD i false = v.getD i false) :
    (w ++ [a]).getD i false = (v ++ [a]).getD i false := by
  rcases lt_or_ge i w.length with h1 | h1
  · rw [getD_app w a i h1, getD_app v a i (by omega), h]
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right h1, List.getElem?_append_right (by omega), hl]

lemma key (f : Fin 9 → Fin 9) : ∀ (gs : List Gate) (w v : List Bool), w.length = v.length →
    9 ≤ v.length → (∀ i, w.getD (sg f i) false = v.getD i false) →
    ∀ i, ((gs.map fun g => ({ op := g.op, inputs := g.inputs.map (sg f) } : Gate)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD (sg f i) false
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).getD i false := by
  intro gs
  induction gs with
  | nil => intro w v _ _ h i; exact h i
  | cons g gs ih =>
    intro w v hl h9 h i
    simp only [List.map_cons, List.foldl_cons, List.map_map]
    have he : (g.inputs.map ((fun i => w.getD i false) ∘ sg f)) =
        g.inputs.map (fun i => v.getD i false) := by
      apply List.map_congr_left
      intro j _
      exact h j
    rw [he]
    apply ih
    · simp [hl]
    · simp; omega
    · intro j
      by_cases hj : j < 9
      · have hs : sg f j < 9 := by simp [sg, hj]
        rw [getD_app w _ _ (by omega), getD_app v _ _ (by omega)]
        exact h j
      · have hs : sg f j = j := by simp [sg, hj]
        rw [hs]
        apply getD_app2 w v _ j hl
        have := h j
        rw [hs] at this
        exact this

end PEqualNP.Outside.L_meta_2921_aux

theorem PEqualNP.Outside.L_meta_2921 : ∀ (x1 : Fin (9 : ℕ) → Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (9 : ℕ) ≤ x4.length → (∀ (x7 : ℕ), x3.getD (if x8 : x7 < (9 : ℕ) then ↑(x1 (⟨x7, x8⟩ : Fin (9 : ℕ))) else x7) Bool.false = x4.getD x7 Bool.false) → { gates := List.map (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => { op := x8.op, inputs := List.map (fun (x9 : ℕ) => if x10 : x9 < (9 : ℕ) then ↑(x1 (⟨x9, x10⟩ : Fin (9 : ℕ))) else x9) x8.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := if x8 : x2.output < (9 : ℕ) then ↑(x1 (⟨x2.output, x8⟩ : Fin (9 : ℕ))) else x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x3 = x2.eval x4 := by
  intro x1 x2 x3 x4 hl h9 h
  exact PEqualNP.Outside.L_meta_2921_aux.key x1 x2.gates x3 x4 hl h9 h x2.output
