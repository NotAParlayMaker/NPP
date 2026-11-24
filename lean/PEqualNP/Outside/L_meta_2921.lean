import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2921_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def r (x1 : Fin 9 → Fin 9) (k : ℕ) : ℕ := if h : k < 9 then (x1 ⟨k, h⟩).val else k

def reGate (x1 : Fin 9 → Fin 9) (g : Gate) : Gate := ⟨g.op, g.inputs.map (r x1)⟩

lemma step_inv (x1 : Fin 9 → Fin 9) (W Y : List Bool) (g : Gate) (hl : W.length = Y.length)
    (h9 : 9 ≤ Y.length) (hv : ∀ k, W.getD (r x1 k) false = Y.getD k false) :
    ∀ k, (stepW W (reGate x1 g)).getD (r x1 k) false = (stepW Y g).getD k false := by
  intro k
  have hm : (g.inputs.map (r x1)).map (fun i => W.getD i false)
      = g.inputs.map (fun i => Y.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hv i)
  show (W ++ [g.op.eval ((g.inputs.map (r x1)).map fun i => W.getD i false)]).getD (r x1 k) false
    = (Y ++ [g.op.eval (g.inputs.map fun i => Y.getD i false)]).getD k false
  rw [hm]
  have hr : r x1 k < W.length ↔ k < Y.length := by
    unfold r
    split_ifs with h
    · have := (x1 ⟨k, h⟩).isLt
      constructor <;> intro <;> omega
    · omega
  by_cases hk : k < Y.length
  · rw [List.getD_append _ _ _ _ (hr.mpr hk), List.getD_append _ _ _ _ hk, hv k]
  · have hrk : r x1 k = k := by
      unfold r
      rw [dif_neg (by omega)]
    rw [hrk, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]

lemma fold_inv (x1 : Fin 9 → Fin 9) (gs : List Gate) : ∀ (W Y : List Bool), W.length = Y.length →
    9 ≤ Y.length → (∀ k, W.getD (r x1 k) false = Y.getD k false) →
    ∀ k, ((gs.map (reGate x1)).foldl stepW W).getD (r x1 k) false = (gs.foldl stepW Y).getD k false := by
  induction gs with
  | nil => intro W Y _ _ hv; exact hv
  | cons g gs ih =>
    intro W Y hl h9 hv
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_ ?_ (step_inv x1 W Y g hl h9 hv)
    · simp [stepW, hl]
    · simp [stepW]; omega

end PEqualNP.Outside.L_meta_2921_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2921_aux in
theorem PEqualNP.Outside.L_meta_2921 : ∀ (x1 : Fin (9 : ℕ) → Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (9 : ℕ) ≤ x4.length → (∀ (x7 : ℕ), x3.getD (if x8 : x7 < (9 : ℕ) then ↑(x1 (⟨x7, x8⟩ : Fin (9 : ℕ))) else x7) Bool.false = x4.getD x7 Bool.false) → { gates := List.map (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => { op := x8.op, inputs := List.map (fun (x9 : ℕ) => if x10 : x9 < (9 : ℕ) then ↑(x1 (⟨x9, x10⟩ : Fin (9 : ℕ))) else x9) x8.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := if x8 : x2.output < (9 : ℕ) then ↑(x1 (⟨x2.output, x8⟩ : Fin (9 : ℕ))) else x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x3 = x2.eval x4 := by
  intro x1 C x3 x4 hl h9 hv
  exact fold_inv x1 C.gates x3 x4 hl h9 hv C.output
