import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_476

open PEqualNP.CircuitLowerBounds

private lemma foldl_wires_length (gs : List Gate) (w0 : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs generalizing w0 with
  | nil => simp
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

private lemma foldl_wires_getD (gs : List Gate) (w0 : List Bool) (i : ℕ) :
    i < w0.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).getD i false
      = w0.getD i false := by
  induction gs generalizing w0 i with
  | nil => intro hi; rfl
  | cons g gs ih =>
      intro hi
      simp only [List.foldl_cons]
      have hsub : i < (w0 ++ [g.op.eval (g.inputs.map fun j => w0.getD j false)]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have h2 := ih (w0 ++ [g.op.eval (g.inputs.map fun j => w0.getD j false)]) i hsub
      rw [h2]
      exact List.getD_append _ _ _ _ hi

theorem wires_append (gs hs : List Gate) (o o' : ℕ) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    (Circuit.wires (Circuit.mk (gs ++ hs) o) x).getD i false
      = (Circuit.wires (Circuit.mk gs o') x).getD i false := by
  unfold Circuit.wires
  have hlen := foldl_wires_length gs x
  have hiw : i < (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x).length := by
    rw [hlen]; exact hi
  rw [List.foldl_append]
  exact foldl_wires_getD hs (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x) i hiw

end PEqualNP.Outside.L_meta_476

theorem PEqualNP.Outside.L_meta_476 : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (o o' : ℕ) (x : List Bool) (i : ℕ),
    i < x.length + gs.length →
    (PEqualNP.CircuitLowerBounds.Circuit.wires (PEqualNP.CircuitLowerBounds.Circuit.mk (gs ++ hs) o) x).getD i false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires (PEqualNP.CircuitLowerBounds.Circuit.mk gs o') x).getD i false := by
  intro gs hs o o' x i hi
  exact PEqualNP.Outside.L_meta_476.wires_append gs hs o o' x i hi
