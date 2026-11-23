import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_311_aux

private def step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [step, List.length_append, List.length_singleton]
      omega

private lemma foldl_getD_lt (hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
    (i : ℕ) (hi : i < w.length) :
    (hs.foldl step w).getD i false = w.getD i false := by
  induction hs generalizing w with
  | nil => rfl
  | cons g rest ih =>
      simp only [List.foldl_cons]
      have hlt : i < (step w g).length := by
        simp only [step, List.length_append, List.length_singleton]
        omega
      rw [ih (step w g) hlt]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

end PEqualNP.Outside.L_meta_311_aux

theorem PEqualNP.Outside.L_meta_311 :
    ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (o o' : ℕ) (x : List Bool) (i : ℕ),
      i < x.length + gs.length →
      (PEqualNP.CircuitLowerBounds.Circuit.wires
        (PEqualNP.CircuitLowerBounds.Circuit.mk (gs ++ hs) o) x).getD i false =
      (PEqualNP.CircuitLowerBounds.Circuit.wires
        (PEqualNP.CircuitLowerBounds.Circuit.mk gs o') x).getD i false := by
  intro gs hs o o' x i hi
  change ((gs ++ hs).foldl PEqualNP.Outside.L_meta_311_aux.step x).getD i false =
    (gs.foldl PEqualNP.Outside.L_meta_311_aux.step x).getD i false
  rw [List.foldl_append]
  have hlen : i < (gs.foldl PEqualNP.Outside.L_meta_311_aux.step x).length := by
    rw [PEqualNP.Outside.L_meta_311_aux.foldl_length]
    exact hi
  exact PEqualNP.Outside.L_meta_311_aux.foldl_getD_lt hs _ i hlen
