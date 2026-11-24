import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2727_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

lemma fold_pre (gs : List Gate) : ∀ w : List Bool, ∃ s, gs.foldl stepW w = w ++ s := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨s, hs⟩ := ih (stepW w g)
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: s, by rw [List.foldl_cons, hs]; simp [stepW]⟩

lemma fold_get (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  obtain ⟨s, hs⟩ := fold_pre gs w
  rw [hs]; exact List.getD_append _ _ _ _ h

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

end PEqualNP.Outside.L_meta_2727_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2727_aux in
theorem PEqualNP.Outside.L_meta_2727 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ),
  j < C.gates.length →
  C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [u, t] } →
  u < n + j → t < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD u false = true →
      (C.wires (List.ofFn x)).getD t false = true) →
  ∀ x : Fin n → Bool,
    ({ gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] },
       output := C.output } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x) =
    C.wires (List.ofFn x) := by
  intro n C j u t hj hg hu ht hyp x
  obtain ⟨gs, out⟩ := C
  simp only at hj hg hyp ⊢
  have hdec : gs = gs.take j ++ (Gate.mk GateOp.and [u, t]) :: gs.drop (j + 1) := by
    have h1 : gs[j] = (Gate.mk GateOp.and [u, t]) := by
      rw [List.getElem?_eq_getElem hj] at hg; exact Option.some.inj hg
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj, h1]
  have hset : gs.set j (Gate.mk GateOp.or [u]) = gs.take j ++ (Gate.mk GateOp.or [u]) :: gs.drop (j + 1) := by
    simp [List.set_eq_take_append_cons_drop, hj]
  have hA : (gs.take j).length = j := by simp; omega
  have hW : ((gs.take j).foldl stepW (List.ofFn x)).length = n + j := by rw [fold_len]; simp [hA]
  have hwires : ∀ G : List Gate, (Circuit.mk G out).wires (List.ofFn x) = G.foldl stepW (List.ofFn x) := by
    intro G; rfl
  have hyp' := hyp x
  rw [hwires, hdec, List.foldl_append, List.foldl_cons] at hyp'
  generalize hWd : (gs.take j).foldl stepW (List.ofFn x) = W at hW hyp'
  have hs : ∀ g : Gate, ∀ i, i < W.length → ((gs.drop (j + 1)).foldl stepW (stepW W g)).getD i false = W.getD i false := by
    intro g i hi
    rw [fold_get _ _ _ (by simp [stepW]; omega)]
    exact List.getD_append _ _ _ _ hi
  rw [hs _ _ (by omega), hs _ _ (by omega)] at hyp'
  rw [hwires, hwires, hset]
  conv_rhs => rw [hdec]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, hWd]
  congr 1
  simp only [stepW, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true]
  cases hU : W.getD u false
  · rfl
  · rw [hyp' hU]; rfl
