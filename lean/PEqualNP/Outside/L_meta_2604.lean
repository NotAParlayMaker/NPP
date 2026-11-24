import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2604_aux

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

lemma core (n : ℕ) (A B : List Gate) (u t out : ℕ) (x : List Bool) (hx : x.length = n)
    (ht : t < n + A.length)
    (hyp : ((A ++ (Gate.mk GateOp.or [u, t]) :: B).foldl stepW x).getD t false = true →
      ((A ++ (Gate.mk GateOp.or [u, t]) :: B).foldl stepW x).getD out false = true) :
    ((A ++ (Gate.mk GateOp.or [u]) :: B ++ [(Gate.mk GateOp.or [out, t])]).foldl stepW x).getD
      (n + (A ++ (Gate.mk GateOp.or [u, t]) :: B).length) false
    = ((A ++ (Gate.mk GateOp.or [u, t]) :: B).foldl stepW x).getD out false := by
  have hl0 : (A.foldl stepW x).length = n + A.length := by rw [fold_len, hx]
  have htv : ∀ g : Gate, ∀ C : List Gate,
      ((A ++ g :: C).foldl stepW x).getD t false = (A.foldl stepW x).getD t false := by
    intro g C
    rw [List.foldl_append, fold_get _ _ _ (by omega)]
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have hL : ((A ++ (Gate.mk GateOp.or [u]) :: B).foldl stepW x).length = n + (A ++ (Gate.mk GateOp.or [u, t]) :: B).length := by
    rw [fold_len]; simp [hx]
  rw [stepW, List.getD_append_right _ _ _ _ (by rw [hL])]
  simp only [hL, Nat.sub_self, List.getD_cons_zero, GateOp.eval, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, id, Bool.or_false]
  have ht1 := htv (Gate.mk GateOp.or [u]) B
  have ht2 := htv (Gate.mk GateOp.or [u, t]) B
  rw [ht1]
  cases hT : (A.foldl stepW x).getD t false
  · have hsame : stepW (A.foldl stepW x) (Gate.mk GateOp.or [u]) = stepW (A.foldl stepW x) (Gate.mk GateOp.or [u, t]) := by
      simp only [List.getD_eq_getElem?_getD] at hT; simp [stepW, GateOp.eval, hT]
    rw [List.foldl_append, List.foldl_cons, hsame, ← List.foldl_cons, ← List.foldl_append]
    simp
  · have := hyp (by rw [ht2, hT])
    rw [List.foldl_append, List.foldl_cons] at this; simp at this ⊢; simp [this]

end PEqualNP.Outside.L_meta_2604_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2604_aux in
theorem PEqualNP.Outside.L_meta_2604 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ), PEqualNP.MetaComplexity.Monotone2 C → j < C.gates.length → C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } → t < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }], output := n + C.gates.length } = PEqualNP.MetaComplexity.circuitFun n C := by
  intro n C j u t _ hj hg ht hyp
  funext x
  obtain ⟨gs, out⟩ := C
  simp only at hj hg ht hyp ⊢
  have hdec : gs = gs.take j ++ (Gate.mk GateOp.or [u, t]) :: gs.drop (j + 1) := by
    have h1 : gs[j] = (Gate.mk GateOp.or [u, t]) := by
      rw [List.getElem?_eq_getElem hj] at hg; exact Option.some.inj hg
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj, h1]
  have hset : gs.set j (Gate.mk GateOp.or [u]) = gs.take j ++ (Gate.mk GateOp.or [u]) :: gs.drop (j + 1) := by
    simp [List.set_eq_take_append_cons_drop, hj]
  have hA : (gs.take j).length = j := by simp; omega
  have key := core n (gs.take j) (gs.drop (j + 1)) u t out (List.ofFn x) (by simp) (by omega)
    (by intro h; rw [← hdec] at h ⊢; exact hyp x h)
  rw [← hdec] at key
  show List.getD (List.foldl stepW (List.ofFn x) (gs.set j (Gate.mk GateOp.or [u]) ++ [(Gate.mk GateOp.or [out, t])])) _ false
    = List.getD (List.foldl stepW (List.ofFn x) gs) out false
  rw [hset]
  exact key

