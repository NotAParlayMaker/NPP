import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_591_aux

open PEqualNP.CircuitLowerBounds

def wire {n : ℕ} (u v : Fin n) (i : ℕ) : ℕ :=
  if i = u.val then v.val else i

def redirect {n : ℕ} (u v : Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire u v)⟩

private lemma lookupInput {n : ℕ} (x : Fin n → Bool) (t : List Bool) (j : Fin n) :
    (List.ofFn x ++ t).getD j.val false = x j := by
  have hj : j.val < (List.ofFn x).length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hj,
    List.getElem?_eq_getElem hj]
  simp

private lemma lookup {n : ℕ} (u v : Fin n) (x : Fin n → Bool) (t : List Bool) (i : ℕ) :
    (List.ofFn x ++ t).getD (wire u v i) false =
    (List.ofFn (Function.update x u (x v)) ++ t).getD i false := by
  by_cases h : i = u.val
  · subst i
    rw [show wire u v u.val = v.val by simp [wire], lookupInput, lookupInput]
    simp
  · rw [show wire u v i = i by simp [wire, h]]
    by_cases hi : i < n
    · let j : Fin n := ⟨i, hi⟩
      have hj : j ≠ u := fun he => h (congrArg Fin.val he)
      change (List.ofFn x ++ t).getD j.val false =
        (List.ofFn (Function.update x u (x v)) ++ t).getD j.val false
      rw [lookupInput, lookupInput, Function.update_of_ne hj]
    · have hx : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_gt hi
      have hy : (List.ofFn (Function.update x u (x v))).length ≤ i := by simpa using Nat.le_of_not_gt hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hx,
        List.getElem?_append_right hy, List.length_ofFn]

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma evaluate {n : ℕ} (u v : Fin n) (x : Fin n → Bool) (gs : List Gate)
    (t : List Bool) (o : ℕ) :
    ((gs.map (redirect u v)).foldl step (List.ofFn x ++ t)).getD (wire u v o) false =
    (gs.foldl step (List.ofFn (Function.update x u (x v)) ++ t)).getD o false := by
  induction gs generalizing t with
  | nil => exact lookup u v x t o
  | cons g gs ih =>
    let y := Function.update x u (x v)
    let b := g.op.eval (g.inputs.map fun i => (List.ofFn y ++ t).getD i false)
    have hargs :
        (g.inputs.map (wire u v)).map (fun i => (List.ofFn x ++ t).getD i false) =
        g.inputs.map (fun i => (List.ofFn y ++ t).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact lookup u v x t i
    have hstep : step (List.ofFn x ++ t) (redirect u v g) = List.ofFn x ++ (t ++ [b]) := by
      simp only [step, redirect, hargs, List.append_assoc, b]
    have hstep' : step (List.ofFn y ++ t) g = List.ofFn y ++ (t ++ [b]) := by
      simp only [step, b, List.append_assoc]
    change (List.foldl step (step (List.ofFn x ++ t) (redirect u v g)) (gs.map (redirect u v))).getD (wire u v o) false =
      (List.foldl step (step (List.ofFn y ++ t) g) gs).getD o false
    rw [hstep, hstep']
    exact ih (t ++ [b])

def transform {n : ℕ} (u v : Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (redirect u v), wire u v C.output⟩

lemma transform_eval {n : ℕ} (u v : Fin n) (C : Circuit) (x : Fin n → Bool) :
    (transform u v C).eval (List.ofFn x) = C.eval (List.ofFn (Function.update x u (x v))) := by
  have hh := evaluate u v x C.gates [] C.output
  unfold step at hh
  simpa only [Circuit.eval, Circuit.wires, transform, List.append_nil] using hh

end PEqualNP.Outside.L_meta_591_aux

namespace PEqualNP.Outside

open L_meta_591_aux

theorem L_meta_591 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n), PEqualNP.MetaComplexity.HasCircuitSize n F s → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => F (Function.update x u (x v))) s := by
  intro n s F u v h
  obtain ⟨C, hfan, hsize, heval⟩ := h
  refine ⟨transform u v C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa [redirect] using hfan g' hg'
  · simpa [transform, PEqualNP.CircuitLowerBounds.Circuit.size] using hsize
  · intro x
    exact (transform_eval u v C x).trans (heval _)

end PEqualNP.Outside
