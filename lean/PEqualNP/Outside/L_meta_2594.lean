import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2594_aux

namespace Relabel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

end Relabel

end PEqualNP.Outside.L_meta_2594_aux

open PEqualNP.Outside.L_meta_2594_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_2594 :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x3 →
      ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧
          ∀ (x6 : Fin x1 → Bool) (x7 : Bool),
            x5.eval (List.ofFn x6 ++ [x7]) =
              x3.eval (List.ofFn (x6 ∘ x2) ++ [x7]) := by
  intro n π C hfan
  let π' : Fin (n + 1) → Fin (n + 1) :=
    Fin.snoc (fun i => Fin.castSucc (π i)) (Fin.last n)
  let C' : Circuit := Relabel.relabel (n + 1) (n + 1) π' C
  have hfan' : FanInTwo C' := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hfan g0 hg0).1, by simpa [C', Relabel.relGate] using (hfan g0 hg0).2⟩
  have hsize : C'.size = C.size := by
    simp [C', Relabel.relabel, Circuit.size]
  refine ⟨C', hfan', hsize, ?_⟩
  intro x6 x7
  let l : List Bool := List.ofFn x6 ++ [x7]
  let l' : List Bool := List.ofFn (fun i => x6 (π i)) ++ [x7]
  let x : Fin (n + 1) → Bool := fun i => l[i]'(by simp [l]; omega)
  have hx : List.ofFn x = l := by simpa [x, l] using (List.ofFn_getElem (xs := l))
  have hcomp : (x ∘ π') = fun i => l'[i]'(by simp [l']; omega) := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp [x, l, l', π', Fin.snoc]
    · intro j
      simp [x, l, l', π', Fin.snoc]
  have hx' : List.ofFn (x ∘ π') = l' := by
    rw [hcomp]
    simpa [l'] using (List.ofFn_getElem (xs := l'))
  change C'.eval l = C.eval l'
  rw [← hx, ← hx']
  show C'.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π'))
  unfold Circuit.eval
  exact (Relabel.rel_fold (n + 1) (n + 1) π' C.gates (List.ofFn (x ∘ π')) (List.ofFn x)
    (Relabel.rel_init (n + 1) (n + 1) π' x)).2.2 C.output
