import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8831
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

end PEqualNP.Outside.L_meta_8831

open PEqualNP.Outside.L_meta_8831 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8831 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → x1 ≤ x4.output ∧ x4.output < x1 + x4.size := by
  intro n G _ C hf ⟨a, b, hab⟩
  have hval : ∀ y : Fin n → Bool, (wf C.gates (List.ofFn y)).getD C.output false
      = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y := fun y => congrFun hf y
  have hne : a ≠ b := fun h => G.loopless.irrefl a (h ▸ hab)
  have htrue : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (fun i => decide (i = a ∨ i = b)) = true := by
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    simp only [Bool.or_eq_true, decide_eq_true_iff]
    exact Or.inr ⟨a, b, hab, by simp, by simp⟩
  have hone : ∀ (c : Fin n) (y : Fin n → Bool), (∀ i, y i = true → i = c) →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = false := by
    intro c y hy
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_false_iff_not]
    rintro ⟨u, w, huw, hu, hw⟩
    rw [hy u hu, hy w hw] at huw
    exact G.loopless.irrefl c huw
  constructor
  · by_contra hlt
    push_neg at hlt
    have h1 := hval (fun i => decide (i = (⟨C.output, hlt⟩ : Fin n)))
    rw [hone ⟨C.output, hlt⟩ _ (by simp), wf_keep _ _ _ (by simpa using hlt)] at h1
    have h2 := getD_ofFn (fun i => decide (i = (⟨C.output, hlt⟩ : Fin n))) ⟨C.output, hlt⟩
    simp only at h2
    rw [h2] at h1
    simp at h1
  · by_contra hge
    have h1 := hval (fun i => decide (i = a ∨ i = b))
    rw [htrue, List.getD_eq_default _ _ (by
      rw [wf_len]
      simp
      have : C.size = C.gates.length := rfl
      omega)] at h1
    simp at h1
