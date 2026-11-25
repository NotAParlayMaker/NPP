import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5989
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_5989

open PEqualNP.Outside.L_meta_5989 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5989 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (62 : ℕ) → ∀ (x4 x5 : Fin ((26 : ℕ) + x1.size)), x4 ≠ x5 → ∀ (x7 : Set (Fin (26 : ℕ) → Bool)) (x8 : (Fin (26 : ℕ) → Bool) → Bool), (∀ x9 ∈ x7, (x1.wireOn x9 ↑x4 || x1.wireOn x9 ↑x5) = x8 x9) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ (63 : ℕ) ∧ ∀ x11 ∈ x7, PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x10 x11 = x8 x11 := by
  intro C hm hs a b _ X f hf
  refine ⟨⟨C.gates ++ [⟨GateOp.or, [(a : ℕ), (b : ℕ)]⟩], 26 + C.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hm g h
    · simp only [List.mem_singleton] at h
      subst h
      exact ⟨Or.inr rfl, by simp⟩
  · show (C.gates ++ [(⟨GateOp.or, [(a : ℕ), (b : ℕ)]⟩ : Gate)]).length ≤ 63
    have : C.gates.length ≤ 62 := hs
    simp
    omega
  · intro x hx
    rw [← hf x hx]
    show (wf (C.gates ++ [(⟨GateOp.or, [(a : ℕ), (b : ℕ)]⟩ : Gate)]) (List.ofFn x)).getD (26 + C.gates.length) false
      = ((wf C.gates (List.ofFn x)).getD (a : ℕ) false || (wf C.gates (List.ofFn x)).getD (b : ℕ) false)
    rw [wf_snoc]
    have hl : (wf C.gates (List.ofFn x)).length = 26 + C.gates.length := by
      rw [wf_len]; simp
    rw [← hl, getD_snoc_eq]
    simp [GateOp.eval]
