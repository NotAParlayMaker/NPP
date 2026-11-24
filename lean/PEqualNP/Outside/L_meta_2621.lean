import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2621_aux

open PEqualNP.CircuitLowerBounds

def F (C : Circuit) (k : ℕ) (w : List Bool) (i : ℕ) : Bool :=
  if i < 26 then decide (i = k) else
  match C.gates[i - 26]? with
  | some g =>
    match g.inputs with
    | [a, b] =>
      if _ha : a < i then
        if _hb : b < i then
          match g.op with
          | GateOp.and => (w.getD a false && F C k w b || F C k w a && w.getD b false)
          | GateOp.or => (F C k w a || F C k w b)
          | _ => false
        else false
      else false
    | _ => false
  | none => false
termination_by i

end PEqualNP.Outside.L_meta_2621_aux

open PEqualNP.Outside.L_meta_2621_aux in
theorem PEqualNP.Outside.L_meta_2621 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → ∀ (x3 : ℕ) (x4 : List Bool), ∃ (x5 : ℕ → Bool), (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = x3)) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x4.getD x8 Bool.false && x5 x9 || x5 x8 && x4.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9)) := by
  intro C hC k w
  refine ⟨F C k w, ?_, ?_⟩
  · intro i hi
    rw [F]; simp [hi]
  · intro j g a b hg hin
    obtain ⟨_, hrb, _⟩ := hC
    have hj : j < C.gates.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hg]
    have ha : a < 26 + j := hrb j hj a (by rw [hga, hin]; simp)
    have hb : b < 26 + j := hrb j hj b (by rw [hga, hin]; simp)
    have e1 : ¬ (26 + j < 26) ↔ True := by simp
    have e2 : 26 + j - 26 = j := by omega
    constructor
    · intro hop
      rw [F]; simp [e2, hg, hin, ha, hb, hop]
    · intro hop
      rw [F]; simp [e2, hg, hin, ha, hb, hop]
