import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7690

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    unfold step
    simp
    omega

lemma foldl_step_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    (gs ++ [g]).foldl step w =
      gs.foldl step w ++ [g.op.eval (g.inputs.map fun i => (gs.foldl step w).getD i false)] := by
  simp [step, List.foldl_append]

lemma wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  rw [wires_eq, Circuit.size, foldl_step_len]

end PEqualNP.Outside.L_meta_7690

theorem PEqualNP.Outside.L_meta_7690 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.GateOp), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 ∈ x1.gates, x6.inputs.Nodup) → x4 = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x4 = PEqualNP.CircuitLowerBounds.GateOp.and → x2 < (14 : ℕ) + x1.size → x3 < (14 : ℕ) + x1.size → x2 ≠ x3 → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x11.size = x1.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x11 ∧ (∀ x12 ∈ x11.gates, x12.inputs.Nodup) ∧ x11.output = (14 : ℕ) + x1.size ∧ x11.gates[x1.size]? = Option.some { op := x4, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x12 : Fin (14 : ℕ) → Bool), (∀ x13 < (14 : ℕ) + x1.size, PEqualNP.BlindGate.wireValue x11 (14 : ℕ) x12 x13 = PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x12 x13) ∧ PEqualNP.BlindGate.wireValue x11 (14 : ℕ) x12 x11.output = x4.eval [PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x12 x2, PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x12 x3] := by
  intro C a b op hAO hnd hop ha hb hab
  let gNew : PEqualNP.CircuitLowerBounds.Gate := ⟨op, [a, b]⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates ++ [gNew], 14 + C.size⟩
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp [D, List.mem_append] at hg
      rcases hg with hg | hg
      · exact hAO.1 g hg
      · have : g = gNew := by simpa [gNew] using hg
        subst this
        exact hop.elim Or.inr Or.inl
    · intro j hj i hi
      have hj' : j < C.gates.length + 1 := by
        simpa [D, PEqualNP.CircuitLowerBounds.Circuit.size] using hj
      by_cases hjC : j < C.gates.length
      · have hget : (PEqualNP.MetaComplexity.NestedCover.gateAt D j) = PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
          simp [D, PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hjC]
        have hiC : i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs := by
          simpa [hget] using hi
        exact hAO.2.1 j hjC i hiC
      · have hjEq : j = C.gates.length := by omega
        subst hjEq
        have hget : PEqualNP.MetaComplexity.NestedCover.gateAt D C.gates.length = gNew := by
          simp [D, gNew, PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
            List.getElem?_append_right]
        have hiN : i ∈ gNew.inputs := by
          simpa [hget] using hi
        simp [gNew] at hiN
        rcases hiN with rfl | rfl
        · exact ha
        · exact hb
    · intro g hg
      simp [D, List.mem_append] at hg
      rcases hg with hg | hg
      · exact hAO.2.2 g hg
      · have : g = gNew := by simpa [gNew] using hg
        subst this
        simp [gNew]
  · intro g hg
    simp [D, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hnd g hg
    · have : g = gNew := by simpa [gNew] using hg
      subst this
      simpa [gNew, List.nodup_cons] using hab
  · rfl
  · simp [D, gNew, PEqualNP.CircuitLowerBounds.Circuit.size, List.getElem?_append_right]
  · intro x
    constructor
    · intro i hi
      change (D.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false
      rw [PEqualNP.Outside.L_meta_7690.wires_eq, PEqualNP.Outside.L_meta_7690.wires_eq]
      simp only [D]
      rw [PEqualNP.Outside.L_meta_7690.foldl_step_snoc]
      have hlen : (C.gates.foldl PEqualNP.Outside.L_meta_7690.step (List.ofFn x)).length = 14 + C.size := by
        simpa [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_ofFn] using
          PEqualNP.Outside.L_meta_7690.foldl_step_len C.gates (List.ofFn x)
      exact List.getD_append _ _ _ _ (by omega)
    · change (D.wires (List.ofFn x)).getD D.output false =
        op.eval [(C.wires (List.ofFn x)).getD a false, (C.wires (List.ofFn x)).getD b false]
      rw [PEqualNP.Outside.L_meta_7690.wires_eq, PEqualNP.Outside.L_meta_7690.wires_eq]
      simp only [D]
      rw [PEqualNP.Outside.L_meta_7690.foldl_step_snoc]
      have hlen : (C.gates.foldl PEqualNP.Outside.L_meta_7690.step (List.ofFn x)).length = 14 + C.size := by
        simpa [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_ofFn] using
          PEqualNP.Outside.L_meta_7690.foldl_step_len C.gates (List.ofFn x)
      simp [gNew]
      rw [← hlen]
      simp [List.getD_append_right]
