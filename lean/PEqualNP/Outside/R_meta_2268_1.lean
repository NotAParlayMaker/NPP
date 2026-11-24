import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_2268_1_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def IsClean (n : ℕ) (C : Circuit) : Prop :=
  FanInTwo C ∧
  C.output < n + C.gates.length ∧
  ∀ i : Fin C.gates.length,
    let g := C.gates.get i
    (g.op = GateOp.not → g.inputs.length = 1) ∧
    ((g.op = GateOp.and ∨ g.op = GateOp.or) →
      g.inputs.length = 2 ∧ g.inputs.headD 0 ≠ g.inputs.tail.headD 0) ∧
    (∀ w ∈ g.inputs, w < n + (i : ℕ))

end PEqualNP.Outside.R_meta_2268_1_aux

theorem PEqualNP.Outside.R_meta_2268_1
    (h1 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      (∃ x y : Fin n → Bool, f x ≠ f y) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.Outside.R_meta_2268_1_aux.IsClean n D ∧ D.size ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x)
    (h2 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1))
      (x4 : (Fin x1 → Bool) → Bool),
      x2.Colorable (2 : ℕ) →
      (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →
      (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
      (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
      (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
      (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔
        (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨
        ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.Outside.R_meta_2268_1_aux.IsClean x1 D →
        (∀ x : Fin x1 → Bool, D.eval (List.ofFn x) = x4 x) →
        ∃ (x13 : Fin x1) (x14 : Fin x1),
          x13 ∉ x3 ∧ x14 ∉ x3 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧
          ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ D.size ∧
            PEqualNP.MetaComplexity.HasCircuitSize x1
              (fun (x16 : Fin x1 → Bool) =>
                x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false))
              x15) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x13 ≠ x14 ∧ ¬x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  intro x1 x2 x3 x4 hcol hdeg hcyc hno_or hedge hfun x11 hhas
  obtain ⟨C, hCfan, hCsize, hCeval⟩ := hhas
  have hnonconst : ∃ x y : Fin x1 → Bool, x4 x ≠ x4 y := by
    refine ⟨fun _ => Bool.false, fun _ => Bool.true, ?_⟩
    have h0 : x4 (fun _ => Bool.false) = Bool.false := by
      cases hval : x4 (fun _ => Bool.false) with
      | false => rfl
      | true =>
        have h := (hfun (fun _ => Bool.false)).mp hval
        rcases h with ⟨v, _, hv⟩ | ⟨u, v, _, hu, _⟩
        · cases hv
        · cases hu
    have h1val : x4 (fun _ => Bool.true) = Bool.true := by
      obtain ⟨u, v, huv⟩ := hedge
      exact (hfun (fun _ => Bool.true)).mpr (Or.inr ⟨u, v, huv, rfl, rfl⟩)
    rw [h0, h1val]
    decide
  obtain ⟨D, hDclean, hDsize, hDeval⟩ := h1 x1 x4 C hCfan hCeval hnonconst
  obtain ⟨x13, x14, h13, h14, hne, hnadj, x15, hx15le, hhas'⟩ :=
    h2 x1 x2 x3 x4 hcol hdeg hcyc hno_or hedge hfun D hDclean hDeval
  exact ⟨x13, x14, h13, h14, hne, hnadj, x15, Nat.le_trans hx15le (Nat.le_trans hDsize hCsize), hhas'⟩
