import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- Use an extra false input for missing wires and preserve the effective reads
-- of the original input wires, including the first-operand rule for NOT.
theorem PEqualNP.Outside.R_meta_3553_381
    (normalize : ∀ (n : ℕ) (C : Circuit), FanInTwo C →
      let reads := fun (C : Circuit) (j w : ℕ) =>
        let g := gateAt C j
        g.inputs[0]? = some w ∨ g.op ≠ .not ∧ w ∈ g.inputs
      ∃ D : Circuit, D.size = C.size ∧ D.output < n+1+D.size ∧
      (∀ j g, D.gates[j]? = some g →
        (∀ w ∈ g.inputs, w < n+1+j) ∧
        ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∨
          g.op = .not ∧ g.inputs.length = 1)) ∧
      (∀ j < C.size, ∀ w < n, reads C j w ↔ reads D j w) ∧
      ∀ x : List Bool, x.length = n → D.eval (x ++ [false]) = C.eval x)
    (bound : ∀ D : Circuit, D.output < 11+D.size →
      (∀ j g, D.gates[j]? = some g →
        (∀ w ∈ g.inputs, w < 11+j) ∧
        ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∨
          g.op = .not ∧ g.inputs.length = 1)) →
      let reads := fun (C : Circuit) (j w : ℕ) =>
        let g := gateAt C j
        g.inputs[0]? = some w ∨ g.op ≠ .not ∧ w ∈ g.inputs
      (∃ a b : ℕ, a < b ∧ b < D.size ∧ reads D a 6 ∧ reads D b 4 ∧
        (∀ j < D.size, reads D j 6 → j = a) ∧ (∀ j < D.size, reads D j 4 → j = b)) →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6,false]) =
        ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))) →
      15 ≤ D.size) :
∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } →     (∀ (x4 : Fin (9 : ℕ) → Bool), { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x4 ++ [x4 (4 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ))]) = (fun (x5 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (9 : ℕ) (x6 / (9 : ℕ))) && x5 (Fin.ofNat (9 : ℕ) (x6 % (9 : ℕ)))) x4) →       (∃ (x5 : Fin x1.length) (x6 : Fin x1.length),           x5 < x6 ∧             (have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.get x5;               x7.inputs[(0 : ℕ)]? = Option.some (6 : ℕ) ∨ x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (6 : ℕ) ∈ x7.inputs) ∧               (have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.get x6;                 x7.inputs[(0 : ℕ)]? = Option.some (4 : ℕ) ∨ x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (4 : ℕ) ∈ x7.inputs) ∧                 (∀ (x7 : Fin x1.length),                     (have x8 : PEqualNP.CircuitLowerBounds.Gate := x1.get x7;                       x8.inputs[(0 : ℕ)]? = Option.some (6 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (6 : ℕ) ∈ x8.inputs) →                       x7 = x5) ∧                   ∀ (x7 : Fin x1.length),                     (have x8 : PEqualNP.CircuitLowerBounds.Gate := x1.get x7;                       x8.inputs[(0 : ℕ)]? = Option.some (4 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (4 : ℕ) ∈ x8.inputs) →                       x7 = x6) →         (15 : ℕ) ≤ x1.length := by

  intro gates out fan computes readsOriginal
  let C : Circuit := ⟨gates,out⟩
  let reads (A : Circuit) (j w : ℕ) :=
    let g := gateAt A j
    g.inputs[0]? = some w ∨ g.op ≠ .not ∧ w ∈ g.inputs
  obtain ⟨D, size, output, shape, refs, eval⟩ := normalize 10 C fan
  have expose (j : Fin gates.length) : gateAt C j.val = gates.get j := by
    change gates.getD j.val ⟨.or,[]⟩ = gates.get j
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt]
    rfl
  have preserve (j : Fin gates.length) (w : ℕ) (hw : w < 10) :
      (let g := gates.get j
       g.inputs[0]? = some w ∨ g.op ≠ .not ∧ w ∈ g.inputs) ↔ reads D j.val w := by
    have h := refs j.val (show j.val < C.size from j.isLt) w hw
    change reads C j.val w ↔ reads D j.val w at h
    simpa only [reads, expose] using h
  obtain ⟨a,b,ab,ha,hb,onlyA,onlyB⟩ := readsOriginal
  have newReads : ∃ u v : ℕ, u < v ∧ v < D.size ∧ reads D u 6 ∧ reads D v 4 ∧
      (∀ j < D.size, reads D j 6 → j = u) ∧ (∀ j < D.size, reads D j 4 → j = v) := by
    refine ⟨a.val,b.val,ab,?_,(preserve a 6 (by decide)).mp ha,(preserve b 4 (by decide)).mp hb,?_,?_⟩
    · rw [size]; exact b.isLt
    · intro j hj h
      let k : Fin gates.length := ⟨j,by rw [size] at hj; exact hj⟩
      exact congrArg Fin.val (onlyA k ((preserve k 6 (by decide)).mpr h))
    · intro j hj h
      let k : Fin gates.length := ⟨j,by rw [size] at hj; exact hj⟩
      exact congrArg Fin.val (onlyB k ((preserve k 4 (by decide)).mpr h))
  rw [← show C.size = gates.length from rfl, ← size]
  apply bound D output shape newReads
  intro x
  rw [show List.ofFn x ++ [x 4 || x 6,false] = (List.ofFn x ++ [x 4 || x 6]) ++ [false] by
    simp only [List.append_assoc,List.cons_append,List.nil_append]]
  exact (eval _ (by simp)).trans (computes x)
