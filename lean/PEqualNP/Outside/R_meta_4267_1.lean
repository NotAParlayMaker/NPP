import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- L-meta-2960 excludes NOT gates in an eleven-gate circuit for this graph.
-- The rows encode minimal true inputs and maximal false inputs of both functions.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4267_1
    (bound : ∀ C : Circuit, FanInTwo C →
      circuitFun 7 C = (fun x : Fin 7 → Bool =>
        ([(0,1), (1,2), (0,4), (1,5), (2,6), (3,5), (4,6), (6,3)] :
          List (Fin 7 × Fin 7)).any (fun e => x e.1 && x e.2)) →
      11 ≤ C.gates.countP (fun g =>
        GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op))
    (clean : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C → Monotone2 C →
      0 < C.gates.length →
      (∃ x y, circuitFun n C x ≠ circuitFun n C y) →
      C.output + 1 = n + C.gates.length ∧
      ∀ (j : ℕ) (h : j < C.gates.length), ∃ p q : ℕ,
        C.gates[j].inputs = [p,q] ∧ p ≠ q ∧ p < n+j ∧ q < n+j)
    (pinCost : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 7 → Bool, D.eval (true :: List.ofFn (Function.update x 2 false)) =
        ([1,4,15,35,46,36] : List ℕ).any
          (fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10)))) →
      8 + (D.gates.filter (fun g =>
        g.inputs.contains 0 || g.op.eval [true,false] && g.inputs.contains 3)).length ≤ D.gates.length)
    (exclude :
      let x (m : ℕ) (i : Fin 7) := m.testBit i.val
      ∀ (C D : Circuit) (a b : ℕ), C.gates.length = 11 → C.output = 17 → Monotone2 C →
      (∀ (j : ℕ) (h : j < C.gates.length), ∃ p q : ℕ,
        C.gates[j].inputs = [p,q] ∧ p ≠ q ∧ p < 7+j ∧ q < 7+j) →
      List.Forall₂ (fun g h : Gate => g.op = h.op ∧
        List.Forall₂ (fun p q => q = p+1 ∨ q = 0 ∧ (p = a ∨ p = b)) g.inputs h.inputs)
        C.gates D.gates →
      (D.gates.filter (fun g =>
        g.inputs.contains 0 || g.op.eval [true,false] && g.inputs.contains 3)).length ≤ 3 →
      (∀ m ∈ ([4,9,13,26,28,37,48,52,66,97,131,134,145,162,168,196,200,208] : List ℕ),
        C.eval (List.ofFn (x m)) = m.testBit 7 ∧
        (D.wires (true :: List.ofFn (x m))).getD 18 false = (m.testBit 7 || m.testBit 2)) →
      (∀ m ∈ ([9,26,48,66,97] : List ℕ),
        ¬ ∀ g ∈ C.gates, 2 ∈ g.inputs → g.op = .or ∧
          ∃ i : Fin 7, i ≠ 2 ∧ i.val ∈ g.inputs ∧ x m i = true) →
      (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length < 2) :
    have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (2 : Fin (7 : ℕ)))) → (∀ (x11 : Fin (7 : ℕ) → Bool), x11 (2 : Fin (7 : ℕ)) = Bool.false → x1 x11 = Bool.false → ¬∀ x14 ∈ x2.gates, (2 : ℕ) ∈ x14.inputs → x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ (x17 : Fin (7 : ℕ)), x17 ≠ (2 : Fin (7 : ℕ)) ∧ ↑x17 ∈ x14.inputs ∧ x11 x17 = Bool.true) → (List.filter (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => x12.op.eval [Bool.true, Bool.false] && x12.inputs.contains (2 : ℕ)) x2.gates).length < (2 : ℕ) := by
  intro f C D a b fan size computes rewire edited unmasked
  let active (g : Gate) : Bool :=
    GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op
  have sizeLen : C.gates.length = 11 := size
  have graph : ∀ x, f x =
      ([(0,1), (1,2), (0,4), (1,5), (2,6), (3,5), (4,6), (6,3)] :
        List (Fin 7 × Fin 7)).any (fun e => x e.1 && x e.2) := by decide +kernel
  have base := computes.trans (funext graph)
  have keep : C.gates.countP active = C.gates.length := by
    have low := bound C fan base
    have high : C.gates.countP active ≤ C.gates.length := List.countP_le_length
    change 11 ≤ C.gates.countP active at low
    omega
  have mono : Monotone2 C := by
    intro g hm
    have valid := fan g hm
    have ops : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using valid.1
    have noNot (h : g.op = .not) : False := by
      have alive := List.countP_eq_length.mp keep g hm
      simp [active, h] at alive
    have ops' : g.op = .and ∨ g.op = .or := by
      rcases ops with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (noNot h).elim
    exact ⟨by simpa using ops', valid.2⟩
  have minC : IsMinimalCircuit 7 C := by
    refine ⟨fan, fun H hfan same => ?_⟩
    have low := bound H hfan (same.trans base)
    rw [size]
    exact low.trans List.countP_le_length
  have varying : ∃ x y, circuitFun 7 C x ≠ circuitFun 7 C y := by
    rw [computes]
    refine ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), ?_⟩
    decide +kernel
  obtain ⟨last, pins⟩ := clean 7 C minC mono (by omega) varying
  have out : C.output = 17 := by omega
  have lengthD : D.gates.length = 11 := rewire.length_eq.symm.trans sizeLen
  have monoD : Monotone2 D := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    have hiC : i < C.gates.length := rewire.length_eq.symm ▸ hi
    have rel := rewire.get hiC hi
    have hg := mono C.gates[i] (List.getElem_mem hiC)
    exact ⟨rel.1 ▸ hg.1, rel.2.length_eq ▸ hg.2⟩
  have cycle : ∀ x : Fin 7 → Bool,
      (f (Function.update x 2 false) || (Function.update x 2 false) 2) =
        ([1,4,15,35,46,36] : List ℕ).any
          (fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))) := by
    decide +kernel
  have thin : (D.gates.filter (fun g =>
      g.inputs.contains 0 || g.op.eval [true,false] && g.inputs.contains 3)).length ≤ 3 := by
    have cost := pinCost (Circuit.mk D.gates 18) (show Monotone2 (Circuit.mk D.gates 18) from monoD) (by
      intro x
      have h := edited (Function.update x 2 false)
      rw [out] at h
      exact h.trans (cycle x))
    change 8 + (D.gates.filter (fun g =>
      g.inputs.contains 0 || g.op.eval [true,false] && g.inputs.contains 3)).length ≤ D.gates.length at cost
    omega
  apply exclude C D a b sizeLen out mono pins rewire thin
  · intro m hm
    let x (i : Fin 7) := m.testBit i.val
    have values : ∀ m ∈ ([4,9,13,26,28,37,48,52,66,97,131,134,145,162,168,196,200,208] : List ℕ),
        f (fun i : Fin 7 => m.testBit i.val) = m.testBit 7 := by decide +kernel
    have h := values m hm
    refine ⟨(congrFun computes x).trans h, ?_⟩
    have hd := edited x
    rw [out] at hd
    rw [hd, h]
    rfl
  · intro m hm
    have negative : ∀ m ∈ ([9,26,48,66,97] : List ℕ),
        m.testBit 2 = false ∧ f (fun i : Fin 7 => m.testBit i.val) = false := by decide +kernel
    obtain ⟨off, zero⟩ := negative m hm
    exact unmasked _ off zero
