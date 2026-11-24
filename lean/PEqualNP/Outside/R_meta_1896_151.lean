import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadTwo

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_1896_151
    (normalize : ∀ C : Circuit, Monotone2 C →
      let r := {i : Fin C.gates.length | (C.gates.get i).op = GateOp.or}.ncard
      ∃ D : Circuit, (∀ g ∈ D.gates, g.op = GateOp.and ∨ (g.op = GateOp.or ∧ g.inputs.length ≤ 2)) ∧
        D.size ≤ 3*r+1 ∧ nOr D ≤ r ∧ circuitFun 26 D = circuitFun 26 C)
    (bounded : let inc := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      ∀ D : Circuit, D.size ≤ 151 →
      (∀ g ∈ D.gates, g.op = GateOp.and ∨ (g.op = GateOp.or ∧ g.inputs.length ≤ 2)) →
      (∀ p l : Fin 13, inc p l → circuitFun 26 D (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
      (∀ X : Finset (Fin 13), let off := fun l : Fin 13 => ∀ p ∈ X, ¬ inc p l
        (∀ p ∉ X, ∃ l, off l ∧ inc p l) →
        ((¬ ∃ l, ∀ p ∈ X, inc p l) ∧ ¬ ∃ p, ∀ l, off l → inc p l) →
        circuitFun 26 D (fun i => decide ((∃ p ∈ X, i = Fin.castAdd 13 p) ∨ ∃ l, i = Fin.natAdd 13 l ∧ off l)) = false) →
      51 ≤ nOr D) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (51 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C hm hp hn
  by_contra! small
  obtain ⟨D, hshape, hsize, hcount, heq⟩ := normalize C hm
  have hD := bounded D (by omega) hshape
    (fun p l hi => (congrFun heq _).trans (hp p l hi))
    (fun X hx hg => (congrFun heq _).trans (hn X hx hg))
  omega
