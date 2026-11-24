import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2112_624
    (nextGate : let target : (Fin 9 → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ));
      ∀ C : Circuit, FanInTwo C → C.size ≤ 15 → circuitFun 9 C = target → ReadsBack 9 C →
      (∀ i : Fin C.size, let g := C.gates.get i;
        (g.op = .not ∧ g.inputs.length = 1) ∨ (g.op ≠ .not ∧ g.inputs.length = 2)) →
      ∀ v ∈ ([4,6,7] : List (Fin 9)), ∀ j : Fin C.size,
      v.val ∈ (C.gates.get j).inputs →
      (∀ i : Fin C.size, v.val ∈ (C.gates.get i).inputs → i = j) →
      (C.gates.get j).op ≠ .or →
      ∃ k : Fin C.size, j < k ∧ 9+j.val ∈ (C.gates.get k).inputs ∧
        (∀ l : Fin C.size, 9+j.val ∈ (C.gates.get l).inputs → l = k) ∧
        (((C.gates.get j).op = .and ∧ (C.gates.get k).op = .or) ∨
         ((C.gates.get j).op = .not ∧ (C.gates.get k).op = .and)))
    (andCase : let target : (Fin 9 → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ));
      ∀ C : Circuit, IsMinimalCircuit 9 C → C.size ≤ 15 →
      circuitFun 9 C = target → ReadsBack 9 C →
      ∀ v ∈ ([4,6,7] : List (Fin 9)), ∀ j k : Fin C.size, j < k →
      (C.gates.get j).op = .and → (C.gates.get k).op = .or →
      v.val ∈ (C.gates.get j).inputs → 9+j.val ∈ (C.gates.get k).inputs →
      (∀ i : Fin C.size, v.val ∈ (C.gates.get i).inputs → i = j) →
      (∀ l : Fin C.size, 9+j.val ∈ (C.gates.get l).inputs → l = k) → False)
    (notCase : let target : (Fin 9 → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ));
      ∀ C : Circuit, IsMinimalCircuit 9 C → C.size ≤ 15 →
      circuitFun 9 C = target → ReadsBack 9 C →
      ∀ v ∈ ([4,6,7] : List (Fin 9)), ∀ j k : Fin C.size, j < k →
      (C.gates.get j).op = .not → (C.gates.get k).op = .and →
      v.val ∈ (C.gates.get j).inputs → 9+j.val ∈ (C.gates.get k).inputs →
      (∀ i : Fin C.size, v.val ∈ (C.gates.get i).inputs → i = j) →
      (∀ l : Fin C.size, 9+j.val ∈ (C.gates.get l).inputs → l = k) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∃ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ x7 ∈ x2 x4 x6, (x4.gates.get x7).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  intro target readers eligible C hC nonOR
  classical
  obtain ⟨minimal, small, correct, legal, rules⟩ := hC
  obtain ⟨v,hv,j,hj,hn⟩ := nonOR
  let S := readers C v
  have mem (i : Fin C.size) : i ∈ S ↔ v.val ∈ (C.gates.get i).inputs := by
    simp [S,readers]
  have unique (i : Fin C.size) (hi : v.val ∈ (C.gates.get i).inputs) : i = j := by
    by_contra different
    have pair : ({i,j} : Finset (Fin C.size)) ⊆ S := by
      intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact (mem _).2 hi
      · exact hj
    have lower := Finset.card_le_card pair
    rw [Finset.card_pair different] at lower
    have e : S.card = 2 := le_antisymm (rules v hv).2.1 lower
    exact hn ((rules v hv).2.2 e j hj)
  have back : ReadsBack 9 C := by
    intro i hi w hw
    let z : Fin C.size := ⟨i,hi⟩
    have eq : gateAt C i = C.gates.get z := by
      change C.gates.getD i ⟨.or,[]⟩ = C.gates.get z
      rw [List.getD_eq_getElem _ _ hi]
      rfl
    rw [eq] at hw
    exact (legal z).1 w hw
  have arity (i : Fin C.size) := (legal i).2.2
  have matchTarget : circuitFun 9 C = target := correct
  obtain ⟨k,horder,hlink,onlyK,forms⟩ :=
    nextGate C minimal.1 small matchTarget back arity v hv j ((mem j).1 hj) unique hn
  rcases forms with ⟨hjOp,hkOp⟩ | ⟨hjOp,hkOp⟩
  · exact andCase C minimal small matchTarget back v hv j k horder hjOp hkOp
      ((mem j).1 hj) hlink unique onlyK
  · exact notCase C minimal small matchTarget back v hv j k horder hjOp hkOp
      ((mem j).1 hj) hlink unique onlyK
