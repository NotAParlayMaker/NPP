import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.SingleLevel PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_2600_2
    (account : let I := fun p l : Fin 13 => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
    let F := fun x : Fin 26 → Bool => ∃ p l, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    let row := fun (e : Fin 13 × Fin 13) => pairInput (Fin.castAdd 13 e.1) (Fin.natAdd 13 e.2)
    ∀ C : Circuit, PEqualNP.TopForm.IsAO2 26 C →
    (∀ x, circuitFun 26 C x = true ↔ F x) → C.size ≤ 62 →
    let ds := andDepths C 26
    let D : Circuit := ⟨(C.gates.zipIdx 26).map (fun z =>
      if andLevel z.1 = 1 ∧ 1 < ds.getD z.2 0 then (⟨.or, []⟩ : Gate) else z.1), C.output⟩
    let lost := Finset.univ.filter (fun e : Fin 13 × Fin 13 => I e.1 e.2 ∧ circuitFun 26 D (row e) = false)
    3 ≤ lost.card)
    (core : let I := fun p l : Fin 13 => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
    let F := fun x : Fin 26 → Bool => ∃ p l, I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    let row := fun (e : Fin 13 × Fin 13) => pairInput (Fin.castAdd 13 e.1) (Fin.natAdd 13 e.2)
    ∀ C : Circuit, PEqualNP.TopForm.IsAO2 26 C →
    (∀ e, I e.1 e.2 → circuitFun 26 C (row e) = true) →
    (∀ x, ¬F x → (∀ y, x ≤ y → ¬F y → y ≤ x) → circuitFun 26 C x = false) →
    let ds := andDepths C 26
    let D : Circuit := ⟨(C.gates.zipIdx 26).map (fun z =>
      if andLevel z.1 = 1 ∧ 1 < ds.getD z.2 0 then (⟨.or, []⟩ : Gate) else z.1), C.output⟩
    let lost := Finset.univ.filter (fun e : Fin 13 × Fin 13 => I e.1 e.2 ∧ circuitFun 26 D (row e) = false)
    3 ≤ lost.card → 63 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  classical
  intro C good right
  have ao : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hg
      exact (good i g (by rw [List.getElem?_eq_getElem hi,eq])).1
    · intro i hi w hw
      obtain ⟨_,a,b,inputs,_,ha,hb⟩ := good i C.gates[i] (List.getElem?_eq_getElem hi)
      unfold NestedCover.gateAt at hw
      rw [List.getD_eq_getElem _ _ hi,inputs] at hw
      simp at hw
      rcases hw with rfl|rfl <;> assumption
    · intro g hg
      obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨_,_,_,inputs,_,_,_⟩ := good i g (by rw [List.getElem?_eq_getElem hi,eq])
      simp [inputs]
  by_contra! small
  apply (Nat.not_lt_of_ge (core C ao ?_ ?_ (account C ao right (by omega)))) small
  · rintro ⟨p,l⟩ h
    exact (right _).mpr ⟨p,l,h,decide_eq_true (Or.inl rfl),decide_eq_true (Or.inr rfl)⟩
  · intro x neg _
    cases h : circuitFun 26 C x with
    | false => rfl
    | true => exact (neg ((right x).mp h)).elim
