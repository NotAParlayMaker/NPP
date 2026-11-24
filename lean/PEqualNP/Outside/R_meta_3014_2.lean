import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3014_2
    (core : ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (q r : ℕ),
      PEqualNP.TopForm.IsAO2 12 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.size ≤ 21 ∧
      C.output < 12+C.size ∧ q < 12+C.size ∧ r < 12+C.size ∧ ∀ y : Fin 12 → Bool,
      let z := C.eval (List.ofFn y)
      let w := C.wires (List.ofFn y)
      (z = true ↔ ∃ i j : Fin 12, (([2176,3136,1536,2816,1408,704] : List ℕ).getD i.val 0).testBit j.val = true ∧
        y i = true ∧ y j = true) ∧
      (z = false → w.getD q false = (y 6 || y 8) ∧ w.getD r false = (y 0 || y 2)))
    (extend : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (q r : ℕ),
      PEqualNP.TopForm.IsAO2 12 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      C.output < 12+C.size → q < 12+C.size → r < 12+C.size →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 14 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        2 ≤ D.size ∧ D.size ≤ C.size+5 ∧ ∀ x : Fin 14 → Bool,
        let y := List.ofFn (fun i : Fin 12 => x (Fin.ofNat 14 (if i.val<6 then i.val+1 else i.val+2)))
        let w := C.wires y
        D.eval (List.ofFn x) = (C.eval y || ((x 0 && (w.getD q false || x 7)) ||
          (x 7 && w.getD r false)))) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (2 : ℕ) ≤ x3.size ∧ x3.size ≤ (26 : ℕ) ∧ (∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.true → (∀ x6 ≤ x4, x2 x6 = Bool.true → x6 = x4) → x3.eval (List.ofFn x4) = Bool.true) ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.false → (∀ (x6 : Fin (14 : ℕ) → Bool), x4 ≤ x6 → x2 x6 = Bool.false → x6 = x4) → x3.eval (List.ofFn x4) = Bool.false := by
  intro full goalFn
  obtain ⟨C,q,r,model,unique,small,oc,qc,rc,eval⟩ := core
  obtain ⟨D,modelD,uniqueD,lo,hi,deval⟩ := extend C q r model unique oc qc rc
  let src (i : Fin 12) : Fin 14 := Fin.ofNat 14 (if i.val<6 then i.val+1 else i.val+2)
  let inv (i : Fin 14) : Fin 12 := Fin.ofNat 12 (if i.val<7 then i.val-1 else i.val-2)
  let edge := fun i j : Fin 12 => (([2176,3136,1536,2816,1408,704] : List ℕ).getD i.val 0).testBit j.val = true
  have forward : ∀ i j : Fin 12, edge i j → ((src i).val,(src j).val) ∈ full := by decide +kernel
  have back : ∀ a b : Fin 14, (a.val,b.val) ∈ full →
      (src (inv a) = a ∧ src (inv b) = b ∧ edge (inv a) (inv b)) ∨
      (a=0 ∧ (b=8 ∨ b=10 ∨ b=7)) ∨ (b=7 ∧ (a=1 ∨ a=3)) := by decide +kernel
  have ends : ∀ a b : Fin 14, (a=0 ∧ (b=8 ∨ b=10 ∨ b=7)) ∨ (b=7 ∧ (a=1 ∨ a=3)) →
      (a.val,b.val) ∈ full := by decide +kernel
  have correct (x : Fin 14 → Bool) : D.eval (List.ofFn x) = goalFn x := by
    let y := fun i => x (src i)
    have h := eval y
    let H := ∃ i j : Fin 12, edge i j ∧ y i = true ∧ y j = true
    have hcore : C.eval (List.ofFn y) = true ↔ H := h.1
    have split : goalFn x = true ↔ H ∨
        ((x 0 = true ∧ ((x 8 = true ∨ x 10 = true) ∨ x 7 = true)) ∨
        (x 7 = true ∧ (x 1 = true ∨ x 3 = true))) := by
      change decide (∃ a b : Fin 14, (a.val,b.val) ∈ full ∧ x a = true ∧ x b = true) = true ↔ _
      rw [decide_eq_true_eq]
      constructor
      · rintro ⟨a,b,he,ha,hb⟩
        rcases back a b he with ⟨ea,eb,ec⟩ | ⟨rfl,hb'⟩ | ⟨rfl,ha'⟩
        · exact Or.inl ⟨inv a,inv b,ec,by simpa only [y,ea] using ha,by simpa only [y,eb] using hb⟩
        · rcases hb' with rfl | rfl | rfl <;> tauto
        · rcases ha' with rfl | rfl <;> tauto
      · rintro (⟨i,j,he,ya,yb⟩ | ⟨ha,(hb | hb) | hb⟩ | ⟨hb,ha | ha⟩)
        · exact ⟨src i,src j,forward i j he,ya,yb⟩
        · exact ⟨0,8,ends 0 8 (by decide),ha,hb⟩
        · exact ⟨0,10,ends 0 10 (by decide),ha,hb⟩
        · exact ⟨0,7,ends 0 7 (by decide),ha,hb⟩
        · exact ⟨1,7,ends 1 7 (by decide),ha,hb⟩
        · exact ⟨3,7,ends 3 7 (by decide),ha,hb⟩
    have actual : D.eval (List.ofFn x) = (C.eval (List.ofFn y) ||
        ((x 0 && ((x 8 || x 10) || x 7)) || (x 7 && (x 1 || x 3)))) := by
      have v := deval x
      change D.eval (List.ofFn x) = (C.eval (List.ofFn y) ||
        ((x 0 && ((C.wires (List.ofFn y)).getD q false || x 7)) ||
          (x 7 && (C.wires (List.ofFn y)).getD r false))) at v
      rw [v]
      cases z : C.eval (List.ofFn y)
      · obtain ⟨aq,ar⟩ := h.2 z
        rw [aq,ar]
        rfl
      · rfl
    apply Bool.eq_iff_iff.mpr
    simpa only [actual,Bool.or_eq_true_iff,Bool.and_eq_true_iff,hcore] using split.symm
  refine ⟨D,modelD,uniqueD,lo,by omega,?_,?_⟩
  · intro x hx _; exact (correct x).trans hx
  · intro x hx _; exact (correct x).trans hx
