import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2346_713
    (collision : ∀ (C : Circuit), IsAO2 14 C → ∀ b : Bool,
      let s := fun i : Fin 14 => decide (i = if b = true then (0 : Fin 14) else 7)
      let t := PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7
      let w := C.wires (List.ofFn s)
      let y := C.wires (List.ofFn t)
      ∀ d : ℕ → Bool,
        (∀ i < 14, d i = decide (i = if b = true then (7 : ℕ) else 0)) →
        (∀ j < C.size, let g := gateAt C j; let a := opnd C j 0; let k := opnd C j 1
          (g.op = GateOp.and → d (14+j) = ((w.getD a false && d k) || (d a && w.getD k false))) ∧
          (g.op = GateOp.or → d (14+j) = (d a || d k))) →
        d C.output = false → C.eval (List.ofFn s) = false → C.eval (List.ofFn t) = true →
        ∃ j < C.size, (gateAt C j).op = GateOp.and ∧
          ∀ k : Fin 2, y.getD (opnd C j k) false = true ∧ w.getD (opnd C j k) false = false)
    (search : ∀ (C : Circuit), C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) → (gateAt C 0).op = GateOp.and →
      (∀ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) →
        C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l))) = true) →
      (∀ s : Fin 7 → Bool, let off := fun l : Fin 7 => !(s l || s (l+1) || s (l+3))
        (∀ p : Fin 7, s p = false → (off p || off (p-1) || off (p-3)) = true) →
        C.eval (List.ofFn (Fin.addCases s off)) = false) →
      (∀ b : Bool,
        let w := C.wires (List.ofFn fun i : Fin 14 => decide (i = if b = true then (0 : Fin 14) else 7))
        let y := C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput (0 : Fin 14) 7))
        ∃ j < C.size, (gateAt C j).op = GateOp.and ∧
          ∀ k : Fin 2, y.getD (opnd C j k) false = true ∧ w.getD (opnd C j k) false = false) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
  x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
  (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin 2) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin 2)) →
  (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  (∀ (x6 : Fin 14 → Bool), x1.eval (List.ofFn x6) = Bool.true ↔
    ∃ (x7 : Fin 7) (x8 : Fin 7), (x7 = x8 ∨ x7 = x8 + (1 : Fin 7) ∨ x7 = x8 + (3 : Fin 7)) ∧
    x6 (Fin.castAdd 7 x7) = Bool.true ∧ x6 (Fin.natAdd 7 x8) = Bool.true) →
  (∀ (x7 : Bool), ∃ (x8 : ℕ → Bool),
    let x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin 14) => decide (x9 = if x7 = Bool.true then (0 : Fin 14) else (7 : Fin 14)))
    (∀ x10 < (14 : ℕ), x8 x10 = decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧
    (∀ x10 < x1.size, let x12 := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10
      let x13 := PEqualNP.TopForm.opnd x1 x10 (0 : Fin 2)
      let x14 := PEqualNP.TopForm.opnd x1 x10 (1 : Fin 2)
      (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        x8 (14+x10) = ((x9.getD x13 false && x8 x14) || (x8 x13 && x9.getD x14 false))) ∧
      (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 (14+x10) = (x8 x13 || x8 x14))) ∧
    x8 x1.output = Bool.false) → False := by
  intro C size ao distinct first semantic traces
  apply search C size ao distinct first
  · intro p l incident
    apply (semantic _).mpr
    exact ⟨p,l,incident,decide_eq_true (Or.inl rfl),decide_eq_true (Or.inr rfl)⟩
  · intro s off _
    apply Bool.eq_false_iff.mpr
    intro hit
    obtain ⟨p,l,inc,hp,hl⟩ := (semantic _).mp hit
    simp only [Fin.addCases_left] at hp
    simp only [Fin.addCases_right,off,Bool.not_eq_true',Bool.or_eq_false_iff] at hl
    rcases inc with h|h|h
    · rw [h,hl.1.1] at hp
      contradiction
    · rw [h,hl.1.2] at hp
      contradiction
    · rw [h,hl.2] at hp
      contradiction
  · intro b
    obtain ⟨d,raw,rec,lost⟩ := traces b
    apply collision C ao b d raw rec lost
    · apply Bool.eq_false_iff.mpr
      intro hit
      obtain ⟨p,l,_,hp,hl⟩ := (semantic _).mp hit
      cases b
      · have impossible : ∀ p : Fin 7, Fin.castAdd 7 p ≠ (7 : Fin 14) := by decide +kernel
        exact impossible p (of_decide_eq_true hp)
      · have impossible : ∀ l : Fin 7, Fin.natAdd 7 l ≠ (0 : Fin 14) := by decide +kernel
        exact impossible l (of_decide_eq_true hl)
    · apply (semantic _).mpr
      exact ⟨0,0,Or.inl rfl,by decide,by decide⟩
