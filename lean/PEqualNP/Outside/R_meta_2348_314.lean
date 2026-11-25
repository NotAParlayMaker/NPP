import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.GenericRejection

-- A mixed OR has a singleton-accepting input on exactly one of its two pins.
-- The other obstruction is an AND accepting a graph-negative row of at most two vertices.
theorem PEqualNP.Outside.R_meta_2348_314
    (obstruction : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C → (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) →
    (∃ v : ℕ → Bool,
      let W := C.wires (List.ofFn (fun i : Fin 14 => decide (i = 0)))
      (∀ i < 14, v i = decide (i = 7)) ∧
      (∀ j < C.size,
        let g := gateAt C j
        let a := opnd C j 0
        let b := opnd C j 1
        (g.op = .and → v (14+j) = (W.getD a false && v b || v a && W.getD b false)) ∧
        (g.op = .or → v (14+j) = (v a || v b))) ∧ v C.output = false) → (let single (w : ℕ) := ∃ i : Fin 14, wireVal 14 C w (pairInput i i) = true
      ∃ j < C.size, (gateAt C j).op = .or ∧ ¬ (single (opnd C j 0) ↔ single (opnd C j 1))) ∨ (∃ j < C.size, (gateAt C j).op = .and ∧ ∃ a b : Fin 14,
        gateVal 14 C j (pairInput a b) = true ∧ wireVal 14 C C.output (pairInput a b) = false))
    (mixedCase : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C → (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) → (gateAt C 0).op = .or →
    ComputesIncidence fanoLines C → (let single (w : ℕ) := ∃ i : Fin 14, wireVal 14 C w (pairInput i i) = true
      ∃ j < C.size, (gateAt C j).op = .or ∧ ¬ (single (opnd C j 0) ↔ single (opnd C j 1))) → (∀ s : Bool, ∃ v : ℕ → Bool,
      let W := C.wires (List.ofFn (fun i : Fin 14 => decide (i = if s then 0 else 7)))
      (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧
      (∀ j < C.size,
        let g := gateAt C j
        let a := opnd C j 0
        let b := opnd C j 1
        (g.op = .and → v (14+j) = (W.getD a false && v b || v a && W.getD b false)) ∧
        (g.op = .or → v (14+j) = (v a || v b))) ∧ v C.output = false) → False)
    (dirtyCase : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C → (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) → (gateAt C 0).op = .or →
    ComputesIncidence fanoLines C → (∃ j < C.size, (gateAt C j).op = .and ∧ ∃ a b : Fin 14,
        gateVal 14 C j (pairInput a b) = true ∧ wireVal 14 C C.output (pairInput a b) = false) → (∀ s : Bool, ∃ v : ℕ → Bool,
      let W := C.wires (List.ofFn (fun i : Fin 14 => decide (i = if s then 0 else 7)))
      (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧
      (∀ j < C.size,
        let g := gateAt C j
        let a := opnd C j 0
        let b := opnd C j 1
        (g.op = .and → v (14+j) = (W.getD a false && v b || v a && W.getD b false)) ∧
        (g.op = .or → v (14+j) = (v a || v b))) ∧ v C.output = false) → False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  intro C size ao distinct first correct tang
  have flags : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p=l ∨ p=l+1 ∨ p=l+3 := by decide
  have same : ComputesIncidence fanoLines C := by
    intro P L
    let x := Fin.append (fun p : Fin 7 => decide (p ∈ P)) (fun l : Fin 7 => decide (l ∈ L))
    have input : List.ofFn x = incidenceInput P L := List.ofFn_fin_append ..
    rw [←input]
    apply Bool.eq_iff_iff.mpr
    rw [correct x]
    change _ ↔ decide (∃ p ∈ P, ∃ l ∈ L, p ∈ fanoLines l) = true
    rw [decide_eq_true_eq]
    simp only [x,Fin.append_left,Fin.append_right,decide_eq_true_eq,flags]
    constructor
    · rintro ⟨p,l,inc,pt,ln⟩
      exact ⟨p,pt,l,ln,inc⟩
    · rintro ⟨p,pt,l,ln,inc⟩
      exact ⟨p,l,inc,pt,ln⟩
  rcases obstruction C size ao correct (tang true) with h|h
  · exact mixedCase C size ao distinct first same h tang
  · exact dirtyCase C size ao distinct first same h tang
