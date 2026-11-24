import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_5270_418
    (recenter :
    let I (p l : Fin 7) := p=l ∨ p=l+1 ∨ p=l+3
    let valid (C : Circuit) := C.size≤27 ∧
      (∀ j (g : Gate), C.gates[j]?=some g → (g.op=.and ∨ g.op=.or) ∧
        ∃ a b : Nat, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j) ∧
      ∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔
        ∃ p l : Fin 7, I p l ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
    let tree (C : Circuit) := ((C.output :: C.gates.flatMap Gate.inputs).filter (fun n => decide (14≤n))).Nodup
    let high (C : Circuit) := ∃ p l : Fin 7, I p l ∧ 2≤C.lineDeg 14 {p.val} ∧ 2≤C.lineDeg 14 {7+l.val}
    ∀ C : Circuit, valid C → tree C → high C →
      ∃ D : Circuit, valid D ∧ tree D ∧ 2≤D.lineDeg 14 {0} ∧ 2≤D.lineDeg 14 {7})
    (witness :
    let I (p l : Fin 7) := p=l ∨ p=l+1 ∨ p=l+3
    let valid (C : Circuit) := C.size≤27 ∧
      (∀ j (g : Gate), C.gates[j]?=some g → (g.op=.and ∨ g.op=.or) ∧
        ∃ a b : Nat, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j) ∧
      ∀ x : Fin 14 → Bool, C.eval (List.ofFn x)=true ↔
        ∃ p l : Fin 7, I p l ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true
    let tree (C : Circuit) := ((C.output :: C.gates.flatMap Gate.inputs).filter (fun n => decide (14≤n))).Nodup
    let high (C : Circuit) := ∃ p l : Fin 7, I p l ∧ 2≤C.lineDeg 14 {p.val} ∧ 2≤C.lineDeg 14 {7+l.val}
    (∃ C : Circuit, valid C ∧ ¬tree C ∧ 2≤C.lineDeg 14 {0} ∧ 2≤C.lineDeg 14 {7}) →
      ∃ D : Circuit, valid D ∧ tree D ∧ high D) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2 x4 → ¬x3 x4 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x2 x9 ∧ x3 x9 ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(7 : ℕ)} := by
  dsimp only at *
  intro C valid shared dp dl
  obtain ⟨D,ok,t,mark⟩ := witness ⟨C,valid,shared,dp,dl⟩
  exact recenter D ok t mark
