import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_2225_2
  (origin : let inc := fun p l : Fin 7 => p = l ∨ p = l + 1 ∨ p = l + 3
    let eligible := fun C : Circuit => C.size ≤ 27 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, inc p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧
      ((C.output :: C.gates.flatMap Gate.inputs).filter (fun i => decide (14 ≤ i))).Nodup
    ∀ D, eligible D → HasLineDegree 14 {0} D 1 ∨ HasLineDegree 14 {7} D 1)
  (transport : let inc := fun p l : Fin 7 => p = l ∨ p = l + 1 ∨ p = l + 3
    let eligible := fun C : Circuit => C.size ≤ 27 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, inc p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧
      ((C.output :: C.gates.flatMap Gate.inputs).filter (fun i => decide (14 ≤ i))).Nodup
    ∀ (a u v : Fin 7),
      Function.Bijective (fun i : Fin 7 => a*i+u) →
      Function.Bijective (fun i : Fin 7 => a*i+v) →
      (∀ i j, inc (a*i+u) (a*j+v) ↔ inc i j) →
      ∀ C, eligible C → ∃ D, eligible D ∧
        C.lineDeg 14 {u.val} = D.lineDeg 14 {0} ∧
        C.lineDeg 14 {7+v.val} = D.lineDeg 14 {7}) :
  have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x3 x4 → x1 x5 x6 → PEqualNP.CircuitLowerBounds.HasLineDegree (14 : ℕ) {↑x5} x4 (1 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (14 : ℕ) {(7 : ℕ) + ↑x6} x4 (1 : ℕ) := by
  intro inc valid tree C p l hc ht flag
  have symmetries : ∀ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) →
      ∃ a : Fin 7,
        (∀ i j : Fin 7, a*i+p = a*j+p → i = j) ∧
        (∀ i j : Fin 7, a*i+l = a*j+l → i = j) ∧
        (∀ i j : Fin 7,
          (a*i+p = a*j+l ∨ a*i+p = a*j+l+1 ∨ a*i+p = a*j+l+3) ↔
          (i = j ∨ i = j+1 ∨ i = j+3)) := by decide +kernel
  obtain ⟨a,hp,hl,hrel⟩ := symmetries p l flag
  obtain ⟨D,hd,hpDeg,hlDeg⟩ := transport a p l
    (Finite.injective_iff_bijective.mp hp) (Finite.injective_iff_bijective.mp hl)
    hrel C ⟨hc.1,hc.2.1,hc.2.2,ht⟩
  rcases origin D hd with h | h
  · exact Or.inl (hpDeg.trans_le h)
  · exact Or.inr (hlDeg.trans_le h)
