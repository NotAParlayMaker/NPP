import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.ReadK

-- Route the two operands through a mixed OR or a colliding first accepting AND.
theorem PEqualNP.Outside.R_meta_4215_521 :
  (∀ (C : Circuit),
    let V (w : ℕ) (a b : Fin 14) := wireVal 14 C w (pairInput a b)
    let I (j w : ℕ) := 14 + j = w ∨ InCone 14 C j (w-14)
    let P := opnd C
    let A (j : ℕ) := (gateAt C j).op = .and
    let S (w : ℕ) := ∃ i : Fin 14, readsAtMost ⟨C.gates,w⟩ 14 [i.val] 1 = true
    let B (k : ℕ) (e : Fin 14 × Fin 14) := e.1 < e.2 ∧ V C.output e.1 e.2 = true ∧
      V (14+k) e.1 e.2 = true ∧ ∀ q < k, A q → I q C.output → V (14+q) e.1 e.2 = false
    C.size ≤ 27 → IsAO2 14 C →
    circuitFun 14 C = (fun x : Fin 14 → Bool => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
    ∀ j g : ℕ, A j → A g → I g C.output → P g 0 ≠ P g 1 → (∀ b, I j (P g b)) →
    (∃ k : ℕ, ¬ A k ∧ I j (14+k) ∧ I k (14+g) ∧ ¬ (S (P k 0) ↔ S (P k 1))) ∨
    (∃ k : ℕ, A k ∧ I k C.output ∧ (∃ e f : Fin 14 × Fin 14, e ≠ f ∧ B k e ∧ B k f) ∧
      ∃ a b : Fin 14, V (14+k) a b = true ∧ V C.output a b = false)) →
  (∀ (C : Circuit),
    let V (w : ℕ) (a b : Fin 14) := wireVal 14 C w (pairInput a b)
    let I (j w : ℕ) := 14 + j = w ∨ InCone 14 C j (w-14)
    let P := opnd C
    let A (j : ℕ) := (gateAt C j).op = .and
    let Z (w : ℕ) := V w 0 0 = false ∧ V w 7 7 = false
    let S (w : ℕ) := ∃ i : Fin 14, readsAtMost ⟨C.gates,w⟩ 14 [i.val] 1 = true
    C.size ≤ 27 → IsAO2 14 C →
    circuitFun 14 C = (fun x : Fin 14 → Bool => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
    ∀ j g : ℕ, A j → A g → I g C.output → P g 0 ≠ P g 1 → V (14+g) 0 7 = true →
    (∀ b : Fin 2, I j (P g b) ∧ Z (P g b)) → Z (14+j) →
    (∃ b : Fin 2, V (P j b) 0 0 = true ∧ V (P j (1-b)) 7 7 = true) →
    ¬ ∃ k : ℕ, ¬ A k ∧ I j (14+k) ∧ I k (14+g) ∧ ¬ (S (P k 0) ↔ S (P k 1))) →
  (∀ (C : Circuit),
    let n : ℕ := 14
    let V (w : ℕ) (a b : Fin n) := wireVal n C w (pairInput a b)
    let I (j w : ℕ) := n + j = w ∨ InCone n C j (w-n)
    let P := opnd C
    let A (j : ℕ) := (gateAt C j).op = .and
    let Z (w : ℕ) := V w 0 0 = false ∧ V w 7 7 = false
    let B (k : ℕ) (e : Fin n × Fin n) := e.1 < e.2 ∧ V C.output e.1 e.2 = true ∧
      V (n+k) e.1 e.2 = true ∧ ∀ q < k, A q → I q C.output → V (n+q) e.1 e.2 = false
    C.size ≤ 27 → IsAO2 n C →
    circuitFun n C = (fun x : Fin n → Bool => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
    ∀ j g : ℕ, A j → A g → I g C.output → P g 0 ≠ P g 1 → V (n+g) 0 7 = true →
    (∀ b : Fin 2, I j (P g b) ∧ Z (P g b)) → Z (n+j) →
    (∃ b : Fin 2, V (P j b) 0 0 = true ∧ V (P j (1-b)) 7 7 = true) →
    ¬ ∃ k : ℕ, A k ∧ I k C.output ∧ (∃ e f : Fin n × Fin n, e ≠ f ∧ B k e ∧ B k f) ∧
      ∃ a b : Fin n, V (n+k) a b = true ∧ V C.output a b = false) →
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).inputs.Nodup) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x7 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x8 : Fin (7 : ℕ)) (x9 : Fin (7 : ℕ)), x8 ∈ PEqualNP.CircuitLowerBounds.fanoLines x9 ∧ x7 (Fin.castAdd (7 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (7 : ℕ) x9) = Bool.true)) → ∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → (14 : ℕ) + x8 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x8 (x1.output - (14 : ℕ)) → x2 ((14 : ℕ) + x8) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x12 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x8 x12) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x8 x12) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → ¬∃ (x13 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x13 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x13 := by
  intro split mixed collision C V birth small ao distinct good g gAnd live pairOn single
  rintro ⟨j,left,right⟩
  have valid : g < C.gates.length := by
    by_contra! past
    have eq : gateAt C g = ⟨.or,[]⟩ := List.getD_eq_default _ _ past
    rw [eq] at gAnd
    cases gAnd
  have mem : gateAt C g ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ valid]
    exact List.getElem_mem valid
  obtain ⟨a,b,inputs⟩ := List.length_eq_two.mp (ao.2.2 _ mem)
  have different : opnd C g 0 ≠ opnd C g 1 := by
    have no := distinct g valid
    unfold opnd
    simpa [inputs] using no
  have receives (b : Fin 2) : 14+j = opnd C g b ∨ InCone 14 C j (opnd C g b-14) := by
    fin_cases b
    · exact left.1
    · exact right.1
  have zeros (b : Fin 2) := And.intro (receives b) (single b)
  have jAnd := left.2.1
  have jZero := And.intro left.2.2.1 left.2.2.2.1
  have start := left.2.2.2.2
  rcases split C small ao good j g jAnd gAnd live different receives with h|h
  · exact mixed C small ao good j g jAnd gAnd live different pairOn zeros jZero start h
  · exact collision C small ao good j g jAnd gAnd live different pairOn zeros jZero start h
