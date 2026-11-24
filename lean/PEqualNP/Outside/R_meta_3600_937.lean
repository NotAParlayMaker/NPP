import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK PEqualNP.TopForm

-- Count edges with a witness that reads each active input once.
-- The remaining circuits have fewer than N*q/100 such incident pairs.
theorem PEqualNP.Outside.R_meta_3600_937
    (count : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      let edges := Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ readsAtMost C (N+N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 1 = true)
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ (a b : Fin (N+N)), circuitFun (N+N) C (fun i => decide (i = a ∨ i = b)) = true →
        ∃ p l : Fin N, I p l ∧ (Fin.castAdd N p = a ∨ Fin.castAdd N p = b) ∧
          (Fin.natAdd N l = a ∨ Fin.natAdd N l = b)) → edges.card ≤ C.size)
    (remaining : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      let edges := Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ readsAtMost C (N+N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 1 = true)
      300 ≤ q → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      IsAO2 (N+N) C → N+N ≤ C.output → C.output < N+N+C.size →
      (gateAt C (C.output-(N+N))).op = .or →
      (∀ p l : Fin N, I p l → circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      100*edges.card < N*q → N*q ≤ 100*C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x5.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x14]? = Option.some x15 → ∃ (x17 : ℕ) (x18 : ℕ), x15.inputs = [x17, x18] ∧ x17 < x18 ∧ x18 < x2 + x2 + x14) → (∀ (x15 x16 : Fin x2), x3 x15 x16 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x18 : Fin (x2 + x2)) => Decidable.decide (x18 = Fin.castAdd x2 x15 ∨ x18 = Fin.natAdd x2 x16)) = Bool.true) → (∀ (x16 : Fin (x2 + x2) → Bool), Fintype.card { x17 : Fin x2 // x16 (Fin.natAdd x2 x17) = Bool.true } ≤ x1 → (¬∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x16 (Fin.castAdd x2 x18) = Bool.true ∧ x16 (Fin.natAdd x2 x19) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x16 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq order degree unique mono outLo outHi outOr shape accept reject
  have lookup (k : ℕ) (hk : k < C.size) : gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hk
  have ao : IsAO2 (N+N) C := by
    refine ⟨fun g hg => (mono g hg).1, ?_, ?_⟩
    · intro k hk w hw
      obtain ⟨a,b,inputs,ab,upper⟩ := shape k C.gates[k] (List.getElem?_eq_getElem hk)
      rw [lookup k hk, inputs] at hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ab.trans upper
      · simpa using (show w = b from by simpa using hw) ▸ upper
    · intro g hg
      obtain ⟨k,hk,eq⟩ := List.getElem_of_mem hg
      obtain ⟨a,b,inputs,_,_⟩ := shape k g (by rw [List.getElem?_eq_getElem hk, eq])
      simp [inputs]
  have op : (gateAt C (C.output-(N+N))).op = .or := by
    obtain ⟨g,hg,op⟩ := outOr
    have hk : C.output-(N+N) < C.size := by omega
    rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hg
    rw [lookup _ hk, hg, op]
  let edges := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ readsAtMost C (N+N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 1 = true)
  by_cases few : 100*edges.card < N*q
  · exact remaining q N I C hq order degree unique ao outLo outHi op accept reject few
  · have paid : edges.card ≤ C.size := by
      apply count N I C unique ao
      intro a b hit
      let z : Fin (N+N) → Bool := fun i => decide (i = a ∨ i = b)
      have lineCount : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 2 := by
        let S : Finset (Fin (N+N)) := {a,b}
        let f (l : {l : Fin N // z (Fin.natAdd N l) = true}) : S :=
          ⟨Fin.natAdd N l.val, by simpa [S,z] using l.property⟩
        have injective : Function.Injective f := by
          intro l m eq
          apply Subtype.ext
          exact Fin.natAdd_injective N N (congrArg Subtype.val eq)
        have card := Fintype.card_le_of_injective f injective
        rw [Fintype.card_coe] at card
        exact card.trans (by simpa [S] using Finset.card_insert_le (a := a) (s := {b}))
      by_contra absent
      have off := reject z (lineCount.trans (by omega)) (by simpa [z] using absent)
      exact Bool.noConfusion (hit.symm.trans off)
    exact (Nat.le_of_not_gt few).trans (Nat.mul_le_mul_left _ paid)
