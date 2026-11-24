import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

-- At the first wire with too many pivotal lines, an AND joins two smaller pivotal sets.
theorem PEqualNP.Outside.R_meta_1782_615
    (threshold : ∀ (n q : ℕ) (C : Circuit) (x : Fin n → Bool) (M : Finset (Fin n)),
      let v := fun y w => (C.wires (List.ofFn y)).getD w false
      let K := fun w => M.filter fun i => v (Function.update x i false) w = false
      Monotone2 C → 1 ≤ q → v x C.output = true → q < (K C.output).card →
      ∃ (j a b : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = .and ∧ g.inputs = [a,b] ∧
        a < n+j ∧ b < n+j ∧ v x a = true ∧ v x b = true ∧
        (K a).card ≤ q ∧ (K b).card ≤ q ∧ q < (K a ∪ K b).card)
    (remaining : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      let right := Fin.natAdd n
      let v := fun y w => (C.wires (List.ofFn y)).getD w false
      199 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      Monotone2 C → RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      ∀ x, (¬∃ p l, p ∈ S l ∧ x (Fin.castAdd n p) = true ∧ x (right l) = true) →
      circuitFun (n+n) C x = true →
      (∀ l, x (right l) = true → circuitFun (n+n) C (Function.update x (right l) false) = false) →
      let M := ((Finset.univ : Finset (Fin n)).filter fun l => x (right l) = true).map (Fin.natAddEmb n)
      let K := fun w => M.filter fun i => v (Function.update x i false) w = false
      (∃ (j a b : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = .and ∧ g.inputs = [a,b] ∧
        a < n+n+j ∧ b < n+n+j ∧ v x a = true ∧ v x b = true ∧
        (K a).card ≤ q ∧ (K b).card ≤ q ∧ q < (K a ∪ K b).card) →
      n*q ≤ 100*C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → ∀ (x13 : Fin (x2 + x2) → Bool), (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.true → x1 < Fintype.card { x16 : Fin x2 // x13 (Fin.natAdd x2 x16) = Bool.true } → (∀ (x17 : Fin x2), x13 (Fin.natAdd x2 x17) = Bool.true → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (Function.update x13 (Fin.natAdd x2 x17) Bool.false) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n I relation C hq size lines pair model positives rejects x independent accepts count critical
  let F (l : Fin n) : Finset (Fin n) := Finset.univ.filter fun p => I p l
  have membership (p l : Fin n) : p ∈ F l ↔ I p l := by simp [F]
  have degree (l : Fin n) : (F l).card = q+1 :=
    (Fintype.card_of_finset' (p := {p : Fin n | I p l}) (F l) (fun p => membership p l)).symm.trans (lines l)
  have pairF (a b : Fin n) (ne : a ≠ b) :
      ∃! l, a ∈ F l ∧ b ∈ F l := by simpa only [membership] using pair a b ne
  let encode (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
    Fin.addCases (fun p : Fin n => decide (p ∈ X)) (fun l : Fin n => decide (l ∈ Y))
  have encodedPoint (X Y : Finset (Fin n)) (p : Fin n) :
      encode X Y (Fin.castAdd n p) = decide (p ∈ X) := by
    exact Fin.addCases_left p
  have encodedLine (X Y : Finset (Fin n)) (l : Fin n) :
      encode X Y (Fin.natAdd n l) = decide (l ∈ Y) := by
    exact Fin.addCases_right l
  have encodes (X Y : Finset (Fin n)) : List.ofFn (encode X Y) = incidenceInput X Y := by
    rw [List.ofFn_add]
    unfold incidenceInput
    congr 1 <;> congr 1 <;> funext i
    · exact encodedPoint X Y i
    · exact encodedLine X Y i
  have opposite (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro h
    have vv := congrArg Fin.val h
    simp at vv
    omega
  have acceptsF : RightOnIncidentPairs F C := by
    intro l p h
    have pairInputs : encode {p} {l} =
        (fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) := by
      funext i
      refine Fin.addCases (fun r => ?_) (fun s => ?_) i
      · rw [encodedPoint]
        rw [decide_eq_decide, Finset.mem_singleton]
        constructor
        · intro h
          exact Or.inl (congrArg (Fin.castAdd n) h)
        · rintro (same | cross)
          · apply Fin.eq_of_val_eq
            change (Fin.castAdd n r).val = (Fin.castAdd n p).val
            exact congrArg Fin.val same
          · exact (opposite r l cross).elim
      · rw [encodedLine]
        rw [decide_eq_decide, Finset.mem_singleton]
        constructor
        · intro h
          exact Or.inr (congrArg (Fin.natAdd n) h)
        · rintro (cross | same)
          · exact (opposite p s cross.symm).elim
          · apply Fin.eq_of_val_eq
            have values := congrArg Fin.val same
            simp at values
            omega
    rw [← encodes, pairInputs]
    exact positives p l ((membership p l).mp h)
  have rejectsF (X Y : Finset (Fin n)) (few : Y.card ≤ q) (bad : IsFalseInput F X Y) :
      C.eval (incidenceInput X Y) = false := by
    rw [← encodes]
    apply rejects (encode X Y)
    · have cardinal : Fintype.card {l : Fin n // encode X Y (Fin.natAdd n l) = true} = Y.card := by
        apply Fintype.card_of_finset' (p := {l : Fin n | encode X Y (Fin.natAdd n l) = true}) Y
        intro l
        simp only [Set.mem_ofPred_eq, encodedLine, decide_eq_true_eq]
      exact cardinal.le.trans few
    · rintro ⟨p, l, edge, hp, hl⟩
      have pIn : p ∈ X := by simpa only [encodedPoint, decide_eq_true_eq] using hp
      have lIn : l ∈ Y := by simpa only [encodedLine, decide_eq_true_eq] using hl
      exact (Finset.disjoint_left.mp (bad l lIn)) ((membership p l).mpr edge) pIn
  let S : Finset (Fin n) := Finset.univ.filter fun l => x (Fin.natAdd n l) = true
  let M : Finset (Fin (n+n)) := S.map (Fin.natAddEmb n)
  have sizeM : M.card = Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} := by
    change (S.map _).card = _
    rw [Finset.card_map]
    exact (Fintype.card_of_finset' (p := {l : Fin n | x (Fin.natAdd n l) = true})
      S (fun l => by simp [S])).symm
  have outputPivotal : M.filter (fun i =>
      (C.wires (List.ofFn (Function.update x i false))).getD C.output false = false) = M := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hi
      refine ⟨hi, ?_⟩
      obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hi
      exact critical l (Finset.mem_filter.mp hl).2
  have enough : q < (M.filter (fun i =>
      (C.wires (List.ofFn (Function.update x i false))).getD C.output false = false)).card := by
    rw [outputPivotal, sizeM]
    exact count
  have split := threshold (n+n) q C x M model (by omega) accepts enough
  exact remaining q n F C hq size degree pairF model acceptsF rejectsF
    x (by simpa only [membership] using independent) accepts critical split
