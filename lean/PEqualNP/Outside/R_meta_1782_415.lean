import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection
open PEqualNP.MetaComplexity

-- Each critical line beyond the first requires an AND gate with two switching inputs.
-- These gates are disjoint from the OR gates counted by the plane bound.
theorem PEqualNP.Outside.R_meta_1782_415
    (orBound : ∀ (x1 x2 : ℕ) (x3 : Fin x2 →
      Fin x2 →
      Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 →
      ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
      PEqualNP.MetaComplexity.Monotone2 x5 →
      (∀ (x11 x12 : Fin x2), x3 x11 x12 →
      (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →
      (∀ (x12 : Fin (x2 + x2) →
      Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 →
      (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) →
      PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →
      (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length)
    (localDeficit : ∀ (x1 x2 : ℕ) (x3 : Fin x2 →
      Fin x2 →
      Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 →
      ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
      PEqualNP.MetaComplexity.Monotone2 x5 →
      (∀ (x11 x12 : Fin x2), x3 x11 x12 →
      (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →
      (∀ (x12 : Fin (x2 + x2) →
      Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 →
      (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) →
      PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →
      ∀ (x13 : Fin (x2 + x2) →
      Bool), (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x2 x15) = Bool.true) →
      PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.true →
      x1 < Fintype.card { x16 : Fin x2 // x13 (Fin.natAdd x2 x16) = Bool.true } →
      (∀ (x17 : Fin x2), x13 (Fin.natAdd x2 x17) = Bool.true →
      PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (Function.update x13 (Fin.natAdd x2 x17) Bool.false) = Bool.false) →
      2 * x1 ^ 2 + 1 ≤ (x5.gates.filter (fun g => g.op.eval [Bool.true, Bool.false])).length →
      100 * ((x5.gates.filter (fun g => g.op.eval [Bool.true, Bool.false])).length + Fintype.card {l : Fin x2 // x13 (Fin.natAdd x2 l) = Bool.true} - 1) < x2 * x1 →
      x2 * x1 ≤ (100 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 →
      Fin x2 →
      Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 →
      ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
      PEqualNP.MetaComplexity.Monotone2 x5 →
      (∀ (x11 x12 : Fin x2), x3 x11 x12 →
      (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →
      (∀ (x12 : Fin (x2 + x2) →
      Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 →
      (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) →
      PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →
      ∀ (x13 : Fin (x2 + x2) →
      Bool), (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x2 x15) = Bool.true) →
      PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.true →
      x1 < Fintype.card { x16 : Fin x2 // x13 (Fin.natAdd x2 x16) = Bool.true } →
      (∀ (x17 : Fin x2), x13 (Fin.natAdd x2 x17) = Bool.true →
      PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (Function.update x13 (Fin.natAdd x2 x17) Bool.false) = Bool.false) →
      x2 * x1 ≤ (100 : ℕ) * x5.size := by
  let encodeInput {a b : ℕ} (X : Finset (Fin a)) (Y : Finset (Fin b)) : List Bool :=
    List.ofFn (fun p : Fin a => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin b => decide (l ∈ Y))

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let legal (gs : List Gate) : Prop :=
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

  have wireLength (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega

  have oldWire (gs : List Gate) (w : List Bool) (g : Gate) (i : ℕ)
      (hi : i < w.length + gs.length) :
      ((gs ++ [g]).foldl step w).getD i false = (gs.foldl step w).getD i false := by
    rw [List.foldl_append]
    exact List.getD_append _ _ _ _ (by rw [wireLength]; exact hi)

  have newWire (gs : List Gate) (w : List Bool) (g : Gate) :
      ((gs ++ [g]).foldl step w).getD (w.length + gs.length) false =
        g.op.eval (g.inputs.map fun i => (gs.foldl step w).getD i false) := by
    rw [List.foldl_append]
    change ((gs.foldl step w) ++ _).getD _ _ = _
    rw [List.getD_append_right _ _ _ _ (by rw [wireLength]), wireLength, Nat.sub_self]
    rfl

  -- A gate is counted only when two inputs change from off to on.
  let priced (base upper : List Bool) (g : Gate) : Bool :=
    (g.inputs.length == 2) && !(g.op.eval [false, true]) &&
      g.inputs.all (fun i => !(base.getD i false) && upper.getD i false)

  let charge (base upper : List Bool) (gs : List Gate) : ℕ :=
    (gs.foldr (fun g next lower higher =>
      (priced lower higher g).toNat + next (step lower g) (step higher g))
        (fun _ _ => 0)) base upper

  have chargeNil (base upper : List Bool) : charge base upper [] = 0 := rfl

  have chargeCons (base upper : List Bool) (g : Gate) (gs : List Gate) :
      charge base upper (g::gs) =
        (priced base upper g).toNat + charge (step base g) (step upper g) gs := rfl

  have charge_append (base upper : List Bool) (gs : List Gate) (g : Gate) :
      charge base upper (gs ++ [g]) =
        charge base upper gs + (priced (gs.foldl step base) (gs.foldl step upper) g).toNat := by
    induction gs generalizing base upper with
    | nil => simp [chargeCons,chargeNil]
    | cons h hs ih =>
      simp only [List.cons_append, chargeCons, List.foldl_cons, ih, Nat.add_assoc]

  let preservesOnes (base upper : List Bool) : Prop :=
    ∀ i, base.getD i false = true → upper.getD i false = true

  have legalBefore (gs : List Gate) (g : Gate)
      (model : legal (gs ++ [g])) : legal gs :=
    fun i hi => model i (List.mem_append_left _ hi)

  have legalLast (gs : List Gate) (g : Gate)
      (model : legal (gs ++ [g])) :
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 :=
    model g (List.mem_append_right _ (by simp))

  have gateInputs (g : Gate) (count : g.inputs.length ≤ 2) :
      g.inputs = [] ∨ (∃ a, g.inputs = [a]) ∨ ∃ a b, g.inputs = [a,b] := by
    cases h : g.inputs with
    | nil => exact Or.inl rfl
    | cons a tail =>
      cases tail with
      | nil => exact Or.inr (Or.inl ⟨a,rfl⟩)
      | cons b rest =>
        cases rest with
        | nil => exact Or.inr (Or.inr ⟨a,b,rfl⟩)
        | cons c rest => simp [h] at count

  have oldValueCopy (w : List Bool) (gs : List Gate) (g : Gate) (a : ℕ)
      (pins : g.inputs = [a]) (kind : g.op = .and ∨ g.op = .or) :
      ((gs++[g]).foldl step w).getD (w.length+gs.length) false =
        (gs.foldl step w).getD a false := by
    rw [newWire,pins]
    rcases kind with and | or
    · rw [and]
      change (((_ && true) = _))
      exact Bool.and_true _
    · rw [or]
      change (((_ || false) = _))
      exact Bool.or_false _

  have gateMonotone (g : Gate) (base upper : List Bool)
      (kind : g.op = .and ∨ g.op = .or) (on : preservesOnes base upper)
      (before : g.op.eval (g.inputs.map fun i => base.getD i false) = true) :
      g.op.eval (g.inputs.map fun i => upper.getD i false) = true := by
    rcases kind with and | or
    · rw [and] at before ⊢
      change (g.inputs.map (fun i => base.getD i false)).all id = true at before
      change (g.inputs.map (fun i => upper.getD i false)).all id = true
      rw [List.all_eq_true] at before ⊢
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      exact on i (before _ (List.mem_map.mpr ⟨i,hi,rfl⟩))
    · rw [or] at before ⊢
      change (g.inputs.map (fun i => base.getD i false)).any id = true at before
      change (g.inputs.map (fun i => upper.getD i false)).any id = true
      rw [List.any_eq_true] at before ⊢
      obtain ⟨x,hx,yes⟩ := before
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      exact ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,on i yes⟩

  have oldValueAnd (w : List Bool) (gs : List Gate) (g : Gate) (a b : ℕ)
      (pins : g.inputs = [a,b]) (kind : g.op = .and) :
      ((gs++[g]).foldl step w).getD (w.length+gs.length) false = true ↔
        (gs.foldl step w).getD a false = true ∧ (gs.foldl step w).getD b false = true := by
    rw [newWire, pins, kind]
    change ((_ && (_ && true)) = true) ↔ _
    simp only [Bool.and_true, Bool.and_eq_true, id_eq]

  have oldValueOr (w : List Bool) (gs : List Gate) (g : Gate) (a b : ℕ)
      (pins : g.inputs = [a,b]) (kind : g.op = .or) :
      ((gs++[g]).foldl step w).getD (w.length+gs.length) false = true ↔
        (gs.foldl step w).getD a false = true ∨ (gs.foldl step w).getD b false = true := by
    rw [newWire, pins, kind]
    change ((_ || (_ || false)) = true) ↔ _
    simp only [Bool.or_false, Bool.or_eq_true, id_eq]

  have extendFold (gs : List Gate) (base upper : List Bool)
      (len : upper.length = base.length) (held : preservesOnes base upper)
      (model : legal gs) : preservesOnes (gs.foldl step base) (gs.foldl step upper) := by
    induction gs using List.reverseRecOn with
    | nil => exact held
    | append_singleton gs g ih =>
      have prior := ih (legalBefore _ _ model)
      intro i trueAtBase
      rcases lt_trichotomy i (base.length+gs.length) with early | last | late
      · rw [oldWire gs base g i early] at trueAtBase
        rw [oldWire gs upper g i (by rwa [len])]
        exact prior i trueAtBase
      · have kind := (legalLast gs g model).1
        have upperLast : i = upper.length+gs.length := by rwa [len]
        rw [last,newWire] at trueAtBase
        rw [upperLast,newWire]
        exact gateMonotone g _ _ kind prior trueAtBase
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
              rw [wireLength, List.length_append, List.length_singleton]; omega)] at trueAtBase
        contradiction

  have lineCertify (gs : List Gate) (base upper : List Bool) (W : Finset ℕ)
      (baseLen : base.length = upper.length) (model : legal gs)
      (bounds : ∀ i ∈ W, i < upper.length + gs.length)
      (facts : ∀ i ∈ W, (gs.foldl step upper).getD i false = true)
      (unsettled : ∀ i ∈ W, (gs.foldl step base).getD i false = false) :
      ∃ T : Finset ℕ, T.card ≤ W.card + charge base upper gs ∧
        (∀ i ∈ T, i < upper.length ∧ upper.getD i false = true ∧ base.getD i false = false) ∧
        ∀ z : List Bool, z.length = upper.length → preservesOnes base z →
          (∀ i ∈ T, z.getD i false = true) →
          ∀ i ∈ W, (gs.foldl step z).getD i false = true := by
    induction gs using List.reverseRecOn generalizing W with
    | nil =>
      exact ⟨W,by simp [chargeNil],
        fun i hi => ⟨by simpa using bounds i hi,facts i hi,unsettled i hi⟩,
        fun _ _ _ hz i hi => hz i hi⟩
    | append_singleton gs g ih =>
      let last := upper.length + gs.length
      let B := W.erase last
      have legalPrefix := legalBefore _ _ model
      have nonDecrease : charge base upper gs ≤ charge base upper (gs++[g]) := by
        rw [charge_append]
        omega
      have earlier (i : ℕ) (hi : i ∈ W) (hne : i ≠ last) : i < last := by
        have h := bounds i hi
        simp only [List.length_append, List.length_singleton] at h
        omega
      by_cases takeLast : last ∈ W
      · obtain ⟨op, arity⟩ := legalLast gs g model
        have boundB : ∀ i ∈ B, i < last :=
          fun i hi => earlier i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
        have trueB : ∀ i ∈ B, (gs.foldl step upper).getD i false = true := by
          intro i hi
          rw [← oldWire gs upper g i (boundB i hi)]
          exact facts i (Finset.mem_of_mem_erase hi)
        have falseB : ∀ i ∈ B, (gs.foldl step base).getD i false = false := by
          intro i hi
          rw [← oldWire gs base g i (by rw [baseLen]; exact boundB i hi)]
          exact unsettled i (Finset.mem_of_mem_erase hi)
        have budgetB : B.card + 1 = W.card := Finset.card_erase_add_one takeLast
        have lastUpper : ((gs++[g]).foldl step upper).getD (upper.length+gs.length) false = true :=
          facts last takeLast
        have lastBase : ((gs++[g]).foldl step base).getD (base.length+gs.length) false = false := by
          rw [baseLen]
          exact unsettled last takeLast
        have combine (P : Finset ℕ) (pbound : ∀ i ∈ P, i < last)
            (ptrue : ∀ i ∈ P, (gs.foldl step upper).getD i false = true)
            (pfalse : ∀ i ∈ P, (gs.foldl step base).getD i false = false)
            (budget : (B ∪ P).card + charge base upper gs ≤ W.card + charge base upper (gs++[g]))
            (derive : ∀ z : List Bool, z.length = upper.length → preservesOnes base z →
              (∀ i ∈ P, (gs.foldl step z).getD i false = true) →
              ((gs++[g]).foldl step z).getD last false = true) :
            ∃ T : Finset ℕ, T.card ≤ W.card + charge base upper (gs++[g]) ∧
              (∀ i ∈ T, i < upper.length ∧ upper.getD i false = true ∧ base.getD i false = false) ∧
              ∀ z : List Bool, z.length = upper.length → preservesOnes base z →
                (∀ i ∈ T, (z.getD i false = true)) →
                ∀ i ∈ W, ((gs++[g]).foldl step z).getD i false = true := by
          have union (P' : ℕ → Prop) (hB : ∀ i ∈ B, P' i) (hP : ∀ i ∈ P, P' i) :
              ∀ i ∈ B ∪ P, P' i := by
            intro i hi
            rcases Finset.mem_union.mp hi with localB | localP
            · exact hB i localB
            · exact hP i localP
          obtain ⟨T,card,inputs,yes⟩ := ih (B ∪ P) legalPrefix
            (union _ boundB pbound) (union _ trueB ptrue) (union _ falseB pfalse)
          refine ⟨T,card.trans budget,inputs,fun z len ext hz i hi => ?_⟩
          have holds := yes z len ext hz
          by_cases atEnd : i = last
          · subst i
            exact derive z len ext (fun j hj => holds j (Finset.mem_union_right _ hj))
          · rw [oldWire gs z g i (by rw [len]; exact earlier i hi atEnd)]
            exact holds i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨atEnd,hi⟩))
        have available (i : ℕ) (on : (gs.foldl step upper).getD i false = true) : i < last := by
          by_contra! late
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
            rw [wireLength]; exact late)] at on
          contradiction
        rcases gateInputs g arity with pins | ⟨a,pins⟩ | ⟨a,b,pins⟩
        · rcases op with and | or
          · rw [newWire,pins,and] at lastBase
            contradiction
          · rw [newWire,pins,or] at lastUpper
            contradiction
        · have onA := lastUpper
          have offA := lastBase
          rw [oldValueCopy _ _ _ _ pins op] at onA offA
          have join := Finset.card_union_le B ({a} : Finset ℕ)
          rw [Finset.card_singleton] at join
          refine combine {a} (by simpa only [Finset.mem_singleton,forall_eq] using available a onA)
            (by simpa only [Finset.mem_singleton,forall_eq] using onA)
            (by simpa only [Finset.mem_singleton,forall_eq] using offA) (by omega) ?_
          intro z len _ hz
          rw [show last = z.length+gs.length by rw [len], oldValueCopy _ _ _ _ pins op]
          exact hz a (by simp)
        · rcases op with and | or
          · obtain ⟨trueA,trueB'⟩ := (oldValueAnd _ _ _ _ _ pins and).mp lastUpper
            let P := ({a,b} : Finset ℕ).filter (fun i => (gs.foldl step base).getD i false = false)
            have pcond : ∀ i, i ∈ P ↔ (i = a ∨ i = b) ∧ (gs.foldl step base).getD i false = false := by
              simp [P]
            have cardF : P.card ≤ 2 :=
              (Finset.card_filter_le _ _).trans (by simpa using Finset.card_insert_le a ({b} : Finset ℕ))
            have localBudget : P.card ≤ 1 + (priced (gs.foldl step base) (gs.foldl step upper) g).toNat := by
              by_cases aFalse : (gs.foldl step base).getD a false = false
              · by_cases bFalse : (gs.foldl step base).getD b false = false
                · have work : priced (gs.foldl step base) (gs.foldl step upper) g = true := by
                    simp only [priced,pins,and,List.all_cons,List.all_nil,aFalse,bFalse,trueA,trueB']; rfl
                  rw [work]
                  exact cardF
                · have sub : P ⊆ {a} := by
                    intro i hi
                    rcases (pcond i).mp hi with ⟨rfl | rfl,h⟩
                    · exact Finset.mem_singleton_self _
                    · exact (bFalse h).elim
                  have le := Finset.card_le_card sub
                  rw [Finset.card_singleton] at le
                  omega
              · have sub : P ⊆ {b} := by
                  intro i hi
                  rcases (pcond i).mp hi with ⟨rfl | rfl,h⟩
                  · exact (aFalse h).elim
                  · exact Finset.mem_singleton_self _
                have le := Finset.card_le_card sub
                rw [Finset.card_singleton] at le
                omega
            refine combine P ?_ ?_ ?_ ?_ ?_
            · intro i hi
              rcases ((pcond i).mp hi).1 with rfl | rfl
              · exact available _ trueA
              · exact available _ trueB'
            · intro i hi
              rcases ((pcond i).mp hi).1 with rfl | rfl
              · exact trueA
              · exact trueB'
            · exact fun i hi => ((pcond i).mp hi).2
            · have join := Finset.card_union_le B P
              rw [charge_append]
              omega
            · intro z len ext hz
              have stable := extendFold gs base z (len.trans baseLen.symm) ext legalPrefix
              have enough (i : ℕ) (read : i = a ∨ i = b) :
                  (gs.foldl step z).getD i false = true := by
                cases flag : (gs.foldl step base).getD i false
                · exact hz i ((pcond i).mpr ⟨read,flag⟩)
                · exact stable i flag
              rw [show last = z.length+gs.length by rw [len], oldValueAnd _ _ _ _ _ pins and]
              exact ⟨enough a (Or.inl rfl),enough b (Or.inr rfl)⟩
          · have neither : (gs.foldl step base).getD a false = false ∧
                (gs.foldl step base).getD b false = false := by
              constructor
              · cases h : (gs.foldl step base).getD a false
                · rfl
                · have impossible := (oldValueOr _ _ _ _ _ pins or).mpr (Or.inl h)
                  rw [lastBase] at impossible
                  contradiction
              · cases h : (gs.foldl step base).getD b false
                · rfl
                · have impossible := (oldValueOr _ _ _ _ _ pins or).mpr (Or.inr h)
                  rw [lastBase] at impossible
                  contradiction
            obtain ⟨i, earlierI, reads, trueI, falseI⟩ :
                ∃ i, i < last ∧ (i = a ∨ i = b) ∧ (gs.foldl step upper).getD i false = true ∧
                  (gs.foldl step base).getD i false = false := by
              rcases (oldValueOr _ _ _ _ _ pins or).mp lastUpper with trueA | trueB'
              · exact ⟨a,available a trueA,Or.inl rfl,trueA,neither.1⟩
              · exact ⟨b,available b trueB',Or.inr rfl,trueB',neither.2⟩
            have join := Finset.card_union_le B ({i} : Finset ℕ)
            rw [Finset.card_singleton] at join
            refine combine {i} (by simpa only [Finset.mem_singleton,forall_eq] using earlierI)
              (by simpa only [Finset.mem_singleton,forall_eq] using trueI)
              (by simpa only [Finset.mem_singleton,forall_eq] using falseI) (by omega) ?_
            intro z len _ hz
            rw [show last = z.length+gs.length by rw [len], oldValueOr _ _ _ _ _ pins or]
            exact reads.elim (fun e => Or.inl (e ▸ hz i (by simp))) (fun e => Or.inr (e ▸ hz i (by simp)))
      · have early : ∀ i ∈ W, i < last :=
          fun i hi => earlier i hi (fun h => takeLast (h ▸ hi))
        have yes : ∀ i ∈ W, (gs.foldl step upper).getD i false = true := by
          intro i hi
          rw [← oldWire gs upper g i (early i hi)]
          exact facts i hi
        have no : ∀ i ∈ W, (gs.foldl step base).getD i false = false := by
          intro i hi
          rw [← oldWire gs base g i (by rw [baseLen]; exact early i hi)]
          exact unsettled i hi
        obtain ⟨T,card,inputs,certified⟩ := ih W legalPrefix early yes no
        refine ⟨T,by omega,inputs,fun z len ext hz i hi => ?_⟩
        rw [oldWire gs z g i (by rw [len]; exact early i hi)]
        exact certified z len ext hz i hi

  have legalOfMonotone2 (C : Circuit) (model : Monotone2 C) : legal C.gates := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using model g hg

  have pointValue {a b : ℕ} (X : Finset (Fin a)) (Y : Finset (Fin b)) (p : Fin a) :
      (encodeInput X Y).getD p.val false = decide (p ∈ X) := by
    unfold encodeInput
    rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

  have lineValue {a b : ℕ} (X : Finset (Fin a)) (Y : Finset (Fin b)) (l : Fin b) :
      (encodeInput X Y).getD (a + l.val) false = decide (l ∈ Y) := by
    unfold encodeInput
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn,
      show a + l.val - a = l.val by omega, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]


  have inputLength {a b : ℕ} (X : Finset (Fin a)) (Y : Finset (Fin b)) :
      (encodeInput X Y).length = a+b := by
    simp [encodeInput]

  have inputExtends {a b : ℕ} (X : Finset (Fin a)) (Y Z : Finset (Fin b))
      (subset : Y ⊆ Z) : preservesOnes (encodeInput X Y) (encodeInput X Z) := by
    intro i on
    by_cases point : i < a
    · let p : Fin a := ⟨i,point⟩
      change (encodeInput X Y).getD p.val false = true at on
      change (encodeInput X Z).getD p.val false = true
      simpa only [pointValue] using on
    · have inside : i < a+b := by
        by_contra! large
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
          rw [inputLength]; exact large)] at on
        contradiction
      let l : Fin b := ⟨i-a,by omega⟩
      have form : i = a + l.val := by change i = a+(i-a); omega
      rw [form,lineValue,decide_eq_true_eq] at on ⊢
      exact subset on

  let activeLineAnds {a b : ℕ} (C : Circuit) (X : Finset (Fin a)) (Y : Finset (Fin b)) : ℕ :=
    charge (encodeInput X (∅ : Finset (Fin b))) (encodeInput X Y) C.gates

  have relative_line_certificate {a b : ℕ} (C : Circuit) (model : Monotone2 C)
      (X : Finset (Fin a)) (Y : Finset (Fin b))
      (baseFalse : C.eval (encodeInput X (∅ : Finset (Fin b))) = false)
      (accepted : C.eval (encodeInput X Y) = true) :
      ∃ Z ⊆ Y, Z.card ≤ 1 + activeLineAnds C X Y ∧ C.eval (encodeInput X Z) = true := by
    let base := encodeInput X (∅ : Finset (Fin b))
    let upper := encodeInput X Y
    have baseLen : base.length = upper.length := by rw [inputLength,inputLength]
    have upperLen : upper.length = a+b := inputLength _ _
    have model' : legal C.gates := legalOfMonotone2 C model
    have selected : (C.gates.foldl step upper).getD C.output false = true := accepted
    have rejected : (C.gates.foldl step base).getD C.output false = false := baseFalse
    have inside : C.output < upper.length + C.gates.length := by
      by_contra! high
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by rw [wireLength]; exact high)] at selected
      contradiction
    obtain ⟨T,card,inputs,support⟩ := lineCertify C.gates base upper {C.output}
      baseLen model' (by simpa only [Finset.mem_singleton,forall_eq] using inside)
      (by simpa only [Finset.mem_singleton,forall_eq] using selected)
      (by simpa only [Finset.mem_singleton,forall_eq] using rejected)
    let Z := Finset.univ.filter fun l : Fin b => a+l.val ∈ T
    have lines (l : Fin b) : l ∈ Z ↔ a+l.val ∈ T := by simp [Z]
    have sub : Z ⊆ Y := by
      intro l inZ
      have on := (inputs (a+l.val) ((lines l).mp inZ)).2.1
      change (encodeInput X Y).getD (a+l.val) false = true at on
      rwa [lineValue,decide_eq_true_eq] at on
    refine ⟨Z,sub,?_,?_⟩
    · have count : Z.card ≤ T.card := by
        apply Finset.card_le_card_of_injOn (fun l : Fin b => a + l.val)
        · intro l hl
          exact (lines l).mp hl
        · intro i _ j _ eq
          change a+i.val = a+j.val at eq
          exact Fin.ext (by omega)
      exact count.trans (by simpa only [Finset.card_singleton, activeLineAnds] using card)
    · let z := encodeInput X Z
      have len : z.length = upper.length := by rw [inputLength,inputLength]
      have extend : preservesOnes base z := inputExtends X ∅ Z (Finset.empty_subset Z)
      have needed : ∀ i ∈ T, z.getD i false = true := by
        intro i hi
        obtain ⟨inside,on,off⟩ := inputs i hi
        by_cases point : i < a
        · let p : Fin a := ⟨i,point⟩
          change (encodeInput X Y).getD p.val false = true at on
          change (encodeInput X (∅ : Finset (Fin b))).getD p.val false = false at off
          rw [pointValue] at on off
          rw [on] at off
          contradiction
        · have range : i < a+b := upperLen ▸ inside
          let l : Fin b := ⟨i-a,by omega⟩
          have form : i = a+l.val := by change i = a+(i-a); omega
          change (encodeInput X Z).getD i false = true
          rw [form,lineValue,decide_eq_true_eq]
          exact (lines l).mpr (form ▸ hi)
      exact support z len extend needed C.output (Finset.mem_singleton_self _)

  have critical_lines_need_active_ands {a b : ℕ} (C : Circuit) (model : Monotone2 C)
      (X : Finset (Fin a)) (Y : Finset (Fin b))
      (baseFalse : C.eval (encodeInput X (∅ : Finset (Fin b))) = false)
      (accepted : C.eval (encodeInput X Y) = true)
      (critical : ∀ l ∈ Y, C.eval (encodeInput X (Y.erase l)) = false) :
      Y.card ≤ 1 + activeLineAnds C X Y := by
    obtain ⟨Z,sub,price,works⟩ := relative_line_certificate C model X Y baseFalse accepted
    suffices same : Y ⊆ Z from (Finset.card_le_card same).trans price
    intro l inY
    by_contra notInZ
    have subErase : Z ⊆ Y.erase l := by
      intro u hu
      exact Finset.mem_erase.mpr ⟨fun same => notInZ (same ▸ hu),sub hu⟩
    let lower := encodeInput X Z
    let upper := encodeInput X (Y.erase l)
    have sameLen : upper.length = lower.length := by rw [inputLength,inputLength]
    have model' : legal C.gates := legalOfMonotone2 C model
    have preserves := extendFold C.gates lower upper sameLen (inputExtends X Z (Y.erase l) subErase) model'
    have remains : C.eval upper = true := preserves C.output works
    rw [critical l inY] at remains
    contradiction


  let activePoints {a b : ℕ} (input : Fin (a+b) → Bool) : Finset (Fin a) :=
    Finset.univ.filter fun p => input (Fin.castAdd b p) = true

  let activeLines {a b : ℕ} (input : Fin (a+b) → Bool) : Finset (Fin b) :=
    Finset.univ.filter fun l => input (Fin.natAdd a l) = true

  have inputOfFn {a b : ℕ} (input : Fin (a+b) → Bool) :
      List.ofFn input = encodeInput (activePoints input) (activeLines input) := by
    rw [List.ofFn_add]
    unfold encodeInput
    congr 1
    · apply congrArg List.ofFn
      funext p
      change input (Fin.castAdd b p) = decide (p ∈ activePoints input)
      cases h : input (Fin.castAdd b p) <;> simp [activePoints,h]
    · apply congrArg List.ofFn
      funext l
      cases h : input (Fin.natAdd a l) <;> simp [activeLines,h]

  have point_ne_line {a b : ℕ} (p : Fin a) (l : Fin b) :
      Fin.castAdd b p ≠ Fin.natAdd a l := by
    intro same
    have val := congrArg Fin.val same
    change p.val = a+l.val at val
    omega

  have eraseLine {a b : ℕ} (input : Fin (a+b) → Bool) (l : Fin b) :
      List.ofFn (Function.update input (Fin.natAdd a l) false) =
        encodeInput (activePoints input) ((activeLines input).erase l) := by
    rw [inputOfFn]
    congr 1
    · ext p
      simp [activePoints,Function.update_of_ne (point_ne_line p l)]
    · ext j
      by_cases same : j = l
      · subst j
        simp [activeLines]
      · simp [activeLines,Finset.mem_erase,same]

  have essential_line_count_le_active_ands {q N : ℕ} (I : Fin N → Fin N → Prop)
      (C : Circuit) (model : Monotone2 C)
      (sound : ∀ input : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // input (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ input (Fin.castAdd N p) = true ∧
          input (Fin.natAdd N l) = true) → circuitFun (N+N) C input = false)
      (input : Fin (N+N) → Bool) (on : circuitFun (N+N) C input = true)
      (essential : ∀ l : Fin N, input (Fin.natAdd N l) = true →
        circuitFun (N+N) C (Function.update input (Fin.natAdd N l) false) = false) :
      Fintype.card {l : Fin N // input (Fin.natAdd N l) = true} ≤
        1 + activeLineAnds C (activePoints input) (activeLines input) := by
    let base : Fin (N+N) → Bool :=
      Fin.addCases (fun p => input (Fin.castAdd N p)) (fun _ => false)
    have onBasePoints : activePoints base = activePoints input := by
      ext p
      simp [activePoints,base]
    have baseOffLine (l : Fin N) : base (Fin.natAdd N l) = false :=
      Fin.addCases_right l
    have offBaseLines : activeLines base = ∅ := by
      ext l
      simp only [activeLines,Finset.mem_filter,Finset.mem_univ,true_and,baseOffLine,
        Bool.false_eq_true,Finset.notMem_empty]
    have less : Fintype.card {l : Fin N // base (Fin.natAdd N l) = true} ≤ q := by
      rw [Fintype.card_subtype]
      change (activeLines base).card ≤ q
      simp [offBaseLines]
    have independent : ¬ ∃ p l : Fin N, I p l ∧ base (Fin.castAdd N p) = true ∧
        base (Fin.natAdd N l) = true := by
      rintro ⟨p,l,_,_,onLine⟩
      rw [baseOffLine] at onLine
      contradiction
    have baseOff := sound base less independent
    change C.eval (List.ofFn base) = false at baseOff
    rw [inputOfFn,onBasePoints,offBaseLines] at baseOff
    change C.eval (List.ofFn input) = true at on
    rw [inputOfFn] at on
    have drops : ∀ l ∈ activeLines input,
        C.eval (encodeInput (activePoints input) ((activeLines input).erase l)) = false := by
      intro l hl
      have h := essential l ((Finset.mem_filter.mp hl).2)
      change C.eval (List.ofFn (Function.update input (Fin.natAdd N l) false)) = false at h
      rwa [eraseLine] at h
    have needed := critical_lines_need_active_ands C model (activePoints input)
      (activeLines input) baseOff on drops
    rw [Fintype.card_subtype]
    exact needed


  have prices_separate_from_ors (gs : List Gate) (base upper : List Bool)
      (model : legal gs) :
      charge base upper gs + (gs.filter (fun g => g.op.eval [true,false])).length ≤ gs.length := by
    induction gs generalizing base upper with
    | nil => simp [chargeNil]
    | cons g tail ih =>
      have gut := (model g List.mem_cons_self).1
      have rest := ih (step base g) (step upper g)
        (fun k hk => model k (List.mem_cons_of_mem _ hk))
      rcases gut with and | or
      · have drops : g.op.eval [true,false] = false := by rw [and]; rfl
        simp only [chargeCons,List.filter_cons,drops,Bool.false_eq_true,ite_false,List.length_cons]
        cases priced base upper g <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
      · have keeps : g.op.eval [true,false] = true := by rw [or]; rfl
        have free : priced base upper g = false := by
          unfold priced
          rw [or]
          have visible : GateOp.or.eval [false,true] = true := by rfl
          rw [visible]
          simp
        simp only [chargeCons,free,List.filter_cons,keeps,ite_true,List.length_cons,Bool.toNat_false]
        omega

  intro q N I _ C hq hN degree uniqueLine model pairs sound input nonincident on many critical
  have orFloor := orBound q N I C (by omega) hN degree uniqueLine model pairs sound
  have lineFloor := essential_line_count_le_active_ands I C model sound input on critical
  have separate := prices_separate_from_ors C.gates
    (encodeInput (activePoints input) (∅ : Finset (Fin N)))
    (encodeInput (activePoints input) (activeLines input)) (legalOfMonotone2 C model)
  change activeLineAnds C (activePoints input) (activeLines input) +
    (C.gates.filter (fun g => g.op.eval [true,false])).length ≤ C.size at separate
  let r := (C.gates.filter (fun g => g.op.eval [true,false])).length
  let y := Fintype.card {l : Fin N // input (Fin.natAdd N l) = true}
  have combined : r + y - 1 ≤ C.size := by
    change y ≤ 1 + activeLineAnds C (activePoints input) (activeLines input) at lineFloor
    change activeLineAnds C (activePoints input) (activeLines input) + r ≤ C.size at separate
    omega
  by_cases enough : N*q ≤ 100*(r+y-1)
  · exact enough.trans (Nat.mul_le_mul_left 100 combined)
  · have deficit : 100*(r+y-1) < N*q := Nat.lt_of_not_ge enough
    have large : 200 ≤ q := by
      by_contra! below
      have q199 : q = 199 := by omega
      have floor : 2*q^2+1 ≤ r := orFloor
      change q < y at many
      rw [q199] at floor many deficit hN
      norm_num at floor hN deficit
      omega
    exact localDeficit q N I C large hN degree uniqueLine model pairs sound input nonincident
      on many critical orFloor deficit
