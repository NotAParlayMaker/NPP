import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 3500000 in
theorem PEqualNP.Outside.R_meta_3469_417
    (orBound : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q ^ 2 + q + 1 →
      (∀ l, (S l).card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → n+n ≤ C.output → C.output < n+n+C.size →
      (∃ g, C.gates[C.output-(n+n)]? = some g ∧ g.op = GateOp.or) →
      RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      n*q ≤ 100*C.size)
    (bothNeeded : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (a b : ℕ),
      200 ≤ q → n = q ^ 2 + q + 1 →
      (∀ l, (S l).card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → n+n ≤ a → n+n ≤ b → a < C.output → b < C.output →
      C.output < n+n+C.size → a ≠ b →
      C.gates[C.output-(n+n)]? = some ⟨GateOp.and,[a,b]⟩ →
      RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      (∀ w ∈ [a,b], ∃ X Y, Y.card ≤ q ∧ IsFalseInput S X Y ∧
        wireValue C (incidenceInput X Y) w = true) →
      n*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq hn hcard huniq model outLo outHi outAnd rightOn sound
  classical
  let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
  have keep (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
      (gs.foldl step x).getD i false = x.getD i false := by
    induction gs generalizing x with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · exact List.getD_append _ _ _ _ hi
      · simp only [step,List.length_append,List.length_singleton]; omega
  have gateValue (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate)
      (seen : gs[j]? = some g) (reads : ∀ i ∈ g.inputs, i < x.length+j) :
      (gs.foldl step x).getD (x.length+j) false =
        g.op.eval (g.inputs.map fun i => (gs.foldl step x).getD i false) := by
    induction gs generalizing x j with
    | nil => simp at seen
    | cons head gs ih =>
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at seen
          subst head
          rw [List.foldl_cons,Nat.add_zero,keep]
          · rw [show (step x g).getD x.length false =
                g.op.eval (g.inputs.map fun i => x.getD i false) from by
                  change (x ++ [_]).getD x.length false = _
                  rw [List.getD_append_right _ _ _ _ (le_refl _),Nat.sub_self]
                  rfl]
            congr 1
            apply List.map_congr_left
            intro i hi
            have lt : i < x.length := by simpa only [Nat.add_zero] using reads i hi
            rw [keep _ _ _ (by simp only [step,List.length_append,List.length_singleton]; omega)]
            exact (List.getD_append _ _ _ _ lt).symm
          · simp only [step,List.length_append,List.length_singleton]; omega
        | succ j =>
          have size : (step x head).length = x.length + 1 := by
            simp only [step,List.length_append,List.length_singleton]
          rw [List.foldl_cons,show x.length+(j+1) = (step x head).length+j by omega]
          apply ih
          · exact seen
          · intro i hi
            have h := reads i hi
            omega
  have inputLen (X Y : Finset (Fin n)) : (incidenceInput X Y).length = n+n := by
    change (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin n => decide (l ∈ Y))).length = n+n
    simp only [List.length_append,List.length_ofFn]
  have nbig : 2 ≤ n := by omega
  have otherIndex (a : Fin n) : ∃ b : Fin n, b ≠ a := by
    let zero : Fin n := ⟨0,by omega⟩
    let one : Fin n := ⟨1,by omega⟩
    by_cases eq : a = zero
    · refine ⟨one,?_⟩
      rw [eq]
      intro same
      have h := congrArg Fin.val same
      change 1 = 0 at h
      omega
    · exact ⟨zero,Ne.symm eq⟩
  have avoidsRaw (i : ℕ) (raw : i < n+n) :
      ∃ (l p : Fin n), p ∈ S l ∧ (incidenceInput {p} {l}).getD i false = false := by
    by_cases isPoint : i < n
    · let pi : Fin n := ⟨i,isPoint⟩
      obtain ⟨p,pne⟩ := otherIndex pi
      obtain ⟨l,inc,_⟩ := huniq p pi pne
      refine ⟨l,p,inc.1,?_⟩
      change (List.ofFn (fun k : Fin n => decide (k ∈ ({p} : Finset (Fin n)))) ++
        List.ofFn (fun k : Fin n => decide (k ∈ ({l} : Finset (Fin n))))).getD i false = false
      rw [List.getD_append _ _ _ _ (by simpa using isPoint)]
      rw [List.getD_eq_getElem _ _ (by simpa using isPoint),List.getElem_ofFn]
      exact decide_eq_false (by simpa only [Finset.mem_singleton] using Ne.symm pne)
    · let li : Fin n := ⟨i-n,by omega⟩
      obtain ⟨l,lne⟩ := otherIndex li
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (by rw [hcard]; omega : 0 < (S l).card)
      refine ⟨l,p,hp,?_⟩
      change (List.ofFn (fun k : Fin n => decide (k ∈ ({p} : Finset (Fin n)))) ++
        List.ofFn (fun k : Fin n => decide (k ∈ ({l} : Finset (Fin n))))).getD i false = false
      rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt isPoint),List.length_ofFn]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega),List.getElem_ofFn]
      exact decide_eq_false (by simpa only [Finset.mem_singleton] using Ne.symm lne)
  let V (w : ℕ) : Circuit := ⟨C.gates,w⟩
  have lower (w : ℕ) (existsWire : w < n+n+C.size)
      (accepts : RightOnIncidentPairs S (V w))
      (rejects : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y → (V w).eval (incidenceInput X Y) = false) :
      n*q ≤ 100*C.size := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      have wge : n+n ≤ w := by
        by_contra! raw
        obtain ⟨l,p,inc,off⟩ := avoidsRaw w raw
        have eq := accepts l p inc
        change (C.gates.foldl step (incidenceInput {p} {l})).getD w false = true at eq
        rw [keep _ _ _ (by rwa [inputLen]),off] at eq
        exact Bool.noConfusion eq
      have jlt : w-(n+n) < C.gates.length := by
        change w-(n+n) < C.size
        omega
      obtain ⟨g,lookup⟩ : ∃ g, C.gates[w-(n+n)]? = some g :=
        ⟨C.gates[w-(n+n)],getElem?_pos C.gates _ jlt⟩
      have member := List.mem_of_getElem? lookup
      rcases model.1 g member with hop | hop
      · obtain ⟨a,b,inputs⟩ : ∃ a b, g.inputs = [a,b] := by
          have arity := model.2.2 g member
          cases hs : g.inputs with
          | nil => simp [hs] at arity
          | cons a rest =>
            cases rest with
            | nil => simp [hs] at arity
            | cons b rest =>
              have empty : rest = [] := by
                apply List.length_eq_zero_iff.mp
                simp only [hs,List.length_cons] at arity
                omega
              subst rest
              exact ⟨a,b,rfl⟩
        have earlier (i : ℕ) (hi : i ∈ [a,b]) : i < w := by
          obtain ⟨_,atGate⟩ := List.getElem?_eq_some_iff.mp lookup
          have back := model.2.1 (w-(n+n)) jlt
          change ∀ i ∈ (C.gates.getD (w-(n+n)) ⟨GateOp.or,[]⟩).inputs, i < n+n+(w-(n+n)) at back
          rw [List.getD_eq_getElem _ _ jlt,atGate,inputs] at back
          have h := back i hi
          omega
        have andValue (X Y : Finset (Fin n)) :
            (V w).eval (incidenceInput X Y) =
              (wireValue C (incidenceInput X Y) a && wireValue C (incidenceInput X Y) b) := by
          have gateReads : ∀ i ∈ g.inputs, i < (incidenceInput X Y).length + (w-(n+n)) := by
            rw [inputs,inputLen]
            intro i hi
            have hr := earlier i hi
            omega
          have e := gateValue C.gates (incidenceInput X Y) _ g lookup gateReads
          rw [inputLen,show n+n+(w-(n+n)) = w by omega,hop,inputs] at e
          change (V w).eval (incidenceInput X Y) =
            (wireValue C (incidenceInput X Y) a && (wireValue C (incidenceInput X Y) b && true)) at e
          simpa only [Bool.and_true] using e
        have subAccepts (i : ℕ) (hi : i ∈ [a,b]) : RightOnIncidentPairs S (V i) := by
          intro l p hp
          have e := accepts l p hp
          rw [andValue] at e
          rcases List.mem_cons.mp hi with hi | hi
          · subst i
            exact (Bool.and_eq_true_iff.mp e).1
          · have eq : i = b := List.mem_singleton.mp hi
            subst i
            exact (Bool.and_eq_true_iff.mp e).2
        by_cases bothFail : ∀ i ∈ [a,b], ∃ X Y, Y.card ≤ q ∧ IsFalseInput S X Y ∧
            wireValue C (incidenceInput X Y) i = true
        · have operandInternal (i : ℕ) (hi : i ∈ [a,b]) : n+n ≤ i := by
            by_contra! raw
            obtain ⟨l,p,inc,off⟩ := avoidsRaw i raw
            have eq := subAccepts i hi l p inc
            change (C.gates.foldl step (incidenceInput {p} {l})).getD i false = true at eq
            rw [keep _ _ _ (by rwa [inputLen]),off] at eq
            exact Bool.noConfusion eq
          have distinct : a ≠ b := by
            intro same
            obtain ⟨X,Y,small,nonedge,positive⟩ := bothFail a (by simp)
            have e := rejects X Y small nonedge
            rw [andValue,← same,positive] at e
            exact Bool.noConfusion e
          have eq : g = ⟨GateOp.and,[a,b]⟩ := by cases g; simp_all only
          exact bothNeeded q n S (V w) a b hq hn hcard huniq model
            (operandInternal a (by simp)) (operandInternal b (by simp))
            (earlier a (by simp)) (earlier b (by simp)) existsWire distinct
            (lookup.trans (congrArg some eq)) accepts rejects bothFail
        · push Not at bothFail
          obtain ⟨i,hi,hs⟩ := bothFail
          apply ih i (earlier i hi) (by have h := earlier i hi; omega) (subAccepts i hi)
          intro X Y small nonedge
          have e := hs X Y small nonedge
          change wireValue C (incidenceInput X Y) i = false
          cases v : wireValue C (incidenceInput X Y) i with
          | false => rfl
          | true => exact (e v).elim
      · exact orBound q n S (V w) hq hn hcard huniq model wge existsWire ⟨g,lookup,hop⟩ accepts rejects
  exact lower C.output outHi rightOn sound
