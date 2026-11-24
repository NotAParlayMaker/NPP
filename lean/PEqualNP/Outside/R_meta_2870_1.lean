import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.GenericRejection in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2870_1
    (supportBound : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → C.output < n + C.size →
      (∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
        circuitFun n C x ≠ circuitFun n C y) → n ≤ C.size + 1)
    (lowMultiplicity : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      PEqualNP.ReadTwo.Lin (fun p l => p ∈ S l) → IsAO2 (n+n) C →
      (∀ X Y, Y.card ≤ 2 → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      ∀ E : Finset (Fin n × Fin n),
        (∀ e ∈ E, e.1 ∈ S e.2 ∧
          PEqualNP.ReadK.readsAtMost C (n+n) [e.1.val, n+e.2.val] 2 = true) →
        E.card ≤ 62 * C.size + 2 * n)
    (highMultiplicity : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      100 < q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      PEqualNP.ReadTwo.Lin (fun p l => p ∈ S l) → IsAO2 (n+n) C →
      RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      100 * C.size < n * q →
      ∀ E : Finset (Fin n × Fin n),
        (∀ e ∈ E, e.1 ∈ S e.2 ∧
          PEqualNP.ReadK.readsAtMost C (n+n) [e.1.val, n+e.2.val] 2 = false) →
        E.card ≤ 36 * C.size) :

  have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (1 : ℕ) ≤ x16.card → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  dsimp only
  intro q n R dec C qLarge geom lines connects basis output order accept reject U urange positiveU exactU few
  let S (l : Fin n) := Finset.univ.filter fun p : Fin n => R p l
  have incident (p l : Fin n) : p ∈ S l ↔ R p l := by simp [S]
  have lineSize (l : Fin n) : (S l).card = q+1 := by
    rw [← Fintype.card_coe]
    exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun p => incident p l))).trans (lines l)
  have through (p p' : Fin n) (unequal : p ≠ p') :
      ∃! l : Fin n, p ∈ S l ∧ p' ∈ S l := by
    simpa only [incident] using connects p p' unequal
  have gateSome (j : ℕ) (hj : j < C.gates.length) :
      C.gates[j]? = some (gateAt C j) := by
    have eq : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
    rw [eq]
    exact List.getElem?_eq_getElem hj
  have model : IsAO2 (n+n) C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simpa using (basis g hg).1
    · intro j hj i hi
      obtain ⟨a,b,ab,lt,back⟩ := order j _ (gateSome j hj)
      rw [ab, List.mem_cons, List.mem_singleton] at hi
      rcases hi with rfl | rfl <;> omega
    · intro g hg
      obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
      have get : C.gates[j]? = some g := by
        rw [List.getElem?_eq_getElem hj, eq]
      obtain ⟨a,b,ab,_,_⟩ := order j g get
      simp [ab]
  let vector (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
    Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have listForm (X Y : Finset (Fin n)) : List.ofFn (vector X Y) = incidenceInput X Y :=
    List.ofFn_fin_append _ _
  have vp (X Y : Finset (Fin n)) (p : Fin n) : vector X Y (Fin.castAdd n p) = decide (p ∈ X) :=
    Fin.addCases_left ..
  have vl (X Y : Finset (Fin n)) (l : Fin n) : vector X Y (Fin.natAdd n l) = decide (l ∈ Y) :=
    Fin.addCases_right ..
  have diff (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro equal
    have values := congrArg Fin.val equal
    simp only [Fin.val_castAdd, Fin.val_natAdd] at values
    have lt := p.isLt
    omega
  have pair (p l : Fin n) :
      vector {p} {l} = fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l) := by
    funext i
    refine Fin.addCases (motive := fun i => vector {p} {l} i =
      decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) ?_ ?_ i
    · intro a
      rw [vp]
      simp only [Finset.mem_singleton, Fin.castAdd_inj, diff a l, or_false]
    · intro b
      rw [vl]
      simp only [Finset.mem_singleton, Fin.natAdd_inj, Ne.symm (diff p b), false_or]
  have correct : RightOnIncidentPairs S C := by
    intro l p hp
    rw [← listForm, pair]
    exact accept p l ((incident p l).mp hp)
  have sound (X Y : Finset (Fin n)) (budget : Y.card ≤ q) (empty : IsFalseInput S X Y) :
      C.eval (incidenceInput X Y) = false := by
    have count : Fintype.card {l : Fin n // vector X Y (Fin.natAdd n l) = true} = Y.card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      refine Equiv.subtypeEquivRight (fun l => ?_)
      simp only [vl, decide_eq_true_eq]
    have outside : ¬ ∃ (p l : Fin n), R p l ∧ vector X Y (Fin.castAdd n p) = true ∧
        vector X Y (Fin.natAdd n l) = true := by
      rintro ⟨p,l,h,px,ly⟩
      have pX : p ∈ X := of_decide_eq_true ((vp X Y p).symm.trans px)
      have lY : l ∈ Y := of_decide_eq_true ((vl X Y l).symm.trans ly)
      exact Finset.disjoint_left.mp (empty l lY) ((incident p l).mpr h) pX
    rw [← listForm]
    exact reject (vector X Y) (count.trans_le budget) outside

  classical
  have lin : PEqualNP.ReadTwo.Lin (fun p l => p ∈ S l) := by
    intro a b l l' hab hll h
    obtain ⟨_, _, huniq⟩ := through a b hab
    exact hll ((huniq l ⟨h.1, h.2.1⟩).trans (huniq l' ⟨h.2.2.1, h.2.2.2⟩).symm)
  have hn : 1 < n := by rw [geom]; omega
  have pointNeighbor (p : Fin n) : ∃ l, p ∈ S l := by
    let p' : Fin n := if p.val = 0 then ⟨1, hn⟩ else ⟨0, by omega⟩
    have hp : p ≠ p' := by
      intro e
      have ev := congrArg Fin.val e
      by_cases hz : p.val = 0 <;> simp [p', hz] at ev
    obtain ⟨l, h, _⟩ := through p p' hp
    exact ⟨l, h.1⟩
  have lineNeighbor (l : Fin n) : ∃ p, p ∈ S l :=
    Finset.card_pos.1 (by rw [lineSize]; omega)
  have vc (X Y : Finset (Fin n)) :
      circuitFun (n+n) C (vector X Y) = C.eval (incidenceInput X Y) := by
    change C.eval (List.ofFn (vector X Y)) = _
    rw [listForm]
  have support : n + n ≤ C.size + 1 := by
    apply supportBound (n+n) C model output
    intro i
    refine Fin.addCases (motive := fun i => ∃ x y : Fin (n+n) → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ circuitFun (n+n) C x ≠ circuitFun (n+n) C y) ?_ ?_ i
    · intro p
      obtain ⟨l, hp⟩ := pointNeighbor p
      refine ⟨vector {p} {l}, vector ∅ {l}, ?_, ?_⟩
      · intro j hj
        refine Fin.addCases (motive := fun j => j ≠ Fin.castAdd n p →
          vector {p} {l} j = vector ∅ {l} j) ?_ ?_ j hj
        · intro p' hne
          have hpp : p' ≠ p := fun e => hne (congrArg (Fin.castAdd n) e)
          simp [vp, hpp]
        · intro l' _
          simp only [vl]
      · rw [vc, vc, correct l p hp, sound ∅ {l} (by simp; omega) (by
          intro l' _
          simp)]
        decide
    · intro l
      obtain ⟨p, hl⟩ := lineNeighbor l
      refine ⟨vector {p} {l}, vector {p} ∅, ?_, ?_⟩
      · intro j hj
        refine Fin.addCases (motive := fun j => j ≠ Fin.natAdd n l →
          vector {p} {l} j = vector {p} ∅ j) ?_ ?_ j hj
        · intro p' _
          simp only [vp]
        · intro l' hne
          have hll : l' ≠ l := fun e => hne (congrArg (Fin.natAdd n) e)
          change vector {p} {l} (Fin.natAdd n l') = vector {p} ∅ (Fin.natAdd n l')
          rw [vl, vl]
          simp [hll]
      · rw [vc, vc, correct l p hl, sound {p} ∅ (by simp) (by
          intro l' hl'
          simp at hl')]
        decide
  by_contra! small
  let E : Finset (Fin n × Fin n) := Finset.univ.filter fun e => e.1 ∈ S e.2
  let F (l : Fin n) : Finset (Fin n × Fin n) :=
    (S l).map ⟨fun p => (p,l), fun _ _ he => congrArg Prod.fst he⟩
  have memF (l : Fin n) (e : Fin n × Fin n) : e ∈ F l ↔ e.1 ∈ S l ∧ e.2 = l := by
    constructor
    · intro he
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp he
      exact ⟨hp,rfl⟩
    · rintro ⟨hp,hl⟩
      exact Finset.mem_map.mpr ⟨e.1,hp,Prod.ext rfl hl.symm⟩
  have edgeCount : E.card = n * (q + 1) := by
    have hE : E = (Finset.univ : Finset (Fin n)).biUnion F := by
      ext e
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, memF]
      constructor
      · intro h
        exact ⟨e.2, h, rfl⟩
      · rintro ⟨l, h, eql⟩
        exact eql ▸ h
    rw [hE, Finset.card_biUnion]
    · simp [F, lineSize]
    · intro l _ l' _ hne
      refine Finset.disjoint_left.mpr ?_
      intro e he he'
      exact hne (((memF l e).mp he).2.symm.trans ((memF l' e).mp he').2)
  let readable (e : Fin n × Fin n) : Prop :=
    PEqualNP.ReadK.readsAtMost C (n+n) [e.1.val, n+e.2.val] 2 = true
  letI : DecidablePred readable := fun e => inferInstanceAs (Decidable (_ = true))
  have lowBound : (E.filter readable).card ≤ 62 * C.size + 2 * n := by
    apply lowMultiplicity n S C lin model
      (fun X Y hY hNone => sound X Y (hY.trans (by omega)) hNone)
    intro e he
    obtain ⟨hm, hr⟩ := Finset.mem_filter.mp he
    exact ⟨(Finset.mem_filter.mp hm).2, hr⟩
  have highBound : (E.filter fun e => ¬ readable e).card ≤ 36 * C.size := by
    apply highMultiplicity q n S C qLarge geom lineSize lin model correct sound small
    intro e he
    obtain ⟨hm, hr⟩ := Finset.mem_filter.mp he
    exact ⟨(Finset.mem_filter.mp hm).2, Bool.eq_false_iff.mpr hr⟩
  have split : (E.filter readable).card + (E.filter fun e => ¬ readable e).card = E.card :=
    Finset.card_filter_add_card_filter_not (s := E) (p := readable)
  have positive : 1 ≤ C.size := by omega
  have lower : n*q ≤ 100*C.size := calc
    n*q ≤ n*(q+1) := Nat.mul_le_mul_left n (Nat.le_succ q)
    _ = E.card := edgeCount.symm
    _ ≤ 100*C.size := by rw [← split]; omega
  exact (not_lt_of_ge lower) small