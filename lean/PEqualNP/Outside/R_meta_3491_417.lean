import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open scoped BigOperators

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3491_417
    (prune : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → n ≤ C.output → C.output < n + C.size →
      ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = circuitFun n C ∧
        n ≤ D.output ∧ D.output + 1 = n + D.size ∧
        (∀ w ∈ Finset.Ico n D.output, ∃ g ∈ D.gates, w ∈ g.inputs))
    (liveBound : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) [DecidableRel I] (D : Circuit),
      (∀ p q l r, p ≠ q → l ≠ r → ¬(I p l ∧ I p r ∧ I q l ∧ I q r)) →
      IsAO2 (N+M) D →
      (∀ x : Fin (N+M) → Bool, circuitFun (N+M) D x =
        decide (∃ p l, I p l ∧ x (Fin.castAdd M p) = true ∧ x (Fin.natAdd N l) = true)) →
      D.output + 1 = N+M+D.size →
      (∀ w ∈ Finset.Ico (N+M) D.output, ∃ g ∈ D.gates, w ∈ g.inputs) →
      let E := PEqualNP.ReadTwo.incid I
      let S := E.image (fun e => e.1.val) ∪ E.image (fun e => N+e.2.val)
      let refs : Multiset ℕ := (D.gates.flatMap Gate.inputs : List ℕ)
      S.card ≤ D.size + 1 →
      (D.size + 1 < 2*S.card → ∃ w ∈ S, refs.count w = 1) →
      ∃ T : Finset (Fin (N+M)),
        (∀ p l, I p l → Fin.castAdd M p ∈ T ∨ Fin.natAdd N l ∈ T) ∧ E.card + T.card ≤ D.size+1) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : Finset (Fin (x1 + x2))), (∀ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 → Fin.castAdd x2 x10 ∈ x9 ∨ Fin.natAdd x1 x11 ∈ x9) ∧ (PEqualNP.ReadTwo.incid x3).card + x9.card ≤ x5.size + (1 : ℕ) := by
  intro N M I decision C linear shape correct
  classical
  let n := N+M
  let E := PEqualNP.ReadTwo.incid I
  let S := E.image (fun e => e.1.val) ∪ E.image (fun e => N+e.2.val)
  let point (p : Fin N) : Fin n := Fin.castAdd M p
  let line (l : Fin M) : Fin n := Fin.natAdd N l
  let goal (x : Fin n → Bool) := decide (∃ p l, I p l ∧ x (point p) = true ∧ x (line l) = true)
  have memEdge (p : Fin N) (l : Fin M) : (p,l) ∈ E ↔ I p l := by
    dsimp only [E]
    delta PEqualNP.ReadTwo.incid
    simp
  by_cases empty : E = ∅
  · refine ⟨∅, ?_, ?_⟩
    · intro p l e
      have h := (memEdge p l).mpr e
      rw [empty] at h
      exact (Finset.notMem_empty _ h).elim
    · change E.card + (∅ : Finset (Fin n)).card ≤ C.size + 1
      simp [empty]
  have nonempty : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr empty
  have separated (p : Fin N) (l : Fin M) : point p ≠ line l := by
    intro eq
    have ev := congrArg Fin.val eq
    change p.val = N+l.val at ev
    omega
  let step (z : List Bool) (g : Gate) := z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]
  have runLen (gs : List Gate) (z : List Bool) :
      (gs.foldl step z).length = z.length+gs.length := by
    induction gs generalizing z with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have keep (gs : List Gate) (z : List Bool) (i : ℕ) (hi : i < z.length) :
      (gs.foldl step z).getD i false = z.getD i false := by
    induction gs generalizing z with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · exact List.getD_append _ _ _ _ hi
      · simp only [step, List.length_append, List.length_singleton]; omega
  have input (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  let one (w : Fin n) (i : Fin n) := decide (i = w)
  have singleton (w : Fin n) : goal (one w) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨p,l,_,hp,hl⟩ := of_decide_eq_true h
    exact separated p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  have pair (p : Fin N) (l : Fin M) (edge : I p l) :
      goal (fun i => decide (i = point p ∨ i = line l)) = true := by
    apply decide_eq_true
    exact ⟨p,l,edge,decide_eq_true (Or.inl rfl),decide_eq_true (Or.inr rfl)⟩
  have cEval (x : Fin n → Bool) : circuitFun n C x = goal x := correct x
  have cMade : n ≤ C.output := by
    by_contra! h
    let i : Fin n := ⟨C.output,h⟩
    have t := cEval (one i)
    change (C.gates.foldl step (List.ofFn (one i))).getD i.val false = goal (one i) at t
    rw [keep _ _ _ (by simp), input, singleton] at t
    have on : one i i = true := decide_eq_true rfl
    exact Bool.noConfusion (on.symm.trans t)
  have cWithin : C.output < n + C.size := by
    by_contra! h
    obtain ⟨⟨p,l⟩, mem⟩ := nonempty
    let x : Fin n → Bool := fun i => decide (i = point p ∨ i = line l)
    have t := cEval x
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = goal x at t
    rw [List.getD_eq_default _ _ (by rw [runLen, List.length_ofFn]; exact h),
      pair p l ((memEdge p l).mp mem)] at t
    exact Bool.noConfusion t
  obtain ⟨D, dShape, dSize, dVal, dMade, dLast, dLive⟩ := prune n C shape cMade cWithin
  have dEval (x : Fin n → Bool) : circuitFun n D x = goal x :=
    (congrFun dVal x).trans (cEval x)
  let refs : Multiset ℕ := (D.gates.flatMap Gate.inputs : List ℕ)
  have countPos (w : ℕ) (read : ∃ g ∈ D.gates, w ∈ g.inputs) : 0 < refs.count w := by
    apply Multiset.count_pos.mpr
    change w ∈ D.gates.flatMap Gate.inputs
    exact List.mem_flatMap.mpr read
  have refsLen (gs : List Gate) (sized : ∀ g ∈ gs, g.inputs.length = 2) :
      (gs.flatMap Gate.inputs).length = 2*gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.flatMap_cons, List.length_append, sized g List.mem_cons_self,
        ih (fun h hh => sized h (List.mem_cons_of_mem _ hh)), List.length_cons]
      omega
  have refCard : refs.card = 2*D.size := refsLen D.gates dShape.2.2
  have notRead (gs : List Gate) (w : ℕ) (unused : ∀ g ∈ gs, w ∉ g.inputs)
      (u v : List Bool) (len : u.length = v.length)
      (same : ∀ k ≠ w, u.getD k false = v.getD k false) :
      ∀ k ≠ w, (gs.foldl step u).getD k false = (gs.foldl step v).getD k false := by
    induction gs generalizing u v with
    | nil => exact same
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have equal : g.inputs.map (fun k => u.getD k false) =
          g.inputs.map (fun k => v.getD k false) :=
        List.map_congr_left (fun k hk => same k (fun h => unused g List.mem_cons_self (h ▸ hk)))
      apply ih (fun h hh => unused h (List.mem_cons_of_mem _ hh))
      · simp only [step,List.length_append,List.length_singleton,len]
      · intro k hk
        dsimp only [step]
        rw [equal]
        by_cases low : k < u.length
        · rw [List.getD_append _ _ _ _ low, List.getD_append _ _ _ _ (by omega)]
          exact same k hk
        · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), len]
  have oneEndpoint (w v : Fin n) (yes : goal (fun k => decide (k = v ∨ k = w)) = true) :
      0 < refs.count w.val := by
    by_contra! no
    have unused : ∀ g ∈ D.gates, w.val ∉ g.inputs := fun g hg pin =>
      (not_lt_of_ge no) (countPos w.val ⟨g,hg,pin⟩)
    let x : Fin n → Bool := fun i => decide (i = v ∨ i = w)
    let y := one v
    have agrees : ∀ k ≠ w.val, (List.ofFn x).getD k false = (List.ofFn y).getD k false := by
      intro k neq
      by_cases kn : k < n
      · let j : Fin n := ⟨k,kn⟩
        have different : j ≠ w := fun eq => neq (congrArg Fin.val eq)
        change (List.ofFn x).getD j.val false = (List.ofFn y).getD j.val false
        rw [input, input]
        simp [x, y, one, different]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt kn),
            List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt kn)]
    have h := notRead D.gates w.val unused (List.ofFn x) (List.ofFn y) (by simp) agrees D.output (by omega)
    change circuitFun n D x = circuitFun n D y at h
    rw [dEval, dEval, singleton, yes] at h
    exact Bool.noConfusion h
  have active (w : ℕ) (hw : w ∈ S) : 0 < refs.count w := by
    rcases Finset.mem_union.mp hw with hp | hl
    · obtain ⟨⟨p,l⟩, hEdge, rfl⟩ := Finset.mem_image.mp hp
      exact oneEndpoint (point p) (line l) (by
        simpa only [or_comm] using pair p l ((memEdge p l).mp hEdge))
    · obtain ⟨⟨p,l⟩, hEdge, rfl⟩ := Finset.mem_image.mp hl
      exact oneEndpoint (line l) (point p) (pair p l ((memEdge p l).mp hEdge))
  have supportSmall (w : ℕ) (hw : w ∈ S) : w < n := by
    rcases Finset.mem_union.mp hw with hp | hl
    · obtain ⟨⟨p,l⟩, _, rfl⟩ := Finset.mem_image.mp hp
      dsimp only [n]
      omega
    · obtain ⟨⟨p,l⟩, _, rfl⟩ := Finset.mem_image.mp hl
      dsimp only [n]
      omega
  let internal := Finset.Ico n D.output
  have disjoint : Disjoint S internal := Finset.disjoint_left.mpr (fun w hw h =>
    (Nat.not_lt_of_ge (Finset.mem_Ico.mp h).1) (supportSmall w hw))
  have gatesCount : internal.card = D.size-1 := by
    change (Finset.Ico n D.output).card = _
    rw [Nat.card_Ico]
    omega
  have internalCount : D.size-1 ≤ ∑ i ∈ internal, refs.count i := by
    rw [← gatesCount]
    simpa using (Finset.sum_le_sum (s := internal)
      (f := fun _ => 1) (g := fun w => refs.count w)
      (fun w hw => countPos w (dLive w hw)))
  have sumCount : (∑ w ∈ S, refs.count w) + (∑ w ∈ internal, refs.count w) ≤ 2*D.size := by
    rw [← Finset.sum_union disjoint, ← refCard]
    calc
      _ ≤ ∑ w ∈ (S ∪ internal) ∪ refs.toFinset, refs.count w :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun _ _ _ => Nat.zero_le _)
      _ = refs.card := Multiset.sum_count_eq_card (fun w hw => Finset.mem_union_right _ (by simpa using hw))
  have ones : S.card ≤ ∑ w ∈ S, refs.count w := by
    simpa using (Finset.sum_le_sum (s := S) (f := fun _ => 1) (g := fun w => refs.count w) active)
  have cardBound : S.card ≤ D.size+1 := by omega
  have oneRead (sparse : D.size+1 < 2*S.card) : ∃ w ∈ S, refs.count w = 1 := by
    by_contra! no
    have two : (∑ _w ∈ S, 2) ≤ ∑ w ∈ S, refs.count w := by
      apply Finset.sum_le_sum
      intro w hw
      have pos := active w hw
      have diff := no w hw
      omega
    simp only [Finset.sum_const, Nat.nsmul_eq_mul] at two
    omega
  obtain ⟨T,tc,tb⟩ := liveBound N M I D linear dShape dEval dLast dLive cardBound oneRead
  exact ⟨T, tc, tb.trans (Nat.add_le_add_right dSize 1)⟩
