import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3241_739
    (countOr : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit),
      (∀ p q l m, p ≠ q → l ≠ m → ¬ (I p l ∧ I p m ∧ I q l ∧ I q m)) →
      PEqualNP.TopForm.IsAO2 (P+L) C →
      (∀ x : Fin (P+L) → Bool, circuitFun (P+L) C x =
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      (PEqualNP.ReadTwo.incid I).card ≤
        PEqualNP.ReadTwo.nOr C + 1)
    (coverAnd : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit),
      (∀ p q l m, p ≠ q → l ≠ m → ¬ (I p l ∧ I p m ∧ I q l ∧ I q m)) →
      PEqualNP.TopForm.IsAO2 (P+L) C →
      (∀ x : Fin (P+L) → Bool, circuitFun (P+L) C x =
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      ∃ S : Finset (Fin (P+L)),
        (∀ p l, I p l → Fin.castAdd L p ∈ S ∨ Fin.natAdd P l ∈ S) ∧
        S.card ≤ PEqualNP.ReadTwo.nAnd C) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   let x6 : ℕ := x1 + x2;   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬(x3 x7 x9 ∧ x3 x7 x10 ∧ x3 x8 x9 ∧ x3 x8 x10)) → PEqualNP.TopForm.IsAO2 x6 x5 → (∀ (x9 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → ∃ (x10 : List (ℕ × List ℕ)), (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < x6) ∨ x1 ≤ x11.1 ∧ x11.1 < x6 ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧ (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧ (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - (1 : ℕ) ≤ x5.size := by
  intro P L I _ C
  dsimp only
  intro free ao correct
  have edgeBound := countOr P L I C free ao correct
  obtain ⟨S, cover, coverBound⟩ := coverAnd P L I C free ao correct
  classical
  let E : Finset (Fin P × Fin L) := Finset.univ.filter (fun e => I e.1 e.2)
  let owner (e : Fin P × Fin L) := if Fin.castAdd L e.1 ∈ S then
    Fin.castAdd L e.1 else Fin.natAdd P e.2
  have owns (e : Fin P × Fin L) :
      owner e = Fin.castAdd L e.1 ∨ owner e = Fin.natAdd P e.2 := by
    by_cases h : Fin.castAdd L e.1 ∈ S
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (ite_eq_right h)
  have ownerMem {e : Fin P × Fin L} (h : e ∈ E) : owner e ∈ S := by
    have he : I e.1 e.2 := (Finset.mem_filter.mp h).2
    rcases cover e.1 e.2 he with h₁ | h₂
    · simpa only [owner, ite_eq_left h₁] using h₁
    · by_cases hp : Fin.castAdd L e.1 ∈ S
      · simpa only [owner, ite_eq_left hp] using hp
      · simpa only [owner, ite_eq_right hp] using h₂
  let fiber (v : Fin (P+L)) := E.filter (fun e => owner e = v)
  let active := S.filter (fun v => (fiber v).Nonempty)
  let leaf (v : Fin (P+L)) (e : Fin P × Fin L) :=
    if v.val < P then P + e.2.val else e.1.val
  let star (v : Fin (P+L)) := (v.val, (fiber v).toList.map (leaf v))
  let stars := active.toList.map star
  have fiberMem {e : Fin P × Fin L} {v : Fin (P+L)} (he : e ∈ E) (hv : owner e = v) :
      e ∈ fiber v := Finset.mem_filter.mpr ⟨he, hv⟩
  have activeMem {e : Fin P × Fin L} (he : e ∈ E) : owner e ∈ active :=
    Finset.mem_filter.mpr ⟨ownerMem he, ⟨e, fiberMem he rfl⟩⟩
  have leafLeft (v : Fin (P+L)) (e : Fin P × Fin L) (hv : v.val < P) :
      leaf v e = P + e.2.val := ite_eq_left hv
  have leafRight (v : Fin (P+L)) (e : Fin P × Fin L) (hv : P ≤ v.val) :
      leaf v e = e.1.val := ite_eq_right (Nat.not_lt.mpr hv)
  refine ⟨stars, ?_, ?_, ?_⟩
  · intro tx htx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp htx
    have hf := (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2
    have hn : (star v).2 ≠ [] := by
      obtain ⟨e, he⟩ := hf
      have hm : leaf v e ∈ (star v).2 :=
        List.mem_map.mpr ⟨e, Finset.mem_toList.mpr he, rfl⟩
      intro h
      rw [h] at hm
      exact List.not_mem_nil hm
    refine ⟨hn, ?_⟩
    by_cases left : v.val < P
    · refine Or.inl ⟨left, ?_⟩
      intro k hk
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hk
      have hlt := e.2.isLt
      rw [leafLeft v e left]
      omega
    · have right := Nat.le_of_not_gt left
      refine Or.inr ⟨right, v.isLt, ?_⟩
      intro k hk
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hk
      rw [leafRight v e right]
      exact e.1.isLt
  · intro p l
    constructor
    · intro he
      have he' : (p,l) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
      let v := owner (p,l)
      refine ⟨star v, List.mem_map.mpr ⟨v, Finset.mem_toList.mpr (activeMem he'), rfl⟩, ?_⟩
      have hl : leaf v (p,l) ∈ (star v).2 :=
        List.mem_map.mpr ⟨(p,l), Finset.mem_toList.mpr (fiberMem he' rfl), rfl⟩
      rcases owns (p,l) with h | h
      · have hv : v.val = p.val := congrArg Fin.val h
        have hlt : v.val < P := by rw [hv]; exact p.isLt
        rw [leafLeft v (p,l) hlt] at hl
        exact Or.inl ⟨hv, hl⟩
      · have hv : v.val = P + l.val := congrArg Fin.val h
        have hge : P ≤ v.val := by omega
        rw [leafRight v (p,l) hge] at hl
        exact Or.inr ⟨hv, hl⟩
    · rintro ⟨tx, htx, h⟩
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp htx
      rcases h with ⟨hp, hl⟩ | ⟨hl, hp⟩
      · change v.val = p.val at hp
        have hlt : v.val < P := by rw [hp]; exact p.isLt
        obtain ⟨e, hem, heq⟩ := List.mem_map.mp hl
        obtain ⟨he, hv⟩ := Finset.mem_filter.mp (Finset.mem_toList.mp hem)
        rw [leafLeft v e hlt] at heq
        have h₁ : e.1 = p := by
          apply Fin.ext
          rcases owns e with h | h
          · exact (congrArg Fin.val (h.symm.trans hv)).trans hp
          · have hb : P + e.2.val = v.val := congrArg Fin.val (h.symm.trans hv)
            omega
        have h₂ : e.2 = l := Fin.ext (by omega)
        have hi : I e.1 e.2 := (Finset.mem_filter.mp he).2
        rwa [h₁, h₂] at hi
      · change v.val = P + l.val at hl
        have hge : P ≤ v.val := by omega
        obtain ⟨e, hem, heq⟩ := List.mem_map.mp hp
        obtain ⟨he, hv⟩ := Finset.mem_filter.mp (Finset.mem_toList.mp hem)
        rw [leafRight v e hge] at heq
        have h₁ : e.1 = p := Fin.ext heq
        have h₂ : e.2 = l := by
          apply Fin.ext
          rcases owns e with h | h
          · have hb : e.1.val = v.val := congrArg Fin.val (h.symm.trans hv)
            have hlt := e.1.isLt
            omega
          · have hb : P + e.2.val = v.val := congrArg Fin.val (h.symm.trans hv)
            omega
        have hi : I e.1 e.2 := (Finset.mem_filter.mp he).2
        rwa [h₁, h₂] at hi
  · have length : stars.length = active.card := by simp only [stars, List.length_map, Finset.length_toList]
    have activeLe : active.card ≤ S.card := Finset.card_filter_le _ _
    have sumLengths :
        (stars.map (fun tx => tx.2.length)).sum = E.card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := owner) (t := active) (fun e he => activeMem he)]
      change _ = ∑ v ∈ active, (fiber v).card
      simp only [stars, List.map_map]
      have sizes : active.toList.map ((fun tx : Nat × List Nat => tx.2.length) ∘ star) =
          active.toList.map (fun v => (fiber v).card) := by
        apply List.map_congr_left
        intro v _
        change ((fiber v).toList.map (leaf v)).length = (fiber v).card
        rw [List.length_map, Finset.length_toList]
      rw [sizes]
      simpa only [Finset.toList_toFinset] using (List.sum_toFinset (fun v => (fiber v).card) active.nodup_toList).symm
    let isOr (g : Gate) := @decide (g.op = .or) (NestedCover.gateOpDecEq _ _)
    let isAnd (g : Gate) := @decide (g.op = .and) (NestedCover.gateOpDecEq _ _)
    have complement : C.gates.countP isAnd = C.gates.countP (fun g => !isOr g) := by
      apply List.countP_congr
      intro g hg
      change @decide (g.op = .and) (NestedCover.gateOpDecEq _ _) = true ↔
        (! @decide (g.op = .or) (NestedCover.gateOpDecEq _ _)) = true
      rcases ao.1 g hg with h | h <;> rw [h] <;> decide
    have gates : C.size = PEqualNP.ReadTwo.nOr C + PEqualNP.ReadTwo.nAnd C := by
      change C.size = (C.gates.filter isOr).length + (C.gates.filter isAnd).length
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, complement]
      exact List.length_eq_countP_add_countP isOr
    have incidences : PEqualNP.ReadTwo.incid I = E := by
      ext e
      simp only [PEqualNP.ReadTwo.incid,E,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [incidences] at edgeBound
    rw [length, sumLengths]
    omega
