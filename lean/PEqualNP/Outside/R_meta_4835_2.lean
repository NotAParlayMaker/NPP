import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadTwo

-- A gate replacement can use the value of the restricted input and the equation of one earlier gate.
-- Three direct readers already produce replacements, so the graph hypothesis concerns only sparse readers.
theorem PEqualNP.Outside.R_meta_4835_2
  (structure_step :
    let G := PEqualNP.EdgeOwnership.edgeGraph 11
      [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
       (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ C : Circuit, IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 →
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card <
        2 * (Ustar G C).card →
      (∀ v : Fin 11, v.val < 4 →
        ((Finset.range C.size).filter (fun j => v.val ∈ (gateAt C j).inputs)).card ≤ 2) →
      ∃ v : Fin 11, v.val < 4 ∧ ∃ r : ℕ → ℕ, (∀ i < 11, r i = i) ∧
        (let gate := gateAt C
         let E := fun (y : ℕ → Bool) (j : ℕ) => (gate j).op.eval ((gate j).inputs.map (y ∘ r))
         ∀ j < C.size, r (11 + j) ≠ 11 + j →
           ∃ k ≤ j, ∀ y : ℕ → Bool, y v.val = false →
             (k < j → y (11 + k) = E y k) → E y j = y (r (11 + j))) ∧
        3 ≤ ((Finset.range C.size).filter (fun j => r (11 + j) < 11 + j)).card)
  (propagation :
    ∀ (C : Circuit) (v : Fin 11) (r : ℕ → ℕ), ReadsBack 11 C → (∀ i < 11, r i = i) →
      (let gate := gateAt C
       let E := fun (y : ℕ → Bool) (j : ℕ) => (gate j).op.eval ((gate j).inputs.map (y ∘ r))
       ∀ j < C.size, r (11 + j) ≠ 11 + j →
         ∃ k ≤ j, ∀ y : ℕ → Bool, y v.val = false →
           (k < j → y (11 + k) = E y k) → E y j = y (r (11 + j))) →
      ∀ j < C.size, ∀ x : Fin 11 → Bool, x v = false →
        wval C x (11 + j) = wval C x (r (11 + j))) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
      [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)),
       ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)),
       ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)),
       ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
    ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsLeastAO x1 x2 →
      PEqualNP.TopForm.TopForm x1 x2 →
      (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →
      x2.size ≤ (21 : ℕ) →
      (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card +
        (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
      ∃ (x8 : Fin (11 : ℕ)), ↑x8 < (4 : ℕ) ∧
        have x9 : ℕ → Prop := fun (x9 : ℕ) =>
          ∃ x10 < (11 : ℕ) + x9,
          ∀ (x11 : Fin (11 : ℕ) → Bool), x11 x8 = Bool.false →
            PEqualNP.ReadTwo.wval x2 x11 ((11 : ℕ) + x9) =
            PEqualNP.ReadTwo.wval x2 x11 x10;
        ∃ (x10 : ℕ) (x11 : ℕ) (x12 : ℕ), x10 < x11 ∧ x11 < x12 ∧ x12 < x2.size ∧ x9 x10 ∧ x9 x11 ∧ x9 x12 := by
  have direct (C : Circuit) (v : Fin 11) (hao : IsAO2 11 C)
      (hthree : 3 ≤ ((Finset.range C.size).filter (fun j => v.val ∈ (gateAt C j).inputs)).card) :
      ∃ r : ℕ → ℕ, (∀ i < 11, r i = i) ∧
        (let gate := gateAt C
         let E := fun (y : ℕ → Bool) (j : ℕ) => (gate j).op.eval ((gate j).inputs.map (y ∘ r))
         ∀ j < C.size, r (11 + j) ≠ 11 + j →
           ∃ k ≤ j, ∀ y : ℕ → Bool, y v.val = false →
             (k < j → y (11 + k) = E y k) → E y j = y (r (11 + j))) ∧
        3 ≤ ((Finset.range C.size).filter (fun j => r (11 + j) < 11 + j)).card := by
    classical
    let mate (j : ℕ) := if (gateAt C j).inputs.getD 0 v.val = v.val
      then (gateAt C j).inputs.getD 1 v.val else (gateAt C j).inputs.getD 0 v.val
    let step (w : ℕ) (prev : (u : ℕ) → u < w → ℕ) : ℕ :=
      if w < 11 then w else
      let j := w - 11
      if v.val ∈ (gateAt C j).inputs then
        if (gateAt C j).op = GateOp.and then v.val else
        if h : mate j < w then prev (mate j) h else w
      else w
    let rep := Nat.strongRec (motive := fun _ => ℕ) step
    have unfoldRep (w : ℕ) : rep w = step w (fun i _ => rep i) := Nat.strongRec_eq step w
    have input (i : ℕ) (hi : i < 11) : rep i = i := by
      rw [unfoldRep]
      simp [step, hi]
    have casesAt (j : ℕ) (hj : j < C.size) :
        (∃ a b, (gateAt C j).inputs = [a,b]) ∧
        ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
      have hlen : j < C.gates.length := hj
      have hg : gateAt C j = C.gates[j] := by
        change C.gates.getD j ⟨.or, []⟩ = C.gates[j]
        simp [List.getD_eq_getElem?_getD, hlen]
      have hmem : gateAt C j ∈ C.gates := hg ▸ List.getElem_mem hlen
      exact ⟨List.length_eq_two.mp (hao.2.2 _ hmem), hao.1 _ hmem⟩
    have earlier (j : ℕ) (hj : j < C.size) : mate j < 11 + j := by
      obtain ⟨a,b,h⟩ := (casesAt j hj).1
      apply hao.2.1 j hj
      unfold mate
      rw [h]
      split <;> simp
    have output (j : ℕ) (hj : j < C.size) : rep (11 + j) =
        if v.val ∈ (gateAt C j).inputs then
          if (gateAt C j).op = GateOp.and then v.val else rep (mate j)
        else 11 + j := by
      rw [unfoldRep]
      simp only [step, show ¬ 11 + j < 11 by omega, ite_false, Nat.add_sub_cancel_left,
        dite_eq_left (earlier j hj)]
    have le (w : ℕ) (hw : w < 11 + C.size) : rep w ≤ w := by
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        by_cases small : w < 11
        · rw [input w small]
        · obtain ⟨j, rfl⟩ : ∃ j, w = 11+j := ⟨w-11, by omega⟩
          have hj : j < C.size := by omega
          rw [output j hj]
          split
          · split
            · have := v.isLt; omega
            · exact le_trans (ih _ (earlier _ hj) (by have := earlier _ hj; omega)) (earlier _ hj).le
          · rfl
    refine ⟨rep, input, ?_, le_trans hthree (Finset.card_le_card ?_)⟩
    · intro gate E j hj hne
      have hd : v.val ∈ (gateAt C j).inputs := by
        by_contra h
        exact hne (by rw [output j hj, ite_eq_right h])
      refine ⟨j, le_rfl, ?_⟩
      intro y hy _
      obtain ⟨⟨a,b,h⟩,hop⟩ := casesAt j hj
      have hva : v.val = a ∨ v.val = b := by simpa [h] using hd
      have hv : y (rep v.val) = false := by rw [input _ v.isLt, hy]
      change (gateAt C j).op.eval ((gateAt C j).inputs.map (y ∘ rep)) = _
      rw [output j hj, ite_eq_left hd]
      have evalAnd (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
      have evalOr (bs : List Bool) : GateOp.or.eval bs = bs.any id := rfl
      rcases hop with hop | hop
      · rw [ite_eq_left hop, hop, h]
        rcases hva with ha | hb
        · subst a; simp [evalAnd, Function.comp_def, hv, hy]
        · subst b; simp [evalAnd, Function.comp_def, hv, hy]
      · have hn : (gateAt C j).op ≠ GateOp.and := by rw [hop]; intro he; cases he
        rw [ite_eq_right hn, hop, h]
        unfold mate
        rw [h]
        rcases hva with ha | hb
        · subst a; simp [evalOr, Function.comp_def, hv]
        · subst b; by_cases ha : a = v.val
          · subst a; simp [evalOr, Function.comp_def, hv]
          · simp [evalOr, Function.comp_def, hv, ha]
    · intro j hj
      obtain ⟨hsize, hd⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨hsize, ?_⟩
      have hj := Finset.mem_range.mp hsize
      rw [output j hj, ite_eq_left hd]
      split
      · have := v.isLt; omega
      · have hm := earlier j hj
        exact lt_of_le_of_lt (le _ (by omega)) hm
  intro G C hleast htop hj hsize hcount
  have cert :
      ∃ v : Fin 11, v.val < 4 ∧ ∃ r : ℕ → ℕ, (∀ i < 11, r i = i) ∧
        (let gate := gateAt C
         let E := fun (y : ℕ → Bool) (j : ℕ) => (gate j).op.eval ((gate j).inputs.map (y ∘ r))
         ∀ j < C.size, r (11 + j) ≠ 11 + j →
           ∃ k ≤ j, ∀ y : ℕ → Bool, y v.val = false →
             (k < j → y (11 + k) = E y k) → E y j = y (r (11 + j))) ∧
        3 ≤ ((Finset.range C.size).filter (fun j => r (11 + j) < 11 + j)).card := by
    classical
    by_cases hs : ∀ v : Fin 11, v.val < 4 →
        ((Finset.range C.size).filter (fun j => v.val ∈ (gateAt C j).inputs)).card ≤ 2
    · exact structure_step C hleast htop hj hsize hcount hs
    · push Not at hs
      obtain ⟨v, hv, hread⟩ := hs
      exact ⟨v, hv, direct C v hleast.1 (by omega)⟩
  obtain ⟨v, hv, r, hinput, hlocal, hcard⟩ := cert
  let S := (Finset.range C.size).filter (fun j => r (11 + j) < 11 + j)
  change 3 ≤ S.card at hcard
  let f := S.orderEmbOfFin rfl
  let a : Fin S.card := ⟨0, by omega⟩
  let b : Fin S.card := ⟨1, by omega⟩
  let c : Fin S.card := ⟨2, by omega⟩
  have hab : f a < f b := f.strictMono (show a < b from Nat.lt_succ_self _)
  have hbc : f b < f c := f.strictMono (show b < c from Nat.lt_succ_self _)
  have data (i : Fin S.card) : f i < C.size ∧ r (11 + f i) < 11 + f i := by
    have hi : f i ∈ S := S.orderEmbOfFin_mem rfl i
    exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  have earlier (i : Fin S.card) :
      ∃ w < 11 + f i, ∀ x : Fin 11 → Bool, x v = false →
        wval C x (11 + f i) = wval C x w :=
    ⟨r (11 + f i), (data i).2, propagation C v r hleast.1.2.1 hinput hlocal (f i) (data i).1⟩
  exact ⟨v, hv, f a, f b, f c, hab, hbc, (data c).1, earlier a, earlier b, earlier c⟩
