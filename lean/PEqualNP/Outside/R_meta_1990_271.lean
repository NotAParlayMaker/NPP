import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.GenericRejection PEqualNP.HeptadCover

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1990_271
    (normalize :
      let S := fun l : Fin 13 => Finset.univ.filter fun p : Fin 13 =>
        (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      ∀ (C : Circuit) (pins : List ℕ), Monotone2 C → pins.length ≤ 2 →
        (∀ X Y : Finset (Fin 13), GateOp.or.eval (pins.map fun i =>
          (C.wires (incidenceInput X Y)).getD i false) = incidenceFun S X Y) →
        ∃ D : Circuit, SingleLevel.IsSingleLevel 26 D ∧ ComputesIncidence S D ∧
          D.size ≤ C.size + 1)
    (extractCover :
      let S := fun l : Fin 13 => Finset.univ.filter fun p : Fin 13 =>
        (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      ∀ D : Circuit, SingleLevel.IsSingleLevel 26 D → ComputesIncidence S D →
        ∃ F : Finset (Finset (Fin 13) × Finset (Fin 13)),
          F.biUnion (fun r => r.1 ×ˢ r.2) = incidences S ∧
          (∑ r ∈ F, (r.1.card + r.2.card)) ≤ D.size + 1) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (63 : ℕ) ≤ x1.size := by
  intro C pins mono arity tests
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let S := fun l : Fin 13 => Finset.univ.filter fun p : Fin 13 => near p l
  let off := fun X : Finset (Fin 13) => Finset.univ.filter fun l : Fin 13 => ∀ p ∈ X, ¬near p l
  let bits (X Y : Finset (Fin 13)) (i : Fin 26) :=
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ X) else decide (Fin.ofNat 13 i.val ∈ Y)
  let read (X Y : Finset (Fin 13)) := GateOp.or.eval (pins.map fun i =>
    (C.wires (List.ofFn (bits X Y))).getD i false)
  change (∀ p l, near p l → read {p} {l} = true) ∧
    (∀ X : Finset (Fin 13), X.card ≤ 3 → read X (off X) = false ∧ read (off X) X = false) at tests
  -- Four points meet at least ten lines. There are sixteen incidences
  -- and each of the six pairs can account for at most one repeated line.
  have miss4 : ∀ q ∈ (Finset.univ : Finset (Fin 13)).powersetCard 4, (off q).card ≤ 3 := by
    let N (p : Fin 13) := Finset.univ.filter fun l : Fin 13 => near p l
    have degree : ∀ p, (N p).card = 4 := by
      dsimp only [N, near]
      decide +kernel
    have overlap : ∀ p p', p ≠ p' → ((N p) ∩ (N p')).card ≤ 1 := by
      dsimp only [N, near]
      decide +kernel
    have interBound (A B T : Finset (Fin 13)) :
        ((A ∪ B) ∩ T).card ≤ (A ∩ T).card + (B ∩ T).card := by
      rw [Finset.union_inter_distrib_right]
      exact Finset.card_union_le _ _
    intro q hq
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ :=
      Finset.card_eq_four.mp (Finset.mem_powersetCard.mp hq).2
    have size : 10 ≤ (N a ∪ N b ∪ N c ∪ N d).card := by
      have ab := Finset.card_union_add_card_inter (N a) (N b)
      have abc := Finset.card_union_add_card_inter (N a ∪ N b) (N c)
      have abcd := Finset.card_union_add_card_inter (N a ∪ N b ∪ N c) (N d)
      have acbc := interBound (N a) (N b) (N c)
      have adbd := interBound (N a) (N b) (N d)
      have bdcd := interBound (N a ∪ N b) (N c) (N d)
      have := overlap a b hab
      have := overlap a c hac
      have := overlap a d had
      have := overlap b c hbc
      have := overlap b d hbd
      have := overlap c d hcd
      simp only [degree] at ab abc abcd
      omega
    have comp : off {a, b, c, d} = (N a ∪ N b ∪ N c ∪ N d)ᶜ := by
      ext l
      simp [off, N]
    rw [comp, Finset.card_compl]
    simpa using (show 13 - (N a ∪ N b ∪ N c ∪ N d).card ≤ 3 by omega)
  have smallSide (X Y : Finset (Fin 13)) (empty : ∀ p ∈ X, ∀ l ∈ Y, ¬near p l) :
      X.card ≤ 3 ∨ Y.card ≤ 3 := by
    by_cases hx : X.card ≤ 3
    · exact Or.inl hx
    obtain ⟨q, hq, hcard⟩ := Finset.exists_subset_card_eq (s := X) (n := 4) (by omega)
    have sub : Y ⊆ off q := by
      intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => empty p (hq hp) l hl⟩
    exact Or.inr ((Finset.card_le_card sub).trans (miss4 q (Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hcard⟩)))
  have input_eq (X Y : Finset (Fin 13)) : List.ofFn (bits X Y) = incidenceInput X Y := by
    rfl
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have snoc (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false =
        if i < w.length then w.getD i false else if i = w.length then b else false := by
    by_cases h : i < w.length
    · rw [ite_eq_left h, List.getD_append _ _ _ _ h]
    rw [ite_eq_right h]
    by_cases he : i = w.length
    · subst i
      simp [List.getD_eq_getElem?_getD]
    · rw [ite_eq_right he, List.getD_eq_default _ _ (by simp; omega)]
  have wireMono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (x y : List Bool) (len : x.length = y.length)
      (xy : ∀ i, x.getD i false = true → y.getD i false = true) :
      ∀ i, (gs.foldl step x).getD i false = true → (gs.foldl step y).getD i false = true := by
    induction gs generalizing x y with
    | nil => exact xy
    | cons g gs ih =>
      apply ih (fun a ha => hg a (List.mem_cons_of_mem _ ha))
      · simp [step, len]
      · intro i
        simp only [step, snoc, ← len]
        split
        · exact xy i
        split
        · intro old
          rcases hg g (by simp) with h | h <;> rw [h] at old ⊢
          · change (g.inputs.map fun i => x.getD i false).all id = true at old
            change (g.inputs.map fun i => y.getD i false).all id = true
            simp at old ⊢
            intro j hj
            exact xy j (old j hj)
          · change (g.inputs.map fun i => x.getD i false).any id = true at old
            change (g.inputs.map fun i => y.getD i false).any id = true
            simp at old ⊢
            obtain ⟨j, hj, hbit⟩ := old
            exact ⟨j, hj, xy j hbit⟩
        · exact id
  have readMono {X Y X' Y' : Finset (Fin 13)} (hX : X ⊆ X') (hY : Y ⊆ Y') :
      read X Y = true → read X' Y' = true := by
    have inputLe : ∀ i, (List.ofFn (bits X Y)).getD i false = true →
        (List.ofFn (bits X' Y')).getD i false = true := by
      intro i
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      by_cases h : i < 26
      · simp only [h, dite_eq_left, Option.getD_some]
        by_cases hj : i < 13
        · simpa [bits, hj] using (show Fin.ofNat 13 i ∈ X → Fin.ofNat 13 i ∈ X' from fun hi => hX hi)
        · simpa [bits, hj] using (show Fin.ofNat 13 i ∈ Y → Fin.ofNat 13 i ∈ Y' from fun hi => hY hi)
      · simp [h]
    have hw := wireMono C.gates (fun g hg => (mono g hg).1) _ _ (by simp) inputLe
    change (pins.map fun i => (C.wires (List.ofFn (bits X Y))).getD i false).any id = true →
      (pins.map fun i => (C.wires (List.ofFn (bits X' Y'))).getD i false).any id = true
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hv⟩
    exact ⟨i, hi, hw i hv⟩
  have allInputs (X Y : Finset (Fin 13)) : read X Y = incidenceFun S X Y := by
    change read X Y = decide (∃ a ∈ X, ∃ b ∈ Y, a ∈ S b)
    by_cases h : ∃ p ∈ X, ∃ l ∈ Y, near p l
    · obtain ⟨p, hp, l, hl, inc⟩ := h
      have yes := readMono (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl)
        (tests.1 p l inc)
      have hit : p ∈ S l := Finset.mem_filter.mpr ⟨Finset.mem_univ _, inc⟩
      rw [decide_eq_true (show (∃ a ∈ X, ∃ b ∈ Y, a ∈ S b) from ⟨p, hp, l, hl, hit⟩)]
      exact yes
    · have empty : ∀ p ∈ X, ∀ l ∈ Y, ¬near p l := fun p hp l hl hit => h ⟨p, hp, l, hl, hit⟩
      have no : ¬ ∃ a ∈ X, ∃ b ∈ Y, a ∈ S b := by
        rintro ⟨a, ha, b, hb, hit⟩
        exact empty a ha b hb (Finset.mem_filter.mp hit).2
      simp only [decide_eq_false no]
      apply Bool.eq_false_iff.mpr
      intro yes
      rcases smallSide X Y empty with small | small
      · have sub : Y ⊆ off X := fun l hl => Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, fun p hp => empty p hp l hl⟩
        have bad := readMono (Finset.Subset.rfl (s := X)) sub yes
        rw [(tests.2 X small).1] at bad
        exact Bool.noConfusion bad
      · have sub : X ⊆ off Y := by
          intro p hp
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro l hl
          simpa only [near, Nat.add_comm] using empty p hp l hl
        have bad := readMono sub (Finset.Subset.rfl (s := Y)) yes
        rw [(tests.2 Y small).2] at bad
        exact Bool.noConfusion bad
  obtain ⟨D, singleLevel, computes, gates⟩ := normalize C pins mono arity (fun X Y => by
    unfold read at allInputs
    simpa only [input_eq] using allInputs X Y)
  obtain ⟨F, full, cost⟩ := extractCover D singleLevel computes
  change F.biUnion (fun r => r.1 ×ˢ r.2) = incidences S at full
  -- Each nonempty incidence rectangle is a star on at most four edges.
  -- A star with k edges uses k + 1 vertices, so four times its vertex
  -- count pays for five times its edge count, even when stars overlap.
  have edges : (incidences S).card = 52 := by
    dsimp only [S, near, incidences]
    decide +kernel
  have degree : ∀ l, (S l).card = 4 := by
    dsimp only [S, near]
    decide +kernel
  have overlap : ∀ l k, l ≠ k → ((S l) ∩ (S k)).card ≤ 1 := by
    dsimp only [S, near]
    decide +kernel
  have weight (r : Finset (Fin 13) × Finset (Fin 13)) (hr : r ∈ F) :
      5 * (r.1 ×ˢ r.2).card ≤ 4 * (r.1.card + r.2.card) := by
    have inside (p : Fin 13) (hp : p ∈ r.1) (l : Fin 13) (hl : l ∈ r.2) : p ∈ S l := by
      have e : (p,l) ∈ F.biUnion (fun t => t.1 ×ˢ t.2) :=
        Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_product.mpr ⟨hp, hl⟩⟩
      rw [full] at e
      exact (Finset.mem_filter.mp e).2
    rw [Finset.card_product]
    rcases r.1.eq_empty_or_nonempty with h | ⟨p, hp⟩
    · simp [h]
    rcases r.2.eq_empty_or_nonempty with h | ⟨l, hl⟩
    · simp [h]
    have pts : r.1.card ≤ 4 := (Finset.card_le_card (fun a ha => inside a ha l hl)).trans_eq (degree l)
    have lines : r.2.card ≤ 4 := by
      apply Nat.le_trans _ (Nat.le_of_eq (degree p))
      apply Finset.card_le_card
      intro b hb
      have mem := (Finset.mem_filter.mp (inside p hp b hb)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [near, Nat.add_comm] using mem⟩
    by_cases one : r.2.card ≤ 1
    · have eq : r.2.card = 1 := by have := Finset.card_pos.mpr ⟨l, hl⟩; omega
      rw [eq, Nat.mul_one]
      omega
    · obtain ⟨j,hj,k,hk,ne⟩ := Finset.one_lt_card.mp (by omega : 1 < r.2.card)
      have sub : r.1 ⊆ S j ∩ S k := fun a ha =>
        Finset.mem_inter.mpr ⟨inside a ha j hj, inside a ha k hk⟩
      have bound := (Finset.card_le_card sub).trans (overlap j k ne)
      have eq : r.1.card = 1 := by have := Finset.card_pos.mpr ⟨p, hp⟩; omega
      rw [eq, Nat.one_mul]
      omega
  have tot := Finset.sum_le_sum weight
  rw [← Finset.mul_sum, ← Finset.mul_sum] at tot
  have cover := Finset.card_biUnion_le (s := F) (t := fun r => r.1 ×ˢ r.2)
  rw [full, edges] at cover
  omega
