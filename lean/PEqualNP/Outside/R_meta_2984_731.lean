import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

-- A wire labels a rectangle of positive and negative rows it separates.
-- Each gate covers its rectangle by the two operand rectangles.
-- At order 200, each input has cells for which it is the only possible answer.
-- The first gate cannot replace two of these inputs because mixing their rows gives
-- a cell outside both operands. Tracing the remaining gates back proves the bound.
theorem PEqualNP.Outside.R_meta_2984_731
    (wireRectangles : ∀ (n N : ℕ) (C : Circuit)
        (pos : Fin N × Fin N → List Bool) (neg : Finset (Fin N) → List Bool),
      PEqualNP.TopForm.IsAO2 n C → (∀ e, (pos e).length = n) → (∀ Y, (neg Y).length = n) →
      ∃ (U : ℕ → Set (Fin N × Fin N)) (V : ℕ → Set (Finset (Fin N))),
        let R := fun i => (U i) ×ˢ (V i)
        (∀ i < n, ∀ z ∈ R i, (pos z.1).getD i false = true ∧ (neg z.2).getD i false = false) ∧
        (∀ j < C.size, ∃ a < n+j, ∃ b < n+j, R (n+j) ⊆ R a ∪ R b) ∧
        ∀ e Y, C.eval (pos e) = true → C.eval (neg Y) = false → (e,Y) ∈ R C.output)
    (rectangleBound : ∀ (q N s : ℕ) (S : Fin N → Finset (Fin N)),
      201 ≤ q → N = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p t, p ≠ t → ∃! l, p ∈ S l ∧ t ∈ S l) →
      ∀ (U : ℕ → Set (Fin N × Fin N)) (V : ℕ → Set (Finset (Fin N))),
        let R := fun i => (U i) ×ˢ (V i)
        (∀ p : Fin N, ∀ z ∈ R p.val, z.1.1 = p ∧ ∃ l ∈ z.2, p ∈ S l) →
        (∀ l : Fin N, ∀ z ∈ R (N+l.val), z.1.2 = l ∧ l ∉ z.2) →
        (∀ j < s, ∃ a < N+N+j, ∃ b < N+N+j, R (N+N+j) ⊆ R a ∪ R b) →
        (∃ o < N+N+s, ∀ l, ∀ p ∈ S l, ∀ Y : Finset (Fin N), Y.card ≤ q → ((p,l),Y) ∈ R o) →
        N*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N S C hq hN cards uniqueLines gates out pairs reject
  let pos := fun e : Fin N × Fin N => incidenceInput {e.1} {e.2}
  let neg := fun Y : Finset (Fin N) => incidenceInput (zeroSet S Y) Y
  have len (X Y : Finset (Fin N)) : (incidenceInput X Y).length = N+N := by
    change (List.ofFn (fun i : Fin N => decide (i ∈ X)) ++ List.ofFn (fun i : Fin N => decide (i ∈ Y))).length = _
    simp
  obtain ⟨U,V,leaves,forks,root⟩ := wireRectangles (N+N) N C pos neg gates
    (fun _ => len _ _) (fun _ => len _ _)
  have leftBit (X Y : Finset (Fin N)) (p : Fin N) :
      (incidenceInput X Y).getD p.val false = decide (p ∈ X) := by
    change (List.ofFn (fun i : Fin N => decide (i ∈ X)) ++ List.ofFn (fun i : Fin N => decide (i ∈ Y))).getD p.val false = _
    rw [List.getD_append _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  have rightBit (X Y : Finset (Fin N)) (l : Fin N) :
      (incidenceInput X Y).getD (N+l.val) false = decide (l ∈ Y) := by
    change (List.ofFn (fun i : Fin N => decide (i ∈ X)) ++ List.ofFn (fun i : Fin N => decide (i ∈ Y))).getD (N+l.val) false = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  have useBound (hleft : ∀ p : Fin N, ∀ z ∈ (U p.val ×ˢ V p.val), z.1.1 = p ∧ ∃ l ∈ z.2, p ∈ S l)
      (hright : ∀ l : Fin N, ∀ z ∈ (U (N+l.val) ×ˢ V (N+l.val)), z.1.2 = l ∧ l ∉ z.2)
      (hout : ∃ o < N+N+C.size, ∀ l, ∀ p ∈ S l, ∀ Y : Finset (Fin N), Y.card ≤ q →
        ((p,l),Y) ∈ U o ×ˢ V o) : N*q ≤ 100*C.size := by
    by_cases hlarge : 201 ≤ q
    · exact rectangleBound q N C.size S hlarge hN cards uniqueLines U V hleft hright forks hout
    have order : q = 200 := by omega
    have enough : q+1 < N := by rw [hN, order]; decide
    -- Trace a set of wires back through k gates. Replacing one wire by
    -- its operands adds at most one wire to the set.
    have unwind {X : Type} (R : ℕ → Set X) (m k : ℕ)
        (h : ∀ j < k, ∃ a < m+j, ∃ b < m+j, R (m+j) ⊆ R a ∪ R b)
        (T : Finset ℕ) (ht : ∀ x ∈ T, x < m+k) :
        ∃ W : Finset ℕ, (∀ x ∈ W, x < m) ∧ W.card ≤ T.card+k ∧
          ∀ i ∈ T, ∀ z ∈ R i, ∃ u ∈ W, z ∈ R u := by
      induction k generalizing T with
      | zero => exact ⟨T, ht, le_rfl, fun i hi z hz => ⟨i,hi,hz⟩⟩
      | succ k ih =>
        obtain ⟨a,ha,b,hb,hab⟩ := h k (by omega)
        have prev := ih (fun j hj => h j (by omega))
        by_cases he : m+k ∈ T
        · let D := insert a (insert b (T.erase (m+k)))
          have smaller (x : ℕ) (hx : x ∈ D) : x < m+k := by
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact ha
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hb
            have := ht x (Finset.mem_erase.mp hx).2
            have := (Finset.mem_erase.mp hx).1
            omega
          obtain ⟨W,hw,hn,hcover⟩ := prev D smaller
          refine ⟨W,hw,?_,?_⟩
          · have h₁ := Finset.card_insert_le a (insert b (T.erase (m+k)))
            have h₂ := Finset.card_insert_le b (T.erase (m+k))
            have h₃ := Finset.card_erase_add_one he
            dsimp [D] at hn
            omega
          · intro i hi z hz
            by_cases e : i = m+k
            · subst i
              rcases hab hz with h | h
              · exact hcover a (by simp [D]) _ h
              · exact hcover b (by simp [D]) _ h
            · exact hcover i (by simp [D, e,hi]) _ hz
        · obtain ⟨W,hw,hn,hcover⟩ := prev T (by
            intro i hi
            have := ht i hi
            have : i ≠ m+k := fun e => he (e ▸ hi)
            omega)
          exact ⟨W,hw,by omega,hcover⟩

    -- Stop before the first gate. Every missing input must then have all
    -- its private cells in the first gate, which cannot happen for two inputs.
    have two_leaves {X : Type} (m s : ℕ) (R : ℕ → Set X) (o : ℕ) (ho : o < m+s)
        (h : ∀ j < s, ∃ a < m+j, ∃ b < m+j, R (m+j) ⊆ R a ∪ R b)
        (A : ℕ → Set X)
        (privateCells : ∀ i < m, (A i).Nonempty ∧ A i ⊆ R o ∧
          ∀ j < m, i ≠ j → Disjoint (A i) (R j))
        (obstruction : ∀ i < m, ∀ j < m, i ≠ j → R m ⊆ R i ∪ R j →
          ¬ (A i ⊆ R m ∧ A j ⊆ R m))
        (hm : 2 ≤ m) : m ≤ s := by
      cases s with
      | zero =>
        have diff : ∃ i < m, i ≠ o := by
          by_cases e : o = 0
          · exact ⟨1,by omega,by omega⟩
          · exact ⟨0,by omega,Ne.symm e⟩
        obtain ⟨i,hi,ne⟩ := diff
        obtain ⟨⟨x,hx⟩,incl,disj⟩ := privateCells i hi
        exact False.elim (Set.disjoint_left.mp (disj o ho ne) hx (incl hx))
      | succ k =>
        obtain ⟨a,ha,b,hb,hsub⟩ := h 0 (by omega)
        simp only [Nat.add_zero] at ha hb hsub
        obtain ⟨W,hw,hn,hcover⟩ := unwind R (m+1) k (by
          intro j hj
          simpa only [Nat.add_right_comm m 1 j, Nat.add_assoc] using h (j+1) (by omega))
          {o} (by simpa using (show o < m+1+k by omega))
        have needed (i : ℕ) (hi : i < m) (hnW : i ∉ W) :
            A i ⊆ R m ∧ m ∈ W ∧ (i = a ∨ i = b) := by
          obtain ⟨⟨z,hz⟩,ho',hd⟩ := privateCells i hi
          have all (x : X) (hx : x ∈ A i) : x ∈ R m ∧ m ∈ W := by
            obtain ⟨u,hu,hu'⟩ := hcover o (by simp) x (ho' hx)
            have lt := hw u hu
            by_cases e : u = m
            · exact e ▸ ⟨hu',hu⟩
            · have ine : i ≠ u := fun ie => hnW (ie ▸ hu)
              exact False.elim (Set.disjoint_left.mp (hd _ (by omega) ine) hx hu')
          refine ⟨fun _ hx => (all _ hx).1, (all z hz).2, ?_⟩
          rcases hsub (all z hz).1 with hza | hzb
          · exact Or.inl (by by_contra ne; exact Set.disjoint_left.mp (hd _ ha ne) hz hza)
          · exact Or.inr (by by_contra ne; exact Set.disjoint_left.mp (hd _ hb ne) hz hzb)
        have small : ((Finset.range m) \ W).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro i hi j hj
          rcases Finset.mem_sdiff.mp hi with ⟨hi,hn₁⟩
          rcases Finset.mem_sdiff.mp hj with ⟨hj,hn₂⟩
          obtain ⟨hiR,_,eqi⟩ := needed i (Finset.mem_range.mp hi) hn₁
          obtain ⟨hjR,_,eqj⟩ := needed j (Finset.mem_range.mp hj) hn₂
          by_contra ne
          rcases eqi with rfl | rfl <;> rcases eqj with rfl | rfl
          · exact ne rfl
          · exact obstruction _ ha _ hb ne hsub ⟨hiR,hjR⟩
          · exact obstruction _ ha _ hb (Ne.symm ne) hsub ⟨hjR,hiR⟩
          · exact ne rfl
        have budget : W.card ≤ 1+k := by simpa using hn
        by_cases subset : Finset.range m ⊆ W
        · have hcard := Finset.card_le_card subset
          simp at hcard
          omega
        · obtain ⟨i,hi,missing⟩ := Finset.not_subset.mp subset
          have present := (needed i (Finset.mem_range.mp hi) missing).2.1
          have sub : Finset.range m ⊆ (Finset.range m \ W) ∪ W.erase m := by
            intro j hj
            by_cases jW : j ∈ W
            · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by have := Finset.mem_range.mp hj; omega,jW⟩)
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hj,jW⟩)
          have c := Finset.card_le_card sub
          have u := Finset.card_union_le (Finset.range m \ W) (W.erase m)
          have e := Finset.card_erase_add_one present
          rw [Finset.card_range] at c
          omega

    let Label (N : ℕ) := Fin N ⊕ Fin N
    let Cell (N : ℕ) := (Fin N × Fin N) × Finset (Fin N)
    let OK {N : ℕ} (S : Fin N → Finset (Fin N)) (i : Label N) (z : Cell N) : Prop :=
      Sum.elim (fun p => z.1.1 = p ∧ ∃ k ∈ z.2, p ∈ S k)
        (fun l => z.1.2 = l ∧ l ∉ z.2) i
    -- A private cell is an incidence and a small line set with just one valid
    -- answer among the input labels. The root must contain every such cell.
    let Private {N : ℕ} (q : ℕ) (S : Fin N → Finset (Fin N)) (i : Label N) : Set (Cell N) :=
      {z | z.1.1 ∈ S z.1.2 ∧ z.2.card ≤ q ∧ ∀ t, OK S t z → i = t}

    have pointCell {N : ℕ} (S : Fin N → Finset (Fin N)) (q : ℕ) (hq : 1 ≤ q)
        (p l : Fin N) (h : p ∈ S l) : ((p,l),{l}) ∈ Private q S (.inl p) := by
      refine ⟨h,by simpa,?_⟩
      intro t ht
      cases t with
      | inl t => exact congrArg Sum.inl ht.1
      | inr t => obtain ⟨rfl,hh⟩ := ht; simp at hh
    have lineCell {N : ℕ} (S : Fin N → Finset (Fin N)) (q : ℕ) (p l : Fin N)
        (h : p ∈ S l) (Y : Finset (Fin N)) (hy : Y.card ≤ q)
        (away : ∀ k ∈ Y, p ∉ S k) : ((p,l),Y) ∈ Private q S (.inr l) := by
      refine ⟨h,hy,?_⟩
      intro t ht
      cases t with
      | inr t => exact congrArg Sum.inr ht.1
      | inl t =>
        obtain ⟨e,k,hk,ht⟩ := ht
        have e' : p = t := e
        exact (away k hk (e' ▸ ht)).elim

    -- Cross the incidence of one private cell with the line set of another.
    -- A rectangle containing both cells also contains this cross.
    let Bad {N : ℕ} (q : ℕ) (S : Fin N → Finset (Fin N)) (i j : Label N) : Prop :=
      ∃ z ∈ Private q S i, ∃ w ∈ Private q S j,
        ¬ OK S i (z.1,w.2) ∧ ¬ OK S j (z.1,w.2)

    -- A point can use a singleton incident line. A line can use an empty
    -- line set, or a singleton line that misses its chosen point.
    have geometry (q N : ℕ) (S : Fin N → Finset (Fin N)) (hq : 2 ≤ q)
        (total : q+1 < N) (sizes : ∀ l, (S l).card = q+1)
        (lines : ∀ p t, p ≠ t → ∃! l, p ∈ S l ∧ t ∈ S l) :
        (∀ i, (Private q S i).Nonempty) ∧
          ∀ i j, i ≠ j → Bad q S i j ∨ Bad q S j i := by
      classical
      have outside (l : Fin N) : ∃ t, t ∉ S l := by
        by_contra! h
        have all : S l = Finset.univ := Finset.eq_univ_of_forall h
        have c := sizes l
        rw [all, Finset.card_univ, Fintype.card_fin] at c
        omega
      have diff (p : Fin N) : ∃ t : Fin N, t ≠ p := by
        have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr (by omega)
        exact exists_ne p
      have through (p : Fin N) : ∃ l, p ∈ S l := by
        obtain ⟨t,ne⟩ := diff p
        obtain ⟨l,h,_⟩ := lines p t (Ne.symm ne)
        exact ⟨l,h.1⟩
      have other (p l : Fin N) : ∃ k, k ≠ l ∧ p ∈ S k := by
        by_cases hp : p ∈ S l
        · obtain ⟨t,ht⟩ := outside l
          have ne : p ≠ t := fun e => ht (e ▸ hp)
          obtain ⟨k,h,_⟩ := lines p t ne
          exact ⟨k,fun e => ht (e ▸ h.2),h.1⟩
        · obtain ⟨k,h⟩ := through p
          exact ⟨k,fun e => hp (e ▸ h),h⟩
      have on (l : Fin N) : (S l).Nonempty := Finset.card_pos.mp (by rw [sizes]; omega)
      have mixed (p l : Fin N) : Bad q S (.inl p) (.inr l) := by
        obtain ⟨k,ne,hp⟩ := other p l
        obtain ⟨t,ht⟩ := on l
        refine ⟨_,pointCell S q (by omega) p k hp,_,lineCell S q t l ht ∅ (by simp) (by simp),?_,?_⟩
        · simp [OK]
        · simpa [OK] using ne
      constructor
      · intro i
        cases i with
        | inl p =>
          obtain ⟨l,hl⟩ := through p
          exact ⟨_,pointCell S q (by omega) p l hl⟩
        | inr l =>
          obtain ⟨p,hp⟩ := on l
          exact ⟨_,lineCell S q p l hp ∅ (by simp) (by simp)⟩
      · intro i j ne
        cases i with
        | inl p =>
          cases j with
          | inr l => exact .inl (mixed p l)
          | inl t =>
            have pt : p ≠ t := fun e => ne (congrArg Sum.inl e)
            obtain ⟨l,hl,unique⟩ := lines p t pt
            obtain ⟨k,kl,tk⟩ := other t l
            have pk : p ∉ S k := fun h => kl (unique _ ⟨h,tk⟩)
            left
            exact ⟨_,pointCell S q (by omega) p l hl.1,_,pointCell S q (by omega) t k tk,
              by simpa [OK] using pk,by simp [OK,pt]⟩
        | inr l =>
          cases j with
          | inl p => exact .inr (mixed p l)
          | inr k =>
            have lk : l ≠ k := fun e => ne (congrArg Sum.inr e)
            obtain ⟨p,hp⟩ := on l
            have notsub : ¬ S k ⊆ S l := by
              obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (show 1 < (S k).card by rw [sizes]; omega)
              obtain ⟨u,_,unique⟩ := lines a b ab
              intro sub
              exact lk ((unique _ ⟨sub ha,sub hb⟩).trans (unique _ ⟨ha,hb⟩).symm)
            obtain ⟨t,tk,tl⟩ := Finset.not_subset.mp notsub
            left
            refine ⟨_,lineCell S q p l hp ∅ (by simp) (by simp),_,
              lineCell S q t k tk {l} (by simpa using (show 1 ≤ q by omega)) (by simpa using tl),?_,?_⟩
            · simp [OK]
            · simp [OK,lk]

    -- The geometric witnesses give the obstruction for the first gate.
    have linear (q N s : ℕ) (S : Fin N → Finset (Fin N))
        (hq : 2 ≤ q) (total : q+1 < N) (sizes : ∀ l, (S l).card = q+1)
        (lines : ∀ p t, p ≠ t → ∃! l, p ∈ S l ∧ t ∈ S l)
        (U : ℕ → Set (Fin N × Fin N)) (V : ℕ → Set (Finset (Fin N))) :
        let R := fun i => U i ×ˢ V i
        (∀ p : Fin N, ∀ z ∈ R p.val, z.1.1 = p ∧ ∃ l ∈ z.2, p ∈ S l) →
        (∀ l : Fin N, ∀ z ∈ R (N+l.val), z.1.2 = l ∧ l ∉ z.2) →
        (∀ j < s, ∃ a < N+N+j, ∃ b < N+N+j, R (N+N+j) ⊆ R a ∪ R b) →
        (∃ o < N+N+s, ∀ l, ∀ p ∈ S l, ∀ Y : Finset (Fin N), Y.card ≤ q → ((p,l),Y) ∈ R o) →
        N+N ≤ s := by
      dsimp only
      intro hpoint hline hfork output
      obtain ⟨o,ho,hroot⟩ := output
      let R := fun i => U i ×ˢ V i
      have : NeZero N := ⟨by omega⟩
      let lbl (i : ℕ) : Label N := if i < N then .inl (Fin.ofNat N i) else .inr (Fin.ofNat N (i-N))
      let idx : Label N → ℕ := Sum.elim Fin.val (fun l => N+l.val)
      have inv (i : ℕ) (hi : i < N+N) : idx (lbl i) = i := by
        by_cases e : i < N
        · simp [idx,lbl,e,Nat.mod_eq_of_lt e]
        · have h' : i-N < N := by omega
          simp [idx,lbl,e,Nat.mod_eq_of_lt h']; omega
      have leaves (i : ℕ) (hi : i < N+N) : R i ⊆ {z | OK S (lbl i) z} := by
        intro z hz
        by_cases e : i < N
        · have hp := hpoint (Fin.ofNat N i) z
          simp only [Fin.val_ofNat,Nat.mod_eq_of_lt e] at hp
          simpa [lbl,e,OK] using hp hz
        · have h' : i-N < N := by omega
          have e' : N+(i-N) = i := by omega
          have hl := hline (Fin.ofNat N (i-N)) z
          simp only [Fin.val_ofNat,Nat.mod_eq_of_lt h',e'] at hl
          simpa [lbl,e,OK] using hl hz
      obtain ⟨nonempty,clash⟩ := geometry q N S hq total sizes lines
      apply two_leaves (N+N) s R o ho hfork (fun i => Private q S (lbl i))
      · intro i hi
        refine ⟨nonempty _,?_,?_⟩
        · intro z hz
          exact hroot z.1.2 z.1.1 hz.1 z.2 hz.2.1
        · intro j hj ne
          apply Set.disjoint_left.mpr
          intro z hz hz'
          have eq := hz.2.2 (lbl j) (leaves j hj hz')
          exact ne ((inv i hi).symm.trans ((congrArg idx eq).trans (inv j hj)))
      · have cannot (i j : ℕ) (hi : i < N+N) (hj : j < N+N)
            (bad : Bad q S (lbl i) (lbl j)) (incl : R (N+N) ⊆ R i ∪ R j)
            (ai : Private q S (lbl i) ⊆ R (N+N)) (aj : Private q S (lbl j) ⊆ R (N+N)) : False := by
          obtain ⟨z,hz,w,hw,ni,nj⟩ := bad
          have mix : (z.1,w.2) ∈ R (N+N) := ⟨(ai hz).1,(aj hw).2⟩
          exact (incl mix).elim (fun h => ni (leaves i hi h)) (fun h => nj (leaves j hj h))
        intro i hi j hj ne hsub both
        obtain ⟨ai,aj⟩ := both
        have labNe : lbl i ≠ lbl j := fun e =>
          ne ((inv i hi).symm.trans ((congrArg idx e).trans (inv j hj)))
        rcases clash _ _ labNe with h | h
        · exact cannot i j hi hj h hsub ai aj
        · exact cannot j i hj hi h (by rwa [Set.union_comm]) aj ai
      · omega
    have count := linear q N C.size S (by omega) enough cards uniqueLines U V hleft hright forks hout
    rw [order]
    omega
  refine useBound ?_ ?_ ?_
  · intro p z hz
    obtain ⟨hp,hn⟩ := leaves p.val (by omega) z hz
    change (incidenceInput {z.1.1} {z.1.2}).getD p.val false = true at hp
    change (incidenceInput (zeroSet S z.2) z.2).getD p.val false = false at hn
    rw [leftBit] at hp hn
    have e : p = z.1.1 := by simpa using hp
    refine ⟨e.symm, ?_⟩
    by_contra! allMiss
    have mem : p ∈ zeroSet S z.2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,allMiss⟩
    simp [mem] at hn
  · intro l z hz
    obtain ⟨hp,hn⟩ := leaves (N+l.val) (by omega) z hz
    change (incidenceInput {z.1.1} {z.1.2}).getD (N+l.val) false = true at hp
    change (incidenceInput (zeroSet S z.2) z.2).getD (N+l.val) false = false at hn
    rw [rightBit] at hp hn
    exact ⟨(show l = z.1.2 by simpa using hp).symm, by simpa using hn⟩
  · refine ⟨C.output, out, ?_⟩
    intro l p hp Y hy
    apply root (p,l) Y (pairs l p hp)
    apply reject _ Y hy
    intro k hk
    apply Finset.disjoint_left.mpr
    intro t ht hz
    exact (Finset.mem_filter.mp hz).2 k hk ht
