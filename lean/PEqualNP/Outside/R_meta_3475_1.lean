import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.ReadK PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_3475_1
    (pairGraph : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
        (E : Finset (Fin N × Fin N)),
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ 2 →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun _ C x = false) →
      (∀ e ∈ E, circuitFun _ C (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true) →
      ∃ G : SimpleGraph (Fin (N+N)),
        (∀ a b c d, a ≠ c → b ≠ d → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
        (∀ a b, circuitFun _ C (fun i => decide (i = a ∨ i = b)) = true ↔ G.Adj a b) ∧
        ∀ e ∈ E, G.Adj (Fin.castAdd N e.1) (Fin.natAdd N e.2))
    (branchCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (U : Finset (Fin n)),
      Monotone2 C →
      (∀ a b c d, a ≠ c → b ≠ d → ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
      (∀ a b, circuitFun n C (fun i => decide (i = a ∨ i = b)) = true ↔ G.Adj a b) →
      (∀ v ∈ U, 2 ≤ (G.neighborSet v).ncard) →
      ∃ T ⊆ U, (∀ u ∈ U, ∀ v ∈ U, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ U.card+T.card ≤ C.size+1)
    (obstruction : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : Circuit) (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      let hits := fun (i : Fin (N+N)) (e : Fin N × Fin N) => i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2
      let degree := fun i => (E.filter (hits i)).card
      (∀ e ∈ E, I e.1 e.2 ∧ circuitFun _ C (fun i => decide (hits i e)) = true ∧
        lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
        lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false) →
      (∀ e ∈ E, ∀ i, hits i e → 24 < degree i) →
      11000 < C.size → (∃ i, 71 < degree i) → 24*C.size < E.card →
      ∃ Y : Finset (Fin N), Y.card ≤ q ∧ C.eval
        (incidenceInput (Finset.univ.filter fun p => ∀ l ∈ Y, ¬I p l) Y) = true) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
        (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun _ C x = false) →
      let hits := fun (i : Fin (N+N)) (e : Fin N × Fin N) => i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2
      (∀ e ∈ E, I e.1 e.2 ∧ circuitFun _ C (fun i => decide (hits i e)) = true ∧
        lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
        lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false) →
      (∀ e ∈ E, ∀ i, hits i e → 24 < (E.filter (hits i)).card) → E.card ≤ 24*C.size := by
  classical
  intro q N I inst C E hq hN cols uniq ao quiet hits acc dense
  by_contra! bad
  let L (p : Fin N) := Fin.castAdd N p
  let R (l : Fin N) := Fin.natAdd N l
  let ends := E.image (fun e => L e.1) ∪ E.image (fun e => R e.2)
  have side_ne (p l : Fin N) : L p ≠ R l := by
    intro h
    have eq := congrArg Fin.val h
    change p.val = N+l.val at eq
    omega
  obtain ⟨G,ns,ev,adj⟩ := pairGraph N I C E uniq
    (fun x hx hn => quiet x (by omega) hn) (fun e h => (acc e h).2.1)
  have hdeg (i) (hi : i ∈ ends) : 2 ≤ (G.neighborSet i).ncard := by
    obtain ⟨e,he,hi⟩ : ∃ e ∈ E, hits i e := by
      rcases Finset.mem_union.mp hi with h | h
      · obtain ⟨e,he,eq⟩ := Finset.mem_image.mp h
        exact ⟨e,he,Or.inl eq.symm⟩
      · obtain ⟨e,he,eq⟩ := Finset.mem_image.mp h
        exact ⟨e,he,Or.inr eq.symm⟩
    have hd := dense e he i hi
    obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (show 1 < (E.filter (hits i)).card by omega)
    obtain ⟨ae,ai⟩ := Finset.mem_filter.mp ha
    obtain ⟨be,bi⟩ := Finset.mem_filter.mp hb
    apply (Set.one_lt_ncard_iff (s := G.neighborSet i)).mpr
    rcases ai with rfl|rfl
    · rcases bi with h|h
      · have f := (Fin.castAdd_injective _ _) h
        exact ⟨R a.2,R b.2,adj a ae,h ▸ adj b be,fun k => ab (Prod.ext f ((Fin.natAdd_injective _ _) k))⟩
      · exact (side_ne _ _ h).elim
    · rcases bi with h|h
      · exact (side_ne _ _ h.symm).elim
      · have f := (Fin.natAdd_injective _ _) h
        exact ⟨L a.1,L b.1,(adj a ae).symm,h ▸ (adj b be).symm,fun k => ab (Prod.ext ((Fin.castAdd_injective _ _) k) f)⟩
  have mono : Monotone2 C := fun g hg => ⟨ao.1 g hg,(ao.2.2 g hg).le⟩
  obtain ⟨T,_,covered,sz⟩ := branchCover _ G C ends mono ns ev hdeg
  have cov (e) (he : e ∈ E) := covered (L e.1) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ he))
    (R e.2) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)) (adj e he)
  -- Rows have disjoint sets of ordered neighbor pairs because the graph has no four-cycle.
  have star_count (A B : Finset (Fin (N+N)))
      (a b : (Fin N × Fin N) → Fin (N+N)) (memA : ∀ e ∈ E, a e ∈ A) (memB : ∀ e ∈ E, b e ∈ B)
      (inj : ∀ x ∈ E, ∀ y ∈ E, a x = a y → b x = b y → x = y)
      (edge : ∀ e ∈ E, G.Adj (a e) (b e)) (k : ℕ) :
      (2*k-1)*E.card ≤ k^2*A.card + B.card*(B.card-1) := by
    classical
    let F (u) := E.filter fun e => a e = u
    let S (u) := (F u).image b
    have sc (u) : (S u).card = (F u).card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy eq
      obtain ⟨hx,ex⟩ := Finset.mem_filter.mp hx
      obtain ⟨hy,ey⟩ := Finset.mem_filter.mp hy
      exact inj x hx y hy (ex.trans ey.symm) eq
    have inside (u v) (hv : v ∈ S u) : v ∈ B ∧ G.Adj u v := by
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨h,eq⟩ := Finset.mem_filter.mp he
      exact ⟨memB e h, eq ▸ edge e h⟩
    have dis : (↑A : Set (Fin (N+N))).PairwiseDisjoint (fun p => (S p).offDiag) := by
      intro p _ r _ pr
      apply Finset.disjoint_left.mpr
      intro x hp hr
      obtain ⟨pa,pb,ab⟩ := Finset.mem_offDiag.mp hp
      obtain ⟨ra,rb,_⟩ := Finset.mem_offDiag.mp hr
      exact ns p x.1 r x.2 pr ab ⟨(inside _ _ pa).2,(inside _ _ ra).2.symm,(inside _ _ rb).2,(inside _ _ pb).2.symm⟩
    have incl : A.biUnion (fun u => (S u).offDiag) ⊆ B.offDiag := by
      intro x hx
      obtain ⟨u,_,h⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨a,b,ne⟩ := Finset.mem_offDiag.mp h
      exact Finset.mem_offDiag.mpr ⟨(inside _ _ a).1,(inside _ _ b).1,ne⟩
    have cap := Finset.card_le_card incl
    rw [Finset.card_biUnion dis,Finset.offDiag_card] at cap
    have tan (d : ℕ) : (2*k-1)*d ≤ k^2 + d*(d-1) := by
      cases k with
      | zero => simp
      | succ k =>
        cases d with
        | zero => simp
        | succ d =>
          rw [show 2*(k+1)-1 = 2*k+1 by omega, Nat.add_sub_cancel]
          zify
          nlinarith [sq_nonneg ((k : ℤ)-(d : ℤ))]
    rw [Finset.card_eq_sum_card_fiberwise memA,Finset.mul_sum]
    calc
      _ ≤ ∑ u ∈ A, (k^2+(S u).offDiag.card) := Finset.sum_le_sum fun u _ => by
        rw [Finset.offDiag_card,sc]; simpa only [Nat.mul_sub_left_distrib,Nat.mul_one] using tan (F u).card
      _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        simpa [Nat.mul_comm,Nat.mul_sub_left_distrib] using Nat.add_le_add_left cap (k^2*A.card)
  let p (e : Fin N × Fin N) := L e.1
  let l (e : Fin N × Fin N) := R e.2
  let A := E.image p
  let B := E.image l
  have pa (e) (h : e ∈ E) : p e ∈ A := Finset.mem_image_of_mem _ h
  have lb (e) (h : e ∈ E) : l e ∈ B := Finset.mem_image_of_mem _ h
  have pl (x y : Fin N × Fin N) (h : p x = p y) (h' : l x = l y) : x=y :=
    Prod.ext ((Fin.castAdd_injective _ _) h) ((Fin.natAdd_injective _ _) h')
  have dis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,_,h⟩ := Finset.mem_image.mp hw
    exact side_ne _ _ h.symm
  have sum : A.card+B.card = ends.card := (Finset.card_union_of_disjoint dis).symm
  have left := star_count A B p l pa lb (fun x _ y _ => pl x y) adj
  have right := star_count B A l p lb pa (fun x _ y _ h h' => pl x y h' h) (fun e he => (adj e he).symm)
  -- Orient each edge toward one covering endpoint to count a third family of rows.
  let a (e : Fin N × Fin N) := if p e ∈ T then l e else p e
  let b (e : Fin N × Fin N) := if p e ∈ T then p e else l e
  have cover (k : ℕ) : (2*k-1)*E.card ≤ k^2*(A.card+B.card)+T.card*(T.card-1) := by
    rw [sum]
    apply star_count ends T a b _ _ _ _ k
    · intro e he; by_cases h : p e ∈ T
      · rw [show a e = l e by simp [a,h]]; exact Finset.mem_union_right A (lb e he)
      · rw [show a e = p e by simp [a,h]]; exact Finset.mem_union_left B (pa e he)
    · intro e he; by_cases h : p e ∈ T
      · simp [b,h]
      · rw [show b e = l e by simp [b,h]]; exact (cov e he).resolve_left h
    · intro x _ y _ ha hb
      by_cases hx : p x ∈ T <;> by_cases hy : p y ∈ T <;> simp only [a,b,hx,hy,ite_true,ite_false] at ha hb
      · exact pl x y hb ha
      · exact (side_ne _ _ ha.symm).elim
      · exact (side_ne _ _ ha).elim
      · exact pl x y ha hb
    · intro e he; by_cases h : p e ∈ T
      · simpa only [a,b,h,ite_true] using (adj e he).symm
      · simpa only [a,b,h,ite_false] using adj e he
  have numeric (s e a b t : ℕ) (budget : a+b+t ≤ s+1)
      (left : ∀ k, (2*k-1)*e ≤ k^2*a+b*(b-1))
      (right : ∀ k, (2*k-1)*e ≤ k^2*b+a*(a-1))
      (cover : ∀ k, (2*k-1)*e ≤ k^2*(a+b)+t*(t-1))
      (hs : s ≤ 11000) : e ≤ 24*s := by
    by_cases zero : s=0
    · subst s
      have l := left 1
      have r := right 1
      have ha : a ≤ 1 := by omega
      have hb : b ≤ 1 := by omega
      rw [Nat.sub_eq_zero_of_le hb, Nat.mul_zero] at l
      rw [Nat.sub_eq_zero_of_le ha, Nat.mul_zero] at r
      norm_num at l r
      omega
    by_cases small : s ≤ 200
    · have h := cover 15
      have c := Nat.mul_le_mul_left t (show t-1 ≤ 225 by omega)
      norm_num at h
      omega
    -- A small cover controls its own ordered pairs. A large cover leaves fewer active endpoints.
    by_cases tc : 50*t ≤ 13*(s+1)
    · have h := cover 32
      have c := Nat.mul_le_mul_left t (show t-1 ≤ 2860 by omega)
      norm_num at h
      omega
    have compact (x y : ℕ) (hb : x+y+t ≤ s+1) (hxy : y ≤ x)
        (lim : (2*64-1)*e ≤ 64^2*x+y*(y-1)) : e ≤ 24*s := by
      have c := Nat.mul_le_mul_left y (show y-1 ≤ 4096 by omega)
      norm_num at lim
      omega
    rcases le_total a b with h|h
    · exact compact b a (by omega) h (right 64)
    · exact compact a b budget h (left 64)
  have large : 11000 < C.size := by
    by_contra! hs
    exact (Nat.not_le_of_lt bad) (numeric C.size E.card A.card B.card T.card (by omega) left right cover hs)
  have high : ∃ i, 71 < (E.filter (hits i)).card := by
    by_contra! cap
    have count (f : Fin N × Fin N → Fin (N+N)) (Y : Finset (Fin (N+N))) (toY : ∀ e ∈ E, f e ∈ Y)
        (hf : ∀ e ∈ E, hits (f e) e) : E.card ≤ 71*Y.card := by
      rw [Finset.card_eq_sum_card_fiberwise toY]
      calc
        _ ≤ ∑ _ ∈ Y, 71 := Finset.sum_le_sum fun v _ => (Finset.card_le_card (t := E.filter (hits v)) (by
          intro e he
          obtain ⟨h,eq⟩ := Finset.mem_filter.mp he
          exact Finset.mem_filter.mpr ⟨h,eq ▸ hf e h⟩)).trans (cap v)
        _ = _ := by simp [Nat.mul_comm]
    -- Each edge contributes once on each side and once to its chosen covering endpoint.
    have cP := count p A pa (fun _ _ => Or.inl rfl)
    have cL := count l B lb (fun _ _ => Or.inr rfl)
    have cT := count b T (fun e he => by
      by_cases h : p e ∈ T
      · rw [show b e = p e by simp [b,h]]; exact h
      · rw [show b e = l e by simp [b,h]]; exact (cov e he).resolve_left h) (fun e _ => by
        by_cases h : p e ∈ T
        · rw [show b e = p e by simp [b,h]]; exact Or.inl rfl
        · rw [show b e = l e by simp [b,h]]; exact Or.inr rfl)
    omega
  obtain ⟨Y,hy,hot⟩ := obstruction q N I C E hq hN cols uniq ao acc dense large high bad
  let X := Finset.univ.filter fun p => ∀ l ∈ Y, ¬I p l
  let x := Fin.append (fun p : Fin N => decide (p ∈ X)) (fun l : Fin N => decide (l ∈ Y))
  have lines : Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q := by
    rw [Fintype.card_subtype]
    have eq : Finset.univ.filter (fun l : Fin N => x (Fin.natAdd N l) = true) = Y := by
      ext l
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,x,Fin.append,Fin.addCases_right,decide_eq_true_eq]
    rwa [eq]
  have no : ¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
    rintro ⟨p,l,inc,hp,hl⟩
    simp only [x,Fin.append,Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq] at hp hl
    exact (Finset.mem_filter.mp hp).2 l hl inc
  have cold := quiet x lines no
  change C.eval (List.ofFn x) = false at cold
  rw [show List.ofFn x = incidenceInput X Y from List.ofFn_fin_append ..] at cold
  exact Bool.noConfusion (hot.symm.trans cold)
