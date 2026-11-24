import Mathlib
import PEqualNP.Defs

-- Each rectangle pairs an accepted incidence with a rejected line query.
-- Each line may be tested against any sparse query containing it.
-- Removing up to four times the gate count in flags still leaves a split across 97 lines.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_5339_547
    (count : ∀ (N m s t o : ℕ) (S : ℕ → Fin N → Finset (Fin N)) (a b : ℕ → ℕ)
    (ho : o < m+s)
    (input : ∀ w < m, ∀ l, (S w l).card ≤ 1)
    (gate : ∀ j < s, max (a j) (b j) < m+j ∧ ∀ l, S (m+j) l ⊆ S (a j) l ∪ S (b j) l),
    (∑ l, (S o l).card) ≤ N+t*s ∨ ∃ j < s,
      t < ({l : Fin N | ¬ S (m+j) l ⊆ S (a j) l ∧ ¬ S (m+j) l ⊆ S (b j) l} : Set _).ncard)
    (geometric : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop), 100 < q → N=q^2+q+1 →
    (∀ l, ({p : Fin N | I p l} : Set _).ncard=q+1) →
    (∀ p r, p≠r → ∃! l, I p l ∧ I r l) →
    ∀ (s o : ℕ) (a b : ℕ → ℕ) (R : ℕ → Set ((Fin N × Fin N) × Finset (Fin N))),
    let m := N+N
    o < m+s →
    (∀ p : Fin N, R p.val ⊆ {z | z.1.1=p ∧ ∃ l∈z.2, I p l} ∧
      R (N+p.val) ⊆ {z | z.1.2=p ∧ p∉z.2}) →
    (∀ j < s, max (a j) (b j) < m+j ∧ R (m+j) ⊆ R (a j) ∪ R (b j) ∧
      ∃ A B, R (m+j) = Set.prod A B) →
    (∀ p l, I p l → ∀ Y : Finset (Fin N), Y.card ≤ q → ((p,l),Y) ∈ R o) →
    (∀ Z : Finset (Fin N × Fin N), Z.card ≤ 4*s →
      ∀ tests : Fin N → Finset (Fin N), (∀ l, l ∈ tests l ∧ (tests l).card ≤ q) →
      ∃ j < s, ∃ T : Finset (Fin N), T.card = 97 ∧
        ∀ l ∈ T, ∃ p r, I p l ∧ I r l ∧ (p,l) ∉ Z ∧ (r,l) ∉ Z ∧
          ∀ k ∈ T, ((p,l),tests k) ∈ (R (m+j) ∩ R (a j)) \ R (b j) ∧
            ((r,l),tests k) ∈ (R (m+j) ∩ R (b j)) \ R (a j)) →
    N*q ≤ 100*s) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      100 < q → N=q^2+q+1 → (∀ l, Fintype.card {p : Fin N // I p l}=q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
      let m := N+N
      let one := fun (a b : Fin N) => decide (b=a)
      let R := {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ k < s, W (m+k) ⊆ W o ∧
        (one e.1,one e.2) ∈ W (m+k) ∧ ∃ a b, max a b < m+k ∧
        W (m+k) = W a ∩ W b ∧ ∃ A B, W a = A ×ˢ Set.univ ∧ W b = Set.univ ×ˢ B}
      o < m+s →
      (∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true}) →
      (∀ k < s, ∃ a b, max a b < m+k ∧ W (m+k) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
      (∀ p l, I p l → (one p,one l) ∈ W o) →
      (∀ T : Fin N → Bool, Fintype.card {l : Fin N // T l = true} ≤ q →
        ((fun p => decide (¬∃ l, I p l ∧ T l = true)),T) ∉ W o) →
      R.ncard ≤ 4*s →
      ∀ (E : Finset (Fin N × Fin N)), (∀ e, e ∈ E ↔ I e.1 e.2 ∧ e ∉ R) →
      ∀ (A B : Finset (Fin N)), A.Nonempty → B.Nonempty →
        (∀ p ∈ A, 12*q/25 < (B.filter fun l => (p,l) ∈ E).card) →
        (∀ l ∈ B, 12*q/25 < (A.filter fun p => (p,l) ∈ E).card) →
        N*q ≤ 100*s := by
  classical
  intro q N I di hq hN degree geom s o W
  dsimp only
  intro hout raw gates yes no _ _ _ _ _ _ _ _ _
  let m := N+N
  let one (v : Fin N) := fun w : Fin N => decide (w=v)
  let pos (e : Fin N × Fin N) := (one e.1,one e.2)
  let neg (Y : Finset (Fin N)) :=
    (fun p : Fin N => decide (¬∃ l ∈ Y, I p l),fun l : Fin N => decide (l∈Y))
  let accept (w : ℕ) := {e : Fin N × Fin N | I e.1 e.2 ∧ pos e ∈ W w}
  let reject (w : ℕ) := {Y : Finset (Fin N) | neg Y ∉ W w}
  let R (w : ℕ) := accept w ×ˢ reject w
  have leaf (p : Fin N) : R p.val ⊆ {z | z.1.1=p ∧ ∃ l∈z.2, I p l} ∧
      R (N+p.val) ⊆ {z | z.1.2=p ∧ p∉z.2} := by
    obtain ⟨lp,rp⟩ := raw p
    constructor
    · rintro ⟨⟨v,l⟩,Y⟩ ⟨⟨_,hit⟩,miss⟩
      change pos (v,l) ∈ W p.val at hit
      change neg Y ∉ W p.val at miss
      rw [lp] at hit miss
      change decide (p=v) = true at hit
      change ¬decide (¬∃ t∈Y, I p t) = true at miss
      exact ⟨(of_decide_eq_true hit).symm,by simpa using miss⟩
    · rintro ⟨⟨v,l⟩,Y⟩ ⟨⟨_,hit⟩,miss⟩
      change pos (v,l) ∈ W (N+p.val) at hit
      change neg Y ∉ W (N+p.val) at miss
      rw [rp] at hit miss
      change decide (p=l) = true at hit
      change ¬decide (p∈Y) = true at miss
      exact ⟨(of_decide_eq_true hit).symm,by simpa using miss⟩
  have parents (j : ℕ) (hj : j < s) : ∃ a b, max a b < m+j ∧ R (m+j) ⊆ R a ∪ R b := by
    obtain ⟨a,b,h,op⟩ := gates j hj
    refine ⟨a,b,h,?_⟩
    rintro ⟨e,Y⟩ ⟨⟨inc,hit⟩,miss⟩
    change pos e ∈ W (m+j) at hit
    change neg Y ∉ W (m+j) at miss
    change ((I e.1 e.2 ∧ pos e ∈ W a) ∧ neg Y ∉ W a) ∨ ((I e.1 e.2 ∧ pos e ∈ W b) ∧ neg Y ∉ W b)
    change W (m+j) ∈ _ at op
    simp only [List.mem_cons,List.not_mem_nil,or_false] at op
    rcases op with h|h|h|h <;> rw [h] at hit miss <;> simp_all only [Set.mem_union,Set.mem_inter_iff,Set.mem_empty_iff_false] <;> tauto
  choose pa pb prop using parents
  let a j := if h : j < s then pa j h else 0
  let b j := if h : j < s then pb j h else 0
  have coverage (j : ℕ) (hj : j < s) : max (a j) (b j) < m+j ∧ R (m+j) ⊆ R (a j) ∪ R (b j) := by
    simpa only [a,b,dite_eq_left hj] using prop j hj
  have root (p l : Fin N) (inc : I p l) (Y : Finset (Fin N)) (small : Y.card ≤ q) :
      ((p,l),Y) ∈ R o := by
    refine ⟨⟨inc,yes p l inc⟩,?_⟩
    let y := fun t : Fin N => decide (t∈Y)
    have size : Fintype.card {t : Fin N // y t=true} ≤ q := by
      simpa [y] using small
    have miss := no y size
    change neg Y ∉ W o
    have hv : (fun p : Fin N => decide (¬∃ t∈Y, I p t)) = (fun p => decide (¬∃ t, I p t ∧ y t = true)) := by
      funext p
      apply decide_eq_decide.mpr
      simp only [y,decide_eq_true_eq]
      simp only [and_comm]
    simpa only [neg,hv,y] using miss
  by_cases done : N*q ≤ 100*s
  · exact done
  have lineDegree (l : Fin N) : ({p : Fin N | I p l} : Set _).ncard=q+1 := by
    rw [Set.ncard_eq_toFinset_card']
    simpa [Fintype.card_subtype] using degree l
  apply geometric q N I hq hN lineDegree geom s o a b R hout leaf
    (fun j hj => ⟨(coverage j hj).1,(coverage j hj).2,accept _,reject _,rfl⟩) root
  intro Z hz tests admissible
  let S (w : ℕ) (l : Fin N) := Finset.univ.filter fun p : Fin N => (p,l) ∉ Z ∧ ((p,l),tests l)∈R w
  have input (w : ℕ) (hw : w < m) (l : Fin N) : (S w l).card ≤ 1 := by
    by_cases h : w < N
    · let p : Fin N := ⟨w,h⟩
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact ((leaf p).1 (Finset.mem_filter.mp hi).2.2).1.trans (((leaf p).1 (Finset.mem_filter.mp hj).2.2).1.symm)
    · let t : Fin N := ⟨w-N,by dsimp [m] at hw; omega⟩
      have wt : w=N+t.val := by dsimp [t]; omega
      have empty : S w l=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨eq,no⟩ := (leaf t).2 (wt ▸ (Finset.mem_filter.mp hp).2.2)
        exact no ((congrArg (fun v => v ∈ tests l) eq).mp (admissible l).1)
      simp [empty]
  have legal (j : ℕ) (hj : j < s) := (coverage j hj).1
  have step (j : ℕ) (hj : j < s) (l : Fin N) : S (m+j) l ⊆ S (a j) l ∪ S (b j) l := by
    intro p hp
    have h := (coverage j hj).2 (Finset.mem_filter.mp hp).2.2
    exact h.elim (fun h => Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.1,h⟩))
      (fun h => Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.1,h⟩))
  have deficit (l : Fin N) : q+1 ≤ (S o l).card + (Z.filter fun e => e.2=l).card := by
    let points := Finset.univ.filter fun p : Fin N => I p l
    let deleted := (Z.filter fun e => e.2=l).image Prod.fst
    have inc : points ⊆ S o l ∪ deleted := by
      intro p hp
      by_cases lost : (p,l) ∈ Z
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p,l),Finset.mem_filter.mpr ⟨lost,rfl⟩,rfl⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lost,
          root _ _ (Finset.mem_filter.mp hp).2 (tests l) (admissible l).2⟩)
    have card : points.card = q+1 := by simpa [points,Fintype.card_subtype] using degree l
    rw [←card]
    exact ((Finset.card_le_card inc).trans (Finset.card_union_le _ _)).trans
      (Nat.add_le_add_left Finset.card_image_le _)
  have mass : N*(q+1) ≤ (∑ l, (S o l).card) + Z.card := by
    have z : (∑ l : Fin N, (Z.filter fun e => e.2=l).card) = Z.card := by
      simpa using Finset.sum_card_fiberwise_eq_card_filter Z (Finset.univ : Finset (Fin N)) Prod.snd
    calc N*(q+1) = ∑ _l : Fin N, (q+1) := by simp
         _ ≤ ∑ l : Fin N, ((S o l).card + (Z.filter fun e => e.2=l).card) :=
           Finset.sum_le_sum fun l _ => deficit l
         _ = _ := by rw [Finset.sum_add_distrib,z]
  rcases count N m s 96 o S a b hout input (fun j hj => ⟨legal j hj,step j hj⟩) with small|heavy
  · rw [Nat.mul_succ] at mass
    omega
  obtain ⟨j,hj,many⟩ := heavy
  let fails (l : Fin N) := ¬ S (m+j) l ⊆ S (a j) l ∧ ¬ S (m+j) l ⊆ S (b j) l
  let J := Finset.univ.filter fails
  have jbig : 97 ≤ J.card := by
    have h : ({l|fails l} : Set (Fin N)) = (J : Set (Fin N)) := by ext; simp [J]
    change 96 < ({l|fails l} : Set (Fin N)).ncard at many
    rwa [h,Set.ncard_coe_finset] at many
  obtain ⟨T,inJ,cardT⟩ := Finset.exists_subset_card_eq jbig
  have split (l : Fin N) (hl : l ∈ T) :
      ∃ p r, ((p,l) ∉ Z ∧ (p,l) ∈ accept (m+j) ∧ (p,l) ∈ accept (a j) ∧ (p,l) ∉ accept (b j)) ∧
             ((r,l) ∉ Z ∧ (r,l) ∈ accept (m+j) ∧ (r,l) ∈ accept (b j) ∧ (r,l) ∉ accept (a j)) ∧
             tests l ∈ reject (m+j) ∧ tests l ∈ reject (a j) ∧ tests l ∈ reject (b j) := by
    obtain ⟨na,nb⟩ := (Finset.mem_filter.mp (inJ hl)).2
    obtain ⟨p,pw,pb⟩ := Finset.not_subset.mp nb
    obtain ⟨r,rw',ra⟩ := Finset.not_subset.mp na
    obtain ⟨_,pz,pleft,pneg⟩ := Finset.mem_filter.mp pw
    obtain ⟨_,rz,rleft,rneg⟩ := Finset.mem_filter.mp rw'
    have pa := (Finset.mem_union.mp (step j hj l pw)).resolve_right pb
    have rb := (Finset.mem_union.mp (step j hj l rw')).resolve_left ra
    obtain ⟨_,_,pA,yA⟩ := Finset.mem_filter.mp pa
    obtain ⟨_,_,rB,yB⟩ := Finset.mem_filter.mp rb
    exact ⟨p,r,⟨pz,pleft,pA,fun h => pb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,pz,h,yB⟩)⟩,
      ⟨rz,rleft,rB,fun h => ra (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rz,h,yA⟩)⟩,pneg,yA,yB⟩
  refine ⟨j,hj,T,cardT,?_⟩
  intro l hl
  obtain ⟨p,r,⟨pz,pp,pa,pb⟩,⟨rz,rp,rb,ra⟩,_⟩ := split l hl
  refine ⟨p,r,pp.1,rp.1,pz,rz,?_⟩
  intro k hk
  obtain ⟨_,_,_,_,yP,yA,yB⟩ := split k hk
  exact ⟨⟨⟨⟨pp,yP⟩,⟨pa,yA⟩⟩,fun h => pb h.1⟩,⟨⟨⟨rp,yP⟩,⟨rb,yB⟩⟩,fun h => ra h.1⟩⟩
