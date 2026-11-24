import PEqualNP.Defs

-- A false certificate lists primary bits whose simultaneous absence forces rejection.
-- The gate in this step becomes a union of two certificate families. Every certificate
-- on either side must contain the same three point bits or the same three line bits. Each side also forces a private bit.
-- Their common mandatory bits cannot be obtained by taking the union of two older sets.
-- The covering and small-order arguments follow the checked reduction R_meta_2794_601.
theorem PEqualNP.Outside.R_meta_3252_17
    (certificates : ∀ (Z : Type) (m s : ℕ) (X : ℕ → Set Z), (∀ g < s, ∃ a < m+g, ∃ b < m+g,
        X (m+g) = X a ∪ X b ∨ X (m+g) = X a ∨ X (m+g) = ∅ ∨ X (m+g) = X a ∩ X b) →
      ∃ F : ℕ → Set (Finset ℕ), (∀ v < m, F v = {{v}}) ∧
        (∀ g < s, ∃ a < m+g, ∃ b < m+g,
        F (m+g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (m+g) = F a ∨
        F (m+g) = {∅} ∨ F (m+g) = F a ∪ F b) ∧
        ∀ w < m+s, (∀ A ∈ F w, ∀ v ∈ A, v < m) ∧
          ∀ z, z ∉ X w ↔ ∃ A ∈ F w, ∀ v ∈ A, z ∉ X v)
    (coverBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 200 ≤ q → N = q^2+q+1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l) →
      ∀ (s o : ℕ) (F : ℕ → Set (Finset ℕ)), o < N+N+s → (∀ v < N+N, F v = {{v}}) →
      (∀ g < s, ∃ a < N+N+g, ∃ b < N+N+g,
        F (N+N+g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (N+N+g) = F a ∨
        F (N+N+g) = {∅} ∨ F (N+N+g) = F a ∪ F b) →
      (∀ A ∈ F o, ∀ p l : Fin N, I p l → p.val ∈ A ∨ N+l.val ∈ A) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N,
        (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A ↔ p ∉ T)) →
      (∃ i < s, ∃ a b, max a b < N+N+i ∧ F (N+N+i) = F a ∪ F b ∧
        let K := fun w => {v : ℕ | ∀ A ∈ F w, v ∈ A}
        (∃ U : Finset ℕ, U.card = 3 ∧ (U : Set ℕ) ⊆ K a ∩ K b ∧ ((∀ v ∈ U, v < N) ∨ ∀ v ∈ U, N ≤ v)) ∧
          ¬ K a ⊆ K b ∧ ¬ K b ⊆ K a ∧
          ¬ ∃ u < N+N+i, ∃ v < N+N+i, K (N+N+i) = K u ∪ K v) → N*q ≤ 100*s) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (x22 : Fin x2) => Bool.false) else (fun (x22 : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Bool) (x22 : Fin x2) (x23 : Fin x2), x22 ≠ x23 ∧ x22 ∈ x19 x21 (x12 + x20) ∧ x23 ∈ x19 x21 (x12 + x20) ∧ ¬∃ x24 < x12 + x20, ∃ x25 < x12 + x20, x19 x21 (x12 + x20) = x19 x21 x24 ∪ x19 x21 x25) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  dsimp only
  intro q N I inst hq hN degrees unique s o X ho inputs steps pos neg bad
  have freshPoint : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ a b : Fin N, a ≠ b → ∃! l, I a l ∧ I b l) →
      ∀ T : Finset (Fin N), T.card ≤ q → ∀ l : Fin N, l ∉ T →
        ∃ p : Fin N, I p l ∧ ∀ k ∈ T, ¬ I p k := by
    intro q N I inst degree unique T small l hl
    classical
    by_contra! allCovered
    have covered (p : {p : Fin N // I p l}) : ∃ k : ↥T, I p.val k.val := by
      obtain ⟨k,hk,inc⟩ := allCovered p.val p.property
      exact ⟨⟨k,hk⟩,inc⟩
    choose f incident using covered
    have injective : Function.Injective f := by
      intro a b same
      by_contra ne
      obtain ⟨m,hm,only⟩ := unique a.val b.val (fun h => ne (Subtype.ext h))
      have h := incident b
      rw [← same] at h
      have eq := (only _ ⟨incident a,h⟩).trans (only l ⟨a.property,b.property⟩).symm
      exact hl (eq ▸ (f a).property)
    have bound := Fintype.card_le_of_injective f injective
    rw [degree, Fintype.card_coe] at bound
    omega
  let one (p r : Fin N) := decide (r=p)
  let row (d : Bool) (p : Fin N) : (Fin N → Bool) × (Fin N → Bool) :=
    if d then (one p,fun _ => false) else (fun _ => false,one p)
  obtain ⟨F, leaves, gates, spec⟩ := certificates _ (N+N) s X (by
    intro i hi
    obtain ⟨a,b,h,op⟩ := steps i hi
    exact ⟨a,(max_lt_iff.mp h).1,b,(max_lt_iff.mp h).2,by simpa only [List.mem_cons,List.not_mem_nil,or_false] using op⟩)
  have cover (A : Finset ℕ) (hA : A ∈ F o) (p l : Fin N) (h : I p l) : p.val ∈ A ∨ N+l.val ∈ A := by
    by_contra! miss
    apply ((spec o ho).2 _).mpr ⟨A,hA,?_⟩ (pos p l h)
    intro v hv
    have hvb := (spec o ho).1 A hA v hv
    by_cases small : v < N
    · let k : Fin N := ⟨v,small⟩
      rw [(inputs k).1]
      change ¬ decide (k = p) = true
      exact fun e => miss.1 ((congrArg Fin.val (of_decide_eq_true e)) ▸ hv)
    · let k : Fin N := ⟨v-N,by omega⟩
      have e : v = N + k.val := by dsimp [k]; omega
      rw [e,(inputs k).2]
      change ¬ decide (k = l) = true
      intro eq
      have : v = N+l.val := e.trans (congrArg (fun a : Fin N => N+a.val) (of_decide_eq_true eq))
      exact miss.2 (this ▸ hv)
  have saturated : ∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N,
      (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N+p.val ∈ A ↔ p ∉ T) := by
    intro T ht
    let y := fun l : Fin N => decide (l ∈ T)
    let x := fun p : Fin N => decide (¬ ∃ l, I p l ∧ y l = true)
    have cy : Fintype.card {l : Fin N // y l = true} ≤ q := by
      simpa [Fintype.card_subtype, y] using ht
    obtain ⟨A,hA,zero⟩ := ((spec o ho).2 (x,y)).mp (neg y cy)
    have pl (p : Fin N) (h : p.val ∈ A) : ∃ l ∈ T, I p l := by
      have hh := zero p.val h
      rw [(inputs p).1] at hh
      change ¬ x p = true at hh
      simpa [x,y,and_comm] using hh
    have ln (l : Fin N) (h : N+l.val ∈ A) : l ∉ T := by
      have hh := zero _ h
      rw [(inputs l).2] at hh
      exact fun m => hh (show y l = true from decide_eq_true m)
    refine ⟨A,hA,fun p => ⟨⟨pl p,?_⟩,⟨ln p,?_⟩⟩⟩
    · rintro ⟨l,hl,inc⟩
      exact (cover A hA p l inc).resolve_right (fun bad => ln l bad hl)
    · intro hp
      obtain ⟨a, ha, avoid⟩ := freshPoint q N I degrees unique T ht p hp
      apply (cover A hA a p ha).resolve_left
      intro bad
      obtain ⟨l,hl,inc⟩ := pl a bad
      exact avoid l hl inc
  by_cases large : 200 ≤ q
  · apply coverBound q N I large hN degrees unique s o F ho leaves gates cover saturated
    obtain ⟨i,hi,d,p,r,hpr,hp,hr,fresh⟩ := bad
    let w := N+N+i
    let code (t : Fin N) := if d then t.val else N+t.val
    have inj : Function.Injective code := by
      intro x y h
      apply Fin.ext
      cases d <;> simpa [code] using h
    let K (v : ℕ) := {t : ℕ | ∀ A ∈ F v, t ∈ A}
    have prim (t : Fin N) (v : ℕ) (hv : v < N+N) : row d t ∈ X v ↔ code t=v := by
      by_cases small : v < N
      · let j : Fin N := ⟨v,small⟩
        change row d t ∈ X j.val ↔ code t=j.val
        rw [(inputs j).1]
        cases d <;> simp [row,one,code,Fin.ext_iff,j] <;> omega
      · let j : Fin N := ⟨v-N,by omega⟩
        have e : v = N+j.val := by dsimp [j]; omega
        rw [e,(inputs j).2]
        cases d <;> simp [row,one,code,Fin.ext_iff,j] <;> omega
    have trace (v : ℕ) (hv : v < N+N+s) :
        {t : Fin N | row d t ∈ X v} = code ⁻¹' K v := by
      ext t
      change row d t ∈ X v ↔ ∀ A ∈ F v, code t ∈ A
      have reject := (spec v hv).2 (row d t)
      constructor
      · intro yes A mem
        by_contra missingBit
        apply reject.mpr ⟨A,mem,?_⟩ yes
        intro b hb hz
        exact missingBit ((prim t b ((spec v hv).1 A mem b hb)).mp hz ▸ hb)
      · intro common
        by_contra no
        obtain ⟨A,mem,absent⟩ := reject.mp no
        have h := common A mem
        exact absent _ h ((prim t _ ((spec v hv).1 A mem _ h)).mpr rfl)
    have hw : w < N+N+s := by dsimp [w]; omega
    have small (v : ℕ) (h : v < w) : v < N+N+s := h.trans hw
    let P (v : ℕ) := code ⁻¹' K v
    change ¬ ∃ a < w, ∃ b < w, {t : Fin N | row d t ∈ X w} =
      {t : Fin N | row d t ∈ X a} ∪ {t : Fin N | row d t ∈ X b} at fresh
    have f : ¬ ∃ a < w, ∃ b < w, P w = P a ∪ P b := by
      rintro ⟨a,ha,b,hb,e⟩
      exact fresh ⟨a,ha,b,hb,by rw [trace w hw,trace a (small a ha),trace b (small b hb)]; exact e⟩
    have hh (t : Fin N) (h : row d t ∈ X w) : t ∈ P w := by
      change t ∈ code ⁻¹' K w
      rw [← trace w hw]
      exact h
    have hp' := hh p hp
    have hr' := hh r hr
    have third : ∃ t ∈ P w, t ≠ p ∧ t ≠ r := by
      by_contra! none
      have lt (x : Fin N) : code x < N+N := by cases d <;> simp [code] <;> omega
      have atom (x : Fin N) : P (code x) = {x} := by
        ext y
        change (∀ A ∈ F (code x), code y ∈ A) ↔ y=x
        simp [leaves _ (lt x),inj.eq_iff]
      apply f ⟨code p,(lt p).trans_le (by dsimp [w]; omega),code r,(lt r).trans_le (by dsimp [w]; omega),?_⟩
      rw [atom,atom]
      ext t
      change t ∈ P w ↔ t=p ∨ t=r
      constructor
      · intro h
        by_cases e : t=p
        · exact Or.inl e
        · exact Or.inr (none t h e)
      · rintro (rfl | rfl) <;> assumption
    obtain ⟨a,ha,b,hb,op⟩ := gates i hi
    change F w = _ ∨ F w = _ ∨ F w = _ ∨ F w = _ at op
    have noCopy (v : ℕ) (hv : v < w) (e : P w = P v) : False :=
      f ⟨v,hv,v,hv,by simpa only [Set.union_self] using e⟩
    rcases op with pair | copy | zero | union
    · apply (f ⟨a,ha,b,hb,?_⟩).elim
      ext t
      change (∀ A ∈ F w, code t ∈ A) ↔ (∀ A ∈ F a, code t ∈ A) ∨ (∀ B ∈ F b, code t ∈ B)
      rw [pair]
      constructor
      · intro all
        by_cases both : ∀ A ∈ F a, code t ∈ A
        · exact Or.inl both
        · push Not at both
          obtain ⟨A,mem,missingBit⟩ := both
          exact Or.inr (fun B hB => (Finset.mem_union.mp (all _ ⟨A,mem,B,hB,rfl⟩)).resolve_left missingBit)
      · rintro (h | h) U ⟨A,hA,B,hB,rfl⟩
        · exact Finset.mem_union_left _ (h A hA)
        · exact Finset.mem_union_right _ (h B hB)
    · exact (noCopy a ha (by dsimp [P,K]; rw [copy])).elim
    · have hh : ∅ ∈ F w := zero ▸ Set.mem_singleton _
      exact (Finset.notMem_empty _ (hp' ∅ hh)).elim
    · have core : K w = K a ∩ K b := by
        ext v
        simp only [K,Set.mem_setOf_eq,Set.mem_inter_iff,union,Set.forall_mem_union]
      have cross : P w = P a ∩ P b := by dsimp [P]; rw [core,Set.preimage_inter]
      refine ⟨i,hi,a,b,max_lt ha hb,union,?_,?_,?_,?_⟩
      · obtain ⟨t,ht,htp,htr⟩ := third
        refine ⟨{code p,code r,code t},by simp [inj.eq_iff,hpr,Ne.symm htp,Ne.symm htr],?_,?_⟩
        swap
        · cases d
          · right; simp [code]
          · left; simp [code]
        intro u hu
        rw [← core]
        simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact hp'
        · exact hr'
        · exact ht
      · intro incl
        exact noCopy a ha (cross.trans (Set.inter_eq_left.mpr (Set.preimage_mono incl)))
      · intro incl
        exact noCopy b hb (cross.trans (Set.inter_eq_right.mpr (Set.preimage_mono incl)))
      · rintro ⟨u,hu,v,hv,e⟩
        have same : K w = K u ∪ K v := e
        exact f ⟨u,hu,v,hv,congrArg (fun S => code ⁻¹' S) same⟩
  have propagate (g : ℕ) (hg : g < s) : ∃ a < N+N+g, ∃ b < N+N+g,
      ∀ A ∈ F (N+N+g), ∀ v ∈ A, ∃ B, (B ∈ F a ∨ B ∈ F b) ∧ v ∈ B := by
    obtain ⟨a,ha,b,hb,law⟩ := gates g hg
    refine ⟨a,ha,b,hb,?_⟩
    intro A hA v hv
    rcases law with join|copy|empty|meet
    · rw [join] at hA
      obtain ⟨U,hU,V,hV,rfl⟩ := hA
      exact (Finset.mem_union.mp hv).elim (fun h => ⟨U,Or.inl hU,h⟩) (fun h => ⟨V,Or.inr hV,h⟩)
    · exact ⟨A,Or.inl (copy ▸ hA),hv⟩
    · have e : A = ∅ := Set.mem_singleton_iff.mp (empty ▸ hA)
      exact False.elim (Finset.notMem_empty _ (e ▸ hv))
    · rw [meet] at hA; exact ⟨A,hA,hv⟩
  have reach (k : ℕ) (hk : k ≤ s) (W : Finset ℕ) (hw : ∀ w ∈ W, w < N+N+k) :
      ∃ S : Finset ℕ, S.card ≤ W.card+k ∧ ∀ w ∈ W, ∀ A ∈ F w, A ⊆ S := by
    induction k generalizing W with
    | zero =>
      refine ⟨W,by omega,?_⟩
      intro w mem A cert
      rw [leaves w (by simpa using hw w mem)] at cert
      have : A = {w} := Set.mem_singleton_iff.mp cert
      simpa [this] using mem
    | succ k ih =>
      let w := N+N+k
      by_cases use : w ∈ W
      · obtain ⟨a,ha,b,hb,parent⟩ := propagate k (by omega)
        let U := insert a (insert b (W.erase w))
        have bounds : ∀ u ∈ U, u < w := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl|h
          · exact ha
          rcases Finset.mem_insert.mp h with rfl|h
          · exact hb
          obtain ⟨ne,inc⟩ := Finset.mem_erase.mp h
          have bound := hw u inc
          change u ≠ N+N+k at ne
          change u < N+N+k
          omega
        obtain ⟨S,c,dep⟩ := ih (by omega) U bounds
        have uc : U.card ≤ W.card+1 := by
          have c1 := Finset.card_insert_le a (insert b (W.erase w))
          have c2 := Finset.card_insert_le b (W.erase w)
          rw [Finset.card_erase_of_mem use] at c2
          have := Finset.card_pos.mpr ⟨_,use⟩
          dsimp [U]; omega
        refine ⟨S,by omega,?_⟩
        intro u hu A cert v hv
        by_cases eq : u=w
        · subst u
          obtain ⟨B,anc,hv'⟩ := parent A cert v hv
          rcases anc with h|h
          · exact dep a (by simp [U]) B h hv'
          · exact dep b (by simp [U]) B h hv'
        · exact dep u (by simp [U,eq,hu]) A cert hv
      · have bounds : ∀ u ∈ W, u < w := by
          intro u hu
          have ne : u ≠ w := fun eq => use (eq ▸ hu)
          have bound := hw u hu
          change u ≠ N+N+k at ne
          change u < N+N+k
          omega
        obtain ⟨S,c,h⟩ := ih (by omega) W bounds
        exact ⟨S,by omega,h⟩
  obtain ⟨S,card,dep⟩ := reach s le_rfl {o} (by simpa using ho)
  have allBits : Finset.range (N+N) ⊆ S := by
    intro v hv
    have bound := Finset.mem_range.mp hv
    by_cases point : v < N
    · let p : Fin N := ⟨v,point⟩
      have big : 2 ≤ N := by nlinarith [Nat.zero_le (q^2)]
      let p' : Fin N := if p.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
      have ne : p ≠ p' := by
        intro e
        have eq := congrArg Fin.val e
        unfold p' at eq
        split at eq
        · change p.val = 1 at eq; omega
        · change p.val = 0 at eq; contradiction
      obtain ⟨l,hl,_⟩ := unique p p' ne
      obtain ⟨A,hA,eq⟩ := saturated {l} (by simp; omega)
      exact dep o (by simp) A hA ((eq p).1.mpr ⟨l,by simp,hl.1⟩)
    · let l : Fin N := ⟨v-N,by omega⟩
      obtain ⟨A,hA,eq⟩ := saturated ∅ (by simp)
      have inc := dep o (by simp) A hA ((eq l).2.mpr (by simp))
      have e : N+l.val=v := by dsimp [l]; omega
      exact e ▸ inc
  have count := Finset.card_le_card allBits
  simp only [Finset.card_range] at count
  simp only [Finset.card_singleton] at card
  have qmax : q ≤ 199 := by omega
  have := Nat.mul_le_mul_left N qmax
  have nn : 100 ≤ N := by nlinarith [Nat.zero_le (q^2)]
  omega
