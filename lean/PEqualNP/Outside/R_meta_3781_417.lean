import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3781_417
    (points : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 200 ≤ q →
      N = q^2 + q + 1 → (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → q % 2 = 0 →
      ∀ (s o : ℕ) (X : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
      let m := N+N
      let e := fun (p r : Fin N) => decide (r = p)
      let S := fun (b : Bool) (w : ℕ) => {p : Fin N |
        (if b then (e p,fun _ => false) else (fun _ => false,e p)) ∈ X w}
      let U := fun b w => ∃ a < w, ∃ c < w, S b w = S b a ∪ S b c
      o < m+s →
      (∀ p : Fin N, X p.val = {x | x.1 p = true} ∧ X (N+p.val) = {x | x.2 p = true}) →
      (∀ j < s, ∃ a < m+j, ∃ b < m+j, X (m+j) ∈ [X a ∪ X b, X a, ∅, X a ∩ X b]) →
      (∀ p l, I p l → (e p,e l) ∈ X o) →
      (∀ y : Fin N → Bool, Fintype.card {l : Fin N // y l = true} ≤ q →
        (fun p => decide (¬∃ l, I p l ∧ y l = true),y) ∉ X o) →
      (∃ j < s, ∃ a < m+j, ∃ b < m+j,
        X (m+j) = X a ∩ X b ∧ 3 ≤ (S true (m+j)).ncard ∧
        S true (m+j) ⊂ S true a ∧ S true (m+j) ⊂ S true b ∧ ¬ U true (m+j) ∧
        ∀ i < j, ∀ c, (S c (m+i)).ncard ≤ 1 ∨ U c (m+i)) → N*q ≤ 100*s)
    (lines : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 200 ≤ q →
      N = q^2 + q + 1 → (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → q % 2 = 0 →
      ∀ (s o : ℕ) (X : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
      let m := N+N
      let e := fun (p r : Fin N) => decide (r = p)
      let S := fun (b : Bool) (w : ℕ) => {p : Fin N |
        (if b then (e p,fun _ => false) else (fun _ => false,e p)) ∈ X w}
      let U := fun b w => ∃ a < w, ∃ c < w, S b w = S b a ∪ S b c
      o < m+s →
      (∀ p : Fin N, X p.val = {x | x.1 p = true} ∧ X (N+p.val) = {x | x.2 p = true}) →
      (∀ j < s, ∃ a < m+j, ∃ b < m+j, X (m+j) ∈ [X a ∪ X b, X a, ∅, X a ∩ X b]) →
      (∀ p l, I p l → (e p,e l) ∈ X o) →
      (∀ y : Fin N → Bool, Fintype.card {l : Fin N // y l = true} ≤ q →
        (fun p => decide (¬∃ l, I p l ∧ y l = true),y) ∉ X o) →
      (∃ j < s, ∃ a < m+j, ∃ b < m+j,
        X (m+j) = X a ∩ X b ∧ 3 ≤ (S false (m+j)).ncard ∧
        S false (m+j) ⊂ S false a ∧ S false (m+j) ⊂ S false b ∧ ¬ U false (m+j) ∧
        ∀ i < j, ∀ c, (S c (m+i)).ncard ≤ 1 ∨ U c (m+i)) → N*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           x1 % (2 : ℕ) = (0 : ℕ) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               x11 < x13 + x10 →                 (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →                   (∀ x17 < x10, ∃ (x19 : ℕ) (x20 : ℕ), Max.max x19 x20 < x13 + x17 ∧ x12 (x13 + x17) ∈ [x12 x19 ∪ x12 x20, x12 x19, ∅, x12 x19 ∩ x12 x20]) →                     (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x11) →                       (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x11) →                         (have x20 : Bool → ℕ → Set (Fin x2) := fun (x20 : Bool) (x21 : ℕ) => {x22 : Fin x2 | (if x20 = Bool.true then (x14 x22, fun (x23 : Fin x2) => Bool.false) else (fun (x23 : Fin x2) => Bool.false, x14 x22)) ∈ x12 x21};                           ∃ x21 < x10, ∃ (x22 : Bool) (x23 : Fin x2) (x24 : Fin x2), x23 ≠ x24 ∧ x23 ∈ x20 x22 (x13 + x21) ∧ x24 ∈ x20 x22 (x13 + x21) ∧ ¬∃ x25 < x13 + x21, ∃ x26 < x13 + x21, x20 x22 (x13 + x21) = x20 x22 x25 ∪ x20 x22 x26) →                           x2 * x1 ≤ (100 : ℕ) * x10 := by
  classical
  intro q N I inst qmin plane degrees together even s o X m e out input law accepts rejects event
  have gates (j : ℕ) (hj : j < s) : ∃ a < m+j, ∃ b < m+j,
      X (m+j) ∈ [X a ∪ X b, X a, ∅, X a ∩ X b] := by
    obtain ⟨a,b,small,valid⟩ := law j hj
    exact ⟨a,(le_max_left _ _).trans_lt small,b,(le_max_right _ _).trans_lt small,valid⟩
  by_cases large : 200 ≤ q
  · let S (b : Bool) (w : ℕ) : Set (Fin N) := {p |
      (if b then (e p,fun _ => false) else (fun _ => false,e p)) ∈ X w}
    let U (b : Bool) (w : ℕ) := ∃ a < w, ∃ c < w, S b w = S b a ∪ S b c
    let Bad (j : ℕ) := j < s ∧ ∃ b : Bool, 2 ≤ (S b (m+j)).ncard ∧ ¬ U b (m+j)
    have card2 (T : Set (Fin N)) (a b : Fin N) (ha : a ∈ T) (hb : b ∈ T) (ne : a ≠ b) :
        2 ≤ T.ncard := by
      have sub : ({a,b} : Set (Fin N)) ⊆ T := by
        intro p hp
        rcases Set.mem_insert_iff.mp hp with rfl | hp
        · exact ha
        · rwa [Set.mem_singleton_iff.mp hp]
      simpa only [Set.ncard_pair ne] using Set.ncard_le_ncard sub
    have existsBad : ∃ j, Bad j := by
      obtain ⟨j,jlt,b,p,r,ne,hp,hr,missing⟩ := event
      exact ⟨j,jlt,b,card2 _ p r hp hr ne,missing⟩
    let j := Nat.find existsBad
    obtain ⟨jlt,b,atLeastTwo,missing⟩ := Nat.find_spec existsBad
    change j < s at jlt
    change 2 ≤ (S b (m+j)).ncard at atLeastTwo
    change ¬ U b (m+j) at missing
    have previous (i : ℕ) (hi : i < j) (c : Bool) : (S c (m+i)).ncard ≤ 1 ∨ U c (m+i) := by
      by_cases withUnion : U c (m+i)
      · exact Or.inr withUnion
      by_contra! false
      have prior : Bad i := ⟨by omega,c,by omega,withUnion⟩
      exact (Nat.not_le_of_lt hi) (Nat.find_min' existsBad prior)
    let pin (c : Bool) (p : Fin N) := if c then p.val else N+p.val
    have before (c : Bool) (p : Fin N) : pin c p < m+j := by
      have h := p.isLt
      cases c <;> simp [pin,m] <;> omega
    have alone (c : Bool) (p : Fin N) : S c (pin c p) = {p} := by
      ext r
      cases c
      · change (fun _ => false,e r) ∈ X (N+p.val) ↔ r ∈ ({p} : Set (Fin N))
        rw [(input p).2]
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, e, decide_eq_true_eq]
        exact eq_comm
      · change (e r,fun _ => false) ∈ X p.val ↔ r ∈ ({p} : Set (Fin N))
        rw [(input p).1]
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, e, decide_eq_true_eq]
        exact eq_comm
    have atLeastThree : 3 ≤ (S b (m+j)).ncard := by
      by_contra! small
      obtain ⟨p,r,hp,hr,ne⟩ := (Set.one_lt_ncard_iff (s := S b (m+j))).mp (by omega : 1 < (S b (m+j)).ncard)
      have sub : ({p,r} : Set (Fin N)) ⊆ S b (m+j) := by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact hp
        · rwa [Set.mem_singleton_iff.mp hu]
      have equal : ({p,r} : Set (Fin N)) = S b (m+j) :=
        Set.eq_of_subset_of_ncard_le sub (by rw [Set.ncard_pair ne]; omega)
      apply missing
      refine ⟨pin b p,before b p,pin b r,before b r,?_⟩
      rw [alone,alone,← equal]
      ext a; simp [or_comm]
    have notCopy (k : ℕ) (hk : k < m+j) : S b (m+j) ≠ S b k := by
      intro eq
      apply missing
      exact ⟨k,hk,k,hk,by simpa only [Set.union_self] using eq⟩
    obtain ⟨a,ha,c,hc,form⟩ := gates j jlt
    simp only [List.mem_cons,List.not_mem_nil,or_false] at form
    have strict : X (m+j) = X a ∩ X c := by
      rcases form with union | copy | empty | inter
      · apply False.elim (missing ⟨a,ha,c,hc,?_⟩)
        ext z
        change (_ ∈ X (m+j)) ↔ (_ ∈ X a ∨ _ ∈ X c)
        simp only [union,Set.mem_union]
      · apply False.elim (notCopy a ha ?_)
        ext z
        change (_ ∈ X (m+j)) ↔ (_ ∈ X a)
        rw [copy]
      · have h : S b (m+j) = ∅ := by
          ext z
          change (_ ∈ X (m+j)) ↔ False
          simp [empty]
        rw [h, Set.ncard_empty] at atLeastTwo
        omega
      · exact inter
    have left : S b (m+j) ⊂ S b a := by
      refine Set.ssubset_iff_subset_ne.mpr ⟨?_,notCopy a ha⟩
      intro z hz
      change _ ∈ X (m+j) at hz
      rw [strict] at hz
      exact hz.1
    have right : S b (m+j) ⊂ S b c := by
      refine Set.ssubset_iff_subset_ne.mpr ⟨?_,notCopy c hc⟩
      intro z hz
      change _ ∈ X (m+j) at hz
      rw [strict] at hz
      exact hz.2
    cases b
    · exact lines q N I large plane degrees together even s o X out input gates accepts rejects
        ⟨j,jlt,a,ha,c,hc,strict,atLeastThree,left,right,missing,previous⟩
    · exact points q N I large plane degrees together even s o X out input gates accepts rejects
        ⟨j,jlt,a,ha,c,hc,strict,atLeastThree,left,right,missing,previous⟩
  have expand (k : ℕ) (hk : k ≤ s) (V : Finset ℕ) (bound : ∀ w ∈ V, w < m+k) :
      ∃ T : Finset ℕ, T.card ≤ V.card+k ∧ (∀ u ∈ T, u < m) ∧ ∀ z z' : (Fin N → Bool) × (Fin N → Bool),
        (∀ i ∈ T, z ∈ X i → z' ∈ X i) → ∀ w ∈ V, z ∈ X w → z' ∈ X w := by
    induction k generalizing V with
    | zero => exact ⟨V,by omega,(by simpa using bound),fun z z' h => h⟩
    | succ k ih =>
      let w := m+k
      by_cases hit : w ∈ V
      · obtain ⟨a,ha,b,hb,form⟩ := gates k (by omega)
        let P := insert a (insert b (V.erase w))
        have prior : ∀ i ∈ P, i < m+k := by
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact ha
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hb
          have ne := (Finset.mem_erase.mp hi).1
          have index := bound i (Finset.mem_erase.mp hi).2
          change i ≠ m+k at ne
          omega
        obtain ⟨T,size,primitive,control⟩ := ih (by omega) P prior
        have cardP : P.card ≤ V.card+1 := by
          have f := Finset.card_insert_le a (insert b (V.erase w))
          have g := Finset.card_insert_le b (V.erase w)
          rw [Finset.card_erase_of_mem hit] at g
          have vcpos : 0 < V.card := Finset.card_pos.mpr ⟨_,hit⟩
          change (insert a (insert b (V.erase w))).card ≤ _
          omega
        refine ⟨T,by omega,primitive,?_⟩
        intro z z' inp i hi zi
        have first := control z z' inp a (by simp [P])
        have second := control z z' inp b (by simp [P])
        by_cases eq : i = w
        · subst i
          change z ∈ X (m+k) at zi
          change z' ∈ X (m+k)
          simp only [List.mem_cons,List.not_mem_nil,or_false] at form
          rcases form with union | copy | empty | inter
          · rw [union] at zi ⊢
            exact zi.elim (fun h => Or.inl (first h)) (fun h => Or.inr (second h))
          · rw [copy] at zi ⊢
            exact first zi
          · rw [empty] at zi
            exact False.elim zi
          · rw [inter] at zi ⊢
            exact ⟨first zi.1,second zi.2⟩
        · exact control z z' inp i (by simp [P,eq,hi]) zi
      · have prior : ∀ i ∈ V, i < m+k := by
          intro i hi
          have ne : i ≠ m+k := by
            intro eq
            apply hit
            change m+k ∈ V
            rwa [← eq]
          have hi' := bound i hi
          omega
        obtain ⟨T,size,primitive,h⟩ := ih (by omega) V prior
        exact ⟨T,by omega,primitive,h⟩
  obtain ⟨T,count,primitive,control⟩ := expand s le_rfl {o} (by simpa using out)
  have hitAll : Finset.range m ⊆ T := by
    intro w hw
    have wm := Finset.mem_range.mp hw
    by_contra missing
    by_cases isPoint : w < N
    · let p : Fin N := ⟨w,isPoint⟩
      have two : 2 ≤ N := by nlinarith [Nat.zero_le (q^2)]
      let r : Fin N := if p.val = 0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
      have distinct : p ≠ r := by
        intro eq
        have vals := congrArg Fin.val eq
        unfold r at vals
        split at vals
        · change p.val = 1 at vals
          omega
        · rename_i hz
          change p.val = 0 at vals
          exact hz vals
      obtain ⟨l,inc,_⟩ := together p r distinct
      have small : Fintype.card {l' : Fin N // e l l' = true} ≤ q := by
        simpa [Fintype.card_subtype,e] using (show 1 ≤ q by omega)
      apply rejects (e l) small
      refine control _ _ ?_ o (by simp) (accepts p l inc.1)
      intro u ut hu
      by_cases first : u < N
      · let a : Fin N := ⟨u,first⟩
        rw [(input a).1] at hu ⊢
        have eq : a = p := of_decide_eq_true hu
        have equal : u = w := congrArg Fin.val eq
        rw [equal] at ut
        exact False.elim (missing ut)
      · have inRange := primitive u ut
        let a : Fin N := ⟨u-N,by dsimp [m] at inRange; omega⟩
        have index : u = N+a.val := by dsimp [a]; omega
        rw [index,(input a).2] at hu ⊢
        exact hu
    · let l : Fin N := ⟨w-N,by dsimp [m] at wm; omega⟩
      have index : w = N+l.val := by dsimp [l]; omega
      have nonempty : Nonempty {p : Fin N // I p l} := Fintype.card_pos_iff.mp (by rw [degrees]; omega)
      obtain ⟨⟨p,inc⟩⟩ := nonempty
      let noLines : Fin N → Bool := fun _ => false
      have small : Fintype.card {l' : Fin N // noLines l' = true} ≤ q := by simp [noLines]
      apply rejects noLines small
      refine control _ _ ?_ o (by simp) (accepts p l inc)
      intro u ut hu
      by_cases first : u < N
      · let a : Fin N := ⟨u,first⟩
        rw [(input a).1]
        change decide (¬∃ k, I a k ∧ noLines k = true) = true
        simp [noLines]
      · have inRange := primitive u ut
        let a : Fin N := ⟨u-N,by dsimp [m] at inRange; omega⟩
        have equals : u = N+a.val := by dsimp [a]; omega
        rw [equals,(input a).2] at hu
        have eqa : a = l := of_decide_eq_true hu
        have equal : u = w := equals.trans ((congrArg (fun l : Fin N => N+l.val) eqa).trans index.symm)
        exact False.elim (missing (equal ▸ ut))
  have size := Finset.card_le_card hitAll
  simp only [Finset.card_range] at size
  simp only [Finset.card_singleton] at count
  have top : q ≤ 199 := by omega
  have := Nat.mul_le_mul_left N top
  have nLarge : 100 ≤ N := by nlinarith [Nat.zero_le (q^2)]
  dsimp [m] at size
  omega
