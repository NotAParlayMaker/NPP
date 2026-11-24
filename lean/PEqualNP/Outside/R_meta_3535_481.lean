import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3535_481
    (transport : let gate := fun (w : List Nat) (z : Nat) => ∃ a∈w, ∃ b∈w, z=a&&&b ∨ z=a|||b
    let builds := fun (s p : List Nat) => ∀ i : Fin p.length, gate (s++p.take i.val) (p.get i)
    ∀ R : Nat → Nat → Prop,
      (∀ {u v x y}, R u x → R v y → R (u&&&v) (x&&&y) ∧ R (u|||v) (x|||y)) →
      let sim := fun (s t : List Nat) => ∀ x∈s, ∃ y∈t, R x y
      ∀ ps s t : List Nat, sim s t → builds s ps →
        ∃ qs : List Nat, qs.length = ps.length ∧ builds t qs ∧ sim (s++ps) (t++qs))
    (search : let S : List Nat := [152087017553927, 213868587515960, 179307129340352, 224404491472384, 264019155906560, 281337537986560, 93086069030977, 123862810632, 995430402, 4260640858624, 16110191744, 13606557860112, 54031766784036, 93174464544841, 96747896218185]
    ∃ p : List Nat, p.length ≤ 22 ∧ 262143 ∈ S++p ∧
      ∃ (a b : Fin p.length → Nat) (op : Fin p.length → Bool),
        (∀ i, a i ∈ S++p.take i.val ∧ b i ∈ S++p.take i.val ∧
          p.get i = if op i then a i &&& b i else a i ||| b i) ∧
        6 ≤ (List.ofFn op).count true ∧
        ∃ i j : Fin p.length, i < j ∧ ∃ v ∈ p.take i.val, v ∉ S ∧
          (a i = v ∨ b i = v) ∧ (a j = v ∨ b j = v)) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)] ++ [(191866593364673099 : ℕ), (193001360500003407 : ℕ), (7 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (22 : ℕ) ∧ (∃ x3 ∈ x1 ++ x2, x3 ||| (7 : ℕ) = (2097151 : ℕ)) ∧ ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5 := by
  let gate (w : List Nat) (z : Nat) : Prop := ∃ a∈w, ∃ b∈w, z=a&&&b ∨ z=a|||b
  let builds (s p : List Nat) : Prop := ∀ i : Fin p.length, gate (s++p.take i.val) (p.get i)
  have cons (s : List Nat) (x : Nat) (p : List Nat) :
      builds s (x::p) ↔ gate s x ∧ builds (s++[x]) p := by
    constructor
    · intro h
      refine ⟨?_,?_⟩
      · simpa [gate] using h ⟨0,by simp⟩
      · rintro ⟨j,hj⟩
        simpa only [List.take_succ_cons,List.get_eq_getElem,List.getElem_cons_succ,List.append_assoc,List.cons_append,List.nil_append]
          using h ⟨j+1,by simpa using hj⟩
    · rintro ⟨hx,hp⟩ ⟨i,hi⟩
      cases i with
      | zero => simpa using hx
      | succ n =>
        simpa only [List.take_succ_cons,List.get_eq_getElem,List.getElem_cons_succ,List.append_assoc,List.cons_append,List.nil_append]
          using hp ⟨n,by simpa using hi⟩
  have bounds (s p : List Nat) (n : Nat) (hs : ∀ x∈s,x<2^n) (hb : builds s p) :
      ∀ x ∈ s++p, x<2^n := by
    induction p generalizing s with
    | nil => simpa using hs
    | cons y p ih =>
      obtain ⟨⟨a,ha,b,hsb,hv⟩,rest⟩ := (cons s y p).mp hb
      have hy : y < 2^n := by
        rcases hv with rfl|rfl
        · exact Nat.and_lt_two_pow _ (hs b hsb)
        · exact Nat.or_lt_two_pow (hs a ha) (hs b hsb)
      have hh := ih (s++[y]) (fun z hz => (List.mem_append.mp hz).elim (hs z) (fun h => (List.mem_singleton.mp h) ▸ hy)) rest
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using hh
  let signed {n : Nat} (a b : Fin n → Nat) (p : Fin n → Bool) (x y : Nat) : Prop :=
    ∀ i, x.testBit (a i) = p i → y.testBit (b i) = p i
  have combine {n : Nat} {a b : Fin n → Nat} {p : Fin n → Bool} {u v x y : Nat}
      (hu : signed a b p u x) (hv : signed a b p v y) :
      signed a b p (u&&&v) (x&&&y) ∧ signed a b p (u|||v) (x|||y) := by
    have C : ∀ (t a b c d : Bool), (a=t → c=t) → (b=t → d=t) →
        ((a&&b)=t → (c&&d)=t) ∧ ((a||b)=t → (c||d)=t) := by decide
    constructor <;> intro i
    · simpa only [Nat.testBit_and] using (C _ _ _ _ _ (hu i) (hv i)).1
    · simpa only [Nat.testBit_or] using (C _ _ _ _ _ (hu i) (hv i)).2
  let sim (R : Nat → Nat → Prop) (s t : List Nat) : Prop := ∀ x∈s, ∃ y∈t, R x y
  let orig : List Nat := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]++[191866593364673099,193001360500003407,7]
  let compressed : List Nat := [152087017553927, 213868587515960, 179307129340352, 224404491472384, 264019155906560, 281337537986560, 93086069030977, 123862810632, 995430402, 4260640858624, 16110191744, 13606557860112, 54031766784036, 93174464544841, 96747896218185]
  let recover (j : Fin 55) := ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 47, 46, 36, 35, 29, 27, 28, 41, 39, 23, 24, 33, 32, 31, 20, 21, 20, 43, 42, 26, 25, 25, 38, 19, 19, 45, 44, 34, 22, 40, 22, 30, 30, 37, 37, 18, 18] : List Nat).getD j.val 0
  let bit55 (j : Fin 55) := decide (j.val<18)
  let src55 (j : Fin 55) := 3+j.val
  have rsim : sim (signed recover src55 bit55) compressed orig := by
    have cert : ∀ i : Fin 15, signed recover src55 bit55 (compressed.getD i.val 0) (orig.getD (i.val+1) 0) := by
      dsimp only [signed]
      decide +kernel
    intro v hv
    obtain ⟨i,rfl⟩ := List.get_of_mem hv
    have hi : i.val<15 := i.isLt
    have ho : i.val+1<orig.length := by change i.val+1<17; omega
    refine ⟨orig.getD (i.val+1) 0,?_,?_⟩
    · rw [List.getD_eq_getElem _ _ ho]
      exact List.getElem_mem _
    · simpa only [List.getD_eq_getElem _ _ i.isLt,List.get_eq_getElem] using cert ⟨i.val,hi⟩
  have rbits : ∀ i : Fin 55, (7:Nat).testBit (src55 i) = false ∧
      (2097151:Nat).testBit (src55 i)=bit55 i ∧ (262143:Nat).testBit (recover i)=bit55 i := by decide +kernel
  have small : ∀ i : Fin 3, (7:Nat).testBit i.val=true ∧ (2097151:Nat).testBit i.val=true := by decide
  have obounds : ∀ z∈orig,z<2^58 := by decide +kernel
  change ∃ p : List Nat, p.length≤22 ∧ (∃ x∈orig++p,x|||7=2097151) ∧ builds orig p
  obtain ⟨q,hq,ht,a,b,op,hg,_hcount,_hshare⟩ := search
  have bq : builds compressed q := by
    intro i
    obtain ⟨ha,hb,hv⟩ := hg i
    refine ⟨a i,ha,b i,hb,?_⟩
    cases h : op i
    · exact Or.inr (by simpa only [h,Bool.false_eq_true,ite_false] using hv)
    · exact Or.inl (by simpa only [h,ite_true] using hv)
  obtain ⟨p,hl,bp,hp⟩ := transport (signed recover src55 bit55) (fun hu hv => combine hu hv) q compressed orig rsim bq
  obtain ⟨y,hy,hs⟩ := hp _ ht
  refine ⟨p,by omega,⟨y,hy,?_⟩,bp⟩
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases low : i<3
  · obtain ⟨a,b⟩ := small ⟨i,low⟩
    change (7:Nat).testBit i=true at a
    change (2097151:Nat).testBit i=true at b
    rw [a,b,Bool.or_true]
  by_cases high : i<58
  · let j : Fin 55 := ⟨i-3,by omega⟩
    have id : src55 j=i := by change 3+(i-3)=i; omega
    rw [←id,(rbits j).1,Bool.or_false,(rbits j).2.1]
    exact hs j (rbits j).2.2
  · have pow : 2^58 ≤ (2:Nat)^i := Nat.pow_le_pow_right (by decide) (by omega)
    have yb := bounds orig p 58 obounds bp y hy
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le yb pow),Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 7<2^58) pow), Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 2097151<2^58) pow)]
    rfl
