import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5102_937
 (compile : ∀ (Q : Type) (J : Bool → Q → Q → Q) (pack : Q → Nat),
  (∀ o a b, pack (J o a b) = if o then pack a ||| pack b else pack a &&& pack b) →
  ∀ (s p : List Q) (d : Nat), (∀ i : Fin p.length, ∃ a ∈ s ++ p.take i.val, ∃ b ∈ s ++ p.take i.val, ∃ o : Bool, p.get i = J o a b) →
  ∃ gs : List (Bool × Nat × Nat), gs.length = p.length ∧
    gs.foldl (fun (w : List Nat) (g : Bool × Nat × Nat) => w ++ [if g.1 then w.getD g.2.1 d ||| w.getD g.2.2 d else w.getD g.2.1 d &&& w.getD g.2.2 d]) (s.map pack) = (s ++ p).map pack)
 (front : let S := ([917681504273,14878052356,31886295704066,257731462272,42884715528480,82789891049544,248671168364547,198670308868108,158476001083504,238332533539200,176488259259904,212188564320256,280375465312256,271282175737871,280357743624591] : List Nat).map (fun (n : Nat) => (BitVec.ofNat 18 n, BitVec.ofNat 30 (n / 262144)))
 let J := fun (o : Bool) (a b : (BitVec 18 × BitVec 30)) => if o then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
 ∃ k ∈ ([31,61,91,127,180,181,187,211,240,241,247,253,271,276,277,283,287,301,306,307,317,347,391,397,407,421,427,437] : List Nat),
   let s := S ++ [J (k % 2 == 1) (S[k / 2 % 15]!) (S[k / 30]!)]
   ∃ p : List (BitVec 18 × BitVec 30), p.length ≤ 19 ∧ (∀ i : Fin p.length, ∃ a ∈ s ++ p.take i.val, ∃ b ∈ s ++ p.take i.val, ∃ o : Bool, p.get i = J o a b) ∧
     let w := s ++ p
     ∃ a ∈ w, ∃ b ∈ w, ∃ c ∈ w, ∃ o : Bool,
       let v := J o a b
       (v.2 = 0 ∧ c.2 = 0 ∧ v.1 ||| c.1 = -1) ∨
       (v.1 = -1 ∧ c.1 = -1 ∧ v.2 &&& c.2 = 0)) :
have x1 : List ℕ → List (Bool × ℕ × ℕ) → ℕ → ℕ := fun (x1 : List ℕ) (x2 : List (Bool × ℕ × ℕ)) (x3 : ℕ) =>   have x4 : ℕ := x1.headD (0 : ℕ);   (List.foldl         (fun (x5 : List ℕ) (x6 : Bool × ℕ × ℕ) =>           have x7 : ℕ → ℕ := fun (x7 : ℕ) => x5.getD x7 x4;           x5 ++ [if x6.1 = Bool.true then x7 x6.2.1 ||| x7 x6.2.2 else x7 x6.2.1 &&& x7 x6.2.2])         x1 x2).getD     x3 x4; have x2 : List ℕ := [(917681504273 : ℕ), (14878052356 : ℕ), (31886295704066 : ℕ), (257731462272 : ℕ), (42884715528480 : ℕ), (82789891049544 : ℕ), (248671168364547 : ℕ), (198670308868108 : ℕ), (158476001083504 : ℕ), (238332533539200 : ℕ), (176488259259904 : ℕ), (212188564320256 : ℕ), (280375465312256 : ℕ), (271282175737871 : ℕ), (280357743624591 : ℕ)]; ∃ (x3 : List (Bool × ℕ × ℕ)), x3.length ≤ (22 : ℕ) ∧ ∃ (x4 : ℕ), x1 x2 x3 x4 = (262143 : ℕ) := by
  let S : List Nat := [917681504273,14878052356,31886295704066,257731462272,42884715528480,82789891049544,248671168364547,198670308868108,158476001083504,238332533539200,176488259259904,212188564320256,280375465312256,271282175737871,280357743624591]
  let split := fun (n : Nat) => (BitVec.ofNat 18 n, BitVec.ofNat 30 (n / 262144))
  let pack := fun (a : (BitVec 18 × BitVec 30)) => (a.2 ++ a.1).toNat
  let J := fun (o : Bool) (a b : (BitVec 18 × BitVec 30)) => if o then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
  let d := S.headD 0
  let step := fun (w : List Nat) (g : Bool × Nat × Nat) => w ++ [if g.1 then w.getD g.2.1 d ||| w.getD g.2.2 d else w.getD g.2.1 d &&& w.getD g.2.2 d]
  have hop (o : Bool) (a b : BitVec 18 × BitVec 30) :
      pack (J o a b) = if o then pack a ||| pack b else pack a &&& pack b := by
    rcases a with ⟨l1,h1⟩
    rcases b with ⟨l2,h2⟩
    cases o
    · change ((h1 &&& h2) ++ (l1 &&& l2)).toNat = (h1 ++ l1).toNat &&& (h2 ++ l2).toNat
      rw [← BitVec.and_append, BitVec.toNat_and]
    · change ((h1 ||| h2) ++ (l1 ||| l2)).toNat = (h1 ++ l1).toNat ||| (h2 ++ l2).toNat
      rw [← BitVec.or_append, BitVec.toNat_or]
  let U := S.map split
  obtain ⟨k, hk, p, hp, hmid, a, ha, b, hb, c, hc, o, hterm⟩ := front
  let g : Bool × Nat × Nat := (k % 2 == 1,k / 2 % 15,k / 30)
  let aux := J g.1 (U[g.2.1]!) (U[g.2.2]!)
  let s := U ++ [aux]
  have hseed : step S g = s.map pack := by
    have h : ∀ k ∈ ([31,61,91,127,180,181,187,211,240,241,247,253,271,276,277,283,287,301,306,307,317,347,391,397,407,421,427,437] : List Nat),
      step S (k % 2 == 1,k / 2 % 15,k / 30) =
        (U ++ [J (k % 2 == 1) (U[k / 2 % 15]!) (U[k / 30]!)]).map pack := by
      decide +kernel
    exact h k hk
  let v := J o a b
  let z : BitVec 18 × BitVec 30 := (-1,0)
  have hm : ∀ i : Fin p.length, ∃ x ∈ s ++ p.take i.val, ∃ y ∈ s ++ p.take i.val,
        ∃ f : Bool, p.get i = J f x y := hmid
  change a ∈ s ++ p at ha
  change b ∈ s ++ p at hb
  change c ∈ s ++ p at hc
  change (v.2 = 0 ∧ c.2 = 0 ∧ v.1 ||| c.1 = -1) ∨
         (v.1 = -1 ∧ c.1 = -1 ∧ v.2 &&& c.2 = 0) at hterm
  have hex : ∃ f : Bool, z = J f v c := by
    rcases hterm with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
    · exact ⟨true, Prod.ext (by simpa [z,J] using h3.symm) (by simp [z,J,h1,h2])⟩
    · exact ⟨false, Prod.ext (by simp [z,J,h1,h2]) (by simpa [z,J] using h3.symm)⟩
  obtain ⟨f,hf⟩ := hex
  have tail : ∀ i : Fin (p ++ [v,z]).length,
      ∃ x ∈ s ++ (p ++ [v,z]).take i.val, ∃ y ∈ s ++ (p ++ [v,z]).take i.val,
      ∃ op : Bool, (p ++ [v,z]).get i = J op x y := by
    intro i
    by_cases h : i.val < p.length
    · obtain ⟨x,hx,y,hy,t,ht⟩ := hm ⟨i.val,h⟩
      rw [List.take_append_of_le_length (Nat.le_of_lt h)]
      exact ⟨x,hx,y,hy,t,by simpa [List.get_eq_getElem, List.getElem_append_left h] using ht⟩
    · have hi := i.isLt
      simp at hi
      have h' : i.val = p.length ∨ i.val = p.length+1 := by omega
      rcases h' with he | he
      · refine ⟨a,?_,b,?_,o,?_⟩
        · simpa [he] using ha
        · simpa [he] using hb
        · simp [List.get_eq_getElem, he, v]
      · refine ⟨v,?_,c,?_,f,?_⟩
        · simp [he,List.take_append]
        · simp only [he,List.take_append, List.take_of_length_le (by omega : p.length ≤ p.length+1)]
          simp [List.mem_append] at hc ⊢
          exact hc.elim Or.inl (fun h => Or.inr (Or.inl h))
        · simpa [List.get_eq_getElem, he, List.getElem_append_right (by omega : p.length ≤ i.val)] using hf
  obtain ⟨gs, hl, hs⟩ := compile _ J pack hop s (p++[v,z]) d tail
  change ∃ instr : List (Bool × Nat × Nat), instr.length ≤ 22 ∧
    ∃ i, (instr.foldl step S).getD i d = 262143
  refine ⟨g::gs, ?_, (s++p++[v]).length, ?_⟩
  · simp at hl
    simp only [List.length_cons]
    omega
  · change (gs.foldl step (step S g)).getD _ d = _
    rw [hseed]
    change gs.foldl step (s.map pack) = _ at hs
    rw [hs]
    have : ((s++(p++[v,z])).map pack) = (s++p++[v]).map pack ++ [pack z] := by simp [List.append_assoc]
    rw [this]
    simp [List.getD, pack, z]
