import PEqualNP.Defs

-- Complementary truth tables share one representative, chosen by their bit on the all-zero row.
set_option maxRecDepth 18000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_3901_812
    (project : ∀ (gs : List (Fin 24 × Fin 24 × Bool × Bool)) (w : List (BitVec 512))
      (o : Fin 24) (r : Fin 512),
      let sign := fun (v : BitVec 512) (p : Bool) => if p then v else ~~~v
      ((gs.foldl (fun (w : List Bool) (g : Fin 24 × Fin 24 × Bool × Bool) =>
        w ++ [(w.getD g.1.val false == g.2.2.1) && (w.getD g.2.1.val false == g.2.2.2)]) (w.map fun v => v.getLsbD r.val)).getD o.val false) =
        ((gs.foldl (fun (w : List (BitVec 512)) (g : Fin 24 × Fin 24 × Bool × Bool) =>
        w ++ [sign (w.getD g.1.val 0) g.2.2.1 &&& sign (w.getD g.2.1.val 0) g.2.2.2]) w).getD o.val 0).getLsbD r.val)
    (certificate : let col := fun (i : ℕ) => BitVec.ofNat 512 (((2^512-1) / (2^(2^i)+1)) * 2^(2^i))
      let base := (List.range 9).map col ++ [col 0 ||| col 1, 0]
      let target := (([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).map
          (fun e => col (e / 10) &&& col (e % 10))).foldr (· ||| ·) 0
      let q := fun (v : BitVec 512) => if v.getLsbD 0 then ~~~v else v
      let sign := fun (v : BitVec 512) (p : Bool) => if p then v else ~~~v
      let add := fun (a b : BitVec 512) (p t : Bool) => q (sign a p &&& sign b t)
      let root := insert (0 : BitVec 512) (base.map q).toFinset
      let perm := fun (i : ℕ) => [1,0,5,8,6,2,4,7,3].getD i i
      ∃ keep : ℕ → Finset (BitVec 512) → Prop,
        (∀ (i j : Fin 24) (b : Bool), [i.val,j.val] ≤ [perm i.val,perm j.val] →
          keep 12 (insert (add (base.getD i.val 0) (base.getD j.val 0) false b) root)) ∧
        (∀ k S, keep (k+1) S → keep k S) ∧
        (∀ k S, keep (k+1) S → ∀ a ∈ S, ∀ b ∈ S, ∀ p t : Bool,
          add a b p t ∉ S → keep k (insert (add a b p t) S)) ∧
        (∀ S, keep 0 S → q target ∉ S)) :
    ∀ (x1 : List (Fin (24 : ℕ) × Fin (24 : ℕ) × Bool × Bool)),   x1.length ≤ (13 : ℕ) →     (∀ x3 ∈ x1.head?.toList,         x3.2.2.1 = Bool.false ∧           have x5 : ℕ → ℕ := fun (x5 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x5 x5;           [↑x3.1, ↑x3.2.1] ≤ [x5 ↑x3.1, x5 ↑x3.2.1]) →       ∀ (x4 : Fin (24 : ℕ)) (x5 : Bool),         ∃ (x6 : Fin (512 : ℕ)),           have x7 : Fin (9 : ℕ) → Bool := fun (x7 : Fin (9 : ℕ)) => (BitVec.ofNat (9 : ℕ) ↑x6).getLsbD ↑x7;           have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)), Bool.false];           ((List.foldl (fun (x9 : List Bool) (x10 : Fin (24 : ℕ) × Fin (24 : ℕ) × Bool × Bool) => x9 ++ [x9.getD (↑x10.1) Bool.false == x10.2.2.1 && x9.getD (↑x10.2.1) Bool.false == x10.2.2.2]) x8 x1).getD (↑x4) Bool.false != x5) ≠ ([(18440827511444797640 : ℕ), (18441957826578283724 : ℕ), (18446744073709222136 : ℕ), (18446744073709485308 : ℕ), (18446744073708175304 : ℕ), (18446744073709551615 : ℕ), (18446744073709223928 : ℕ), (18446744073709551615 : ℕ)].getD (↑x6 / (64 : ℕ)) (0 : ℕ)).testBit (↑x6 % (64 : ℕ)) := by
  classical
  let col := fun (i : ℕ) => BitVec.ofNat 512 (((2^512-1) / (2^(2^i)+1)) * 2^(2^i))
  let base := (List.range 9).map col ++ [col 0 ||| col 1, 0]
  let target := (([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).map
          (fun e => col (e / 10) &&& col (e % 10))).foldr (· ||| ·) 0
  let q := fun (v : BitVec 512) => if v.getLsbD 0 then ~~~v else v
  let sign := fun (v : BitVec 512) (p : Bool) => if p then v else ~~~v
  let add := fun (a b : BitVec 512) (p t : Bool) => q (sign a p &&& sign b t)
  let root := insert (0 : BitVec 512) (base.map q).toFinset
  let perm := fun (i : ℕ) => [1,0,5,8,6,2,4,7,3].getD i i
  let bs := fun (w : List Bool) (g : Fin 24 × Fin 24 × Bool × Bool) =>
        w ++ [(w.getD g.1.val false == g.2.2.1) && (w.getD g.2.1.val false == g.2.2.2)]
  let ws := fun (w : List (BitVec 512)) (g : Fin 24 × Fin 24 × Bool × Bool) =>
        w ++ [sign (w.getD g.1.val 0) g.2.2.1 &&& sign (w.getD g.2.1.val 0) g.2.2.2]
  obtain ⟨keep, start, drop, extend, finish⟩ := certificate
  have zeroQ : q 0 = 0 := rfl
  have flip (x : BitVec 512) : q (~~~x) = q x := by
    cases bit : x.getLsbD 0 <;> simp at bit <;> simp [q, bit]
  have chooseSign (x : BitVec 512) (p : Bool) : ∃ t, sign (q x) t = sign x p := by
    cases bit : x.getLsbD 0 <;> simp at bit <;> cases p
    · exact ⟨false, by simp [sign, q, bit]⟩
    · exact ⟨true, by simp [sign, q, bit]⟩
    · exact ⟨true, by simp [sign, q, bit]⟩
    · exact ⟨false, by simp [sign, q, bit]⟩
  have baseIn (x : BitVec 512) (hx : x ∈ base) : q x ∈ root := by
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩))
  have bottom (S : Finset (BitVec 512)) (k : ℕ) : keep k S → keep 0 S := by
    induction k with
    | zero => exact id
    | succ k ih => exact fun h => ih (drop k S h)
  have readIn {w : List (BitVec 512)} {S : Finset (BitVec 512)}
      (zero : 0 ∈ S) (contained : ∀ x ∈ w, q x ∈ S) (i : ℕ) : q (w.getD i 0) ∈ S := by
    by_cases hi : i < w.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact contained _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega), zeroQ]
      exact zero
  have safe (gs : List (Fin 24 × Fin 24 × Bool × Bool)) :
      ∀ (w : List (BitVec 512)) (S : Finset (BitVec 512)) (k : ℕ),
        gs.length ≤ k → 0 ∈ S → (∀ x ∈ w, q x ∈ S) → keep k S → ∀ o : Fin 24,
        q ((gs.foldl ws w).getD o.val 0) ≠ q target := by
    induction gs with
    | nil =>
      intro w S k _ zero inside valid o eq
      have used := readIn zero inside o.val
      change q (w.getD o.val 0) = q target at eq
      rw [eq] at used
      exact finish S (bottom S k valid) used
    | cons g gs ih =>
      intro w S k size zero inside valid o
      cases k with
      | zero => simp at size
      | succ k =>
        let a := w.getD g.1.val 0
        let b := w.getD g.2.1.val 0
        let z := sign a g.2.2.1 &&& sign b g.2.2.2
        obtain ⟨p, hp⟩ := chooseSign a g.2.2.1
        obtain ⟨t, ht⟩ := chooseSign b g.2.2.2
        have same : add (q a) (q b) p t = q z := by simp [add, hp, ht, z]
        have next : keep k (insert (q z) S) := by
          by_cases present : q z ∈ S
          · rw [Finset.insert_eq_of_mem present]
            exact drop k S valid
          · rw [← same] at present ⊢
            exact extend k S valid (q a) (readIn zero inside _) (q b) (readIn zero inside _) p t present
        apply ih (w ++ [z]) (insert (q z) S) k (by simpa using size)
          (Finset.mem_insert_of_mem zero) _ next o
        intro x hx
        rcases List.mem_append.mp hx with old | added
        · exact Finset.mem_insert_of_mem (inside x old)
        · exact List.mem_singleton.mp added ▸ Finset.mem_insert_self _ _
  let input := fun (r : Fin 512) (i : Fin 9) => (BitVec.ofNat 9 r.val).getLsbD i.val
  let seed := fun r : Fin 512 => List.ofFn (input r) ++ [input r 0 || input r 1, false]
  let chunks : List ℕ := [18440827511444797640,18441957826578283724,18446744073709222136,
    18446744073709485308,18446744073708175304,18446744073709551615,18446744073709223928,
    18446744073709551615]
  have seedRows : ∀ r : Fin 512, base.map (fun x => x.getLsbD r.val) = seed r := by
    decide +kernel
  have targetRows : ∀ r : Fin 512,
      target.getLsbD r.val = (chunks.getD (r.val / 64) 0).testBit (r.val % 64) := by
    decide +kernel
  intro gs bound head o p
  by_contra! agree
  let finalWord := (gs.foldl ws base).getD o.val 0
  have equalAt (r : Fin 512) : (finalWord.getLsbD r.val != p) = target.getLsbD r.val := by
    have er : ((gs.foldl bs (seed r)).getD o.val false != p) =
        (chunks.getD (r.val / 64) 0).testBit (r.val % 64) := not_not.mp (agree r)
    have projection := project gs base o r
    change (gs.foldl bs (base.map fun v => v.getLsbD r.val)).getD o.val false =
      finalWord.getLsbD r.val at projection
    rw [← seedRows r, projection, ← targetRows r] at er
    exact er
  have equalClass : q finalWord = q target := by
    cases p with
    | false =>
      apply congrArg q
      apply BitVec.eq_of_getLsbD_eq_iff.mpr
      intro i hi
      simpa using equalAt ⟨i, hi⟩
    | true =>
      have eq : ~~~finalWord = target := by
        apply BitVec.eq_of_getLsbD_eq_iff.mpr
        intro i hi
        simpa [BitVec.getLsbD_not, hi] using equalAt ⟨i, hi⟩
      exact (flip finalWord).symm.trans (congrArg q eq)
  cases gs with
  | nil =>
    have init := start (0 : Fin 24) (0 : Fin 24) true (by decide)
    exact safe [] base _ 12 (by simp)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      (fun x hx => Finset.mem_insert_of_mem (baseIn x hx)) init o equalClass
  | cons g rest =>
    have first := head g (by simp)
    change g.2.2.1 = false ∧ [g.1.val,g.2.1.val] ≤ [perm g.1.val,perm g.2.1.val] at first
    let z := sign (base.getD g.1.val 0) g.2.2.1 &&& sign (base.getD g.2.1.val 0) g.2.2.2
    have init : keep 12 (insert (q z) root) := by
      simpa only [z, first.1, add] using start g.1 g.2.1 g.2.2.2 first.2
    apply safe rest (base ++ [z]) (insert (q z) root) 12 (by simp only [List.length_cons] at bound; omega)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) _ init o equalClass
    intro x hx
    rcases List.mem_append.mp hx with old | added
    · exact Finset.mem_insert_of_mem (baseIn x old)
    · exact List.mem_singleton.mp added ▸ Finset.mem_insert_self _ _
