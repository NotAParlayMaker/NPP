import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 12000 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.R_meta_3077_41
    (h1 : ∀ (out : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)), tail.length ≤ 13 →
      (∀ v : ℕ, v < 9 → ∃ g ∈ tail, g.2.1.val = v ∨ g.2.2.val = v) →
      ∃ m : ℕ, m < 512 ∧
        let x := fun i : Fin 9 => m.testBit i.val
        let read := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
        let u := x 0 || x 4
        let w := tail.foldl (fun w g => w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
          else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1])
          (List.ofFn x ++ [u, u || x 1])
        w.getD out.val false ≠ ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (h2 : ∀ (out : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)), tail.length ≤ 13 →
      (∀ v : ℕ, v < 9 → ∃ g ∈ tail, g.2.1.val = v ∨ g.2.2.val = v) →
      ∃ m : ℕ, m < 512 ∧
        let x := fun i : Fin 9 => m.testBit i.val
        let read := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
        let u := x 0 || x 4
        let w := tail.foldl (fun w g => w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
          else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1])
          (List.ofFn x ++ [u, u || x 2])
        w.getD out.val false ≠ ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (h3 : ∀ (out : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)), tail.length ≤ 13 →
      (∀ v : ℕ, v < 9 → ∃ g ∈ tail, g.2.1.val = v ∨ g.2.2.val = v) →
      ∃ m : ℕ, m < 512 ∧
        let x := fun i : Fin 9 => m.testBit i.val
        let read := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
        let u := x 0 || x 4
        let w := tail.foldl (fun w g => w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
          else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1])
          (List.ofFn x ++ [u, u || x 3])
        w.getD out.val false ≠ ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (h6 : ∀ (out : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)), tail.length ≤ 13 →
      (∀ v : ℕ, v < 9 → ∃ g ∈ tail, g.2.1.val = v ∨ g.2.2.val = v) →
      ∃ m : ℕ, m < 512 ∧
        let x := fun i : Fin 9 => m.testBit i.val
        let read := fun (w : List Bool) (i : Fin 26) => if i.val = 25 then true else w.getD i.val false
        let u := x 0 || x 4
        let w := tail.foldl (fun w g => w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
          else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1])
          (List.ofFn x ++ [u, u || x 6])
        w.getD out.val false ≠ ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
    ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 = (9 : ℕ) ∨ ↑x2 = (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro a b out tail hlen anchor ha hb cover
  let row (m : Fin 512) (i : Fin 9) := m.val.testBit i.val
  let edge (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
  let step (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) :=
    w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
      else if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1]
  let u (x : Fin 9 → Bool) := x 0 || x 4
  let seed (k : Fin 9) (x : Fin 9 → Bool) := List.ofFn x ++ [u x, u x || x k]
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [u x]
  let p (i : Fin 9) : Fin 9 := ([0,5,8,3,4,1,7,6,2] : List (Fin 9)).getD i.val 0
  let flipped (m : Fin 512) : Fin 512 :=
    ⟨((List.finRange 9).foldl (fun n i => n + if row m (p i) then 2 ^ i.val else 0) 0) % 512,
     Nat.mod_lt _ (by decide)⟩
  have edgeOk : ∀ m, edge (row (flipped m)) = edge (row m) := by decide +kernel
  let other := if a.val = 9 then b else a
  have setup (x : Fin 9 → Bool) : step (base x) (1,a,b) = base x ++ [u x || read (base x) other] := by
    have e : read (base x) (9 : Fin 26) = u x := rfl
    rcases anchor with h | h
    · have ea : a = 9 := Fin.ext h
      subst a
      simp [step, other, e, h]
    · have eb : b = 9 := Fin.ext h
      subst b
      by_cases ea : a.val = 9
      · have eqa : a = 9 := Fin.ext ea
        subst a
        simp [step, other, e]
      · simp [step, other, ea, e, Bool.or_comm]
  have otherOk : other.val ≠ 25 := by simp only [other]; split <;> assumption
  let swap (j : Fin 26) : Bool := decide (j.val = 5 ∨ j.val = 7 ∨ j.val = 8)
  let dup (j : Fin 26) : Bool := decide (j.val = 0 ∨ j.val = 4 ∨ 9 ≤ j.val)
  let key (j : Fin 26) : Fin 9 := if j.val = 2 ∨ j.val = 8 then 2
    else if j.val = 3 then 3 else if j.val = 6 ∨ j.val = 7 then 6 else 1
  let ren (j i : Fin 26) : Fin 26 :=
    if h : i.val < 9 then if swap j then ⟨(p ⟨i.val,h⟩).val, Nat.lt_trans (p ⟨i.val,h⟩).isLt (by decide : 9 < 26)⟩ else i
    else if i.val = 10 ∧ dup j = true then 9 else i
  let trans (j : Fin 26) (m : Fin 512) := if swap j then flipped m else m
  have flipOk : ∀ m i, row (flipped m) i = row m (p i) := by decide +kernel
  have rowEq (j : Fin 26) (m : Fin 512) :
      row (trans j m) = fun i => if swap j then row m (p i) else row m i := by
    funext i
    cases hs : swap j <;> simp only [trans, hs, Bool.false_eq_true, ite_false, ite_true, flipOk]
  have firstEq (j : Fin 26) (m : Fin 512) : u (row (trans j m)) = u (row m) := by
    rw [rowEq]
    cases swap j <;> rfl
  have secondEq (j : Fin 26) (hj : j.val ≠ 25) (x : Fin 9 → Bool) :
      (u x || read (base (fun i => if swap j then x (p i) else x i)) j) =
      (if dup j then u x else u x || x (key j)) := by
    have values : ∀ i : Fin 26, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 := by decide
    rcases values j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact False.elim (hj rfl) | rfl
            | (change ((x 0 || x 4) || x 0) = (x 0 || x 4); cases x 0 <;> cases x 4 <;> rfl)
            | (change ((x 0 || x 4) || x 4) = (x 0 || x 4); cases x 0 <;> cases x 4 <;> rfl)
            | (change (u x || u x) = u x; cases u x <;> rfl)
            | (change (u x || false) = u x; cases u x <;> rfl)
  have rawget (x : Fin 9 → Bool) (z : List Bool) (i : ℕ) (hi : i < 9) :
      (List.ofFn x ++ z).getD i false = x ⟨i,hi⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi), List.getElem?_ofFn]
    simp [hi]
  have seedRel (j : Fin 26) (hj : j.val ≠ 25) (m : Fin 512) (i : Fin 26) :
      ((base (row (trans j m))) ++ [u (row (trans j m)) || read (base (row (trans j m))) j]).getD i.val false =
      (seed (key j) (row m)).getD (ren j i).val false := by
    have hsecond : (u (row (trans j m)) || read (base (row (trans j m))) j) =
        (if dup j then u (row m) else u (row m) || row m (key j)) := by
      rw [firstEq, rowEq]; exact secondEq j hj (row m)
    rw [hsecond]
    by_cases hi : i.val < 9
    · have hr : (ren j i).val < 9 := by
        unfold ren; rw [dite_eq_left hi]; split
        · exact (p ⟨i.val,hi⟩).isLt
        · exact hi
      unfold base seed
      rw [List.append_assoc, rawget _ _ _ hi, rawget _ _ _ hr, rowEq]
      cases hs : swap j <;> simp [ren, hi, hs]
    · by_cases h9 : i.val = 9
      · have he : i = 9 := Fin.ext h9
        subst i
        exact firstEq j m
      by_cases h10 : i.val = 10
      · have he : i = 10 := Fin.ext h10
        subst i
        cases hd : dup j
        · have r : ren j 10 = 10 := by simp [ren, hd, show (10 : Fin 26).val = 10 by rfl]
          rw [r]; rfl
        · have r : ren j 10 = 9 := by simp [ren, hd, show (10 : Fin 26).val = 10 by rfl]
          rw [r]; rfl
      · have hr : ren j i = i := by simp [ren, hi, h10]
        rw [hr]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp [base]; omega), List.getElem?_eq_none (by simp [seed]; omega)]
  let mapped (j : Fin 26) (g : Fin 3 × Fin 26 × Fin 26) := (g.1, ren j g.2.1, ren j g.2.2)
  have sim (j : Fin 26) (gs : List (Fin 3 × Fin 26 × Fin 26)) (w v : List Bool)
      (hl : w.length = v.length) (h11 : 11 ≤ w.length)
      (rel : ∀ i : Fin 26, w.getD i.val false = v.getD (ren j i).val false) :
      ∀ i : Fin 26, (gs.foldl step w).getD i.val false =
        ((gs.map (mapped j)).foldl step v).getD (ren j i).val false := by
    induction gs generalizing w v with
    | nil => exact rel
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      have fixed (i : Fin 26) (h : 11 ≤ i.val) : ren j i = i := by
        simp [ren, show ¬ i.val < 9 by omega, show i.val ≠ 10 by omega]
      have early (i : Fin 26) (h : i.val < 11) : (ren j i).val < 11 := by
        simp only [ren]
        split
        · split
          · exact Nat.lt_trans (p ⟨i.val, by assumption⟩).isLt (by decide : 9 < 11)
          · exact h
        · split
          · exact (by decide : (9 : Fin 26).val < 11)
          · exact h
      have reads (i : Fin 26) : read w i = read v (ren j i) := by
        by_cases he : 11 ≤ i.val
        · simp only [read, fixed i he]; split
          · rfl
          · simpa only [fixed i he] using rel i
        · have he' := early i (by omega)
          simp only [read, ite_eq_right (show i.val ≠ 25 by omega), ite_eq_right (show (ren j i).val ≠ 25 by omega), rel i]
      let z := if g.1.val = 0 then read w g.2.1 && read w g.2.2 else
        if g.1.val = 1 then read w g.2.1 || read w g.2.2 else !read w g.2.1
      have eqv : step v (mapped j g) = v ++ [z] := by simp only [step, mapped, z, reads]
      rw [eqv]
      change ∀ i : Fin 26, (gs.foldl step (w ++ [z])).getD i.val false = _
      apply ih
      · simp [hl]
      · simp; omega
      · intro i
        by_cases he : i.val < w.length
        · have hr : (ren j i).val < v.length := by
            by_cases ho : i.val < 11
            · have := early i ho; omega
            · simpa [fixed i (by omega), ← hl] using he
          simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left he,
            List.getElem?_append_left hr] using rel i
        · simp only [fixed i (by omega), List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by omega : w.length ≤ i.val),
            List.getElem?_append_right (by omega : v.length ≤ i.val), hl]
  let t := tail.map (mapped other)
  have ht : t.length ≤ 13 := by simpa [t] using hlen
  have rawOnto : ∀ (j : Fin 26) (v : Fin 9), ∃ i : Fin 9,
      (ren j ⟨i.val, Nat.lt_trans i.isLt (by decide : 9 < 26)⟩).val = v.val := by decide +kernel
  have tcov : ∀ v : ℕ, v < 9 → ∃ g ∈ t, g.2.1.val = v ∨ g.2.2.val = v := by
    intro v hv
    obtain ⟨i, hi⟩ := rawOnto other ⟨v,hv⟩
    obtain ⟨g, hg, he⟩ := cover i.val i.isLt
    refine ⟨mapped other g, List.mem_map.mpr ⟨g, hg, rfl⟩, ?_⟩
    have port (w : Fin 26) (hw : w.val = i.val) : (ren other w).val = v := by
      have same : w = ⟨i.val, Nat.lt_trans i.isLt (by decide : 9 < 26)⟩ := Fin.ext hw
      rw [same]
      exact hi
    exact he.elim (fun h => Or.inl (port _ h)) (fun h => Or.inr (port _ h))
  have caseBound (k : Fin 9) (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6) :
      ∃ m : Fin 512, (t.foldl step (seed k (row m))).getD (ren other out).val false ≠ edge (row m) := by
    rcases hk with rfl | rfl | rfl | rfl
    · obtain ⟨n, hn, bad⟩ := h1 _ t ht tcov
      exact ⟨⟨n, hn⟩, bad⟩
    · obtain ⟨n, hn, bad⟩ := h2 _ t ht tcov
      exact ⟨⟨n, hn⟩, bad⟩
    · obtain ⟨n, hn, bad⟩ := h3 _ t ht tcov
      exact ⟨⟨n, hn⟩, bad⟩
    · obtain ⟨n, hn, bad⟩ := h6 _ t ht tcov
      exact ⟨⟨n, hn⟩, bad⟩
  have hk : key other = 1 ∨ key other = 2 ∨ key other = 3 ∨ key other = 6 := by
    unfold key
    repeat' split
    all_goals decide
  obtain ⟨m, hm⟩ := caseBound _ hk
  let x := row (trans other m)
  refine ⟨(trans other m).val, (trans other m).isLt, ?_⟩
  change (tail.foldl step (step (base x) (1,a,b))).getD out.val false ≠ edge x
  rw [setup]
  have eqout := sim other tail (base x ++ [u x || read (base x) other]) (seed (key other) (row m))
    (by simp [base, seed]) (by simp [base]) (seedRel other otherOk m) out
  have eedge : edge x = edge (row m) := by cases hs : swap other <;> simp [x, trans, hs, edgeOk]
  simpa only [eqout, eedge] using hm
