import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3676_1
    (noAnd :
      let raw : List (BitVec 256) := [
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
        0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
        0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
        0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
        0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
        0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
        0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
        0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
      let base := 0 :: ~~~0 :: raw.flatMap (fun v => [v, ~~~v])
      let target : BitVec 256 := 0xfffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
      let step := fun (s : List (BitVec 256)) (ab : BitVec 256 × BitVec 256) =>
        let z := ab.1 &&& ab.2
        if ab.1 ∈ s ∧ ab.2 ∈ s ∧ z ∉ s then z :: ~~~z :: s else s
      ∀ ts : List (BitVec 256 × BitVec 256), ts.length ≤ 10 →
        ∀ a ∈ ts.foldl step base, ∀ b ∈ ts.foldl step base,
          a &&& b ≠ target)
    (noNand :
      let raw : List (BitVec 256) := [
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
        0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
        0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
        0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
        0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
        0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
        0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
        0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
      let base := 0 :: ~~~0 :: raw.flatMap (fun v => [v, ~~~v])
      let target : BitVec 256 := 0xfffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
      let step := fun (s : List (BitVec 256)) (ab : BitVec 256 × BitVec 256) =>
        let z := ab.1 &&& ab.2
        if ab.1 ∈ s ∧ ab.2 ∈ s ∧ z ∉ s then z :: ~~~z :: s else s
      ∀ ts : List (BitVec 256 × BitVec 256), ts.length ≤ 10 →
        ∀ a ∈ ts.foldl step base, ∀ b ∈ ts.foldl step base,
          a &&& b ≠ ~~~target) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ) (x6 : (Fin (8 : ℕ) → Bool) → ℕ → Bool),   x1 ≤ (11 : ℕ) →     (∀ (x8 : Fin x1), (x3 x8).1 < (10 : ℕ) + ↑x8 ∧ (x4 x8).1 < (10 : ℕ) + ↑x8) →       x5 < (10 : ℕ) + x1 →         (∀ (x10 : Fin (8 : ℕ) → Bool) (x11 : Fin (8 : ℕ)), x6 x10 ↑x11 = x10 x11) →           (∀ (x11 : Fin (8 : ℕ) → Bool), x6 x11 (8 : ℕ) = Bool.false ∧ x6 x11 (9 : ℕ) = Bool.false) →             (∀ (x12 : Fin (8 : ℕ) → Bool) (x13 : Fin x1),                 have x14 : ℕ × Bool → Bool := fun (x14 : ℕ × Bool) => x6 x12 x14.1 ^^ x14.2;                 x6 x12 ((10 : ℕ) + ↑x13) = if x2 x13 = Bool.true then x14 (x3 x13) && x14 (x4 x13) else x14 (x3 x13) || x14 (x4 x13)) →               ∃ (x13 : Fin (8 : ℕ) → Bool), (!x6 x13 x5) ≠ (x13 (0 : Fin (8 : ℕ)) && x13 (1 : Fin (8 : ℕ)) || x13 (1 : Fin (8 : ℕ)) && x13 (2 : Fin (8 : ℕ)) || x13 (2 : Fin (8 : ℕ)) && x13 (3 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ)) && x13 (4 : Fin (8 : ℕ)) || x13 (4 : Fin (8 : ℕ)) && x13 (0 : Fin (8 : ℕ)) || x13 (0 : Fin (8 : ℕ)) && x13 (5 : Fin (8 : ℕ)) || x13 (1 : Fin (8 : ℕ)) && x13 (6 : Fin (8 : ℕ)) || x13 (2 : Fin (8 : ℕ)) && x13 (7 : Fin (8 : ℕ)) || x13 (5 : Fin (8 : ℕ)) && x13 (7 : Fin (8 : ℕ))) := by
  intro n op a b output v cap read out input zeros formulas
  let pack (f : Fin 256 → Bool) : BitVec 256 :=
    (BitVec.iunfoldr (fun i (_ : Unit) => ((), f i)) ()).2

  have bit_pack (f : Fin 256 → Bool) (i : ℕ) (hi : i < 256) :
      (pack f).getLsbD i = f ⟨i, hi⟩ := by
    exact BitVec.iunfoldr_getLsbD (fun _ => ()) ⟨i, hi⟩ (fun _ => rfl)

  let steps (s : List (BitVec 256)) (ab : BitVec 256 × BitVec 256) :
      List (BitVec 256) :=
    let z := ab.1 &&& ab.2
    if ab.1 ∈ s ∧ ab.2 ∈ s ∧ z ∉ s then z :: ~~~z :: s else s

  have stays (s : List (BitVec 256)) (ab : BitVec 256 × BitVec 256) :
      s ⊆ steps s ab := by
    intro c hc
    simp only [steps]
    split
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)
    · exact hc

  let Closed (s : List (BitVec 256)) : Prop :=
    ∀ a ∈ s, (~~~a) ∈ s

  have closed_step (s : List (BitVec 256)) (ab : BitVec 256 × BitVec 256)
      (hs : Closed s) : Closed (steps s ab) := by
    intro a ha
    simp only [steps] at ha ⊢
    by_cases h : ab.1 ∈ s ∧ ab.2 ∈ s ∧ (ab.1 &&& ab.2) ∉ s
    · simp only [ite_eq_left h] at ha ⊢
      simp only [List.mem_cons] at ha ⊢
      rcases ha with rfl | rfl | ha
      · exact Or.inr (Or.inl rfl)
      · simp
      · exact Or.inr (Or.inr (hs _ ha))
    · simp only [ite_eq_right h] at ha ⊢
      exact hs a ha

  have closed_fold (s : List (BitVec 256)) (ts : List (BitVec 256 × BitVec 256))
      (hs : Closed s) : Closed (ts.foldl steps s) := by
    induction ts generalizing s with
    | nil => exact hs
    | cons ab ts ih => exact ih _ (closed_step s ab hs)

  have pair_step (s : List (BitVec 256)) (a b : BitVec 256)
      (ha : a ∈ s) (hb : b ∈ s) (hs : Closed s) :
      (a &&& b) ∈ steps s (a, b) ∧ (~~~(a &&& b)) ∈ steps s (a, b) := by
    by_cases p : (a &&& b) ∈ s
    · exact ⟨stays s (a, b) p, stays s (a, b) (hs _ p)⟩
    · simp [steps, ha, hb, p]

  let edge (x : Fin 8 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 5 && x 7

  let rows (r : Fin 256) (i : Fin 8) : Bool := r.val.testBit i.val

  let inputs : List (BitVec 256) :=
    (0 : BitVec 256) :: ~~~(0 : BitVec 256) ::
      (List.ofFn (fun i : Fin 8 => pack (fun r => rows r i))).flatMap (fun z => [z, ~~~z])

  have inputs_closed : Closed inputs := by
    intro a ha
    simp only [inputs, List.mem_cons, List.mem_flatMap, List.mem_ofFn, List.not_mem_nil,
      or_false] at ha ⊢
    rcases ha with rfl | rfl | ⟨z, ⟨i, rfl⟩, rfl | rfl⟩
    · exact Or.inr (Or.inl rfl)
    · simp
    · exact Or.inr (Or.inr ⟨_, ⟨i, rfl⟩, Or.inr rfl⟩)
    · simp only [BitVec.not_not]
      exact Or.inr (Or.inr ⟨_, ⟨i, rfl⟩, Or.inl rfl⟩)

  have input_mem (i : Fin 8) :
      pack (fun r => rows r i) ∈ inputs ∧ (~~~pack (fun r => rows r i)) ∈ inputs := by
    apply And.intro
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_flatMap.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, by simp⟩))
    · exact inputs_closed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_flatMap.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, by simp⟩)))
  by_contra hn
  have correct (x : Fin 8 → Bool) : (!v x output) = edge x := by
    by_contra hd
    exact hn ⟨x, hd⟩
  let mask (w : ℕ) := pack (fun r => v (rows r) w)
  let lit (p : ℕ × Bool) := if p.2 then ~~~(mask p.1) else mask p.1
  let ports (i : Fin n) :=
    if op i then (lit (a i), lit (b i)) else (~~~lit (a i), ~~~lit (b i))
  let all : List (BitVec 256 × BitVec 256) := List.ofFn ports
  let state (k : ℕ) := (all.take k).foldl steps inputs
  have bit_mask (w j : ℕ) (hj : j < 256) :
      (mask w).getLsbD j = v (rows ⟨j, hj⟩) w := bit_pack _ _ hj
  have bit_lit (p : ℕ × Bool) (j : ℕ) (hj : j < 256) :
      (lit p).getLsbD j = (v (rows ⟨j, hj⟩) p.1 ^^ p.2) := by
    cases h : p.2
    · simp only [lit, h, Bool.false_eq_true, ite_false, Bool.xor_false, bit_mask _ _ hj]
    · simp only [lit, h, ite_true, BitVec.getLsbD_not, hj, decide_true, Bool.true_and,
        bit_mask _ _ hj, Bool.xor_true]
  have seed (w : ℕ) (hw : w < 10) : mask w ∈ inputs ∧ (~~~mask w) ∈ inputs := by
    by_cases h : w < 8
    · let i : Fin 8 := ⟨w, h⟩
      have eq : mask w = pack (fun r => rows r i) := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        rw [bit_mask _ _ hj, bit_pack _ _ hj]
        exact input (rows ⟨j, hj⟩) i
      rw [eq]
      exact input_mem i
    · have eq : mask w = 0 := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        rw [bit_mask _ _ hj]
        have choice : w = 8 ∨ w = 9 := by omega
        rcases choice with rfl | rfl
        · simpa using (zeros (rows ⟨j, hj⟩)).1
        · simpa using (zeros (rows ⟨j, hj⟩)).2
      rw [eq]
      exact ⟨by simp [inputs], by simp [inputs]⟩
  have closed (k : ℕ) : Closed (state k) := closed_fold _ _ inputs_closed
  have cover (k : ℕ) (hk : k ≤ n) (w : ℕ) (hw : w < 10 + k) :
      mask w ∈ state k ∧ (~~~mask w) ∈ state k := by
    induction k generalizing w with
    | zero => exact seed w (by omega)
    | succ k ih =>
      let i : Fin n := ⟨k, by omega⟩
      have hlen : k < all.length := by simp only [all, List.length_ofFn]; omega
      have advance : state (k + 1) = steps (state k) (ports i) := by
        simp only [state, List.take_succ_eq_append_getElem hlen, List.foldl_append,
          List.foldl_cons, List.foldl_nil, all, List.getElem_ofFn]
        rfl
      rw [advance]
      by_cases older : w < 10 + k
      · have haveOld := ih (by omega) w older
        exact ⟨stays _ _ haveOld.1, stays _ _ haveOld.2⟩
      have eq : w = 10 + k := by omega
      subst w
      have pre (p : ℕ × Bool) (hp : p.1 < 10 + k) :
          lit p ∈ state k ∧ (~~~lit p) ∈ state k := by
        obtain ⟨a, b⟩ := ih (by omega) p.1 hp
        cases h : p.2 <;> simp [lit, h, a, b]
      have lp := pre (a i) (read i).1
      have rp := pre (b i) (read i).2
      cases hop : op i with
      | true =>
        have equals : mask (10 + k) = lit (a i) &&& lit (b i) := by
          apply BitVec.eq_of_getLsbD_eq
          intro j hj
          rw [bit_mask _ _ hj, BitVec.getLsbD_and, bit_lit _ _ hj, bit_lit _ _ hj]
          simpa [hop] using formulas (rows ⟨j, hj⟩) i
        rw [equals, show ports i = (lit (a i), lit (b i)) by simp [ports, hop]]
        exact pair_step _ _ _ lp.1 rp.1 (closed k)
      | false =>
        have equals : mask (10 + k) = ~~~(~~~lit (a i) &&& ~~~lit (b i)) := by
          apply BitVec.eq_of_getLsbD_eq
          intro j hj
          rw [bit_mask _ _ hj]
          simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, hj, decide_true, Bool.true_and,
            bit_lit _ _ hj, Bool.not_and, Bool.not_not]
          simpa [hop] using formulas (rows ⟨j, hj⟩) i
        rw [equals, BitVec.not_not,
          show ports i = (~~~lit (a i), ~~~lit (b i)) by simp [ports, hop]]
        exact (pair_step _ _ _ lp.2 rp.2 (closed k)).symm
  have target : (~~~mask output) = pack (fun r => edge (rows r)) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_not, bit_mask _ _ hj, bit_pack _ _ hj]
    simpa [hj] using correct (rows ⟨j, hj⟩)
  have present := (cover n (Nat.le_refl n) output out).2
  rw [target] at present
  have len : all.length = n := List.length_ofFn
  have takeAll : all.take n = all := by simp [← len]
  change _ ∈ (all.take n).foldl steps inputs at present
  rw [takeAll] at present
  let wanted := pack (fun r => edge (rows r))
  let literalRaw : List (BitVec 256) := [
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
        0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
        0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
        0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
        0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
        0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
        0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
        0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
  let literalInputs := 0 :: ~~~0 :: literalRaw.flatMap (fun v => [v, ~~~v])
  let rawLiteral : Fin 8 → BitVec 256 :=
    ![0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
      0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
      0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
      0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
      0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
      0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
      0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
      0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
  have rawBits : ∀ (i : Fin 8) (r : Fin 256),
      (rawLiteral i).getLsbD r.val = rows r i := by decide
  have rawEq : (fun i : Fin 8 => pack (fun r => rows r i)) = rawLiteral := by
    funext i
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [bit_pack _ _ hj]
    exact (rawBits i ⟨j, hj⟩).symm
  have inputsEq : inputs = literalInputs := by
    simp only [inputs, rawEq]
    rfl
  have targetBits : ∀ r : Fin 256,
      (0xfffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8 : BitVec 256).getLsbD r.val = edge (rows r) := by
    decide
  have targetEq : wanted = (0xfffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8 : BitVec 256) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [bit_pack _ _ hj]
    exact (targetBits ⟨j, hj⟩).symm
  have absent : wanted ∉ inputs := by
    intro hm
    simp only [inputs, List.mem_cons, List.mem_flatMap, List.mem_ofFn, List.not_mem_nil,
      or_false] at hm
    have atZero : wanted.getLsbD 0 = false := by
      rw [bit_pack _ _ (by decide : 0 < 256)]
      decide
    rcases hm with h | h | ⟨z, ⟨i, rfl⟩, h | h⟩
    · have atEdge : wanted.getLsbD 3 = true := by
        rw [bit_pack _ _ (by decide : 3 < 256)]
        decide
      rw [h] at atEdge
      contradiction
    · rw [h] at atZero
      contradiction
    · have single : ∀ i : Fin 8, ∃ r : Fin 256, rows r i = true ∧ edge (rows r) = false := by
        decide
      obtain ⟨r, hi, he⟩ := single i
      have hbit := congrArg (fun v : BitVec 256 => v.getLsbD r.val) h
      change (pack (fun r => edge (rows r))).getLsbD r.val =
        (pack (fun r => rows r i)).getLsbD r.val at hbit
      rw [bit_pack _ _ r.isLt, bit_pack _ _ r.isLt, hi, he] at hbit
      contradiction
    · have hz : (~~~pack (fun r => rows r i)).getLsbD 0 = true := by
        rw [BitVec.getLsbD_not, bit_pack _ _ (by decide : 0 < 256)]
        simp [rows]
      rw [h, hz] at atZero
      contradiction
  have missing (ts : List (BitVec 256 × BitVec 256)) (ht : ts.length ≤ 11) :
      wanted ∉ ts.foldl steps inputs := by
    induction ts using List.reverseRecOn with
    | nil => exact absent
    | append_singleton prior ab ih =>
      have short : prior.length ≤ 10 := by simp at ht; omega
      have earlier := ih (by omega)
      intro mem
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, steps] at mem
      let state := prior.foldl steps inputs
      by_cases avail : ab.1 ∈ state ∧ ab.2 ∈ state ∧ (ab.1 &&& ab.2) ∉ state
      · change wanted ∈ (if _ then _ :: _ :: state else state) at mem
        rw [ite_eq_left avail] at mem
        have first : ab.1 ∈ prior.foldl steps literalInputs := by simpa only [← inputsEq] using avail.1
        have second : ab.2 ∈ prior.foldl steps literalInputs := by simpa only [← inputsEq] using avail.2.1
        rcases List.mem_cons.mp mem with eq | rest
        · exact noAnd prior short ab.1 first ab.2 second (eq.symm.trans targetEq)
        · rcases List.mem_cons.mp rest with eq | old
          · have en := congrArg (fun c : BitVec 256 => ~~~c) eq
            rw [BitVec.not_not] at en
            exact noNand prior short ab.1 first ab.2 second (en.symm.trans (congrArg (fun c : BitVec 256 => ~~~c) targetEq))
          · exact earlier old
      · change wanted ∈ (if _ then _ :: _ :: state else state) at mem
        rw [ite_eq_right avail] at mem
        exact earlier mem
  exact missing all (len ▸ cap) present
