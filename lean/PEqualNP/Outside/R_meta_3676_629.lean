import Mathlib
import PEqualNP.Defs

-- Adapts the truth-column simulation in shev-art's PR #7566.
-- Fixing leaf 6 to false lets us remove a gate and use 128 rows.

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3676_629
    (mustRead : ∀ (n : ℕ) (a b : Fin n → ℕ) (d : ℕ → Prop) (out : ℕ),
  (∀ j, a j < 10+j.val ∧ b j < 10+j.val) →
  (∀ w < 10, d w → w=6) →
  (∀ j : Fin n, d (10+j.val) → d (a j) ∨ d (b j)) →
  out < 10+n → d out → out ≠ 6 → ∃ j, a j=6 ∨ b j=6)
    (noColumn :
      let raw : List (BitVec 128) := [
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
        0xcccccccccccccccccccccccccccccccc,
        0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
        0xff00ff00ff00ff00ff00ff00ff00ff00,
        0xffff0000ffff0000ffff0000ffff0000,
        0xffffffff00000000ffffffff00000000,
        0x0,
        0xffffffffffffffff0000000000000000]
      let base := 0 :: ~~~0 :: raw.flatMap (fun v => [v, ~~~v])
      let target : BitVec 128 := 0xfffffffffffaf8f8ffeafaeaffeaf8c8
      let step := fun (s : List (BitVec 128)) (ab : BitVec 128 × BitVec 128) =>
        let z := ab.1 &&& ab.2
        if ab.1 ∈ s ∧ ab.2 ∈ s ∧ z ∉ s then z :: ~~~z :: s else s
      ∀ ts : List (BitVec 128 × BitVec 128), ts.length ≤ 10 →
        target ∉ ts.foldl step base) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ) (x6 : (Fin (8 : ℕ) → Bool) → ℕ → Bool),   x1 ≤ (11 : ℕ) →     (∀ (x8 : Fin x1), (x3 x8).1 < (10 : ℕ) + ↑x8 ∧ (x4 x8).1 < (10 : ℕ) + ↑x8) →       x5 < (10 : ℕ) + x1 →         (∀ (x10 : Fin (8 : ℕ) → Bool) (x11 : Fin (8 : ℕ)), x6 x10 ↑x11 = x10 x11) →           (∀ (x11 : Fin (8 : ℕ) → Bool), x6 x11 (8 : ℕ) = Bool.false ∧ x6 x11 (9 : ℕ) = Bool.false) →             (∀ (x12 : Fin (8 : ℕ) → Bool) (x13 : Fin x1),                 have x14 : ℕ × Bool → Bool := fun (x14 : ℕ × Bool) => x6 x12 x14.1 ^^ x14.2;                 x6 x12 ((10 : ℕ) + ↑x13) = if x2 x13 = Bool.true then x14 (x3 x13) && x14 (x4 x13) else x14 (x3 x13) || x14 (x4 x13)) →               ∃ (x13 : Fin (8 : ℕ) → Bool), (!x6 x13 x5) ≠ (x13 (0 : Fin (8 : ℕ)) && x13 (1 : Fin (8 : ℕ)) || x13 (1 : Fin (8 : ℕ)) && x13 (2 : Fin (8 : ℕ)) || x13 (2 : Fin (8 : ℕ)) && x13 (3 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ)) && x13 (4 : Fin (8 : ℕ)) || x13 (4 : Fin (8 : ℕ)) && x13 (0 : Fin (8 : ℕ)) || x13 (0 : Fin (8 : ℕ)) && x13 (5 : Fin (8 : ℕ)) || x13 (1 : Fin (8 : ℕ)) && x13 (6 : Fin (8 : ℕ)) || x13 (2 : Fin (8 : ℕ)) && x13 (7 : Fin (8 : ℕ)) || x13 (5 : Fin (8 : ℕ)) && x13 (7 : Fin (8 : ℕ))) := by
  intro n op a b output v cap read out input zeros formulas
  let pack (f : Fin 128 → Bool) : BitVec 128 :=
    (BitVec.iunfoldr (fun i (_ : Unit) => ((), f i)) ()).2

  have bit_pack (f : Fin 128 → Bool) (i : ℕ) (hi : i < 128) :
      (pack f).getLsbD i = f ⟨i, hi⟩ := by
    exact BitVec.iunfoldr_getLsbD (fun _ => ()) ⟨i, hi⟩ (fun _ => rfl)

  let steps (s : List (BitVec 128)) (ab : BitVec 128 × BitVec 128) :
      List (BitVec 128) :=
    let z := ab.1 &&& ab.2
    if ab.1 ∈ s ∧ ab.2 ∈ s ∧ z ∉ s then z :: ~~~z :: s else s

  have stays (s : List (BitVec 128)) (ab : BitVec 128 × BitVec 128) :
      s ⊆ steps s ab := by
    intro c hc
    simp only [steps]
    split
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)
    · exact hc

  let Closed (s : List (BitVec 128)) : Prop :=
    ∀ a ∈ s, (~~~a) ∈ s

  have closed_step (s : List (BitVec 128)) (ab : BitVec 128 × BitVec 128)
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

  have closed_fold (s : List (BitVec 128)) (ts : List (BitVec 128 × BitVec 128))
      (hs : Closed s) : Closed (ts.foldl steps s) := by
    induction ts generalizing s with
    | nil => exact hs
    | cons ab ts ih => exact ih _ (closed_step s ab hs)

  have pair_step (s : List (BitVec 128)) (a b : BitVec 128)
      (ha : a ∈ s) (hb : b ∈ s) (hs : Closed s) :
      (a &&& b) ∈ steps s (a, b) ∧ (~~~(a &&& b)) ∈ steps s (a, b) := by
    by_cases p : (a &&& b) ∈ s
    · exact ⟨stays s (a, b) p, stays s (a, b) (hs _ p)⟩
    · simp [steps, ha, hb, p]

  let edge (x : Fin 8 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 5 && x 7

  let rows (r : Fin 128) (i : Fin 8) : Bool := if i.val=6 then false else r.val.testBit (if i.val<6 then i.val else 6)

  let inputs : List (BitVec 128) :=
    (0 : BitVec 128) :: ~~~(0 : BitVec 128) ::
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
  let all : List (BitVec 128 × BitVec 128) := List.ofFn ports
  let state (k : ℕ) := (all.take k).foldl steps inputs
  have bit_mask (w j : ℕ) (hj : j < 128) :
      (mask w).getLsbD j = v (rows ⟨j, hj⟩) w := bit_pack _ _ hj
  have bit_lit (p : ℕ × Bool) (j : ℕ) (hj : j < 128) :
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
  let literalRaw : List (BitVec 128) := [
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
        0xcccccccccccccccccccccccccccccccc,
        0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
        0xff00ff00ff00ff00ff00ff00ff00ff00,
        0xffff0000ffff0000ffff0000ffff0000,
        0xffffffff00000000ffffffff00000000,
        0x0,
        0xffffffffffffffff0000000000000000]
  let literalInputs := 0 :: ~~~0 :: literalRaw.flatMap (fun v => [v, ~~~v])
  let rawLiteral : Fin 8 → BitVec 128 :=
    ![0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
      0xcccccccccccccccccccccccccccccccc,
      0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
      0xff00ff00ff00ff00ff00ff00ff00ff00,
      0xffff0000ffff0000ffff0000ffff0000,
      0xffffffff00000000ffffffff00000000,
      0x0,
      0xffffffffffffffff0000000000000000]
  have rawBits : ∀ (i : Fin 8) (r : Fin 128),
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
  have targetBits : ∀ r : Fin 128,
      (0xfffffffffffaf8f8ffeafaeaffeaf8c8 : BitVec 128).getLsbD r.val = edge (rows r) := by
    decide
  have targetEq : wanted = (0xfffffffffffaf8f8ffeafaeaffeaf8c8 : BitVec 128) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [bit_pack _ _ hj]
    exact (targetBits ⟨j, hj⟩).symm

  let x (i : Fin 8) := decide (i.val=1)
  let y (i : Fin 8) := decide (i.val=1 ∨ i.val=6)
  let d (w : ℕ) := v x w ≠ v y w
  have seedDiff (w : ℕ) (hw : w < 10) (hd : d w) : w=6 := by
    by_contra ne
    apply hd
    by_cases small : w < 8
    · let i : Fin 8 := ⟨w,small⟩
      exact (input x i).trans ((show x i=y i by simp [x,y,i,ne]).trans (input y i).symm)
    · have h : w=8 ∨ w=9 := by omega
      rcases h with rfl|rfl
      · exact (zeros x).1.trans (zeros y).1.symm
      · exact (zeros x).2.trans (zeros y).2.symm
  have cause (i : Fin n) (hd : d (10+i.val)) : d (a i).1 ∨ d (b i).1 := by
    by_contra! h
    apply hd
    rw [formulas x i,formulas y i]
    dsimp [d] at h
    obtain ⟨l,r⟩ := h
    simp_all
  have dx : d output := by
    have e := correct x
    have f := correct y
    have ex : edge x=false := by decide
    have ey : edge y=true := by decide
    intro eq
    rw [eq,ex] at e
    rw [ey] at f
    exact Bool.false_ne_true (e.symm.trans f)
  have other : output ≠ 6 := by
    intro eq
    have h := correct (fun _ => false)
    rw [eq,show v (fun _ => false) 6=false from input _ (6 : Fin 8)] at h
    contradiction
  obtain ⟨j,touch⟩ := mustRead n (fun i => (a i).1) (fun i => (b i).1) d output read seedDiff cause out dx other
  have const : mask 6 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro t ht
    rw [bit_mask _ _ ht,show v (rows ⟨t,ht⟩) 6=rows ⟨t,ht⟩ (6 : Fin 8) from input (rows ⟨t,ht⟩) (6 : Fin 8)]
    simp [rows]
  have lp (p : ℕ × Bool) (hp : p.1 < 10+j.val) : lit p ∈ state j.val ∧ ~~~lit p ∈ state j.val := by
    obtain ⟨l,r⟩ := cover j.val (by omega) p.1 hp
    cases he : p.2 <;> simp [lit,he,l,r]
  have gz : (0 : BitVec 128) ∈ state j.val := by
    have hz : mask 6 ∈ state j.val := (cover j.val (by omega) 6 (by omega)).1
    rwa [const] at hz
  have skip : steps (state j.val) (ports j) = state j.val := by
    have l := lp (a j) (read j).1
    have r := lp (b j) (read j).2
    rcases touch with ha|hb
    · have hh : lit (a j)=0 ∨ lit (a j)= ~~~0 := by cases he : (a j).2 <;> simp [lit,he,ha,const]
      rcases hh with hh|hh <;> cases he : op j <;> simp [ports,he,hh,steps,gz,r.1,r.2]
      all_goals
        intro _ fresh
        exfalso
        apply fresh
        change (BitVec.allOnes 128 &&& _) ∈ _
        rw [BitVec.allOnes_and]
        first | exact r.1 | exact r.2
    · have hh : lit (b j)=0 ∨ lit (b j)= ~~~0 := by cases he : (b j).2 <;> simp [lit,he,hb,const]
      rcases hh with hh|hh <;> cases he : op j <;> simp [ports,he,hh,steps,gz,l.1,l.2]
      all_goals
        intro _ fresh
        exfalso
        apply fresh
        change (_ &&& BitVec.allOnes 128) ∈ _
        rw [BitVec.and_allOnes]
        first | exact l.1 | exact l.2
  let small := all.take j.val ++ all.drop (j.val+1)
  have short : small.length ≤ 10 := by
    simp [small,List.length_take,List.length_drop,len,Nat.min_eq_left (by omega : j.val ≤ n)]
    omega
  have advance : (all.take (j.val+1)).foldl steps inputs = state j.val := by
    rw [List.take_succ_eq_append_getElem (by rw [len]; exact j.isLt),List.foldl_append]
    simpa only [List.foldl_cons,List.foldl_nil,all,List.getElem_ofFn] using skip
  have eq : small.foldl steps inputs = all.foldl steps inputs := by
    conv_rhs => rw [← List.take_append_drop (j.val+1) all, List.foldl_append,advance]
    simp [small,state,List.foldl_append]
  apply noColumn small short
  change (0xfffffffffffaf8f8ffeafaeaffeaf8c8: BitVec 128) ∈ small.foldl steps literalInputs
  rw [← targetEq,← inputsEq,eq]
  exact present
