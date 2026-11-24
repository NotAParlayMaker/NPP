import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3537

def masks : List ℕ :=
  [(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)]

def edgeFn (x : Fin 14 → Bool) : Bool :=
  Decidable.decide (∃ (a b : Fin 14),
    (masks.getD a.val 0).testBit b.val = Bool.true ∧ x a = Bool.true ∧ x b = Bool.true)

def score4 (a b c d : ℕ) : ℕ :=
  ((15 : ℕ) * Min.min a b + Max.max a b) * (225 : ℕ) + (15 : ℕ) * Min.min c d + Max.max c d

def lift15 (f : Fin 14 → Fin 14) (u : Fin 15) : ℕ :=
  if u.val < 14 then (f (Fin.ofNat 14 u.val)).val else 14

def tableRaw : List (List ℕ) :=
  [[(226 : ℕ), (227 : ℕ), (228 : ℕ), (232 : ℕ), (233 : ℕ), (234 : ℕ), (236 : ℕ), (239 : ℕ), (258 : ℕ), (259 : ℕ), (260 : ℕ), (262 : ℕ), (263 : ℕ)],
   [(264 : ℕ), (266 : ℕ), (267 : ℕ), (269 : ℕ), (277 : ℕ), (278 : ℕ), (281 : ℕ), (284 : ℕ), (338 : ℕ), (341 : ℕ), (344 : ℕ), (354 : ℕ), (355 : ℕ)],
   [(356 : ℕ), (359 : ℕ), (402 : ℕ), (404 : ℕ), (1576 : ℕ), (1577 : ℕ), (1582 : ℕ), (1583 : ℕ), (1584 : ℕ), (1589 : ℕ), (1592 : ℕ), (1593 : ℕ), (1598 : ℕ)],
   [(1599 : ℕ), (1601 : ℕ), (1604 : ℕ), (1609 : ℕ), (1611 : ℕ), (1614 : ℕ), (1617 : ℕ), (1619 : ℕ), (2026 : ℕ), (2027 : ℕ), (2032 : ℕ), (2034 : ℕ), (2036 : ℕ)],
   [(2039 : ℕ), (2042 : ℕ), (2043 : ℕ), (2045 : ℕ), (2047 : ℕ), (2048 : ℕ), (2051 : ℕ), (2053 : ℕ), (2054 : ℕ), (2058 : ℕ), (2066 : ℕ), (2067 : ℕ), (2069 : ℕ)]]

def entryVal (x4 : Fin 65) : ℕ :=
  (tableRaw.getD (x4.val / 13) []).getD (x4.val % 13) 0

def adjBool (u v : Fin 14) : Bool :=
  (masks.getD u.val 0).testBit v.val || (masks.getD v.val 0).testBit u.val

def nbrs (u : Fin 14) : List (Fin 14) :=
  match u.val with
  | 0 => [7, 8, 10]
  | 1 => [7, 9, 13]
  | 2 => [8, 12, 13]
  | 3 => [7, 11, 12]
  | 4 => [10, 11, 13]
  | 5 => [9, 10, 12]
  | 6 => [8, 9, 11]
  | 7 => [0, 1, 3]
  | 8 => [0, 2, 6]
  | 9 => [1, 5, 6]
  | 10 => [0, 4, 5]
  | 11 => [3, 4, 6]
  | 12 => [2, 3, 5]
  | _ => [1, 2, 4]

lemma mem_nbrs_iff : ∀ u v : Fin 14, v ∈ nbrs u ↔ adjBool u v = true := by
  decide

lemma mask_irrefl : ∀ u : Fin 14, (masks.getD u.val 0).testBit u.val = false := by
  decide

def pairVec (u v w : Fin 14) : Bool :=
  decide (w = u ∨ w = v)

lemma edgeFn_pair (u v : Fin 14) : edgeFn (pairVec u v) = adjBool u v := by
  rw [Bool.eq_iff_iff]
  dsimp only [edgeFn, adjBool]
  rw [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairVec, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rw [mask_irrefl] at hab
      exact Bool.noConfusion hab
    · exact Or.inl hab
    · exact Or.inr hab
    · rw [mask_irrefl] at hab
      exact Bool.noConfusion hab
  · rintro (huv | hvu)
    · exact ⟨u, v, huv, by simp [pairVec], by simp [pairVec]⟩
    · exact ⟨v, u, hvu, by simp [pairVec], by simp [pairVec]⟩

lemma perm_preserves_adj (x9 : Equiv.Perm (Fin 14))
    (h : ∀ x10 : Fin 14 → Bool, edgeFn (x10 ∘ x9) = edgeFn x10) :
    ∀ u v : Fin 14, adjBool (x9 u) (x9 v) = adjBool u v := by
  intro u v
  have hcomp : pairVec (x9 u) (x9 v) ∘ x9 = pairVec u v := by
    funext w
    dsimp only [Function.comp, pairVec]
    simp only [x9.injective.eq_iff]
  have he := h (pairVec (x9 u) (x9 v))
  rw [hcomp, edgeFn_pair, edgeFn_pair] at he
  exact he.symm

def thirdNbr (u a b : Fin 14) : Fin 14 :=
  match nbrs u with
  | [x, y, z] =>
    if x != a && x != b then x
    else if y != a && y != b then y
    else z
  | _ => 0

def commonNbr (a b : Fin 14) : Fin 14 :=
  match nbrs a with
  | [x, y, z] =>
    if adjBool b x then x
    else if adjBool b y then y
    else z
  | _ => 0

lemma thirdNbr_eq : ∀ u : Fin 14, ∀ a ∈ nbrs u, ∀ b ∈ nbrs u, ∀ c ∈ nbrs u,
    a ≠ b → c ≠ a → c ≠ b → c = thirdNbr u a b := by
  decide

lemma commonNbr_eq : ∀ a : Fin 14, ∀ c ∈ nbrs a, ∀ b ∈ nbrs c, a ≠ b → c = commonNbr a b := by
  decide

def buildAut (p0 p7 p8 p1 p2 : Fin 14) (k : Fin 14) : Fin 14 :=
  let p10 := thirdNbr p0 p7 p8
  let p3 := thirdNbr p7 p0 p1
  let p6 := thirdNbr p8 p0 p2
  let p9 := commonNbr p1 p6
  let p11 := commonNbr p3 p6
  let p12 := commonNbr p2 p3
  let p13 := commonNbr p1 p2
  let p4 := thirdNbr p11 p3 p6
  let p5 := thirdNbr p9 p1 p6
  match k.val with
  | 0 => p0
  | 1 => p1
  | 2 => p2
  | 3 => p3
  | 4 => p4
  | 5 => p5
  | 6 => p6
  | 7 => p7
  | 8 => p8
  | 9 => p9
  | 10 => p10
  | 11 => p11
  | 12 => p12
  | _ => p13

def aut15 (p0 p7 p8 p1 p2 : Fin 14) : List ℕ :=
  let p10 := thirdNbr p0 p7 p8
  let p3 := thirdNbr p7 p0 p1
  let p6 := thirdNbr p8 p0 p2
  let p9 := commonNbr p1 p6
  let p11 := commonNbr p3 p6
  let p12 := commonNbr p2 p3
  let p13 := commonNbr p1 p2
  let p4 := thirdNbr p11 p3 p6
  let p5 := thirdNbr p9 p1 p6
  [p0.val, p1.val, p2.val, p3.val, p4.val, p5.val, p6.val,
   p7.val, p8.val, p9.val, p10.val, p11.val, p12.val, p13.val, 14]

lemma aut15_getD_0 (p0 p7 p8 p1 p2 : Fin 14) :
    (aut15 p0 p7 p8 p1 p2).getD 0 14 = p0.val := rfl

lemma aut15_getD_14 (p0 p7 p8 p1 p2 k : Fin 14) :
    (aut15 p0 p7 p8 p1 p2).getD k.val 14 = (buildAut p0 p7 p8 p1 p2 k).val := by
  rcases k with ⟨k, hk⟩
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k'
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · omega

lemma aut15_getD_15 (p0 p7 p8 p1 p2 : Fin 14) (u : Fin 15) :
    (aut15 p0 p7 p8 p1 p2).getD u.val 14 = lift15 (buildAut p0 p7 p8 p1 p2) u := by
  rcases u with ⟨u, hu⟩
  rcases u with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | u'
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · omega

lemma perm_eq_buildAut (x9 : Equiv.Perm (Fin 14))
    (hadj : ∀ u v : Fin 14, adjBool (x9 u) (x9 v) = adjBool u v) :
    x9 7 ∈ nbrs (x9 0) ∧
    x9 8 ∈ nbrs (x9 0) ∧
    x9 8 ≠ x9 7 ∧
    x9 1 ∈ nbrs (x9 7) ∧
    x9 1 ≠ x9 0 ∧
    x9 2 ∈ nbrs (x9 8) ∧
    x9 2 ≠ x9 0 ∧
    ∀ k : Fin 14, x9 k = buildAut (x9 0) (x9 7) (x9 8) (x9 1) (x9 2) k := by
  have h_nbr : ∀ u v : Fin 14, v ∈ nbrs u → x9 v ∈ nbrs (x9 u) := by
    intro u v huv
    rw [mem_nbrs_iff] at huv ⊢
    rw [hadj u v, huv]
  have h07 : x9 7 ∈ nbrs (x9 0) := h_nbr 0 7 (by decide)
  have h08 : x9 8 ∈ nbrs (x9 0) := h_nbr 0 8 (by decide)
  have h010 : x9 10 ∈ nbrs (x9 0) := h_nbr 0 10 (by decide)
  have h70 : x9 0 ∈ nbrs (x9 7) := h_nbr 7 0 (by decide)
  have h71 : x9 1 ∈ nbrs (x9 7) := h_nbr 7 1 (by decide)
  have h73 : x9 3 ∈ nbrs (x9 7) := h_nbr 7 3 (by decide)
  have h80 : x9 0 ∈ nbrs (x9 8) := h_nbr 8 0 (by decide)
  have h82 : x9 2 ∈ nbrs (x9 8) := h_nbr 8 2 (by decide)
  have h86 : x9 6 ∈ nbrs (x9 8) := h_nbr 8 6 (by decide)
  have h19 : x9 9 ∈ nbrs (x9 1) := h_nbr 1 9 (by decide)
  have h96 : x9 6 ∈ nbrs (x9 9) := h_nbr 9 6 (by decide)
  have h91 : x9 1 ∈ nbrs (x9 9) := h_nbr 9 1 (by decide)
  have h95 : x9 5 ∈ nbrs (x9 9) := h_nbr 9 5 (by decide)
  have h311 : x9 11 ∈ nbrs (x9 3) := h_nbr 3 11 (by decide)
  have h116 : x9 6 ∈ nbrs (x9 11) := h_nbr 11 6 (by decide)
  have h11_3 : x9 3 ∈ nbrs (x9 11) := h_nbr 11 3 (by decide)
  have h114 : x9 4 ∈ nbrs (x9 11) := h_nbr 11 4 (by decide)
  have h212 : x9 12 ∈ nbrs (x9 2) := h_nbr 2 12 (by decide)
  have h123 : x9 3 ∈ nbrs (x9 12) := h_nbr 12 3 (by decide)
  have h1_13 : x9 13 ∈ nbrs (x9 1) := h_nbr 1 13 (by decide)
  have h132 : x9 2 ∈ nbrs (x9 13) := h_nbr 13 2 (by decide)
  have hne87 : x9 8 ≠ x9 7 := x9.injective.ne (by decide)
  have hne10 : x9 1 ≠ x9 0 := x9.injective.ne (by decide)
  have hne20 : x9 2 ≠ x9 0 := x9.injective.ne (by decide)
  have hp10 : x9 10 = thirdNbr (x9 0) (x9 7) (x9 8) :=
    thirdNbr_eq (x9 0) (x9 7) h07 (x9 8) h08 (x9 10) h010
      (x9.injective.ne (by decide)) (x9.injective.ne (by decide)) (x9.injective.ne (by decide))
  have hp3 : x9 3 = thirdNbr (x9 7) (x9 0) (x9 1) :=
    thirdNbr_eq (x9 7) (x9 0) h70 (x9 1) h71 (x9 3) h73
      (x9.injective.ne (by decide)) (x9.injective.ne (by decide)) (x9.injective.ne (by decide))
  have hp6 : x9 6 = thirdNbr (x9 8) (x9 0) (x9 2) :=
    thirdNbr_eq (x9 8) (x9 0) h80 (x9 2) h82 (x9 6) h86
      (x9.injective.ne (by decide)) (x9.injective.ne (by decide)) (x9.injective.ne (by decide))
  have hp9 : x9 9 = commonNbr (x9 1) (x9 6) :=
    commonNbr_eq (x9 1) (x9 9) h19 (x9 6) h96 (x9.injective.ne (by decide))
  have hp11 : x9 11 = commonNbr (x9 3) (x9 6) :=
    commonNbr_eq (x9 3) (x9 11) h311 (x9 6) h116 (x9.injective.ne (by decide))
  have hp12 : x9 12 = commonNbr (x9 2) (x9 3) :=
    commonNbr_eq (x9 2) (x9 12) h212 (x9 3) h123 (x9.injective.ne (by decide))
  have hp13 : x9 13 = commonNbr (x9 1) (x9 2) :=
    commonNbr_eq (x9 1) (x9 13) h1_13 (x9 2) h132 (x9.injective.ne (by decide))
  have hp4 : x9 4 = thirdNbr (x9 11) (x9 3) (x9 6) :=
    thirdNbr_eq (x9 11) (x9 3) h11_3 (x9 6) h116 (x9 4) h114
      (x9.injective.ne (by decide)) (x9.injective.ne (by decide)) (x9.injective.ne (by decide))
  have hp5 : x9 5 = thirdNbr (x9 9) (x9 1) (x9 6) :=
    thirdNbr_eq (x9 9) (x9 1) h91 (x9 6) h96 (x9 5) h95
      (x9.injective.ne (by decide)) (x9.injective.ne (by decide)) (x9.injective.ne (by decide))
  refine ⟨h07, h08, hne87, h71, hne10, h82, hne20, ?_⟩
  intro k
  rcases k with ⟨k, hk⟩
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k'
  · rfl
  · rfl
  · rfl
  · exact hp3
  · dsimp only [buildAut]; rw [← hp3, ← hp6, ← hp11]; exact hp4
  · dsimp only [buildAut]; rw [← hp6, ← hp9]; exact hp5
  · exact hp6
  · rfl
  · rfl
  · dsimp only [buildAut]; rw [← hp6]; exact hp9
  · exact hp10
  · dsimp only [buildAut]; rw [← hp3, ← hp6]; exact hp11
  · dsimp only [buildAut]; rw [← hp3]; exact hp12
  · exact hp13
  · omega

def decodedEntries : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.finRange 65).map fun x4 =>
    let x5 := entryVal x4
    let x6 := (Fin.ofNat 14 (x5 / 225)).val
    let x7 := (Fin.ofNat 15 (x5 % 225 / 15)).val
    let x8 := (Fin.ofNat 15 (x5 % 15)).val
    (x6, x7, x8, score4 0 x6 x7 x8)

lemma order_ok : (List.finRange 65).all (fun x4 =>
    let x5 := entryVal x4
    decide ((0 : Fin 14) < Fin.ofNat 14 (x5 / 225)) &&
      decide (Fin.ofNat 15 (x5 % 225 / 15) < Fin.ofNat 15 (x5 % 15))) = true := by
  decide

def checkP0 (p0 : Fin 14) : Bool :=
  (nbrs p0).all fun p7 =>
    (nbrs p0).all fun p8 =>
      (p8 == p7) ||
        (nbrs p7).all fun p1 =>
          (p1 == p0) ||
            (nbrs p8).all fun p2 =>
              (p2 == p0) ||
                let aut := aut15 p0 p7 p8 p1 p2
                decodedEntries.all fun e =>
                  decide (e.2.2.2 ≤ score4 (aut.getD 0 14) (aut.getD e.1 14)
                    (aut.getD e.2.1 14) (aut.getD e.2.2.1 14))

lemma checkP0_0 : checkP0 0 = true := by decide
lemma checkP0_1 : checkP0 1 = true := by decide
lemma checkP0_2 : checkP0 2 = true := by decide
lemma checkP0_3 : checkP0 3 = true := by decide
lemma checkP0_4 : checkP0 4 = true := by decide
lemma checkP0_5 : checkP0 5 = true := by decide
lemma checkP0_6 : checkP0 6 = true := by decide
lemma checkP0_7 : checkP0 7 = true := by decide
lemma checkP0_8 : checkP0 8 = true := by decide
lemma checkP0_9 : checkP0 9 = true := by decide
lemma checkP0_10 : checkP0 10 = true := by decide
lemma checkP0_11 : checkP0 11 = true := by decide
lemma checkP0_12 : checkP0 12 = true := by decide
lemma checkP0_13 : checkP0 13 = true := by decide

lemma checkP0_all (p0 : Fin 14) : checkP0 p0 = true := by
  rcases p0 with ⟨p, hp⟩
  rcases p with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | p'
  · exact checkP0_0
  · exact checkP0_1
  · exact checkP0_2
  · exact checkP0_3
  · exact checkP0_4
  · exact checkP0_5
  · exact checkP0_6
  · exact checkP0_7
  · exact checkP0_8
  · exact checkP0_9
  · exact checkP0_10
  · exact checkP0_11
  · exact checkP0_12
  · exact checkP0_13
  · omega

lemma solve : ∀ (x4 : Fin 65),
    let x5 := entryVal x4
    let x6 : Fin 14 := Fin.ofNat 14 (x5 / 225)
    let x7 : Fin 15 := Fin.ofNat 15 (x5 % 225 / 15)
    let x8 : Fin 15 := Fin.ofNat 15 (x5 % 15)
    (0 : Fin 14) < x6 ∧ x7 < x8 ∧
      ∀ (x9 : Equiv.Perm (Fin 14)), (∀ x10 : Fin 14 → Bool, edgeFn (x10 ∘ x9) = edgeFn x10) →
        score4 0 x6.val x7.val x8.val ≤
          score4 (x9 0).val (x9 x6).val (lift15 x9 x7) (lift15 x9 x8) := by
  intro x4
  dsimp only
  have hord := List.all_eq_true.mp order_ok x4 (List.mem_finRange x4)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hord
  refine ⟨hord.1, hord.2, ?_⟩
  intro x9 hsym
  have hadj := perm_preserves_adj x9 hsym
  rcases perm_eq_buildAut x9 hadj with ⟨h07, h08, hne87, h71, hne10, h82, hne20, hbuild⟩
  have hc0 := checkP0_all (x9 0)
  rw [checkP0, List.all_eq_true] at hc0
  have hc7 := hc0 (x9 7) h07
  rw [List.all_eq_true] at hc7
  have hc8 := hc7 (x9 8) h08
  rw [Bool.or_eq_true] at hc8
  have hc8' : ((nbrs (x9 7)).all fun p1 => (p1 == x9 0) ||
      (nbrs (x9 8)).all fun p2 => (p2 == x9 0) ||
        let aut := aut15 (x9 0) (x9 7) (x9 8) p1 p2
        decodedEntries.all fun e =>
          decide (e.2.2.2 ≤ score4 (aut.getD 0 14) (aut.getD e.1 14)
            (aut.getD e.2.1 14) (aut.getD e.2.2.1 14))) = true := by
    rcases hc8 with hbeq | hrest
    · simp only [beq_iff_eq] at hbeq
      exact (hne87 hbeq).elim
    · exact hrest
  rw [List.all_eq_true] at hc8'
  have hc1 := hc8' (x9 1) h71
  rw [Bool.or_eq_true] at hc1
  have hc1' : ((nbrs (x9 8)).all fun p2 => (p2 == x9 0) ||
      let aut := aut15 (x9 0) (x9 7) (x9 8) (x9 1) p2
      decodedEntries.all fun e =>
        decide (e.2.2.2 ≤ score4 (aut.getD 0 14) (aut.getD e.1 14)
          (aut.getD e.2.1 14) (aut.getD e.2.2.1 14))) = true := by
    rcases hc1 with hbeq | hrest
    · simp only [beq_iff_eq] at hbeq
      exact (hne10 hbeq).elim
    · exact hrest
  rw [List.all_eq_true] at hc1'
  have hc2 := hc1' (x9 2) h82
  rw [Bool.or_eq_true] at hc2
  have hc2' : (decodedEntries.all fun e =>
      let aut := aut15 (x9 0) (x9 7) (x9 8) (x9 1) (x9 2)
      decide (e.2.2.2 ≤ score4 (aut.getD 0 14) (aut.getD e.1 14)
        (aut.getD e.2.1 14) (aut.getD e.2.2.1 14))) = true := by
    rcases hc2 with hbeq | hrest
    · simp only [beq_iff_eq] at hbeq
      exact (hne20 hbeq).elim
    · exact hrest
  rw [List.all_eq_true] at hc2'
  have hce := hc2' _ (List.mem_map_of_mem (List.mem_finRange x4))
  dsimp only at hce
  rw [decide_eq_true_eq] at hce
  have hfn : buildAut (x9 0) (x9 7) (x9 8) (x9 1) (x9 2) = x9 :=
    funext fun k => (hbuild k).symm
  rw [aut15_getD_0 _ _ _ _ _,
    aut15_getD_14 _ _ _ _ _ (Fin.ofNat 14 (entryVal x4 / 225)),
    aut15_getD_15 _ _ _ _ _ (Fin.ofNat 15 (entryVal x4 % 225 / 15)),
    aut15_getD_15 _ _ _ _ _ (Fin.ofNat 15 (entryVal x4 % 15)),
    hfn] at hce
  exact hce

end PEqualNP.Outside.L_meta_3537

theorem PEqualNP.Outside.L_meta_3537 : have x1 : (Fin (14 : ℕ) → Bool) → Bool := fun (x1 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true); have x2 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x2 x3 x4 x5 : ℕ) => ((15 : ℕ) * Min.min x2 x3 + Max.max x2 x3) * (225 : ℕ) + (15 : ℕ) * Min.min x4 x5 + Max.max x4 x5; have x3 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x3 : Equiv.Perm (Fin (14 : ℕ))) (x4 : Fin (15 : ℕ)) => if ↑x4 < (14 : ℕ) then ↑(x3 (Fin.ofNat (14 : ℕ) ↑x4)) else (14 : ℕ); ∀ (x4 : Fin (65 : ℕ)),   have x5 : ℕ := ([[(226 : ℕ), (227 : ℕ), (228 : ℕ), (232 : ℕ), (233 : ℕ), (234 : ℕ), (236 : ℕ), (239 : ℕ), (258 : ℕ), (259 : ℕ), (260 : ℕ), (262 : ℕ), (263 : ℕ)], [(264 : ℕ), (266 : ℕ), (267 : ℕ), (269 : ℕ), (277 : ℕ), (278 : ℕ), (281 : ℕ), (284 : ℕ), (338 : ℕ), (341 : ℕ), (344 : ℕ), (354 : ℕ), (355 : ℕ)], [(356 : ℕ), (359 : ℕ), (402 : ℕ), (404 : ℕ), (1576 : ℕ), (1577 : ℕ), (1582 : ℕ), (1583 : ℕ), (1584 : ℕ), (1589 : ℕ), (1592 : ℕ), (1593 : ℕ), (1598 : ℕ)], [(1599 : ℕ), (1601 : ℕ), (1604 : ℕ), (1609 : ℕ), (1611 : ℕ), (1614 : ℕ), (1617 : ℕ), (1619 : ℕ), (2026 : ℕ), (2027 : ℕ), (2032 : ℕ), (2034 : ℕ), (2036 : ℕ)], [(2039 : ℕ), (2042 : ℕ), (2043 : ℕ), (2045 : ℕ), (2047 : ℕ), (2048 : ℕ), (2051 : ℕ), (2053 : ℕ), (2054 : ℕ), (2058 : ℕ), (2066 : ℕ), (2067 : ℕ), (2069 : ℕ)]].getD (↑x4 / (13 : ℕ)) []).getD (↑x4 % (13 : ℕ)) (0 : ℕ);   have x6 : Fin (14 : ℕ) := Fin.ofNat (14 : ℕ) (x5 / (225 : ℕ));   have x7 : Fin (15 : ℕ) := Fin.ofNat (15 : ℕ) (x5 % (225 : ℕ) / (15 : ℕ));   have x8 : Fin (15 : ℕ) := Fin.ofNat (15 : ℕ) (x5 % (15 : ℕ));   (0 : Fin (14 : ℕ)) < x6 ∧ x7 < x8 ∧ ∀ (x9 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x10 : Fin (14 : ℕ) → Bool), x1 (x10 ∘ ⇑x9) = x1 x10) → x2 (0 : ℕ) ↑x6 ↑x7 ↑x8 ≤ x2 (↑(x9 (0 : Fin (14 : ℕ)))) (↑(x9 x6)) (x3 x9 x7) (x3 x9 x8) := PEqualNP.Outside.L_meta_3537.solve
