import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3014_129
    (boundary :
       have E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
    (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8),
    (6, 9), (6, 11)];
    have hit : ℕ → Bool := fun r => E.any (fun p => r.testBit p.1 && r.testBit
    p.2);
    ∀ r : Fin 16384, hit r.val = false →     (∀ i : Fin 14, r.val.testBit i.val = false → hit
    (r.val ||| 2 ^ i.val) = true) →     r.val ∈ ([127, 244, 314, 432, 541, 660, 792, 1102, 1220,
    1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426,
    8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256] : List ℕ))
    (witness :
       ∃ C : PEqualNP.CircuitLowerBounds.Circuit,     PEqualNP.TopForm.IsAO2 14 C ∧     (∀ g ∈
    C.gates, g.inputs.Nodup) ∧ 2 ≤ C.size ∧ C.size ≤ 26 ∧     (∀ r ∈ ([129, 257, 1025, 130, 514,
    8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] :
    List ℕ),       C.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val)) = true) ∧     ∀ r ∈ ([127,
    244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179,
    4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656,
    12353, 13504, 14849, 16256] : List ℕ),       C.eval (List.ofFn (fun i : Fin 14 => r.testBit
    i.val)) = false) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7
        : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 :
        ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 :
        ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 :
        ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];
    have x2 : (Fin (14 : ℕ) → Bool) → Bool := fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3
        : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true);
    ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates,
        x4.inputs.Nodup) ∧ (2 : ℕ) ≤ x3.size ∧ x3.size ≤ (26 : ℕ) ∧ (∀ (x4 : Fin (14 : ℕ) → Bool), x2 x4
        = Bool.true → (∀ x6 ≤ x4, x2 x6 = Bool.true → x6 = x4) → x3.eval (List.ofFn x4) = Bool.true) ∧ ∀
        (x4 : Fin (14 : ℕ) → Bool), x2 x4 = Bool.false → (∀ (x6 : Fin (14 : ℕ) → Bool), x4 ≤ x6 → x2 x6
        = Bool.false → x6 = x4) → x3.eval (List.ofFn x4) = Bool.false := by
  let E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let hit : ℕ → Bool := fun r => E.any (fun p => r.testBit p.1 && r.testBit p.2)
  let bits (r : ℕ) (i : Fin 14) : Bool := r.testBit i.val
  let f (x : Fin 14 → Bool) : Bool :=
    decide (∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true)
  change ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 14 C ∧
    (∀ g ∈ C.gates, g.inputs.Nodup) ∧ 2 ≤ C.size ∧ C.size ≤ 26 ∧
    (∀ x, f x = true → (∀ y ≤ x, f y = true → y = x) → C.eval (List.ofFn x) = true) ∧
    (∀ x, f x = false → (∀ y, x ≤ y → f y = false → y = x) → C.eval (List.ofFn x) = false)
  have inRange : ∀ p ∈ E, p.1 < 14 ∧ p.2 < 14 := by dsimp [E]; decide
  have evalBits (r : ℕ) : f (bits r) = hit r := by
    apply Bool.eq_iff_iff.mpr
    simp only [f, hit, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨u, v, h, hu, hv⟩
      exact ⟨(u.val, v.val), h, hu, hv⟩
    · rintro ⟨⟨u,v⟩, h, hu, hv⟩
      exact ⟨⟨u,(inRange _ h).1⟩, ⟨v,(inRange _ h).2⟩, h, hu, hv⟩
  have edgeRow : ∀ p ∈ E, (2 ^ p.1 ||| 2 ^ p.2) ∈ ([129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112] : List ℕ) := by dsimp [E]; decide
  obtain ⟨C, hC, hND, hLo, hHi, hPos, hNeg⟩ := witness
  refine ⟨C, hC, hND, hLo, hHi, ?_, ?_⟩
  · intro x hx hmin
    obtain ⟨u, v, huv, hu, hv⟩ := of_decide_eq_true hx
    let r := (2 ^ u.val ||| 2 ^ v.val)
    have onEdge (i : Fin 14) : bits r i = (decide (u.val = i.val) || decide (v.val = i.val)) := by
      simp [r, bits, Nat.testBit_or, Nat.testBit_two_pow]
    have below : bits r ≤ x := by
      intro i
      rw [onEdge]
      by_cases e₁ : u = i
      · subst i
        simp [hu]
      · have ne₁ : u.val ≠ i.val := fun h => e₁ (Fin.ext h)
        by_cases e₂ : v = i
        · subst i
          simp [ne₁, hv]
        · have ne₂ : v.val ≠ i.val := fun h => e₂ (Fin.ext h)
          simp [ne₁, ne₂]
    have htrue : f (bits r) = true := by
      apply decide_eq_true
      exact ⟨u, v, huv, by simp [onEdge], by simp [onEdge]⟩
    rw [← hmin (bits r) below htrue]
    exact hPos r (edgeRow (u.val,v.val) huv)
  · intro x hx hmax
    let r := BitVec.ofBoolListLE (List.ofFn x)
    have hbound : r.toNat < 16384 := by simpa [r] using r.isLt
    have rep : bits r.toNat = x := by
      funext i
      change r.getLsbD i.val = x i
      dsimp only [r]
      simp only [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]
    have hf : hit r.toNat = false := by rw [← evalBits, rep, hx]
    have plus (i : Fin 14) (hi : r.toNat.testBit i.val = false) :
        hit (r.toNat ||| 2 ^ i.val) = true := by
      let y := bits (r.toNat ||| 2 ^ i.val)
      have le : x ≤ y := by
        intro j
        have h := congrFun rep j
        change r.toNat.testBit j.val = x j at h
        change x j ≤ (r.toNat ||| 2 ^ i.val).testBit j.val
        rw [Nat.testBit_or, h]
        cases x j <;> simp
      have hy : y i = true := by simp [y, bits, Nat.testBit_or]
      have hxi : x i = false := (congrFun rep i).symm.trans hi
      by_cases H : f y = false
      · have eq := congrFun (hmax y le H) i
        rw [hy, hxi] at eq
        exact Bool.noConfusion eq
      · rw [← evalBits]
        change f y = true
        exact Bool.eq_true_of_not_eq_false H
    have m := boundary ⟨r.toNat,hbound⟩ hf plus
    rw [← rep]
    exact hNeg r.toNat m
