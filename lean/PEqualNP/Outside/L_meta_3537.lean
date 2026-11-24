import PEqualNP.Defs



namespace PEqualNP.Outside.L_meta_3537

namespace Invariant

def masks : List Nat := [1408,8832,12544,6272,11264,5632,2816]

def dir {n : Nat} (a b : Fin n) : Bool := (masks.getD a.val 0).testBit b.val

def graphFun (x : Fin 14 → Bool) : Bool :=
  decide (∃ a b : Fin 14, dir a b = true ∧ x a = true ∧ x b = true)

def lift (a : Fin 14) : Fin 15 := ⟨a.val, Nat.lt_trans a.isLt (by decide)⟩

def extend (π : Equiv.Perm (Fin 14)) (a : Fin 15) : Fin 15 :=
  if a.val < 14 then lift (π (Fin.ofNat 14 a.val)) else 14

theorem extend_val (π : Equiv.Perm (Fin 14)) (a : Fin 15) :
    (extend π a).val = if a.val < 14 then (π (Fin.ofNat 14 a.val)).val else 14 := by
  by_cases ha : a.val < 14 <;> simp [extend, lift, ha]

theorem extend_lift (π : Equiv.Perm (Fin 14)) (a : Fin 14) :
    extend π (lift a) = lift (π a) := by
  have h : Fin.ofNat 14 a.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
  simpa [extend,lift,a.isLt,h]

theorem extend_sentinel (π : Equiv.Perm (Fin 14)) : extend π 14 = 14 := by
  rfl

def adj (a b : Fin 15) : Bool := dir a b || dir b a

def common₂ (a b : Fin 15) : Bool :=
  decide (∃ w : Fin 14, adj a (lift w) = true ∧ adj b (lift w) = true)

def hasCommon (a b c : Fin 15) : Bool :=
  decide (∃ w : Fin 14, adj a (lift w) = true ∧ adj b (lift w) = true ∧ adj c (lift w) = true)

def pair (a b : Fin 15) : Nat :=
  if a = b then 3 else if adj a b then 2 else if common₂ a b then 1 else 0

def flag (x : Bool) : Nat := if x then 1 else 0

def fp (a b c d : Fin 15) : Nat :=
  (1024*pair a b + 256*pair a c + 64*pair a d + 16*pair b c + 4*pair b d + pair c d)*64 +
  32*flag (hasCommon a b c) + 16*flag (hasCommon a b d) +
  8*flag (hasCommon a c d) + 4*flag (hasCommon b c d) +
  2*flag (decide (c = 14)) + flag (decide (d = 14))

private theorem bool_eq (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem real_or_sentinel (a : Fin 15) : (∃ w : Fin 14, a = lift w) ∨ a = 14 := by
  by_cases ha : a.val < 14
  · exact Or.inl ⟨⟨a.val,ha⟩, Fin.ext rfl⟩
  · exact Or.inr (Fin.ext (by omega))

theorem extend_injective (π : Equiv.Perm (Fin 14)) : Function.Injective (extend π) := by
  have hinv : Function.LeftInverse (extend π.symm) (extend π) := by
    intro a
    rcases real_or_sentinel a with ⟨w,rfl⟩ | rfl
    · rw [extend_lift,extend_lift,Equiv.symm_apply_apply]
    · rw [extend_sentinel,extend_sentinel]
  exact hinv.injective

theorem extend_sentinel_iff (π : Equiv.Perm (Fin 14)) (a : Fin 15) :
    extend π a = 14 ↔ a = 14 := by
  rw [← extend_sentinel π]
  exact (extend_injective π).eq_iff

private theorem dir_diag : ∀ a : Fin 14, dir a a = false := by decide

private theorem adj_sentinel_left : ∀ a : Fin 15, adj 14 a = false := by decide

private theorem adj_sentinel_right : ∀ a : Fin 15, adj a 14 = false := by decide

private def twohot (a b : Fin 14) (u : Fin 14) : Bool := decide (u = a ∨ u = b)

private theorem graph_twohot (a b : Fin 14) :
    graphFun (twohot a b) = adj (lift a) (lift b) := by
  apply bool_eq
  simp only [graphFun, decide_eq_true_eq, twohot, adj, Bool.or_eq_true_iff]
  change (∃ u v : Fin 14, dir u v = true ∧ (u = a ∨ u = b) ∧ (v = a ∨ v = b)) ↔
    dir a b = true ∨ dir b a = true
  constructor
  · rintro ⟨u,v,he,hu,hv⟩
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rw [dir_diag] at he
      contradiction
    · exact Or.inl he
    · exact Or.inr he
    · rw [dir_diag] at he
      contradiction
  · rintro (hab | hba)
    · exact ⟨a,b,hab,Or.inl rfl,Or.inr rfl⟩
    · exact ⟨b,a,hba,Or.inr rfl,Or.inl rfl⟩

private theorem twohot_comp (π : Equiv.Perm (Fin 14)) (a b : Fin 14) :
    twohot (π a) (π b) ∘ ⇑π = twohot a b := by
  funext u
  simp only [Function.comp_apply,twohot,π.injective.eq_iff]

theorem adj_preserved (π : Equiv.Perm (Fin 14))
    (h : ∀ x : Fin 14 → Bool, graphFun (x ∘ ⇑π) = graphFun x)
    (a b : Fin 15) : adj (extend π a) (extend π b) = adj a b := by
  rcases real_or_sentinel a with ⟨a,rfl⟩ | rfl <;>
    rcases real_or_sentinel b with ⟨b,rfl⟩ | rfl
  · rw [extend_lift, extend_lift, ← graph_twohot, ← graph_twohot]
    rw [← h (twohot (π a) (π b)), twohot_comp]
  · simp only [extend_sentinel, adj_sentinel_right]
  · simp only [extend_sentinel, adj_sentinel_left]
  · simp only [extend_sentinel]

private theorem exists_map_iff
    (π : Equiv.Perm (Fin 14)) {p q : Fin 14 → Prop}
    (h : ∀ w, p (π w) ↔ q w) : (∃ w, p w) ↔ ∃ w, q w := by
  constructor
  · rintro ⟨w,hw⟩
    refine ⟨π.symm w, (h _).mp ?_⟩
    simpa only [Equiv.apply_symm_apply] using hw
  · rintro ⟨w,hw⟩
    exact ⟨π w,(h w).mpr hw⟩

theorem common₂_preserved (π : Equiv.Perm (Fin 14))
    (h : ∀ x : Fin 14 → Bool, graphFun (x ∘ ⇑π) = graphFun x)
    (a b : Fin 15) :
    common₂ (extend π a) (extend π b) = common₂ a b := by
  apply bool_eq
  simp only [common₂,decide_eq_true_eq]
  apply exists_map_iff π
  intro w
  simp only [← extend_lift π w, adj_preserved π h]

theorem hasCommon_preserved (π : Equiv.Perm (Fin 14))
    (h : ∀ x : Fin 14 → Bool, graphFun (x ∘ ⇑π) = graphFun x)
    (a b c : Fin 15) :
    hasCommon (extend π a) (extend π b) (extend π c) = hasCommon a b c := by
  apply bool_eq
  simp only [hasCommon,decide_eq_true_eq]
  apply exists_map_iff π
  intro w
  simp only [← extend_lift π w, adj_preserved π h]

theorem pair_preserved (π : Equiv.Perm (Fin 14))
    (h : ∀ x : Fin 14 → Bool, graphFun (x ∘ ⇑π) = graphFun x)
    (a b : Fin 15) : pair (extend π a) (extend π b) = pair a b := by
  simp only [pair, (extend_injective π).eq_iff, adj_preserved π h, common₂_preserved π h]

private theorem sentinel_flag (π : Equiv.Perm (Fin 14)) (a : Fin 15) :
    decide (extend π a = 14) = decide (a = 14) := by
  apply bool_eq
  simp only [decide_eq_true_eq, extend_sentinel_iff]

theorem fp_preserved (π : Equiv.Perm (Fin 14))
    (h : ∀ x : Fin 14 → Bool, graphFun (x ∘ ⇑π) = graphFun x)
    (a b c d : Fin 15) :
    fp (extend π a) (extend π b) (extend π c) (extend π d) = fp a b c d := by
  simp only [fp, pair_preserved π h, hasCommon_preserved π h, sentinel_flag π]

end Invariant

namespace Finite

open Invariant (fp lift)

def pairCode (a b c d : Nat) : Nat :=
  (15 * min a b + max a b) * 225 + 15 * min c d + max c d

def blocks : List (List Nat) :=
  [[226, 227, 228, 232, 233, 234, 236, 239, 258, 259, 260, 262, 263],
   [264, 266, 267, 269, 277, 278, 281, 284, 338, 341, 344, 354, 355],
   [356, 359, 402, 404, 1576, 1577, 1582, 1583, 1584, 1589, 1592, 1593, 1598],
   [1599, 1601, 1604, 1609, 1611, 1614, 1617, 1619, 2026, 2027, 2032, 2034, 2036],
   [2039, 2042, 2043, 2045, 2047, 2048, 2051, 2053, 2054, 2058, 2066, 2067, 2069]]

def label (i : Fin 65) : Nat :=
  (blocks.getD (i.val / 13) []).getD (i.val % 13) 0

def labelB (i : Fin 65) : Fin 14 := Fin.ofNat 14 (label i / 225)

def labelC (i : Fin 65) : Fin 15 := Fin.ofNat 15 (label i % 225 / 15)

def labelD (i : Fin 65) : Fin 15 := Fin.ofNat 15 (label i % 15)

private inductive SearchTree where
  | empty
  | node (key value : Nat) (less greater : SearchTree)

private def SearchTree.lookup (s : Nat) : SearchTree → Nat
  | .empty => 99999
  | .node key value less greater =>
    if s < key then less.lookup s else if key < s then greater.lookup s else value

/-- A finite table of the least code for each observed ordered graph signature. -/
private def table : SearchTree :=
  (.node 87364 259
    (.node 38528 2047
      (.node 16768 2067
        (.node 5760 2053
          (.node 3396 2027
            (.node 1344 2058
              (.node 770 2039
                (.node 258 2069 .empty .empty)
                (.node 1025 2069 .empty .empty))
              (.node 3073 2039
                (.node 1860 2027 .empty .empty)
                .empty))
            (.node 5120 2066
              (.node 4610 2054
                (.node 4098 2069 .empty .empty)
                .empty)
              (.node 5632 2051
                (.node 5248 2067 .empty .empty)
                .empty)))
          (.node 11588 2026
            (.node 8450 2054
              (.node 7808 2032
                (.node 7168 2036 .empty .empty)
                .empty)
              (.node 9540 2043
                (.node 9536 2042 .empty .empty)
                .empty))
            (.node 15360 2034
              (.node 13312 2036
                (.node 12290 2039 .empty .empty)
                .empty)
              (.node 16640 2066
                (.node 16385 2069 .empty .empty)
                .empty))))
        (.node 24960 2053
          (.node 21056 2042
            (.node 18816 2053
              (.node 18433 2054
                (.node 17152 2036 .empty .empty)
                (.node 18688 2051 .empty .empty))
              (.node 20544 2058
                (.node 19328 2032 .empty .empty)
                .empty))
            (.node 22600 2043
              (.node 22592 2042
                (.node 21064 2043 .empty .empty)
                .empty)
              (.node 24832 2051
                (.node 23104 2045 .empty .empty)
                .empty)))
          (.node 34112 2042
            (.node 28744 2027
              (.node 27008 2047
                (.node 26880 2048 .empty .empty)
                .empty)
              (.node 33793 2054
                (.node 30792 2026 .empty .empty)
                .empty))
            (.node 37888 2051
              (.node 34628 2026
                (.node 34116 2043 .empty .empty)
                .empty)
              (.node 38400 2048
                (.node 38016 2053 .empty .empty)
                .empty)))))
      (.node 71952 278
        (.node 66112 356
          (.node 53832 2026
            (.node 49408 2036
              (.node 46208 2032
                (.node 42304 2045 .empty .empty)
                (.node 49153 2039 .empty .empty))
              (.node 53320 2027
                (.node 49920 2034 .empty .empty)
                .empty))
            (.node 65538 404
              (.node 65537 404
                (.node 57728 2032 .empty .empty)
                .empty)
              (.node 66050 359
                (.node 65600 402 .empty .empty)
                .empty)))
          (.node 69906 284
            (.node 68160 355
              (.node 67648 356
                (.node 67585 359 .empty .empty)
                .empty)
              (.node 69890 269
                (.node 69888 266 .empty .empty)
                .empty))
            (.node 70416 236
              (.node 70032 281
                (.node 70016 267 .empty .empty)
                .empty)
              (.node 71936 264
                (.node 70418 239 .empty .empty)
                .empty))))
        (.node 82944 266
          (.node 74304 341
            (.node 73730 359
              (.node 72592 233
                (.node 72064 263 .empty .empty)
                .empty)
              (.node 74242 344
                (.node 73792 356 .empty .empty)
                .empty))
            (.node 78096 236
              (.node 76352 338
                (.node 75840 354 .empty .empty)
                .empty)
              (.node 80144 234
                (.node 78098 239 .empty .empty)
                .empty)))
          (.node 83488 278
            (.node 83072 267
              (.node 82977 284
                (.node 82945 269 .empty .empty)
                .empty)
              (.node 83456 264
                (.node 83104 281 .empty .empty)
                .empty))
            (.node 85025 239
              (.node 85024 236
                (.node 83584 263 .empty .empty)
                .empty)
              (.node 87360 260
                (.node 85664 233 .empty .empty)
                .empty))))))
    (.node 135682 1604
      (.node 102672 278
        (.node 93216 234
          (.node 89468 228
            (.node 87892 227
              (.node 87376 258
                (.node 87368 259 .empty .empty)
                (.node 87392 258 .empty .empty))
              (.node 89444 227
                (.node 87932 228 .empty .empty)
                .empty))
            (.node 91264 263
              (.node 91168 278
                (.node 91136 264 .empty .empty)
                .empty)
              (.node 91808 277
                (.node 91648 262 .empty .empty)
                .empty)))
          (.node 98368 356
            (.node 95612 228
              (.node 95576 227
                (.node 93856 232 .empty .empty)
                .empty)
              (.node 98305 359
                (.node 97660 226 .empty .empty)
                .empty))
            (.node 100416 341
              (.node 100353 344
                (.node 98880 354 .empty .empty)
                .empty)
              (.node 102656 264
                (.node 100928 338 .empty .empty)
                .empty))))
        (.node 115745 239
          (.node 106560 355
            (.node 104704 262
              (.node 103184 234
                (.node 102784 263 .empty .empty)
                .empty)
              (.node 105360 232
                (.node 104848 277 .empty .empty)
                .empty))
            (.node 110992 233
              (.node 108608 338
                (.node 107072 338 .empty .empty)
                .empty)
              (.node 115744 236
                (.node 113040 232 .empty .empty)
                .empty)))
          (.node 124576 232
            (.node 120188 228
              (.node 120168 227
                (.node 116256 234 .empty .empty)
                .empty)
              (.node 124064 233
                (.node 120700 226 .empty .empty)
                .empty))
            (.node 132416 1609
              (.node 132097 1619
                (.node 131330 1619 .empty .empty)
                .empty)
              (.node 135170 1619
                (.node 132420 1611 .empty .empty)
                .empty)))))
      (.node 157952 1598
        (.node 147840 1617
          (.node 140608 1592
            (.node 136832 1599
              (.node 136320 1617
                (.node 136192 1614 .empty .empty)
                (.node 136704 1601 .empty .empty))
              (.node 140034 1589
                (.node 139522 1604 .empty .empty)
                .empty))
            (.node 144896 1584
              (.node 143874 1589
                (.node 141124 1577 .empty .empty)
                .empty)
              (.node 147712 1614
                (.node 147457 1619 .empty .empty)
                .empty)))
          (.node 152128 1592
            (.node 149888 1599
              (.node 149760 1601
                (.node 149505 1604 .empty .empty)
                .empty)
              (.node 151624 1611
                (.node 151616 1609 .empty .empty)
                .empty))
            (.node 155904 1601
              (.node 154184 1593
                (.node 153664 1592 .empty .empty)
                .empty)
              (.node 156416 1584
                (.node 156032 1599 .empty .empty)
                .empty))))
        (.node 171648 1583
          (.node 166913 1589
            (.node 162376 1576
              (.node 160328 1577
                (.node 158592 1583 .empty .empty)
                .empty)
              (.node 165184 1592
                (.node 164865 1604 .empty .empty)
                .empty))
            (.node 169088 1599
              (.node 168960 1601
                (.node 167236 1577 .empty .empty)
                .empty)
              (.node 171008 1584
                (.node 169472 1598 .empty .empty)
                .empty)))
          (.node 182273 1589
            (.node 175428 1576
              (.node 173892 1576
                (.node 173380 1593 .empty .empty)
                .empty)
              (.node 179840 1582
                (.node 177792 1583 .empty .empty)
                .empty))
            (.node 186952 1576
              (.node 186440 1577
                (.node 182528 1584 .empty .empty)
                .empty)
              (.node 191360 1582
                (.node 190848 1583 .empty .empty)
                .empty)))))))

def minBySignature (s : Nat) : Nat :=
  table.lookup s

private def widen (i : Fin 10) : Fin 15 :=
  ⟨i.val, by have h := i.isLt; omega⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
theorem label_check :
    ∀ i : Fin 65,
      (0 : Fin 14) < labelB i ∧ labelC i < labelD i ∧ label i ≤ 2069 ∧
      pairCode 0 (labelB i).val (labelC i).val (labelD i).val = label i ∧
      minBySignature (fp 0 (lift (labelB i)) (labelC i) (labelD i)) = label i := by
  decide +kernel

set_option maxHeartbeats 7000000 in
set_option maxRecDepth 8000 in
private theorem image_ranges (b : Fin 10) :
    ∀ c d : Fin 15, b.val ≠ 0 → c ≠ d →
      minBySignature (fp 0 (widen b) c d) ≤ pairCode 0 b.val c.val d.val ∧
      minBySignature (fp (widen b) 0 c d) ≤ pairCode b.val 0 c.val d.val := by
  fin_cases b
  · intro c d hb
    exact (hb rfl).elim
  all_goals decide +kernel

theorem image_check (a b c d : Fin 15) (hab : a ≠ b) (hcd : c ≠ d)
    (hsmall : pairCode a.val b.val c.val d.val ≤ 2069) :
    minBySignature (fp a b c d) ≤ pairCode a.val b.val c.val d.val := by
  by_cases hsort : a.val ≤ b.val
  · have hs : (15 * a.val + b.val) * 225 ≤ 2069 := by
      simp only [pairCode, Nat.min_eq_left hsort, Nat.max_eq_right hsort] at hsmall
      omega
    have ha : a = 0 := Fin.ext (by omega)
    have hb : b.val < 10 := by omega
    have hb0 : b.val ≠ 0 := fun hz => hab (ha.trans (Fin.ext hz).symm)
    subst a
    exact (image_ranges ⟨b.val, hb⟩ c d hb0 hcd).1
  · have hsort' : b.val ≤ a.val := by omega
    have hs : (15 * b.val + a.val) * 225 ≤ 2069 := by
      simp only [pairCode, Nat.min_eq_right hsort', Nat.max_eq_left hsort'] at hsmall
      omega
    have hb : b = 0 := Fin.ext (by omega)
    have ha : a.val < 10 := by omega
    have ha0 : a.val ≠ 0 := fun hz => hab ((Fin.ext hz).trans hb.symm)
    subst b
    exact (image_ranges ⟨a.val, ha⟩ c d ha0 hcd).2

end Finite

end PEqualNP.Outside.L_meta_3537



open PEqualNP.Outside.L_meta_3537

theorem PEqualNP.Outside.L_meta_3537 :
    have x1 : (Fin (14 : ℕ) → Bool) → Bool := fun (x1 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true); have x2 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x2 x3 x4 x5 : ℕ) => ((15 : ℕ) * Min.min x2 x3 + Max.max x2 x3) * (225 : ℕ) + (15 : ℕ) * Min.min x4 x5 + Max.max x4 x5; have x3 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x3 : Equiv.Perm (Fin (14 : ℕ))) (x4 : Fin (15 : ℕ)) => if ↑x4 < (14 : ℕ) then ↑(x3 (Fin.ofNat (14 : ℕ) ↑x4)) else (14 : ℕ); ∀ (x4 : Fin (65 : ℕ)),   have x5 : ℕ := ([[(226 : ℕ), (227 : ℕ), (228 : ℕ), (232 : ℕ), (233 : ℕ), (234 : ℕ), (236 : ℕ), (239 : ℕ), (258 : ℕ), (259 : ℕ), (260 : ℕ), (262 : ℕ), (263 : ℕ)], [(264 : ℕ), (266 : ℕ), (267 : ℕ), (269 : ℕ), (277 : ℕ), (278 : ℕ), (281 : ℕ), (284 : ℕ), (338 : ℕ), (341 : ℕ), (344 : ℕ), (354 : ℕ), (355 : ℕ)], [(356 : ℕ), (359 : ℕ), (402 : ℕ), (404 : ℕ), (1576 : ℕ), (1577 : ℕ), (1582 : ℕ), (1583 : ℕ), (1584 : ℕ), (1589 : ℕ), (1592 : ℕ), (1593 : ℕ), (1598 : ℕ)], [(1599 : ℕ), (1601 : ℕ), (1604 : ℕ), (1609 : ℕ), (1611 : ℕ), (1614 : ℕ), (1617 : ℕ), (1619 : ℕ), (2026 : ℕ), (2027 : ℕ), (2032 : ℕ), (2034 : ℕ), (2036 : ℕ)], [(2039 : ℕ), (2042 : ℕ), (2043 : ℕ), (2045 : ℕ), (2047 : ℕ), (2048 : ℕ), (2051 : ℕ), (2053 : ℕ), (2054 : ℕ), (2058 : ℕ), (2066 : ℕ), (2067 : ℕ), (2069 : ℕ)]].getD (↑x4 / (13 : ℕ)) []).getD (↑x4 % (13 : ℕ)) (0 : ℕ);   have x6 : Fin (14 : ℕ) := Fin.ofNat (14 : ℕ) (x5 / (225 : ℕ));   have x7 : Fin (15 : ℕ) := Fin.ofNat (15 : ℕ) (x5 % (225 : ℕ) / (15 : ℕ));   have x8 : Fin (15 : ℕ) := Fin.ofNat (15 : ℕ) (x5 % (15 : ℕ));   (0 : Fin (14 : ℕ)) < x6 ∧ x7 < x8 ∧ ∀ (x9 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x10 : Fin (14 : ℕ) → Bool), x1 (x10 ∘ ⇑x9) = x1 x10) → x2 (0 : ℕ) ↑x6 ↑x7 ↑x8 ≤ x2 (↑(x9 (0 : Fin (14 : ℕ)))) (↑(x9 x6)) (x3 x9 x7) (x3 x9 x8) := by
  dsimp only
  intro i
  obtain ⟨hFirst, hOrder, hMax, hLabel, hMin⟩ := Finite.label_check i
  refine ⟨hFirst, hOrder, ?_⟩
  intro π hPreserves
  let a := Invariant.lift (π (0 : Fin 14))
  let b := Invariant.lift (π (Finite.labelB i))
  let c := Invariant.extend π (Finite.labelC i)
  let d := Invariant.extend π (Finite.labelD i)
  have hab : a ≠ b := by
    intro equal
    apply ne_of_lt hFirst
    apply π.injective
    have hVal : a.val = b.val := congrArg (fun u : Fin 15 => u.val) equal
    exact Fin.ext hVal
  have hcd : c ≠ d := fun equal => (ne_of_lt hOrder) (Invariant.extend_injective π equal)
  have hSig :
      Invariant.fp a b c d =
      Invariant.fp 0 (Invariant.lift (Finite.labelB i)) (Finite.labelC i) (Finite.labelD i) := by
    have hLiftZero : Invariant.lift (0 : Fin 14) = (0 : Fin 15) := by decide
    have h := Invariant.fp_preserved π hPreserves (Invariant.lift (0 : Fin 14))
      (Invariant.lift (Finite.labelB i)) (Finite.labelC i) (Finite.labelD i)
    simp only [Invariant.extend_lift] at h
    rw [hLiftZero] at h
    exact h
  have hCode : Finite.label i ≤ Finite.pairCode a.val b.val c.val d.val := by
    by_cases hsmall : Finite.pairCode a.val b.val c.val d.val ≤ 2069
    · have hImage := Finite.image_check a b c d hab hcd hsmall
      rwa [hSig, hMin] at hImage
    · exact hMax.trans (Nat.le_of_lt (Nat.lt_of_not_ge hsmall))
  have hComparison :
      Finite.pairCode 0 (Finite.labelB i).val (Finite.labelC i).val (Finite.labelD i).val
        ≤ Finite.pairCode a.val b.val c.val d.val := hLabel.le.trans hCode
  change Finite.pairCode 0 (Finite.labelB i).val (Finite.labelC i).val (Finite.labelD i).val ≤
    Finite.pairCode (π (0 : Fin 14)).val (π (Finite.labelB i)).val
      (if (Finite.labelC i).val < 14 then (π (Fin.ofNat 14 (Finite.labelC i).val)).val else 14)
      (if (Finite.labelD i).val < 14 then (π (Fin.ofNat 14 (Finite.labelD i).val)).val else 14)
  rw [← Invariant.extend_val π (Finite.labelC i), ← Invariant.extend_val π (Finite.labelD i)]
  exact hComparison
