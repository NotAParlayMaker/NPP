import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4883_601
    (cut : (let ok := fun (A V : List (BitVec 24)) => ∀ i : Fin V.length,
      let old := A ++ V.take i.val
      ∃ a ∈ old, ∃ b ∈ old, V.get i = a &&& b ∨ V.get i = a ||| b
    ∀ (A V : List (BitVec 24)) (t : BitVec 24), V.length ≤ 13 →
      t ∈ A ++ V → ok A V →
      ∃ F K Z : List (BitVec 24), F.length ≤ 8 ∧ K.length ≤ 6 ∧ Z.length ≤ 5 ∧
        ok A F ∧ (∀ k ∈ K, k ∈ A ++ F) ∧ ok K Z ∧ t ∈ K ++ Z))
    (exclude : (let B : List ℕ := [375475, 474471, 650134, 786390, 1015671, 1166075, 1299821, 1374315, 1631101, 1832829, 2723570, 3722473, 4471039, 4557534, 4658652, 5208028, 5554429, 11714683, 13684585, 13733778, 13836100, 13897692, 13909795, 14384980]
    let A : List (BitVec 24) := [202052, 276515, 549652, 1097833, 101010, 10616859, 4456668, 2624736, 13635328, 751444]
    let ok := fun (A V : List (BitVec 24)) => ∀ i : Fin V.length,
      let old := A ++ V.take i.val
      ∃ a ∈ old, ∃ b ∈ old, V.get i = a &&& b ∨ V.get i = a ||| b
    ∀ b ∈ B, ∀ F K Z : List (BitVec 24),
      let A' := A ++ [BitVec.ofNat 24 b]
      F.length ≤ 8 → K.length ≤ 6 → Z.length ≤ 5 →
      ok A' F → (∀ k ∈ K, k ∈ A' ++ F) → ok K Z → 16773120 ∉ K ++ Z)) :
    ∀ x1 ∈ [(375475 : BitVec (24 : ℕ)), (474471 : BitVec (24 : ℕ)), (650134 : BitVec (24 : ℕ)), (786390 : BitVec (24 : ℕ)), (1015671 : BitVec (24 : ℕ)), (1166075 : BitVec (24 : ℕ)), (1299821 : BitVec (24 : ℕ)), (1374315 : BitVec (24 : ℕ)), (1631101 : BitVec (24 : ℕ)), (1832829 : BitVec (24 : ℕ)), (2723570 : BitVec (24 : ℕ)), (3722473 : BitVec (24 : ℕ)), (4471039 : BitVec (24 : ℕ)), (4557534 : BitVec (24 : ℕ)), (4658652 : BitVec (24 : ℕ)), (5208028 : BitVec (24 : ℕ)), (5554429 : BitVec (24 : ℕ)), (11714683 : BitVec (24 : ℕ)), (13684585 : BitVec (24 : ℕ)), (13733778 : BitVec (24 : ℕ)), (13836100 : BitVec (24 : ℕ)), (13897692 : BitVec (24 : ℕ)), (13909795 : BitVec (24 : ℕ)), (14384980 : BitVec (24 : ℕ))],   ∀ (x3 : List (BitVec (24 : ℕ))),     have x4 : List (BitVec (24 : ℕ)) := [(202052 : BitVec (24 : ℕ)), (276515 : BitVec (24 : ℕ)), (549652 : BitVec (24 : ℕ)), (1097833 : BitVec (24 : ℕ)), (101010 : BitVec (24 : ℕ)), (10616859 : BitVec (24 : ℕ)), (4456668 : BitVec (24 : ℕ)), (2624736 : BitVec (24 : ℕ)), (13635328 : BitVec (24 : ℕ)), (751444 : BitVec (24 : ℕ))] ++ [x1];     (16773120 : BitVec (24 : ℕ)) ∈ x4 ++ x3 →       (∀ (x6 : Fin x3.length),           have x7 : List (BitVec (24 : ℕ)) := x4 ++ List.take (↑x6) x3;           ∃ x8 ∈ x7, ∃ x9 ∈ x7, x3.get x6 = x8 &&& x9 ∨ x3.get x6 = x8 ||| x9) →         (14 : ℕ) ≤ x3.length := by
  intro s hs V A ht hv
  let B : List ℕ := [375475, 474471, 650134, 786390, 1015671, 1166075, 1299821, 1374315, 1631101, 1832829, 2723570, 3722473, 4471039, 4557534, 4658652, 5208028, 5554429, 11714683, 13684585, 13733778, 13836100, 13897692, 13909795, 14384980]
  have mem : s ∈ B.map (BitVec.ofNat 24) := hs
  obtain ⟨b, hb, he⟩ := List.mem_map.mp mem
  by_contra hlarge
  obtain ⟨F, K, Z, hf, hk, hz, hfok, hports, hzok, htarget⟩ :=
    cut A V 16773120 (by omega) ht hv
  subst s
  exact exclude b hb F K Z hf hk hz hfok hports hzok htarget
