import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4247_7
    (search : let E : List ℕ := [33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528, 1026, 2052, 4104, 8208, 16385, 32769, 32772]
      let H : List ℕ := [6291, 12551, 25102, 51226]
      let N : List ℕ := [31, 1053, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 7313, 8207, 8455, 8718, 9229, 10251, 11337, 12295, 13573, 14723, 15809, 16414, 16910, 17436, 18458, 20502, 21556, 24590, 26124, 29446, 30500, 34842, 49178, 52248, 55442, 56496, 59914, 61000, 64386, 65504]
      ∃ (C : Circuit) (s : Fin 6), Monotone2 C ∧ NestedCover.ReadsBack 16 C ∧ C.size ≤ 22 ∧
        let read := fun m : ℕ => circuitFun 16 C (fun i => m.testBit i.val)
        (∀ m ∈ E, read m = true) ∧ (∀ m ∈ N, read m = false) ∧
        ∀ m ∈ H, read m = decide (m ∈ (if s.val = 5 then [6291,25102] else H.take s.val)))
    (cover : let E : List ℕ := [33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528, 1026, 2052, 4104, 8208, 16385, 32769, 32772]
      let H : List ℕ := [6291, 12551, 25102, 51226]
      let N : List ℕ := [31, 1053, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 7313, 8207, 8455, 8718, 9229, 10251, 11337, 12295, 13573, 14723, 15809, 16414, 16910, 17436, 18458, 20502, 21556, 24590, 26124, 29446, 30500, 34842, 49178, 52248, 55442, 56496, 59914, 61000, 64386, 65504]
      ∀ x : Fin 16 → Bool,
        (∃ m ∈ E, ∀ i : Fin 16, m.testBit i.val = true → x i = true) ∨
        (∃ m ∈ H, x = (fun i : Fin 16 => m.testBit i.val)) ∨
        (∃ m ∈ N, ∀ i : Fin 16, x i = true → m.testBit i.val = true))
    (propagate : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ x y : Fin n → Bool,
      (∀ i, x i = true → y i = true) → circuitFun n C x = true → circuitFun n C y = true) :
    have x1 : List ℕ := [(33 : ℕ), (34 : ℕ), (40 : ℕ), (66 : ℕ), (68 : ℕ), (80 : ℕ), (132 : ℕ), (136 : ℕ), (264 : ℕ), (272 : ℕ), (513 : ℕ), (528 : ℕ), (1026 : ℕ), (2052 : ℕ), (4104 : ℕ), (8208 : ℕ), (16385 : ℕ), (32769 : ℕ), (32772 : ℕ)]; have x2 : List ℕ := [(6291 : ℕ), (12551 : ℕ), (25102 : ℕ), (51226 : ℕ)]; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (6 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 : ℕ) x3 ∧ x3.size ≤ (22 : ℕ) ∧ ∀ (x5 : Fin (16 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x3 x5 = Decidable.decide (∃ x6 ∈ x1 ++ if ↑x4 = (5 : ℕ) then [(6291 : ℕ), (25102 : ℕ)] else List.take (↑x4) x2, ∀ (x7 : Fin (16 : ℕ)), x6.testBit ↑x7 = Bool.true → x5 x7 = Bool.true) := by
  let E : List ℕ := [33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528, 1026, 2052, 4104, 8208, 16385, 32769, 32772]
  let H : List ℕ := [6291, 12551, 25102, 51226]
  let N : List ℕ := [31, 1053, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 7313, 8207, 8455, 8718, 9229, 10251, 11337, 12295, 13573, 14723, 15809, 16414, 16910, 17436, 18458, 20502, 21556, 24590, 26124, 29446, 30500, 34842, 49178, 52248, 55442, 56496, 59914, 61000, 64386, 65504]
  change ∃ (C : Circuit) (s : Fin 6), Monotone2 C ∧ NestedCover.ReadsBack 16 C ∧ C.size ≤ 22 ∧
    ∀ x : Fin 16 → Bool, circuitFun 16 C x = decide (∃ m ∈ E ++ (if s.val = 5 then [6291,25102] else H.take s.val),
      ∀ i : Fin 16, m.testBit i.val = true → x i = true)
  obtain ⟨C,s,hmono,hback,hsize,hpos,hneg,hhole⟩ := search
  refine ⟨C,s,hmono,hback,hsize,?_⟩
  let extra : List ℕ := if s.val = 5 then [6291,25102] else H.take s.val
  have subset : ∀ m ∈ extra, m ∈ H := by
    intro m hm
    by_cases hs : s.val = 5
    · simp only [extra,hs,↓reduceIte,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl <;> decide
    · have h : m ∈ H.take s.val := by simpa [extra,hs] using hm
      exact List.mem_of_mem_take h
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro hx
    rcases cover x with ⟨m,he,hsub⟩ | ⟨m,hh,rfl⟩ | ⟨m,hn,hsub⟩
    · exact ⟨m,List.mem_append_left _ he,hsub⟩
    · have htrue := (hhole m hh).symm.trans hx
      have hm : m ∈ extra := of_decide_eq_true htrue
      exact ⟨m,List.mem_append_right _ hm,fun i hi => hi⟩
    · have impossible := propagate 16 C hmono x (fun i : Fin 16 => m.testBit i.val) hsub hx
      exact False.elim ((by decide : false ≠ true) ((hneg m hn).symm.trans impossible))
  · rintro ⟨m,hm,hsub⟩
    apply propagate 16 C hmono (fun i : Fin 16 => m.testBit i.val) x hsub
    rcases List.mem_append.mp hm with he | hh
    · exact hpos m he
    · exact (hhole m (subset m hh)).trans (decide_eq_true hh)
