import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2644_611
    (classify : let P : List (BitVec 17) := List.ofFn (fun i : Fin 20 => BitVec.ofNat 17 ((([281492223819809, 1133875888129, 1172526334978, 1125968895279236, 4535503290408, 4672934907912, 1075839504] : List Nat).getD (i.val / 3) 0) >>> (17*(i.val % 3))))
    let N : List (BitVec 17) := List.ofFn (fun i : Fin 44 => BitVec.ofNat 17 ((([37710084833311, 72894724836377, 105880207626503, 149775207768079, 211227835245581, 290513739331971, 352224097354780, 581044215242766, 688591171389465, 796138098827277, 933285659721153, 1161539248252428, 1592276197654554, 2096509234543490, 17175801416] : List Nat).getD (i.val / 3) 0) >>> (17*(i.val % 3))))
    let H : List (BitVec 17) := List.ofFn (fun i : Fin 8 => BitVec.ofNat 17 ((([431250721347731, 721507934964761, 11009311772] : List Nat).getD (i.val / 3) 0) >>> (17*(i.val % 3))))
    ∀ F : BitVec 17 → Bool,
      ((∀ x ∈ P, F x = true) ∧ (∀ x ∈ N, F x = false) ∧
       (∀ x y : BitVec 17, (x &&& y) = x → F x = true → F y = true)) ↔
      ∃ select : BitVec 17 → Bool, ∀ x,
        F x = ((P.any fun a => (a &&& x) == a) || (H.contains x && select x)))
    (search : let P : List (BitVec 17) := List.ofFn (fun i : Fin 20 => BitVec.ofNat 17 ((([281492223819809, 1133875888129, 1172526334978, 1125968895279236, 4535503290408, 4672934907912, 1075839504] : List Nat).getD (i.val / 3) 0) >>> (17*(i.val % 3))))
    let H : List (BitVec 17) := List.ofFn (fun i : Fin 8 => BitVec.ofNat 17 ((([431250721347731, 721507934964761, 11009311772] : List Nat).getD (i.val / 3) 0) >>> (17*(i.val % 3))))
    ∃ (k : Nat) (C : Circuit),
      (([18131750489313308587, 12321848583706935296, 9223512776490647680, 9223372036854775808] : List Nat).getD (k / 64) 0).testBit (k % 64) = true ∧
      Monotone2 C ∧ NestedCover.ReadsBack 17 C ∧ C.size ≤ 23 ∧
      (∃ i j : Fin C.gates.length, i < j ∧ ∃ v ∈ (C.gates.get i).inputs,
        17 ≤ v ∧ v ∈ (C.gates.get j).inputs) ∧
      ∀ x : BitVec 17, circuitFun 17 C (fun i => x.getLsbD i.val) =
        ((P.any fun a => (a &&& x) == a) ||
          (H.contains x && k.testBit (H.idxOf x)))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (17 : ℕ) x1 ∧       x1.size ≤ (23 : ℕ) ∧         (∀ x2 ∈ [(33 : ℕ), (513 : ℕ), (16385 : ℕ), (65537 : ℕ), (34 : ℕ), (66 : ℕ), (1026 : ℕ), (32770 : ℕ), (68 : ℕ), (132 : ℕ), (2052 : ℕ), (65540 : ℕ), (40 : ℕ), (136 : ℕ), (264 : ℕ), (4104 : ℕ), (80 : ℕ), (272 : ℕ), (528 : ℕ), (8208 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x1 fun (x4 : Fin (17 : ℕ)) => x2.testBit ↑x4) = Bool.true) ∧           ∀             x2 ∈               have x3 : List ℕ :=                 have x3 : List ℕ :=                   have x3 : List ℕ := [(92682 : ℕ), (97154 : ℕ), (117784 : ℕ), (122032 : ℕ), (126536 : ℕ), (131040 : ℕ)];                   (58892 : ℕ) :: (63268 : ℕ) :: (67610 : ℕ) :: (81946 : ℕ) :: (88210 : ℕ) :: x3;                 have x4 : List ℕ := (40973 : ℕ) :: (44105 : ℕ) :: (46341 : ℕ) :: (48577 : ℕ) :: (49180 : ℕ) :: (54324 : ℕ) :: x3;                 (29446 : ℕ) :: (33821 : ℕ) :: (34841 : ℕ) :: (36885 : ℕ) :: (40081 : ℕ) :: x4;               have x4 : List ℕ :=                 have x4 : List ℕ := (16414 : ℕ) :: (16910 : ℕ) :: (17436 : ℕ) :: (18458 : ℕ) :: (20502 : ℕ) :: (24590 : ℕ) :: x3;                 (8718 : ℕ) :: (9229 : ℕ) :: (10251 : ℕ) :: (12295 : ℕ) :: (14723 : ℕ) :: x4;               have x5 : List ℕ := (4243 : ℕ) :: (4359 : ℕ) :: (5141 : ℕ) :: (6163 : ℕ) :: (8207 : ℕ) :: (8455 : ℕ) :: x4;               (31 : ℕ) :: (2075 : ℕ) :: (2195 : ℕ) :: (3097 : ℕ) :: (4119 : ℕ) :: x5,             (PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x1 fun (x4 : Fin (17 : ℕ)) => x2.testBit ↑x4) = Bool.false := by
  let P : List (BitVec 17) := List.ofFn (fun i : Fin 20 => BitVec.ofNat 17 ((([281492223819809, 1133875888129, 1172526334978, 1125968895279236, 4535503290408, 4672934907912, 1075839504] : List Nat).getD (i.val / 3) 0) >>> (17*(i.val % 3))))
  let N : List (BitVec 17) := List.ofFn (fun i : Fin 44 => BitVec.ofNat 17 ((([37710084833311, 72894724836377, 105880207626503, 149775207768079, 211227835245581, 290513739331971, 352224097354780, 581044215242766, 688591171389465, 796138098827277, 933285659721153, 1161539248252428, 1592276197654554, 2096509234543490, 17175801416] : List Nat).getD (i.val / 3) 0) >>> (17*(i.val % 3))))
  let H : List (BitVec 17) := List.ofFn (fun i : Fin 8 => BitVec.ofNat 17 ((([431250721347731, 721507934964761, 11009311772] : List Nat).getD (i.val / 3) 0) >>> (17*(i.val % 3))))
  obtain ⟨k,C,_orbit,hm,hb,hs,_sharing,eq⟩ := search
  let F (x : BitVec 17) := circuitFun 17 C (fun i => x.getLsbD i.val)
  obtain ⟨hp,hn,_⟩ := (classify F).mpr ⟨fun x => k.testBit (H.idxOf x),eq⟩
  let ps : List Nat := [33, 513, 16385, 65537, 34, 66, 1026, 32770, 68, 132, 2052, 65540, 40, 136, 264, 4104, 80, 272, 528, 8208]
  let ns : List Nat := [31, 2075, 2195, 3097, 4119, 4243, 4359, 5141, 6163, 8207, 8455, 8718, 9229, 10251, 12295, 14723, 16414, 16910, 17436, 18458, 20502, 24590, 29446, 33821, 34841, 36885, 40081, 40973, 44105, 46341, 48577, 49180, 54324, 58892, 63268, 67610, 81946, 88210, 92682, 97154, 117784, 122032, 126536, 131040]
  have pos : ∀ m ∈ ps, BitVec.ofNat 17 m ∈ P := by decide +kernel
  have neg : ∀ m ∈ ns, BitVec.ofNat 17 m ∈ N := by decide +kernel
  have coord (m : Nat) : F (BitVec.ofNat 17 m) = circuitFun 17 C (fun i => m.testBit i.val) := by
    apply congrArg (circuitFun 17 C)
    funext i
    simp only [BitVec.getLsbD_ofNat,i.isLt,decide_true,Bool.true_and]
  refine ⟨C,hm,hb,hs,?_,?_⟩
  · intro m hx
    exact (coord m).symm.trans (hp _ (pos _ hx))
  · intro m hx
    exact (coord m).symm.trans (hn _ (neg _ hx))
