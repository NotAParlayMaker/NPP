import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4131_849
    (rule0 :
      let encoded : List ℕ := [9, 10, 20, 24, 37, 42, 54, 55, 72, 74, 88, 89, 103, 106, 121, 137]
      let G := edgeGraph 11 (encoded.map fun w => (w / 16, w % 16))
      let data : List (ℕ × ℕ) := [(11, 5986356378520657894229315720148312279192243496157185), (47, 12958297458147505814240829151523017899598476265044910793778792325512697993169188286528462210932747281820835788226342723554682656999743443300547333611402730431873175575172847827680696865155021041966773496318379779190723462823941)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        ∀ q : Fin 2, B = U.card + (0 + q.val) → B < 2 * U.card →
        let block := data.getD q.val (0,0)
        ∀ m ∈ (List.range block.1).map (fun j => (block.2 >>> (16*j)) &&& 65535),
          ¬ (∀ i : Fin 16, m.testBit i.val = true →
            let w := encoded.getD i.val 0
            s(Fin.ofNat 11 (w / 16), Fin.ofNat 11 (w % 16)) ∈ U))
    (rule1 :
      let encoded : List ℕ := [9, 10, 20, 24, 37, 42, 54, 55, 72, 74, 88, 89, 103, 106, 121, 137]
      let G := edgeGraph 11 (encoded.map fun w => (w / 16, w % 16))
      let data : List (ℕ × ℕ) := [(96, 2372980451906980001649206208652614078519812694728790956356448683025924831693774128290497177792979560125336243228796272873065683550743657664517881213454799377614415211516327218545489205358374450770993169331485087096314831904329563673115838220697990915269964189920586366678335908575467088733913551129558505417817125860972584554114693112425157651626893334683855174323445021034828045937547121147695270617967519269750268463754904304061798489990763207410483630290763845)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        ∀ q : Fin 1, B = U.card + (2 + q.val) → B < 2 * U.card →
        let block := data.getD q.val (0,0)
        ∀ m ∈ (List.range block.1).map (fun j => (block.2 >>> (16*j)) &&& 65535),
          ¬ (∀ i : Fin 16, m.testBit i.val = true →
            let w := encoded.getD i.val 0
            s(Fin.ofNat 11 (w / 16), Fin.ofNat 11 (w % 16)) ∈ U))
    (rule2 :
      let encoded : List ℕ := [9, 10, 20, 24, 37, 42, 54, 55, 72, 74, 88, 89, 103, 106, 121, 137]
      let G := edgeGraph 11 (encoded.map fun w => (w / 16, w % 16))
      let data : List (ℕ × ℕ) := [(96, 2402699151626886411991503102175150153673391881280810854318539983212149760329080494120654080169583685246154603026791705701697328762081832915505349486815554492106641066486024894890566974665918351047413571572572778190603207740571700153276799927188403304594756686570011331654316564706241944552730290371729161047569034171946195834450536883194996125403870849922817756569095237731493447311018122119258919869508143474424401400702801024715371081455144482492757270112503893)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        ∀ q : Fin 1, B = U.card + (3 + q.val) → B < 2 * U.card →
        let block := data.getD q.val (0,0)
        ∀ m ∈ (List.range block.1).map (fun j => (block.2 >>> (16*j)) &&& 65535),
          ¬ (∀ i : Fin 16, m.testBit i.val = true →
            let w := encoded.getD i.val 0
            s(Fin.ofNat 11 (w / 16), Fin.ofNat 11 (w % 16)) ∈ U))
    (rule3 :
      let encoded : List ℕ := [9, 10, 20, 24, 37, 42, 54, 55, 72, 74, 88, 89, 103, 106, 121, 137]
      let G := edgeGraph 11 (encoded.map fun w => (w / 16, w % 16))
      let data : List (ℕ × ℕ) := [(47, 23684123698027387783960782518486454501523501579288492852919057949700465617061134272682993875010729284011184746597123404222132024913157285435012868426212886033276494855237241691134496149823166350904934085331694840937299949458908), (11, 95776586531580784005680230684182606174250449669404670), (1, 65535)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        ∀ q : Fin 3, B = U.card + (4 + q.val) → B < 2 * U.card →
        let block := data.getD q.val (0,0)
        ∀ m ∈ (List.range block.1).map (fun j => (block.2 >>> (16*j)) &&& 65535),
          ¬ (∀ i : Fin 16, m.testBit i.val = true →
            let w := encoded.getD i.val 0
            s(Fin.ofNat 11 (w / 16), Fin.ofNat 11 (w % 16)) ∈ U))
    : have x1 : List (ℕ × ℕ) := [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) x1; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x2 x3 →       PEqualNP.TopForm.TopForm x2 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card + (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → ∀ (x12 x13 : Finset (Fin (11 : ℕ))), x12.card = (7 : ℕ) → x2.IsVertexCover ↑x12 → x13 ⊆ x12 → (x2.deleteEdges ↑x8).IsVertexCover ↑(x12 \ x13) → x13.card ≤ x9 - x8.card := by
  intro E G C short least top dirty U B low high T X seven cover sub residual
  let d := B - U.card
  change X.card ≤ d
  by_contra! small
  have bound := Finset.card_le_card sub
  have dmax : d ≤ 6 := by omega
  have budget : B = U.card + d := by dsimp [d]; omega
  obtain ⟨Y, hYX, hY⟩ := Finset.exists_subset_card_eq (show d + 1 ≤ X.card by omega)
  let I := (Finset.univ : Finset (Fin 11)) \ T
  let S := (Finset.univ : Finset (Fin 11)) \ (T \ Y)
  have iy : Y ⊆ T := hYX.trans sub
  have four : I.card = 4 := by
    rw [show I = Finset.univ \ T from rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), seven]
    rfl
  have card : S.card = d + 5 := by
    have hsplit := Finset.card_sdiff_add_card_eq_card iy
    have hcard : S.card = 11 - (T \ Y).card := by
      rw [show S = Finset.univ \ (T \ Y) from rfl,
        Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      rfl
    omega
  have IS : I ⊆ S := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp h).1⟩
  have independent : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
    intro u hu v hv edge
    exact (cover edge).elim (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mp hv).2
  have disjoint : ∀ u ∈ S, ∀ v ∈ S, ¬ (G.deleteEdges ↑U).Adj u v := by
    intro u hu v hv edge
    rcases residual edge with a | b
    · obtain ⟨atT,notX⟩ := Finset.mem_sdiff.mp a
      exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mpr ⟨atT, fun h => notX (hYX h)⟩)
    · obtain ⟨atT,notX⟩ := Finset.mem_sdiff.mp b
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mpr ⟨atT, fun h => notX (hYX h)⟩)
  let encoded : List ℕ := [9, 10, 20, 24, 37, 42, 54, 55, 72, 74, 88, 89, 103, 106, 121, 137]
  let source (i : Fin 16) : Fin 11 := Fin.ofNat 11 (encoded.getD i.val 0 / 16)
  let target (i : Fin 16) : Fin 11 := Fin.ofNat 11 (encoded.getD i.val 0 % 16)
  have listed : ∀ i, G.Adj (source i) (target i) := by decide +kernel
  let bases : List (Finset (Fin 11)) := [{0, 1, 2, 3}, {0, 2, 3, 4}, {0, 1, 3, 5}, {0, 3, 4, 5}, {0, 1, 2, 6}, {0, 2, 4, 6}, {0, 1, 5, 6}, {0, 4, 5, 6}, {0, 1, 2, 7}, {0, 2, 4, 7}, {0, 1, 5, 7}, {0, 4, 5, 7}, {0, 2, 3, 8}, {0, 2, 6, 8}, {0, 2, 7, 8}, {1, 2, 3, 9}, {2, 3, 4, 9}, {1, 2, 6, 9}, {2, 4, 6, 9}, {1, 3, 5, 10}, {1, 5, 7, 10}, {1, 3, 9, 10}]
  let patterns : List (List ℕ) := [[1, 2, 4, 8, 16, 32, 64, 128, 256, 2048, 4096],
        [5, 20, 65, 68, 72, 80, 130, 132, 136, 144, 320, 384, 4100, 4104, 4112, 4352, 35, 42, 50, 268, 518, 548, 1034, 1048, 1296, 2051, 2065, 2096, 2564, 4288, 8258, 8288, 10304, 12290, 16513, 16544, 18560, 20481, 32777, 32808, 33025, 802, 1794, 28704, 30720, 33568, 35848],
        [69, 84, 148, 4116, 170, 178, 332, 396, 646, 1112, 1162, 1176, 1360, 1424, 2069, 2129, 4292, 4296, 4304, 4364, 4544, 5144, 5392, 16517, 20485, 32841, 33089, 551, 566, 930, 1082, 1308, 1922, 2099, 2567, 2612, 8291, 8298, 8306, 8774, 8804, 9290, 10307, 10352, 10820, 12330, 12338, 12482, 12806, 13322, 16547, 17060, 18563, 18577, 18608, 19076, 20673, 22545, 32811, 33037, 41064, 49289, 49320, 49537, 53257, 53505, 814, 1806, 1842, 9058, 10050, 13090, 14082, 28707, 28896, 29220, 30723, 30768, 30912, 31236, 33571, 33580, 35851, 35865, 35896, 36113, 41824, 44104, 50080, 52360, 61480, 36611, 36620, 36656, 62240, 64520],
        [2133, 4308, 694, 1210, 1372, 1436, 4556, 5336, 5404, 5584, 18581, 20677, 22549, 33101, 942, 1934, 1970, 2615, 8807, 8822, 9338, 10355, 10823, 10868, 12522, 12530, 12854, 12998, 13370, 13514, 17063, 18611, 19079, 19124, 22737, 35929, 36177, 41067, 49323, 49549, 53449, 53517, 53697, 1854, 9070, 10062, 10098, 13102, 13282, 14094, 14130, 14274, 28899, 29223, 29412, 30771, 30915, 30960, 31239, 31284, 31428, 33583, 35899, 36125, 41827, 41836, 44107, 44152, 50083, 50092, 52363, 52377, 52408, 52625, 56345, 56593, 61483, 61672, 36623, 36659, 36668, 44867, 44876, 44912, 53123, 53132, 53168, 62243, 62252, 62432, 64523, 64568, 64712, 65283, 65292, 65328],
        [5596, 22741, 1982, 10871, 13046, 13562, 19127, 36189, 53709, 10110, 13294, 14142, 14286, 14322, 29415, 30963, 31287, 31431, 31476, 41839, 44155, 50095, 52411, 52637, 56537, 56605, 56785, 61675, 36671, 44879, 44915, 44924, 53135, 53171, 53180, 62255, 62435, 62444, 64571, 64715, 64760, 65295, 65331, 65340, 65475, 65484, 65520],
        [14334, 31479, 56797, 44927, 53183, 62447, 64763, 65343, 65487, 65523, 65532],
        [65535]]
  have baseCheck : ∀ I : Finset (Fin 11),
      I.card = 4 → (∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v) → I ∈ bases := by
    decide +kernel
  let contains (S : Finset (Fin 11)) (m : ℕ) : Bool :=
    (List.finRange 16).all fun i =>
      !m.testBit i.val || decide (source i ∈ S ∧ target i ∈ S)
  have profiles : ∀ S : Finset (Fin 11), 5 ≤ S.card →
      (bases.any fun A => decide (A ⊆ S)) = true →
      ((patterns.getD (S.card-5) []).any (contains S)) = true := by
    decide +kernel
  have baseInside : (bases.any fun A => decide (A ⊆ S)) = true :=
    List.any_eq_true.mpr ⟨I, baseCheck I four independent, decide_eq_true IS⟩
  have hmatches := profiles S (by omega) baseInside
  rw [show S.card - 5 = d by omega] at hmatches
  obtain ⟨m, hm, ht⟩ := List.any_eq_true.mp hmatches
  have included : ∀ i : Fin 16, m.testBit i.val = true → s(source i, target i) ∈ U := by
    intro i hi
    have accepted := List.all_eq_true.mp ht i (List.mem_finRange i)
    have hboth : source i ∈ S ∧ target i ∈ S := by simpa [hi] using accepted
    by_contra missing
    exact disjoint _ hboth.1 _ hboth.2 (SimpleGraph.deleteEdges_adj.mpr ⟨listed i, missing⟩)
  have dCases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
  rcases dCases with hd | hd | hd | hd | hd | hd | hd
  · have hb : B = U.card + (0 + (0 : Fin 2).val) := by
      change B = U.card + 0
      omega
    exact (rule0 C short least top dirty (0 : Fin 2) hb high m
      (by
        change m ∈ [1, 2, 4, 8, 16, 32, 64, 128, 256, 2048, 4096]
        simpa [patterns, hd] using hm)) included
  · have hb : B = U.card + (0 + (1 : Fin 2).val) := by
      change B = U.card + 1
      omega
    exact (rule0 C short least top dirty (1 : Fin 2) hb high m
      (by
        change m ∈ [5, 20, 65, 68, 72, 80, 130, 132, 136, 144, 320, 384, 4100, 4104, 4112, 4352, 35, 42, 50, 268, 518, 548, 1034, 1048, 1296, 2051, 2065, 2096, 2564, 4288, 8258, 8288, 10304, 12290, 16513, 16544, 18560, 20481, 32777, 32808, 33025, 802, 1794, 28704, 30720, 33568, 35848]
        simpa [patterns, hd] using hm)) included
  · have hb : B = U.card + (2 + (0 : Fin 1).val) := by
      change B = U.card + 2
      omega
    exact (rule1 C short least top dirty (0 : Fin 1) hb high m
      (by
        change m ∈ [69, 84, 148, 4116, 170, 178, 332, 396, 646, 1112, 1162, 1176, 1360, 1424, 2069, 2129, 4292, 4296, 4304, 4364, 4544, 5144, 5392, 16517, 20485, 32841, 33089, 551, 566, 930, 1082, 1308, 1922, 2099, 2567, 2612, 8291, 8298, 8306, 8774, 8804, 9290, 10307, 10352, 10820, 12330, 12338, 12482, 12806, 13322, 16547, 17060, 18563, 18577, 18608, 19076, 20673, 22545, 32811, 33037, 41064, 49289, 49320, 49537, 53257, 53505, 814, 1806, 1842, 9058, 10050, 13090, 14082, 28707, 28896, 29220, 30723, 30768, 30912, 31236, 33571, 33580, 35851, 35865, 35896, 36113, 41824, 44104, 50080, 52360, 61480, 36611, 36620, 36656, 62240, 64520]
        simpa [patterns, hd] using hm)) included
  · have hb : B = U.card + (3 + (0 : Fin 1).val) := by
      change B = U.card + 3
      omega
    exact (rule2 C short least top dirty (0 : Fin 1) hb high m
      (by
        change m ∈ [2133, 4308, 694, 1210, 1372, 1436, 4556, 5336, 5404, 5584, 18581, 20677, 22549, 33101, 942, 1934, 1970, 2615, 8807, 8822, 9338, 10355, 10823, 10868, 12522, 12530, 12854, 12998, 13370, 13514, 17063, 18611, 19079, 19124, 22737, 35929, 36177, 41067, 49323, 49549, 53449, 53517, 53697, 1854, 9070, 10062, 10098, 13102, 13282, 14094, 14130, 14274, 28899, 29223, 29412, 30771, 30915, 30960, 31239, 31284, 31428, 33583, 35899, 36125, 41827, 41836, 44107, 44152, 50083, 50092, 52363, 52377, 52408, 52625, 56345, 56593, 61483, 61672, 36623, 36659, 36668, 44867, 44876, 44912, 53123, 53132, 53168, 62243, 62252, 62432, 64523, 64568, 64712, 65283, 65292, 65328]
        simpa [patterns, hd] using hm)) included
  · have hb : B = U.card + (4 + (0 : Fin 3).val) := by
      change B = U.card + 4
      omega
    exact (rule3 C short least top dirty (0 : Fin 3) hb high m
      (by
        change m ∈ [5596, 22741, 1982, 10871, 13046, 13562, 19127, 36189, 53709, 10110, 13294, 14142, 14286, 14322, 29415, 30963, 31287, 31431, 31476, 41839, 44155, 50095, 52411, 52637, 56537, 56605, 56785, 61675, 36671, 44879, 44915, 44924, 53135, 53171, 53180, 62255, 62435, 62444, 64571, 64715, 64760, 65295, 65331, 65340, 65475, 65484, 65520]
        simpa [patterns, hd] using hm)) included
  · have hb : B = U.card + (4 + (1 : Fin 3).val) := by
      change B = U.card + 5
      omega
    exact (rule3 C short least top dirty (1 : Fin 3) hb high m
      (by
        change m ∈ [14334, 31479, 56797, 44927, 53183, 62447, 64763, 65343, 65487, 65523, 65532]
        simpa [patterns, hd] using hm)) included
  · have hb : B = U.card + (4 + (2 : Fin 3).val) := by
      change B = U.card + 6
      omega
    exact (rule3 C short least top dirty (2 : Fin 3) hb high m
      (by
        change m ∈ [65535]
        simpa [patterns, hd] using hm)) included
