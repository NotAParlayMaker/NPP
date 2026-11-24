import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4673_487
    (witness :
      let tab : List ℕ := [23436204834831, 182934682992880, 219356612005632, 272683161939968, 5726601217, 281444911874048, 8606650368, 62088299872512, 98510228881424, 281444911874048, 2920583340034, 515397075456, 17230398496, 1752350031936, 44152348018692, 79749239079048, 281444911874048, 2937813672994, 281462091752482, 98515669155857, 281444911890944, 281449206858257, 62096905539840, 281444911874184, 281453501813128, 281453501812736, 133832107296788, 281453501814804, 281449206841345, 63737570492736, 281449206874433]
      ∃ D : Circuit, ∃ u : ℕ, IsAO2 31 D ∧ D.size ≤ 20 ∧ D.output < 31 + D.size ∧ u < 31 + D.size ∧
        (∀ j < D.size, (gateAt D j).inputs.Nodup ∧
          (31 + j = D.output ∨ 31 + j = u ∨ ∃ k < D.size, 31 + j ∈ (gateAt D k).inputs)) ∧
        ∀ k : Fin 48, let row := List.ofFn (fun i : Fin 31 => (tab.getD i.val 0).testBit k.val)
          D.eval row = decide (k.val < 16) ∧ ((281473500315648 : ℕ).testBit k.val = true →
            (D.wires row).getD u false = (30064771072 : ℕ).testBit k.val))
    (certifyMain :
      let tab : List ℕ := [23436204834831, 182934682992880, 219356612005632, 272683161939968, 5726601217, 281444911874048, 8606650368, 62088299872512, 98510228881424, 281444911874048, 2920583340034, 515397075456, 17230398496, 1752350031936, 44152348018692, 79749239079048, 281444911874048, 2937813672994, 281462091752482, 98515669155857, 281444911890944, 281449206858257, 62096905539840, 281444911874184, 281453501813128, 281453501812736, 133832107296788, 281453501814804, 281449206841345, 63737570492736, 281449206874433]
      let masks : List ℕ := [1, 2, 4, 8, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 17408, 163840, 181248, 8704, 81920, 90624, 6144, 1064960, 1071104, 3072, 532480, 535552, 1536, 266240, 267776]
      let map := fun (x : Fin 21 → Bool) (i : Fin 31) => (List.range 21).any fun j =>
        (masks.getD i.val 0).testBit j && x (Fin.ofNat 21 j)
      ∀ D : Circuit, Monotone2 D →
        (∀ k : Fin 48, D.eval (List.ofFn fun i : Fin 31 => (tab.getD i.val 0).testBit k.val) = decide (k.val < 16)) →
        ∀ x : Fin 21 → Bool, D.eval (List.ofFn (map x)) =
          ([(0,3137),(1,2832),(2,1416),(3,708)] : List (ℕ × ℕ)).any (fun r =>
            x (Fin.ofNat 21 r.1) && (List.range 12).any fun j => r.2.testBit j && x (Fin.ofNat 21 (j + 9))))
    (certifyAux :
      let sub : List ℕ := [43704, 340776, 408624, 507960, 1, 524280, 2, 115656, 183504, 524280, 5440, 960, 4, 3264, 82240, 148544, 524280, 5444, 524284, 183505, 524280, 524281, 115658, 524280, 524282, 524282, 249296, 524282, 524281, 118728, 524281]
      let masks : List ℕ := [1, 2, 4, 8, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 17408, 163840, 181248, 8704, 81920, 90624, 6144, 1064960, 1071104, 3072, 532480, 535552, 1536, 266240, 267776]
      let map := fun (x : Fin 21 → Bool) (i : Fin 31) => (List.range 21).any fun j =>
        (masks.getD i.val 0).testBit j && x (Fin.ofNat 21 j)
      ∀ (D : Circuit) (u : ℕ), Monotone2 D →
        (∀ k : Fin 19, (D.wires (List.ofFn fun i : Fin 31 => (sub.getD i.val 0).testBit k.val)).getD u false =
          decide (k.val < 3)) →
        ∀ x : Fin 21 → Bool,
          ([(0,3137),(1,2832),(2,1416),(3,708)] : List (ℕ × ℕ)).any (fun r =>
            x (Fin.ofNat 21 r.1) && (List.range 12).any fun j => r.2.testBit j && x (Fin.ofNat 21 (j + 9))) = false →
          (D.wires (List.ofFn (map x))).getD u false = (x 9 || x 11 || x 17))
    (assemble :
      let masks : List ℕ := [1, 2, 4, 8, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 17408, 163840, 181248, 8704, 81920, 90624, 6144, 1064960, 1071104, 3072, 532480, 535552, 1536, 266240, 267776]
      let map := fun (x : Fin 21 → Bool) (i : Fin 31) => (List.range 21).any fun j =>
        (masks.getD i.val 0).testBit j && x (Fin.ofNat 21 j)
      let good := fun (n : ℕ) (C : Circuit) (v : ℕ) =>
        IsAO2 n C ∧ C.output < n + C.size ∧ v < n + C.size ∧
        ∀ j < C.size, (gateAt C j).inputs.Nodup ∧
          (n + j = C.output ∨ n + j = v ∨ ∃ k < C.size, n + j ∈ (gateAt C k).inputs)
      ∀ (D : Circuit) (u : ℕ), good 31 D u → ∃ (C : Circuit) (v : ℕ),
        good 21 C v ∧ C.size ≤ D.size + 25 ∧
        ∀ x : Fin 21 → Bool, let row := List.ofFn (map x)
          C.eval (List.ofFn x) = (([(4,354),(5,177),(6,2092),(7,1046),(8,523)] : List (ℕ × ℕ)).any (fun r =>
            x (Fin.ofNat 21 r.1) && (List.range 12).any fun j => r.2.testBit j && x (Fin.ofNat 21 (j + 9))) ||
            D.eval row) ∧ (C.wires (List.ofFn x)).getD v false = (D.wires row).getD u false) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 (21 : ℕ) x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (21 : ℕ) + x1.size ∧ x2 < (21 : ℕ) + x1.size ∧ (∀ x3 < x1.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).inputs.Nodup ∧ ((21 : ℕ) + x3 = x1.output ∨ (21 : ℕ) + x3 = x2 ∨ ∃ x5 < x1.size, (21 : ℕ) + x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).inputs)) ∧ ∀ (x3 : Fin (21 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (9 : ℕ)) (x5 : Fin (12 : ℕ)), ([(1 : ℕ), (3 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (9 : ℕ), (10 : ℕ), (11 : ℕ)].getD ↑x4 (0 : ℕ) + ↑x5 + (15 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x3 (Fin.castAdd (12 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (9 : ℕ) x5) = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (9 : Fin (21 : ℕ)) || x3 (11 : Fin (21 : ℕ)) || x3 (17 : Fin (21 : ℕ)))) := by
  obtain ⟨D, u, ao, small, bounded, ubound, dLive, tests⟩ := witness
  have mono : Monotone2 D := by
    intro g hg
    have ops := ao.1 g hg
    exact ⟨ops, le_of_eq (ao.2.2 g hg)⟩
  obtain ⟨C, v, ⟨cAO, cBound, vBound, cLive⟩, cost, joined⟩ := assemble D u ⟨ao, bounded, ubound, dLive⟩
  refine ⟨C, v, cAO, by omega, cBound, vBound, cLive, ?_⟩
  intro x
  obtain ⟨value, aux⟩ := joined x
  have core := certifyMain D mono (fun k => (tests k).1) x
  constructor
  · rw [value, core, ← List.any_append]
    let data : List (ℕ × ℕ) := [(4,354),(5,177),(6,2092),(7,1046),(8,523),
      (0,3137),(1,2832),(2,1416),(3,708)]
    let incidence (p : Fin 9) (l : Fin 12) :=
      (([1,3,4,5,6,7,9,10,11] : List ℕ).getD p.val 0 + l.val + 15) % 13 ∈ ([0,1,3,9] : List ℕ)
    have geometry : ∀ p : Fin 9, ∀ l : Fin 12, incidence p l ↔
        ∃ r ∈ data, r.1 = p.val ∧ r.2.testBit l.val = true := by decide
    have pointIdx : ∀ r ∈ data, r.1 < 9 := by decide
    have pointPlace (p : Fin 9) : Fin.ofNat 21 p.val = Fin.castAdd 12 p := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by have h := p.isLt; omega)
    have linePlace (l : Fin 12) : Fin.ofNat 21 (l.val + 9) = Fin.natAdd 9 l := by
      apply Fin.ext
      change (l.val + 9) % 21 = 9 + l.val
      rw [Nat.mod_eq_of_lt (by have h := l.isLt; omega), Nat.add_comm]
    change data.any (fun r => x (Fin.ofNat 21 r.1) &&
      (List.range 12).any fun j => r.2.testBit j && x (Fin.ofNat 21 (j + 9))) = true ↔
      ∃ (p : Fin 9) (l : Fin 12), incidence p l ∧ x (Fin.castAdd 12 p) = true ∧ x (Fin.natAdd 9 l) = true
    constructor
    · intro t
      obtain ⟨r, hr, h⟩ := List.any_eq_true.mp t
      simp only [Bool.and_eq_true] at h
      obtain ⟨j, hj, on⟩ := List.any_eq_true.mp h.2
      simp only [Bool.and_eq_true] at on
      let p : Fin 9 := ⟨r.1, pointIdx r hr⟩
      let l : Fin 12 := ⟨j, List.mem_range.mp hj⟩
      refine ⟨p, l, (geometry p l).mpr ⟨r, hr, rfl, on.1⟩, ?_, ?_⟩
      · rw [← pointPlace]
        exact h.1
      · rw [← linePlace]
        exact on.2
    · rintro ⟨p, l, hit, hp, hl⟩
      obtain ⟨r, hr, rIndex, bit⟩ := (geometry p l).mp hit
      apply List.any_eq_true.mpr
      refine ⟨r, hr, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨by rwa [rIndex, pointPlace], List.any_eq_true.mpr ⟨l.val, List.mem_range.mpr l.isLt, ?_⟩⟩
      simp only [Bool.and_eq_true, linePlace]
      exact ⟨bit, hl⟩
  · intro zero
    rw [aux]
    have values := value.symm
    rw [zero, Bool.or_eq_false_iff] at values
    apply certifyAux D u mono ?_ x (core.symm.trans values.2)
    let full : List ℕ := [23436204834831, 182934682992880, 219356612005632, 272683161939968, 5726601217, 281444911874048, 8606650368, 62088299872512, 98510228881424, 281444911874048, 2920583340034, 515397075456, 17230398496, 1752350031936, 44152348018692, 79749239079048, 281444911874048, 2937813672994, 281462091752482, 98515669155857, 281444911890944, 281449206858257, 62096905539840, 281444911874184, 281453501813128, 281453501812736, 133832107296788, 281453501814804, 281449206841345, 63737570492736, 281449206874433]
    let sub : List ℕ := [43704, 340776, 408624, 507960, 1, 524280, 2, 115656, 183504, 524280, 5440, 960, 4, 3264, 82240, 148544, 524280, 5444, 524284, 183505, 524280, 524281, 115658, 524280, 524282, 524282, 249296, 524282, 524281, 118728, 524281]
    let selected (k : Fin 19) : Fin 48 := Fin.ofNat 48
      (([32,33,34,27,29,31,35,36,37,38,39,40,41,42,43,44,45,46,47] : List ℕ).getD k.val 0)
    have correspondence : ∀ k : Fin 19,
        (281473500315648 : ℕ).testBit (selected k).val = true ∧
        (30064771072 : ℕ).testBit (selected k).val = decide (k.val < 3) ∧
        ∀ i : Fin 31, (full.getD i.val 0).testBit (selected k).val = (sub.getD i.val 0).testBit k.val := by decide
    intro k
    obtain ⟨active, labels, columns⟩ := correspondence k
    have checked := (tests (selected k)).2 active
    change (D.wires (List.ofFn fun i : Fin 31 => (full.getD i.val 0).testBit (selected k).val)).getD u false = _ at checked
    rw [show (fun i : Fin 31 => (full.getD i.val 0).testBit (selected k).val) =
      (fun i : Fin 31 => (sub.getD i.val 0).testBit k.val) from funext columns, labels] at checked
    exact checked
