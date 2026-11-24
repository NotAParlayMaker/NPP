import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3785_487
    (witness :
      let tab : List ℕ := [2863267855,3435921648,4042264320,4278251520,1431633921,4294901760,
        16715776,252641536,858980368,4294901760,5578754,999936,50529312,3375168,84215812,
        286326920,4294901760,56042530,4294911010,2004287505,4294918656,4294918673,268374272,
        4294901896,4294906248,4294905856,926353428,4294907924,4294901761,255820096,4294934849]
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 18 ∧ D.output < 31 + D.size ∧
        ∀ k : Fin 32, D.eval (List.ofFn fun i : Fin 31 => (tab.getD i.val 0).testBit k.val) = decide (k.val < 16))
    (certify :
      let tab : List ℕ := [2863267855,3435921648,4042264320,4278251520,1431633921,4294901760,
        16715776,252641536,858980368,4294901760,5578754,999936,50529312,3375168,84215812,
        286326920,4294901760,56042530,4294911010,2004287505,4294918656,4294918673,268374272,
        4294901896,4294906248,4294905856,926353428,4294907924,4294901761,255820096,4294934849]
      let masks : List ℕ := [1,2,4,8,512,1024,2048,4096,8192,16384,32768,65536,131072,
        262144,524288,1048576,17408,163840,181248,8704,81920,90624,6144,1064960,1071104,
        3072,532480,535552,1536,266240,267776]
      let map := fun (x : Fin 21 → Bool) (i : Fin 31) => (List.range 21).any fun j =>
        (masks.getD i.val 0).testBit j && x (Fin.ofNat 21 j)
      ∀ D : Circuit, Monotone2 D →
        (∀ k : Fin 32, D.eval (List.ofFn fun i : Fin 31 => (tab.getD i.val 0).testBit k.val) = decide (k.val < 16)) →
        ∀ x : Fin 21 → Bool, D.eval (List.ofFn (map x)) =
          ([(0,3137),(1,2832),(2,1416),(3,708)] : List (ℕ × ℕ)).any (fun r =>
            x (Fin.ofNat 21 r.1) && (List.range 12).any fun j => r.2.testBit j && x (Fin.ofNat 21 (j + 9))))
    (assemble :
      let masks : List ℕ := [1,2,4,8,512,1024,2048,4096,8192,16384,32768,65536,131072,
        262144,524288,1048576,17408,163840,181248,8704,81920,90624,6144,1064960,1071104,
        3072,532480,535552,1536,266240,267776]
      let map := fun (x : Fin 21 → Bool) (i : Fin 31) => (List.range 21).any fun j =>
        (masks.getD i.val 0).testBit j && x (Fin.ofNat 21 j)
      ∀ D : Circuit, Monotone2 D → D.output < 31 + D.size →
        ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 25 ∧ C.output < 21 + C.size ∧
          ∀ x : Fin 21 → Bool, C.eval (List.ofFn x) =
            (([(4,354),(5,177),(6,2092),(7,1046),(8,523)] : List (ℕ × ℕ)).any (fun r =>
              x (Fin.ofNat 21 r.1) && (List.range 12).any fun j => r.2.testBit j && x (Fin.ofNat 21 (j + 9))) ||
              D.eval (List.ofFn (map x)))) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (43 : ℕ) ∧       x1.output < (21 : ℕ) + x1.size ∧         have x2 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))];         have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         ∀ (x5 x6 : Finset (Fin (13 : ℕ))), x1.eval (List.map (x3 x5 x6) x2) = Bool.true ↔ ∃ x7 ∈ x5, ↑x7 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x8 ∈ x6, x4 x7 x8 := by
  obtain ⟨D, hD, short, Doutput, rows⟩ := witness
  obtain ⟨C, hC, larger, Coutput, joined⟩ := assemble D hD Doutput
  refine ⟨C, hC, by omega, Coutput, ?_⟩
  dsimp only
  intro points lines
  let labels : Fin 21 → Fin 26 := ![2,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25]
  let raw (i : Fin 26) := if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ points)
    else decide (Fin.ofNat 13 i.val ∈ lines)
  let x := raw ∘ labels
  have inputList : List.ofFn x = [2,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25].map raw := by
    have enumerate : List.ofFn labels = [2,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25] := by decide
    rw [← enumerate, List.map_ofFn]
  change C.eval ([2,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25].map raw) = true ↔
    ∃ p ∈ points, p.val ∉ ([0,1,3,9] : List ℕ) ∧ ∃ l ∈ lines, (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  rw [← inputList, joined x, certify D hD rows x, ← List.any_append]
  let data : List (ℕ × ℕ) := [(4,354),(5,177),(6,2092),(7,1046),(8,523),
    (0,3137),(1,2832),(2,1416),(3,708)]
  let point (i : ℕ) : Fin 13 := Fin.ofNat 13 (labels (Fin.ofNat 21 i)).val
  let line (j : Fin 12) : Fin 13 := Fin.ofNat 13 (j.val + 1)
  have sides : (∀ r ∈ data, (labels (Fin.ofNat 21 r.1)).val < 13) ∧
      ∀ j : Fin 12, 13 ≤ (labels (Fin.ofNat 21 (j.val + 9))).val ∧
        Fin.ofNat 13 (labels (Fin.ofNat 21 (j.val + 9))).val = line j := by decide
  have pin (r : ℕ × ℕ) (hr : r ∈ data) : x (Fin.ofNat 21 r.1) = decide (point r.1 ∈ points) :=
    if_pos (sides.1 r hr)
  have lin (j : Fin 12) : x (Fin.ofNat 21 (j.val + 9)) = decide (line j ∈ lines) := by
    change raw (labels (Fin.ofNat 21 (j.val + 9))) = _
    simp only [raw, if_neg (Nat.not_lt.mpr (sides.2 j).1), (sides.2 j).2]
  have geometry : ∀ p l : Fin 13,
      p.val ∉ ([0,1,3,9] : List ℕ) ∧ (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ) ↔
      ∃ r ∈ data, point r.1 = p ∧ ∃ j : Fin 12, r.2.testBit j.val = true ∧ line j = l := by decide
  change data.any (fun r => x (Fin.ofNat 21 r.1) &&
    (List.range 12).any fun j => r.2.testBit j && x (Fin.ofNat 21 (j + 9))) = true ↔ _
  constructor
  · intro yes
    obtain ⟨r, hr, signal⟩ := List.any_eq_true.mp yes
    simp only [Bool.and_eq_true] at signal
    obtain ⟨on, hit⟩ := signal
    rw [pin r hr, decide_eq_true_eq] at on
    obtain ⟨j, hj, accept⟩ := List.any_eq_true.mp hit
    let q : Fin 12 := ⟨j, List.mem_range.mp hj⟩
    simp only [Bool.and_eq_true] at accept
    obtain ⟨incident, lon⟩ := accept
    change x (Fin.ofNat 21 (q.val + 9)) = true at lon
    rw [lin, decide_eq_true_eq] at lon
    obtain ⟨outside, near⟩ := (geometry (point r.1) (line q)).mpr ⟨r, hr, rfl, q, incident, rfl⟩
    exact ⟨point r.1, on, outside, line q, lon, near⟩
  · rintro ⟨p, hp, outside, l, hl, near⟩
    obtain ⟨r, hr, rfl, j, adjacent, rfl⟩ := (geometry p l).mp ⟨outside, near⟩
    apply List.any_eq_true.mpr
    refine ⟨r, hr, ?_⟩
    simp only [Bool.and_eq_true]
    constructor
    · rw [pin r hr, decide_eq_true_eq]
      exact hp
    · apply List.any_eq_true.mpr
      refine ⟨j.val, List.mem_range.mpr j.isLt, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨adjacent, ?_⟩
      rw [lin, decide_eq_true_eq]
      exact hl
