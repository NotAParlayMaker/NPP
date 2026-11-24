import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

-- The smaller side of a generic false row determines the other side. This lets
-- the search use noncollinear point triples and nonconcurrent line triples as rows.
theorem PEqualNP.Outside.R_meta_2401_731
    (shape :
      let S : Fin 13 → Finset (Fin 13) := fun w => ({0, 1, 3, 9} : Finset (Fin 13)).image (w + ·)
      ∀ P : Finset (Fin 13),
        let W := PEqualNP.HeptadCover.missLines S P
        InNoLine S P → InNoPencil S W → P.card = 3 ∨ W.card = 3)
    (candidate :
      let S : Fin 13 → Finset (Fin 13) := fun w => ({0, 1, 3, 9} : Finset (Fin 13)).image (w + ·)
      let row (P W : Finset (Fin 13)) : Fin 26 → Bool := fun i =>
        decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ w ∈ W, i = Fin.natAdd 13 w)
      let aug (q : Fin 4) (x : Fin 26 → Bool) : Fin 27 → Bool :=
        let j : Fin 26 := if q.val = 1 then 1 else if q.val = 3 then 14 else 13
        Fin.lastCases (if decide (q.val = 0) = true then x 0 && x j else x 0 || x j) x
      ∃ (q : Fin 4) (C : Circuit), Monotone2 C ∧ NestedCover.ReadsBack 27 C ∧ C.size ≤ 62 ∧
        (∀ p w : Fin 13, p ∈ S w → circuitFun 27 C (aug q (row {p} {w})) = true) ∧
        ∀ (b : Bool) (T : Finset (Fin 13)), T.card = 3 →
          (if b then InNoLine S T else InNoPencil S T) →
          circuitFun 27 C (aug q (if b then row T (PEqualNP.HeptadCover.missLines S T)
            else row (zeroSet S T) T)) = false) :
    ∃ (x1 : Fin (4 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x2 ∧       x2.size ≤ (62 : ℕ) ∧         have x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => ∃ x6 ∈ x3, x4 = x5 + x6;         have x5 : Fin (26 : ℕ) := if ↑x1 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x1 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x6 : Bool := Decidable.decide (↑x1 = (0 : ℕ));         have x7 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x6 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x5 else x7 (0 : Fin (26 : ℕ)) || x7 x5) x7 x8;         (∀ (x8 x9 : Fin (13 : ℕ)), x4 x8 x9 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x8 ∨ x11 = Fin.natAdd (13 : ℕ) x9)) = Bool.true) ∧           ∀ (x8 : Finset (Fin (13 : ℕ))),             have x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => ∀ x10 ∈ x8, ¬x4 x10 x9;             (∀ x10 ∉ x8, ∃ (x12 : Fin (13 : ℕ)), x9 x12 ∧ x4 x10 x12) → ((¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x8, x4 x12 x11) ∧ ¬∃ (x11 : Fin (13 : ℕ)), ∀ (x12 : Fin (13 : ℕ)), x9 x12 → x4 x11 x12) → ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ (x13 : Fin (26 : ℕ)), x12 x13 = Bool.true ↔ (∃ x14 ∈ x8, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ (x14 : Fin (13 : ℕ)), x13 = Fin.natAdd (13 : ℕ) x14 ∧ x9 x14) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 x12) = Bool.false := by
  let offsets : Finset (Fin 13) := {0, 1, 3, 9}
  let I (p w : Fin 13) : Prop := ∃ d ∈ offsets, p = w + d
  let S : Fin 13 → Finset (Fin 13) := fun w => offsets.image (w + ·)
  let row (P W : Finset (Fin 13)) : Fin 26 → Bool := fun i =>
    decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ w ∈ W, i = Fin.natAdd 13 w)
  let aug (q : Fin 4) (x : Fin 26 → Bool) : Fin 27 → Bool :=
    let j : Fin 26 := if q.val = 1 then 1 else if q.val = 3 then 14 else 13
    Fin.lastCases (if decide (q.val = 0) = true then x 0 && x j else x 0 || x j) x
  have inc (p w : Fin 13) : I p w ↔ p ∈ S w := by
    change (∃ d ∈ offsets, p = w + d) ↔ p ∈ offsets.image (w + ·)
    rw [Finset.mem_image]
    exact exists_congr (fun d => and_congr_right (fun _ => eq_comm))
  obtain ⟨q, C, mono, reads, size, accepts, rejects⟩ := candidate
  refine ⟨q, C, mono, reads, size, ?_, ?_⟩
  · intro p w adjacent
    change circuitFun 27 C (aug q (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w))) = true
    have singleton : row {p} {w} = fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w) := by
      funext i
      simp [row]
    rw [← singleton]
    exact accepts p w ((inc p w).mp adjacent)
  intro P missing maximal generic x bits
  let W := PEqualNP.HeptadCover.missLines S P
  have memW (w : Fin 13) : w ∈ W ↔ missing w := by
    change w ∈ (Finset.univ.filter fun w => Disjoint (S w) P) ↔ ∀ p ∈ P, ¬ I p w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
    constructor
    · intro disjoint p hp h
      exact disjoint ((inc p w).mp h) hp
    · intro misses p incident hp
      exact misses p hp ((inc p w).mpr incident)
  have pointShape : InNoLine S P := by
    intro w containing
    exact generic.1 ⟨w, fun p hp => (inc p w).mpr (containing hp)⟩
  have lineShape : InNoPencil S W := by
    intro p all
    exact generic.2 ⟨p, fun w misses => (inc p w).mpr (all w ((memW w).mpr misses))⟩
  have closed (p : Fin 13) (outside : p ∉ P) : ∃ w ∈ W, p ∈ S w := by
    obtain ⟨w, misses, hits⟩ := maximal p outside
    exact ⟨w, (memW w).mpr misses, (inc p w).mp hits⟩
  have pointSet : zeroSet S W = P := by
    ext p
    change p ∈ (Finset.univ.filter fun p => ∀ w ∈ W, p ∉ S w) ↔ p ∈ P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro disjoint
      by_contra outside
      obtain ⟨w, hw, hit⟩ := closed p outside
      exact disjoint w hw hit
    · intro present w hw hit
      exact (memW w).mp hw p present ((inc p w).mpr hit)
  have xEq : x = row P W := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simpa only [row, decide_eq_true_eq, memW, and_comm] using bits i
  change circuitFun 27 C (aug q x) = false
  rw [xEq]
  rcases shape P pointShape lineShape with h | h
  · exact rejects true P h pointShape
  · have reject : circuitFun 27 C (aug q (row (zeroSet S W) W)) = false :=
      rejects false W h lineShape
    rwa [pointSet] at reject
