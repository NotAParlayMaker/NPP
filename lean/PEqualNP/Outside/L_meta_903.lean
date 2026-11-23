import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_903_aux

open PEqualNP.MetaComplexity

private def graph (p : Fin 8 → Fin 8) : SimpleGraph (Fin 8) where
  Adj a b := (a < b ∧ p b = a) ∨ (b < a ∧ p a = b)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by simp⟩

private def adjacency (p : Fin 8 → Fin 8) : DecidableRel (graph p).Adj :=
  fun a b => inferInstanceAs (Decidable ((a < b ∧ p b = a) ∨ (b < a ∧ p a = b)))

private def covers (p : Fin 8 → Fin 8) (T : Finset (Fin 8)) : Prop :=
  ∀ j, j ≠ 0 → p j ∈ T ∨ j ∈ T

private def decCover (p : Fin 8 → Fin 8) (T : Finset (Fin 8)) : Decidable (covers p T) :=
  inferInstanceAs (Decidable (∀ j, j ≠ 0 → p j ∈ T ∨ j ∈ T))

private def edgeList (p : Fin 8 → Fin 8) (x : Fin 8 → Bool) : Bool :=
  ([1,2,3,4,5,6,7] : List (Fin 8)).any fun j => x (p j) && x j

private theorem exactTree (p : Fin 8 → Fin 8) (T : Finset (Fin 8)) (k b : ℕ)
    (hp : ∀ j, j ≠ 0 → p j < j)
    (hc : letI := adjacency p; (graph p).edgeFinset.card = 7)
    (ht : covers p T) (hcard : T.card = k)
    (hmin : ∀ U, covers p U → k ≤ U.card) (hb : 7 + k - 1 = b)
    (s : ℕ) : HasCircuitSize 8 (edgeList p) s ↔ b ≤ s := by
  letI := adjacency p
  have edge (j : Fin 8) (hj : j ≠ 0) : (graph p).Adj (p j) j := Or.inl ⟨hp j hj, rfl⟩
  have he : ∃ i j, (graph p).Adj i j := ⟨p 1, 1, edge 1 (by decide)⟩
  have tree : (graph p).IsTree := by
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    constructor
    · apply ((graph p).connected_iff_exists_forall_reachable).mpr
      refine ⟨0, ?_⟩
      intro j
      induction j using WellFoundedLT.induction with
      | ind j ih =>
        by_cases h : j = 0
        · subst j; exact SimpleGraph.Reachable.refl _
        · exact (ih (p j) (hp j h)).trans (edge j h).reachable
    · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [SimpleGraph.card_edgeSet]
      omega
  have nonzero (a b : Fin 8) (h : a < b) : b ≠ 0 := by
    intro heq
    subst b
    exact (Fin.not_lt_zero a) h
  have cv : ∀ a b, (graph p).Adj a b → a ∈ T ∨ b ∈ T := by
    rintro a b (⟨hlt, rfl⟩ | ⟨hlt, rfl⟩)
    · exact ht _ (nonzero _ _ hlt)
    · exact (ht _ (nonzero _ _ hlt)).symm
  have mincv (U : Finset (Fin 8)) (h : ∀ a b, (graph p).Adj a b → a ∈ U ∨ b ∈ U) :
      k ≤ U.card := hmin U (fun j hj => h (p j) j (edge j hj))
  have chars : ∀ j : Fin 8, j ∈ ([1,2,3,4,5,6,7] : List (Fin 8)) ↔ j ≠ 0 := by decide
  have convert : edgeList p =
      (fun x : Fin 8 → Bool => decide (∃ i j, (graph p).Adj i j ∧ x i = true ∧ x j = true)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [edgeList, List.any_eq_true, chars, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨j,hj,ha,hb'⟩
      exact ⟨p j,j,edge j hj,ha,hb'⟩
    · rintro ⟨a,b,hab,ha,hb'⟩
      rcases hab with ⟨hlt,rfl⟩ | ⟨hlt,rfl⟩
      · exact ⟨b,nonzero _ _ hlt,ha,hb'⟩
      · exact ⟨a,nonzero _ _ hlt,hb',ha⟩
  rw [convert]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 8 k s (graph p) tree.isAcyclic he mincv h
    rw [hc] at this
    omega
  · intro h
    have upper := PEqualNP.MetaComplexity.L105 8 (graph p) T he cv
    rw [hc, hcard, hb] at upper
    obtain ⟨C, basis, size, spec⟩ := upper
    exact ⟨C,basis,size.trans h,spec⟩

private def p1 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 0, 0, 0, 0]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row1 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7)) s ↔ 7 ≤ s := by
  letI := decCover p1
  have h := exactTree p1 {0} 1 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p1, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p2 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 0, 0, 0, 1]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row2 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)) s ↔ 8 ≤ s := by
  letI := decCover p2
  have h := exactTree p2 {0, 1} 2 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p2, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p3 : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 1, 1, 2]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row3 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) s ↔ 8 ≤ s := by
  letI := decCover p3
  have h := exactTree p3 {1, 2} 2 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p3, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p4 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 0, 0, 1, 1]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row4 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 1 && x 7)) s ↔ 8 ≤ s := by
  letI := decCover p4
  have h := exactTree p4 {0, 1} 2 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p4, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p5 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 0, 0, 1, 2]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row5 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p5
  have h := exactTree p5 {0, 1, 2} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p5, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p6 : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 1, 2, 2]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row6 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 2 && x 7)) s ↔ 8 ≤ s := by
  letI := decCover p6
  have h := exactTree p6 {1, 2} 2 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p6, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p7 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 0, 1, 1, 1]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row7 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7)) s ↔ 8 ≤ s := by
  letI := decCover p7
  have h := exactTree p7 {0, 1} 2 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p7, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p8 : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 1, 2, 6]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row8 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 6 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p8
  have h := exactTree p8 {0, 1, 6} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p8, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p9 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 0, 1, 2, 5]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row9 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p9
  have h := exactTree p9 {0, 2, 5} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p9, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p10 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 1, 1, 2]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row10 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p10
  have h := exactTree p10 {0, 1, 2} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p10, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p11 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 0, 1, 1, 2]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row11 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p11
  have h := exactTree p11 {0, 1, 2} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p11, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p12 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 0, 1, 2, 3]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row12 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) s ↔ 10 ≤ s := by
  letI := decCover p12
  have h := exactTree p12 {0, 1, 2, 3} 4 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p12, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p13 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 1, 2, 6]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row13 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 6 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p13
  have h := exactTree p13 {0, 1, 6} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p13, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p14 : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 3, 3, 4]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row14 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p14
  have h := exactTree p14 {0, 3, 4} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p14, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p15 : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 5, 5]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row15 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 5 && x 6) || (x 5 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p15
  have h := exactTree p15 {0, 1, 5} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p15, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p16 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 2, 4, 4]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row16 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 4 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p16
  have h := exactTree p16 {0, 2, 4} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p16, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p17 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 2, 4, 5]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row17 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p17
  have h := exactTree p17 {0, 4, 5} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p17, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p18 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 1, 2, 2]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row18 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 2 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p18
  have h := exactTree p18 {0, 1, 2} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p18, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p19 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 1, 2, 3]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row19 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) s ↔ 9 ≤ s := by
  letI := decCover p19
  have h := exactTree p19 {1, 2, 3} 3 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p19, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p20 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 2, 3, 4]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row20 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 7)) s ↔ 10 ≤ s := by
  letI := decCover p20
  have h := exactTree p20 {0, 2, 3, 4} 4 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p20, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p21 : Fin 8 → Fin 8 := ![0, 0, 0, 1, 1, 2, 3, 5]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row21 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 5 && x 7)) s ↔ 10 ≤ s := by
  letI := decCover p21
  have h := exactTree p21 {0, 1, 3, 5} 4 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p21, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

private def p22 : Fin 8 → Fin 8 := ![0, 0, 0, 0, 1, 1, 2, 4]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in

private theorem row22 (s : ℕ) : HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 7)) s ↔ 10 ≤ s := by
  letI := decCover p22
  have h := exactTree p22 {0, 1, 2, 4} 4 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s
  convert h using 2 <;> first | rfl | (funext x; simp [edgeList, p22, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm])

end PEqualNP.Outside.L_meta_903_aux

open PEqualNP.Outside.L_meta_903_aux

theorem PEqualNP.Outside.L_meta_903 : (∀ s1 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x1 : Fin 8 → Bool => (x1 0 && x1 1) || (x1 0 && x1 2) || (x1 0 && x1 3) || (x1 0 && x1 4) || (x1 0 && x1 5) || (x1 0 && x1 6) || (x1 0 && x1 7)) s1 ↔ 7 ≤ s1) ∧ (∀ s2 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x2 : Fin 8 → Bool => (x2 0 && x2 1) || (x2 0 && x2 2) || (x2 0 && x2 3) || (x2 0 && x2 4) || (x2 0 && x2 5) || (x2 0 && x2 6) || (x2 1 && x2 7)) s2 ↔ 8 ≤ s2) ∧ (∀ s3 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x3 : Fin 8 → Bool => (x3 0 && x3 1) || (x3 0 && x3 2) || (x3 1 && x3 3) || (x3 1 && x3 4) || (x3 1 && x3 5) || (x3 1 && x3 6) || (x3 2 && x3 7)) s3 ↔ 8 ≤ s3) ∧ (∀ s4 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x4 : Fin 8 → Bool => (x4 0 && x4 1) || (x4 0 && x4 2) || (x4 0 && x4 3) || (x4 0 && x4 4) || (x4 0 && x4 5) || (x4 1 && x4 6) || (x4 1 && x4 7)) s4 ↔ 8 ≤ s4) ∧ (∀ s5 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x5 : Fin 8 → Bool => (x5 0 && x5 1) || (x5 0 && x5 2) || (x5 0 && x5 3) || (x5 0 && x5 4) || (x5 0 && x5 5) || (x5 1 && x5 6) || (x5 2 && x5 7)) s5 ↔ 9 ≤ s5) ∧ (∀ s6 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x6 : Fin 8 → Bool => (x6 0 && x6 1) || (x6 0 && x6 2) || (x6 1 && x6 3) || (x6 1 && x6 4) || (x6 1 && x6 5) || (x6 2 && x6 6) || (x6 2 && x6 7)) s6 ↔ 8 ≤ s6) ∧ (∀ s7 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x7 : Fin 8 → Bool => (x7 0 && x7 1) || (x7 0 && x7 2) || (x7 0 && x7 3) || (x7 0 && x7 4) || (x7 1 && x7 5) || (x7 1 && x7 6) || (x7 1 && x7 7)) s7 ↔ 8 ≤ s7) ∧ (∀ s8 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x8 : Fin 8 → Bool => (x8 0 && x8 1) || (x8 0 && x8 2) || (x8 1 && x8 3) || (x8 1 && x8 4) || (x8 1 && x8 5) || (x8 2 && x8 6) || (x8 6 && x8 7)) s8 ↔ 9 ≤ s8) ∧ (∀ s9 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x9 : Fin 8 → Bool => (x9 0 && x9 1) || (x9 0 && x9 2) || (x9 0 && x9 3) || (x9 0 && x9 4) || (x9 1 && x9 5) || (x9 2 && x9 6) || (x9 5 && x9 7)) s9 ↔ 9 ≤ s9) ∧ (∀ s10 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x10 : Fin 8 → Bool => (x10 0 && x10 1) || (x10 0 && x10 2) || (x10 0 && x10 3) || (x10 1 && x10 4) || (x10 1 && x10 5) || (x10 1 && x10 6) || (x10 2 && x10 7)) s10 ↔ 9 ≤ s10) ∧ (∀ s11 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x11 : Fin 8 → Bool => (x11 0 && x11 1) || (x11 0 && x11 2) || (x11 0 && x11 3) || (x11 0 && x11 4) || (x11 1 && x11 5) || (x11 1 && x11 6) || (x11 2 && x11 7)) s11 ↔ 9 ≤ s11) ∧ (∀ s12 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x12 : Fin 8 → Bool => (x12 0 && x12 1) || (x12 0 && x12 2) || (x12 0 && x12 3) || (x12 0 && x12 4) || (x12 1 && x12 5) || (x12 2 && x12 6) || (x12 3 && x12 7)) s12 ↔ 10 ≤ s12) ∧ (∀ s13 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x13 : Fin 8 → Bool => (x13 0 && x13 1) || (x13 0 && x13 2) || (x13 0 && x13 3) || (x13 1 && x13 4) || (x13 1 && x13 5) || (x13 2 && x13 6) || (x13 6 && x13 7)) s13 ↔ 9 ≤ s13) ∧ (∀ s14 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x14 : Fin 8 → Bool => (x14 0 && x14 1) || (x14 0 && x14 2) || (x14 1 && x14 3) || (x14 2 && x14 4) || (x14 3 && x14 5) || (x14 3 && x14 6) || (x14 4 && x14 7)) s14 ↔ 9 ≤ s14) ∧ (∀ s15 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x15 : Fin 8 → Bool => (x15 0 && x15 1) || (x15 0 && x15 2) || (x15 1 && x15 3) || (x15 1 && x15 4) || (x15 2 && x15 5) || (x15 5 && x15 6) || (x15 5 && x15 7)) s15 ↔ 9 ≤ s15) ∧ (∀ s16 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x16 : Fin 8 → Bool => (x16 0 && x16 1) || (x16 0 && x16 2) || (x16 0 && x16 3) || (x16 1 && x16 4) || (x16 2 && x16 5) || (x16 4 && x16 6) || (x16 4 && x16 7)) s16 ↔ 9 ≤ s16) ∧ (∀ s17 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x17 : Fin 8 → Bool => (x17 0 && x17 1) || (x17 0 && x17 2) || (x17 0 && x17 3) || (x17 1 && x17 4) || (x17 2 && x17 5) || (x17 4 && x17 6) || (x17 5 && x17 7)) s17 ↔ 9 ≤ s17) ∧ (∀ s18 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x18 : Fin 8 → Bool => (x18 0 && x18 1) || (x18 0 && x18 2) || (x18 0 && x18 3) || (x18 1 && x18 4) || (x18 1 && x18 5) || (x18 2 && x18 6) || (x18 2 && x18 7)) s18 ↔ 9 ≤ s18) ∧ (∀ s19 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x19 : Fin 8 → Bool => (x19 0 && x19 1) || (x19 0 && x19 2) || (x19 0 && x19 3) || (x19 1 && x19 4) || (x19 1 && x19 5) || (x19 2 && x19 6) || (x19 3 && x19 7)) s19 ↔ 9 ≤ s19) ∧ (∀ s20 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x20 : Fin 8 → Bool => (x20 0 && x20 1) || (x20 0 && x20 2) || (x20 0 && x20 3) || (x20 1 && x20 4) || (x20 2 && x20 5) || (x20 3 && x20 6) || (x20 4 && x20 7)) s20 ↔ 10 ≤ s20) ∧ (∀ s21 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x21 : Fin 8 → Bool => (x21 0 && x21 1) || (x21 0 && x21 2) || (x21 1 && x21 3) || (x21 1 && x21 4) || (x21 2 && x21 5) || (x21 3 && x21 6) || (x21 5 && x21 7)) s21 ↔ 10 ≤ s21) ∧ (∀ s22 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x22 : Fin 8 → Bool => (x22 0 && x22 1) || (x22 0 && x22 2) || (x22 0 && x22 3) || (x22 1 && x22 4) || (x22 1 && x22 5) || (x22 2 && x22 6) || (x22 4 && x22 7)) s22 ↔ 10 ≤ s22) := by
  exact ⟨row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22⟩
