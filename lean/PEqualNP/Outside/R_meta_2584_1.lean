import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK

-- A circuit in top form with at most one dirty AND has a read-two proof for each edge.
-- Otherwise the exchange step lowers the number of incidences still requiring more reads.
theorem PEqualNP.Outside.R_meta_2584_1
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C →
      ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧
        (junk G D).card = (junk G C).card ∧ TopForm G D)
    (few : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → TopForm G C → (junk G C).card ≤ 1 → IsReadK n C 2)
    (exchange : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.IsBipartite → NoFourCycle G → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      ¬ IsReadK n C 2 →
      let bad (B : Circuit) : Finset (Fin n × Fin n) :=
        Finset.univ.filter (fun uv =>
          G.Adj uv.1 uv.2 ∧ readsAtMost B n (setList {uv.1, uv.2}) 2 = false)
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ (bad D).card < (bad C).card) :
∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 2 := by
  classical
  intro P L I _ C hRectangle hAO hCompute
  by_cases nonempty : ∃ p l, I p l
  swap
  · refine ⟨C, hAO, hCompute, le_rfl, ?_⟩
    intro S hS
    have hZero : circuitFun (P + L) C (setInput S) = false := by
      rw [hCompute]
      apply decide_eq_false
      rintro ⟨p, l, h, _, _⟩
      exact nonempty ⟨p, l, h⟩
    have hTrue := hS.1
    rw [hZero] at hTrue
    exact (Bool.false_ne_true hTrue).elim
  let point (p : Fin P) : Fin (P + L) := Fin.castAdd L p
  let line (l : Fin L) : Fin (P + L) := Fin.natAdd P l
  have diff (p : Fin P) (l : Fin L) : point p ≠ line l := by
    intro h
    have hn : p.val = P + l.val := congrArg Fin.val h
    have hp := p.isLt
    omega
  have pi : Function.Injective point := by
    intro p q h
    apply Fin.ext
    have hn : (point p).val = (point q).val := congrArg Fin.val h
    exact hn
  have li : Function.Injective line := by
    intro p q h
    apply Fin.ext
    have hn : P + p.val = P + q.val := congrArg Fin.val h
    omega
  let incidence (u v : Fin (P + L)) : Prop := ∃ p l, I p l ∧
    ((u = point p ∧ v = line l) ∨ (u = line l ∧ v = point p))
  let G : SimpleGraph (Fin (P + L)) := {
    Adj := incidence
    symm := ⟨by
      rintro u v ⟨p, l, hi, h | h⟩
      · exact ⟨p, l, hi, Or.inr h.symm⟩
      · exact ⟨p, l, hi, Or.inl h.symm⟩⟩
    loopless := ⟨by
      rintro u ⟨p, l, _, h | h⟩
      · exact diff p l (h.1.symm.trans h.2)
      · exact diff p l (h.2.symm.trans h.1)⟩ }
  let _ : DecidableRel G.Adj := Classical.decRel _
  have fromPoint (p : Fin P) (v : Fin (P + L)) (h : G.Adj (point p) v) :
      ∃ l, v = line l ∧ I p l := by
    rcases h with ⟨q, l, hi, h | h⟩
    · exact ⟨l, h.2, pi h.1 ▸ hi⟩
    · exact (diff p l h.1).elim
  have fromLine (l : Fin L) (v : Fin (P + L)) (h : G.Adj (line l) v) :
      ∃ p, v = point p ∧ I p l := by
    rcases h with ⟨p, k, hi, h | h⟩
    · exact (diff p l h.1.symm).elim
    · exact ⟨p, h.2, li h.1 ▸ hi⟩
  have split (v : Fin (P + L)) : (∃ p, v = point p) ∨ (∃ l, v = line l) :=
    Fin.addCases (fun p => Or.inl ⟨p, rfl⟩) (fun l => Or.inr ⟨l, rfl⟩) v
  have bipartite : G.IsBipartite := by
    refine SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mpr
      ⟨Set.range point, Set.range line, ⟨?_, ?_⟩⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨p, rfl⟩ ⟨l, h⟩
      exact diff p l h.symm
    · rintro u v ⟨p, l, _, h | h⟩
      · exact Or.inl ⟨⟨p, h.1.symm⟩, ⟨l, h.2.symm⟩⟩
      · exact Or.inr ⟨⟨l, h.1.symm⟩, ⟨p, h.2.symm⟩⟩
  have noFour : NoFourCycle G := by
    intro a b hne
    apply Finset.card_le_one.mpr
    intro u hu v hv
    have hu' : G.Adj a u ∧ G.Adj b u := (Finset.mem_filter.mp hu).2
    have hv' : G.Adj a v ∧ G.Adj b v := (Finset.mem_filter.mp hv).2
    rcases split a with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · obtain ⟨l, rfl, hpl⟩ := fromPoint p u hu'.1
      obtain ⟨l', rfl, hpl'⟩ := fromPoint p v hv'.1
      obtain ⟨p', rfl, hp'l⟩ := fromLine l b hu'.2.symm
      obtain ⟨k, he, hkl'⟩ := fromPoint p' (line l') hv'.2
      have hp'l' : I p' l' := li he ▸ hkl'
      have hpp' : p ≠ p' := fun he => hne (congrArg point he)
      by_contra hu
      exact hRectangle p p' l l' hpp' (fun he => hu (congrArg line he)) ⟨hpl, hpl', hp'l, hp'l'⟩
    · obtain ⟨p, rfl, hpl⟩ := fromLine l u hu'.1
      obtain ⟨p', rfl, hp'l⟩ := fromLine l v hv'.1
      obtain ⟨l', rfl, hpl'⟩ := fromPoint p b hu'.2.symm
      obtain ⟨k, he, hp'k⟩ := fromLine l' (point p') hv'.2
      have hp'l' : I p' l' := pi he ▸ hp'k
      have hll' : l ≠ l' := fun he => hne (congrArg line he)
      by_contra hu
      exact hRectangle p p' l l' (fun he => hu (congrArg point he)) hll' ⟨hpl, hpl', hp'l, hp'l'⟩
  have containsGraphEdge : G.edgeFinset.Nonempty := by
    obtain ⟨p, l, h⟩ := nonempty
    exact ⟨s(point p, line l), SimpleGraph.mem_edgeFinset.mpr ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩⟩
  have graphSpec (x : Fin (P + L) → Bool) :
      graphFun G ∅ x = decide (∃ p l, I p l ∧ x (point p) = true ∧ x (line l) = true) := by
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ a ∈ (∅ : Finset (Fin (P + L))), x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, ⟨p, l, hi, h | h⟩, hu, hv⟩
      · exact ⟨p, l, hi, h.1 ▸ hu, h.2 ▸ hv⟩
      · exact ⟨p, l, hi, h.2 ▸ hv, h.1 ▸ hu⟩
    · rintro ⟨p, l, hi, hp, hl⟩
      exact ⟨point p, line l, ⟨p, l, hi, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩
  have hGraph : circuitFun (P + L) C = graphFun G ∅ := by
    funext x
    exact (hCompute x).trans (graphSpec x).symm
  let realizes (k : ℕ) := ∃ A : Circuit, IsAO2 (P + L) A ∧
    circuitFun (P + L) A = graphFun G ∅ ∧ A.size = k
  have existsSize : ∃ k, realizes k := ⟨C.size, C, hAO, hGraph, rfl⟩
  obtain ⟨A, hAAO, hAGraph, hASize⟩ := Nat.find_spec existsSize
  have leastA : IsLeastAO G A := by
    refine ⟨hAAO, hAGraph, fun B hBAO hBGraph => ?_⟩
    rw [hASize]
    exact Nat.find_min' existsSize (show realizes B.size from ⟨B, hBAO, hBGraph, rfl⟩)
  obtain ⟨N, leastN, _, _, topN⟩ := normalize (P + L) G A containsGraphEdge leastA
  let bad (B : Circuit) :=
    ((Finset.univ : Finset (Fin (P + L) × Fin (P + L))).filter (fun uv =>
      G.Adj uv.1 uv.2 ∧ readsAtMost B (P + L) (setList {uv.1, uv.2}) 2 = false)).card
  let feasible (k : ℕ) := ∃ B : Circuit, IsLeastAO G B ∧ TopForm G B ∧ bad B = k
  have existsBad : ∃ k, feasible k := ⟨bad N, N, leastN, topN, rfl⟩
  obtain ⟨B, leastB, topB, minBad⟩ := Nat.find_spec existsBad
  have readTwo : IsReadK (P + L) B 2 := by
    by_contra tooMany
    have enough : 2 ≤ (junk G B).card := by
      by_contra small
      exact tooMany (few (P + L) G B leastB topB (by omega))
    obtain ⟨D, leastD, topD, less⟩ := exchange (P + L) G B bipartite noFour leastB topB enough tooMany
    change bad D < bad B at less
    have lower := Nat.find_min' existsBad (show feasible (bad D) from ⟨D, leastD, topD, rfl⟩)
    omega
  exact ⟨B, leastB.1, fun x => congrFun leastB.2.1 x |>.trans (graphSpec x),
    leastB.2.2 C hAO hGraph, readTwo⟩
