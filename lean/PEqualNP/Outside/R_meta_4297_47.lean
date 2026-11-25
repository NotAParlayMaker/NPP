import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Read the incidence relation as a bipartite graph G on the points and lines, with no 4-cycle.
-- First: a least circuit in top form, with the counting bound of the part the top form controls.
-- Second: the open core, the bound on the part it does not control (the edges no top covers).
-- Together they give a vertex cover K of G with |E| + |K| at most the size plus one. Each
-- incidence goes to its point when that point is in K, else to its line: one star per centre.
theorem PEqualNP.Outside.R_meta_4297_47
    (normalForm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ C' : Circuit, IsLeastAO G C' ∧ TopForm G C' ∧
        G.edgeFinset.card + (tops G C' \ centreless G C').card + 2 * (centreless G C').card +
            (junk G C').card + (orN G C' \ lam G C').card ≤ C'.size + (Ustar G C').card + 1 ∧
        ∀ K : Finset (Fin n), IsMinCover (G.deleteEdges ↑(Ustar G C')) K →
          K.card ≤ (tops G C' \ centreless G C').card)
    (delta : ∀ (n m : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ u v : Fin n, G.Adj u v → ((u : ℕ) < m ↔ m ≤ (v : ℕ))) → NoFourCycle G →
      G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      ∃ K : Finset (Fin n), (∀ e ∈ Ustar G C, ∃ v ∈ K, v ∈ e) ∧
        (Ustar G C).card + K.card ≤
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → x5.output < x1 + x2 + x5.gates.length → (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → (∀ x10 < x5.gates.length, ∀ (x12 x13 : ℕ), x5.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x12, x13] : PEqualNP.CircuitLowerBounds.Gate } → (x1 + x2 ≤ x13 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x13 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x12) ∧ (x1 + x2 ≤ x12 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x12 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x13)) → ∃ (x11 : List (ℕ × List ℕ)), (∀ x12 ∈ x11, x12.2 ≠ [] ∧ ((x12.1 < x1 ∧ ∀ x14 ∈ x12.2, x1 ≤ x14 ∧ x14 < x1 + x2) ∨ x1 ≤ x12.1 ∧ x12.1 < x1 + x2 ∧ ∀ x14 ∈ x12.2, x14 < x1)) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 ↔ ∃ x14 ∈ x11, x14.1 = ↑x12 ∧ x1 + ↑x13 ∈ x14.2 ∨ x14.1 = x1 + ↑x13 ∧ ↑x12 ∈ x14.2) ∧ (List.map (fun (x12 : ℕ × List ℕ) => x12.2.length) x11).sum + x11.length - (1 : ℕ) ≤ x5.size := by
  intro x1 x2 R _ C0 hno hC0 _ hfun _
  classical
  obtain ⟨G, hG⟩ : ∃ G : SimpleGraph (Fin (x1 + x2)), ∀ u v, G.Adj u v ↔ u ≠ v ∧
      ((∃ p l, u = Fin.castAdd x2 p ∧ v = Fin.natAdd x1 l ∧ R p l) ∨
        (∃ p l, v = Fin.castAdd x2 p ∧ u = Fin.natAdd x1 l ∧ R p l)) :=
    ⟨SimpleGraph.fromRel fun u v => ∃ p l, u = Fin.castAdd x2 p ∧ v = Fin.natAdd x1 l ∧ R p l,
      fun u v => SimpleGraph.fromRel_adj _ _ _⟩
  have hne : ∀ (p : Fin x1) (l : Fin x2), Fin.castAdd x2 p ≠ Fin.natAdd x1 l := by
    intro p l h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    have := p.isLt
    omega
  have hPL : ∀ (p : Fin x1) (l : Fin x2), G.Adj (Fin.castAdd x2 p) (Fin.natAdd x1 l) ↔ R p l := by
    intro p l
    rw [hG]
    constructor
    · rintro ⟨_, ⟨p', l', h1, h2, h3⟩ | ⟨p', l', h1, h2, h3⟩⟩
      · rw [Fin.ext_iff] at h1 h2
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h1 h2
        rwa [show p = p' from Fin.ext h1, show l = l' from Fin.ext (by omega)]
      · rw [Fin.ext_iff] at h1 h2
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h1 h2
        have := p.isLt
        omega
    · intro h
      exact ⟨hne p l, Or.inl ⟨p, l, rfl, rfl, h⟩⟩
  have hLP : ∀ (p : Fin x1) (l : Fin x2), G.Adj (Fin.natAdd x1 l) (Fin.castAdd x2 p) ↔ R p l :=
    fun p l => (G.adj_comm _ _).trans (hPL p l)
  have hPP : ∀ p q : Fin x1, ¬ G.Adj (Fin.castAdd x2 p) (Fin.castAdd x2 q) := by
    intro p q h
    rcases ((hG _ _).1 h).2 with ⟨p', l', h1, h2, h3⟩ | ⟨p', l', h1, h2, h3⟩
    · rw [Fin.ext_iff] at h1 h2
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h1 h2
      have := q.isLt
      omega
    · rw [Fin.ext_iff] at h1 h2
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h1 h2
      have := p.isLt
      omega
  have hLL : ∀ l k : Fin x2, ¬ G.Adj (Fin.natAdd x1 l) (Fin.natAdd x1 k) := by
    intro l k h
    rcases ((hG _ _).1 h).2 with ⟨p', l', h1, h2, h3⟩ | ⟨p', l', h1, h2, h3⟩
    · rw [Fin.ext_iff] at h1 h2
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h1 h2
      have := p'.isLt
      omega
    · rw [Fin.ext_iff] at h1 h2
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h1 h2
      have := p'.isLt
      omega
  have hbip : ∀ u v : Fin (x1 + x2), G.Adj u v → ((u : ℕ) < x1 ↔ x1 ≤ (v : ℕ)) := by
    intro u v h
    induction u using Fin.addCases with
    | left p =>
      induction v using Fin.addCases with
      | left q => exact absurd h (hPP p q)
      | right l =>
        simp only [Fin.val_castAdd, Fin.val_natAdd]
        have := p.isLt
        omega
    | right l =>
      induction v using Fin.addCases with
      | left q =>
        simp only [Fin.val_castAdd, Fin.val_natAdd]
        have := q.isLt
        omega
      | right k => exact absurd h (hLL l k)
  have h4 : NoFourCycle G := by
    intro a b hab
    rw [Finset.card_le_one]
    intro w1 hw1 w2 hw2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
    by_contra hw
    induction a using Fin.addCases <;> induction b using Fin.addCases <;>
      induction w1 using Fin.addCases <;> induction w2 using Fin.addCases <;>
      simp only [hPL, hLP, hPP, hLL, false_and, and_false] at hw1 hw2
    · exact hno _ _ _ _ (fun h => hab (by rw [h])) (fun h => hw (by rw [h]))
        ⟨hw1.1, hw2.1, hw1.2, hw2.2⟩
    · exact hno _ _ _ _ (fun h => hw (by rw [h])) (fun h => hab (by rw [h]))
        ⟨hw1.1, hw1.2, hw2.1, hw2.2⟩
  have key : ∀ x : Fin (x1 + x2) → Bool, graphFun G ∅ x = Decidable.decide (∃ (p : Fin x1)
      (l : Fin x2), R p l ∧ x (Fin.castAdd x2 p) = true ∧ x (Fin.natAdd x1 l) = true) := by
    intro x
    unfold graphFun
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false,
      false_or]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      induction u using Fin.addCases with
      | left p =>
        induction v using Fin.addCases with
        | left q => exact absurd huv (hPP p q)
        | right l => exact ⟨p, l, (hPL p l).1 huv, hu, hv⟩
      | right l =>
        induction v using Fin.addCases with
        | left q => exact ⟨q, l, (hLP q l).1 huv, hv, hu⟩
        | right k => exact absurd huv (hLL l k)
    · rintro ⟨p, l, h, hp, hl⟩
      exact ⟨_, _, (hPL p l).2 h, hp, hl⟩
  have hfunG : circuitFun (x1 + x2) C0 = graphFun G ∅ :=
    funext fun x => (hfun x).trans (key x).symm
  have hmc : ∀ H : SimpleGraph (Fin (x1 + x2)), ∃ K1, IsMinCover H K1 := by
    intro H
    obtain ⟨K1, hK1, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun T :
      Finset (Fin (x1 + x2)) => H.IsVertexCover (T : Set _))
      Finset.card ⟨Finset.univ, by simp [SimpleGraph.IsVertexCover]⟩
    exact ⟨K1, (Finset.mem_filter.1 hK1).2, fun T hT => hmin T (by simp [hT])⟩
  have hcu : ∀ (U : Finset (Sym2 (Fin (x1 + x2)))) (K1 K2 : Finset (Fin (x1 + x2))),
      (G.deleteEdges ↑U).IsVertexCover (K1 : Set (Fin (x1 + x2))) →
      (∀ e ∈ U, ∃ v ∈ K2, v ∈ e) → G.IsVertexCover ((K1 ∪ K2 : Finset _) : Set (Fin (x1 + x2))) := by
    intro U K1 K2 hK1 hK2 v w hvw
    by_cases hU : s(v, w) ∈ U
    · obtain ⟨y, hy, hye⟩ := hK2 _ hU
      rcases Sym2.mem_iff.1 hye with rfl | rfl
      · left; simp [hy]
      · right; simp [hy]
    · have := hK1 (v := v) (w := w) (by simp [SimpleGraph.deleteEdges_adj, hvw, hU])
      rcases this with h | h
      · left; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at h ⊢; exact Or.inl h
      · right; simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at h ⊢; exact Or.inl h
  -- The incidences are the edges of G.
  obtain ⟨E, hI⟩ : ∃ E : Finset (Fin x1 × Fin x2), ∀ q, q ∈ E ↔ R q.1 q.2 :=
    ⟨Finset.univ.filter fun q => R q.1 q.2, fun q => by simp⟩
  have hEcard : E.card = G.edgeFinset.card := by
    refine Finset.card_bij (fun q _ => s(Fin.castAdd x2 q.1, Fin.natAdd x1 q.2)) ?_ ?_ ?_
    · intro q hq
      exact SimpleGraph.mem_edgeFinset.2 ((hPL _ _).2 ((hI q).1 hq))
    · rintro ⟨p, l⟩ _ ⟨p', l'⟩ _ h
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, _⟩
      · rw [Fin.castAdd_inj] at h1
        rw [Fin.natAdd_inj] at h2
        simp only at h1 h2
        rw [h1, h2]
      · exact absurd h1 (hne p l')
    · intro e he
      induction e using Sym2.ind with
      | h u v =>
        have huv := SimpleGraph.mem_edgeFinset.1 he
        induction u using Fin.addCases with
        | left p =>
          induction v using Fin.addCases with
          | left q => exact absurd huv (hPP p q)
          | right l => exact ⟨(p, l), (hI _).2 ((hPL p l).1 huv), rfl⟩
        | right l =>
          induction v using Fin.addCases with
          | left q => exact ⟨(q, l), (hI _).2 ((hLP q l).1 huv), Sym2.eq_swap⟩
          | right k => exact absurd huv (hLL l k)
  obtain ⟨K, hKc, hKs⟩ : ∃ K : Finset (Fin (x1 + x2)), G.IsVertexCover (K : Set (Fin (x1 + x2))) ∧
      G.edgeFinset.card + K.card ≤ C0.size + 1 := by
    by_cases hE : G.edgeFinset.Nonempty
    · obtain ⟨C, hL, hT, hcount, hcov⟩ := normalForm (x1 + x2) G C0 h4 hE hC0 hfunG
      obtain ⟨K2, hK2, hD⟩ := delta (x1 + x2) x1 G C hbip h4 hE hL hT
      obtain ⟨K1, hK1⟩ := hmc (G.deleteEdges ↑(Ustar G C))
      have h1 := hcov K1 hK1
      have hsz : C.size ≤ C0.size := hL.2.2 C0 hC0 hfunG
      refine ⟨K1 ∪ K2, hcu _ K1 K2 hK1.1 hK2, ?_⟩
      have := Finset.card_union_le K1 K2
      omega
    · refine ⟨∅, ?_, ?_⟩
      · intro v w hvw
        exact absurd ⟨s(v, w), (SimpleGraph.mem_edgeFinset).2 hvw⟩ hE
      · rw [Finset.not_nonempty_iff_eq_empty.1 hE]
        simp
  -- The star list: each incidence goes to its point when the point is in K, else to its line.
  obtain ⟨NP, hNP⟩ : ∃ NP : Fin x1 → Finset (Fin x2), ∀ p l, l ∈ NP p ↔ R p l :=
    ⟨fun p => Finset.univ.filter fun l => R p l, fun p l => by simp⟩
  obtain ⟨NL, hNL⟩ : ∃ NL : Fin x2 → Finset (Fin x1), ∀ l p, p ∈ NL l ↔
      R p l ∧ Fin.castAdd x2 p ∉ K :=
    ⟨fun l => Finset.univ.filter fun p => R p l ∧ Fin.castAdd x2 p ∉ K, fun l p => by simp⟩
  obtain ⟨PC, hPC⟩ : ∃ PC : Finset (Fin x1), ∀ p, p ∈ PC ↔
      Fin.castAdd x2 p ∈ K ∧ (NP p).Nonempty :=
    ⟨Finset.univ.filter fun p => Fin.castAdd x2 p ∈ K ∧ (NP p).Nonempty, fun p => by simp⟩
  obtain ⟨LC, hLC⟩ : ∃ LC : Finset (Fin x2), ∀ l, l ∈ LC ↔
      Fin.natAdd x1 l ∈ K ∧ (NL l).Nonempty :=
    ⟨Finset.univ.filter fun l => Fin.natAdd x1 l ∈ K ∧ (NL l).Nonempty, fun l => by simp⟩
  have hsum : ((PC.toList.map fun p : Fin x1 => ((p : ℕ), (NP p).toList.map fun l : Fin x2 => x1 + (l : ℕ))) ++
      LC.toList.map fun l : Fin x2 => (x1 + (l : ℕ), (NL l).toList.map fun p : Fin x1 => (p : ℕ))).map
        (fun e => e.2.length) =
      PC.toList.map (fun p => (NP p).card) ++ LC.toList.map (fun l => (NL l).card) := by
    simp [List.map_append, Function.comp_def]
  -- The leaves are distinct incidences.
  have hS : (∑ p ∈ PC, (NP p).card) + (∑ l ∈ LC, (NL l).card) ≤ E.card := by
    have inj1 : Function.Injective (fun s : (_ : Fin x1) × Fin x2 => (s.1, s.2)) := by
      rintro ⟨a, b⟩ ⟨c, d⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have inj2 : Function.Injective (fun s : (_ : Fin x2) × Fin x1 => (s.2, s.1)) := by
      rintro ⟨a, b⟩ ⟨c, d⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have e1 : ∑ p ∈ PC, (NP p).card = ((PC.sigma NP).image fun s => (s.1, s.2)).card := by
      rw [Finset.card_image_of_injective _ inj1, Finset.card_sigma]
    have e2 : ∑ l ∈ LC, (NL l).card = ((LC.sigma NL).image fun s => (s.2, s.1)).card := by
      rw [Finset.card_image_of_injective _ inj2, Finset.card_sigma]
    have hdisj : Disjoint ((PC.sigma NP).image fun s => (s.1, s.2))
        ((LC.sigma NL).image fun s => (s.2, s.1)) := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hq1
      obtain ⟨t, ht, hts⟩ := Finset.mem_image.1 hq2
      rw [Finset.mem_sigma] at hs ht
      have h1 := ((hPC _).1 hs.1).1
      have h2 := ((hNL _ _).1 ht.2).2
      simp only [Prod.mk.injEq] at hts
      rw [hts.1] at h2
      exact h2 h1
    have hsub : ((PC.sigma NP).image fun s => (s.1, s.2)) ∪
        ((LC.sigma NL).image fun s => (s.2, s.1)) ⊆ E := by
      intro q hq
      rcases Finset.mem_union.1 hq with hq | hq
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hq
        rw [Finset.mem_sigma] at hs
        exact (hI _).2 ((hNP _ _).1 hs.2)
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hq
        rw [Finset.mem_sigma] at hs
        exact (hI _).2 ((hNL _ _).1 hs.2).1
    rw [e1, e2, ← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  -- At most one star per vertex of K.
  have hcen : PC.card + LC.card ≤ K.card := by
    have hdisj : Disjoint (PC.image (Fin.castAdd x2)) (LC.image (Fin.natAdd x1)) := by
      rw [Finset.disjoint_left]
      simp only [Finset.mem_image]
      rintro u ⟨p, _, rfl⟩ ⟨l, _, h⟩
      exact hne p l h.symm
    have hsub : PC.image (Fin.castAdd x2) ∪ LC.image (Fin.natAdd x1) ⊆ K := by
      intro u hu
      rcases Finset.mem_union.1 hu with hu | hu
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
        exact ((hPC p).1 hp).1
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hu
        exact ((hLC l).1 hl).1
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (Fin.castAdd_injective _ _),
      Finset.card_image_of_injective _ (Fin.natAdd_injective _ _)] at this
    exact this
  refine ⟨(PC.toList.map fun p : Fin x1 => ((p : ℕ), (NP p).toList.map fun l : Fin x2 => x1 + (l : ℕ))) ++
      LC.toList.map fun l : Fin x2 => (x1 + (l : ℕ), (NL l).toList.map fun p : Fin x1 => (p : ℕ)), ?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.1 he with he | he
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
      obtain ⟨l, hl⟩ := ((hPC p).1 (Finset.mem_toList.1 hp)).2
      refine ⟨?_, Or.inl ⟨p.isLt, ?_⟩⟩
      · exact List.ne_nil_of_mem (List.mem_map.2 ⟨l, Finset.mem_toList.2 hl, rfl⟩)
      · intro w hw
        obtain ⟨l', _, rfl⟩ := List.mem_map.1 hw
        have := l'.isLt
        omega
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 he
      obtain ⟨p, hp⟩ := ((hLC l).1 (Finset.mem_toList.1 hl)).2
      refine ⟨?_, Or.inr ⟨by omega, by have := l.isLt; omega, ?_⟩⟩
      · exact List.ne_nil_of_mem (List.mem_map.2 ⟨p, Finset.mem_toList.2 hp, rfl⟩)
      · intro w hw
        obtain ⟨p', _, rfl⟩ := List.mem_map.1 hw
        exact p'.isLt
  · intro p l
    constructor
    · intro h
      by_cases hp : Fin.castAdd x2 p ∈ K
      · refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨p, Finset.mem_toList.2
          ((hPC p).2 ⟨hp, ⟨l, (hNP p l).2 h⟩⟩), rfl⟩), Or.inl ⟨rfl, ?_⟩⟩
        exact List.mem_map.2 ⟨l, Finset.mem_toList.2 ((hNP p l).2 h), rfl⟩
      · have hl : Fin.natAdd x1 l ∈ K := by
          have := hKc ((hPL p l).2 h)
          simp only [Finset.mem_coe] at this
          exact this.resolve_left hp
        refine ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨l, Finset.mem_toList.2
          ((hLC l).2 ⟨hl, ⟨p, (hNL l p).2 ⟨h, hp⟩⟩⟩), rfl⟩), Or.inr ⟨rfl, ?_⟩⟩
        exact List.mem_map.2 ⟨p, Finset.mem_toList.2 ((hNL l p).2 ⟨h, hp⟩), rfl⟩
    · rintro ⟨e, he, h⟩
      rcases List.mem_append.1 he with he | he
      · obtain ⟨p', _, rfl⟩ := List.mem_map.1 he
        rcases h with ⟨h1, h2⟩ | ⟨h1, _⟩
        · obtain ⟨l', hl', hll⟩ := List.mem_map.1 h2
          have e1 : p' = p := Fin.ext h1
          have e2 : l' = l := Fin.ext (by (try simp only at hll); omega)
          rw [← e1, ← e2]
          exact (hNP _ _).1 (Finset.mem_toList.1 hl')
        · have := p'.isLt
          try simp only at h1
          omega
      · obtain ⟨l', _, rfl⟩ := List.mem_map.1 he
        rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
        · have := p.isLt
          try simp only at h1
          omega
        · obtain ⟨p', hp', hpp⟩ := List.mem_map.1 h2
          have e1 : p' = p := Fin.ext hpp
          have e2 : l' = l := Fin.ext (by (try simp only at h1); omega)
          rw [← e1, ← e2]
          exact ((hNL _ _).1 (Finset.mem_toList.1 hp')).1
  · rw [hsum, List.sum_append, Finset.sum_map_toList, Finset.sum_map_toList, List.length_append,
      List.length_map, List.length_map, Finset.length_toList, Finset.length_toList]
    omega
