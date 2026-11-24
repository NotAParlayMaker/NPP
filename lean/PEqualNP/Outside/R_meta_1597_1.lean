import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_1597_1
    (h1 : let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]; ∀ (U : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11)), (G.deleteEdges ↑U).IsVertexCover ↑K → ([16,12,8,5,3,2,1] : List ℕ).getD K.card 0 ≤ U.card ∧ (K.card = 5 → U.card = 2 → ∀ v : Fin 11, (U.filter (fun e => v ∈ e)).card ≤ 1))
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n D → (PEqualNP.TopForm.centreless G D).card = 0 → (PEqualNP.TopForm.Ustar G D).Nonempty → (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ 1 → (∀ u v : Fin n, s(u,v) ∈ PEqualNP.TopForm.Ustar G D → ∃ h ∈ PEqualNP.TopForm.junk G D, ∃ a ∈ PEqualNP.TopForm.tops G D, ∃ b : Fin 2, PEqualNP.EdgeOwnership.gateVal n D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches n D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal n D h (PEqualNP.EdgeOwnership.pairInput u v) = true) → (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card = 1 ∧ (∃ h ∈ PEqualNP.TopForm.junk G D, ∀ u v : Fin n, s(u,v) ∈ PEqualNP.TopForm.Ustar G D → ∃ a ∈ PEqualNP.TopForm.tops G D, ∃ b : Fin 2, PEqualNP.EdgeOwnership.gateVal n D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches n D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal n D h (PEqualNP.EdgeOwnership.pairInput u v) = true))
    (h3 : let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]; ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D → (PEqualNP.TopForm.Ustar G D).card = 2 → (∀ v : Fin 11, ((PEqualNP.TopForm.Ustar G D).filter (fun e => v ∈ e)).card ≤ 1) → (PEqualNP.TopForm.tops G D \ PEqualNP.TopForm.centreless G D).card = 5 → (PEqualNP.TopForm.centreless G D).card = 0 → (PEqualNP.TopForm.junk G D).card = 2 → (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card = 1 → (∃ h ∈ PEqualNP.TopForm.junk G D, ∀ u v : Fin 11, s(u,v) ∈ PEqualNP.TopForm.Ustar G D → ∃ a ∈ PEqualNP.TopForm.tops G D, ∃ b : Fin 2, PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) → 22 ≤ D.size)
    (h4 : let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]; ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (K : Finset (Fin 11)), PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D → 3 ≤ (PEqualNP.TopForm.Ustar G D).card → 2 ≤ (PEqualNP.TopForm.junk G D).card → (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G D)).IsVertexCover ↑K → K.card ≤ (PEqualNP.TopForm.tops G D \ PEqualNP.TopForm.centreless G D).card → ([16,12,8,5,3,2,1] : List ℕ).getD K.card 0 ≤ (PEqualNP.TopForm.Ustar G D).card → (PEqualNP.TopForm.tops G D \ PEqualNP.TopForm.centreless G D).card + 2 * (PEqualNP.TopForm.centreless G D).card + (PEqualNP.TopForm.junk G D).card + (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ (PEqualNP.TopForm.Ustar G D).card + 6 → (∀ u v : Fin 11, s(u,v) ∈ PEqualNP.TopForm.Ustar G D → ∃ h ∈ PEqualNP.TopForm.junk G D, ∃ a ∈ PEqualNP.TopForm.tops G D, ∃ b : Fin 2, PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) → 22 ≤ D.size) : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → (∀ a ∈ PEqualNP.TopForm.tops G C, Disjoint (PEqualNP.TopForm.side (n := n) C a 0) (PEqualNP.TopForm.side (n := n) C a 1) ∧ (∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C a 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C a 1).card ≤ 1)) ∧ ∀ u v : Fin n, s(u, v) ∈ PEqualNP.TopForm.Ustar G C → ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C, PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h ∧ PEqualNP.EdgeOwnership.gateVal n C h (PEqualNP.EdgeOwnership.pairInput u v) = true) → (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card + 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧ ∀ K : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K → K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → PEqualNP.TopForm.TopForm (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → 2 ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D).card → 22 ≤ D.size := by
  intro struct count D least top hj
  by_contra notsize
  have hs : D.size ≤ 21 := by omega
  let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  have he : G.edgeFinset.card = 16 := by decide
  have hf : PEqualNP.TopForm.NoFourCycle G := by decide
  have hn : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨_, route⟩ := struct 11 G D hf hn least top
  obtain ⟨budget, covers⟩ := count 11 G D hf hn least top
  have hroute : ∀ u v : Fin 11, s(u,v) ∈ PEqualNP.TopForm.Ustar G D → ∃ h ∈ PEqualNP.TopForm.junk G D, ∃ a ∈ PEqualNP.TopForm.tops G D, ∃ b : Fin 2, PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true := by
    intro u v huv
    obtain ⟨a,ha,b,h,hh,hv,hr,ht⟩ := route u v huv
    exact ⟨h,hh,a,ha,b,hv,hr,ht⟩
  have hmin : ∃ K : Finset (Fin 11),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G D)) K := by
    classical
    let H := G.deleteEdges ↑(PEqualNP.TopForm.Ustar G D)
    let S : Finset (Finset (Fin 11)) := Finset.univ.filter (fun K => H.IsVertexCover ↑K)
    have hS : S.Nonempty := ⟨Finset.univ, by simp [S,SimpleGraph.IsVertexCover]⟩
    obtain ⟨K,hK,hmin⟩ := Finset.exists_min_image S Finset.card hS
    exact ⟨K,(Finset.mem_filter.mp hK).2,fun K' hk' => hmin K' (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk'⟩)⟩
  obtain ⟨K,hK⟩ := hmin
  have hkt := covers K hK
  obtain ⟨hp,hm⟩ := h1 (PEqualNP.TopForm.Ustar G D) K hK.1
  rw [he] at budget
  change 2 ≤ (PEqualNP.TopForm.junk G D).card at hj
  have hb : (PEqualNP.TopForm.tops G D \ PEqualNP.TopForm.centreless G D).card + 2 * (PEqualNP.TopForm.centreless G D).card + (PEqualNP.TopForm.junk G D).card + (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ (PEqualNP.TopForm.Ustar G D).card + 6 := by omega
  by_cases hu : 3 ≤ (PEqualNP.TopForm.Ustar G D).card
  · exact notsize (h4 D K least top hu hj hK.1 hkt hp hb hroute)
  have hk5 : 5 ≤ K.card := by
    by_contra hn
    have hlt : K.card < 5 := by omega
    interval_cases hkc : K.card <;> simp [hkc] at hp <;> omega
  have hu2 : (PEqualNP.TopForm.Ustar G D).card = 2 := by
    by_contra hne
    have hk6 : 6 ≤ K.card := by
      by_contra hn
      have hlt : K.card < 6 := by omega
      interval_cases hkc : K.card <;> simp [hkc] at hp <;> omega
    omega
  have hc0 : (PEqualNP.TopForm.centreless G D).card = 0 := by omega
  have hr1 : (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ 1 := by omega
  have hupos : (PEqualNP.TopForm.Ustar G D).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hr,common⟩ := h2 11 G D least.1 hc0 hupos hr1 hroute
  have hk : K.card = 5 := by omega
  have ht : (PEqualNP.TopForm.tops G D \ PEqualNP.TopForm.centreless G D).card = 5 := by omega
  have hj2 : (PEqualNP.TopForm.junk G D).card = 2 := by omega
  exact notsize (h3 D least top hu2 (hm hk hu2) ht hc0 hj2 hr common)
