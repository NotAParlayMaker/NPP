import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxHeartbeats 2500000 in
-- A raw input on each side turns the junk AND on. Appending the OR of
-- its safe vertices gives three clauses. On this graph the edges accepted
-- by such a sound conjunction all meet one of two fixed vertices.
theorem PEqualNP.Outside.R_meta_4007_47
    (gateCover : let G := edgeGraph 11 ( ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).map (fun k => (k/11,k%11)))
      ∀ (C : Circuit), IsAO2 11 C → ∀ j ∈ junk G C,
      ∃ a b : Fin 11, ∀ u v, G.Adj u v →
        (∀ i : Fin 2, u ∈ side C j i ∨ v ∈ side C j i) →
        (u ∈ wmax G C j ∨ v ∈ wmax G C j) →
        u=a ∨ v=a ∨ u=b ∨ v=b)
    (count : let G := edgeGraph 11 ( ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).map (fun k => (k/11,k%11)))
      ∀ (C : Circuit) (g h : Nat), IsLeastAO G C → TopForm G C →
      junk G C = {g,h} → InCone 11 C g h →
      let U := Ustar G C
      let Z := centreless G C
      let q := 2*Z.card + (orN G C \ lam G C).card
      3+q ≤ 2*U.card → (tops G C \ Z).card+q ≤ 4+U.card →
      (∃ K : Nat → Fin 11 × Fin 11, ∀ u v, s(u,v) ∈ U →
        ∃ j ∈ junk G C, (∀ i : Fin 2, u ∈ side C j i ∨ v ∈ side C j i) ∧
        ((u ∈ wmax G C j ∨ v ∈ wmax G C j) →
          u=(K j).1 ∨ v=(K j).1 ∨ u=(K j).2 ∨ v=(K j).2)) → 22 ≤ C.size) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : ℕ := (2 : ℕ) * x12.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;             (3 : ℕ) + x13 ≤ (2 : ℕ) * x11.card → (PEqualNP.TopForm.tops x1 x3 \ x12).card + x13 ≤ (4 : ℕ) + x11.card → (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ PEqualNP.TopForm.junk x1 x3, ∀ (x20 : Fin (2 : ℕ)), x16 ∈ PEqualNP.TopForm.side x3 x19 x20 ∨ x17 ∈ PEqualNP.TopForm.side x3 x19 x20) → (22 : ℕ) ≤ x3.size := by
  intro G inst C g h graph least top pair cone U Z q low high witness
  let F := edgeGraph 11 ( ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).map (fun k => (k/11,k%11)))
  have hF : G = F := graph
  subst G
  have eqInst : inst = (inferInstance : DecidableRel F.Adj) := Subsingleton.elim _ _
  cases eqInst
  classical
  have covers (j : Nat) : ∃ a b : Fin 11, ∀ u v, j ∈ junk F C → F.Adj u v →
      (∀ i : Fin 2, u ∈ side C j i ∨ v ∈ side C j i) →
      (u ∈ wmax F C j ∨ v ∈ wmax F C j) → u=a ∨ v=a ∨ u=b ∨ v=b := by
    by_cases hj : j ∈ junk F C
    · obtain ⟨a,b,hc⟩ := gateCover C least.1 j hj
      exact ⟨a,b,fun u v _ => hc u v⟩
    · exact ⟨0,0,fun _ _ hm => (hj hm).elim⟩
  choose a b cover using covers
  apply count C g h least top pair cone low high
  refine ⟨fun j => (a j,b j), ?_⟩
  intro u v huv
  obtain ⟨j,hj,hside⟩ := witness u v huv
  have adj : F.Adj u v := by
    have he := (Finset.mem_sdiff.mp huv).1
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
  exact ⟨j,hj,hside,cover j u v hj adj hside⟩
