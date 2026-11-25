import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge

namespace PEqualNP.Outside.R_meta_5264_1

noncomputable def edgeProp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
  (¬ ∃ u v : Fin n, e = s(u, v) ∧ ∃ h < C.gates.length, ∃ b : Fin 2,
    2 ≤ (orIn n C (n + h)).card ∧
    (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
    orIn n C (opnd C h b) = {v}) ∧
  ∃ a ∈ tops G C \ centreless G C,
    e ∈ gammaE G C a ∧
    ∃ w ∈ side C a 0 ∪ side C a 1, w ∈ e

noncomputable def edgeSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Finset (Sym2 (Fin n)) := by
  classical
  exact (Ustar G C).filter (edgeProp G C)

def pairWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
  ∃ u v : Fin n, e = s(u, v) ∧ ∃ j ∈ junk G C,
    gateVal n C j (pairInput u v) = true ∧
    gateVal n C j (pairInput u u) = false ∧
    gateVal n C j (pairInput v v) = false

def contactWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
  ∃ u v : Fin n, e = s(u, v) ∧ ∃ j ∈ junk G C,
    gateVal n C j (pairInput u u) = true ∧ v ∈ wmax G C j

noncomputable def vertices {n : ℕ} (F : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ e ∈ F, v ∈ e

def minimumDegreeThree {n : ℕ} (F : Finset (Sym2 (Fin n))) : Prop :=
  ∀ v, v ∈ vertices F → 3 ≤ (F.filter fun e => v ∈ e).card

theorem peel_to_minimum_degree_three {n : ℕ} (E : Finset (Sym2 (Fin n))) :
    ∃ F ⊆ E, minimumDegreeThree F ∧
      E.card ≤ F.card + 2 * (vertices E).card := by
  classical
  induction E using Finset.strongInductionOn with
  | _ E ih =>
      by_cases hdense : minimumDegreeThree E
      · exact ⟨E, Finset.Subset.rfl, hdense, by omega⟩
      · have hlow : ∃ v, v ∈ vertices E ∧ (E.filter fun e => v ∈ e).card < 3 := by
          by_contra h
          push Not at h
          apply hdense
          intro v hv
          have := h v hv
          omega
        obtain ⟨v, hv, hdeg⟩ := hlow
        obtain ⟨e, he, hve⟩ := (Finset.mem_filter.mp hv).2
        let K := E.filter fun e => v ∉ e
        have hKsub : K ⊆ E := Finset.filter_subset _ _
        have hKne : K ≠ E := by
          intro heq
          have : e ∈ K := heq ▸ he
          exact (Finset.mem_filter.mp this).2 hve
        have hKlt : K ⊂ E := Finset.ssubset_iff_subset_ne.mpr ⟨hKsub, hKne⟩
        obtain ⟨F, hFsub, hFdense, hFcard⟩ := ih K hKlt
        have hVsub : vertices K ⊆ vertices E := by
          intro w hw
          simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          obtain ⟨e', he', hw'⟩ := hw
          exact ⟨e', hKsub he', hw'⟩
        have hvnot : v ∉ vertices K := by
          intro h
          simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and] at h
          obtain ⟨e', he', hve'⟩ := h
          exact (Finset.mem_filter.mp he').2 hve'
        have hVlt : (vertices K).card < (vertices E).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hVsub, fun h => hvnot (h ▸ hv)⟩)
        have hsplit : (E.filter fun e => v ∈ e).card + K.card = E.card :=
          Finset.card_filter_add_card_filter_not (s := E) _
        have hdeg' : (E.filter fun e => v ∈ e).card ≤ 2 := by omega
        refine ⟨F, hFsub.trans hKsub, hFdense, ?_⟩
        omega

end PEqualNP.Outside.R_meta_5264_1

open PEqualNP.Outside.R_meta_5264_1

/-- Splits the bound into the small-junk case, an edge-to-junk route lemma,
    endpoint locality, and a dense-core counting lemma. -/
theorem PEqualNP.Outside.R_meta_5264_1
    (smallJunk : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      (junk G C).card ≤ 3 → (edgeSet G C).card ≤ k * (C.size + 1))
    (route : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      4 ≤ (junk G C).card → ∀ e ∈ edgeSet G C,
        pairWitness G C e ∨ contactWitness G C e)
    (endpointBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), IsLeastAO G C → ∀ F, F ⊆ edgeSet G C →
        (vertices F).card ≤ 2 * C.size)
    (denseCore : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
      4 ≤ (junk G C).card → ∀ F, F ⊆ edgeSet G C → minimumDegreeThree F →
        (∀ e ∈ F, pairWitness G C e ∨ contactWitness G C e) →
        F.card ≤ k * (C.size + 1)) :
    ∃ (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        (edgeSet G C).card ≤ c * (C.size + 1) := by
  classical
  obtain ⟨kSmall, hSmall⟩ := smallJunk
  obtain ⟨kCore, hCore⟩ := denseCore
  refine ⟨kSmall + kCore + 4, ?_⟩
  intro n G hDec hGirth hNonempty C hLeast hTop
  let E := edgeSet G C
  change E.card ≤ (kSmall + kCore + 4) * (C.size + 1)
  by_cases hFew : (junk G C).card ≤ 3
  · have h := hSmall n G hGirth hNonempty C hLeast hTop hFew
    change E.card ≤ kSmall * (C.size + 1) at h
    calc
      E.card ≤ kSmall * (C.size + 1) := h
      _ ≤ (kSmall + kCore + 4) * (C.size + 1) :=
        Nat.mul_le_mul_right (C.size + 1) (by omega)
  · have hMany : 4 ≤ (junk G C).card := by omega
    have hRoute : ∀ e ∈ E, pairWitness G C e ∨ contactWitness G C e := by
      intro e he
      exact route n G hGirth hNonempty C hLeast hTop hMany e he
    obtain ⟨F, hFsub, hDense, hPeel⟩ := peel_to_minimum_degree_three E
    have hVert := endpointBound n G C hLeast E (by intro e he; exact he)
    have hBound := hCore n G hGirth hNonempty C hLeast hTop hMany F hFsub hDense
      (fun e he => hRoute e (hFsub he))
    calc
      E.card ≤ F.card + 2 * (vertices E).card := hPeel
      _ ≤ kCore * (C.size + 1) + 4 * C.size := by omega
      _ ≤ kCore * (C.size + 1) + 4 * (C.size + 1) := by
        gcongr <;> omega
      _ = (kCore + 4) * (C.size + 1) := by rw [Nat.add_mul]
      _ ≤ (kSmall + kCore + 4) * (C.size + 1) :=
        Nat.mul_le_mul_right (C.size + 1) (by omega)
