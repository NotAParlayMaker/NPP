import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_731

open Classical

theorem fin3 : ∀ a : Fin 3, a ≠ 2 → a = 0 ∨ a = 1 := by decide

-- In the first two colour classes of an orientation there is an independent set K that every
-- other vertex of those classes reaches by one arc. K is built from the least fixed point Y of
-- the map sending Y to the colour-1 vertices all of whose colour-0 out-neighbours touch Y.
theorem kernel {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop) (c : Fin n → Fin 3)
    (hc : ∀ u v, G.Adj u v → c u ≠ c v)
    (hD : ∀ u v, G.Adj u v ↔ (D u v ∨ D v u)) :
    ∃ K : Set (Fin n), (∀ v ∈ K, c v ≠ 2) ∧ (∀ u ∈ K, ∀ v ∈ K, ¬ G.Adj u v) ∧
      (∀ v, c v ≠ 2 → v ∉ K → ∃ u ∈ K, D v u) := by
  let Φ : Set (Fin n) →o Set (Fin n) :=
    { toFun := fun Y => {y | c y = 1 ∧ ∀ x, c x = 0 → D y x → ∃ y' ∈ Y, G.Adj x y'}
      monotone' := by
        intro Y Y' hYY' y hy
        refine ⟨hy.1, fun x hx hyx => ?_⟩
        obtain ⟨y', hy', hxy'⟩ := hy.2 x hx hyx
        exact ⟨y', hYY' hy', hxy'⟩ }
  have hfix : Φ Φ.lfp = Φ.lfp := Φ.map_lfp
  have hYmem : ∀ y, y ∈ Φ.lfp ↔
      (c y = 1 ∧ ∀ x, c x = 0 → D y x → ∃ y' ∈ Φ.lfp, G.Adj x y') := by
    intro y
    have h := congrArg (fun S : Set (Fin n) => y ∈ S) hfix
    exact (Iff.of_eq h).symm
  have hW : ∀ y ∈ Φ.lfp, ∀ x, c x = 0 → G.Adj x y → ∃ y' ∈ Φ.lfp, D x y' := by
    let W : Set (Fin n) :=
      {y | y ∈ Φ.lfp ∧ ∀ x, c x = 0 → G.Adj x y → ∃ y' ∈ Φ.lfp, D x y'}
    have hle : Φ.lfp ≤ W := by
      apply OrderHom.lfp_le
      intro y hy
      have hyY : y ∈ Φ.lfp := by
        have hmono : Φ W ≤ Φ Φ.lfp := Φ.monotone (fun z hz => hz.1)
        rw [hfix] at hmono
        exact hmono hy
      refine ⟨hyY, fun x hx hxy => ?_⟩
      rcases (hD x y).1 hxy with h | h
      · exact ⟨y, hyY, h⟩
      · obtain ⟨w, hw, hxw⟩ := hy.2 x hx h
        exact hw.2 x hx hxw
    intro y hy
    exact (hle hy).2
  refine ⟨Φ.lfp ∪ {x | c x = 0 ∧ ∀ y ∈ Φ.lfp, ¬ G.Adj x y}, ?_, ?_, ?_⟩
  · rintro v (hv | hv)
    · rw [((hYmem v).1 hv).1]; decide
    · rw [hv.1]; decide
  · rintro u (hu | hu) v (hv | hv) huv
    · exact hc u v huv (by rw [((hYmem u).1 hu).1, ((hYmem v).1 hv).1])
    · exact hv.2 u hu huv.symm
    · exact hu.2 v hv huv
    · exact hc u v huv (by rw [hu.1, hv.1])
  · intro v hv2 hvK
    rcases fin3 (c v) hv2 with h0 | h1
    · have hex : ¬ (∀ y ∈ Φ.lfp, ¬ G.Adj v y) := fun hall => hvK (Or.inr ⟨h0, hall⟩)
      push Not at hex
      obtain ⟨y, hy, hvy⟩ := hex
      obtain ⟨y', hy', hvy'⟩ := hW y hy v h0 hvy
      exact ⟨y', Or.inl hy', hvy'⟩
    · have hvY : ¬ (c v = 1 ∧ ∀ x, c x = 0 → D v x → ∃ y' ∈ Φ.lfp, G.Adj x y') :=
        fun h => hvK (Or.inl ((hYmem v).2 h))
      push Not at hvY
      obtain ⟨x, hx0, hvx, hxY⟩ := hvY h1
      exact ⟨x, Or.inr ⟨hx0, fun y hy hxy => hxY y hy hxy⟩, hvx⟩

end PEqualNP.Outside.L_meta_731

open PEqualNP.Outside.L_meta_731 in
theorem PEqualNP.Outside.L_meta_731 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop),
  G.Colorable 3 → (∀ u v, G.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
  ∃ I : Set (Fin n),
    (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) ∧
    n ≤ {v : Fin n | v ∈ I ∧ ∃ w, D v w}.ncard + {v : Fin n | v ∉ I ∧ ∃ w ∈ I, D v w}.ncard
      + G.indepNum := by
  classical
  intro n G D hcol hD hanti
  obtain ⟨C⟩ := hcol
  have hc : ∀ u v, G.Adj u v → (C u : Fin 3) ≠ C v := fun u v h => C.valid h
  obtain ⟨K, hK2, hKind, hKabs⟩ := kernel G D (fun v => C v) hc hD
  let I : Set (Fin n) := K ∪ {v | C v = 2 ∧ ∀ u ∈ K, ¬ G.Adj v u}
  have hIind : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
    rintro u (hu | hu) v (hv | hv) huv
    · exact hKind u hu v hv huv
    · exact hv.2 u hu huv.symm
    · exact hu.2 v hv huv
    · exact hc u v huv (by rw [hu.1, hv.1])
  have hImax : ∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u := by
    intro v hv
    by_cases h2 : C v = 2
    · have hex : ¬ ∀ u ∈ K, ¬ G.Adj v u := fun hall => hv (Or.inr ⟨h2, hall⟩)
      push Not at hex
      obtain ⟨u, hu, hvu⟩ := hex
      exact ⟨u, Or.inl hu, hvu⟩
    · obtain ⟨u, hu, hvu⟩ := hKabs v h2 (fun h => hv (Or.inl h))
      exact ⟨u, Or.inl hu, (hD v u).2 (Or.inl hvu)⟩
  have hB2 : ∀ v, v ∉ I → (¬ ∃ w ∈ I, D v w) → C v = 2 := by
    intro v hv hno
    by_contra h2
    obtain ⟨u, hu, hvu⟩ := hKabs v h2 (fun h => hv (Or.inl h))
    exact hno ⟨u, Or.inl hu, hvu⟩
  refine ⟨I, hIind, hImax, ?_⟩
  let A : Set (Fin n) := {v | v ∈ I ∧ ∃ w, D v w}
  let B : Set (Fin n) := {v | v ∉ I ∧ ∃ w ∈ I, D v w}
  let U : Set (Fin n) := {v | (v ∈ I ∧ ¬ ∃ w, D v w) ∨ (v ∉ I ∧ ¬ ∃ w ∈ I, D v w)}
  show n ≤ A.ncard + B.ncard + G.indepNum
  have hU : G.IsIndepSet U := by
    intro u hu v hv _ hadj
    rcases hu with ⟨huI, hus⟩ | ⟨huI, hun⟩ <;> rcases hv with ⟨hvI, hvs⟩ | ⟨hvI, hvn⟩
    · exact hIind u huI v hvI hadj
    · rcases (hD u v).1 hadj with h | h
      · exact hus ⟨v, h⟩
      · exact hvn ⟨u, huI, h⟩
    · rcases (hD u v).1 hadj with h | h
      · exact hun ⟨v, hvI, h⟩
      · exact hvs ⟨u, h⟩
    · exact hc u v hadj (by rw [hB2 u huI hun, hB2 v hvI hvn])
  have hUle : U.ncard ≤ G.indepNum := by
    have hU' : G.IsIndepSet (U.toFinset : Set (Fin n)) := by
      rw [Set.coe_toFinset]
      exact hU
    have h := SimpleGraph.IsIndepSet.card_le_indepNum hU'
    rwa [Set.ncard_eq_toFinset_card']
  have huniv : (Set.univ : Set (Fin n)) = (A ∪ B) ∪ U := by
    ext v
    simp only [Set.mem_univ, true_iff, Set.mem_union]
    by_cases hvI : v ∈ I
    · by_cases h1 : ∃ w, D v w
      · exact Or.inl (Or.inl ⟨hvI, h1⟩)
      · exact Or.inr (Or.inl ⟨hvI, h1⟩)
    · by_cases h2 : ∃ w ∈ I, D v w
      · exact Or.inl (Or.inr ⟨hvI, h2⟩)
      · exact Or.inr (Or.inr ⟨hvI, h2⟩)
  have hdisj1 : Disjoint A B := Set.disjoint_left.2 (fun v hA hB => hB.1 hA.1)
  have hdisj2 : Disjoint (A ∪ B) U := by
    rw [Set.disjoint_left]
    rintro v (hA | hB) hU'
    · rcases hU' with ⟨_, h⟩ | ⟨h, _⟩
      · exact h hA.2
      · exact h hA.1
    · rcases hU' with ⟨h, _⟩ | ⟨_, h⟩
      · exact hB.1 h
      · exact h hB.2
  have hn : n = A.ncard + B.ncard + U.ncard := by
    have h1 := Set.ncard_union_eq hdisj2
    have h2 := Set.ncard_union_eq hdisj1
    rw [← huniv, Set.ncard_univ, h2] at h1
    simpa using h1
  omega
