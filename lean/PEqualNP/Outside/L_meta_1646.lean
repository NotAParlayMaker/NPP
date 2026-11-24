import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1646_aux

open PEqualNP.TopForm

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {U : Finset (Sym2 (Fin n))} {x : Fin n} {Y R : Finset (Fin n)}
  {π : Finset (Finset (Fin n))}

lemma card_inter_le_one (h4 : NoFourCycle G) (hU : ∀ e ∈ U, e ∈ G.edgeSet)
    (hY : ∀ y ∈ Y, s(x, y) ∈ U)
    (hπ : ∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n,
      (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U)))
    {B : Finset (Fin n)} (hB : B ∈ π) : (B ∩ Y).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro y1 hy1 y2 hy2
  obtain ⟨hy1B, hy1Y⟩ := Finset.mem_inter.mp hy1
  obtain ⟨hy2B, hy2Y⟩ := Finset.mem_inter.mp hy2
  rcases (hπ B hB).2 with h1 | ⟨h2, c, hc, hcU⟩
  · exact Finset.card_le_one.mp (le_of_eq h1) y1 hy1B y2 hy2B
  · by_contra hne
    have hcy1 : G.Adj c y1 := hc y1 hy1B
    have hcy2 : G.Adj c y2 := hc y2 hy2B
    have hxy1 : G.Adj x y1 := (SimpleGraph.mem_edgeSet (G := G)).mp (hU _ (hY y1 hy1Y))
    have hxy2 : G.Adj x y2 := (SimpleGraph.mem_edgeSet (G := G)).mp (hU _ (hY y2 hy2Y))
    have hcm : c ∈ Finset.univ.filter (fun w => G.Adj y1 w ∧ G.Adj y2 w) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(G.adj_comm y1 c).mpr hcy1, (G.adj_comm y2 c).mpr hcy2⟩
    have hxm : x ∈ Finset.univ.filter (fun w => G.Adj y1 w ∧ G.Adj y2 w) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(G.adj_comm y1 x).mpr hxy1, (G.adj_comm y2 x).mpr hxy2⟩
    have heq : c = x := Finset.card_le_one.mp (h4 y1 y2 hne) c hcm x hxm
    exact (hcU y1 hy1B) (heq ▸ hY y1 hy1Y)

lemma inter_empty_of_block (h4 : NoFourCycle G) (hU : ∀ e ∈ U, e ∈ G.edgeSet)
    (hY : ∀ y ∈ Y, s(x, y) ∈ U)
    (hπ : ∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n,
      (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U)))
    (hAdj : ∀ v ∈ R, G.Adj x v)
    {r0 : Fin n} (hr0R : r0 ∈ R) (hr0Y : r0 ∉ Y)
    {B : Finset (Fin n)} (hB : B ∈ π) (hr0B : r0 ∈ B) : B ∩ Y = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  obtain ⟨hyB, hyY⟩ := Finset.mem_inter.mp hy
  have hne : r0 ≠ y := fun h => hr0Y (h ▸ hyY)
  rcases (hπ B hB).2 with h1 | ⟨h2, c, hc, hcU⟩
  · exact hne (Finset.card_le_one.mp (le_of_eq h1) r0 hr0B y hyB)
  · have hcr : G.Adj c r0 := hc r0 hr0B
    have hcy : G.Adj c y := hc y hyB
    have hxr : G.Adj x r0 := hAdj r0 hr0R
    have hxy : G.Adj x y := (SimpleGraph.mem_edgeSet (G := G)).mp (hU _ (hY y hyY))
    have hcm : c ∈ Finset.univ.filter (fun w => G.Adj r0 w ∧ G.Adj y w) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(G.adj_comm r0 c).mpr hcr, (G.adj_comm y c).mpr hcy⟩
    have hxm : x ∈ Finset.univ.filter (fun w => G.Adj r0 w ∧ G.Adj y w) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(G.adj_comm r0 x).mpr hxr, (G.adj_comm y x).mpr hxy⟩
    have heq : c = x := Finset.card_le_one.mp (h4 r0 y hne) c hcm x hxm
    exact (hcU y hyB) (heq ▸ hY y hyY)

end PEqualNP.Outside.L_meta_1646_aux

open PEqualNP.Outside.L_meta_1646_aux

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  intro n G hdec h4 U hU x Y hY R π hπ hcover
  classical
  let f : Fin n → Finset (Fin n) := fun z => if hz : z ∈ R then (hcover z hz).choose else ∅
  have hf : ∀ z (hz : z ∈ R), f z ∈ π ∧ z ∈ f z := by
    intro z hz
    dsimp only [f]
    rw [dif_pos hz]
    exact (hcover z hz).choose_spec
  refine ⟨?_, ?_⟩
  · have hinj : Set.InjOn f ↑(R ∩ Y) := by
      intro y1 hy1 y2 hy2 heq
      simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at hy1 hy2
      by_contra hne
      have h1 : (f y1 ∩ Y).card ≤ 1 :=
        card_inter_le_one h4 hU hY hπ (hf y1 hy1.1).1
      have hmem1 : y1 ∈ f y1 ∩ Y := Finset.mem_inter.mpr ⟨(hf y1 hy1.1).2, hy1.2⟩
      have hmem2 : y2 ∈ f y1 ∩ Y := by
        refine Finset.mem_inter.mpr ⟨?_, hy2.2⟩
        rw [heq]
        exact (hf y2 hy2.1).2
      exact hne (Finset.card_le_one.mp h1 y1 hmem1 y2 hmem2)
    calc (R ∩ Y).card = ((R ∩ Y).image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ π.card := Finset.card_le_card (by
          intro B hB
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hB
          exact (hf z (Finset.mem_inter.mp hz).1).1)
  · intro hAdj hnotsub
    obtain ⟨r0, hr0R, hr0Y⟩ := Finset.not_subset.mp hnotsub
    set S : Finset (Fin n) := insert r0 (R ∩ Y) with hS
    have hScard : S.card = (R ∩ Y).card + 1 := by
      rw [hS, Finset.card_insert_of_notMem]
      simp [hr0Y]
    have hinj : Set.InjOn f ↑S := by
      intro z1 hz1 z2 hz2 heq
      simp only [hS, Finset.coe_insert, Finset.coe_inter, Set.mem_insert_iff,
        Set.mem_inter_iff, Finset.mem_coe] at hz1 hz2
      rcases hz1 with hz1r | ⟨hz1R, hz1Y⟩
      · rcases hz2 with hz2r | ⟨hz2R, hz2Y⟩
        · rw [hz1r, hz2r]
        · have hz1R : z1 ∈ R := by rw [hz1r]; exact hr0R
          have hz2in : z2 ∈ f z1 := by
            rw [heq]
            exact (hf z2 hz2R).2
          have hr0in : r0 ∈ f z1 := hz1r ▸ (hf z1 hz1R).2
          have hempty := inter_empty_of_block h4 hU hY hπ hAdj hr0R hr0Y
            (hf z1 hz1R).1 hr0in
          have hmem : z2 ∈ f z1 ∩ Y := Finset.mem_inter.mpr ⟨hz2in, hz2Y⟩
          rw [hempty] at hmem
          exact absurd hmem (Finset.notMem_empty z2)
      · rcases hz2 with hz2r | ⟨hz2R, hz2Y⟩
        · have hz2R : z2 ∈ R := by rw [hz2r]; exact hr0R
          have hz1in : z1 ∈ f z2 := by
            rw [← heq]
            exact (hf z1 hz1R).2
          have hr0in : r0 ∈ f z2 := hz2r ▸ (hf z2 hz2R).2
          have hempty := inter_empty_of_block h4 hU hY hπ hAdj hr0R hr0Y
            (hf z2 hz2R).1 hr0in
          have hmem : z1 ∈ f z2 ∩ Y := Finset.mem_inter.mpr ⟨hz1in, hz1Y⟩
          rw [hempty] at hmem
          exact absurd hmem (Finset.notMem_empty z1)
        · have h1 : (f z1 ∩ Y).card ≤ 1 :=
            card_inter_le_one h4 hU hY hπ (hf z1 hz1R).1
          have hmem1 : z1 ∈ f z1 ∩ Y := Finset.mem_inter.mpr ⟨(hf z1 hz1R).2, hz1Y⟩
          have hmem2 : z2 ∈ f z1 ∩ Y := by
            refine Finset.mem_inter.mpr ⟨?_, hz2Y⟩
            rw [heq]
            exact (hf z2 hz2R).2
          exact Finset.card_le_one.mp h1 z1 hmem1 z2 hmem2
    have himg : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
    calc (R ∩ Y).card + 1 = S.card := hScard.symm
      _ = (S.image f).card := himg.symm
      _ ≤ π.card := Finset.card_le_card (by
          intro B hB
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hB
          refine (hf z ?_).1
          rcases Finset.mem_insert.mp hz with hzr | hz
          · rw [hzr]
            exact hr0R
          · exact (Finset.mem_inter.mp hz).1)
