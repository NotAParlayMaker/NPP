import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1646 :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  classical
  intro n G _ hC4 U hEdge x Y hY R π hBlocks hCover
  have hAdj (y : Fin n) (hy : y ∈ Y) : G.Adj x y := G.mem_edgeSet.mp (hEdge _ (hY y hy))
  have common (B : Finset (Fin n)) (hB : B ∈ π) (y z : Fin n)
      (hy : y ∈ B) (hz : z ∈ B) (hyY : y ∈ Y) (hzx : G.Adj x z) : y = z := by
    rcases (hBlocks B hB).2 with hs | ⟨_,c,hc,hNoU⟩
    · exact Finset.card_le_one.mp hs.le y hy z hz
    · have hne : x ≠ c := by
        intro h
        exact hNoU y hy (h ▸ hY y hyY)
      apply Finset.card_le_one.mp (hC4 x c hne)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAdj y hyY,hc y hy⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzx,hc z hz⟩
  have count (V : Finset (Fin n)) (hVR : V ⊆ R)
      (hOne : ∀ B ∈ π, (V ∩ B).card ≤ 1) : V.card ≤ π.card := by
    have hSub : V ⊆ π.biUnion (fun B => V ∩ B) := by
      intro r hr
      obtain ⟨B,hB,hrB⟩ := hCover r (hVR hr)
      exact Finset.mem_biUnion.mpr ⟨B,hB,Finset.mem_inter.mpr ⟨hr,hrB⟩⟩
    exact (Finset.card_le_card hSub).trans (by
      simpa only [Nat.mul_one] using Finset.card_biUnion_le_card_mul π (fun B => V ∩ B) 1 hOne)
  constructor
  · apply count (R ∩ Y) Finset.inter_subset_left
    intro B hB
    apply Finset.card_le_one.mpr
    intro y hy z hz
    obtain ⟨hyRY,hyB⟩ := Finset.mem_inter.mp hy
    obtain ⟨hzRY,hzB⟩ := Finset.mem_inter.mp hz
    exact common B hB y z hyB hzB (Finset.mem_inter.mp hyRY).2 (hAdj z (Finset.mem_inter.mp hzRY).2)
  · intro hAll hn
    obtain ⟨r,hr,hrY⟩ : ∃ r ∈ R, r ∉ Y := by
      by_contra! h
      exact hn h
    let V := insert r (R ∩ Y)
    have hVR : V ⊆ R := Finset.insert_subset_iff.mpr ⟨hr,Finset.inter_subset_left⟩
    have hV := count V hVR (by
      intro B hB
      apply Finset.card_le_one.mpr
      intro y hy z hz
      obtain ⟨hyV,hyB⟩ := Finset.mem_inter.mp hy
      obtain ⟨hzV,hzB⟩ := Finset.mem_inter.mp hz
      rcases Finset.mem_insert.mp hyV with hy' | hy'
      · rcases Finset.mem_insert.mp hzV with hz' | hz'
        · exact hy'.trans hz'.symm
        · exact (common B hB z y hzB hyB (Finset.mem_inter.mp hz').2 (hAll y (hVR hyV))).symm
      · exact common B hB y z hyB hzB (Finset.mem_inter.mp hy').2 (hAll z (hVR hzV)))
    change (insert r (R ∩ Y)).card ≤ π.card at hV
    rwa [Finset.card_insert_of_notMem (fun h => hrY (Finset.mem_inter.mp h).2)] at hV
