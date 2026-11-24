import Mathlib.Data.Finset.Card
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  classical
  intro n G _ hfour U hU x Y hY R π hblocks hcover
  have adjY (a : Fin n) (ha : a ∈ Y) : G.Adj x a := hU _ (hY a ha)
  have unique {B : Finset (Fin n)} (hB : B ∈ π) {a b : Fin n}
      (ha : a ∈ B) (hb : b ∈ B) (haY : a ∈ Y) (hbX : G.Adj x b) : a = b := by
    rcases (hblocks B hB).2 with one | ⟨_, c, hc, hoff⟩
    · exact Finset.card_le_one_iff.mp one.le ha hb
    · have hcx : x ≠ c := by
        rintro rfl
        exact hoff a ha (hY a haY)
      apply Finset.card_le_one_iff.mp (hfour x c hcx)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, adjY a haY, hc a ha⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbX, hc b hb⟩
  let f (a : Fin n) : Finset (Fin n) := if h : a ∈ R then (hcover a h).choose else ∅
  have hf (a : Fin n) (ha : a ∈ R) : f a ∈ π ∧ a ∈ f a := by
    simpa [f, ha] using (hcover a ha).choose_spec
  have count (S : Finset (Fin n)) (hS : S ⊆ R) (hAdj : ∀ a ∈ S, G.Adj x a)
      (hOutside : ∀ a ∈ S, ∀ b ∈ S, a ∉ Y → b ∉ Y → a = b) : S.card ≤ π.card := by
    apply Finset.card_le_card_of_injOn f
    · intro a ha
      exact (hf a (hS ha)).1
    · intro a ha b hb hab
      have fa := hf a (hS ha)
      have fb := hf b (hS hb)
      by_cases hA : a ∈ Y
      · exact unique fb.1 (hab ▸ fa.2) fb.2 hA (hAdj b hb)
      by_cases hB : b ∈ Y
      · exact (unique fb.1 fb.2 (hab ▸ fa.2) hB (hAdj a ha)).symm
      exact hOutside a ha b hb hA hB
  constructor
  · apply count _ Finset.inter_subset_left
    · exact fun a ha => adjY a (Finset.mem_inter.mp ha).2
    · exact fun _ ha _ _ h _ => (h (Finset.mem_inter.mp ha).2).elim
  · intro hAdj hn
    obtain ⟨r, hr, hrY⟩ := Finset.not_subset.mp hn
    have hrI : r ∉ R ∩ Y := fun h => hrY (Finset.mem_inter.mp h).2
    have hS : insert r (R ∩ Y) ⊆ R := Finset.insert_subset hr Finset.inter_subset_left
    rw [← Finset.card_insert_of_notMem hrI]
    apply count _ hS (fun a ha => hAdj a (hS ha))
    intro a ha b hb hA hB
    have solo {v : Fin n} (hv : v ∈ insert r (R ∩ Y)) (hnY : v ∉ Y) : v = r :=
      (Finset.mem_insert.mp hv).resolve_right (fun h => hnY (Finset.mem_inter.mp h).2)
    exact (solo ha hA).trans (solo hb hB).symm
