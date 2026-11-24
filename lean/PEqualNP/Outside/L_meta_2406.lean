import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2406

def St (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (ra rb : ℕ) : Prop :=
  ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs

theorem r_le (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) :
    ∀ a b, Relation.ReflTransGen (St n C) a b → a ≤ b := by
  intro a b h
  induction h with
  | refl => exact le_refl _
  | tail _ hs ih => exact le_trans ih (le_of_lt hs.1)

theorem r_last (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) :
    ∀ a b, Relation.ReflTransGen (St n C) a b → a = b ∨ ∃ rj, b = n + rj ∧ rj < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
  intro a b h
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, _, hs⟩
  · exact Or.inl h1.symm
  · obtain ⟨_, rj, h1, h2, h3, _⟩ := hs
    exact Or.inr ⟨rj, h1, h2, h3⟩

theorem r_dec (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) :
    ∀ m rj, Relation.ReflTransGen (St n C) m (n + rj) → m = n + rj ∨
      ∃ c ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs, Relation.ReflTransGen (St n C) m c := by
  intro m rj h
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, hmc, hs⟩
  · exact Or.inl h1.symm
  · obtain ⟨_, rj2, h1, h2, h3, h4⟩ := hs
    have h5 : rj2 = rj := by omega
    subst h5
    exact Or.inr ⟨c, h4, hmc⟩

theorem count {α : Type} [DecidableEq α] (L : ℕ → Finset α) (Rr : ℕ → ℕ → Prop) (isOr : ℕ → Prop)
    (hle : ∀ a b, Rr a b → a ≤ b) (hrefl : ∀ a, Rr a a)
    (htrans : ∀ a b c, Rr a b → Rr b c → Rr a c)
    (hleaf : ∀ w, ¬ isOr w → (L w).card ≤ 2)
    (hor : ∀ w, isOr w → ∃ p q, p < w ∧ q < w ∧ L w ⊆ L p ∪ L q ∧ Rr p w ∧ Rr q w) :
    ∀ N, ∀ W : Finset ℕ, (∀ w ∈ W, w < N) → ∀ B : Finset ℕ,
      (∀ g, isOr g → 3 ≤ (L g).card → (∃ r ∈ W, Rr g r) → g ∈ B) →
      (W.biUnion L).card ≤ 2 * (W.card + B.card) := by
  intro N
  induction N with
  | zero =>
    intro W hW B _
    have hWe : W = ∅ := Finset.eq_empty_of_forall_notMem (fun w hw => by have := hW w hw; omega)
    subst hWe
    simp
  | succ N ih =>
    intro W hW B hB
    by_cases hN : N ∈ W
    · by_cases hbig : 3 ≤ (L N).card
      · have hisor : isOr N := by
          by_contra h
          have := hleaf N h
          omega
        obtain ⟨p, q, hp, hq, hsub, hRp, hRq⟩ := hor N hisor
        have hNB : N ∈ B := hB N hisor hbig ⟨N, hN, hrefl N⟩
        have h1 := ih (insert p (insert q (W.erase N))) (by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_erase] at hw
            rcases hw with rfl | rfl | ⟨hne, hw⟩
            · exact hp
            · exact hq
            · have := hW w hw
              omega) (B.erase N) (by
            intro g hg hg3 ⟨r, hr, hgr⟩
            simp only [Finset.mem_insert, Finset.mem_erase] at hr
            have hgle := hle g r hgr
            rcases hr with rfl | rfl | ⟨hne, hr⟩
            · exact Finset.mem_erase.mpr ⟨by omega, hB g hg hg3 ⟨N, hN, htrans _ _ _ hgr hRp⟩⟩
            · exact Finset.mem_erase.mpr ⟨by omega, hB g hg hg3 ⟨N, hN, htrans _ _ _ hgr hRq⟩⟩
            · have := hW r hr
              exact Finset.mem_erase.mpr ⟨by omega, hB g hg hg3 ⟨r, hr, hgr⟩⟩)
        have hsubU : W.biUnion L ⊆ (insert p (insert q (W.erase N))).biUnion L := by
          intro x hx
          rw [Finset.mem_biUnion] at hx ⊢
          obtain ⟨w, hw, hxw⟩ := hx
          by_cases hwN : w = N
          · rw [hwN] at hxw
            rcases Finset.mem_union.mp (hsub hxw) with h | h
            · exact ⟨p, by simp, h⟩
            · exact ⟨q, by simp, h⟩
          · exact ⟨w, by simp [hwN, hw], hxw⟩
        have hc1 := Finset.card_le_card hsubU
        have hc2 : (insert p (insert q (W.erase N))).card ≤ (W.erase N).card + 2 := by
          have a1 := Finset.card_insert_le p (insert q (W.erase N))
          have a2 := Finset.card_insert_le q (W.erase N)
          omega
        have hc3 := Finset.card_erase_of_mem hN
        have hc4 := Finset.card_erase_of_mem hNB
        have hc5 : 0 < W.card := Finset.card_pos.mpr ⟨N, hN⟩
        have hc6 : 0 < B.card := Finset.card_pos.mpr ⟨N, hNB⟩
        omega
      · have h1 := ih (W.erase N) (by
            intro w hw
            have h2 := Finset.mem_erase.mp hw
            have := hW w h2.2
            omega) B (by
            intro g hg hg3 ⟨r, hr, hgr⟩
            exact hB g hg hg3 ⟨r, (Finset.mem_erase.mp hr).2, hgr⟩)
        have hsubU : W.biUnion L ⊆ L N ∪ (W.erase N).biUnion L := by
          intro x hx
          rw [Finset.mem_biUnion] at hx
          obtain ⟨w, hw, hxw⟩ := hx
          by_cases hwN : w = N
          · rw [hwN] at hxw
            exact Finset.mem_union_left _ hxw
          · exact Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwN, hw⟩, hxw⟩)
        have hc1 := Finset.card_le_card hsubU
        have hc2 := Finset.card_union_le (L N) ((W.erase N).biUnion L)
        have hc3 := Finset.card_erase_of_mem hN
        have hc5 : 0 < W.card := Finset.card_pos.mpr ⟨N, hN⟩
        omega
    · exact ih W (by
        intro w hw
        have := hW w hw
        have hne : w ≠ N := by
          rintro rfl
          exact hN hw
        omega) B hB

end PEqualNP.Outside.L_meta_2406

theorem PEqualNP.Outside.L_meta_2406 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (α : Type) (S : Finset α) (roots labelled : Finset ℕ) (lab : ℕ → Finset α), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (lab m).card ≤ 2) → (∀ a ∈ S, ∃ r ∈ roots, ∃ m1 ∈ labelled, R m1 r ∧ a ∈ lab m1) → S.card ≤ 2 * (roots.card + {jb : ℕ | jb < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jb).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ r2 ∈ roots, R (n + jb) r2) ∧ 3 ≤ ({x3 : α | ∃ m3 ∈ labelled, R m3 (n + jb) ∧ x3 ∈ lab m3}).ncard}.ncard) := by
  intro n C α S roots labelled lab hAO R hR hlab hS
  have hR2 : R = Relation.ReflTransGen (PEqualNP.Outside.L_meta_2406.St n C) := hR
  clear hR
  subst hR2
  classical
  obtain ⟨L, mem_L⟩ : ∃ L : ℕ → Finset α, ∀ w x, x ∈ L w ↔ ∃ m ∈ labelled,
      Relation.ReflTransGen (PEqualNP.Outside.L_meta_2406.St n C) m w ∧ x ∈ lab m := by
    refine ⟨fun w => (labelled.filter (fun m =>
      Relation.ReflTransGen (PEqualNP.Outside.L_meta_2406.St n C) m w)).biUnion lab, ?_⟩
    intro w x
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨m, ⟨hm, hr⟩, hx⟩
      exact ⟨m, hm, hr, hx⟩
    · rintro ⟨m, hm, hr, hx⟩
      exact ⟨m, ⟨hm, hr⟩, hx⟩
  have hleaf : ∀ w, ¬ (∃ rj, w = n + rj ∧ rj < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (L w).card ≤ 2 := by
    intro w hnot
    by_cases hw : w ∈ labelled
    · have hsub : L w ⊆ lab w := by
        intro x hx
        obtain ⟨m, hm, hmw, hxm⟩ := (mem_L w x).mp hx
        rcases PEqualNP.Outside.L_meta_2406.r_last n C m w hmw with h | h
        · rw [← h]
          exact hxm
        · exact absurd h hnot
      exact le_trans (Finset.card_le_card hsub) (hlab w hw).2
    · have hsub : L w ⊆ ∅ := by
        intro x hx
        obtain ⟨m, hm, hmw, hxm⟩ := (mem_L w x).mp hx
        rcases PEqualNP.Outside.L_meta_2406.r_last n C m w hmw with h | h
        · rw [h] at hm
          exact absurd hm hw
        · exact absurd h hnot
      rw [Finset.subset_empty.mp hsub]
      simp
  have hor : ∀ w, (∃ rj, w = n + rj ∧ rj < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∃ p q, p < w ∧ q < w ∧ L w ⊆ L p ∪ L q ∧
        Relation.ReflTransGen (PEqualNP.Outside.L_meta_2406.St n C) p w ∧
        Relation.ReflTransGen (PEqualNP.Outside.L_meta_2406.St n C) q w := by
    rintro w ⟨rj, rfl, hlt, hop⟩
    have hmemg : PEqualNP.MetaComplexity.NestedCover.gateAt C rj ∈ C.gates := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem _
    have hlen := hAO.2.2 _ hmemg
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
    have hpm : p ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs := by
      rw [hpq]
      simp
    have hqm : q ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs := by
      rw [hpq]
      simp
    have hp : p < n + rj := hAO.2.1 rj hlt p hpm
    have hq : q < n + rj := hAO.2.1 rj hlt q hqm
    refine ⟨p, q, hp, hq, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨m, hm, hmw, hxm⟩ := (mem_L _ x).mp hx
      rcases PEqualNP.Outside.L_meta_2406.r_dec n C m rj hmw with h | ⟨c, hc, hmc⟩
      · rcases (hlab m hm).1 with h2 | ⟨j, hj, _, hand⟩
        · omega
        · have hjj : j = rj := by omega
          subst hjj
          exact absurd (hop.symm.trans hand) (by intro h3; cases h3)
      · rw [hpq] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact Finset.mem_union_left _ ((mem_L _ x).mpr ⟨m, hm, hmc, hxm⟩)
        · exact Finset.mem_union_right _ ((mem_L _ x).mpr ⟨m, hm, hmc, hxm⟩)
    · exact Relation.ReflTransGen.single ⟨hp, rj, rfl, hlt, hop, hpm⟩
    · exact Relation.ReflTransGen.single ⟨hq, rj, rfl, hlt, hop, hqm⟩
  have key : ∀ T : Set ℕ, (∀ jb, jb < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C jb).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (∃ r2 ∈ roots, Relation.ReflTransGen (PEqualNP.Outside.L_meta_2406.St n C) (n + jb) r2) →
      3 ≤ (L (n + jb)).card → jb ∈ T) → T.Finite → S.card ≤ 2 * (roots.card + T.ncard) := by
    intro T hT hfin
    have hcount := PEqualNP.Outside.L_meta_2406.count L
      (Relation.ReflTransGen (PEqualNP.Outside.L_meta_2406.St n C))
      (fun w => ∃ rj, w = n + rj ∧ rj < C.gates.length ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or)
      (PEqualNP.Outside.L_meta_2406.r_le n C) (fun a => Relation.ReflTransGen.refl)
      (fun a b c h1 h2 => Relation.ReflTransGen.trans h1 h2) hleaf hor
      (roots.sup id + 1) roots (fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := id) hw))
      (hfin.toFinset.image (fun j => n + j)) (by
        rintro g ⟨rj, rfl, hlt, hop⟩ hg3 hr
        exact Finset.mem_image.mpr ⟨rj, hfin.mem_toFinset.mpr (hT rj hlt hop hr hg3), rfl⟩)
    have hSsub : S ⊆ roots.biUnion L := by
      intro a ha
      obtain ⟨r, hr, m1, hm1, hR1, ha1⟩ := hS a ha
      exact Finset.mem_biUnion.mpr ⟨r, hr, (mem_L r a).mpr ⟨m1, hm1, hR1, ha1⟩⟩
    have h1 := Finset.card_le_card hSsub
    have h2 : (hfin.toFinset.image (fun j => n + j)).card ≤ T.ncard := by
      rw [Set.ncard_eq_toFinset_card T hfin]
      exact Finset.card_image_le
    omega
  refine key _ ?_ ?_
  · intro jb h1 h2 h3 h4
    refine ⟨h1, h2, h3, ?_⟩
    refine le_of_le_of_eq h4 ?_
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    rw [Finset.mem_coe, mem_L]
    rfl
  · exact Set.Finite.subset (Set.finite_lt_nat C.gates.length) (fun j hj => hj.1)
