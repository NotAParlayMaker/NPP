import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1719

theorem two_le_one {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hU : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (l m : Fin N) (hlm : l ≠ m) :
    (Finset.univ.filter (fun u => I u l ∧ I u m)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  exact hlm ((hU a b hab).unique ⟨ha'.1, hb'.1⟩ ⟨ha'.2, hb'.2⟩)

theorem pt_lines {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card ≤ q + 1 := by
  have hdisj : ∀ l ∈ Finset.univ.filter (fun l => I p l), ∀ m ∈ Finset.univ.filter (fun l => I p l), l ≠ m →
      Disjoint ((Finset.univ.filter (fun x => I x l)).erase p)
        ((Finset.univ.filter (fun x => I x m)).erase p) := by
    intro l hl m hm hlm
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := Finset.mem_erase.mp hx
    have h2 := Finset.mem_erase.mp hx'
    exact hlm ((hU x p h1.1).unique ⟨(Finset.mem_filter.mp h1.2).2, (Finset.mem_filter.mp hl).2⟩
      ⟨(Finset.mem_filter.mp h2.2).2, (Finset.mem_filter.mp hm).2⟩)
  have hcard := Finset.card_biUnion hdisj
  have hsum : ∑ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.filter (fun x => I x l)).erase p).card
      = (Finset.univ.filter (fun l => I p l)).card * q := by
    apply Finset.sum_const_nat
    intro l hl
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ p, (Finset.mem_filter.mp hl).2⟩),
      hc l]
    omega
  have hsub : (Finset.univ.filter (fun l => I p l)).biUnion
      (fun l => (Finset.univ.filter (fun x => I x l)).erase p) ⊆ Finset.univ.erase p := by
    intro x hx
    obtain ⟨l, _, hx2⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx2).1, Finset.mem_univ x⟩
  have hle := Finset.card_le_card hsub
  rw [hcard, hsum, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at hle
  have h3 : N = (q + 1) * q + 1 := by rw [hN]; ring
  have h4 : (Finset.univ.filter (fun l => I p l)).card * q ≤ (q + 1) * q := by omega
  exact Nat.le_of_mul_le_mul_right h4 (by omega)

end PEqualNP.Outside.L_meta_1719

theorem PEqualNP.Outside.L_meta_1719 : ∀ (q131 N131 r131 : ℕ) (I131 : Fin N131 → Fin N131 → Prop) [DecidableRel I131] (S131 W131 : Finset (Fin N131)), 2 ≤ q131 → N131 = q131 ^ 2 + q131 + 1 → (∀ l131f : Fin N131, (Finset.univ.filter (fun p131b => I131 p131b l131f)).card = q131 + 1) → (∀ pa131 pb131 : Fin N131, pa131 ≠ pb131 → ∃! lb131 : Fin N131, I131 pa131 lb131 ∧ I131 pb131 lb131) → (∀ (pz131 : Fin N131) (T131 : Finset (Fin N131)), T131.card ≤ r131 → (W131 \ W131.filter (fun l131 => ¬ I131 pz131 l131 ∧ l131 ∉ T131)).card ≤ q131 + 1 + r131 ∧ ∀ l131b ∈ W131.filter (fun l131a => ¬ I131 pz131 l131a ∧ l131a ∉ T131), (S131.filter (fun u131 => I131 u131 l131b)).card ≤ ((S131.filter (fun u131a => u131a ≠ pz131 ∧ ∀ m131 ∈ T131, ¬ I131 u131a m131)).filter (fun u131b => I131 u131b l131b)).card + r131) ∧ (∀ (wz131 : Fin N131) (Q131 : Finset (Fin N131)), Q131.card ≤ r131 → (W131 \ W131.filter (fun l131c => l131c ≠ wz131 ∧ ∀ p131 ∈ Q131, ¬ I131 p131 l131c)).card ≤ 1 + r131 * (q131 + 1) ∧ ∀ l131e ∈ W131.filter (fun l131d => l131d ≠ wz131 ∧ ∀ p131a ∈ Q131, ¬ I131 p131a l131d), (S131.filter (fun u131c => I131 u131c l131e)).card ≤ ((S131.filter (fun u131d => ¬ I131 u131d wz131 ∧ u131d ∉ Q131)).filter (fun u131e => I131 u131e l131e)).card + 1) := by
  intro q N r I _ S W hq hN hc hU
  refine ⟨?_, ?_⟩
  · intro pz T hT
    refine ⟨?_, ?_⟩
    · have hsub : W \ W.filter (fun l => ¬ I pz l ∧ l ∉ T) ⊆ Finset.univ.filter (fun l => I pz l) ∪ T := by
        intro x hx
        obtain ⟨hxW, hxn⟩ := Finset.mem_sdiff.mp hx
        by_cases h1 : I pz x
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h1⟩)
        · by_cases h2 : x ∈ T
          · exact Finset.mem_union_right _ h2
          · exact absurd (Finset.mem_filter.mpr ⟨hxW, h1, h2⟩) hxn
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (Finset.univ.filter (fun l => I pz l)) T
      have h3 := PEqualNP.Outside.L_meta_1719.pt_lines q I hq hN hc hU pz
      omega
    · intro l hl
      have hl' := (Finset.mem_filter.mp hl).2
      have hsub : S.filter (fun u => I u l) ⊆
          (S.filter (fun u => u ≠ pz ∧ ∀ m ∈ T, ¬ I u m)).filter (fun u => I u l) ∪
            T.biUnion (fun m => Finset.univ.filter (fun u => I u l ∧ I u m)) := by
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        by_cases hex : ∃ m ∈ T, I x m
        · obtain ⟨m, hm, hxm⟩ := hex
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨m, hm, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx'.2, hxm⟩⟩)
        · refine Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨hx'.1, ?_, ?_⟩, hx'.2⟩)
          · intro h
            rw [h] at hx'
            exact hl'.1 hx'.2
          · intro m hm hxm
            exact hex ⟨m, hm, hxm⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le
        ((S.filter (fun u => u ≠ pz ∧ ∀ m ∈ T, ¬ I u m)).filter (fun u => I u l))
        (T.biUnion (fun m => Finset.univ.filter (fun u => I u l ∧ I u m)))
      have h3 := Finset.card_biUnion_le_card_mul T
        (fun m => Finset.univ.filter (fun u => I u l ∧ I u m)) 1
        (fun m hm => PEqualNP.Outside.L_meta_1719.two_le_one I hU l m
          (fun h => hl'.2 (by rw [h]; exact hm)))
      omega
  · intro wz Q hQ
    refine ⟨?_, ?_⟩
    · have hsub : W \ W.filter (fun l => l ≠ wz ∧ ∀ p ∈ Q, ¬ I p l) ⊆
          {wz} ∪ Q.biUnion (fun p => Finset.univ.filter (fun l => I p l)) := by
        intro x hx
        obtain ⟨hxW, hxn⟩ := Finset.mem_sdiff.mp hx
        by_cases h1 : x = wz
        · exact Finset.mem_union_left _ (Finset.mem_singleton.mpr h1)
        · by_cases hex : ∃ p ∈ Q, I p x
          · obtain ⟨p, hp, hpx⟩ := hex
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
              ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hpx⟩⟩)
          · exact absurd (Finset.mem_filter.mpr ⟨hxW, h1, fun p hp hpx => hex ⟨p, hp, hpx⟩⟩) hxn
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le ({wz} : Finset (Fin N))
        (Q.biUnion (fun p => Finset.univ.filter (fun l => I p l)))
      have h3 := Finset.card_biUnion_le_card_mul Q
        (fun p => Finset.univ.filter (fun l => I p l)) (q + 1)
        (fun p _ => PEqualNP.Outside.L_meta_1719.pt_lines q I hq hN hc hU p)
      have h4 : Q.card * (q + 1) ≤ r * (q + 1) := Nat.mul_le_mul_right _ hQ
      have h5 : ({wz} : Finset (Fin N)).card = 1 := Finset.card_singleton wz
      omega
    · intro l hl
      have hl' := (Finset.mem_filter.mp hl).2
      have hsub : S.filter (fun u => I u l) ⊆
          (S.filter (fun u => ¬ I u wz ∧ u ∉ Q)).filter (fun u => I u l) ∪
            Finset.univ.filter (fun u => I u l ∧ I u wz) := by
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        by_cases h : I x wz
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx'.2, h⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨hx'.1, h, fun hxQ => hl'.2 x hxQ hx'.2⟩, hx'.2⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le
        ((S.filter (fun u => ¬ I u wz ∧ u ∉ Q)).filter (fun u => I u l))
        (Finset.univ.filter (fun u => I u l ∧ I u wz))
      have h3 := PEqualNP.Outside.L_meta_1719.two_le_one I hU l wz hl'.1
      omega
