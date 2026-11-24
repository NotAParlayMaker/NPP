import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1719
-- Point degrees follow by partitioning the other points by their unique joining line.
-- This generalizes the count in L-meta-1619 to arbitrary order.
def Pts {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun p => I p l)

lemma thru {N q : ℕ} (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h4 : ∀ l, (Pts I l).card = q + 1)
    (hu : ∀ p q : Fin N, p ≠ q → ∃! l : Fin N, I p l ∧ I q l) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  classical
  have hb : ((Finset.univ.filter (fun l => I p l)).biUnion (fun l => (Pts I l).erase p))
      = Finset.univ.erase p := by
    ext q
    rw [Finset.mem_biUnion, Finset.mem_erase]
    constructor
    · rintro ⟨l, _, hq⟩
      exact ⟨(Finset.mem_erase.mp hq).1, Finset.mem_univ _⟩
    · rintro ⟨hq, _⟩
      obtain ⟨l, ⟨hl1, hl2⟩, _⟩ := hu p q (Ne.symm hq)
      exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl1⟩,
        Finset.mem_erase.mpr ⟨hq, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl2⟩⟩⟩
  have hd : ∀ l ∈ Finset.univ.filter (fun l => I p l), ∀ l' ∈ Finset.univ.filter (fun l => I p l),
      l ≠ l' → Disjoint ((Pts I l).erase p) ((Pts I l').erase p) := by
    intro l hl l' hl' hne
    rw [Finset.disjoint_left]
    intro q hq hq'
    rw [Finset.mem_erase] at hq hq'
    have a1 := (Finset.mem_filter.mp hl).2
    have a2 := (Finset.mem_filter.mp hl').2
    have b1 := (Finset.mem_filter.mp hq.2).2
    have b2 := (Finset.mem_filter.mp hq'.2).2
    exact hne ((hu p q (Ne.symm hq.1)).unique ⟨a1, b1⟩ ⟨a2, b2⟩)
  have hc := Finset.card_biUnion hd
  rw [hb] at hc
  have h3 : ∀ l ∈ Finset.univ.filter (fun l => I p l), ((Pts I l).erase p).card = q := by
    intro l hl
    have hp : p ∈ Pts I l := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
    rw [Finset.card_erase_of_mem hp, h4]
    omega
  rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hc
  apply Nat.eq_of_mul_eq_mul_right (m := q) (by omega)
  rw [← hc, show N - 1 = q ^ 2 + q by omega]
  ring

lemma meet_le {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (uniq : ∀ p v : Fin N, p ≠ v → ∃! l, I p l ∧ I v l)
    {l m : Fin N} (hne : l ≠ m) :
    ((Pts I l) ∩ (Pts I m)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp v hv
  by_contra h
  simp only [Pts, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hp hv
  exact hne ((uniq p v h).unique ⟨hp.1,hv.1⟩ ⟨hp.2,hv.2⟩)

lemma cover {α : Type*} [DecidableEq α] (A B C : Finset α)
    (h : A ⊆ B ∪ C) : A.card ≤ B.card + C.card :=
  (Finset.card_le_card h).trans (Finset.card_union_le _ _)

lemma many {α β : Type*} [DecidableEq β] (T : Finset α) (f : α → Finset β) (k : ℕ)
    (bound : ∀ i ∈ T, (f i).card ≤ k) : (T.biUnion f).card ≤ T.card * k := by
  calc
    _ ≤ ∑ i ∈ T, (f i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ T, k := Finset.sum_le_sum bound
    _ = _ := by simp

end PEqualNP.Outside.L_meta_1719

open PEqualNP.Outside.L_meta_1719

theorem PEqualNP.Outside.L_meta_1719 : ∀ (q131 N131 r131 : ℕ) (I131 : Fin N131 → Fin N131 → Prop) [DecidableRel I131] (S131 W131 : Finset (Fin N131)), 2 ≤ q131 → N131 = q131 ^ 2 + q131 + 1 → (∀ l131f : Fin N131, (Finset.univ.filter (fun p131b => I131 p131b l131f)).card = q131 + 1) → (∀ pa131 pb131 : Fin N131, pa131 ≠ pb131 → ∃! lb131 : Fin N131, I131 pa131 lb131 ∧ I131 pb131 lb131) → (∀ (pz131 : Fin N131) (T131 : Finset (Fin N131)), T131.card ≤ r131 → (W131 \ W131.filter (fun l131 => ¬ I131 pz131 l131 ∧ l131 ∉ T131)).card ≤ q131 + 1 + r131 ∧ ∀ l131b ∈ W131.filter (fun l131a => ¬ I131 pz131 l131a ∧ l131a ∉ T131), (S131.filter (fun u131 => I131 u131 l131b)).card ≤ ((S131.filter (fun u131a => u131a ≠ pz131 ∧ ∀ m131 ∈ T131, ¬ I131 u131a m131)).filter (fun u131b => I131 u131b l131b)).card + r131) ∧ (∀ (wz131 : Fin N131) (Q131 : Finset (Fin N131)), Q131.card ≤ r131 → (W131 \ W131.filter (fun l131c => l131c ≠ wz131 ∧ ∀ p131 ∈ Q131, ¬ I131 p131 l131c)).card ≤ 1 + r131 * (q131 + 1) ∧ ∀ l131e ∈ W131.filter (fun l131d => l131d ≠ wz131 ∧ ∀ p131a ∈ Q131, ¬ I131 p131a l131d), (S131.filter (fun u131c => I131 u131c l131e)).card ≤ ((S131.filter (fun u131d => ¬ I131 u131d wz131 ∧ u131d ∉ Q131)).filter (fun u131e => I131 u131e l131e)).card + 1) := by
  intro q N r I inst S W hq hN hsize uniq
  classical
  let lines (p : Fin N) := Finset.univ.filter (fun l => I p l)
  have degree (p : Fin N) : (lines p).card = q+1 := thru hq hN I hsize uniq p
  constructor
  · intro z T hT
    constructor
    · have h := cover (W \ W.filter (fun l => ¬ I z l ∧ l ∉ T)) (lines z) T (by
        intro l hl
        simp only [Finset.mem_sdiff, Finset.mem_filter] at hl
        simp [lines]
        tauto)
      rw [degree] at h
      omega
    · intro l hl
      have good := (Finset.mem_filter.mp hl).2
      let f (m : Fin N) := Pts I l ∩ Pts I m
      have hb := many T f 1 (fun m hm => meet_le I uniq (by intro e; exact good.2 (e ▸ hm)))
      let kept := (S.filter (fun u => u ≠ z ∧ ∀ m ∈ T, ¬ I u m)).filter (fun u => I u l)
      have h : (S.filter (fun u => I u l)).card ≤ kept.card + (T.biUnion f).card := by
        apply cover
        intro u hu
        obtain ⟨huS,hul⟩ := Finset.mem_filter.mp hu
        by_cases leak : ∃ m ∈ T, I u m
        · obtain ⟨m,hm,hum⟩ := leak
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m,hm,by simp [f,Pts,hul,hum]⟩)
        · apply Finset.mem_union_left
          simp [kept,huS,hul]
          exact ⟨fun e => good.1 (e ▸ hul),fun m hm a => leak ⟨m,hm,a⟩⟩
      change _ ≤ kept.card + r
      omega
  · intro w Q hQ
    constructor
    · let removed := W \ W.filter (fun l => l ≠ w ∧ ∀ p ∈ Q, ¬ I p l)
      have h : removed.card ≤ ({w} : Finset _).card + (Q.biUnion lines).card := by
        apply cover
        intro l hl
        simp only [removed, Finset.mem_sdiff,Finset.mem_filter] at hl
        simp [lines]
        by_contra! bad
        exact hl.2 ⟨hl.1,bad.1,bad.2⟩
      have hb := many Q lines (q+1) (fun i _ => (degree i).le)
      simp only [Finset.card_singleton] at h
      change removed.card ≤ _
      exact h.trans (Nat.add_le_add_left (hb.trans (Nat.mul_le_mul_right _ hQ)) 1)
    · intro l hl
      obtain ⟨hne,havoid⟩ := (Finset.mem_filter.mp hl).2
      let kept := (S.filter (fun u => ¬ I u w ∧ u ∉ Q)).filter (fun u => I u l)
      have h : (S.filter (fun u => I u l)).card ≤ kept.card + (Pts I l ∩ Pts I w).card := by
        apply cover
        intro u hu
        obtain ⟨huS,hul⟩ := Finset.mem_filter.mp hu
        by_cases hUw : I u w
        · exact Finset.mem_union_right _ (by simp [Pts,hul,hUw])
        · exact Finset.mem_union_left _ (by simp [kept,huS,hul,hUw,show u ∉ Q from fun hq => havoid u hq hul])
      exact h.trans (Nat.add_le_add_left (meet_le I uniq hne) _)
