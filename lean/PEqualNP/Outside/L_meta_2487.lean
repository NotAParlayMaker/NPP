import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2487

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def G {α : Type} (src : α → ℕ) (seg : α → ℕ → Prop) (D : ℕ → Finset α) (isOr : ℕ → Prop)
    (g0 g1 : ℕ → ℕ) (p : α) (y x : ℕ) : Prop :=
  seg p y ∧ 2 ≤ (D y).card ∧
    (y = src p ∨ (seg p x ∧ (D x).card < 2 ∧ isOr y ∧ (g0 y = x ∨ g1 y = x)))

theorem core {α : Type} (Pl : Finset α) (src top : α → ℕ) (seg : α → ℕ → Prop)
    (D : ℕ → Finset α) (L : ℕ) (isOr : ℕ → Prop) (g0 g1 : ℕ → ℕ)
    (h1 : ∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ¬ isOr (src p))
    (h2 : ∀ p ∈ Pl, ∀ x, seg p x → p ∈ D x ∧ x < L)
    (h3 : ∀ p ∈ Pl, ∀ x, seg p x → x ≠ top p →
      ∃ y, isOr y ∧ (g0 y = x ∨ g1 y = x) ∧ seg p y ∧ D x ⊆ D y ∧ x < y)
    (h4 : ∀ g : ℕ, (Pl.filter (fun p => src p = g)).card ≤ 2)
    (W : Finset ℕ) (mem_W : ∀ x, x ∈ W ↔ ∃ p ∈ Pl, seg p x ∧ 2 ≤ (D x).card) :
    Pl.card ≤ W.card + (Pl.image top).card := by
  classical
  have stepA : ∀ p ∈ Pl, ∀ k x, L - x ≤ k → seg p x → (D x).card < 2 →
      (∃ y x1, seg p y ∧ 2 ≤ (D y).card ∧ seg p x1 ∧ (D x1).card < 2 ∧ isOr y ∧
        (g0 y = x1 ∨ g1 y = x1)) ∨ (D (top p)).card < 2 := by
    intro p hp k
    induction k with
    | zero =>
      intro x hk hs _
      have := (h2 p hp x hs).2
      omega
    | succ k ih =>
      intro x hk hs hn
      by_cases hxt : x = top p
      · right
        rw [← hxt]
        exact hn
      · obtain ⟨y, hyo, hys, hsy, _, hxy⟩ := h3 p hp x hs hxt
        by_cases hwy : 2 ≤ (D y).card
        · exact Or.inl ⟨y, x, hsy, hwy, hs, hn, hyo, hys⟩
        · exact ih y (by omega) hsy (by omega)
  have stepB : ∀ p ∈ Pl, (∃ y x, G src seg D isOr g0 g1 p y x) ∨ (D (top p)).card < 2 := by
    intro p hp
    obtain ⟨hs, _, _⟩ := h1 p hp
    by_cases hw : 2 ≤ (D (src p)).card
    · exact Or.inl ⟨src p, 0, hs, hw, Or.inl rfl⟩
    · rcases stepA p hp (L - src p) (src p) le_rfl hs (by omega) with ⟨y, x, a, b, c, d, e, f⟩ | h
      · exact Or.inl ⟨y, x, a, b, Or.inr ⟨c, d, e, f⟩⟩
      · exact Or.inr h
  obtain ⟨P2, P1, hsum, mem_P2, mem_P1⟩ : ∃ P2 P1 : Finset α, P2.card + P1.card = Pl.card ∧
      (∀ p, p ∈ P2 ↔ p ∈ Pl ∧ ∃ y x, G src seg D isOr g0 g1 p y x) ∧
      (∀ p, p ∈ P1 ↔ p ∈ Pl ∧ ¬ ∃ y x, G src seg D isOr g0 g1 p y x) :=
    ⟨_, _, Finset.card_filter_add_card_filter_not (s := Pl)
      (fun p => ∃ y x, G src seg D isOr g0 g1 p y x),
      fun p => Finset.mem_filter, fun p => Finset.mem_filter⟩
  have hG : ∀ p ∈ P2, ∃ y x, G src seg D isOr g0 g1 p y x := fun p hp => ((mem_P2 p).mp hp).2
  choose! m px hm using hG
  have hP2Pl : ∀ p ∈ P2, p ∈ Pl := fun p hp => ((mem_P2 p).mp hp).1
  have hfib : ∀ p ∈ P2, isOr (m p) →
      seg p (px p) ∧ (D (px p)).card < 2 ∧ (g0 (m p) = px p ∨ g1 (m p) = px p) := by
    intro p hp ho
    obtain ⟨_, _, h | ⟨a, b, _, d⟩⟩ := hm p hp
    · rw [h] at ho
      exact absurd ho (h1 p (hP2Pl p hp)).2.2
    · exact ⟨a, b, d⟩
  have hsrc : ∀ p ∈ P2, ¬ isOr (m p) → m p = src p := by
    intro p hp ho
    obtain ⟨_, _, h | ⟨_, _, c, _⟩⟩ := hm p hp
    · exact h
    · exact absurd c ho
  have hmW : ∀ p ∈ P2, m p ∈ W := by
    intro p hp
    obtain ⟨hs, hw, _⟩ := hm p hp
    exact (mem_W _).mpr ⟨p, hP2Pl p hp, hs, hw⟩
  have hpar : ∀ y ∈ W \ Pl.image top, ∃ z, z ∈ W ∧ isOr z ∧ (g0 z = y ∨ g1 z = y) := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    obtain ⟨p, hp, hs, hw⟩ := (mem_W y).mp hy.1
    have hne : y ≠ top p := by
      intro h
      apply hy.2
      rw [h]
      exact Finset.mem_image_of_mem top hp
    obtain ⟨z, hzo, hzs, hsz, hD, _⟩ := h3 p hp y hs hne
    exact ⟨z, (mem_W z).mpr ⟨p, hp, hsz, le_trans hw (Finset.card_le_card hD)⟩, hzo, hzs⟩
  choose! par hpar1 using hpar
  have hwide : ∀ y ∈ W \ Pl.image top, 2 ≤ (D y).card := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    obtain ⟨_, _, _, hw⟩ := (mem_W y).mp hy.1
    exact hw
  have hnar : ∀ p ∈ P1, (D (top p)).card < 2 := by
    intro p hp
    have hp1 := (mem_P1 p).mp hp
    rcases stepB p hp1.1 with h | h
    · exact absurd h hp1.2
    · exact h
  have hP1c : P1.card ≤ (Pl.image top \ W).card := by
    apply Finset.card_le_card_of_injOn top
    · intro p hp
      have hp0 : p ∈ P1 := Finset.mem_coe.mp hp
      have hp1 := (mem_P1 p).mp hp0
      have hn := hnar p hp0
      refine Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem top hp1.1, ?_⟩)
      intro hw
      obtain ⟨_, _, _, hw2⟩ := (mem_W _).mp hw
      omega
    · intro p hp q hq hpq
      have hp0 : p ∈ P1 := Finset.mem_coe.mp hp
      have hq0 : q ∈ P1 := Finset.mem_coe.mp hq
      have hp1 := (mem_P1 p).mp hp0
      have hq1 := (mem_P1 q).mp hq0
      have hn := hnar p hp0
      have h1p := (h2 p hp1.1 (top p) (h1 p hp1.1).2.1).1
      have h1q := (h2 q hq1.1 (top q) (h1 q hq1.1).2.1).1
      rw [← hpq] at h1q
      exact Finset.card_le_one.mp (by omega) p h1p q h1q
  have hQ : (P2.disjSum (W \ Pl.image top)).card ≤ 2 * W.card := by
    refine Finset.card_le_mul_card_image_of_maps_to (f := Sum.elim m par) ?_ 2 ?_
    · intro q hq
      rcases Finset.mem_disjSum.mp hq with ⟨p, hp, rfl⟩ | ⟨y, hy, rfl⟩
      · exact hmW p hp
      · exact (hpar1 y hy).1
    · intro y hy
      by_cases hyo : isOr y
      · refine le_trans (Finset.card_le_card_of_injOn (t := ({g0 y, g1 y} : Finset ℕ))
          (Sum.elim px id) ?_ ?_) Finset.card_le_two
        · intro q hq
          obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
          rcases Finset.mem_disjSum.mp hq1 with ⟨p, hp, rfl⟩ | ⟨z, hz, rfl⟩
          · have hq3 : m p = y := hq2
            obtain ⟨_, _, hsl⟩ := hfib p hp (by rw [hq3]; exact hyo)
            rw [hq3] at hsl
            refine Finset.mem_coe.mpr ?_
            show px p ∈ ({g0 y, g1 y} : Finset ℕ)
            rw [Finset.mem_insert, Finset.mem_singleton]
            rcases hsl with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          · have hq3 : par z = y := hq2
            have hsl := (hpar1 z hz).2.2
            rw [hq3] at hsl
            refine Finset.mem_coe.mpr ?_
            show z ∈ ({g0 y, g1 y} : Finset ℕ)
            rw [Finset.mem_insert, Finset.mem_singleton]
            rcases hsl with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
        · intro q hq q1 hq1 heq
          obtain ⟨hqa, hqb⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
          obtain ⟨hq1a, hq1b⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq1)
          rcases Finset.mem_disjSum.mp hqa with ⟨p, hp, rfl⟩ | ⟨z, hz, rfl⟩
          · have hq3 : m p = y := hqb
            obtain ⟨hsp, hnp, _⟩ := hfib p hp (by rw [hq3]; exact hyo)
            rcases Finset.mem_disjSum.mp hq1a with ⟨p1, hp1, rfl⟩ | ⟨z1, hz1, rfl⟩
            · have hq4 : m p1 = y := hq1b
              obtain ⟨hsp1, _, _⟩ := hfib p1 hp1 (by rw [hq4]; exact hyo)
              have he : px p = px p1 := heq
              have hd := (h2 p (hP2Pl p hp) _ hsp).1
              have hd1 := (h2 p1 (hP2Pl p1 hp1) _ hsp1).1
              rw [← he] at hd1
              have : p = p1 := Finset.card_le_one.mp (by omega) p hd p1 hd1
              rw [this]
            · have he : px p = z1 := heq
              have := hwide z1 hz1
              rw [← he] at this
              omega
          · rcases Finset.mem_disjSum.mp hq1a with ⟨p1, hp1, rfl⟩ | ⟨z1, hz1, rfl⟩
            · have hq4 : m p1 = y := hq1b
              obtain ⟨_, hnp1, _⟩ := hfib p1 hp1 (by rw [hq4]; exact hyo)
              have he : z = px p1 := heq
              have := hwide z hz
              rw [he] at this
              omega
            · have he : z = z1 := heq
              rw [he]
      · refine le_trans (Finset.card_le_card ?_)
          (le_trans (Finset.card_image_le (f := Sum.inl)) (h4 y))
        intro q hq
        obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
        rcases Finset.mem_disjSum.mp hq1 with ⟨p, hp, rfl⟩ | ⟨z, hz, rfl⟩
        · have hq3 : m p = y := hq2
          refine Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hP2Pl p hp, ?_⟩, rfl⟩
          rw [← hsrc p hp (by rw [hq3]; exact hyo)]
          exact hq3
        · have hq3 : par z = y := hq2
          have := (hpar1 z hz).2.1
          rw [hq3] at this
          exact absurd this hyo
  rw [Finset.card_disjSum] at hQ
  have e1 := Finset.card_sdiff_add_card_inter W (Pl.image top)
  have e2 := Finset.card_sdiff_add_card_inter (Pl.image top) W
  rw [Finset.inter_comm] at e2
  omega

theorem main (n N : ℕ) (C : Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ)
    (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (h1 : ∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and)
    (h2 : ∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length)
    (h3 : ∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧
      (gateAt C j2).op = GateOp.or ∧ (gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧
      seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2))
    (h4 : ∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2) :
    Pl.card ≤ {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.ncard + (Pl.image top).card := by
  have hfin : {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.Finite :=
    (Set.finite_lt_nat (n + C.gates.length)).subset (fun x hx => by
      obtain ⟨p, hp, hs, _⟩ := hx
      exact (h2 p hp x hs).2.2)
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine core Pl src top seg D (n + C.gates.length)
    (fun y => ∃ j, y = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.or)
    (fun y => (gateAt C (y - n)).inputs.getD 0 0) (fun y => (gateAt C (y - n)).inputs.getD 1 0)
    ?_ ?_ ?_ h4 hfin.toFinset (fun x => hfin.mem_toFinset)
  · intro p hp
    obtain ⟨a, b, j, hj, hjl, hop⟩ := h1 p hp
    refine ⟨a, b, ?_⟩
    rintro ⟨j1, hj1, _, hop1⟩
    have hjj : j = j1 := by omega
    subst hjj
    rw [hop] at hop1
    cases hop1
  · intro p hp x hs
    exact ⟨(h2 p hp x hs).1, (h2 p hp x hs).2.2⟩
  · intro p hp x hs hne
    obtain ⟨j, c, hjl, hop, hc, hc2, hsj, hD⟩ := h3 p hp x hs hne
    refine ⟨n + j, ⟨j, rfl, hjl, hop⟩, ?_, hsj, hD, ?_⟩
    · show (gateAt C (n + j - n)).inputs.getD 0 0 = x ∨ (gateAt C (n + j - n)).inputs.getD 1 0 = x
      rw [Nat.add_sub_cancel_left]
      rcases (by omega : c = 0 ∨ c = 1) with hc0 | hc0
      · rw [hc0] at hc
        exact Or.inl hc
      · rw [hc0] at hc
        exact Or.inr hc
    · have hmemg : gateAt C j ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hjl]
        exact List.getElem_mem _
      have hlen := hAO.2.2 _ hmemg
      have hlt : c < (gateAt C j).inputs.length := by omega
      have hxm : x ∈ (gateAt C j).inputs := by
        rw [← hc, List.getD_eq_getElem _ _ hlt]
        exact List.getElem_mem _
      exact hAO.2.1 j hjl x hxm

end PEqualNP.Outside.L_meta_2487

theorem PEqualNP.Outside.L_meta_2487 : ∀ (n N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ) (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)), PEqualNP.TopForm.IsAO2 n C → (∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length) → (∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧ seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2)) → (∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2) → Pl.card ≤ {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.ncard + (Pl.image top).card := by
  intro n N C Pl src top seg D hAO h1 h2 h3 h4
  exact PEqualNP.Outside.L_meta_2487.main n N C Pl src top seg D hAO h1 h2 h3 h4
