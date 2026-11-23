import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_734

/-- A saturated set on the far side gives a maximal independent set. -/
theorem mis {n : ℕ} (G : SimpleGraph (Fin n)) (X B : Set (Fin n))
    (hb : ∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X))
    (hBX : ∀ b ∈ B, b ∉ X)
    (hsat : ∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) → y ∈ B)) :
    (∀ u ∈ {v | v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)},
      ∀ v ∈ {v | v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)}, ¬ G.Adj u v) ∧
    (∀ v, v ∉ {v | v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)} →
      ∃ u ∈ {v | v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)}, G.Adj v u) := by
  constructor
  · intro u hu v hv huv
    rcases hu with hu1 | ⟨hux, hun⟩
    · rcases hv with hv1 | ⟨hvx, hvn⟩
      · exact hBX u hu1 ((hb u v huv).mpr (hBX v hv1))
      · exact hvn u hu1 huv.symm
    · rcases hv with hv1 | ⟨hvx, hvn⟩
      · exact hun v hv1 huv
      · exact (hb u v huv).mp hux hvx
  · intro v hv
    by_cases hx : v ∈ X
    · by_contra hno
      exact hv (Or.inr ⟨hx, fun b hbB hvb => hno ⟨b, Or.inl hbB, hvb⟩⟩)
    · have hvB : v ∉ B := fun h => hv (Or.inl h)
      have h1 : ¬ ∀ x, G.Adj v x → ∃ b ∈ B, G.Adj x b := fun h => hvB (hsat v hx h)
      push_neg at h1
      obtain ⟨x, hvx, hxno⟩ := h1
      have hxX : x ∈ X := by
        by_contra hxn
        exact hx ((hb v x hvx).mpr hxn)
      exact ⟨x, Or.inr ⟨hxX, fun b hbB => hxno b hbB⟩, hvx⟩

theorem pigeon {n : ℕ} (S : Set (Fin n)) (hS : S.ncard ≤ 2) (a b c : Fin n)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) : a = b ∨ a = c ∨ b = c := by
  by_contra h
  push_neg at h
  have : 2 < S.ncard := (Set.two_lt_ncard_iff (Set.toFinite S)).mpr
    ⟨a, b, c, ha, hb, hc, h.1, h.2.1, h.2.2⟩
  omega

theorem side {n : ℕ} (G : SimpleGraph (Fin n)) (X : Set (Fin n))
    (hb : ∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X))
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hdeg : ∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard)
    (T : Set (Fin n)) (hT : (T ∩ X).ncard ≤ 2)
    (hmeet : ∀ I : Set (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) → ∃ t ∈ T, t ∈ I) :
    ∃ v ∈ T, ∀ w, G.Adj v w → w ∈ T := by
  classical
  by_contra hno
  have hno' : ∀ v, ∃ w, v ∈ T → (G.Adj v w ∧ w ∉ T) := by
    intro v
    by_cases hv : v ∈ T
    · have : ¬ ∀ w, G.Adj v w → w ∈ T := fun h => hno ⟨v, hv, h⟩
      push_neg at this
      obtain ⟨w, hw1, hw2⟩ := this
      exact ⟨w, fun _ => ⟨hw1, hw2⟩⟩
    · exact ⟨v, fun h => absurd h hv⟩
  choose f hf using hno'
  let N0 : Set (Fin n) := {x | ∃ s, s ∈ T ∧ s ∈ X ∧ G.Adj x (f s)}
  let B : Set (Fin n) := {y | y ∉ X ∧ ∀ x, G.Adj y x → x ∈ N0}
  have hBX : ∀ b ∈ B, b ∉ X := fun b hbB => hbB.1
  have hsat : ∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) → y ∈ B) := by
    intro y hy h
    refine ⟨hy, fun x hyx => ?_⟩
    obtain ⟨b, hbB, hxb⟩ := h x hyx
    exact hbB.2 x hxb.symm
  obtain ⟨hind, hdom⟩ := mis G X B hb hBX hsat
  obtain ⟨t, htT, htI⟩ := hmeet _ hind hdom
  rcases htI with htB | ⟨htX, htn⟩
  · -- t is on the far side and all its neighbours see the chosen vertices
    obtain ⟨x1, x2, x3, h1, h2, h3, h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).mp (hdeg t)
    obtain ⟨s1, hs1T, hs1X, ha1⟩ := htB.2 x1 h1
    obtain ⟨s2, hs2T, hs2X, ha2⟩ := htB.2 x2 h2
    obtain ⟨s3, hs3T, hs3X, ha3⟩ := htB.2 x3 h3
    have key : ∀ (xa xb sa sb : Fin n), G.Adj t xa → G.Adj t xb → xa ≠ xb → sa ∈ T →
        G.Adj xa (f sa) → G.Adj xb (f sb) → sa = sb → False := by
      intro xa xb sa sb hta htb hne hsaT haa hab hs
      subst hs
      rcases h4 t xa (f sa) xb hta haa hab.symm htb.symm with h | h
      · exact (hf sa hsaT).2 (h ▸ htT)
      · exact hne h
    rcases pigeon (T ∩ X) hT s1 s2 s3 ⟨hs1T, hs1X⟩ ⟨hs2T, hs2X⟩ ⟨hs3T, hs3X⟩ with h | h | h
    · exact key x1 x2 s1 s2 h1 h2 h12 hs1T ha1 ha2 h
    · exact key x1 x3 s1 s3 h1 h3 h13 hs1T ha1 ha3 h
    · exact key x2 x3 s2 s3 h2 h3 h23 hs2T ha2 ha3 h
  · -- t is on the near side: its chosen neighbour is in B
    have hft := hf t htT
    have hfB : f t ∈ B := by
      refine ⟨(hb t (f t) hft.1).mp htX, fun x hx => ⟨t, htT, htX, hx.symm⟩⟩
    exact htn (f t) hfB hft.1

end PEqualNP.Outside.L_meta_734

theorem PEqualNP.Outside.L_meta_734 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  G.Colorable 2 →
  (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
  (∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard) →
  ∀ T : Set (Fin n), T.ncard ≤ 5 →
    (∀ I : Set (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) →
      ∃ t ∈ T, t ∈ I) →
    ∃ v ∈ T, ∀ w, G.Adj v w → w ∈ T := by
  intro n G hcol h4 hdeg T hT hmeet
  obtain ⟨c⟩ := hcol
  have hb : ∀ u v, G.Adj u v → (u ∈ {v | c v = 0} ↔ v ∉ {v | c v = 0}) := by
    intro u v huv
    have hne := c.valid huv
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hu hv
      exact hne (hu.trans hv.symm)
    · intro hv
      by_contra hu
      apply hne
      have h1 : c u = 1 := by
        have := (c u).isLt
        ext
        have h0 : (c u).val ≠ 0 := fun h => hu (Fin.ext h)
        simp only [Fin.val_one]
        omega
      have h2 : c v = 1 := by
        have := (c v).isLt
        ext
        have h0 : (c v).val ≠ 0 := fun h => hv (Fin.ext h)
        simp only [Fin.val_one]
        omega
      rw [h1, h2]
  have hsplit := Set.ncard_inter_add_ncard_diff_eq_ncard T {v | c v = 0} (Set.toFinite T)
  by_cases hX : (T ∩ {v | c v = 0}).ncard ≤ 2
  · exact PEqualNP.Outside.L_meta_734.side G _ hb h4 hdeg T hX hmeet
  · have hY : (T ∩ {v | c v = 0}ᶜ).ncard ≤ 2 := by
      rw [← Set.diff_eq]
      omega
    refine PEqualNP.Outside.L_meta_734.side G _ ?_ h4 hdeg T hY hmeet
    intro u v huv
    have := hb u v huv
    simp only [Set.mem_compl_iff]
    tauto
