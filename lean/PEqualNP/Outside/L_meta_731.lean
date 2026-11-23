import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta731

theorem bip_kernel {n : ℕ} (D : Fin n → Fin n → Prop) (X Y : Set (Fin n))
    (hX : ∀ u ∈ X, ∀ v ∈ X, ¬ D u v) (hY : ∀ u ∈ Y, ∀ v ∈ Y, ¬ D u v) :
    ∃ K : Set (Fin n), K ⊆ X ∪ Y ∧ (∀ v ∈ X ∪ Y, v ∉ K → ∃ k ∈ K, D v k) ∧
      (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) := by
  let A : Set (Fin n) → Set (Fin n) := fun B => {x | x ∈ X ∧ ¬ ∃ b ∈ B, D x b}
  let g : Set (Fin n) →o Set (Fin n) :=
    ⟨fun B => {y | y ∈ Y ∧ ¬ ∃ a ∈ A B, D y a}, by
      intro B B' h y hy
      exact ⟨hy.1, fun ⟨a, ha, hya⟩ =>
        hy.2 ⟨a, ⟨ha.1, fun ⟨b, hb, hab⟩ => ha.2 ⟨b, h hb, hab⟩⟩, hya⟩⟩⟩
  obtain ⟨B, hB⟩ : ∃ B, g B = B := ⟨g.lfp, g.map_lfp⟩
  have hfix : ∀ y, y ∈ B ↔ y ∈ Y ∧ ¬ ∃ a ∈ A B, D y a := fun y => by
    exact (Set.ext_iff.mp hB y).symm
  refine ⟨A B ∪ B, ?_, ?_, ?_⟩
  · rintro v (hv | hv)
    · exact Or.inl hv.1
    · exact Or.inr ((hfix v).mp hv).1
  · rintro v (hv | hv) hvK
    · by_contra hcon
      refine hvK (Or.inl ⟨hv, fun ⟨b, hb, hvb⟩ => hcon ⟨b, Or.inr hb, hvb⟩⟩)
    · by_contra hcon
      refine hvK (Or.inr ((hfix v).mpr ⟨hv, fun ⟨a, ha, hva⟩ => hcon ⟨a, Or.inl ha, hva⟩⟩))
  · rintro u (hu | hu) v (hv | hv) h
    · exact hX u hu.1 v hv.1 h
    · exact hu.2 ⟨v, hv, h⟩
    · exact ((hfix u).mp hu).2 ⟨v, hv, h⟩
    · exact hY u ((hfix u).mp hu).1 v ((hfix v).mp hv).1 h

theorem exists_max_indep {n : ℕ} (G : SimpleGraph (Fin n)) (K : Set (Fin n))
    (hK : ∀ u ∈ K, ∀ v ∈ K, ¬ G.Adj u v) :
    ∃ I : Set (Fin n), K ⊆ I ∧ (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧
      ∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u := by
  classical
  let S : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun J => K ⊆ (J : Set (Fin n)) ∧ ∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v)
  have hne : S.Nonempty := by
    refine ⟨(Set.toFinite K).toFinset, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Set.Finite.coe_toFinset,
      Set.Finite.mem_toFinset]
    exact ⟨subset_rfl, hK⟩
  obtain ⟨J, hJS, hJmax⟩ := Finset.exists_max_image S Finset.card hne
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hJS
  refine ⟨(J : Set (Fin n)), hJS.1, fun u hu v hv => hJS.2 u hu v hv, ?_⟩
  intro v hv
  by_contra hcon
  have hcon' : ∀ u ∈ (J : Set (Fin n)), ¬ G.Adj v u := fun u hu hadj => hcon ⟨u, hu, hadj⟩
  have hmem : insert v J ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · intro k hk
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp (hJS.1 hk)))
    · intro u hu w hw
      rw [Finset.mem_insert] at hu hw
      rcases hu with rfl | hu <;> rcases hw with rfl | hw
      · exact G.loopless.irrefl _
      · exact hcon' w (Finset.mem_coe.mpr hw)
      · intro hadj
        exact hcon' u (Finset.mem_coe.mpr hu) hadj.symm
      · exact hJS.2 u hu w hw
  have hle := hJmax _ hmem
  rw [Finset.card_insert_of_notMem (fun h => hv (Finset.mem_coe.mpr h))] at hle
  omega

end PEqualNP.Outside.Meta731

theorem PEqualNP.Outside.L_meta_731 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop),
  G.Colorable 3 → (∀ u v, G.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
  ∃ I : Set (Fin n),
    (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) ∧
    n ≤ {v : Fin n | v ∈ I ∧ ∃ w, D v w}.ncard + {v : Fin n | v ∉ I ∧ ∃ w ∈ I, D v w}.ncard
      + G.indepNum := by
  classical
  intro n G D hc hD _
  obtain ⟨col⟩ := hc
  have hcol : ∀ u v, D u v → col u ≠ col v := fun u v h =>
    col.valid ((hD u v).mpr (Or.inl h))
  obtain ⟨K, hKXY, hKabs, hKind⟩ := PEqualNP.Outside.Meta731.bip_kernel D
    {v | col v = 0} {v | col v = 1}
    (fun u hu v hv h => hcol u v h (hu.trans hv.symm))
    (fun u hu v hv h => hcol u v h (hu.trans hv.symm))
  obtain ⟨I, hKI, hIind, hImax⟩ := PEqualNP.Outside.Meta731.exists_max_indep G K
    (fun u hu v hv hadj => by
      rcases (hD u v).mp hadj with h | h
      · exact hKind u hu v hv h
      · exact hKind v hv u hu h)
  refine ⟨I, hIind, hImax, ?_⟩
  -- uncounted vertices
  let U : Set (Fin n) := {v | (v ∈ I ∧ ¬ ∃ w, D v w) ∨ (v ∉ I ∧ ¬ ∃ w ∈ I, D v w)}
  have hUcol : ∀ v, v ∉ I → (¬ ∃ w ∈ I, D v w) → col v = 2 := by
    intro v hvI hno
    by_contra hne
    have hv : v ∈ ({v | col v = 0} ∪ {v | col v = 1} : Set (Fin n)) := by
      have : col v = 0 ∨ col v = 1 := by omega
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hvK : v ∉ K := fun h => hvI (hKI h)
    obtain ⟨k, hk, hvk⟩ := hKabs v hv hvK
    exact hno ⟨k, hKI hk, hvk⟩
  have hUind : G.IsIndepSet U := by
    intro u hu v hv _ hadj
    rcases hu with ⟨huI, hun⟩ | ⟨huI, hun⟩ <;> rcases hv with ⟨hvI, hvn⟩ | ⟨hvI, hvn⟩
    · exact hIind u huI v hvI hadj
    · rcases (hD u v).mp hadj with h | h
      · exact hun ⟨v, h⟩
      · exact hvn ⟨u, huI, h⟩
    · rcases (hD u v).mp hadj with h | h
      · exact hun ⟨v, hvI, h⟩
      · exact hvn ⟨u, h⟩
    · exact col.valid hadj ((hUcol u huI hun).trans (hUcol v hvI hvn).symm)
  have hUle : U.ncard ≤ G.indepNum := by
    rw [Set.ncard_eq_toFinset_card U (Set.toFinite U)]
    apply SimpleGraph.IsIndepSet.card_le_indepNum
    rw [Set.Finite.coe_toFinset]
    exact hUind
  have hcover : (Set.univ : Set (Fin n)) ⊆
      ({v : Fin n | v ∈ I ∧ ∃ w, D v w} ∪ {v : Fin n | v ∉ I ∧ ∃ w ∈ I, D v w}) ∪ U := by
    intro v _
    by_cases hvI : v ∈ I
    · by_cases hw : ∃ w, D v w
      · exact Or.inl (Or.inl ⟨hvI, hw⟩)
      · exact Or.inr (Or.inl ⟨hvI, hw⟩)
    · by_cases hw : ∃ w ∈ I, D v w
      · exact Or.inl (Or.inr ⟨hvI, hw⟩)
      · exact Or.inr (Or.inr ⟨hvI, hw⟩)
  have h1 := Set.ncard_le_ncard hcover (Set.toFinite _)
  have h2 := Set.ncard_union_le
    ({v : Fin n | v ∈ I ∧ ∃ w, D v w} ∪ {v : Fin n | v ∉ I ∧ ∃ w ∈ I, D v w}) U
  have h3 := Set.ncard_union_le {v : Fin n | v ∈ I ∧ ∃ w, D v w}
    {v : Fin n | v ∉ I ∧ ∃ w ∈ I, D v w}
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  omega
