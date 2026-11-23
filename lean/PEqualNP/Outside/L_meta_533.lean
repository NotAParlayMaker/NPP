import Mathlib
import PEqualNP.Defs

open Classical
open scoped BigOperators

-- Based on the CC0 proof at https://github.com/sneed-and-feed/lean-theorems-1/tree/main/Formalization/KonigMatching

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LMeta533

lemma fin2_cases (y : Fin 2) : y = 0 ∨ y = 1 := by revert y; decide

def EdgesShareEndpoint (e₁ e₂ : Sym2 V) : Prop :=
  ∃ v : V, v ∈ e₁ ∧ v ∈ e₂

def IsMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ¬ EdgesShareEndpoint e₁ e₂)

def IsVertexCover (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ u v : V, G.Adj u v → u ∈ C ∨ v ∈ C

omit [Fintype V] [DecidableEq V] in

lemma isMatching_empty (G : SimpleGraph V) : IsMatching G ∅ :=
  ⟨by simp, by simp⟩

omit [DecidableEq V] in

lemma isVertexCover_univ (G : SimpleGraph V) : IsVertexCover G Finset.univ :=
  fun _ _ _ => Or.inl (Finset.mem_univ _)

noncomputable def matchingNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ M : Finset (Sym2 V), IsMatching G M ∧ M.card = k }

noncomputable def vertexCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf { k : ℕ | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k }

def IsIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

omit [Fintype V] [DecidableEq V] in

lemma isIndependentSet_empty (G : SimpleGraph V) : IsIndependentSet G ∅ := by
  simp [IsIndependentSet]

noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset V, IsIndependentSet G S ∧ S.card = k }

lemma isIndependentSet_iff_isVertexCover_compl (G : SimpleGraph V) (S : Finset V) :
    IsIndependentSet G S ↔ IsVertexCover G (Finset.univ \ S) := by
  simp [IsIndependentSet, IsVertexCover, or_iff_not_and_not]
  exact ⟨fun h u v hadj hu hv => h u hu v hv hadj, fun h u hu v hv hadj => h u v hadj hu hv⟩

omit [Fintype V] in

lemma matching_card_le_vertexCover_card (G : SimpleGraph V) {M : Finset (Sym2 V)} {C : Finset V}
    (hM : IsMatching G M) (hC : IsVertexCover G C) :
    M.card ≤ C.card := by
  have : ∀ e ∈ M, ∃ v ∈ C, v ∈ e := fun e he => Sym2.inductionOn e (fun u v hadj =>
    (hC u v hadj).elim (⟨u, ·, Sym2.mem_mk_left u v⟩) (⟨v, ·, Sym2.mem_mk_right u v⟩)) (hM.1 e he)
  choose f hfC hfe using this
  have h_inj : ∀ (e₁ e₂ : M), f e₁.1 e₁.2 = f e₂.1 e₂.2 → e₁ = e₂ :=
    fun ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ heq => Subtype.ext <| by_contra fun hne =>
      hM.2 e₁ h₁ e₂ h₂ hne ⟨f e₁ h₁, hfe e₁ h₁, heq ▸ hfe e₂ h₂⟩
  rw [← Finset.card_attach (s := M), ← Finset.card_image_of_injective _ h_inj]
  exact Finset.card_le_card (Finset.image_subset_iff.mpr fun ⟨e, he⟩ _ => hfC e he)

lemma weak_duality (G : SimpleGraph V) :
    matchingNumber G ≤ vertexCoverNumber G := by
  refine le_csInf ⟨_, _, isVertexCover_univ G, rfl⟩ ?_
  rintro _ ⟨C, hC, rfl⟩
  refine csSup_le ⟨_, _, isMatching_empty G, rfl⟩ ?_
  rintro _ ⟨M, hM, rfl⟩
  exact matching_card_le_vertexCover_card G hM hC

end LMeta533

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LMeta533

lemma exists_max_defect (G : SimpleGraph V) (A : Finset V) :
    ∃ (S₀ : Finset V) (d : ℕ), S₀ ⊆ A ∧
      (S₀.biUnion (fun a => G.neighborFinset a)).card ≤ S₀.card ∧
      d = S₀.card - (S₀.biUnion (fun a => G.neighborFinset a)).card ∧
      ∀ S ⊆ A, S.card ≤ (S.biUnion (fun a => G.neighborFinset a)).card + d := by
  let f (S : Finset V) : ℕ := S.card - (S.biUnion (fun a => G.neighborFinset a)).card
  obtain ⟨S₁, hS₁, hmax⟩ := Finset.exists_max_image A.powerset f ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset A)⟩
  by_cases hd : f S₁ = 0
  · refine ⟨∅, 0, Finset.empty_subset A, by simp, by simp, fun S hS => ?_⟩
    have := hmax S (Finset.mem_powerset.mpr hS); dsimp [f] at hd this; omega
  · refine ⟨S₁, f S₁, Finset.mem_powerset.mp hS₁, by dsimp [f] at *; omega, rfl, fun S hS => ?_⟩
    have := hmax S (Finset.mem_powerset.mpr hS); dsimp [f] at *; omega

lemma bipartite_neighborFinset_subset (G : SimpleGraph V) (c : G.Coloring (Fin 2)) (S : Finset V)
    (hS : ∀ x ∈ S, c x = 0) :
    S.biUnion (fun a => G.neighborFinset a) ⊆ Finset.filter (fun v => c v = 1) Finset.univ := by
  rintro b hb
  obtain ⟨a, ha, hadj⟩ := Finset.mem_biUnion.mp hb
  have := c.valid ((G.mem_neighborFinset a b).mp hadj)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases fin2_cases (c b) with
  | inl h0 => cases this (by rw [hS a ha, h0])
  | inr h1 => exact h1

lemma isVertexCover_bipartite_defect (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (A S₀ : Finset V) (hA : A = Finset.filter (fun v => c v = 0) Finset.univ) (_hS₀ : S₀ ⊆ A) :
    IsVertexCover G ((A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a)) := by
  have h_cov (x y : V) (hxy : G.Adj x y) (hx0 : c x = 0) :
      x ∈ (A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a) ∨ y ∈ (A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a) := by
    by_cases hxS : x ∈ S₀
    · exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, hxS, (G.mem_neighborFinset x y).mpr hxy⟩))
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨by simp [hA, hx0], hxS⟩))
  intro u v hadj
  rcases fin2_cases (c u) with hu0 | hu1
  · exact h_cov u v hadj hu0
  · rcases fin2_cases (c v) with hv0 | hv1
    · exact (h_cov v u hadj.symm hv0).symm
    · exact (c.valid hadj (by rw [hu1, hv1])).elim

lemma bipartite_defect_cover_card (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (A S₀ : Finset V) (d : ℕ)
    (hA : A = Finset.filter (fun v => c v = 0) Finset.univ)
    (hS₀ : S₀ ⊆ A)
    (hd_eq : d = S₀.card - (S₀.biUnion (fun a => G.neighborFinset a)).card)
    (hS₀_le : (S₀.biUnion (fun a => G.neighborFinset a)).card ≤ S₀.card) :
    ((A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a)).card = A.card - d := by
  have h_disj : Disjoint (A \ S₀) (S₀.biUnion (fun a => G.neighborFinset a)) := by
    refine Disjoint.mono Finset.sdiff_subset (bipartite_neighborFinset_subset G c S₀ ?_) ?_
    · intro x hx
      have := hS₀ hx
      rw [hA, Finset.mem_filter] at this
      exact this.2
    · rw [hA, Finset.disjoint_left]
      intro x hxA hxB
      have := (Finset.mem_filter.mp hxA).2.symm.trans (Finset.mem_filter.mp hxB).2
      revert this; decide
  rw [Finset.card_union_of_disjoint h_disj, Finset.card_sdiff, Finset.inter_eq_left.mpr hS₀, hd_eq]
  have := Finset.card_le_card hS₀; omega

noncomputable def augmentedNeighbors (G : SimpleGraph V) (d : ℕ) (a : V) : Finset (V ⊕ Fin d) :=
  (G.neighborFinset a).image Sum.inl ∪ (Finset.univ : Finset (Fin d)).image Sum.inr

lemma augmentedNeighbors_biUnion (G : SimpleGraph V) (d : ℕ) {S : Finset V} (hS : S.Nonempty) :
    S.biUnion (augmentedNeighbors G d) =
      (S.biUnion (fun a => G.neighborFinset a)).image Sum.inl ∪ (Finset.univ : Finset (Fin d)).image Sum.inr := by
  ext (v | i) <;> simp [augmentedNeighbors, hS.exists_mem]

lemma card_augmentedNeighbors_biUnion (G : SimpleGraph V) (d : ℕ) {S : Finset V} (hS : S.Nonempty) :
    (S.biUnion (augmentedNeighbors G d)).card = (S.biUnion (fun a => G.neighborFinset a)).card + d := by
  rw [augmentedNeighbors_biUnion G d hS, Finset.card_union_of_disjoint (by simp [Finset.disjoint_left]),
      Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_image_of_injective _ Sum.inr_injective,
      Finset.card_fin]

lemma hall_condition_augmented (G : SimpleGraph V) (A : Finset V) (d : ℕ)
    (hd_max : ∀ S ⊆ A, S.card ≤ (S.biUnion (fun a => G.neighborFinset a)).card + d)
    (S' : Finset A) :
    S'.card ≤ (S'.biUnion (fun a => augmentedNeighbors G d a.val)).card := by
  by_cases hS' : S'.Nonempty
  · have h_sub : S'.image Subtype.val ⊆ A := Finset.image_subset_iff.mpr fun x _ => x.2
    have h_biUnion : (S'.image Subtype.val).biUnion (augmentedNeighbors G d) =
        S'.biUnion (fun a => augmentedNeighbors G d a.val) := by ext x; simp [augmentedNeighbors]
    rw [← Finset.card_image_of_injective S' Subtype.val_injective, ← h_biUnion,
        card_augmentedNeighbors_biUnion G d (hS'.image _)]
    exact hd_max _ h_sub
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS']; simp

lemma exists_matching_from_hall_inj (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (A : Finset V) (d : ℕ)
    (hA : A = Finset.filter (fun v => c v = 0) Finset.univ)
    (f : A → V ⊕ Fin d) (hf_inj : Function.Injective f)
    (hf_mem : ∀ a : A, f a ∈ augmentedNeighbors G d a.val) :
    ∃ M : Finset (Sym2 V), IsMatching G M ∧ A.card - d ≤ M.card := by
  let A_mat : Finset A := Finset.filter (fun a => ∃ v : V, f a = Sum.inl v) Finset.univ
  have h_compl_card : (Finset.univ \ A_mat : Finset A).card ≤ d := by
    have h_inr : ∀ a ∈ (Finset.univ \ A_mat : Finset A), ∃ i : Fin d, f a = Sum.inr i := by
      intro a ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter, not_exists, A_mat] at ha
      cases hfa : f a with
      | inl v => exact (ha v hfa).elim
      | inr i => exact ⟨i, rfl⟩
    choose finr hfinr using h_inr
    have h_inj' : ∀ (x y : { a : A // a ∈ Finset.univ \ A_mat }), finr x.1 x.2 = finr y.1 y.2 → x = y :=
      fun ⟨a₁, h₁⟩ ⟨a₂, h₂⟩ heq => Subtype.ext (hf_inj (by rw [hfinr a₁ h₁, hfinr a₂ h₂, heq]))
    have := Finset.card_le_card (Finset.subset_univ ((Finset.univ \ A_mat).attach.image (fun ⟨a, ha⟩ => finr a ha)))
    rw [Finset.card_image_of_injective _ (fun _ _ => h_inj' _ _), Finset.card_attach, Finset.card_fin] at this
    exact this
  have hA_mat_card : A.card - d ≤ A_mat.card := by
    have h_split := Finset.card_sdiff (s := A_mat) (t := Finset.univ)
    rw [Finset.inter_univ, Finset.card_univ, Fintype.card_coe] at h_split
    omega
  have hg_choice : ∀ a ∈ A_mat, ∃ v : V, f a = Sum.inl v ∧ G.Adj a.val v := by
    intro a ha
    obtain ⟨v, hv⟩ := (Finset.mem_filter.mp ha).2
    have hfa := hf_mem a
    simp only [augmentedNeighbors, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hfa
    rcases hfa with (⟨v', hv', heq⟩ | ⟨i, heq⟩)
    · exact ⟨v, hv, (G.mem_neighborFinset a.val v).mp (by cases Sum.inl.inj (hv.symm.trans heq.symm); exact hv')⟩
    · cases hv.symm.trans heq.symm
  choose g hg_f hg_adj using hg_choice
  let M : Finset (Sym2 V) := A_mat.attach.image (fun ⟨a, ha⟩ => s(a.val, g a ha))
  have ha_c : ∀ a : A, c a.val = 0 := fun a => by
    have ha := a.property
    have : a.val ∈ Finset.filter (fun v => c v = 0) Finset.univ := hA ▸ ha
    exact (Finset.mem_filter.mp this).2
  have hg_c : ∀ (a : A) (ha : a ∈ A_mat), c (g a ha) = 1 := fun a ha =>
    (fin2_cases (c (g a ha))).resolve_left fun h0 => c.valid (hg_adj a ha) (by rw [ha_c a, h0])
  have hM_card : M.card = A_mat.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · rintro ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ heq
      rcases Sym2.eq_iff.mp heq with (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact Subtype.ext (Subtype.ext h1)
      · exfalso; have := congrArg c h1; rw [ha_c a₁, hg_c a₂ ha₂] at this; revert this; decide
  refine ⟨M, ⟨?_, ?_⟩, by omega⟩
  · rintro e he
    obtain ⟨⟨a, ha⟩, -, rfl⟩ := Finset.mem_image.mp he
    exact hg_adj a ha
  · rintro e₁ he₁ e₂ he₂ hne ⟨w, hw₁, hw₂⟩
    obtain ⟨⟨a₁, ha₁⟩, -, rfl⟩ := Finset.mem_image.mp he₁
    obtain ⟨⟨a₂, ha₂⟩, -, rfl⟩ := Finset.mem_image.mp he₂
    rcases Sym2.mem_iff.mp hw₁ with (hw1 | hw1) <;> rcases Sym2.mem_iff.mp hw₂ with (hw2 | hw2)
    · have h_eq : a₁.val = a₂.val := hw1.symm.trans hw2
      have : a₁ = a₂ := Subtype.ext h_eq
      subst this; exact hne rfl
    · exfalso; have := congrArg c (hw1.symm.trans hw2 : a₁.val = g a₂ ha₂); rw [ha_c a₁, hg_c a₂ ha₂] at this; revert this; decide
    · exfalso; have := congrArg c (hw1.symm.trans hw2 : g a₁ ha₁ = a₂.val); rw [hg_c a₁ ha₁, ha_c a₂] at this; revert this; decide
    · have hg_eq : g a₁ ha₁ = g a₂ ha₂ := hw1.symm.trans hw2
      have hf_eq : f a₁ = f a₂ := by rw [hg_f a₁ ha₁, hg_f a₂ ha₂, hg_eq]
      have : a₁ = a₂ := hf_inj hf_eq
      subst this; exact hne rfl

end LMeta533

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LMeta533

lemma konig_duality_le (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    vertexCoverNumber G ≤ matchingNumber G := by
  obtain ⟨c⟩ := h_bip
  let A := Finset.filter (fun v => c v = 0) Finset.univ
  obtain ⟨S₀, d, hS₀_sub, hS₀_le, hd_eq, hd_max⟩ := exists_max_defect G A
  obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective _).mp
    (hall_condition_augmented G A d hd_max)
  obtain ⟨M, hM_match, hM_card⟩ := exists_matching_from_hall_inj G c A d rfl f hf_inj hf_mem
  have hC_cov := isVertexCover_bipartite_defect G c A S₀ rfl hS₀_sub
  have hC_card := bipartite_defect_cover_card G c A S₀ d rfl hS₀_sub hd_eq hS₀_le
  have h_tau_le : vertexCoverNumber G ≤ A.card - d :=
    hC_card ▸ csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨_, hC_cov, rfl⟩
  have h_le_nu : M.card ≤ matchingNumber G :=
    le_csSup ⟨Fintype.card (Sym2 V), by rintro _ ⟨M', -, rfl⟩; exact Finset.card_le_univ M'⟩ ⟨M, hM_match, rfl⟩
  omega

lemma konig_duality (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    matchingNumber G = vertexCoverNumber G :=
  le_antisymm (weak_duality G) (konig_duality_le G h_bip)

lemma gallai_independence_vertex_cover (G : SimpleGraph V) :
    independenceNumber G + vertexCoverNumber G = Fintype.card V := by
  have hSC_nonempty : { k : ℕ | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k }.Nonempty :=
    ⟨Fintype.card V, Finset.univ, isVertexCover_univ G, Finset.card_univ⟩
  obtain ⟨C, hC_cov, hC_card⟩ := Nat.sInf_mem hSC_nonempty
  have hS_ind : IsIndependentSet G (Finset.univ \ C) := by
    rw [isIndependentSet_iff_isVertexCover_compl, Finset.sdiff_sdiff_eq_self (Finset.subset_univ C)]; exact hC_cov
  have hS_card : (Finset.univ \ C).card = Fintype.card V - vertexCoverNumber G := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hC_card]
    rfl
  have h_le1 : Fintype.card V - vertexCoverNumber G ≤ independenceNumber G :=
    le_csSup ⟨Fintype.card V, by rintro _ ⟨S, -, rfl⟩; exact Finset.card_le_univ S⟩ ⟨_, hS_ind, hS_card⟩
  have h_ind_le : independenceNumber G ≤ Fintype.card V - vertexCoverNumber G := by
    refine csSup_le ⟨0, ∅, isIndependentSet_empty G, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    have h_tau : vertexCoverNumber G ≤ (Finset.univ \ S).card :=
      csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨_, (isIndependentSet_iff_isVertexCover_compl G S).mp hS, rfl⟩
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ] at h_tau
    have := Finset.card_le_univ S; omega
  have h_tau_le : vertexCoverNumber G ≤ Fintype.card V :=
    csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨Finset.univ, isVertexCover_univ G, Finset.card_univ⟩
  omega

lemma konig_independence_matching (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    independenceNumber G + matchingNumber G = Fintype.card V :=
  konig_duality G h_bip ▸ gallai_independence_vertex_cover G

end LMeta533

namespace PEqualNP.Outside

theorem L_meta_533 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) →
      ∃ (M : Finset (Sym2 (Fin n))) (T : Finset (Fin n)),
        (∀ e ∈ M, e ∈ G.edgeFinset) ∧
        (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v : Fin n, v ∈ e → v ∉ f) ∧
        (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        T.card = M.card := by
  intro n G _ ⟨c, hc⟩
  have hColor : G.Colorable 2 := by
    refine ⟨SimpleGraph.Coloring.mk (fun v => if c v then 1 else 0) ?_⟩
    intro u v hadj
    have hne := hc u v hadj
    cases hcu : c u <;> cases hcv : c v <;> simp_all
  let matchSizes : Set ℕ :=
    { k | ∃ M : Finset (Sym2 (Fin n)), LMeta533.IsMatching G M ∧ M.card = k }
  let coverSizes : Set ℕ :=
    { k | ∃ T : Finset (Fin n), LMeta533.IsVertexCover G T ∧ T.card = k }
  have hmNonempty : matchSizes.Nonempty :=
    ⟨0, ∅, LMeta533.isMatching_empty G, rfl⟩
  have hmBounded : BddAbove matchSizes := by
    refine ⟨Fintype.card (Sym2 (Fin n)), ?_⟩
    rintro k ⟨M, _, rfl⟩
    exact Finset.card_le_univ M
  have hcNonempty : coverSizes.Nonempty :=
    ⟨Fintype.card (Fin n), Finset.univ, LMeta533.isVertexCover_univ G, Finset.card_univ⟩
  obtain ⟨M, hM, hMcard⟩ := Nat.sSup_mem hmNonempty hmBounded
  obtain ⟨T, hT, hTcard⟩ := Nat.sInf_mem hcNonempty
  have heq : M.card = T.card := by
    have h := LMeta533.konig_duality G hColor
    change sSup matchSizes = sInf coverSizes at h
    rw [hMcard, hTcard]
    exact h
  refine ⟨M, T, ?_, ?_, hT, heq.symm⟩
  · intro e he
    exact (SimpleGraph.mem_edgeFinset).2 (hM.1 e he)
  · intro e he f hf hne v hve hvf
    exact hM.2 e he f hf hne ⟨v, hve, hvf⟩

end PEqualNP.Outside
