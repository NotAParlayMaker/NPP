import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9477

open PEqualNP.ProofComplexity PEqualNP.Search

private lemma cardLt (n : ℕ) (H : Finset (Fin n)) : H.card < n + 1 := by
  have h1 : H.card ≤ Fintype.card (Fin n) := Finset.card_le_univ H
  rw [Fintype.card_fin] at h1
  omega

private def clauseE (n : ℕ) (H : Finset (Fin n)) (h : Fin n) : Clause (Fin (n + 1) × Fin n) :=
  insert ((⟨H.card, cardLt n H⟩, h), false)
    ((Finset.univ.filter (fun p : Fin (n + 1) × Fin n => p.1.val < H.card ∧ p.2 ∉ H)).image
      (fun p => (p, true)))

private lemma upForces_mono_gamma {V : Type} {Γ₁ Γ₂ : Set (Clause V)} {A : Set (Literal V)}
    {l : Literal V} (hsub : Γ₁ ⊆ Γ₂) (h : UPForces Γ₁ A l) : UPForces Γ₂ A l := by
  induction h with
  | hyp ha => exact UPForces.hyp ha
  | unit hD hl _ ih => exact UPForces.unit (hsub hD) hl ih

private lemma isRUP_mono {V : Type} {Γ₁ Γ₂ : Set (Clause V)} {C : Clause V}
    (hsub : Γ₁ ⊆ Γ₂) (h : IsRUP Γ₁ C) : IsRUP Γ₂ C := by
  rcases h with ⟨D, hD, hf⟩
  exact ⟨D, hsub hD, fun l hl => upForces_mono_gamma hsub (hf l hl)⟩

private lemma isRUPRun_append_of_forall {V : Type} {F : Set (Clause V)} {L ρ : List (Clause V)}
    (hρ : IsRUPRun F ρ) (hL : ∀ C ∈ L, IsRUP (F ∪ {D | D ∈ ρ}) C) :
    IsRUPRun F (L ++ ρ) := by
  induction L with
  | nil => exact hρ
  | cons C L ih =>
    apply IsRUPRun.learn (ih (fun C' hC' => hL C' (List.mem_cons_of_mem C hC')))
    refine isRUP_mono ?_ (hL C List.mem_cons_self)
    intro D hD
    rcases hD with hF | hmem
    · exact Or.inl hF
    · exact Or.inr (List.mem_append_right L hmem)

private lemma force_pigeon {n : ℕ} {Γ : Set (Clause (Fin (n + 1) × Fin n))}
    {A : Set (Literal (Fin (n + 1) × Fin n))} (hPHP : PHP (n + 1) n ⊆ Γ)
    (i : Fin (n + 1)) (h0 : Fin n)
    (hother : ∀ j : Fin n, j ≠ h0 → UPForces Γ A ((i, j), false)) :
    UPForces Γ A ((i, h0), true) := by
  have hD : Finset.univ.image (fun j : Fin n => ((i, j), true)) ∈ Γ :=
    hPHP (Or.inl ⟨i, rfl⟩)
  refine UPForces.unit hD (Finset.mem_image.mpr ⟨h0, Finset.mem_univ h0, rfl⟩) ?_
  intro l' hl' hne
  rcases Finset.mem_image.mp hl' with ⟨j, _, rfl⟩
  have hjne : j ≠ h0 := by
    intro heq
    apply hne
    rw [heq]
  exact hother j hjne

private lemma force_hole {n : ℕ} {Γ : Set (Clause (Fin (n + 1) × Fin n))}
    {A : Set (Literal (Fin (n + 1) × Fin n))} (hPHP : PHP (n + 1) n ⊆ Γ)
    (i1 i2 : Fin (n + 1)) (hne : i1 ≠ i2) (j : Fin n)
    (htrue : UPForces Γ A ((i2, j), true)) :
    UPForces Γ A ((i1, j), false) := by
  have hD : ({((i1, j), false), ((i2, j), false)} : Clause (Fin (n + 1) × Fin n)) ∈ Γ :=
    hPHP (Or.inr ⟨i1, i2, j, hne, rfl⟩)
  refine UPForces.unit hD (by simp) ?_
  intro l' hl' hne'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
  rcases hl' with rfl | rfl
  · exact absurd rfl hne'
  · exact htrue

private lemma conflict_hole {n : ℕ} {Γ : Set (Clause (Fin (n + 1) × Fin n))}
    {A : Set (Literal (Fin (n + 1) × Fin n))} (hPHP : PHP (n + 1) n ⊆ Γ)
    (i1 i2 : Fin (n + 1)) (hne : i1 ≠ i2) (j : Fin n)
    (h1 : UPForces Γ A ((i1, j), true)) (h2 : UPForces Γ A ((i2, j), true)) :
    ∃ D ∈ Γ, ∀ l ∈ D, UPForces Γ A (negLit l) := by
  refine ⟨{((i1, j), false), ((i2, j), false)}, hPHP (Or.inr ⟨i1, i2, j, hne, rfl⟩), ?_⟩
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · exact h1
  · exact h2

private lemma conflict_of_forced {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∀ (H : Finset (Fin n)), H.card = k →
    ∀ (Γ : Set (Clause (Fin (n + 1) × Fin n))),
      PHP (n + 1) n ⊆ Γ →
      (∀ (H' : Finset (Fin n)) (h' : Fin n),
        2 ≤ H'.card → H'.card ≤ k → h' ∈ H' → (∃ h0 ∈ H', h0 < h') → clauseE n H' h' ∈ Γ) →
      ∀ (A : Set (Literal (Fin (n + 1) × Fin n))),
        (∀ (i : Fin (n + 1)) (j : Fin n), i.val ≤ k → j ∉ H → UPForces Γ A ((i, j), false)) →
        ∃ D ∈ Γ, ∀ l ∈ D, UPForces Γ A (negLit l) := by
  induction k with
  | zero => omega
  | succ k' ih =>
    intro H hcard Γ hPHP hE A hF
    by_cases hk0 : k' = 0
    · subst hk0
      rcases Finset.card_eq_one.mp hcard with ⟨h0, rfl⟩
      let i0 : Fin (n + 1) := ⟨0, by omega⟩
      let i1 : Fin (n + 1) := ⟨1, by omega⟩
      have hne : i0 ≠ i1 := by
        intro heq
        have := congrArg Fin.val heq
        simp [i0, i1] at this
      have hf0 : UPForces Γ A ((i0, h0), true) :=
        force_pigeon hPHP i0 h0 fun j hj => hF i0 j (by simp [i0]) (by simp [hj])
      have hf1 : UPForces Γ A ((i1, h0), true) :=
        force_pigeon hPHP i1 h0 fun j hj => hF i1 j (by simp [i1]) (by simp [hj])
      exact conflict_hole hPHP i0 i1 hne h0 hf0 hf1
    · have hk'1 : 1 ≤ k' := by omega
      have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
      let h0 : Fin n := H.min' hHne
      have hh0_mem : h0 ∈ H := Finset.min'_mem H hHne
      let ik : Fin (n + 1) := ⟨H.card, cardLt n H⟩
      have hforce_other : ∀ h ∈ H, h ≠ h0 → UPForces Γ A ((ik, h), false) := by
        intro h hh hne
        have hlt : h0 < h := lt_of_le_of_ne (Finset.min'_le H h hh) (Ne.symm hne)
        have hcl : clauseE n H h ∈ Γ := hE H h (by omega) (by omega) hh ⟨h0, hh0_mem, hlt⟩
        refine UPForces.unit hcl (Finset.mem_insert_self _ _) ?_
        intro l' hl' hne'
        rcases Finset.mem_insert.mp hl' with rfl | hmem
        · exact absurd rfl hne'
        · rcases Finset.mem_image.mp hmem with ⟨p, hp, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          exact hF p.1 p.2 (by omega) hp.2
      have hforce_h0 : UPForces Γ A ((ik, h0), true) := by
        refine force_pigeon hPHP ik h0 ?_
        intro j hjne
        by_cases hjH : j ∈ H
        · exact hforce_other j hjH hjne
        · exact hF ik j (by simp [ik, hcard]) hjH
      have hforce_col : ∀ i : Fin (n + 1), i.val ≤ k' → UPForces Γ A ((i, h0), false) := by
        intro i hi
        have hine : i ≠ ik := by
          intro heq
          have := congrArg Fin.val heq
          simp [ik] at this
          omega
        exact force_hole hPHP i ik hine h0 hforce_h0
      have hcard' : (H.erase h0).card = k' := by
        rw [Finset.card_erase_of_mem hh0_mem, hcard]
        omega
      refine ih hk'1 (by omega) (H.erase h0) hcard' Γ hPHP ?_ A ?_
      · intro H' h' h2 hle hh' hex
        exact hE H' h' h2 (by omega) hh' hex
      · intro i j hi hj
        by_cases hj0 : j = h0
        · subst hj0
          exact hforce_col i hi
        · have hjH : j ∉ H := fun hmem => hj (Finset.mem_erase.mpr ⟨hj0, hmem⟩)
          exact hF i j (by omega) hjH

private lemma isRUP_clauseE {n : ℕ} (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (H : Finset (Fin n)) (hcard : H.card = k) (h : Fin n) (hh : h ∈ H)
    (Γ : Set (Clause (Fin (n + 1) × Fin n)))
    (hPHP : PHP (n + 1) n ⊆ Γ)
    (hE : ∀ (H' : Finset (Fin n)) (h' : Fin n),
      2 ≤ H'.card → H'.card ≤ k - 1 → h' ∈ H' → (∃ h0 ∈ H', h0 < h') → clauseE n H' h' ∈ Γ) :
    IsRUP Γ (clauseE n H h) := by
  let A : Set (Literal (Fin (n + 1) × Fin n)) := negLit '' (↑(clauseE n H h) : Set _)
  let ik : Fin (n + 1) := ⟨H.card, cardLt n H⟩
  have hkh_true : UPForces Γ A ((ik, h), true) := by
    apply UPForces.hyp
    exact ⟨((ik, h), false), Finset.mem_insert_self _ _, rfl⟩
  have hcard' : (H.erase h).card = k - 1 := by
    rw [Finset.card_erase_of_mem hh, hcard]
  refine conflict_of_forced (k - 1) (by omega) (by omega) (H.erase h) hcard' Γ hPHP hE A ?_
  intro i j hi hj
  by_cases hjh : j = h
  · subst hjh
    have hine : i ≠ ik := by
      intro heq
      have := congrArg Fin.val heq
      simp [ik] at this
      omega
    exact force_hole hPHP i ik hine j hkh_true
  · have hjH : j ∉ H := fun hmem => hj (Finset.mem_erase.mpr ⟨hjh, hmem⟩)
    apply UPForces.hyp
    refine ⟨((i, j), true), ?_, rfl⟩
    refine Finset.mem_insert_of_mem ?_
    refine Finset.mem_image.mpr ⟨(i, j), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, hjH⟩

private def pairsAt (n k : ℕ) : Finset (Finset (Fin n) × Fin n) :=
  (Finset.univ : Finset (Finset (Fin n) × Fin n)).filter
    (fun p => p.1.card = k ∧ p.2 ∈ p.1 ∧ ∃ h0 ∈ p.1, h0 < p.2)

private noncomputable def layer (n k : ℕ) : List (Clause (Fin (n + 1) × Fin n)) :=
  (pairsAt n k).toList.map (fun p => clauseE n p.1 p.2)

private lemma mem_layer_iff {n k : ℕ} {C : Clause (Fin (n + 1) × Fin n)} :
    C ∈ layer n k ↔
      ∃ H : Finset (Fin n), ∃ h : Fin n,
        H.card = k ∧ h ∈ H ∧ (∃ h0 ∈ H, h0 < h) ∧ clauseE n H h = C := by
  simp only [layer, List.mem_map, Finset.mem_toList, pairsAt, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.exists, and_assoc]

private lemma card_pairsAt_le (n k : ℕ) (hk : 1 ≤ k) :
    (pairsAt n k).card ≤ Nat.choose n k * (k - 1) := by
  let S : Finset (Finset (Fin n)) := Finset.powersetCard k (Finset.univ : Finset (Fin n))
  let f : Finset (Fin n) → Finset (Finset (Fin n) × Fin n) :=
    fun H => (H.filter (fun h => ∃ h0 ∈ H, h0 < h)).image (fun h => (H, h))
  have hsub : pairsAt n k ⊆ S.biUnion f := by
    intro p hp
    simp only [pairsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine Finset.mem_biUnion.mpr ⟨p.1, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hp.1⟩
    · refine Finset.mem_image.mpr ⟨p.2, ?_, by simp⟩
      exact Finset.mem_filter.mpr ⟨hp.2.1, hp.2.2⟩
  have h1 : (pairsAt n k).card ≤ ∑ H ∈ S, (f H).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have h2 : ∀ H ∈ S, (f H).card ≤ k - 1 := by
    intro H hH
    have hcard : H.card = k := (Finset.mem_powersetCard.mp hH).2
    have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
    let h0 := H.min' hHne
    have hh0 : h0 ∈ H := Finset.min'_mem H hHne
    have hsubH : H.filter (fun h => ∃ x ∈ H, x < h) ⊆ H.erase h0 := by
      intro h hh
      rcases Finset.mem_filter.mp hh with ⟨hhH, ⟨x, hxH, hxh⟩⟩
      refine Finset.mem_erase.mpr ⟨?_, hhH⟩
      intro heq
      subst heq
      exact not_lt_of_ge (Finset.min'_le H x hxH) hxh
    calc (f H).card
        ≤ (H.filter (fun h => ∃ x ∈ H, x < h)).card := Finset.card_image_le
      _ ≤ (H.erase h0).card := Finset.card_le_card hsubH
      _ = k - 1 := by rw [Finset.card_erase_of_mem hh0, hcard]
  have h3 : ∑ H ∈ S, (f H).card ≤ ∑ _H ∈ S, (k - 1) := Finset.sum_le_sum h2
  rw [Finset.sum_const, smul_eq_mul] at h3
  have hScard : S.card = Nat.choose n k := by
    simp [S, Finset.card_powersetCard]
  rw [hScard] at h3
  exact le_trans h1 h3

private lemma layer_length_le (n k : ℕ) (hk : 1 ≤ k) :
    (layer n k).length ≤ Nat.choose n k * (k - 1) := by
  simp only [layer, List.length_map, Finset.length_toList]
  exact card_pairsAt_le n k hk

private noncomputable def run5 : List (Clause (Fin (5 + 1) × Fin 5)) :=
  (∅ : Clause (Fin (5 + 1) × Fin 5)) ::
    (layer 5 5 ++ layer 5 4 ++ layer 5 3 ++ layer 5 2)

private lemma run5_spec :
    IsRUPRun (PHP (5 + 1) 5) run5 ∧
      (∅ : Clause (Fin (5 + 1) × Fin 5)) ∈ run5 ∧ run5.length ≤ 64 := by
  have h2 : IsRUPRun (PHP (5 + 1) 5) (layer 5 2) := by
    have h := isRUPRun_append_of_forall (F := PHP (5 + 1) 5) (L := layer 5 2) (ρ := [])
      IsRUPRun.nil ?_
    · simpa using h
    · intro C hC
      rcases mem_layer_iff.mp hC with ⟨H, h, hcard, hh, _, rfl⟩
      refine isRUP_clauseE 2 (by omega) (by omega) H hcard h hh _ Set.subset_union_left ?_
      intro H' _ h2' hle'
      omega
  have h3 : IsRUPRun (PHP (5 + 1) 5) (layer 5 3 ++ layer 5 2) := by
    refine isRUPRun_append_of_forall h2 ?_
    intro C hC
    rcases mem_layer_iff.mp hC with ⟨H, h, hcard, hh, _, rfl⟩
    refine isRUP_clauseE 3 (by omega) (by omega) H hcard h hh _ Set.subset_union_left ?_
    intro H' h' h2' hle' hh' hex'
    exact Or.inr (mem_layer_iff.mpr ⟨H', h', by omega, hh', hex', rfl⟩)
  have h4 : IsRUPRun (PHP (5 + 1) 5) (layer 5 4 ++ (layer 5 3 ++ layer 5 2)) := by
    refine isRUPRun_append_of_forall h3 ?_
    intro C hC
    rcases mem_layer_iff.mp hC with ⟨H, h, hcard, hh, _, rfl⟩
    refine isRUP_clauseE 4 (by omega) (by omega) H hcard h hh _ Set.subset_union_left ?_
    intro H' h' h2' hle' hh' hex'
    refine Or.inr ?_
    by_cases hc : H'.card = 3
    · exact List.mem_append_left _ (mem_layer_iff.mpr ⟨H', h', hc, hh', hex', rfl⟩)
    · exact List.mem_append_right _ (mem_layer_iff.mpr ⟨H', h', by omega, hh', hex', rfl⟩)
  have h5 : IsRUPRun (PHP (5 + 1) 5)
      (layer 5 5 ++ (layer 5 4 ++ (layer 5 3 ++ layer 5 2))) := by
    refine isRUPRun_append_of_forall h4 ?_
    intro C hC
    rcases mem_layer_iff.mp hC with ⟨H, h, hcard, hh, _, rfl⟩
    refine isRUP_clauseE 5 (by omega) (by omega) H hcard h hh _ Set.subset_union_left ?_
    intro H' h' h2' hle' hh' hex'
    refine Or.inr ?_
    by_cases hc4 : H'.card = 4
    · exact List.mem_append_left _ (mem_layer_iff.mpr ⟨H', h', hc4, hh', hex', rfl⟩)
    · refine List.mem_append_right _ ?_
      by_cases hc3 : H'.card = 3
      · exact List.mem_append_left _ (mem_layer_iff.mpr ⟨H', h', hc3, hh', hex', rfl⟩)
      · exact List.mem_append_right _ (mem_layer_iff.mpr ⟨H', h', by omega, hh', hex', rfl⟩)
  have h5' : IsRUPRun (PHP (5 + 1) 5) (layer 5 5 ++ layer 5 4 ++ layer 5 3 ++ layer 5 2) := by
    simpa [List.append_assoc] using h5
  have hempty : IsRUP (PHP (5 + 1) 5 ∪ {D | D ∈ layer 5 5 ++ layer 5 4 ++ layer 5 3 ++ layer 5 2})
      (∅ : Clause (Fin (5 + 1) × Fin 5)) := by
    refine conflict_of_forced 5 (by omega) (by omega) (Finset.univ : Finset (Fin 5))
      (by simp) _ Set.subset_union_left ?_ _ ?_
    · intro H' h' h2' hle' hh' hex'
      refine Or.inr ?_
      simp only [Set.mem_ofPred_eq, List.mem_append]
      by_cases hc5 : H'.card = 5
      · exact Or.inl (Or.inl (Or.inl (mem_layer_iff.mpr ⟨H', h', hc5, hh', hex', rfl⟩)))
      · by_cases hc4 : H'.card = 4
        · exact Or.inl (Or.inl (Or.inr (mem_layer_iff.mpr ⟨H', h', hc4, hh', hex', rfl⟩)))
        · by_cases hc3 : H'.card = 3
          · exact Or.inl (Or.inr (mem_layer_iff.mpr ⟨H', h', hc3, hh', hex', rfl⟩))
          · exact Or.inr (mem_layer_iff.mpr ⟨H', h', by omega, hh', hex', rfl⟩)
    · intro _ j _ hj
      exact absurd (Finset.mem_univ j) hj
  have hrun : IsRUPRun (PHP (5 + 1) 5) run5 := IsRUPRun.learn h5' hempty
  have hmem : (∅ : Clause (Fin (5 + 1) × Fin 5)) ∈ run5 := List.mem_cons_self
  have hlen : run5.length ≤ 64 := by
    have l2 := layer_length_le 5 2 (by omega)
    have l3 := layer_length_le 5 3 (by omega)
    have l4 := layer_length_le 5 4 (by omega)
    have l5 := layer_length_le 5 5 (by omega)
    have c2 : Nat.choose 5 2 = 10 := by decide
    have c3 : Nat.choose 5 3 = 10 := by decide
    have c4 : Nat.choose 5 4 = 5 := by decide
    have c5 : Nat.choose 5 5 = 1 := by decide
    simp only [run5, List.length_cons, List.length_append]
    omega
  exact ⟨hrun, hmem, hlen⟩

end PEqualNP.Outside.L_meta_9477

theorem PEqualNP.Outside.L_meta_9477 : ∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (5 + 1) × Fin 5)), PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (5 + 1) 5) ρ ∧ (∅ : PEqualNP.ProofComplexity.Clause (Fin (5 + 1) × Fin 5)) ∈ ρ ∧ ρ.length ≤ 64 :=
  ⟨PEqualNP.Outside.L_meta_9477.run5, PEqualNP.Outside.L_meta_9477.run5_spec⟩
