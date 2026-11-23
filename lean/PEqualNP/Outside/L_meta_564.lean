import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta564

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private def step {n : ℕ} (C : AndCountCircuit n) (S : Finset (Fin C.size)) : Finset (Fin C.size) :=
  S ∪ S.biUnion (fun k => C.leftGates k ∪ C.rightGates k)

private def reach {n : ℕ} (C : AndCountCircuit n) : ℕ → Finset (Fin C.size)
  | 0 => C.outGates
  | m + 1 => step C (reach C m)

private lemma subset_step {n : ℕ} (C : AndCountCircuit n) (S : Finset (Fin C.size)) :
    S ⊆ step C S := Finset.subset_union_left

private lemma reach_mono {n : ℕ} (C : AndCountCircuit n) {a b : ℕ} (h : a ≤ b) :
    reach C a ⊆ reach C b := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (subset_step C _)

private lemma reach_stable {n : ℕ} (C : AndCountCircuit n) {m : ℕ}
    (h : reach C (m + 1) = reach C m) :
    ∀ t : ℕ, reach C (m + t) = reach C m := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    change step C (reach C (m + t)) = reach C m
    rw [ih]
    exact h

private lemma reach_fixpoint {n : ℕ} (C : AndCountCircuit n) :
    step C (reach C C.size) = reach C C.size := by
  by_cases hex : ∃ m ≤ C.size, reach C (m + 1) = reach C m
  · obtain ⟨m, hm, heq⟩ := hex
    have h1 : reach C (m + (C.size - m)) = reach C m := reach_stable C heq (C.size - m)
    have h2 : reach C (m + (C.size - m + 1)) = reach C m := reach_stable C heq (C.size - m + 1)
    have ha : m + (C.size - m) = C.size := by omega
    have hb : m + (C.size - m + 1) = C.size + 1 := by omega
    rw [ha] at h1
    rw [hb] at h2
    change reach C (C.size + 1) = reach C C.size
    rw [h1, h2]
  · exfalso
    push Not at hex
    have hcard : ∀ m ≤ C.size + 1, m ≤ (reach C m).card := by
      intro m
      induction m with
      | zero => intro _; omega
      | succ m ih =>
        intro hm
        have hlt : reach C m ⊂ reach C (m + 1) :=
          Finset.ssubset_iff_subset_ne.mpr ⟨subset_step C _, (hex m (by omega)).symm⟩
        have hclt : (reach C m).card < (reach C (m + 1)).card := Finset.card_lt_card hlt
        have ihm := ih (by omega)
        omega
    have hbig := hcard (C.size + 1) (le_refl _)
    have hle : (reach C (C.size + 1)).card ≤ (Finset.univ : Finset (Fin C.size)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at hle
    omega

private lemma reach_closed {n : ℕ} (C : AndCountCircuit n) {k : Fin C.size}
    (hk : k ∈ reach C C.size) :
    C.leftGates k ⊆ reach C C.size ∧ C.rightGates k ⊆ reach C C.size := by
  have hfix := reach_fixpoint C
  constructor
  · intro j hj
    rw [← hfix]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_union_left _ hj⟩)
  · intro j hj
    rw [← hfix]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_union_right _ hj⟩)

private lemma reach_used {n : ℕ} (C : AndCountCircuit n) :
    ∀ (m : ℕ) (i : Fin C.size), i ∈ reach C m →
      i ∈ C.outGates ∨ ∃ k ∈ reach C m, i ∈ C.leftGates k ∨ i ∈ C.rightGates k := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact Or.inl hi
  | succ m ih =>
    intro i hi
    change i ∈ reach C m ∪ (reach C m).biUnion (fun k => C.leftGates k ∪ C.rightGates k) at hi
    rw [Finset.mem_union] at hi
    rcases hi with him | hbi
    · rcases ih i him with ho | ⟨k, hk, hlr⟩
      · exact Or.inl ho
      · exact Or.inr ⟨k, subset_step C _ hk, hlr⟩
    · rw [Finset.mem_biUnion] at hbi
      obtain ⟨k, hk, hlr⟩ := hbi
      rw [Finset.mem_union] at hlr
      exact Or.inr ⟨k, subset_step C _ hk, hlr⟩

private def restrictCircuit {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size)) :
    AndCountCircuit n where
  size := K.card
  leftVars i := C.leftVars (K.orderEmbOfFin rfl i)
  leftGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i))
  rightVars i := C.rightVars (K.orderEmbOfFin rfl i)
  rightGates i := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i))
  outVars := C.outVars
  outGates := Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates)

private lemma restrict_mem_leftGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).leftGates i ↔
      K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.leftGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_rightGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (i j : Fin K.card) :
    j ∈ (restrictCircuit C K).rightGates i ↔
      K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i) := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.rightGates (K.orderEmbOfFin rfl i)) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_mem_outGates {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (j : Fin K.card) :
    j ∈ (restrictCircuit C K).outGates ↔ K.orderEmbOfFin rfl j ∈ C.outGates := by
  change j ∈ Finset.univ.filter (fun j => K.orderEmbOfFin rfl j ∈ C.outGates) ↔ _
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

private lemma restrict_wf {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (hWF : C.WellFormed) : (restrictCircuit C K).WellFormed := by
  intro i
  constructor
  · intro j hj
    have hj' := (restrict_mem_leftGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).1 _ hj')
  · intro j hj
    have hj' := (restrict_mem_rightGates C K i j).mp hj
    exact (K.orderEmbOfFin rfl).lt_iff_lt.mp ((hWF (K.orderEmbOfFin rfl i)).2 _ hj')

private lemma restrict_gateVal_eq {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (hclosed : ∀ k ∈ K, C.leftGates k ⊆ K ∧ C.rightGates k ⊆ K)
    (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin K.card), i.val < m →
      (restrictCircuit C K).gateVal U i = C.gateVal U (K.orderEmbOfFin rfl i) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    have hiK : K.orderEmbOfFin rfl i ∈ K := Finset.orderEmbOfFin_mem K rfl i
    rw [gateVal_unfold (restrictCircuit C K) U i, gateVal_unfold C U (K.orderEmbOfFin rfl i)]
    congr 1
    · unfold sideTrue
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjF' := (restrict_mem_leftGates C K i j).mp hjF
          refine Or.inr ⟨K.orderEmbOfFin rfl j, hjF', (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, ?_⟩
          rwa [← ih j (by omega)]
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjK : j ∈ K := (hclosed _ hiK).1 hjF
          have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]
            exact hjK
          obtain ⟨j', hj'⟩ := hjr
          have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
          refine Or.inr ⟨j', (restrict_mem_leftGates C K i j').mpr (by rw [hj']; exact hjF),
            hj'lt, ?_⟩
          rw [ih j' (by omega), hj']
          exact hjv
    · unfold sideTrue
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjF' := (restrict_mem_rightGates C K i j).mp hjF
          refine Or.inr ⟨K.orderEmbOfFin rfl j, hjF', (K.orderEmbOfFin rfl).lt_iff_lt.mpr hji, ?_⟩
          rwa [← ih j (by omega)]
      · rintro (hv | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl hv
        · have hjK : j ∈ K := (hclosed _ hiK).2 hjF
          have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]
            exact hjK
          obtain ⟨j', hj'⟩ := hjr
          have hj'lt : j' < i := (K.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hj']; exact hji)
          refine Or.inr ⟨j', (restrict_mem_rightGates C K i j').mpr (by rw [hj']; exact hjF),
            hj'lt, ?_⟩
          rw [ih j' (by omega), hj']
          exact hjv

private lemma restrict_eval_eq {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin C.size))
    (hout : C.outGates ⊆ K)
    (hclosed : ∀ k ∈ K, C.leftGates k ⊆ K ∧ C.rightGates k ⊆ K)
    (U : Finset (Fin n)) :
    (restrictCircuit C K).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjO, hjv⟩)
    · exact Or.inl hv
    · have hjO' := (restrict_mem_outGates C K j).mp hjO
      refine Or.inr ⟨K.orderEmbOfFin rfl j, hjO', ?_⟩
      rwa [← restrict_gateVal_eq C K hclosed U _ j j.isLt]
  · rintro (hv | ⟨j, hjO, hjv⟩)
    · exact Or.inl hv
    · have hjK : j ∈ K := hout hjO
      have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hjK
      obtain ⟨j', hj'⟩ := hjr
      refine Or.inr ⟨j', (restrict_mem_outGates C K j').mpr (by rw [hj']; exact hjO), ?_⟩
      rw [restrict_gateVal_eq C K hclosed U _ j' j'.isLt, hj']
      exact hjv

end PEqualNP.Outside.LMeta564

theorem PEqualNP.Outside.L_meta_564 : ∀ (n : ℕ) (C : PEqualNP.AndCount.AndCountCircuit n),
    C.WellFormed →
      ∃ C' : PEqualNP.AndCount.AndCountCircuit n,
        C'.WellFormed ∧ C'.size ≤ C.size ∧ (∀ U : Finset (Fin n), C'.eval U = C.eval U) ∧
        (∀ i : Fin C'.size, i ∈ C'.outGates ∨
          ∃ k : Fin C'.size, i ∈ C'.leftGates k ∨ i ∈ C'.rightGates k) ∧
        ((∀ i : Fin C.size, ((C.leftVars i).Nonempty ∨ (C.leftGates i).Nonempty) ∧
            ((C.rightVars i).Nonempty ∨ (C.rightGates i).Nonempty)) →
          ∀ i : Fin C'.size, ((C'.leftVars i).Nonempty ∨ (C'.leftGates i).Nonempty) ∧
            ((C'.rightVars i).Nonempty ∨ (C'.rightGates i).Nonempty)) ∧
        ((∀ (i : Fin C.size) (v : Fin n), C.gateVal {v} i = false) →
          ∀ (i : Fin C'.size) (v : Fin n), C'.gateVal {v} i = false) := by
  intro n C hWF
  let K : Finset (Fin C.size) := PEqualNP.Outside.LMeta564.reach C C.size
  have hout : C.outGates ⊆ K := PEqualNP.Outside.LMeta564.reach_mono C (Nat.zero_le _)
  have hclosed : ∀ k ∈ K, C.leftGates k ⊆ K ∧ C.rightGates k ⊆ K :=
    fun _ hk => PEqualNP.Outside.LMeta564.reach_closed C hk
  refine ⟨PEqualNP.Outside.LMeta564.restrictCircuit C K,
    PEqualNP.Outside.LMeta564.restrict_wf C K hWF, ?_, ?_, ?_, ?_, ?_⟩
  · change K.card ≤ C.size
    have hle : K.card ≤ (Finset.univ : Finset (Fin C.size)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rwa [Finset.card_univ, Fintype.card_fin] at hle
  · intro U
    exact PEqualNP.Outside.LMeta564.restrict_eval_eq C K hout hclosed U
  · intro i
    have hiK : K.orderEmbOfFin rfl i ∈ K := Finset.orderEmbOfFin_mem K rfl i
    rcases PEqualNP.Outside.LMeta564.reach_used C C.size _ hiK with ho | ⟨k0, hk0, hlr⟩
    · exact Or.inl ((PEqualNP.Outside.LMeta564.restrict_mem_outGates C K i).mpr ho)
    · have hkr : k0 ∈ Set.range (K.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hk0
      obtain ⟨k, hk⟩ := hkr
      refine Or.inr ⟨k, ?_⟩
      rcases hlr with hL | hR
      · exact Or.inl ((PEqualNP.Outside.LMeta564.restrict_mem_leftGates C K k i).mpr (by rw [hk]; exact hL))
      · exact Or.inr ((PEqualNP.Outside.LMeta564.restrict_mem_rightGates C K k i).mpr (by rw [hk]; exact hR))
  · intro hne i
    have hiK : K.orderEmbOfFin rfl i ∈ K := Finset.orderEmbOfFin_mem K rfl i
    obtain ⟨hL, hR⟩ := hne (K.orderEmbOfFin rfl i)
    constructor
    · rcases hL with hLv | ⟨j, hj⟩
      · exact Or.inl hLv
      · have hjK : j ∈ K := (hclosed _ hiK).1 hj
        have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hjK
        obtain ⟨j', hj'⟩ := hjr
        exact Or.inr ⟨j', (PEqualNP.Outside.LMeta564.restrict_mem_leftGates C K i j').mpr (by rw [hj']; exact hj)⟩
    · rcases hR with hRv | ⟨j, hj⟩
      · exact Or.inl hRv
      · have hjK : j ∈ K := (hclosed _ hiK).2 hj
        have hjr : j ∈ Set.range (K.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hjK
        obtain ⟨j', hj'⟩ := hjr
        exact Or.inr ⟨j', (PEqualNP.Outside.LMeta564.restrict_mem_rightGates C K i j').mpr (by rw [hj']; exact hj)⟩
  · intro hsing i v
    rw [PEqualNP.Outside.LMeta564.restrict_gateVal_eq C K hclosed {v} _ i i.isLt]
    exact hsing (K.orderEmbOfFin rfl i) v
