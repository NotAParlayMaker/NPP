import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1566

def L0 (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def LS : Finset (Fin 13) := {4, 10, 12}

def MS : Finset (Fin 13) := {1, 5, 11}

def adj (t u : Fin 13) : Prop :=
  (t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ LS ∧ u ∈ MS) ∨ (t ∈ MS ∧ u ∈ LS)

lemma part1 : ∀ t u : Fin 13,
    (t ≠ u ∧
      (∃ p ∈ L0 t \ L0 u, ∃ v ∈ L0 u,
        (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L0 t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L0 0 else ∅))) v = true) ∧
      (∃ p ∈ L0 u \ L0 t, ∃ v ∈ L0 t,
        (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L0 u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L0 0 else ∅))) v = true)) ↔
    adj t u := by
  intro t u
  unfold adj
  revert t u
  decide

lemma ls_ms_disjoint : ∀ x : Fin 13, ¬ (x ∈ LS ∧ x ∈ MS) := by
  decide

lemma zero_not_ls : (0 : Fin 13) ∉ LS := by
  decide

lemma zero_not_ms : (0 : Fin 13) ∉ MS := by
  decide

lemma adj_nonzero {t u : Fin 13} (ht : t ≠ 0) (hu : u ≠ 0) (h : adj t u) :
    (t ∈ LS ∧ u ∈ MS) ∨ (t ∈ MS ∧ u ∈ LS) := by
  rcases h with ⟨_, h0 | h0⟩ | h | h
  · exact absurd h0 ht
  · exact absurd h0 hu
  · exact Or.inl h
  · exact Or.inr h

lemma clique_erase_zero_card_le_two {K : Finset (Fin 13)}
    (hK : ∀ t ∈ K, ∀ u ∈ K, t ≠ u → adj t u) : (K.erase 0).card ≤ 2 := by
  by_contra h
  have hlt : 2 < (K.erase 0).card := by omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hlt
  have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
  have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
  have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
  have haK : a ∈ K := (Finset.mem_erase.mp ha).2
  have hbK : b ∈ K := (Finset.mem_erase.mp hb).2
  have hcK : c ∈ K := (Finset.mem_erase.mp hc).2
  have h1 := adj_nonzero ha0 hb0 (hK a haK b hbK hab)
  have h2 := adj_nonzero ha0 hc0 (hK a haK c hcK hac)
  have h3 := adj_nonzero hb0 hc0 (hK b hbK c hcK hbc)
  rcases h1 with ⟨haL, hbM⟩ | ⟨haM, hbL⟩
  · rcases h2 with ⟨_, hcM⟩ | ⟨haM, _⟩
    · rcases h3 with ⟨hbL, _⟩ | ⟨_, hcL⟩
      · exact ls_ms_disjoint b ⟨hbL, hbM⟩
      · exact ls_ms_disjoint c ⟨hcL, hcM⟩
    · exact ls_ms_disjoint a ⟨haL, haM⟩
  · rcases h2 with ⟨haL, _⟩ | ⟨_, hcL⟩
    · exact ls_ms_disjoint a ⟨haL, haM⟩
    · rcases h3 with ⟨_, hcM⟩ | ⟨hbM, _⟩
      · exact ls_ms_disjoint c ⟨hcL, hcM⟩
      · exact ls_ms_disjoint b ⟨hbL, hbM⟩

lemma clique_card_ge_three {K : Finset (Fin 13)} (h3 : 3 ≤ K.card)
    (hK : ∀ t ∈ K, ∀ u ∈ K, t ≠ u → adj t u) :
    ∃ l ∈ LS, ∃ m ∈ MS, K = {0, l, m} := by
  have hle : (K.erase 0).card ≤ 2 := clique_erase_zero_card_le_two hK
  have h0 : (0 : Fin 13) ∈ K := by
    by_contra h0
    rw [Finset.erase_eq_of_notMem h0] at hle
    omega
  have hcard : (K.erase 0).card = 2 := by
    have h1 := Finset.card_erase_of_mem h0
    omega
  obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ K.erase 0 := by rw [heq]; simp
  have hb : b ∈ K.erase 0 := by rw [heq]; simp
  have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
  have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
  have haK : a ∈ K := (Finset.mem_erase.mp ha).2
  have hbK : b ∈ K := (Finset.mem_erase.mp hb).2
  have hKeq : K = insert 0 {a, b} := by
    rw [← heq, Finset.insert_erase h0]
  rcases adj_nonzero ha0 hb0 (hK a haK b hbK hab) with ⟨haL, hbM⟩ | ⟨haM, hbL⟩
  · exact ⟨a, haL, b, hbM, hKeq⟩
  · refine ⟨b, hbL, a, haM, ?_⟩
    rw [hKeq, Finset.pair_comm]

lemma triple_is_clique {l m : Fin 13} (hl : l ∈ LS) (hm : m ∈ MS) :
    ∀ t ∈ ({0, l, m} : Finset (Fin 13)), ∀ u ∈ ({0, l, m} : Finset (Fin 13)), t ≠ u → adj t u := by
  intro t ht u hu htu
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht hu
  rcases ht with rfl | rfl | rfl
  · exact Or.inl ⟨htu, Or.inl rfl⟩
  · rcases hu with rfl | rfl | rfl
    · exact Or.inl ⟨htu, Or.inr rfl⟩
    · exact absurd rfl htu
    · exact Or.inr (Or.inl ⟨hl, hm⟩)
  · rcases hu with rfl | rfl | rfl
    · exact Or.inl ⟨htu, Or.inr rfl⟩
    · exact Or.inr (Or.inr ⟨hm, hl⟩)
    · exact absurd rfl htu

lemma triple_card {l m : Fin 13} (hl : l ∈ LS) (hm : m ∈ MS) :
    ({0, l, m} : Finset (Fin 13)).card = 3 := by
  have h0l : (0 : Fin 13) ≠ l := fun h => zero_not_ls (h ▸ hl)
  have h0m : (0 : Fin 13) ≠ m := fun h => zero_not_ms (h ▸ hm)
  have hlm : l ≠ m := fun h => ls_ms_disjoint l ⟨hl, h ▸ hm⟩
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [hlm]
  · simp [h0l, h0m]

lemma part3 {K : Finset (Fin 13)} (h1 : 1 ≤ K.card)
    (hK : ∀ t ∈ K, ∀ u ∈ K, t ≠ u → adj t u) :
    K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
      (if ∃ l ∈ K, ∃ m ∈ K, l ∈ LS ∧ m ∈ MS then 1 else 0) := by
  by_cases hc1 : K.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
    have hno : ¬ ∃ l ∈ ({a} : Finset (Fin 13)), ∃ m ∈ ({a} : Finset (Fin 13)), l ∈ LS ∧ m ∈ MS := by
      rintro ⟨l, hl, m, hm, hlL, hmM⟩
      simp only [Finset.mem_singleton] at hl hm
      subst hl; subst hm
      exact ls_ms_disjoint _ ⟨hlL, hmM⟩
    simp only [Finset.card_singleton, Nat.sub_self, Nat.not_le.mpr (by decide : 1 < 2), and_false,
      ite_false, hno, add_zero]
  · by_cases hc2 : K.card = 2
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc2
      have hcard : ({a, b} : Finset (Fin 13)).card = 2 := Finset.card_pair hab
      by_cases h0 : (0 : Fin 13) ∈ ({a, b} : Finset (Fin 13))
      · have hno : ¬ ∃ l ∈ ({a, b} : Finset (Fin 13)), ∃ m ∈ ({a, b} : Finset (Fin 13)), l ∈ LS ∧ m ∈ MS := by
          rintro ⟨l, hl, m, hm, hlL, hmM⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at h0 hl hm
          have hl0 : l ≠ 0 := fun h => zero_not_ls (h ▸ hlL)
          have hm0 : m ≠ 0 := fun h => zero_not_ms (h ▸ hmM)
          rcases h0 with rfl | rfl
          · rcases hl with rfl | rfl
            · exact hl0 rfl
            · rcases hm with rfl | rfl
              · exact hm0 rfl
              · exact ls_ms_disjoint _ ⟨hlL, hmM⟩
          · rcases hl with rfl | rfl
            · rcases hm with rfl | rfl
              · exact ls_ms_disjoint _ ⟨hlL, hmM⟩
              · exact hm0 rfl
            · exact hl0 rfl
        simp only [hcard, h0, le_refl, and_self, ite_true, hno, ite_false, add_zero]
      · have ha0 : a ≠ 0 := fun h => h0 (by simp [h])
        have hb0 : b ≠ 0 := fun h => h0 (by simp [h])
        have hyes : ∃ l ∈ ({a, b} : Finset (Fin 13)), ∃ m ∈ ({a, b} : Finset (Fin 13)), l ∈ LS ∧ m ∈ MS := by
          rcases adj_nonzero ha0 hb0 (hK a (by simp) b (by simp) hab) with ⟨haL, hbM⟩ | ⟨haM, hbL⟩
          · exact ⟨a, by simp, b, by simp, haL, hbM⟩
          · exact ⟨b, by simp, a, by simp, hbL, haM⟩
        simp only [hcard, h0, false_and, ite_false, hyes, ite_true, zero_add]
    · have h3 : 3 ≤ K.card := by omega
      obtain ⟨l, hl, m, hm, rfl⟩ := clique_card_ge_three h3 hK
      have hcard : ({0, l, m} : Finset (Fin 13)).card = 3 := triple_card hl hm
      have h0 : (0 : Fin 13) ∈ ({0, l, m} : Finset (Fin 13)) := by simp
      have hyes : ∃ l' ∈ ({0, l, m} : Finset (Fin 13)), ∃ m' ∈ ({0, l, m} : Finset (Fin 13)), l' ∈ LS ∧ m' ∈ MS :=
        ⟨l, by simp, m, by simp, hl, hm⟩
      simp only [hcard, h0, show (2 : ℕ) ≤ 3 by decide, and_self, ite_true, hyes]

end PEqualNP.Outside.L_meta_1566

theorem PEqualNP.Outside.L_meta_1566 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ t u : Fin 13, (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true)) ↔
      (t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13)))) ∧
    (∀ K : Finset (Fin 13), 3 ≤ K.card → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) ↔
      ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m})) ∧
    (∀ K : Finset (Fin 13), 1 ≤ K.card → (∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) →
      K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
        (if ∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0)) := by
  intro L hL
  have hLeq : L = PEqualNP.Outside.L_meta_1566.L0 := funext hL
  subst hLeq
  refine ⟨PEqualNP.Outside.L_meta_1566.part1, ?_, ?_⟩
  · intro K h3
    constructor
    · intro hK
      exact PEqualNP.Outside.L_meta_1566.clique_card_ge_three h3
        (fun t ht u hu htu => (PEqualNP.Outside.L_meta_1566.part1 t u).mp (hK t ht u hu htu))
    · rintro ⟨l, hl, m, hm, rfl⟩ t ht u hu htu
      exact (PEqualNP.Outside.L_meta_1566.part1 t u).mpr
        (PEqualNP.Outside.L_meta_1566.triple_is_clique hl hm t ht u hu htu)
  · intro K h1 hK
    exact PEqualNP.Outside.L_meta_1566.part3 h1
      (fun t ht u hu htu => (PEqualNP.Outside.L_meta_1566.part1 t u).mp (hK t ht u hu htu))
