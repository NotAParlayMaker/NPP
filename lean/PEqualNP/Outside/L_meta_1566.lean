import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1566

def R (t u : Fin 13) : Bool :=
  decide ((t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))

theorem tri : ∀ t u w : Fin 13, R t u = true → R u w = true → R t w = true → t = 0 ∨ u = 0 ∨ w = 0 := by
  decide +kernel

theorem nz : ∀ u w : Fin 13, u ≠ 0 → w ≠ 0 → R u w = true →
    (u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ w ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (w ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) := by
  decide +kernel

theorem back : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ t ∈ ({0, l, m} : Finset (Fin 13)), ∀ u ∈ ({0, l, m} : Finset (Fin 13)), t ≠ u → R t u = true := by
  decide +kernel

theorem c3 : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)),
    ({0, l, m} : Finset (Fin 13)).card - 1 = (if (0 : Fin 13) ∈ ({0, l, m} : Finset (Fin 13)) ∧ 2 ≤ ({0, l, m} : Finset (Fin 13)).card then 1 else 0) +
        (if ∃ x ∈ ({0, l, m} : Finset (Fin 13)), ∃ y ∈ ({0, l, m} : Finset (Fin 13)), x ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0) := by
  decide +kernel

theorem c2 : ∀ a b : Fin 13, a ≠ b → R a b = true →
    ({a, b} : Finset (Fin 13)).card - 1 = (if (0 : Fin 13) ∈ ({a, b} : Finset (Fin 13)) ∧ 2 ≤ ({a, b} : Finset (Fin 13)).card then 1 else 0) +
        (if ∃ x ∈ ({a, b} : Finset (Fin 13)), ∃ y ∈ ({a, b} : Finset (Fin 13)), x ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0) := by
  decide +kernel

theorem c1 : ∀ a : Fin 13,
    ({a} : Finset (Fin 13)).card - 1 = (if (0 : Fin 13) ∈ ({a} : Finset (Fin 13)) ∧ 2 ≤ ({a} : Finset (Fin 13)).card then 1 else 0) +
        (if ∃ x ∈ ({a} : Finset (Fin 13)), ∃ y ∈ ({a} : Finset (Fin 13)), x ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0) := by
  decide +kernel

theorem clique (K : Finset (Fin 13)) (h3 : 3 ≤ K.card)
    (hK : ∀ t ∈ K, ∀ u ∈ K, t ≠ u → R t u = true) :
    ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m} := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
  have h0 : (0 : Fin 13) ∈ K := by
    rcases tri a b c (hK a ha b hb hab) (hK b hb c hc hbc) (hK a ha c hc hac) with h | h | h
    · exact h ▸ ha
    · exact h ▸ hb
    · exact h ▸ hc
  have hcard : (K.erase 0).card = 2 := by
    have h1 : (K.erase 0).card = K.card - 1 := Finset.card_erase_of_mem h0
    by_contra hne
    have h2 : 2 < (K.erase 0).card := by omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h2
    have ha' := Finset.mem_erase.mp ha
    have hb' := Finset.mem_erase.mp hb
    have hc' := Finset.mem_erase.mp hc
    rcases tri a b c (hK a ha'.2 b hb'.2 hab) (hK b hb'.2 c hc'.2 hbc) (hK a ha'.2 c hc'.2 hac) with h | h | h
    · exact ha'.1 h
    · exact hb'.1 h
    · exact hc'.1 h
  obtain ⟨u, w, huw, he⟩ := Finset.card_eq_two.mp hcard
  have hu : u ∈ K.erase 0 := by rw [he]; simp
  have hw : w ∈ K.erase 0 := by rw [he]; simp
  have hu' := Finset.mem_erase.mp hu
  have hw' := Finset.mem_erase.mp hw
  have hKe : K = insert 0 {u, w} := by rw [← he, Finset.insert_erase h0]
  rcases nz u w hu'.1 hw'.1 (hK u hu'.2 w hw'.2 huw) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨u, h1, w, h2, hKe⟩
  · exact ⟨w, h1, u, h2, by rw [hKe, Finset.pair_comm]⟩

theorem core (M : Fin 13 → Fin 13 → Prop) (h : ∀ t u, M t u ↔ R t u = true) :
    (∀ K : Finset (Fin 13), 3 ≤ K.card → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → M t u) ↔
      ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m})) ∧
    (∀ K : Finset (Fin 13), 1 ≤ K.card → (∀ t ∈ K, ∀ u ∈ K, t ≠ u → M t u) →
      K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
        (if ∃ x ∈ K, ∃ y ∈ K, x ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ y ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0)) := by
  simp only [h]
  refine ⟨fun K h3 => ⟨clique K h3, ?_⟩, fun K h1 hK => ?_⟩
  · rintro ⟨l, hl, m, hm, rfl⟩
    exact back l hl m hm
  · by_cases h1' : K.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1'
      exact c1 a
    by_cases h2 : K.card = 2
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
      exact c2 a b hab (hK a (by simp) b (by simp) hab)
    obtain ⟨l, hl, m, hm, rfl⟩ := clique K (by omega) hK
    exact c3 l hl m hm

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
  obtain rfl : L = fun t => {t, t + 1, t + 3, t + 9} := funext hL
  have aux : ∀ {A B : Prop}, A → (A → B) → A ∧ B := fun a f => ⟨a, f a⟩
  refine aux ?_ ?_
  · decide +kernel
  · intro h1
    exact PEqualNP.Outside.L_meta_1566.core _ (fun t u => (h1 t u).trans
      (by simp only [PEqualNP.Outside.L_meta_1566.R, decide_eq_true_eq]))
