import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The list gives one representative per simultaneous cyclic-shift orbit.
-- Bits 0 through 12 mark points, and bits 13 through 25 mark lines.
-- The first four representatives are incident pairs. The rest are generic maximal false inputs.

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_1682_620
    (normalize : ∀ (I : Type) (n : ℕ) (X : I → Fin n → Bool) (Y : Set I) (C : Circuit),
      Monotone2 C → (∀ i, circuitFun n C (X i) = true ↔ i ∈ Y) →
      let available (L : List (Set I)) (j : ℕ) :=
        [∅, Set.univ] ++ (List.ofFn fun k : Fin n => {i : I | X i k = true}) ++ L.take j
      let legal (L : List (Set I)) : Prop := ∀ j : Fin L.length,
        let prev := available L j.val
        (∃ a ∈ prev, ∃ b ∈ prev, L.get j = a ∪ b ∨ L.get j = a ∩ b) ∧
        ∀ u ∈ prev, ¬ (L.get j ∩ Y ⊆ u ∧ u ⊆ L.get j ∪ Y)
      ∃ L : List (Set I), L.length ≤ C.size ∧ legal L ∧ Y ∈ available L L.length)
    (positive :
      let X (i : Fin 520) (k : Fin 26) : Bool :=
        Nat.testBit ([8193, 8194, 8200, 8704, 61888, 92576, 162112, 177472, 192832, 208132, 308368, 339076, 408580, 470020, 555296, 570640, 601376, 616736, 670976, 686336, 701696, 732416, 801808, 832528, 932864, 1079392, 1194052, 1210432, 1325076, 1456132, 1603616, 1849360, 2172068, 2241604, 2274368, 2405504, 2434180, 2503684, 3289156, 4532356].getD (i.val / 13) 0) (13 * (k.val / 13) + (k.val + 13 - i.val % 13) % 13)
      let inc (p w : Fin 13) : Prop := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
      ∀ i : Fin 520, i.val < 52 → ∃ p w : Fin 13, inc p w ∧ X i =
        fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w))
    (negative :
      let X (i : Fin 520) (k : Fin 26) : Bool :=
        Nat.testBit ([8193, 8194, 8200, 8704, 61888, 92576, 162112, 177472, 192832, 208132, 308368, 339076, 408580, 470020, 555296, 570640, 601376, 616736, 670976, 686336, 701696, 732416, 801808, 832528, 932864, 1079392, 1194052, 1210432, 1325076, 1456132, 1603616, 1849360, 2172068, 2241604, 2274368, 2405504, 2434180, 2503684, 3289156, 4532356].getD (i.val / 13) 0) (13 * (k.val / 13) + (k.val + 13 - i.val % 13) % 13)
      let inc (p w : Fin 13) : Prop := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
      let off (P : Finset (Fin 13)) (w : Fin 13) : Prop := ∀ p ∈ P, ¬ inc p w
      ∀ i : Fin 520, 52 ≤ i.val → ∃ P : Finset (Fin 13),
        (∀ v : Fin 13, v ∉ P → ∃ w, off P w ∧ inc v w) ∧
        (¬ ∃ w : Fin 13, ∀ p ∈ P, inc p w) ∧ (¬ ∃ v : Fin 13, ∀ w, off P w → inc v w) ∧
        X i = fun k => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨ (∃ w, k = Fin.natAdd 13 w ∧ off P w)))
    (obstruction :
      let X (i : Fin 520) (k : Fin 26) : Bool :=
        Nat.testBit ([8193, 8194, 8200, 8704, 61888, 92576, 162112, 177472, 192832, 208132, 308368, 339076, 408580, 470020, 555296, 570640, 601376, 616736, 670976, 686336, 701696, 732416, 801808, 832528, 932864, 1079392, 1194052, 1210432, 1325076, 1456132, 1603616, 1849360, 2172068, 2241604, 2274368, 2405504, 2434180, 2503684, 3289156, 4532356].getD (i.val / 13) 0) (13 * (k.val / 13) + (k.val + 13 - i.val % 13) % 13)
      let Y : Set (Fin 520) := {i | i.val < 52}
      let available (L : List (Set (Fin 520))) (j : ℕ) :=
        [∅, Set.univ] ++ (List.ofFn fun k : Fin 26 => {i : (Fin 520) | X i k = true}) ++ L.take j
      let legal (L : List (Set (Fin 520))) : Prop := ∀ j : Fin L.length,
        let prev := available L j.val
        (∃ a ∈ prev, ∃ b ∈ prev, L.get j = a ∪ b ∨ L.get j = a ∩ b) ∧
        ∀ u ∈ prev, ¬ (L.get j ∩ Y ⊆ u ∧ u ⊆ L.get j ∪ Y)
      ¬ ∃ L : List (Set (Fin 520)), L.length ≤ 63 ∧ legal L ∧ Y ∈ available L L.length) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  rintro ⟨C, hmono, hsize, hp, hn⟩
  have incidence (p w : Fin 13) :
      (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d) ↔
      (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) := by simp
  simp_rw [incidence] at hp hn
  let X (i : Fin 520) (k : Fin 26) : Bool :=
    Nat.testBit ([8193, 8194, 8200, 8704, 61888, 92576, 162112, 177472, 192832, 208132, 308368, 339076, 408580, 470020, 555296, 570640, 601376, 616736, 670976, 686336, 701696, 732416, 801808, 832528, 932864, 1079392, 1194052, 1210432, 1325076, 1456132, 1603616, 1849360, 2172068, 2241604, 2274368, 2405504, 2434180, 2503684, 3289156, 4532356].getD (i.val / 13) 0) (13 * (k.val / 13) + (k.val + 13 - i.val % 13) % 13)
  let Y : Set (Fin 520) := {i | i.val < 52}
  have separates : ∀ i : Fin 520, circuitFun 26 C (X i) = true ↔ i ∈ Y := by
    intro i
    change circuitFun 26 C (X i) = true ↔ i.val < 52
    by_cases h : i.val < 52
    · obtain ⟨p, w, he, hx⟩ := positive i h
      change X i = _ at hx
      rw [hx]
      exact ⟨fun _ => h, fun _ => hp p w he⟩
    · obtain ⟨P, hc, h1, h2, hx⟩ := negative i (by omega)
      change X i = _ at hx
      rw [hx, hn P hc ⟨h1, h2⟩]
      simp [h]
  obtain ⟨L, hlen, hlegal, houtput⟩ := normalize (Fin 520) 26 X Y C hmono separates
  exact obstruction ⟨L, hlen.trans hsize, hlegal, houtput⟩
