import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection
open PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_3469_421 :
    (∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      2 ≤ n → (∀ l, 2 ≤ (S l).card) → RightOnIncidentPairs S C →
      C.output < n + n + C.size → PEqualNP.TopForm.IsAO2 (n + n) C →
      ∃ F : Finset ℕ, (∀ j ∈ F, j < C.size ∧ (gateAt C j).op = .or) ∧
        ∀ x : List Bool, x.length = n + n →
          (C.eval x = true ↔ ∀ j ∈ F, (C.wires x).getD (n + n + j) false = true)) →
    (∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (F : Finset ℕ),
      200 ≤ q → n = q ^ 2 + q + 1 → (∀ l, (S l).card = q + 1) →
      (∀ a b, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l) → PEqualNP.TopForm.IsAO2 (n + n) C →
      n + n ≤ C.output → C.output < n + n + C.size →
      (∃ g : Gate, C.gates[C.output - (n + n)]? = some g ∧ g.op = .and) →
      (∀ j ∈ F, j < C.size ∧ (gateAt C j).op = .or) →
      (∀ x : List Bool, x.length = n + n →
        (C.eval x = true ↔ ∀ j ∈ F, (C.wires x).getD (n + n + j) false = true)) →
      (∀ l p, p ∈ S l → ∀ j ∈ F,
        (C.wires (incidenceInput {p} {l})).getD (n + n + j) false = true) →
      (∀ (X Y : Finset (Fin n)), Y.card ≤ q → IsFalseInput S X Y → ∃ j ∈ F,
        (C.wires (incidenceInput X Y)).getD (n + n + j) false = false) →
      n * q ≤ 100 * C.size) →
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro hfront hbound q n S C hq hn hsize hpair hao hlo hhi hand hok hreject
  obtain ⟨F, hgates, hrows⟩ := hfront n S C (by omega)
    (fun l => by rw [hsize]; omega) hok hhi hao
  apply hbound q n S C F hq hn hsize hpair hao hlo hhi hand hgates hrows
  · intro l p hp
    exact (hrows (incidenceInput {p} {l}) (by simp [incidenceInput])).mp (hok l p hp)
  · intro X Y hy hfalse
    by_contra hnone
    push Not at hnone
    have hall : ∀ j ∈ F, (C.wires (incidenceInput X Y)).getD (n + n + j) false = true := by
      intro j hj
      simpa using hnone j hj
    have htrue := (hrows (incidenceInput X Y) (by simp [incidenceInput])).mpr hall
    rw [hreject X Y hy hfalse] at htrue
    contradiction
