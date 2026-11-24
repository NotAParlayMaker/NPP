import PEqualNP.Defs

-- A wire separates a rectangle of accepting and rejecting tests. At either kind of
-- binary gate its operand rectangles together cover the gate rectangle.
-- The counting child has no circuit semantics: it deals only with binary rectangle covers.
theorem PEqualNP.Outside.R_meta_2984_154
    (trace : ∀ (A B : Type) (m : ℕ) (P : A → List Bool) (M : B → List Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a, (P a).length = m) → (∀ b, (M b).length = m) → PEqualNP.TopForm.IsAO2 m C →
      ∃ R : ℕ → Set A × Set B, (∀ i < m, R i = ({a | (P a).getD i false = true}, {b | (M b).getD i false = false})) ∧
      (∀ j < C.size, ∃ K : Finset ℕ, K.card ≤ 2 ∧ (∀ k ∈ K, k < m + j) ∧
        ∀ a ∈ (R (m + j)).1, ∀ b ∈ (R (m + j)).2, ∃ k ∈ K, a ∈ (R k).1 ∧ b ∈ (R k).2) ∧
      ∀ a b, C.eval (P a) = true → C.eval (M b) = false → a ∈ (R C.output).1 ∧ b ∈ (R C.output).2)
    (count : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (s o : ℕ),
      200 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      let m := n+n
      let P := fun e : Fin n × Fin n => PEqualNP.GenericRejection.incidenceInput {e.1} {e.2}
      let M := fun Y : Finset (Fin n) => PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet S Y) Y
      ∀ R : ℕ → Set (Fin n × Fin n) × Set (Finset (Fin n)),
      (∀ i < m, R i = ({a | (P a).getD i false = true}, {b | (M b).getD i false = false})) →
      (∀ j < s, ∃ K : Finset ℕ, K.card ≤ 2 ∧ (∀ k ∈ K, k < m + j) ∧
        ∀ a ∈ (R (m + j)).1, ∀ b ∈ (R (m + j)).2, ∃ k ∈ K, a ∈ (R k).1 ∧ b ∈ (R k).2) →
      o < m + s → (∀ p l, p ∈ S l → (p,l) ∈ (R o).1) →
      (∀ Y : Finset (Fin n), Y.card ≤ q → Y ∈ (R o).2) → n*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq hn hcard hunique hao hout hpos hneg
  let P := fun e : Fin n × Fin n => PEqualNP.GenericRejection.incidenceInput {e.1} {e.2}
  let M := fun Y : Finset (Fin n) => PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet S Y) Y
  have len (X Y : Finset (Fin n)) : (PEqualNP.GenericRejection.incidenceInput X Y).length = n+n := by
    change (List.ofFn _ ++ List.ofFn _).length = _
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
  obtain ⟨R, hleaf, hcover, hroot⟩ := trace _ _ (n+n) P M C
    (fun _ => len _ _) (fun _ => len _ _) hao
  have reject (Y : Finset (Fin n)) (hy : Y.card ≤ q) : C.eval (M Y) = false := by
    apply hneg _ _ hy
    intro l hl
    rw [Finset.disjoint_left]
    intro p hp hz
    have hmiss : ∀ k ∈ Y, p ∉ S k := (Finset.mem_filter.mp hz).2
    exact hmiss l hl hp
  let k₀ : Fin n := ⟨0, by omega⟩
  have hline : 0 < (S k₀).card := by rw [hcard]; omega
  obtain ⟨p₀, hp⟩ := Finset.card_pos.mp hline
  apply count q n S C.size C.output hq hn hcard hunique R hleaf hcover hout
  · intro p k hk
    exact (hroot (p,k) ∅ (hpos k p hk) (reject ∅ (by simp))).1
  · intro Y hy
    exact (hroot (p₀,k₀) Y (hpos _ _ hp) (reject Y hy)).2
