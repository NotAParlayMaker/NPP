import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_2382_527
    (trace : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
        (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        ∀ u v : Fin 11, s(u,v) ∈ Ustar G C →
          ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
            gateVal 11 C a (pairInput u v) = true ∧
            OrReaches 11 C (opnd C a b) h ∧ gateVal 11 C h (pairInput u v) = true)
    (nested : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
        (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        ∀ j k : ℕ, j ≠ k → junk G C = {j, k} → InCone 11 C j k →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        (∀ u v : Fin 11, s(u,v) ∈ U →
          ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
            gateVal 11 C a (pairInput u v) = true ∧
            OrReaches 11 C (opnd C a b) h ∧ gateVal 11 C h (pairInput u v) = true) →
        B < U.card → False)
    (independent : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
        (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        ∀ j k : ℕ, j ≠ k → junk G C = {j, k} →
        ¬ InCone 11 C j k → ¬ InCone 11 C k j →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        (∀ u v : Fin 11, s(u,v) ∈ U →
          ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
            gateVal 11 C a (pairInput u v) = true ∧
            OrReaches 11 C (opnd C a b) h ∧ gateVal 11 C h (pairInput u v) = true) →
        B < U.card → False)
    (many : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
        (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 3 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        (∀ u v : Fin 11, s(u,v) ∈ U →
          ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
            gateVal 11 C a (pairInput u v) = true ∧
            OrReaches 11 C (opnd C a b) h ∧ gateVal 11 C h (pairInput u v) = true) →
        B < U.card → False) :
let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) → x8 < (2 : ℕ) * x7.card → x7.card ≤ x8 := by
  intro G C hsize hleast htop hcard U B _ _
  have routes := trace C hleast htop
  by_contra! deficit
  change 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card <
    (Ustar G C).card at deficit
  by_cases two : (junk G C).card = 2
  · obtain ⟨j, k, hjk, hpair⟩ := Finset.card_eq_two.mp two
    by_cases forward : InCone 11 C j k
    · exact nested C hsize hleast htop j k hjk hpair forward routes deficit
    by_cases backward : InCone 11 C k j
    · have swapped : junk G C = {k, j} := by
        rw [hpair]
        ext i
        simp [or_comm]
      exact nested C hsize hleast htop k j hjk.symm swapped backward routes deficit
    exact independent C hsize hleast htop j k hjk hpair forward backward routes deficit
  · have three : 3 ≤ (junk G C).card := by omega
    exact many C hsize hleast htop three routes deficit
