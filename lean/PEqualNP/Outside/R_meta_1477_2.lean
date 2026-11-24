import Mathlib
import PEqualNP.Defs

-- Eliminate AND gates nested below AND gates, then bound circuits without nesting for any
-- bipartite graph without four-cycles. Point p is on line w iff (w - p) mod 21 lies in the
-- difference set {0, 5, 7, 17, 20}; the plane has 105 incidences and cover number 21.
theorem PEqualNP.Outside.R_meta_1477_2
    (shrink : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 124 → (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ p w : Fin 21, (w.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) ∧ x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 w) = true)) → (∃ i j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone 42 C i j) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size < C.size ∧ (∀ x : Fin 42 → Bool, (D.eval (List.ofFn x) = true ↔ ∃ p w : Fin 21, (w.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) ∧ x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 w) = true)))
    (flat : ∀ (R : Fin 21 → Fin 21 → Prop) [DecidableRel R], (∀ p q : Fin 21, p ≠ q → Fintype.card {w : Fin 21 // R p w ∧ R q w} ≤ 1) → ∀ t : ℕ, (∀ S : Finset (Fin 42), (∀ p w : Fin 21, R p w → Fin.castAdd 21 p ∈ S ∨ Fin.natAdd 21 w ∈ S) → t ≤ S.card) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ p w : Fin 21, R p w ∧ x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 w) = true)) → ¬ (∃ i j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone 42 C i j) → Fintype.card {pw : Fin 21 × Fin 21 // R pw.1 pw.2} + t ≤ C.size + 1) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  intro hC
  obtain ⟨C₀, hmon₀, hsize₀, hcorr₀⟩ := hC
  have fwd : ∀ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) → ∃ p w : Fin 21, Fin.castAdd 21 p = u ∧ Fin.natAdd 21 w = v ∧ (w.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) := by
    decide +kernel
  have bwd : ∀ p w : Fin 21, (w.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) → (p.val, 21 + w.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) := by
    decide +kernel
  have conv : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ p w : Fin 21, (w.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) ∧ x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 w) = true)) := by
    intro C h x
    rw [h x]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨p, w, rfl, rfl, hq⟩ := fwd u v huv
      exact ⟨p, w, hq, hu, hv⟩
    · rintro ⟨p, w, hq, hu, hv⟩
      exact ⟨Fin.castAdd 21 p, Fin.natAdd 21 w, bwd p w hq, hu, hv⟩
  have hdiag : ∀ i : Fin 21, (i.val + 21 - i.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) := by
    decide +kernel
  have tau : ∀ S : Finset (Fin 42), (∀ p w : Fin 21, (w.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) → Fin.castAdd 21 p ∈ S ∨ Fin.natAdd 21 w ∈ S) → 21 ≤ S.card := by
    intro S hS
    let g : Fin 21 → Fin 42 := fun i => if Fin.castAdd 21 i ∈ S then Fin.castAdd 21 i else Fin.natAdd 21 i
    have hg : ∀ i ∈ (Finset.univ : Finset (Fin 21)), g i ∈ S := by
      intro i _
      show (if Fin.castAdd 21 i ∈ S then Fin.castAdd 21 i else Fin.natAdd 21 i) ∈ S
      split_ifs with h
      · exact h
      · exact (hS i i (hdiag i)).resolve_left h
    have hinj : Set.InjOn g (Finset.univ : Finset (Fin 21)) := by
      intro i _ j _ hij
      simp only [g] at hij
      split_ifs at hij <;> (apply Fin.ext; have h2 := congrArg Fin.val hij; simp at h2; omega)
    have h3 := Finset.card_le_card_of_injOn g hg hinj
    simpa using h3
  have c4f : ∀ p q : Fin 21, p ≠ q → (Finset.univ.filter (fun w : Fin 21 => (w.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) ∧ (w.val + 21 - q.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ))).card ≤ 1 := by
    decide +kernel
  have c4 : ∀ p q : Fin 21, p ≠ q → Fintype.card {w : Fin 21 // (w.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) ∧ (w.val + 21 - q.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)} ≤ 1 := by
    intro p q hpq
    rw [Fintype.card_subtype]
    exact c4f p q hpq
  have ecard : Fintype.card {pw : Fin 21 × Fin 21 // (pw.2.val + 21 - pw.1.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)} = 105 := by
    rw [Fintype.card_subtype]
    decide +kernel
  have lower : ∀ m : ℕ, ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C.size = m → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ p w : Fin 21, (w.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) ∧ x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 w) = true)) → 125 ≤ C.size := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro C hm hmon hcorr
      by_cases hn : (∃ i j : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone 42 C i j)
      · by_contra hb
        have hsz : C.size ≤ 124 := by omega
        obtain ⟨D, hDmon, hDsize, hDcorr⟩ := shrink C hmon hsz hcorr hn
        have := ih D.size (by omega) D rfl hDmon hDcorr
        omega
      · have hf := flat (fun p w : Fin 21 => (w.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)) c4 21 tau C hmon hcorr hn
        rw [ecard] at hf
        omega
  have := lower C₀.size C₀ rfl hmon₀ (conv C₀ hcorr₀)
  omega
