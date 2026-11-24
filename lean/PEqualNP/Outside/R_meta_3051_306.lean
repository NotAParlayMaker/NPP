import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3051_306
    (h1 : ∀ (X Y : Type) (n : Nat) (A : X → Fin n → Bool) (B : Y → Fin n → Bool)
      (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      (∀ a, PEqualNP.MetaComplexity.circuitFun n C (A a) = true) →
      (∀ b, PEqualNP.MetaComplexity.circuitFun n C (B b) = false) →
      ∃ r : List (Set X × Set Y), r.length ≤ C.size ∧
      let old := fun (k : Nat) (z : Set X × Set Y) =>
        z.1 = ∅ ∨ z.2 = ∅ ∨ (∃ i, z = ({a | A a i = true}, {b | B b i = false})) ∨ z ∈ r.take k
      old r.length (Set.univ,Set.univ) ∧ ∀ i : Fin r.length,
        ∃ u v, old i.val u ∧ old i.val v ∧
          ((r[i].1 ⊆ u.1 ∪ v.1 ∧ r[i].2 ⊆ u.2 ∩ v.2) ∨
           (r[i].1 ⊆ u.1 ∩ v.1 ∧ r[i].2 ⊆ u.2 ∪ v.2)))
    (h2 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      300 ≤ q → N = q^2 + q + 1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p t, p ≠ t → ∃! l, I p l ∧ I t l) →
      let X := {a : Fin N × Fin N // I a.1 a.2}
      let Y := {b : Finset (Fin N) // b.card ≤ q}
      let A := fun (a : X) (j : Fin (N+N)) => decide (j = Fin.castAdd N a.val.1 ∨ j = Fin.natAdd N a.val.2)
      let B := fun (b : Y) => Fin.addCases (motive := fun _ : Fin (N+N) => Bool)
        (fun p => decide (∀ l ∈ b.val, ¬I p l)) (fun l => decide (l ∈ b.val))
      ∀ r : List (Set X × Set Y), (let old := fun (k : Nat) (z : Set X × Set Y) =>
        z.1 = ∅ ∨ z.2 = ∅ ∨ (∃ i, z = ({a | A a i = true}, {b | B b i = false})) ∨ z ∈ r.take k
      old r.length (Set.univ,Set.univ) ∧ ∀ i : Fin r.length,
        ∃ u v, old i.val u ∧ old i.val v ∧
          ((r[i].1 ⊆ u.1 ∪ v.1 ∧ r[i].2 ⊆ u.2 ∩ v.2) ∨
           (r[i].1 ⊆ u.1 ∩ v.1 ∧ r[i].2 ⊆ u.2 ∪ v.2))) → N*q ≤ 100*r.length) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I _ C hq hn hc hj hm hp hneg
  let X := {a : Fin N × Fin N // I a.1 a.2}
  let Y := {b : Finset (Fin N) // b.card ≤ q}
  let A := fun (a : X) (j : Fin (N+N)) => decide (j = Fin.castAdd N a.val.1 ∨ j = Fin.natAdd N a.val.2)
  let B := fun (b : Y) => Fin.addCases (motive := fun _ : Fin (N+N) => Bool)
    (fun p => decide (∀ l ∈ b.val, ¬I p l)) (fun l => decide (l ∈ b.val))
  have neg (b : Y) : PEqualNP.MetaComplexity.circuitFun (N+N) C (B b) = false := by
    have lines (l) : B b (Fin.natAdd N l) = true ↔ l ∈ b.val := by
      simp only [B, Fin.addCases_right, decide_eq_true_eq]
    apply hneg
    · rw [Fintype.card_subtype]
      have mask : Finset.univ.filter (fun l : Fin N => B b (Fin.natAdd N l) = true) = b.val := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, lines]
      rw [mask]
      exact b.property
    · rintro ⟨p,l,hit,pon,lon⟩
      have pno : ∀ k ∈ b.val, ¬I p k := by
        simpa only [B, Fin.addCases_left, decide_eq_true_eq] using pon
      exact pno l ((lines l).mp lon) hit
  obtain ⟨r,hr,valid⟩ := h1 X Y (N+N) A B C hm (fun a => hp _ _ a.property) neg
  exact (h2 q N I hq hn hc hj r valid).trans (Nat.mul_le_mul_left 100 hr)
