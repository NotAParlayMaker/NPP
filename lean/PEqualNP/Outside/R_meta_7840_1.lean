import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7840_1
    (H1 : ∀ (G : SimpleGraph (Fin 42)), G = SimpleGraph.fromRel (fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) → (∀ a b c e : Fin 42, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) ∧ ∃ E : Finset (Fin 42 × Fin 42), E.card = 21 ∧ (∀ p ∈ E, G.Adj p.1 p.2) ∧ ∀ p ∈ E, ∀ q ∈ E, p ≠ q → Disjoint ({p.1, p.2} : Finset (Fin 42)) {q.1, q.2})
    (H2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨ b = e) → ∀ (C : PEqualNP.AndCount.AndCountCircuit n), C.WellFormed → C.Computes G → (∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i)) → (∃ i : Fin C.size, ∃ a ∈ C.leftVars i, ∃ b ∈ C.rightVars i, ¬ G.Adj a b) → ∀ (E : Finset (Fin n × Fin n)), (∀ p ∈ E, G.Adj p.1 p.2) → (∀ p ∈ E, ∀ q ∈ E, p ≠ q → Disjoint ({p.1, p.2} : Finset (Fin n)) {q.1, q.2}) → E.card ≤ C.size) : have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → (∃ (x8 : Fin x2.size), ∃ x9 ∈ x2.leftVars x8, ∃ x10 ∈ x2.rightVars x8, ¬x1.Adj x9 x10) → (21 : ℕ) ≤ x2.size := by
  intro x1 C hwf hcomp _hout _hsingle hdisj hbad
  obtain ⟨hc4, E, hEcard, hEedge, hEdisj⟩ := H1 x1 rfl
  have hle := H2 42 x1 hc4 C hwf hcomp hdisj hbad E hEedge hEdisj
  rw [hEcard] at hle
  exact hle
