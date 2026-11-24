import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open scoped Sym2

-- Peel a residual vertex whenever its degree costs at most twice its raw input occurrences.
theorem PEqualNP.Outside.R_meta_2579_41
    (peel : ∀ (n : ℕ) (C : Circuit), (∀ g ∈ C.gates, g.inputs.length=2) →
      ∀ E : Finset (Sym2 (Fin n)), ∃ H ⊆ E, E.card ≤ H.card+4*C.size ∧ (let degree := fun v : Fin n => (H.filter (fun e => v∈e)).card
      ∀ v : Fin n, 0 < degree v → 2*(C.gates.flatMap Gate.inputs).count v.val < degree v))
    (heavy : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5≤p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ H ⊆ {e ∈ Ustar G C | ¬∃ u v : Fin n, e=s(u,v) ∧ ∃ j<C.gates.length, ∃ b : Fin 2, 2≤(orIn n C (n+j)).card ∧ (∀ w∈orIn n C (n+j), G.Adj u w) ∧ orIn n C (opnd C j b)={v}}, (let degree := fun v : Fin n => (H.filter (fun e => v∈e)).card
      ∀ v : Fin n, 0 < degree v → 2*(C.gates.flatMap Gate.inputs).count v.val < degree v) → H.card ≤ k*(C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k,cap⟩ := heavy
  refine ⟨k+4,?_⟩
  intro n G dec girth edge C least top
  let E : Finset (Sym2 (Fin n)) := {e ∈ Ustar G C | ¬∃ u v : Fin n, e=s(u,v) ∧ ∃ j<C.gates.length, ∃ b : Fin 2, 2≤(orIn n C (n+j)).card ∧ (∀ w∈orIn n C (n+j), G.Adj u w) ∧ orIn n C (opnd C j b)={v}}
  obtain ⟨H,sub,small,degrees⟩ := peel n C least.1.2.2 E
  have limit := cap n G girth edge C least top H sub degrees
  change E.card ≤ (k+4)*(C.size+1)
  rw [Nat.add_mul]
  omega
