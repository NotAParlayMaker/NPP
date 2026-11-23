import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta461

lemma filter_weight_sum {α : Type} (L : List α) (p : α → Bool) (c : α → ℚ) :
    ((L.filter p).map c).sum = (L.map (fun e => if p e then c e else 0)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => cases hp : p a <;> simp [hp, ih]

end PEqualNP.Outside.LMeta461

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_461 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] → ∀ τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6, (∀ e ∈ E, ∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 6 × Fin 6 → ℚ, (∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 6, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  classical
  intro E hE
  subst E
  intro τ hτ c hc
  let E : List (Fin 6 × Fin 6) := [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)]
  have hind (i : Fin 6) : ∀ f ∈ E,
      ¬ (f.1 ∈ ({i} : Finset (Fin 6)) ∧ f.2 ∈ ({i} : Finset (Fin 6))) := by
    fin_cases i <;> decide
  have ht (i : Fin 6) (e : Fin 6 × Fin 6) (he : e ∈ E) :
      (τ e {i} = e.1 ∨ τ e {i} = e.2) ∧ τ e {i} ≠ i := by
    simpa only [Finset.mem_singleton] using hτ e he {i} (hind i)
  have forceL (u v : Fin 6) (he : (u, v) ∈ E) : τ (u, v) {u} = v :=
    (ht u (u, v) he).1.resolve_left (ht u (u, v) he).2
  have forceR (u v : Fin 6) (he : (u, v) ∈ E) : τ (u, v) {v} = u :=
    (ht v (u, v) he).1.resolve_right (ht v (u, v) he).2
  have never (i v : Fin 6) (e : Fin 6 × Fin 6) (he : e ∈ E)
      (hne : e.1 ≠ v ∧ e.2 ≠ v) : τ e {i} ≠ v := by
    intro h
    rcases (ht i e he).1 with h0 | h1
    · exact hne.1 (h0.symm.trans h)
    · exact hne.2 (h1.symm.trans h)
  have p03 : c (0, 3) = 0 := by
    simpa [E,
      forceL 0 3 (by decide),
      never 0 3 (0, 1) (by decide) (by decide),
      never 0 3 (0, 2) (by decide) (by decide),
      never 0 3 (1, 2) (by decide) (by decide),
      never 0 3 (1, 4) (by decide) (by decide),
      never 0 3 (2, 5) (by decide) (by decide)] using hc {0} (hind 0) 3
  have p14 : c (1, 4) = 0 := by
    simpa [E,
      forceL 1 4 (by decide),
      never 1 4 (0, 1) (by decide) (by decide),
      never 1 4 (0, 2) (by decide) (by decide),
      never 1 4 (1, 2) (by decide) (by decide),
      never 1 4 (0, 3) (by decide) (by decide),
      never 1 4 (2, 5) (by decide) (by decide)] using hc {1} (hind 1) 4
  have p25 : c (2, 5) = 0 := by
    simpa [E,
      forceL 2 5 (by decide),
      never 2 5 (0, 1) (by decide) (by decide),
      never 2 5 (0, 2) (by decide) (by decide),
      never 2 5 (1, 2) (by decide) (by decide),
      never 2 5 (0, 3) (by decide) (by decide),
      never 2 5 (1, 4) (by decide) (by decide)] using hc {2} (hind 2) 5
  have hs (i v : Fin 6) :
      (if τ (0, 1) {i} = v then c (0, 1) else 0) +
        ((if τ (0, 2) {i} = v then c (0, 2) else 0) +
          (if τ (1, 2) {i} = v then c (1, 2) else 0)) = 0 := by
    have h := hc {i} (hind i) v
    rw [PEqualNP.Outside.LMeta461.filter_weight_sum] at h
    simpa [E, p03, p14, p25] using h
  have htri : c (0, 1) = 0 ∧ c (0, 2) = 0 ∧ c (1, 2) = 0 := by
    rcases (ht 0 (1, 2) (by decide)).1 with h12 | h12
    · have z02 : c (0, 2) = 0 := by
        simpa [forceL 0 1 (by decide), forceL 0 2 (by decide), h12] using hs 0 2
      have z01 : c (0, 1) = 0 := by
        simpa [forceR 0 1 (by decide), forceL 1 2 (by decide), z02] using hs 1 0
      have z12 : c (1, 2) = 0 := by
        simpa [forceL 0 1 (by decide), forceL 0 2 (by decide), h12, z01, z02] using hs 0 1
      exact ⟨z01, z02, z12⟩
    · have z01 : c (0, 1) = 0 := by
        simpa [forceL 0 1 (by decide), forceL 0 2 (by decide), h12] using hs 0 1
      have z02 : c (0, 2) = 0 := by
        simpa [forceR 0 2 (by decide), forceR 1 2 (by decide), z01] using hs 2 0
      have z12 : c (1, 2) = 0 := by
        simpa [forceL 0 1 (by decide), forceL 0 2 (by decide), h12, z01, z02] using hs 0 2
      exact ⟨z01, z02, z12⟩
  intro e he
  change e ∈ E at he
  simp only [E, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact htri.1
  · exact htri.2.1
  · exact htri.2.2
  · exact p03
  · exact p14
  · exact p25
