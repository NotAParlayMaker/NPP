import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_365_aux

open PEqualNP.MetaComplexity.SingleLevel

private lemma assignedStar {n : ℕ} (E : Edges n) (τ : Fin n × Fin n → Finset (Fin n) → Fin n)
    (hτ : ∀ e ∈ E, ∀ I : Finset (Fin n),
      (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (w : Fin n) (I : Finset (Fin n)) (independent : ∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I))
    (neighbors : ∀ e ∈ E, (e.1 = w → e.2 ∈ I) ∧ (e.2 = w → e.1 ∈ I)) :
    E.filter (fun e => τ e I = w) = E.filter (fun e => e.1 = w ∨ e.2 = w) := by
  apply List.filter_congr
  intro e he
  simp only [decide_eq_decide]
  have ⟨endpoint, outside⟩ := hτ e he I independent
  constructor
  · intro assigned
    exact endpoint.elim (fun h => Or.inl (h.symm.trans assigned))
      (fun h => Or.inr (h.symm.trans assigned))
  · rintro (left | right)
    · rcases endpoint with h | h
      · exact h.trans left
      · exact (outside (h.symm ▸ (neighbors e he).1 left)).elim
    · rcases endpoint with h | h
      · exact (outside (h.symm ▸ (neighbors e he).2 right)).elim
      · exact h.trans right

private lemma solve {n : ℕ} (E : Edges n) (hwf : WF E)
    (τ : Fin n × Fin n → Finset (Fin n) → Fin n)
    (hτ : ∀ e ∈ E, ∀ I : Finset (Fin n),
      (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (c : Fin n × Fin n → ℚ)
    (zero : ∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
      ∀ v : Fin n, ((E.filter (fun e => τ e I = v)).map c).sum = 0) :
    (∀ w : Fin n,
      (∀ a b : Fin n, ((w, a) ∈ E ∨ (a, w) ∈ E) → ((w, b) ∈ E ∨ (b, w) ∈ E) →
        ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) →
      ((E.filter (fun e => e.1 = w ∨ e.2 = w)).map c).sum = 0) ∧
    (∀ e ∈ E, ((∀ f ∈ E, f ≠ e → f.1 ≠ e.1 ∧ f.2 ≠ e.1) ∨
      (∀ f ∈ E, f ≠ e → f.1 ≠ e.2 ∧ f.2 ≠ e.2)) → c e = 0) := by
  have starZero (w : Fin n) (I : Finset (Fin n))
      (independent : ∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I))
      (neighbors : ∀ e ∈ E, (e.1 = w → e.2 ∈ I) ∧ (e.2 = w → e.1 ∈ I)) :
      ((E.filter (fun e => e.1 = w ∨ e.2 = w)).map c).sum = 0 := by
    rw [← assignedStar E τ hτ w I independent neighbors]
    exact zero I independent w
  constructor
  · intro w independentNeighbors
    let I := Finset.univ.filter fun a => (w, a) ∈ E ∨ (a, w) ∈ E
    have inI (a : Fin n) : a ∈ I ↔ (w, a) ∈ E ∨ (a, w) ∈ E := by simp [I]
    apply starZero w I
    · intro f hf both
      exact independentNeighbors f.1 f.2 ((inI _).mp both.1) ((inI _).mp both.2)
        (Or.inl hf)
    · rintro ⟨a, b⟩ he
      constructor
      · rintro rfl
        exact (inI b).mpr (Or.inl he)
      · rintro rfl
        exact (inI a).mpr (Or.inr he)
  · intro e he leaf
    have nodup : E.Nodup := by
      change E.Pairwise (fun a b => a ≠ b)
      exact hwf.2.imp (fun {a b} notSame equal => by
        subst b
        exact notSame (Or.inl ⟨rfl, rfl⟩))
    have leafZero (w u : Fin n) (hw : e.1 = w ∨ e.2 = w)
        (other : (e.1 = w → e.2 = u) ∧ (e.2 = w → e.1 = u))
        (unique : ∀ f ∈ E, f ≠ e → f.1 ≠ w ∧ f.2 ≠ w) : c e = 0 := by
      have eqEdge (f : Fin n × Fin n) (hf : f ∈ E) (incident : f.1 = w ∨ f.2 = w) :
          f = e := by
        by_contra hne
        exact incident.elim (unique f hf hne).1 (unique f hf hne).2
      have independent : ∀ f ∈ E, ¬ (f.1 ∈ ({u} : Finset (Fin n)) ∧
          f.2 ∈ ({u} : Finset (Fin n))) := by
        intro f hf both
        exact hwf.1 f hf ((Finset.mem_singleton.mp both.1).trans
          (Finset.mem_singleton.mp both.2).symm)
      have neighbors (f : Fin n × Fin n) (hf : f ∈ E) :
          (f.1 = w → f.2 ∈ ({u} : Finset (Fin n))) ∧
          (f.2 = w → f.1 ∈ ({u} : Finset (Fin n))) := by
        constructor
        · intro h
          have hfe := eqEdge f hf (Or.inl h)
          subst f
          exact Finset.mem_singleton.mpr (other.1 h)
        · intro h
          have hfe := eqEdge f hf (Or.inr h)
          subst f
          exact Finset.mem_singleton.mpr (other.2 h)
      have filterSingleton : E.filter (fun f => f.1 = w ∨ f.2 = w) = [e] := by
        apply List.Perm.eq_singleton
        refine (List.perm_ext_iff_of_nodup (nodup.filter _) (by simp)).mpr ?_
        intro f
        simp only [List.mem_filter, decide_eq_true_eq, List.mem_singleton]
        refine ⟨fun h => eqEdge f h.1 h.2, ?_⟩
        rintro rfl
        exact ⟨he, hw⟩
      have hzero := starZero w {u} independent neighbors
      rw [filterSingleton] at hzero
      simpa using hzero
    rcases leaf with left | right
    · exact leafZero e.1 e.2 (Or.inl rfl)
        ⟨fun _ => rfl, fun h => (hwf.1 e he h.symm).elim⟩ left
    · exact leafZero e.2 e.1 (Or.inr rfl)
        ⟨fun h => (hwf.1 e he h).elim, fun _ => rfl⟩ right

end PEqualNP.Outside.L_meta_365_aux

open PEqualNP.Outside.L_meta_365_aux in
theorem PEqualNP.Outside.L_meta_365 :
    ∀ (n : ℕ) (E : PEqualNP.MetaComplexity.SingleLevel.Edges n),
      PEqualNP.MetaComplexity.SingleLevel.WF E →
      ∀ τ : Fin n × Fin n → Finset (Fin n) → Fin n,
      (∀ e ∈ E, ∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
        (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) →
      ∀ c : Fin n × Fin n → ℚ,
      (∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin n,
        ((E.filter (fun e => τ e I = v)).map c).sum = 0) →
      (∀ w : Fin n, (∀ a b : Fin n, ((w, a) ∈ E ∨ (a, w) ∈ E) →
        ((w, b) ∈ E ∨ (b, w) ∈ E) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) →
        ((E.filter (fun e => e.1 = w ∨ e.2 = w)).map c).sum = 0) ∧
      (∀ e ∈ E, ((∀ f ∈ E, f ≠ e → f.1 ≠ e.1 ∧ f.2 ≠ e.1) ∨
        (∀ f ∈ E, f ≠ e → f.1 ≠ e.2 ∧ f.2 ≠ e.2)) → c e = 0) := by
  intro n E hwf τ hτ c hzero
  exact solve E hwf τ hτ c hzero
