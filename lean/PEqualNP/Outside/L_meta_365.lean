import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_365 : ∀ (n : ℕ) (E : PEqualNP.MetaComplexity.SingleLevel.Edges n), PEqualNP.MetaComplexity.SingleLevel.WF E → ∀ τ : Fin n × Fin n → Finset (Fin n) → Fin n, (∀ e ∈ E, ∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin n × Fin n → ℚ, (∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin n, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → (∀ w : Fin n, (∀ a b : Fin n, ((w, a) ∈ E ∨ (a, w) ∈ E) → ((w, b) ∈ E ∨ (b, w) ∈ E) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) → ((E.filter (fun e => e.1 = w ∨ e.2 = w)).map c).sum = 0) ∧ (∀ e ∈ E, ((∀ f ∈ E, f ≠ e → f.1 ≠ e.1 ∧ f.2 ≠ e.1) ∨ (∀ f ∈ E, f ≠ e → f.1 ≠ e.2 ∧ f.2 ≠ e.2)) → c e = 0) := by
  intro n E wf τ orient c zero
  have sumAt (w : Fin n) (I : Finset (Fin n))
      (independent : ∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I))
      (leftNeighbor : ∀ f ∈ E, f.1 = w → f.2 ∈ I)
      (rightNeighbor : ∀ f ∈ E, f.2 = w → f.1 ∈ I) :
      ((E.filter (fun e => e.1 = w ∨ e.2 = w)).map c).sum = 0 := by
    have same : E.filter (fun e => τ e I = w) =
        E.filter (fun e => e.1 = w ∨ e.2 = w) := by
      apply List.filter_congr
      intro f hf
      simp only [decide_eq_decide]
      obtain ⟨endpoint, outside⟩ := orient f hf I independent
      constructor
      · intro hw
        exact endpoint.elim (fun h => Or.inl (h.symm.trans hw))
          (fun h => Or.inr (h.symm.trans hw))
      · rintro (hl | hr)
        · exact endpoint.resolve_right (fun h => outside (h ▸ leftNeighbor f hf hl)) |>.trans hl
        · exact endpoint.resolve_left (fun h => outside (h ▸ rightNeighbor f hf hr)) |>.trans hr
    rw [← same]
    exact zero I independent w
  constructor
  · intro w independentNeighbors
    let I := Finset.univ.filter (fun a : Fin n => (w, a) ∈ E ∨ (a, w) ∈ E)
    have memI (a : Fin n) : a ∈ I ↔ (w, a) ∈ E ∨ (a, w) ∈ E := by
      simp [I]
    apply sumAt w I
    · intro f hf both
      exact independentNeighbors f.1 f.2 ((memI _).mp both.1)
        ((memI _).mp both.2) (Or.inl (by simpa using hf))
    · intro f hf h
      exact (memI _).mpr (Or.inl (by simpa [← h] using hf))
    · intro f hf h
      exact (memI _).mpr (Or.inr (by simpa [← h] using hf))
  · intro e he pendant
    have onlyEdge (w z : Fin n) (ne : w ≠ z)
        (ends : e = (w, z) ∨ e = (z, w))
        (unique : ∀ f ∈ E, (f.1 = w ∨ f.2 = w) → f = e) : c e = 0 := by
      have hz : ∀ f ∈ E, ¬ (f.1 ∈ ({z} : Finset (Fin n)) ∧ f.2 ∈ ({z} : Finset (Fin n))) := by
        intro f hf both
        have h₁ := Finset.mem_singleton.mp both.1
        have h₂ := Finset.mem_singleton.mp both.2
        exact wf.1 f hf (h₁.trans h₂.symm)
      have sumZero := sumAt w {z} hz
      have hl (f : Fin n × Fin n) (hf : f ∈ E) (h : f.1 = w) : f.2 ∈ ({z} : Finset (Fin n)) := by
        have eq := unique f hf (Or.inl h)
        rw [eq] at h ⊢
        rcases ends with hEnds | hEnds
        · simp [hEnds]
        · exact (ne (by simpa [hEnds] using h.symm)).elim
      have hr (f : Fin n × Fin n) (hf : f ∈ E) (h : f.2 = w) : f.1 ∈ ({z} : Finset (Fin n)) := by
        have eq := unique f hf (Or.inr h)
        rw [eq] at h ⊢
        rcases ends with hEnds | hEnds
        · exact (ne (by simpa [hEnds] using h.symm)).elim
        · simp [hEnds]
      specialize sumZero hl hr
      let star := E.filter (fun f => f.1 = w ∨ f.2 = w)
      have nodup : E.Nodup := List.nodup_iff_pairwise_ne.mpr (wf.2.imp (by
        intro f g notSame eq
        subst g
        exact notSame (Or.inl ⟨rfl, rfl⟩)))
      have starNodup : star.Nodup := nodup.filter _
      have inStar : e ∈ star := by
        apply List.mem_filter.mpr
        refine ⟨he, ?_⟩
        rcases ends with h | h <;> simp [h]
      have starUnique (f) (hf : f ∈ star) : f = e := by
        have hf' := List.mem_filter.mp hf
        exact unique f hf'.1 (by simpa using hf'.2)
      have eqStar : star = [e] := by
        cases h : star with
        | nil => simp [h] at inStar
        | cons a as =>
          have hae : a = e := starUnique a (by simp [h])
          have ha : a ∉ as := List.nodup_cons.mp (h ▸ starNodup) |>.1
          cases as with
          | nil => simp [hae]
          | cons b bs =>
            have hbe : b = e := starUnique b (by simp [h])
            exact (ha (by simp [hae, hbe])).elim
      change (star.map c).sum = 0 at sumZero
      simpa [eqStar] using sumZero
    rcases pendant with left | right
    · refine onlyEdge e.1 e.2 (wf.1 e he) (Or.inl (Prod.eta e).symm) ?_
      intro f hf h
      by_contra hne
      exact h.elim (left f hf hne).1 (left f hf hne).2
    · refine onlyEdge e.2 e.1 (wf.1 e he).symm (Or.inr (Prod.eta e).symm) ?_
      intro f hf h
      by_contra hne
      exact h.elim (right f hf hne).1 (right f hf hne).2
