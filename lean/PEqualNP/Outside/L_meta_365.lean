import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity.SingleLevel

namespace PEqualNP.Outside

/-- Neighbours of `w` in the undirected simple graph given by edge list `E`. -/
private def neigh {n : ℕ} (E : Edges n) (w : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun a => (w, a) ∈ E ∨ (a, w) ∈ E

private lemma neigh_mem {n : ℕ} {E : Edges n} {w a : Fin n} :
    a ∈ neigh E w ↔ (w, a) ∈ E ∨ (a, w) ∈ E := by
  simp [neigh]

/-- If `w` has an independent neighbourhood, then `neigh E w` is an independent set. -/
private lemma indep_neigh {n : ℕ} {E : Edges n} {w : Fin n}
    (hN : ∀ a b : Fin n,
      ((w, a) ∈ E ∨ (a, w) ∈ E) → ((w, b) ∈ E ∨ (b, w) ∈ E) →
        ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) :
    ∀ f ∈ E, ¬ (f.1 ∈ neigh E w ∧ f.2 ∈ neigh E w) := by
  intro f hf ⟨h1, h2⟩
  exact hN f.1 f.2 (neigh_mem.1 h1) (neigh_mem.1 h2) (Or.inl hf)

/-- A star edge at `w` has its other endpoint in `neigh E w`. -/
private lemma other_end_mem_neigh {n : ℕ} {E : Edges n} {w : Fin n} {e : Fin n × Fin n}
    (he : e ∈ E) (hst : e.1 = w ∨ e.2 = w) :
    (e.1 ≠ w → e.1 ∈ neigh E w) ∧ (e.2 ≠ w → e.2 ∈ neigh E w) := by
  constructor
  · intro hne
    have hw : e.2 = w := hst.resolve_left hne
    refine neigh_mem.2 (Or.inr ?_)
    -- need (e.1, w) ∈ E, i.e. (e.1, e.2) ∈ E
    convert he
    exact hw.symm
  · intro hne
    have hw : e.1 = w := hst.resolve_right hne
    refine neigh_mem.2 (Or.inl ?_)
    convert he
    exact hw.symm

/-- On `I = neigh E w`, every star edge is assigned to `w` by `τ`. -/
private lemma tau_star_eq_w {n : ℕ} {E : Edges n} {w : Fin n}
    {τ : Fin n × Fin n → Finset (Fin n) → Fin n}
    (hτ : ∀ e ∈ E, ∀ I : Finset (Fin n),
      (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (hN : ∀ a b : Fin n,
      ((w, a) ∈ E ∨ (a, w) ∈ E) → ((w, b) ∈ E ∨ (b, w) ∈ E) →
        ¬ ((a, b) ∈ E ∨ (b, a) ∈ E))
    {e : Fin n × Fin n} (he : e ∈ E) (hst : e.1 = w ∨ e.2 = w) :
    τ e (neigh E w) = w := by
  have hI := indep_neigh (E := E) (w := w) hN
  obtain ⟨hch, hnotin⟩ := hτ e he (neigh E w) hI
  obtain ⟨h1mem, h2mem⟩ := other_end_mem_neigh he hst
  rcases hch with h | h
  · by_cases hw : e.1 = w
    · exact h.trans hw
    · exact (hnotin (by simpa [h] using h1mem hw)).elim
  · by_cases hw : e.2 = w
    · exact h.trans hw
    · exact (hnotin (by simpa [h] using h2mem hw)).elim

/-- If `τ e (neigh E w) = w`, then `e` is incident to `w`. -/
private lemma tau_eq_w_implies_star {n : ℕ} {E : Edges n} {w : Fin n}
    {τ : Fin n × Fin n → Finset (Fin n) → Fin n}
    (hτ : ∀ e ∈ E, ∀ I : Finset (Fin n),
      (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (hN : ∀ a b : Fin n,
      ((w, a) ∈ E ∨ (a, w) ∈ E) → ((w, b) ∈ E ∨ (b, w) ∈ E) →
        ¬ ((a, b) ∈ E ∨ (b, a) ∈ E))
    {e : Fin n × Fin n} (he : e ∈ E)
    (hteq : τ e (neigh E w) = w) : e.1 = w ∨ e.2 = w := by
  have hI := indep_neigh (E := E) (w := w) hN
  obtain ⟨hch, _⟩ := hτ e he (neigh E w) hI
  rcases hch with h | h
  · exact Or.inl (h.symm.trans hteq)
  · exact Or.inr (h.symm.trans hteq)

private lemma filter_star_eq_filter_tau {n : ℕ} {E : Edges n} {w : Fin n}
    {τ : Fin n × Fin n → Finset (Fin n) → Fin n}
    (hτ : ∀ e ∈ E, ∀ I : Finset (Fin n),
      (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (hN : ∀ a b : Fin n,
      ((w, a) ∈ E ∨ (a, w) ∈ E) → ((w, b) ∈ E ∨ (b, w) ∈ E) →
        ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) :
    E.filter (fun e => e.1 = w ∨ e.2 = w) = E.filter (fun e => τ e (neigh E w) = w) := by
  refine List.filter_congr fun e he => ?_
  refine decide_eq_decide.mpr ⟨?_, ?_⟩
  · intro hst; exact tau_star_eq_w hτ hN he hst
  · intro hteq; exact tau_eq_w_implies_star hτ hN he hteq

/-- Star sum at an independent-neighbourhood vertex is zero. -/
private lemma star_sum_zero {n : ℕ} {E : Edges n} {w : Fin n}
    {τ : Fin n × Fin n → Finset (Fin n) → Fin n}
    {c : Fin n × Fin n → ℚ}
    (hτ : ∀ e ∈ E, ∀ I : Finset (Fin n),
      (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (hsum : ∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
      ∀ v : Fin n, ((E.filter (fun e => τ e I = v)).map c).sum = 0)
    (hN : ∀ a b : Fin n,
      ((w, a) ∈ E ∨ (a, w) ∈ E) → ((w, b) ∈ E ∨ (b, w) ∈ E) →
        ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) :
    ((E.filter (fun e => e.1 = w ∨ e.2 = w)).map c).sum = 0 := by
  have hI := indep_neigh (E := E) (w := w) hN
  rw [filter_star_eq_filter_tau hτ hN]
  exact hsum (neigh E w) hI w

/-- The unique neighbour of a degree-1 left endpoint is the other end of `e`. -/
private lemma unique_neigh_left {n : ℕ} {E : Edges n} (hWF : WF E)
    {e : Fin n × Fin n} (he : e ∈ E)
    (hdeg : ∀ f ∈ E, f ≠ e → f.1 ≠ e.1 ∧ f.2 ≠ e.1)
    {x : Fin n} (hx : (e.1, x) ∈ E ∨ (x, e.1) ∈ E) : x = e.2 := by
  rcases hx with hx | hx
  · by_cases hne : (e.1, x) = e
    · exact (Prod.mk.inj hne).2
    · have h := hdeg (e.1, x) hx hne
      exact absurd rfl h.1
  · by_cases hne : (x, e.1) = e
    · have ⟨h1, h2⟩ := Prod.mk.inj hne
      -- x = e.1 and e.1 = e.2, so x = e.2; contradict no loops
      exact absurd h2 (hWF.1 e he)
    · have h := hdeg (x, e.1) hx hne
      exact absurd rfl h.2

/-- The unique neighbour of a degree-1 right endpoint is the other end of `e`. -/
private lemma unique_neigh_right {n : ℕ} {E : Edges n} (hWF : WF E)
    {e : Fin n × Fin n} (he : e ∈ E)
    (hdeg : ∀ f ∈ E, f ≠ e → f.1 ≠ e.2 ∧ f.2 ≠ e.2)
    {x : Fin n} (hx : (e.2, x) ∈ E ∨ (x, e.2) ∈ E) : x = e.1 := by
  rcases hx with hx | hx
  · by_cases hne : (e.2, x) = e
    · have ⟨h1, _⟩ := Prod.mk.inj hne
      exact absurd h1.symm (hWF.1 e he)
    · have h := hdeg (e.2, x) hx hne
      exact absurd rfl h.1
  · by_cases hne : (x, e.2) = e
    · exact (Prod.mk.inj hne).1
    · have h := hdeg (x, e.2) hx hne
      exact absurd rfl h.2

/-- Degree-1 at left endpoint ⇒ independent neighbourhood of that endpoint. -/
private lemma deg1_left_indep_neigh {n : ℕ} {E : Edges n} (hWF : WF E)
    {e : Fin n × Fin n} (he : e ∈ E)
    (hdeg : ∀ f ∈ E, f ≠ e → f.1 ≠ e.1 ∧ f.2 ≠ e.1) :
    ∀ a b : Fin n,
      ((e.1, a) ∈ E ∨ (a, e.1) ∈ E) → ((e.1, b) ∈ E ∨ (b, e.1) ∈ E) →
        ¬ ((a, b) ∈ E ∨ (b, a) ∈ E) := by
  intro a b ha hb hab
  have ha' : a = e.2 := unique_neigh_left hWF he hdeg ha
  have hb' : b = e.2 := unique_neigh_left hWF he hdeg hb
  subst ha'; subst hb'
  rcases hab with h | h
  · exact (hWF.1 _ h) rfl
  · exact (hWF.1 _ h) rfl

/-- Degree-1 at right endpoint ⇒ independent neighbourhood of that endpoint. -/
private lemma deg1_right_indep_neigh {n : ℕ} {E : Edges n} (hWF : WF E)
    {e : Fin n × Fin n} (he : e ∈ E)
    (hdeg : ∀ f ∈ E, f ≠ e → f.1 ≠ e.2 ∧ f.2 ≠ e.2) :
    ∀ a b : Fin n,
      ((e.2, a) ∈ E ∨ (a, e.2) ∈ E) → ((e.2, b) ∈ E ∨ (b, e.2) ∈ E) →
        ¬ ((a, b) ∈ E ∨ (b, a) ∈ E) := by
  intro a b ha hb hab
  have ha' : a = e.1 := unique_neigh_right hWF he hdeg ha
  have hb' : b = e.1 := unique_neigh_right hWF he hdeg hb
  subst ha'; subst hb'
  rcases hab with h | h
  · exact (hWF.1 _ h) rfl
  · exact (hWF.1 _ h) rfl

/-- WF implies the edge list has no duplicate identical pairs. -/
private lemma wf_nodup {n : ℕ} {E : Edges n} (hWF : WF E) : E.Nodup := by
  have : E.Pairwise (· ≠ ·) :=
    hWF.2.imp fun {e f} hsame heq => hsame (by subst heq; exact Or.inl ⟨rfl, rfl⟩)
  exact List.nodup_iff_pairwise_ne.mpr this

/-- Filtering a nodup list for equality to a member yields the singleton. -/
private lemma filter_eq_singleton_of_mem_nodup {α : Type*} [DecidableEq α]
    {E : List α} {e : α} (he : e ∈ E) (hn : E.Nodup) :
    E.filter (fun f => f = e) = [e] := by
  induction E with
  | nil => cases he
  | cons f fs ih =>
    simp only [List.filter]
    by_cases hf : f = e
    · -- f = e: remaining filter must be empty
      subst hf
      have : fs.filter (fun g => g = f) = [] := by
        refine List.filter_eq_nil_iff.mpr ?_
        intro a ha
        simp only [decide_eq_true_eq]
        rintro rfl
        exact List.not_nodup_cons_of_mem ha hn
      simp [this]
    · have he' : e ∈ fs := List.mem_of_ne_of_mem (Ne.symm hf) he
      have hn' : fs.Nodup := List.Nodup.of_cons hn
      simp [hf, ih he' hn']

/-- The star at a degree-1 left endpoint is exactly `[e]`. -/
private lemma star_eq_singleton_left {n : ℕ} {E : Edges n} (hWF : WF E)
    {e : Fin n × Fin n} (he : e ∈ E)
    (hdeg : ∀ f ∈ E, f ≠ e → f.1 ≠ e.1 ∧ f.2 ≠ e.1) :
    E.filter (fun f => f.1 = e.1 ∨ f.2 = e.1) = [e] := by
  have hcongr :
      E.filter (fun f => f.1 = e.1 ∨ f.2 = e.1) = E.filter (fun f => f = e) := by
    refine List.filter_congr fun f hf => decide_eq_decide.mpr ⟨?_, ?_⟩
    · intro hst
      by_contra hne
      have := hdeg f hf hne
      rcases hst with h | h
      · exact this.1 h
      · exact this.2 h
    · rintro rfl
      exact Or.inl rfl
  rw [hcongr]
  exact filter_eq_singleton_of_mem_nodup he (wf_nodup hWF)

/-- The star at a degree-1 right endpoint is exactly `[e]`. -/
private lemma star_eq_singleton_right {n : ℕ} {E : Edges n} (hWF : WF E)
    {e : Fin n × Fin n} (he : e ∈ E)
    (hdeg : ∀ f ∈ E, f ≠ e → f.1 ≠ e.2 ∧ f.2 ≠ e.2) :
    E.filter (fun f => f.1 = e.2 ∨ f.2 = e.2) = [e] := by
  have hcongr :
      E.filter (fun f => f.1 = e.2 ∨ f.2 = e.2) = E.filter (fun f => f = e) := by
    refine List.filter_congr fun f hf => decide_eq_decide.mpr ⟨?_, ?_⟩
    · intro hst
      by_contra hne
      have := hdeg f hf hne
      rcases hst with h | h
      · exact this.1 h
      · exact this.2 h
    · rintro rfl
      exact Or.inr rfl
  rw [hcongr]
  exact filter_eq_singleton_of_mem_nodup he (wf_nodup hWF)

/-- A pendant-type edge has weight zero. -/
private lemma pendant_zero {n : ℕ} {E : Edges n} (hWF : WF E)
    {τ : Fin n × Fin n → Finset (Fin n) → Fin n}
    {c : Fin n × Fin n → ℚ}
    (hτ : ∀ e ∈ E, ∀ I : Finset (Fin n),
      (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (hsum : ∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
      ∀ v : Fin n, ((E.filter (fun e => τ e I = v)).map c).sum = 0)
    {e : Fin n × Fin n} (he : e ∈ E)
    (hpend : (∀ f ∈ E, f ≠ e → f.1 ≠ e.1 ∧ f.2 ≠ e.1) ∨
             (∀ f ∈ E, f ≠ e → f.1 ≠ e.2 ∧ f.2 ≠ e.2)) :
    c e = 0 := by
  rcases hpend with hdeg | hdeg
  · have hN := deg1_left_indep_neigh hWF he hdeg
    have hs := star_sum_zero (w := e.1) hτ hsum hN
    rw [star_eq_singleton_left hWF he hdeg] at hs
    simpa using hs
  · have hN := deg1_right_indep_neigh hWF he hdeg
    have hs := star_sum_zero (w := e.2) hτ hsum hN
    rw [star_eq_singleton_right hWF he hdeg] at hs
    simpa using hs

theorem L_meta_365 :
    ∀ (n : ℕ) (E : Edges n), WF E →
      ∀ τ : Fin n × Fin n → Finset (Fin n) → Fin n,
        (∀ e ∈ E, ∀ I : Finset (Fin n),
          (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
            (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) →
        ∀ c : Fin n × Fin n → ℚ,
          (∀ I : Finset (Fin n),
            (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
              ∀ v : Fin n, ((E.filter (fun e => τ e I = v)).map c).sum = 0) →
          (∀ w : Fin n,
              (∀ a b : Fin n,
                ((w, a) ∈ E ∨ (a, w) ∈ E) → ((w, b) ∈ E ∨ (b, w) ∈ E) →
                  ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) →
              ((E.filter (fun e => e.1 = w ∨ e.2 = w)).map c).sum = 0) ∧
          (∀ e ∈ E,
              ((∀ f ∈ E, f ≠ e → f.1 ≠ e.1 ∧ f.2 ≠ e.1) ∨
                (∀ f ∈ E, f ≠ e → f.1 ≠ e.2 ∧ f.2 ≠ e.2)) →
              c e = 0) := by
  intro n E hWF τ hτ c hsum
  constructor
  · intro w hN
    exact star_sum_zero hτ hsum hN
  · intro e he hpend
    exact pendant_zero hWF hτ hsum he hpend

end PEqualNP.Outside
