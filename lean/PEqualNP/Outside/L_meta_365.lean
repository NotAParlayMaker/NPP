import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_365

lemma sum_single {α : Type} [DecidableEq α] (c : α → ℚ) (e : α) (E : List α) (hnd : E.Nodup)
    (he : e ∈ E) : ((E.filter (fun f => decide (f = e))).map c).sum = c e := by
  induction E with
  | nil => simp at he
  | cons a l ih =>
    have hnd' := List.nodup_cons.mp hnd
    by_cases hae : a = e
    · have hnil : l.filter (fun f => decide (f = e)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro f hf
        simp only [decide_eq_true_eq]
        intro hfe
        apply hnd'.1
        rw [hae, ← hfe]
        exact hf
      rw [List.filter_cons_of_pos (by simp [hae]), hnil, hae]
      simp
    · have hel : e ∈ l := by
        rcases List.mem_cons.mp he with h | h
        · exact absurd h.symm hae
        · exact h
      rw [List.filter_cons_of_neg (by simp [hae])]
      exact ih hnd'.2 hel

end PEqualNP.Outside.L_meta_365

theorem PEqualNP.Outside.L_meta_365 : ∀ (n : ℕ) (E : PEqualNP.MetaComplexity.SingleLevel.Edges n), PEqualNP.MetaComplexity.SingleLevel.WF E → ∀ τ : Fin n × Fin n → Finset (Fin n) → Fin n, (∀ e ∈ E, ∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin n × Fin n → ℚ, (∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin n, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → (∀ w : Fin n, (∀ a b : Fin n, ((w, a) ∈ E ∨ (a, w) ∈ E) → ((w, b) ∈ E ∨ (b, w) ∈ E) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) → ((E.filter (fun e => e.1 = w ∨ e.2 = w)).map c).sum = 0) ∧ (∀ e ∈ E, ((∀ f ∈ E, f ≠ e → f.1 ≠ e.1 ∧ f.2 ≠ e.1) ∨ (∀ f ∈ E, f ≠ e → f.1 ≠ e.2 ∧ f.2 ≠ e.2)) → c e = 0) := by
  intro n E hWF τ hτ c hc
  obtain ⟨hloop, hpw⟩ := hWF
  have hnd : E.Nodup := by
    apply List.Pairwise.imp _ hpw
    intro a b h hab
    apply h
    rw [hab]
    exact Or.inl ⟨rfl, rfl⟩
  constructor
  · intro w hw
    classical
    have hI : ∀ f ∈ E, ¬ (f.1 ∈ Finset.univ.filter (fun a : Fin n => (w, a) ∈ E ∨ (a, w) ∈ E) ∧
        f.2 ∈ Finset.univ.filter (fun a : Fin n => (w, a) ∈ E ∨ (a, w) ∈ E)) := by
      intro f hf hboth
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hboth
      exact hw f.1 f.2 hboth.1 hboth.2 (Or.inl hf)
    have h0 := hc _ hI w
    rw [← h0]
    congr 2
    apply List.filter_congr
    intro f hf
    rw [decide_eq_decide]
    obtain ⟨h1, h2⟩ := hτ f hf _ hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
    constructor
    · rintro (h | h)
      · rcases h1 with e1 | e1
        · rw [e1, h]
        · exfalso
          apply h2
          rw [e1]
          left
          rw [← h]
          exact hf
      · rcases h1 with e1 | e1
        · exfalso
          apply h2
          rw [e1]
          right
          rw [← h]
          exact hf
        · rw [e1, h]
    · intro h
      rcases h1 with e1 | e1
      · left
        rw [← e1, h]
      · right
        rw [← e1, h]
  · intro e he hpend
    classical
    rcases hpend with hp | hp
    · have hI : ∀ f ∈ E, ¬ (f.1 ∈ ({e.2} : Finset (Fin n)) ∧ f.2 ∈ ({e.2} : Finset (Fin n))) := by
        intro f hf hboth
        simp only [Finset.mem_singleton] at hboth
        exact hloop f hf (hboth.1.trans hboth.2.symm)
      have h0 := hc _ hI e.1
      rw [← PEqualNP.Outside.L_meta_365.sum_single c e E hnd he, ← h0]
      congr 2
      apply List.filter_congr
      intro f hf
      rw [decide_eq_decide]
      obtain ⟨h1, h2⟩ := hτ f hf _ hI
      simp only [Finset.mem_singleton] at h2
      constructor
      · intro hfe
        rw [hfe] at h1 h2
        rcases h1 with e1 | e1
        · rw [hfe]
          exact e1
        · exact absurd e1 h2
      · intro h
        by_contra hne
        obtain ⟨p1, p2⟩ := hp f hf hne
        rcases h1 with e1 | e1
        · exact p1 (e1.symm.trans h)
        · exact p2 (e1.symm.trans h)
    · have hI : ∀ f ∈ E, ¬ (f.1 ∈ ({e.1} : Finset (Fin n)) ∧ f.2 ∈ ({e.1} : Finset (Fin n))) := by
        intro f hf hboth
        simp only [Finset.mem_singleton] at hboth
        exact hloop f hf (hboth.1.trans hboth.2.symm)
      have h0 := hc _ hI e.2
      rw [← PEqualNP.Outside.L_meta_365.sum_single c e E hnd he, ← h0]
      congr 2
      apply List.filter_congr
      intro f hf
      rw [decide_eq_decide]
      obtain ⟨h1, h2⟩ := hτ f hf _ hI
      simp only [Finset.mem_singleton] at h2
      constructor
      · intro hfe
        rw [hfe] at h1 h2
        rcases h1 with e1 | e1
        · exact absurd e1 h2
        · rw [hfe]
          exact e1
      · intro h
        by_contra hne
        obtain ⟨p1, p2⟩ := hp f hf hne
        rcases h1 with e1 | e1
        · exact p1 (e1.symm.trans h)
        · exact p2 (e1.symm.trans h)
