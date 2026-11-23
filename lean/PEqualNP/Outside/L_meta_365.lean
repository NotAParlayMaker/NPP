import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta365

open PEqualNP.MetaComplexity.SingleLevel

private theorem nodup_of_wf {n : ℕ} {E : Edges n} (hE : WF E) : E.Nodup := by
  have hp : E.Pairwise (· ≠ ·) := by
    apply List.Pairwise.imp _ hE.2
    intro a b hab heq
    subst b
    apply hab
    exact Or.inl ⟨rfl, rfl⟩
  exact hp.nodup

private theorem sum_filter_map_singleton {α β : Type*} [AddCommMonoid β]
    (l : List α) (p : α → Prop) [DecidablePred p] (e : α) (f : α → β)
    (hnodup : l.Nodup) (he : e ∈ l)
    (hcond : ∀ a ∈ l, p a ↔ a = e) :
    ((l.filter p).map f).sum = f e := by
  induction l with
  | nil => simp at he
  | cons a l ih =>
    rcases List.nodup_cons.mp hnodup with ⟨hnot, hnodup⟩
    by_cases hae : a = e
    · subst a
      have hpa : p e := (hcond e (by simp)).2 rfl
      have htail : l.filter p = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb hp
        have hbe : b = e := (hcond b (by simp [hb])).1 (of_decide_eq_true hp)
        exact hnot (hbe ▸ hb)
      simp [hpa, htail]
    · have hpa : ¬ p a := by
        intro hp
        exact hae ((hcond a (by simp)).1 hp)
      have hel : e ∈ l := by
        rcases List.mem_cons.mp he with h | h
        · exact (hae h.symm).elim
        · exact h
      have hcond' : ∀ b ∈ l, p b ↔ b = e := by
        intro b hb
        exact hcond b (by simp [hb])
      simp [hpa, ih hnodup hel hcond']

end PEqualNP.Outside.LMeta365

namespace PEqualNP.Outside

theorem L_meta_365 : ∀ (n : ℕ) (E : PEqualNP.MetaComplexity.SingleLevel.Edges n), PEqualNP.MetaComplexity.SingleLevel.WF E → ∀ τ : Fin n × Fin n → Finset (Fin n) → Fin n, (∀ e ∈ E, ∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin n × Fin n → ℚ, (∀ I : Finset (Fin n), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin n, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → (∀ w : Fin n, (∀ a b : Fin n, ((w, a) ∈ E ∨ (a, w) ∈ E) → ((w, b) ∈ E ∨ (b, w) ∈ E) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) → ((E.filter (fun e => e.1 = w ∨ e.2 = w)).map c).sum = 0) ∧ (∀ e ∈ E, ((∀ f ∈ E, f ≠ e → f.1 ≠ e.1 ∧ f.2 ≠ e.1) ∨ (∀ f ∈ E, f ≠ e → f.1 ≠ e.2 ∧ f.2 ≠ e.2)) → c e = 0) := by
  intro n E hE τ hτ c hbalance
  have hnodup : E.Nodup := PEqualNP.Outside.LMeta365.nodup_of_wf hE
  constructor
  · intro w hstar
    let I : Finset (Fin n) := Finset.univ.filter (fun v => (w, v) ∈ E ∨ (v, w) ∈ E)
    have hImem (v : Fin n) : v ∈ I ↔ (w, v) ∈ E ∨ (v, w) ∈ E := by
      simp [I]
    have hIind : ∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I) := by
      intro f hf ⟨h1, h2⟩
      exact hstar f.1 f.2 (hImem f.1 |>.mp h1) (hImem f.2 |>.mp h2) (Or.inl hf)
    have hwI : w ∉ I := by
      intro hw
      rcases (hImem w).mp hw with h | h
      · exact hE.1 (w, w) h rfl
      · exact hE.1 (w, w) h rfl
    have hassign (e : Fin n × Fin n) (he : e ∈ E) :
        τ e I = w ↔ e.1 = w ∨ e.2 = w := by
      constructor
      · intro ht
        rcases (hτ e he I hIind).1 with h | h
        · exact Or.inl (h.symm.trans ht)
        · exact Or.inr (h.symm.trans ht)
      · rintro (h1 | h2)
        · have he' : (e.1, e.2) ∈ E := by simpa using he
          have h2I : e.2 ∈ I :=
            (hImem e.2).2 (Or.inl (by simpa [h1] using he'))
          rcases hτ e he I hIind with ⟨hsel | hsel, hnot⟩
          · exact hsel.trans h1
          · exact False.elim (hnot (hsel ▸ h2I))
        · have he' : (e.1, e.2) ∈ E := by simpa using he
          have h1I : e.1 ∈ I :=
            (hImem e.1).2 (Or.inr (by simpa [h2] using he'))
          rcases hτ e he I hIind with ⟨hsel | hsel, hnot⟩
          · exact False.elim (hnot (hsel ▸ h1I))
          · exact hsel.trans h2
    have hfilter :
        E.filter (fun e => τ e I = w) = E.filter (fun e => e.1 = w ∨ e.2 = w) := by
      apply List.filter_congr
      intro e he
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using hassign e he
    rw [← hfilter]
    exact hbalance I hIind w
  · intro e he hleaf
    have hzero (v : Fin n) (I : Finset (Fin n))
        (hI : ∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) :
        ((E.filter (fun f => τ f I = v)).map c).sum = 0 := hbalance I hI v
    rcases hleaf with hleaf | hleaf
    · let I : Finset (Fin n) := {e.2}
      have hIind : ∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I) := by
        intro f hf hboth
        rcases hboth with ⟨hfirst, hsecond⟩
        have h1 : f.1 = e.2 := Finset.mem_singleton.mp (by simpa [I] using hfirst)
        have h2 : f.2 = e.2 := Finset.mem_singleton.mp (by simpa [I] using hsecond)
        apply hE.1 f hf
        exact h1.trans h2.symm
      have hτe : τ e I = e.1 := by
        rcases hτ e he I hIind with ⟨h1 | h2, hnot⟩
        · exact h1
        · exact False.elim (hnot (by simpa [I, h2]))
      have honly (f : Fin n × Fin n) (hf : f ∈ E) : τ f I = e.1 ↔ f = e := by
        constructor
        · intro htf
          by_contra hne
          have hleaf' := hleaf f hf hne
          rcases (hτ f hf I hIind).1 with hassigned1 | hassigned2
          · exact hleaf'.1 (hassigned1.symm.trans htf)
          · exact hleaf'.2 (hassigned2.symm.trans htf)
        · rintro rfl
          exact hτe
      have hsum := PEqualNP.Outside.LMeta365.sum_filter_map_singleton
        E (fun f => τ f I = e.1) e c hnodup he honly
      have hz := hzero e.1 I hIind
      rw [hsum] at hz
      exact hz
    · let I : Finset (Fin n) := {e.1}
      have hIind : ∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I) := by
        intro f hf hboth
        rcases hboth with ⟨hfirst, hsecond⟩
        have h1 : f.1 = e.1 := Finset.mem_singleton.mp (by simpa [I] using hfirst)
        have h2 : f.2 = e.1 := Finset.mem_singleton.mp (by simpa [I] using hsecond)
        apply hE.1 f hf
        exact h1.trans h2.symm
      have hτe : τ e I = e.2 := by
        rcases hτ e he I hIind with ⟨h1 | h2, hnot⟩
        · exact False.elim (hnot (by simpa [I, h1]))
        · exact h2
      have honly (f : Fin n × Fin n) (hf : f ∈ E) : τ f I = e.2 ↔ f = e := by
        constructor
        · intro htf
          by_contra hne
          have hleaf' := hleaf f hf hne
          rcases (hτ f hf I hIind).1 with hassigned1 | hassigned2
          · exact hleaf'.1 (hassigned1.symm.trans htf)
          · exact hleaf'.2 (hassigned2.symm.trans htf)
        · rintro rfl
          exact hτe
      have hsum := PEqualNP.Outside.LMeta365.sum_filter_map_singleton
        E (fun f => τ f I = e.2) e c hnodup he honly
      have hz := hzero e.2 I hIind
      rw [hsum] at hz
      exact hz
end PEqualNP.Outside
