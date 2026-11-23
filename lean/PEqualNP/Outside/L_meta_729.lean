import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_729

private def Walk {V : Type} (E : V → V → Prop) (a b : V) (l : ℕ) : Prop :=
  ∃ f : ℕ → V, f 0 = a ∧ f l = b ∧ ∀ i, i < l → E (f i) (f (i + 1))

private theorem stationary {V : Type} (E : V → V → Prop) (a : V) :
    Walk E a a 0 := ⟨fun _ => a, rfl, rfl, by simp⟩

private theorem prepend {V : Type} {E : V → V → Prop} {a b c : V} {l : ℕ}
    (h : E a b) (w : Walk E b c l) : Walk E a c (l + 1) := by
  obtain ⟨f, hf, hc, he⟩ := w
  refine ⟨fun i => Nat.casesOn i a f, rfl, hc, ?_⟩
  intro i hi
  cases i with
  | zero => simpa [hf] using h
  | succ j => exact he j (by omega)

private theorem appendWalk {V : Type} {E : V → V → Prop} {a b c : V} {l m : ℕ}
    (w : Walk E a b l) (z : Walk E b c m) : Walk E a c (l + m) := by
  obtain ⟨f, ha, hb, hf⟩ := w
  obtain ⟨g, hb', hc, hg⟩ := z
  let p (i : ℕ) := if i < l then f i else g (i - l)
  have atCut : p l = f l := by simp [p, hb, hb']
  refine ⟨p, ?_, by simpa [p, show ¬ l + m < l by omega] using hc, ?_⟩
  · by_cases h : 0 < l
    · simpa [p, h] using ha
    · have : l = 0 := by omega
      subst l
      exact atCut.trans ha
  · intro i hi
    by_cases h : i < l
    · by_cases h' : i + 1 < l
      · simpa [p, h, h'] using hf i h
      · have hcut : i + 1 = l := by omega
        rw [hcut, atCut]
        simpa [p, h, hcut] using hf i h
    · have h' : ¬ i + 1 < l := by omega
      have heq : i + 1 - l = (i - l) + 1 := by omega
      simpa [p, h, h', heq] using hg (i-l) (by omega)

private def KernelOn {n : ℕ} (D : Fin n → Fin n → Prop) (s : Finset (Fin n))
    (K : Set (Fin n)) : Prop :=
  (∀ x ∈ K, x ∈ s) ∧ (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧
    ∀ v ∈ s, v ∉ K → ∃ k ∈ K, D v k

private theorem kernel {n : ℕ} (D : Fin n → Fin n → Prop)
    (noOdd : ¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2*k+1) = c 0 ∧
      ∀ i, i < 2*k+1 → D (c i) (c (i+1))) (s : Finset (Fin n)) :
    ∃ K, KernelOn D s K := by
  classical
  by_cases hs : s.Nonempty
  · let E := fun u v => D u v ∧ v ∈ s
    let zone (a : Fin n) := s.filter (fun v => ∃ l, Walk E a v l)
    have self (a : Fin n) (ha : a ∈ s) : a ∈ zone a :=
      Finset.mem_filter.mpr ⟨ha, 0, stationary E a⟩
    have minExists : ∃ m, ∃ r ∈ s, (zone r).card = m := by
      obtain ⟨a, ha⟩ := hs
      exact ⟨_, a, ha, rfl⟩
    obtain ⟨r, hr, hsize⟩ := Nat.find_spec minExists
    have same {v} (hv : v ∈ zone r) : zone v = zone r := by
      obtain ⟨hvs, l, w⟩ := Finset.mem_filter.mp hv
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨hxs, m, z⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hxs, _, appendWalk w z⟩
      · rw [hsize]
        exact Nat.find_min' minExists ⟨v, hvs, rfl⟩
    have closed {u v} (hu : u ∈ zone r) (e : E u v) : v ∈ zone r := by
      rw [← same hu]
      exact Finset.mem_filter.mpr ⟨e.2, 1, prepend e (stationary E v)⟩
    have evenLoop {a l} (w : Walk E a a l) : l % 2 = 0 := by
      by_contra h
      obtain ⟨f, hf, hf', he⟩ := w
      have hl : 2 * (l/2) + 1 = l := by omega
      apply noOdd
      refine ⟨l/2, f, ?_, ?_⟩
      · rw [hl, hf', hf]
      · rw [hl]
        exact fun i hi => (he i hi).1
    let A : Set (Fin n) := {v | v ∈ zone r ∧ ∃ l, Walk E v r l ∧ l % 2 = 0}
    have rA : r ∈ A := ⟨self r hr, 0, stationary E r, rfl⟩
    have indA {u} (hu : u ∈ A) {v} (hv : v ∈ A) (e : D u v) : False := by
      obtain ⟨hur, l, w, hl⟩ := hu
      obtain ⟨hvr, m, z, hm⟩ := hv
      obtain ⟨_, t, p⟩ := Finset.mem_filter.mp hur
      have h₁ := evenLoop (appendWalk p w)
      have h₂ := evenLoop (appendWalk p (prepend ⟨e, (Finset.mem_filter.mp hvr).1⟩ z))
      omega
    have absorb {v} (hv : v ∈ zone r) (hna : v ∉ A) : ∃ a ∈ A, D v a := by
      have : r ∈ zone v := by rw [same hv]; exact self r hr
      obtain ⟨_, l, w⟩ := Finset.mem_filter.mp this
      have odd : l % 2 ≠ 0 := fun h => hna ⟨hv, l, w, h⟩
      obtain ⟨f, hf, hf', he⟩ := w
      have e := he 0 (by omega)
      rw [hf] at e
      refine ⟨f 1, ⟨closed hv e, l-1, ?_, by omega⟩, e.1⟩
      refine ⟨fun i => f (i+1), rfl, ?_, fun i hi => he (i+1) (by omega)⟩
      simpa [show l-1+1 = l by omega] using hf'
    let rest := s.filter (fun v => v ∉ A ∧ ¬ ∃ a ∈ A, D v a)
    have small : rest.card < s.card := by
      apply Finset.card_lt_card
      apply (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2
      exact ⟨r, hr, fun h => (Finset.mem_filter.mp h).2.1 rA⟩
    obtain ⟨B, hBs, hBi, hBa⟩ := kernel D noOdd rest
    refine ⟨A ∪ B, ?_, ?_, ?_⟩
    · intro v hv
      rcases hv with ha | hb
      · exact (Finset.mem_filter.mp ha.1).1
      · exact (Finset.mem_filter.mp (hBs v hb)).1
    · intro u hu v hv e
      rcases hu with hua | hub <;> rcases hv with hva | hvb
      · exact indA hua hva e
      · obtain ⟨hvs, hna, hn⟩ := Finset.mem_filter.mp (hBs v hvb)
        exact hn (absorb (closed hua.1 ⟨e, hvs⟩) hna)
      · exact (Finset.mem_filter.mp (hBs u hub)).2.2 ⟨v, hva, e⟩
      · exact hBi u hub v hvb e
    · intro v hv hn
      by_cases h : ∃ a ∈ A, D v a
      · obtain ⟨a, ha, he⟩ := h
        exact ⟨a, Or.inl ha, he⟩
      · have hrest : v ∈ rest := Finset.mem_filter.mpr ⟨hv, fun hA => hn (Or.inl hA), h⟩
        obtain ⟨b, hb, he⟩ := hBa v hrest (fun hB => hn (Or.inr hB))
        exact ⟨b, Or.inr hb, he⟩
  · refine ⟨∅, by simp, by simp, ?_⟩
    exact fun v hv => (hs ⟨v, hv⟩).elim
termination_by s.card

end PEqualNP.Outside.L_meta_729

theorem PEqualNP.Outside.L_meta_729 : ∀ (n : ℕ) (D : Fin n → Fin n → Prop),
  (∀ v, ¬ D v v) → (∀ u v, D u v → ¬ D v u) →
  (¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧ ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) →
  ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  intro n D _ _ h
  obtain ⟨K, _, hi, ha⟩ := PEqualNP.Outside.L_meta_729.kernel D h Finset.univ
  exact ⟨K, hi, fun v => ha v (Finset.mem_univ v)⟩
