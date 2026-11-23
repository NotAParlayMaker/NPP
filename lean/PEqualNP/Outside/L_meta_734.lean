import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Push

theorem PEqualNP.Outside.L_meta_734 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  G.Colorable 2 →
  (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
  (∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard) →
  ∀ T : Set (Fin n), T.ncard ≤ 5 →
    (∀ I : Set (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) →
      ∃ t ∈ T, t ∈ I) →
    ∃ v ∈ T, ∀ w, G.Adj v w → w ∈ T := by
  classical
  intro n G hcol square deg T bound hit
  obtain ⟨c⟩ := hcol
  let side (i : Fin 2) : Set (Fin n) := {v | v ∈ T ∧ c v = i}
  have unionEq : side 0 ∪ side 1 = T := by
    ext v
    change ((v ∈ T ∧ c v = 0) ∨ (v ∈ T ∧ c v = 1)) ↔ v ∈ T
    constructor
    · rintro (h|h) <;> exact h.1
    · intro h
      have : c v = 0 ∨ c v = 1 := by omega
      exact this.elim (fun e => Or.inl ⟨h,e⟩) (fun e => Or.inr ⟨h,e⟩)
  have apart : side 0 ∩ side 1 = ∅ := by
    ext v
    change ((v ∈ T ∧ c v = 0) ∧ v ∈ T ∧ c v = 1) ↔ False
    simp_all
  have sum := Set.ncard_union_add_ncard_inter (side 0) (side 1)
  rw [unionEq,apart,Set.ncard_empty,Nat.add_zero] at sum
  obtain ⟨i,small⟩ : ∃ i : Fin 2, (side i).ncard ≤ 2 := by
    by_cases h : (side 0).ncard ≤ 2
    · exact ⟨0,h⟩
    · exact ⟨1,by omega⟩
  by_contra missing
  push_neg at missing
  let pick (v : Fin n) : Fin n := if h : v ∈ T then Classical.choose (missing v h) else v
  have picked (v : Fin n) (h : v ∈ T) : G.Adj v (pick v) ∧ pick v ∉ T := by
    simpa [pick,h] using Classical.choose_spec (missing v h)
  let P := pick '' (side i)
  have pp (p : Fin n) (h : p ∈ P) : c p ≠ i ∧ p ∉ T := by
    obtain ⟨v,hv,rfl⟩ := h
    obtain ⟨ht,hc⟩ := hv
    exact ⟨hc ▸ (c.valid (picked v ht).1).symm,(picked v ht).2⟩
  let S : Set (Fin n) := {v | c v = i ∧ ∀ p ∈ P, ¬ G.Adj v p}
  let U : Set (Fin n) := {v | c v ≠ i ∧ ∀ s ∈ S, ¬ G.Adj v s}
  have pu : P ⊆ U := by
    intro p hp
    exact ⟨(pp p hp).1,fun s hs adj => hs.2 p hp adj.symm⟩
  have independent : ∀ u ∈ S ∪ U, ∀ v ∈ S ∪ U, ¬ G.Adj u v := by
    intro u hu v hv adj
    rcases hu with hu|hu <;> rcases hv with hv|hv
    · exact c.valid adj (hu.1.trans hv.1.symm)
    · exact hv.2 u hu adj.symm
    · exact hu.2 v hv adj
    · have h1 := hu.1
      have h2 := hv.1
      exact c.valid adj (by omega)
  have maximal : ∀ v, v ∉ S ∪ U → ∃ u ∈ S ∪ U, G.Adj v u := by
    intro v hv
    by_contra no
    push_neg at no
    apply hv
    by_cases h : c v = i
    · exact Or.inl ⟨h,fun p hp => no p (Or.inr (pu hp))⟩
    · exact Or.inr ⟨h,fun s hs => no s (Or.inl hs)⟩
  obtain ⟨v,ht,hv⟩ := hit (S ∪ U) independent maximal
  rcases hv with hs|hu
  · exact hs.2 (pick v) ⟨v,⟨ht,hs.1⟩,rfl⟩ (picked v ht).1
  · have witness (w : Fin n) (adj : G.Adj v w) : ∃ p ∈ P, G.Adj w p := by
      by_contra no
      push_neg at no
      have h1 := hu.1
      have h2 := c.valid adj
      exact hu.2 w ⟨by omega,no⟩ adj
    let f (w : Fin n) := if h : G.Adj v w then Classical.choose (witness w h) else v
    have hf (w : Fin n) (h : G.Adj v w) : f w ∈ P ∧ G.Adj w (f w) := by
      simpa [f,h] using Classical.choose_spec (witness w h)
    have inj : Set.InjOn f {w | G.Adj v w} := by
      intro a ha b hb eq
      obtain hvp|hab := square v a (f a) b ha (hf a ha).2 (eq ▸ (hf b hb).2.symm) hb.symm
      · exact False.elim ((pp (f a) (hf a ha).1).2 (hvp ▸ ht))
      · exact hab
    have card := Set.ncard_le_ncard_of_injOn f (fun a (ha : a ∈ {w | G.Adj v w}) => (hf a ha).1) inj
    have cap : P.ncard ≤ (side i).ncard := Set.ncard_image_le
    have lo := deg v
    omega
