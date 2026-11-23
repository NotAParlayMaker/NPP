import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_307 : ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ c : ℕ, (∀ S : Finset V, (∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S) → c ≤ S.card) ↔ (∀ S : Finset (Fin N), (∀ a b, G'.Adj a b → a ∈ S ∨ b ∈ S) → c ≤ S.card) := by
  classical
  intro V G N num H hlt hinj hadj c
  constructor
  · intro lower S covers
    rcases isEmpty_or_nonempty V with hi | hv
    · have bound := lower ∅ (fun u => isEmptyElim u)
      simp only [Finset.card_empty] at bound
      exact bound.trans (Nat.zero_le _)
    let active (u : V) := ∃ v, G.Adj u v
    let pick (i : Fin N) : V :=
      if h : ∃ u, active u ∧ num u = i.val then h.choose else Classical.choice hv
    have pick_eq (u v : V) (e : G.Adj u v) (i : Fin N) (hi : num u = i.val) :
        pick i = u := by
      have ex : ∃ w, active w ∧ num w = i.val := ⟨u, ⟨v,e⟩, hi⟩
      have spec := ex.choose_spec
      obtain ⟨z,hz⟩ := spec.1
      simpa [pick,ex] using hinj ex.choose z u v hz e (spec.2.trans hi.symm)
    apply le_trans (lower (S.image pick) ?_) (Finset.card_image_le)
    intro u v e
    let a : Fin N := ⟨num u, hlt u v e⟩
    let b : Fin N := ⟨num v, hlt v u e.symm⟩
    rcases covers a b ((hadj a b).2 ⟨u,v,e,rfl,rfl⟩) with ha | hb
    · exact Or.inl (Finset.mem_image.mpr ⟨a,ha,pick_eq u v e a rfl⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨b,hb,pick_eq v u e.symm b rfl⟩)
  · intro lower S covers
    let T := S.filter (fun u => num u < N)
    let f (u : T) : Fin N := ⟨num u.val, (Finset.mem_filter.mp u.property).2⟩
    have has (u : V) (hu : u ∈ S) (i : Fin N) (hi : num u = i.val) :
        i ∈ T.attach.image f := by
      have huT : u ∈ T := Finset.mem_filter.mpr ⟨hu, hi ▸ i.isLt⟩
      exact Finset.mem_image.mpr ⟨⟨u,huT⟩, Finset.mem_attach _ _, Fin.ext hi⟩
    have hc := lower (T.attach.image f) (by
      intro a b e
      obtain ⟨u,v,edge,ha,hb⟩ := (hadj a b).1 e
      rcases covers u v edge with hu | hv
      · exact Or.inl (has u hu a ha)
      · exact Or.inr (has v hv b hb))
    have count : (T.attach.image f).card ≤ T.card := by
      simpa using (Finset.card_image_le (s := T.attach) (f := f))
    exact hc.trans (count.trans (Finset.card_filter_le _ _))
