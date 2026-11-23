import Mathlib.Combinatorics.SimpleGraph.Basic

theorem PEqualNP.Outside.L_meta_473 : ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)) (T0 : Finset V) (T1 : Finset (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → (∀ u ∈ T0, ∃ v, G0.Adj u v) → (∀ a : Fin N, a ∈ T1 ↔ ∃ u ∈ T0, num u = a.val) → (∀ u v, G0.Adj u v → u ∈ T0 ∨ v ∈ T0) → (∀ a b, G'.Adj a b → a ∈ T1 ∨ b ∈ T1) ∧ T1.card = T0.card := by
  classical
  intro V G0 N num G' T0 T1 hBound hInject hGraph hIncident hMembers hCover
  constructor
  · intro a b hab
    obtain ⟨u, v, huv, ha, hb⟩ := (hGraph a b).mp hab
    rcases hCover u v huv with hu | hv
    · left
      exact (hMembers a).mpr ⟨u, hu, ha⟩
    · right
      exact (hMembers b).mpr ⟨v, hv, hb⟩
  · let f : T0 → Fin N := fun u =>
      ⟨num u.val, by
        obtain ⟨v, huv⟩ := hIncident u.val u.property
        exact hBound u.val v huv⟩
    let e : T0 → T1 := fun u =>
      ⟨f u, (hMembers (f u)).mpr ⟨u.val, u.property, rfl⟩⟩
    have heinj : Function.Injective e := by
      intro u w he
      apply Subtype.ext
      have hnum : num u.val = num w.val :=
        congrArg (fun a : T1 => (a.val : Fin N).val) he
      obtain ⟨v, huv⟩ := hIncident u.val u.property
      obtain ⟨z, hwz⟩ := hIncident w.val w.property
      exact hInject u.val v w.val z huv hwz hnum
    have hesurj : Function.Surjective e := by
      intro a
      obtain ⟨u, hu, heq⟩ := (hMembers a.val).mp a.property
      refine ⟨⟨u, hu⟩, ?_⟩
      apply Subtype.ext
      apply Fin.ext
      exact heq
    have hcard : Fintype.card T0 = Fintype.card T1 :=
      Fintype.card_congr (Equiv.ofBijective e ⟨heinj, hesurj⟩)
    simpa using hcard.symm
