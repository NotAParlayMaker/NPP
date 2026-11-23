import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_307 :
    ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)),
      (∀ u v, G0.Adj u v → num u < N) →
      (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) →
      (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) →
      ∀ c : ℕ,
        (∀ S : Finset V, (∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S) → c ≤ S.card) ↔
        (∀ S : Finset (Fin N), (∀ a b, G'.Adj a b → a ∈ S ∨ b ∈ S) → c ≤ S.card) := by
  classical
  intro V G0 N num G' bounded injectiveOnEdges adj_iff c
  constructor
  · intro lowerBound S covers
    let T := S.filter fun a => ∃ u v, G0.Adj u v ∧ num u = a.val
    have hasPreimage (a : {a // a ∈ T}) : ∃ u v, G0.Adj u v ∧ num u = a.val.val :=
      (Finset.mem_filter.mp a.property).2
    let lift (a : {a // a ∈ T}) : V := Classical.choose (hasPreimage a)
    let U := T.attach.image lift
    have memLift (u v : V) (edge : G0.Adj u v)
        (ha : (⟨num u, bounded u v edge⟩ : Fin N) ∈ S) : u ∈ U := by
      let a : {a // a ∈ T} :=
        ⟨⟨num u, bounded u v edge⟩, Finset.mem_filter.mpr ⟨ha, u, v, edge, rfl⟩⟩
      obtain ⟨w, hw, hnum⟩ := Classical.choose_spec (hasPreimage a)
      exact Finset.mem_image.mpr
        ⟨a, Finset.mem_attach T a, injectiveOnEdges (lift a) w u v hw edge hnum⟩
    have coversU : ∀ u v, G0.Adj u v → u ∈ U ∨ v ∈ U := by
      intro u v edge
      have placedEdge : G'.Adj ⟨num u, bounded u v edge⟩ ⟨num v, bounded v u edge.symm⟩ :=
        (adj_iff _ _).2 ⟨u, v, edge, rfl, rfl⟩
      exact (covers _ _ placedEdge).imp (memLift u v edge) (memLift v u edge.symm)
    calc
      c ≤ U.card := lowerBound U coversU
      _ ≤ T.attach.card := Finset.card_image_le
      _ = T.card := Finset.card_attach
      _ ≤ S.card := Finset.card_filter_le _ _
  · intro lowerBound S covers
    let T := S.filter fun u => num u < N
    let place (u : {u // u ∈ T}) : Fin N :=
      ⟨num u.val, (Finset.mem_filter.mp u.property).2⟩
    let U := T.attach.image place
    have memPlace (u v : V) (edge : G0.Adj u v) (a : Fin N)
        (ha : num u = a.val) (hu : u ∈ S) : a ∈ U := by
      let point : {u // u ∈ T} := ⟨u, Finset.mem_filter.mpr ⟨hu, bounded u v edge⟩⟩
      exact Finset.mem_image.mpr ⟨point, Finset.mem_attach T point, Fin.ext ha⟩
    have coversU : ∀ a b, G'.Adj a b → a ∈ U ∨ b ∈ U := by
      intro a b edge
      obtain ⟨u, v, huv, hu, hv⟩ := (adj_iff a b).1 edge
      exact (covers u v huv).imp (memPlace u v huv a hu) (memPlace v u huv.symm b hv)
    calc
      c ≤ U.card := lowerBound U coversU
      _ ≤ T.attach.card := Finset.card_image_le
      _ = T.card := Finset.card_attach
      _ ≤ S.card := Finset.card_filter_le _ _
