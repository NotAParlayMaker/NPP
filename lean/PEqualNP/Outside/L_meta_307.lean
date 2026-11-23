import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_307 :
    ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)),
      (∀ u v, G0.Adj u v → num u < N) →
      (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) →
      (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) →
      ∀ c : ℕ, (∀ S : Finset V, (∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S) → c ≤ S.card) ↔
        (∀ S : Finset (Fin N), (∀ a b, G'.Adj a b → a ∈ S ∨ b ∈ S) → c ≤ S.card) := by
  classical
  intro V G0 N num G' bounded injective edges c
  let isEndpoint := fun u : V => ∃ v, G0.Adj u v
  let label : Subtype isEndpoint ↪ Fin N :=
    { toFun := fun u => ⟨num u.val, by
        obtain ⟨v, huv⟩ := u.property
        exact bounded u.val v huv⟩
      inj' := by
        intro u w equalLabels
        obtain ⟨v, huv⟩ := u.property
        obtain ⟨z, hwz⟩ := w.property
        exact Subtype.ext (injective u.val v w.val z huv hwz (congrArg Fin.val equalLabels)) }
  constructor
  · intro lowerOriginal T coversT
    let endpointsInT := T.preimage label label.injective.injOn
    let forget : Subtype isEndpoint ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    let S := endpointsInT.map forget
    have coversS : ∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S := by
      intro u v huv
      let u' : Subtype isEndpoint := ⟨u, v, huv⟩
      let v' : Subtype isEndpoint := ⟨v, u, huv.symm⟩
      have hadj : G'.Adj (label u') (label v') :=
        (edges _ _).mpr ⟨u, v, huv, rfl, rfl⟩
      exact (coversT _ _ hadj).imp
        (fun hu => Finset.mem_map.mpr ⟨u', Finset.mem_preimage.mpr hu, rfl⟩)
        (fun hv => Finset.mem_map.mpr ⟨v', Finset.mem_preimage.mpr hv, rfl⟩)
    calc
      c ≤ S.card := lowerOriginal S coversS
      _ = endpointsInT.card := Finset.card_map forget
      _ ≤ T.card := by
        apply Finset.card_le_card_of_injOn label _ label.injective.injOn
        intro u hu
        exact Finset.mem_preimage.mp hu
  · intro lowerLabelled S coversS
    let endpointsInS := S.subtype isEndpoint
    let T := endpointsInS.map label
    have coversT : ∀ a b, G'.Adj a b → a ∈ T ∨ b ∈ T := by
      intro a b hab
      obtain ⟨u, v, huv, hu, hv⟩ := (edges a b).mp hab
      let u' : Subtype isEndpoint := ⟨u, v, huv⟩
      let v' : Subtype isEndpoint := ⟨v, u, huv.symm⟩
      exact (coversS u v huv).imp
        (fun h => Finset.mem_map.mpr ⟨u', Finset.mem_subtype.mpr h, Fin.ext hu⟩)
        (fun h => Finset.mem_map.mpr ⟨v', Finset.mem_subtype.mpr h, Fin.ext hv⟩)
    calc
      c ≤ T.card := lowerLabelled T coversT
      _ = endpointsInS.card := Finset.card_map label
      _ = (S.filter isEndpoint).card := Finset.card_subtype isEndpoint S
      _ ≤ S.card := Finset.card_filter_le S isEndpoint
