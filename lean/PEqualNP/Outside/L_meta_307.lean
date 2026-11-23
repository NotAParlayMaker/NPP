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
  intro V G0 N num G' hlt hinj hG' c
  constructor
  · intro h0 S' hS'
    let T : Finset (Fin N) := S'.filter (fun a => ∃ u v, G0.Adj u v ∧ num u = a.val)
    let pick : {a // a ∈ T} → V := fun x =>
      Classical.choose ((Finset.mem_filter.1 (show x.1 ∈ S'.filter _ from x.2)).2)
    let S : Finset V := T.attach.image pick
    have hS : ∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S := by
      intro u v huv
      have hvu : G0.Adj v u := (SimpleGraph.adj_comm G0 u v).1 huv
      let a : Fin N := ⟨num u, hlt u v huv⟩
      let b : Fin N := ⟨num v, hlt v u hvu⟩
      have hab : G'.Adj a b := (hG' a b).2 ⟨u, v, huv, rfl, rfl⟩
      rcases hS' a b hab with ha | hb
      · left
        have haT : a ∈ T := Finset.mem_filter.2 ⟨ha, ⟨u, v, huv, rfl⟩⟩
        rw [Finset.mem_image]
        refine ⟨⟨a, haT⟩, Finset.mem_attach _ _, ?_⟩
        rcases Classical.choose_spec
          ((Finset.mem_filter.1 (show a ∈ S'.filter _ from haT)).2) with ⟨v', huv', hnum'⟩
        exact hinj _ v' u v huv' huv hnum'
      · right
        have hbT : b ∈ T := Finset.mem_filter.2 ⟨hb, ⟨v, u, hvu, rfl⟩⟩
        rw [Finset.mem_image]
        refine ⟨⟨b, hbT⟩, Finset.mem_attach _ _, ?_⟩
        rcases Classical.choose_spec
          ((Finset.mem_filter.1 (show b ∈ S'.filter _ from hbT)).2) with ⟨v', huv', hnum'⟩
        exact hinj _ v' v u huv' hvu hnum'
    have hcard : S.card ≤ S'.card := by
      calc S.card
          ≤ T.attach.card := Finset.card_image_le
        _ = T.card := Finset.card_attach
        _ ≤ S'.card := Finset.card_filter_le _ _
    exact le_trans (h0 S hS) hcard
  · intro h' S hS
    let S1 : Finset V := S.filter (fun u => num u < N)
    let push : {u // u ∈ S1} → Fin N := fun x =>
      ⟨num x.1, (Finset.mem_filter.1 (show x.1 ∈ S.filter (fun u => num u < N) from x.2)).2⟩
    let S' : Finset (Fin N) := S1.attach.image push
    have hS' : ∀ a b, G'.Adj a b → a ∈ S' ∨ b ∈ S' := by
      intro a b hab
      rcases (hG' a b).1 hab with ⟨u, v, huv, hnu, hnv⟩
      rcases hS u v huv with hu | hv
      · left
        have hu1 : u ∈ S1 := Finset.mem_filter.2 ⟨hu, by omega⟩
        rw [Finset.mem_image]
        refine ⟨⟨u, hu1⟩, Finset.mem_attach _ _, ?_⟩
        exact Fin.ext hnu
      · right
        have hv1 : v ∈ S1 := Finset.mem_filter.2 ⟨hv, by omega⟩
        rw [Finset.mem_image]
        refine ⟨⟨v, hv1⟩, Finset.mem_attach _ _, ?_⟩
        exact Fin.ext hnv
    have hcard : S'.card ≤ S.card := by
      calc S'.card
          ≤ S1.attach.card := Finset.card_image_le
        _ = S1.card := Finset.card_attach
        _ ≤ S.card := Finset.card_filter_le _ _
    exact le_trans (h' S' hS') hcard
