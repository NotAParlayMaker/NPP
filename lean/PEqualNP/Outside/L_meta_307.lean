import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

theorem PEqualNP.Outside.L_meta_307 :
    ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)),
      (∀ u v, G0.Adj u v → num u < N) →
      (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) →
      (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) →
      ∀ c : ℕ,
        (∀ S : Finset V, (∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S) → c ≤ S.card) ↔
        (∀ S : Finset (Fin N), (∀ a b, G'.Adj a b → a ∈ S ∨ b ∈ S) → c ≤ S.card) := by
  intro V G0 N num G' hlt hinj hadj c
  classical
  constructor
  · intro h0 S hS
    let f : Fin N → Finset V := fun a =>
      if h : ∃ u : V, (∃ v : V, G0.Adj u v) ∧ num u = a.val then {Classical.choose h} else ∅
    let T : Finset V := S.biUnion f
    have hTcov : ∀ u v, G0.Adj u v → u ∈ T ∨ v ∈ T := by
      intro u v huv
      let a : Fin N := ⟨num u, hlt u v huv⟩
      let b : Fin N := ⟨num v, hlt v u (G0.symm.symm _ _ huv)⟩
      have hab : G'.Adj a b := (hadj a b).mpr ⟨u, v, huv, rfl, rfl⟩
      rcases hS a b hab with ha | hb
      · left
        refine Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩
        have hex : ∃ u' : V, (∃ v' : V, G0.Adj u' v') ∧ num u' = a.val := ⟨u, ⟨v, huv⟩, rfl⟩
        simp only [f, hex, ↓reduceDIte, Finset.mem_singleton]
        rcases Classical.choose_spec hex with ⟨⟨v', hv'⟩, hnum⟩
        exact hinj u v (Classical.choose hex) v' huv hv' hnum.symm
      · right
        refine Finset.mem_biUnion.mpr ⟨b, hb, ?_⟩
        have hex : ∃ u' : V, (∃ v' : V, G0.Adj u' v') ∧ num u' = b.val :=
          ⟨v, ⟨u, G0.symm.symm _ _ huv⟩, rfl⟩
        simp only [f, hex, ↓reduceDIte, Finset.mem_singleton]
        rcases Classical.choose_spec hex with ⟨⟨v', hv'⟩, hnum⟩
        exact hinj v u (Classical.choose hex) v' (G0.symm.symm _ _ huv) hv' hnum.symm
    have hcard : T.card ≤ S.card := by
      calc T.card ≤ ∑ a ∈ S, (f a).card := Finset.card_biUnion_le
        _ ≤ ∑ _a ∈ S, 1 := by
            refine Finset.sum_le_sum fun a _ => ?_
            dsimp only [f]
            split_ifs <;> simp
        _ = S.card := by simp
    exact (h0 T hTcov).trans hcard
  · intro h' S hS
    let g : V → Finset (Fin N) := fun u =>
      if h : num u < N then {⟨num u, h⟩} else ∅
    let T : Finset (Fin N) := S.biUnion g
    have hTcov : ∀ a b, G'.Adj a b → a ∈ T ∨ b ∈ T := by
      intro a b hab
      rcases (hadj a b).mp hab with ⟨u, v, huv, hnu, hnv⟩
      rcases hS u v huv with hu | hv
      · left
        refine Finset.mem_biUnion.mpr ⟨u, hu, ?_⟩
        have hlt_u : num u < N := hlt u v huv
        simp only [g, hlt_u, ↓reduceDIte, Finset.mem_singleton]
        exact Fin.ext hnu.symm
      · right
        refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
        have hlt_v : num v < N := hlt v u (G0.symm.symm _ _ huv)
        simp only [g, hlt_v, ↓reduceDIte, Finset.mem_singleton]
        exact Fin.ext hnv.symm
    have hcard : T.card ≤ S.card := by
      calc T.card ≤ ∑ u ∈ S, (g u).card := Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ S, 1 := by
            refine Finset.sum_le_sum fun u _ => ?_
            dsimp only [g]
            split_ifs <;> simp
        _ = S.card := by simp
    exact (h' T hTcov).trans hcard
