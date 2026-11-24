import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Removing the top ANDs leaves OR unions over the eleven inputs and two designated wires.
-- Count the union gates, both designated ANDs and the top ANDs with their output OR tree.
theorem PEqualNP.Outside.R_meta_2264_813
  (normalize : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (p q : ℕ),
    G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C → p < q → junk G C = {p,q} →
    ¬ InCone 11 C p q → ¬ InCone 11 C q p →
    (∀ a ∈ tops G C, InCone 11 C p a → ¬ InCone 11 C q a) →
    ∃ (R : Finset ℕ) (S : ℕ → Finset (Fin 11 ⊕ Bool)) (A : Bool → Fin 2 → ℕ) (B : ℕ → Fin 2 → ℕ),
      let T := tops G C
      R.card + 2*T.card + 1 ≤ C.size ∧
      (let avail := fun w => w < 13 ∨ w ∈ R
      let hit := fun (x : Fin 11 → Bool) (d : Bool → Bool) w =>
        ∃ z ∈ S w, Sum.elim x d z = true
      let D := fun (x : Fin 11 → Bool) (b : Bool) =>
        decide (hit x (fun _ => false) (A b 0) ∧ hit x (fun _ => false) (A b 1))
      (∀ z, S (Sum.elim Fin.val (fun d : Bool => 11+d.toNat) z) = {z}) ∧
      (∀ r ∈ R, 13 ≤ r ∧ ∃ u < r, ∃ v < r, avail u ∧ avail v ∧ S r = S u ∪ S v) ∧
      (∀ d b, avail (A d b) ∧ ∀ c : Bool, Sum.inr c ∉ S (A d b)) ∧
      (∀ a ∈ T, ∀ b, avail (B a b)) ∧
      (∀ a ∈ T, ∀ b c, Sum.inr false ∈ S (B a b) → Sum.inr true ∉ S (B a c)) ∧
      (∀ a ∈ T, ∀ d : Bool, Sum.inr d ∈ S (B a 0) → Sum.inr d ∉ S (B a 1)) ∧
      (∀ d, ∃ x, graphFun G ∅ x = false ∧ D x d = true) ∧
      (∀ x, (∃ a ∈ T, hit x (D x) (B a 0) ∧ hit x (D x) (B a 1)) ↔ graphFun G ∅ x = true)))
  (exclude : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (R T : Finset ℕ)
    (S : ℕ → Finset (Fin 11 ⊕ Bool)) (A : Bool → Fin 2 → ℕ) (B : ℕ → Fin 2 → ℕ),
    G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
    R.card + 2*T.card + 1 ≤ 21 →
    (let avail := fun w => w < 13 ∨ w ∈ R
      let hit := fun (x : Fin 11 → Bool) (d : Bool → Bool) w =>
        ∃ z ∈ S w, Sum.elim x d z = true
      let D := fun (x : Fin 11 → Bool) (b : Bool) =>
        decide (hit x (fun _ => false) (A b 0) ∧ hit x (fun _ => false) (A b 1))
      (∀ z, S (Sum.elim Fin.val (fun d : Bool => 11+d.toNat) z) = {z}) ∧
      (∀ r ∈ R, 13 ≤ r ∧ ∃ u < r, ∃ v < r, avail u ∧ avail v ∧ S r = S u ∪ S v) ∧
      (∀ d b, avail (A d b) ∧ ∀ c : Bool, Sum.inr c ∉ S (A d b)) ∧
      (∀ a ∈ T, ∀ b, avail (B a b)) ∧
      (∀ a ∈ T, ∀ b c, Sum.inr false ∈ S (B a b) → Sum.inr true ∉ S (B a c)) ∧
      (∀ a ∈ T, ∀ d : Bool, Sum.inr d ∈ S (B a 0) → Sum.inr d ∉ S (B a 1)) ∧
      (∀ d, ∃ x, graphFun G ∅ x = false ∧ D x d = true) ∧
      (∀ x, (∃ a ∈ T, hit x (D x) (B a 0) ∧ hit x (D x) (B a 1)) ↔ graphFun G ∅ x = true)) → False) :
  ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∀ x21 ∈ x9, x12 x4 x21 → ¬x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  classical
  intro G inst C p q hg hL hT
  dsimp only
  intro _ _ _ _ hpq hj hp hq apart
  by_contra! short
  have edge : G.Adj 0 9 := by
    rw [hg]
    decide +kernel
  have hne : G.edgeFinset.Nonempty := ⟨s((0 : Fin 11), (9 : Fin 11)), SimpleGraph.mem_edgeFinset.mpr edge⟩
  obtain ⟨R, S, A, B, hsize, plan⟩ := normalize G C p q hne hL hT hpq hj hp hq apart
  exact exclude G R (tops G C) S A B hg (by omega) plan
