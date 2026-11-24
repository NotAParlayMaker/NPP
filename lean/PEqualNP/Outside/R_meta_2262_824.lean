import PEqualNP.Defs
import Mathlib.Data.Nat.BitIndices

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

-- For each edge (u,v) listed in the conclusion, the larger endpoint is in 4..10.
-- Bit 7*u+(v-4) records this edge, with seven columns per vertex u.
-- A common clean AND can receive the two dirty gates at the same or opposite operands.
set_option maxHeartbeats 3500000 in
theorem PEqualNP.Outside.R_meta_2262_824 :
(let G := PEqualNP.EdgeOwnership.edgeGraph 11 ((Nat.bitIndices 2324175737840503008).map (fun k : Nat => (k / 7, k % 7 + 4)))
∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i j t : ℕ),
let T := PEqualNP.TopForm.tops G C
let Z := PEqualNP.TopForm.centreless G C
let U := PEqualNP.TopForm.Ustar G C
let r := (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
let cone := PEqualNP.EdgeOwnership.InCone 11 C
let reaches := fun (a : ℕ) (s : Fin 2) => PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C a s)
PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
PEqualNP.TopForm.junk G C = {i,j} → i < j → ¬cone i j → ¬cone j i →
t ∈ T → cone i t → cone j t →
(r = 0 ∨ U.card ≤ 2) →
17 + (T \ Z).card + 2*Z.card + r ≤ C.size + U.card →
(∀ X, PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) X → X.card ≤ (T \ Z).card) →
(∀ a ∈ T, let S := PEqualNP.TopForm.side (n := 11) C a
 (∀ v ∈ S 0, ∀ w ∈ S 1, G.Adj v w) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
(∀ e ∈ U, ∃ a ∈ T, ∃ s : Fin 2, ∃ k : ℕ,
  (k = i ∨ k = j) ∧ reaches a s k ∧ e ∈ PEqualNP.TopForm.gammaE G C a ∩ PEqualNP.TopForm.gammaE G C k) →
22 ≤ C.size) →
(∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (i j t : ℕ),
PEqualNP.TopForm.IsAO2 n C → PEqualNP.TopForm.TopForm G C → PEqualNP.TopForm.junk G C = {i,j} →
¬ PEqualNP.EdgeOwnership.InCone n C i j → t ∈ PEqualNP.TopForm.tops G C → PEqualNP.EdgeOwnership.InCone n C i t →
∃ b : Fin 2, PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C t b) i) →
(let G := PEqualNP.EdgeOwnership.edgeGraph 11 ((Nat.bitIndices 2324175737840503008).map (fun k : Nat => (k / 7, k % 7 + 4)))
∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i j t : ℕ) (b : Fin 2),
let T := PEqualNP.TopForm.tops G C
let Z := PEqualNP.TopForm.centreless G C
let U := PEqualNP.TopForm.Ustar G C
let r := (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
let cone := PEqualNP.EdgeOwnership.InCone 11 C
let reaches := fun (a : ℕ) (s : Fin 2) => PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C a s)
PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
PEqualNP.TopForm.junk G C = {i,j} → i < j → ¬cone i j → ¬cone j i →
t ∈ T → reaches t b i → reaches t (b) j →
0 < r → 3 ≤ U.card →
17 + (T \ Z).card + 2*Z.card + r ≤ C.size + U.card →
(∀ X, PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) X → X.card ≤ (T \ Z).card) →
(∀ a ∈ T, let S := PEqualNP.TopForm.side (n := 11) C a
 (∀ v ∈ S 0, ∀ w ∈ S 1, G.Adj v w) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
(∀ e ∈ U, ∃ a ∈ T, ∃ s : Fin 2, ∃ k : ℕ,
  (k = i ∨ k = j) ∧ reaches a s k ∧ e ∈ PEqualNP.TopForm.gammaE G C a ∩ PEqualNP.TopForm.gammaE G C k) →
22 ≤ C.size) →
(let G := PEqualNP.EdgeOwnership.edgeGraph 11 ((Nat.bitIndices 2324175737840503008).map (fun k : Nat => (k / 7, k % 7 + 4)))
∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i j t : ℕ) (b : Fin 2),
let T := PEqualNP.TopForm.tops G C
let Z := PEqualNP.TopForm.centreless G C
let U := PEqualNP.TopForm.Ustar G C
let r := (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
let cone := PEqualNP.EdgeOwnership.InCone 11 C
let reaches := fun (a : ℕ) (s : Fin 2) => PEqualNP.CleanedNonEdge.OrReaches 11 C (PEqualNP.TopForm.opnd C a s)
PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
PEqualNP.TopForm.junk G C = {i,j} → i < j → ¬cone i j → ¬cone j i →
t ∈ T → reaches t b i → reaches t (1-b) j →
0 < r → 3 ≤ U.card →
17 + (T \ Z).card + 2*Z.card + r ≤ C.size + U.card →
(∀ X, PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) X → X.card ≤ (T \ Z).card) →
(∀ a ∈ T, let S := PEqualNP.TopForm.side (n := 11) C a
 (∀ v ∈ S 0, ∀ w ∈ S 1, G.Adj v w) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
(∀ e ∈ U, ∃ a ∈ T, ∃ s : Fin 2, ∃ k : ℕ,
  (k = i ∨ k = j) ∧ reaches a s k ∧ e ∈ PEqualNP.TopForm.gammaE G C a ∩ PEqualNP.TopForm.gammaE G C k) →
22 ≤ C.size) →
∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∃ x21 ∈ x9, x12 x4 x21 ∧ x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  let edgeDecision {n : Nat} (es : List (Nat × Nat)) : DecidableRel (edgeGraph n es).Adj := inferInstance
  let G11 := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7), (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9)]
  intro closed extract same opposite G inst C i j hg least top
  dsimp only
  intro sides source count cover ord marked ij ji common
  change G = G11 at hg
  subst G
  have sameInstance : inst = edgeDecision _ := Subsingleton.elim _ _
  subst inst
  obtain ⟨t,ht,it,jt⟩ := common
  have rawSource : ∀ e ∈ Ustar G11 C, ∃ a ∈ tops G11 C, ∃ s : Fin 2, ∃ k : Nat,
      (k=i ∨ k=j) ∧ OrReaches 11 C (opnd C a s) k ∧ e ∈ gammaE G11 C a ∩ gammaE G11 C k := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      obtain ⟨a,ha,s,k,hk,onA,hit,onK⟩ := source u v he
      have edgeMem := (Finset.mem_sdiff.mp he).1
      refine ⟨a,ha,s,k,hk,hit,Finset.mem_inter.mpr ⟨?_,?_⟩⟩
      · exact Finset.mem_filter.mpr ⟨edgeMem,u,v,rfl,onA⟩
      · exact Finset.mem_filter.mpr ⟨edgeMem,u,v,rfl,onK⟩
  by_cases small : (orN G11 C \ lam G11 C).card = 0 ∨ (Ustar G11 C).card ≤ 2
  · exact closed C i j t least top marked ord ij ji ht it jt small count cover sides rawSource
  obtain ⟨b,hb⟩ := extract 11 G11 C i j t least.1 top marked ij ht it
  obtain ⟨d,hd⟩ := extract 11 G11 C j i t least.1 top (marked.trans (Finset.pair_comm _ _)) ji ht jt
  have rPos : 0 < (orN G11 C \ lam G11 C).card := by omega
  have uLarge : 3 ≤ (Ustar G11 C).card := by omega
  by_cases eq : b = d
  · subst d
    exact same C i j t b least top marked ord ij ji ht hb hd rPos uLarge count cover sides rawSource
  · have other : d = 1-b := by fin_cases b <;> fin_cases d <;> first | rfl | contradiction
    subst d
    exact opposite C i j t b least top marked ord ij ji ht hb hd rPos uLarge count cover sides rawSource
