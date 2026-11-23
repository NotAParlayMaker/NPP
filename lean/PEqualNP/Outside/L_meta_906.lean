import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906.Six

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  congr 1
  apply propext
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

theorem sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

theorem fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : ℕ, ∀ i : Fin C.size, i.val < d →
      gateValFuel C U (d + 1) i = gateValFuel C U d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    show (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U (d + 1)) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U (d + 1))) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d))
    have hc : ∀ j : Fin C.size, j < i → gateValFuel C U (d + 1) j = gateValFuel C U d j := by
      intro j hji
      apply ih
      have : j.val < i.val := hji
      omega
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]

theorem gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h := fuel_succ C U C.size i i.isLt
  exact h.symm

theorem gateVal_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔
      (((∃ x ∈ C.leftVars i, x ∈ U) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true) ∧
       ((∃ x ∈ C.rightVars i, x ∈ U) ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal U j = true)) := by
  rw [gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]

theorem eval_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔
      ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff






open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

variable {n : ℕ} (C : AndCountCircuit n)

def pickVars (b : Fin C.size → Bool) (i : Fin C.size) :=
  if b i then C.rightVars i else C.leftVars i

def pickGates (b : Fin C.size → Bool) (i : Fin C.size) :=
  if b i then C.rightGates i else C.leftGates i

def active (b : Fin C.size → Bool) (i : Fin C.size) : Prop :=
  ∀ P : Fin C.size → Prop, (∀ k ∈ C.outGates, P k) →
    (∀ k, P k → ∀ j < k, j ∈ pickGates C b k → P j) → P i

theorem active_out (b : Fin C.size → Bool) (i : Fin C.size) (hi : i ∈ C.outGates) :
    active C b i := fun _ h _ => h i hi

theorem active_step (b : Fin C.size → Bool) {i j : Fin C.size} (hi : active C b i)
    (hji : j < i) (hj : j ∈ pickGates C b i) : active C b j :=
  fun P ho hs => hs i (hi P ho hs) j hji hj

noncomputable def clause (b : Fin C.size → Bool) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => v ∈ C.outVars ∨ ∃ i, active C b i ∧ v ∈ pickVars C b i)

theorem mem_clause (b : Fin C.size → Bool) (v : Fin n) :
    v ∈ clause C b ↔ v ∈ C.outVars ∨ ∃ i, active C b i ∧ v ∈ pickVars C b i := by
  classical
  simp [clause]

theorem pick_hit (b : Fin C.size → Bool) (U : Finset (Fin n)) (i : Fin C.size)
    (h : C.gateVal U i = true) :
    (∃ v ∈ pickVars C b i, v ∈ U) ∨ ∃ j ∈ pickGates C b i, j < i ∧ C.gateVal U j = true := by
  have ht := (gateVal_iff C U i).1 h
  cases he : b i with
  | false => simpa [pickVars, pickGates, he] using ht.1
  | true => simpa [pickVars, pickGates, he] using ht.2

theorem clause_hits (b : Fin C.size → Bool) (U : Finset (Fin n)) (h : C.eval U = true) :
    ∃ v ∈ clause C b, v ∈ U := by
  have aux : ∀ k : ℕ, ∀ i : Fin C.size, i.val = k → active C b i → C.gateVal U i = true →
      ∃ v ∈ clause C b, v ∈ U := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      rintro i rfl hi hv
      rcases pick_hit C b U i hv with ⟨v, hp, hu⟩ | ⟨j, hj, hji, hvj⟩
      · exact ⟨v, (mem_clause C b v).2 (Or.inr ⟨i, hi, hp⟩), hu⟩
      · exact ih j.val hji j rfl (active_step C b hi hji hj) hvj
  rcases (eval_iff C U).1 h with ⟨v, ho, hu⟩ | ⟨j, ho, hv⟩
  · exact ⟨v, (mem_clause C b v).2 (Or.inl ho), hu⟩
  · exact aux _ j rfl (active_out C b j ho) hv

def falseMask (U : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U)

theorem falseMask_miss (U : Finset (Fin n)) (i : Fin C.size) (h : C.gateVal U i ≠ true) :
    ¬ ((∃ v ∈ pickVars C (falseMask C U) i, v ∈ U) ∨
      ∃ j ∈ pickGates C (falseMask C U) i, j < i ∧ C.gateVal U j = true) := by
  cases he : falseMask C U i with
  | false =>
    simp only [pickVars, pickGates, he, Bool.false_eq_true, ite_false]
    intro hp
    exact Bool.noConfusion (he.symm.trans ((sideTrue_iff ..).2 hp))
  | true =>
    simp only [pickVars, pickGates, he, ite_true]
    intro hp
    exact h ((gateVal_iff C U i).2 ⟨(sideTrue_iff ..).1 he, hp⟩)

theorem clause_misses (U : Finset (Fin n)) (h : C.eval U ≠ true) :
    ∀ v ∈ clause C (falseMask C U), v ∉ U := by
  have ho := mt (eval_iff C U).2 h
  have ha : ∀ i, active C (falseMask C U) i → C.gateVal U i ≠ true := by
    intro i hi
    apply hi
    · intro j hj hv
      exact ho (Or.inr ⟨j, hj, hv⟩)
    · intro k hk j hj hg hv
      exact falseMask_miss C U k hk (Or.inr ⟨j, hg, hj, hv⟩)
  intro v hv hu
  rcases (mem_clause ..).1 hv with h1 | ⟨i, hi, hp⟩
  · exact ho (Or.inl ⟨v, h1, hu⟩)
  · exact falseMask_miss C U i (ha i hi) (Or.inl ⟨v, hp, hu⟩)




open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit


theorem boundary_clause {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n))
    (hf : C.eval I = false)
    (hp : ∀ u, u ∉ I → C.eval (insert u I) = true) :
    clause C (falseMask C I) = Iᶜ := by
  classical
  have hm := clause_misses C I (by simp [hf])
  ext v
  constructor
  · exact fun hv => Finset.mem_compl.mpr (hm v hv)
  · intro hv
    obtain ⟨x, hx, hxu⟩ := clause_hits C (falseMask C I) _ (hp v (Finset.mem_compl.mp hv))
    rcases Finset.mem_insert.mp hxu with rfl | hxi
    · exact hx
    · exact (hm x hx hxi).elim

theorem boundary_count {n : ℕ} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (h : ∀ I ∈ F, C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) :
    F.card ≤ 2 ^ C.size := by
  classical
  calc
    _ ≤ (Finset.univ : Finset (Fin C.size → Bool)).card := by
      apply Finset.card_le_card_of_injOn (falseMask C)
      · exact fun _ _ => Finset.mem_univ _
      · intro I hI J hJ heq
        have hh := congrArg (clause C) heq
        rw [boundary_clause C I (h I hI).1 (h I hI).2,
          boundary_clause C J (h J hJ).1 (h J hJ).2] at hh
        exact compl_injective hh
    _ = _ := by simp



def maxFamily {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] :
    Finset (Finset (Fin m)) :=
  Finset.univ.filter fun I =>
    (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧
    (∀ w : Fin m, w ∉ I → ∃ a ∈ I, G.Adj a w)

def admissible {m : ℕ} (G : SimpleGraph (Fin m)) (D : AndCountCircuit m) : Prop :=
  ∀ I : Finset (Fin m), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
    (∀ w : Fin m, w ∉ I → ∃ a ∈ I, G.Adj a w) →
    D.eval I = false ∧ ∀ w : Fin m, w ∉ I → D.eval (insert w I) = true

theorem family_lower {m k : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (hcard : 2 ^ k < (maxFamily G).card)
    (D : AndCountCircuit m) (_hw : D.WellFormed) (h : admissible G D) :
    k + 1 ≤ D.size := by
  have hc := boundary_count D (maxFamily G) (by
    intro I hI
    obtain ⟨hi, hd⟩ := (Finset.mem_filter.mp hI).2
    exact h I hi hd)
  by_contra! hbad
  have hk : D.size ≤ k := by omega
  have hp : 2 ^ D.size ≤ (2 : ℕ) ^ k := Nat.pow_le_pow_right (by decide) hk
  omega

abbrev graphFrom (m : ℕ) (edges : List (ℕ × ℕ)) :=
  SimpleGraph.fromRel (fun a b : Fin m => ((a : ℕ), (b : ℕ)) ∈ edges)

theorem lo6 (G : SimpleGraph (Fin 6))
    (hG : G = graphFrom 6 [(0,1),(1,2),(0,2),(3,4),(4,5),(3,5)]) :
    ∀ C : AndCountCircuit 6, C.WellFormed → admissible G C → 4 ≤ C.size := by
  subst G
  apply family_lower (k := 3)
  decide

theorem lo5 (G : SimpleGraph (Fin 5))
    (hG : G = graphFrom 5 [(0,1),(1,2),(2,3),(3,4),(4,0)]) :
    ∀ C : AndCountCircuit 5, C.WellFormed → admissible G C → 3 ≤ C.size := by
  subst G
  apply family_lower (k := 2)
  decide

theorem lo7 (G : SimpleGraph (Fin 7))
    (hG : G = graphFrom 7 [(0,2),(0,3),(1,3),(1,4),(2,4),(2,5),(3,5),(3,6),
      (4,6),(4,0),(5,0),(5,1),(6,1),(6,2)]) :
    ∀ C : AndCountCircuit 7, C.WellFormed → admissible G C → 3 ≤ C.size := by
  subst G
  apply family_lower (k := 2)
  decide

end PEqualNP.Outside.L_meta_906.Six

namespace PEqualNP.Outside.L_meta_906.Two

open PEqualNP.AndCount

private def C6 : AndCountCircuit 6 where
  size := 4
  leftVars := ![{0}, {1}, {3}, {4}]
  rightVars := ![{1, 2}, {2}, {4, 5}, {5}]
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

private def C5 : AndCountCircuit 5 where
  size := 3
  leftVars := ![{0}, {2}, {4}]
  rightVars := ![{4, 1}, {1, 3}, {3}]
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

private def C7 : AndCountCircuit 7 where
  size := 3
  leftVars := ![{2, 5}, {3, 4}, {5, 6}]
  rightVars := ![{0, 4}, {0, 1, 6}, {1, 2, 3}]
  leftGates := ![∅, {0}, {0, 1}]
  rightGates := ![∅, ∅, {1}]
  outVars := ∅
  outGates := {2}

def correctRows {n : ℕ} (C : AndCountCircuit n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun I => C.eval I = false ∧
    ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true

theorem fromRows {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : AndCountCircuit n) (h : Six.maxFamily G ⊆ correctRows C) :
    ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
      (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true := by
  intro I hi hd
  have hm : I ∈ Six.maxFamily G := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hd⟩
  exact (Finset.mem_filter.mp (h hm)).2

private abbrev upper {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ C : AndCountCircuit n, C.WellFormed ∧ C.size ≤ k ∧
    ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
      (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true


private abbrev rows {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) :=
  ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
      (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true

private theorem checkRows {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (inst : DecidableRel G.Adj)
    (ok : decide (rows G C) = true) : rows G C := of_decide_eq_true ok

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem up6 (G : SimpleGraph (Fin 6))
    (h : G = SimpleGraph.fromRel (fun a b : Fin 6 =>
      ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] :
        List (ℕ × ℕ)))) : upper G 4 := by
  subst G
  refine ⟨C6, ?_, by decide, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide
  · apply fromRows
    decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem up5 (G : SimpleGraph (Fin 5))
    (h : G = SimpleGraph.fromRel (fun a b : Fin 5 =>
      ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] :
        List (ℕ × ℕ)))) : upper G 3 := by
  subst G
  refine ⟨C5, ?_, by decide, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide
  · apply fromRows
    decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem up7 (G : SimpleGraph (Fin 7))
    (h : G = SimpleGraph.fromRel (fun a b : Fin 7 =>
      ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5),
        (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] :
        List (ℕ × ℕ)))) : upper G 3 := by
  subst G
  refine ⟨C7, ?_, by decide, ?_⟩
  · unfold AndCountCircuit.WellFormed
    decide
  · apply fromRows
    decide

end PEqualNP.Outside.L_meta_906.Two

open PEqualNP.Outside.L_meta_906 in
theorem PEqualNP.Outside.L_meta_906 : (∀ G : SimpleGraph (Fin 6), G = SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 6, C.WellFormed ∧ C.size ≤ 4 ∧
    (∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 6, C.WellFormed →
    (∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true) →
    4 ≤ C.size) ∧
(∀ G : SimpleGraph (Fin 5), G = SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed →
    (∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true) →
    3 ≤ C.size) ∧
(∀ G : SimpleGraph (Fin 7), G = SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed →
    (∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true) →
    3 ≤ C.size) := by
  refine ⟨?_, ?_, ?_⟩
  · intro G hG
    exact ⟨Two.up6 G hG, Six.lo6 G hG⟩
  · intro G hG
    exact ⟨Two.up5 G hG, Six.lo5 G hG⟩
  · intro G hG
    exact ⟨Two.up7 G hG, Six.lo7 G hG⟩
