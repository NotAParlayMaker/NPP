import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first child permits unrestricted use of the first two monotone gates.
-- With an initial inverter it permits unrestricted use of that first gate.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_4938_423
  (tree : ∀ (P C : Circuit) (a b : ℕ),
    ((P.size = 2 ∧ Monotone2 P) ∨ (P.size = 1 ∧ FanInTwo P)) → Monotone2 C →
    (∀ i,10 + P.size ≤ i → ([a,b] ++ C.gates.flatMap Gate.inputs).count i ≤ 1) →
    let G := fun x : Fin 10 → Bool => ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
    let W := fun (x : Fin 10 → Bool) (j : ℕ) => (C.wires (P.wires (List.ofFn x))).getD j false
    (∀ x,(W x a || W x b) = G x) → 18 ≤ P.size+C.size)
  (rest : ∀ (t : Gate) (C : Circuit) (a b : ℕ),
    FanInTwo (Circuit.mk [t] 0) → FanInTwo C → C.size ≤ 16 →
    ((∃ g ∈ C.gates,g.op = .not) ∨ ∃ i,11 ≤ i ∧ (12 ≤ i ∨ t.op = .not) ∧ 2 ≤ ([a,b] ++ C.gates.flatMap Gate.inputs).count i) →
    let G := fun x : Fin 10 → Bool => ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
    let W := fun (x : Fin 10 → Bool) (j : ℕ) => (C.wires ((Circuit.mk [t] 0).wires (List.ofFn x))).getD j false
    (∃ x,W x a = true ∧ W x b = false) → (∃ x,W x a = false ∧ W x b = true) →
    ¬ ∀ x,(W x a || W x b)=G x) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (16 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro t C a b ht hc lim
  dsimp only
  let W := fun (x : Fin 10 → Bool) (j : ℕ) => (C.wires ((Circuit.mk [t] 0).wires (List.ofFn x))).getD j false
  let G := fun x : Fin 10 → Bool => ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)
  intro left right off
  by_contra fail
  have expand (x : Fin 10 → Bool) : G x = (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))) := by
    simp only [G,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
  have compute (x : Fin 10 → Bool) : (W x a || W x b)=G x := by
    rw [expand]
    cases e : (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)))
    · obtain ⟨ha,hb⟩ := off x e
      change W x a=false at ha
      change W x b=false at hb
      rw [ha,hb]; rfl
    · cases h : W x a || W x b
      · obtain ⟨ha,hb⟩ := Bool.or_eq_false_iff.mp h
        exact (fail ⟨x,e,ha,hb⟩).elim
      · rfl
  by_cases bad : (∃ g ∈ C.gates,g.op = .not) ∨ ∃ i,11 ≤ i ∧ (12 ≤ i ∨ t.op = .not) ∧ 2 ≤ ([a,b] ++ C.gates.flatMap Gate.inputs).count i
  · exact rest t C a b ht hc lim bad left right compute
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨hop,len⟩ := hc g hg
    rcases hop with h|h|h
    · exact ⟨Or.inl h,len⟩
    · exact ⟨Or.inr h,len⟩
    · exact (bad (Or.inl ⟨g,hg,h⟩)).elim
  by_cases one : ∀ i,11 ≤ i → ([a,b] ++ C.gates.flatMap Gate.inputs).count i ≤ 1
  · have bound := tree ⟨[t],0⟩ C a b (Or.inr ⟨rfl,ht⟩) mono one compute
    change 18 ≤ 1 + C.size at bound
    omega
  push Not at one
  obtain ⟨i,hi,hm⟩ := one
  have hn : ¬ (12 ≤ i ∨ t.op = .not) := fun h => bad (Or.inr ⟨i,hi,h,by omega⟩)
  have hne : a ≠ b := by
    obtain ⟨x,ha,hb⟩ := left
    rintro rfl
    simp_all
  rcases C with ⟨gs,o⟩
  cases gs with
  | nil =>
    change 1 < ([a,b] : List ℕ).count i at hm
    clear * - hm hne
    by_cases ha : a=i <;> by_cases hb : b=i <;> simp_all [List.count_cons,eq_comm]
  | cons q qs =>
    let P : Circuit := ⟨[t,q],0⟩
    let S : Circuit := ⟨qs,o⟩
    have hp : Monotone2 P := by
      intro g hg
      change g ∈ [t,q] at hg
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hg
      rcases hg with rfl|rfl
      · obtain ⟨op,len⟩ := ht g (by simp)
        rcases op with h|h|h
        · exact ⟨Or.inl h,len⟩
        · exact ⟨Or.inr h,len⟩
        · exact (hn (Or.inr h)).elim
      · exact mono _ (by simp)
    have hs : Monotone2 S := fun g hg => mono g (List.mem_cons_of_mem _ hg)
    have once (j) (hj : 12 ≤ j) : ([a,b]++qs.flatMap Gate.inputs).count j ≤ 1 := by
      by_contra! h
      apply bad
      right
      refine ⟨j,by omega,Or.inl hj,?_⟩
      simp only [List.flatMap_cons,List.count_append] at h ⊢
      omega
    have bound := tree P S a b (Or.inl ⟨rfl,hp⟩) hs once compute
    change 18 ≤ 2+qs.length at bound
    change (q::qs).length ≤ 16 at lim
    simp only [List.length_cons] at lim
    omega



