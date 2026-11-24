import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_2567_482 (affine : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 43 ∧
    ∀ P L : Fin 13 → Bool, C.eval [P 0, P 1, P 2, P 4, P 5, P 6, P 7, P 8, P 9, P 10, P 11, P 12, L 1, L 2, L 3, L 4, L 5, L 7, L 8, L 9, L 12, (P 0 || P 1 || P 9), (P 7 || P 8 || P 10), (P 4 || P 6 || P 12), (P 2 || P 5 || P 11)] =
      decide (∃ i j : Fin 13, j ∈ ([1, 2, 3, 4, 5, 7, 8, 9, 12] : List (Fin 13)) ∧
        (i.val+j.val)%13 ∈ ([0,1,3,9] : List Nat) ∧ P i = true ∧ L j = true))
  (extend : ∀ C : Circuit, Monotone2 C → C.size ≤ 43 →
  ∃ S : Circuit, Monotone2 S ∧ S.size ≤ 62 ∧ ∀ P L : Fin 13 → Bool,
    S.eval ((List.ofFn P ++ List.ofFn L) ++ [P 0 || P 1]) = (C.eval [P 0, P 1, P 2, P 4, P 5, P 6, P 7, P 8, P 9, P 10, P 11, P 12, L 1, L 2, L 3, L 4, L 5, L 7, L 8, L 9, L 12, (P 0 || P 1 || P 9), (P 7 || P 8 || P 10), (P 4 || P 6 || P 12), (P 2 || P 5 || P 11)] || ((((P 0 || P 1 || P 9) || P 3) && L 0) || (((P 7 || P 8 || P 10) || P 3) && L 6) || (((P 4 || P 6 || P 12) || P 3) && L 10) || (((P 2 || P 5 || P 11) || P 3) && L 11))))
  (geometry : ∀ P L : Fin 13 → Bool, (decide (∃ i j : Fin 13, j ∈ ([1, 2, 3, 4, 5, 7, 8, 9, 12] : List (Fin 13)) ∧ (i.val+j.val)%13 ∈ ([0,1,3,9] : List Nat) ∧ P i = true ∧ L j = true) || ((((P 0 || P 1 || P 9) || P 3) && L 0) || (((P 7 || P 8 || P 10) || P 3) && L 6) || (((P 4 || P 6 || P 12) || P 3) && L 10) || (((P 2 || P 5 || P 11) || P 3) && L 11))) = decide (∃ i j : Fin 13, (i.val+j.val)%13 ∈ ([0,1,3,9] : List Nat) ∧ P i = true ∧ L j = true)) :
∃ (x1 : PEqualNP.CircuitLowerBounds.GateOp) (x2 : Fin (26 : ℕ)) (x3 : Fin (26 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x1 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧     (x2, x3) ∈ [((0 : Fin (26 : ℕ)), (1 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)))] ∧       PEqualNP.MetaComplexity.Monotone2 x4 ∧         x4.size ≤ (62 : ℕ) ∧           let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];           have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);           have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};           have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => x4.eval (List.ofFn (x6 x8 x9) ++ [x1.eval [x6 x8 x9 x2, x6 x8 x9 x3]]);           (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false := by

  classical
  obtain ⟨C,ok,size,compute⟩ := affine
  obtain ⟨S,valid,bound,run⟩ := extend C ok size
  refine ⟨.or,0,1,S,Or.inr rfl,by decide,valid,bound,?_⟩
  let point (A : Finset (Fin 13)) (i : Fin 13) := decide (i∈A)
  let adj (i j : Fin 13) := (i.val+j.val)%13 ∈ ([0,1,3,9] : List Nat)
  let neg (A : Finset (Fin 13)) := Finset.univ.filter (fun j => ∀ i∈A, ¬adj i j)
  let row (A B : Finset (Fin 13)) (i : Fin 26) := if i.val<13 then
    decide (Fin.ofNat 13 i.val∈A) else decide (Fin.ofNat 13 i.val∈B)
  have form (A B : Finset (Fin 13)) :
      S.eval (List.ofFn (row A B) ++ [GateOp.or.eval [row A B 0,row A B 1]]) =
      decide (∃ i j : Fin 13, adj i j ∧ i∈A ∧ j∈B) := by
    let P := point A
    let L := point B
    have rr : List.ofFn (row A B) = (List.ofFn P ++ List.ofFn L) := rfl
    rw [rr]
    change S.eval (_ ++ [P 0 || (P 1 || false)]) = _
    rw [Bool.or_false]
    rw [run P L,compute P L,geometry P L]
    simp [adj,P,L,point]
  constructor
  · intro i j hit
    change S.eval (List.ofFn (row {i} {j}) ++ [_]) = true
    rw [form]; simp only [decide_eq_true_eq]
    exact ⟨i,j,hit,by simp,by simp⟩
  · intro A small
    have zero (U V : Finset (Fin 13)) (miss : ∀ i∈U, ∀ j∈V, ¬adj i j) :
        S.eval (List.ofFn (row U V) ++ [GateOp.or.eval [row U V 0,row U V 1]]) = false := by
      rw [form]; apply decide_eq_false_iff_not.mpr
      rintro ⟨i,j,e,ui,vj⟩
      exact miss i ui j vj e
    constructor
    · apply zero A (neg A)
      intro i ai j bj; exact (Finset.mem_filter.mp bj).2 i ai
    · apply zero (neg A) A
      intro i ai j bj e
      have swapped : adj j i := by simpa [adj,Nat.add_comm] using e
      exact (Finset.mem_filter.mp ai).2 j bj swapped
