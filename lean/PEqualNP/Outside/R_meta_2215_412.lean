import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2215_412
    (geometry : ∀ P L : Finset (Fin 25), (∀ i ∈ P, i.val < 12) →
      (∀ j ∈ L, 12 ≤ j.val) →
      (∀ i ∈ P, ∀ j ∈ L, (i.val + j.val + 2) % 13 ∉ ([0,1,3,9] : List ℕ)) →
      P.card ≤ 3 ∨ L.card ≤ 3)
    (search :
      let I (i j : Fin 25) := i.val < 12 ∧ 12 ≤ j.val ∧
        (i.val + j.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ)
      let P := Finset.univ.filter fun i : Fin 25 => i.val < 12
      let A : Finset (Fin 25) := {12,13,15,21}
      let side (b : Bool) := if b then P else Finset.univ \ P
      let sat (b : Bool) (S : Finset (Fin 25)) :=
        S ∪ ((side (!b)).filter fun j => ∀ i ∈ S, ¬ (I i j ∨ I j i))
      let input (S : Finset (Fin 25)) := List.ofFn fun i => decide (i ∈ S)
      ∃ (C : Circuit) (q : ℕ), Monotone2 C ∧ C.size ≤ 61 ∧
        C.output < 25 + C.size ∧ q < 25 + C.size ∧
        (∀ i j, I i j → C.eval (input {i,j}) = true) ∧
        (∀ i ∈ A, (C.wires (input {i})).getD q false = true) ∧
        (∀ b S, S ⊆ side b → S.card ≤ 3 →
          C.eval (input (sat b S)) = false ∧
          (C.wires (input (sat b S \ A))).getD q false = false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  let I (i j : Fin 25) := i.val < 12 ∧ 12 ≤ j.val ∧
    (i.val + j.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ)
  let P := Finset.univ.filter fun i : Fin 25 => i.val < 12
  let A : Finset (Fin 25) := {12,13,15,21}
  let side (b : Bool) := if b then P else Finset.univ \ P
  let sat (b : Bool) (S : Finset (Fin 25)) :=
    S ∪ ((side (!b)).filter fun j => ∀ i ∈ S, ¬ (I i j ∨ I j i))
  let input (S : Finset (Fin 25)) := List.ofFn fun i => decide (i ∈ S)
  change ∃ (C : Circuit) (q : ℕ), Monotone2 C ∧ C.size ≤ 61 ∧
    C.output < 25 + C.size ∧ q < 25 + C.size ∧
    (∀ i j, I i j → C.eval (input {i,j}) = true) ∧
    (∀ i ∈ A, (C.wires (input {i})).getD q false = true) ∧
    (∀ b S, S ⊆ side b → S.card ≤ 3 →
      C.eval (input (sat b S)) = false ∧
      (C.wires (input (sat b S \ A))).getD q false = false) at search
  obtain ⟨C,q,hm,hs,ho,hq,accept,flag,tests⟩ := search
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let Le (w z : List Bool) := ∀ i : ℕ, w.getD i false = true → z.getD i false = true
  have extend (gs : List Gate) (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (w z : List Bool) (len : w.length = z.length) (le : Le w z) :
      Le (gs.foldl step w) (gs.foldl step z) := by
    induction gs generalizing w z with
    | nil => exact le
    | cons g gs ih =>
      apply ih (fun k hk => ok k (by simp [hk])) (step w g) (step z g) (by simp [step,len])
      have gate : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
          g.op.eval (g.inputs.map fun i => z.getD i false) = true := by
        rcases ok g (by simp) with hop | hop
        · rw [hop]
          change (g.inputs.map fun i => w.getD i false).all id = true →
            (g.inputs.map fun i => z.getD i false).all id = true
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          intro h i hi
          exact le i (h i hi)
        · rw [hop]
          change (g.inputs.map fun i => w.getD i false).any id = true →
            (g.inputs.map fun i => z.getD i false).any id = true
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          rintro ⟨i,hi,ha⟩
          exact ⟨i,hi,le i ha⟩
      intro i
      by_cases small : i < w.length
      · simpa only [step,List.getD_append _ _ _ _ small,List.getD_append _ _ _ _ (len ▸ small)] using le i
      · have big : w.length ≤ i := by omega
        simp only [step,List.getD_append_right _ _ _ _ big,List.getD_append_right _ _ _ _ (len ▸ big), ← len]
        cases e : i-w.length with
        | zero => exact gate
        | succ j => simp
  have mono {S T : Finset (Fin 25)} (sub : S ⊆ T) (j : ℕ) :
      (C.wires (input S)).getD j false = true → (C.wires (input T)).getD j false = true := by
    have init : Le (input S) (input T) := by
      intro k
      by_cases hk : k < 25
      · rw [List.getD_eq_getElem (input S) false (by simpa [input] using hk),
            List.getD_eq_getElem (input T) false (by simpa [input] using hk)]
        simp only [input, List.getElem_ofFn, decide_eq_true_eq]
        exact sub (x := (⟨k,hk⟩ : Fin 25))
      · rw [List.getD_eq_default (input S) false (by simpa [input] using Nat.le_of_not_gt hk)]
        intro h
        exact Bool.noConfusion h
    exact extend C.gates (fun g hg => (hm g hg).1) _ _ (by simp [input]) init j
  have satCovers (X : Finset (Fin 25)) (miss : ∀ i ∈ X, ∀ j ∈ X, ¬ I i j) :
      ∃ b S, S ⊆ side b ∧ S.card ≤ 3 ∧ X ⊆ sat b S := by
    let U := X.filter fun i => i.val < 12
    let V := X.filter fun i => 12 ≤ i.val
    have memU {i : Fin 25} : i ∈ U ↔ i ∈ X ∧ i.val < 12 := Finset.mem_filter
    have memV {i : Fin 25} : i ∈ V ↔ i ∈ X ∧ 12 ≤ i.val := Finset.mem_filter
    have noninc (i) (hi : i ∈ U) (j) (hj : j ∈ V) :
        (i.val + j.val + 2) % 13 ∉ ([0,1,3,9] : List ℕ) := fun h =>
      miss i (memU.mp hi).1 j (memV.mp hj).1 ⟨(memU.mp hi).2,(memV.mp hj).2,h⟩
    rcases geometry U V (fun i hi => (memU.mp hi).2) (fun j hj => (memV.mp hj).2) noninc with h | h
    · refine ⟨true,U,?_,h,?_⟩
      · intro i hi
        simpa [side,P] using (memU.mp hi).2
      · intro j hj
        by_cases hjP : j.val < 12
        · exact Finset.mem_union_left _ (memU.mpr ⟨hj,hjP⟩)
        · apply Finset.mem_union_right
          apply Finset.mem_filter.mpr
          refine ⟨by simp [side,P,hjP], ?_⟩
          intro i hi bad
          exact bad.elim (miss i (memU.mp hi).1 j hj) (miss j hj i (memU.mp hi).1)
    · refine ⟨false,V,?_,h,?_⟩
      · intro i hi
        simpa [side,P] using (memV.mp hi).2
      · intro j hj
        by_cases hjP : j.val < 12
        · apply Finset.mem_union_right
          apply Finset.mem_filter.mpr
          refine ⟨by simp [side,P,hjP], ?_⟩
          intro i hi bad
          exact bad.elim (miss i (memV.mp hi).1 j hj) (miss j hj i (memV.mp hi).1)
        · exact Finset.mem_union_left _ (memV.mpr ⟨hj,Nat.le_of_not_gt hjP⟩)
  refine ⟨C,q,hm,hs,ho,hq,?_⟩
  intro x
  change (C.eval (List.ofFn x) = true ↔ ∃ i j, I i j ∧ x i = true ∧ x j = true) ∧
    (C.eval (List.ofFn x) = false → (C.wires (List.ofFn x)).getD q false =
      (x 12 || x 13 || x 15 || x 21))
  let X := Finset.univ.filter fun i => x i = true
  have memX {i : Fin 25} : i ∈ X ↔ x i = true := by simp [X]
  have repr : input X = List.ofFn x := by
    unfold input
    congr 1
    funext i
    simp [memX]
  rw [← repr]
  have hmain : C.eval (input X) = true ↔ ∃ i j, I i j ∧ x i = true ∧ x j = true := by
    constructor
    · intro yes
      by_contra none
      have miss : ∀ i ∈ X, ∀ j ∈ X, ¬ I i j :=
        fun i hi j hj hij => none ⟨i,j,hij,memX.mp hi,memX.mp hj⟩
      obtain ⟨b,S,hS,hcard,sub⟩ := satCovers X miss
      have yes' : C.eval (input (sat b S)) = true := mono sub C.output yes
      exact Bool.noConfusion ((tests b S hS hcard).1.symm.trans yes')
    · rintro ⟨i,j,hij,hi,hj⟩
      have sub : ({i,j} : Finset (Fin 25)) ⊆ X := by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hj'
        · exact memX.mpr hi
        · obtain rfl := Finset.mem_singleton.mp hj'
          exact memX.mpr hj
      exact mono sub C.output (accept i j hij)
  refine ⟨hmain,?_⟩
  intro no
  have miss : ∀ i ∈ X, ∀ j ∈ X, ¬ I i j := by
    intro i hi j hj hij
    have yes := hmain.mpr ⟨i,j,hij,memX.mp hi,memX.mp hj⟩
    exact Bool.noConfusion (no.symm.trans yes)
  have flagTrue : (x 12 || x 13 || x 15 || x 21) = true ↔ ∃ i ∈ A, x i = true := by
    simp [A, Bool.or_eq_true, or_assoc]
  cases value : (x 12 || x 13 || x 15 || x 21)
  · obtain ⟨b,S,hS,hcard,sub⟩ := satCovers X miss
    have sub' : X ⊆ sat b S \ A := by
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨sub hi, ?_⟩
      intro ai
      have f := flagTrue.mpr ⟨i,ai,memX.mp hi⟩
      exact Bool.noConfusion (value.symm.trans f)
    cases aux : (C.wires (input X)).getD q false
    · rfl
    · have f := mono sub' q aux
      exact Bool.noConfusion ((tests b S hS hcard).2.symm.trans f)
  · obtain ⟨i,ai,hi⟩ := flagTrue.mp value
    have sub : ({i} : Finset (Fin 25)) ⊆ X := Finset.singleton_subset_iff.mpr (memX.mpr hi)
    exact mono sub q (flag i ai)
