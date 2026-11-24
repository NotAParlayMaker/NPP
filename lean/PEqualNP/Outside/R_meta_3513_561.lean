import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_3513_561
    (case1 :
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →
      PEqualNP.MetaComplexity.FanInTwo x3 →
      (∀ (x6 : Fin (9 : ℕ) →
      Bool),           have x7 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ))]);           x3.eval (x7 ++ [!x7.getD x2.output Bool.false]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2) →
      (13 : ℕ) ≤ x2.size + x3.size)
    (case2 :
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →
      PEqualNP.MetaComplexity.FanInTwo x3 →
      (∀ (x6 : Fin (9 : ℕ) →
      Bool),           have x7 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))]);           x3.eval (x7 ++ [!x7.getD x2.output Bool.false]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2) →
      (13 : ℕ) ≤ x2.size + x3.size)
    (case3 :
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →
      PEqualNP.MetaComplexity.FanInTwo x3 →
      (∀ (x6 : Fin (9 : ℕ) →
      Bool),           have x7 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ))]);           x3.eval (x7 ++ [!x7.getD x2.output Bool.false]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2) →
      (13 : ℕ) ≤ x2.size + x3.size)
    (case6 :
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →
      PEqualNP.MetaComplexity.FanInTwo x3 →
      (∀ (x6 : Fin (9 : ℕ) →
      Bool),           have x7 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ))]);           x3.eval (x7 ++ [!x7.getD x2.output Bool.false]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2) →
      (13 : ℕ) ≤ x2.size + x3.size)
    :
    (∀ (x1 : Fin (9 : ℕ)) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →
     PEqualNP.MetaComplexity.FanInTwo x3 →
     (∀ (x6 : Fin (9 : ℕ) →
     Bool),           have x7 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x1]);           x3.eval (x7 ++ [!x7.getD x2.output Bool.false]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2) →
     (13 : ℕ) ≤ x2.size + x3.size) := by
  intro j C D mono fan computes
  let seed (x : Fin 9 → Bool) (i : Fin 9) :=
    List.ofFn x ++ [x 0 || x 4, (x 0 || x 4) || x i]
  let target (x : Fin 9 → Bool) :=
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let bounds (i : Fin 9) : Prop :=
    ∀ A B : Circuit, Monotone2 A → FanInTwo B →
      (∀ x : Fin 9 → Bool, let w := A.wires (seed x i)
        B.eval (w ++ [!(w.getD A.output false)]) = target x) →
      13 ≤ A.size + B.size
  have lengthSeed (x : Fin 9 → Bool) (i : Fin 9) : (seed x i).length = 11 := by
    simp [seed]
  let mapGate (wire : ℕ → ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map wire⟩
  let mapCircuit (wire : ℕ → ℕ) (A : Circuit) : Circuit :=
    ⟨A.gates.map (mapGate wire), wire A.output⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let reads (wire : ℕ → ℕ) (old new : List Bool) : Prop :=
    ∀ i, old.getD i false = new.getD (wire i) false
  have mapSize (wire : ℕ → ℕ) (A : Circuit) : (mapCircuit wire A).size = A.size := by
    change (A.gates.map (mapGate wire)).length = A.gates.length
    simp only [List.length_map]
  have mapGood (wire : ℕ → ℕ) (A : Circuit) (ops : Set GateOp)
      (good : ∀ g ∈ A.gates, g.op ∈ ops ∧ g.inputs.length ≤ 2) :
      ∀ g ∈ (mapCircuit wire A).gates, g.op ∈ ops ∧ g.inputs.length ≤ 2 := by
    intro g hg
    change g ∈ A.gates.map (mapGate wire) at hg
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
    simpa [mapGate] using good k hk
  -- Every changed index is in the initial segment, so appending preserves the relation.
  have extend (wire : ℕ → ℕ)
      (fixed : ∀ i, 11 ≤ i → wire i = i)
      (small : ∀ i, i < 11 → wire i < 11)
      {old new : List Bool} (len : old.length = new.length) (lower : 11 ≤ new.length)
      (agree : reads wire old new) (b : Bool) :
      reads wire (old ++ [b]) (new ++ [b]) := by
    intro i
    by_cases hi : i < new.length
    · have hi' : i < old.length := by omega
      have wi : wire i < new.length := by
        by_cases h : i < 11
        · exact lt_of_lt_of_le (small i h) lower
        · rwa [fixed i (by omega)]
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi',
        List.getElem?_append_left wi] using agree i
    · rw [fixed i (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : old.length ≤ i),
        List.getElem?_append_right (by omega : new.length ≤ i), len]
  have folds (wire : ℕ → ℕ)
      (fixed : ∀ i, 11 ≤ i → wire i = i)
      (small : ∀ i, i < 11 → wire i < 11)
      (gs : List Gate) (old new : List Bool) (len : old.length = new.length)
      (lower : 11 ≤ new.length) (agree : reads wire old new) :
      let oldW := gs.foldl step old
      let newW := (gs.map (mapGate wire)).foldl step new
      oldW.length = newW.length ∧ 11 ≤ newW.length ∧ reads wire oldW newW := by
    induction gs generalizing old new with
    | nil => exact ⟨len, lower, agree⟩
    | cons g gs ih =>
      have values : g.inputs.map (fun i => old.getD i false) =
          (mapGate wire g).inputs.map (fun i => new.getD i false) := by
        simp only [mapGate, List.map_map]
        exact congrArg (fun f => g.inputs.map f) (funext agree)
      simp only [List.foldl_cons, List.map_cons]
      apply ih (step old g) (step new (mapGate wire g))
      · simp [step, len]
      · simp [step]; omega
      · simp only [step, values]
        exact extend wire fixed small len lower agree _
  have transport (i : Fin 9) (wire : ℕ → ℕ)
      (fixed : ∀ k, 11 ≤ k → wire k = k)
      (small : ∀ k, k < 11 → wire k < 11)
      (lift : (Fin 9 → Bool) → (Fin 9 → Bool))
      (targetEq : ∀ x, target (lift x) = target x)
      (seedEq : ∀ x, reads wire (seed (lift x) j) (seed x i))
      (bound : bounds i) : 13 ≤ C.size + D.size := by
    have mono' : Monotone2 (mapCircuit wire C) := mapGood wire C _ mono
    have fan' : FanInTwo (mapCircuit wire D) := mapGood wire D _ fan
    have computes' (x : Fin 9 → Bool) :
        let w := (mapCircuit wire C).wires (seed x i)
        (mapCircuit wire D).eval (w ++ [!(w.getD (mapCircuit wire C).output false)]) = target x := by
      let old := C.wires (seed (lift x) j)
      let new := (mapCircuit wire C).wires (seed x i)
      obtain ⟨len, lower, agree⟩ := folds wire fixed small C.gates
        (seed (lift x) j) (seed x i) (by simp [lengthSeed]) (by simp [lengthSeed]) (seedEq x)
      change old.length = new.length at len
      change 11 ≤ new.length at lower
      change reads wire old new at agree
      have outputEq : old.getD C.output false = new.getD (mapCircuit wire C).output false :=
        agree C.output
      have agree' : reads wire (old ++ [!(old.getD C.output false)])
          (new ++ [!(new.getD (mapCircuit wire C).output false)]) := by
        rw [outputEq]
        exact extend wire fixed small len lower agree _
      obtain ⟨_, _, final⟩ := folds wire fixed small D.gates
        (old ++ [!(old.getD C.output false)])
        (new ++ [!(new.getD (mapCircuit wire C).output false)])
        (by simp [len]) (by simp; omega) agree'
      have evalEq := final D.output
      change D.eval (old ++ [!(old.getD C.output false)]) =
        (mapCircuit wire D).eval (new ++ [!(new.getD (mapCircuit wire C).output false)]) at evalEq
      have h := computes (lift x)
      change D.eval (old ++ [!(old.getD C.output false)]) = target (lift x) at h
      change (mapCircuit wire D).eval (new ++ [!(new.getD (mapCircuit wire C).output false)]) =
        target x
      rw [← evalEq, h, targetEq]
    simpa only [mapSize] using bound (mapCircuit wire C) (mapCircuit wire D) mono' fan' computes'
  -- This permutation fixes both vertices in the first auxiliary signal.
  let symmetry : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
  let permuteWire (i : ℕ) : ℕ := if h : i < 9 then (symmetry ⟨i, h⟩).val else i
  have symmetryTarget (x : Fin 9 → Bool) : target (x ∘ symmetry) = target x := by
    have h0 : symmetry 0 = 0 := rfl
    have h1 : symmetry 1 = 5 := rfl
    have h2 : symmetry 2 = 8 := rfl
    have h3 : symmetry 3 = 3 := rfl
    have h4 : symmetry 4 = 4 := rfl
    have h5 : symmetry 5 = 1 := rfl
    have h6 : symmetry 6 = 7 := rfl
    have h7 : symmetry 7 = 6 := rfl
    have h8 : symmetry 8 = 2 := rfl
    simp only [target, List.any_cons, List.any_nil, Bool.or_false, Function.comp_apply,
      h0, h1, h2, h3, h4, h5, h6, h7, h8,
      Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
  have permuteFixed : ∀ i, 11 ≤ i → permuteWire i = i := by
    intro i hi
    simp [permuteWire, Nat.not_lt.mpr (by omega : 9 ≤ i)]
  have permuteSmall : ∀ i, i < 11 → permuteWire i < 11 := by
    intro i hi
    by_cases h : i < 9
    · have hs : (symmetry ⟨i, h⟩).val < 11 :=
        lt_trans (symmetry ⟨i, h⟩).isLt (by decide)
      simpa [permuteWire, h] using hs
    · simp [permuteWire, h, hi]
  have reflect (bound : bounds (symmetry j)) : 13 ≤ C.size + D.size := by
    apply transport (symmetry j) permuteWire permuteFixed permuteSmall
      (fun x => x ∘ symmetry) symmetryTarget _ bound
    intro x i
    by_cases hi : i < 11
    · interval_cases i <;> rfl
    · rw [permuteFixed i (by omega)]
      rw [List.getD_eq_default _ _ (by rw [lengthSeed]; omega),
        List.getD_eq_default _ _ (by rw [lengthSeed]; omega)]
  -- If the two auxiliary signals agree, every read of wire 10 can read wire 9 instead.
  let mergeWire (i : ℕ) : ℕ := if i = 10 then 9 else i
  have mergeFixed : ∀ i, 11 ≤ i → mergeWire i = i := by
    intro i hi
    simp [mergeWire, show i ≠ 10 by omega]
  have mergeSmall : ∀ i, i < 11 → mergeWire i < 11 := by
    intro i hi
    by_cases h : i = 10 <;> simp [mergeWire, h, hi]
  have merge (hj : j = 0 ∨ j = 4) : 13 ≤ C.size + D.size := by
    apply transport 1 mergeWire mergeFixed mergeSmall id (fun _ => rfl) _ case1
    intro x i
    by_cases hi : i < 11
    · interval_cases i <;> try rfl
      change ((x 0 || x 4) || x j) = (x 0 || x 4)
      rcases hj with rfl | rfl <;> cases x 0 <;> cases x 4 <;> rfl
    · rw [mergeFixed i (by omega)]
      rw [List.getD_eq_default _ _ (by rw [lengthSeed]; omega),
        List.getD_eq_default _ _ (by rw [lengthSeed]; omega)]
  fin_cases j
  · exact merge (Or.inl rfl)
  · exact case1 C D mono fan computes
  · exact case2 C D mono fan computes
  · exact case3 C D mono fan computes
  · exact merge (Or.inr rfl)
  · exact reflect case1
  · exact case6 C D mono fan computes
  · exact reflect case6
  · exact reflect case2
