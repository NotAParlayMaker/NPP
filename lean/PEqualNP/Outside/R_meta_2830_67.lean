import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Bits zero through eleven record the positive rows and the next twelve the negative rows.
-- A transition retains in U the wires needed after a gate has read its two operands.
theorem PEqualNP.Outside.R_meta_2830_67
    (compile :
      let w : List (BitVec 24) := [5521449,8532035,3227782,430612,11083800,111904,903232,13500800,15732224,14053483]
      let step := fun A B : Finset (BitVec 24) =>
        ∃ (U : Finset (BitVec 24)) (a b : BitVec 24) (o : Bool),
          let z := if o then a ||| b else a &&& b
          A = insert a (insert b U) ∧ a ≠ b ∧ z ∉ A ∧ B = insert z U
      let separates := fun A : Finset (BitVec 24) => ∀ i j : Fin 12, ∃ v ∈ A,
        v.getLsbD i.val = true ∧ v.getLsbD (j.val+12) = false
      ∀ C : Circuit, Monotone2 C →
        (∀ i : Fin 24, C.eval (w.map fun v => v.getLsbD i.val) = (4095 : BitVec 24).getLsbD i.val) →
        ∃ (S : Finset (BitVec 24)) (p : List (Finset (BitVec 24))),
          (S = (w.take 9).toFinset ∨ S = w.toFinset) ∧ p.length ≤ C.size ∧
          (S::p).IsChain step ∧ (S::p).getLast? = some {4095} ∧ ∀ B ∈ S::p, separates B)
    (ordinary :
      let w : List (BitVec 24) := [5521449,8532035,3227782,430612,11083800,111904,903232,13500800,15732224,14053483]
      let step := fun A B : Finset (BitVec 24) =>
        ∃ (U : Finset (BitVec 24)) (a b : BitVec 24) (o : Bool),
          let z := if o then a ||| b else a &&& b
          A = insert a (insert b U) ∧ a ≠ b ∧ z ∉ A ∧ B = insert z U
      let separates := fun A : Finset (BitVec 24) => ∀ i j : Fin 12, ∃ v ∈ A,
        v.getLsbD i.val = true ∧ v.getLsbD (j.val+12) = false
      let root := (w.take 9).toFinset
      ∀ p : List (Finset (BitVec 24)), (root::p).IsChain step →
        (root::p).getLast? = some {4095} → (∀ B ∈ root::p, separates B) → 15 ≤ p.length)
    (extra :
      let w : List (BitVec 24) := [5521449,8532035,3227782,430612,11083800,111904,903232,13500800,15732224,14053483]
      let step := fun A B : Finset (BitVec 24) =>
        ∃ (U : Finset (BitVec 24)) (a b : BitVec 24) (o : Bool),
          let z := if o then a ||| b else a &&& b
          A = insert a (insert b U) ∧ a ≠ b ∧ z ∉ A ∧ B = insert z U
      let separates := fun A : Finset (BitVec 24) => ∀ i j : Fin 12, ∃ v ∈ A,
        v.getLsbD i.val = true ∧ v.getLsbD (j.val+12) = false
      let root := w.toFinset
      ∀ p : List (Finset (BitVec 24)), (root::p).IsChain step →
        (root::p).getLast? = some {4095} → (∀ B ∈ root::p, separates B) → 15 ≤ p.length) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)], x1.eval ((List.ofFn fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5) ++ [x3.testBit (0 : ℕ) || x3.testBit (1 : ℕ)]) = Bool.true) → (∀ x4 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x6 : Fin (9 : ℕ)) => x4.testBit ↑x6) ++ [x4.testBit (0 : ℕ) || x4.testBit (1 : ℕ)]) = Bool.false) → (15 : ℕ) ≤ x1.size := by
  intro C hm hp hn
  let w : List (BitVec 24) := [5521449,8532035,3227782,430612,11083800,111904,903232,13500800,15732224,14053483]
  let pos : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320]
  let neg : List ℕ := [42,50,69,104,116,138,201,208,261,276,385,402]
  let input (m : ℕ) := (List.ofFn (fun i : Fin 9 => m.testBit i.val)) ++ [m.testBit 0 || m.testBit 1]
  have rows : ∀ i : Fin 24,
      let r := (pos ++ neg).getD i.val 0
      w.map (fun v => v.getLsbD i.val) = input r ∧
      ((r ∈ pos ∧ (4095 : BitVec 24).getLsbD i.val = true) ∨
       (r ∈ neg ∧ (4095 : BitVec 24).getLsbD i.val = false)) := by decide +kernel
  have he (i : Fin 24) : C.eval (w.map fun v => v.getLsbD i.val) = (4095 : BitVec 24).getLsbD i.val := by
    obtain ⟨eq, mem⟩ := rows i
    rw [eq]
    rcases mem with ⟨m,h⟩ | ⟨m,h⟩
    · exact (hp _ m).trans h.symm
    · exact (hn _ m).trans h.symm
  obtain ⟨S,p,root,len,chain,last,covered⟩ := compile C hm he
  rcases root with rfl | rfl
  · exact (ordinary p chain last covered).trans len
  · exact (extra p chain last covered).trans len
