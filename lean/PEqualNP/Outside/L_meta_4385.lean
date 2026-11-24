import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4385

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bvL {n : ℕ} : GateOp → List (BitVec n) → BitVec n
  | GateOp.and, [] => BitVec.allOnes n &&& BitVec.allOnes n
  | GateOp.and, [a] => a &&& a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0 ||| 0
  | GateOp.or, [a] => a ||| a
  | GateOp.or, a :: b :: _ => a ||| b
  | _, _ => 0 ||| 0

def bv {n : ℕ} (g : Gate) (W : List (BitVec n)) : BitVec n :=
  bvL g.op (g.inputs.map fun i => W.getD i 0)

def prog {n : ℕ} : List Gate → List (BitVec n) → List (BitVec n)
  | [], _ => []
  | g :: gs, W => bv g W :: prog gs (W ++ [bv g W])

lemma prog_length {n : ℕ} (gs : List Gate) (W : List (BitVec n)) :
    (prog gs W).length = gs.length := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih => simp [prog, ih]

lemma getD_mem {n : ℕ} (W : List (BitVec n)) (i : ℕ) :
    W.getD i 0 ∈ (0 : BitVec n) :: BitVec.allOnes n :: W := by
  rw [List.getD_eq_getElem?_getD]
  cases h : W[i]? with
  | none => simp
  | some v =>
    simp only [Option.getD_some]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_getElem? h))

lemma bvL_shape {n : ℕ} (S : List (BitVec n)) (op : GateOp) (L : List (BitVec n))
    (hL : ∀ x ∈ L, x ∈ (0 : BitVec n) :: BitVec.allOnes n :: S) :
    ∃ a ∈ (0 : BitVec n) :: BitVec.allOnes n :: S, ∃ b ∈ (0 : BitVec n) :: BitVec.allOnes n :: S,
      bvL op L = a &&& b ∨ bvL op L = a ||| b := by
  have h0 : (0 : BitVec n) ∈ (0 : BitVec n) :: BitVec.allOnes n :: S := by simp
  have h1 : BitVec.allOnes n ∈ (0 : BitVec n) :: BitVec.allOnes n :: S := by simp
  rcases op with _ | _ | _ | m | _ <;> rcases L with _ | ⟨a, _ | ⟨b, L⟩⟩
  all_goals first
    | exact ⟨_, h1, _, h1, Or.inl rfl⟩
    | exact ⟨_, h0, _, h0, Or.inr rfl⟩
    | exact ⟨a, hL a (by simp), a, hL a (by simp), Or.inl rfl⟩
    | exact ⟨a, hL a (by simp), a, hL a (by simp), Or.inr rfl⟩
    | exact ⟨a, hL a (by simp), b, hL b (by simp), Or.inl rfl⟩
    | exact ⟨a, hL a (by simp), b, hL b (by simp), Or.inr rfl⟩

lemma bv_shape {n : ℕ} (g : Gate) (W : List (BitVec n)) :
    ∃ a ∈ (0 : BitVec n) :: BitVec.allOnes n :: W, ∃ b ∈ (0 : BitVec n) :: BitVec.allOnes n :: W,
      bv g W = a &&& b ∨ bv g W = a ||| b := by
  apply bvL_shape
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact getD_mem W i

lemma prog_shape {n : ℕ} (gs : List Gate) (W : List (BitVec n)) (i : ℕ)
    (hi : i < (prog gs W).length) :
    ∃ a ∈ (0 : BitVec n) :: BitVec.allOnes n :: (W ++ List.take i (prog gs W)),
    ∃ b ∈ (0 : BitVec n) :: BitVec.allOnes n :: (W ++ List.take i (prog gs W)),
      (prog gs W)[i] = a &&& b ∨ (prog gs W)[i] = a ||| b := by
  induction gs generalizing W i with
  | nil => simp [prog] at hi
  | cons g gs ih =>
    cases i with
    | zero =>
      simp only [prog, List.take_zero, List.append_nil, List.getElem_cons_zero]
      exact bv_shape g W
    | succ k =>
      have hk : k < (prog gs (W ++ [bv g W])).length := by
        simp [prog] at hi; simpa [prog_length] using hi
      have e : W ++ List.take (k + 1) (prog (g :: gs) W) =
          (W ++ [bv g W]) ++ List.take k (prog gs (W ++ [bv g W])) := by
        simp [prog]
      rw [e]
      simpa [prog] using ih (W ++ [bv g W]) k hk

lemma getD_map_bit {n : ℕ} (W : List (BitVec n)) (i j : ℕ) :
    (W.map fun x => x.getLsbD j).getD i false = (W.getD i 0).getLsbD j := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> simp

lemma bvL_bit {n : ℕ} (op : GateOp) (L : List (BitVec n)) (j : ℕ) (hj : j < n)
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hl : L.length ≤ 2) :
    (bvL op L).getLsbD j = op.eval (L.map fun x => x.getLsbD j) := by
  rcases hop with rfl | rfl <;> rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, L⟩⟩⟩
  all_goals simp_all [bvL, GateOp.eval]

lemma prog_bits {n : ℕ} (j : ℕ) (hj : j < n) (gs : List Gate) (W : List (BitVec n))
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (W ++ prog gs W).map (fun x => x.getLsbD j) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (W.map fun x => x.getLsbD j) := by
  induction gs generalizing W with
  | nil => simp [prog]
  | cons g gs ih =>
    have e : W ++ prog (g :: gs) W = (W ++ [bv g W]) ++ prog gs (W ++ [bv g W]) := by
      simp [prog]
    rw [e, ih (W ++ [bv g W]) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')),
      List.foldl_cons]
    congr 1
    obtain ⟨h1, h2⟩ := hg g (by simp)
    simp only [List.map_append, List.map_cons, List.map_nil]
    congr 2
    rw [bv, bvL_bit g.op _ j hj h1 (by simpa using h2), List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact (getD_map_bit W i j).symm

end PEqualNP.Outside.L_meta_4385

open PEqualNP.Outside.L_meta_4385
theorem PEqualNP.Outside.L_meta_4385 : ∀ (x1 : ℕ) (x2 : List (BitVec x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : List (BitVec x1)), x5.length ≤ x3.size ∧ (∀ (x6 : Fin x5.length), ∃ x7 ∈ (0 : BitVec x1) :: BitVec.allOnes x1 :: (x2 ++ List.take (↑x6) x5), ∃ x8 ∈ (0 : BitVec x1) :: BitVec.allOnes x1 :: (x2 ++ List.take (↑x6) x5), x5.get x6 = x7 &&& x8 ∨ x5.get x6 = x7 ||| x8) ∧ ∃ x6 ∈ (0 : BitVec x1) :: BitVec.allOnes x1 :: (x2 ++ x5), ∀ (x7 : Fin x1), x6.getLsbD ↑x7 = x3.eval (List.map (fun (x8 : BitVec x1) => x8.getLsbD ↑x7) x2) := by
  intro n X C hC
  refine ⟨prog C.gates X, by simp [prog_length, PEqualNP.CircuitLowerBounds.Circuit.size], ?_, ?_⟩
  · intro i
    exact prog_shape C.gates X i.1 i.2
  · refine ⟨(X ++ prog C.gates X).getD C.output 0, ?_, ?_⟩
    · exact getD_mem _ _
    · intro j
      rw [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
        ← prog_bits j.1 j.2 C.gates X hC, getD_map_bit]
