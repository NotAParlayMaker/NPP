import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_211_aux

open PEqualNP.MetaComplexity

abbrev Input := Fin 4 → Bool

def code (x : Input) : ℕ :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) +
    (if x 2 then 4 else 0) + (if x 3 then 8 else 0)

def target (x : Input) : Bool := decide ((if x 0 = true then 1 else 0) + (if x 1 = true then 2 else 0) + (if x 2 = true then 4 else 0) + (if x 3 = true then 8 else 0) ∈ ({3, 4, 6, 7, 8, 9, 11, 12} : Finset ℕ))

def rows (i : Fin 4) (b : Bool) : Finset ℕ :=
  (if b then ![{3, 11}, {3, 6, 7, 11}, {4, 6, 7, 12}, {8, 9}]
   else ![{4, 12}, {4, 8, 9, 12}, {3, 8, 9, 11}, {6, 7}]) i

def cols (i : Fin 4) (b : Bool) : Finset ℕ :=
  (if b then ![{0, 2, 10, 14}, {1, 5}, {0, 2}, {0, 1, 2, 5}]
   else ![{1, 5, 13, 15}, {10, 14}, {13, 15}, {10, 13, 14, 15}]) i

def typing (x y : Input) : ℕ :=
  if (∃ b : Bool, code x ∈ rows 0 b ∧ code y ∈ cols 0 b) then 0 else
  if (∃ b : Bool, code x ∈ rows 1 b ∧ code y ∈ cols 1 b) then 1 else
  if (∃ b : Bool, code x ∈ rows 2 b ∧ code y ∈ cols 2 b) then 2 else
  3

def u (i : Fin 4) (b : Bool) (x : Input) : ℚ := if code x ∈ rows i b then 1 else 0

def v (i : Fin 4) (b : Bool) (y : Input) : ℚ := if code y ∈ cols i b then 1 else 0

theorem allInputs {P : Input → Prop} : (∀ x, P x) ↔ ∀ a b c d, P ![a, b, c, d] :=
  (FinVec.forall_iff P).symm

set_option maxRecDepth 100000 in
theorem valid : IsTyping 4 target typing := by
  unfold IsTyping
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem factors : ∀ (i : Fin 4) (b : Bool) (x y : Input),
    typedMatrix 4 target typing i b x y = Matrix.vecMulVec (u i b) (v i b) x y := by
  intro i b
  fin_cases i <;> cases b <;> simp only [allInputs] <;> decide +kernel

theorem rank_bound (i : Fin 4) (b : Bool) : (typedMatrix 4 target typing i b).rank ≤ 1 := by
  have h : typedMatrix 4 target typing i b = Matrix.vecMulVec (u i b) (v i b) := by
    ext x y
    exact factors i b x y
  rw [h]
  exact Matrix.rank_vecMulVec_le _ _

theorem upper : HasTypedRank 4 target 8 := by
  refine ⟨typing, valid, ?_⟩
  calc
    ∑ i : Fin 4, ∑ b : Bool, (typedMatrix 4 target typing i b).rank
      ≤ ∑ _i : Fin 4, ∑ _b : Bool, (1 : ℕ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => rank_bound i b
    _ = 8 := by decide

end PEqualNP.Outside.L_meta_211_aux

theorem PEqualNP.Outside.L_meta_211 : PEqualNP.MetaComplexity.HasTypedRank 4 (fun x : Fin 4 → Bool => decide ((if x 0 = true then 1 else 0) + (if x 1 = true then 2 else 0) + (if x 2 = true then 4 else 0) + (if x 3 = true then 8 else 0) ∈ ({3, 4, 6, 7, 8, 9, 11, 12} : Finset ℕ))) 8 := by
  exact PEqualNP.Outside.L_meta_211_aux.upper
