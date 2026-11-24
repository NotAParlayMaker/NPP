import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

/-- Petersen-minus-vertex edge function on 9-bit inputs. -/
abbrev E3077 : (Fin 9 → Bool) → Bool := fun x =>
  [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (e : ℕ) =>
    x (Fin.ofNat (9 : ℕ) (e / (10 : ℕ))) && x (Fin.ofNat (9 : ℕ) (e % (10 : ℕ)))

/-- Bits of `x10 < 512` as a 9-bit input. -/
abbrev bits3077 (x10 : ℕ) : Fin 9 → Bool := fun i => x10.testBit ↑i

/-- Read wire `i` (wire 25 is constant true). -/
abbrev read3077 (w : List Bool) (i : Fin 26) : Bool :=
  if ↑i = (25 : ℕ) then Bool.true else w.getD (↑i) Bool.false

/-- One gate step. -/
abbrev step3077 (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) : List Bool :=
  w ++ [if ↑g.1 = (0 : ℕ) then read3077 w g.2.1 && read3077 w g.2.2
        else if ↑g.1 = (1 : ℕ) then read3077 w g.2.1 || read3077 w g.2.2
        else !read3077 w g.2.1]

/-- Evaluate a gate list from the seed wires (inputs ++ [x0 || x4]). -/
abbrev eval3077 (x : Fin 9 → Bool) (gs : List (Fin 3 × Fin 26 × Fin 26)) : List Bool :=
  gs.foldl step3077 (List.ofFn x ++ [x 0 || x 4])

/-- The gap's conclusion for a gate list `L` and output wire `x3`. -/
abbrev Goal3077 (L : List (Fin 3 × Fin 26 × Fin 26)) (x3 : Fin 26) : Prop :=
  ∃ x10 < (512 : ℕ), (eval3077 (bits3077 x10) L).getD (↑x3) Bool.false ≠ E3077 (bits3077 x10)

/-- The gap's hypotheses for a gate list `L` (first gate + rest). -/
abbrev Hyps3077 (L : List (Fin 3 × Fin 26 × Fin 26)) : Prop :=
  L.length ≤ 14 ∧
  (∃ x1 x2 : Fin 26, ∃ rest : List (Fin 3 × Fin 26 × Fin 26),
    L = ((1 : Fin 3), x1, x2) :: rest ∧ (↑x1 = (9 : ℕ) ∨ ↑x2 = (9 : ℕ)) ∧
    ↑x1 ≠ (25 : ℕ) ∧ ↑x2 ≠ (25 : ℕ)) ∧
  (∀ x9 < (9 : ℕ), ∃ g ∈ L, ↑g.2.1 = x9 ∨ ↑g.2.2 = x9)

/-- Folding gates does not change wires below the initial length. -/
private lemma readLemma3077 (gs : List (Fin 3 × Fin 26 × Fin 26)) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl step3077 w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : (step3077 w g).length = w.length + 1 := by simp [step3077]
    rw [ih (step3077 w g) (by omega)]
    exact List.getD_append _ _ _ _ hi

/-- Folding gates appends one wire per gate. -/
private lemma evalLength3077 (gs : List (Fin 3 × Fin 26 × Fin 26)) (w : List Bool) :
    (gs.foldl step3077 w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    have hlen : (step3077 w g).length = w.length + 1 := by simp [step3077]
    simp only [List.foldl_cons, ih, List.length_cons]
    omega

set_option maxRecDepth 10000 in
/-- For any seed wire, some input makes the seed value differ from the edge function. -/
private lemma seedCase3077 (i : Fin 10) :
    ∃ x10 < (512 : ℕ),
      (List.ofFn (bits3077 x10) ++ [bits3077 x10 0 || bits3077 x10 4]).getD (↑i) false ≠
        E3077 (bits3077 x10) := by
  fin_cases i <;> decide

/-- Reduce L-meta-3077 by the op of the gate producing the output wire. -/
theorem R_meta_3077_1 :
    (∀ (L : List (Fin 3 × Fin 26 × Fin 26)) (x3 : Fin 26), Hyps3077 L →
      (∃ k, ∃ _ : k < L.length, (L[k]).1 = (0 : Fin 3) ∧ ↑x3 = 10 + k) → Goal3077 L x3) →
    (∀ (L : List (Fin 3 × Fin 26 × Fin 26)) (x3 : Fin 26), Hyps3077 L →
      (∃ k, ∃ _ : k < L.length, (L[k]).1 = (1 : Fin 3) ∧ ↑x3 = 10 + k) → Goal3077 L x3) →
    (∀ (L : List (Fin 3 × Fin 26 × Fin 26)) (x3 : Fin 26), Hyps3077 L →
      (∃ k, ∃ _ : k < L.length, (L[k]).1 = (2 : Fin 3) ∧ ↑x3 = 10 + k) → Goal3077 L x3) →
    ∀ (x1 x2 x3 : Fin 26) (x4 : List (Fin 3 × Fin 26 × Fin 26)),
      x4.length ≤ (13 : ℕ) → ↑x1 = (9 : ℕ) ∨ ↑x2 = (9 : ℕ) → ↑x1 ≠ (25 : ℕ) → ↑x2 ≠ (25 : ℕ) →
      (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →
      ∃ x10 < (512 : ℕ),
        have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;
        have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;
        have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);
        x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro andCase orCase notCase x1 x2 x3 x4 hlen h9 h1 h2 hread
  have hL : Hyps3077 (((1 : Fin 3), x1, x2) :: x4) := by
    refine ⟨?_, ⟨x1, x2, x4, rfl, h9, h1, h2⟩, ?_⟩
    · simp only [List.length_cons]; omega
    · intro x9 hx9
      obtain ⟨g, hg, hgi⟩ := hread x9 hx9
      exact ⟨g, List.mem_cons_of_mem _ hg, hgi⟩
  show Goal3077 (((1 : Fin 3), x1, x2) :: x4) x3
  by_cases hA : (↑x3 : ℕ) < 10
  · -- Output is a seed wire (an input literal or OR(x0,x4)): exhibit a failing input.
    obtain ⟨x10, hx10, hne⟩ := seedCase3077 ⟨↑x3, hA⟩
    refine ⟨x10, hx10, ?_⟩
    have hside : (↑x3 : ℕ) <
        (List.ofFn (bits3077 x10) ++ [bits3077 x10 0 || bits3077 x10 4]).length := by
      have h10 : (List.ofFn (bits3077 x10) ++ [bits3077 x10 0 || bits3077 x10 4]).length
          = 10 := by simp
      omega
    simp only [eval3077]
    rw [readLemma3077 _ _ _ hside]
    exact hne
  · by_cases hB : (↑x3 : ℕ) < 10 + (((1 : Fin 3), x1, x2) :: x4).length
    · -- Output wire is produced by a gate: split on that gate's op.
      set k : ℕ := (↑x3 : ℕ) - 10 with hkdef
      have hk : k < (((1 : Fin 3), x1, x2) :: x4).length := by omega
      have hop : ((((1 : Fin 3), x1, x2) :: x4)[k]).1 = (0 : Fin 3) ∨
          ((((1 : Fin 3), x1, x2) :: x4)[k]).1 = (1 : Fin 3) ∨
          ((((1 : Fin 3), x1, x2) :: x4)[k]).1 = (2 : Fin 3) := by omega
      rcases hop with h0 | h1 | h2
      · exact andCase _ _ hL ⟨k, hk, h0, by omega⟩
      · exact orCase _ _ hL ⟨k, hk, h1, by omega⟩
      · exact notCase _ _ hL ⟨k, hk, h2, by omega⟩
    · -- Output wire does not exist: it reads as false; the edge is true on (0,1).
      refine ⟨3, by decide, ?_⟩
      have hlen2 : (eval3077 (bits3077 3) (((1 : Fin 3), x1, x2) :: x4)).length
          = 10 + (((1 : Fin 3), x1, x2) :: x4).length := by
        simp only [eval3077, evalLength3077, List.length_append, List.length_singleton,
          List.length_ofFn]
      have hget : (eval3077 (bits3077 3) (((1 : Fin 3), x1, x2) :: x4)).getD (↑x3) false
          = false :=
        List.getD_eq_default _ _ (by omega)
      rw [hget]
      decide

end PEqualNP.Outside
