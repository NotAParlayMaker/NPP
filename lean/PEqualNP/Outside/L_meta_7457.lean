import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7457
open PEqualNP.CircuitLowerBounds



def stepB (S : List (BitVec 59)) (z : Bool × Fin 40 × Fin 40) : List (BitVec 59) :=
  S ++ [if z.1 = true then S.getD (z.2.1 : ℕ) 0 ||| S.getD (z.2.2 : ℕ) 0
    else S.getD (z.2.1 : ℕ) 0 &&& S.getD (z.2.2 : ℕ) 0]

theorem pref : ∀ (l : List (Bool × Fin 40 × Fin 40)) (S : List (BitVec 59)),
    ∃ t, List.foldl stepB S l = S ++ t := by
  intro l
  induction l with
  | nil => intro S; exact ⟨[], by simp⟩
  | cons a l ih =>
    intro S
    obtain ⟨t, ht⟩ := ih (stepB S a)
    refine ⟨(if a.1 = true then S.getD (a.2.1 : ℕ) 0 ||| S.getD (a.2.2 : ℕ) 0
      else S.getD (a.2.1 : ℕ) 0 &&& S.getD (a.2.2 : ℕ) 0) :: t, ?_⟩
    rw [List.foldl_cons, ht]
    simp [stepB]

end PEqualNP.Outside.L_meta_7457

open PEqualNP.Outside.L_meta_7457 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7457 : ∀ (x1 x2 : List (BitVec (59 : ℕ))), x1.length = (14 : ℕ) → x2.length ≤ (25 : ℕ) → (∀ (x5 : Fin x2.length), ∃ x6 ∈ x1 ++ List.take (↑x5) x2, ∃ x7 ∈ x1 ++ List.take (↑x5) x2, x2.get x5 = x6 &&& x7 ∨ x2.get x5 = x6 ||| x7) → ∃ (x6 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))), x6.length = (25 : ℕ) ∧ ∀ (x7 : Fin x2.length), (List.foldl (fun (x8 : List (BitVec (59 : ℕ))) (x9 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x8 ++ [if x9.1 = Bool.true then x8.getD ↑x9.2.1 (0 : BitVec (59 : ℕ)) ||| x8.getD ↑x9.2.2 (0 : BitVec (59 : ℕ)) else x8.getD ↑x9.2.1 (0 : BitVec (59 : ℕ)) &&& x8.getD ↑x9.2.2 (0 : BitVec (59 : ℕ))]) x1 x6).getD ((14 : ℕ) + ↑x7) (0 : BitVec (59 : ℕ)) = x2.get x7 := by
  intro L G hL hG hP
  classical
  have hc : ∀ j, ∃ c : Bool × Fin 40 × Fin 40, ∀ hj : j < G.length,
      stepB (L ++ G.take j) c = L ++ G.take j ++ [G.get ⟨j, hj⟩] := by
    intro j
    by_cases hj : j < G.length
    · obtain ⟨u, hu, v, hv, h⟩ := hP ⟨j, hj⟩
      obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hv
      have hlen : (L ++ G.take j).length = 14 + j := by
        rw [List.length_append, hL, List.length_take, Nat.min_eq_left (le_of_lt hj)]
      have hp2 : p < (L ++ G.take j).length := hp
      have hq2 : q < (L ++ G.take j).length := hq
      have hp' : p < 40 := by omega
      have hq' : q < 40 := by omega
      rcases h with h | h
      · refine ⟨(false, ⟨p, hp'⟩, ⟨q, hq'⟩), fun _ => ?_⟩
        simp only [stepB]
        rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hq]
        simp [← h]
      · refine ⟨(true, ⟨p, hp'⟩, ⟨q, hq'⟩), fun _ => ?_⟩
        simp only [stepB]
        rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hq]
        simp [← h]
    · exact ⟨(false, 0, 0), fun h => absurd h hj⟩
  choose c hc using hc
  have key : ∀ k, k ≤ G.length → List.foldl stepB L ((List.range k).map c) = L ++ G.take k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [hc k (by omega), List.take_succ_eq_append_getElem (by omega : k < G.length),
        List.append_assoc]
      rfl
  refine ⟨(List.range G.length).map c ++ List.replicate (25 - G.length) (false, 0, 0),
    by simp; omega, fun i => ?_⟩
  show (List.foldl stepB L ((List.range G.length).map c ++
    List.replicate (25 - G.length) (false, 0, 0))).getD (14 + (i : ℕ)) 0 = G.get i
  rw [List.foldl_append, key _ le_rfl, List.take_length]
  obtain ⟨t, ht⟩ := pref (List.replicate (25 - G.length) (false, 0, 0)) (L ++ G)
  rw [ht]
  have h1 : 14 + i.val < (L ++ G).length := by
    rw [List.length_append, hL]
    have := i.isLt
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1,
    List.getElem?_append_right (by omega : L.length ≤ 14 + i.val)]
  simp [hL]
