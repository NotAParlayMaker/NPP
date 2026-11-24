import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2778_1
    (h1 : have x1 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))];
      ∀ (x2 : List (BitVec (24 : ℕ))), x2.length ≤ (14 : ℕ) →
      (∃ x6 ∈ x1, ∃ x7 ∈ x1, x2[0]? = Option.some (x6 &&& x7)) →
      (∀ (x4 : ℕ) (x5 : x4 < x2.length), x2[x4] ∉ x1 ++ List.take x4 x2 ∧ ∃ x6 ∈ x1 ++ List.take x4 x2, ∃ x7 ∈ x1 ++ List.take x4 x2, x2[x4] = x6 &&& x7 ∨ x2[x4] = x6 ||| x7) →
      (3428671 : BitVec (24 : ℕ)) ∉ x1 ++ x2)
    (h2 : have x1 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))];
      ∀ (x2 : List (BitVec (24 : ℕ))), x2.length ≤ (14 : ℕ) →
      (∃ x6 ∈ x1, ∃ x7 ∈ x1, x2[0]? = Option.some (x6 ||| x7)) →
      (∀ (x4 : ℕ) (x5 : x4 < x2.length), x2[x4] ∉ x1 ++ List.take x4 x2 ∧ ∃ x6 ∈ x1 ++ List.take x4 x2, ∃ x7 ∈ x1 ++ List.take x4 x2, x2[x4] = x6 &&& x7 ∨ x2[x4] = x6 ||| x7) →
      (3428671 : BitVec (24 : ℕ)) ∉ x1 ++ x2) :
    have x1 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))]; ∀ (x2 : List (BitVec (24 : ℕ))), x2.length ≤ (14 : ℕ) → (∀ (x4 : ℕ) (x5 : x4 < x2.length), x2[x4] ∉ x1 ++ List.take x4 x2 ∧ ∃ x6 ∈ x1 ++ List.take x4 x2, ∃ x7 ∈ x1 ++ List.take x4 x2, x2[x4] = x6 &&& x7 ∨ x2[x4] = x6 ||| x7) → (3428671 : BitVec (24 : ℕ)) ∉ x1 ++ x2 := by
  intro x1 x2 hlen hstep
  match x2 with
  | [] =>
    decide
  | g :: gs =>
    have h0 := (hstep 0 (by simp)).2
    simp only [List.take_zero, List.append_nil, List.getElem_cons_zero] at h0
    rcases h0 with ⟨x6, hx6, x7, hx7, hge | hge⟩
    · exact h1 (g :: gs) hlen ⟨x6, hx6, x7, hx7, by simp [hge]⟩ hstep
    · exact h2 (g :: gs) hlen ⟨x6, hx6, x7, hx7, by simp [hge]⟩ hstep
