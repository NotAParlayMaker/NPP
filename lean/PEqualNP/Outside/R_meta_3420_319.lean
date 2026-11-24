import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3420_319
    (h1 : ¬∃ (x1 : List (BitVec (24 : ℕ))),
      x1.length = (24 : ℕ) ∧
      List.take (10 : ℕ) x1 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧
      x1.getD (10 : ℕ) (0 : BitVec (24 : ℕ)) = (16777215 : BitVec (24 : ℕ)) ∧
      x1.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧
      ((0 : BitVec (24 : ℕ)) :: x1).Nodup ∧
      ∀ (x2 : ℕ), (0 : ℕ) < x2 → x2 < (15 : ℕ) →
        have x5 : BitVec (24 : ℕ) := x1.getD ((9 : ℕ) + x2) (0 : BitVec (24 : ℕ));
        x5 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x6 : BitVec (24 : ℕ)) (x7 : BitVec (24 : ℕ)), x6 ∈ List.take ((9 : ℕ) + x2) x1 ∧ x7 ∈ List.take ((9 : ℕ) + x2) x1 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7))
    (h2 : ¬∃ (x1 : List (BitVec (24 : ℕ))),
      x1.length = (24 : ℕ) ∧
      List.take (10 : ℕ) x1 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧
      (∃ (x6 : BitVec (24 : ℕ)) (x7 : BitVec (24 : ℕ)), x6 ∈ List.take (10 : ℕ) x1 ∧ x7 ∈ List.take (10 : ℕ) x1 ∧ x1.getD (10 : ℕ) (0 : BitVec (24 : ℕ)) = x6 &&& x7) ∧
      x1.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧
      ((0 : BitVec (24 : ℕ)) :: x1).Nodup ∧
      ∀ (x2 : ℕ), (0 : ℕ) < x2 → x2 < (15 : ℕ) →
        have x5 : BitVec (24 : ℕ) := x1.getD ((9 : ℕ) + x2) (0 : BitVec (24 : ℕ));
        x5 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x6 : BitVec (24 : ℕ)) (x7 : BitVec (24 : ℕ)), x6 ∈ List.take ((9 : ℕ) + x2) x1 ∧ x7 ∈ List.take ((9 : ℕ) + x2) x1 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7))
    (h3 : ¬∃ (x1 : List (BitVec (24 : ℕ))),
      x1.length = (24 : ℕ) ∧
      List.take (10 : ℕ) x1 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧
      (∃ (x6 : BitVec (24 : ℕ)) (x7 : BitVec (24 : ℕ)), x6 ∈ List.take (10 : ℕ) x1 ∧ x7 ∈ List.take (10 : ℕ) x1 ∧ x1.getD (10 : ℕ) (0 : BitVec (24 : ℕ)) = x6 ||| x7) ∧
      x1.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧
      ((0 : BitVec (24 : ℕ)) :: x1).Nodup ∧
      ∀ (x2 : ℕ), (0 : ℕ) < x2 → x2 < (15 : ℕ) →
        have x5 : BitVec (24 : ℕ) := x1.getD ((9 : ℕ) + x2) (0 : BitVec (24 : ℕ));
        x5 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x6 : BitVec (24 : ℕ)) (x7 : BitVec (24 : ℕ)), x6 ∈ List.take ((9 : ℕ) + x2) x1 ∧ x7 ∈ List.take ((9 : ℕ) + x2) x1 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7)) :
    ¬∃ (x1 : List (BitVec (24 : ℕ))),     x1.length = (24 : ℕ) ∧       List.take (10 : ℕ) x1 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧         x1.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧           ((0 : BitVec (24 : ℕ)) :: x1).Nodup ∧             ∀ (x2 : ℕ),               (0 : ℕ) < x2 →                 x2 < (15 : ℕ) →                   have x5 : BitVec (24 : ℕ) := x1.getD ((9 : ℕ) + x2) (0 : BitVec (24 : ℕ));                   x5 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x6 : BitVec (24 : ℕ)) (x7 : BitVec (24 : ℕ)), x6 ∈ List.take ((9 : ℕ) + x2) x1 ∧ x7 ∈ List.take ((9 : ℕ) + x2) x1 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7) := by
  rintro ⟨x1, hlen, htake, hlast, hnd, hstep⟩
  rcases hstep 1 (by omega) (by omega) with hconst | ⟨x6, x7, hx6, hx7, hand | hor⟩
  · exact h1 ⟨x1, hlen, htake, hconst, hlast, hnd, hstep⟩
  · exact h2 ⟨x1, hlen, htake, ⟨x6, x7, hx6, hx7, hand⟩, hlast, hnd, hstep⟩
  · exact h3 ⟨x1, hlen, htake, ⟨x6, x7, hx6, hx7, hor⟩, hlast, hnd, hstep⟩
