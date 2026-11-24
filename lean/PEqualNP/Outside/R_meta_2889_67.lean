import Mathlib.Tactic
import PEqualNP.Defs

-- The seven columns distinguish 78 test rows of the theta graph left by fixing input zero.
-- Both polarities of each previous wire and both constants are available at no gate cost.
theorem PEqualNP.Outside.R_meta_2889_67
    (projection :
      let w : List (BitVec 78) := [77920222974858904429981,83181564482533640438,175486507760930102481191,28592957965639045029432,265342003954011127947200,1175982184299908554752,301050865534739561840640]
      let available := fun (l : List (BitVec 78)) (x : BitVec 78) =>
        x = 0 ∨ x = ~~~(0 : BitVec 78) ∨ ∃ a ∈ l, x = a ∨ x = ~~~a
      let valid := fun (t : List (BitVec 78)) => ∀ j : Fin t.length,
        ∃ a, available (w ++ t.take j.val) a ∧ ∃ b, available (w ++ t.take j.val) b ∧
          (t.get j = a &&& b ∨ t.get j = a ||| b)
      (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (12 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (0 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)))) → ∃ t : List (BitVec 78), t.length ≤ 10 ∧ valid t ∧ available (w ++ t) 2251799813685247)
    (lower :
      let w : List (BitVec 78) := [77920222974858904429981,83181564482533640438,175486507760930102481191,28592957965639045029432,265342003954011127947200,1175982184299908554752,301050865534739561840640]
      let available := fun (l : List (BitVec 78)) (x : BitVec 78) =>
        x = 0 ∨ x = ~~~(0 : BitVec 78) ∨ ∃ a ∈ l, x = a ∨ x = ~~~a
      let valid := fun (t : List (BitVec 78)) => ∀ j : Fin t.length,
        ∃ a, available (w ++ t.take j.val) a ∧ ∃ b, available (w ++ t.take j.val) b ∧
          (t.get j = a &&& b ∨ t.get j = a ||| b)
      ¬ ∃ t : List (BitVec 78), t.length ≤ 10 ∧ valid t ∧ available (w ++ t) 2251799813685247) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (12 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (0 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ))) := by
  intro counterexample
  exact lower (projection counterexample)
