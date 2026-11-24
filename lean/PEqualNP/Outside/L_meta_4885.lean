import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4885

theorem PEqualNP.Outside.L_meta_4885 :
  (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
   have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true;
   ∃ x3 ∈ [(1 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ))],
     ∃ (x4 : Bool),
       (have x5 : List ((Fin (26 : ℕ) → Bool) → Bool) := (List.ofFn fun (x5 : Fin (26 : ℕ)) (x6 : Fin (26 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (26 : ℕ) → Bool) => if x4 = Bool.true then x5 (0 : Fin (26 : ℕ)) || x5 x3 else x5 (0 : Fin (26 : ℕ)) && x5 x3];
        have x6 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map (fun (x6 : (Fin (26 : ℕ) → Bool) → Bool) (x7 : Bool) => {x8 : Fin (26 : ℕ) → Bool | x6 x8 = x7}) x5;
        ∃ (x7 : List (Bool → Set (Fin (26 : ℕ) → Bool))) (x8 : Bool → Set (Fin (26 : ℕ) → Bool)),
          x7.length ≤ (62 : ℕ) ∧
          x8 ∈ x6 ++ x7 ∧
          (∀ (x9 : Fin x7.length),
            (have x10 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x6 ++ List.take (↑x9) x7;
             ∃ x11 ∈ x10, ∃ x12 ∈ x10, ∃ (x13 : Bool), ∀ (x14 : Bool), x7.get x9 x14 ⊆ if x14 = x13 then x11 x14 ∪ x12 x14 else x11 x14 ∩ x12 x14)) ∧
          ∀ (x9 : Fin (26 : ℕ) → Bool), (Minimal x2 x9 → x9 ∈ x8 Bool.true) ∧ (Maximal (fun (x10 : Fin (26 : ℕ) → Bool) => ¬x2 x10) x9 → x9 ∈ x8 Bool.false))) := by
  sorry

end PEqualNP.Outside.L_meta_4885