import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7150 : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (16 : ℕ), x1 % (16 : ℕ))) [(9 : ℕ), (10 : ℕ), (20 : ℕ), (24 : ℕ), (37 : ℕ), (42 : ℕ), (54 : ℕ), (55 : ℕ), (72 : ℕ), (74 : ℕ), (88 : ℕ), (89 : ℕ), (103 : ℕ), (106 : ℕ), (121 : ℕ), (137 : ℕ)]); ∀ (x2 : Finset (Fin (11 : ℕ))), x2.card ≤ (4 : ℕ) + List.countP (fun (x3 : ℕ) => Decidable.decide (x3 ≤ (x2.sym2 ∩ x1.edgeFinset).card)) [(1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (8 : ℕ), (12 : ℕ), (16 : ℕ)] := by
  dsimp only
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  decide +kernel
