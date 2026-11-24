import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pinning the first variable bounds the number of gates that can read a fixed input.
-- An extra input is a constant, a copy of an input or a conjunction with the complemented first input.
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_5130_519
    (coverage : ∀ columns : List (BitVec 29), columns = [503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407] →
      let raw := columns.take 9
      let pairs := raw.flatMap fun a => (raw.filter (fun b => a != b)).map (fun b => a &&& b)
      let pool := 0 :: columns
      let admitted := (536870911 :: pool.flatMap (fun a => pool.map (fun b => a &&& b))).filter
        (fun u => decide (u ∉ pairs))
      let signatures : List ℕ := [0, 536870911, 503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407, 18022409, 8912915, 3473478, 30015492, 983200, 7078152, 24117296, 25166272]
      ∀ t ∈ admitted, ∃ k : Fin 20, BitVec.ofNat 29 (signatures.getD k.val 0) = t)
    (tight : let seed : List (BitVec 29) := [503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407]
      let signatures : List ℕ := [0, 536870911, 503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407, 18022409, 8912915, 3473478, 30015492, 983200, 7078152, 24117296, 25166272]
      let acceptsRows := fun (k : Fin 20) (C : Circuit) =>
        ∀ r : Fin 29, C.eval ((seed ++ [BitVec.ofNat 29 (signatures.getD k.val 0)]).map (fun z => z.getLsbD r.val)) =
          (65535 : BitVec 29).getLsbD r.val
      let pins := fun (k : Fin 20) (g : Gate) => g.inputs.any fun i =>
        decide (i = 0 ∨ i = 9 ∨ (i = 10 ∧ (k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 11)))
      let noNeg := fun (k : Fin 20) (C : Circuit) =>
        ∀ g ∈ C.gates, 9 ∉ g.inputs ∧ (k.val = 11 → 10 ∉ g.inputs)
      ∀ (C : Circuit) (k : Fin 20), Monotone2 C → C.size ≤ 13 → acceptsRows k C →
        C.size = 13 ∧ C.gates.countP (pins k) = 1 ∧ noNeg k C)
    (aliasOrConstant : let seed : List (BitVec 29) := [503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407]
      let signatures : List ℕ := [0, 536870911, 503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407, 18022409, 8912915, 3473478, 30015492, 983200, 7078152, 24117296, 25166272]
      let acceptsRows := fun (k : Fin 20) (C : Circuit) =>
        ∀ r : Fin 29, C.eval ((seed ++ [BitVec.ofNat 29 (signatures.getD k.val 0)]).map (fun z => z.getLsbD r.val)) =
          (65535 : BitVec 29).getLsbD r.val
      let pins := fun (k : Fin 20) (g : Gate) => g.inputs.any fun i =>
        decide (i = 0 ∨ i = 9 ∨ (i = 10 ∧ (k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 11)))
      let noNeg := fun (k : Fin 20) (C : Circuit) =>
        ∀ g ∈ C.gates, 9 ∉ g.inputs ∧ (k.val = 11 → 10 ∉ g.inputs)
      ∀ (C : Circuit) (k : Fin 20), k.val ≤ 11 → Monotone2 C → C.size = 13 → C.gates.countP (pins k) = 1 → noNeg k C →
        ¬acceptsRows k C)
    (masked : let seed : List (BitVec 29) := [503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407]
      let signatures : List ℕ := [0, 536870911, 503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407, 18022409, 8912915, 3473478, 30015492, 983200, 7078152, 24117296, 25166272]
      let acceptsRows := fun (k : Fin 20) (C : Circuit) =>
        ∀ r : Fin 29, C.eval ((seed ++ [BitVec.ofNat 29 (signatures.getD k.val 0)]).map (fun z => z.getLsbD r.val)) =
          (65535 : BitVec 29).getLsbD r.val
      let pins := fun (k : Fin 20) (g : Gate) => g.inputs.any fun i =>
        decide (i = 0 ∨ i = 9 ∨ (i = 10 ∧ (k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 11)))
      let noNeg := fun (k : Fin 20) (C : Circuit) =>
        ∀ g ∈ C.gates, 9 ∉ g.inputs ∧ (k.val = 11 → 10 ∉ g.inputs)
      ∀ (C : Circuit) (k : Fin 20), 11 < k.val → Monotone2 C → C.size = 13 → C.gates.countP (pins k) = 1 → noNeg k C →
        ¬acceptsRows k C)
    : have x1 : List (BitVec (29 : ℕ)) := [(503381504 : BitVec (29 : ℕ)), (18022921 : BitVec (29 : ℕ)), (176694291 : BitVec (29 : ℕ)), (70599750 : BitVec (29 : ℕ)), (30017540 : BitVec (29 : ℕ)), (987296 : BitVec (29 : ℕ)), (107774216 : BitVec (29 : ℕ)), (359669808 : BitVec (29 : ℕ)), (427868608 : BitVec (29 : ℕ)), (33489407 : BitVec (29 : ℕ))]; have x2 : List (BitVec (29 : ℕ)) := List.take (9 : ℕ) x1; have x3 : List (BitVec (29 : ℕ)) := List.flatMap (fun (x3 : BitVec (29 : ℕ)) => List.map (fun (x4 : BitVec (29 : ℕ)) => x3 &&& x4) (List.filter (fun (x4 : BitVec (29 : ℕ)) => x3 != x4) x2)) x2; have x4 : List (BitVec (29 : ℕ)) := (0 : BitVec (29 : ℕ)) :: x1; have x5 : List (BitVec (29 : ℕ)) := (536870911 : BitVec (29 : ℕ)) :: List.flatMap (fun (x5 : BitVec (29 : ℕ)) => List.map (fun (x6 : BitVec (29 : ℕ)) => x5 &&& x6) x4) x4; ∀ x6 ∈ List.filter (fun (x7 : BitVec (29 : ℕ)) => Decidable.decide (x7 ∉ x3)) x5, ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 → (12 : ℕ) ≤ x8.size → x8.size ≤ (13 : ℕ) → ¬∀ (x12 : Fin (29 : ℕ)), x8.eval (List.map (fun (x13 : BitVec (29 : ℕ)) => x13.getLsbD ↑x12) (x1 ++ [x6])) = BitVec.getLsbD (65535 : BitVec (29 : ℕ)) ↑x12 := by
  dsimp only
  intro t ht C mono _lo hi fits
  let seed : List (BitVec 29) := [503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407]
  let signatures : List ℕ := [0, 536870911, 503381504, 18022921, 176694291, 70599750, 30017540, 987296, 107774216, 359669808, 427868608, 33489407, 18022409, 8912915, 3473478, 30015492, 983200, 7078152, 24117296, 25166272]
  obtain ⟨k,indexed⟩ := coverage seed rfl t ht
  have rows (r : Fin 29) :
      C.eval ((seed ++ [BitVec.ofNat 29 (signatures.getD k.val 0)]).map (fun z => z.getLsbD r.val)) =
        (65535 : BitVec 29).getLsbD r.val := by
    rw [indexed]
    exact fits r
  obtain ⟨cs,once,noComplement⟩ := tight C k mono hi rows
  by_cases mask : k.val ≤ 11
  · exact aliasOrConstant C k mask mono cs once noComplement rows
  · exact masked C k (by omega) mono cs once noComplement rows
