import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

-- The list encodes each Petersen edge by ten times its first endpoint plus its second.
-- The marked AND fires on one nonedge and on at least two distinct edges.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_2590_317
    (normalize : let E := ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).map fun n => (Fin.ofNat 10 (n / 10), Fin.ofNat 10 (n % 10))
      let good (C : Circuit) := ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = E.any (fun p => x p.1 && x p.2)
      let hot (D : Circuit) := ∃ (k : ℕ) (g : Gate), D.gates[k]? = some g ∧ g.op = GateOp.and ∧
        (D.wires (List.ofFn (pairInput 0 2 : Fin 10 → Bool))).getD (10+k) false = true ∧
        2 ≤ (E.filter (fun p => (D.wires (List.ofFn (pairInput p.1 p.2))).getD (10+k) false)).length
      ∀ C : Circuit, Monotone2 C → C.size ≤ 19 → good C → ∃ D : Circuit, Monotone2 D ∧ D.size=C.size ∧ good D ∧ hot D)
    (exclude : let E := ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).map fun n => (Fin.ofNat 10 (n / 10), Fin.ofNat 10 (n % 10))
      let good (C : Circuit) := ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = E.any (fun p => x p.1 && x p.2)
      let hot (D : Circuit) := ∃ (k : ℕ) (g : Gate), D.gates[k]? = some g ∧ g.op = GateOp.and ∧
        (D.wires (List.ofFn (pairInput 0 2 : Fin 10 → Bool))).getD (10+k) false = true ∧
        2 ≤ (E.filter (fun p => (D.wires (List.ofFn (pairInput p.1 p.2))).getD (10+k) false)).length
      ∀ D : Circuit, Monotone2 D → D.size ≤ 19 → hot D → ¬ good D) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → ¬∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C hm hs correct
  let E := ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).map fun n => (Fin.ofNat 10 (n / 10), Fin.ofNat 10 (n % 10))
  have enum : ∀ x : Fin 10 → Bool, (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x = E.any (fun p => x p.1 && x p.2) := by
    decide +kernel
  obtain ⟨D,hd,hsize,hgood,hhot⟩ := normalize C hm hs (fun x => (correct x).trans (enum x))
  exact exclude D hd (hsize.trans_le hs) hhot hgood
