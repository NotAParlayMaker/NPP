import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The extra input at position 25 is the first gate. The twelve pair codes
-- represent unordered input pairs under incidence and pencil symmetries.
theorem PEqualNP.Outside.R_meta_2215_421
  (join : ∀ (C : Circuit) (g : Gate), Monotone2 C →
    (g.op = .and ∨ g.op = .or) → g.inputs.length ≤ 2 →
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size+1 ∧ D.output = C.output ∧
      ∀ x : List Bool, D.wires x = C.wires (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]))
  (find : ∃ (C : Circuit) (q a b : ℕ) (g : Gate),
    (25*a+b) ∈ ([0,1,2,12,13,14,16,312,313,314,364,366] : List ℕ) ∧ b < 25 ∧
    (g.op = .and ∨ g.op = .or) ∧ (g.inputs=[] ∨ g.inputs=[a,b]) ∧
    Monotone2 C ∧ C.size ≤ 60 ∧ C.output < 26+C.size ∧ q < 26+C.size ∧
    ∀ x : Fin 25 → Bool,
      let X := List.ofFn x
      let Y := X ++ [g.op.eval (g.inputs.map fun i => X.getD i false)]
      (C.eval Y = true ↔ ∃ i j : Fin 25,
        (i.val<12 ∧ 12≤j.val ∧ (i.val+j.val+2)%13 ∈ ([0,1,3,9] : List ℕ)) ∧ x i=true ∧ x j=true) ∧
      (C.eval Y = false → (C.wires Y).getD q false = (x 12 || x 13 || x 15 || x 21))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  obtain ⟨C,q,a,b,g,_,_,hop,ins,hm,hs,ho,hq,hf⟩ := find
  have arity : g.inputs.length ≤ 2 := by rcases ins with e|e <;> simp [e]
  obtain ⟨D,hd,sz,out,run⟩ := join C g hm hop arity
  refine ⟨D,q,hd,by omega,by omega,by omega,?_⟩
  intro x
  dsimp only
  have eqv := run (List.ofFn x)
  change ((D.wires (List.ofFn x)).getD D.output false = true ↔ _) ∧ ((D.wires (List.ofFn x)).getD D.output false = false → _)
  rw [eqv,out]
  exact hf x
