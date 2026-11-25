import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17197
def seeds : List (List ℕ) := [[],[0],[13],[0,1],[0,2],[0,13],[0,14],[0,15],[0,17],[0,20],[13,14],[13,15]]
def row (p : Fin 13) := (List.ofFn (fun i : Fin 13 => decide (i=p))) ++ List.ofFn (fun i : Fin 13 => decide (i=p))
def aug (p : Fin 13) (s : List ℕ) := row p ++ [s.any fun i => (row p).getD i false]

theorem separate : seeds.all (fun s => decide (∀ i : Fin 27,
    ¬((aug 10 s).getD i false=true ∧ (aug 11 s).getD i false=true))) = true := by decide +kernel
end PEqualNP.Outside.L_meta_17197

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_17197
theorem PEqualNP.Outside.L_meta_17197 :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), ∀ x6 ∈ (x4.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5; have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]]; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ x5, PEqualNP.MetaComplexity.Monotone2 x6 → x4 x6 → x3 x6 x7 → x6.gates = [] → (63 : ℕ) ≤ x6.size := by
  dsimp only
  intro C s hs _ _ correct empty
  have pos (p : Fin 13) : (aug p s).getD C.output false=true := by
    have test := correct.1 p p (by simp)
    simpa only [Circuit.eval,Circuit.wires,empty,List.foldl_nil,aug,row] using test
  by_cases small : C.output<27
  · have dis := of_decide_eq_true (List.all_eq_true.mp separate s hs)
    exact (dis ⟨C.output,small⟩ ⟨pos 10,pos 11⟩).elim
  · have len : (aug 10 s).length=27 := by simp [aug,row]
    have bad := pos 10
    rw [List.getD_eq_default _ _ (by omega)] at bad
    contradiction
