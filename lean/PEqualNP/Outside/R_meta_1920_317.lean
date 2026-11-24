import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.R_meta_1920_317
    (projection : ∀ (D : Circuit) (f : (Fin 9 → Bool) → Bool),
      FanInTwo D → D.size=14 → D.output=23 →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!(x 4)]) = f x) →
      (¬ HasCircuitSize 8 (fun z => f ((4 : Fin 9).insertNth false z)) 12) →
      ∃ (s : Bool) (C : Circuit), FanInTwo C ∧ C.size=14 ∧ C.output=22 ∧
        (C.gates.filter (fun g => g.inputs.contains 4)).length ≤ 1 ∧
        ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
          f (fun i => if i = 4 && s then !(x i) else x i))
    (minor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
      (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (exclude : ∀ (s : Bool) (C : Circuit), FanInTwo C → C.size = 14 → C.output = 22 →
      (C.gates.filter (fun g => g.inputs.contains 4)).length ≤ 1 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠
      (let y := if s then !(x 4) else x 4
       (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && y) || (y && x 0) ||
       (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
       (x 6 && x 8) || (x 8 && x 5))) :
∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate), x1.length = (15 : ℕ) → x1.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(4 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x4 : Fin x1.length), (∃ (x5 : ℕ) (x6 : ℕ), x5 ≤ x6 ∧ x6 ≤ (9 : ℕ) + ↑x4 ∧ (x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate })) ∨ ∃ x5 ≤ (9 : ℕ) + ↑x4, x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }) → ∃ (x5 : Fin (9 : ℕ) → Bool), { gates := x1, output := (23 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x5) ≠ (fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) x5 := by
  intro all len head form
  by_contra! agree
  let f := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)
  have ok (g : Gate) (hg : g∈all) :
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length≤2 := by
    obtain ⟨j,rfl⟩ := List.mem_iff_get.1 hg
    rcases form j with ⟨a,b,_,_,h|h⟩ | ⟨a,_,h⟩ <;> rw [h] <;> simp
  cases all with
  | nil => contradiction
  | cons g gs =>
    have hfirst : g=⟨.not,[4]⟩ := Option.some.inj head
    subst g
    let D : Circuit := ⟨gs,23⟩
    have shape : FanInTwo D := fun t ht => ok t (List.mem_cons_of_mem _ ht)
    have value (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [!(x 4)]) = f x := agree x
    have eq : (fun z : Fin 8 → Bool => f ((4 : Fin 9).insertNth false z)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
       (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
       (x 5 && x 7) || (x 7 && x 4)) := by decide +kernel
    obtain ⟨s,C,fan,sz,out,reads,realizes⟩ := projection D f shape
      (by change gs.length=14; simpa using len) rfl value (by rw [eq]; exact minor)
    obtain ⟨x,bad⟩ := exclude s C fan sz out reads
    apply bad
    rw [realizes]
    cases s <;> rfl
