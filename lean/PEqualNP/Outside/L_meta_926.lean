import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_926

-- A program entry specifies one binary gate and its two input wires.
private abbrev Entry := Bool × ℕ × ℕ
private def a (i j : ℕ) : Entry := (true, i, j)
private def o (i j : ℕ) : Entry := (false, i, j)
private def gate (e : Entry) : Gate := ⟨if e.1 then .and else .or, [e.2.1, e.2.2]⟩
private def program (n : ℕ) (gs : List Entry) : Circuit := ⟨gs.map gate, n + gs.length - 1⟩

private theorem certify {n : ℕ} {f : (Fin n → Bool) → Bool} (gs : List Entry)
    (correct : ∀ x, (program n gs).eval (List.ofFn x) = f x) : HasCircuitSize n f gs.length := by
  refine ⟨program n gs, ?_, ?_, correct⟩
  · intro g hg
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hg
    cases h : e.1 <;> simp [gate, h]
  · simp [program, Circuit.size]

end PEqualNP.Outside.L_meta_926

open PEqualNP.Outside.L_meta_926 in
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_926 :
    (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧
    (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) := by
  -- For each graph, partition its edges into stars centered in a vertex cover.
  -- OR the leaves of each star, AND with its center, then OR the star outputs.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact certify [a 0 1] (by decide +kernel)
  · exact certify [o 1 2, a 0 3] (by decide +kernel)
  · exact certify [o 1 2, a 0 3, a 1 2, o 4 5] (by decide +kernel)
  · exact certify [a 0 1, a 2 3, o 4 5] (by decide +kernel)
  · exact certify [o 1 2, o 4 3, a 0 5] (by decide +kernel)
  · exact certify [o 1 2, a 0 4, a 1 3, o 5 6] (by decide +kernel)
  · exact certify [o 1 2, o 4 3, a 0 5, a 1 2, o 6 7] (by decide +kernel)
  · exact certify [o 1 2, a 0 5, a 3 4, o 6 7] (by decide +kernel)
  · exact certify [o 1 2, o 5 3, o 6 4, a 0 7] (by decide +kernel)
  · exact certify [o 1 2, o 5 3, a 0 6, a 1 4, o 7 8] (by decide +kernel)
  · exact certify [o 1 2, a 0 5, a 1 2, a 3 4, o 6 7, o 9 8] (by decide +kernel)
  · exact certify [o 0 3, a 1 5, o 0 4, a 2 7, o 6 8] (by decide +kernel)
  · exact certify [o 1 2, o 5 3, o 6 4, a 0 7, a 1 2, o 8 9] (by decide +kernel)
  · exact certify [o 1 2, o 5 3, a 0 6, o 2 4, a 1 8, o 7 9] (by decide +kernel)
  · exact certify [o 1 2, o 5 3, a 0 6, a 1 2, a 3 4, o 7 8, o 10 9] (by decide +kernel)
  · exact certify [o 1 2, a 0 5, a 2 4, o 1 4, a 3 8, o 6 7, o 10 9] (by decide +kernel)
  · exact certify [o 1 2, o 5 3, o 6 4, a 0 7, a 1 2, a 3 4, o 8 9, o 11 10] (by decide +kernel)
  · exact certify [a 0 1, a 2 3, a 4 5, o 6 7, o 9 8] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, a 0 7, a 4 5, o 8 9] (by decide +kernel)
  · exact certify [o 1 2, a 0 6, a 1 3, a 4 5, o 7 8, o 10 9] (by decide +kernel)
  · exact certify [o 1 2, a 0 6, o 4 5, a 3 8, o 7 9] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, o 7 4, o 8 5, a 0 9] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, o 7 4, a 0 8, a 1 5, o 9 10] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, a 0 7, a 1 2, a 4 5, o 8 9, o 11 10] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, a 0 7, o 4 5, a 1 9, o 8 10] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, a 0 7, a 1 4, a 2 5, o 8 9, o 11 10] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, a 0 7, o 1 5, a 4 9, o 8 10] (by decide +kernel)
  · exact certify [o 1 2, a 0 6, a 1 2, o 4 5, a 3 9, o 7 8, o 11 10] (by decide +kernel)
  · exact certify [o 1 2, a 0 6, a 2 4, o 1 5, a 3 9, o 7 8, o 11 10] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, o 7 4, o 8 5, a 0 9, a 1 2, o 10 11] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, o 7 4, a 0 8, o 2 5, a 1 10, o 9 11] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, o 7 4, a 0 8, a 1 2, a 3 5, o 9 10, o 12 11] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, a 0 7, o 2 4, a 1 9, a 2 5, o 8 10, o 12 11] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, a 0 7, o 2 4, a 1 9, a 3 5, o 8 10, o 12 11] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, a 0 7, a 1 2, o 4 5, a 3 10, o 8 9, o 12 11] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, a 0 7, a 1 2, o 3 5, a 4 10, o 8 9, o 12 11] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, a 0 7, a 2 5, o 1 5, a 4 10, o 8 9, o 12 11] (by decide +kernel)
  · exact certify [o 1 2, a 0 6, a 1 2, o 4 5, a 3 9, a 4 5, o 7 8, o 12 10, o 13 11] (by decide +kernel)
  · exact certify [o 1 2, a 0 6, o 1 5, a 3 8, o 2 5, a 4 10, o 7 9, o 12 11] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, o 7 4, o 8 5, a 0 9, a 1 2, a 3 4, o 10 11, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, o 7 4, a 0 8, o 2 5, a 1 10, a 3 4, o 9 11, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, o 6 3, a 0 7, o 2 4, a 1 9, o 3 4, a 5 11, o 8 10, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, a 0 7, a 3 4, a 5 6, o 8 9, o 11 10] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, a 5 6, o 10 11] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, a 1 4, a 5 6, o 9 10, o 12 11] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, o 5 6, a 4 10, o 9 11] (by decide +kernel)
  · exact certify [o 1 2, a 0 7, a 1 2, a 3 4, a 5 6, o 8 9, o 12 10, o 13 11] (by decide +kernel)
  · exact certify [o 0 3, a 1 7, o 0 4, a 2 9, a 5 6, o 8 10, o 12 11] (by decide +kernel)
  · exact certify [o 1 2, a 0 7, a 1 3, o 5 6, a 4 10, o 8 9, o 12 11] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, o 9 5, o 10 6, a 0 11] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, o 9 5, a 0 10, a 1 6, o 11 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, a 1 2, a 5 6, o 10 11, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, o 5 6, a 1 11, o 10 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, a 1 5, a 2 6, o 10 11, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, o 1 6, a 5 11, o 10 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, o 2 4, a 1 10, a 5 6, o 9 11, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, a 1 2, a 3 4, a 5 6, o 9 10, o 13 11, o 14 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, a 1 2, o 5 6, a 4 11, o 9 10, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, o 4 5, a 1 10, a 2 6, o 9 11, o 13 12] (by decide +kernel)
  · exact certify [o 0 4, a 1 7, o 0 5, a 2 9, o 0 6, a 3 11, o 8 10, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, a 2 5, o 1 6, a 4 11, o 9 10, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, o 1 5, o 10 6, a 4 11, o 9 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, a 1 4, o 4 6, a 5 11, o 9 10, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, o 5 6, a 4 10, a 5 6, o 9 11, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, a 0 7, a 1 2, o 4 5, a 3 10, a 4 6, o 8 9, o 13 11, o 14 12] (by decide +kernel)
  · exact certify [o 1 2, a 0 7, a 2 4, o 1 4, a 3 10, a 5 6, o 8 9, o 13 11, o 14 12] (by decide +kernel)
  · exact certify [o 1 2, a 0 7, o 1 5, a 3 9, o 2 6, a 4 11, o 8 10, o 13 12] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, o 9 5, o 10 6, a 0 11, a 1 2, o 12 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, o 9 5, a 0 10, o 2 6, a 1 12, o 11 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, o 9 5, a 0 10, a 1 2, a 3 6, o 11 12, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, o 2 5, o 11 6, a 1 12, o 10 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, o 2 5, a 1 11, a 2 6, o 10 12, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, o 2 5, a 1 11, a 3 6, o 10 12, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, o 2 5, a 1 11, a 5 6, o 10 12, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, a 1 2, o 5 6, a 3 12, o 10 11, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, a 1 2, o 3 6, a 5 12, o 10 11, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, o 5 6, a 1 11, a 5 6, o 10 12, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, o 8 4, a 0 9, a 2 6, o 1 6, a 5 12, o 10 11, o 14 13] (by decide +kernel)
  · exact certify [o 0 2, o 7 4, a 1 8, o 0 5, a 2 10, o 0 6, a 3 12, o 9 11, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, o 2 4, a 1 10, o 5 6, a 3 12, o 9 11, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, o 2 4, a 1 10, o 3 6, a 5 12, o 9 11, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, a 1 2, o 3 5, o 11 6, a 4 12, o 9 10, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, o 4 5, a 1 10, o 2 4, a 6 12, o 9 11, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, a 2 5, o 1 5, o 11 6, a 4 12, o 9 10, o 14 13] (by decide +kernel)
  · exact certify [o 1 2, o 7 3, a 0 8, o 1 6, a 4 10, o 2 6, a 5 12, o 9 11, o 14 13] (by decide +kernel)
