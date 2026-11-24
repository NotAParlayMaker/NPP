import Mathlib.LinearAlgebra.Matrix.Notation
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3174_315
    (rename : ∀ (p : Fin 9 → Fin 9) (C : Circuit), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
        ∀ (x : Fin 9 → Bool) (u v : Bool),
          D.eval (List.ofFn x ++ [u,v]) = C.eval (List.ofFn (x ∘ p) ++ [u,v]))
    (bound : ∀ (j : Fin 9), j ∈ ([2,3,8] : List (Fin 9)) →
      ∀ D : Circuit, FanInTwo D → D.size ≤ 13 → ∃ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [!x 0, x 1 || x j]) ≠
          ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
            List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) :
∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       ((¬∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) ∧ ¬∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro ops hl hs hm C hf hc
  let edge := fun (x : Fin 9 → Bool) =>
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let swap : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]
  have sym (x : Fin 9 → Bool) : edge (x ∘ swap) = edge x := by
    change ((x 0 && x 5) || ((x 5 && x 8) || ((x 8 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 1) || ((x 5 && x 7) || ((x 8 && x 6) || ((x 3 && x 2) || ((x 1 && x 6) || ((x 7 && x 2) || ((x 2 && x 1) || false)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || ((x 8 && x 5) || false))))))))))))
    simp only [Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  have usePair (p : Fin 9 → Fin 9) (j : Fin 9) (hj : j ∈ ([2,3,8] : List (Fin 9)))
      (hz : p 0 = 0) (he : ∀ x, edge (x ∘ p) = edge x)
      (hv : ∀ x : Fin 9 → Bool,
        GateOp.or.eval (ops.map (fun i => (List.ofFn (x ∘ p) ++ [!(x ∘ p) 0]).getD i false)) =
          (x 1 || x j)) : ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!x 0]
        C.eval (w ++ [GateOp.or.eval (ops.map (fun i => w.getD i false))]) ≠ edge x := by
    obtain ⟨D, hd, hsz, hD⟩ := rename p C hf
    obtain ⟨x,hx⟩ := bound j hj D hd (by simpa only [hsz] using hc)
    refine ⟨x ∘ p, ?_⟩
    dsimp only
    rw [hv, he, List.append_assoc]
    change C.eval (List.ofFn (x ∘ p) ++ [!x (p 0), x 1 || x j]) ≠ edge x
    rw [hz, ← hD]
    exact hx
  have hfinal : ∃ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [!x 0]
      C.eval (w ++ [GateOp.or.eval (ops.map (fun i => w.getD i false))]) ≠ edge x := by
    obtain ⟨a,b,rfl⟩ : ∃ a b : ℕ, ops = [a,b] := by
      cases ops with
      | nil => simp at hl
      | cons a tail =>
        cases tail with
        | nil => simp at hl
        | cons b tail =>
          cases tail with
          | nil => exact ⟨a,b,rfl⟩
          | cons c cs => simp at hl
    have ha := hs a (by simp)
    have hb := hs b (by simp)
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      try (first | exact (hm.1 (by decide)).elim | exact (hm.2 (by decide)).elim)
    all_goals
      first
      | (apply usePair id 2 (by decide) rfl (fun _ => rfl); intro x; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]; first | rfl | exact Bool.or_comm _ _)
      | (apply usePair id 3 (by decide) rfl (fun _ => rfl); intro x; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]; first | rfl | exact Bool.or_comm _ _)
      | (apply usePair id 8 (by decide) rfl (fun _ => rfl); intro x; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]; first | rfl | exact Bool.or_comm _ _)
      | (apply usePair swap 2 (by decide) rfl sym; intro x; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]; first | rfl | exact Bool.or_comm _ _)
      | (apply usePair swap 3 (by decide) rfl sym; intro x; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]; first | rfl | exact Bool.or_comm _ _)
      | (apply usePair swap 8 (by decide) rfl sym; intro x; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]; first | rfl | exact Bool.or_comm _ _)
  obtain ⟨x,hx⟩ := hfinal
  refine ⟨x, ?_⟩
  simpa only [edge, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using hx
