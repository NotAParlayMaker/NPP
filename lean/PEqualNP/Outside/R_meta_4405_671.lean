import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4405_671
    (erase : ∀ (n : ℕ) (C : Circuit) (pins : List (Option (Fin n))) (zeros : List ℕ),
      FanInTwo C → (∀ i ∈ zeros, pins[i]? = some none) →
      (∃ x y : Fin n → Bool,
        C.eval (pins.map (fun p => p.elim false x)) ≠ C.eval (pins.map (fun p => p.elim false y))) →
      ∃ D : Circuit, FanInTwo D ∧ D.size +
        (C.gates.filter (fun g => zeros.any (fun i =>
          (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains i))).length ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (pins.map (fun p => p.elim false x)))
    (theta : ∀ s : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool =>
      x 0 && x 2 || x 2 && x 1 || x 0 && x 3 || x 3 && x 4 ||
      x 4 && x 1 || x 0 && x 5 || x 5 && x 6 || x 6 && x 1) s → 11 ≤ s)
    (few :
      let target (x : Fin 9 → Bool) :=
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ m ∈ ([81, 84, 208] : List ℕ), ∀ C : Circuit, FanInTwo C →
        (C.gates.filter (fun g => ([4, 6, 9] : List ℕ).any (fun i =>
          (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains i))).length ≤ 2 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 || x 6,
          (List.finRange 9).any (fun i => m.testBit i.val && x i)]) = target x) → 14 ≤ C.size)
    (pairs :
      let target (x : Fin 9 → Bool) :=
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ m ∈ ([3, 5, 9, 33, 65, 129, 257, 36, 132] : List ℕ), ∀ C : Circuit, FanInTwo C →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 || x 6,
          (List.finRange 9).any (fun i => m.testBit i.val && x i)]) = target x) → 14 ≤ C.size) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : ℕ → (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : ℕ) (x3 : Fin (9 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)), (List.finRange (9 : ℕ)).any fun (x4 : Fin (9 : ℕ)) => x2.testBit ↑x4 && x3 x4]; ∀ x3 ∈ [(3 : ℕ), (5 : ℕ), (9 : ℕ), (33 : ℕ), (65 : ℕ), (129 : ℕ), (257 : ℕ), (36 : ℕ), (132 : ℕ), (81 : ℕ), (84 : ℕ), (208 : ℕ)], ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → (∀ (x7 : Fin (9 : ℕ) → Bool), x5.eval (x2 x3 x7) = x1 x7) → (14 : ℕ) ≤ x5.size := by
  dsimp only
  intro m hm C fan correct
  let target : (Fin 9 → Bool) → Bool := fun x =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let args (m : ℕ) (x : Fin 9 → Bool) : List Bool :=
    List.ofFn x ++ [x 4 || x 6, (List.finRange 9).any (fun i => m.testBit i.val && x i)]
  let thetaValue (x : Fin 7 → Bool) : Bool :=
    x 0 && x 2 || x 2 && x 1 || x 0 && x 3 || x 3 && x 4 ||
    x 4 && x 1 || x 0 && x 5 || x 5 && x 6 || x 6 && x 1
  let lift (x : Fin 7 → Bool) : Fin 9 → Bool :=
    ![x 4, x 3, x 0, x 5, false, x 1, false, x 2, x 6]
  let pins (k : Fin 7) : List (Option (Fin 7)) :=
    [some 4, some 3, some 0, some 5, none, some 1, none, some 2, some 6, none, some k]
  have eqTarget : ∀ x : Fin 9 → Bool,
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) = target x := by
    decide +kernel
  have sameTarget (x : Fin 9 → Bool) : C.eval (args m x) = target x :=
    (correct x).trans (eqTarget x)
  have hmask :
      m ∈ ([3, 5, 9, 33, 65, 129, 257, 36, 132] : List ℕ) ∨
      m ∈ ([81, 84, 208] : List ℕ) := by
    exact List.mem_append.mp hm
  rcases hmask with hpair | htriple
  · exact pairs m hpair C fan sameTarget
  · let readers := (C.gates.filter (fun g => ([4, 6, 9] : List ℕ).any (fun i =>
      (if g.op.eval [false] then g.inputs.take 1 else g.inputs).contains i))).length
    by_cases hread : readers ≤ 2
    · exact few m htriple C fan hread sameTarget
    · have cof : ∀ x, target (lift x) = thetaValue x := by decide +kernel
      have bridge : ∃ k : Fin 7, ∀ x : Fin 7 → Bool,
          args m (lift x) = (pins k).map (fun p => p.elim false x) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at htriple
        rcases htriple with rfl | rfl | rfl
        · exact ⟨4, by decide +kernel⟩
        · exact ⟨0, by decide +kernel⟩
        · exact ⟨2, by decide +kernel⟩
      obtain ⟨k, hk⟩ := bridge
      have fixed (i : ℕ) (hi : i ∈ ([4, 6, 9] : List ℕ)) : (pins k)[i]? = some none := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> rfl
      have spec (x : Fin 7 → Bool) :
          C.eval ((pins k).map (fun p => p.elim false x)) = thetaValue x := by
        rw [← hk, sameTarget, cof]
      have varying : ∃ x y : Fin 7 → Bool,
          C.eval ((pins k).map (fun p => p.elim false x)) ≠
          C.eval ((pins k).map (fun p => p.elim false y)) := by
        refine ⟨fun _ => false, fun _ => true, ?_⟩
        rw [spec, spec]
        decide +kernel
      obtain ⟨D, hD, saved, computes⟩ := erase 7 C (pins k) [4, 6, 9] fan fixed varying
      have hsize : 11 ≤ D.size := theta D.size
        ⟨D, hD, le_rfl, fun x => (computes x).trans (spec x)⟩
      change D.size + readers ≤ C.size at saved
      omega
