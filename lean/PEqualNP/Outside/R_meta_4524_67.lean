import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Cut out the last inverter. The remaining suffix is monotone on the
-- wires at the cut, including the complemented input of the inverter.
-- Its truth sets need only fresh intersections or unions. The test
-- space has 256 rows and the two portions share twelve gates.
theorem PEqualNP.Outside.R_meta_4524_67
    (splitLast : ∀ (n : ℕ) (C : Circuit), FanInTwo C → (∃ g ∈ C.gates, g.op = GateOp.not) →
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!(P.eval (List.ofFn x))]))
    (encode : ∀ (n w : ℕ) (b : (Fin n → Bool) → List Bool), (∀ x, (b x).length = w) →
    ∀ Q : Circuit, Monotone2 Q →
    let rows : Finset (Fin n → Bool) := Finset.univ
    let B := (∅ : Finset (Fin n → Bool)) :: Finset.univ :: (List.range w).map (fun i => rows.filter fun x : Fin n → Bool => (b x).getD i false)
    ∃ L : List (Finset (Fin n → Bool)), L.length ≤ Q.size ∧ L.Nodup ∧
      (∀ z ∈ L, z ∉ B) ∧ (∀ j : Fin L.length, let A := B ++ L.take j.val
        ∃ a ∈ A, ∃ c ∈ A, L.get j = a ∩ c ∨ L.get j = a ∪ c) ∧
      (rows.filter fun x : Fin n → Bool => Q.eval (b x)) ∈ B ++ L)
    (exclude : ∀ P : Circuit, FanInTwo P → P.size ≤ 12 →
    let b := fun (x : Fin 8 → Bool) => P.wires (List.ofFn x) ++ [!(P.eval (List.ofFn x))]
    let rows : Finset (Fin 8 → Bool) := Finset.univ
    let B := (∅ : Finset (Fin 8 → Bool)) :: Finset.univ :: (List.range (8+P.size+1)).map (fun i => rows.filter fun x : Fin 8 → Bool => (b x).getD i false)
    let F := rows.filter (fun (x : Fin 8 → Bool) => ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any
        (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))))
    ∀ L : List (Finset (Fin 8 → Bool)), L.length + P.size ≤ 12 → L.Nodup →
      (∀ z ∈ L, z ∉ B) → (∀ j : Fin L.length, let A := B ++ L.take j.val
        ∃ a ∈ A, ∃ c ∈ A, L.get j = a ∩ c ∨ L.get j = a ∪ c) → F ∉ B ++ L) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (13 : ℕ) → (∀ (x4 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (8 : ℕ) → Bool) => x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ))) x4) → ∀ x5 ∈ x1.gates, x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
  classical
  intro C fan size correct g mem neg
  obtain ⟨P, Q, pFan, qMono, count, same⟩ := splitLast 8 C fan ⟨g, mem, neg⟩
  let b := fun (x : Fin 8 → Bool) => P.wires (List.ofFn x) ++ [!(P.eval (List.ofFn x))]
  have lengths : ∀ (gs : List Gate) (xs : List Bool),
      (gs.foldl (fun (w : List Bool) (g : Gate) =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro xs
      rw [List.foldl_cons, ih]
      simp [Nat.add_comm, Nat.add_left_comm]
  have blen (x : Fin 8 → Bool) : (b x).length = 8 + P.size + 1 := by
    dsimp only [b]
    rw [List.length_append, List.length_singleton]
    change (P.gates.foldl _ (List.ofFn x)).length + 1 = _
    rw [lengths, List.length_ofFn]
    rfl
  obtain ⟨L, length, nodup, fresh, builds, out⟩ := encode 8 _ b blen Q qMono
  have eq : (Finset.univ.filter (fun (x : Fin 8 → Bool) => ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any
        (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10))))) =
      (Finset.univ.filter fun x : Fin 8 → Bool => Q.eval (b x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show Q.eval (b x) = C.eval (List.ofFn x) from (same x).symm, correct x]
    simp [List.any_cons, Bool.or_assoc]
    rfl
  exact exclude P pFan (by omega) L (by omega) nodup fresh builds (eq ▸ out)
