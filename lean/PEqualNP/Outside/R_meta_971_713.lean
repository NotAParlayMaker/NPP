import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16384 in
theorem PEqualNP.Outside.R_meta_971_713
    (normalize : ∀ (rows : Fin 58 → Fin 14 → Bool) (t : Fin 58 → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C → (∀ i, C.eval (List.ofFn (rows i)) = t i) →
      let src : List (Fin 58 → Bool) := (fun _ : Fin 58 => false) :: (fun _ : Fin 58 => true) :: List.ofFn (fun u : Fin 14 => fun i => rows i u)
      ∃ fs : List (Fin 58 → Bool), fs.length ≤ C.size ∧ t ∈ src ++ fs ∧
      ∀ j : Fin fs.length,
        let prev := src ++ fs.take j.val
        let v := fs.get j
        (∃ a ∈ prev, ∃ b ∈ prev, v = (fun i => a i && b i) ∨ v = (fun i => a i || b i)) ∧
        ∀ a ∈ prev, ∃ i, v i = t i ∧ a i ≠ t i)
    (exclude : let rows := fun (i : Fin 58) (u : Fin 14) => (27100321562855002520517520580012742248824378795708664412127748656491125098734460563633593280333336662142036550621417671358586257697027368867971489186403052057072961283871061193322549110396220698310063367192158989181571413407477755618014925963393 : Nat).testBit (14*i.val+u.val)
      let t := fun i : Fin 58 => decide (i.val < 21)
      let src : List (Fin 58 → Bool) := (fun _ : Fin 58 => false) :: (fun _ : Fin 58 => true) :: List.ofFn (fun u : Fin 14 => fun i => rows i u)
      ∀ fs : List (Fin 58 → Bool), t ∈ src ++ fs →
      (∀ j : Fin fs.length,
        let prev := src ++ fs.take j.val
        let v := fs.get j
        (∃ a ∈ prev, ∃ b ∈ prev, v = (fun i => a i && b i) ∨ v = (fun i => a i || b i)) ∧
        ∀ a ∈ prev, ∃ i, v i = t i ∧ a i ≠ t i) → 27 ≤ fs.length) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 27 ≤ C.size := by
  intro C hf he
  let rows := fun (i : Fin 58) (u : Fin 14) => (27100321562855002520517520580012742248824378795708664412127748656491125098734460563633593280333336662142036550621417671358586257697027368867971489186403052057072961283871061193322549110396220698310063367192158989181571413407477755618014925963393 : Nat).testBit (14*i.val+u.val)
  let t := fun i : Fin 58 => decide (i.val < 21)
  have check : ∀ i : Fin 58, (t i = true ↔ ∃ u v : Fin 14,
    (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (Nat × Nat)) ∧ rows i u = true ∧ rows i v = true) := by
    dsimp [t, rows]
    decide +kernel
  have ht : ∀ i, C.eval (List.ofFn (rows i)) = t i := fun i =>
    Bool.eq_iff_iff.mpr ((he (rows i)).trans (check i).symm)
  obtain ⟨fs, size, available, witness⟩ := normalize rows t C hf ht
  exact le_trans (exclude fs available witness) size
