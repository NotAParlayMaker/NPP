import PEqualNP.Defs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_972_317
    (and_bound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p w : Fin 13, (p.val + w.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true) → 13 ≤ C.gates.countP (fun g => match g.op with | .and => true | _ => false))
    (or_bound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p w : Fin 13, (p.val + w.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true) → 51 ≤ C.gates.countP (fun g => match g.op with | .or => true | _ => false)) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 64 ≤ C.size := by
  intro C mono computes
  let near := fun p w : Fin 13 => (p.val + w.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let edges : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
  have table : ∀ u v : Fin 26, (u.val, v.val) ∈ edges ↔
      ∃ p w : Fin 13, u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 w ∧ near p w := by
    decide +kernel
  have transformed : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p w : Fin 13, near p w ∧ x (Fin.castAdd 13 p) = true ∧
        x (Fin.natAdd 13 w) = true := by
    intro x
    rw [computes]
    constructor
    · rintro ⟨u, v, he, hu, hv⟩
      obtain ⟨p, w, rfl, rfl, hpw⟩ := (table u v).mp he
      exact ⟨p, w, hpw, hu, hv⟩
    · rintro ⟨p, w, hpw, hp, hw⟩
      exact ⟨Fin.castAdd 13 p, Fin.natAdd 13 w,
        (table _ _).mpr ⟨p, w, rfl, rfl, hpw⟩, hp, hw⟩
  have ha := and_bound C mono transformed
  have ho := or_bound C mono transformed
  have partition :
      C.gates.countP (fun g => match g.op with | .and => true | _ => false) +
      C.gates.countP (fun g => match g.op with | .or => true | _ => false) ≤
      C.gates.length := by
    induction C.gates with
    | nil => simp
    | cons g gs ih =>
      obtain ⟨op, inputs⟩ := g
      cases op <;> simp_all [List.countP_cons] <;> omega
  change 64 ≤ C.gates.length
  omega
