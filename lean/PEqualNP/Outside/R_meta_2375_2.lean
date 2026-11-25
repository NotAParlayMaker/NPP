import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2375_2
    (hMono :
      let F := fun x : Fin 10 → Bool =>
        (List.finRange 5).any fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
      ∀ C : Circuit, Monotone2 C → C.size ≤ 19 → circuitFun 10 C ≠ F)
    (hOneNot :
      let F := fun x : Fin 10 → Bool =>
        (List.finRange 5).any fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
      ∀ (C : Circuit) (u v : Fin 28), FanInTwo C → C.size ≤ 18 →
        C.gates.countP (fun g => g.op.eval [false]) = 1 →
        let w := fun (x : Fin 10 → Bool) (k : ℕ) => (C.wires (List.ofFn x)).getD k false
        (∃ x, w x u.val = true ∧ w x v.val = false) →
        (∃ x, w x u.val = false ∧ w x v.val = true) →
        ¬ (∀ x, (w x u.val && w x v.val) = F x))
    (hTwoNot :
      let F := fun x : Fin 10 → Bool =>
        (List.finRange 5).any fun i =>
          (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
          (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
          (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
      ∀ (C : Circuit) (u v : Fin 28), FanInTwo C → C.size ≤ 18 →
        2 ≤ C.gates.countP (fun g => g.op.eval [false]) →
        let w := fun (x : Fin 10 → Bool) (k : ℕ) => (C.wires (List.ofFn x)).getD k false
        (∃ x, w x u.val = true ∧ w x v.val = false) →
        (∃ x, w x u.val = false ∧ w x v.val = true) →
        ¬ (∀ x, (w x u.val && w x v.val) = F x)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  intro g D u v hg hD hSz
  let Fraw := fun x : Fin 10 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let F := fun x : Fin 10 → Bool =>
    (List.finRange 5).any fun i =>
      (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
      (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
      (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))
  let C : Circuit := ⟨g :: D.gates, 0⟩
  let w := fun (x : Fin 10 → Bool) (k : ℕ) => (C.wires (List.ofFn x)).getD k false
  change (∃ x, w x u = true ∧ w x v = false) → (∃ x, w x u = false ∧ w x v = true) →
    (∀ x, Fraw x = true → w x u = true ∧ w x v = true) →
    ∃ x, Fraw x = false ∧ w x u = true ∧ w x v = true
  intro hu hv hpos
  by_contra hno
  have hSame (x : Fin 10 → Bool) : F x = Fraw x := by
    change (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) ||
      (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) ||
      (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) ||
      (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) ||
      (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false))))) = Fraw x
    simp only [Bool.or_false]
    dsimp only [Fraw]
    ac_rfl
  have hFanC : FanInTwo C := by
    intro gate hmem
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact hg _ List.mem_cons_self
    · exact hD _ htail
  have hSzC : C.size ≤ 18 := by
    change (g :: D.gates).length ≤ 18
    change D.gates.length ≤ 17 at hSz
    simp only [List.length_cons]
    omega
  have hAndEq (x : Fin 10 → Bool) : (w x u && w x v) = F x := by
    rw [hSame x]
    cases hf : Fraw x with
    | true =>
      obtain ⟨h1, h2⟩ := hpos x hf
      rw [h1, h2]; rfl
    | false =>
      cases hwu : w x u with
      | false => rfl
      | true =>
        cases hwv : w x v with
        | false => rfl
        | true => exact (hno ⟨x, hf, hwu, hwv⟩).elim
  let stepW : List Bool → Gate → List Bool :=
    fun ws gate => ws ++ [gate.op.eval (gate.inputs.map fun i => ws.getD i false)]
  have wiresLen (gs : List Gate) (ws : List Bool) :
      (gs.foldl stepW ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp
    | cons a as ih =>
      rw [List.foldl_cons, ih]
      simp only [stepW, List.length_append, List.length_cons, List.length_nil]
      omega
  have hCLen (x : Fin 10 → Bool) : (C.wires (List.ofFn x)).length = 10 + C.gates.length := by
    change (C.gates.foldl stepW (List.ofFn x)).length = 10 + C.gates.length
    rw [wiresLen, List.length_ofFn]
  have huLt : u < 28 := by
    obtain ⟨x, hwu, _⟩ := hu
    by_contra hge
    have hdef : w x u = false := List.getD_eq_default _ _ (by rw [hCLen x]; change C.gates.length ≤ 18 at hSzC; omega)
    rw [hdef] at hwu
    exact Bool.false_ne_true hwu
  have hvLt : v < 28 := by
    obtain ⟨x, _, hwv⟩ := hv
    by_contra hge
    have hdef : w x v = false := List.getD_eq_default _ _ (by rw [hCLen x]; change C.gates.length ≤ 18 at hSzC; omega)
    rw [hdef] at hwv
    exact Bool.false_ne_true hwv
  let nc := C.gates.countP (fun gate => gate.op.eval [false])
  by_cases hnc0 : nc = 0
  · let total : Circuit := ⟨C.gates ++ [⟨GateOp.and, [u, v]⟩], 10 + C.gates.length⟩
    have hNoNot : ∀ gate ∈ C.gates, gate.op = GateOp.and ∨ gate.op = GateOp.or := by
      intro gate hmem
      have hfalse : gate.op.eval [false] = false := by
        by_contra hne
        have htrue : gate.op.eval [false] = true := by
          cases hv' : gate.op.eval [false] with
          | true => rfl
          | false => exact (hne hv').elim
        have hposNc : 0 < nc := List.countP_pos_iff.mpr ⟨gate, hmem, htrue⟩
        omega
      rcases (hFanC gate hmem).1 with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · rw [h3] at hfalse
        cases hfalse
    have hMonoTot : Monotone2 total := by
      intro gate hmem
      change gate ∈ C.gates ++ [⟨GateOp.and, [u, v]⟩] at hmem
      rcases List.mem_append.mp hmem with h1 | h2
      · exact ⟨hNoNot gate h1, (hFanC gate h1).2⟩
      · obtain rfl := List.mem_singleton.mp h2
        exact ⟨Or.inl rfl, by simp⟩
    have hSzTot : total.size ≤ 19 := by
      change (C.gates ++ [({ op := GateOp.and, inputs := [u, v] } : Gate)]).length ≤ 19
      change C.gates.length ≤ 18 at hSzC
      rw [List.length_append, List.length_singleton]
      omega
    have hFunTot : circuitFun 10 total = F := by
      funext x
      change ((C.gates ++ [({ op := GateOp.and, inputs := [u, v] } : Gate)]).foldl stepW (List.ofFn x)).getD (10 + C.gates.length) false = F x
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (C.wires (List.ofFn x) ++ [w x u && (w x v && true)]).getD (10 + C.gates.length) false = F x
      rw [List.getD_append_right _ _ _ _ (by rw [hCLen x]), hCLen x, Nat.sub_self]
      change (w x u && (w x v && true)) = F x
      rw [Bool.and_true]
      exact hAndEq x
    exact hMono total hMonoTot hSzTot hFunTot
  · by_cases hnc1 : nc = 1
    · exact hOneNot C ⟨u, huLt⟩ ⟨v, hvLt⟩ hFanC hSzC hnc1 hu hv hAndEq
    · exact hTwoNot C ⟨u, huLt⟩ ⟨v, hvLt⟩ hFanC hSzC (by omega) hu hv hAndEq
