import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3931_719
    (lower :
      let F := fun (x : Fin 9 → Bool) =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ C : Circuit, FanInTwo C → circuitFun 9 C = F → 15 ≤ C.size)
    (minimalWires :
      ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
        (∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) →
        let W := fun (x : Fin n → Bool) i => (C.wires (List.ofFn x)).getD i false
        (∀ j < C.size, ∃ x y, W x (n + j) ≠ W y (n + j)) ∧
        (∀ i j, i < n + j → j < C.size → ∃ x, W x i ≠ W x (n + j)) ∧
        (C.gates ≠ [] → C.output + 1 = n + C.size))
    (suffix :
      let F := fun (x : Fin 9 → Bool) =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let P := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 1]
      let R := fun (a b : Fin 10) x => P x ++ [((P x).getD a.val false && (P x).getD b.val false)]
      let W := fun (D : Circuit) a b (x : Fin 9 → Bool) i => (D.wires (R a b x)).getD i false
      ∀ (D : Circuit) (a b : Fin 10), FanInTwo D → D.size = 13 → D.output = 23 →
        a < b → (b.val = 9 → 2 ≤ a.val) → (∀ x, D.eval (R a b x) = F x) →
        ∃ (v : Fin 9) (S : Finset ℕ),
          (∀ j ∈ S, j < 15 ∧
            ((∃ c : Bool, ∀ x, x v = false → W D a b x (9 + j) = c) ∨
              ∃ i < 9 + j, ∀ x, x v = false → W D a b x (9 + j) = W D a b x i)) ∧
          (if v ∈ ([4, 6, 7] : List (Fin 9)) then 2 else 3) < S.card) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin (9 : ℕ)) (x6 : Finset ℕ), (∀ x7 ∈ x6, x7 < x1.size ∧ ((∃ (x9 : Bool), ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = x9) ∨ ∃ x9 < (9 : ℕ) + x7, ∀ (x10 : Fin (9 : ℕ) → Bool), x10 x5 = Bool.false → (x1.wires (List.ofFn x10)).getD ((9 : ℕ) + x7) Bool.false = (x1.wires (List.ofFn x10)).getD x9 Bool.false)) → (x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))] → x6.card ≤ (3 : ℕ)) ∧ (x5 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))] → x6.card ≤ (2 : ℕ))) → (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (16 : ℕ) ≤ x1.size := by
  intro C hFan hFirst hFun hCollapse hAnd
  obtain ⟨g, hGate, hOp⟩ := hAnd
  by_contra! hSmall
  let F := fun (x : Fin 9 → Bool) =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have hTarget : circuitFun 9 C = F := hFun
  have hSize : C.size = 15 := by
    have h := lower C hFan hTarget
    omega
  have hMinimum : IsMinimalCircuit 9 C := ⟨hFan, fun D hD hEq => by
    rw [hSize]
    exact lower D hD (hEq.trans hTarget)⟩
  have hVary : ∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y := by
    rw [hTarget]
    exact ⟨fun _ => false, fun _ => true, by decide⟩
  obtain ⟨hNonconstant, hDistinct, hOutput⟩ := minimalWires 9 C hMinimum hVary

  let W := fun (x : Fin 9 → Bool) i => (C.wires (List.ofFn x)).getD i false
  have hSecondExists : 1 < C.size := by omega
  have noConstant (c : Bool) (he : ∀ x, W x 10 = c) : False := by
    obtain ⟨x, y, hxy⟩ := hNonconstant 1 hSecondExists
    change W x 10 ≠ W y 10 at hxy
    exact hxy ((he x).trans (he y).symm)
  have noAlias (i : ℕ) (hi : i < 10) (he : ∀ x, W x 10 = W x i) : False := by
    obtain ⟨x, hx⟩ := hDistinct i 1 hi hSecondExists
    change W x i ≠ W x 10 at hx
    exact hx (he x).symm

  obtain ⟨first, rest, hGates⟩ : ∃ first rest, C.gates = first :: g :: rest := by
    cases h : C.gates with
    | nil => simp [h] at hGate
    | cons first tail =>
      cases tail with
      | nil => simp [h] at hGate
      | cons second rest =>
        have he : second = g := by simpa [h] using hGate
        exact ⟨first, rest, by rw [he]⟩

  let P := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 1]
  let emit (w : List Bool) (gate : Gate) :=
    w ++ [gate.op.eval (gate.inputs.map fun i => w.getD i false)]
  have emitLength (w : List Bool) (gate : Gate) : (emit w gate).length = w.length + 1 := by
    simp [emit]
  have emitRead (w : List Bool) (gate : Gate) :
      (emit w gate).getD w.length false =
        gate.op.eval (gate.inputs.map fun i => w.getD i false) := by
    unfold emit
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simp
  have preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl emit w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons head tail ih =>
      rw [List.foldl_cons, ih (emit w head) (by rw [emitLength]; omega)]
      exact List.getD_append _ _ _ _ hi
  have firstPrefix (x : Fin 9 → Bool) : emit (List.ofFn x) first = P x := by
    have hv : W x 9 = (emit (List.ofFn x) first).getD 9 false := by
      change (C.gates.foldl emit (List.ofFn x)).getD 9 false = _
      rw [hGates, List.foldl_cons]
      apply preserves
      simp [emitLength]
    have hi : (List.ofFn x).length = 9 := by simp
    have firstValue : W x 9 = (x 0 || x 1) := hFirst x
    have he := emitRead (List.ofFn x) first
    rw [hi, ← hv, firstValue] at he
    exact congrArg (fun b => List.ofFn x ++ [b]) he.symm
  have foldPrefix (x : Fin 9 → Bool) :
      C.wires (List.ofFn x) = (g :: rest).foldl emit (P x) := by
    change C.gates.foldl emit (List.ofFn x) = _
    rw [hGates, List.foldl_cons, firstPrefix]
  have prefixLength (x : Fin 9 → Bool) : (P x).length = 10 := by simp [P]
  have early (x : Fin 9 → Bool) (i : ℕ) (hi : i < 10) : W x i = (P x).getD i false := by
    change (C.wires (List.ofFn x)).getD i false = _
    rw [foldPrefix]
    exact preserves _ _ _ (by rwa [prefixLength])
  have secondValue (x : Fin 9 → Bool) :
      W x 10 = g.op.eval (g.inputs.map fun i => (P x).getD i false) := by
    change (C.wires (List.ofFn x)).getD 10 false = _
    rw [foldPrefix, List.foldl_cons,
      preserves rest (emit (P x) g) 10 (by rw [emitLength, prefixLength]; decide)]
    simpa only [prefixLength] using emitRead (P x) g
  have outside (x : Fin 9 → Bool) (i : ℕ) (hi : 10 ≤ i) : (P x).getD i false = false :=
    List.getD_eq_default _ _ (by rwa [prefixLength])

  -- Order the two operands and rule out absorption by the first gate.
  have ordered (u v : ℕ) (hu : u < 10) (hv : v < 10) (hlt : u < v)
      (he : ∀ x, W x 10 = ((P x).getD u false && (P x).getD v false)) :
      ∃ (a b : Fin 10), a < b ∧ (b.val = 9 → 2 ≤ a.val) ∧
        ∀ x, W x 10 = ((P x).getD a.val false && (P x).getD b.val false) := by
    refine ⟨⟨u, hu⟩, ⟨v, hv⟩, hlt, ?_, he⟩
    intro hv9
    change v = 9 at hv9
    change 2 ≤ u
    by_contra! hu2
    have hu01 : u = 0 ∨ u = 1 := by omega
    apply noAlias u hu
    intro x
    rw [he, early x u hu, hv9]
    rcases hu01 with rfl | rfl
    · change (x 0 && (x 0 || x 1)) = x 0
      cases x 0 <;> cases x 1 <;> rfl
    · change (x 1 && (x 0 || x 1)) = x 1
      cases x 0 <;> cases x 1 <;> rfl

  have gMem : g ∈ C.gates := List.mem_iff_getElem?.mpr ⟨1, hGate⟩
  have gBound := (hFan g gMem).2
  have andEval (bits : List Bool) : GateOp.and.eval bits = bits.all id := rfl
  obtain ⟨a, b, hab, hAbsorb, hProduct⟩ :
      ∃ (a b : Fin 10), a < b ∧ (b.val = 9 → 2 ≤ a.val) ∧
        ∀ x, W x 10 = ((P x).getD a.val false && (P x).getD b.val false) := by
    cases hInputs : g.inputs with
    | nil =>
        exact (noConstant true (fun x => by
          simp [secondValue, hInputs, hOp, andEval])).elim
    | cons u tail =>
      cases tail with
      | nil =>
          have huVal (x : Fin 9 → Bool) : W x 10 = (P x).getD u false := by
            simp [secondValue, hInputs, hOp, andEval]
          by_cases hu : u < 10
          · exact (noAlias u hu (fun x => (huVal x).trans (early x u hu).symm)).elim
          · exact (noConstant false (fun x => (huVal x).trans (outside x u (by omega)))).elim
      | cons v tail =>
        cases tail with
        | nil =>
            have he (x : Fin 9 → Bool) :
                W x 10 = ((P x).getD u false && (P x).getD v false) := by
              simp [secondValue, hInputs, hOp, andEval]
            by_cases hu : u < 10
            · by_cases hv : v < 10
              · rcases lt_trichotomy u v with huv | huv | hvu
                · exact ordered u v hu hv huv he
                · subst v
                  exact (noAlias u hu (fun x => by rw [he, Bool.and_self, early x u hu])).elim
                · exact ordered v u hv hu hvu (fun x => (he x).trans (Bool.and_comm _ _))
              · exact (noConstant false (fun x => by rw [he, outside x v (by omega), Bool.and_false])).elim
            · exact (noConstant false (fun x => by rw [he, outside x u (by omega), Bool.false_and])).elim
        | cons w tail =>
            simp [hInputs] at gBound

  let D : Circuit := ⟨rest, C.output⟩
  have hDSize : D.size = 13 := by
    change rest.length = 13
    change C.gates.length = 15 at hSize
    rw [hGates] at hSize
    simp only [List.length_cons] at hSize
    omega
  have hDOutput : D.output = 23 := by
    have hout := hOutput (by rw [hGates]; simp)
    change C.output = 23
    omega
  have hDFan : FanInTwo D := by
    intro gate hgate
    apply hFan gate
    change gate ∈ rest at hgate
    rw [hGates]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hgate)

  have suffixWires (x : Fin 9 → Bool) :
      D.wires (P x ++ [((P x).getD a.val false && (P x).getD b.val false)]) =
        C.wires (List.ofFn x) := by
    have hEmit : emit (P x) g = P x ++ [((P x).getD a.val false && (P x).getD b.val false)] := by
      unfold emit
      rw [← secondValue x, hProduct x]
    change rest.foldl emit _ = _
    rw [foldPrefix, List.foldl_cons, hEmit]
  have suffixTarget (x : Fin 9 → Bool) :
      D.eval (P x ++ [((P x).getD a.val false && (P x).getD b.val false)]) = F x := by
    change (D.wires _).getD C.output false = F x
    rw [suffixWires]
    exact congrFun hTarget x
  obtain ⟨v, S, hSet, hMany⟩ := suffix D a b hDFan hDSize hDOutput hab hAbsorb suffixTarget
  have hOriginal : ∀ j ∈ S, j < C.size ∧
      ((∃ c : Bool, ∀ x, x v = false → W x (9 + j) = c) ∨
        ∃ i < 9 + j, ∀ x, x v = false → W x (9 + j) = W x i) := by
    intro j hj
    refine ⟨by rw [hSize]; exact (hSet j hj).1, ?_⟩
    rcases (hSet j hj).2 with ⟨c, hc⟩ | ⟨i, hi, he⟩
    · refine Or.inl ⟨c, fun x hx => ?_⟩
      change (C.wires (List.ofFn x)).getD (9 + j) false = c
      rw [← suffixWires x]
      exact hc x hx
    · refine Or.inr ⟨i, hi, fun x hx => ?_⟩
      change (C.wires (List.ofFn x)).getD (9 + j) false =
        (C.wires (List.ofFn x)).getD i false
      rw [← suffixWires x]
      exact he x hx
  have hLimit := hCollapse v S hOriginal
  have cover : ∀ z : Fin 9, z ∈ ([4, 6, 7] : List (Fin 9)) ∨
      z ∈ ([0, 1, 2, 3, 5, 8] : List (Fin 9)) := by decide
  by_cases hv : v ∈ ([4, 6, 7] : List (Fin 9))
  · have hb := hLimit.2 hv
    simp only [hv, ↓reduceIte] at hMany
    omega
  · have hb := hLimit.1 ((cover v).resolve_left hv)
    simp only [hv, ↓reduceIte] at hMany
    omega
