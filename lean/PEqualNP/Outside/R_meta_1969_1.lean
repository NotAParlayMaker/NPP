import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Structural cone-dichotomy + Fano point-line duality reduction of L-meta-1969.
-- Proves cleaner-above and pair-born-below lemmas, collapses the two mixed cases via the
-- anti-automorphism (p, l) |-> (-l, -p) fixing (0, 7) and swapping 0 <-> 7, and splits
-- into 3 canonical 4-AND configurations (both-dirty, mixed, both-clean).
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_1969_1
    (hBothDirty :
      ∀ (C : Circuit), C.size ≤ 27 → IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
        circuitFun 14 C = (fun x : Fin 14 → Bool => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
        let V := wireVal 14 C; let P := @pairInput 14
        let L := fun g : ℕ => (gateAt C g).op = GateOp.and ∧ (14 + g = C.output ∨ InCone 14 C g (C.output - 14))
        let W := fun (g : ℕ) (p : Fin 14) => L g ∧ V (14 + g) (P 0 7) = true ∧ ∀ b : Fin 2, V (opnd C g b) (P p p) = false
        ¬ ∃ k1 k2 k3 k4 : ℕ, k1 ≠ k2 ∧ ¬ InCone 14 C k1 k2 ∧ ¬ InCone 14 C k2 k1 ∧
          W k1 0 ∧ W k2 7 ∧ V (14 + k1) (P 7 7) = true ∧ V (14 + k2) (P 0 0) = true ∧
          L k3 ∧ InCone 14 C k1 k3 ∧ V (14 + k3) (P 7 7) = false ∧
          L k4 ∧ InCone 14 C k2 k4 ∧ V (14 + k4) (P 0 0) = false)
    (hMixed :
      ∀ (C : Circuit), C.size ≤ 27 → IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
        circuitFun 14 C = (fun x : Fin 14 → Bool => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
        let V := wireVal 14 C; let P := @pairInput 14; let I := InCone 14 C
        let L := fun g : ℕ => (gateAt C g).op = GateOp.and ∧ (14 + g = C.output ∨ I g (C.output - 14))
        let W := fun (g : ℕ) (p : Fin 14) => L g ∧ V (14 + g) (P 0 7) = true ∧ ∀ b : Fin 2, V (opnd C g b) (P p p) = false
        ¬ ∃ k1 k2 k3 m0 : ℕ, k1 ≠ k2 ∧ ¬ I k1 k2 ∧ ¬ I k2 k1 ∧
          W k1 0 ∧ W k2 7 ∧ V (14 + k1) (P 7 7) = true ∧ V (14 + k2) (P 0 0) = false ∧
          L k3 ∧ I k1 k3 ∧ V (14 + k3) (P 7 7) = false ∧
          (gateAt C m0).op = GateOp.and ∧ I m0 k2 ∧ V (14 + m0) (P 0 7) = true ∧
          V (14 + m0) (P 0 0) = false ∧ V (14 + m0) (P 7 7) = false)
    (hBothClean :
      ∀ (C : Circuit), C.size ≤ 27 → IsAO2 14 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
        circuitFun 14 C = (fun x : Fin 14 → Bool => decide (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
        let V := wireVal 14 C; let P := @pairInput 14; let I := InCone 14 C
        let W := fun (g : ℕ) (p : Fin 14) =>
          (gateAt C g).op = GateOp.and ∧ (14 + g = C.output ∨ I g (C.output - 14)) ∧
          V (14 + g) (P 0 7) = true ∧ ∀ b : Fin 2, V (opnd C g b) (P p p) = false
        let B := fun m k : ℕ => (gateAt C m).op = GateOp.and ∧ I m k ∧ V (14 + m) (P 0 7) = true ∧ V (14 + m) (P 0 0) = false ∧ V (14 + m) (P 7 7) = false
        ¬ ∃ k1 k2 k0 m0 : ℕ, k1 ≠ k2 ∧ ¬ I k1 k2 ∧ ¬ I k2 k1 ∧
          W k1 0 ∧ W k2 7 ∧ V (14 + k1) (P 7 7) = false ∧ V (14 + k2) (P 0 0) = false ∧
          B k0 k1 ∧ B m0 k2) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), x2 ≠ x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∧ ¬PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  let sig : Fin 14 → Fin 14 := fun i =>
    if i.val < 7 then Fin.ofNat 14 (7 + (7 - i.val) % 7) else Fin.ofNat 14 ((14 - i.val) % 7)
  have hRows : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p = l ∨ p = l + 1 ∨ p = l + 3 := by decide +kernel
  have hSigInv : ∀ i : Fin 14, sig (sig i) = i := by dsimp only [sig]; decide +kernel
  have hSigInj : Function.Injective sig := fun a b hab => by
    have := congrArg sig hab; rwa [hSigInv a, hSigInv b] at this
  have hSigDual : ∀ p l : Fin 7, p ∈ fanoLines l ↔
      ∃ p2 l2 : Fin 7, p2 ∈ fanoLines l2 ∧
        sig (Fin.castAdd 7 p) = Fin.natAdd 7 l2 ∧ sig (Fin.natAdd 7 l) = Fin.castAdd 7 p2 := by
    dsimp only [sig]; decide +kernel
  have hSigP0 : ∀ i : Fin 14, pairInput (0 : Fin 14) 0 (sig i) = pairInput (7 : Fin 14) 7 i := by
    dsimp only [sig]; decide +kernel
  have hSigP7 : ∀ i : Fin 14, pairInput (7 : Fin 14) 7 (sig i) = pairInput (0 : Fin 14) 0 i := by
    dsimp only [sig]; decide +kernel
  have hSigP07 : ∀ i : Fin 14, pairInput (0 : Fin 14) 7 (sig i) = pairInput (0 : Fin 14) 7 i := by
    dsimp only [sig]; decide +kernel
  have hF_p0 : decide (∃ p l : Fin 7, p ∈ fanoLines l ∧
      pairInput (0 : Fin 14) 0 (Fin.castAdd 7 p) = true ∧
      pairInput (0 : Fin 14) 0 (Fin.natAdd 7 l) = true) = false := by decide +kernel
  have hF_p7 : decide (∃ p l : Fin 7, p ∈ fanoLines l ∧
      pairInput (7 : Fin 14) 7 (Fin.castAdd 7 p) = true ∧
      pairInput (7 : Fin 14) 7 (Fin.natAdd 7 l) = true) = false := by decide +kernel
  have hF_p07 : decide (∃ p l : Fin 7, p ∈ fanoLines l ∧
      pairInput (0 : Fin 14) 7 (Fin.castAdd 7 p) = true ∧
      pairInput (0 : Fin 14) 7 (Fin.natAdd 7 l) = true) = true := by decide +kernel
  have hP0_0 : pairInput (0 : Fin 14) 0 0 = true := by decide +kernel
  have hP7_7 : pairInput (7 : Fin 14) 7 7 = true := by decide +kernel
  classical
  rintro ⟨C, hSz, hShape, hOk, k1, k2, hNe, hN12, hN21, hA1, hL1, hV1, hOp1, hA2, hL2, hV2, hOp2⟩
  let F : (Fin 14 → Bool) → Bool := fun x =>
    decide (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
  let P := @pairInput 14
  have hData : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ i j : ℕ, g.inputs = [i, j] ∧ i ≠ j := by
    intro g hg
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hg
    obtain ⟨op, i, j, eq, ne, _, _⟩ := hShape k g hk
    exact ⟨op, i, j, eq, ne⟩
  have hAO2 : IsAO2 14 C := by
    refine ⟨fun g hg => (hData g hg).1, ?_, ?_⟩
    · intro k hk i hi
      have hget : C.gates[k]? = some (gateAt C k) := by
        change C.gates[k]? = some (C.gates.getD k ⟨GateOp.or, []⟩)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
      obtain ⟨_, u, v, heq, _, hu, hv⟩ := hShape k (gateAt C k) hget
      rw [heq] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨_, i, j, heq, _⟩ := hData g hg
      rw [heq]; rfl
  have hNodup : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨_, i, j, heq, hne⟩ := hData g hg
    rw [heq]; simp [hne]
  have hFun : circuitFun 14 C = F := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x) = true ↔
      decide (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) = true
    rw [decide_eq_true_eq]
    constructor
    · intro h
      obtain ⟨p, l, hpl, hp, hl⟩ := (hOk x).mp h
      exact ⟨p, l, (hRows p l).mpr hpl, hp, hl⟩
    · rintro ⟨p, l, hpl, hp, hl⟩
      exact (hOk x).mpr ⟨p, l, (hRows p l).mp hpl, hp, hl⟩
  let wstep : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let Wf : List Gate → List Bool → List Bool := fun gs x => gs.foldl wstep x
  have hWf_len : ∀ (gs : List Gate) (w : List Bool), (Wf gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; change w.length = w.length + 0; omega
    | cons g gs ih =>
      intro w
      change (Wf gs (wstep w g)).length = w.length + (g :: gs).length
      rw [ih (wstep w g)]
      have hl : (wstep w g).length = w.length + 1 := by
        dsimp only [wstep]; rw [List.length_append]; simp
      rw [hl, List.length_cons]; omega
  have hWf_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (Wf gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      change (Wf gs (wstep w g)).getD i false = w.getD i false
      have hl : i < (wstep w g).length := by
        dsimp only [wstep]; rw [List.length_append]; simp; omega
      rw [ih (wstep w g) i hl]
      dsimp only [wstep]
      exact List.getD_append w _ false i hi
  have hWf_append : ∀ (gs1 gs2 : List Gate) (w : List Bool),
      Wf (gs1 ++ gs2) w = Wf gs2 (Wf gs1 w) := by
    intro gs1 gs2 w; dsimp only [Wf]; exact List.foldl_append
  have hConesLen : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 14) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      have hl : (coneStep 14 cs g).length = cs.length + 1 := by
        change (cs ++ [_]).length = cs.length + 1
        rw [List.length_append]; simp
      rw [hl, List.length_cons]; omega
  have hConesChar : ∀ (gs : List Gate) (i j : ℕ),
      i ∈ (gs.foldl (coneStep 14) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
          14 ≤ w ∧ w < 14 + j ∧ (i = w - 14 ∨ i ∈ (gs.foldl (coneStep 14) []).getD (w - 14) []) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      let prev := gs.foldl (coneStep 14) []
      have hprev_len : prev.length = gs.length := by dsimp only [prev]; rw [hConesLen]; simp
      have hkeep : ∀ k, k < gs.length → (coneStep 14 prev g).getD k [] = prev.getD k [] := by
        intro k hk
        change (prev ++ [_]).getD k [] = prev.getD k []
        exact List.getD_append prev _ [] k (by omega)
      rcases Nat.lt_trichotomy j gs.length with hlt | heq | hgt
      · have hg_eq : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
          List.getD_append gs [g] ⟨GateOp.or, []⟩ j hlt
        rw [hkeep j hlt, ih i j, hg_eq]
        constructor
        · rintro ⟨_, w, hw, hnw, hwlt, hmem⟩
          refine ⟨by rw [List.length_append]; simp; omega, w, hw, hnw, hwlt, ?_⟩
          rcases hmem with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by rw [hkeep (w - 14) (by omega)]; exact h2)
        · rintro ⟨_, w, hw, hnw, hwlt, hmem⟩
          refine ⟨hlt, w, hw, hnw, hwlt, ?_⟩
          rcases hmem with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by rw [hkeep (w - 14) (by omega)] at h2; exact h2)
      · subst heq
        have hg_eq : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by simp
        have hstep_at : (coneStep 14 prev g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + prev.length))).flatMap
              (fun w => (w - 14) :: prev.getD (w - 14) []) := by
          change (prev ++ [_]).getD gs.length [] = _
          rw [← hprev_len]; simp
        rw [hstep_at, hg_eq, hprev_len]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, hnw, hwlt⟩, hmem⟩
          refine ⟨by rw [List.length_append]; simp, w, hw, hnw, hwlt, ?_⟩
          rcases hmem with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by rw [hkeep (w - 14) (by omega)]; exact h2)
        · rintro ⟨_, w, hw, hnw, hwlt, hmem⟩
          refine ⟨w, ⟨hw, hnw, hwlt⟩, ?_⟩
          rcases hmem with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by rw [hkeep (w - 14) (by omega)] at h2; exact h2)
      · have hlen_step : (coneStep 14 prev g).length = gs.length + 1 := by
          change (prev ++ [_]).length = gs.length + 1
          rw [List.length_append, hprev_len]; simp
        have hnone : (coneStep 14 prev g).getD j [] = [] := List.getD_eq_default _ _ (by omega)
        rw [hnone]
        constructor
        · intro h; simp at h
        · rintro ⟨hjlt, _⟩; rw [List.length_append] at hjlt; simp at hjlt; omega
  have hInCone_iff : ∀ i j, InCone 14 C i j ↔
      j < C.gates.length ∧ ∃ w ∈ (gateAt C j).inputs,
        14 ≤ w ∧ w < 14 + j ∧ (i = w - 14 ∨ InCone 14 C i (w - 14)) := fun i j =>
    hConesChar C.gates i j
  have hInCone_trans : ∀ a b c, InCone 14 C a b → InCone 14 C b c → InCone 14 C a c := by
    intro a b c hab hbc
    induction c using Nat.strong_induction_on with
    | ind c ih =>
      obtain ⟨hclt, w, hw, hnw, hwlt, hmem⟩ := (hInCone_iff b c).mp hbc
      refine (hInCone_iff a c).mpr ⟨hclt, w, hw, hnw, hwlt, Or.inr ?_⟩
      rcases hmem with rfl | hrec
      · exact hab
      · exact ih (w - 14) (by omega) hrec
  have hGateAt_eq : ∀ j (hj : j < C.gates.length), gateAt C j = C.gates[j]'hj := by
    intro j hj
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]'hj
    exact List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ hj
  have hInputs_pair : ∀ j, j < C.gates.length → (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    intro j hj
    have hmem : gateAt C j ∈ C.gates := by rw [hGateAt_eq j hj]; exact List.getElem_mem hj
    obtain ⟨_, a, b, heq, _⟩ := hData (gateAt C j) hmem
    change (gateAt C j).inputs = [(gateAt C j).inputs.getD 0 0, (gateAt C j).inputs.getD 1 0]
    rw [heq]; rfl
  have hOpnd_lt : ∀ j, j < C.gates.length → ∀ b : Fin 2, opnd C j b < 14 + j := by
    intro j hj b
    have hmem : opnd C j b ∈ (gateAt C j).inputs := by rw [hInputs_pair j hj]; fin_cases b <;> simp
    exact hAO2.2.1 j hj (opnd C j b) hmem
  have hWireVal_in : ∀ (i : Fin 14) (x : Fin 14 → Bool), wireVal 14 C i.val x = x i := by
    intro i x
    change (Wf C.gates (List.ofFn x)).getD i.val false = x i
    rw [hWf_prefix C.gates (List.ofFn x) i.val (by rw [List.length_ofFn]; exact i.isLt)]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt)]
    exact List.getElem_ofFn (by rw [List.length_ofFn]; exact i.isLt)
  have hWireVal_ge : ∀ w, 14 + C.gates.length ≤ w → ∀ x : Fin 14 → Bool, wireVal 14 C w x = false := by
    intro w hw x
    change (Wf C.gates (List.ofFn x)).getD w false = false
    rw [List.getD_eq_default]; rw [hWf_len, List.length_ofFn]; exact hw
  have hGateVal_eq : ∀ j, j < C.gates.length → ∀ x : Fin 14 → Bool,
      gateVal 14 C j x =
        if (gateAt C j).op = GateOp.and then (wireVal 14 C (opnd C j 0) x && wireVal 14 C (opnd C j 1) x)
        else (wireVal 14 C (opnd C j 0) x || wireVal 14 C (opnd C j 1) x) := by
    intro j hj x
    let pre := C.gates.take j
    let post := C.gates.drop (j + 1)
    let gj := C.gates[j]'hj
    have hpre_len : pre.length = j := by
      dsimp only [pre]; rw [List.length_take]; exact min_eq_left (Nat.le_of_lt hj)
    have hsplit : C.gates = pre ++ gj :: post := by
      dsimp only [pre, post, gj]
      have h1 := (List.take_append_drop j C.gates).symm
      rw [List.drop_eq_getElem_cons hj] at h1; exact h1
    have hgj : gj = gateAt C j := (hGateAt_eq j hj).symm
    let wpre := Wf pre (List.ofFn x)
    have hwpre_len : wpre.length = 14 + j := by
      dsimp only [wpre]; rw [hWf_len, List.length_ofFn, hpre_len]
    have hC_eq : Wf C.gates (List.ofFn x) = Wf post (wstep wpre gj) := by
      rw [hsplit, hWf_append]; rfl
    have hget_lt : ∀ u, u < 14 + j → wpre.getD u false = wireVal 14 C u x := by
      intro u hu
      change wpre.getD u false = (Wf C.gates (List.ofFn x)).getD u false
      rw [hC_eq]
      have h1 : u < (wstep wpre gj).length := by
        dsimp only [wstep]; rw [List.length_append]; simp; omega
      rw [hWf_prefix post (wstep wpre gj) u h1]
      dsimp only [wstep]
      exact (List.getD_append wpre _ false u (by omega)).symm
    have hval_at : gateVal 14 C j x = gj.op.eval (gj.inputs.map fun i => wpre.getD i false) := by
      change (Wf C.gates (List.ofFn x)).getD (14 + j) false = _
      rw [hC_eq]
      have h1 : 14 + j < (wstep wpre gj).length := by
        dsimp only [wstep]; rw [List.length_append]; simp; omega
      rw [hWf_prefix post (wstep wpre gj) (14 + j) h1]
      dsimp only [wstep]; rw [← hwpre_len]; simp
    rw [hval_at, hgj, hInputs_pair j hj]
    have h0 := hget_lt (opnd C j 0) (hOpnd_lt j hj 0)
    have h1 := hget_lt (opnd C j 1) (hOpnd_lt j hj 1)
    rw [List.map_cons, List.map_cons, List.map_nil, h0, h1]
    have hmem : gateAt C j ∈ C.gates := by rw [hGateAt_eq j hj]; exact List.getElem_mem hj
    rcases (hData (gateAt C j) hmem).1 with hAnd | hOr
    · rw [if_pos hAnd, hAnd]
      change List.all [wireVal 14 C (opnd C j 0) x, wireVal 14 C (opnd C j 1) x] id =
        (wireVal 14 C (opnd C j 0) x && wireVal 14 C (opnd C j 1) x)
      cases wireVal 14 C (opnd C j 0) x <;> cases wireVal 14 C (opnd C j 1) x <;> rfl
    · have hne : (gateAt C j).op ≠ GateOp.and := by rw [hOr]; intro h; cases h
      rw [if_neg hne, hOr]
      change List.any [wireVal 14 C (opnd C j 0) x, wireVal 14 C (opnd C j 1) x] id =
        (wireVal 14 C (opnd C j 0) x || wireVal 14 C (opnd C j 1) x)
      cases wireVal 14 C (opnd C j 0) x <;> cases wireVal 14 C (opnd C j 1) x <;> rfl
  have hOutBounds : 14 ≤ C.output ∧ C.output < 14 + C.gates.length := by
    have h1 : wireVal 14 C C.output (P 0 7) = true := by
      have := congrFun hFun (P 0 7)
      change wireVal 14 C C.output (P 0 7) = F (P 0 7) at this
      rw [this]; exact hF_p07
    have hlt : C.output < 14 + C.gates.length := by
      by_contra hge
      rw [hWireVal_ge C.output (by omega) (P 0 7)] at h1; cases h1
    have hge14 : 14 ≤ C.output := by
      by_contra hlt14
      let idx : Fin 14 := ⟨C.output, by omega⟩
      have h0 : wireVal 14 C C.output (P 0 0) = false := by
        have := congrFun hFun (P 0 0); change wireVal 14 C C.output (P 0 0) = F (P 0 0) at this
        rw [this]; exact hF_p0
      have h7 : wireVal 14 C C.output (P 7 7) = false := by
        have := congrFun hFun (P 7 7); change wireVal 14 C C.output (P 7 7) = F (P 7 7) at this
        rw [this]; exact hF_p7
      rw [hWireVal_in idx (P 0 7)] at h1
      rw [hWireVal_in idx (P 0 0)] at h0
      rw [hWireVal_in idx (P 7 7)] at h7
      have h1' : idx = 0 ∨ idx = 7 := of_decide_eq_true h1
      rcases h1' with h | h
      · rw [h] at h0; change pairInput (0 : Fin 14) 0 0 = false at h0; rw [hP0_0] at h0; cases h0
      · rw [h] at h7; change pairInput (7 : Fin 14) 7 7 = false at h7; rw [hP7_7] at h7; cases h7
    exact ⟨hge14, hlt⟩
  have hCleaner : ∀ (g : ℕ) (x : Fin 14 → Bool),
      g < C.gates.length → (14 + g = C.output ∨ InCone 14 C g (C.output - 14)) →
      gateVal 14 C g x = true → wireVal 14 C C.output x = false →
      ∃ c : ℕ, (gateAt C c).op = GateOp.and ∧
        (14 + c = C.output ∨ InCone 14 C c (C.output - 14)) ∧
        InCone 14 C g c ∧ gateVal 14 C c x = false := by
    intro g x hglt hlive hgx houtf
    have hSub : ∀ j, j < C.gates.length →
        (14 + j = C.output ∨ InCone 14 C j (C.output - 14)) →
        InCone 14 C g j → gateVal 14 C j x = false →
        ∃ c : ℕ, (gateAt C c).op = GateOp.and ∧
          (14 + c = C.output ∨ InCone 14 C c (C.output - 14)) ∧
          InCone 14 C g c ∧ gateVal 14 C c x = false := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hjlt hjlive hgj hjf
        by_cases hAnd : (gateAt C j).op = GateOp.and
        · exact ⟨j, hAnd, hjlive, hgj, hjf⟩
        · obtain ⟨_, w, hw, hnw, hwlt, hmem⟩ := (hInCone_iff g j).mp hgj
          let k := w - 14
          have hkw : w = 14 + k := by omega
          have hklt : k < j := by omega
          have hkInJ : InCone 14 C k j := (hInCone_iff k j).mpr ⟨hjlt, w, hw, hnw, hwlt, Or.inl rfl⟩
          have hklive : 14 + k = C.output ∨ InCone 14 C k (C.output - 14) := by
            rcases hjlive with heq | hic
            · exact Or.inr (by rw [← heq, Nat.add_sub_cancel_left]; exact hkInJ)
            · exact Or.inr (hInCone_trans k j (C.output - 14) hkInJ hic)
          have hkf : gateVal 14 C k x = false := by
            rw [hGateVal_eq j hjlt x, if_neg hAnd, Bool.or_eq_false_iff] at hjf
            rw [hInputs_pair j hjlt] at hw
            rcases List.mem_cons.mp hw with h0 | hw'
            · change wireVal 14 C (14 + k) x = false; rw [← hkw, h0]; exact hjf.1
            · rcases List.mem_cons.mp hw' with h1 | hnil
              · change wireVal 14 C (14 + k) x = false; rw [← hkw, h1]; exact hjf.2
              · cases hnil
          rcases hmem with hgk | hrec
          · subst hgk; rw [hgx] at hkf; cases hkf
          · exact ih k hklt (by omega) hklive hrec hkf
    rcases hlive with heq | hic
    · have : gateVal 14 C g x = false := by change wireVal 14 C (14 + g) x = false; rw [heq]; exact houtf
      rw [hgx] at this; cases this
    · have houtf' : gateVal 14 C (C.output - 14) x = false := by
        change wireVal 14 C (14 + (C.output - 14)) x = false
        rw [Nat.add_sub_of_le hOutBounds.1]; exact houtf
      exact hSub (C.output - 14) (by omega) (Or.inl (Nat.add_sub_of_le hOutBounds.1)) hic houtf'
  have hPairBorn : ∀ w, w < 14 + C.gates.length →
      wireVal 14 C w (P 0 7) = true → wireVal 14 C w (P 0 0) = false → wireVal 14 C w (P 7 7) = false →
      ∃ m : ℕ, (gateAt C m).op = GateOp.and ∧ (w = 14 + m ∨ (14 ≤ w ∧ InCone 14 C m (w - 14))) ∧
        gateVal 14 C m (P 0 7) = true ∧ gateVal 14 C m (P 0 0) = false ∧ gateVal 14 C m (P 7 7) = false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwlt h07 h0 h7
      by_cases hwn : w < 14
      · let idx : Fin 14 := ⟨w, hwn⟩
        rw [hWireVal_in idx (P 0 7)] at h07
        rw [hWireVal_in idx (P 0 0)] at h0
        rw [hWireVal_in idx (P 7 7)] at h7
        have h1' : idx = 0 ∨ idx = 7 := of_decide_eq_true h07
        rcases h1' with h | h
        · rw [h] at h0; change pairInput (0 : Fin 14) 0 0 = false at h0; rw [hP0_0] at h0; cases h0
        · rw [h] at h7; change pairInput (7 : Fin 14) 7 7 = false at h7; rw [hP7_7] at h7; cases h7
      · let j := w - 14
        have hwj : w = 14 + j := by omega
        have hjlt : j < C.gates.length := by omega
        by_cases hAnd : (gateAt C j).op = GateOp.and
        · exact ⟨j, hAnd, Or.inl hwj, by change wireVal 14 C (14 + j) (P 0 7) = true; rw [← hwj]; exact h07, by change wireVal 14 C (14 + j) (P 0 0) = false; rw [← hwj]; exact h0, by change wireVal 14 C (14 + j) (P 7 7) = false; rw [← hwj]; exact h7⟩
        · have h07' : wireVal 14 C (opnd C j 0) (P 0 7) = true ∨ wireVal 14 C (opnd C j 1) (P 0 7) = true := by
            have := h07; rw [hwj] at this; change gateVal 14 C j (P 0 7) = true at this
            rw [hGateVal_eq j hjlt, if_neg hAnd, Bool.or_eq_true] at this; exact this
          have h0' : wireVal 14 C (opnd C j 0) (P 0 0) = false ∧ wireVal 14 C (opnd C j 1) (P 0 0) = false := by
            have := h0; rw [hwj] at this; change gateVal 14 C j (P 0 0) = false at this
            rw [hGateVal_eq j hjlt, if_neg hAnd, Bool.or_eq_false_iff] at this; exact this
          have h7' : wireVal 14 C (opnd C j 0) (P 7 7) = false ∧ wireVal 14 C (opnd C j 1) (P 7 7) = false := by
            have := h7; rw [hwj] at this; change gateVal 14 C j (P 7 7) = false at this
            rw [hGateVal_eq j hjlt, if_neg hAnd, Bool.or_eq_false_iff] at this; exact this
          have lift : ∀ b : Fin 2, wireVal 14 C (opnd C j b) (P 0 7) = true →
              wireVal 14 C (opnd C j b) (P 0 0) = false → wireVal 14 C (opnd C j b) (P 7 7) = false →
              ∃ m : ℕ, (gateAt C m).op = GateOp.and ∧ (w = 14 + m ∨ (14 ≤ w ∧ InCone 14 C m (w - 14))) ∧
                gateVal 14 C m (P 0 7) = true ∧ gateVal 14 C m (P 0 0) = false ∧ gateVal 14 C m (P 7 7) = false := by
            intro b hb07 hb0 hb7
            have hltb : opnd C j b < w := by have := hOpnd_lt j hjlt b; omega
            obtain ⟨m, hmA, hmloc, hm07, hm0, hm7⟩ := ih (opnd C j b) hltb (by omega) hb07 hb0 hb7
            have hmemb : opnd C j b ∈ (gateAt C j).inputs := by rw [hInputs_pair j hjlt]; fin_cases b <;> simp
            refine ⟨m, hmA, Or.inr ⟨by omega, ?_⟩, hm07, hm0, hm7⟩
            rcases hmloc with heq | ⟨hge14, hic⟩
            · exact (hInCone_iff m j).mpr ⟨hjlt, opnd C j b, hmemb, by omega, hOpnd_lt j hjlt b, Or.inl (by omega)⟩
            · exact (hInCone_iff m j).mpr ⟨hjlt, opnd C j b, hmemb, hge14, hOpnd_lt j hjlt b, Or.inr hic⟩
          rcases h07' with h0b | h1b
          · exact lift 0 h0b h0'.1 h7'.1
          · exact lift 1 h1b h0'.2 h7'.2
  have hPairBelow : ∀ (k : ℕ), k < C.gates.length → (gateAt C k).op = GateOp.and →
      gateVal 14 C k (P 0 7) = true →
      (∀ b : Fin 2, wireVal 14 C (opnd C k b) (P 0 0) = false) ∨
      (∀ b : Fin 2, wireVal 14 C (opnd C k b) (P 7 7) = false) →
      gateVal 14 C k (P 0 0) = false → gateVal 14 C k (P 7 7) = false →
      ∃ m0 : ℕ, (gateAt C m0).op = GateOp.and ∧ InCone 14 C m0 k ∧
        gateVal 14 C m0 (P 0 7) = true ∧ gateVal 14 C m0 (P 0 0) = false ∧ gateVal 14 C m0 (P 7 7) = false := by
    intro k hklt hkA hk07 hOpF hk0 hk7
    have hk07' := hk07; rw [hGateVal_eq k hklt, if_pos hkA, Bool.and_eq_true] at hk07'
    have fromOpnd : ∀ b : Fin 2, wireVal 14 C (opnd C k b) (P 0 7) = true →
        wireVal 14 C (opnd C k b) (P 0 0) = false → wireVal 14 C (opnd C k b) (P 7 7) = false →
        ∃ m0 : ℕ, (gateAt C m0).op = GateOp.and ∧ InCone 14 C m0 k ∧
          gateVal 14 C m0 (P 0 7) = true ∧ gateVal 14 C m0 (P 0 0) = false ∧ gateVal 14 C m0 (P 7 7) = false := by
      intro b hb07 hb0 hb7
      have hltb := hOpnd_lt k hklt b
      have hmemb : opnd C k b ∈ (gateAt C k).inputs := by rw [hInputs_pair k hklt]; fin_cases b <;> simp
      obtain ⟨m0, hmA, hmloc, hm07, hm0, hm7⟩ := hPairBorn (opnd C k b) (by omega) hb07 hb0 hb7
      refine ⟨m0, hmA, ?_, hm07, hm0, hm7⟩
      rcases hmloc with heq | ⟨hge14, hic⟩
      · exact (hInCone_iff m0 k).mpr ⟨hklt, opnd C k b, hmemb, by omega, hltb, Or.inl (by omega)⟩
      · exact (hInCone_iff m0 k).mpr ⟨hklt, opnd C k b, hmemb, hge14, hltb, Or.inr hic⟩
    rcases hOpF with hAll0 | hAll7
    · rw [hGateVal_eq k hklt, if_pos hkA, Bool.and_eq_false_iff] at hk7
      rcases hk7 with h70 | h71
      · exact fromOpnd 0 hk07'.1 (hAll0 0) h70
      · exact fromOpnd 1 hk07'.2 (hAll0 1) h71
    · rw [hGateVal_eq k hklt, if_pos hkA, Bool.and_eq_false_iff] at hk0
      rcases hk0 with h00 | h01
      · exact fromOpnd 0 hk07'.1 h00 (hAll7 0)
      · exact fromOpnd 1 hk07'.2 h01 (hAll7 1)
  have hk1lt : k1 < C.gates.length := by
    by_contra hge
    have := hWireVal_ge (14 + k1) (by omega) (P 0 7)
    change gateVal 14 C k1 (P 0 7) = false at this
    rw [hV1] at this; cases this
  have hk2lt : k2 < C.gates.length := by
    by_contra hge
    have := hWireVal_ge (14 + k2) (by omega) (P 0 7)
    change gateVal 14 C k2 (P 0 7) = false at this
    rw [hV2] at this; cases this
  have hk1_p0 : gateVal 14 C k1 (P 0 0) = false := by
    rw [hGateVal_eq k1 hk1lt, if_pos hA1, hOp1 0]; rfl
  have hk2_p7 : gateVal 14 C k2 (P 7 7) = false := by
    rw [hGateVal_eq k2 hk2lt, if_pos hA2, hOp2 0]; rfl
  have hOut_p0 : wireVal 14 C C.output (P 0 0) = false := by
    have := congrFun hFun (P 0 0); change wireVal 14 C C.output (P 0 0) = F (P 0 0) at this
    rw [this]; exact hF_p0
  have hOut_p7 : wireVal 14 C C.output (P 7 7) = false := by
    have := congrFun hFun (P 7 7); change wireVal 14 C C.output (P 7 7) = F (P 7 7) at this
    rw [this]; exact hF_p7
  cases hk1_p7 : gateVal 14 C k1 (P 7 7) with
  | true =>
    obtain ⟨k3, hk3A, hk3L, hk13, hk3f⟩ := hCleaner k1 (P 7 7) hk1lt hL1 hk1_p7 hOut_p7
    cases hk2_p0 : gateVal 14 C k2 (P 0 0) with
    | true =>
      obtain ⟨k4, hk4A, hk4L, hk24, hk4f⟩ := hCleaner k2 (P 0 0) hk2lt hL2 hk2_p0 hOut_p0
      exact hBothDirty C hSz hAO2 hNodup hFun ⟨k1, k2, k3, k4, hNe, hN12, hN21,
        ⟨⟨hA1, hL1⟩, hV1, hOp1⟩, ⟨⟨hA2, hL2⟩, hV2, hOp2⟩, hk1_p7, hk2_p0,
        ⟨hk3A, hk3L⟩, hk13, hk3f, ⟨hk4A, hk4L⟩, hk24, hk4f⟩
    | false =>
      obtain ⟨m0, hm0A, hm02, hm007, hm00, hm07⟩ := hPairBelow k2 hk2lt hA2 hV2 (Or.inr hOp2) hk2_p0 hk2_p7
      exact hMixed C hSz hAO2 hNodup hFun ⟨k1, k2, k3, m0, hNe, hN12, hN21,
        ⟨⟨hA1, hL1⟩, hV1, hOp1⟩, ⟨⟨hA2, hL2⟩, hV2, hOp2⟩, hk1_p7, hk2_p0,
        ⟨hk3A, hk3L⟩, hk13, hk3f, hm0A, hm02, hm007, hm00, hm07⟩
  | false =>
    obtain ⟨k0, hk0A, hk01, hk007, hk00, hk07⟩ := hPairBelow k1 hk1lt hA1 hV1 (Or.inl hOp1) hk1_p0 hk1_p7
    cases hk2_p0 : gateVal 14 C k2 (P 0 0) with
    | false =>
      obtain ⟨m0, hm0A, hm02, hm007, hm00, hm07⟩ := hPairBelow k2 hk2lt hA2 hV2 (Or.inr hOp2) hk2_p0 hk2_p7
      exact hBothClean C hSz hAO2 hNodup hFun ⟨k1, k2, k0, m0, hNe, hN12, hN21,
        ⟨hA1, hL1, hV1, hOp1⟩, ⟨hA2, hL2, hV2, hOp2⟩, hk1_p7, hk2_p0,
        ⟨hk0A, hk01, hk007, hk00, hk07⟩, ⟨hm0A, hm02, hm007, hm00, hm07⟩⟩
    | true =>
      obtain ⟨k4, hk4A, hk4L, hk24, hk4f⟩ := hCleaner k2 (P 0 0) hk2lt hL2 hk2_p0 hOut_p0
      let fw : ℕ → ℕ := fun w => if h : w < 14 then (sig ⟨w, h⟩).val else w
      have hfw_lt : ∀ w, w < 14 → fw w < 14 := by
        intro w hw; dsimp only [fw]; rw [dif_pos hw]; exact (sig ⟨w, hw⟩).isLt
      have hfw_ge : ∀ w, 14 ≤ w → fw w = w := by
        intro w hw; dsimp only [fw]; rw [dif_neg (by omega)]
      have hfw_inj : Function.Injective fw := by
        intro a b hab
        by_cases ha : a < 14 <;> by_cases hb : b < 14
        · dsimp only [fw] at hab; rw [dif_pos ha, dif_pos hb] at hab
          have h1 : (⟨a, ha⟩ : Fin 14) = ⟨b, hb⟩ := hSigInj (Fin.ext hab)
          exact congrArg Fin.val h1
        · have h1 := hfw_lt a ha; rw [hab, hfw_ge b (by omega)] at h1; omega
        · have h1 := hfw_lt b hb; rw [← hab, hfw_ge a (by omega)] at h1; omega
        · rw [hfw_ge a (by omega), hfw_ge b (by omega)] at hab; exact hab
      let mg : Gate → Gate := fun g => ⟨g.op, g.inputs.map fw⟩
      let D : Circuit := ⟨C.gates.map mg, C.output⟩
      have hD_sz : D.size ≤ 27 := by
        change (C.gates.map mg).length ≤ 27
        rw [List.length_map]; exact hSz
      have hD_gateAt : ∀ j, gateAt D j = mg (gateAt C j) := by
        intro j
        by_cases hj : j < C.gates.length
        · change (C.gates.map mg).getD j ⟨GateOp.or, []⟩ = mg (C.gates.getD j ⟨GateOp.or, []⟩)
          rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj),
              List.getD_eq_getElem _ _ hj, List.getElem_map]
        · change (C.gates.map mg).getD j ⟨GateOp.or, []⟩ = mg (C.gates.getD j ⟨GateOp.or, []⟩)
          rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega),
              List.getD_eq_default _ _ (by omega)]
          rfl
      have hD_opnd : ∀ j, j < C.gates.length → ∀ b : Fin 2, opnd D j b = fw (opnd C j b) := by
        intro j hj b
        change (gateAt D j).inputs.getD b.val 0 = fw ((gateAt C j).inputs.getD b.val 0)
        rw [hD_gateAt j]
        dsimp only [mg]
        rw [hInputs_pair j hj]
        fin_cases b <;> rfl
      have hD_AO2 : IsAO2 14 D := by
        refine ⟨?_, ?_, ?_⟩
        · intro g hg
          obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
          exact hAO2.1 g0 hg0
        · intro j hj w hw
          have hj' : j < C.gates.length := by
            change j < (C.gates.map mg).length at hj; rwa [List.length_map] at hj
          rw [hD_gateAt j] at hw
          obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
          by_cases h14 : w0 < 14
          · have := hfw_lt w0 h14; omega
          · rw [hfw_ge w0 (by omega)]; exact hAO2.2.1 j hj' w0 hw0
        · intro g hg
          obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
          dsimp only [mg]; rw [List.length_map]; exact hAO2.2.2 g0 hg0
      have hD_Nodup : ∀ g ∈ D.gates, g.inputs.Nodup := by
        intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        dsimp only [mg]; exact List.Nodup.map hfw_inj (hNodup g0 hg0)
      have hD_cones : ∀ (gs : List Gate) (cs : List (List ℕ)),
          (gs.map mg).foldl (coneStep 14) cs = gs.foldl (coneStep 14) cs := by
        intro gs
        induction gs with
        | nil => intro cs; rfl
        | cons g gs ih =>
          intro cs
          rw [List.map_cons, List.foldl_cons, List.foldl_cons]
          have hStepEq : coneStep 14 cs (mg g) = coneStep 14 cs g := by
            change cs ++ [((g.inputs.map fw).filter (fun w => decide (14 ≤ w ∧ w < 14 + cs.length))).flatMap
              (fun w => (w - 14) :: cs.getD (w - 14) [])] =
              cs ++ [(g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + cs.length))).flatMap
              (fun w => (w - 14) :: cs.getD (w - 14) [])]
            congr 2
            have hFiltEq : (g.inputs.map fw).filter (fun w => decide (14 ≤ w ∧ w < 14 + cs.length)) =
                g.inputs.filter (fun w => decide (14 ≤ w ∧ w < 14 + cs.length)) := by
              induction g.inputs with
              | nil => rfl
              | cons u us ihu =>
                rw [List.map_cons, List.filter_cons, List.filter_cons]
                by_cases hu : u < 14
                · have h1 : decide (14 ≤ fw u ∧ fw u < 14 + cs.length) = false := by
                    have := hfw_lt u hu; exact decide_eq_false (by omega)
                  have h2 : decide (14 ≤ u ∧ u < 14 + cs.length) = false :=
                    decide_eq_false (by omega)
                  rw [h1, h2]; exact ihu
                · rw [hfw_ge u (by omega)]
                  by_cases hc : decide (14 ≤ u ∧ u < 14 + cs.length) = true
                  · rw [hc]; rw [ihu]
                  · have hcf : decide (14 ≤ u ∧ u < 14 + cs.length) = false := Bool.eq_false_iff.mpr hc
                    rw [hcf]; exact ihu
            rw [hFiltEq]
          rw [hStepEq, ih]
      have hD_InCone : ∀ a b, InCone 14 D a b ↔ InCone 14 C a b := by
        intro a b
        change a ∈ ((C.gates.map mg).foldl (coneStep 14) []).getD b [] ↔
          a ∈ (C.gates.foldl (coneStep 14) []).getD b []
        rw [hD_cones C.gates []]
      have hD_wires : ∀ (gs : List Gate) (x : Fin 14 → Bool) (accD accC : List Bool),
          accD.length = accC.length → 14 ≤ accC.length →
          (∀ i : Fin 14, accD.getD (sig i).val false = accC.getD i.val false) →
          (∀ w, 14 ≤ w → accD.getD w false = accC.getD w false) →
          ∀ w, 14 ≤ w → (Wf (gs.map mg) accD).getD w false = (Wf gs accC).getD w false := by
        intro gs
        induction gs with
        | nil => intro x accD accC _ _ _ hge w hw; exact hge w hw
        | cons g gs ih =>
          intro x accD accC hlen h14 hin hge w hw
          rw [List.map_cons]
          change (Wf (gs.map mg) (wstep accD (mg g))).getD w false =
            (Wf gs (wstep accC g)).getD w false
          have hMapEq : (mg g).inputs.map (fun i => accD.getD i false) =
              g.inputs.map (fun i => accC.getD i false) := by
            dsimp only [mg]; rw [List.map_map]
            apply List.map_congr_left
            intro u _
            dsimp only [Function.comp]
            by_cases hu : u < 14
            · dsimp only [fw]; rw [dif_pos hu]; exact hin ⟨u, hu⟩
            · rw [hfw_ge u (by omega)]; exact hge u (by omega)
          have hBitEq : (mg g).op.eval ((mg g).inputs.map fun i => accD.getD i false) =
              g.op.eval (g.inputs.map fun i => accC.getD i false) := by
            rw [hMapEq]
          apply ih x (wstep accD (mg g)) (wstep accC g)
          · dsimp only [wstep]; rw [List.length_append, List.length_append, hlen]; simp
          · dsimp only [wstep]; rw [List.length_append]; simp; omega
          · intro i
            dsimp only [wstep]
            rw [List.getD_append accD _ false _ (by have := (sig i).isLt; omega),
                List.getD_append accC _ false _ (by have := i.isLt; omega)]
            exact hin i
          · intro u hu
            dsimp only [wstep]
            rcases Nat.lt_trichotomy u accC.length with hlt | heq | hgt
            · rw [List.getD_append accD _ false u (by omega),
                  List.getD_append accC _ false u hlt]
              exact hge u hu
            · subst heq
              have h1 : (accD ++ [(mg g).op.eval ((mg g).inputs.map fun i => accD.getD i false)]).getD accC.length false =
                  (mg g).op.eval ((mg g).inputs.map fun i => accD.getD i false) := by rw [← hlen]; simp
              have h2 : (accC ++ [g.op.eval (g.inputs.map fun i => accC.getD i false)]).getD accC.length false =
                  g.op.eval (g.inputs.map fun i => accC.getD i false) := by simp
              rw [h1, h2]; exact hBitEq
            · rw [List.getD_eq_default _ _ (by rw [List.length_append]; simp; omega),
                  List.getD_eq_default _ _ (by rw [List.length_append]; simp; omega)]
          · exact hw
      have hD_gateVal : ∀ (j : ℕ) (x : Fin 14 → Bool),
          gateVal 14 D j x = gateVal 14 C j (fun i => x (sig i)) := by
        intro j x
        change (Wf (C.gates.map mg) (List.ofFn x)).getD (14 + j) false =
          (Wf C.gates (List.ofFn (fun i => x (sig i)))).getD (14 + j) false
        apply hD_wires C.gates x (List.ofFn x) (List.ofFn (fun i => x (sig i)))
        · simp
        · simp
        · intro i
          rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact (sig i).isLt),
              List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
              List.getElem_ofFn, List.getElem_ofFn]
        · intro w hw
          rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega),
              List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
        · omega
      have hD_wireVal_fw : ∀ (w : ℕ) (x : Fin 14 → Bool),
          wireVal 14 D (fw w) x = wireVal 14 C w (fun i => x (sig i)) := by
        intro w x
        by_cases hw : w < 14
        · dsimp only [fw]; rw [dif_pos hw]
          change (Wf (C.gates.map mg) (List.ofFn x)).getD (sig ⟨w, hw⟩).val false =
            (Wf C.gates (List.ofFn (fun i => x (sig i)))).getD w false
          rw [hWf_prefix _ _ _ (by rw [List.length_ofFn]; exact (sig ⟨w, hw⟩).isLt),
              hWf_prefix _ _ _ (by rw [List.length_ofFn]; exact hw),
              List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact (sig ⟨w, hw⟩).isLt),
              List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hw),
              List.getElem_ofFn, List.getElem_ofFn]
        · rw [hfw_ge w (by omega)]
          have hwEq : w = 14 + (w - 14) := by omega
          rw [hwEq]; exact hD_gateVal (w - 14) x
      have hD_fun : circuitFun 14 D = F := by
        funext x
        have hOutEq : circuitFun 14 D x = circuitFun 14 C (fun i => x (sig i)) := by
          change (Wf (C.gates.map mg) (List.ofFn x)).getD C.output false =
            (Wf C.gates (List.ofFn (fun i => x (sig i)))).getD C.output false
          have heq : C.output = 14 + (C.output - 14) := by omega
          rw [heq]; exact hD_gateVal (C.output - 14) x
        rw [hOutEq, hFun]
        apply Bool.eq_iff_iff.mpr
        dsimp only [F]
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨p, l, hpl, hp, hl⟩
          obtain ⟨p2, l2, hp2l2, hsp, hsl⟩ := (hSigDual p l).mp hpl
          rw [hsp] at hp; rw [hsl] at hl
          exact ⟨p2, l2, hp2l2, hl, hp⟩
        · rintro ⟨p2, l2, hp2l2, hp2, hl2⟩
          obtain ⟨p', l', hpl', hsp1, hsl1⟩ := (hSigDual p2 l2).mp hp2l2
          refine ⟨p', l', hpl', ?_, ?_⟩
          · have h1 := congrArg sig hsl1; rw [hSigInv] at h1; rw [← h1]; exact hl2
          · have h1 := congrArg sig hsp1; rw [hSigInv] at h1; rw [← h1]; exact hp2
      have hD_eval0 : ∀ j, gateVal 14 D j (P 0 0) = gateVal 14 C j (P 7 7) := fun j => by
        rw [hD_gateVal j (P 0 0)]; congr 1; funext i; exact hSigP0 i
      have hD_eval7 : ∀ j, gateVal 14 D j (P 7 7) = gateVal 14 C j (P 0 0) := fun j => by
        rw [hD_gateVal j (P 7 7)]; congr 1; funext i; exact hSigP7 i
      have hD_eval07 : ∀ j, gateVal 14 D j (P 0 7) = gateVal 14 C j (P 0 7) := fun j => by
        rw [hD_gateVal j (P 0 7)]; congr 1; funext i; exact hSigP07 i
      have hD_op1 : ∀ b : Fin 2, wireVal 14 D (opnd D k2 b) (P 0 0) = false := fun b => by
        rw [hD_opnd k2 hk2lt b, hD_wireVal_fw]
        have h1 : (fun i => P 0 0 (sig i)) = P 7 7 := funext hSigP0
        rw [h1]; exact hOp2 b
      have hD_op2 : ∀ b : Fin 2, wireVal 14 D (opnd D k1 b) (P 7 7) = false := fun b => by
        rw [hD_opnd k1 hk1lt b, hD_wireVal_fw]
        have h1 : (fun i => P 7 7 (sig i)) = P 0 0 := funext hSigP7
        rw [h1]; exact hOp1 b
      have hD_live : ∀ g, (14 + g = C.output ∨ InCone 14 C g (C.output - 14)) →
          (14 + g = D.output ∨ InCone 14 D g (D.output - 14)) := fun g h => by
        rcases h with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ((hD_InCone g (C.output - 14)).mpr h2)
      exact hMixed D hD_sz hD_AO2 hD_Nodup hD_fun ⟨k2, k1, k4, k0,
        hNe.symm, (hD_InCone k2 k1).not.mpr hN21, (hD_InCone k1 k2).not.mpr hN12,
        ⟨⟨by rw [hD_gateAt k2]; exact hA2, hD_live k2 hL2⟩, by change gateVal 14 D k2 (P 0 7) = true; rw [hD_eval07]; exact hV2, hD_op1⟩,
        ⟨⟨by rw [hD_gateAt k1]; exact hA1, hD_live k1 hL1⟩, by change gateVal 14 D k1 (P 0 7) = true; rw [hD_eval07]; exact hV1, hD_op2⟩,
        by change gateVal 14 D k2 (P 7 7) = true; rw [hD_eval7]; exact hk2_p0,
        by change gateVal 14 D k1 (P 0 0) = false; rw [hD_eval0]; exact hk1_p7,
        ⟨by rw [hD_gateAt k4]; exact hk4A, hD_live k4 hk4L⟩, (hD_InCone k2 k4).mpr hk24,
        by change gateVal 14 D k4 (P 7 7) = false; rw [hD_eval7]; exact hk4f,
        by rw [hD_gateAt k0]; exact hk0A, (hD_InCone k0 k1).mpr hk01,
        by change gateVal 14 D k0 (P 0 7) = true; rw [hD_eval07]; exact hk007,
        by change gateVal 14 D k0 (P 0 0) = false; rw [hD_eval0]; exact hk07,
        by change gateVal 14 D k0 (P 7 7) = false; rw [hD_eval7]; exact hk00⟩
