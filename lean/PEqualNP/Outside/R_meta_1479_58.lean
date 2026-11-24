import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadK in
set_option maxHeartbeats 2800000 in
theorem PEqualNP.Outside.R_meta_1479_58
    (mono :
      ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ x y : Fin n → Bool,
        (∀ i, x i = true → y i = true) →
        circuitFun n C x = true → circuitFun n C y = true)
    (trace :
    ∀ (n : ℕ) (C : Circuit), IsAO2 n C → ∀ (s t : Fin n) (mark : ℕ → Bool),
      mark s.val = false → mark t.val = true →
      lineSingle C n mark s.val t.val = false →
      ∃ v : ℕ → Bool, (∀ i : Fin n, v i.val = decide (i = t)) ∧
        (∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] →
          (g.op = GateOp.and → v (n + j) =
            (((C.wires (List.ofFn (fun i : Fin n => decide (i = s)))).getD a false && v b) ||
              (v a && (C.wires (List.ofFn (fun i : Fin n => decide (i = s)))).getD b false))) ∧
          (g.op = GateOp.or → v (n + j) = (v a || v b))) ∧ v C.output = false)
    (search :
      let inc (p l : Fin 7) := p = l ∨ p = l + 1 ∨ p = l + 3
      let closed (P : Finset (Fin 7)) : Fin 14 → Bool := fun i => Fin.addCases (motive := fun _ => Bool)
        (fun p : Fin 7 => decide (∀ l : Fin 7, (∀ r ∈ P, ¬ inc r l) → ¬ inc p l))
        (fun l : Fin 7 => decide (∀ p ∈ P, ¬ inc p l)) i
      ∃ C : Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
        (∀ p l : Fin 7, inc p l →
          circuitFun 14 C
            (fun i => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)) = true) ∧
        (∀ P : Finset (Fin 7), circuitFun 14 C (closed P) = false) ∧
        lineSingle C 14 (fun i => decide (7 ≤ i)) 0 7 = false ∧
        lineSingle C 14 (fun i => decide (i < 7)) 7 0 = false) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  classical
  let inc (p l : Fin 7) := p = l ∨ p = l + 1 ∨ p = l + 3
  let closed (P : Finset (Fin 7)) : Fin 14 → Bool := fun i => Fin.addCases (motive := fun _ => Bool)
        (fun p : Fin 7 => decide (∀ l : Fin 7, (∀ r ∈ P, ¬ inc r l) → ¬ inc p l))
        (fun l : Fin 7 => decide (∀ p ∈ P, ¬ inc p l)) i
  obtain ⟨C, cap, strict, accept, reject, lineFlag, pointFlag⟩ := search
  have getGate (j : ℕ) (hj : j < C.gates.length) :
      C.gates[j]? = some (gateAt C j) := by
    change C.gates[j]? = some (C.gates.getD j ⟨.or, []⟩)
    rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  have ao : IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
      exact (strict j g hj).1
    · intro j hj i hi
      obtain ⟨a, b, form, _, ha, hb⟩ := (strict j _ (getGate j hj)).2
      rw [form] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    · intro g hg
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨a, b, form, _, _, _⟩ := (strict j g hj).2
      rw [form]
      rfl
  have hm : Monotone2 C := fun g hg => ⟨ao.1 g hg, (ao.2.2 g hg).le⟩
  have correct (x : Fin 14 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 7, inc p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    change circuitFun 14 C x = true ↔ _
    constructor
    · intro on
      by_contra absent
      let P : Finset (Fin 7) := Finset.univ.filter (fun p => x (Fin.castAdd 7 p) = true)
      have dominates (i : Fin (7 + 7)) : x i = true → closed P i = true := by
        induction i using Fin.addCases with
        | left p =>
          intro hp
          simp only [closed, Fin.addCases_left, decide_eq_true_eq]
          intro l h
          exact h p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
        | right l =>
          intro hl
          simp only [closed, Fin.addCases_right, decide_eq_true_eq]
          intro p hp hi
          exact absent ⟨p, l, hi, (Finset.mem_filter.mp hp).2, hl⟩
      exact Bool.noConfusion ((mono 14 C hm x (closed P) dominates on).symm.trans (reject P))
    · rintro ⟨p, l, hi, hp, hl⟩
      let pair (i : Fin 14) : Bool := decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
      apply mono 14 C hm pair x _ (accept p l hi)
      intro i h
      rcases of_decide_eq_true h with rfl | rfl
      · exact hp
      · exact hl
  have sep (p l : Fin 7) : (Fin.castAdd 7 p : Fin 14) ≠ Fin.natAdd 7 l := by
    intro h
    have he := congrArg Fin.val h
    change p.val = 7 + l.val at he
    have := p.isLt
    omega
  have leftEq (p : Fin 7) : Fin.castAdd 7 p = Fin.castAdd 7 (0 : Fin 7) ↔ p = 0 :=
    (Fin.castAddEmb 7).injective.eq_iff
  have rightEq (l : Fin 7) : Fin.natAdd 7 l = Fin.natAdd 7 (0 : Fin 7) ↔ l = 0 :=
    (Fin.natAddEmb 7).injective.eq_iff
  let p0 : Fin 14 := Fin.castAdd 7 (0 : Fin 7)
  let l0 : Fin 14 := Fin.natAdd 7 (0 : Fin 7)
  obtain ⟨v, vbase, vsteps, vout⟩ := trace 14 C ao p0 l0 (fun i => decide (7 ≤ i))
    (by decide) (by decide) lineFlag
  obtain ⟨w, wbase, wsteps, wout⟩ := trace 14 C ao l0 p0 (fun i => decide (i < 7))
    (by decide) (by decide) pointFlag
  refine ⟨C, cap, strict, correct, 0, 0, Or.inl rfl, ⟨v, ?_, vsteps, vout⟩, ⟨w, ?_, wsteps, wout⟩⟩
  · intro my
    constructor
    · simpa only [l0, Fin.val_castAdd, sep my 0, decide_false] using vbase (Fin.castAdd 7 my)
    · simpa only [l0, Fin.val_natAdd, rightEq] using vbase (Fin.natAdd 7 my)
  · intro mx
    constructor
    · simpa only [p0, Fin.val_castAdd, leftEq] using wbase (Fin.castAdd 7 mx)
    · simpa only [p0, Fin.val_natAdd, (sep 0 mx).symm, decide_false] using wbase (Fin.natAdd 7 mx)
