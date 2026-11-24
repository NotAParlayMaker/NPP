import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 400000 in
theorem PEqualNP.Outside.R_meta_4562_721
    (no12 : ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ))) (12 : ℕ))
    (andNot : ∀ (gs : List Gate) (a b : ℕ), gs.length = 11 → FanInTwo ⟨gs, 0⟩ →
      8 ≤ a → a ≤ 18 → 8 ≤ b → b ≤ 18 → a ≠ b → (a = 18 ∨ b = 18) →
      ∃ x : Fin 8 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x)
        (w.getD a false && !(w.getD b false)) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
           x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4))
    (andAnd : ∀ (gs : List Gate) (a b : ℕ), gs.length = 11 → FanInTwo ⟨gs, 0⟩ →
      8 ≤ a → a < b → b < 18 →
      ∃ x : Fin 8 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x)
        (w.getD a false && (w.getD b false && w.getD 18 false)) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
           x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4))
    (andOr : ∀ (gs : List Gate) (a u v : ℕ), gs.length = 11 → FanInTwo ⟨gs, 0⟩ →
      8 ≤ a → a ≤ 18 → u < v → 8 ≤ v → v ≤ 18 → u ≠ a → v ≠ a → (a = 18 ∨ v = 18) →
      ∃ x : Fin 8 → Bool,
        let w := (Circuit.mk gs 0).wires (List.ofFn x)
        (w.getD a false && (w.getD u false || w.getD v false)) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
           x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length ≤ (12 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (8 : ℕ) ≤ x2 →         x2 < x3 →           x3 < (8 : ℕ) + x1.length →             ∃ (x9 : Fin (8 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9);               (x10.getD x2 Bool.false && x10.getD x3 Bool.false) ≠ (fun (x11 : Fin (8 : ℕ) → Bool) => x11 (0 : Fin (8 : ℕ)) && x11 (1 : Fin (8 : ℕ)) || x11 (1 : Fin (8 : ℕ)) && x11 (2 : Fin (8 : ℕ)) || x11 (2 : Fin (8 : ℕ)) && x11 (3 : Fin (8 : ℕ)) || x11 (0 : Fin (8 : ℕ)) && x11 (4 : Fin (8 : ℕ)) || x11 (1 : Fin (8 : ℕ)) && x11 (5 : Fin (8 : ℕ)) || x11 (2 : Fin (8 : ℕ)) && x11 (6 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ)) && x11 (7 : Fin (8 : ℕ)) || x11 (4 : Fin (8 : ℕ)) && x11 (6 : Fin (8 : ℕ)) || x11 (5 : Fin (8 : ℕ)) && x11 (7 : Fin (8 : ℕ)) || x11 (7 : Fin (8 : ℕ)) && x11 (4 : Fin (8 : ℕ))) x9 := by
  let F8 (x : Fin 8 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have extend (gs : List Gate) (w : List Bool) :
      ∃ extra : List Bool, gs.foldl step w = w ++ extra ∧ extra.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      obtain ⟨extra, he, hl⟩ := ih (step w g)
      exact ⟨_, by simpa [step, List.append_assoc] using he, by simp [hl]⟩
  have foldLen (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    obtain ⟨extra, he, hl⟩ := extend gs w
    rw [he, List.length_append, hl]
  have foldKeep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    obtain ⟨extra, he, _⟩ := extend gs w
    rw [he, List.getD_append _ _ _ _ hi]
  have takeKeep (gs : List Gate) (k : ℕ) (w : List Bool) (i : ℕ) (hi : i < w.length + k) (hk : k ≤ gs.length) :
      (gs.foldl step w).getD i false = ((gs.take k).foldl step w).getD i false := by
    have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_lhs => rw [hsplit]
    rw [List.foldl_append]
    apply foldKeep
    rw [foldLen, List.length_take]
    omega
  have fanTake (gs : List Gate) (k : ℕ) (hf : FanInTwo ⟨gs, 0⟩) : FanInTwo ⟨gs.take k, 0⟩ :=
    fun g hg => hf g (List.mem_of_mem_take hg)
  have snocGetLast (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    simp
  have snocGetOld (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
      (w ++ [b]).getD i false = w.getD i false :=
    List.getD_append _ _ _ _ hi
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have evalNot (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  intro x1 x2 x3 hlen hfan hx2 h23 hx3
  apply Classical.byContradiction
  intro hno
  have hcomp (x : Fin 8 → Bool) :
      ((x1.foldl step (List.ofFn x)).getD x2 false &&
       (x1.foldl step (List.ofFn x)).getD x3 false) = F8 x := by
    apply Classical.byContradiction
    intro hne
    exact hno ⟨x, hne⟩
  have hx3_ge : 19 ≤ x3 := by
    apply Classical.byContradiction
    intro hlt
    have hk_le : x3 - 7 ≤ x1.length := by omega
    have hk_11 : x3 - 7 ≤ 11 := by omega
    let pref := x1.take (x3 - 7)
    have hplen : pref.length = x3 - 7 := by simp [pref]; omega
    let C : Circuit := ⟨pref ++ [⟨GateOp.and, [x2, x3]⟩], 8 + pref.length⟩
    have hCfan : FanInTwo C := by
      intro g hg
      rcases List.mem_append.mp hg with hp | hl
      · exact fanTake x1 (x3 - 7) hfan g hp
      · rw [List.mem_singleton.mp hl]
        exact ⟨Or.inl rfl, by simp⟩
    have hCsize : C.size ≤ 12 := by
      change (pref ++ [(⟨GateOp.and, [x2, x3]⟩ : Gate)]).length ≤ 12
      rw [List.length_append, List.length_singleton, hplen]
      omega
    have hCeval (x : Fin 8 → Bool) : C.eval (List.ofFn x) = F8 x := by
      change ((pref ++ [(⟨GateOp.and, [x2, x3]⟩ : Gate)]).foldl step (List.ofFn x)).getD (8 + pref.length) false = F8 x
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      set w := pref.foldl step (List.ofFn x)
      have hwlen : w.length = 8 + pref.length := by rw [foldLen, List.length_ofFn]
      change (w ++ [GateOp.and.eval ([w.getD x2 false, w.getD x3 false])]).getD (8 + pref.length) false = F8 x
      rw [← hwlen, snocGetLast]
      simp only [evalAnd, List.all_cons, List.all_nil, id, Bool.and_true]
      have e2 : w.getD x2 false = (x1.foldl step (List.ofFn x)).getD x2 false :=
        (takeKeep x1 (x3 - 7) (List.ofFn x) x2 (by rw [List.length_ofFn]; omega) hk_le).symm
      have e3 : w.getD x3 false = (x1.foldl step (List.ofFn x)).getD x3 false :=
        (takeKeep x1 (x3 - 7) (List.ofFn x) x3 (by rw [List.length_ofFn]; omega) hk_le).symm
      rw [e2, e3]
      exact hcomp x
    exact no12 ⟨C, hCfan, hCsize, hCeval⟩
  have hx3_eq : x3 = 19 := by omega
  have hx1_len : x1.length = 12 := by omega
  let gs := x1.take 11
  let g := x1[11]'(by omega)
  have hgs_len : gs.length = 11 := by simp [gs, hx1_len]
  have hgs_fan : FanInTwo ⟨gs, 0⟩ := fanTake x1 11 hfan
  have hx1_eq : x1 = gs ++ [g] := by
    have hdrop : x1.drop 11 = [g] := by
      apply List.ext_getElem
      · simp [hx1_len]
      · intro i hi1 hi2
        have hi0 : i = 0 := by simp at hi2; omega
        subst hi0
        simp [g]
    rw [← hdrop]
    exact (List.take_append_drop 11 x1).symm
  let W (x : Fin 8 → Bool) : List Bool := gs.foldl step (List.ofFn x)
  have hWlen (x : Fin 8 → Bool) : (W x).length = 19 := by
    rw [foldLen, List.length_ofFn, hgs_len]
  have hWx2 (x : Fin 8 → Bool) : (x1.foldl step (List.ofFn x)).getD x2 false = (W x).getD x2 false := by
    exact takeKeep x1 11 (List.ofFn x) x2 (by rw [List.length_ofFn]; omega) (by omega)
  have hWx3 (x : Fin 8 → Bool) :
      (x1.foldl step (List.ofFn x)).getD 19 false = g.op.eval (g.inputs.map fun i => (W x).getD i false) := by
    conv_lhs => rw [hx1_eq]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (W x ++ [g.op.eval (g.inputs.map fun i => (W x).getD i false)]).getD 19 false = _
    rw [← hWlen x, snocGetLast]
  have hmain (x : Fin 8 → Bool) :
      ((W x).getD x2 false && g.op.eval (g.inputs.map fun i => (W x).getD i false)) = F8 x := by
    have h := hcomp x
    rw [hx3_eq, hWx2, hWx3] at h
    exact h
  have noSingle (i : ℕ) (h : ∀ x, (W x).getD i false = F8 x) : False :=
    no12 ⟨⟨gs, i⟩, hgs_fan, by change gs.length ≤ 12; omega, h⟩
  have noAndPair (i j : ℕ) (h : ∀ x, ((W x).getD i false && (W x).getD j false) = F8 x) : False := by
    let C : Circuit := ⟨gs ++ [⟨GateOp.and, [i, j]⟩], 19⟩
    have hCf : FanInTwo C := by
      intro q hq
      rcases List.mem_append.mp hq with h1 | h2
      · exact hgs_fan q h1
      · rw [List.mem_singleton.mp h2]; exact ⟨Or.inl rfl, by simp⟩
    have hCs : C.size ≤ 12 := by
      change (gs ++ [(⟨GateOp.and, [i, j]⟩ : Gate)]).length ≤ 12
      rw [List.length_append, List.length_singleton, hgs_len]
    have hCe (x : Fin 8 → Bool) : C.eval (List.ofFn x) = F8 x := by
      change ((gs ++ [(⟨GateOp.and, [i, j]⟩ : Gate)]).foldl step (List.ofFn x)).getD 19 false = F8 x
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (W x ++ [GateOp.and.eval [(W x).getD i false, (W x).getD j false]]).getD 19 false = F8 x
      rw [← hWlen x, snocGetLast]
      simp only [evalAnd, List.all_cons, List.all_nil, id, Bool.and_true]
      exact h x
    exact no12 ⟨C, hCf, hCs, hCe⟩
  have noConst (b : Bool) (h : ∀ x, b = F8 x) : False := by
    have h0 : b = false := (h (fun _ => false)).trans (by decide)
    have h1 : b = true := (h (fun _ => true)).trans (by decide)
    rw [h0] at h1
    exact Bool.noConfusion h1
  have readInput (x : Fin 8 → Bool) (i : ℕ) (hi : i < 8) : (W x).getD i false = x ⟨i, hi⟩ := by
    rw [foldKeep gs (List.ofFn x) i (by rw [List.length_ofFn]; exact hi)]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
  have notInputSuper (i : ℕ) (hi : i < 8) (h : ∀ x, F8 x = true → (W x).getD i false = true) : False := by
    by_cases h04 : i = 0 ∨ i = 4
    · let y : Fin 8 → Bool := fun j => decide (j.val = 1 ∨ j.val = 5)
      have hy := h y (by decide)
      rw [readInput y i hi] at hy
      have : y ⟨i, hi⟩ = false := by
        rcases h04 with rfl | rfl <;> simp [y]
      rw [this] at hy
      exact Bool.noConfusion hy
    · let y : Fin 8 → Bool := fun j => decide (j.val = 0 ∨ j.val = 4)
      have hy := h y (by decide)
      rw [readInput y i hi] at hy
      have : y ⟨i, hi⟩ = false := by
        simp [y]
        omega
      rw [this] at hy
      exact Bool.noConfusion hy
  have notOutOfRangeSuper (i : ℕ) (hi : 19 ≤ i) (h : ∀ x, F8 x = true → (W x).getD i false = true) : False := by
    have hy := h (fun _ => true) (by decide)
    rw [List.getD_eq_default _ _ (by rw [hWlen]; exact hi)] at hy
    exact Bool.noConfusion hy
  have notNotInputSuper (i : ℕ) (hi : i < 8) (h : ∀ x, F8 x = true → (!((W x).getD i false)) = true) : False := by
    have hy := h (fun _ => true) (by decide)
    rw [readInput (fun _ => true) i hi] at hy
    exact Bool.noConfusion hy
  have notTwoInputOrSuper (u v : ℕ) (hu : u < 8) (hv : v < 8)
      (h : ∀ x, F8 x = true → ((W x).getD u false || (W x).getD v false) = true) : False := by
    by_cases h04 : (u ≠ 0 ∧ u ≠ 4) ∧ (v ≠ 0 ∧ v ≠ 4)
    · let y : Fin 8 → Bool := fun j => decide (j.val = 0 ∨ j.val = 4)
      have hy := h y (by decide)
      rw [readInput y u hu, readInput y v hv] at hy
      have e1 : y ⟨u, hu⟩ = false := by simp [y]; omega
      have e2 : y ⟨v, hv⟩ = false := by simp [y]; omega
      rw [e1, e2] at hy
      exact Bool.noConfusion hy
    · by_cases h15 : (u ≠ 1 ∧ u ≠ 5) ∧ (v ≠ 1 ∧ v ≠ 5)
      · let y : Fin 8 → Bool := fun j => decide (j.val = 1 ∨ j.val = 5)
        have hy := h y (by decide)
        rw [readInput y u hu, readInput y v hv] at hy
        have e1 : y ⟨u, hu⟩ = false := by simp [y]; omega
        have e2 : y ⟨v, hv⟩ = false := by simp [y]; omega
        rw [e1, e2] at hy
        exact Bool.noConfusion hy
      · let y : Fin 8 → Bool := fun j => decide (j.val = 2 ∨ j.val = 6)
        have hy := h y (by decide)
        rw [readInput y u hu, readInput y v hv] at hy
        have e1 : y ⟨u, hu⟩ = false := by simp [y]; omega
        have e2 : y ⟨v, hv⟩ = false := by simp [y]; omega
        rw [e1, e2] at hy
        exact Bool.noConfusion hy
  have buildTwo (g1 g2 : Gate) (hf1 : g1.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g1.inputs.length ≤ 2)
      (hf2 : g2.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g2.inputs.length ≤ 2)
      (he : ∀ x : Fin 8 → Bool,
        let w10 := (gs.take 10).foldl step (List.ofFn x)
        let w11 := step w10 g1
        g2.op.eval (g2.inputs.map fun i => w11.getD i false) = F8 x) : False := by
    let p10 := gs.take 10
    have hp10 : p10.length = 10 := by simp [p10, hgs_len]
    let C : Circuit := ⟨p10 ++ [g1, g2], 19⟩
    have hCf : FanInTwo C := by
      intro q hq
      rcases List.mem_append.mp hq with h1 | h2
      · exact fanTake gs 10 hgs_fan q h1
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact hf1
        · rw [List.mem_singleton.mp h3]; exact hf2
    have hCs : C.size ≤ 12 := by
      change (p10 ++ [g1, g2]).length ≤ 12
      rw [List.length_append, List.length_cons, List.length_singleton, hp10]
    have hCe (x : Fin 8 → Bool) : C.eval (List.ofFn x) = F8 x := by
      change ((p10 ++ [g1, g2]).foldl step (List.ofFn x)).getD 19 false = F8 x
      rw [List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
      set w10 := p10.foldl step (List.ofFn x)
      set w11 := step w10 g1
      have hw11len : w11.length = 19 := by
        rw [show w11 = step w10 g1 from rfl, show step w10 g1 = w10 ++ [_] from rfl,
          List.length_append, List.length_singleton, foldLen, List.length_ofFn, hp10]
      change (w11 ++ [g2.op.eval (g2.inputs.map fun i => w11.getD i false)]).getD 19 false = F8 x
      rw [← hw11len, snocGetLast]
      exact he x
    exact no12 ⟨C, hCf, hCs, hCe⟩
  have keep10 (x : Fin 8 → Bool) (i : ℕ) (hi : i < 18) :
      ((gs.take 10).foldl step (List.ofFn x)).getD i false = (W x).getD i false :=
    (takeKeep gs 10 (List.ofFn x) i (by rw [List.length_ofFn]; omega) (by omega)).symm
  have mustUse18_not (a b : ℕ) (ha : a < 18) (hb : b < 18)
      (h : ∀ x, ((W x).getD a false && !((W x).getD b false)) = F8 x) : False := by
    apply buildTwo ⟨GateOp.not, [b]⟩ ⟨GateOp.and, [a, 18]⟩
      ⟨Or.inr (Or.inr rfl), by simp⟩ ⟨Or.inl rfl, by simp⟩
    intro x
    set w10 := (gs.take 10).foldl step (List.ofFn x)
    have hw10len : w10.length = 18 := by rw [foldLen, List.length_ofFn, List.length_take]; omega
    change GateOp.and.eval [(step w10 ⟨GateOp.not, [b]⟩).getD a false,
      (step w10 ⟨GateOp.not, [b]⟩).getD 18 false] = F8 x
    have e1 : (step w10 ⟨GateOp.not, [b]⟩).getD a false = (W x).getD a false := by
      rw [snocGetOld w10 _ a (by rw [hw10len]; exact ha), keep10 x a ha]
    have e2 : (step w10 ⟨GateOp.not, [b]⟩).getD 18 false = !((W x).getD b false) := by
      change (w10 ++ [GateOp.not.eval [w10.getD b false]]).getD 18 false = _
      rw [← hw10len, snocGetLast, evalNot]
      simp only [List.headD_cons]
      rw [keep10 x b hb]
    rw [e1, e2]
    simp only [evalAnd, List.all_cons, List.all_nil, id, Bool.and_true]
    exact h x
  have mustUse18_and (a b c : ℕ) (ha : a < 18) (hb : b < 18) (hc : c < 18)
      (h : ∀ x, ((W x).getD a false && ((W x).getD b false && (W x).getD c false)) = F8 x) : False := by
    apply buildTwo ⟨GateOp.and, [b, c]⟩ ⟨GateOp.and, [a, 18]⟩
      ⟨Or.inl rfl, by simp⟩ ⟨Or.inl rfl, by simp⟩
    intro x
    set w10 := (gs.take 10).foldl step (List.ofFn x)
    have hw10len : w10.length = 18 := by rw [foldLen, List.length_ofFn, List.length_take]; omega
    change GateOp.and.eval [(step w10 ⟨GateOp.and, [b, c]⟩).getD a false,
      (step w10 ⟨GateOp.and, [b, c]⟩).getD 18 false] = F8 x
    have e1 : (step w10 ⟨GateOp.and, [b, c]⟩).getD a false = (W x).getD a false := by
      rw [snocGetOld w10 _ a (by rw [hw10len]; exact ha), keep10 x a ha]
    have e2 : (step w10 ⟨GateOp.and, [b, c]⟩).getD 18 false = ((W x).getD b false && (W x).getD c false) := by
      change (w10 ++ [GateOp.and.eval [w10.getD b false, w10.getD c false]]).getD 18 false = _
      rw [← hw10len, snocGetLast, evalAnd]
      simp only [List.all_cons, List.all_nil, id, Bool.and_true]
      rw [keep10 x b hb, keep10 x c hc]
    rw [e1, e2]
    simp only [evalAnd, List.all_cons, List.all_nil, id, Bool.and_true]
    exact h x
  have mustUse18_or (a u v : ℕ) (ha : a < 18) (hu : u < 18) (hv : v < 18)
      (h : ∀ x, ((W x).getD a false && ((W x).getD u false || (W x).getD v false)) = F8 x) : False := by
    apply buildTwo ⟨GateOp.or, [u, v]⟩ ⟨GateOp.and, [a, 18]⟩
      ⟨Or.inr (Or.inl rfl), by simp⟩ ⟨Or.inl rfl, by simp⟩
    intro x
    set w10 := (gs.take 10).foldl step (List.ofFn x)
    have hw10len : w10.length = 18 := by rw [foldLen, List.length_ofFn, List.length_take]; omega
    change GateOp.and.eval [(step w10 ⟨GateOp.or, [u, v]⟩).getD a false,
      (step w10 ⟨GateOp.or, [u, v]⟩).getD 18 false] = F8 x
    have e1 : (step w10 ⟨GateOp.or, [u, v]⟩).getD a false = (W x).getD a false := by
      rw [snocGetOld w10 _ a (by rw [hw10len]; exact ha), keep10 x a ha]
    have e2 : (step w10 ⟨GateOp.or, [u, v]⟩).getD 18 false = ((W x).getD u false || (W x).getD v false) := by
      change (w10 ++ [GateOp.or.eval [w10.getD u false, w10.getD v false]]).getD 18 false = _
      rw [← hw10len, snocGetLast, evalOr]
      simp only [List.any_cons, List.any_nil, id, Bool.or_false]
      rw [keep10 x u hu, keep10 x v hv]
    rw [e1, e2]
    simp only [evalAnd, List.all_cons, List.all_nil, id, Bool.and_true]
    exact h x
  have hg_mem : g ∈ x1 := List.getElem_mem (by omega)
  obtain ⟨hg_op, hg_in⟩ := hfan g hg_mem
  have hg_op' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg_op
  have hx2_18 : x2 ≤ 18 := by omega
  rcases hg_op' with hop | hop | hop
  · -- g.op = GateOp.and
    rcases hin : g.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
    · apply noSingle x2
      intro x
      have h := hmain x
      rw [hop, hin] at h
      simpa [evalAnd] using h
    · apply noAndPair x2 u
      intro x
      have h := hmain x
      rw [hop, hin] at h
      simpa [evalAnd] using h
    · have h3 (x : Fin 8 → Bool) :
          ((W x).getD x2 false && ((W x).getD u false && (W x).getD v false)) = F8 x := by
        have h := hmain x
        rw [hop, hin] at h
        simpa [evalAnd] using h
      have hu_ge : 8 ≤ u := by
        apply Classical.byContradiction
        intro hlt
        exact notInputSuper u (by omega) (fun x hx => by
          have e := (h3 x).trans hx
          exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp e).2).1)
      have hu_le : u ≤ 18 := by
        apply Classical.byContradiction
        intro hgt
        exact notOutOfRangeSuper u (by omega) (fun x hx => by
          have e := (h3 x).trans hx
          exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp e).2).1)
      have hv_ge : 8 ≤ v := by
        apply Classical.byContradiction
        intro hlt
        exact notInputSuper v (by omega) (fun x hx => by
          have e := (h3 x).trans hx
          exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp e).2).2)
      have hv_le : v ≤ 18 := by
        apply Classical.byContradiction
        intro hgt
        exact notOutOfRangeSuper v (by omega) (fun x hx => by
          have e := (h3 x).trans hx
          exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp e).2).2)
      have closeAnd3 (p q r : ℕ) (hp : 8 ≤ p) (hpq : p < q) (hqr : q < r) (hr : r ≤ 18)
          (h : ∀ x, ((W x).getD p false && ((W x).getD q false && (W x).getD r false)) = F8 x) : False := by
        by_cases hr18 : r = 18
        · subst hr18
          obtain ⟨x, hx⟩ := andAnd gs p q hgs_len hgs_fan hp hpq hqr
          exact hx (h x)
        · exact mustUse18_and p q r (by omega) (by omega) (by omega) h
      by_cases huv : u = v
      · subst huv
        exact noAndPair x2 u (fun x => by simpa [Bool.and_self] using h3 x)
      by_cases hxu : x2 = u
      · subst hxu
        exact noAndPair x2 v (fun x => by
          have e := h3 x
          rw [← Bool.and_assoc, Bool.and_self] at e
          exact e)
      by_cases hxv : x2 = v
      · subst hxv
        exact noAndPair x2 u (fun x => by
          have e := h3 x
          rw [Bool.and_comm ((W x).getD u false), ← Bool.and_assoc, Bool.and_self] at e
          exact e)
      by_cases h1 : x2 < u
      · by_cases h2 : u < v
        · exact closeAnd3 x2 u v hx2 h1 h2 hv_le h3
        · by_cases h4 : x2 < v
          · exact closeAnd3 x2 v u hx2 h4 (by omega) hu_le (fun x => by
              rw [Bool.and_comm ((W x).getD v false)]; exact h3 x)
          · exact closeAnd3 v x2 u hv_ge (by omega) h1 hu_le (fun x => by
              rw [← h3 x]; cases (W x).getD x2 false <;> cases (W x).getD u false <;> cases (W x).getD v false <;> rfl)
      · by_cases h2 : x2 < v
        · exact closeAnd3 u x2 v hu_ge (by omega) h2 hv_le (fun x => by
            rw [← h3 x]; cases (W x).getD x2 false <;> cases (W x).getD u false <;> cases (W x).getD v false <;> rfl)
        · by_cases h4 : u < v
          · exact closeAnd3 u v x2 hu_ge h4 (by omega) hx2_18 (fun x => by
              rw [← h3 x]; cases (W x).getD x2 false <;> cases (W x).getD u false <;> cases (W x).getD v false <;> rfl)
          · exact closeAnd3 v u x2 hv_ge (by omega) (by omega) hx2_18 (fun x => by
              rw [← h3 x]; cases (W x).getD x2 false <;> cases (W x).getD u false <;> cases (W x).getD v false <;> rfl)
    · rw [hin] at hg_in
      simp at hg_in
  · -- g.op = GateOp.or
    rcases hin : g.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
    · apply noConst false
      intro x
      have h := hmain x
      rw [hop, hin] at h
      simpa [evalOr] using h
    · apply noAndPair x2 u
      intro x
      have h := hmain x
      rw [hop, hin] at h
      simpa [evalOr] using h
    · have hor (x : Fin 8 → Bool) :
          ((W x).getD x2 false && ((W x).getD u false || (W x).getD v false)) = F8 x := by
        have h := hmain x
        rw [hop, hin] at h
        simpa [evalOr] using h
      by_cases hu19 : 19 ≤ u
      · apply noAndPair x2 v
        intro x
        have hu0 : (W x).getD u false = false := List.getD_eq_default _ _ (by rw [hWlen]; exact hu19)
        have h := hor x
        rw [hu0, Bool.false_or] at h
        exact h
      by_cases hv19 : 19 ≤ v
      · apply noAndPair x2 u
        intro x
        have hv0 : (W x).getD v false = false := List.getD_eq_default _ _ (by rw [hWlen]; exact hv19)
        have h := hor x
        rw [hv0, Bool.or_false] at h
        exact h
      by_cases huv : u = v
      · subst huv
        exact noAndPair x2 u (fun x => by simpa [Bool.or_self] using hor x)
      by_cases hxu : u = x2
      · subst hxu
        apply noSingle u
        intro x
        rw [← hor x]
        cases (W x).getD u false <;> cases (W x).getD v false <;> rfl
      by_cases hxv : v = x2
      · subst hxv
        apply noSingle v
        intro x
        rw [← hor x]
        cases (W x).getD u false <;> cases (W x).getD v false <;> rfl
      have closeOr (p q : ℕ) (hpq : p < q) (hq18 : q ≤ 18) (hpne : p ≠ x2) (hqne : q ≠ x2)
          (h : ∀ x, ((W x).getD x2 false && ((W x).getD p false || (W x).getD q false)) = F8 x) : False := by
        have hq8 : 8 ≤ q := by
          apply Classical.byContradiction
          intro hlt
          exact notTwoInputOrSuper p q (by omega) (by omega) (fun x hx => by
            exact (Bool.and_eq_true_iff.mp ((h x).trans hx)).2)
        by_cases htop : x2 = 18 ∨ q = 18
        · obtain ⟨x, hx⟩ := andOr gs x2 p q hgs_len hgs_fan hx2 hx2_18 hpq hq8 hq18 hpne hqne htop
          exact hx (h x)
        · exact mustUse18_or x2 p q (by omega) (by omega) (by omega) h
      by_cases hlt : u < v
      · exact closeOr u v hlt (by omega) hxu hxv hor
      · exact closeOr v u (by omega) (by omega) hxv hxu (fun x => by
          rw [Bool.or_comm]; exact hor x)
    · rw [hin] at hg_in
      simp at hg_in
  · -- g.op = GateOp.not
    rcases hin : g.inputs with _ | ⟨u, rest⟩
    · apply noSingle x2
      intro x
      have h := hmain x
      rw [hop, hin] at h
      simpa [evalNot] using h
    · have hnot (x : Fin 8 → Bool) :
          ((W x).getD x2 false && !((W x).getD u false)) = F8 x := by
        have h := hmain x
        rw [hop, hin] at h
        simpa [evalNot] using h
      by_cases hu19 : 19 ≤ u
      · apply noSingle x2
        intro x
        have hu0 : (W x).getD u false = false := List.getD_eq_default _ _ (by rw [hWlen]; exact hu19)
        have h := hnot x
        rw [hu0] at h
        simpa using h
      have hu8 : 8 ≤ u := by
        apply Classical.byContradiction
        intro hlt
        exact notNotInputSuper u (by omega) (fun x hx => by
          exact (Bool.and_eq_true_iff.mp ((hnot x).trans hx)).2)
      by_cases hxu : x2 = u
      · subst hxu
        apply noConst false
        intro x
        rw [← hnot x]
        cases (W x).getD x2 false <;> rfl
      by_cases htop : x2 = 18 ∨ u = 18
      · obtain ⟨x, hx⟩ := andNot gs x2 u hgs_len hgs_fan hx2 hx2_18 hu8 (by omega) hxu htop
        exact hx (hnot x)
      · exact mustUse18_not x2 u (by omega) (by omega) hnot
