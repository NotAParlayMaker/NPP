import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/--
Count the accepted incident pairs before and after replacing binary AND gates with two
positive line-degree operands by false. The surviving pairs need only one-line soundness.
The lost pairs are counted for a minimum-size circuit.
-/
theorem R_meta_4921_731
    (survivors : ∀ (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      Monotone2 C →
      (∀ x : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ 1 →
        (¬ ∃ p l : Fin N, p ∈ S l ∧
          x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false) →
      let D : Circuit := ⟨C.gates.map (fun g =>
        if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
          (g.inputs.all fun i => decide (0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0)) = true
        then ⟨GateOp.or, []⟩ else g), C.output⟩
      ∑ l : Fin N, Fintype.card {p : Fin N // p ∈ S l ∧
        circuitFun (N + N) D
          (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true} ≤
        6 * C.size + 2 * N)
    (losses : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, (S l).card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsMinimalMonoCircuit (N + N) C →
      (∀ x : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, p ∈ S l ∧
          x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false) →
      let D : Circuit := ⟨C.gates.map (fun g =>
        if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
          (g.inputs.all fun i => decide (0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0)) = true
        then ⟨GateOp.or, []⟩ else g), C.output⟩
      ∑ l : Fin N, Fintype.card {p : Fin N // p ∈ S l ∧
        circuitFun (N + N) C
          (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true ∧
        circuitFun (N + N) D
          (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = false} ≤
        93 * C.size) :
    ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, (S l).card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      Monotone2 C →
      (∀ x : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        circuitFun (N + N) C x =
          decide (∃ p l : Fin N, p ∈ S l ∧
            x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)) →
      ∃ O : Circuit, O.size ≤ 100 * C.size ∧
        (∀ g ∈ O.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
        ∀ l : Fin N, ∃ out : ℕ, ∀ p : Fin N,
          (O.wires (List.ofFn fun a : Fin N => decide (a = p))).getD out false =
            decide (p ∈ S l) := by
  intro q N S C hq hN hcard hpair hmono hspec
  let wireStep (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have fold_length (gs : List Gate) (w : List Bool) :
      (gs.foldl wireStep w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [wireStep, List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.add_assoc, Nat.add_comm 1]

  have fold_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl wireStep w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl wireStep (wireStep w g)).getD i false = w.getD i false
      have hstep : i < (wireStep w g).length := by
        simp only [wireStep, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
        exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)
      rw [ih _ hstep]
      simp [wireStep, List.getD, List.getElem?_append_left hi]

  let orStep (a b : ℕ) : Gate := ⟨GateOp.or, [a, b]⟩

  have add_or (gs : List Gate) (w : List Bool) (a b : ℕ) :
      ((gs ++ [orStep a b]).foldl wireStep w).getD (w.length + gs.length) false =
        ((gs.foldl wireStep w).getD a false || (gs.foldl wireStep w).getD b false) := by
    rw [List.foldl_append, ← fold_length gs w]
    change ((gs.foldl wireStep w) ++ [
      ([a, b].map fun i => (gs.foldl wireStep w).getD i false).any id]).getD
        (gs.foldl wireStep w).length false = _
    simp [List.getD]

  have or_list {N : ℕ} (gs : List Gate) (p : Fin N) (ps : List (Fin N)) :
      ∃ (extra : List Gate) (out : ℕ),
        extra.length = ps.length ∧
        (∀ g ∈ extra, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
        out < N + (gs ++ extra).length ∧
        ∀ x : Fin N → Bool,
          ((gs ++ extra).foldl wireStep (List.ofFn x)).getD out false =
            (x p || ps.any x) := by
    induction ps using List.reverseRecOn with
    | nil =>
      refine ⟨[], p.val, by simp, by simp, ?_, ?_⟩
      · rw [List.append_nil]
        exact Nat.lt_of_lt_of_le p.isLt (Nat.le_add_right _ _)
      · intro x
        rw [List.append_nil, fold_prefix]
        · simp
        · simp
    | append_singleton ps a ih =>
      obtain ⟨extra, out, hlen, hshape, hout, heval⟩ := ih
      let g := orStep out a.val
      refine ⟨extra ++ [g], N + (gs ++ extra).length, by simp [hlen],
        ?_, by simp, ?_⟩
      · intro gate hgate
        rcases List.mem_append.mp hgate with h | h
        · exact hshape _ h
        · have e := List.mem_singleton.mp h
          subst gate
          simp [g, orStep]
      · intro x
        have hlenx : (List.ofFn x).length = N := by simp
        rw [← List.append_assoc]
        convert add_or (gs ++ extra) (List.ofFn x) out a.val using 1
        · rw [hlenx]
        rw [heval, fold_prefix]
        · simp [List.any_append, Bool.or_assoc]
        · simp

  have or_lines {N q : ℕ} (S : Fin N → Finset (Fin N))
      (hcard : ∀ l, (S l).card = q + 1) :
      ∃ D : Circuit, D.size = N * q ∧
        (∀ g ∈ D.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
        ∀ l : Fin N, ∃ out : ℕ, ∀ p : Fin N,
          (D.wires (List.ofFn fun a : Fin N => decide (a = p))).getD out false =
            decide (p ∈ S l) := by
    have build (ls : List (Fin N)) :
        ∃ gs : List Gate, gs.length = ls.length * q ∧
          (∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
          ∀ l ∈ ls, ∃ out < N + gs.length, ∀ p : Fin N,
            (gs.foldl wireStep (List.ofFn fun a : Fin N => decide (a = p))).getD out false =
              decide (p ∈ S l) := by
      induction ls with
      | nil => exact ⟨[], by simp, by simp, by simp⟩
      | cons l ls ih =>
        obtain ⟨gs, hlen, hshape, houts⟩ := ih
        have hlist : (S l).toList.length = q + 1 := by simp [hcard]
        cases h : (S l).toList with
        | nil => simp [h] at hlist
        | cons a as =>
          have htail : as.length = q := by simpa [h] using hlist
          obtain ⟨extra, out, hlen', hshape', hout, heval⟩ := or_list gs a as
          refine ⟨gs ++ extra, ?_, ?_, ?_⟩
          · simp [hlen, hlen', htail, Nat.add_mul]
          · intro g hg
            exact (List.mem_append.mp hg).elim (hshape g) (hshape' g)
          · intro l' hl'
            rcases List.mem_cons.mp hl' with rfl | hmem
            · refine ⟨out, hout, fun p => ?_⟩
              rw [heval]
              apply Bool.eq_iff_iff.mpr
              rw [decide_eq_true_eq, ← Finset.mem_toList, h, List.mem_cons, Bool.or_eq_true]
              rw [List.any_eq_true]
              simp only [decide_eq_true_eq]
              rw [exists_eq_right]
              exact or_congr eq_comm Iff.rfl
            · obtain ⟨out', hlt, hval⟩ := houts l' hmem
              refine ⟨out', ?_, fun p => ?_⟩
              · rw [List.length_append, ← Nat.add_assoc]
                exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _)
              · rw [List.foldl_append, fold_prefix, hval]
                simpa [fold_length] using hlt
    obtain ⟨gs, hlen, hshape, houts⟩ := build (List.finRange N)
    refine ⟨⟨gs, 0⟩, ?_, hshape, ?_⟩
    · change gs.length = N * q
      simpa only [List.length_finRange] using hlen
    · intro l
      obtain ⟨out, _, heval⟩ := houts l (by simp)
      exact ⟨out, heval⟩

  let pairInput {N : ℕ} (p l : Fin N) (i : Fin (N + N)) : Bool :=
    decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)

  have pair_spec {N : ℕ} (S : Fin N → Finset (Fin N)) (p l : Fin N) :
      Fintype.card {j : Fin N // pairInput p l (Fin.natAdd N j) = true} = 1 ∧
        (∃ a b : Fin N, a ∈ S b ∧
          pairInput p l (Fin.castAdd N a) = true ∧
          pairInput p l (Fin.natAdd N b) = true) ↔
      p ∈ S l := by
    have hsep (a b : Fin N) : Fin.castAdd N a ≠ Fin.natAdd N b := by
      intro heq
      have he : a.val = N + b.val := congrArg Fin.val heq
      have hge : N ≤ a.val := he.symm ▸ Nat.le_add_right N b.val
      exact Nat.not_lt_of_ge hge a.isLt
    have hl (j : Fin N) : pairInput p l (Fin.natAdd N j) = true ↔ j = l := by
      simp only [pairInput, decide_eq_true_eq, (hsep p j).symm, false_or]
      exact Fin.natAdd_inj N
    have hp (a : Fin N) : pairInput p l (Fin.castAdd N a) = true ↔ a = p := by
      simp only [pairInput, decide_eq_true_eq, hsep a l, or_false]
      exact Fin.castAdd_inj
    have hcard : Fintype.card {j : Fin N // pairInput p l (Fin.natAdd N j) = true} = 1 := by
      rw [Fintype.card_congr (Equiv.subtypeEquivRight hl)]
      exact Fintype.card_unique
    constructor
    · intro hh
      obtain ⟨_, a, b, hab, ha, hb⟩ := hh
      rwa [hp a |>.mp ha, hl b |>.mp hb] at hab
    · intro h
      exact ⟨hcard, p, l, h, (hp _).mpr rfl, (hl _).mpr rfl⟩

  let dropLineAnd (N : ℕ) (C : Circuit) : Circuit :=
    ⟨C.gates.map (fun g =>
      if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
        (g.inputs.all fun i => decide (0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0)) = true
      then ⟨GateOp.or, []⟩ else g), C.output⟩
  classical
  let P (s : ℕ) := ∃ E : Circuit, E.size = s ∧ Monotone2 E ∧
    circuitFun (N + N) E = circuitFun (N + N) C
  have hex : ∃ s, P s := ⟨C.size, C, rfl, hmono, rfl⟩
  obtain ⟨E, hsize, hmonoE, heval⟩ := Nat.find_spec hex
  have hmin : IsMinimalMonoCircuit (N + N) E :=
    ⟨hmonoE, fun A hm he => hsize.trans_le (Nat.find_min' hex ⟨A, rfl, hm, he.trans heval⟩)⟩
  have hle := hmin.2 C hmono heval.symm
  have hneg (x : Fin (N + N) → Bool)
      (hsmall : Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q)
      (hno : ¬ ∃ p l : Fin N, p ∈ S l ∧
        x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) :
      circuitFun (N + N) E x = false := by
    rw [heval, hspec x hsmall]
    exact decide_eq_false hno
  have hqpos : 1 ≤ q := (by decide : 1 ≤ 200).trans hq
  have haccept {p l : Fin N} (hp : p ∈ S l) :
      circuitFun (N + N) E (pairInput p l) = true := by
    obtain ⟨hc, hi⟩ := (pair_spec S p l).mpr hp
    rw [heval, hspec _ (hc.symm ▸ hqpos)]
    exact decide_eq_true hi
  let D := dropLineAnd N E
  let survives (p l : Fin N) := circuitFun (N + N) D (pairInput p l) = true
  let Good (l : Fin N) := (S l).filter (fun p => survives p l)
  let Lost (l : Fin N) := (S l).filter (fun p => ¬ survives p l)
  have hGood (l : Fin N) :
      (Good l).card = Fintype.card {p : Fin N // p ∈ S l ∧ survives p l} := by
    rw [← Fintype.card_coe (Good l)]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun p => Finset.mem_filter))
  have hLost (l : Fin N) :
      (Lost l).card = Fintype.card {p : Fin N // p ∈ S l ∧
        circuitFun (N + N) E (pairInput p l) = true ∧
        circuitFun (N + N) D (pairInput p l) = false} := by
    rw [← Fintype.card_coe (Lost l)]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro p
    rw [Finset.mem_filter]
    constructor
    · intro hh
      obtain ⟨hm, hn⟩ := hh
      exact ⟨hm, haccept hm, Bool.eq_false_of_not_eq_true hn⟩
    · intro hh
      obtain ⟨hm, _, hf⟩ := hh
      exact ⟨hm, by simp [survives, hf]⟩
  have hgood : ∑ l : Fin N, (Good l).card ≤ 6 * E.size + 2 * N := by
    simp only [hGood]
    exact survivors N S E hpair hmonoE (fun x hx => hneg x (hx.trans hqpos))
  have hlost : ∑ l : Fin N, (Lost l).card ≤ 93 * E.size := by
    simp only [hLost]
    exact losses q N S E hq hN hcard hpair hmin hneg
  have hsum : N * (q + 1) ≤ (6 * E.size + 2 * N) + 93 * E.size := by
    have h := Nat.add_le_add hgood hlost
    rw [← Finset.sum_add_distrib] at h
    simpa only [Good, Lost, Finset.card_filter_add_card_filter_not, hcard, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using h
  have hcount : N * q + N ≤ 99 * E.size + 2 * N := by
    rw [Nat.mul_add, Nat.mul_one] at hsum
    calc
      N * q + N ≤ 6 * E.size + 2 * N + 93 * E.size := hsum
      _ = (6 + 93) * E.size + 2 * N := by rw [Nat.add_right_comm, ← Nat.add_mul]
      _ = 99 * E.size + 2 * N := rfl
  have hlarge : 199 * N ≤ 99 * E.size := by
    apply Nat.le_of_add_le_add_right (b := 2 * N)
    calc
      199 * N + 2 * N = N * 200 + N := by
        rw [← Nat.add_mul, Nat.mul_comm N 200, ← Nat.add_one_mul]
      _ ≤ N * q + N := Nat.add_le_add_right (Nat.mul_le_mul_left N hq) N
      _ ≤ 99 * E.size + 2 * N := hcount
  have hNsize : N ≤ E.size := by
    apply Nat.le_of_mul_le_mul_left (c := 100) _ (by decide)
    exact (Nat.mul_le_mul_right N (by decide : 100 ≤ 199)).trans
      (hlarge.trans (Nat.mul_le_mul_right E.size (by decide : 99 ≤ 100)))
  have hbudget : N * q ≤ 100 * E.size := by
    apply Nat.le_of_add_le_add_right (b := N)
    calc
      N * q + N ≤ 99 * E.size + 2 * N := hcount
      _ = 99 * E.size + N + N := by rw [Nat.two_mul, Nat.add_assoc]
      _ ≤ 99 * E.size + E.size + N := Nat.add_le_add_right (Nat.add_le_add_left hNsize _) _
      _ = 100 * E.size + N := by rw [← Nat.add_one_mul]
  obtain ⟨O, hOsize, hOshape, hOout⟩ := or_lines S hcard
  exact ⟨O, hOsize ▸ hbudget.trans (Nat.mul_le_mul_left 100 hle), hOshape, hOout⟩

end PEqualNP.Outside
