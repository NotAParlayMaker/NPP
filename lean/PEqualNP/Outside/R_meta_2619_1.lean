import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate
  PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2619_1
    (hsearch :
      let incident (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let hit (x : Fin 26 → Bool) := ∃ p l, incident p l ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∃ (C : Circuit) (a b : ℕ), C.size ≤ 63 ∧ IsAO2 26 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧ a ≠ b ∧
        a < 26 + C.size ∧ b < 26 + C.size ∧
        (∀ p l, incident p l →
          let x (i : Fin 26) := decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
          wireValue C 26 x a = true ∧ wireValue C 26 x b = true) ∧
        ∀ z, Maximal (fun x => ¬ hit x) z →
          wireValue C 26 z (if z (15 : Fin 26) = true then b else a) = false)
    (hmono : ∀ (n : ℕ) (C : Circuit), IsAO2 n C →
      ∀ w, Monotone (fun x : Fin n → Bool => wireValue C n x w)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧       (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧         (∀ (x2 x3 : Fin (13 : ℕ) → Bool), x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)), x3 x4 = Bool.true ∧ (x2 x4 || x2 (x4 + (1 : Fin (13 : ℕ))) || x2 (x4 + (3 : Fin (13 : ℕ))) || x2 (x4 + (9 : Fin (13 : ℕ)))) = Bool.true) ∧           ∃ (x2 : ℕ) (x3 : ℕ) (x4 : ℕ),             x1.output = (26 : ℕ) + x2 ∧               x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } ∧                 ∀ (x5 : Bool),                   have x6 : List Bool := x1.wires (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                   x6.getD x3 Bool.false = Bool.false ∧ x6.getD x4 Bool.false = Bool.false := by
  classical
  obtain ⟨C, a, b, hsize, hao, hnd, hab, ha, hb, hpos, hneg⟩ := hsearch
  let incident (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let hit (x : Fin 26 → Bool) := ∃ p l, incident p l ∧
    x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  let pair (i j : Fin 26) (k : Fin 26) := decide (k = i ∨ k = j)
  let single (i : Fin 26) (k : Fin 26) := decide (k.val = i.val)
  let V := wireValue C 26
  have mono (w : ℕ) : Monotone (fun x => V x w) := hmono 26 C hao w
  have lower {x y : Fin 26 → Bool} (hle : x ≤ y) (w : ℕ)
      (hy : V y w = false) : V x w = false :=
    le_antisymm (hy ▸ mono w hle) (Bool.false_le _)
  have pair_le {i j : Fin 26} {x : Fin 26 → Bool} (hi : x i = true) (hj : x j = true) :
      pair i j ≤ x := by
    intro k
    by_cases hk : k = i ∨ k = j
    · rcases hk with rfl | rfl
      · simp [hi]
      · simp [hj]
    · change decide (k = i ∨ k = j) ≤ x k
      rw [decide_eq_false hk]
      exact Bool.false_le _
  have single_le (i j : Fin 26) : single i ≤ pair i j := by
    intro k
    by_cases hk : k = i
    · subst k
      simp [single, pair]
    · have hn : k.val ≠ i.val := fun h => hk (Fin.ext h)
      simp [single, hn]
  have dark (i : Fin 26)
      (hp : ¬ hit (pair i (2 : Fin 26)))
      (hl : ¬ hit (pair i (15 : Fin 26))) :
      V (single i) a = false ∧ V (single i) b = false := by
    constructor
    · obtain ⟨z, hle, hz⟩ := Finite.exists_le_maximal (p := fun x => ¬ hit x) hp
      have hpoint : z (2 : Fin 26) = true :=
        Bool.eq_true_of_true_le (by simpa [pair] using hle (2 : Fin 26))
      have hline : z (15 : Fin 26) = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        exact hz.1 ⟨2, 2, Or.inl rfl, hpoint, ht⟩
      exact lower ((single_le _ _).trans hle) a (by simpa [hline] using hneg z hz)
    · obtain ⟨z, hle, hz⟩ := Finite.exists_le_maximal (p := fun x => ¬ hit x) hl
      have hline : z (15 : Fin 26) = true :=
        Bool.eq_true_of_true_le (by simpa [pair] using hle (15 : Fin 26))
      exact lower ((single_le _ _).trans hle) b (by simpa [hline] using hneg z hz)
  have correct (x : Fin 26 → Bool) : (V x a && V x b) = true ↔ hit x := by
    rw [Bool.and_eq_true]
    constructor
    · rintro ⟨hxa, hxb⟩
      by_contra hx
      obtain ⟨z, hle, hz⟩ := Finite.exists_le_maximal (p := fun y => ¬ hit y) hx
      have rejected := hneg z hz
      cases hline : z (15 : Fin 26)
      · rw [lower hle a (by simpa [hline] using rejected)] at hxa
        contradiction
      · rw [lower hle b (by simpa [hline] using rejected)] at hxb
        contradiction
    · rintro ⟨p, l, hi, hp, hl⟩
      obtain ⟨left, right⟩ := hpos p l hi
      change V (pair (Fin.castAdd 13 p) (Fin.natAdd 13 l)) a = true at left
      change V (pair (Fin.castAdd 13 p) (Fin.natAdd 13 l)) b = true at right
      have hle := pair_le hp hl
      exact ⟨Bool.eq_true_of_true_le (left ▸ mono a hle),
        Bool.eq_true_of_true_le (right ▸ mono b hle)⟩
  let g : Gate := ⟨GateOp.and, [a, b]⟩
  let D : Circuit := ⟨C.gates ++ [g], 26 + C.gates.length⟩
  have dg : ∀ u ∈ D.gates, u ∈ C.gates ∨ u = g := by
    intro u hu
    simpa [D] using hu
  have hlen (xs : List Bool) : (C.wires xs).length = xs.length + C.gates.length := by
    unfold Circuit.wires
    generalize C.gates = gs
    induction gs generalizing xs with
    | nil => simp
    | cons u gs ih =>
      rw [List.foldl_cons, ih]
      simp
      omega
  have wires (x : Fin 26 → Bool) :
      D.wires (List.ofFn x) = C.wires (List.ofFn x) ++ [V x a && V x b] := by
    simp [D, Circuit.wires, List.foldl_append, g, GateOp.eval, V, PEqualNP.BlindGate.wireValue]
  have len (x : Fin 26 → Bool) : (C.wires (List.ofFn x)).length = 26 + C.gates.length := by
    simp [hlen]
  change a < 26 + C.gates.length at ha
  change b < 26 + C.gates.length at hb
  have nd : ∀ u ∈ D.gates, u.inputs.Nodup := by
    intro u hu
    rcases dg u hu with hu | rfl
    · exact hnd u hu
    · simpa [g] using hab
  have dAO : IsAO2 26 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      rcases dg u hu with hu | rfl
      · exact hao.1 u hu
      · exact Or.inl rfl
    · intro j hj i hi
      have hj' : j < C.gates.length + 1 := by simpa [D] using hj
      by_cases hprev : j < C.gates.length
      · have heq : gateAt D j = gateAt C j := by
          exact List.getD_append _ _ _ _ hprev
        rw [heq] at hi
        exact hao.2.1 j hprev i hi
      · have heq : j = C.gates.length := by omega
        subst j
        have hgate : gateAt D C.gates.length = g := by simp [gateAt, D]
        rw [hgate] at hi
        simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ha
        · exact hb
    · intro u hu
      rcases dg u hu with hu | rfl
      · exact hao.2.2 u hu
      · rfl
  have ev (x : Fin 26 → Bool) : D.eval (List.ofFn x) = (V x a && V x b) := by
    rw [Circuit.eval, wires]
    change (_ ++ [_]).getD (26 + C.gates.length) false = _
    rw [← len x]
    simp
  have hs' : D.size = C.size + 1 := by simp [D, Circuit.size]
  have hs : D.size ≤ 64 := by omega
  refine ⟨D, hs, dAO, nd, ?_, C.gates.length, a, b, rfl, ?_, ?_⟩
  · intro p l
    rw [ev, correct]
    simp only [hit, Fin.addCases_left, Fin.addCases_right]
    constructor
    · rintro ⟨q, j, hq, hpq, hlj⟩
      refine ⟨j, hlj, ?_⟩
      simp only [Bool.or_eq_true]
      rcases hq with rfl | rfl | rfl | rfl <;> tauto
    · rintro ⟨j, hlj, hpj⟩
      simp only [Bool.or_eq_true] at hpj
      rcases hpj with ((h | h) | h) | h
      · exact ⟨j, j, Or.inl rfl, h, hlj⟩
      · exact ⟨j + 1, j, Or.inr (Or.inl rfl), h, hlj⟩
      · exact ⟨j + 3, j, Or.inr (Or.inr (Or.inl rfl)), h, hlj⟩
      · exact ⟨j + 9, j, Or.inr (Or.inr (Or.inr rfl)), h, hlj⟩
  · simp [D, g]
  · intro s
    let x (i : Fin 26) := decide (i.val = if s = true then 13 else 0)
    change (D.wires (List.ofFn x)).getD a false = false ∧
      (D.wires (List.ofFn x)).getD b false = false
    rw [wires, List.getD_append _ _ _ _ (by rw [len]; exact ha),
      List.getD_append _ _ _ _ (by rw [len]; exact hb)]
    change V x a = false ∧ V x b = false
    cases s
    · have hx : x = single (0 : Fin 26) := rfl
      rw [hx]
      exact dark _ (by dsimp [hit, incident, pair]; decide)
        (by dsimp [hit, incident, pair]; decide)
    · have hx : x = single (13 : Fin 26) := rfl
      rw [hx]
      exact dark _ (by dsimp [hit, incident, pair]; decide)
        (by dsimp [hit, incident, pair]; decide)
