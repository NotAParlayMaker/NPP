import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2619_1
    (candidate :
      let clear := fun (p : Fin 13 → Bool) (j : Fin 13) =>
        !(p j || p (j + 1) || p (j + 3) || p (j + 9))
      ∃ (C : Circuit) (a b : ℕ), C.size ≤ 63 ∧ PEqualNP.TopForm.IsAO2 26 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧ a ≠ b ∧ a < 26 + C.size ∧ b < 26 + C.size ∧
        (∀ s : Bool,
          let w := C.wires (List.ofFn fun i : Fin 26 =>
            decide (i.val = if s = true then 13 else 0))
          w.getD a false = false ∧ w.getD b false = false) ∧
        (∀ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) →
          let w := C.wires (List.ofFn fun k =>
            Fin.addCases (fun i => decide (i = p)) (fun i => decide (i = l)) k)
          (w.getD a false && w.getD b false) = true) ∧
        (∀ p : Fin 13 → Bool,
          let w := C.wires (List.ofFn fun k => Fin.addCases p (clear p) k)
          (w.getD a false && w.getD b false) = false))
    (monotone :
      ∀ (C : Circuit), PEqualNP.EdgeOwnership.AndOrOnly C →
        ∀ (x y : Fin 26 → Bool), (∀ i, x i = true → y i = true) →
          C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧       (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧         (∀ (x2 x3 : Fin (13 : ℕ) → Bool), x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)), x3 x4 = Bool.true ∧ (x2 x4 || x2 (x4 + (1 : Fin (13 : ℕ))) || x2 (x4 + (3 : Fin (13 : ℕ))) || x2 (x4 + (9 : Fin (13 : ℕ)))) = Bool.true) ∧           ∃ (x2 : ℕ) (x3 : ℕ) (x4 : ℕ),             x1.output = (26 : ℕ) + x2 ∧               x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } ∧                 ∀ (x5 : Bool),                   have x6 : List Bool := x1.wires (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                   x6.getD x3 Bool.false = Bool.false ∧ x6.getD x4 Bool.false = Bool.false := by
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let incident (p l : Fin 13) : Prop :=
    p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

  let clearLines (p : Fin 13 → Bool) (j : Fin 13) : Bool :=
    !(p j || p (j + 1) || p (j + 3) || p (j + 9))

  let pairValue (C : Circuit) (a b : ℕ) (x : Fin 26 → Bool) : Bool :=
    let w := C.wires (List.ofFn x)
    w.getD a false && w.getD b false

  let cold (C : Circuit) (a b : ℕ) : Prop :=
    ∀ s : Bool,
      let w := C.wires (List.ofFn fun i : Fin 26 => decide (i.val = if s = true then 13 else 0))
      w.getD a false = false ∧ w.getD b false = false

  let make (C : Circuit) (a b : ℕ) : Circuit :=
    ⟨C.gates ++ [⟨.and, [a, b]⟩], 26 + C.size⟩

  have wireLen (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega

  have wiresMake (C : Circuit) (a b : ℕ) (x : Fin 26 → Bool) :
      (make C a b).wires (List.ofFn x) = C.wires (List.ofFn x) ++ [pairValue C a b x] := by
    simp [make, Circuit.wires, pairValue, List.foldl_append, GateOp.eval]

  have len (C : Circuit) (x : Fin 26 → Bool) :
      (C.wires (List.ofFn x)).length = 26 + C.size := by
    change (C.gates.foldl step (List.ofFn x)).length = _
    simp [wireLen, Circuit.size]

  have evalMake (C : Circuit) (a b : ℕ) (x : Fin 26 → Bool) :
      (make C a b).eval (List.ofFn x) = pairValue C a b x := by
    rw [Circuit.eval, wiresMake]
    change (_ ++ [_]).getD (26 + C.size) false = _
    rw [← len C x]
    simp [List.getD_eq_getElem?_getD]

  have legal (C : Circuit) (a b : ℕ) (h : PEqualNP.TopForm.IsAO2 26 C)
      (ha : a < 26 + C.size) (hb : b < 26 + C.size) :
      PEqualNP.TopForm.IsAO2 26 (make C a b) := by
    obtain ⟨ho, hr, hn⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [make, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact ho g hg
      · exact Or.inl rfl
    · intro j hj i hi
      by_cases hlt : j < C.gates.length
      · apply hr j hlt i
        simpa only [gateAt, make, List.getD_append _ _ _ _ hlt] using hi
      · have heq : j = C.gates.length := by
          simp [make] at hj
          omega
        subst j
        simp [gateAt, make, List.getD_eq_getElem?_getD] at hi
        rcases hi with rfl | rfl
        · exact ha
        · exact hb
    · intro g hg
      simp only [make, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hn g hg
      · rfl
  obtain ⟨C, a, b, hs, hlegal, hnd, hab, ha, hb, hcold, hpos, hneg⟩ := candidate
  change cold C a b at hcold
  change (∀ p l : Fin 13, incident p l →
    pairValue C a b (fun k => Fin.addCases (fun i => decide (i = p)) (fun i => decide (i = l)) k) = true) at hpos
  change (∀ p : Fin 13 → Bool, pairValue C a b (fun k => Fin.addCases p (clearLines p) k) = false) at hneg
  let D := make C a b
  have hd := legal C a b hlegal ha hb
  refine ⟨D, ?_, hd, ?_, ?_, C.size, a, b, rfl, ?_, ?_⟩
  · change (C.gates ++ [_]).length ≤ 64
    simpa [Circuit.size] using Nat.succ_le_succ hs
  · intro g hg
    simp only [D, make, List.mem_append, List.mem_singleton] at hg
    rcases hg with h | rfl
    · exact hnd g h
    · simpa using hab
  · intro p l
    constructor
    · intro htrue
      by_contra! hnone
      have hle : ∀ i : Fin 13, l i = true → clearLines p i = true := by
        intro i hi
        simpa [clearLines] using hnone i hi
      have hmono : ∀ i : Fin 26, Fin.addCases p l i = true →
          Fin.addCases p (clearLines p) i = true := by
        intro j
        refine @Fin.addCases 13 13
          (fun k => Fin.addCases p l k = true → Fin.addCases p (clearLines p) k = true) ?_ ?_ j
        · intro i
          simp
        · intro i
          simpa only [Fin.addCases_right] using hle i
      have ht := monotone D hd.1 _ _ hmono htrue
      rw [evalMake, hneg p] at ht
      contradiction
    · rintro ⟨j, hj, hp⟩
      have hex : ∃ i : Fin 13, incident i j ∧ p i = true := by
        simp only [Bool.or_eq_true] at hp
        rcases hp with ((h | h) | h) | h
        · exact ⟨j, Or.inl rfl, h⟩
        · exact ⟨j + 1, Or.inr (Or.inl rfl), h⟩
        · exact ⟨j + 3, Or.inr (Or.inr (Or.inl rfl)), h⟩
        · exact ⟨j + 9, Or.inr (Or.inr (Or.inr rfl)), h⟩
      obtain ⟨i, hij, hi⟩ := hex
      have hmono : ∀ k : Fin 26,
          Fin.addCases (fun q : Fin 13 => decide (q = i)) (fun q : Fin 13 => decide (q = j)) k = true →
          Fin.addCases p l k = true := by
        intro k
        refine @Fin.addCases 13 13 (fun t =>
          Fin.addCases (fun q : Fin 13 => decide (q = i)) (fun q : Fin 13 => decide (q = j)) t = true →
            Fin.addCases p l t = true) ?_ ?_ k
        · intro q
          simpa using (fun e : q = i => e.symm ▸ hi)
        · intro q
          simpa only [Fin.addCases_right, decide_eq_true_eq] using
            (fun e : q = j => e.symm ▸ hj)
      apply monotone D hd.1 _ _ hmono
      exact (evalMake C a b _).trans (hpos i j hij)
  · change (C.gates ++ [_])[C.gates.length]? = _
    simp
  · intro s
    let x : Fin 26 → Bool := fun i => decide (i.val = if s = true then 13 else 0)
    change (D.wires (List.ofFn x)).getD a false = false ∧
      (D.wires (List.ofFn x)).getD b false = false
    rw [wiresMake, List.getD_append _ _ _ _ (by rwa [len]),
      List.getD_append _ _ _ _ (by rwa [len])]
    exact hcold s
