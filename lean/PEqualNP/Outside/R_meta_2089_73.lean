import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2089_73
    (hinputs : have D : Finset (Fin 13) := {0, 1, 3, 9}; ∀ i : Fin 26, ∃ p l : Fin 13, (∃ d ∈ D, p = l + d) ∧ i ≠ Fin.castAdd 13 p ∧ i ≠ Fin.natAdd 13 l)
    (hfinal : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 62 → ∀ a : Fin (26 + C.size), 26 ≤ a.val → a.val < 25 + C.size → (∀ p l : Fin 13, x2 p l → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 C a.val (x4 p l), x6 C (25 + C.size) (x4 p l)] = true) → (∀ A : Finset (Fin 13), (∀ p ∉ A, ∃ l : Fin 13, x3 A l ∧ x2 p l) → ((∃ l : Fin 13, ∀ p ∈ A, x2 p l) ∨ ∃ p : Fin 13, ∀ l : Fin 13, x3 A l → x2 p l) → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 C a.val (x5 A), x6 C (25 + C.size) (x5 A)] = false) → False) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (62 : ℕ) → ∀ (x10 x11 : Fin ((26 : ℕ) + x7.size)), x10 ≠ x11 → (∀ (x13 x14 : Fin (13 : ℕ)), x2 x13 x14 → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x4 x13 x14), x6 x7 (↑x11) (x4 x13 x14)] = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), (∀ x15 ∉ x14, ∃ (x17 : Fin (13 : ℕ)), x3 x14 x17 ∧ x2 x15 x17) → ((∃ (x16 : Fin (13 : ℕ)), ∀ x17 ∈ x14, x2 x17 x16) ∨ ∃ (x16 : Fin (13 : ℕ)), ∀ (x17 : Fin (13 : ℕ)), x3 x14 x17 → x2 x16 x17) → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x5 x14), x6 x7 (↑x11) (x5 x14)] = Bool.false) → False := by
  intro D I N pos neg V C hmono hsize a b hab hacc hrej
  let runW : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have snoc : ∀ gs g x, runW (gs ++ [g]) x =
      runW gs x ++ [g.op.eval (g.inputs.map fun i => (runW gs x).getD i false)] := by
    intro gs g x
    simp [runW]
  have lengthRun : ∀ gs x, (runW gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [runW]
    | append_singleton gs g ih =>
      rw [snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
      omega
  have prefixGet : ∀ g1 g2 x i, i < x.length + g1.length →
      (runW (g1 ++ g2) x).getD i false = (runW g1 x).getD i false := by
    intro g1 g2 x i hi
    induction g2 using List.reverseRecOn with
    | nil => simp
    | append_singleton g2 g ih =>
      rw [← List.append_assoc, snoc, List.getD_eq_getElem?_getD, List.getElem?_append_left]
      · rw [← List.getD_eq_getElem?_getD]
        exact ih
      · rw [lengthRun, List.length_append]
        omega
  have inputVal : ∀ (K : PEqualNP.CircuitLowerBounds.Circuit) (i : ℕ) (hi : i < 26)
      (z : Fin 26 → Bool), V K i z = z ⟨i, hi⟩ := by
    intro K i hi z
    change (runW K.gates (List.ofFn z)).getD i false = _
    rw [show K.gates = [] ++ K.gates from rfl, prefixGet [] K.gates (List.ofFn z) i (by simpa using hi)]
    simp only [runW, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      hi, ↓reduceDIte, Option.getD_some]
  have outputGe : ∀ i : Fin (26 + C.size),
      (∀ p l : Fin 13, I p l → V C i.val (pos p l) = true) → 26 ≤ i.val := by
    intro i accepts
    by_contra notGe
    have hi : i.val < 26 := by omega
    obtain ⟨p, l, incidence, hp, hl⟩ := hinputs ⟨i.val, hi⟩
    have one := accepts p l incidence
    rw [inputVal C i.val hi] at one
    have zero : pos p l ⟨i.val, hi⟩ = false := by
      simp only [pos, decide_eq_false_iff_not, not_or]
      exact ⟨hp, hl⟩
    rw [zero] at one
    cases one
  have geA : 26 ≤ a.val := by
    apply outputGe a
    intro p l incidence
    have hh := hacc p l incidence
    change (V C a.val (pos p l) && (V C b.val (pos p l) && true)) = true at hh
    simp only [Bool.and_eq_true] at hh
    exact hh.1
  have geB : 26 ≤ b.val := by
    apply outputGe b
    intro p l incidence
    have hh := hacc p l incidence
    change (V C a.val (pos p l) && (V C b.val (pos p l) && true)) = true at hh
    simp only [Bool.and_eq_true] at hh
    exact hh.2.1
  have ordered : ∀ (a b : Fin (26 + C.size)), 26 ≤ a.val → 26 ≤ b.val → a.val < b.val →
      (∀ p l : Fin 13, I p l → PEqualNP.CircuitLowerBounds.GateOp.and.eval
        [V C a.val (pos p l), V C b.val (pos p l)] = true) →
      (∀ A : Finset (Fin 13), (∀ p ∉ A, ∃ l : Fin 13, N A l ∧ I p l) →
        ((∃ l : Fin 13, ∀ p ∈ A, I p l) ∨ ∃ p : Fin 13, ∀ l : Fin 13, N A l → I p l) →
        PEqualNP.CircuitLowerBounds.GateOp.and.eval [V C a.val (neg A), V C b.val (neg A)] = false) → False := by
    intro a b ga gb ab accept reject
    let m : ℕ := b.val + 1 - 26
    have hm : m ≤ C.gates.length := by
      have hb := b.isLt
      change b.val < 26 + C.gates.length at hb
      omega
    have hmSize : m ≤ C.size := hm
    let K : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.take m, C.output⟩
    have ksize : K.size = m := by
      change (C.gates.take m).length = m
      exact List.length_take_of_le hm
    have km : PEqualNP.MetaComplexity.Monotone2 K := by
      intro g hg
      exact hmono g (List.mem_of_mem_take hg)
    have stable : ∀ i : ℕ, i < 26 + m → ∀ z : Fin 26 → Bool, V K i z = V C i z := by
      intro i hi z
      change (runW (C.gates.take m) (List.ofFn z)).getD i false =
        (runW C.gates (List.ofFn z)).getD i false
      have hh := prefixGet (C.gates.take m) (C.gates.drop m) (List.ofFn z) i (by
        rw [List.length_ofFn, List.length_take_of_le hm]
        exact hi)
      rw [List.take_append_drop] at hh
      exact hh.symm
    have last : 25 + K.size = b.val := by omega
    have avalid : a.val < 26 + K.size := by omega
    apply hfinal K km (by omega) ⟨a.val, avalid⟩ ga
      (by change a.val < 25 + K.size; omega)
    · intro p l incidence
      change PEqualNP.CircuitLowerBounds.GateOp.and.eval
        [V K a.val (pos p l), V K (25 + K.size) (pos p l)] = true
      rw [last, stable a.val (by omega), stable b.val (by omega)]
      exact accept p l incidence
    · intro A closed degenerate
      change PEqualNP.CircuitLowerBounds.GateOp.and.eval
        [V K a.val (neg A), V K (25 + K.size) (neg A)] = false
      rw [last, stable a.val (by omega), stable b.val (by omega)]
      exact reject A closed degenerate
  have evalComm (x y : Bool) :
      PEqualNP.CircuitLowerBounds.GateOp.and.eval [x, y] =
        PEqualNP.CircuitLowerBounds.GateOp.and.eval [y, x] := by
    cases x <;> cases y <;> rfl
  by_cases ab : a.val < b.val
  · exact ordered a b geA geB ab hacc hrej
  · have ba : b.val < a.val := by
      have ne : a.val ≠ b.val := fun h => hab (Fin.ext h)
      omega
    apply ordered b a geB geA ba
    · intro p l incidence
      rw [evalComm]
      exact hacc p l incidence
    · intro A closed degenerate
      rw [evalComm]
      exact hrej A closed degenerate
