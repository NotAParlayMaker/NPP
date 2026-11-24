import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3975_627 :
    (have mark : Gate → Bool := fun g => g.inputs.contains 0 || g.inputs.contains 9
     have absorb : Gate → Prop := fun g => (g.op = .and ∧ 0 ∈ g.inputs) ∨ (g.op = .or ∧ 9 ∈ g.inputs)
     have lo : (Fin 8 → Bool) → Bool := fun y => [(1 : ℕ),10,19,5,14,23,38,47,60].any fun k => y (Fin.ofNat 8 (k / 8)) && y (Fin.ofNat 8 (k % 8))
     have hi : (Fin 8 → Bool) → Bool := fun y => y 0 || y 3 || y 4 || y 1 && y 2 || y 1 && y 6 || y 2 && y 7 || y 5 && y 7
     ∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
       (∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) →
       (C.gates.filter mark).length ≤ 2 →
       (¬ ∃ p g t, C.gates = p ++ g :: t ∧ absorb g ∧
         ∃ h ∈ t, mark h = false ∧ 10 + p.length ∈ h.inputs) →
       (∀ y, C.eval (false :: List.ofFn y ++ [true]) = lo y) →
       (∀ y, C.eval (true :: List.ofFn y ++ [false]) = hi y) →
       ∀ g ∈ C.gates, ¬ absorb g) →
    (have mark : Gate → Bool := fun g => g.inputs.contains 0 || g.inputs.contains 9
     have absorb : Gate → Prop := fun g => (g.op = .and ∧ 0 ∈ g.inputs) ∨ (g.op = .or ∧ 9 ∈ g.inputs)
     have lo : (Fin 8 → Bool) → Bool := fun y => [(1 : ℕ),10,19,5,14,23,38,47,60].any fun k => y (Fin.ofNat 8 (k / 8)) && y (Fin.ofNat 8 (k % 8))
     have hi : (Fin 8 → Bool) → Bool := fun y => y 0 || y 3 || y 4 || y 1 && y 2 || y 1 && y 6 || y 2 && y 7 || y 5 && y 7
     ∀ C : Circuit, FanInTwo C → C.size = 14 → C.output < 24 →
       (∀ g ∈ C.gates, (g.op = .not → g.inputs.length ≤ 1) ∧ ∀ w ∈ g.inputs, w ≤ 24) →
       (C.gates.filter mark).length = 2 →
       (C.gates.filter fun g => !mark g && g.inputs.contains 4).length ≤ 1 →
       (∀ g ∈ C.gates, ¬ absorb g) →
       (∀ y, C.eval (false :: List.ofFn y ++ [true]) = lo y) →
       ∃ y, C.eval (true :: List.ofFn y ++ [false]) ≠ hi y) →
    (∀ (x1 x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → x1.length + x2.length + x3.length = (12 : ℕ) → x6 < (24 : ℕ) → (∀ x11 ∈ x7.gates, (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not → x11.inputs.length ≤ (1 : ℕ)) ∧ ∀ x13 ∈ x11.inputs, x13 ≤ (24 : ℕ)) → (∀ x12 ∈ x1 ++ x2 ++ x3, (0 : ℕ) ∉ x12.inputs ∧ (9 : ℕ) ∉ x12.inputs) → (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.inputs.contains (4 : ℕ)) (x1 ++ x2 ++ x3)).length ≤ (1 : ℕ) → (∀ x14 ∈ [x4, x5], (0 : ℕ) ∈ x14.inputs ∨ (9 : ℕ) ∈ x14.inputs) → (¬∃ (x15 : List PEqualNP.CircuitLowerBounds.Gate) (x16 : PEqualNP.CircuitLowerBounds.Gate) (x17 : List PEqualNP.CircuitLowerBounds.Gate), x7.gates = x15 ++ x16 :: x17 ∧ (x16.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x16.inputs ∨ x16.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x16.inputs) ∧ ∃ x18 ∈ x17, (0 : ℕ) ∉ x18.inputs ∧ (9 : ℕ) ∉ x18.inputs ∧ (10 : ℕ) + x15.length ∈ x18.inputs) → (∀ (x16 : Fin (8 : ℕ) → Bool), x7.eval (Bool.false :: List.ofFn x16 ++ [Bool.true]) = [(1 : ℕ), (10 : ℕ), (19 : ℕ), (5 : ℕ), (14 : ℕ), (23 : ℕ), (38 : ℕ), (47 : ℕ), (60 : ℕ)].any fun (x17 : ℕ) => x16 (Fin.ofNat (8 : ℕ) (x17 / (8 : ℕ))) && x16 (Fin.ofNat (8 : ℕ) (x17 % (8 : ℕ)))) → ∃ (x17 : Fin (8 : ℕ) → Bool), x7.eval (Bool.true :: List.ofFn x17 ++ [Bool.false]) ≠ (x17 (0 : Fin (8 : ℕ)) || x17 (3 : Fin (8 : ℕ)) || x17 (4 : Fin (8 : ℕ)) || x17 (1 : Fin (8 : ℕ)) && x17 (2 : Fin (8 : ℕ)) || x17 (1 : Fin (8 : ℕ)) && x17 (6 : Fin (8 : ℕ)) || x17 (2 : Fin (8 : ℕ)) && x17 (7 : Fin (8 : ℕ)) || x17 (5 : Fin (8 : ℕ)) && x17 (7 : Fin (8 : ℕ)))) := by
  intro absent residual a b c first second out C fan count outputBound valid ordinary cap marked escape lo
  by_contra! hi
  let mark (g : Gate) := g.inputs.contains 0 || g.inputs.contains 9
  let ordinaryFour (g : Gate) := !mark g && g.inputs.contains 4
  have markedIff (g : Gate) : mark g = true ↔ 0 ∈ g.inputs ∨ 9 ∈ g.inputs := by simp [mark]
  have ordinaryFalse (g : Gate) (hg : g ∈ a ++ b ++ c) : mark g = false := by
    apply Bool.eq_false_iff.mpr
    intro hm
    exact (markedIff g).mp hm |>.elim (ordinary g hg).1 (ordinary g hg).2
  have markedFirst : mark first = true := markedIff first |>.mpr (marked first (by simp))
  have markedSecond : mark second = true := markedIff second |>.mpr (marked second (by simp))
  have zeros (xs : List Gate) (subset : ∀ g ∈ xs, g ∈ a ++ b ++ c) : xs.filter mark = [] :=
    List.filter_eq_nil_iff.mpr fun g hg => by simp [ordinaryFalse g (subset g hg)]
  have za := zeros a (by intro g hg; simp [List.mem_append,hg])
  have zb := zeros b (by intro g hg; simp [List.mem_append,hg])
  have zc := zeros c (by intro g hg; simp [List.mem_append,hg])
  have two : (C.gates.filter mark).length = 2 := by
    simp [C,za,zb,zc,markedFirst,markedSecond]
  have readFilter (xs : List Gate) (subset : ∀ g ∈ xs, g ∈ a ++ b ++ c) :
      xs.filter ordinaryFour = xs.filter (fun g => g.inputs.contains 4) := by
    apply List.filter_congr
    intro g hg
    simp [ordinaryFour,ordinaryFalse g (subset g hg)]
  have ca := readFilter a (by intro g hg; simp [List.mem_append,hg])
  have cb := readFilter b (by intro g hg; simp [List.mem_append,hg])
  have cc := readFilter c (by intro g hg; simp [List.mem_append,hg])
  have skipFirst : ordinaryFour first = false := by simp [ordinaryFour,markedFirst]
  have skipSecond : ordinaryFour second = false := by simp [ordinaryFour,markedSecond]
  have one : (C.gates.filter ordinaryFour).length ≤ 1 := by
    simpa [C, ca, cb, cc, skipFirst, skipSecond, List.append_assoc] using cap
  have size : C.size = 14 := by
    change (a ++ first :: (b ++ second :: c)).length = 14
    simp only [List.length_append, List.length_cons]
    omega
  have noEscape : ¬ ∃ (p : List Gate) (g : Gate) (t : List Gate), C.gates = p ++ g :: t ∧
      ((g.op = .and ∧ 0 ∈ g.inputs) ∨ (g.op = .or ∧ 9 ∈ g.inputs)) ∧
      ∃ h ∈ t, mark h = false ∧ 10 + p.length ∈ h.inputs := by
    rintro ⟨p,g,t,same,absorb,h,ht,hm,reader⟩
    have missing : ¬ (0 ∈ h.inputs ∨ 9 ∈ h.inputs) := by
      intro present
      have yes := (markedIff h).mpr present
      simp [hm] at yes
    exact escape ⟨p,g,t,same,absorb,h,ht,fun h0 => missing (Or.inl h0),fun h9 => missing (Or.inr h9),reader⟩
  have noAbsorber := absent C fan (le_of_eq size) (fun g hg => (valid g hg).1)
    (by rw [two]) noEscape lo hi
  obtain ⟨y,fail⟩ := residual C fan size outputBound valid two one noAbsorber lo
  exact fail (hi y)
