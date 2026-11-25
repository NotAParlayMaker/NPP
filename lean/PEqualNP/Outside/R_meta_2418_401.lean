import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.TopForm PEqualNP.FactorSubst PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_2418_401
    (deg2Exact :
      let S : Fin 13 → Finset (Fin 13) := fun l => {l, l + 1, l + 3, l + 9}
      ∀ C : Circuit, IsAO2 26 C → C.size ≤ 63 → C.output + 1 = 26 + C.size →
        liveSize 26 C = C.size →
        (∀ j < C.size, opnd C j 0 < opnd C j 1) →
        C.lineDeg 26 (Finset.Ico 13 26) = 2 →
        2 ≤ C.lineDeg 26 (Finset.range 13) →
        ComputesIncidence S C →
        (∀ D : Circuit, Monotone2 D → ComputesIncidence S D → C.size ≤ D.size) →
        False)
    (deg3Exact :
      let S : Fin 13 → Finset (Fin 13) := fun l => {l, l + 1, l + 3, l + 9}
      ∀ C : Circuit, IsAO2 26 C → C.size ≤ 63 → C.output + 1 = 26 + C.size →
        liveSize 26 C = C.size →
        (∀ j < C.size, opnd C j 0 < opnd C j 1) →
        3 ≤ C.lineDeg 26 (Finset.Ico 13 26) →
        C.lineDeg 26 (Finset.Ico 13 26) ≤ C.lineDeg 26 (Finset.range 13) →
        ComputesIncidence S C →
        (∀ D : Circuit, Monotone2 D → ComputesIncidence S D → C.size ≤ D.size) →
        False)
    (deg3Generic :
      let S : Fin 13 → Finset (Fin 13) := fun l => {l, l + 1, l + 3, l + 9}
      let degSep := fun C : Circuit =>
        RightOnIncidentPairs S C ∧
        ∀ X Y : Finset (Fin 13), IsMaximalFalse S X Y →
          (¬ InNoLine S X ∨ ¬ InNoPencil S Y) →
          C.eval (incidenceInput X Y) = false
      ∀ C : Circuit, IsAO2 26 C → C.size ≤ 63 → C.output + 1 = 26 + C.size →
        liveSize 26 C = C.size →
        (∀ j < C.size, opnd C j 0 < opnd C j 1) →
        3 ≤ C.lineDeg 26 (Finset.Ico 13 26) →
        3 ≤ C.lineDeg 26 (Finset.range 13) →
        degSep C →
        (∀ D : Circuit, Monotone2 D → degSep D → C.size ≤ D.size) →
        C.eval (incidenceInput ({0, 1, 2} : Finset (Fin 13)) ({3, 7, 8, 9} : Finset (Fin 13))) = true →
        False) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false; have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ (63 : ℕ) → x4 x6 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x6.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x10 (1 : ℕ) ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), x5 x11 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x10 x11 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 x11 := by
  let S : Fin 13 → Finset (Fin 13) := fun l => {l, l + 1, l + 3, l + 9}
  let incb (p w : Fin 13) : Bool := decide (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9)
  have hincb : ∀ p w : Fin 13, p ∈ S w ↔ incb p w = true := by
    intro p w; simp [S, incb]
  let degSep : Circuit → Prop := fun C =>
    RightOnIncidentPairs S C ∧
    ∀ X Y : Finset (Fin 13), IsMaximalFalse S X Y →
      (¬ InNoLine S X ∨ ¬ InNoPencil S Y) →
      C.eval (incidenceInput X Y) = false
  have hGateOp_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have hGateOp_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have hCircuit_size : ∀ C : Circuit, C.size = C.gates.length := fun _ => rfl
  have hzeroSet_def : ∀ Y : Finset (Fin 13),
      zeroSet S Y = Finset.univ.filter (fun p => ∀ l ∈ Y, p ∉ S l) := fun _ => rfl
  have hincIn_def : ∀ X Y : Finset (Fin 13),
      incidenceInput X Y = List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++
        List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) := fun _ _ => rfl
  have hconeStep_def : ∀ (cs : List (List ℕ)) (g : Gate),
      coneStep 26 cs g = cs ++ [(g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
        (fun w => (w - 26) :: cs.getD (w - 26) [])] := fun _ _ => rfl
  have hcones_def : ∀ C : Circuit, cones 26 C = C.gates.foldl (coneStep 26) [] := fun _ => rfl
  have hInCone_def : ∀ (C : Circuit) (i j : ℕ),
      InCone 26 C i j = (i ∈ (cones 26 C).getD j []) := fun _ _ _ => rfl
  have hliveGates_def : ∀ C : Circuit,
      liveGates 26 C = (Finset.range C.gates.length).filter (fun j =>
        26 ≤ C.output ∧ (j = C.output - 26 ∨ InCone 26 C j (C.output - 26))) := fun _ => rfl
  have hliveSize_def : ∀ C : Circuit, liveSize 26 C = (liveGates 26 C).card := fun _ => rfl
  have hS_shift : ∀ p w c : Fin 13, incb (p + c) (w + c) = incb p w := by
    intro p w c
    simp only [incb]
    apply decide_eq_decide.mpr
    constructor <;> rintro (h | h | h | h)
    · left; exact add_right_cancel h
    · right; left; exact add_right_cancel (h.trans (by abel))
    · right; right; left; exact add_right_cancel (h.trans (by abel))
    · right; right; right; exact add_right_cancel (h.trans (by abel))
    · left; rw [h]
    · right; left; rw [h]; abel
    · right; right; left; rw [h]; abel
    · right; right; right; rw [h]; abel
  have hS_dual_0 : ∀ d : Fin 13, incb d 0 = incb 0 (-d) := by decide
  have hS_dual_b : ∀ p w : Fin 13, incb p w = incb (-w) (-p) := by
    intro p w
    have h1 := hS_shift p w (-w)
    have h2 := hS_shift 0 (-(p + -w)) (-w)
    rw [add_neg_cancel] at h1
    have e1 : (0 : Fin 13) + -w = -w := by abel
    have e2 : -(p + -w) + -w = -p := by abel
    rw [e1, e2] at h2
    rw [← h1, hS_dual_0 (p + -w), h2]
  have hS_twoPts_0 : ∀ d : Fin 13, ∃ w : Fin 13, incb 0 w = true ∧ incb d w = true := by decide
  have hS_twoPts_b : ∀ p q : Fin 13, ∃ w : Fin 13, incb p w = true ∧ incb q w = true := by
    intro p q
    obtain ⟨w, h1, h2⟩ := hS_twoPts_0 (q + -p)
    refine ⟨w + p, ?_, ?_⟩
    · simpa [zero_add] using (hS_shift 0 w p).trans h1
    · have := (hS_shift (q + -p) w p).trans h2
      simpa [add_assoc, neg_add_cancel, add_zero] using this
  have hS_twoLns_b : ∀ u v : Fin 13, ∃ p : Fin 13, incb p u = true ∧ incb p v = true := by
    intro u v
    obtain ⟨w, h1, h2⟩ := hS_twoPts_b (-u) (-v)
    refine ⟨-w, ?_, ?_⟩
    · rw [hS_dual_b (-w) u, neg_neg]; exact h1
    · rw [hS_dual_b (-w) v, neg_neg]; exact h2
  have hS_cnt1 : ∀ w : Fin 13, w ≠ 0 →
      ([0, 1, 3, 9] : List (Fin 13)).countP (fun p => incb p w) ≤ 1 := by decide
  have hS_cover2_b : ∀ w1 w2 w3 : Fin 13,
      w3 ≠ w1 → w3 ≠ w2 → ∃ p : Fin 13, incb p w3 = true ∧ incb p w1 = false ∧ incb p w2 = false := by
    intro w1 w2 w3 hne1 hne2
    let u1 := w1 + -w3
    let u2 := w2 + -w3
    have hu1 : u1 ≠ 0 := fun h => hne1 (by
      have := congrArg (· + w3) h
      simpa [u1, add_assoc, neg_add_cancel, add_zero] using this.symm)
    have hu2 : u2 ≠ 0 := fun h => hne2 (by
      have := congrArg (· + w3) h
      simpa [u2, add_assoc, neg_add_cancel, add_zero] using this.symm)
    have hc1 := hS_cnt1 u1 hu1
    have hc2 := hS_cnt1 u2 hu2
    have hsum : ∀ (l : List (Fin 13)) (f g : Fin 13 → Bool),
        l.countP (fun x => f x || g x) ≤ l.countP f + l.countP g := by
      intro l f g
      induction l with
      | nil => simp
      | cons a t ih =>
        simp only [List.countP_cons]
        cases f a <;> cases g a <;> simp <;> omega
    have hlt : ([0, 1, 3, 9] : List (Fin 13)).countP (fun p => incb p u1 || incb p u2) <
        ([0, 1, 3, 9] : List (Fin 13)).length := by
      have hs := hsum [0, 1, 3, 9] (fun p => incb p u1) (fun p => incb p u2)
      simp only [List.length_cons, List.length_nil]
      omega
    have hex : ∃ p ∈ ([0, 1, 3, 9] : List (Fin 13)), (incb p u1 || incb p u2) = false := by
      by_contra hno
      have hall : ∀ p ∈ ([0, 1, 3, 9] : List (Fin 13)), (incb p u1 || incb p u2) = true := by
        intro p hp
        cases h : (incb p u1 || incb p u2)
        · exact False.elim (hno ⟨p, hp, h⟩)
        · rfl
      rw [List.countP_eq_length.mpr hall] at hlt
      exact Nat.lt_irrefl _ hlt
    obtain ⟨p, hp, hfalse⟩ := hex
    have hp1 : incb p u1 = false := (Bool.or_eq_false_iff.mp hfalse).1
    have hp2 : incb p u2 = false := (Bool.or_eq_false_iff.mp hfalse).2
    have hp0 : incb p 0 = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    refine ⟨p + w3, ?_, ?_, ?_⟩
    · have := hS_shift p 0 w3; simpa [zero_add] using this.trans hp0
    · have := hS_shift p u1 w3
      have eu : u1 + w3 = w1 := by dsimp only [u1]; abel
      rw [eu] at this; exact this.trans hp1
    · have := hS_shift p u2 w3
      have eu : u2 + w3 = w2 := by dsimp only [u2]; abel
      rw [eu] at this; exact this.trans hp2
  have hS_pt_sep_0 : ∀ d : Fin 13, d ≠ 0 → ∃ w : Fin 13, incb 0 w = false ∧ incb d w = true := by
    decide
  have hS_pt_sep_b : ∀ p q : Fin 13, p ≠ q → ∃ w : Fin 13, incb p w = false ∧ incb q w = true := by
    intro p q hne
    have hd : q + -p ≠ 0 := fun h => hne (by
      have := congrArg (· + p) h
      simpa [add_assoc, neg_add_cancel, add_zero] using this.symm)
    obtain ⟨w, h1, h2⟩ := hS_pt_sep_0 (q + -p) hd
    refine ⟨w + p, ?_, ?_⟩
    · simpa [zero_add] using (hS_shift 0 w p).trans h1
    · have := (hS_shift (q + -p) w p).trans h2
      simpa [add_assoc, neg_add_cancel, add_zero] using this
  have htri0_miss_b : ∀ w : Fin 13,
      (incb 0 w = false ∧ incb 1 w = false ∧ incb 2 w = false) ↔
        (w = 3 ∨ w = 7 ∨ w = 8 ∨ w = 9) := by decide
  have htri0_hit_b : ∀ p : Fin 13, p ≠ 0 → p ≠ 1 → p ≠ 2 →
      incb p 3 = true ∨ incb p 7 = true ∨ incb p 8 = true ∨ incb p 9 = true := by decide
  let vs : Fin 13 → ZMod 3 × ZMod 3 × ZMod 3 := fun p =>
    ([(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (0, 1, 1), (1, 1, 1), (1, 2, 1),
      (1, 2, 2), (2, 0, 2), (2, 1, 0), (0, 2, 1), (1, 1, 2), (2, 0, 1)] :
        List (ZMod 3 × ZMod 3 × ZMod 3)).getD p.val (0, 0, 0)
  let us : Fin 13 → ZMod 3 × ZMod 3 × ZMod 3 := fun w =>
    ([(0, 0, 1), (1, 0, 0), (2, 1, 0), (1, 2, 1), (0, 2, 1), (2, 0, 1), (1, 1, 0),
      (1, 2, 2), (1, 1, 2), (1, 1, 1), (0, 1, 1), (2, 0, 2), (0, 1, 0)] :
        List (ZMod 3 × ZMod 3 × ZMod 3)).getD w.val (0, 0, 0)
  let dot3 (a b : ZMod 3 × ZMod 3 × ZMod 3) : ZMod 3 :=
    a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2
  let cross3 (a b : ZMod 3 × ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 × ZMod 3 :=
    (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)
  let smul3 (c : ZMod 3) (a : ZMod 3 × ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 × ZMod 3 :=
    (c * a.1, c * a.2.1, c * a.2.2)
  have hz3_sq : ∀ c : ZMod 3, c ≠ 0 → c * c = 1 := by decide
  have hdot_inc_b : ∀ p w : Fin 13, incb p w = decide (dot3 (us w) (vs p) = 0) := by decide
  have hvs_surj : ∀ a b c : ZMod 3, (a, b, c) ≠ (0, 0, 0) →
      ∃ p : Fin 13, ∃ k : ZMod 3, k ≠ 0 ∧ (a, b, c) = smul3 k (vs p) := by decide
  have hus_surj : ∀ a b c : ZMod 3, (a, b, c) ≠ (0, 0, 0) →
      ∃ w : Fin 13, ∃ k : ZMod 3, k ≠ 0 ∧ (a, b, c) = smul3 k (us w) := by decide
  have hvs_inj : ∀ p q : Fin 13, ∀ k : ZMod 3, k ≠ 0 → vs p = smul3 k (vs q) → p = q := by decide
  have hus_inj : ∀ u v : Fin 13, ∀ k : ZMod 3, k ≠ 0 → us u = smul3 k (us v) → u = v := by decide
  have hvs_cross0 : ∀ p q : Fin 13, cross3 (vs p) (vs q) = (0, 0, 0) → p = q := by decide
  have hvs_ne0 : ∀ p : Fin 13, vs p ≠ (0, 0, 0) := by decide
  have hus_ne0 : ∀ w : Fin 13, us w ≠ (0, 0, 0) := by decide
  classical
  have hS_dual : ∀ p w : Fin 13, p ∈ S w ↔ -w ∈ S (-p) := by
    intro p w; rw [hincb, hincb, hS_dual_b]
  have hS_twoPts : ∀ p q : Fin 13, ∃ w : Fin 13, p ∈ S w ∧ q ∈ S w := by
    intro p q; obtain ⟨w, h1, h2⟩ := hS_twoPts_b p q
    exact ⟨w, (hincb _ _).mpr h1, (hincb _ _).mpr h2⟩
  have hS_twoLns : ∀ u v : Fin 13, ∃ p : Fin 13, p ∈ S u ∧ p ∈ S v := by
    intro u v; obtain ⟨p, h1, h2⟩ := hS_twoLns_b u v
    exact ⟨p, (hincb _ _).mpr h1, (hincb _ _).mpr h2⟩
  have hdeg_univ : IsMaximalFalse S Finset.univ ∅ ∧ ¬ InNoPencil S ∅ := by
    refine ⟨⟨fun l hl => by simp at hl, fun p hp => by simp at hp, fun l _ hf => ?_⟩, ?_⟩
    · exact Finset.disjoint_left.mp (hf l (Finset.mem_insert_self l ∅)) (by simp [S]) (Finset.mem_univ l)
    · intro h; exact h 0 fun l hl => by simp at hl
  have hdeg_empty : IsMaximalFalse S ∅ Finset.univ ∧ ¬ InNoLine S ∅ := by
    refine ⟨⟨fun l _ => by simp, fun p _ hf => ?_, fun l hl => by simp at hl⟩, ?_⟩
    · exact Finset.disjoint_left.mp (hf p (Finset.mem_univ p)) (by simp [S]) (Finset.mem_insert_self p ∅)
    · intro h; exact h 0 (Finset.empty_subset _)
  have hdeg_twoLine : ∀ w1 w2 : Fin 13,
      IsMaximalFalse S (zeroSet S {w1, w2}) {w1, w2} ∧ ¬ InNoPencil S {w1, w2} := by
    intro w1 w2
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro l hl
      rw [Finset.disjoint_left]
      intro p hpS hpZ
      exact (Finset.mem_filter.mp hpZ).2 l hl hpS
    · intro p hpZ hf
      have hex : ∃ l ∈ ({w1, w2} : Finset (Fin 13)), p ∈ S l := by
        by_contra hno
        exact hpZ (Finset.mem_filter.mpr ⟨Finset.mem_univ p, fun l hl hmem => hno ⟨l, hl, hmem⟩⟩)
      obtain ⟨l, hl, hpl⟩ := hex
      exact Finset.disjoint_left.mp (hf l hl) hpl (Finset.mem_insert_self p _)
    · intro w3 hw3 hf
      have hne1 : w3 ≠ w1 := fun h => hw3 (by simp [h])
      have hne2 : w3 ≠ w2 := fun h => hw3 (by simp [h])
      obtain ⟨p, hp3, hp1, hp2⟩ := hS_cover2_b w1 w2 w3 hne1 hne2
      have hpZ : p ∈ zeroSet S {w1, w2} := by
        simp only [hzeroSet_def, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        rintro l (rfl | rfl) hmem
        · exact Bool.noConfusion (((hincb p l).mp hmem).symm.trans hp1)
        · exact Bool.noConfusion (((hincb p l).mp hmem).symm.trans hp2)
      exact Finset.disjoint_left.mp (hf w3 (Finset.mem_insert_self w3 _)) ((hincb p w3).mpr hp3) hpZ
    · intro hnp
      obtain ⟨p, hp1, hp2⟩ := hS_twoLns w1 w2
      apply hnp p
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl <;> assumption
  have hdeg_oneLine : ∀ w : Fin 13, IsMaximalFalse S (zeroSet S {w}) {w} ∧ ¬ InNoPencil S {w} := by
    intro w
    have h := hdeg_twoLine w w
    simpa only [Finset.pair_eq_singleton] using h
  have hdeg_onePt : ∀ p : Fin 13,
      IsMaximalFalse S {p} (Finset.univ.filter fun w => p ∉ S w) ∧ ¬ InNoLine S {p} := by
    intro p
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro l hl
      rw [Finset.disjoint_left]
      intro q hq hqp
      rw [Finset.mem_singleton.mp hqp] at hq
      exact (Finset.mem_filter.mp hl).2 hq
    · intro q hq hf
      have hne : p ≠ q := fun h => hq (by simp [h])
      obtain ⟨w, hpw, hqw⟩ := hS_pt_sep_b p q hne
      have hw : w ∈ Finset.univ.filter (fun w => p ∉ S w) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro hmem
        exact Bool.noConfusion (((hincb p w).mp hmem).symm.trans hpw)
      exact Finset.disjoint_left.mp (hf w hw) ((hincb q w).mpr hqw) (Finset.mem_insert_self q _)
    · intro w hw hf
      have hpw : p ∈ S w := by
        by_contra hnot
        exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hnot⟩)
      exact Finset.disjoint_left.mp (hf w (Finset.mem_insert_self w _)) hpw (Finset.mem_singleton_self p)
    · intro hnl
      exact hnl p (by intro q hq; rw [Finset.mem_singleton.mp hq]; simp [S])
  intro x1 x2 x3 x4 x5 C0 hmono0 hsize0 hgood0
  have hinc_iff : ∀ p w : Fin 13, x2 p w ↔ p ∈ S w := by
    intro p w
    change (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + d) ↔ p ∈ ({w, w + 1, w + 3, w + 9} : Finset (Fin 13))
    simp [add_zero]
  let stepW (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]
  let runW (gs : List Gate) (w : List Bool) : List Bool := gs.foldl stepW w
  have hrunW_len : ∀ (gs : List Gate) (w : List Bool), (runW gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [runW]
    | cons g gs ih =>
      intro w
      change (runW gs (stepW w g)).length = _
      rw [ih]
      simp [stepW]
      omega
  have hrunW_append : ∀ (gs1 gs2 : List Gate) (w : List Bool),
      runW (gs1 ++ gs2) w = runW gs2 (runW gs1 w) := fun gs1 gs2 w => List.foldl_append
  have hrunW_pref : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (runW gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      change (runW gs (stepW w g)).getD i false = _
      rw [ih (stepW w g) i (by simp [stepW]; omega)]
      exact List.getD_append _ _ _ _ hi
  have hsnoc_lt : ∀ {α : Type} (L : List α) (a d : α) (i : ℕ), i < L.length →
      (L ++ [a]).getD i d = L.getD i d := by
    intro α L a d i h
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  have hsnoc_eq : ∀ {α : Type} (L : List α) (a d : α), (L ++ [a]).getD L.length d = a := by
    intro α L a d
    simp [List.getD_eq_getElem?_getD]
  have hsnoc_gt : ∀ {α : Type} (L : List α) (a d : α) (i : ℕ), L.length < i →
      (L ++ [a]).getD i d = d := by
    intro α L a d i h
    rw [List.getD_eq_default]
    simp
    omega
  have hmono_wires : ∀ (C : Circuit), Monotone2 C →
      ∀ (x y : List Bool), x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ i, (C.wires x).getD i false = true → (C.wires y).getD i false = true := by
    intro C hm x y hlen hxy
    have hgen : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ (w1 w2 : List Bool), w1.length = w2.length →
        (∀ i, w1.getD i false = true → w2.getD i false = true) →
        ∀ i, (runW gs w1).getD i false = true → (runW gs w2).getD i false = true := by
      intro gs
      induction gs with
      | nil => intro _ w1 w2 _ h i hi; exact h i hi
      | cons g gs ih =>
        intro hgs w1 w2 hwl hw
        have hg := hgs g (by simp)
        apply ih (fun u hu => hgs u (by simp [hu])) (stepW w1 g) (stepW w2 g)
        · simp [stepW, hwl]
        · intro i hi
          rcases Nat.lt_trichotomy i w1.length with hlt | heq | hgt
          · rw [hsnoc_lt w1 _ false i hlt] at hi
            rw [hsnoc_lt w2 _ false i (by omega)]
            exact hw i hi
          · rw [heq, hsnoc_eq w1 _ false] at hi
            rw [heq, hwl, hsnoc_eq w2 _ false]
            rcases hg with hop | hop
            · rw [hop] at hi ⊢
              simp only [hGateOp_and, hGateOp_or, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
                and_imp, forall_apply_eq_imp_iff₂] at hi ⊢
              intro a ha
              exact hw a (hi a ha)
            · rw [hop] at hi ⊢
              simp only [hGateOp_and, hGateOp_or, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
              obtain ⟨_, ⟨a, ha, rfl⟩, ha1⟩ := hi
              exact ⟨true, ⟨a, ha, hw a ha1⟩, rfl⟩
          · rw [hsnoc_gt w1 _ false i hgt] at hi
            exact Bool.noConfusion hi
    exact hgen C.gates (fun g hg => by simpa using (hm g hg).1) x y hlen hxy
  have hmono_cfun : ∀ (C : Circuit), Monotone2 C →
      ∀ (x y : Fin 26 → Bool), (∀ k, x k = true → y k = true) →
      circuitFun 26 C x = true → circuitFun 26 C y = true := by
    intro C hm x y hxy hx
    apply hmono_wires C hm (List.ofFn x) (List.ofFn y) (by simp) _ C.output hx
    intro i hi
    by_cases hlt : i < 26
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true, Option.getD_some] at hi ⊢
      exact hxy ⟨i, hlt⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact Bool.noConfusion hi
  have hincIn : ∀ (X Y : Finset (Fin 13)),
      incidenceInput X Y = List.ofFn (fun k : Fin 26 =>
        decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨ (∃ w ∈ Y, k = Fin.natAdd 13 w))) := by
    intro X Y
    apply List.ext_getElem
    · simp [hincIn_def]
    · intro i h1 h2
      simp only [hincIn_def, List.getElem_ofFn]
      by_cases hi : i < 13
      · rw [List.getElem_append_left (by simp; exact hi), List.getElem_ofFn]
        apply decide_eq_decide.mpr
        constructor
        · intro hp
          exact Or.inl ⟨⟨i, hi⟩, hp, by apply Fin.ext; simp⟩
        · rintro (⟨p, hp, he⟩ | ⟨w, _, he⟩)
          · have hpi : (⟨i, hi⟩ : Fin 13) = p := Fin.ext (by
              have h' := congrArg Fin.val he; simpa using h')
            rwa [hpi]
          · have h' := congrArg Fin.val he; simp at h'; omega
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_ofFn, List.getElem_ofFn]
        apply decide_eq_decide.mpr
        constructor
        · intro hw
          exact Or.inr ⟨⟨i - 13, by simp at h2; omega⟩, hw, by apply Fin.ext; simp; omega⟩
        · rintro (⟨p, _, he⟩ | ⟨w, hw, he⟩)
          · have h' := congrArg Fin.val he; simp at h'; have := p.isLt; omega
          · have hwi : (⟨i - 13, by simp at h2; omega⟩ : Fin 13) = w := by
              have h' : i = 13 + w.val := by simpa only [Fin.val_natAdd] using congrArg Fin.val he
              exact Fin.ext (by dsimp only; omega)
            rwa [hwi]
  have hgood_iff : ∀ C : Circuit, x4 C ↔ degSep C := by
    intro C
    constructor
    · rintro ⟨hpos, hneg⟩
      refine ⟨?_, ?_⟩
      · intro w p hp
        rw [hincIn {p} {w}]
        have h1 := hpos p w ((hinc_iff p w).mpr hp)
        have hfn : (fun k : Fin 26 => decide ((∃ q ∈ ({p} : Finset (Fin 13)), k = Fin.castAdd 13 q) ∨
            (∃ u ∈ ({w} : Finset (Fin 13)), k = Fin.natAdd 13 u))) =
            (fun k : Fin 26 => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) := by
          funext k
          simp
        rw [hfn]
        exact h1
      · intro X Y hmf hdeg
        have hY : ∀ w : Fin 13, w ∈ Y ↔ x3 X w := by
          intro w
          constructor
          · intro hw p hp hinc
            have hdisj := hmf.1 w hw
            exact Finset.disjoint_left.mp hdisj ((hinc_iff p w).mp hinc) hp
          · intro hav
            by_contra hnot
            have h2 := hmf.2.2 w hnot
            apply h2
            intro u hu
            rw [Finset.mem_insert] at hu
            rcases hu with rfl | hu
            · rw [Finset.disjoint_left]
              intro p hp hpX
              exact hav p hpX ((hinc_iff p u).mpr hp)
            · exact hmf.1 u hu
        have hclosed : ∀ v ∉ X, ∃ w : Fin 13, x3 X w ∧ x2 v w := by
          intro v hv
          have h1 := hmf.2.1 v hv
          unfold IsFalseInput at h1
          have hex : ∃ w ∈ Y, ¬ Disjoint (S w) (insert v X) := by
            by_contra hno
            exact h1 fun w hw => by by_contra hnd; exact hno ⟨w, hw, hnd⟩
          obtain ⟨w, hw, hnd⟩ := hex
          rw [Finset.not_disjoint_iff] at hnd
          obtain ⟨p, hpS, hpIns⟩ := hnd
          rw [Finset.mem_insert] at hpIns
          rcases hpIns with rfl | hpX
          · exact ⟨w, (hY w).mp hw, (hinc_iff p w).mpr hpS⟩
          · exact False.elim ((hY w).mp hw p hpX ((hinc_iff p w).mpr hpS))
        have hdeg' : (∃ w, ∀ p ∈ X, x2 p w) ∨ (∃ v, ∀ w, x3 X w → x2 v w) := by
          rcases hdeg with hnl | hnp
          · unfold InNoLine at hnl
            have hex : ∃ w : Fin 13, X ⊆ S w := by
              by_contra hno
              exact hnl fun w hw => hno ⟨w, hw⟩
            obtain ⟨w, hw⟩ := hex
            exact Or.inl ⟨w, fun p hp => (hinc_iff p w).mpr (hw hp)⟩
          · unfold InNoPencil at hnp
            have hex : ∃ v : Fin 13, ∀ w ∈ Y, v ∈ S w := by
              by_contra hno
              exact hnp fun v hv => hno ⟨v, hv⟩
            obtain ⟨v, hv⟩ := hex
            exact Or.inr ⟨v, fun w hw => (hinc_iff v w).mpr (hv w ((hY w).mpr hw))⟩
        rw [hincIn X Y]
        have hfn : (fun k : Fin 26 => decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨
            (∃ w ∈ Y, k = Fin.natAdd 13 w))) =
            (fun k : Fin 26 => decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨
            (∃ w : Fin 13, k = Fin.natAdd 13 w ∧ x3 X w))) := by
          funext k
          apply decide_eq_decide.mpr
          constructor
          · rintro (h | ⟨w, hw, rfl⟩)
            · exact Or.inl h
            · exact Or.inr ⟨w, rfl, (hY w).mp hw⟩
          · rintro (h | ⟨w, rfl, hw⟩)
            · exact Or.inl h
            · exact Or.inr ⟨w, (hY w).mpr hw, rfl⟩
        rw [hfn]
        exact hneg X hclosed hdeg'
    · rintro ⟨hpos, hneg⟩
      refine ⟨?_, ?_⟩
      · intro p w hpw
        have h1 := hpos w p ((hinc_iff p w).mp hpw)
        rw [hincIn {p} {w}] at h1
        have hfn : (fun k : Fin 26 => decide ((∃ q ∈ ({p} : Finset (Fin 13)), k = Fin.castAdd 13 q) ∨
            (∃ u ∈ ({w} : Finset (Fin 13)), k = Fin.natAdd 13 u))) =
            (fun k : Fin 26 => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) := by
          funext k
          simp
        rw [hfn] at h1
        exact h1
      · intro X hclosed hdeg
        let Y : Finset (Fin 13) := Finset.univ.filter fun w => x3 X w
        have hY : ∀ w, w ∈ Y ↔ x3 X w := fun w => by simp [Y]
        have hmf : IsMaximalFalse S X Y := by
          refine ⟨?_, ?_, ?_⟩
          · intro w hw
            rw [Finset.disjoint_left]
            intro p hpS hpX
            exact (hY w).mp hw p hpX ((hinc_iff p w).mpr hpS)
          · intro v hv hfalse
            obtain ⟨w, hw, hvw⟩ := hclosed v hv
            exact Finset.disjoint_left.mp (hfalse w ((hY w).mpr hw)) ((hinc_iff v w).mp hvw)
              (Finset.mem_insert_self v X)
          · intro w hw hfalse
            have hnot : ¬ x3 X w := fun h => hw ((hY w).mpr h)
            have hex : ∃ p ∈ X, x2 p w := by
              by_contra hno
              exact hnot fun p hp hinc => hno ⟨p, hp, hinc⟩
            obtain ⟨p, hpX, hpw⟩ := hex
            exact Finset.disjoint_left.mp (hfalse w (Finset.mem_insert_self w Y))
              ((hinc_iff p w).mp hpw) hpX
        have hdeg' : ¬ InNoLine S X ∨ ¬ InNoPencil S Y := by
          rcases hdeg with ⟨w, hw⟩ | ⟨v, hv⟩
          · left
            intro hnl
            exact hnl w fun p hp => (hinc_iff p w).mp (hw p hp)
          · right
            intro hnp
            exact hnp v fun w hw => (hinc_iff v w).mp (hv w ((hY w).mp hw))
        have h1 := hneg X Y hmf hdeg'
        rw [hincIn X Y] at h1
        have hfn : (fun k : Fin 26 => decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨
            (∃ w ∈ Y, k = Fin.natAdd 13 w))) =
            (fun k : Fin 26 => decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨
            (∃ w : Fin 13, k = Fin.natAdd 13 w ∧ x3 X w))) := by
          funext k
          apply decide_eq_decide.mpr
          constructor
          · rintro (h | ⟨w, hw, rfl⟩)
            · exact Or.inl h
            · exact Or.inr ⟨w, rfl, (hY w).mp hw⟩
          · rintro (h | ⟨w, rfl, hw⟩)
            · exact Or.inl h
            · exact Or.inr ⟨w, (hY w).mpr hw, rfl⟩
        rw [hfn] at h1
        exact h1
  have hsplit26 : ∀ {P : Fin 26 → Prop},
      (∀ p : Fin 13, P (Fin.castAdd 13 p)) → (∀ w : Fin 13, P (Fin.natAdd 13 w)) → ∀ k : Fin 26, P k := by
    intro P hL hR k
    have hklt : k.val < 26 := k.isLt
    by_cases hk : k.val < 13
    · have heq : k = Fin.castAdd 13 ⟨k.val, hk⟩ := Fin.ext rfl
      rw [heq]; exact hL ⟨k.val, hk⟩
    · let w : Fin 13 := ⟨k.val - 13, by omega⟩
      have heq : k = Fin.natAdd 13 w := Fin.ext (show k.val = 13 + w.val by dsimp only [w]; omega)
      rw [heq]; exact hR w
  have hthin_line : ∀ C : Circuit, Monotone2 C → degSep C → ∀ x : Fin 26 → Bool, x5 x →
      (circuitFun 26 C x = true ↔
        ∃ p w : Fin 13, p ∈ S w ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true) := by
    intro C hm hsep x hx5
    constructor
    · intro hCx
      by_contra hno
      obtain ⟨w0, hw0⟩ := hx5
      by_cases h0 : x (Fin.natAdd 13 w0) = true
      · have hle : ∀ k : Fin 26, x k = true →
            decide ((∃ p ∈ zeroSet S {w0}, k = Fin.castAdd 13 p) ∨
              (∃ w ∈ ({w0} : Finset (Fin 13)), k = Fin.natAdd 13 w)) = true := by
          refine hsplit26 (fun p hk => ?_) (fun w hk => ?_)
          · apply decide_eq_true
            refine Or.inl ⟨p, ?_, rfl⟩
            simp only [hzeroSet_def, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            intro l hl hpl
            subst hl
            exact hno ⟨p, l, hpl, hk, h0⟩
          · exact decide_eq_true (Or.inr ⟨w, Finset.mem_singleton.mpr (hw0 w hk), rfl⟩)
        have h1 := hmono_cfun C hm x _ hle hCx
        have h2 := hsep.2 (zeroSet S {w0}) {w0} (hdeg_oneLine w0).1 (Or.inr (hdeg_oneLine w0).2)
        rw [hincIn] at h2
        exact Bool.noConfusion (h1.symm.trans h2)
      · have hle : ∀ k : Fin 26, x k = true →
            decide ((∃ p ∈ (Finset.univ : Finset (Fin 13)), k = Fin.castAdd 13 p) ∨
              (∃ w ∈ (∅ : Finset (Fin 13)), k = Fin.natAdd 13 w)) = true := by
          refine hsplit26 (fun p _ => decide_eq_true (Or.inl ⟨p, Finset.mem_univ p, rfl⟩)) (fun w hk => ?_)
          have hw := hw0 w hk
          subst hw
          exact False.elim (h0 hk)
        have h1 := hmono_cfun C hm x _ hle hCx
        have h2 := hsep.2 Finset.univ ∅ hdeg_univ.1 (Or.inr hdeg_univ.2)
        rw [hincIn] at h2
        exact Bool.noConfusion (h1.symm.trans h2)
    · rintro ⟨p, w, hpw, hp, hw⟩
      have h1 := hsep.1 w p hpw
      rw [hincIn {p} {w}] at h1
      apply hmono_cfun C hm _ x _ h1
      intro k hk
      rcases of_decide_eq_true hk with ⟨q, hq, rfl⟩ | ⟨u, hu, rfl⟩
      · rw [Finset.mem_singleton.mp hq]; exact hp
      · rw [Finset.mem_singleton.mp hu]; exact hw
  have hthin_pt : ∀ C : Circuit, Monotone2 C → degSep C → ∀ x : Fin 26 → Bool,
      (∃ p0 : Fin 13, ∀ p : Fin 13, x (Fin.castAdd 13 p) = true → p = p0) →
      (circuitFun 26 C x = true ↔
        ∃ p w : Fin 13, p ∈ S w ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true) := by
    intro C hm hsep x hpt
    constructor
    · intro hCx
      by_contra hno
      obtain ⟨p0, hp0⟩ := hpt
      by_cases h0 : x (Fin.castAdd 13 p0) = true
      · let Y0 : Finset (Fin 13) := Finset.univ.filter fun w => p0 ∉ S w
        have hle : ∀ k : Fin 26, x k = true →
            decide ((∃ p ∈ ({p0} : Finset (Fin 13)), k = Fin.castAdd 13 p) ∨
              (∃ w ∈ Y0, k = Fin.natAdd 13 w)) = true := by
          refine hsplit26 (fun p hk => decide_eq_true (Or.inl ⟨p, Finset.mem_singleton.mpr (hp0 p hk), rfl⟩)) (fun w hk => ?_)
          apply decide_eq_true
          refine Or.inr ⟨w, ?_, rfl⟩
          simp only [Y0, Finset.mem_filter, Finset.mem_univ, true_and]
          intro hmem
          exact hno ⟨p0, w, hmem, h0, hk⟩
        have h1 := hmono_cfun C hm x _ hle hCx
        have h2 := hsep.2 {p0} Y0 (hdeg_onePt p0).1 (Or.inl (hdeg_onePt p0).2)
        rw [hincIn] at h2
        exact Bool.noConfusion (h1.symm.trans h2)
      · have hle : ∀ k : Fin 26, x k = true →
            decide ((∃ p ∈ (∅ : Finset (Fin 13)), k = Fin.castAdd 13 p) ∨
              (∃ w ∈ (Finset.univ : Finset (Fin 13)), k = Fin.natAdd 13 w)) = true := by
          refine hsplit26 (fun p hk => ?_) (fun w _ => decide_eq_true (Or.inr ⟨w, Finset.mem_univ w, rfl⟩))
          have hp := hp0 p hk
          subst hp
          exact False.elim (h0 hk)
        have h1 := hmono_cfun C hm x _ hle hCx
        have h2 := hsep.2 ∅ Finset.univ hdeg_empty.1 (Or.inl hdeg_empty.2)
        rw [hincIn] at h2
        exact Bool.noConfusion (h1.symm.trans h2)
    · rintro ⟨p, w, hpw, hp, hw⟩
      have h1 := hsep.1 w p hpw
      rw [hincIn {p} {w}] at h1
      apply hmono_cfun C hm _ x _ h1
      intro k hk
      rcases of_decide_eq_true hk with ⟨q, hq, rfl⟩ | ⟨u, hu, rfl⟩
      · rw [Finset.mem_singleton.mp hq]; exact hp
      · rw [Finset.mem_singleton.mp hu]; exact hw
  let mapC (ρ : ℕ → ℕ) (C : Circuit) : Circuit :=
    ⟨C.gates.map fun g => ⟨g.op, g.inputs.map ρ⟩, ρ C.output⟩
  let sort2 (l : List ℕ) : List ℕ :=
    List.casesOn l [] fun a t =>
      List.casesOn t [a] fun b r =>
        List.casesOn r (if a ≤ b then [a, b] else [b, a]) fun c r' => a :: b :: c :: r'
  let sortC (C : Circuit) : Circuit :=
    ⟨C.gates.map fun g => ⟨g.op, sort2 g.inputs⟩, C.output⟩
  have hfold_len : ∀ {α : Type} (F : Gate → List α → α) (gs : List Gate) (init : List α),
      (gs.foldl (fun L g => L ++ [F g L]) init).length = init.length + gs.length := by
    intro α F gs
    induction gs with
    | nil => intro init; simp
    | cons g gs ih =>
      intro init
      rw [List.foldl_cons, ih]
      simp
      omega
  have hgen_rel : ∀ {α : Type} (d : α) (F : Gate → List α → α) (ρ : ℕ → ℕ),
      (∀ i < 26, ρ i < 26) → (∀ i, 26 ≤ i → ρ i = i) →
      (∀ (g : Gate) (L L' : List α), (∀ j, L'.getD (ρ j) d = L.getD j d) →
        F ⟨g.op, g.inputs.map ρ⟩ L' = F g L) →
      ∀ (gs : List Gate) (init init' : List α), init.length = 26 → init'.length = 26 →
      (∀ j, init'.getD (ρ j) d = init.getD j d) →
      ∀ j, ((gs.map fun g : Gate => (⟨g.op, g.inputs.map ρ⟩ : Gate)).foldl (fun L g => L ++ [F g L]) init').getD (ρ j) d =
        (gs.foldl (fun L g => L ++ [F g L]) init).getD j d := by
    intro α d F ρ hlt hge hF gs init init' hl hl' h0
    induction gs using List.reverseRecOn with
    | nil => intro j; simpa using h0 j
    | append_singleton gs g ih =>
      intro j
      have e1 : (gs.foldl (fun L g => L ++ [F g L]) init).length = 26 + gs.length := by
        rw [hfold_len, hl]
      have e2 : ((gs.map fun g : Gate => (⟨g.op, g.inputs.map ρ⟩ : Gate)).foldl (fun L g => L ++ [F g L]) init').length = 26 + gs.length := by
        rw [hfold_len, hl', List.length_map]
      rw [List.map_append, List.foldl_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      generalize (gs.foldl (fun L g => L ++ [F g L]) init) = L at ih e1 ⊢
      generalize ((gs.map fun g : Gate => (⟨g.op, g.inputs.map ρ⟩ : Gate)).foldl (fun L g => L ++ [F g L]) init') = L' at ih e2 ⊢
      rcases Nat.lt_trichotomy j (26 + gs.length) with hj | hj | hj
      · have hρj : ρ j < 26 + gs.length := by
          by_cases hjn : j < 26
          · have := hlt j hjn; omega
          · rw [hge j (by omega)]; exact hj
        rw [hsnoc_lt L' _ d (ρ j) (by omega), hsnoc_lt L _ d j (by omega)]
        exact ih j
      · rw [hge j (by omega), hj]
        have a1 := hsnoc_eq L' (F ⟨g.op, g.inputs.map ρ⟩ L') d
        have a2 := hsnoc_eq L (F g L) d
        rw [e2] at a1; rw [e1] at a2
        rw [a1, a2]
        exact hF g L L' ih
      · rw [hge j (by omega), hsnoc_gt L' _ d j (by omega), hsnoc_gt L _ d j (by omega)]
  have hmap_val : ∀ (C : Circuit) (ρ : ℕ → ℕ) (hlt : ∀ i < 26, ρ i < 26),
      (∀ i, 26 ≤ i → ρ i = i) →
      ∀ (x y : Fin 26 → Bool), (∀ j : Fin 26, y j = x ⟨ρ j.val, hlt j.val j.isLt⟩) →
      circuitFun 26 (mapC ρ C) x = circuitFun 26 C y := by
    intro C ρ hlt hge x y hxy
    have h0 : ∀ j, (List.ofFn x).getD (ρ j) false = (List.ofFn y).getD j false := by
      intro j
      by_cases hj : j < 26
      · have hr := hlt j hj
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr, hj, dite_true, Option.getD_some]
        exact (hxy ⟨j, hj⟩).symm
      · rw [hge j (by omega), List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact hgen_rel false (fun g L => g.op.eval (g.inputs.map fun i => L.getD i false)) ρ hlt hge
      (fun g L L' h => by
        show g.op.eval ((g.inputs.map ρ).map fun i => L'.getD i false) = _
        rw [List.map_map]
        congr 1
        exact List.map_congr_left fun j _ => h j)
      C.gates (List.ofFn y) (List.ofFn x) (by simp) (by simp) h0 C.output
  have hmap_deg : ∀ (C : Circuit) (ρ : ℕ → ℕ) (M M' : Finset ℕ),
      (∀ i < 26, ρ i < 26) → (∀ i, 26 ≤ i → ρ i = i) →
      (∀ j < 26, ρ j ∈ M' ↔ j ∈ M) →
      (mapC ρ C).lineDeg 26 M' = C.lineDeg 26 M := by
    intro C ρ M M' hlt hge hmark
    have h0 : ∀ j, ((List.range 26).map fun i => if i ∈ M' then 1 else 0).getD (ρ j) 0 =
        ((List.range 26).map fun i => if i ∈ M then 1 else 0).getD j 0 := by
      intro j
      by_cases hj : j < 26
      · have hr := hlt j hj
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
          List.getElem?_range hr, List.getElem?_range hj]
        simp only [Option.map_some, Option.getD_some]
        by_cases hm : j ∈ M
        · simp only [hm, (hmark j hj).mpr hm, ite_true]
        · have hm2 : ρ j ∉ M' := fun h => hm ((hmark j hj).mp h)
          simp only [hm, hm2, ite_false]
      · rw [hge j (by omega), List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact hgen_rel 0 (fun g L => g.lineDegree L) ρ hlt hge
      (fun g L L' h => by
        have hl : (g.inputs.map ρ).map (fun i => L'.getD i 0) = g.inputs.map (fun i => L.getD i 0) := by
          rw [List.map_map]
          exact List.map_congr_left fun j _ => h j
        delta Gate.lineDegree
        dsimp only
        rw [hl])
      C.gates _ _ (by simp) (by simp) h0 C.output
  have hmap_cones : ∀ (C : Circuit) (ρ : ℕ → ℕ),
      (∀ i < 26, ρ i < 26) → (∀ i, 26 ≤ i → ρ i = i) →
      cones 26 (mapC ρ C) = cones 26 C := by
    intro C ρ hlt hge
    have hfilt : ∀ (l : List ℕ) (m : ℕ),
        (l.map ρ).filter (fun w => decide (26 ≤ w ∧ w < 26 + m)) =
        l.filter (fun w => decide (26 ≤ w ∧ w < 26 + m)) := by
      intro l m
      induction l with
      | nil => rfl
      | cons a t ih =>
        simp only [List.map_cons, List.filter_cons]
        by_cases ha : a < 26
        · have hra := hlt a ha
          have h1 : decide (26 ≤ ρ a ∧ ρ a < 26 + m) = false := decide_eq_false (by omega)
          have h2 : decide (26 ≤ a ∧ a < 26 + m) = false := decide_eq_false (by omega)
          rw [h1, h2]
          exact ih
        · rw [hge a (by omega)]
          by_cases hcond : 26 ≤ a ∧ a < 26 + m
          · rw [decide_eq_true hcond, ih]
          · rw [decide_eq_false hcond, ih]
    have hfold : ∀ (gs : List Gate) (acc : List (List ℕ)),
        (gs.map fun g : Gate => (⟨g.op, g.inputs.map ρ⟩ : Gate)).foldl (coneStep 26) acc =
        gs.foldl (coneStep 26) acc := by
      intro gs
      induction gs with
      | nil => intro acc; rfl
      | cons g gs ih =>
        intro acc
        simp only [List.map_cons, List.foldl_cons]
        have hst : coneStep 26 acc ⟨g.op, g.inputs.map ρ⟩ = coneStep 26 acc g := by
          simp only [hconeStep_def]
          rw [hfilt]
        rw [hst, ih]
    exact hfold C.gates []
  have hmap_live : ∀ (C : Circuit) (ρ : ℕ → ℕ),
      (∀ i < 26, ρ i < 26) → (∀ i, 26 ≤ i → ρ i = i) → 26 ≤ C.output →
      liveSize 26 (mapC ρ C) = liveSize 26 C := by
    intro C ρ hlt hge hout
    simp only [hliveSize_def, hliveGates_def]
    apply congrArg Finset.card
    ext j
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    have hlen : (mapC ρ C).gates.length = C.gates.length := List.length_map _
    have ho : (mapC ρ C).output = C.output := hge C.output hout
    simp only [hInCone_def, hlen, ho, hmap_cones C ρ hlt hge]
  have hmap_ao2 : ∀ (C : Circuit) (ρ : ℕ → ℕ),
      (∀ i < 26, ρ i < 26) → (∀ i, 26 ≤ i → ρ i = i) →
      IsAO2 26 C → IsAO2 26 (mapC ρ C) := by
    rintro C ρ hlt hge ⟨hao, hrb, hlen2⟩
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact hao g0 hg0
    · intro j hj i hi
      rw [List.length_map] at hj
      have hga : gateAt (mapC ρ C) j = ⟨(gateAt C j).op, (gateAt C j).inputs.map ρ⟩ := by
        unfold gateAt
        simp only [mapC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
        rfl
      rw [hga] at hi
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
      have ha' := hrb j hj a ha
      by_cases h26 : a < 26
      · have := hlt a h26; omega
      · rw [hge a (by omega)]; exact ha'
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      simpa using hlen2 g0 hg0
  have hmap_nodup : ∀ (C : Circuit) (ρ : ℕ → ℕ),
      Function.Injective ρ →
      (∀ g ∈ C.gates, g.inputs.length = 2) →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      ∀ j < (mapC ρ C).size, opnd (mapC ρ C) j 0 ≠ opnd (mapC ρ C) j 1 := by
    intro C ρ hinj hlen2 hnd j hj
    have hj' : j < C.gates.length := by simpa [hCircuit_size, mapC] using hj
    have hga : gateAt (mapC ρ C) j = ⟨(gateAt C j).op, (gateAt C j).inputs.map ρ⟩ := by
      unfold gateAt
      simp only [mapC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj']
      rfl
    have hgmem : gateAt C j ∈ C.gates := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hj']; exact List.getElem_mem hj'
    have hgl : (gateAt C j).inputs.length = 2 := hlen2 _ hgmem
    unfold opnd at hnd ⊢
    rw [hga]
    dsimp only
    intro heq
    have h0 := hnd j hj'
    cases h : (gateAt C j).inputs with
    | nil => simp [h] at hgl
    | cons a t =>
      cases t with
      | nil => simp [h] at hgl
      | cons b r =>
        simp only [h, List.map_cons, List.getD_cons_zero, List.getD_cons_succ] at heq
        exact h0 (by simp [h, hinj heq])
  have hsort_all : ∀ C : Circuit, IsAO2 26 C → (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (sortC C).size = C.size ∧ (sortC C).output = C.output ∧ IsAO2 26 (sortC C) ∧
      (∀ j < (sortC C).size, opnd (sortC C) j 0 < opnd (sortC C) j 1) ∧
      (∀ x : List Bool, (sortC C).wires x = C.wires x) ∧
      (∀ M : Finset ℕ, (sortC C).lineDegrees 26 M = C.lineDegrees 26 M) ∧
      liveSize 26 (sortC C) = liveSize 26 C := by
    rintro C ⟨hao, hrb, hlen2⟩ hnd
    have hsz : (sortC C).size = C.size := List.length_map _
    have ho : (sortC C).output = C.output := rfl
    have h2 : ∀ (g : Gate), g.inputs.length = 2 → ∃ a b, g.inputs = [a, b] := by
      intro g hl
      cases h : g.inputs with
      | nil => simp [h] at hl
      | cons a t =>
        cases t with
        | nil => simp [h] at hl
        | cons b r =>
          cases r with
          | nil => exact ⟨a, b, rfl⟩
          | cons c r' => simp [h] at hl
    have hsort_mem : ∀ (l : List ℕ) (x : ℕ), x ∈ sort2 l ↔ x ∈ l := by
      intro l x
      cases l with
      | nil => simp [sort2]
      | cons a t =>
        cases t with
        | nil => simp [sort2]
        | cons b r =>
          cases r with
          | nil =>
            dsimp only [sort2]
            split_ifs <;> simp [or_comm]
          | cons c r' => simp [sort2]
    have hsort_len : ∀ l : List ℕ, (sort2 l).length = l.length := by
      intro l
      cases l with
      | nil => rfl
      | cons a t =>
        cases t with
        | nil => rfl
        | cons b r =>
          cases r with
          | nil => dsimp only [sort2]; split_ifs <;> rfl
          | cons c r' => rfl
    have hao2' : IsAO2 26 (sortC C) := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        exact hao g0 hg0
      · intro j hj i hi
        rw [List.length_map] at hj
        have hga : gateAt (sortC C) j = ⟨(gateAt C j).op, sort2 (gateAt C j).inputs⟩ := by
          unfold gateAt
          simp only [sortC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
          rfl
        rw [hga] at hi
        exact hrb j hj i ((hsort_mem _ i).mp hi)
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        exact (hsort_len _).trans (hlen2 g0 hg0)
    have hlt' : ∀ j < (sortC C).size, opnd (sortC C) j 0 < opnd (sortC C) j 1 := by
      intro j hj
      have hj' : j < C.gates.length := by simpa [hCircuit_size, sortC] using hj
      have hga : gateAt (sortC C) j = ⟨(gateAt C j).op, sort2 (gateAt C j).inputs⟩ := by
        unfold gateAt
        simp only [sortC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj']
        rfl
      have hgmem : gateAt C j ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hj']
        exact List.getElem_mem hj'
      obtain ⟨a, b, hab⟩ := h2 (gateAt C j) (hlen2 _ hgmem)
      have hne : a ≠ b := by
        have h0 := hnd j hj'
        unfold opnd at h0
        simpa [hab] using h0
      unfold opnd
      rw [hga]
      dsimp only
      rw [hab]
      dsimp only [sort2]
      split_ifs with hle <;> simp <;> omega
    have hwires' : ∀ x : List Bool, (sortC C).wires x = C.wires x := by
      intro x
      have hfold : ∀ (gs : List Gate), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) →
          ∀ w : List Bool,
          (gs.map fun g : Gate => (⟨g.op, sort2 g.inputs⟩ : Gate)).foldl stepW w = gs.foldl stepW w := by
        intro gs
        induction gs with
        | nil => intro _ w; rfl
        | cons g gs ih =>
          intro hgs w
          obtain ⟨hop, hl⟩ := hgs g (by simp)
          obtain ⟨a, b, hab⟩ := h2 g hl
          simp only [List.map_cons, List.foldl_cons]
          have hst : stepW w ⟨g.op, sort2 g.inputs⟩ = stepW w g := by
            simp only [stepW, hab, sort2]
            split_ifs
            · rfl
            · congr 2
              rcases hop with h | h <;> rw [h]
              · simp [hGateOp_and, Bool.and_comm]
              · simp [hGateOp_or, Bool.or_comm]
          rw [hst]
          exact ih (fun u hu => hgs u (by simp [hu])) _
      exact hfold C.gates (fun g hg => ⟨hao g hg, hlen2 g hg⟩) x
    have hdeg' : ∀ M : Finset ℕ, (sortC C).lineDegrees 26 M = C.lineDegrees 26 M := by
      intro M
      have hfold : ∀ (gs : List Gate), (∀ g ∈ gs, g.inputs.length = 2) →
          ∀ d : List ℕ,
          (gs.map fun g : Gate => (⟨g.op, sort2 g.inputs⟩ : Gate)).foldl (fun d g => d ++ [g.lineDegree d]) d =
          gs.foldl (fun d g => d ++ [g.lineDegree d]) d := by
        intro gs
        induction gs with
        | nil => intro _ d; rfl
        | cons g gs ih =>
          intro hgs d
          obtain ⟨a, b, hab⟩ := h2 g (hgs g (by simp))
          simp only [List.map_cons, List.foldl_cons]
          have hst : (⟨g.op, sort2 g.inputs⟩ : Gate).lineDegree d = g.lineDegree d := by
            delta Gate.lineDegree
            dsimp only
            rw [hab]
            dsimp only [sort2]
            by_cases hle : a ≤ b
            · rw [if_pos hle]
            · rw [if_neg hle]
              split_ifs
              · simp [Nat.add_comm]
              · simp [Nat.max_comm]
          rw [hst]
          exact ih (fun u hu => hgs u (by simp [hu])) _
      exact hfold C.gates hlen2 _
    have hlive' : liveSize 26 (sortC C) = liveSize 26 C := by
      have hcone_eq : ∀ (gs : List Gate) (acc1 acc2 : List (List ℕ)),
          acc1.length = acc2.length →
          (∀ j i, i ∈ acc1.getD j [] ↔ i ∈ acc2.getD j []) →
          ∀ j i, i ∈ ((gs.map fun g : Gate => (⟨g.op, sort2 g.inputs⟩ : Gate)).foldl (coneStep 26) acc1).getD j [] ↔
            i ∈ (gs.foldl (coneStep 26) acc2).getD j [] := by
        intro gs
        induction gs with
        | nil => intro acc1 acc2 _ h j i; exact h j i
        | cons g gs ih =>
          intro acc1 acc2 hlen hacc j i
          simp only [List.map_cons, List.foldl_cons]
          apply ih
          · simp [hconeStep_def, hlen]
          · intro j0 i0
            simp only [hconeStep_def]
            rcases Nat.lt_trichotomy j0 acc1.length with hlt | heq | hgt
            · rw [hsnoc_lt acc1 _ [] j0 hlt, hsnoc_lt acc2 _ [] j0 (by omega)]
              exact hacc j0 i0
            · rw [heq, hsnoc_eq acc1 _ [], hlen, hsnoc_eq acc2 _ []]
              simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
              constructor
              · rintro ⟨w, ⟨hw1, hw2⟩, hw3⟩
                refine ⟨w, ⟨(hsort_mem _ w).mp hw1, by omega⟩, ?_⟩
                rcases hw3 with rfl | hw3
                · exact Or.inl rfl
                · exact Or.inr ((hacc (w - 26) i0).mp hw3)
              · rintro ⟨w, ⟨hw1, hw2⟩, hw3⟩
                refine ⟨w, ⟨(hsort_mem _ w).mpr hw1, by omega⟩, ?_⟩
                rcases hw3 with rfl | hw3
                · exact Or.inl rfl
                · exact Or.inr ((hacc (w - 26) i0).mpr hw3)
            · rw [hsnoc_gt acc1 _ [] j0 hgt, hsnoc_gt acc2 _ [] j0 (by omega)]
      simp only [hliveSize_def, hliveGates_def]
      apply congrArg Finset.card
      ext j
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_range]
      simp only [sortC, List.length_map, hInCone_def, hcones_def]
      have h1 := hcone_eq C.gates [] [] rfl (fun _ _ => Iff.rfl) (C.output - 26) j
      exact and_congr_right fun _ => and_congr_right fun _ => or_congr_right h1
    exact ⟨hsz, ho, hao2', hlt', hwires', hdeg', hlive'⟩
  let ρ_dual (j : ℕ) : ℕ :=
    if j < 13 then 13 + (13 - j) % 13 else if j < 26 then (26 - j) % 13 else j
  have hdual_lt : ∀ i < 26, ρ_dual i < 26 := by
    intro i hi; dsimp only [ρ_dual]; split_ifs <;> omega
  have hdual_ge : ∀ i, 26 ≤ i → ρ_dual i = i := by
    intro i hi; dsimp only [ρ_dual]; split_ifs <;> omega
  have hdual_inj : Function.Injective ρ_dual := by
    intro a b hab
    dsimp only [ρ_dual] at hab
    split_ifs at hab <;> omega
  have hdual_Ico : ∀ j < 26, ρ_dual j ∈ Finset.Ico 13 26 ↔ j ∈ Finset.range 13 := by
    intro j hj; dsimp only [ρ_dual]; simp only [Finset.mem_Ico, Finset.mem_range]; split_ifs <;> omega
  have hdual_range : ∀ j < 26, ρ_dual j ∈ Finset.range 13 ↔ j ∈ Finset.Ico 13 26 := by
    intro j hj; dsimp only [ρ_dual]; simp only [Finset.mem_Ico, Finset.mem_range]; split_ifs <;> omega
  have hdual_eval : ∀ (C : Circuit) (X Y : Finset (Fin 13)),
      (mapC ρ_dual C).eval (incidenceInput X Y) =
      C.eval (incidenceInput (Y.image fun w => -w) (X.image fun p => -p)) := by
    intro C X Y
    rw [hincIn X Y, hincIn]
    apply hmap_val C ρ_dual hdual_lt hdual_ge
    refine hsplit26 (fun q => ?_) (fun w => ?_)
    · apply decide_eq_decide.mpr
      have hq : (⟨ρ_dual (Fin.castAdd 13 q).val, hdual_lt _ (Fin.castAdd 13 q).isLt⟩ : Fin 26) = Fin.natAdd 13 (-q) := by
        apply Fin.ext
        simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_neg', ρ_dual]
        have := q.isLt
        split_ifs
        omega
      rw [hq]
      constructor
      · rintro (⟨p, hp, he⟩ | ⟨w, _, he⟩)
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
          have hqu : q = -u := Fin.ext (by have h' := congrArg Fin.val he; simpa using h')
          subst hqu
          exact Or.inr ⟨u, hu, by rw [neg_neg]⟩
        · have h' := congrArg Fin.val he; simp at h'; have := q.isLt; omega
      · rintro (⟨p, _, he⟩ | ⟨w, hw, he⟩)
        · have h' := congrArg Fin.val he; simp at h'; have := p.isLt; omega
        · have hqw : w = -q := Fin.ext (by have h' := congrArg Fin.val he; simp at h'; omega)
          subst hqw
          exact Or.inl ⟨q, Finset.mem_image.mpr ⟨-q, hw, neg_neg q⟩, rfl⟩
    · apply decide_eq_decide.mpr
      have hw : (⟨ρ_dual (Fin.natAdd 13 w).val, hdual_lt _ (Fin.natAdd 13 w).isLt⟩ : Fin 26) = Fin.castAdd 13 (-w) := by
        apply Fin.ext
        simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_neg', ρ_dual]
        have := w.isLt
        split_ifs <;> omega
      rw [hw]
      constructor
      · rintro (⟨p, _, he⟩ | ⟨u, hu, he⟩)
        · have h' := congrArg Fin.val he; simp at h'; have := p.isLt; omega
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
          have hwp : w = -p := Fin.ext (by have h' := congrArg Fin.val he; simp at h'; omega)
          subst hwp
          exact Or.inl ⟨p, hp, by rw [neg_neg]⟩
      · rintro (⟨p, hp, he⟩ | ⟨u, _, he⟩)
        · have hpw : p = -w := Fin.ext (by have h' := congrArg Fin.val he; simpa using h'.symm)
          subst hpw
          exact Or.inr ⟨w, Finset.mem_image.mpr ⟨-w, hp, neg_neg w⟩, rfl⟩
        · have h' := congrArg Fin.val he; simp at h'; have := (-w).isLt; omega
  have hdual_degSep : ∀ C : Circuit, degSep C → degSep (mapC ρ_dual C) := by
    rintro C ⟨hpos, hneg⟩
    refine ⟨?_, ?_⟩
    · intro w p hpw
      rw [hdual_eval C {p} {w}]
      simp only [Finset.image_singleton]
      exact hpos (-p) (-w) ((hS_dual p w).mp hpw)
    · intro X Y hmf hdeg
      rw [hdual_eval C X Y]
      have hmf' : IsMaximalFalse S (Y.image fun w => -w) (X.image fun p => -p) := by
        refine ⟨?_, ?_, ?_⟩
        · intro u hu
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
          rw [Finset.disjoint_left]
          intro q hq hqY
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hqY
          exact Finset.disjoint_left.mp (hmf.1 w hw) ((hS_dual p w).mpr hq) hp
        · intro q hq hfalse
          have hnot : -q ∉ Y := fun h => hq (Finset.mem_image.mpr ⟨-q, h, neg_neg q⟩)
          apply hmf.2.2 (-q) hnot
          intro u hu
          rw [Finset.mem_insert] at hu
          rcases hu with rfl | hu
          · rw [Finset.disjoint_left]
            intro p hp hpX
            have h1 := hfalse (-p) (Finset.mem_image.mpr ⟨p, hpX, rfl⟩)
            have hinc : q ∈ S (-p) := by have := (hS_dual p (-q)).mp hp; rwa [neg_neg] at this
            exact Finset.disjoint_left.mp h1 hinc (Finset.mem_insert_self q _)
          · exact hmf.1 u hu
        · intro u hu hfalse
          have hnot : -u ∉ X := fun h => hu (Finset.mem_image.mpr ⟨-u, h, neg_neg u⟩)
          apply hmf.2.1 (-u) hnot
          intro w hw
          rw [Finset.disjoint_left]
          intro p hp hpIns
          rw [Finset.mem_insert] at hpIns
          rcases hpIns with rfl | hpX
          · have h1 := hfalse u (Finset.mem_insert_self u _)
            have hmem : -w ∈ Y.image fun v => -v := Finset.mem_image.mpr ⟨w, hw, rfl⟩
            have hinc : -w ∈ S u := by
              have := (hS_dual (-u) w).mp hp
              rwa [neg_neg] at this
            exact Finset.disjoint_left.mp h1 hinc hmem
          · exact Finset.disjoint_left.mp (hmf.1 w hw) hp hpX
      have hdeg' : ¬ InNoLine S (Y.image fun w => -w) ∨ ¬ InNoPencil S (X.image fun p => -p) := by
        rcases hdeg with hnl | hnp
        · right
          intro hnp'
          apply hnl
          intro w hw
          apply hnp' (-w)
          intro u hu
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
          exact (hS_dual p w).mp (hw hp)
        · left
          intro hnl'
          apply hnp
          intro p hp
          apply hnl' (-p)
          intro q hq
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
          exact (hS_dual p w).mp (hp w hw)
      exact hneg _ _ hmf' hdeg'
  have hdual_exact : ∀ C : Circuit, ComputesIncidence S C → ComputesIncidence S (mapC ρ_dual C) := by
    intro C hex X Y
    rw [hdual_eval C X Y, hex]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨q, hq, u, hu, hqu⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨p, hp, w, hw, (hS_dual p w).mpr hqu⟩
    · rintro ⟨p, hp, w, hw, hpw⟩
      exact ⟨-w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, -p, Finset.mem_image.mpr ⟨p, hp, rfl⟩,
        (hS_dual p w).mp hpw⟩
  have hdual_thin : ∀ C : Circuit, Monotone2 C → degSep C →
      ∀ x : Fin 26 → Bool, x5 x →
      circuitFun 26 (mapC ρ_dual C) x = circuitFun 26 C x := by
    intro C hm hsep x hx5
    let y : Fin 26 → Bool := fun j => x ⟨ρ_dual j.val, hdual_lt j.val j.isLt⟩
    have hv := hmap_val C ρ_dual hdual_lt hdual_ge x y (fun _ => rfl)
    rw [hv]
    obtain ⟨w0, hw0⟩ := hx5
    have hy_pt : ∃ p0 : Fin 13, ∀ p : Fin 13, y (Fin.castAdd 13 p) = true → p = p0 := by
      refine ⟨-w0, fun p hp => ?_⟩
      have hidx : (⟨ρ_dual (Fin.castAdd 13 p).val, hdual_lt _ (Fin.castAdd 13 p).isLt⟩ : Fin 26) = Fin.natAdd 13 (-p) := by
        apply Fin.ext
        simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_neg', ρ_dual]
        have := p.isLt; split_ifs <;> omega
      have h1 : x (Fin.natAdd 13 (-p)) = true := by dsimp only [y] at hp; rwa [hidx] at hp
      have h2 := hw0 (-p) h1
      calc p = -(-p) := (neg_neg p).symm
        _ = -w0 := congrArg Neg.neg h2
    have hiff : circuitFun 26 C y = true ↔ circuitFun 26 C x = true := by
      rw [hthin_pt C hm hsep y hy_pt, hthin_line C hm hsep x ⟨w0, hw0⟩]
      constructor
      · rintro ⟨q, u, hqu, hq, hu⟩
        have hidx1 : (⟨ρ_dual (Fin.castAdd 13 q).val, hdual_lt _ (Fin.castAdd 13 q).isLt⟩ : Fin 26) = Fin.natAdd 13 (-q) := by
          apply Fin.ext; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_neg', ρ_dual]; have := q.isLt; split_ifs <;> omega
        have hidx2 : (⟨ρ_dual (Fin.natAdd 13 u).val, hdual_lt _ (Fin.natAdd 13 u).isLt⟩ : Fin 26) = Fin.castAdd 13 (-u) := by
          apply Fin.ext; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_neg', ρ_dual]; have := u.isLt; split_ifs <;> omega
        refine ⟨-u, -q, ?_, ?_, ?_⟩
        · exact (hS_dual (-u) (-q)).mpr (by rw [neg_neg, neg_neg]; exact hqu)
        · dsimp only [y] at hu; rwa [hidx2] at hu
        · dsimp only [y] at hq; rwa [hidx1] at hq
      · rintro ⟨p, w, hpw, hp, hw⟩
        have hidx1 : (⟨ρ_dual (Fin.castAdd 13 (-w)).val, hdual_lt _ (Fin.castAdd 13 (-w)).isLt⟩ : Fin 26) = Fin.natAdd 13 w := by
          apply Fin.ext; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_neg', ρ_dual]; have := w.isLt; split_ifs <;> omega
        have hidx2 : (⟨ρ_dual (Fin.natAdd 13 (-p)).val, hdual_lt _ (Fin.natAdd 13 (-p)).isLt⟩ : Fin 26) = Fin.castAdd 13 p := by
          apply Fin.ext; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_neg', ρ_dual]; have := p.isLt; split_ifs <;> omega
        refine ⟨-w, -p, (hS_dual p w).mp hpw, ?_, ?_⟩
        · dsimp only [y]; rwa [hidx1]
        · dsimp only [y]; rwa [hidx2]
    exact Bool.eq_iff_iff.mpr hiff
  have hsep0 : degSep C0 := (hgood_iff C0).mp hgood0
  have hex_min : ∃ n : ℕ, ∃ C : Circuit, C.size = n ∧ Monotone2 C ∧ degSep C :=
    ⟨C0.size, C0, rfl, hmono0, hsep0⟩
  obtain ⟨C, hCsz, hCmono, hCsep⟩ := Nat.find_spec hex_min
  have hCmin : ∀ D : Circuit, Monotone2 D → degSep D → C.size ≤ D.size := fun D hDm hDs => by
    rw [hCsz]
    exact Nat.find_min' hex_min ⟨D, rfl, hDm, hDs⟩
  have hCle0 : C.size ≤ C0.size := hCmin C0 hmono0 hsep0
  have hCsize63 : C.size ≤ 63 := hCle0.trans hsize0
  have hagree0 : ∀ x : Fin 26 → Bool, x5 x → circuitFun 26 C x = circuitFun 26 C0 x := by
    intro x hx5
    have hiff : circuitFun 26 C x = true ↔ circuitFun 26 C0 x = true := by
      rw [hthin_line C hCmono hCsep x hx5, hthin_line C0 hmono0 hsep0 x hx5]
    exact Bool.eq_iff_iff.mpr hiff
  by_cases hld1 : C.lineDeg 26 (Finset.Ico 13 26) ≤ 1
  · exact ⟨C, hCmono, hCle0, hld1, hagree0⟩
  · by_cases hpd1 : C.lineDeg 26 (Finset.range 13) ≤ 1
    · refine ⟨mapC ρ_dual C, ?_, ?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        obtain ⟨k1, k2⟩ := hCmono g0 hg0
        exact ⟨k1, by simpa using k2⟩
      · have : (mapC ρ_dual C).size = C.size := List.length_map _
        omega
      · show (mapC ρ_dual C).lineDeg 26 (Finset.Ico 13 26) ≤ 1
        rw [hmap_deg C ρ_dual (Finset.range 13) (Finset.Ico 13 26) hdual_lt hdual_ge hdual_Ico]
        exact hpd1
      · intro x hx5
        rw [hdual_thin C hCmono hCsep x hx5, hagree0 x hx5]
    · exfalso
      have hCsz_def : C.size = C.gates.length := rfl
      have hld2 : 2 ≤ C.lineDeg 26 (Finset.Ico 13 26) := by omega
      have hpd2 : 2 ≤ C.lineDeg 26 (Finset.range 13) := by omega
      have hnoConst : ∀ b : Bool, (∀ x : Fin 26 → Bool, circuitFun 26 C x = b) → False := by
        intro b hb
        have hb' : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = b := hb
        cases b with
        | false =>
          have h1 := hCsep.1 0 0 (by simp [S])
          rw [hincIn, hb'] at h1
          exact Bool.noConfusion h1
        | true =>
          have h1 := hCsep.2 Finset.univ ∅ hdeg_univ.1 (Or.inr hdeg_univ.2)
          rw [hincIn, hb'] at h1
          exact Bool.noConfusion h1
      have hCout_ge : 26 ≤ C.output := by
        by_contra hlt
        have hi : C.output < 26 := by omega
        have hbit : ∀ x : Fin 26 → Bool, circuitFun 26 C x = x ⟨C.output, hi⟩ := by
          intro x
          change (runW C.gates (List.ofFn x)).getD C.output false = _
          rw [hrunW_pref _ _ _ (by simp; exact hi), List.getD_eq_getElem _ _ (by simp; exact hi)]
          exact List.getElem_ofFn _
        have h0 := hCsep.1 0 0 (by simp [S])
        have h1 := hCsep.1 1 1 (by simp [S])
        rw [hincIn] at h0 h1
        change circuitFun 26 C _ = true at h0 h1
        rw [hbit] at h0 h1
        have h0' := of_decide_eq_true h0
        have h1' := of_decide_eq_true h1
        have hdis : ∀ k : Fin 26,
            ¬ (((∃ p ∈ ({0} : Finset (Fin 13)), k = Fin.castAdd 13 p) ∨
                (∃ w ∈ ({0} : Finset (Fin 13)), k = Fin.natAdd 13 w)) ∧
               ((∃ p ∈ ({1} : Finset (Fin 13)), k = Fin.castAdd 13 p) ∨
                (∃ w ∈ ({1} : Finset (Fin 13)), k = Fin.natAdd 13 w))) := by
          rintro k ⟨(⟨p, hp, rfl⟩ | ⟨w, hw, rfl⟩), (⟨q, hq, he⟩ | ⟨u, hu, he⟩)⟩
          · rw [Finset.mem_singleton.mp hp, Finset.mem_singleton.mp hq] at he
            have h' := congrArg Fin.val he; simp at h'
          · have h' := congrArg Fin.val he; simp at h'; have := p.isLt; omega
          · have h' := congrArg Fin.val he; simp at h'; have := q.isLt; omega
          · rw [Finset.mem_singleton.mp hw, Finset.mem_singleton.mp hu] at he
            have h' := congrArg Fin.val he; simp at h'
        exact hdis ⟨C.output, hi⟩ ⟨h0', h1'⟩
      have hCout_lt : C.output < 26 + C.size := by
        by_contra hge
        apply hnoConst false
        intro x
        change (runW C.gates (List.ofFn x)).getD C.output false = false
        apply List.getD_eq_default
        rw [hrunW_len, List.length_ofFn]
        omega
      have hCout_last : C.output + 1 = 26 + C.size := by
        let m := C.output - 26 + 1
        have hmle : m ≤ C.size := by dsimp only [m]; omega
        let C' : Circuit := ⟨C.gates.take m, C.output⟩
        have hC'mono : Monotone2 C' := fun g hg => hCmono g (List.mem_of_mem_take hg)
        have hC'eq : ∀ x : Fin 26 → Bool, circuitFun 26 C' x = circuitFun 26 C x := by
          intro x
          change (runW (C.gates.take m) (List.ofFn x)).getD C.output false =
            (runW C.gates (List.ofFn x)).getD C.output false
          conv_rhs => rw [← List.take_append_drop m C.gates, hrunW_append]
          symm
          apply hrunW_pref
          rw [hrunW_len, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
          dsimp only [m]; omega
        have hC'sep : degSep C' := by
          refine ⟨fun w p hpw => ?_, fun X Y hmf hdeg => ?_⟩
          · rw [hincIn]; change circuitFun 26 C' _ = true; rw [hC'eq]
            have := hCsep.1 w p hpw; rwa [hincIn] at this
          · rw [hincIn]; change circuitFun 26 C' _ = false; rw [hC'eq]
            have := hCsep.2 X Y hmf hdeg; rwa [hincIn] at this
        have hmin' := hCmin C' hC'mono hC'sep
        have hC'sz : C'.size = m := by
          change (C.gates.take m).length = m
          rw [List.length_take, Nat.min_eq_left (by omega)]
        omega
      let delIdx (k w : ℕ) : ℕ := if w < 26 + k then w else w - 1
      have hdel_step : ∀ (k : ℕ) (hk : k < C.size) (P : ℕ → Prop) (hPk : ¬ P (26 + k)) (f : Gate → Gate),
          (∀ (x : Fin 26 → Bool) (r : ℕ) (hr : r < (C.gates.drop (k + 1)).length)
            (w1 w2 : List Bool),
            w1.length = 26 + k + r → w2.length = 26 + k + 1 + r →
            (∀ i < 26 + k + 1 + r, P i → w1.getD (delIdx k i) false = w2.getD i false) →
            w2 = runW (C.gates.take (k + 1 + r)) (List.ofFn x) →
            P (26 + k + 1 + r) →
            (f ((C.gates.drop (k + 1))[r])).op.eval ((f ((C.gates.drop (k + 1))[r])).inputs.map fun a => w1.getD a false) =
            ((C.gates.drop (k + 1))[r]).op.eval (((C.gates.drop (k + 1))[r]).inputs.map fun a => w2.getD a false)) →
          ∀ (x : Fin 26 → Bool) (i : ℕ), i < 26 + C.size → P i →
          ((⟨C.gates.take k ++ (C.gates.drop (k + 1)).map f, 0⟩ : Circuit).wires (List.ofFn x)).getD (delIdx k i) false =
          (C.wires (List.ofFn x)).getD i false := by
        intro k hk P hPk f hstep x
        let pref := C.gates.take k
        let suff := C.gates.drop (k + 1)
        have hpref_len : pref.length = k := by
          simp [pref, List.length_take]; omega
        have hsuff_len : suff.length = C.size - (k + 1) := by
          simp [suff, hCircuit_size]
        have hsplit : ∀ r ≤ suff.length,
            C.gates.take (k + 1 + r) = pref ++ [C.gates[k]] ++ suff.take r := by
          intro r hr
          have h1 : C.gates.take (k + 1) = pref ++ [C.gates[k]] := List.take_succ_eq_append_getElem hk
          rw [← h1]
          conv_lhs => rw [← List.take_append_drop (k + 1) C.gates]
          rw [List.take_append, List.take_take, Nat.min_eq_right (by omega)]
          congr 2
          rw [List.length_take, Nat.min_eq_left (by omega)]
          omega
        have hind : ∀ r ≤ suff.length, ∀ i < 26 + k + 1 + r, P i →
            (runW (pref ++ (suff.take r).map f) (List.ofFn x)).getD (delIdx k i) false =
            (runW (C.gates.take (k + 1 + r)) (List.ofFn x)).getD i false := by
          intro r
          induction r with
          | zero =>
            intro _ i hi hPi
            simp only [Nat.add_zero, List.take_zero, List.map_nil, List.append_nil]
            rw [hsplit 0 (Nat.zero_le _), List.take_zero, List.append_nil, hrunW_append]
            have hlt : i < 26 + k := by
              by_contra hge
              have heq : i = 26 + k := by omega
              subst heq
              exact hPk hPi
            have hdi : delIdx k i = i := if_pos hlt
            rw [hdi]
            symm
            exact hrunW_pref [C.gates[k]] _ i (by rw [hrunW_len, List.length_ofFn, hpref_len]; exact hlt)
          | succ r ih =>
            intro hr i hi hPi
            have hrlt : r < suff.length := by omega
            have htake1 : suff.take (r + 1) = suff.take r ++ [suff[r]] :=
              List.take_succ_eq_append_getElem hrlt
            have htake2 : C.gates.take (k + 1 + (r + 1)) = C.gates.take (k + 1 + r) ++ [suff[r]] := by
              rw [hsplit (r + 1) hr, hsplit r (by omega), htake1]
              simp only [List.append_assoc]
            conv_lhs => rw [htake1, List.map_append, ← List.append_assoc, hrunW_append]
            conv_rhs => rw [htake2, hrunW_append]
            set w1 := runW (pref ++ (suff.take r).map f) (List.ofFn x)
            set w2 := runW (C.gates.take (k + 1 + r)) (List.ofFn x)
            have hw1 : w1.length = 26 + k + r := by
              change (runW _ _).length = _
              rw [hrunW_len, List.length_ofFn, List.length_append, hpref_len, List.length_map,
                List.length_take, Nat.min_eq_left (by omega)]
              omega
            have hw2 : w2.length = 26 + k + 1 + r := by
              change (runW _ _).length = _
              rw [hrunW_len, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
              omega
            change (stepW w1 (f suff[r])).getD (delIdx k i) false = (stepW w2 suff[r]).getD i false
            dsimp only [stepW]
            by_cases hlt : i < 26 + k + 1 + r
            · have hdi : delIdx k i < 26 + k + r := by
                dsimp only [delIdx]
                split_ifs <;> omega
              rw [hsnoc_lt w1 _ false (delIdx k i) (by omega), hsnoc_lt w2 _ false i (by omega)]
              exact ih (by omega) i hlt hPi
            · have heq : i = 26 + k + 1 + r := by omega
              subst heq
              have hdi : delIdx k (26 + k + 1 + r) = 26 + k + r := by
                dsimp only [delIdx]; split_ifs <;> omega
              rw [hdi, ← hw1, hsnoc_eq w1 _ false, ← hw2, hsnoc_eq w2 _ false]
              exact hstep x r hrlt w1 w2 hw1 hw2 (ih (by omega)) rfl hPi
        intro i hi hPi
        have hfull1 : suff.take suff.length = suff := List.take_length
        have hfull2 : C.gates.take (k + 1 + suff.length) = C.gates := by
          rw [List.take_of_length_le]; change C.size ≤ _; omega
        have hres := hind suff.length le_rfl i (by omega) hPi
        rw [hfull1, hfull2] at hres
        exact hres
      have hdel_contra : ∀ (k : ℕ) (hk : k < C.size) (f : Gate → Gate) (out' : ℕ),
          (∀ g ∈ C.gates, (f g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (f g).inputs.length ≤ 2) →
          (∀ x : Fin 26 → Bool,
            circuitFun 26 ⟨C.gates.take k ++ (C.gates.drop (k + 1)).map f, out'⟩ x = circuitFun 26 C x) →
          False := by
        intro k hk f out' hfmono heq
        let C' : Circuit := ⟨C.gates.take k ++ (C.gates.drop (k + 1)).map f, out'⟩
        have hm' : Monotone2 C' := by
          intro g hg
          rw [List.mem_append] at hg
          rcases hg with h1 | h2
          · exact hCmono g (List.mem_of_mem_take h1)
          · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h2
            exact hfmono g0 (List.mem_of_mem_drop hg0)
        have hs' : degSep C' := by
          refine ⟨fun w p hpw => ?_, fun X Y hmf hdeg => ?_⟩
          · rw [hincIn]; change circuitFun 26 C' _ = true; rw [heq]
            have := hCsep.1 w p hpw; rwa [hincIn] at this
          · rw [hincIn]; change circuitFun 26 C' _ = false; rw [heq]
            have := hCsep.2 X Y hmf hdeg; rwa [hincIn] at this
        have hmin' := hCmin C' hm' hs'
        have hsz' : C'.size = C.size - 1 := by
          change (C.gates.take k ++ (C.gates.drop (k + 1)).map f).length = C.size - 1
          rw [List.length_append, List.length_take, List.length_map, List.length_drop, Nat.min_eq_left (by omega)]
          change k + (C.size - (k + 1)) = C.size - 1
          omega
        omega
      have hpref_val : ∀ (m : ℕ) (hm : m ≤ C.size) (x : Fin 26 → Bool) (i : ℕ) (hi : i < 26 + m),
          (runW (C.gates.take m) (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false := by
        intro m hm x i hi
        change _ = (runW C.gates (List.ofFn x)).getD i false
        conv_rhs => rw [← List.take_append_drop m C.gates, hrunW_append]
        symm
        apply hrunW_pref
        rw [hrunW_len, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
        exact hi
      have hgate_eval : ∀ (k : ℕ) (hk : k < C.size) (x : Fin 26 → Bool),
          (C.wires (List.ofFn x)).getD (26 + k) false =
          (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun a => (runW (C.gates.take k) (List.ofFn x)).getD a false) := by
        intro k hk x
        rw [← hpref_val (k + 1) (by omega) x (26 + k) (by omega)]
        rw [List.take_succ_eq_append_getElem hk, hrunW_append]
        simp only [runW, List.foldl_cons, List.foldl_nil, stepW]
        have hl : (runW (C.gates.take k) (List.ofFn x)).length = 26 + k := by
          rw [hrunW_len, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
        rw [← hl, hsnoc_eq]
      have hno_copy : ∀ (k a : ℕ), k < C.size → a < 26 + k →
          (∀ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = (C.wires (List.ofFn x)).getD a false) →
          False := by
        intro k a hk ha hcopy
        let f (g : Gate) : Gate := ⟨g.op, g.inputs.map fun w => if w = 26 + k then a else delIdx k w⟩
        let out' := if C.output = 26 + k then a else delIdx k C.output
        have hstep_res := hdel_step k hk (fun i => i ≠ 26 + k) (by simp) f (by
          intro x r hr w1 w2 hw1 hw2 hih hw2eq _
          dsimp only [f]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro w _
          dsimp only [Function.comp]
          split_ifs with hwk
          · subst hwk
            have hda : delIdx k a = a := if_pos ha
            have h1 := hih a (by omega) (by omega)
            rw [hda] at h1
            rw [h1, hw2eq, hpref_val (k + 1 + r) (by simp at hr; omega) x a (by omega),
              ← hcopy x, ← hpref_val (k + 1 + r) (by simp at hr; omega) x (26 + k) (by omega)]
          · by_cases hlt : w < 26 + k + 1 + r
            · exact hih w hlt hwk
            · have hdge : 26 + k + r ≤ delIdx k w := by dsimp only [delIdx]; split_ifs <;> omega
              rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)])
        apply hdel_contra k hk f out'
        · intro g hg
          obtain ⟨k1, k2⟩ := hCmono g hg
          exact ⟨k1, by simpa [f] using k2⟩
        · intro x
          dsimp only [circuitFun, Circuit.eval, out']
          split_ifs with ho
          · have hda : delIdx k a = a := if_pos ha
            have h1 := hstep_res x a (by omega) (by omega)
            rw [hda] at h1
            exact h1.trans ((hcopy x).symm.trans (by rw [ho]))
          · exact hstep_res x C.output hCout_lt ho
      have hno_const_gate : ∀ (k : ℕ) (b : Bool), k < C.size →
          (∀ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + k) false = b) →
          False := by
        intro k b hk hconst
        have hne_out : C.output ≠ 26 + k := by
          intro ho
          exact hnoConst b fun x => by
            dsimp only [circuitFun, Circuit.eval]
            rw [ho]
            exact hconst x
        let f (g : Gate) : Gate :=
          GateOp.casesOn g.op
            (if b = false then
              if 26 + k ∈ g.inputs then ⟨GateOp.or, []⟩ else ⟨GateOp.and, g.inputs.map (delIdx k)⟩
            else ⟨GateOp.and, (g.inputs.filter fun w => decide (w ≠ 26 + k)).map (delIdx k)⟩)
            (if b = true then
              if 26 + k ∈ g.inputs then ⟨GateOp.and, []⟩ else ⟨GateOp.or, g.inputs.map (delIdx k)⟩
            else ⟨GateOp.or, (g.inputs.filter fun w => decide (w ≠ 26 + k)).map (delIdx k)⟩)
            ⟨GateOp.not, g.inputs.map (delIdx k)⟩
            (fun m => ⟨GateOp.mod m, g.inputs.map (delIdx k)⟩)
            ⟨GateOp.maj, g.inputs.map (delIdx k)⟩
        have hstep_res := hdel_step k hk (fun i => i ≠ 26 + k) (by simp) f (by
          intro x r hr w1 w2 hw1 hw2 hih hw2eq _
          have hmem : (C.gates.drop (k + 1))[r] ∈ C.gates := List.mem_of_mem_drop (List.getElem_mem hr)
          have hgm := hCmono _ hmem
          have hop : ((C.gates.drop (k + 1))[r]).op = .and ∨ ((C.gates.drop (k + 1))[r]).op = .or := by
            simpa using hgm.1
          have hw2k : w2.getD (26 + k) false = b := by
            rw [hw2eq, hpref_val (k + 1 + r) (by simp at hr; omega) x (26 + k) (by omega)]
            exact hconst x
          have hmatch : ∀ w, w ≠ 26 + k → w1.getD (delIdx k w) false = w2.getD w false := by
            intro w hne
            by_cases hlt : w < 26 + k + 1 + r
            · exact hih w hlt hne
            · have hdge : 26 + k + r ≤ delIdx k w := by dsimp only [delIdx]; split_ifs <;> omega
              rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
          set g := (C.gates.drop (k + 1))[r]
          rcases hop with h | h
          · cases b with
            | false =>
              dsimp only [f]
              rw [h]
              simp only [↓reduceIte]
              split_ifs with hin
              · simp only [hGateOp_and, hGateOp_or, List.map_nil, List.any_nil]
                symm
                rw [List.all_eq_false]
                exact ⟨false, List.mem_map.mpr ⟨26 + k, hin, hw2k⟩, by simp⟩
              · simp only [hGateOp_and, hGateOp_or, List.map_map]
                congr 1
                apply List.map_congr_left
                intro w hw
                exact hmatch w (fun heq => hin (heq ▸ hw))
            | true =>
              dsimp only [f]
              rw [h]
              simp only [Bool.true_eq_false, ↓reduceIte, hGateOp_and, hGateOp_or, List.map_map]
              have hfilt_all : ∀ l : List ℕ,
                  ((l.filter fun w => decide (w ≠ 26 + k)).map fun w => w1.getD (delIdx k w) false).all id =
                  (l.map fun w => w2.getD w false).all id := by
                intro l
                induction l with
                | nil => rfl
                | cons u t ihl =>
                  simp only [List.filter_cons, List.map_cons, List.all_cons, id_eq]
                  by_cases hu : u = 26 + k
                  · subst hu
                    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
                      hw2k, Bool.true_and, ihl]
                  · simp only [ne_eq, hu, not_false_eq_true, decide_true, ↓reduceIte,
                      List.map_cons, List.all_cons, id_eq, hmatch u hu, ihl]
              exact hfilt_all g.inputs
          · cases b with
            | true =>
              dsimp only [f]
              rw [h]
              simp only [↓reduceIte]
              split_ifs with hin
              · simp only [hGateOp_and, hGateOp_or, List.map_nil, List.all_nil]
                symm
                rw [List.any_eq_true]
                exact ⟨true, List.mem_map.mpr ⟨26 + k, hin, hw2k⟩, rfl⟩
              · simp only [hGateOp_and, hGateOp_or, List.map_map]
                congr 1
                apply List.map_congr_left
                intro w hw
                exact hmatch w (fun heq => hin (heq ▸ hw))
            | false =>
              dsimp only [f]
              rw [h]
              simp only [Bool.false_eq_true, ↓reduceIte, hGateOp_and, hGateOp_or, List.map_map]
              have hfilt_any : ∀ l : List ℕ,
                  ((l.filter fun w => decide (w ≠ 26 + k)).map fun w => w1.getD (delIdx k w) false).any id =
                  (l.map fun w => w2.getD w false).any id := by
                intro l
                induction l with
                | nil => rfl
                | cons u t ihl =>
                  simp only [List.filter_cons, List.map_cons, List.any_cons, id_eq]
                  by_cases hu : u = 26 + k
                  · subst hu
                    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
                      hw2k, Bool.false_or, ihl]
                  · simp only [ne_eq, hu, not_false_eq_true, decide_true, ↓reduceIte,
                      List.map_cons, List.any_cons, id_eq, hmatch u hu, ihl]
              exact hfilt_any g.inputs)
        apply hdel_contra k hk f (delIdx k C.output)
        · intro g hg
          obtain ⟨k1, k2⟩ := hCmono g hg
          have hop : g.op = .and ∨ g.op = .or := by simpa using k1
          rcases hop with h | h <;> dsimp only [f] <;> rw [h] <;> dsimp only
          · split_ifs <;> refine ⟨by simp, ?_⟩
            · simp
            · simpa using k2
            · calc ((g.inputs.filter _).map _).length = (g.inputs.filter _).length := List.length_map _
                _ ≤ g.inputs.length := List.length_filter_le _ _
                _ ≤ 2 := k2
          · split_ifs <;> refine ⟨by simp, ?_⟩
            · simp
            · simpa using k2
            · calc ((g.inputs.filter _).map _).length = (g.inputs.filter _).length := List.length_map _
                _ ≤ g.inputs.length := List.length_filter_le _ _
                _ ≤ 2 := k2
        · intro x
          exact hstep_res x C.output hCout_lt hne_out
      have hcone_spec : ∀ (gs : List Gate),
          (gs.foldl (coneStep 26) []).length = gs.length ∧
          ∀ j (hj : j < gs.length) i,
            (i ∈ (gs.foldl (coneStep 26) []).getD j [] ↔
              ∃ w ∈ gs[j].inputs, 26 ≤ w ∧ w < 26 + j ∧
                (i = w - 26 ∨ i ∈ (gs.foldl (coneStep 26) []).getD (w - 26) [])) ∧
            (i ∈ (gs.foldl (coneStep 26) []).getD j [] → i < j) := by
        intro gs
        induction gs using List.reverseRecOn with
        | nil => simp
        | append_singleton gs g ih =>
          obtain ⟨hlen, hspec⟩ := ih
          rw [List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          set acc := gs.foldl (coneStep 26) []
          have hlen' : (coneStep 26 acc g).length = (gs ++ [g]).length := by
            simp [hconeStep_def, hlen]
          refine ⟨hlen', ?_⟩
          intro j hj i
          have hlen_app : (gs ++ [g]).length = gs.length + 1 := by simp
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hlen_app ▸ hj)) with hlt | rfl
          · have hacc_j : (coneStep 26 acc g).getD j [] = acc.getD j [] :=
              hsnoc_lt acc _ [] j (by omega)
            rw [hacc_j, List.getElem_append_left hlt]
            refine ⟨?_, (hspec j hlt i).2⟩
            rw [(hspec j hlt i).1]
            constructor
            · rintro ⟨w, hw, h26, hltw, hor⟩
              refine ⟨w, hw, h26, hltw, ?_⟩
              rcases hor with rfl | hmem
              · exact Or.inl rfl
              · exact Or.inr (by rw [hconeStep_def]; rwa [hsnoc_lt acc _ [] (w - 26) (by omega)])
            · rintro ⟨w, hw, h26, hltw, hor⟩
              refine ⟨w, hw, h26, hltw, ?_⟩
              rcases hor with rfl | hmem
              · exact Or.inl rfl
              · exact Or.inr (by rw [hconeStep_def] at hmem; rwa [hsnoc_lt acc _ [] (w - 26) (by omega)] at hmem)
          · have hacc_j : (coneStep 26 acc g).getD gs.length [] =
                (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + acc.length))).flatMap
                  (fun w => (w - 26) :: acc.getD (w - 26) []) := by
              rw [hconeStep_def]
              rw [← hlen, hsnoc_eq acc _ []]
            have hg_j : (gs ++ [g])[gs.length] = g := by simp
            rw [hacc_j, hg_j]
            have hiff : i ∈ (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + acc.length))).flatMap
                (fun w => (w - 26) :: acc.getD (w - 26) []) ↔
                ∃ w ∈ g.inputs, 26 ≤ w ∧ w < 26 + gs.length ∧
                  (i = w - 26 ∨ i ∈ (coneStep 26 acc g).getD (w - 26) []) := by
              simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons, hlen]
              constructor
              · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hor⟩
                refine ⟨w, hw1, hw2, hw3, ?_⟩
                rcases hor with rfl | hmem
                · exact Or.inl rfl
                · exact Or.inr (by rw [hconeStep_def]; rwa [hsnoc_lt acc _ [] (w - 26) (by omega)])
              · rintro ⟨w, hw1, hw2, hw3, hor⟩
                refine ⟨w, ⟨hw1, hw2, hw3⟩, ?_⟩
                rcases hor with rfl | hmem
                · exact Or.inl rfl
                · exact Or.inr (by rw [hconeStep_def] at hmem; rwa [hsnoc_lt acc _ [] (w - 26) (by omega)] at hmem)
            refine ⟨hiff, ?_⟩
            intro hi
            obtain ⟨w, _, h26, hltw, hor⟩ := hiff.mp hi
            rcases hor with rfl | hmem
            · omega
            · rw [hconeStep_def] at hmem
              rw [hsnoc_lt acc _ [] (w - 26) (by omega)] at hmem
              have := (hspec (w - 26) (by omega) i).2 hmem
              omega
      have hcone_trans : ∀ o < C.size, ∀ i j, InCone 26 C i j → InCone 26 C j o → InCone 26 C i o := by
        intro o
        induction o using Nat.strong_induction_on with
        | ind o ih =>
          intro ho i j hij hjo
          have hsp := (hcone_spec C.gates).2 o ho
          obtain ⟨w, hw, h26, hltw, hor⟩ := (hsp j).1.mp hjo
          apply (hsp i).1.mpr
          refine ⟨w, hw, h26, hltw, Or.inr ?_⟩
          rcases hor with rfl | hmem
          · exact hij
          · exact ih (w - 26) (by omega) (by omega) i j hij hmem
      have hC_live : liveSize 26 C = C.size := by
        rw [hliveSize_def]
        have hsub : liveGates 26 C ⊆ Finset.range C.size := Finset.filter_subset _ _
        by_contra hne
        have hlt : (liveGates 26 C).card < (Finset.range C.size).card := by
          have hle := Finset.card_le_card hsub
          rw [Finset.card_range] at hle ⊢
          omega
        have hex : ∃ k ∈ Finset.range C.size, k ∉ liveGates 26 C := by
          by_contra hno
          have hsub2 : Finset.range C.size ⊆ liveGates 26 C := fun k hk => by
            by_contra hn; exact hno ⟨k, hk, hn⟩
          have hle2 := Finset.card_le_card hsub2
          omega
        obtain ⟨k, hkmem, hknlive⟩ := hex
        have hk : k < C.size := Finset.mem_range.mp hkmem
        let P (i : ℕ) : Prop := i < 26 ∨ i - 26 ∈ liveGates 26 C
        have hPk : ¬ P (26 + k) := by
          rintro (h1 | h2)
          · omega
          · exact hknlive (by simpa using h2)
        have hPout : P C.output := by
          right
          simp only [hliveGates_def, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hCout_ge, Or.inl trivial⟩
        let f (g : Gate) : Gate := ⟨g.op, g.inputs.map fun w => if w = 26 + k then 0 else delIdx k w⟩
        have hstep_res := hdel_step k hk P hPk f (by
          intro x r hr w1 w2 hw1 hw2 hih _ hPj
          dsimp only [f]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro w hw
          dsimp only [Function.comp]
          have hj_live : k + 1 + r ∈ liveGates 26 C := by
            rcases hPj with h1 | h2
            · omega
            · have heq : 26 + k + 1 + r - 26 = k + 1 + r := by omega
              rwa [heq] at h2
          have hj_lt : k + 1 + r < C.size := (Finset.mem_range.mp (Finset.mem_filter.mp hj_live).1)
          have hw_eq : (C.gates.drop (k + 1))[r] = C.gates[k + 1 + r] := List.getElem_drop
          rw [hw_eq] at hw
          by_cases hltw : w < 26 + k + 1 + r
          · have hPw : P w := by
              by_cases h26 : w < 26
              · exact Or.inl h26
              · right
                simp only [hliveGates_def, Finset.mem_filter, Finset.mem_range] at hj_live ⊢
                refine ⟨by omega, hCout_ge, Or.inr ?_⟩
                have hwin : InCone 26 C (w - 26) (k + 1 + r) := by
                  exact ((hcone_spec C.gates).2 (k + 1 + r) hj_lt (w - 26)).1.mpr
                    ⟨w, hw, by omega, by omega, Or.inl rfl⟩
                rcases hj_live.2.2 with heq | hinc
                · rw [← heq]; exact hwin
                · exact hcone_trans (C.output - 26) (by omega) (w - 26) (k + 1 + r) hwin hinc
            have hne : w ≠ 26 + k := fun heq => hPk (heq ▸ hPw)
            rw [if_neg hne]
            exact hih w hltw hPw
          · have hne : w ≠ 26 + k := by omega
            rw [if_neg hne]
            have hdge : 26 + k + r ≤ delIdx k w := by dsimp only [delIdx]; split_ifs <;> omega
            rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)])
        apply hdel_contra k hk f (delIdx k C.output)
        · intro g hg
          obtain ⟨k1, k2⟩ := hCmono g hg
          exact ⟨k1, by simpa [f] using k2⟩
        · intro x
          exact hstep_res x C.output hCout_lt hPout
      have hC_clean : IsAO2 26 C ∧ ∀ j < C.size, opnd C j 0 ≠ opnd C j 1 := by
        have hgate_ok : ∀ k (hk : k < C.size),
            ∃ a b : ℕ, C.gates[k].inputs = [a, b] ∧ a ≠ b ∧ a < 26 + k ∧ b < 26 + k := by
          intro k hk
          have hgm := hCmono (C.gates[k]) (List.getElem_mem hk)
          have hop : C.gates[k].op = .and ∨ C.gates[k].op = .or := by simpa using hgm.1
          cases hin : C.gates[k].inputs with
          | nil =>
            exfalso
            rcases hop with h | h
            · exact hno_const_gate k true hk fun x => by rw [hgate_eval k hk x, hin, h]; rfl
            · exact hno_const_gate k false hk fun x => by rw [hgate_eval k hk x, hin, h]; rfl
          | cons a t =>
            cases t with
            | nil =>
              exfalso
              by_cases ha : a < 26 + k
              · exact hno_copy k a hk ha fun x => by
                  rw [hgate_eval k hk x, hin]
                  have hv := hpref_val k (by omega) x a ha
                  rcases hop with h | h <;> rw [h]
                  · simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                      id_eq, Bool.and_true, hv]
                  · simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                      id_eq, Bool.or_false, hv]
              · exact hno_const_gate k false hk fun x => by
                  rw [hgate_eval k hk x, hin]
                  have hd : (runW (C.gates.take k) (List.ofFn x)).getD a false = false := by
                    apply List.getD_eq_default
                    rw [hrunW_len, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
                    omega
                  rcases hop with h | h <;> rw [h]
                  · simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                      id_eq, Bool.and_true, hd]
                  · simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                      id_eq, Bool.or_false, hd]
            | cons b r =>
              cases r with
              | nil =>
                have ha : a < 26 + k := by
                  by_contra hge
                  have hd : ∀ x : Fin 26 → Bool, (runW (C.gates.take k) (List.ofFn x)).getD a false = false := by
                    intro x
                    apply List.getD_eq_default
                    rw [hrunW_len, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
                    omega
                  rcases hop with h | h
                  · exact hno_const_gate k false hk fun x => by
                      rw [hgate_eval k hk x, hin, h]
                      simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                        id_eq, hd x, Bool.false_and]
                  · by_cases hb : b < 26 + k
                    · exact hno_copy k b hk hb fun x => by
                        rw [hgate_eval k hk x, hin, h]
                        simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                          id_eq, hd x, Bool.false_or, Bool.or_false, hpref_val k (by omega) x b hb]
                    · exact hno_const_gate k false hk fun x => by
                        rw [hgate_eval k hk x, hin, h]
                        have hdb : (runW (C.gates.take k) (List.ofFn x)).getD b false = false := by
                          apply List.getD_eq_default
                          rw [hrunW_len, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
                          omega
                        simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                          id_eq, hd x, hdb, Bool.or_false]
                have hb : b < 26 + k := by
                  by_contra hge
                  have hd : ∀ x : Fin 26 → Bool, (runW (C.gates.take k) (List.ofFn x)).getD b false = false := by
                    intro x
                    apply List.getD_eq_default
                    rw [hrunW_len, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
                    omega
                  rcases hop with h | h
                  · exact hno_const_gate k false hk fun x => by
                      rw [hgate_eval k hk x, hin, h]
                      simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                        id_eq, hd x, Bool.and_true, Bool.and_false]
                  · exact hno_copy k a hk ha fun x => by
                      rw [hgate_eval k hk x, hin, h]
                      simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                        id_eq, hd x, Bool.or_false, hpref_val k (by omega) x a ha]
                have hab : a ≠ b := by
                  intro heq
                  subst heq
                  exact hno_copy k a hk ha fun x => by
                    rw [hgate_eval k hk x, hin]
                    have hv := hpref_val k (by omega) x a ha
                    rcases hop with h | h <;> rw [h]
                    · simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                        id_eq, Bool.and_true, Bool.and_self, hv]
                    · simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                        id_eq, Bool.or_false, Bool.or_self, hv]
                exact ⟨a, b, rfl, hab, ha, hb⟩
              | cons c rest =>
                have hl := hgm.2
                rw [hin] at hl
                simp at hl
        refine ⟨⟨fun g hg => by simpa using (hCmono g hg).1, ?_, ?_⟩, ?_⟩
        · intro j hj i hi
          obtain ⟨a, b, hab, _, ha, hb⟩ := hgate_ok j hj
          have hga : gateAt C j = C.gates[j] := by unfold gateAt; exact List.getD_eq_getElem _ _ hj
          rw [hga, hab] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> assumption
        · intro g hg
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
          obtain ⟨a, b, hab, _, _, _⟩ := hgate_ok j hj
          simp [hab]
        · intro j hj
          obtain ⟨a, b, hab, hne, _, _⟩ := hgate_ok j hj
          unfold opnd
          have hga : gateAt C j = C.gates[j] := by unfold gateAt; exact List.getD_eq_getElem _ _ hj
          rw [hga, hab]
          simpa using hne
      have hdeg_witness : ∀ (D : Circuit), Monotone2 D →
          ∀ (x : Fin 26 → Bool) (i : ℕ), (D.wires (List.ofFn x)).getD i false = true →
          ∃ B : Finset (Fin 13), B.card ≤ (D.lineDegrees 26 (Finset.Ico 13 26)).getD i 0 ∧
            (∀ l ∈ B, x (Fin.natAdd 13 l) = true) ∧
            (D.wires (List.ofFn (fun k : Fin 26 =>
              Fin.addCases (fun p => x (Fin.castAdd 13 p)) (fun l => decide (l ∈ B)) k))).getD i false = true := by
        intro D hDm x
        let restr (B : Finset (Fin 13)) : Fin 26 → Bool :=
          fun k => Fin.addCases (fun p => x (Fin.castAdd 13 p)) (fun l => decide (l ∈ B)) k
        have hgen : ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
            ∀ i : ℕ, (runW gs (List.ofFn x)).getD i false = true →
            ∃ B : Finset (Fin 13),
              B.card ≤ (gs.foldl (fun d g => d ++ [g.lineDegree d])
                ((List.range 26).map fun k => if k ∈ Finset.Ico 13 26 then 1 else 0)).getD i 0 ∧
              (∀ l ∈ B, x (Fin.natAdd 13 l) = true) ∧
              (runW gs (List.ofFn (restr B))).getD i false = true := by
          intro gs
          induction gs using List.reverseRecOn with
          | nil =>
            intro _ i hi
            by_cases h26 : i < 26
            · have hxi : x ⟨i, h26⟩ = true := by
                simp only [runW, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn, h26,
                  dite_true, Option.getD_some] at hi
                exact hi
              by_cases h13 : i < 13
              · refine ⟨∅, by simp, by simp, ?_⟩
                have hcast : (⟨i, h26⟩ : Fin 26) = Fin.castAdd 13 ⟨i, h13⟩ := by apply Fin.ext; rfl
                simp only [runW, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn, h26,
                  dite_true, Option.getD_some, restr, hcast, Fin.addCases_left]
                exact hxi
              · let l0 : Fin 13 := ⟨i - 13, by omega⟩
                have hnat : (⟨i, h26⟩ : Fin 26) = Fin.natAdd 13 l0 := by apply Fin.ext; simp [l0]; omega
                have hdeg1 : (((List.range 26).map fun k => if k ∈ Finset.Ico 13 26 then 1 else 0)).getD i 0 = 1 := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h26]
                  simp only [Option.map_some, Option.getD_some, Finset.mem_Ico]
                  rw [if_pos (by omega)]
                refine ⟨{l0}, ?_, ?_, ?_⟩
                · rw [Finset.card_singleton]; change 1 ≤ (((List.range 26).map _).getD i 0); rw [hdeg1]
                · intro l hl; rw [Finset.mem_singleton.mp hl, ← hnat]; exact hxi
                · simp only [runW, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn, h26,
                    dite_true, Option.getD_some, restr, hnat, Fin.addCases_right, Finset.mem_singleton_self,
                    decide_true]
            · change (List.ofFn x).getD i false = true at hi
              rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hi
              exact Bool.noConfusion hi
          | append_singleton gs g ih =>
            intro hgs i hi
            have hgs' : ∀ u ∈ gs, u.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ u.inputs.length ≤ 2 :=
              fun u hu => hgs u (by simp [hu])
            have hg := hgs g (by simp)
            have hop : g.op = .and ∨ g.op = .or := by simpa using hg.1
            set w0 := runW gs (List.ofFn x)
            have hlenW : w0.length = 26 + gs.length := by
              change (runW gs (List.ofFn x)).length = _
              rw [hrunW_len, List.length_ofFn]
            have hlenD : (gs.foldl (fun d g => d ++ [g.lineDegree d])
                ((List.range 26).map fun k => if k ∈ Finset.Ico 13 26 then 1 else 0)).length = 26 + gs.length := by
              rw [hfold_len]; simp
            rw [hrunW_append] at hi
            change (w0 ++ [g.op.eval (g.inputs.map fun a => w0.getD a false)]).getD i false = true at hi
            rcases Nat.lt_trichotomy i (26 + gs.length) with hlt | heq | hgt
            · rw [hsnoc_lt w0 _ false i (by omega)] at hi
              obtain ⟨B, hBc, hBx, hBw⟩ := ih hgs' i hi
              refine ⟨B, ?_, hBx, ?_⟩
              · rw [List.foldl_append]
                simp only [List.foldl_cons, List.foldl_nil]
                rw [hsnoc_lt _ _ 0 i (by omega)]
                exact hBc
              · rw [hrunW_append]
                change (runW gs (List.ofFn (restr B)) ++ [_]).getD i false = true
                rw [hsnoc_lt _ _ false i (by rw [hrunW_len, List.length_ofFn]; exact hlt)]
                exact hBw
            · subst heq
              rw [← hlenW, hsnoc_eq w0 _ false] at hi
              set D0 := gs.foldl (fun d g => d ++ [g.lineDegree d])
                ((List.range 26).map fun k => if k ∈ Finset.Ico 13 26 then 1 else 0)
              have hdeg_g : ((gs ++ [g]).foldl (fun d g => d ++ [g.lineDegree d])
                  ((List.range 26).map fun k => if k ∈ Finset.Ico 13 26 then 1 else 0)).getD (26 + gs.length) 0 =
                  g.lineDegree D0 := by
                rw [List.foldl_append]
                simp only [List.foldl_cons, List.foldl_nil]
                rw [← hlenD, hsnoc_eq]
              rw [hdeg_g]
              have hval_g : ∀ B, (runW (gs ++ [g]) (List.ofFn (restr B))).getD (26 + gs.length) false =
                  g.op.eval (g.inputs.map fun a => (runW gs (List.ofFn (restr B))).getD a false) := by
                intro B
                rw [hrunW_append]
                change (runW gs (List.ofFn (restr B)) ++ [_]).getD (26 + gs.length) false = _
                have hlB : (runW gs (List.ofFn (restr B))).length = 26 + gs.length := by
                  rw [hrunW_len, List.length_ofFn]
                rw [← hlB, hsnoc_eq]
              rcases hop with hop | hop
              · rw [hop] at hi
                have hdeg_and : g.lineDegree D0 = (g.inputs.map fun a => D0.getD a 0).sum := by
                  delta Gate.lineDegree; rw [hop]; simp
                rw [hdeg_and]
                cases hin : g.inputs with
                | nil =>
                  refine ⟨∅, by simp, by simp, ?_⟩
                  rw [hval_g, hop, hin]; rfl
                | cons a t =>
                  cases t with
                  | nil =>
                    have ha : w0.getD a false = true := by
                      rw [hin] at hi
                      simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                        id_eq, Bool.and_true] at hi
                      exact hi
                    obtain ⟨B, hBc, hBx, hBw⟩ := ih hgs' a ha
                    refine ⟨B, by simpa [hin] using hBc, hBx, ?_⟩
                    rw [hval_g, hop, hin]
                    simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                      id_eq, Bool.and_true, hBw]
                  | cons b r =>
                    cases r with
                    | nil =>
                      have hab : w0.getD a false = true ∧ w0.getD b false = true := by
                        rw [hin] at hi
                        simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                          id_eq, Bool.and_true, Bool.and_eq_true] at hi
                        exact hi
                      obtain ⟨Ba, hBac, hBax, hBaw⟩ := ih hgs' a hab.1
                      obtain ⟨Bb, hBbc, hBbx, hBbw⟩ := ih hgs' b hab.2
                      refine ⟨Ba ∪ Bb, ?_, ?_, ?_⟩
                      · calc (Ba ∪ Bb).card ≤ Ba.card + Bb.card := Finset.card_union_le Ba Bb
                          _ ≤ D0.getD a 0 + D0.getD b 0 := Nat.add_le_add hBac hBbc
                          _ = ([a, b].map fun u => D0.getD u 0).sum := by simp
                      · intro l hl
                        rcases Finset.mem_union.mp hl with h1 | h2
                        · exact hBax l h1
                        · exact hBbx l h2
                      · rw [hval_g, hop, hin]
                        have hmgs : Monotone2 ⟨gs, 0⟩ := hgs'
                        have hlift : ∀ B1 B2 : Finset (Fin 13), B1 ⊆ B2 →
                            ∀ u, (runW gs (List.ofFn (restr B1))).getD u false = true →
                              (runW gs (List.ofFn (restr B2))).getD u false = true := by
                          intro B1 B2 hsub u hu
                          apply hmono_wires ⟨gs, 0⟩ hmgs (List.ofFn (restr B1)) (List.ofFn (restr B2)) (by simp) _ u hu
                          intro j hj
                          by_cases hj26 : j < 26
                          · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj26, dite_true,
                              Option.getD_some, restr] at hj ⊢
                            let jf : Fin 26 := ⟨j, hj26⟩
                            refine hsplit26 (P := fun k => restr B1 k = true → restr B2 k = true)
                              (fun p hp => by simpa only [restr, Fin.addCases_left] using hp)
                              (fun l hl => by
                                simp only [restr, Fin.addCases_right, decide_eq_true_eq] at hl ⊢
                                exact hsub hl) jf hj
                          · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hj
                            exact Bool.noConfusion hj
                        have ha' := hlift Ba (Ba ∪ Bb) Finset.subset_union_left a hBaw
                        have hb' := hlift Bb (Ba ∪ Bb) Finset.subset_union_right b hBbw
                        simp only [hGateOp_and, hGateOp_or, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                          id_eq, Bool.and_true, ha', hb']
                    | cons c rest =>
                      have hl := hg.2; rw [hin] at hl; simp at hl
              · rw [hop] at hi
                have hdeg_or : g.lineDegree D0 = (g.inputs.map fun a => D0.getD a 0).foldr max 0 := by
                  delta Gate.lineDegree; rw [hop]; simp
                rw [hdeg_or]
                simp only [hGateOp_and, hGateOp_or, List.any_eq_true, List.mem_map, id_eq] at hi
                obtain ⟨_, ⟨a, ha, rfl⟩, ha1⟩ := hi
                obtain ⟨B, hBc, hBx, hBw⟩ := ih hgs' a ha1
                have hle_max : ∀ (l : List ℕ) (u : ℕ), u ∈ l → u ≤ l.foldr max 0 := by
                  intro l u hu
                  induction l with
                  | nil => simp at hu
                  | cons v t ihl =>
                    simp only [List.mem_cons] at hu
                    simp only [List.foldr_cons]
                    rcases hu with rfl | ht
                    · exact le_max_left _ _
                    · exact (ihl ht).trans (le_max_right _ _)
                refine ⟨B, hBc.trans (hle_max _ _ (List.mem_map.mpr ⟨a, ha, rfl⟩)), hBx, ?_⟩
                rw [hval_g, hop]
                simp only [hGateOp_and, hGateOp_or, List.any_eq_true, List.mem_map, id_eq]
                exact ⟨true, ⟨a, ha, hBw⟩, rfl⟩
            · rw [hsnoc_gt w0 _ false i (by omega)] at hi
              exact Bool.noConfusion hi
        exact hgen D.gates hDm
      have hdeg2_exact : ∀ D : Circuit, Monotone2 D → degSep D →
          D.lineDeg 26 (Finset.Ico 13 26) ≤ 2 → ComputesIncidence S D := by
        intro D hDm hDsep hDd X Y
        by_cases hhit : incidenceFun S X Y = true
        · rw [hhit]
          unfold incidenceFun at hhit
          obtain ⟨p, hpX, w, hwY, hpw⟩ := of_decide_eq_true hhit
          have h1 := hDsep.1 w p hpw
          rw [hincIn {p} {w}] at h1
          rw [hincIn X Y]
          apply hmono_cfun D hDm _ _ _ h1
          intro k hk
          apply decide_eq_true
          rcases of_decide_eq_true hk with ⟨q, hq, rfl⟩ | ⟨u, hu, rfl⟩
          · rw [Finset.mem_singleton.mp hq]; exact Or.inl ⟨p, hpX, rfl⟩
          · rw [Finset.mem_singleton.mp hu]; exact Or.inr ⟨w, hwY, rfl⟩
        · have hf : incidenceFun S X Y = false := Bool.eq_false_iff.mpr hhit
          rw [hf]
          apply Bool.eq_false_iff.mpr
          intro htrue
          have hno_inc : ∀ p ∈ X, ∀ w ∈ Y, p ∉ S w := by
            intro p hpX w hwY hpw
            have : incidenceFun S X Y = true := decide_eq_true ⟨p, hpX, w, hwY, hpw⟩
            exact Bool.noConfusion (hf.symm.trans this)
          rw [hincIn X Y] at htrue
          obtain ⟨B, hBcard, hBY, hBeval⟩ := hdeg_witness D hDm _ D.output htrue
          have hBsubY : B ⊆ Y := by
            intro w hwB
            have h1 := hBY w hwB
            rcases of_decide_eq_true h1 with ⟨p, _, he⟩ | ⟨u, huY, he⟩
            · have h' := congrArg Fin.val he; simp at h'; have := p.isLt; omega
            · have heq : w = u := Fin.ext (by have h' := congrArg Fin.val he; simp at h'; omega)
              rwa [heq]
          have hB2 : B.card ≤ 2 := hBcard.trans hDd
          have hBeval_inc : D.eval (incidenceInput X B) = true := by
            rw [hincIn X B]
            apply hmono_cfun D hDm _ _ _ hBeval
            refine hsplit26 (fun p hk => ?_) (fun w hk => ?_)
            · apply decide_eq_true
              simp only [Fin.addCases_left, decide_eq_true_eq] at hk
              rcases hk with ⟨q, hqX, he⟩ | ⟨u, _, he⟩
              · exact Or.inl ⟨q, hqX, he⟩
              · have h' := congrArg Fin.val he; simp at h'; have := p.isLt; omega
            · apply decide_eq_true
              simp only [Fin.addCases_right, decide_eq_true_eq] at hk
              exact Or.inr ⟨w, hk, rfl⟩
          by_cases hB0 : B = ∅
          · subst hB0
            have hle : ∀ k : Fin 26,
                decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨ (∃ w ∈ (∅ : Finset (Fin 13)), k = Fin.natAdd 13 w)) = true →
                decide ((∃ p ∈ (Finset.univ : Finset (Fin 13)), k = Fin.castAdd 13 p) ∨
                  (∃ w ∈ (∅ : Finset (Fin 13)), k = Fin.natAdd 13 w)) = true := by
              intro k hk
              apply decide_eq_true
              rcases of_decide_eq_true hk with ⟨p, _, rfl⟩ | ⟨w, hw, _⟩
              · exact Or.inl ⟨p, Finset.mem_univ p, rfl⟩
              · simp at hw
            rw [hincIn X ∅] at hBeval_inc
            have h1 := hmono_cfun D hDm _ _ hle hBeval_inc
            have h2 := hDsep.2 Finset.univ ∅ hdeg_univ.1 (Or.inr hdeg_univ.2)
            rw [hincIn] at h2
            exact Bool.noConfusion (h1.symm.trans h2)
          · have hpair : ∃ w1 w2 : Fin 13, B = {w1, w2} := by
              obtain ⟨w1, hw1⟩ := Finset.nonempty_iff_ne_empty.mpr hB0
              by_cases hrest : B \ {w1} = ∅
              · refine ⟨w1, w1, ?_⟩
                ext u
                simp only [Finset.pair_eq_singleton, Finset.mem_singleton]
                constructor
                · intro hu
                  by_contra hne
                  have : u ∈ B \ {w1} := Finset.mem_sdiff.mpr ⟨hu, by simp [hne]⟩
                  rw [hrest] at this; simp at this
                · rintro rfl; exact hw1
              · obtain ⟨w2, hw2⟩ := Finset.nonempty_iff_ne_empty.mpr hrest
                have hw2B : w2 ∈ B := (Finset.mem_sdiff.mp hw2).1
                have hne12 : w2 ≠ w1 := by simpa using (Finset.mem_sdiff.mp hw2).2
                have hsub : ({w1, w2} : Finset (Fin 13)) ⊆ B := by
                  intro u hu
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
                  rcases hu with rfl | rfl <;> assumption
                have hc2 : ({w1, w2} : Finset (Fin 13)).card = 2 := Finset.card_pair hne12.symm
                exact ⟨w1, w2, (Finset.eq_of_subset_of_card_le hsub (by omega)).symm⟩
            obtain ⟨w1, w2, rfl⟩ := hpair
            have hXsub : X ⊆ zeroSet S {w1, w2} := by
              intro p hpX
              simp only [hzeroSet_def, Finset.mem_filter, Finset.mem_univ, true_and]
              intro w hw
              exact hno_inc p hpX w (hBsubY hw)
            have hle : ∀ k : Fin 26,
                decide ((∃ p ∈ X, k = Fin.castAdd 13 p) ∨ (∃ w ∈ ({w1, w2} : Finset (Fin 13)), k = Fin.natAdd 13 w)) = true →
                decide ((∃ p ∈ zeroSet S {w1, w2}, k = Fin.castAdd 13 p) ∨
                  (∃ w ∈ ({w1, w2} : Finset (Fin 13)), k = Fin.natAdd 13 w)) = true := by
              intro k hk
              apply decide_eq_true
              rcases of_decide_eq_true hk with ⟨p, hpX, rfl⟩ | ⟨w, hw, rfl⟩
              · exact Or.inl ⟨p, hXsub hpX, rfl⟩
              · exact Or.inr ⟨w, hw, rfl⟩
            rw [hincIn X {w1, w2}] at hBeval_inc
            have h1 := hmono_cfun D hDm _ _ hle hBeval_inc
            have h2 := hDsep.2 (zeroSet S {w1, w2}) {w1, w2} (hdeg_twoLine w1 w2).1 (Or.inr (hdeg_twoLine w1 w2).2)
            rw [hincIn] at h2
            exact Bool.noConfusion (h1.symm.trans h2)
      have hcoll_tri : ∀ p0 p1 p2 : Fin 13,
          (¬ ∃ w : Fin 13, p0 ∈ S w ∧ p1 ∈ S w ∧ p2 ∈ S w) →
          ∃ (τP τL : Fin 13 → Fin 13), Function.Bijective τP ∧ Function.Bijective τL ∧
            τP p0 = 0 ∧ τP p1 = 1 ∧ τP p2 = 2 ∧
            ∀ p w : Fin 13, τP p ∈ S (τL w) ↔ p ∈ S w := by
        intro p0 p1 p2 hnc
        let a := vs p0
        let b := vs p1
        let c := vs p2
        let d := dot3 a (cross3 b c)
        have hd : d ≠ 0 := by
          intro hd0
          by_cases hcab : cross3 a b = (0, 0, 0)
          · have hp01 : p0 = p1 := hvs_cross0 p0 p1 hcab
            obtain ⟨w, hw0, hw2⟩ := hS_twoPts p0 p2
            exact hnc ⟨w, hw0, hp01 ▸ hw0, hw2⟩
          · obtain ⟨w, k, hk0, hkw⟩ := hus_surj (cross3 a b).1 (cross3 a b).2.1 (cross3 a b).2.2 hcab
            have hda : dot3 (cross3 a b) a = 0 := by dsimp only [dot3, cross3]; ring
            have hdb : dot3 (cross3 a b) b = 0 := by dsimp only [dot3, cross3]; ring
            have hdc : dot3 (cross3 a b) c = 0 := by
              have : dot3 (cross3 a b) c = d := by dsimp only [d, dot3, cross3]; ring
              rw [this, hd0]
            have hsmul_dot : ∀ u v : ZMod 3 × ZMod 3 × ZMod 3, ∀ m : ZMod 3,
                dot3 (smul3 m u) v = m * dot3 u v := fun u v m => by dsimp only [dot3, smul3]; ring
            have hkill : ∀ v : ZMod 3 × ZMod 3 × ZMod 3, dot3 (cross3 a b) v = 0 → dot3 (us w) v = 0 := by
              intro v hv
              have h1 : k * dot3 (us w) v = 0 := by
                rw [← hsmul_dot, ← hkw]; exact hv
              calc dot3 (us w) v = (k * k) * dot3 (us w) v := by rw [hz3_sq k hk0, one_mul]
                _ = k * (k * dot3 (us w) v) := by ring
                _ = 0 := by rw [h1, mul_zero]
            have hp0w : p0 ∈ S w := (hincb p0 w).mpr (by rw [hdot_inc_b, decide_eq_true (hkill a hda)])
            have hp1w : p1 ∈ S w := (hincb p1 w).mpr (by rw [hdot_inc_b, decide_eq_true (hkill b hdb)])
            have hp2w : p2 ∈ S w := (hincb p2 w).mpr (by rw [hdot_inc_b, decide_eq_true (hkill c hdc)])
            exact hnc ⟨w, hp0w, hp1w, hp2w⟩
        let adjA (v : ZMod 3 × ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 × ZMod 3 :=
          (dot3 (cross3 b c) v, dot3 (cross3 c a) v, dot3 (cross3 a b) v)
        let atA (u : ZMod 3 × ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 × ZMod 3 :=
          (dot3 a u, dot3 b u, dot3 c u)
        let mulA (v : ZMod 3 × ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 × ZMod 3 :=
          (a.1 * v.1 + b.1 * v.2.1 + c.1 * v.2.2,
           a.2.1 * v.1 + b.2.1 * v.2.1 + c.2.1 * v.2.2,
           a.2.2 * v.1 + b.2.2 * v.2.1 + c.2.2 * v.2.2)
        let adjAT (u : ZMod 3 × ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 × ZMod 3 :=
          ((cross3 b c).1 * u.1 + (cross3 c a).1 * u.2.1 + (cross3 a b).1 * u.2.2,
           (cross3 b c).2.1 * u.1 + (cross3 c a).2.1 * u.2.1 + (cross3 a b).2.1 * u.2.2,
           (cross3 b c).2.2 * u.1 + (cross3 c a).2.2 * u.2.1 + (cross3 a b).2.2 * u.2.2)
        have hmulA_adj : ∀ v, mulA (adjA v) = smul3 d v := by
          intro v; apply Prod.ext
          · dsimp only [mulA, adjA, smul3, d, dot3, cross3]; ring
          · apply Prod.ext <;> (dsimp only [mulA, adjA, smul3, d, dot3, cross3]; ring)
        have hadjAT_at : ∀ u, adjAT (atA u) = smul3 d u := by
          intro u; apply Prod.ext
          · dsimp only [adjAT, atA, smul3, d, dot3, cross3]; ring
          · apply Prod.ext <;> (dsimp only [adjAT, atA, smul3, d, dot3, cross3]; ring)
        have hlagrange : ∀ u v, dot3 (atA u) (adjA v) = d * dot3 u v := by
          intro u v; dsimp only [atA, adjA, d, dot3, cross3]; ring
        have hsmul_cancel : ∀ k : ZMod 3, k ≠ 0 → ∀ v, smul3 k v = (0, 0, 0) → v = (0, 0, 0) := by
          intro k hk v hv
          have h1 : k * v.1 = 0 := congrArg Prod.fst hv
          have h2 : k * v.2.1 = 0 := congrArg (fun t => t.2.1) hv
          have h3 : k * v.2.2 = 0 := congrArg (fun t => t.2.2) hv
          apply Prod.ext
          · calc v.1 = (k * k) * v.1 := by rw [hz3_sq k hk, one_mul]
              _ = k * (k * v.1) := by ring
              _ = 0 := by rw [h1, mul_zero]
          · apply Prod.ext
            · calc v.2.1 = (k * k) * v.2.1 := by rw [hz3_sq k hk, one_mul]
                _ = k * (k * v.2.1) := by ring
                _ = 0 := by rw [h2, mul_zero]
            · calc v.2.2 = (k * k) * v.2.2 := by rw [hz3_sq k hk, one_mul]
                _ = k * (k * v.2.2) := by ring
                _ = 0 := by rw [h3, mul_zero]
        have hadj_ne0 : ∀ p : Fin 13, adjA (vs p) ≠ (0, 0, 0) := by
          intro p h0
          have hm : mulA (adjA (vs p)) = (0, 0, 0) := by rw [h0]; dsimp only [mulA]; simp
          rw [hmulA_adj] at hm
          exact hvs_ne0 p (hsmul_cancel d hd (vs p) hm)
        have hat_ne0 : ∀ w : Fin 13, atA (us w) ≠ (0, 0, 0) := by
          intro w h0
          have hm : adjAT (atA (us w)) = (0, 0, 0) := by rw [h0]; dsimp only [adjAT]; simp
          rw [hadjAT_at] at hm
          exact hus_ne0 w (hsmul_cancel d hd (us w) hm)
        have hPex : ∀ p : Fin 13, ∃ q : Fin 13, ∃ k : ZMod 3, k ≠ 0 ∧ adjA (vs p) = smul3 k (vs q) :=
          fun p => hvs_surj _ _ _ (hadj_ne0 p)
        have hLex : ∀ w : Fin 13, ∃ u : Fin 13, ∃ k : ZMod 3, k ≠ 0 ∧ atA (us w) = smul3 k (us u) :=
          fun w => hus_surj _ _ _ (hat_ne0 w)
        let τP : Fin 13 → Fin 13 := fun p => Classical.choose (hPex p)
        let τL : Fin 13 → Fin 13 := fun w => Classical.choose (hLex w)
        have hτP : ∀ p, ∃ k : ZMod 3, k ≠ 0 ∧ adjA (vs p) = smul3 k (vs (τP p)) :=
          fun p => Classical.choose_spec (hPex p)
        have hτL : ∀ w, ∃ k : ZMod 3, k ≠ 0 ∧ atA (us w) = smul3 k (us (τL w)) :=
          fun w => Classical.choose_spec (hLex w)
        have hmulA_smul : ∀ m v, mulA (smul3 m v) = smul3 m (mulA v) := fun m v => by
          apply Prod.ext
          · dsimp only [mulA, smul3]; ring
          · apply Prod.ext <;> (dsimp only [mulA, smul3]; ring)
        have hadjAT_smul : ∀ m u, adjAT (smul3 m u) = smul3 m (adjAT u) := fun m u => by
          apply Prod.ext
          · dsimp only [adjAT, smul3]; ring
          · apply Prod.ext <;> (dsimp only [adjAT, smul3]; ring)
        have hsmul_mul : ∀ m n v, smul3 m (smul3 n v) = smul3 (m * n) v := fun m n v => by
          apply Prod.ext
          · dsimp only [smul3]; ring
          · apply Prod.ext <;> (dsimp only [smul3]; ring)
        have hsmul_one : ∀ v, smul3 1 v = v := fun v => by
          apply Prod.ext
          · dsimp only [smul3]; ring
          · apply Prod.ext <;> (dsimp only [smul3]; ring)
        have hτP_inj : Function.Injective τP := by
          intro p q hpq
          obtain ⟨kp, hkp, hvp⟩ := hτP p
          obtain ⟨kq, hkq, hvq⟩ := hτP q
          rw [hpq] at hvp
          have h1 : adjA (vs p) = smul3 (kp * kq) (adjA (vs q)) := by
            rw [hvq, hsmul_mul, hvp]
            have : kp * kq * kq = kp := by
              calc kp * kq * kq = kp * (kq * kq) := by ring
                _ = kp := by rw [hz3_sq kq hkq, mul_one]
            rw [this]
          have h2 : smul3 d (vs p) = smul3 (d * (kp * kq)) (vs q) := by
            rw [← hmulA_adj, h1, hmulA_smul, hmulA_adj, hsmul_mul, mul_comm (kp * kq) d]
          have h3 : vs p = smul3 (kp * kq) (vs q) := by
            have := congrArg (smul3 d) h2
            rw [hsmul_mul, hsmul_mul, hz3_sq d hd, hsmul_one] at this
            have e : d * (d * (kp * kq)) = kp * kq := by
              calc d * (d * (kp * kq)) = (d * d) * (kp * kq) := by ring
                _ = kp * kq := by rw [hz3_sq d hd, one_mul]
            rwa [e] at this
          have hkk : kp * kq ≠ 0 := by
            intro h0
            have : kp = 0 := by
              calc kp = kp * (kq * kq) := by rw [hz3_sq kq hkq, mul_one]
                _ = (kp * kq) * kq := by ring
                _ = 0 := by rw [h0, zero_mul]
            exact hkp this
          exact hvs_inj p q (kp * kq) hkk h3
        have hτL_inj : Function.Injective τL := by
          intro u v huv
          obtain ⟨ku, hku, hvu⟩ := hτL u
          obtain ⟨kv, hkv, hvv⟩ := hτL v
          rw [huv] at hvu
          have h1 : atA (us u) = smul3 (ku * kv) (atA (us v)) := by
            rw [hvv, hsmul_mul, hvu]
            have : ku * kv * kv = ku := by
              calc ku * kv * kv = ku * (kv * kv) := by ring
                _ = ku := by rw [hz3_sq kv hkv, mul_one]
            rw [this]
          have h2 : smul3 d (us u) = smul3 (d * (ku * kv)) (us v) := by
            rw [← hadjAT_at, h1, hadjAT_smul, hadjAT_at, hsmul_mul, mul_comm (ku * kv) d]
          have h3 : us u = smul3 (ku * kv) (us v) := by
            have := congrArg (smul3 d) h2
            rw [hsmul_mul, hsmul_mul, hz3_sq d hd, hsmul_one] at this
            have e : d * (d * (ku * kv)) = ku * kv := by
              calc d * (d * (ku * kv)) = (d * d) * (ku * kv) := by ring
                _ = ku * kv := by rw [hz3_sq d hd, one_mul]
            rwa [e] at this
          have hkk : ku * kv ≠ 0 := by
            intro h0
            have : ku = 0 := by
              calc ku = ku * (kv * kv) := by rw [hz3_sq kv hkv, mul_one]
                _ = (ku * kv) * kv := by ring
                _ = 0 := by rw [h0, zero_mul]
            exact hku this
          exact hus_inj u v (ku * kv) hkk h3
        have hne_mul : ∀ x y : ZMod 3, x ≠ 0 → y ≠ 0 → x * y ≠ 0 := by
          intro x y hx hy h0
          apply hx
          calc x = x * (y * y) := by rw [hz3_sq y hy, mul_one]
            _ = (x * y) * y := by ring
            _ = 0 := by rw [h0, zero_mul]
        have hp0_eq : τP p0 = 0 := by
          obtain ⟨k, hk, hvk⟩ := hτP p0
          have ha0 : adjA a = smul3 d (1, 0, 0) := by
            apply Prod.ext
            · dsimp only [adjA, smul3, d, dot3, cross3]; ring
            · apply Prod.ext <;> (dsimp only [adjA, smul3, d, dot3, cross3]; ring)
          have h1 : vs (τP p0) = smul3 (k * d) (vs 0) := by
            have := congrArg (smul3 k) (hvk.symm.trans ha0)
            rw [hsmul_mul, hz3_sq k hk, hsmul_one, hsmul_mul] at this
            exact this
          exact hvs_inj (τP p0) 0 (k * d) (hne_mul k d hk hd) h1
        have hp1_eq : τP p1 = 1 := by
          obtain ⟨k, hk, hvk⟩ := hτP p1
          have hb0 : adjA b = smul3 d (0, 1, 0) := by
            apply Prod.ext
            · dsimp only [adjA, smul3, d, dot3, cross3]; ring
            · apply Prod.ext <;> (dsimp only [adjA, smul3, d, dot3, cross3]; ring)
          have h1 : vs (τP p1) = smul3 (k * d) (vs 1) := by
            have := congrArg (smul3 k) (hvk.symm.trans hb0)
            rw [hsmul_mul, hz3_sq k hk, hsmul_one, hsmul_mul] at this
            exact this
          exact hvs_inj (τP p1) 1 (k * d) (hne_mul k d hk hd) h1
        have hp2_eq : τP p2 = 2 := by
          obtain ⟨k, hk, hvk⟩ := hτP p2
          have hc0 : adjA c = smul3 d (0, 0, 1) := by
            apply Prod.ext
            · dsimp only [adjA, smul3, d, dot3, cross3]; ring
            · apply Prod.ext <;> (dsimp only [adjA, smul3, d, dot3, cross3]; ring)
          have h1 : vs (τP p2) = smul3 (k * d) (vs 2) := by
            have := congrArg (smul3 k) (hvk.symm.trans hc0)
            rw [hsmul_mul, hz3_sq k hk, hsmul_one, hsmul_mul] at this
            exact this
          exact hvs_inj (τP p2) 2 (k * d) (hne_mul k d hk hd) h1
        have hinc_pres : ∀ p w : Fin 13, τP p ∈ S (τL w) ↔ p ∈ S w := by
          intro p w
          rw [hincb, hincb, hdot_inc_b, hdot_inc_b, decide_eq_true_eq, decide_eq_true_eq]
          obtain ⟨kp, hkp, hvp⟩ := hτP p
          obtain ⟨kw, hkw, hvw⟩ := hτL w
          have heq : kw * kp * dot3 (us (τL w)) (vs (τP p)) = d * dot3 (us w) (vs p) := by
            have h1 : dot3 (smul3 kw (us (τL w))) (smul3 kp (vs (τP p))) =
                kw * kp * dot3 (us (τL w)) (vs (τP p)) := by
              dsimp only [dot3, smul3]; ring
            rw [← h1, ← hvw, ← hvp, hlagrange]
          constructor
          · intro h0
            rw [h0, mul_zero] at heq
            calc dot3 (us w) (vs p) = (d * d) * dot3 (us w) (vs p) := by rw [hz3_sq d hd, one_mul]
              _ = d * (d * dot3 (us w) (vs p)) := by ring
              _ = 0 := by rw [← heq, mul_zero]
          · intro h0
            rw [h0, mul_zero] at heq
            have hkk := hne_mul kw kp hkw hkp
            calc dot3 (us (τL w)) (vs (τP p)) = ((kw * kp) * (kw * kp)) * dot3 (us (τL w)) (vs (τP p)) := by
                  rw [hz3_sq _ hkk, one_mul]
              _ = (kw * kp) * (kw * kp * dot3 (us (τL w)) (vs (τP p))) := by ring
              _ = 0 := by rw [heq, mul_zero]
        exact ⟨τP, τL, Finite.injective_iff_bijective.mp hτP_inj,
          Finite.injective_iff_bijective.mp hτL_inj, hp0_eq, hp1_eq, hp2_eq, hinc_pres⟩
      have hcoll_apply : ∀ (D : Circuit) (τP τL : Fin 13 → Fin 13),
          Function.Bijective τP → Function.Bijective τL →
          (∀ p w : Fin 13, τP p ∈ S (τL w) ↔ p ∈ S w) →
          IsAO2 26 D → D.output + 1 = 26 + D.size → liveSize 26 D = D.size →
          (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
          degSep D →
          ∃ D' : Circuit, D'.size = D.size ∧ D'.output + 1 = 26 + D'.size ∧
            IsAO2 26 D' ∧ liveSize 26 D' = D'.size ∧
            (∀ j < D'.size, opnd D' j 0 < opnd D' j 1) ∧
            D'.lineDeg 26 (Finset.Ico 13 26) = D.lineDeg 26 (Finset.Ico 13 26) ∧
            D'.lineDeg 26 (Finset.range 13) = D.lineDeg 26 (Finset.range 13) ∧
            degSep D' ∧
            ∀ X Y : Finset (Fin 13), D'.eval (incidenceInput (X.image τP) (Y.image τL)) =
              D.eval (incidenceInput X Y) := by
        intro D τP τL hbP hbL hpres hDao hDout hDlive hDnd hDsep
        let ρ (j : ℕ) : ℕ :=
          if h1 : j < 13 then (τP ⟨j, h1⟩).val
          else if h2 : j < 26 then 13 + (τL ⟨j - 13, by omega⟩).val
          else j
        have hρlt : ∀ i < 26, ρ i < 26 := by
          intro i hi; dsimp only [ρ]
          by_cases h1 : i < 13
          · rw [dif_pos h1]; have := (τP ⟨i, h1⟩).isLt; omega
          · rw [dif_neg h1, dif_pos hi]; have := (τL ⟨i - 13, by omega⟩).isLt; omega
        have hρge : ∀ i, 26 ≤ i → ρ i = i := by
          intro i hi; dsimp only [ρ]; rw [dif_neg (by omega), dif_neg (by omega)]
        have hρinj : Function.Injective ρ := by
          intro a b hab
          dsimp only [ρ] at hab
          by_cases ha1 : a < 13 <;> by_cases hb1 : b < 13
          · rw [dif_pos ha1, dif_pos hb1] at hab
            have heq : τP ⟨a, ha1⟩ = τP ⟨b, hb1⟩ := Fin.ext hab
            have := congrArg Fin.val (hbP.1 heq); simpa using this
          · by_cases hb2 : b < 26
            · rw [dif_pos ha1, dif_neg hb1, dif_pos hb2] at hab
              have := (τP ⟨a, ha1⟩).isLt; omega
            · rw [dif_pos ha1, dif_neg hb1, dif_neg hb2] at hab
              have := (τP ⟨a, ha1⟩).isLt; omega
          · by_cases ha2 : a < 26
            · rw [dif_neg ha1, dif_pos ha2, dif_pos hb1] at hab
              have := (τP ⟨b, hb1⟩).isLt; omega
            · rw [dif_neg ha1, dif_neg ha2, dif_pos hb1] at hab
              have := (τP ⟨b, hb1⟩).isLt; omega
          · by_cases ha2 : a < 26 <;> by_cases hb2 : b < 26
            · rw [dif_neg ha1, dif_pos ha2, dif_neg hb1, dif_pos hb2] at hab
              have heq : τL ⟨a - 13, by omega⟩ = τL ⟨b - 13, by omega⟩ := Fin.ext (by omega)
              have := congrArg Fin.val (hbL.1 heq); simp at this; omega
            · rw [dif_neg ha1, dif_pos ha2, dif_neg hb1, dif_neg hb2] at hab
              have := (τL ⟨a - 13, by omega⟩).isLt; omega
            · rw [dif_neg ha1, dif_neg ha2, dif_neg hb1, dif_pos hb2] at hab
              have := (τL ⟨b - 13, by omega⟩).isLt; omega
            · rw [dif_neg ha1, dif_neg ha2, dif_neg hb1, dif_neg hb2] at hab
              exact hab
        have hρIco : ∀ j < 26, ρ j ∈ Finset.Ico 13 26 ↔ j ∈ Finset.Ico 13 26 := by
          intro j hj; dsimp only [ρ]; simp only [Finset.mem_Ico]
          by_cases h1 : j < 13
          · rw [dif_pos h1]; have := (τP ⟨j, h1⟩).isLt; omega
          · rw [dif_neg h1, dif_pos hj]; have := (τL ⟨j - 13, by omega⟩).isLt; omega
        have hρRng : ∀ j < 26, ρ j ∈ Finset.range 13 ↔ j ∈ Finset.range 13 := by
          intro j hj; dsimp only [ρ]; simp only [Finset.mem_range]
          by_cases h1 : j < 13
          · rw [dif_pos h1]; have := (τP ⟨j, h1⟩).isLt; omega
          · rw [dif_neg h1, dif_pos hj]; have := (τL ⟨j - 13, by omega⟩).isLt; omega
        let D1 := mapC ρ D
        let D2 := sortC D1
        have hD1_ao := hmap_ao2 D ρ hρlt hρge hDao
        have hD1_nd := hmap_nodup D ρ hρinj hDao.2.2 hDnd
        obtain ⟨hD2_sz, hD2_out, hD2_ao, hD2_lt, hD2_wires, hD2_deg, hD2_live⟩ := hsort_all D1 hD1_ao hD1_nd
        have hDout_ge : 26 ≤ D.output := by
          by_contra hlt
          have : D.size = 0 := by omega
          have h0 := hDsep.1 0 0 (by simp [S])
          have h1 := hDsep.1 1 1 (by simp [S])
          have hbit : ∀ x : Fin 26 → Bool, circuitFun 26 D x = x ⟨D.output, by omega⟩ := by
            intro x
            have hnil : D.gates = [] := List.eq_nil_of_length_eq_zero this
            change (runW D.gates (List.ofFn x)).getD D.output false = _
            rw [hnil, hrunW_pref _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
            exact List.getElem_ofFn _
          rw [hincIn] at h0 h1
          change circuitFun 26 D _ = true at h0 h1
          rw [hbit] at h0 h1
          rcases of_decide_eq_true h0 with ⟨p, hp, he0⟩ | ⟨w, hw, he0⟩ <;>
          rcases of_decide_eq_true h1 with ⟨q, hq, he1⟩ | ⟨u, hu, he1⟩
          · rw [Finset.mem_singleton.mp hp] at he0
            rw [Finset.mem_singleton.mp hq] at he1
            have := congrArg Fin.val (he0.symm.trans he1); simp at this
          · have := congrArg Fin.val (he0.symm.trans he1); simp at this; have := p.isLt; omega
          · have := congrArg Fin.val (he0.symm.trans he1); simp at this; have := q.isLt; omega
          · rw [Finset.mem_singleton.mp hw] at he0
            rw [Finset.mem_singleton.mp hu] at he1
            have := congrArg Fin.val (he0.symm.trans he1); simp at this
        have hD1_sz : D1.size = D.size := List.length_map _
        have hD1_out : D1.output = D.output := hρge D.output hDout_ge
        have hD1_live : liveSize 26 D1 = D.size := (hmap_live D ρ hρlt hρge hDout_ge).trans hDlive
        have heval_img : ∀ X Y : Finset (Fin 13),
            D2.eval (incidenceInput (X.image τP) (Y.image τL)) = D.eval (incidenceInput X Y) := by
          intro X Y
          have hs_eval : D2.eval (incidenceInput (X.image τP) (Y.image τL)) =
              D1.eval (incidenceInput (X.image τP) (Y.image τL)) := by
            unfold Circuit.eval; rw [hD2_wires, hD2_out]
          rw [hs_eval, hincIn, hincIn]
          apply hmap_val D ρ hρlt hρge
          refine hsplit26 (fun q => ?_) (fun w => ?_)
          · apply decide_eq_decide.mpr
            have hidx : (⟨ρ (Fin.castAdd 13 q).val, hρlt _ (Fin.castAdd 13 q).isLt⟩ : Fin 26) = Fin.castAdd 13 (τP q) := by
              apply Fin.ext; simp only [Fin.val_castAdd, ρ, q.isLt, ↓reduceDIte]
            rw [hidx]
            constructor
            · rintro (⟨p, hp, he⟩ | ⟨w, _, he⟩)
              · have hqp : q = p := Fin.ext (by have := congrArg Fin.val he; simpa using this)
                subst hqp
                exact Or.inl ⟨τP q, Finset.mem_image.mpr ⟨q, hp, rfl⟩, rfl⟩
              · have := congrArg Fin.val he; simp at this; have := q.isLt; omega
            · rintro (⟨p', hp', he⟩ | ⟨w', _, he⟩)
              · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hp'
                have heq : τP q = τP p := Fin.ext (by have := congrArg Fin.val he; simpa using this)
                rw [hbP.1 heq]
                exact Or.inl ⟨p, hp, rfl⟩
              · have := congrArg Fin.val he; simp at this; have := (τP q).isLt; omega
          · apply decide_eq_decide.mpr
            have hidx : (⟨ρ (Fin.natAdd 13 w).val, hρlt _ (Fin.natAdd 13 w).isLt⟩ : Fin 26) = Fin.natAdd 13 (τL w) := by
              apply Fin.ext
              simp only [Fin.val_natAdd, ρ]
              have hw := w.isLt
              have h1 : ¬ (13 + w.val < 13) := by omega
              have h2 : 13 + w.val < 26 := by omega
              rw [dif_neg h1, dif_pos h2]
              have hsub : (⟨13 + w.val - 13, by omega⟩ : Fin 13) = w := Fin.ext (by simp)
              rw [hsub]
            rw [hidx]
            constructor
            · rintro (⟨p, _, he⟩ | ⟨u, hu, he⟩)
              · have := congrArg Fin.val he; simp at this; have := p.isLt; omega
              · have hwu : w = u := Fin.ext (by have := congrArg Fin.val he; simp at this; omega)
                subst hwu
                exact Or.inr ⟨τL w, Finset.mem_image.mpr ⟨w, hu, rfl⟩, rfl⟩
            · rintro (⟨p', _, he⟩ | ⟨u', hu', he⟩)
              · have := congrArg Fin.val he; simp at this; have := p'.isLt; omega
              · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hu'
                have heq : τL w = τL u := Fin.ext (by have := congrArg Fin.val he; simp at this; omega)
                rw [hbL.1 heq]
                exact Or.inr ⟨u, hu, rfl⟩
        have hD2_sep : degSep D2 := by
          refine ⟨?_, ?_⟩
          · intro w' p' hp'w'
            obtain ⟨w, rfl⟩ := hbL.2 w'
            obtain ⟨p, rfl⟩ := hbP.2 p'
            have h1 := heval_img {p} {w}
            simp only [Finset.image_singleton] at h1
            rw [h1]
            exact hDsep.1 w p ((hpres p w).mp hp'w')
          · intro X' Y' hmf' hdeg'
            let X : Finset (Fin 13) := Finset.univ.filter fun p => τP p ∈ X'
            let Y : Finset (Fin 13) := Finset.univ.filter fun w => τL w ∈ Y'
            have hXimg : X.image τP = X' := by
              ext p'
              simp only [X, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨p, hp, rfl⟩; exact hp
              · intro hp'; obtain ⟨p, rfl⟩ := hbP.2 p'; exact ⟨p, hp', rfl⟩
            have hYimg : Y.image τL = Y' := by
              ext w'
              simp only [Y, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨w, hw, rfl⟩; exact hw
              · intro hw'; obtain ⟨w, rfl⟩ := hbL.2 w'; exact ⟨w, hw', rfl⟩
            rw [← hXimg, ← hYimg, heval_img X Y]
            have hmf : IsMaximalFalse S X Y := by
              refine ⟨?_, ?_, ?_⟩
              · intro w hw
                rw [Finset.disjoint_left]
                intro p hpS hpX
                exact Finset.disjoint_left.mp (hmf'.1 (τL w) (Finset.mem_filter.mp hw).2)
                  ((hpres p w).mpr hpS) (Finset.mem_filter.mp hpX).2
              · intro p hp hfalse
                have hp' : τP p ∉ X' := fun h => hp (Finset.mem_filter.mpr ⟨Finset.mem_univ p, h⟩)
                apply hmf'.2.1 (τP p) hp'
                intro w' hw'
                obtain ⟨w, rfl⟩ := hbL.2 w'
                rw [Finset.disjoint_left]
                intro q' hq' hqIns
                obtain ⟨q, rfl⟩ := hbP.2 q'
                rw [Finset.mem_insert] at hqIns
                have hqX : q ∈ insert p X := by
                  rcases hqIns with heq | hmem
                  · rw [hbP.1 heq]; exact Finset.mem_insert_self p X
                  · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hmem⟩)
                exact Finset.disjoint_left.mp (hfalse w (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw'⟩))
                  ((hpres q w).mp hq') hqX
              · intro w hw hfalse
                have hw' : τL w ∉ Y' := fun h => hw (Finset.mem_filter.mpr ⟨Finset.mem_univ w, h⟩)
                apply hmf'.2.2 (τL w) hw'
                intro u' hu'
                obtain ⟨u, rfl⟩ := hbL.2 u'
                rw [Finset.mem_insert] at hu'
                have huY : u ∈ insert w Y := by
                  rcases hu' with heq | hmem
                  · rw [hbL.1 heq]; exact Finset.mem_insert_self w Y
                  · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hmem⟩)
                rw [Finset.disjoint_left]
                intro q' hq' hqX'
                obtain ⟨q, rfl⟩ := hbP.2 q'
                exact Finset.disjoint_left.mp (hfalse u huY) ((hpres q u).mp hq')
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hqX'⟩)
            have hdeg : ¬ InNoLine S X ∨ ¬ InNoPencil S Y := by
              rcases hdeg' with hnl' | hnp'
              · left
                intro hnl
                apply hnl'
                intro w' hw'
                obtain ⟨w, rfl⟩ := hbL.2 w'
                exact hnl w fun p hp => (hpres p w).mp (hw' (Finset.mem_filter.mp hp).2)
              · right
                intro hnp
                apply hnp'
                intro p' hp'
                obtain ⟨p, rfl⟩ := hbP.2 p'
                exact hnp p fun w hw => (hpres p w).mp (hp' (τL w) (Finset.mem_filter.mp hw).2)
            exact hDsep.2 X Y hmf hdeg
        refine ⟨D2, hD2_sz.trans hD1_sz, by rw [hD2_out, hD1_out, hD2_sz, hD1_sz]; exact hDout, hD2_ao, by rw [hD2_live, hD1_live, hD2_sz, hD1_sz], hD2_lt, ?_, ?_, hD2_sep, heval_img⟩
        · unfold Circuit.lineDeg
          rw [hD2_deg, hD2_out]
          exact hmap_deg D ρ (Finset.Ico 13 26) (Finset.Ico 13 26) hρlt hρge hρIco
        · unfold Circuit.lineDeg
          rw [hD2_deg, hD2_out]
          exact hmap_deg D ρ (Finset.range 13) (Finset.range 13) hρlt hρge hρRng
      have hC_orient : ∃ C2 : Circuit, C2.size = C.size ∧ C2.output + 1 = 26 + C2.size ∧
          IsAO2 26 C2 ∧ liveSize 26 C2 = C2.size ∧
          (∀ j < C2.size, opnd C2 j 0 < opnd C2 j 1) ∧
          2 ≤ C2.lineDeg 26 (Finset.Ico 13 26) ∧
          C2.lineDeg 26 (Finset.Ico 13 26) ≤ C2.lineDeg 26 (Finset.range 13) ∧
          degSep C2 := by
        by_cases hle : C.lineDeg 26 (Finset.Ico 13 26) ≤ C.lineDeg 26 (Finset.range 13)
        · have hs := hsort_all C hC_clean.1 hC_clean.2
          refine ⟨sortC C, hs.1, by omega, hs.2.2.1, by omega, hs.2.2.2.1, ?_, ?_, ?_⟩
          · unfold Circuit.lineDeg; rw [hs.2.2.2.2.2.1, hs.2.1]; exact hld2
          · unfold Circuit.lineDeg; rw [hs.2.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.1]; exact hle
          · refine ⟨fun w p hpw => ?_, fun X Y hmf hdeg => ?_⟩
            · unfold Circuit.eval; rw [hs.2.2.2.2.1, hs.2.1]; exact hCsep.1 w p hpw
            · unfold Circuit.eval; rw [hs.2.2.2.2.1, hs.2.1]; exact hCsep.2 X Y hmf hdeg
        · let D1 := mapC ρ_dual C
          have hD1_ao := hmap_ao2 C ρ_dual hdual_lt hdual_ge hC_clean.1
          have hD1_nd := hmap_nodup C ρ_dual hdual_inj hC_clean.1.2.2 hC_clean.2
          have hs := hsort_all D1 hD1_ao hD1_nd
          have hD1_sz : D1.size = C.size := List.length_map _
          have hD1_out : D1.output = C.output := hdual_ge C.output hCout_ge
          have hD1_live : liveSize 26 D1 = C.size := (hmap_live C ρ_dual hdual_lt hdual_ge hCout_ge).trans hC_live
          have hD1_ld : D1.lineDeg 26 (Finset.Ico 13 26) = C.lineDeg 26 (Finset.range 13) :=
            hmap_deg C ρ_dual (Finset.range 13) (Finset.Ico 13 26) hdual_lt hdual_ge hdual_Ico
          have hD1_pd : D1.lineDeg 26 (Finset.range 13) = C.lineDeg 26 (Finset.Ico 13 26) :=
            hmap_deg C ρ_dual (Finset.Ico 13 26) (Finset.range 13) hdual_lt hdual_ge hdual_range
          have hD1_sep := hdual_degSep C hCsep
          refine ⟨sortC D1, by omega, by omega, hs.2.2.1, by omega, hs.2.2.2.1, ?_, ?_, ?_⟩
          · unfold Circuit.lineDeg; rw [hs.2.2.2.2.2.1, hs.2.1]; change D1.lineDeg 26 (Finset.Ico 13 26) ≥ 2; omega
          · unfold Circuit.lineDeg; rw [hs.2.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.1]
            change D1.lineDeg 26 (Finset.Ico 13 26) ≤ D1.lineDeg 26 (Finset.range 13); omega
          · refine ⟨fun w p hpw => ?_, fun X Y hmf hdeg => ?_⟩
            · unfold Circuit.eval; rw [hs.2.2.2.2.1, hs.2.1]; exact hD1_sep.1 w p hpw
            · unfold Circuit.eval; rw [hs.2.2.2.2.1, hs.2.1]; exact hD1_sep.2 X Y hmf hdeg
      obtain ⟨C2, hC2sz, hC2out, hC2ao, hC2live, hC2lt, hC2ld2, hC2le, hC2sep⟩ := hC_orient
      have hC2mono : Monotone2 C2 := fun g hg => ⟨by simpa using hC2ao.1 g hg, by have := hC2ao.2.2 g hg; omega⟩
      have hC2min_deg : ∀ D : Circuit, Monotone2 D → degSep D → C2.size ≤ D.size := fun D hDm hDs => by
        rw [hC2sz]; exact hCmin D hDm hDs
      have hC2min_exact : ∀ D : Circuit, Monotone2 D → ComputesIncidence S D → C2.size ≤ D.size := by
        intro D hDm hDex
        apply hC2min_deg D hDm
        refine ⟨fun w p hpw => ?_, fun X Y hmf _ => ?_⟩
        · rw [hDex {p} {w}]; exact decide_eq_true ⟨p, Finset.mem_singleton_self p, w, Finset.mem_singleton_self w, hpw⟩
        · rw [hDex X Y]
          apply decide_eq_false
          rintro ⟨p, hpX, w, hwY, hpw⟩
          exact Finset.disjoint_left.mp (hmf.1 w hwY) hpw hpX
      by_cases hdeg2 : C2.lineDeg 26 (Finset.Ico 13 26) = 2
      · exact deg2Exact C2 hC2ao (by omega) hC2out hC2live hC2lt hdeg2 (by omega)
          (hdeg2_exact C2 hC2mono hC2sep (by omega)) hC2min_exact
      · have hC2ld3 : 3 ≤ C2.lineDeg 26 (Finset.Ico 13 26) := by omega
        have hC2pd3 : 3 ≤ C2.lineDeg 26 (Finset.range 13) := by omega
        by_cases hexact : ComputesIncidence S C2
        · exact deg3Exact C2 hC2ao (by omega) hC2out hC2live hC2lt hC2ld3 hC2le hexact hC2min_exact
        · have hex_bad : ∃ X Y : Finset (Fin 13), C2.eval (incidenceInput X Y) ≠ incidenceFun S X Y := by
            by_contra hno
            exact hexact fun X Y => by by_contra hne; exact hno ⟨X, Y, hne⟩
          obtain ⟨X0, Y0, hbad⟩ := hex_bad
          have hY0_false : incidenceFun S X0 Y0 = false := by
            cases h : incidenceFun S X0 Y0
            · rfl
            · exfalso
              obtain ⟨p, hpX, w, hwY, hpw⟩ := of_decide_eq_true h
              have h1 := hC2sep.1 w p hpw
              rw [hincIn {p} {w}] at h1
              have h2 : C2.eval (incidenceInput X0 Y0) = true := by
                rw [hincIn X0 Y0]
                apply hmono_cfun C2 hC2mono _ _ _ h1
                intro k hk
                apply decide_eq_true
                rcases of_decide_eq_true hk with ⟨q, hq, rfl⟩ | ⟨u, hu, rfl⟩
                · rw [Finset.mem_singleton.mp hq]; exact Or.inl ⟨p, hpX, rfl⟩
                · rw [Finset.mem_singleton.mp hu]; exact Or.inr ⟨w, hwY, rfl⟩
              exact hbad (h2.trans h.symm)
          have hC2_X0Y0 : C2.eval (incidenceInput X0 Y0) = true := by
            cases h : C2.eval (incidenceInput X0 Y0)
            · exact False.elim (hbad (h.trans hY0_false.symm))
            · rfl
          let Y1 : Finset (Fin 13) := Finset.univ.filter fun w => ∀ p ∈ X0, p ∉ S w
          let X1 : Finset (Fin 13) := zeroSet S Y1
          have hY0sub : Y0 ⊆ Y1 := by
            intro w hwY0
            simp only [Y1, Finset.mem_filter, Finset.mem_univ, true_and]
            intro p hpX0 hpw
            have : incidenceFun S X0 Y0 = true := decide_eq_true ⟨p, hpX0, w, hwY0, hpw⟩
            exact Bool.noConfusion (hY0_false.symm.trans this)
          have hX0sub : X0 ⊆ X1 := by
            intro p hpX0
            simp only [X1, hzeroSet_def, Finset.mem_filter, Finset.mem_univ, true_and]
            intro w hwY1
            exact (Finset.mem_filter.mp hwY1).2 p hpX0
          have hmf1 : IsMaximalFalse S X1 Y1 := by
            refine ⟨?_, ?_, ?_⟩
            · intro w hwY1
              rw [Finset.disjoint_left]
              intro p hpS hpX1
              exact (Finset.mem_filter.mp hpX1).2 w hwY1 hpS
            · intro p hpX1 hfalse
              have hex : ∃ w ∈ Y1, p ∈ S w := by
                by_contra hno
                exact hpX1 (Finset.mem_filter.mpr ⟨Finset.mem_univ p, fun w hw hmem => hno ⟨w, hw, hmem⟩⟩)
              obtain ⟨w, hwY1, hpw⟩ := hex
              exact Finset.disjoint_left.mp (hfalse w hwY1) hpw (Finset.mem_insert_self p X1)
            · intro w hwY1 hfalse
              have hex : ∃ p ∈ X0, p ∈ S w := by
                by_contra hno
                exact hwY1 (Finset.mem_filter.mpr ⟨Finset.mem_univ w, fun p hpX0 hmem => hno ⟨p, hpX0, hmem⟩⟩)
              obtain ⟨p, hpX0, hpw⟩ := hex
              exact Finset.disjoint_left.mp (hfalse w (Finset.mem_insert_self w Y1)) hpw (hX0sub hpX0)
          have hC2_X1Y1 : C2.eval (incidenceInput X1 Y1) = true := by
            rw [hincIn X1 Y1]
            rw [hincIn X0 Y0] at hC2_X0Y0
            apply hmono_cfun C2 hC2mono _ _ _ hC2_X0Y0
            intro k hk
            apply decide_eq_true
            rcases of_decide_eq_true hk with ⟨p, hp, rfl⟩ | ⟨w, hw, rfl⟩
            · exact Or.inl ⟨p, hX0sub hp, rfl⟩
            · exact Or.inr ⟨w, hY0sub hw, rfl⟩
          have hgen1 : InNoLine S X1 ∧ InNoPencil S Y1 := by
            refine ⟨?_, ?_⟩
            · by_contra hbad_deg
              exact Bool.noConfusion (hC2_X1Y1.symm.trans (hC2sep.2 X1 Y1 hmf1 (Or.inl hbad_deg)))
            · by_contra hbad_deg
              exact Bool.noConfusion (hC2_X1Y1.symm.trans (hC2sep.2 X1 Y1 hmf1 (Or.inr hbad_deg)))
          have hpick_tri : ∀ X : Finset (Fin 13), InNoLine S X →
              ∃ p0 p1 p2 : Fin 13, p0 ∈ X ∧ p1 ∈ X ∧ p2 ∈ X ∧
                ¬ ∃ w : Fin 13, p0 ∈ S w ∧ p1 ∈ S w ∧ p2 ∈ S w := by
            intro X hnl
            have hne0 : X.Nonempty := by
              by_contra hem
              rw [Finset.not_nonempty_iff_eq_empty] at hem
              exact hnl 0 (by simp [hem])
            obtain ⟨p0, hp0⟩ := hne0
            have hne1 : (X \ {p0}).Nonempty := by
              by_contra hem
              rw [Finset.not_nonempty_iff_eq_empty] at hem
              apply hnl p0
              intro q hq
              have hqp : q = p0 := by
                by_contra hne
                have : q ∈ X \ {p0} := Finset.mem_sdiff.mpr ⟨hq, by simp [hne]⟩
                rw [hem] at this; simp at this
              subst hqp; simp [S]
            obtain ⟨p1, hp1s⟩ := hne1
            have hp1 : p1 ∈ X := (Finset.mem_sdiff.mp hp1s).1
            have hne01 : p1 ≠ p0 := by simpa using (Finset.mem_sdiff.mp hp1s).2
            obtain ⟨w01, hw0, hw1⟩ := hS_twoPts p0 p1
            have hex2 : ∃ p2 ∈ X, p2 ∉ S w01 := by
              by_contra hno
              exact hnl w01 fun q hq => by by_contra hnot; exact hno ⟨q, hq, hnot⟩
            obtain ⟨p2, hp2, hp2n⟩ := hex2
            refine ⟨p0, p1, p2, hp0, hp1, hp2, ?_⟩
            rintro ⟨w, h0w, h1w, h2w⟩
            have hww : w = w01 := by
              by_contra hne
              have hmeet : ([0, 1, 3, 9] : List (Fin 13)).countP (fun q => incb q (w + -w01)) ≤ 1 :=
                hS_cnt1 (w + -w01) (fun h => hne (by
                  have := congrArg (· + w01) h
                  simpa [add_assoc, neg_add_cancel, add_zero] using this))
              have hq0 : p0 + -w01 ∈ ([0, 1, 3, 9] : List (Fin 13)) := by
                have := (hincb p0 w01).mp hw0
                rw [← hS_shift p0 w01 (-w01), add_neg_cancel] at this
                have := of_decide_eq_true this
                simp only [zero_add] at this
                rcases this with h | h | h | h <;> simp [h]
              have hq1 : p1 + -w01 ∈ ([0, 1, 3, 9] : List (Fin 13)) := by
                have := (hincb p1 w01).mp hw1
                rw [← hS_shift p1 w01 (-w01), add_neg_cancel] at this
                have := of_decide_eq_true this
                simp only [zero_add] at this
                rcases this with h | h | h | h <;> simp [h]
              have hne_q : p1 + -w01 ≠ p0 + -w01 := fun h => hne01 (add_right_cancel h)
              have ht0 : incb (p0 + -w01) (w + -w01) = true := (hS_shift p0 w (-w01)).trans ((hincb p0 w).mp h0w)
              have ht1 : incb (p1 + -w01) (w + -w01) = true := (hS_shift p1 w (-w01)).trans ((hincb p1 w).mp h1w)
              have h2cnt : ∀ (l : List (Fin 13)) (f : Fin 13 → Bool) (a b : Fin 13),
                  a ∈ l → b ∈ l → a ≠ b → f a = true → f b = true → 2 ≤ l.countP f := by
                intro l f a b ha hb hab hfa hfb
                induction l with
                | nil => simp at ha
                | cons x t ih =>
                  simp only [List.mem_cons] at ha hb
                  simp only [List.countP_cons]
                  rcases ha with rfl | hat <;> rcases hb with rfl | hbt
                  · exact False.elim (hab rfl)
                  · rw [hfa, if_pos rfl]
                    have hpos : 0 < t.countP f := List.countP_pos_iff.mpr ⟨b, hbt, hfb⟩
                    omega
                  · rw [hfb, if_pos rfl]
                    have hpos : 0 < t.countP f := List.countP_pos_iff.mpr ⟨a, hat, hfa⟩
                    omega
                  · have := ih hat hbt
                    by_cases hfx : f x = true
                    · rw [if_pos hfx]; omega
                    · rw [if_neg hfx]; omega
              have := h2cnt [0, 1, 3, 9] (fun q => incb q (w + -w01)) (p0 + -w01) (p1 + -w01)
                hq0 hq1 hne_q.symm ht0 ht1
              omega
            subst hww
            exact hp2n h2w
          have hfinish_tri : ∀ (D : Circuit) (X Y : Finset (Fin 13)) (p0 p1 p2 : Fin 13),
              D.size = C.size → D.output + 1 = 26 + D.size → IsAO2 26 D → liveSize 26 D = D.size →
              (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
              3 ≤ D.lineDeg 26 (Finset.Ico 13 26) → 3 ≤ D.lineDeg 26 (Finset.range 13) →
              degSep D → IsMaximalFalse S X Y → X = {p0, p1, p2} →
              (¬ ∃ w : Fin 13, p0 ∈ S w ∧ p1 ∈ S w ∧ p2 ∈ S w) →
              D.eval (incidenceInput X Y) = true → False := by
            intro D X Y p0 p1 p2 hDsz hDout hDao hDlive hDnd hDld hDpd hDsep hmf hXeq hnc hDeval
            obtain ⟨τP, τL, hbP, hbL, hp0e, hp1e, hp2e, hpres⟩ := hcoll_tri p0 p1 p2 hnc
            obtain ⟨D', hD'sz, hD'out, hD'ao, hD'live, hD'lt, hD'ld, hD'pd, hD'sep, hD'ev⟩ :=
              hcoll_apply D τP τL hbP hbL hpres hDao hDout hDlive hDnd hDsep
            have hXimg : X.image τP = ({0, 1, 2} : Finset (Fin 13)) := by
              rw [hXeq]; ext q
              simp [hp0e, hp1e, hp2e]
            have hYimg : Y.image τL = ({3, 7, 8, 9} : Finset (Fin 13)) := by
              ext w'
              obtain ⟨w, rfl⟩ := hbL.2 w'
              have hw_iff : τL w ∈ Y.image τL ↔ w ∈ Y := by
                simp only [Finset.mem_image]
                constructor
                · rintro ⟨u, hu, heq⟩; rwa [← hbL.1 heq]
                · intro hw; exact ⟨w, hw, rfl⟩
              rw [hw_iff]
              have hmiss : w ∈ Y ↔ ∀ p ∈ X, p ∉ S w := by
                constructor
                · intro hw p hpX hpw
                  exact Finset.disjoint_left.mp (hmf.1 w hw) hpw hpX
                · intro hall
                  by_contra hnot
                  apply hmf.2.2 w hnot
                  intro u hu
                  rw [Finset.mem_insert] at hu
                  rcases hu with rfl | hu
                  · rw [Finset.disjoint_left]; intro p hpS hpX; exact hall p hpX hpS
                  · exact hmf.1 u hu
              rw [hmiss, hXeq]
              have h012 : (∀ p ∈ ({p0, p1, p2} : Finset (Fin 13)), p ∉ S w) ↔
                  (incb 0 (τL w) = false ∧ incb 1 (τL w) = false ∧ incb 2 (τL w) = false) := by
                simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
                have e0 : p0 ∉ S w ↔ incb 0 (τL w) = false := by
                  rw [← hpres p0 w, hp0e, hincb]; cases incb 0 (τL w) <;> simp
                have e1 : p1 ∉ S w ↔ incb 1 (τL w) = false := by
                  rw [← hpres p1 w, hp1e, hincb]; cases incb 1 (τL w) <;> simp
                have e2 : p2 ∉ S w ↔ incb 2 (τL w) = false := by
                  rw [← hpres p2 w, hp2e, hincb]; cases incb 2 (τL w) <;> simp
                rw [e0, e1, e2]
              rw [h012, htri0_miss_b]
              simp
            have htrue' : D'.eval (incidenceInput ({0, 1, 2} : Finset (Fin 13)) ({3, 7, 8, 9} : Finset (Fin 13))) = true := by
              rw [← hXimg, ← hYimg, hD'ev X Y]
              exact hDeval
            exact deg3Generic D' hD'ao (by omega) hD'out hD'live hD'lt (by omega) (by omega)
              hD'sep (fun E hEm hEs => by rw [hD'sz, hDsz]; exact hCmin E hEm hEs) htrue'
          obtain ⟨p0, p1, p2, hp0, hp1, hp2, hnc⟩ := hpick_tri X1 hgen1.1
          by_cases hXeq : X1 = {p0, p1, p2}
          · exact hfinish_tri C2 X1 Y1 p0 p1 p2 hC2sz hC2out hC2ao hC2live
              (fun j hj => Nat.ne_of_lt (hC2lt j hj)) hC2ld3 hC2pd3 hC2sep hmf1 hXeq hnc hC2_X1Y1
          · obtain ⟨τP, τL, hbP, hbL, hp0e, hp1e, hp2e, hpres⟩ := hcoll_tri p0 p1 p2 hnc
            have hex3 : ∃ p3 ∈ X1, p3 ∉ ({p0, p1, p2} : Finset (Fin 13)) := by
              by_contra hno
              apply hXeq
              ext q
              constructor
              · intro hq; by_contra hnot; exact hno ⟨q, hq, hnot⟩
              · intro hq
                simp only [Finset.mem_insert, Finset.mem_singleton] at hq
                rcases hq with rfl | rfl | rfl <;> assumption
            obtain ⟨p3, hp3X, hp3n⟩ := hex3
            have hY1_sub : Y1.image τL ⊆ ({3, 7, 8, 9} : Finset (Fin 13)) := by
              intro w' hw'
              obtain ⟨w, hwY, rfl⟩ := Finset.mem_image.mp hw'
              have hmiss : incb 0 (τL w) = false ∧ incb 1 (τL w) = false ∧ incb 2 (τL w) = false := by
                have e0 : p0 ∉ S w := fun h => Finset.disjoint_left.mp (hmf1.1 w hwY) h hp0
                have e1 : p1 ∉ S w := fun h => Finset.disjoint_left.mp (hmf1.1 w hwY) h hp1
                have e2 : p2 ∉ S w := fun h => Finset.disjoint_left.mp (hmf1.1 w hwY) h hp2
                rw [← hpres p0 w, hp0e, hincb] at e0
                rw [← hpres p1 w, hp1e, hincb] at e1
                rw [← hpres p2 w, hp2e, hincb] at e2
                exact ⟨Bool.eq_false_iff.mpr e0, Bool.eq_false_iff.mpr e1, Bool.eq_false_iff.mpr e2⟩
              have hmem := (htri0_miss_b (τL w)).mp hmiss
              simp [hmem]
            have hhit3 : ∃ w' ∈ ({3, 7, 8, 9} : Finset (Fin 13)), τP p3 ∈ S w' := by
              have hne0 : τP p3 ≠ 0 := fun h => hp3n (by rw [← hp0e] at h; simp [hbP.1 h])
              have hne1 : τP p3 ≠ 1 := fun h => hp3n (by rw [← hp1e] at h; simp [hbP.1 h])
              have hne2 : τP p3 ≠ 2 := fun h => hp3n (by rw [← hp2e] at h; simp [hbP.1 h])
              rcases htri0_hit_b (τP p3) hne0 hne1 hne2 with h | h | h | h
              · exact ⟨3, by simp, (hincb _ _).mpr h⟩
              · exact ⟨7, by simp, (hincb _ _).mpr h⟩
              · exact ⟨8, by simp, (hincb _ _).mpr h⟩
              · exact ⟨9, by simp, (hincb _ _).mpr h⟩
            obtain ⟨w'bad, hw'bad_mem, hw'bad_inc⟩ := hhit3
            have hw'bad_not : w'bad ∉ Y1.image τL := by
              intro hmem
              obtain ⟨w, hwY, rfl⟩ := Finset.mem_image.mp hmem
              exact Finset.disjoint_left.mp (hmf1.1 w hwY) ((hpres p3 w).mp hw'bad_inc) hp3X
            have hY1_card : Y1.card ≤ 3 := by
              have hsub2 : Y1.image τL ⊆ ({3, 7, 8, 9} : Finset (Fin 13)) \ {w'bad} := by
                intro u hu
                exact Finset.mem_sdiff.mpr ⟨hY1_sub hu, by simp; rintro rfl; exact hw'bad_not hu⟩
              have hc1 : (Y1.image τL).card = Y1.card := Finset.card_image_of_injective Y1 hbL.1
              have hc2 : (({3, 7, 8, 9} : Finset (Fin 13)) \ {w'bad}).card ≤ 3 := by
                have h4 : ({3, 7, 8, 9} : Finset (Fin 13)).card = 4 := by
                  rw [Finset.card_insert_of_notMem (by decide), Finset.card_insert_of_notMem (by decide),
                    Finset.card_pair (by decide)]
                have hs : ({w'bad} : Finset (Fin 13)) ⊆ {3, 7, 8, 9} := Finset.singleton_subset_iff.mpr hw'bad_mem
                rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hs, Finset.card_singleton, h4]
              rw [← hc1]
              exact (Finset.card_le_card hsub2).trans hc2
            let C3 := mapC ρ_dual C2
            let X3 : Finset (Fin 13) := Y1.image fun w => -w
            let Y3 : Finset (Fin 13) := X1.image fun p => -p
            have hC3_ao := hmap_ao2 C2 ρ_dual hdual_lt hdual_ge hC2ao
            have hC3_nd := hmap_nodup C2 ρ_dual hdual_inj hC2ao.2.2 (fun j hj => Nat.ne_of_lt (hC2lt j hj))
            have hC3_sz : C3.size = C.size := (List.length_map _).trans hC2sz
            have hC2_ge26 : 26 ≤ C2.output := by
              by_contra hlt
              have hdeg1 : C2.lineDeg 26 (Finset.Ico 13 26) ≤ 1 := by
                unfold Circuit.lineDeg Circuit.lineDegrees
                have hpref : ∀ (gs : List Gate) (init : List ℕ) (i : ℕ), i < init.length →
                    (gs.foldl (fun d g => d ++ [g.lineDegree d]) init).getD i 0 = init.getD i 0 := by
                  intro gs
                  induction gs with
                  | nil => intro init i _; rfl
                  | cons g gs ih =>
                    intro init i hi
                    rw [List.foldl_cons, ih _ i (by simp; omega)]
                    exact hsnoc_lt init _ 0 i hi
                rw [hpref _ _ C2.output (by simp; omega), List.getD_eq_getElem?_getD,
                  List.getElem?_map, List.getElem?_range (by omega)]
                simp only [Option.map_some, Option.getD_some]
                split_ifs <;> omega
              omega
            have hC3_out : C3.output + 1 = 26 + C3.size := by
              have : C3.output = C2.output := hdual_ge C2.output hC2_ge26
              omega
            have hC3_live : liveSize 26 C3 = C3.size := by
              rw [hmap_live C2 ρ_dual hdual_lt hdual_ge hC2_ge26, hC2live, hC3_sz, hC2sz]
            have hC3_ld : 3 ≤ C3.lineDeg 26 (Finset.Ico 13 26) := by
              rw [hmap_deg C2 ρ_dual (Finset.range 13) (Finset.Ico 13 26) hdual_lt hdual_ge hdual_Ico]
              exact hC2pd3
            have hC3_pd : 3 ≤ C3.lineDeg 26 (Finset.range 13) := by
              rw [hmap_deg C2 ρ_dual (Finset.Ico 13 26) (Finset.range 13) hdual_lt hdual_ge hdual_range]
              exact hC2ld3
            have hC3_sep := hdual_degSep C2 hC2sep
            have hC3_eval : C3.eval (incidenceInput X3 Y3) = true := by
              rw [hdual_eval C2 X3 Y3]
              have hX3' : Y3.image (fun w => -w) = X1 := by
                ext p; simp [Y3]
              have hY3' : X3.image (fun p => -p) = Y1 := by
                ext w; simp [X3]
              rw [hX3', hY3']
              exact hC2_X1Y1
            have hmf3 : IsMaximalFalse S X3 Y3 := by
              refine ⟨?_, ?_, ?_⟩
              · intro u hu
                obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
                rw [Finset.disjoint_left]
                intro q hq hqX3
                obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hqX3
                exact Finset.disjoint_left.mp (hmf1.1 w hw) ((hS_dual p w).mpr hq) hp
              · intro q hq hfalse
                have hnot : -q ∉ Y1 := fun h => hq (Finset.mem_image.mpr ⟨-q, h, neg_neg q⟩)
                apply hmf1.2.2 (-q) hnot
                intro u hu
                rw [Finset.mem_insert] at hu
                rcases hu with rfl | hu
                · rw [Finset.disjoint_left]
                  intro p hp hpX
                  have h1 := hfalse (-p) (Finset.mem_image.mpr ⟨p, hpX, rfl⟩)
                  exact Finset.disjoint_left.mp h1 ((hS_dual p (-q)).mp hp) (by rw [neg_neg]; exact Finset.mem_insert_self q X3)
                · exact hmf1.1 u hu
              · intro u hu hfalse
                have hnot : -u ∉ X1 := fun h => hu (Finset.mem_image.mpr ⟨-u, h, neg_neg u⟩)
                apply hmf1.2.1 (-u) hnot
                intro w hw
                rw [Finset.disjoint_left]
                intro p hp hpIns
                rw [Finset.mem_insert] at hpIns
                rcases hpIns with rfl | hpX
                · have h1 := hfalse u (Finset.mem_insert_self u Y3)
                  have hmem : -w ∈ X3 := Finset.mem_image.mpr ⟨w, hw, rfl⟩
                  have hinc : -w ∈ S u := by
                    have := (hS_dual (-u) w).mp hp; rwa [neg_neg] at this
                  exact Finset.disjoint_left.mp h1 hinc hmem
                · exact Finset.disjoint_left.mp (hmf1.1 w hw) hp hpX
            have hX3_nl : InNoLine S X3 := by
              intro w hw
              apply hgen1.2 (-w)
              intro u hu
              have : -u ∈ S w := hw (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
              have h1 := (hS_dual (-w) u).mpr (by rwa [neg_neg])
              exact h1
            obtain ⟨q0, q1, q2, hq0, hq1, hq2, hnc3⟩ := hpick_tri X3 hX3_nl
            have hq_ne01 : q0 ≠ q1 := fun h => hnc3 (by
              obtain ⟨w, hw0, hw2⟩ := hS_twoPts q0 q2
              exact ⟨w, hw0, h ▸ hw0, hw2⟩)
            have hq_ne02 : q0 ≠ q2 := fun h => hnc3 (by
              obtain ⟨w, hw0, hw1⟩ := hS_twoPts q0 q1
              exact ⟨w, hw0, hw1, h ▸ hw0⟩)
            have hq_ne12 : q1 ≠ q2 := fun h => hnc3 (by
              obtain ⟨w, hw0, hw1⟩ := hS_twoPts q0 q1
              exact ⟨w, hw0, hw1, h ▸ hw1⟩)
            have hX3_card : X3.card ≤ 3 := by
              have hneg_inj : Function.Injective (fun w : Fin 13 => -w) := fun a b h => by
                have := congrArg Neg.neg h; simpa using this
              rw [Finset.card_image_of_injective Y1 hneg_inj]
              exact hY1_card
            have hX3_sub : ({q0, q1, q2} : Finset (Fin 13)) ⊆ X3 := by
              intro q hq
              simp only [Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with rfl | rfl | rfl <;> assumption
            have h3card : ({q0, q1, q2} : Finset (Fin 13)).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [hq_ne01, hq_ne02]), Finset.card_pair hq_ne12]
            have hX3_eq : X3 = {q0, q1, q2} :=
              (Finset.eq_of_subset_of_card_le hX3_sub (by omega)).symm
            exact hfinish_tri C3 X3 Y3 q0 q1 q2 hC3_sz hC3_out hC3_ao hC3_live hC3_nd
              hC3_ld hC3_pd hC3_sep hmf3 hX3_eq hnc3 hC3_eval
