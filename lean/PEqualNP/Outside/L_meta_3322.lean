import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3322

def rename (p : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ :=
  if hi : i < 14 then (p ⟨i, hi⟩).val else i

lemma rename_input (p : Equiv.Perm (Fin 14)) (i : Fin 14) :
    rename p i = (p i).val := dite_eq_left i.isLt

lemma rename_lt (p : Equiv.Perm (Fin 14)) {i b : ℕ} (hb : 14 ≤ b) :
    rename p i < b ↔ i < b := by
  by_cases hi : i < 14
  · rw [rename, dite_eq_left hi]
    exact iff_of_true (lt_of_lt_of_le (p ⟨i, hi⟩).isLt hb) (lt_of_lt_of_le hi hb)
  · simp [rename, hi]

lemma rename_bound (p : Equiv.Perm (Fin 14)) {i b : ℕ}
    (hb : 14 ≤ b) (hi : i < b) : rename p i < b :=
  (rename_lt p hb).2 hi

lemma rename_id (i : ℕ) : rename (Equiv.refl (Fin 14)) i = i := by
  by_cases hi : i < 14 <;> simp [rename, hi]

lemma rename_trans (p q : Equiv.Perm (Fin 14)) (i : ℕ) :
    rename q (rename p i) = rename (p.trans q) i := by
  by_cases hi : i < 14
  · simp [rename, hi, (p ⟨i, hi⟩).isLt]
  · simp [rename, hi]

lemma rename_injective (p : Equiv.Perm (Fin 14)) : Function.Injective (rename p) := by
  intro i j h
  have leftInverse (k : ℕ) : rename p.symm (rename p k) = k := by
    rw [rename_trans, Equiv.self_trans_symm, rename_id]
  simpa only [leftInverse] using congrArg (rename p.symm) h

def renameGate (p : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rename p)⟩

def renameCircuit (p : Equiv.Perm (Fin 14)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate p), rename p C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma ofFn_getD (x : Fin 14 → Bool) (i : Fin 14) :
    (List.ofFn x).getD i false = x i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]

lemma getD_ofFn_rename (p : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool) (i : ℕ) :
    (List.ofFn x).getD (rename p i) false = (List.ofFn (x ∘ p)).getD i false := by
  by_cases hi : i < 14
  · let j : Fin 14 := ⟨i, hi⟩
    change (List.ofFn x).getD (rename p j) false = (List.ofFn (x ∘ p)).getD j false
    rw [rename_input, ofFn_getD, ofFn_getD]
    rfl
  · simp only [rename, dite_eq_right hi]
    rw [List.getD_eq_default, List.getD_eq_default] <;> simpa using Nat.le_of_not_lt hi

lemma fold_rename (p : Equiv.Perm (Fin 14)) (gs : List Gate)
    (w v : List Bool) (hlen : w.length = v.length) (hbase : 14 ≤ w.length)
    (hw : ∀ i, v.getD (rename p i) false = w.getD i false) (i : ℕ) :
    (List.foldl step v (gs.map (renameGate p))).getD (rename p i) false =
      (List.foldl step w gs).getD i false := by
  induction gs generalizing w v with
  | nil => exact hw i
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hval :
        (g.inputs.map (rename p)).map (fun j => v.getD j false) =
          g.inputs.map (fun j => w.getD j false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun j _ => hw j)
    apply ih
    · simp [step, hlen]
    · simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    · intro j
      simp only [step, renameGate, hval]
      have hj := rename_lt p (i := j) hbase
      by_cases h : j < w.length
      · rw [List.getD_append _ _ _ _ (hlen ▸ hj.2 h), List.getD_append _ _ _ _ h]
        exact hw j
      · have hr : w.length ≤ rename p j := Nat.le_of_not_lt (fun hh => h (hj.1 hh))
        rw [List.getD_append_right _ _ _ _ (hlen ▸ hr),
          List.getD_append_right _ _ _ _ (Nat.le_of_not_lt h), ← hlen]
        have hjbase : ¬ j < 14 := by omega
        simp [rename, hjbase]

lemma eval_rename (p : Equiv.Perm (Fin 14)) (C : Circuit) (x : Fin 14 → Bool) :
    (renameCircuit p C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ p)) := by
  exact fold_rename p C.gates _ _ (by simp) (by simp) (getD_ofFn_rename p x) C.output

def score (a b c d : ℕ) : ℕ :=
  (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

def preserves (f : (Fin 14 → Bool) → Bool) (p : Equiv.Perm (Fin 14)) : Prop :=
  ∀ x, f (x ∘ p) = f x

lemma orbit_min (f : (Fin 14 → Bool) → Bool) (a b c d : ℕ) :
    ∃ p : Equiv.Perm (Fin 14), preserves f p ∧
      ∀ q : Equiv.Perm (Fin 14), preserves f q →
        score (rename p a) (rename p b) (rename p c) (rename p d) ≤
          score (rename q (rename p a)) (rename q (rename p b))
            (rename q (rename p c)) (rename q (rename p d)) := by
  classical
  let S : ℕ → Prop := fun k => ∃ p : Equiv.Perm (Fin 14), preserves f p ∧
    k = score (rename p a) (rename p b) (rename p c) (rename p d)
  have hS : ∃ k, S k :=
    ⟨_, Equiv.refl (Fin 14), fun _ => rfl, rfl⟩
  obtain ⟨p, hp, heq⟩ := Nat.find_spec hS
  refine ⟨p, hp, fun q hq => ?_⟩
  rw [← heq]
  apply Nat.find_min'
  refine ⟨p.trans q, ?_, ?_⟩
  · intro x
    calc
      f (x ∘ ⇑(p.trans q)) = f ((x ∘ q) ∘ p) := rfl
      _ = f (x ∘ q) := hp _
      _ = f x := hq _
  · simp only [rename_trans]

lemma sort_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (v : ℕ → Bool) (a b : ℕ) :
    op.eval [v (min a b), v (max a b)] = op.eval [v a, v b] := by
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right hba, max_eq_left hba]
    rcases hop with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

lemma sort_score (r : ℕ → ℕ) (a b c d : ℕ) :
    score (r (min a b)) (r (max a b)) (r (min c d)) (r (max c d)) =
      score (r a) (r b) (r c) (r d) := by
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · simp [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd]
  · simp [score, min_eq_left hab, max_eq_right hab, min_eq_right hdc, max_eq_left hdc,
      min_comm (r d) (r c), max_comm (r d) (r c)]
  · simp [score, min_eq_right hba, max_eq_left hba, min_eq_left hcd, max_eq_right hcd,
      min_comm (r b) (r a), max_comm (r b) (r a)]
  · simp [score, min_eq_right hba, max_eq_left hba, min_eq_right hdc, max_eq_left hdc,
      min_comm (r b) (r a), max_comm (r b) (r a), min_comm (r d) (r c), max_comm (r d) (r c)]

lemma rename_fin15 (p : Equiv.Perm (Fin 14)) (i : Fin 15) :
    rename p i = if i < (14 : Fin 15) then (p (Fin.ofNat 14 i.val)).val else 14 := by
  by_cases hi : i.val < 14
  · have hfin : i < (14 : Fin 15) := hi
    rw [ite_eq_left hfin, rename, dite_eq_left hi]
    congr 1
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt hi]
  · have hfin : ¬ i < (14 : Fin 15) := hi
    have hi' : i.val < 15 := i.isLt
    simp only [ite_eq_right hfin, rename, dite_eq_right hi]
    omega

lemma split_gates (C : Circuit) (hsize : 2 ≤ C.size) :
    ∃ g h gs out, C = ⟨g :: h :: gs, out⟩ := by
  rcases C with ⟨gates, out⟩
  cases gates with
  | nil => simp [Circuit.size] at hsize
  | cons g gates =>
    cases gates with
    | nil => simp [Circuit.size] at hsize
    | cons h gs => exact ⟨g, h, gs, out, rfl⟩

lemma first_bounds {g h : Gate} {gs : List Gate} {out a b c d : ℕ}
    (hC : PEqualNP.TopForm.IsAO2 14 ⟨g :: h :: gs, out⟩)
    (hg : g.inputs = [a, b]) (hh : h.inputs = [c, d]) :
    a < 14 ∧ b < 14 ∧ c < 15 ∧ d < 15 := by
  have h₁ : ∀ i ∈ [a, b], i < 14 := by
    simpa [NestedCover.gateAt, hg] using hC.2.1 0 (by simp)
  have h₂ : ∀ i ∈ [c, d], i < 15 := by
    simpa [NestedCover.gateAt, hh] using hC.2.1 1 (by simp)
  exact ⟨h₁ a (by simp), h₁ b (by simp), h₂ c (by simp), h₂ d (by simp)⟩

end PEqualNP.Outside.L_meta_3322

open PEqualNP.Outside.L_meta_3322

theorem PEqualNP.Outside.L_meta_3322 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if x10 < (14 : Fin (15 : ℕ)) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  intro f C hC hnd hsize hmax hf
  obtain ⟨g, h, gs, out, rfl⟩ := split_gates C hsize
  have hgmem : g ∈ g :: h :: gs := List.mem_cons_self
  have hhmem : h ∈ g :: h :: gs := List.mem_cons_of_mem _ List.mem_cons_self
  have hgop := hC.1 g hgmem
  have hhop := hC.1 h hhmem
  obtain ⟨a, b, hg⟩ := List.length_eq_two.mp (hC.2.2 g hgmem)
  obtain ⟨c, d, hh⟩ := List.length_eq_two.mp (hC.2.2 h hhmem)
  obtain ⟨ha, hb, hc, hd⟩ := first_bounds hC hg hh
  have hab : a ≠ b := by simpa [hg] using hnd g hgmem
  have hcd : c ≠ d := by simpa [hh] using hnd h hhmem
  obtain ⟨p, hp, hpmin⟩ := orbit_min f a b c d
  let A : Fin 14 :=
    ⟨min (rename p a) (rename p b), lt_of_le_of_lt (min_le_left ..) (rename_bound p le_rfl ha)⟩
  let B : Fin 14 :=
    ⟨max (rename p a) (rename p b), max_lt_iff.mpr
      ⟨rename_bound p le_rfl ha, rename_bound p le_rfl hb⟩⟩
  let E : Fin 15 :=
    ⟨min (rename p c) (rename p d), lt_of_le_of_lt (min_le_left ..) (rename_bound p (by decide) hc)⟩
  let F : Fin 15 :=
    ⟨max (rename p c) (rename p d), max_lt_iff.mpr
      ⟨rename_bound p (by decide) hc, rename_bound p (by decide) hd⟩⟩
  let D := renameCircuit p ⟨gs, out⟩
  refine ⟨A, B, E, F, g.op, h.op, D, ?_, ?_, hgop, hhop, ?_, ?_, ?_, ?_⟩
  · exact min_lt_max.mpr (fun eq => hab (rename_injective p eq))
  · exact min_lt_max.mpr (fun eq => hcd (rename_injective p eq))
  · intro q hq
    change score A B E F ≤ score (q A) (q B)
      (if E < (14 : Fin 15) then (q (Fin.ofNat 14 E.val)).val else 14)
      (if F < (14 : Fin 15) then (q (Fin.ofNat 14 F.val)).val else 14)
    rw [← rename_input q A, ← rename_input q B, ← rename_fin15 q E, ← rename_fin15 q F]
    exact (sort_score id _ _ _ _).le.trans ((hpmin q hq).trans (sort_score (rename q) _ _ _ _).ge)
  · intro k hk
    change k ∈ gs.map (renameGate p) at hk
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    have hjmem : j ∈ g :: h :: gs := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)
    rcases hC.1 j hjmem with hop | hop <;>
      simp [renameGate, hop, show j.inputs.length = 2 from hC.2.2 j hjmem]
  · change (gs.map (renameGate p)).length ≤ 24
    simp only [Circuit.size, List.length_cons] at hmax
    rw [List.length_map]
    omega
  · intro x
    let xs := List.ofFn x ++ [g.op.eval [x A, x B]]
    change D.eval (xs ++ [h.op.eval [xs.getD E false, xs.getD F false]]) = f x
    have hstep1 : step (List.ofFn x) (renameGate p g) = xs := by
      simp only [step, renameGate, hg, List.map_cons, List.map_nil, xs]
      rw [← sort_eval g.op hgop (fun i => (List.ofFn x).getD i false) (rename p a) (rename p b)]
      change List.ofFn x ++ [g.op.eval [(List.ofFn x).getD A false, (List.ofFn x).getD B false]] = _
      rw [ofFn_getD, ofFn_getD]
    have hstep2 :
        step xs (renameGate p h) = xs ++ [h.op.eval [xs.getD E false, xs.getD F false]] := by
      simp only [step, renameGate, hh, List.map_cons, List.map_nil]
      exact congrArg (fun v => xs ++ [v])
        (sort_eval h.op hhop (fun i => xs.getD i false) (rename p c) (rename p d)).symm
    have hsplit :
        (renameCircuit p ⟨g :: h :: gs, out⟩).eval (List.ofFn x) =
          D.eval (step (step (List.ofFn x) (renameGate p g)) (renameGate p h)) := rfl
    rw [← hstep2, ← hstep1, ← hsplit, eval_rename, hf, hp x]
