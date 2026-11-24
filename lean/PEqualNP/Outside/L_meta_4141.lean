import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4141

open PEqualNP.CircuitLowerBounds

abbrev step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma fold_length : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp only [List.foldl_cons, ih, List.length_append,
      List.length_cons, List.length_nil]; omega

lemma fold_prefix : ∀ (gs : List Gate) (w : List Bool), ∃ t, gs.foldl step w = w ++ t := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (step w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t,
      by simp only [List.foldl_cons, ht, step, List.append_assoc]⟩

/-- the 21 inputs of the given circuit, as positions among the 26 -/
def pts : List (Fin 26) :=
  List.filter (fun (x2 : Fin 26) => decide ((x2 : ℕ) ∉ [(0 : ℕ), 1, 3, 9, 13])) (List.finRange 26)

lemma pts_length : pts.length = 21 := by decide

/-- relabelling of wire indices of the given circuit -/
def r (i : ℕ) : ℕ := if i < 21 then ((pts.getD i 0 : Fin 26) : ℕ) else i + 24

def relabel (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

lemma point (A B T : List Bool) (hA : A.length = 45) (hB : B.length = 21)
    (hAB : ∀ i < 21, A.getD ((pts.getD i 0 : Fin 26) : ℕ) false = B.getD i false) (i : ℕ) :
    (A ++ T).getD (r i) false = (B ++ T).getD i false := by
  unfold r
  split_ifs with h
  · have h1 : ((pts.getD i 0 : Fin 26) : ℕ) < A.length := by
      rw [hA]; have := (pts.getD i 0).isLt; omega
    rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ (by rw [hB]; exact h)]
    exact hAB i h
  · rw [List.getD_append_right _ _ _ _ (by rw [hA]; omega),
      List.getD_append_right _ _ _ _ (by rw [hB]; omega), hA, hB]
    congr 1

lemma fold_rel (A B : List Bool) (hA : A.length = 45) (hB : B.length = 21)
    (hAB : ∀ i < 21, A.getD ((pts.getD i 0 : Fin 26) : ℕ) false = B.getD i false) :
    ∀ (gs : List Gate) (T : List Bool), ∃ T2,
      (gs.map relabel).foldl step (A ++ T) = A ++ T2 ∧ gs.foldl step (B ++ T) = B ++ T2 := by
  intro gs
  induction gs with
  | nil => intro T; exact ⟨T, by simp, by simp⟩
  | cons g gs ih =>
    intro T
    have hv : (relabel g).op.eval ((relabel g).inputs.map fun i => (A ++ T).getD i false) =
        g.op.eval (g.inputs.map fun i => (B ++ T).getD i false) := by
      simp only [relabel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact point A B T hA hB hAB i
    obtain ⟨T2, h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i => (B ++ T).getD i false)])
    refine ⟨T2, ?_, ?_⟩
    · rw [List.map_cons, List.foldl_cons, step, hv, List.append_assoc]
      exact h1
    · rw [List.foldl_cons, step, List.append_assoc]
      exact h2

def g2 (o : GateOp) (a b : ℕ) : Gate := ⟨o, [a, b]⟩

/-- 19 gates computing the incidences at the points 0, 1, 3, 9 into wire 44 -/
def extras : List Gate :=
  [g2 .or 13 25, g2 .or 26 23, g2 .or 27 17, g2 .and 0 28,
   g2 .or 14 13, g2 .or 30 24, g2 .or 31 18, g2 .and 1 32,
   g2 .or 16 15, g2 .or 34 13, g2 .or 35 20, g2 .and 3 36,
   g2 .or 22 21, g2 .or 38 19, g2 .or 39 13, g2 .and 9 40,
   g2 .or 29 33, g2 .or 42 37, g2 .or 43 41]

def pairs26 : List (Fin 26 × Fin 26) :=
  [(0, 13), (0, 25), (0, 23), (0, 17), (1, 14), (1, 13), (1, 24), (1, 18),
   (3, 16), (3, 15), (3, 13), (3, 20), (9, 22), (9, 21), (9, 19), (9, 13)]

def D : Finset (Fin 13) := {0, 1, 3, 9}

lemma key : ∀ p l : Fin 13, p ∈ D ∧ p - l ∈ D → (Fin.castAdd 13 p, Fin.natAdd 13 l) ∈ pairs26 := by
  decide +kernel

lemma key2 : ∀ q ∈ pairs26, ∃ p l : Fin 13,
    q = (Fin.castAdd 13 p, Fin.natAdd 13 l) ∧ p ∈ D ∧ p - l ∈ D := by
  decide +kernel

lemma x3_eq (x : Fin 26 → Bool) :
    decide (∃ p ∈ D, ∃ l : Fin 13, p - l ∈ D ∧ x (Fin.castAdd 13 p) = true ∧
      x (Fin.natAdd 13 l) = true) = pairs26.any (fun q => x q.1 && x q.2) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.any_eq_true]
  constructor
  · rintro ⟨p, hp, l, hl, h1, h2⟩
    exact ⟨_, key p l ⟨hp, hl⟩, by simp only [Bool.and_eq_true]; exact ⟨h1, h2⟩⟩
  · rintro ⟨q, hm, hv⟩
    obtain ⟨p, l, rfl, hp, hl⟩ := key2 q hm
    simp only [Bool.and_eq_true] at hv
    exact ⟨p, hp, l, hl, hv.1, hv.2⟩

lemma ofFn26 (x : Fin 26 → Bool) : List.ofFn x =
    [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16,
     x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_ofFn]
  simp only [List.length_ofFn] at h1
  interval_cases n <;> rfl

lemma w44 (x : Fin 26 → Bool) :
    (extras.foldl step (List.ofFn x)).getD 44 false = pairs26.any (fun q => x q.1 && x q.2) := by
  rw [ofFn26]
  simp only [extras, g2, pairs26, List.foldl_cons, List.foldl_nil, step, List.map_cons,
    List.map_nil, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil,
    id, Bool.or_false, Bool.and_true, List.getD_eq_getElem?_getD, List.cons_append,
    List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]

lemma monoExtras : ∀ g ∈ extras, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
    g.inputs.length ≤ 2 := by
  intro g hg
  simp only [extras, g2, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma build (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size ≤ C.size + 20 ∧
      ∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 26 C' x =
        (C.eval (List.map x pts) || pairs26.any (fun q => x q.1 && x q.2)) := by
  refine ⟨⟨extras ++ C.gates.map relabel ++ [g2 .or (r C.output) 44], 45 + C.size⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨g0, hg0, rfl⟩) | rfl
    · exact monoExtras g hg
    · exact ⟨(hC g0 hg0).1, by simpa [relabel] using (hC g0 hg0).2⟩
    · simp [g2]
  · simp [Circuit.size, extras]
  · intro x
    obtain ⟨E, hE⟩ := fold_prefix extras (List.ofFn x)
    set A := extras.foldl step (List.ofFn x) with hAdef
    have hAlen : A.length = 45 := by rw [hAdef, fold_length]; simp [extras]
    have hElen : E.length = 19 := by
      have := congrArg List.length hE; rw [hAlen] at this; simp at this; omega
    have hAB : ∀ i < 21, A.getD ((pts.getD i 0 : Fin 26) : ℕ) false =
        (List.map x pts).getD i false := by
      intro i hi
      have hp : i < pts.length := by rw [pts_length]; exact hi
      rw [hE, List.getD_append _ _ _ _ (by simp)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hp,
        Option.map_some, Option.getD_some, List.getElem?_ofFn]
      simp
    obtain ⟨T2, h1, h2⟩ := fold_rel A (List.map x pts) hAlen (by simp [pts_length]) hAB
      C.gates []
    simp only [List.append_nil] at h1 h2
    have hT2 : T2.length = C.size := by
      have := congrArg List.length h1
      rw [fold_length, List.length_append, hAlen, List.length_map] at this
      simp only [Circuit.size]; omega
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, wires_eq, List.foldl_append]
    rw [← hAdef, h1, List.foldl_cons, List.foldl_nil, step]
    rw [List.getD_append_right _ _ _ _ (by simp [hAlen, hT2])]
    simp only [List.length_append, hAlen, hT2, Nat.sub_self, List.getD_cons_zero, g2,
      List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
    have e1 := point A (List.map x pts) T2 hAlen (by simp [pts_length]) hAB C.output
    rw [e1, List.getD_append A T2 false 44 (by rw [hAlen]; omega), hAdef, w44, h2]

end PEqualNP.Outside.L_meta_4141

theorem PEqualNP.Outside.L_meta_4141 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (Fin (26 : ℕ)) := List.filter (fun (x2 : Fin (26 : ℕ)) => Decidable.decide (↑x2 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ), (13 : ℕ)])) (List.finRange (26 : ℕ)); have x3 : (Fin (26 : ℕ) → Bool) → Bool := fun (x3 : Fin (26 : ℕ) → Bool) => Decidable.decide (∃ x4 ∈ x1, ∃ (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x4.output < (21 : ℕ) + x4.size → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size ≤ x4.size + (20 : ℕ) ∧ ∀ (x8 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 x8 = (x4.eval (List.map x8 x2) || x3 x8) := by
  intro x1 x2 x3 C hC _
  obtain ⟨C', h1, h2, h3⟩ := PEqualNP.Outside.L_meta_4141.build C hC
  refine ⟨C', h1, h2, fun x => ?_⟩
  rw [h3 x]
  congr 1
  exact (PEqualNP.Outside.L_meta_4141.x3_eq x).symm
