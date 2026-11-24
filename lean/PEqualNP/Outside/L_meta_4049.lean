import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4049

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def orsGo (k p : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], p)
  | a :: t => (⟨GateOp.or, [p, a]⟩ :: (orsGo (k + 1) k t).1, (orsGo (k + 1) k t).2)

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem or_eval_two (x y : Bool) : GateOp.or.eval [x, y] = (x || y) := by
  cases x <;> cases y <;> simp [GateOp.eval]

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by
      simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem orsGo_fst_length : ∀ (k p : ℕ) (t : List ℕ), (orsGo k p t).1.length = t.length := by
  intro k p t
  induction t generalizing k p with
  | nil => rfl
  | cons a t ih => simp only [orsGo, List.length_cons, ih]

theorem orsGo_fan : ∀ (k p : ℕ) (t : List ℕ) (g : Gate), g ∈ (orsGo k p t).1 →
    g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  intro k p t g
  induction t generalizing k p with
  | nil => intro hg; simp only [orsGo] at hg; cases hg
  | cons a t ih =>
    intro hg
    have hgo : orsGo k p (a :: t) =
        (⟨GateOp.or, [p, a]⟩ :: (orsGo (k + 1) k t).1, (orsGo (k + 1) k t).2) := by
      simp only [orsGo]
    rw [hgo] at hg
    rcases List.mem_cons.1 hg with rfl | h
    · exact ⟨rfl, by simp⟩
    · exact ih (k + 1) k h

theorem evalGo : ∀ (k p : ℕ) (t : List ℕ), (∀ i ∈ t, i < k) → ∀ (w : List Bool), w.length = k →
    ((orsGo k p t).1.foldl step w).getD (orsGo k p t).2 false =
      ((p :: t).map fun i => w.getD i false).any id := by
  intro k p t
  induction t generalizing k p with
  | nil => intro _ w _; simp only [orsGo, List.foldl_nil, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, id_eq, Bool.or_false]
  | cons a t ih =>
    intro ht w hw
    have hstep : step w ⟨GateOp.or, [p, a]⟩ =
        w ++ [GateOp.or.eval ([p, a].map fun i => w.getD i false)] := rfl
    have hgo : orsGo k p (a :: t) =
        (⟨GateOp.or, [p, a]⟩ :: (orsGo (k + 1) k t).1, (orsGo (k + 1) k t).2) := by
      simp only [orsGo]
    rw [hgo, List.foldl_cons]
    have hw' : (step w ⟨GateOp.or, [p, a]⟩).length = k + 1 := by
      rw [hstep]
      simp only [List.length_append, List.length_cons, List.length_nil, hw]
    rw [ih (k + 1) k (fun i hi => by have h := ht i (List.mem_cons_of_mem _ hi); omega)
      (step w ⟨GateOp.or, [p, a]⟩) hw']
    have hhead : (step w ⟨GateOp.or, [p, a]⟩).getD k false = (w.getD p false || w.getD a false) := by
      rw [hstep, ← hw, getD_snoc_eq]
      simp only [List.map_cons, List.map_nil]
      rw [or_eval_two]
    have htail : t.map (fun i => (step w ⟨GateOp.or, [p, a]⟩).getD i false) =
        t.map (fun i => w.getD i false) := by
      apply List.map_congr_left
      intro i hi
      have hi' : i < w.length := by have h := ht i (List.mem_cons_of_mem _ hi); omega
      rw [hstep]
      exact List.getD_append _ _ _ _ hi'
    simp only [List.map_cons, List.any_cons, id_eq]
    rw [hhead, htail]
    exact Bool.or_assoc _ _ _

end PEqualNP.Outside.L_meta_4049

open PEqualNP.Outside.L_meta_4049 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_4049 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1)) (x3 : (Fin x1 → Bool) → Bool) (x4 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x4 → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x6 : Fin x1 → Bool) => x3 x6 || Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)) (x4 + x2.card) := by
  intro x1 x2 x3 x4 h
  obtain ⟨C, hok, hsz, hev⟩ := h
  set L : List ℕ := (x2.sort (· ≤ ·)).map Fin.val with hL
  set k : ℕ := x1 + C.gates.length with hk
  refine ⟨⟨C.gates ++ (orsGo k C.output L).1, (orsGo k C.output L).2⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h' | h'
    · exact hok g h'
    · obtain ⟨h1, h2⟩ := orsGo_fan k C.output L g h'
      exact ⟨by rw [h1]; simp, h2⟩
  · have h1 : (orsGo k C.output L).1.length = L.length := orsGo_fst_length k C.output L
    have h2 : L.length = x2.card := by rw [hL]; simp
    have h3 : C.size = C.gates.length := rfl
    show (C.gates ++ (orsGo k C.output L).1).length ≤ x4 + x2.card
    rw [List.length_append]
    omega
  · intro x
    have hw : (C.gates.foldl step (List.ofFn x)).length = k := by
      rw [run_length, List.length_ofFn, hk]
    have hin : ∀ a : Fin x1, (C.gates.foldl step (List.ofFn x)).getD (a : ℕ) false = x a := by
      intro a
      rw [run_keep C.gates (List.ofFn x) (a : ℕ) (by rw [List.length_ofFn]; exact a.is_lt)]
      simp
    have hwout : (C.gates.foldl step (List.ofFn x)).getD C.output false = x3 x := hev x
    have hmem : ∀ i ∈ L, i < k := by
      intro i hi
      rw [hL] at hi
      obtain ⟨a, _ha, rfl⟩ := List.mem_map.1 hi
      have hlt := a.is_lt
      omega
    have hany : ((L.map fun i => (C.gates.foldl step (List.ofFn x)).getD i false).any id = true) ↔
        ∃ x7 ∈ x2, x x7 = Bool.true := by
      constructor
      · intro h
        rw [List.any_eq_true] at h
        obtain ⟨i, hi, hv⟩ := h
        rw [hL] at hi
        obtain ⟨a, ha, hai⟩ := List.mem_map.1 hi
        have hai' : (C.gates.foldl step (List.ofFn x)).getD a false = i := hai
        obtain ⟨b, hb, hab⟩ := List.mem_map.1 ha
        refine ⟨b, (Finset.mem_sort (· ≤ ·)).mp hb, ?_⟩
        rw [← hin b, hab, hai']
        exact hv
      · intro ⟨a, ha, hx⟩
        rw [List.any_eq_true]
        refine ⟨(C.gates.foldl step (List.ofFn x)).getD (a : ℕ) false, ?_, ?_⟩
        · rw [hL]
          exact List.mem_map.2 ⟨(a : ℕ),
            List.mem_map.2 ⟨a, (Finset.mem_sort (· ≤ ·)).mpr ha, rfl⟩, rfl⟩
        · rw [hin a, hx]; rfl
    have hdec : Decidable.decide (∃ x7 ∈ x2, x x7 = Bool.true) =
        (L.map fun i => (C.gates.foldl step (List.ofFn x)).getD i false).any id := by
      by_cases h' : ∃ x7 ∈ x2, x x7 = Bool.true
      · rw [decide_eq_true h', hany.mpr h']
      · rw [decide_eq_false h']
        exact (Bool.eq_false_iff.2 fun hc => h' (hany.mp hc)).symm
    show ((C.gates ++ (orsGo k C.output L).1).foldl step (List.ofFn x)).getD
        (orsGo k C.output L).2 false = (x3 x || Decidable.decide (∃ x7 ∈ x2, x x7 = Bool.true))
    rw [List.foldl_append, evalGo k C.output L hmem (C.gates.foldl step (List.ofFn x)) hw]
    simp only [List.map_cons, List.any_cons, id_eq, hwout, hdec]
