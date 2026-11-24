import Mathlib
import PEqualNP.Defs

-- Reduction of L-meta-2946. If the circuit never reads the wire AND(x_0, x_2), its wires from
-- the NOT wire on are a trace of at most 14 steps from the nine inputs, which the first
-- hypothesis (the statement of L-meta-2183) forbids. Otherwise the second hypothesis applies.
theorem PEqualNP.Outside.R_meta_2946_1
    (trace : have x1 : List ((Fin (9 : ℕ) → Bool) → Bool) := (List.ofFn fun (x1 : Fin (9 : ℕ)) (x2 : Fin (9 : ℕ) → Bool) => x2 x1) ++ [fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ))]; ∀ (x2 : List ((Fin (9 : ℕ) → Bool) → Bool)),   (∀ (x3 : Fin x2.length),       have x4 : List ((Fin (9 : ℕ) → Bool) → Bool) := (fun (x4 : Fin (9 : ℕ) → Bool) => Bool.false) :: (fun (x4 : Fin (9 : ℕ) → Bool) => Bool.true) :: (x1 ++ List.take (↑x3) x2);       ∃ x5 ∈ x4, ∃ x6 ∈ x4, (x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => x5 x7 && x6 x7) ∨ (x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => x5 x7 || x6 x7) ∨ x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => !x5 x7) →     (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) ∈ (fun (x4 : Fin (9 : ℕ) → Bool) => Bool.false) :: (x1 ++ x2) → (15 : ℕ) ≤ x2.length)
    (reads : ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (0 : ℕ) < x2.size → x2.size ≤ (13 : ℕ) → (∃ x3 ∈ x2.gates, (9 : ℕ) ∈ x3.inputs) → ∃ (x6 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)), !x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (0 : ℕ) < x2.size → x2.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)), !x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro k C fan pos size
  by_cases hr : ∃ g ∈ C.gates, (9 : ℕ) ∈ g.inputs
  · exact reads k C fan pos size hr
  push_neg at hr
  by_contra hall
  push_neg at hall
  obtain ⟨gs, o⟩ := C
  change 0 < gs.length at pos
  change gs.length ≤ 13 at size
  -- facts about appending one wire per gate
  have L1 : ∀ (F : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool)
      (hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (hs.foldl (fun w g => w ++ [F w g]) w).length = w.length + hs.length := by
    intro F hs
    induction hs with
    | nil => intro w; simp
    | cons g hs ih => intro w; rw [List.foldl_cons, ih]; simp; omega
  have L2 : ∀ (F : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool)
      (hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ), i < w.length →
      (hs.foldl (fun w g => w ++ [F w g]) w).getD i false = w.getD i false := by
    intro F hs
    induction hs with
    | nil => intro w i _; simp
    | cons g hs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hi
  have L3 : ∀ (F : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool)
      (hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j : ℕ) (hj : j < hs.length),
      (hs.foldl (fun w g => w ++ [F w g]) w).getD (w.length + j) false =
        F ((hs.take j).foldl (fun w g => w ++ [F w g]) w) hs[j] := by
    intro F hs w j hj
    have split : hs = hs.take j ++ (hs[j] :: hs.drop (j + 1)) := by
      rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
    have hP : ((hs.take j).foldl (fun w g => w ++ [F w g]) w).length = w.length + j := by
      rw [L1]; simp; omega
    conv_lhs => rw [split]
    rw [List.foldl_append, List.foldl_cons, L2 _ _ _ _ (by simp; omega), ← hP]
    simp
  have L4 : ∀ (F : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool)
      (hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j i : ℕ),
      i < w.length + j → j ≤ hs.length →
      ((hs.take j).foldl (fun w g => w ++ [F w g]) w).getD i false =
        (hs.foldl (fun w g => w ++ [F w g]) w).getD i false := by
    intro F hs w j i hi hj
    have split : hs = hs.take j ++ hs.drop j := by simp
    conv_rhs => rw [split]
    rw [List.foldl_append, L2 F (hs.drop j) ((hs.take j).foldl (fun w g => w ++ [F w g]) w) i
      (by rw [L1]; simp; omega)]
  have L5 : ∀ (F : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool)
      (hs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (j i : ℕ),
      w.length + j ≤ i → j ≤ hs.length →
      ((hs.take j).foldl (fun w g => w ++ [F w g]) w).getD i false = false := by
    intro F hs w j i hi hj
    apply List.getD_eq_default
    rw [L1]
    simp
    omega
  -- one gate of fan-in at most two over members of a list is one step
  have gate_step : ∀ (pool : List ((Fin 9 → Bool) → Bool)) (g : PEqualNP.CircuitLowerBounds.Gate)
      (P : ℕ → (Fin 9 → Bool) → Bool) (h : (Fin 9 → Bool) → Bool),
      (fun _ => false) ∈ pool → (fun _ => true) ∈ pool →
      g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) →
      g.inputs.length ≤ 2 → (∀ i ∈ g.inputs, P i ∈ pool) →
      (∀ x, h x = g.op.eval (g.inputs.map fun i => P i x)) →
      ∃ a ∈ pool, ∃ b ∈ pool,
        (h = fun x => a x && b x) ∨ (h = fun x => a x || b x) ∨ h = fun x => !a x := by
    intro pool g P h fm tm hop hlen hP hh
    have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by simpa using hop
    rcases hin : g.inputs with _ | ⟨i, _ | ⟨i', _ | ⟨i'', rest⟩⟩⟩
    · rcases hop with hop | hop | hop
      · refine ⟨_, tm, _, tm, Or.inl ?_⟩
        funext x; rw [hh, hin, hop]; rfl
      · refine ⟨_, fm, _, fm, Or.inr (Or.inl ?_)⟩
        funext x; rw [hh, hin, hop]; rfl
      · refine ⟨_, fm, _, fm, Or.inr (Or.inr ?_)⟩
        funext x; rw [hh, hin, hop]; rfl
    · have mi := hP i (by rw [hin]; simp)
      rcases hop with hop | hop | hop
      · refine ⟨_, mi, _, mi, Or.inl ?_⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]; cases P i x <;> rfl
      · refine ⟨_, mi, _, mi, Or.inr (Or.inl ?_)⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]; cases P i x <;> rfl
      · refine ⟨_, mi, _, mi, Or.inr (Or.inr ?_)⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]; cases P i x <;> rfl
    · have mi := hP i (by rw [hin]; simp)
      have mi' := hP i' (by rw [hin]; simp)
      rcases hop with hop | hop | hop
      · refine ⟨_, mi, _, mi', Or.inl ?_⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]; cases P i x <;> cases P i' x <;> rfl
      · refine ⟨_, mi, _, mi', Or.inr (Or.inl ?_)⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]; cases P i x <;> cases P i' x <;> rfl
      · refine ⟨_, mi, _, mi', Or.inr (Or.inr ?_)⟩
        funext x; rw [hh, hin, hop]; simp only [List.map_cons, List.map_nil]; cases P i x <;> cases P i' x <;> rfl
    · rw [hin] at hlen; simp at hlen
  -- the wires of the circuit on the extended input
  obtain ⟨E, hE⟩ : ∃ E : (Fin 9 → Bool) → List Bool,
      E = fun x => List.ofFn x ++ [x 0 && x 2, !x k] := ⟨_, rfl⟩
  have Elen (x : Fin 9 → Bool) : (E x).length = 11 := by rw [hE]; simp
  have Ein (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) : (E x).getD i false = x ⟨i, hi⟩ := by
    rw [hE]
    simp only []
    rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_ofFn]
  have E10 (x : Fin 9 → Bool) : (E x).getD 10 false = !x k := by rw [hE]; simp
  obtain ⟨W, hW⟩ : ∃ W : (Fin 9 → Bool) → List Bool,
      W = fun x => gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (E x) := ⟨_, rfl⟩
  have evW (x : Fin 9 → Bool) : (W x).getD o false =
      ({ gates := gs, output := o } : PEqualNP.CircuitLowerBounds.Circuit).eval
        (List.ofFn x ++ [x 0 && x 2, !x k]) := by
    rw [hW, hE]; rfl
  have Wlen (x : Fin 9 → Bool) : (W x).length = 11 + gs.length := by
    rw [hW]; simp only []; rw [L1, Elen]
  have WE (x : Fin 9 → Bool) (i : ℕ) (hi : i < 11) : (W x).getD i false = (E x).getD i false := by
    rw [hW]; simp only []; rw [L2 _ _ _ _ (by rw [Elen]; exact hi)]
  have ev (x : Fin 9 → Bool) := (evW x).trans (hall x)
  have olt : o < 11 + gs.length := by
    by_contra hge
    have e := ev (fun i => decide (i.val < 2))
    rw [List.getD_eq_default _ _ (by rw [Wlen]; omega)] at e
    revert e
    decide
  -- the trace: the NOT wire, then one function per gate
  obtain ⟨tr, htr⟩ : ∃ tr : List ((Fin 9 → Bool) → Bool),
      tr = List.ofFn (fun j : Fin (gs.length + 1) => fun x => (W x).getD (10 + j.val) false) :=
    ⟨_, rfl⟩
  have trlen : tr.length = gs.length + 1 := by rw [htr]; simp
  have trget (m : ℕ) (hm : m < tr.length) : tr[m] = fun x => (W x).getD (10 + m) false := by
    subst htr
    simp only [List.getElem_ofFn]
  have mem_take (n m : ℕ) (hm : m < n) (hl : m < tr.length) : tr[m] ∈ tr.take n := by
    have h1 : m < (tr.take n).length := by simp; omega
    have h2 : (tr.take n)[m] = tr[m] := by simp
    rw [← h2]
    exact List.getElem_mem h1
  have bound := trace tr ?_ ?_
  · omega
  · intro x3
    obtain ⟨n, hn⟩ := x3
    simp only [List.get_eq_getElem]
    rw [trget n hn]
    cases n with
    | zero =>
      refine ⟨fun x => x k, ?_, fun x => x k, ?_, Or.inr (Or.inr ?_)⟩
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_ofFn.mpr ⟨k, rfl⟩))))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_ofFn.mpr ⟨k, rfl⟩))))
      · funext x
        rw [WE x _ (by omega)]
        exact E10 x
    | succ m =>
      have hm : m < gs.length := by omega
      have okg := fan gs[m] (List.getElem_mem hm)
      apply gate_step _ gs[m] (fun i x =>
        ((gs.take m).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (E x)).getD i false)
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact okg.1
      · exact okg.2
      · intro i hi
        by_cases i9 : i < 9
        · have e : (fun x => ((gs.take m).foldl
              (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
              (E x)).getD i false) = fun x => x ⟨i, i9⟩ := by
            funext x
            rw [L2 _ _ _ _ (by rw [Elen]; omega), Ein x i i9]
          rw [e]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_ofFn.mpr ⟨⟨i, i9⟩, rfl⟩))))
        · have n9 : i ≠ 9 := fun h => hr _ (List.getElem_mem hm) (h ▸ hi)
          by_cases ilo : i < 11 + m
          · have e : (fun x => ((gs.take m).foldl
                (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                (E x)).getD i false) = tr[i - 10]'(by omega) := by
              rw [trget (i - 10) (by omega)]
              funext x
              rw [L4 _ _ _ m i (by rw [Elen]; omega) (by omega)]
              rw [hW]
              simp only []
              congr 1
              omega
            rw [e]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
              (mem_take _ _ (by omega) (by omega))))
          · have e : (fun x => ((gs.take m).foldl
                (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
                (E x)).getD i false) = fun _ => false := by
              funext x
              exact L5 _ _ _ m i (by rw [Elen]; omega) (by omega)
            rw [e]
            exact List.mem_cons_self
      · intro x
        have h3 := L3 (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) gs (E x) m hm
        rw [Elen] at h3
        rw [hW]
        simp only []
        rw [show 10 + (m + 1) = 11 + m by omega, h3]
  · by_cases o9 : o < 9
    · exfalso
      have e := ev (fun i => decide (i = ⟨o, o9⟩))
      rw [WE _ o (by omega), Ein _ o o9] at e
      revert e
      generalize (⟨o, o9⟩ : Fin 9) = v
      revert v
      decide
    · by_cases o9' : o = 9
      · exfalso
        subst o9'
        have e := ev (fun i => decide (i.val < 2))
        rw [WE _ 9 (by omega), hE] at e
        revert e
        generalize k = k'
        revert k'
        decide
      · apply List.mem_cons_of_mem
        apply List.mem_append_right
        have e : tr[o - 10]'(by omega) = _ := trget (o - 10) (by omega)
        have e2 : (fun x : Fin 9 → Bool => (W x).getD (10 + (o - 10)) false) =
            fun x => (W x).getD o false := by
          funext x
          congr 1
          omega
        rw [e2] at e
        have e3 := List.getElem_mem (l := tr) (n := o - 10) (by omega)
        rw [e] at e3
        convert e3 using 1
        funext x
        exact (ev x).symm
