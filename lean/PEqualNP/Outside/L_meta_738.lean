import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_738

open PEqualNP.CircuitLowerBounds

-- A list of wire values grown one gate at a time, each new value computed from the list so far.
def run {α : Type} (F : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem run_nil {α : Type} (F : List α → Gate → α) (w : List α) : run F [] w = w := rfl

theorem run_cons {α : Type} (F : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    run F (g :: gs) w = run F gs (w ++ [F w g]) := rfl

theorem run_append {α : Type} (F : List α → Gate → α) (gs1 gs2 : List Gate) (w : List α) :
    run F (gs1 ++ gs2) w = run F gs2 (run F gs1 w) := by
  simp [run, List.foldl_append]

theorem run_length {α : Type} (F : List α → Gate → α) (gs : List Gate) (w : List α) :
    (run F gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

theorem getD_append_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem getD_append_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem run_getD_lt {α : Type} (F : List α → Gate → α) (gs : List Gate) (w : List α) (d : α)
    (i : ℕ) (hi : i < w.length) : (run F gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact getD_append_lt _ _ _ _ hi

theorem run_gate {α : Type} (F : List α → Gate → α) (gs : List Gate) (w : List α) (d : α)
    (j : ℕ) (hlt : j < gs.length) :
    ∃ pre : List α, pre.length = w.length + j ∧
      (∀ i, i < w.length + j → pre.getD i d = (run F gs w).getD i d) ∧
      (run F gs w).getD (w.length + j) d = F pre gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  have hlen : (run F (gs.take j) w).length = w.length + j := by
    rw [run_length, List.length_take, Nat.min_eq_left hlt.le]
  have hrun : run F gs w =
      run F (gs.drop (j + 1)) (run F (gs.take j) w ++ [F (run F (gs.take j) w) gs[j]]) := by
    conv_lhs => rw [hsplit]
    rw [run_append, run_cons]
  refine ⟨run F (gs.take j) w, hlen, ?_, ?_⟩
  · intro i hi
    rw [hrun, run_getD_lt F (gs.drop (j + 1)) _ d i
          (by rw [List.length_append, hlen, List.length_singleton]; omega),
        getD_append_lt _ _ _ _ (by omega)]
  · rw [hrun, run_getD_lt F (gs.drop (j + 1)) _ d (w.length + j)
        (by rw [List.length_append, hlen, List.length_singleton]; omega), ← hlen]
    exact getD_append_len _ _ _

def Fw (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def Fd (d : List ℕ) (g : Gate) : ℕ := g.lineDegree d

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run Fw C.gates x := rfl

theorem degs_eq (C : Circuit) (n : ℕ) (M : Finset ℕ) :
    C.lineDegrees n M = run Fd C.gates ((List.range n).map fun i => if i ∈ M then 1 else 0) :=
  rfl

abbrev mono (D : List Gate) : Prop :=
  ∀ h ∈ D, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2

-- A coefficient: nothing, the constant true, or a wire of the new circuit.
def cv (W : List Bool) : Option (Option ℕ) → Bool
  | none => false
  | some none => true
  | some (some k) => W.getD k false

abbrev Valid (len : ℕ) (c : Option (Option ℕ)) : Prop := ∀ k, c = some (some k) → k < len

theorem cv_ext (W W₂ : List Bool) (len : ℕ) (c : Option (Option ℕ))
    (h : ∀ k, k < len → W₂.getD k false = W.getD k false) (hc : Valid len c) :
    cv W₂ c = cv W c := by
  rcases c with _ | _ | k
  · rfl
  · rfl
  · exact h k (hc k rfl)

theorem Fw_or (W : List Bool) (l : List ℕ) :
    Fw W ⟨GateOp.or, l⟩ = l.any (fun i => W.getD i false) := by
  simp [Fw, GateOp.eval, List.any_map]

theorem Fw_and (W : List Bool) (l : List ℕ) :
    Fw W ⟨GateOp.and, l⟩ = l.all (fun i => W.getD i false) := by
  simp [Fw, GateOp.eval, List.all_map]

-- Change one coefficient without a new gate.
theorem join_free (p : ℕ) (D : List Gate) (σ : ℕ → Option (Option ℕ)) (s : ℕ)
    (c c' : Option (Option ℕ)) (M : Finset ℕ)
    (hc' : Valid (p + D.length) c') (hσ : ∀ u, Valid (p + D.length) (σ u))
    (h1 : c ≠ none → c' ≠ none) (h2 : σ s ≠ none → c' ≠ none)
    (hv : ∀ W : List Bool, cv W c' = (cv W (σ s) || cv W c)) :
    ∃ σ₂ : ℕ → Option (Option ℕ), (∀ u, Valid (p + D.length) (σ₂ u)) ∧
      (M.filter (fun u => σ₂ u ≠ none)).card ≤ (M.filter (fun u => σ u ≠ none)).card + 1 ∧
      (∀ u, σ u ≠ none → σ₂ u ≠ none) ∧ (c ≠ none → σ₂ s ≠ none) ∧
      ∀ (W : List Bool) (u : ℕ),
        cv W (σ₂ u) = (cv W (σ u) || (decide (u = s) && cv W c)) := by
  refine ⟨Function.update σ s c', ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    by_cases hu : u = s
    · rw [hu, Function.update_self]; exact hc'
    · rw [Function.update_of_ne hu]; exact hσ u
  · have hsub : M.filter (fun u => Function.update σ s c' u ≠ none) ⊆
        insert s (M.filter (fun u => σ u ≠ none)) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      by_cases hus : u = s
      · rw [hus]; exact Finset.mem_insert_self _ _
      · rw [Function.update_of_ne hus] at hu
        exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr hu)
    exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
  · intro u hu
    by_cases hus : u = s
    · rw [hus, Function.update_self]; exact h2 (hus ▸ hu)
    · rw [Function.update_of_ne hus]; exact hu
  · intro hc
    rw [Function.update_self]; exact h1 hc
  · intro W u
    by_cases hus : u = s
    · rw [hus, Function.update_self, hv W]; simp
    · rw [Function.update_of_ne hus]; simp [hus]

theorem join_nogate (p : ℕ) (D : List Gate) (σ : ℕ → Option (Option ℕ)) (s : ℕ)
    (c c' : Option (Option ℕ)) (M : Finset ℕ) (hD : mono D)
    (hc' : Valid (p + D.length) c') (hσ : ∀ u, Valid (p + D.length) (σ u))
    (h1 : c ≠ none → c' ≠ none) (h2 : σ s ≠ none → c' ≠ none)
    (hv : ∀ W : List Bool, cv W c' = (cv W (σ s) || cv W c)) :
    ∃ (D₂ : List Gate) (σ₂ : ℕ → Option (Option ℕ)), mono D₂ ∧
      (∀ u, Valid (p + D₂.length) (σ₂ u)) ∧ D.length ≤ D₂.length ∧
      D₂.length + (M.filter (fun u => σ₂ u ≠ none)).card ≤
        D.length + (M.filter (fun u => σ u ≠ none)).card + 1 ∧
      (∀ u, σ u ≠ none → σ₂ u ≠ none) ∧ (c ≠ none → σ₂ s ≠ none) ∧
      ∀ X : List Bool, X.length = p →
        (∀ k, k < p + D.length → (run Fw D₂ X).getD k false = (run Fw D X).getD k false) ∧
        ∀ u, cv (run Fw D₂ X) (σ₂ u) =
          (cv (run Fw D X) (σ u) || (decide (u = s) && cv (run Fw D X) c)) := by
  obtain ⟨σ₂, a1, a2, a3, a4, a5⟩ := join_free p D σ s c c' M hc' hσ h1 h2 hv
  exact ⟨D, σ₂, hD, a1, le_rfl, by omega, a3, a4, fun X _ => ⟨fun k _ => rfl, fun u => a5 _ u⟩⟩

-- Join the coefficient c into the coefficient of s, with at most one new gate.
theorem join (p : ℕ) (D : List Gate) (σ : ℕ → Option (Option ℕ)) (s : ℕ)
    (c : Option (Option ℕ)) (M : Finset ℕ) (hD : mono D)
    (hσ : ∀ u, Valid (p + D.length) (σ u)) (hc : Valid (p + D.length) c) :
    ∃ (D₂ : List Gate) (σ₂ : ℕ → Option (Option ℕ)), mono D₂ ∧
      (∀ u, Valid (p + D₂.length) (σ₂ u)) ∧ D.length ≤ D₂.length ∧
      D₂.length + (M.filter (fun u => σ₂ u ≠ none)).card ≤
        D.length + (M.filter (fun u => σ u ≠ none)).card + 1 ∧
      (∀ u, σ u ≠ none → σ₂ u ≠ none) ∧ (c ≠ none → σ₂ s ≠ none) ∧
      ∀ X : List Bool, X.length = p →
        (∀ k, k < p + D.length → (run Fw D₂ X).getD k false = (run Fw D X).getD k false) ∧
        ∀ u, cv (run Fw D₂ X) (σ₂ u) =
          (cv (run Fw D X) (σ u) || (decide (u = s) && cv (run Fw D X) c)) := by
  rcases c with _ | _ | k
  · exact join_nogate p D σ s none (σ s) M hD (hσ s) hσ (fun h => absurd rfl h) (fun h => h)
      (fun W => by simp [cv])
  · exact join_nogate p D σ s (some none) (some none) M hD (fun k hk => by simp at hk) hσ
      (fun _ => by simp) (fun _ => by simp) (fun W => by simp [cv])
  · rcases hss : σ s with _ | _ | j
    · exact join_nogate p D σ s (some (some k)) (some (some k)) M hD hc hσ
        (fun _ => by simp) (fun _ => by simp) (fun W => by simp [cv, hss])
    · exact join_nogate p D σ s (some (some k)) (some none) M hD (fun k hk => by simp at hk) hσ
        (fun _ => by simp) (fun _ => by simp) (fun W => by simp [cv, hss])
    · have hj : j < p + D.length := hσ s j hss
      have hk : k < p + D.length := hc k rfl
      refine ⟨D ++ [⟨GateOp.or, [j, k]⟩],
        Function.update σ s (some (some (p + D.length))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h hh
        rcases List.mem_append.mp hh with hh | hh
        · exact hD h hh
        · rw [List.mem_singleton] at hh
          rw [hh]
          exact ⟨Or.inr rfl, by simp⟩
      · intro u
        by_cases hus : u = s
        · rw [hus, Function.update_self]
          intro k' hk'
          simp only [Option.some.injEq] at hk'
          rw [← hk', List.length_append, List.length_singleton]
          omega
        · rw [Function.update_of_ne hus]
          intro k' hk'
          have := hσ u k' hk'
          rw [List.length_append, List.length_singleton]
          omega
      · rw [List.length_append, List.length_singleton]; omega
      · have hsub : M.filter (fun u => Function.update σ s (some (some (p + D.length))) u ≠ none) ⊆
            M.filter (fun u => σ u ≠ none) := by
          intro u hu
          rw [Finset.mem_filter] at hu ⊢
          refine ⟨hu.1, ?_⟩
          by_cases hus : u = s
          · rw [hus, hss]; simp
          · have := hu.2
            rw [Function.update_of_ne hus] at this
            exact this
        have := Finset.card_le_card hsub
        rw [List.length_append, List.length_singleton]
        omega
      · intro u hu
        by_cases hus : u = s
        · rw [hus, Function.update_self]; simp
        · rw [Function.update_of_ne hus]; exact hu
      · intro _
        rw [Function.update_self]; simp
      · intro X hX
        have hlen : (run Fw D X).length = p + D.length := by rw [run_length, hX]
        have hpre : ∀ k', k' < p + D.length →
            (run Fw (D ++ [⟨GateOp.or, [j, k]⟩]) X).getD k' false = (run Fw D X).getD k' false := by
          intro k' hk'
          rw [run_append, run_cons, run_nil]
          exact getD_append_lt _ _ _ _ (by omega)
        refine ⟨hpre, ?_⟩
        intro u
        by_cases hus : u = s
        · rw [hus, Function.update_self, hss]
          simp only [cv, decide_true, Bool.true_and]
          rw [run_append, run_cons, run_nil, ← hlen, getD_append_len, Fw_or]
          simp
        · rw [Function.update_of_ne hus]
          rw [cv_ext _ _ (p + D.length) (σ u) hpre (hσ u)]
          simp [hus]

theorem joinList (p : ℕ) (M : Finset ℕ) (c : Option (Option ℕ)) :
    ∀ (T : List ℕ) (D : List Gate) (σ : ℕ → Option (Option ℕ)), mono D →
      (∀ u, Valid (p + D.length) (σ u)) → Valid (p + D.length) c →
      ∃ (D₂ : List Gate) (σ₂ : ℕ → Option (Option ℕ)), mono D₂ ∧
        (∀ u, Valid (p + D₂.length) (σ₂ u)) ∧ D.length ≤ D₂.length ∧
        D₂.length + (M.filter (fun u => σ₂ u ≠ none)).card ≤
          D.length + (M.filter (fun u => σ u ≠ none)).card + T.length ∧
        (∀ u, σ u ≠ none → σ₂ u ≠ none) ∧ (c ≠ none → ∀ s ∈ T, σ₂ s ≠ none) ∧
        ∀ X : List Bool, X.length = p →
          (∀ k, k < p + D.length → (run Fw D₂ X).getD k false = (run Fw D X).getD k false) ∧
          ∀ u, cv (run Fw D₂ X) (σ₂ u) =
            (cv (run Fw D X) (σ u) || (decide (u ∈ T) && cv (run Fw D X) c)) := by
  intro T
  induction T with
  | nil =>
    intro D σ hD hσ hc
    exact ⟨D, σ, hD, hσ, le_rfl, by simp, fun u h => h, fun _ s hs => absurd hs (by simp),
      fun X _ => ⟨fun k _ => rfl, fun u => by simp⟩⟩
  | cons s T ih =>
    intro D σ hD hσ hc
    obtain ⟨D₁, σ₁, b1, b2, b3, b4, b5, b6, b7⟩ := join p D σ s c M hD hσ hc
    have hc1 : Valid (p + D₁.length) c := fun k hk => by have := hc k hk; omega
    obtain ⟨D₂, σ₂, e1, e2, e3, e4, e5, e6, e7⟩ := ih D₁ σ₁ b1 b2 hc1
    refine ⟨D₂, σ₂, e1, e2, by omega, ?_, fun u h => e5 u (b5 u h), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro hcn t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact e5 _ (b6 hcn)
      · exact e6 hcn t ht
    · intro X hX
      obtain ⟨f1, f2⟩ := b7 X hX
      obtain ⟨g1, g2⟩ := e7 X hX
      refine ⟨fun k hk => by rw [g1 k (by omega), f1 k hk], ?_⟩
      intro u
      rw [g2 u, f2 u, cv_ext (run Fw D X) (run Fw D₁ X) (p + D.length) c f1 hc]
      generalize cv (run Fw D X) (σ u) = a
      generalize cv (run Fw D X) c = x
      by_cases h1 : u = s
      · subst h1; cases a <;> cases x <;> simp
      · by_cases h2 : u ∈ T <;> cases a <;> cases x <;> simp [h1, h2]

def cvins : Option (Option ℕ) → List ℕ
  | some (some j) => [j]
  | _ => []

-- AND a coefficient with at most one more wire, with one new gate.
theorem meet (p : ℕ) (D : List Gate) (c : Option (Option ℕ)) (ops : List ℕ) (hD : mono D)
    (hcn : c ≠ none) (hops : ops.length ≤ 1) :
    ∃ (D₁ : List Gate) (c₁ : Option (Option ℕ)), mono D₁ ∧ D₁.length = D.length + 1 ∧
      c₁ ≠ none ∧ Valid (p + D₁.length) c₁ ∧
      ∀ X : List Bool, X.length = p →
        (∀ k, k < p + D.length → (run Fw D₁ X).getD k false = (run Fw D X).getD k false) ∧
        cv (run Fw D₁ X) c₁ =
          (cv (run Fw D X) c && ops.all (fun q => (run Fw D X).getD q false)) := by
  refine ⟨D ++ [⟨GateOp.and, cvins c ++ ops⟩], some (some (p + D.length)), ?_, by simp, by simp,
    ?_, ?_⟩
  · intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hD h hh
    · rw [List.mem_singleton] at hh
      rw [hh]
      refine ⟨Or.inl rfl, ?_⟩
      rcases c with _ | _ | j <;> simp [cvins] <;> omega
  · intro k hk
    simp only [Option.some.injEq] at hk
    rw [← hk, List.length_append, List.length_singleton]
    omega
  · intro X hX
    have hlen : (run Fw D X).length = p + D.length := by rw [run_length, hX]
    refine ⟨?_, ?_⟩
    · intro k hk
      rw [run_append, run_cons, run_nil]
      exact getD_append_lt _ _ _ _ (by omega)
    · rw [run_append, run_cons, run_nil]
      show (run Fw D X ++ [_]).getD (p + D.length) false = _
      rw [← hlen, getD_append_len, Fw_and, List.all_append]
      rcases c with _ | _ | j
      · exact absurd rfl hcn
      · simp [cvins, cv]
      · simp [cvins, cv]

-- The values of the unmarked inputs, in order, and the place of an unmarked input among them.
def U (n : ℕ) (M : Finset ℕ) (z : ℕ → Bool) : List Bool :=
  ((List.range n).filter (fun i => decide (i ∉ M))).map z

def pos (M : Finset ℕ) (a : ℕ) : ℕ := ((List.range a).filter (fun i => decide (i ∉ M))).length

theorem U_length (n : ℕ) (M : Finset ℕ) (z : ℕ → Bool) : (U n M z).length = pos M n := by
  simp [U, pos]

theorem U_succ_not (n : ℕ) (M : Finset ℕ) (z : ℕ → Bool) (hn : n ∉ M) :
    U (n + 1) M z = U n M z ++ [z n] := by
  simp [U, List.range_succ, List.filter_append, hn]

theorem U_succ_mem (n : ℕ) (M : Finset ℕ) (z : ℕ → Bool) (hn : n ∈ M) :
    U (n + 1) M z = U n M z := by
  simp [U, List.range_succ, List.filter_append, hn]

theorem pos_succ_not (n : ℕ) (M : Finset ℕ) (hn : n ∉ M) : pos M (n + 1) = pos M n + 1 := by
  simp [pos, List.range_succ, List.filter_append, hn]

theorem pos_succ_mem (n : ℕ) (M : Finset ℕ) (hn : n ∈ M) : pos M (n + 1) = pos M n := by
  simp [pos, List.range_succ, List.filter_append, hn]

theorem U_congr (n : ℕ) (M : Finset ℕ) (z z' : ℕ → Bool) (h : ∀ i, i < n → i ∉ M → z i = z' i) :
    U n M z = U n M z' := by
  unfold U
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
  exact h i hi.1 hi.2

theorem U_congrM (n : ℕ) (M M' : Finset ℕ) (z : ℕ → Bool) (h : ∀ i, i < n → (i ∈ M' ↔ i ∈ M)) :
    U n M' z = U n M z := by
  unfold U
  congr 1
  apply List.filter_congr
  intro i hi
  rw [List.mem_range] at hi
  simp [h i hi]

theorem pos_congrM (n : ℕ) (M M' : Finset ℕ) (h : ∀ i, i < n → (i ∈ M' ↔ i ∈ M)) :
    pos M' n = pos M n := by
  unfold pos
  congr 1
  apply List.filter_congr
  intro i hi
  rw [List.mem_range] at hi
  simp [h i hi]

theorem U_get (M : Finset ℕ) (z : ℕ → Bool) (a : ℕ) (haM : a ∉ M) :
    ∀ n, a < n → (U n M z)[pos M a]? = some (z a) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro han
    by_cases hn : n ∈ M
    · rw [U_succ_mem n M z hn]
      have : a ≠ n := fun e => haM (e ▸ hn)
      exact ih (by omega)
    · rw [U_succ_not n M z hn]
      by_cases hane : a = n
      · subst hane
        rw [← U_length a M z]
        simp
      · have h := ih (by omega)
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
        exact h

theorem U_getD (M : Finset ℕ) (z : ℕ → Bool) (a n : ℕ) (haM : a ∉ M) (han : a < n) :
    (U n M z).getD (pos M a) false = z a := by
  rw [List.getD_eq_getElem?_getD, U_get M z a haM n han]
  rfl

theorem pos_lt (M : Finset ℕ) (a n : ℕ) (haM : a ∉ M) (han : a < n) : pos M a < pos M n := by
  have h := (List.getElem?_eq_some_iff.mp (U_get M (fun _ => false) a haM n han)).1
  rwa [U_length] at h

theorem Lget (n : ℕ) (z : ℕ → Bool) (a : ℕ) :
    ((List.range n).map z).getD a false = if a < n then z a else false := by
  by_cases h : a < n
  · simp [List.getD_eq_getElem?_getD, h]
  · rw [getD_ge _ _ _ (by simp; omega)]
    simp [h]

def d0 (n : ℕ) (M : Finset ℕ) : List ℕ := (List.range n).map fun i => if i ∈ M then 1 else 0

theorem d0_getD (n : ℕ) (M : Finset ℕ) (hM : ∀ u ∈ M, u < n) (a : ℕ) :
    (d0 n M).getD a 0 = if a ∈ M then 1 else 0 := by
  by_cases h : a < n
  · simp [d0, List.getD_eq_getElem?_getD, h]
  · rw [getD_ge _ _ _ (by simp [d0]; omega)]
    have : a ∉ M := fun ha => h (hM a ha)
    simp [this]

theorem d0_succ (n : ℕ) (M M' : Finset ℕ) (h : ∀ i, i < n → (i ∈ M' ↔ i ∈ M)) :
    d0 (n + 1) M' = d0 n M ++ [if n ∈ M' then 1 else 0] := by
  simp only [d0, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp [h i hi]

theorem deg_and (n : ℕ) (M : Finset ℕ) (hM : ∀ u ∈ M, u < n) (l : List ℕ) :
    (l.map fun i => (d0 n M).getD i 0).sum = (l.filter (fun a => decide (a ∈ M))).length := by
  rw [show (fun i => (d0 n M).getD i 0) = fun i => if i ∈ M then 1 else 0 from
    funext (d0_getD n M hM)]
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    by_cases h : a ∈ M
    · simp [h]; omega
    · simp [h]

theorem deg_or (n : ℕ) (M : Finset ℕ) (hM : ∀ u ∈ M, u < n) (l : List ℕ) :
    (l.map fun i => (d0 n M).getD i 0).foldr max 0 =
      if l.filter (fun a => decide (a ∈ M)) = [] then 0 else 1 := by
  rw [show (fun i => (d0 n M).getD i 0) = fun i => if i ∈ M then 1 else 0 from
    funext (d0_getD n M hM)]
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.foldr_cons, ih, List.filter_cons]
    by_cases h : a ∈ M
    · simp only [h, if_true, decide_true]
      split_ifs <;> simp_all
    · simp [h]

theorem Fd_and (g : Gate) (hop : g.op = GateOp.and) (d : List ℕ) :
    Fd d g = (g.inputs.map fun i => d.getD i 0).sum := by
  simp [Fd, Gate.lineDegree, hop]

theorem Fd_or (g : Gate) (hop : g.op = GateOp.or) (d : List ℕ) :
    Fd d g = (g.inputs.map fun i => d.getD i 0).foldr max 0 := by
  simp [Fd, Gate.lineDegree, hop]

theorem any_split (l : List ℕ) (P f : ℕ → Bool) :
    l.any f = ((l.filter P).any f || (l.filter (fun a => !P a)).any f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : P a <;> simp [List.filter_cons, h, ih, Bool.or_assoc, Bool.or_left_comm]

theorem all_split (l : List ℕ) (P f : ℕ → Bool) :
    l.all f = ((l.filter P).all f && (l.filter (fun a => !P a)).all f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : P a <;> simp [List.filter_cons, h, ih, Bool.and_assoc, Bool.and_left_comm]

-- Wire a is read by the gate that makes wire b.
def rel (G : List Gate) (n : ℕ) (a b : ℕ) : Prop :=
  a < b ∧ ∃ i : Fin G.length, b = n + i.val ∧ a ∈ (G.get i).inputs

theorem rel_cons (g : Gate) (G : List Gate) (n a b : ℕ) (h : rel (g :: G) n a b) :
    (a < n ∧ b = n ∧ a ∈ g.inputs) ∨ rel G (n + 1) a b := by
  obtain ⟨hab, ⟨i, hi⟩, hb, hin⟩ := h
  cases i with
  | zero =>
    left
    simp only [Nat.add_zero] at hb
    exact ⟨by omega, hb, by simpa using hin⟩
  | succ i =>
    right
    exact ⟨hab, ⟨i, by simpa using hi⟩, by simp only at hb ⊢; omega, by simpa using hin⟩

theorem reach_cons (g : Gate) (G : List Gate) (n out : ℕ) :
    ∀ a, Relation.ReflTransGen (rel (g :: G) n) a out →
      (n ≤ a → Relation.ReflTransGen (rel G (n + 1)) a out) ∧
      (a < n → Relation.ReflTransGen (rel G (n + 1)) a out ∨
        (a ∈ g.inputs ∧ Relation.ReflTransGen (rel G (n + 1)) n out)) := by
  intro a h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨fun _ => Relation.ReflTransGen.refl, fun _ => Or.inl Relation.ReflTransGen.refl⟩
  | @head a' c h' h ih =>
    rcases rel_cons _ _ _ _ _ h' with ⟨h1, h2, h3⟩ | hr
    · subst h2
      exact ⟨fun hh => by omega, fun _ => Or.inr ⟨h3, ih.1 le_rfl⟩⟩
    · have hb : n ≤ c := by
        obtain ⟨_, i, hb, _⟩ := hr
        omega
      have := ih.1 hb
      exact ⟨fun _ => Relation.ReflTransGen.head hr this,
        fun _ => Or.inl (Relation.ReflTransGen.head hr this)⟩

theorem reach_nil (n a out : ℕ) (h : Relation.ReflTransGen (rel [] n) a out) : a = out := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head a' c h' h ih =>
    obtain ⟨_, i, _, _⟩ := h'
    exact i.elim0

def zero (M : Finset ℕ) (z : ℕ → Bool) : ℕ → Bool := fun i => if i ∈ M then false else z i

theorem any_congr' (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ a ∈ l, f a = f' a) :
    l.any f = l.any f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem all_congr' (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ a ∈ l, f a = f' a) :
    l.all f = l.all f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem filter_len_split (l : List ℕ) (P : ℕ → Bool) :
    (l.filter P).length + (l.filter (fun a => !P a)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : P a <;> simp [List.filter_cons, h] <;> omega

theorem Fw_or' (W : List Bool) (g : Gate) (hop : g.op = GateOp.or) :
    Fw W g = g.inputs.any (fun i => W.getD i false) := by
  simp [Fw, hop, GateOp.eval, List.any_map]

theorem Fw_and' (W : List Bool) (g : Gate) (hop : g.op = GateOp.and) :
    Fw W g = g.inputs.all (fun i => W.getD i false) := by
  simp [Fw, hop, GateOp.eval, List.all_map]

theorem gate_step (n : ℕ) (M : Finset ℕ) (hM : ∀ u ∈ M, u < n) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hT : g.inputs.filter (fun a => decide (a ∈ M)) ≠ [])
    (hdeg : Fd (d0 n M) g ≤ 1)
    (D' : List Gate) (cn : Option (Option ℕ)) (hD' : mono D') (hcn : cn ≠ none)
    (hcv : Valid (pos M n + D'.length) cn) :
    ∃ (D₁ : List Gate) (c : Option (Option ℕ)) (fv : (ℕ → Bool) → Bool), mono D₁ ∧
      D'.length ≤ D₁.length ∧
      D₁.length + (g.inputs.filter (fun a => decide (a ∈ M))).length ≤ D'.length + 2 ∧
      c ≠ none ∧ Valid (pos M n + D₁.length) c ∧
      (∀ X : List Bool, X.length = pos M n → ∀ k, k < pos M n + D'.length →
        (run Fw D₁ X).getD k false = (run Fw D' X).getD k false) ∧
      (∀ z : ℕ → Bool, cv (run Fw D₁ (U n M z)) c = (cv (run Fw D' (U n M z)) cn && fv z)) ∧
      (∀ z : ℕ → Bool, Fw ((List.range n).map z) g =
        (Fw ((List.range n).map (zero M z)) g ||
          decide (∃ u ∈ g.inputs.filter (fun a => decide (a ∈ M)), z u = true ∧ fv z = true))) := by
  have hTv : ∀ (z : ℕ → Bool), ∀ a ∈ g.inputs.filter (fun a => decide (a ∈ M)),
      ((List.range n).map z).getD a false = z a := by
    intro z a ha
    have haM : a ∈ M := by simpa using (List.mem_filter.mp ha).2
    rw [Lget, if_pos (hM a haM)]
  have hT0 : ∀ (z : ℕ → Bool), ∀ a ∈ g.inputs.filter (fun a => decide (a ∈ M)),
      ((List.range n).map (zero M z)).getD a false = false := by
    intro z a ha
    have haM : a ∈ M := by simpa using (List.mem_filter.mp ha).2
    rw [Lget, if_pos (hM a haM)]
    simp [zero, haM]
  have hR : ∀ (z : ℕ → Bool), ∀ a ∈ g.inputs.filter (fun a => !decide (a ∈ M)),
      ((List.range n).map (zero M z)).getD a false = ((List.range n).map z).getD a false := by
    intro z a ha
    have haM : a ∉ M := by simpa using (List.mem_filter.mp ha).2
    rw [Lget, Lget]
    simp [zero, haM]
  rcases hg.1 with hop | hop
  · have hlen : (g.inputs.filter (fun a => decide (a ∈ M))).length = 1 := by
      rw [Fd_and g hop, deg_and n M hM] at hdeg
      have : (g.inputs.filter (fun a => decide (a ∈ M))).length ≠ 0 := by
        rwa [Ne, List.length_eq_zero_iff]
      omega
    obtain ⟨s, hs⟩ := List.length_eq_one_iff.mp hlen
    have hRlen : (g.inputs.filter (fun a => !decide (a ∈ M))).length ≤ 1 := by
      have := filter_len_split g.inputs (fun a => decide (a ∈ M))
      have := hg.2
      omega
    obtain ⟨D₁, c, k1, k2, k3, k4, k5⟩ := meet (pos M n) D' cn
      ((g.inputs.filter (fun a => !decide (a ∈ M))).map
        (fun a => if a < n then pos M a else pos M n + D'.length)) hD' hcn (by simpa using hRlen)
    refine ⟨D₁, c, fun z => (g.inputs.filter (fun a => !decide (a ∈ M))).all
      (fun a => ((List.range n).map z).getD a false), k1, by omega, by omega, k3, k4,
      fun X hX => (k5 X hX).1, ?_, ?_⟩
    · intro z
      rw [(k5 (U n M z) (U_length n M z)).2, List.all_map]
      congr 1
      apply all_congr'
      intro a ha
      have haM : a ∉ M := by simpa using (List.mem_filter.mp ha).2
      simp only [Function.comp]
      by_cases han : a < n
      · rw [if_pos han, run_getD_lt _ _ _ _ _ (by rw [U_length]; exact pos_lt M a n haM han),
          U_getD M z a n haM han, Lget, if_pos han]
      · rw [if_neg han, getD_ge _ _ _ (by rw [run_length, U_length]), Lget, if_neg han]
    · intro z
      rw [Fw_and' _ g hop, Fw_and' _ g hop, all_split g.inputs (fun a => decide (a ∈ M)),
        all_split g.inputs (fun a => decide (a ∈ M)) (fun i =>
          ((List.range n).map (zero M z)).getD i false)]
      rw [all_congr' _ _ _ (hTv z), all_congr' _ _ (fun _ => false) (hT0 z)]
      rw [hs, Bool.eq_iff_iff]
      simp [List.all_eq_true]
  · refine ⟨D', cn, fun _ => true, hD', le_rfl, ?_, hcn, hcv, fun X _ k _ => rfl, ?_, ?_⟩
    · have := List.length_filter_le (fun a => decide (a ∈ M)) g.inputs
      have := hg.2
      omega
    · intro z; simp
    · intro z
      rw [Fw_or' _ g hop, Fw_or' _ g hop, any_split g.inputs (fun a => decide (a ∈ M)),
        any_split g.inputs (fun a => decide (a ∈ M)) (fun i =>
          ((List.range n).map (zero M z)).getD i false)]
      rw [any_congr' _ _ _ (hTv z), any_congr' _ _ (fun _ => false) (hT0 z),
        any_congr' _ _ _ (hR z)]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, List.mem_filter,
        and_true, Bool.false_eq_true, and_false, exists_false, false_or]
      constructor
      · rintro (⟨x, hx, h3⟩ | h)
        · exact Or.inr ⟨x, hx, h3⟩
        · exact Or.inl h
      · rintro (h | ⟨u, hu, h3⟩)
        · exact Or.inr h
        · exact Or.inl ⟨u, hu, h3⟩

theorem comb0 (M : Finset ℕ) (z z0 cvp : ℕ → Bool) (hz0 : ∀ u ∈ M, z0 u = false)
    (A b b0 cz : Bool) (hcz : cz = false) :
    (A || decide ((∃ u ∈ M, z u = true ∧ cvp u = true) ∨ (b = true ∧ cz = true))) =
      ((A || decide ((∃ u ∈ M, z0 u = true ∧ cvp u = true) ∨ (b0 = true ∧ cz = true))) ||
        decide (∃ u ∈ M, z u = true ∧ cvp u = true)) := by
  subst hcz
  have h0 : ¬ ∃ u ∈ M, z0 u = true ∧ cvp u = true := by
    rintro ⟨u, hu, h1, _⟩
    rw [hz0 u hu] at h1
    exact absurd h1 (by simp)
  simp [h0]

theorem comb (M : Finset ℕ) (T : List ℕ) (hT : ∀ u ∈ T, u ∈ M) (z z0 cvp : ℕ → Bool)
    (hz0 : ∀ u ∈ M, z0 u = false) (A v0 cn f : Bool) :
    (A || decide ((∃ u ∈ M, z u = true ∧ cvp u = true) ∨
        ((v0 || decide (∃ u ∈ T, z u = true ∧ f = true)) = true ∧ cn = true))) =
      ((A || decide ((∃ u ∈ M, z0 u = true ∧ cvp u = true) ∨ (v0 = true ∧ cn = true))) ||
        decide (∃ u ∈ M, z u = true ∧ (cvp u || (decide (u ∈ T) && (cn && f))) = true)) := by
  have h0 : ¬ ∃ u ∈ M, z0 u = true ∧ cvp u = true := by
    rintro ⟨u, hu, h1, _⟩
    rw [hz0 u hu] at h1
    exact absurd h1 (by simp)
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, h0, false_or]
  constructor
  · rintro (hA | ⟨u, hu, h1, h2⟩ | ⟨hv0 | ⟨u, huT, h1, h2⟩, h3⟩)
    · exact Or.inl (Or.inl hA)
    · exact Or.inr ⟨u, hu, h1, Or.inl h2⟩
    · exact Or.inl (Or.inr ⟨hv0, h3⟩)
    · exact Or.inr ⟨u, hT u huT, h1, Or.inr ⟨huT, h3, h2⟩⟩
  · rintro ((hA | ⟨hv0, h3⟩) | ⟨u, hu, h1, h2 | ⟨huT, h3, h4⟩⟩)
    · exact Or.inl hA
    · exact Or.inr (Or.inr ⟨Or.inl hv0, h3⟩)
    · exact Or.inr (Or.inl ⟨u, hu, h1, h2⟩)
    · exact Or.inr (Or.inr ⟨Or.inr ⟨u, huT, h1, h4⟩, h3⟩)

theorem range_map_snoc (n : ℕ) (w : ℕ → Bool) (b : Bool) :
    (List.range (n + 1)).map (fun i => if i = n then b else w i) = (List.range n).map w ++ [b] := by
  rw [List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp [Nat.ne_of_lt hi]
  · simp

-- The construction, by taking the gates off one at a time from the first.
theorem main : ∀ (G : List Gate) (n : ℕ) (M : Finset ℕ) (out : ℕ),
    (∀ u ∈ M, u < n) → mono G → (∀ k, (run Fd G (d0 n M)).getD k 0 ≤ 1) →
    ∃ (D : List Gate) (σ : ℕ → Option (Option ℕ)),
      mono D ∧ (∀ u, Valid (pos M n + D.length) (σ u)) ∧
      D.length + (M.filter (fun u => σ u ≠ none)).card ≤ G.length + 1 ∧
      (∀ u ∈ M, Relation.ReflTransGen (rel G n) u out → σ u ≠ none) ∧
      ∀ z : ℕ → Bool,
        (run Fw G ((List.range n).map z)).getD out false =
          ((run Fw G ((List.range n).map (zero M z))).getD out false ||
            decide (∃ u ∈ M, z u = true ∧ cv (run Fw D (U n M z)) (σ u) = true)) := by
  intro G
  induction G with
  | nil =>
    intro n M out hM _ _
    refine ⟨[], fun u => if u = out then some none else none, ?_, ?_, ?_, ?_, ?_⟩
    · intro h hh
      exact absurd hh (by simp)
    · intro u k hk
      by_cases e : u = out <;> simp [e] at hk
    · have hsub : M.filter (fun u =>
          (if u = out then some none else none : Option (Option ℕ)) ≠ none) ⊆ {out} := by
        intro u hu
        rw [Finset.mem_filter] at hu
        rw [Finset.mem_singleton]
        by_contra hne
        exact hu.2 (by simp [hne])
      have := Finset.card_le_card hsub
      rw [Finset.card_singleton] at this
      simp only [List.length_nil]
      omega
    · intro u _ hr
      rw [reach_nil n u out hr]
      simp
    · intro z
      beta_reduce
      rw [run_nil Fw ((List.range n).map z), run_nil Fw ((List.range n).map (zero M z)),
        Lget, Lget]
      have hcvE : (∃ u ∈ M, z u = true ∧
          cv (run Fw [] (U n M z)) (if u = out then some none else none) = true) ↔
          (out ∈ M ∧ z out = true) := by
        constructor
        · rintro ⟨u, hu, hzu, hcvu⟩
          by_cases e : u = out
          · subst e; exact ⟨hu, hzu⟩
          · rw [if_neg e] at hcvu
            exact absurd hcvu (by simp [cv])
        · rintro ⟨ho, hzo⟩
          exact ⟨out, ho, hzo, by rw [if_pos rfl]; rfl⟩
      by_cases ho : out ∈ M
      · have hlt := hM out ho
        have h0 : zero M z out = false := by simp [zero, ho]
        rw [if_pos hlt, if_pos hlt, h0, Bool.false_or, Bool.eq_iff_iff, decide_eq_true_eq, hcvE]
        exact ⟨fun h => ⟨ho, h⟩, fun h => h.2⟩
      · have hE : ¬ ∃ u ∈ M, z u = true ∧
            cv (run Fw [] (U n M z)) (if u = out then some none else none) = true := by
          rw [hcvE]
          exact fun h => ho h.1
        rw [decide_eq_false hE, Bool.or_false]
        simp [zero, ho]
  | cons g0 G' ih =>
    intro n M out hM hmono hdeg
    have hg0 := hmono g0 (by simp)
    have hmono' : mono G' := fun h hh => hmono h (by simp [hh])
    have hd0len : (d0 n M).length = n := by simp [d0]
    have hdeg0 : Fd (d0 n M) g0 ≤ 1 := by
      have h := hdeg n
      rw [run_cons, run_getD_lt _ _ _ _ _ (by simp [hd0len])] at h
      have e := getD_append_len (d0 n M) (Fd (d0 n M) g0) 0
      rw [hd0len] at e
      rwa [e] at h
    have hnM : n ∉ M := fun h => by have := hM n h; omega
    have hzz : ∀ z : ℕ → Bool,
        (List.range n).map (zero M (zero M z)) = (List.range n).map (zero M z) := by
      intro z
      apply List.map_congr_left
      intro i _
      by_cases hi : i ∈ M <;> simp [zero, hi]
    have hUz : ∀ z : ℕ → Bool, U n M (zero M z) = U n M z := fun z =>
      U_congr n M _ _ (fun i _ hi => by simp [zero, hi])
    have hz0 : ∀ z : ℕ → Bool, ∀ u ∈ M, zero M z u = false := fun z u hu => by simp [zero, hu]
    by_cases hT : g0.inputs.filter (fun a => decide (a ∈ M)) = []
    · have hall : ∀ a ∈ g0.inputs, a ∉ M := by
        intro a ha haM
        have : a ∈ g0.inputs.filter (fun a => decide (a ∈ M)) :=
          List.mem_filter.mpr ⟨ha, by simp [haM]⟩
        rw [hT] at this
        simp at this
      have hFd : Fd (d0 n M) g0 = 0 := by
        rcases hg0.1 with hop | hop
        · rw [Fd_and g0 hop, deg_and n M hM, hT]; rfl
        · rw [Fd_or g0 hop, deg_or n M hM, if_pos hT]
      have hd' : d0 (n + 1) M = d0 n M ++ [Fd (d0 n M) g0] := by
        rw [d0_succ n M M (fun i _ => Iff.rfl), if_neg hnM, hFd]
      obtain ⟨D', σ', i1, i2, i3, i4, i5⟩ := ih (n + 1) M out
        (fun u hu => by have := hM u hu; omega) hmono'
        (by intro k; rw [hd']; have := hdeg k; rwa [run_cons] at this)
      rw [pos_succ_not n M hnM] at i2
      refine ⟨⟨g0.op, g0.inputs.map (fun a => if a < n then pos M a else pos M n)⟩ :: D', σ',
        ?_, ?_, ?_, ?_, ?_⟩
      · intro h hh
        rcases List.mem_cons.mp hh with rfl | hh
        · exact ⟨hg0.1, by simpa using hg0.2⟩
        · exact i1 h hh
      · intro u k hk
        have := i2 u k hk
        simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        omega
      · intro u hu hr
        rcases (reach_cons g0 G' n out u hr).2 (hM u hu) with h | ⟨h, _⟩
        · exact i4 u hu h
        · exact absurd hu (hall u h)
      · intro z
        have key : ∀ w : ℕ → Bool, (∀ a ∈ g0.inputs,
            ((List.range n).map w).getD a false = ((List.range n).map z).getD a false) →
            run Fw (g0 :: G') ((List.range n).map w) = run Fw G' ((List.range (n + 1)).map
              (fun i => if i = n then Fw ((List.range n).map z) g0 else w i)) := by
          intro w hw
          rw [run_cons, range_map_snoc]
          congr 3
          unfold Fw
          congr 1
          apply List.map_congr_left
          intro a ha
          exact hw a ha
        have k1 := key z (fun a _ => rfl)
        have k0 := key (zero M z) (fun a ha => by
          rw [Lget, Lget]; simp [zero, hall a ha])
        rw [k1, k0]
        have ihz := i5 (fun i => if i = n then Fw ((List.range n).map z) g0 else z i)
        have hz0' : (List.range (n + 1)).map (zero M
            (fun i => if i = n then Fw ((List.range n).map z) g0 else z i)) =
            (List.range (n + 1)).map
              (fun i => if i = n then Fw ((List.range n).map z) g0 else zero M z i) := by
          apply List.map_congr_left
          intro i _
          by_cases e : i = n
          · subst e; simp [zero, hnM]
          · simp [zero, e]
        rw [hz0'] at ihz
        rw [ihz]
        congr 1
        have hU : U (n + 1) M (fun i => if i = n then Fw ((List.range n).map z) g0 else z i) =
            U n M z ++ [Fw ((List.range n).map z) g0] := by
          rw [U_succ_not _ _ _ hnM, if_pos rfl]
          congr 1
          exact U_congr n M _ _ (fun i hi _ => by simp [Nat.ne_of_lt hi])
        have hW : run Fw (⟨g0.op, g0.inputs.map (fun a => if a < n then pos M a else pos M n)⟩
            :: D') (U n M z) = run Fw D' (U n M z ++ [Fw ((List.range n).map z) g0]) := by
          rw [run_cons]
          congr 3
          unfold Fw
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro a ha
          simp only [Function.comp]
          by_cases han : a < n
          · rw [if_pos han, U_getD M z a n (hall a ha) han, Lget, if_pos han]
          · rw [if_neg han, getD_ge _ _ _ (by rw [U_length]), Lget, if_neg han]
        rw [hU, hW]
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨u, hu, h1, h2⟩
          have := hM u hu
          exact ⟨u, hu, by simpa [Nat.ne_of_lt this] using h1, h2⟩
        · rintro ⟨u, hu, h1, h2⟩
          have := hM u hu
          exact ⟨u, hu, by simpa [Nat.ne_of_lt this] using h1, h2⟩
    · have hFd : Fd (d0 n M) g0 = 1 := by
        rcases hg0.1 with hop | hop
        · have h := hdeg0
          rw [Fd_and g0 hop, deg_and n M hM] at h ⊢
          have : (g0.inputs.filter (fun a => decide (a ∈ M))).length ≠ 0 := by
            rwa [Ne, List.length_eq_zero_iff]
          omega
        · rw [Fd_or g0 hop, deg_or n M hM, if_neg hT]
      have hiff : ∀ i, i < n → (i ∈ insert n M ↔ i ∈ M) := by
        intro i hi
        simp [Nat.ne_of_lt hi]
      have hnM' : n ∈ insert n M := Finset.mem_insert_self _ _
      have hd' : d0 (n + 1) (insert n M) = d0 n M ++ [Fd (d0 n M) g0] := by
        rw [d0_succ n M (insert n M) hiff, if_pos hnM', hFd]
      have hp' : pos (insert n M) (n + 1) = pos M n := by
        rw [pos_succ_mem n (insert n M) hnM', pos_congrM n M (insert n M) hiff]
      have hU' : ∀ w : ℕ → Bool, U (n + 1) (insert n M) w = U n M w := by
        intro w
        rw [U_succ_mem n (insert n M) w hnM', U_congrM n M (insert n M) w hiff]
      obtain ⟨D', σ', i1, i2, i3, i4, i5⟩ := ih (n + 1) (insert n M) out
        (by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hu
          · omega
          · have := hM u hu; omega) hmono'
        (by intro k; rw [hd']; have := hdeg k; rwa [run_cons] at this)
      rw [hp'] at i2
      have sem : ∀ (w : ℕ → Bool) (b : Bool),
          (run Fw G' ((List.range n).map w ++ [b])).getD out false =
            ((run Fw G' ((List.range n).map (zero M w) ++ [false])).getD out false ||
              decide ((∃ u ∈ M, w u = true ∧ cv (run Fw D' (U n M w)) (σ' u) = true) ∨
                (b = true ∧ cv (run Fw D' (U n M w)) (σ' n) = true))) := by
        intro w b
        have h := i5 (fun i => if i = n then b else w i)
        have e2 : (List.range (n + 1)).map (zero (insert n M) (fun i => if i = n then b else w i)) =
            (List.range n).map (zero M w) ++ [false] := by
          rw [← range_map_snoc]
          apply List.map_congr_left
          intro i _
          by_cases e : i = n
          · subst e; simp [zero]
          · simp [zero, e]
        have e3 : U (n + 1) (insert n M) (fun i => if i = n then b else w i) = U n M w := by
          rw [hU']
          exact U_congr n M _ _ (fun i hi _ => by simp [Nat.ne_of_lt hi])
        rw [range_map_snoc, e2, e3] at h
        rw [h]
        congr 1
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨u, hu, h1, h2⟩
          rcases Finset.mem_insert.mp hu with rfl | hu
          · right
            exact ⟨by simpa using h1, h2⟩
          · left
            have := hM u hu
            exact ⟨u, hu, by simpa [Nat.ne_of_lt this] using h1, h2⟩
        · rintro (⟨u, hu, h1, h2⟩ | ⟨h1, h2⟩)
          · have := hM u hu
            exact ⟨u, Finset.mem_insert_of_mem hu, by simpa [Nat.ne_of_lt this] using h1, h2⟩
          · exact ⟨n, hnM', by simpa using h1, h2⟩
      by_cases hcn : σ' n = none
      · refine ⟨D', σ', i1, i2, ?_, ?_, ?_⟩
        · have := Finset.card_le_card (Finset.filter_subset_filter (fun u => σ' u ≠ none)
            (Finset.subset_insert n M))
          simp only [List.length_cons]
          omega
        · intro u hu hr
          rcases (reach_cons g0 G' n out u hr).2 (hM u hu) with h | ⟨_, h⟩
          · exact i4 u (Finset.mem_insert_of_mem hu) h
          · exact absurd hcn (i4 n hnM' h)
        · intro z
          rw [run_cons, run_cons, sem z (Fw ((List.range n).map z) g0),
            sem (zero M z) (Fw ((List.range n).map (zero M z)) g0), hzz, hUz, hcn]
          exact comb0 M z (zero M z) (fun u => cv (run Fw D' (U n M z)) (σ' u)) (hz0 z) _ _ _ _ rfl
      · obtain ⟨D₁, c, fv, j1, j2, j3, j4, j5, j6, j7, j8⟩ :=
          gate_step n M hM g0 hg0 hT hdeg0 D' (σ' n) i1 hcn (i2 n)
        have hσ1 : ∀ u, Valid (pos M n + D₁.length) (σ' u) := fun u k hk => by
          have := i2 u k hk; omega
        obtain ⟨D, σ, l1, l2, l3, l4, l5, l6, l7⟩ := joinList (pos M n) M c
          (g0.inputs.filter (fun a => decide (a ∈ M))) D₁ σ' j1 hσ1 j5
        refine ⟨D, σ, l1, l2, ?_, ?_, ?_⟩
        · have hK : ((insert n M).filter (fun u => σ' u ≠ none)).card =
              (M.filter (fun u => σ' u ≠ none)).card + 1 := by
            rw [Finset.filter_insert, if_pos hcn, Finset.card_insert_of_notMem (by simp [hnM])]
          simp only [List.length_cons]
          omega
        · intro u hu hr
          rcases (reach_cons g0 G' n out u hr).2 (hM u hu) with h | ⟨h, _⟩
          · exact l5 u (i4 u (Finset.mem_insert_of_mem hu) h)
          · exact l6 j4 u (List.mem_filter.mpr ⟨h, by simp [hu]⟩)
        · intro z
          rw [run_cons, run_cons, sem z (Fw ((List.range n).map z) g0),
            sem (zero M z) (Fw ((List.range n).map (zero M z)) g0), hzz, hUz]
          obtain ⟨-, m2⟩ := l7 (U n M z) (U_length n M z)
          have hcvσ : ∀ u, cv (run Fw D (U n M z)) (σ u) =
              (cv (run Fw D' (U n M z)) (σ' u) ||
                (decide (u ∈ g0.inputs.filter (fun a => decide (a ∈ M))) &&
                  (cv (run Fw D' (U n M z)) (σ' n) && fv z))) := by
            intro u
            rw [m2 u, j7 z, cv_ext (run Fw D' (U n M z)) (run Fw D₁ (U n M z))
              (pos M n + D'.length) (σ' u) (j6 (U n M z) (U_length n M z)) (i2 u)]
          simp only [hcvσ]
          rw [j8 z]
          exact comb M (g0.inputs.filter (fun a => decide (a ∈ M)))
            (fun u hu => by simpa using (List.mem_filter.mp hu).2) z (zero M z)
            (fun u => cv (run Fw D' (U n M z)) (σ' u)) (hz0 z) _ _ _ _

theorem mem_le_sum (l : List ℕ) (x : ℕ) (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem mem_le_foldr_max (l : List ℕ) (x : ℕ) (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem deg_mono_rel (G : List Gate) (n : ℕ) (M : Finset ℕ)
    (hG : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or) (a b : ℕ) (h : rel G n a b) :
    (run Fd G (d0 n M)).getD a 0 ≤ (run Fd G (d0 n M)).getD b 0 := by
  obtain ⟨hab, i, hb, hin⟩ := h
  have hd0len : (d0 n M).length = n := by simp [d0]
  obtain ⟨pre, -, hpre, hv⟩ := run_gate Fd G (d0 n M) 0 i.val i.isLt
  rw [hd0len] at hpre hv
  rw [hb, hv, ← hpre a (by omega)]
  rw [List.get_eq_getElem] at hin
  have hmem : pre.getD a 0 ∈ (G[i.val]).inputs.map (fun j => pre.getD j 0) :=
    List.mem_map_of_mem hin
  rcases hG _ (List.getElem_mem i.isLt) with hop | hop
  · rw [Fd_and _ hop]
    exact mem_le_sum _ _ hmem
  · rw [Fd_or _ hop]
    exact mem_le_foldr_max _ _ hmem

theorem deg_mono_reach (G : List Gate) (n : ℕ) (M : Finset ℕ)
    (hG : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or) (a out : ℕ)
    (h : Relation.ReflTransGen (rel G n) a out) :
    (run Fd G (d0 n M)).getD a 0 ≤ (run Fd G (d0 n M)).getD out 0 := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih (deg_mono_rel G n M hG _ _ hbc)

def zf (P L : ℕ) (x : Fin P → Bool) (y : Fin L → Bool) : ℕ → Bool := fun i =>
  if h : i < P then x ⟨i, h⟩ else if h2 : i - P < L then y ⟨i - P, h2⟩ else false

theorem ofFn_append_eq (P L : ℕ) (x : Fin P → Bool) (y : Fin L → Bool) :
    List.ofFn x ++ List.ofFn y = (List.range (P + L)).map (zf P L x y) := by
  apply List.ext_getElem?
  intro i
  by_cases h1 : i < P
  · have h3 : i < P + L := by omega
    rw [List.getElem?_append_left (by simpa using h1)]
    simp [List.getElem?_ofFn, zf, h1, h3]
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt h1)]
    by_cases h2 : i < P + L
    · have h4 : i - P < L := by omega
      simp [List.getElem?_ofFn, zf, h1, h2, h4]
    · have h4 : ¬ i - P < L := by omega
      simp [List.getElem?_ofFn, h2, h4]

theorem U_points (P L : ℕ) (x : Fin P → Bool) (y : Fin L → Bool) :
    U (P + L) (Finset.Ico P (P + L)) (zf P L x y) = List.ofFn x := by
  have hf : (List.range (P + L)).filter (fun i => decide (i ∉ Finset.Ico P (P + L))) =
      List.range P := by
    rw [List.range_add, List.filter_append]
    have h1 : (List.range P).filter (fun i => decide (i ∉ Finset.Ico P (P + L))) =
        List.range P := by
      apply List.filter_eq_self.mpr
      intro i hi
      rw [List.mem_range] at hi
      simp only [Finset.mem_Ico, decide_eq_true_eq]
      omega
    have h2 : ((List.range L).map (fun j => P + j)).filter
        (fun i => decide (i ∉ Finset.Ico P (P + L))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      rw [List.mem_range] at hj
      simp only [Finset.mem_Ico, decide_eq_true_eq]
      omega
    rw [h1, h2, List.append_nil]
  unfold U
  rw [hf]
  apply List.ext_getElem?
  intro i
  by_cases h1 : i < P
  · simp [List.getElem?_ofFn, zf, h1]
  · simp [List.getElem?_ofFn, h1]

def ow (c : Option (Option ℕ)) (bad : ℕ) : ℕ :=
  match c with
  | some (some k) => k
  | _ => bad

theorem cv_iff (W : List Bool) (c : Option (Option ℕ)) (bad : ℕ) (hbad : W.length ≤ bad) :
    cv W c = true ↔ (c = some none ∨ W.getD (ow c bad) false = true) := by
  rcases c with _ | _ | k
  · simp [cv, ow, List.getElem?_eq_none hbad]
  · simp [cv]
  · simp [cv, ow]

end PEqualNP.Outside.L_meta_738

theorem PEqualNP.Outside.L_meta_738 : ∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true))) := by
  intro P1 L1 C1 N1 hmonoC hfan hdeg hreach hN
  have hM : ∀ u ∈ Finset.Ico P1 (P1 + L1), u < P1 + L1 := fun u hu => (Finset.mem_Ico.mp hu).2
  have hmono : PEqualNP.Outside.L_meta_738.mono C1.gates := fun g hg => ⟨hmonoC g hg, hfan g hg⟩
  have hout : (PEqualNP.Outside.L_meta_738.run PEqualNP.Outside.L_meta_738.Fd C1.gates
      (PEqualNP.Outside.L_meta_738.d0 (P1 + L1) (Finset.Ico P1 (P1 + L1)))).getD C1.output 0 ≤ 1 :=
    hdeg
  have hd0len : (PEqualNP.Outside.L_meta_738.d0 (P1 + L1) (Finset.Ico P1 (P1 + L1))).length =
      P1 + L1 := by simp [PEqualNP.Outside.L_meta_738.d0]
  have hdegall : ∀ k, (PEqualNP.Outside.L_meta_738.run PEqualNP.Outside.L_meta_738.Fd C1.gates
      (PEqualNP.Outside.L_meta_738.d0 (P1 + L1) (Finset.Ico P1 (P1 + L1)))).getD k 0 ≤ 1 := by
    intro k
    by_cases h1 : k < P1 + L1
    · rw [PEqualNP.Outside.L_meta_738.run_getD_lt _ _ _ _ _ (by rw [hd0len]; exact h1),
        PEqualNP.Outside.L_meta_738.d0_getD _ _ hM]
      split_ifs <;> omega
    · by_cases h2 : k < P1 + L1 + C1.gates.length
      · have hr := hreach ⟨k - (P1 + L1), by omega⟩
        have hk : P1 + L1 + (k - (P1 + L1)) = k := by omega
        simp only [hk] at hr
        exact le_trans (PEqualNP.Outside.L_meta_738.deg_mono_reach C1.gates (P1 + L1)
          (Finset.Ico P1 (P1 + L1)) hmonoC k C1.output hr) hout
      · rw [PEqualNP.Outside.L_meta_738.getD_ge _ _ _ (by
          rw [PEqualNP.Outside.L_meta_738.run_length, hd0len]; omega)]
        omega
  obtain ⟨D, σ, m1, m2, m3, m4, m5⟩ := PEqualNP.Outside.L_meta_738.main C1.gates (P1 + L1)
    (Finset.Ico P1 (P1 + L1)) C1.output hM hmono hdegall
  refine ⟨⟨D, 0⟩, Finset.univ.filter (fun w : Fin L1 => σ (P1 + w.val) = some none),
    fun w => PEqualNP.Outside.L_meta_738.ow (σ (P1 + w.val)) (P1 + D.length), ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact (m1 g hg).1
  · intro g hg
    exact (m1 g hg).2
  · have hcard : N1.card ≤ ((Finset.Ico P1 (P1 + L1)).filter (fun u => σ u ≠ none)).card := by
      apply Finset.card_le_card_of_injOn (fun w : Fin L1 => P1 + w.val)
      · intro w hw
        have hmem : P1 + w.val ∈ Finset.Ico P1 (P1 + L1) :=
          Finset.mem_Ico.mpr ⟨by omega, by have := w.isLt; omega⟩
        exact Finset.mem_filter.mpr ⟨hmem, m4 _ hmem ((hN w).mp hw)⟩
      · intro w _ w' _ hww
        apply Fin.ext
        have : P1 + w.val = P1 + w'.val := hww
        omega
    have hs1 : (⟨D, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = D.length := rfl
    have hs2 : C1.size = C1.gates.length := rfl
    rw [hs1, hs2]
    omega
  · intro x y
    have hlenW : (PEqualNP.Outside.L_meta_738.run PEqualNP.Outside.L_meta_738.Fw D
        (List.ofFn x)).length = P1 + D.length := by
      rw [PEqualNP.Outside.L_meta_738.run_length, List.length_ofFn]
    have hzero : (List.range (P1 + L1)).map (PEqualNP.Outside.L_meta_738.zero
        (Finset.Ico P1 (P1 + L1)) (PEqualNP.Outside.L_meta_738.zf P1 L1 x y)) =
        List.ofFn x ++ List.ofFn (fun _ : Fin L1 => false) := by
      rw [PEqualNP.Outside.L_meta_738.ofFn_append_eq]
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      by_cases h1 : i < P1
      · simp [PEqualNP.Outside.L_meta_738.zero, PEqualNP.Outside.L_meta_738.zf, h1]
      · have h2 : i - P1 < L1 := by omega
        have h3 : P1 ≤ i := by omega
        simp [PEqualNP.Outside.L_meta_738.zero, PEqualNP.Outside.L_meta_738.zf, h1, h2, h3, hi]
    have e1 := m5 (PEqualNP.Outside.L_meta_738.zf P1 L1 x y)
    rw [← PEqualNP.Outside.L_meta_738.ofFn_append_eq, hzero,
      PEqualNP.Outside.L_meta_738.U_points] at e1
    show (PEqualNP.Outside.L_meta_738.run PEqualNP.Outside.L_meta_738.Fw C1.gates _).getD
      C1.output false = ((PEqualNP.Outside.L_meta_738.run PEqualNP.Outside.L_meta_738.Fw
        C1.gates _).getD C1.output false || _)
    rw [e1]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨u, hu, hzu, hcu⟩
      have hu' := Finset.mem_Ico.mp hu
      have h1 : ¬ u < P1 := by omega
      have h2 : u - P1 < L1 := by omega
      have hPu : P1 + (u - P1) = u := by omega
      refine ⟨⟨u - P1, h2⟩, ?_, ?_⟩
      · simpa [PEqualNP.Outside.L_meta_738.zf, h1, h2] using hzu
      · rcases (PEqualNP.Outside.L_meta_738.cv_iff _ (σ u) (P1 + D.length)
          (le_of_eq hlenW)).mp hcu with h | h
        · left
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hPu] using h⟩
        · right
          show (PEqualNP.Outside.L_meta_738.run PEqualNP.Outside.L_meta_738.Fw D
            (List.ofFn x)).getD (PEqualNP.Outside.L_meta_738.ow (σ (P1 + (u - P1)))
              (P1 + D.length)) false = true
          rw [hPu]
          exact h
    · rintro ⟨u1, hy, hc⟩
      have hmem : P1 + u1.val ∈ Finset.Ico P1 (P1 + L1) :=
        Finset.mem_Ico.mpr ⟨by omega, by have := u1.isLt; omega⟩
      have h1 : ¬ P1 + u1.val < P1 := by omega
      have h2 : P1 + u1.val - P1 < L1 := by have := u1.isLt; omega
      refine ⟨P1 + u1.val, hmem, ?_, ?_⟩
      · simpa [PEqualNP.Outside.L_meta_738.zf, h1, h2] using hy
      · apply (PEqualNP.Outside.L_meta_738.cv_iff _ (σ (P1 + u1.val)) (P1 + D.length)
          (le_of_eq hlenW)).mpr
        rcases hc with h | h
        · left
          exact (Finset.mem_filter.mp h).2
        · right
          exact h
