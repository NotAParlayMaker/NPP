import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2902

open PEqualNP.CircuitLowerBounds

-- The twelve edges, the twelve edge rows and all twenty-four rows of the statement.
def E : List (Fin 9 × Fin 9) := [(0, 1), (1, 2), (2, 3), (0, 4), (3, 4), (0, 5), (1, 6), (2, 7),
  (5, 7), (3, 8), (5, 8), (6, 8)]
def TR : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
def AR : List ℕ := [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261,
  264, 276, 288, 320, 385, 402]

theorem tr_sub : ∀ r ∈ TR, r ∈ AR := by decide

-- Every input with an edge lies above an edge row; every input without one lies below a row
-- that is not an edge row.
theorem rows_true : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    E.any (fun e => (![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin 9 → Bool) e.1 &&
      (![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin 9 → Bool) e.2) = true →
    ∃ r ∈ TR, ∀ i : Fin 9, r.testBit i = true →
      (![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin 9 → Bool) i = true := by
  decide +kernel

theorem rows_false : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    E.any (fun e => (![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin 9 → Bool) e.1 &&
      (![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin 9 → Bool) e.2) = false →
    ∃ r ∈ AR, r ∉ TR ∧ ∀ i : Fin 9,
      (![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin 9 → Bool) i = true → r.testBit i = true := by
  decide +kernel

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (w : List Bool) (b : Bool) (t : ℕ) :
    (w ++ [b]).getD t false =
      if t < w.length then w.getD t false else if t = w.length then b else false := by
  by_cases h1 : t < w.length
  · simp [h1, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · by_cases h2 : t = w.length
    · subst h2; simp
    · have h4 : ¬ t < (w ++ [b]).length := by simp; omega
      rw [List.getD_eq_default _ _ (not_lt.mp h4)]
      simp [h1, h2]

theorem mono_fold : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (W W' : List Bool), W.length = W'.length →
      (∀ i, W.getD i false = true → W'.getD i false = true) →
      ∀ i, (gs.foldl step W).getD i false = true → (gs.foldl step W').getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ W W' _ h i; exact h i
  | cons g gs ih =>
    intro hops W W' hlen hle
    have hval : g.op.eval (g.inputs.map fun i => W.getD i false) = true →
        g.op.eval (g.inputs.map fun i => W'.getD i false) = true := by
      rcases hops g (List.mem_cons_self ..) with h | h <;> rw [h] <;> intro hv
      · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hv ⊢
        rintro _ ⟨a, ha, rfl⟩
        exact hle a (hv _ ⟨a, ha, rfl⟩)
      · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
        obtain ⟨_, ⟨a, ha, rfl⟩, hb⟩ := hv
        exact ⟨_, ⟨a, ha, rfl⟩, hle a hb⟩
    apply ih (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hlen]
    · intro i
      simp only [step]
      rw [getD_snoc, getD_snoc, hlen]
      split_ifs with h1 h2
      · exact hle i
      · exact hval
      · simp

-- Fixing input v to false: a gate reading v is deleted, its wire redirected to the wire it now
-- equals (F0, a wire that never exists, for false). phi maps old wires to new ones.
def upd (φ : ℕ → ℕ) (a b : ℕ) : ℕ → ℕ := fun i => if i = a then b else φ i

def tgt (v F0 : ℕ) (φ : ℕ → ℕ) (g : Gate) : ℕ :=
  match g.op with
  | GateOp.or =>
    match g.inputs.filter (fun i => i != v) with
    | [] => F0
    | w :: _ => φ w
  | _ => F0

def elim (v F0 : ℕ) : ℕ → ℕ → (ℕ → ℕ) → List Gate → List Gate × (ℕ → ℕ)
  | _, _, φ, [] => ([], φ)
  | k, e, φ, g :: gs =>
    if v ∈ g.inputs then elim v F0 (k + 1) e (upd φ (10 + k) (tgt v F0 φ g)) gs
    else
      ((⟨g.op, g.inputs.map φ⟩ : Gate) ::
          (elim v F0 (k + 1) (e + 1) (upd φ (10 + k) (10 + e)) gs).1,
        (elim v F0 (k + 1) (e + 1) (upd φ (10 + k) (10 + e)) gs).2)

theorem elim_length : ∀ (gs : List Gate) (v F0 k e : ℕ) (φ : ℕ → ℕ),
    (elim v F0 k e φ gs).1.length + (gs.filter (fun g => decide (v ∈ g.inputs))).length =
      gs.length := by
  intro gs
  induction gs with
  | nil => intros; simp [elim]
  | cons g gs ih =>
    intro v F0 k e φ
    by_cases h : v ∈ g.inputs
    · have := ih v F0 (k + 1) e (upd φ (10 + k) (tgt v F0 φ g))
      simp only [elim, h, ↓reduceIte, List.filter_cons, decide_true, List.length_cons]
      omega
    · have := ih v F0 (k + 1) (e + 1) (upd φ (10 + k) (10 + e))
      simp only [elim, h, ↓reduceIte, List.filter_cons, decide_false, List.length_cons]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

theorem elim_ops : ∀ (gs : List Gate) (v F0 k e : ℕ) (φ : ℕ → ℕ),
    ∀ g' ∈ (elim v F0 k e φ gs).1, ∃ g ∈ gs, g'.op = g.op ∧ g'.inputs.length = g.inputs.length := by
  intro gs
  induction gs with
  | nil => intros _ _ _ _ _ g' hg; simp [elim] at hg
  | cons g gs ih =>
    intro v F0 k e φ g' hg
    by_cases h : v ∈ g.inputs
    · simp only [elim, h, ↓reduceIte] at hg
      obtain ⟨g0, hg0, h1, h2⟩ := ih _ _ _ _ _ g' hg
      exact ⟨g0, List.mem_cons_of_mem _ hg0, h1, h2⟩
    · simp only [elim, h, ↓reduceIte, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨g, List.mem_cons_self .., rfl, by simp⟩
      · obtain ⟨g0, hg0, h1, h2⟩ := ih _ _ _ _ _ g' hg
        exact ⟨g0, List.mem_cons_of_mem _ hg0, h1, h2⟩

theorem tgt_range (v F0 e : ℕ) (φ : ℕ → ℕ) (g : Gate)
    (hφall : ∀ i, φ i < 10 + e ∨ φ i = F0) : tgt v F0 φ g < 10 + e ∨ tgt v F0 φ g = F0 := by
  unfold tgt
  split
  · split
    · right; rfl
    · exact hφall _
  · right; rfl

theorem tgt_val (v F0 : ℕ) (φ : ℕ → ℕ) (g : Gate) (W W' : List Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2) (hv : v ∈ g.inputs)
    (hWv : W.getD v false = false) (hF : W'.getD F0 false = false)
    (hinv : ∀ i, W'.getD (φ i) false = W.getD i false) :
    W'.getD (tgt v F0 φ g) false = g.op.eval (g.inputs.map fun i => W.getD i false) := by
  rcases g with ⟨op, ins⟩
  simp only at hop hlen hv ⊢
  rcases hop with rfl | rfl
  · simp only [tgt, hF]
    rw [eq_comm, Bool.eq_false_iff]
    intro h
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h
    have := h _ ⟨v, hv, rfl⟩
    rw [hWv] at this
    exact Bool.false_ne_true this
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp at hv
    · simp only [List.mem_singleton] at hv
      subst hv
      simp only [tgt, List.filter_cons, List.filter_nil, bne_self_eq_false, Bool.false_eq_true,
        ↓reduceIte, hF, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        hWv, id, Bool.or_false]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      by_cases ha : a = v <;> by_cases hb : b = v
      · subst ha; subst hb
        simp only [tgt, List.filter_cons, List.filter_nil, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte, hF, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          hWv, id, Bool.or_false]
      · subst ha
        simp only [tgt, List.filter_cons, List.filter_nil, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte, show (b != a) = true from bne_iff_ne.mpr hb]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          hinv, hWv, Bool.false_or, Bool.or_false]
      · subst hb
        simp only [tgt, List.filter_cons, List.filter_nil, bne_self_eq_false, Bool.false_eq_true,
          ↓reduceIte, show (a != b) = true from bne_iff_ne.mpr ha]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          hinv, hWv, Bool.or_false]
      · exfalso; rcases hv with h | h
        · exact ha h.symm
        · exact hb h.symm
    · simp at hlen

theorem elim_wires : ∀ (gs : List Gate) (v F0 k e : ℕ) (φ : ℕ → ℕ) (W W' : List Bool),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    W.length = 10 + k → W'.length = 10 + e → 10 + e + gs.length ≤ F0 → v < 10 →
    (∀ i, 10 + k ≤ i → φ i = F0) → (∀ i, φ i < 10 + e ∨ φ i = F0) →
    W.getD v false = false →
    (∀ i, W'.getD (φ i) false = W.getD i false) →
    ∀ i, ((elim v F0 k e φ gs).1.foldl step W').getD ((elim v F0 k e φ gs).2 i) false =
      (gs.foldl step W).getD i false := by
  intro gs
  induction gs with
  | nil => intro v F0 k e φ W W' _ _ _ _ _ _ _ _ hinv i; simpa [elim] using hinv i
  | cons g gs ih =>
    intro v F0 k e φ W W' hgs hW hW' hF hv10 hφ hφall hWv hinv
    have hg := hgs g (List.mem_cons_self ..)
    have hgs' : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    simp only [List.length_cons] at hF
    have hF0 : W'.getD F0 false = false := List.getD_eq_default _ _ (by omega)
    by_cases hvg : v ∈ g.inputs
    · simp only [elim, hvg, ↓reduceIte, List.foldl_cons]
      have ht := tgt_val v F0 φ g W W' hg.1 hg.2 hvg hWv hF0 hinv
      have htb := tgt_range v F0 e φ g hφall
      apply ih v F0 (k + 1) e (upd φ (10 + k) (tgt v F0 φ g)) (step W g) W' hgs'
      · simp only [step, List.length_append, List.length_singleton]; omega
      · exact hW'
      · omega
      · exact hv10
      · intro i hi
        simp only [upd]
        rw [ite_eq_right (by omega)]
        exact hφ i (by omega)
      · intro i
        simp only [upd]
        split_ifs
        · exact htb
        · exact hφall i
      · simp only [step]
        rw [getD_snoc, ite_eq_left (by omega)]
        exact hWv
      · intro i
        simp only [upd, step]
        rw [getD_snoc, hW]
        by_cases hi : i = 10 + k
        · subst hi
          simp only [↓reduceIte, lt_irrefl]
          exact ht
        · simp only [hi, ↓reduceIte]
          by_cases hi2 : i < 10 + k
          · simp only [hi2, ↓reduceIte]
            exact hinv i
          · simp only [hi2, ↓reduceIte]
            rw [hφ i (by omega)]
            exact hF0
    · simp only [elim, hvg, ↓reduceIte, List.foldl_cons]
      have hc : GateOp.eval g.op ((g.inputs.map φ).map fun i => W'.getD i false) =
          g.op.eval (g.inputs.map fun i => W.getD i false) := by
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact hinv a
      apply ih v F0 (k + 1) (e + 1) (upd φ (10 + k) (10 + e)) (step W g)
        (step W' ⟨g.op, g.inputs.map φ⟩) hgs'
      · simp only [step, List.length_append, List.length_singleton]; omega
      · simp only [step, List.length_append, List.length_singleton]; omega
      · omega
      · exact hv10
      · intro i hi
        simp only [upd]
        rw [ite_eq_right (by omega)]
        exact hφ i (by omega)
      · intro i
        simp only [upd]
        split_ifs
        · left; omega
        · rcases hφall i with h | h
          · left; omega
          · right; exact h
      · simp only [step]
        rw [getD_snoc, ite_eq_left (by omega)]
        exact hWv
      · intro i
        simp only [upd, step]
        rw [hc, getD_snoc, getD_snoc, hW, hW']
        have hF1 : ¬ F0 < 10 + e := by omega
        have hF2 : ¬ F0 = 10 + e := by omega
        by_cases hi : i = 10 + k
        · subst hi
          simp
        · simp only [hi, ↓reduceIte]
          by_cases hi2 : i < 10 + k
          · rcases hφall i with h | h
            · simp only [h, hi2, ↓reduceIte]
              exact hinv i
            · rw [h]
              simp only [hF1, hF2, hi2, ↓reduceIte]
              rw [← hinv i, h, hF0]
          · rw [hφ i (by omega)]
            simp only [hF1, hF2, hi2, ↓reduceIte]

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem vec9 (y : Fin 9 → Bool) : y = ![y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8] := by
  funext i
  fin_cases i <;> rfl

end PEqualNP.Outside.L_meta_2902

theorem PEqualNP.Outside.L_meta_2902 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       ∀ x4 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], (4 : ℕ) ≤ (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x4 ∈ x6.inputs)) x1.gates).length → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size + (4 : ℕ) ≤ x1.size ∧ ∀ (x8 : Fin (9 : ℕ) → Bool), x7.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x9.1 != x4 && x9.2 != x4 && x8 x9.1 && x8 x9.2 := by
  intro C hmono hrows v hvmem hcount
  have hv0 : v ≠ 0 ∧ v ≠ 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvmem
    rcases hvmem with rfl | rfl | rfl | rfl | rfl <;> decide
  have hops : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have := hmono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    exact this
  -- the input with one more wire, the OR of inputs 0 and 4
  have hin : ∀ (y : Fin 9 → Bool) (i : ℕ),
      (List.ofFn y ++ [y 0 || y 4]).getD i false =
        if h : i < 9 then y ⟨i, h⟩ else if i = 9 then (y 0 || y 4) else false := by
    intro y i
    rw [PEqualNP.Outside.L_meta_2902.getD_snoc, List.length_ofFn]
    by_cases h : i < 9
    · simp only [h, ↓reduceIte, dite_true]
      exact PEqualNP.Outside.L_meta_2902.ofFn_getD y i h
    · simp only [h, ↓reduceIte, dite_false]
  -- monotonicity of the circuit in the nine inputs
  have gmono : ∀ y z : Fin 9 → Bool, (∀ i, y i = true → z i = true) →
      C.eval (List.ofFn y ++ [y 0 || y 4]) = true → C.eval (List.ofFn z ++ [z 0 || z 4]) = true := by
    intro y z hyz h
    refine PEqualNP.Outside.L_meta_2902.mono_fold C.gates (fun g hg => (hops g hg).1)
      (List.ofFn y ++ [y 0 || y 4]) (List.ofFn z ++ [z 0 || z 4]) (by simp) ?_ C.output h
    intro i hi
    rw [hin] at hi ⊢
    by_cases h1 : i < 9
    · simp only [h1, dite_true] at hi ⊢
      exact hyz _ hi
    · simp only [h1, dite_false] at hi ⊢
      by_cases h2 : i = 9
      · simp only [h2, ↓reduceIte, Bool.or_eq_true] at hi ⊢
        rcases hi with h | h
        · exact Or.inl (hyz _ h)
        · exact Or.inr (hyz _ h)
      · simp only [h2, ↓reduceIte] at hi
        exact absurd hi Bool.false_ne_true
  have hrow : ∀ r ∈ PEqualNP.Outside.L_meta_2902.AR,
      C.eval (List.ofFn (fun i : Fin 9 => r.testBit i) ++ [r.testBit 0 || r.testBit 4]) =
        decide (r ∈ PEqualNP.Outside.L_meta_2902.TR) := by
    intro r hr
    exact hrows r hr
  -- the circuit computes the edge function on every input
  have hsand : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y ++ [y 0 || y 4]) =
      PEqualNP.Outside.L_meta_2902.E.any (fun e => y e.1 && y e.2) := by
    intro y
    have hy := PEqualNP.Outside.L_meta_2902.vec9 y
    cases h : PEqualNP.Outside.L_meta_2902.E.any (fun e => y e.1 && y e.2)
    · obtain ⟨r, hr, hrn, hle⟩ := PEqualNP.Outside.L_meta_2902.rows_false (y 0) (y 1) (y 2) (y 3)
        (y 4) (y 5) (y 6) (y 7) (y 8) (by rw [← hy]; exact h)
      rw [← hy] at hle
      have hr' := hrow r hr
      rw [decide_eq_false hrn] at hr'
      rw [Bool.eq_false_iff]
      intro hc
      exact Bool.false_ne_true (hr'.symm.trans (gmono y (fun i => r.testBit i) hle hc))
    · obtain ⟨r, hr, hle⟩ := PEqualNP.Outside.L_meta_2902.rows_true (y 0) (y 1) (y 2) (y 3)
        (y 4) (y 5) (y 6) (y 7) (y 8) (by rw [← hy]; exact h)
      rw [← hy] at hle
      have hr' := hrow r (PEqualNP.Outside.L_meta_2902.tr_sub r hr)
      rw [decide_eq_true hr] at hr'
      exact gmono (fun i => r.testBit i) y hle hr'
  -- eliminate the gates reading v
  have hv10 : (v : ℕ) < 10 := by have := v.2; omega
  let F0 : ℕ := 10 + C.gates.length
  let φ0 : ℕ → ℕ := fun i => if i < 10 ∧ i ≠ (v : ℕ) then i else F0
  let R := PEqualNP.Outside.L_meta_2902.elim (v : ℕ) F0 0 0 φ0 C.gates
  refine ⟨⟨R.1, R.2 C.output⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨g, hg, h1, h2⟩ := PEqualNP.Outside.L_meta_2902.elim_ops C.gates _ _ _ _ _ g' hg'
    rw [h1, h2]
    exact hmono g hg
  · have := PEqualNP.Outside.L_meta_2902.elim_length C.gates (v : ℕ) F0 0 0 φ0
    show (PEqualNP.Outside.L_meta_2902.elim (v : ℕ) F0 0 0 φ0 C.gates).1.length + 4 ≤
      C.gates.length
    omega
  · intro x8
    let y : Fin 9 → Bool := fun i => if i = v then false else x8 i
    have hy0 : y 0 = x8 0 := ite_eq_right (Ne.symm hv0.1)
    have hy4 : y 4 = x8 4 := ite_eq_right (Ne.symm hv0.2)
    have hwire := PEqualNP.Outside.L_meta_2902.elim_wires C.gates (v : ℕ) F0 0 0 φ0
      (List.ofFn y ++ [y 0 || y 4]) (List.ofFn x8 ++ [x8 0 || x8 4]) hops (by simp) (by simp)
      (by simp [F0]) hv10
      (by intro i hi; simp only [φ0]; rw [ite_eq_right (by omega)])
      (by intro i; simp only [φ0]; split_ifs with h; exacts [Or.inl (by omega), Or.inr rfl])
      (by rw [hin]; simp [v.2, y])
      (by
        intro i
        simp only [φ0]
        split_ifs with h
        · rw [hin, hin]
          by_cases h9 : i < 9
          · simp only [h9, dite_true, y]
            rw [ite_eq_right]
            intro hc
            exact h.2 (by rw [← hc])
          · simp only [h9, dite_false, hy0, hy4]
        · rw [List.getD_eq_default _ _ (by simp [F0]), hin]
          by_cases h9 : i < 9
          · have hiv : (⟨i, h9⟩ : Fin 9) = v := by
              apply Fin.ext
              simp only
              omega
            simp [h9, y, hiv]
          · have h9' : i ≠ 9 := by omega
            simp [h9, h9'])
      C.output
    have hev : (⟨R.1, R.2 C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval
        (List.ofFn x8 ++ [x8 0 || x8 4]) = C.eval (List.ofFn y ++ [y 0 || y 4]) := hwire
    rw [hev, hsand y]
    have hany : ∀ l : List (Fin 9 × Fin 9), l.any (fun e => y e.1 && y e.2) =
        l.any (fun e => e.1 != v && e.2 != v && x8 e.1 && x8 e.2) := by
      intro l
      congr 1
      funext e
      simp only [y]
      by_cases h1 : e.1 = v
      · simp [h1]
      · by_cases h2 : e.2 = v
        · simp [h2]
        · rw [show (e.1 != v) = true from bne_iff_ne.mpr h1,
            show (e.2 != v) = true from bne_iff_ne.mpr h2]
          simp [h1, h2]
    exact hany _
