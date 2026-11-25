import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5553_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def targetA (u v : Fin 4) : Bool :=
  (4399 : ℕ).testBit (4 * u.val + v.val)

def w5 : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.and, [1, 5]⟩,
    ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [10, 11]⟩], 12⟩

theorem w5_mono2 : Monotone2 w5 := by
  intro g hg
  simp only [w5, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper : RepSizeAtMost targetA 5 :=
  ⟨w5, w5_mono2, by decide, by decide⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · simp only [show i ≠ l.length by omega, ↓reduceIte]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · simp only [show i ≠ l.length by omega, ↓reduceIte]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step
  rw [getD_snoc]
  simp only [show i ≠ w.length by omega, ↓reduceIte]

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
    i < w.length → (gs.foldl step w).getD i false = w.getD i false
  | [], w, i, _ => rfl
  | g :: gs, w, i, hi => by
    rw [List.foldl_cons, fold_prefix gs (step w g) i (by rw [step_len]; omega), step_lt w g i hi]

theorem fold_eq0 : ∀ (gs : List Gate) (w1 w2 : List Bool),
    w1.length = w2.length →
    (∀ i : ℕ, i ≠ 0 → w1.getD i false = w2.getD i false) →
    (∀ g ∈ gs, 0 ∉ g.inputs) →
    (gs.foldl step w1).length = (gs.foldl step w2).length ∧
      (∀ i : ℕ, i ≠ 0 → (gs.foldl step w1).getD i false = (gs.foldl step w2).getD i false)
  | [], w1, w2, hl, heq, _ => ⟨hl, heq⟩
  | g :: gs, w1, w2, hl, heq, hg => by
    have hg0 : 0 ∉ g.inputs := hg g (by simp)
    have hmap : g.inputs.map (fun i => w1.getD i false) =
        g.inputs.map (fun i => w2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact heq i (fun h0 => hg0 (h0 ▸ hi))
    have hlen1 : (step w1 g).length = (step w2 g).length := by
      simp [step_len, hl]
    have heq1 : ∀ i : ℕ, i ≠ 0 → (step w1 g).getD i false = (step w2 g).getD i false := by
      intro i hi
      unfold step
      rw [getD_snoc, getD_snoc, ← hl]
      split_ifs with hil
      · rw [hmap]
      · rcases lt_or_gt_of_ne hil with hlt | hgt
        · exact heq i hi
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    exact fold_eq0 gs (step w1 g) (step w2 g) hlen1 heq1 (fun g' hg' => hg g' (by simp [hg']))

theorem gate_mono (w1 w2 : List Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hle : ∀ i : ℕ, w1.getD i false = true → w2.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  intro hv
  rcases hop with hop | hop <;> rw [hop] at hv ⊢ <;> simp only [GateOp.eval] at hv ⊢
  · rw [List.all_eq_true] at hv ⊢
    intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact hle i (by simpa [id] using hv (w1.getD i false) (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [List.any_eq_true] at hv ⊢
    obtain ⟨b, hb, hbt⟩ := hv
    simp only [List.mem_map] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    refine ⟨w2.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
    simpa [id] using hle i (by simpa [id] using hbt)

theorem fold_mono : ∀ (gs : List Gate) (w1 w2 : List Bool),
    w1.length = w2.length →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ i : ℕ, w1.getD i false = true → w2.getD i false = true) →
    ∀ i : ℕ, (gs.foldl step w1).getD i false = true → (gs.foldl step w2).getD i false = true
  | [], w1, w2, _, _, hle => hle
  | g :: gs, w1, w2, hl, hg, hle => by
    have hop := (hg g (by simp)).1
    have hl1 : (step w1 g).length = (step w2 g).length := by simp [step_len, hl]
    have hle1 : ∀ i : ℕ, (step w1 g).getD i false = true → (step w2 g).getD i false = true := by
      intro i hi
      unfold step at hi ⊢
      rw [getD_snoc] at hi
      rw [getD_snoc, ← hl]
      by_cases hil : i = w1.length
      · simp only [hil, ↓reduceIte] at hi ⊢
        exact gate_mono w1 w2 g hop hle hi
      · simp only [hil, ↓reduceIte] at hi ⊢
        rcases lt_or_gt_of_ne hil with hlt | hgt
        · exact hle i hi
        · rw [List.getD_eq_default _ _ (by omega)] at hi
          cases hi
    exact fold_mono gs (step w1 g) (step w2 g) hl1 (fun g' hg' => hg g' (by simp [hg'])) hle1

def x0w : List Bool := [false, false, false, false, false, false, true, false]

theorem exists_gate_zero (C : Circuit) (hC : Monotone2 C) (hrep : Represents targetA C) :
    ∃ g ∈ C.gates, 0 ∈ g.inputs := by
  have hout0 : C.output ≠ 0 := by
    intro h0
    have h1 := hrep (1 : Fin 4) (1 : Fin 4)
    have h2 : C.eval (oneEach (1 : Fin 4) (1 : Fin 4)) =
        (C.wires (oneEach (1 : Fin 4) (1 : Fin 4))).getD 0 false := by
      simp [Circuit.eval, h0]
    have h3 : (C.wires (oneEach (1 : Fin 4) (1 : Fin 4))).getD 0 false =
        (oneEach (1 : Fin 4) (1 : Fin 4)).getD 0 false :=
      fold_prefix C.gates (oneEach (1 : Fin 4) (1 : Fin 4)) 0 (by decide)
    have h4 : (oneEach (n := 4) (m := 4) 1 1).getD 0 false = false := by decide
    have h5 : targetA 1 1 = true := by decide
    rw [h2, h3, h4] at h1
    rw [h5] at h1
    cases h1
  by_contra hnone
  have hnone : ∀ g ∈ C.gates, 0 ∉ g.inputs := fun g hg hg0 => hnone ⟨g, hg, hg0⟩
  have hlen02 : (oneEach (n := 4) (m := 4) 0 2).length = 8 := by decide
  have heq0 := (fold_eq0 C.gates x0w (oneEach (n := 4) (m := 4) 0 2) (by decide) (by
    intro i hi
    by_cases h8 : i < 8
    · have key : ∀ j : Fin 8, j.val ≠ 0 →
          x0w.getD j.val false = (oneEach (n := 4) (m := 4) 0 2).getD j.val false := by decide
      exact key ⟨i, h8⟩ hi
    · rw [List.getD_eq_default _ _ (by show (8 : ℕ) ≤ i; omega),
        List.getD_eq_default _ _ (by rw [hlen02]; omega)]) hnone).2 C.output hout0
  have hevx0 : C.eval x0w = true := by
    have ht : targetA 0 2 = true := by decide
    have hc : C.eval (oneEach (n := 4) (m := 4) 0 2) = targetA 0 2 := hrep 0 2
    change (C.gates.foldl step x0w).getD C.output false = true
    change (C.gates.foldl step (oneEach (n := 4) (m := 4) 0 2)).getD C.output false = targetA 0 2 at hc
    rw [heq0, hc, ht]
  have hle : ∀ i : ℕ, x0w.getD i false = true →
      (oneEach (n := 4) (m := 4) 1 2).getD i false = true := by
    intro i hi
    by_cases h8 : i < 8
    · have key : ∀ j : Fin 8, x0w.getD j.val false = true →
          (oneEach (n := 4) (m := 4) 1 2).getD j.val false = true := by decide
      exact key ⟨i, h8⟩ hi
    · rw [List.getD_eq_default _ _ (by show (8 : ℕ) ≤ i; omega)] at hi
      cases hi
  have hev12 := fold_mono C.gates x0w (oneEach (n := 4) (m := 4) 1 2) (by decide) hC hle C.output hevx0
  have hrep12 : C.eval (oneEach (n := 4) (m := 4) 1 2) = targetA 1 2 := hrep 1 2
  have hf12 : targetA 1 2 = false := by decide
  change (C.gates.foldl step (oneEach (n := 4) (m := 4) 1 2)).getD C.output false = true at hev12
  change (C.gates.foldl step (oneEach (n := 4) (m := 4) 1 2)).getD C.output false = targetA 1 2 at hrep12
  rw [hev12, hf12] at hrep12
  cases hrep12

def stepC (pool : List ℕ) : List ℕ :=
  63 :: 0 :: (pool ++ pool.flatMap (fun a => pool.flatMap (fun b => [a &&& b, a ||| b])))

def myDedup : List ℕ → List ℕ
  | [] => []
  | a :: l => if l.contains a then myDedup l else a :: myDedup l

theorem mem_myDedup : ∀ (l : List ℕ) (c : ℕ), c ∈ l → c ∈ myDedup l
  | [], c, h => by simp at h
  | a :: l, c, h => by
    unfold myDedup
    rcases List.mem_cons.mp h with rfl | h
    · split
      · rename_i hc; exact mem_myDedup l _ (by simpa using hc)
      · simp
    · split
      · exact mem_myDedup l c h
      · exact List.mem_cons_of_mem _ (mem_myDedup l c h)

def hitP (T : ℕ) (pool : List ℕ) : Bool := pool.any (fun m => m % 64 == T)

def hit2 (T : ℕ) (pool : List ℕ) : Bool :=
  T == 63 || T == 0 || hitP T pool ||
    pool.any (fun a => pool.any (fun b => (a &&& b) % 64 == T || (a ||| b) % 64 == T))

theorem hit2_of (T : ℕ) (pool : List ℕ) (c : ℕ) (hc : c ∈ stepC pool) (h : c % 64 = T) :
    hit2 T pool = true := by
  simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap] at hc
  simp only [hit2, hitP, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
  rcases hc with rfl | rfl | hc | ⟨a, ha, b, hb, hc⟩
  · left; left; left; omega
  · left; left; right; omega
  · left; right; exact ⟨c, hc, h⟩
  · right; refine ⟨a, ha, b, hb, ?_⟩
    simp only [List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · left; exact h
    · right; exact h

def reach (T : ℕ) : List ℕ → ℕ → Bool
  | pool, 0 => hitP T pool
  | pool, 1 => hitP T pool || hit2 T pool
  | pool, k + 2 => hitP T pool || reach T pool (k + 1) ||
      (myDedup (stepC pool)).any (fun c => !pool.contains c && reach T (pool ++ [c]) (k + 1))

theorem reach_of_hit (T : ℕ) (pool : List ℕ) (h : hitP T pool = true) :
    ∀ k, reach T pool k = true
  | 0 => by simp only [reach]; exact h
  | 1 => by simp only [reach, Bool.or_eq_true]; exact Or.inl h
  | k + 2 => by simp only [reach, Bool.or_eq_true]; exact Or.inl (Or.inl h)

def Inv6 (pool : List ℕ) (ws : Fin 6 → List Bool) : Prop :=
  (0 : ℕ) ∈ pool ∧ (∀ p : Fin 6, (ws p).getD 0 false = false) ∧
    ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 6, m.testBit p = (ws p).getD i false

theorem testBit_63 : ∀ p : Fin 6, (63 : ℕ).testBit p = true := by decide

theorem gate_vec_zero (pool : List ℕ) (ws : Fin 6 → List Bool) (h : Inv6 pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (hz : 0 ∈ g.inputs) :
    ∃ c ∈ pool, ∀ p : Fin 6,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen hz ⊢
  obtain ⟨h0p, hzw, hI⟩ := h
  match ins, hlen with
  | [], _ => simp at hz
  | [a], _ =>
    have ha0 : a = 0 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; exact hz.symm
    subst ha0
    refine ⟨0, h0p, fun p => ?_⟩
    rcases hop with rfl | rfl <;>
      simp only [GateOp.eval, List.map_cons, List.map_nil, hzw p, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false, Nat.zero_testBit]
  | [a, b], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hop with rfl | rfl
    · refine ⟨0, h0p, fun p => ?_⟩
      rcases hz with rfl | rfl <;>
        simp only [GateOp.eval, List.map_cons, List.map_nil, hzw p, List.all_cons, List.all_nil,
          id_eq, Bool.false_and, Bool.and_false, Nat.zero_testBit]
    · rcases hz with rfl | rfl
      · obtain ⟨mb, hmb, hb⟩ := hI b
        refine ⟨mb, hmb, fun p => ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, hzw p, hb p, List.any_cons,
          List.any_nil, id_eq, Bool.false_or, Bool.or_false]
      · obtain ⟨ma, hma, ha⟩ := hI a
        refine ⟨ma, hma, fun p => ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, hzw p, ha p, List.any_cons,
          List.any_nil, id_eq, Bool.or_false]
  | _ :: _ :: _ :: _, hl => simp at hl

theorem gate_vec_any (pool : List ℕ) (ws : Fin 6 → List Bool) (h : Inv6 pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
    ∃ c ∈ stepC pool, ∀ p : Fin 6,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  obtain ⟨_, _, hI⟩ := h
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · exact ⟨63, by simp [stepC], fun p => by simp [GateOp.eval, testBit_63 p]⟩
    · exact ⟨0, by simp [stepC], fun p => by simp [GateOp.eval]⟩
  | [a], _ =>
    obtain ⟨ma, hma, ha⟩ := hI a
    refine ⟨ma, by simp [stepC, hma], fun p => ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval, ha p]
  | [a, b], _ =>
    obtain ⟨ma, hma, ha⟩ := hI a
    obtain ⟨mb, hmb, hb⟩ := hI b
    rcases hop with rfl | rfl
    · refine ⟨ma &&& mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, ha p, hb p]
    · refine ⟨ma ||| mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, ha p, hb p]
  | _ :: _ :: _ :: _, hl => simp at hl

theorem out_hit (T : ℕ) (hT : T < 64) (pool : List ℕ) (ws : Fin 6 → List Bool) (o : ℕ)
    (hI : Inv6 pool ws) (hout : ∀ p : Fin 6, (ws p).getD o false = T.testBit p) :
    hitP T pool = true := by
  obtain ⟨m, hm, hmb⟩ := hI.2.2 o
  have hmT : m % 64 = T := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [show (64 : ℕ) = 2 ^ 6 from rfl, Nat.testBit_mod_two_pow]
    by_cases hi : i < 6
    · simp only [hi, decide_true, Bool.true_and]
      exact (hmb ⟨i, hi⟩).trans (hout ⟨i, hi⟩)
    · simp only [hi, decide_false, Bool.false_and]
      symm; apply Nat.testBit_eq_false_of_lt
      calc T < 2 ^ 6 := hT
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
  exact List.any_eq_true.mpr ⟨m, hm, by simp [hmT]⟩

theorem inv6_step (pool pool' : List ℕ) (ws : Fin 6 → List Bool) (L : ℕ) (hLpos : 0 < L)
    (hL : ∀ p, (ws p).length = L) (hI : Inv6 pool ws) (b : Fin 6 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 6, c.testBit p = b p) (hsub : ∀ m ∈ pool, m ∈ pool') (hcp : c ∈ pool') :
    Inv6 pool' (fun p => ws p ++ [b p]) := by
  refine ⟨hsub 0 hI.1, fun p => ?_, fun i => ?_⟩
  · rw [getD_snoc]
    simp only [show (0 : ℕ) ≠ (ws p).length by rw [hL p]; omega, ↓reduceIte]
    exact hI.2.1 p
  · obtain ⟨m, hm, hmb⟩ := hI.2.2 i
    by_cases hi : i = L
    · subst hi
      exact ⟨c, hcp, fun p => by
        rw [getD_snoc]; simp only [show i = (ws p).length from (hL p).symm, ↓reduceIte, hcv p]⟩
    · exact ⟨m, hsub m hm, fun p => by
        rw [getD_snoc]; simp only [show i ≠ (ws p).length by rw [hL p]; exact hi, ↓reduceIte, hmb p]⟩

def nonZeroCount : List Gate → ℕ
  | [] => 0
  | g :: gs => (if 0 ∈ g.inputs then 0 else 1) + nonZeroCount gs

theorem nonZeroCount_le : ∀ (gs : List Gate), (∃ g ∈ gs, 0 ∈ g.inputs) → nonZeroCount gs + 1 ≤ gs.length
  | [], h => by obtain ⟨g, hg, _⟩ := h; simp at hg
  | g :: gs, h => by
    by_cases h0 : 0 ∈ g.inputs
    · have hle : ∀ l : List Gate, nonZeroCount l ≤ l.length := by
        intro l
        induction l with
        | nil => simp [nonZeroCount]
        | cons x xs ih =>
          unfold nonZeroCount
          split_ifs <;> simp <;> omega
      have := hle gs
      simp [nonZeroCount, h0]
      omega
    · obtain ⟨g', hg', h0'⟩ := h
      simp only [List.mem_cons] at hg'
      rcases hg' with rfl | hg'
      · exact absurd h0' h0
      · have ih := nonZeroCount_le gs ⟨g', hg', h0'⟩
        simp [nonZeroCount, h0]
        omega

theorem inv6_zero_fold (T : ℕ) : ∀ (gs : List Gate) (pool : List ℕ)
    (ws : Fin 6 → List Bool) (L : ℕ),
    0 < L →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    nonZeroCount gs = 0 →
    (∀ p, (ws p).length = L) →
    Inv6 pool ws →
    Inv6 pool (fun p => gs.foldl step (ws p))
  | [], pool, ws, L, _, _, _, _, hI => hI
  | g :: gs, pool, ws, L, hLp, hg, hnz, hL, hI => by
    have hz : 0 ∈ g.inputs := by
      unfold nonZeroCount at hnz
      by_contra h0
      simp [h0] at hnz
    have hnz' : nonZeroCount gs = 0 := by
      simp [nonZeroCount, hz] at hnz
      exact hnz
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec_zero pool ws hI g hop hlen hz
    exact inv6_zero_fold T gs pool (fun p => step (ws p) g) (L + 1) (by omega)
      (fun g' hg' => hg g' (by simp [hg'])) hnz' (fun p => by simp [step_len, hL p])
      (inv6_step pool pool ws L hLp hL hI _ c hcv (fun m hm => hm) hc)

theorem main (T : ℕ) (hT : T < 64) : ∀ (gs : List Gate) (pool : List ℕ)
    (ws : Fin 6 → List Bool) (L k o : ℕ),
    0 < L →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    nonZeroCount gs ≤ k → (∀ p, (ws p).length = L) → Inv6 pool ws →
    (∀ p : Fin 6, (gs.foldl step (ws p)).getD o false = T.testBit p) →
    reach T pool k = true
  | [], pool, ws, L, k, o, _, _, _, _, hI, hout =>
    reach_of_hit T pool (out_hit T hT pool ws o hI (fun p => hout p)) k
  | g :: gs, pool, ws, L, k, o, hLp, hg, hk, hL, hI, hout => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    have hout' : ∀ p : Fin 6, (gs.foldl step (step (ws p) g)).getD o false = T.testBit p :=
      fun p => by have h3 := hout p; rw [List.foldl_cons] at h3; exact h3
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (by simp [hg'])
    have hL' : ∀ p, (step (ws p) g).length = L + 1 :=
      fun p => by simp [step_len, hL p]
    by_cases hz : 0 ∈ g.inputs
    · have hk' : nonZeroCount gs ≤ k := by simp [nonZeroCount, hz] at hk; exact hk
      obtain ⟨c, hc, hcv⟩ := gate_vec_zero pool ws hI g hop hlen hz
      exact main T hT gs pool (fun p => step (ws p) g) (L + 1) k o (by omega) hg' hk' hL'
        (inv6_step pool pool ws L hLp hL hI _ c hcv (fun m hm => hm) hc) hout'
    · obtain ⟨c, hc, hcv⟩ := gate_vec_any pool ws hI g hop hlen
      have hkl : nonZeroCount gs + 1 ≤ k := by simp [nonZeroCount, hz] at hk; omega
      match k, hkl with
      | 0, hkl => omega
      | 1, hkl =>
        have hnz : nonZeroCount gs = 0 := by omega
        have hIf := inv6_zero_fold T gs (pool ++ [c]) (fun p => step (ws p) g) (L + 1) (by omega)
          hg' hnz hL' (inv6_step pool (pool ++ [c]) ws L hLp hL hI _ c hcv (fun m hm => by simp [hm]) (by simp))
        have hh := out_hit T hT (pool ++ [c]) _ o hIf hout'
        rw [hitP, List.any_append, Bool.or_eq_true] at hh
        simp only [reach, Bool.or_eq_true]
        rcases hh with hh | hh
        · exact Or.inl hh
        · simp at hh
          exact Or.inr (hit2_of T pool c hc hh)
      | k + 2, hkl =>
        by_cases hcin : c ∈ pool
        · have IH := main T hT gs pool (fun p => step (ws p) g) (L + 1) (k + 1) o (by omega) hg'
            (by omega) hL' (inv6_step pool pool ws L hLp hL hI _ c hcv (fun m hm => hm) hcin) hout'
          simp only [reach, Bool.or_eq_true]
          exact Or.inl (Or.inr IH)
        · have IH := main T hT gs (pool ++ [c]) (fun p => step (ws p) g) (L + 1) (k + 1) o (by omega) hg'
            (by omega) hL' (inv6_step pool (pool ++ [c]) ws L hLp hL hI _ c hcv (fun m hm => by simp [hm]) (by simp)) hout'
          simp only [reach, Bool.or_eq_true, List.any_eq_true]
          refine Or.inr ⟨c, mem_myDedup _ c hc, ?_⟩
          simp [hcin, IH]

def pool0 : List ℕ := [3, 12, 48, 21, 42, 0]

def X6 (p : Fin 6) : List Bool :=
  oneEach (⟨p.val / 2 + 1, by omega⟩ : Fin 4) (⟨p.val % 2, by omega⟩ : Fin 4)

theorem X6_len (p : Fin 6) : (X6 p).length = 8 := by simp [X6, oneEach]

theorem inv0 : Inv6 pool0 X6 := by
  refine ⟨by decide, by decide, fun i => ?_⟩
  by_cases hi : i < 8
  · have key : ∀ j : Fin 8, ∀ p : Fin 6, (([0, 3, 12, 48, 21, 42, 0, 0] : List ℕ).getD j 0).testBit p =
        (X6 p).getD j false := by decide
    have hmem : ∀ j : Fin 8, ([0, 3, 12, 48, 21, 42, 0, 0] : List ℕ).getD j 0 ∈ pool0 := by decide
    exact ⟨([0, 3, 12, 48, 21, 42, 0, 0] : List ℕ).getD i 0, hmem ⟨i, hi⟩, fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by decide, fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X6_len]; omega)]

theorem targetA_X6 : ∀ q : Fin 6,
    targetA ⟨q.val / 2 + 1, by omega⟩ ⟨q.val % 2, by omega⟩ = (22 : ℕ).testBit q := by
  decide

theorem low_reach : reach 22 pool0 3 = false := by decide +kernel

theorem lower : ¬ RepSizeAtMost targetA 4 := by
  rintro ⟨C, hC, hs, hrep⟩
  have hgz := exists_gate_zero C hC hrep
  have hnz : nonZeroCount C.gates ≤ 3 := by
    have := nonZeroCount_le C.gates hgz
    have hlen : C.gates.length ≤ 4 := hs
    omega
  have hr := main 22 (by decide) C.gates pool0 X6 8 3 C.output (by omega) hC hnz X6_len inv0 (fun p => by
    have h := hrep ⟨p.val / 2 + 1, by omega⟩ ⟨p.val % 2, by omega⟩
    exact h.trans (targetA_X6 p))
  rw [low_reach] at hr
  exact absurd hr (by simp)

end PEqualNP.Outside.L_meta_5553_aux

theorem PEqualNP.Outside.L_meta_5553 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4399 : ℕ).testBit (4 * u.val + v.val)) 5 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4399 : ℕ).testBit (4 * u.val + v.val)) 4 :=
  ⟨PEqualNP.Outside.L_meta_5553_aux.upper, PEqualNP.Outside.L_meta_5553_aux.lower⟩
