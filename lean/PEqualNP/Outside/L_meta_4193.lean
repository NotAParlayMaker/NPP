import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4193

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) x).getD i false) := by
  have hsplit : run gs x = run (gs.drop (j + 1)) (step (run (gs.take j) x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [run_append, run_cons]
  have hl : (run (gs.take j) x).length = x.length + j := by
    rw [run_length, List.length_take]; omega
  rw [hsplit, run_getD _ _ _ (by rw [step_length]; omega), ← hl, step_getD_last]

lemma run_gate_lt (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hins : ∀ i ∈ gs[j].inputs, i < w.length + j) :
    (run gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs w).getD i false) := by
  rw [run_gate gs w j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt := hins i hi
  have hsplit : run gs w = run (gs.drop j) (run (gs.take j) w) := by
    rw [← run_append, List.take_append_drop]
  have h1 : (run (gs.drop j) (run (gs.take j) w)).getD i false = (run (gs.take j) w).getD i false :=
    run_getD (gs.drop j) (run (gs.take j) w) i (by rw [run_length, List.length_take]; omega)
  rw [hsplit, h1]

lemma run_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {x y : List Bool} (hlen : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil =>
    intro i hi
    exact hxy i hi
  | cons g gs ih =>
    have hg := hgs g List.mem_cons_self
    have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    apply ih hgs' (by simp [step_length, hlen])
    intro i hi
    by_cases hilt : i < x.length
    · rw [step_getD _ _ _ hilt] at hi
      rw [step_getD _ _ _ (by omega)]
      exact hxy i hi
    · have hieq : i = x.length ∨ x.length < i := by omega
      rcases hieq with rfl | hgt
      · rw [step_getD_last] at hi
        rw [hlen, step_getD_last]
        rcases hg.1 with hop | hop
        · rw [hop] at hi ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
          intro b hb
          rcases hb with ⟨a, ha, rfl⟩
          exact hxy a (hi (x.getD a false) ⟨a, ha, rfl⟩)
        · rw [hop] at hi ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
          rcases hi with ⟨_, ⟨a, ha, rfl⟩, ha_true⟩
          exact ⟨y.getD a false, ⟨a, ha, rfl⟩, hxy a ha_true⟩
      · have h1 : ¬ i < (step x g).length := by rw [step_length]; omega
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h1)] at hi
        cases hi

def semInit (n : ℕ) (x10 x11 : Fin n → Bool) : List (Bool × Bool × Bool × Bool) :=
  (List.finRange n).map fun i => (false, x10 i, x11 i, false)

lemma semInit_length (n : ℕ) (x10 x11 : Fin n → Bool) :
    (semInit n x10 x11).length = n := by
  simp [semInit]

def orQuad (a b : Bool × Bool × Bool × Bool) : Bool × Bool × Bool × Bool :=
  (a.1 || b.1, a.2.1 || b.2.1, a.2.2.1 || b.2.2.1, a.2.2.2 || b.2.2.2)

def andQuad (a b : Bool × Bool × Bool × Bool) : Bool × Bool × Bool × Bool :=
  (a.1 && b.1,
    (a.1 && b.2.1) || (a.2.1 && b.1),
    (a.1 && b.2.2.1) || (a.2.2.1 && b.1),
    ((a.1 && b.2.2.2) || (a.2.2.2 && b.1)) || ((a.2.1 && b.2.2.1) || (a.2.2.1 && b.2.1)))

def evalQuad (s : List (Bool × Bool × Bool × Bool)) (g : Gate) : Bool × Bool × Bool × Bool :=
  match g.op, g.inputs with
  | GateOp.or, [] => (false, false, false, false)
  | GateOp.or, [a] => s.getD a (false, false, false, false)
  | GateOp.or, [a, b] => orQuad (s.getD a (false, false, false, false)) (s.getD b (false, false, false, false))
  | GateOp.and, [] => (true, false, false, false)
  | GateOp.and, [a] => s.getD a (false, false, false, false)
  | GateOp.and, [a, b] => andQuad (s.getD a (false, false, false, false)) (s.getD b (false, false, false, false))
  | _, _ => (false, false, false, false)

def semStep (s : List (Bool × Bool × Bool × Bool)) (g : Gate) : List (Bool × Bool × Bool × Bool) :=
  s ++ [evalQuad s g]

def semRun (n : ℕ) (gs : List Gate) (x10 x11 : Fin n → Bool) : List (Bool × Bool × Bool × Bool) :=
  gs.foldl semStep (semInit n x10 x11)

lemma semRun_nil (n : ℕ) (x10 x11 : Fin n → Bool) :
    semRun n [] x10 x11 = semInit n x10 x11 := rfl

lemma semRun_append (n : ℕ) (l1 l2 : List Gate) (x10 x11 : Fin n → Bool) :
    semRun n (l1 ++ l2) x10 x11 = l2.foldl semStep (semRun n l1 x10 x11) := by
  simp [semRun, List.foldl_append]

lemma semStep_length (s : List (Bool × Bool × Bool × Bool)) (g : Gate) :
    (semStep s g).length = s.length + 1 := by
  simp [semStep]

lemma semRun_length (n : ℕ) (gs : List Gate) (x10 x11 : Fin n → Bool) :
    (semRun n gs x10 x11).length = n + gs.length := by
  have h : ∀ (l : List Gate) (s : List (Bool × Bool × Bool × Bool)),
      (l.foldl semStep s).length = s.length + l.length := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons g l ih => intro s; simp [List.foldl_cons, ih, semStep_length]; omega
  rw [semRun, h, semInit_length]

lemma semStep_getD (s : List (Bool × Bool × Bool × Bool)) (g : Gate) (i : ℕ) (hi : i < s.length) :
    (semStep s g).getD i (false, false, false, false) = s.getD i (false, false, false, false) := by
  simp only [semStep]
  exact List.getD_append _ _ _ _ hi

lemma semStep_getD_last (s : List (Bool × Bool × Bool × Bool)) (g : Gate) :
    (semStep s g).getD s.length (false, false, false, false) = evalQuad s g := by
  simp only [semStep]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma semFold_getD (l : List Gate) (s : List (Bool × Bool × Bool × Bool)) (i : ℕ) (hi : i < s.length) :
    (l.foldl semStep s).getD i (false, false, false, false) = s.getD i (false, false, false, false) := by
  induction l generalizing s with
  | nil => rfl
  | cons g l ih =>
    rw [List.foldl_cons, ih _ (by rw [semStep_length]; omega), semStep_getD _ _ _ hi]

lemma semRun_snoc_getD_lt (n : ℕ) (gs : List Gate) (g : Gate) (x10 x11 : Fin n → Bool)
    (i : ℕ) (hi : i < n + gs.length) :
    (semRun n (gs ++ [g]) x10 x11).getD i (false, false, false, false) =
      (semRun n gs x10 x11).getD i (false, false, false, false) := by
  rw [semRun_append, List.foldl_cons, List.foldl_nil, semStep_getD]
  rw [semRun_length]
  exact hi

lemma semRun_snoc_getD_last (n : ℕ) (gs : List Gate) (g : Gate) (x10 x11 : Fin n → Bool) :
    (semRun n (gs ++ [g]) x10 x11).getD (n + gs.length) (false, false, false, false) =
      evalQuad (semRun n gs x10 x11) g := by
  rw [semRun_append, List.foldl_cons, List.foldl_nil]
  have hl : (semRun n gs x10 x11).length = n + gs.length := semRun_length n gs x10 x11
  rw [← hl, semStep_getD_last]

def ref (n k w : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if w < n then (2 * n, w, n + w, 2 * n)
  else if w < n + k then
    let b := 2 * n + 2 + 14 * (w - n)
    (b + 10, b + 11, b + 12, b + 13)
  else (2 * n, 2 * n, 2 * n, 2 * n)

lemma ref_lt (n k u wlen : ℕ) (hw : wlen = 2 * n + 2 + 14 * k) :
    (ref n k u).1 < wlen ∧ (ref n k u).2.1 < wlen ∧
    (ref n k u).2.2.1 < wlen ∧ (ref n k u).2.2.2 < wlen := by
  by_cases h1 : u < n <;> by_cases h2 : u < n + k <;> simp [ref, h1, h2, hw] <;> omega

lemma ref_mono (n k u : ℕ) (hu : u < n + k) :
    ref n (k + 1) u = ref n k u := by
  have hu2 : u < n + (k + 1) := by omega
  by_cases h1 : u < n <;> simp [ref, h1, hu, hu2]

def dummyGates : ℕ → List Gate
  | 0 => []
  | m + 1 => ⟨GateOp.or, []⟩ :: dummyGates m

lemma dummyGates_length (m : ℕ) : (dummyGates m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [dummyGates, ih]

lemma dummyGates_mono (m : ℕ) :
    ∀ g ∈ dummyGates m, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction m with
  | zero => intro g hg; cases hg
  | succ m ih =>
    intro g hg
    simp only [dummyGates, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨Or.inr rfl, by simp⟩
    · exact ih g hg

lemma run_dummyGates_getD (m : ℕ) (w : List Bool) (j : ℕ) (hj : j < m) :
    (run (dummyGates m) w).getD (w.length + j) false = false := by
  induction m generalizing w j with
  | zero => cases hj
  | succ m ih =>
    rw [dummyGates, run_cons]
    cases j with
    | zero =>
      rw [Nat.add_zero, run_getD _ _ _ (by rw [step_length]; omega), step_getD_last]
      rfl
    | succ j' =>
      have heq : w.length + (j' + 1) = (step w ⟨GateOp.or, []⟩).length + j' := by
        rw [step_length]; omega
      rw [heq]
      exact ih (step w ⟨GateOp.or, []⟩) j' (by omega)

def compileBlock (n k : ℕ) (g : Gate) : List Gate :=
  let b := 2 * n + 2 + 14 * k
  match g.op, g.inputs with
  | GateOp.or, [] => dummyGates 14
  | GateOp.or, [x] =>
    let p := ref n k x
    dummyGates 10 ++ [⟨GateOp.or, [p.1]⟩, ⟨GateOp.or, [p.2.1]⟩, ⟨GateOp.or, [p.2.2.1]⟩, ⟨GateOp.or, [p.2.2.2]⟩]
  | GateOp.or, [x, y] =>
    let p := ref n k x
    let q := ref n k y
    dummyGates 10 ++ [⟨GateOp.or, [p.1, q.1]⟩, ⟨GateOp.or, [p.2.1, q.2.1]⟩, ⟨GateOp.or, [p.2.2.1, q.2.2.1]⟩, ⟨GateOp.or, [p.2.2.2, q.2.2.2]⟩]
  | GateOp.and, [] =>
    dummyGates 10 ++ [⟨GateOp.and, []⟩, ⟨GateOp.or, []⟩, ⟨GateOp.or, []⟩, ⟨GateOp.or, []⟩]
  | GateOp.and, [x] =>
    let p := ref n k x
    dummyGates 10 ++ [⟨GateOp.or, [p.1]⟩, ⟨GateOp.or, [p.2.1]⟩, ⟨GateOp.or, [p.2.2.1]⟩, ⟨GateOp.or, [p.2.2.2]⟩]
  | GateOp.and, [x, y] =>
    let p := ref n k x
    let q := ref n k y
    [ ⟨GateOp.and, [p.1, q.2.1]⟩,
      ⟨GateOp.and, [p.2.1, q.1]⟩,
      ⟨GateOp.and, [p.1, q.2.2.1]⟩,
      ⟨GateOp.and, [p.2.2.1, q.1]⟩,
      ⟨GateOp.and, [p.1, q.2.2.2]⟩,
      ⟨GateOp.and, [p.2.2.2, q.1]⟩,
      ⟨GateOp.and, [p.2.1, q.2.2.1]⟩,
      ⟨GateOp.and, [p.2.2.1, q.2.1]⟩,
      ⟨GateOp.or, [b + 4, b + 5]⟩,
      ⟨GateOp.or, [b + 6, b + 7]⟩,
      ⟨GateOp.and, [p.1, q.1]⟩,
      ⟨GateOp.or, [b + 0, b + 1]⟩,
      ⟨GateOp.or, [b + 2, b + 3]⟩,
      ⟨GateOp.or, [b + 8, b + 9]⟩ ]
  | _, _ => dummyGates 14

lemma compileBlock_length (n k : ℕ) (g : Gate) : (compileBlock n k g).length = 14 := by
  unfold compileBlock
  rcases g with ⟨op, ins⟩
  cases op <;> (cases ins with
    | nil => simp [dummyGates_length]
    | cons a l => cases l with
      | nil => simp [dummyGates_length]
      | cons b l2 => cases l2 <;> simp [dummyGates_length])

lemma compileBlock_mono (n k : ℕ) (g : Gate) :
    ∀ h ∈ compileBlock n k g, h.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ h.inputs.length ≤ 2 := by
  unfold compileBlock
  rcases g with ⟨op, ins⟩
  cases op
  · cases ins with
    | nil =>
      intro h hh
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hh
      rcases hh with hh | rfl | rfl | rfl | rfl
      · exact dummyGates_mono 10 h hh
      · exact ⟨Or.inl rfl, by simp⟩
      · exact ⟨Or.inr rfl, by simp⟩
      · exact ⟨Or.inr rfl, by simp⟩
      · exact ⟨Or.inr rfl, by simp⟩
    | cons a l => cases l with
      | nil =>
        intro h hh
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hh
        rcases hh with hh | rfl | rfl | rfl | rfl
        · exact dummyGates_mono 10 h hh
        · exact ⟨Or.inr rfl, by simp⟩
        · exact ⟨Or.inr rfl, by simp⟩
        · exact ⟨Or.inr rfl, by simp⟩
        · exact ⟨Or.inr rfl, by simp⟩
      | cons b l2 => cases l2 with
        | nil =>
          intro h hh
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hh
          rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨Or.inl rfl, by simp⟩
          · exact ⟨Or.inl rfl, by simp⟩
          · exact ⟨Or.inl rfl, by simp⟩
          · exact ⟨Or.inl rfl, by simp⟩
          · exact ⟨Or.inl rfl, by simp⟩
          · exact ⟨Or.inl rfl, by simp⟩
          · exact ⟨Or.inl rfl, by simp⟩
          · exact ⟨Or.inl rfl, by simp⟩
          · exact ⟨Or.inr rfl, by simp⟩
          · exact ⟨Or.inr rfl, by simp⟩
          · exact ⟨Or.inl rfl, by simp⟩
          · exact ⟨Or.inr rfl, by simp⟩
          · exact ⟨Or.inr rfl, by simp⟩
          · exact ⟨Or.inr rfl, by simp⟩
        | cons c l3 => exact dummyGates_mono 14
  · cases ins with
    | nil => exact dummyGates_mono 14
    | cons a l => cases l with
      | nil =>
        intro h hh
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hh
        rcases hh with hh | rfl | rfl | rfl | rfl
        · exact dummyGates_mono 10 h hh
        · exact ⟨Or.inr rfl, by simp⟩
        · exact ⟨Or.inr rfl, by simp⟩
        · exact ⟨Or.inr rfl, by simp⟩
        · exact ⟨Or.inr rfl, by simp⟩
      | cons b l2 => cases l2 with
        | nil =>
          intro h hh
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hh
          rcases hh with hh | rfl | rfl | rfl | rfl
          · exact dummyGates_mono 10 h hh
          · exact ⟨Or.inr rfl, by simp⟩
          · exact ⟨Or.inr rfl, by simp⟩
          · exact ⟨Or.inr rfl, by simp⟩
          · exact ⟨Or.inr rfl, by simp⟩
        | cons c l3 => exact dummyGates_mono 14
  · exact dummyGates_mono 14
  · exact dummyGates_mono 14
  · exact dummyGates_mono 14

def compilePrefix (n k : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => compileBlock n k g ++ compilePrefix n (k + 1) gs

lemma compilePrefix_length (n k : ℕ) (gs : List Gate) :
    (compilePrefix n k gs).length = 14 * gs.length := by
  induction gs generalizing k with
  | nil => simp [compilePrefix]
  | cons g gs ih =>
    simp [compilePrefix, compileBlock_length, ih]
    omega

lemma compilePrefix_mono (n k : ℕ) (gs : List Gate) :
    ∀ h ∈ compilePrefix n k gs, h.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ h.inputs.length ≤ 2 := by
  induction gs generalizing k with
  | nil => intro h hh; cases hh
  | cons g gs ih =>
    intro h hh
    simp only [compilePrefix, List.mem_append] at hh
    rcases hh with hh | hh
    · exact compileBlock_mono n k g h hh
    · exact ih (k + 1) h hh

lemma compilePrefix_append (n k : ℕ) (l1 l2 : List Gate) :
    compilePrefix n k (l1 ++ l2) = compilePrefix n k l1 ++ compilePrefix n (k + l1.length) l2 := by
  induction l1 generalizing k with
  | nil => simp [compilePrefix]
  | cons g l1 ih =>
    have heq : k + 1 + l1.length = k + (l1.length + 1) := by omega
    simp [compilePrefix, ih, List.append_assoc, heq]

def compileCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨[⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ compilePrefix n 0 C.gates, (ref n C.gates.length C.output).2.2.2⟩

lemma compileCircuit_mono (n : ℕ) (C : Circuit) : Monotone2 (compileCircuit n C) := by
  intro g hg
  simp only [compileCircuit, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with (rfl | rfl) | hg
  · exact ⟨Or.inr rfl, by simp⟩
  · exact ⟨Or.inl rfl, by simp⟩
  · exact compilePrefix_mono n 0 C.gates g hg

lemma compileCircuit_size (n : ℕ) (C : Circuit) : (compileCircuit n C).size = 2 + 14 * C.size := by
  simp [Circuit.size, compileCircuit, compilePrefix_length]
  omega

lemma run_copy4_getD (w : List Bool) (p : ℕ × ℕ × ℕ × ℕ) (hp : p.1 < w.length ∧ p.2.1 < w.length ∧ p.2.2.1 < w.length ∧ p.2.2.2 < w.length) :
    let gs := dummyGates 10 ++ [⟨GateOp.or, [p.1]⟩, ⟨GateOp.or, [p.2.1]⟩, ⟨GateOp.or, [p.2.2.1]⟩, ⟨GateOp.or, [p.2.2.2]⟩]
    let w' := run gs w
    (w'.getD (w.length + 10) false, w'.getD (w.length + 11) false,
     w'.getD (w.length + 12) false, w'.getD (w.length + 13) false) =
      (w.getD p.1 false, w.getD p.2.1 false, w.getD p.2.2.1 false, w.getD p.2.2.2 false) := by
  rcases hp with ⟨h1, h2, h3, h4⟩
  dsimp only
  set gs := dummyGates 10 ++ [⟨GateOp.or, [p.1]⟩, ⟨GateOp.or, [p.2.1]⟩, ⟨GateOp.or, [p.2.2.1]⟩, ⟨GateOp.or, [p.2.2.2]⟩]
  have hlen : gs.length = 14 := by simp [gs, dummyGates_length]
  have h0 : (run gs w).getD p.1 false = w.getD p.1 false := run_getD gs w p.1 h1
  have h0b : (run gs w).getD p.2.1 false = w.getD p.2.1 false := run_getD gs w p.2.1 h2
  have h0c : (run gs w).getD p.2.2.1 false = w.getD p.2.2.1 false := run_getD gs w p.2.2.1 h3
  have h0d : (run gs w).getD p.2.2.2 false = w.getD p.2.2.2 false := run_getD gs w p.2.2.2 h4
  have hg10 : gs[10] = ⟨GateOp.or, [p.1]⟩ := by
    simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length])]; simp [dummyGates_length]
  have hg11 : gs[11] = ⟨GateOp.or, [p.2.1]⟩ := by
    simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length]; omega)]; simp [dummyGates_length]
  have hg12 : gs[12] = ⟨GateOp.or, [p.2.2.1]⟩ := by
    simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length]; omega)]; simp [dummyGates_length]
  have hg13 : gs[13] = ⟨GateOp.or, [p.2.2.2]⟩ := by
    simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length]; omega)]; simp [dummyGates_length]
  have v10 : (run gs w).getD (w.length + 10) false = w.getD p.1 false := by
    rw [run_gate_lt gs w 10 (by omega) (by rw [hg10]; intro i hi; simp at hi; subst hi; omega)]
    rw [hg10]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    exact h0
  have v11 : (run gs w).getD (w.length + 11) false = w.getD p.2.1 false := by
    rw [run_gate_lt gs w 11 (by omega) (by rw [hg11]; intro i hi; simp at hi; subst hi; omega)]
    rw [hg11]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    exact h0b
  have v12 : (run gs w).getD (w.length + 12) false = w.getD p.2.2.1 false := by
    rw [run_gate_lt gs w 12 (by omega) (by rw [hg12]; intro i hi; simp at hi; subst hi; omega)]
    rw [hg12]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    exact h0c
  have v13 : (run gs w).getD (w.length + 13) false = w.getD p.2.2.2 false := by
    rw [run_gate_lt gs w 13 (by omega) (by rw [hg13]; intro i hi; simp at hi; subst hi; omega)]
    rw [hg13]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    exact h0d
  rw [v10, v11, v12, v13]

lemma run_or4_getD (w : List Bool) (p q : ℕ × ℕ × ℕ × ℕ)
    (hp : p.1 < w.length ∧ p.2.1 < w.length ∧ p.2.2.1 < w.length ∧ p.2.2.2 < w.length)
    (hq : q.1 < w.length ∧ q.2.1 < w.length ∧ q.2.2.1 < w.length ∧ q.2.2.2 < w.length) :
    let gs := dummyGates 10 ++ [⟨GateOp.or, [p.1, q.1]⟩, ⟨GateOp.or, [p.2.1, q.2.1]⟩, ⟨GateOp.or, [p.2.2.1, q.2.2.1]⟩, ⟨GateOp.or, [p.2.2.2, q.2.2.2]⟩]
    let w' := run gs w
    (w'.getD (w.length + 10) false, w'.getD (w.length + 11) false,
     w'.getD (w.length + 12) false, w'.getD (w.length + 13) false) =
      orQuad (w.getD p.1 false, w.getD p.2.1 false, w.getD p.2.2.1 false, w.getD p.2.2.2 false)
        (w.getD q.1 false, w.getD q.2.1 false, w.getD q.2.2.1 false, w.getD q.2.2.2 false) := by
  rcases hp with ⟨hp1, hp2, hp3, hp4⟩
  rcases hq with ⟨hq1, hq2, hq3, hq4⟩
  dsimp only
  set gs := dummyGates 10 ++ [⟨GateOp.or, [p.1, q.1]⟩, ⟨GateOp.or, [p.2.1, q.2.1]⟩, ⟨GateOp.or, [p.2.2.1, q.2.2.1]⟩, ⟨GateOp.or, [p.2.2.2, q.2.2.2]⟩]
  have hlen : gs.length = 14 := by simp [gs, dummyGates_length]
  have hg10 : gs[10] = ⟨GateOp.or, [p.1, q.1]⟩ := by
    simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length])]; simp [dummyGates_length]
  have hg11 : gs[11] = ⟨GateOp.or, [p.2.1, q.2.1]⟩ := by
    simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length]; omega)]; simp [dummyGates_length]
  have hg12 : gs[12] = ⟨GateOp.or, [p.2.2.1, q.2.2.1]⟩ := by
    simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length]; omega)]; simp [dummyGates_length]
  have hg13 : gs[13] = ⟨GateOp.or, [p.2.2.2, q.2.2.2]⟩ := by
    simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length]; omega)]; simp [dummyGates_length]
  have v10 : (run gs w).getD (w.length + 10) false = (w.getD p.1 false || w.getD q.1 false) := by
    rw [run_gate_lt gs w 10 (by omega) (by rw [hg10]; intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)]
    rw [hg10]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [run_getD gs w p.1 hp1, run_getD gs w q.1 hq1]
  have v11 : (run gs w).getD (w.length + 11) false = (w.getD p.2.1 false || w.getD q.2.1 false) := by
    rw [run_gate_lt gs w 11 (by omega) (by rw [hg11]; intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)]
    rw [hg11]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [run_getD gs w p.2.1 hp2, run_getD gs w q.2.1 hq2]
  have v12 : (run gs w).getD (w.length + 12) false = (w.getD p.2.2.1 false || w.getD q.2.2.1 false) := by
    rw [run_gate_lt gs w 12 (by omega) (by rw [hg12]; intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)]
    rw [hg12]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [run_getD gs w p.2.2.1 hp3, run_getD gs w q.2.2.1 hq3]
  have v13 : (run gs w).getD (w.length + 13) false = (w.getD p.2.2.2 false || w.getD q.2.2.2 false) := by
    rw [run_gate_lt gs w 13 (by omega) (by rw [hg13]; intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)]
    rw [hg13]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [run_getD gs w p.2.2.2 hp4, run_getD gs w q.2.2.2 hq4]
  rw [v10, v11, v12, v13]
  rfl

lemma run_and2_getD (w : List Bool) (b : ℕ) (hb : b = w.length) (p q : ℕ × ℕ × ℕ × ℕ)
    (hp : p.1 < w.length ∧ p.2.1 < w.length ∧ p.2.2.1 < w.length ∧ p.2.2.2 < w.length)
    (hq : q.1 < w.length ∧ q.2.1 < w.length ∧ q.2.2.1 < w.length ∧ q.2.2.2 < w.length) :
    let gs : List Gate :=
      [ ⟨GateOp.and, [p.1, q.2.1]⟩,
        ⟨GateOp.and, [p.2.1, q.1]⟩,
        ⟨GateOp.and, [p.1, q.2.2.1]⟩,
        ⟨GateOp.and, [p.2.2.1, q.1]⟩,
        ⟨GateOp.and, [p.1, q.2.2.2]⟩,
        ⟨GateOp.and, [p.2.2.2, q.1]⟩,
        ⟨GateOp.and, [p.2.1, q.2.2.1]⟩,
        ⟨GateOp.and, [p.2.2.1, q.2.1]⟩,
        ⟨GateOp.or, [b + 4, b + 5]⟩,
        ⟨GateOp.or, [b + 6, b + 7]⟩,
        ⟨GateOp.and, [p.1, q.1]⟩,
        ⟨GateOp.or, [b + 0, b + 1]⟩,
        ⟨GateOp.or, [b + 2, b + 3]⟩,
        ⟨GateOp.or, [b + 8, b + 9]⟩ ]
    let w' := run gs w
    (w'.getD (b + 10) false, w'.getD (b + 11) false,
     w'.getD (b + 12) false, w'.getD (b + 13) false) =
      andQuad (w.getD p.1 false, w.getD p.2.1 false, w.getD p.2.2.1 false, w.getD p.2.2.2 false)
        (w.getD q.1 false, w.getD q.2.1 false, w.getD q.2.2.1 false, w.getD q.2.2.2 false) := by
  rcases hp with ⟨hp1, hp2, hp3, hp4⟩
  rcases hq with ⟨hq1, hq2, hq3, hq4⟩
  subst hb
  dsimp only
  set gs : List Gate :=
    [ ⟨GateOp.and, [p.1, q.2.1]⟩,
      ⟨GateOp.and, [p.2.1, q.1]⟩,
      ⟨GateOp.and, [p.1, q.2.2.1]⟩,
      ⟨GateOp.and, [p.2.2.1, q.1]⟩,
      ⟨GateOp.and, [p.1, q.2.2.2]⟩,
      ⟨GateOp.and, [p.2.2.2, q.1]⟩,
      ⟨GateOp.and, [p.2.1, q.2.2.1]⟩,
      ⟨GateOp.and, [p.2.2.1, q.2.1]⟩,
      ⟨GateOp.or, [w.length + 4, w.length + 5]⟩,
      ⟨GateOp.or, [w.length + 6, w.length + 7]⟩,
      ⟨GateOp.and, [p.1, q.1]⟩,
      ⟨GateOp.or, [w.length + 0, w.length + 1]⟩,
      ⟨GateOp.or, [w.length + 2, w.length + 3]⟩,
      ⟨GateOp.or, [w.length + 8, w.length + 9]⟩ ]
  have hlen : gs.length = 14 := rfl
  have v0 : (run gs w).getD (w.length + 0) false = (w.getD p.1 false && w.getD q.2.1 false) := by
    rw [run_gate_lt gs w 0 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
    rw [run_getD gs w p.1 hp1, run_getD gs w q.2.1 hq2]
  have v1 : (run gs w).getD (w.length + 1) false = (w.getD p.2.1 false && w.getD q.1 false) := by
    rw [run_gate_lt gs w 1 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
    rw [run_getD gs w p.2.1 hp2, run_getD gs w q.1 hq1]
  have v2 : (run gs w).getD (w.length + 2) false = (w.getD p.1 false && w.getD q.2.2.1 false) := by
    rw [run_gate_lt gs w 2 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
    rw [run_getD gs w p.1 hp1, run_getD gs w q.2.2.1 hq3]
  have v3 : (run gs w).getD (w.length + 3) false = (w.getD p.2.2.1 false && w.getD q.1 false) := by
    rw [run_gate_lt gs w 3 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
    rw [run_getD gs w p.2.2.1 hp3, run_getD gs w q.1 hq1]
  have v4 : (run gs w).getD (w.length + 4) false = (w.getD p.1 false && w.getD q.2.2.2 false) := by
    rw [run_gate_lt gs w 4 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
    rw [run_getD gs w p.1 hp1, run_getD gs w q.2.2.2 hq4]
  have v5 : (run gs w).getD (w.length + 5) false = (w.getD p.2.2.2 false && w.getD q.1 false) := by
    rw [run_gate_lt gs w 5 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
    rw [run_getD gs w p.2.2.2 hp4, run_getD gs w q.1 hq1]
  have v6 : (run gs w).getD (w.length + 6) false = (w.getD p.2.1 false && w.getD q.2.2.1 false) := by
    rw [run_gate_lt gs w 6 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
    rw [run_getD gs w p.2.1 hp2, run_getD gs w q.2.2.1 hq3]
  have v7 : (run gs w).getD (w.length + 7) false = (w.getD p.2.2.1 false && w.getD q.2.1 false) := by
    rw [run_gate_lt gs w 7 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
    rw [run_getD gs w p.2.2.1 hp3, run_getD gs w q.2.1 hq2]
  have v8 : (run gs w).getD (w.length + 8) false =
      ((w.getD p.1 false && w.getD q.2.2.2 false) || (w.getD p.2.2.2 false && w.getD q.1 false)) := by
    rw [run_gate_lt gs w 8 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [v4, v5]
  have v9 : (run gs w).getD (w.length + 9) false =
      ((w.getD p.2.1 false && w.getD q.2.2.1 false) || (w.getD p.2.2.1 false && w.getD q.2.1 false)) := by
    rw [run_gate_lt gs w 9 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [v6, v7]
  have v10 : (run gs w).getD (w.length + 10) false = (w.getD p.1 false && w.getD q.1 false) := by
    rw [run_gate_lt gs w 10 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
    rw [run_getD gs w p.1 hp1, run_getD gs w q.1 hq1]
  have v11 : (run gs w).getD (w.length + 11) false =
      ((w.getD p.1 false && w.getD q.2.1 false) || (w.getD p.2.1 false && w.getD q.1 false)) := by
    rw [run_gate_lt gs w 11 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [v0, v1]
  have v12 : (run gs w).getD (w.length + 12) false =
      ((w.getD p.1 false && w.getD q.2.2.1 false) || (w.getD p.2.2.1 false && w.getD q.1 false)) := by
    rw [run_gate_lt gs w 12 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [v2, v3]
  have v13 : (run gs w).getD (w.length + 13) false =
      (((w.getD p.1 false && w.getD q.2.2.2 false) || (w.getD p.2.2.2 false && w.getD q.1 false)) ||
       ((w.getD p.2.1 false && w.getD q.2.2.1 false) || (w.getD p.2.2.1 false && w.getD q.2.1 false))) := by
    rw [run_gate_lt gs w 13 (by omega) (by intro i hi; simp [gs] at hi; rcases hi with rfl | rfl <;> omega)]
    simp only [gs, List.getElem_cons_succ, List.getElem_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
    rw [v8, v9]
  rw [v10, v11, v12, v13]
  rfl

lemma run_compileBlock_getD (n k : ℕ) (g : Gate) (w : List Bool) (hw : w.length = 2 * n + 2 + 14 * k)
    (s : List (Bool × Bool × Bool × Bool)) (hs : s.length = n + k)
    (hF : w.getD (2 * n) false = false)
    (hspec : ∀ u < n + k,
      let r := ref n k u
      (w.getD r.1 false, w.getD r.2.1 false, w.getD r.2.2.1 false, w.getD r.2.2.2 false) =
        s.getD u (false, false, false, false)) :
    let w' := run (compileBlock n k g) w
    let b := 2 * n + 2 + 14 * k
    (w'.getD (b + 10) false, w'.getD (b + 11) false, w'.getD (b + 12) false, w'.getD (b + 13) false) =
      evalQuad s g := by
  have href : ∀ u,
      (w.getD (ref n k u).1 false, w.getD (ref n k u).2.1 false,
       w.getD (ref n k u).2.2.1 false, w.getD (ref n k u).2.2.2 false) =
        s.getD u (false, false, false, false) := by
    intro u
    by_cases hu : u < n + k
    · exact hspec u hu
    · have hu1 : ¬ u < n := by omega
      have hout : s.length ≤ u := by omega
      simp only [ref, hu1, hu, ite_false, hF]
      rw [List.getD_eq_default s _ hout]
  have h14 : ∀ (j : ℕ), 10 ≤ j → j < 14 → (run (dummyGates 14) w).getD (2 * n + 2 + 14 * k + j) false = false := by
    intro j _ hj2
    rw [← hw]
    exact run_dummyGates_getD 14 w j hj2
  rcases g with ⟨op, ins⟩
  cases op
  · cases ins with
    | nil =>
      dsimp only [compileBlock, evalQuad]
      set gs := dummyGates 10 ++ [⟨GateOp.and, []⟩, ⟨GateOp.or, []⟩, ⟨GateOp.or, []⟩, ⟨GateOp.or, []⟩]
      have hlen : gs.length = 14 := by simp [gs, dummyGates_length]
      have hg10 : gs[10] = ⟨GateOp.and, []⟩ := by
        simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length])]; simp [dummyGates_length]
      have hg11 : gs[11] = ⟨GateOp.or, []⟩ := by
        simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length]; omega)]; simp [dummyGates_length]
      have hg12 : gs[12] = ⟨GateOp.or, []⟩ := by
        simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length]; omega)]; simp [dummyGates_length]
      have hg13 : gs[13] = ⟨GateOp.or, []⟩ := by
        simp only [gs]; rw [List.getElem_append_right (by rw [dummyGates_length]; omega)]; simp [dummyGates_length]
      have v10 : (run gs w).getD (2 * n + 2 + 14 * k + 10) false = true := by
        rw [← hw, run_gate_lt gs w 10 (by omega) (by rw [hg10]; intro i hi; cases hi)]
        rw [hg10]; rfl
      have v11 : (run gs w).getD (2 * n + 2 + 14 * k + 11) false = false := by
        rw [← hw, run_gate_lt gs w 11 (by omega) (by rw [hg11]; intro i hi; cases hi)]
        rw [hg11]; rfl
      have v12 : (run gs w).getD (2 * n + 2 + 14 * k + 12) false = false := by
        rw [← hw, run_gate_lt gs w 12 (by omega) (by rw [hg12]; intro i hi; cases hi)]
        rw [hg12]; rfl
      have v13 : (run gs w).getD (2 * n + 2 + 14 * k + 13) false = false := by
        rw [← hw, run_gate_lt gs w 13 (by omega) (by rw [hg13]; intro i hi; cases hi)]
        rw [hg13]; rfl
      rw [v10, v11, v12, v13]
    | cons a l => cases l with
      | nil =>
        dsimp only [compileBlock, evalQuad]
        rw [← href a, ← hw]
        exact run_copy4_getD w (ref n k a) (ref_lt n k a w.length hw)
      | cons b l2 => cases l2 with
        | nil =>
          dsimp only [compileBlock, evalQuad]
          rw [← href a, ← href b]
          exact run_and2_getD w (2 * n + 2 + 14 * k) hw.symm (ref n k a) (ref n k b)
            (ref_lt n k a w.length hw) (ref_lt n k b w.length hw)
        | cons c l3 =>
          dsimp only [compileBlock, evalQuad]
          rw [h14 10 (by omega) (by omega), h14 11 (by omega) (by omega),
            h14 12 (by omega) (by omega), h14 13 (by omega) (by omega)]
  · cases ins with
    | nil =>
      dsimp only [compileBlock, evalQuad]
      rw [h14 10 (by omega) (by omega), h14 11 (by omega) (by omega),
        h14 12 (by omega) (by omega), h14 13 (by omega) (by omega)]
    | cons a l => cases l with
      | nil =>
        dsimp only [compileBlock, evalQuad]
        rw [← href a, ← hw]
        exact run_copy4_getD w (ref n k a) (ref_lt n k a w.length hw)
      | cons b l2 => cases l2 with
        | nil =>
          dsimp only [compileBlock, evalQuad]
          rw [← href a, ← href b, ← hw]
          exact run_or4_getD w (ref n k a) (ref n k b) (ref_lt n k a w.length hw) (ref_lt n k b w.length hw)
        | cons c l3 =>
          dsimp only [compileBlock, evalQuad]
          rw [h14 10 (by omega) (by omega), h14 11 (by omega) (by omega),
            h14 12 (by omega) (by omega), h14 13 (by omega) (by omega)]
  · dsimp only [compileBlock, evalQuad]
    rw [h14 10 (by omega) (by omega), h14 11 (by omega) (by omega),
      h14 12 (by omega) (by omega), h14 13 (by omega) (by omega)]
  · dsimp only [compileBlock, evalQuad]
    rw [h14 10 (by omega) (by omega), h14 11 (by omega) (by omega),
      h14 12 (by omega) (by omega), h14 13 (by omega) (by omega)]
  · dsimp only [compileBlock, evalQuad]
    rw [h14 10 (by omega) (by omega), h14 11 (by omega) (by omega),
      h14 12 (by omega) (by omega), h14 13 (by omega) (by omega)]

lemma run_compilePrefix (n : ℕ) (gs : List Gate) (x10 x11 : Fin n → Bool) :
    let w0 := run [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] (List.ofFn x10 ++ List.ofFn x11)
    let w := run (compilePrefix n 0 gs) w0
    w.getD (2 * n) false = false ∧
    ∀ u < n + gs.length,
      let r := ref n gs.length u
      (w.getD r.1 false, w.getD r.2.1 false, w.getD r.2.2.1 false, w.getD r.2.2.2 false) =
        (semRun n gs x10 x11).getD u (false, false, false, false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w0 w
    have hw0 : w = w0 := rfl
    have hlen_in : (List.ofFn x10 ++ List.ofFn x11).length = 2 * n := by
      simp; omega
    have hw0_len : w0.length = 2 * n + 2 := by
      rw [run_length, hlen_in]; rfl
    have hF : w0.getD (2 * n) false = false := by
      have h := run_gate [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] (List.ofFn x10 ++ List.ofFn x11) 0 (by simp)
      rw [hlen_in, Nat.add_zero] at h
      exact h
    refine ⟨hF, ?_⟩
    intro u hu
    simp only [List.length_nil, Nat.add_zero] at hu
    simp only [ref, hu, if_pos, semRun_nil, semInit]
    have hx10 : w0.getD u false = x10 ⟨u, hu⟩ := by
      rw [run_getD _ _ _ (by rw [hlen_in]; omega)]
      rw [List.getD_append _ _ _ _ (by simp [hu])]
      have hof : (List.ofFn x10)[u]? = some (x10 ⟨u, hu⟩) := by
        simp [List.getElem?_eq_getElem (by simp [hu] : u < (List.ofFn x10).length)]
      rw [List.getD, hof]; rfl
    have hx11 : w0.getD (n + u) false = x11 ⟨u, hu⟩ := by
      rw [run_getD _ _ _ (by rw [hlen_in]; omega)]
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
      have hof : (List.ofFn x11)[u]? = some (x11 ⟨u, hu⟩) := by
        simp [List.getElem?_eq_getElem (by simp [hu] : u < (List.ofFn x11).length)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left]
      rw [List.getD, hof]; rfl
    have hsem : ((List.finRange n).map fun i => (false, x10 i, x11 i, false)).getD u (false, false, false, false) =
        (false, x10 ⟨u, hu⟩, x11 ⟨u, hu⟩, false) := by
      have hfr : (List.finRange n)[u]? = some ⟨u, hu⟩ := by
        simp [List.getElem?_eq_getElem (by simp [hu] : u < (List.finRange n).length)]
      rw [List.getD, List.getElem?_map, hfr]; rfl
    rw [hw0, hF, hx10, hx11, hsem]
  | append_singleton gs g ih =>
    intro w0 w'
    set w := run (compilePrefix n 0 gs) w0
    have hw_len : w.length = 2 * n + 2 + 14 * gs.length := by
      have hlen_in : (List.ofFn x10 ++ List.ofFn x11).length = 2 * n := by simp; omega
      rw [run_length, compilePrefix_length, run_length, hlen_in]; rfl
    have hw'_eq : w' = run (compileBlock n gs.length g) w := by
      dsimp only [w', w]
      rw [compilePrefix_append, Nat.zero_add, run_append]
      simp [compilePrefix]
    rcases ih with ⟨hF, hspec⟩
    refine ⟨?_, ?_⟩
    · rw [hw'_eq, run_getD _ _ _ (by omega)]
      exact hF
    · intro u hu
      dsimp only
      rw [List.length_append, List.length_singleton] at hu ⊢
      by_cases hu' : u < n + gs.length
      · rw [ref_mono n gs.length u hu']
        have hlt := ref_lt n gs.length u w.length hw_len
        rw [hw'_eq, run_getD _ _ _ hlt.1, run_getD _ _ _ hlt.2.1,
          run_getD _ _ _ hlt.2.2.1, run_getD _ _ _ hlt.2.2.2]
        rw [semRun_snoc_getD_lt n gs g x10 x11 u hu']
        exact hspec u hu'
      · have hueq : u = n + gs.length := by omega
        subst hueq
        have hnot : ¬ n + gs.length < n := by omega
        have hlt2 : n + gs.length < n + (gs.length + 1) := by omega
        simp only [ref, hnot, hlt2, if_false, if_pos, Nat.add_sub_cancel_left]
        rw [hw'_eq, semRun_snoc_getD_last]
        exact run_compileBlock_getD n gs.length g w hw_len (semRun n gs x10 x11)
          (semRun_length n gs x10 x11) hF hspec

lemma compileCircuit_eval (n : ℕ) (C : Circuit) (x10 x11 : Fin n → Bool) :
    (compileCircuit n C).eval (List.ofFn x10 ++ List.ofFn x11) =
      ((semRun n C.gates x10 x11).getD C.output (false, false, false, false)).2.2.2 := by
  have h := run_compilePrefix n C.gates x10 x11
  rcases h with ⟨hF, hspec⟩
  change (run (compileCircuit n C).gates (List.ofFn x10 ++ List.ofFn x11)).getD (compileCircuit n C).output false = _
  have hrun : run (compileCircuit n C).gates (List.ofFn x10 ++ List.ofFn x11) =
      run (compilePrefix n 0 C.gates) (run [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] (List.ofFn x10 ++ List.ofFn x11)) := by
    dsimp only [compileCircuit]
    rw [run_append]
  rw [hrun]
  dsimp only [compileCircuit]
  by_cases ho : C.output < n + C.gates.length
  · have hsp := hspec C.output ho
    exact congrArg (fun q : Bool × Bool × Bool × Bool => q.2.2.2) hsp
  · have ho1 : ¬ C.output < n := by omega
    have hout : (semRun n C.gates x10 x11).length ≤ C.output := by
      rw [semRun_length]; omega
    simp only [ref, ho1, ho, if_false]
    rw [hF, List.getD_eq_default (semRun n C.gates x10 x11) (false, false, false, false) hout]

lemma semRun_sound (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (x10 x11 : Fin n → Bool) :
    ∀ w,
      let q := (semRun n gs x10 x11).getD w (false, false, false, false)
      (q.1 = true → (run gs (List.replicate n false)).getD w false = true) ∧
      (q.2.1 = true → ∃ u : Fin n, x10 u = true ∧ (run gs (List.ofFn fun i => decide (i = u))).getD w false = true) ∧
      (q.2.2.1 = true → ∃ v : Fin n, x11 v = true ∧ (run gs (List.ofFn fun i => decide (i = v))).getD w false = true) ∧
      (q.2.2.2 = true → ∃ u v : Fin n, x10 u = true ∧ x11 v = true ∧ (run gs (List.ofFn fun i => decide (i = u ∨ i = v))).getD w false = true) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    dsimp only
    by_cases hw : w < n
    · have hsem : (semRun n [] x10 x11).getD w (false, false, false, false) = (false, x10 ⟨w, hw⟩, x11 ⟨w, hw⟩, false) := by
        have hfr : (List.finRange n)[w]? = some ⟨w, hw⟩ := by
          simp [List.getElem?_eq_getElem (by simp [hw] : w < (List.finRange n).length)]
        rw [semRun_nil, semInit, List.getD, List.getElem?_map, hfr]; rfl
      rw [hsem]
      constructor
      · intro h; cases h
      constructor
      · intro h; exact ⟨⟨w, hw⟩, h, by
          have hof : (List.ofFn fun i : Fin n => decide (i = ⟨w, hw⟩))[w]? = some true := by
            simp [List.getElem?_eq_getElem (by simp [hw] : w < (List.ofFn fun i : Fin n => decide (i = ⟨w, hw⟩)).length)]
          rw [run_nil, List.getD, hof]; rfl⟩
      constructor
      · intro h; exact ⟨⟨w, hw⟩, h, by
          have hof : (List.ofFn fun i : Fin n => decide (i = ⟨w, hw⟩))[w]? = some true := by
            simp [List.getElem?_eq_getElem (by simp [hw] : w < (List.ofFn fun i : Fin n => decide (i = ⟨w, hw⟩)).length)]
          rw [run_nil, List.getD, hof]; rfl⟩
      · intro h; cases h
    · have hsem : (semRun n [] x10 x11).getD w (false, false, false, false) = (false, false, false, false) := by
        rw [List.getD_eq_default]; rw [semRun_length]; simp; omega
      rw [hsem]
      exact And.intro (fun h => by cases h) (And.intro (fun h => by cases h) (And.intro (fun h => by cases h) (fun h => by cases h)))
  | append_singleton gs g ih =>
    have hgs0 : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (by simp [hg'])
    have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hgs g (by simp)
    have ih0 := ih hgs0
    intro w
    dsimp only
    by_cases hw : w < n + gs.length
    · rw [semRun_snoc_getD_lt n gs g x10 x11 w hw]
      have rstep : ∀ x : List Bool, x.length = n →
          (run (gs ++ [g]) x).getD w false = (run gs x).getD w false := by
        intro x hx
        rw [run_append, run_cons, run_nil, step_getD]
        rw [run_length, hx]
        exact hw
      have hw' := ih0 w
      exact ⟨fun h => by rw [rstep _ (by simp)]; exact hw'.1 h,
        fun h => by rcases hw'.2.1 h with ⟨u, hu1, hu2⟩; exact ⟨u, hu1, by rw [rstep _ (by simp)]; exact hu2⟩,
        fun h => by rcases hw'.2.2.1 h with ⟨v, hv1, hv2⟩; exact ⟨v, hv1, by rw [rstep _ (by simp)]; exact hv2⟩,
        fun h => by rcases hw'.2.2.2 h with ⟨u, v, h1, h2, h3⟩; exact ⟨u, v, h1, h2, by rw [rstep _ (by simp)]; exact h3⟩⟩
    · by_cases hweq : w = n + gs.length
      · subst hweq
        rw [semRun_snoc_getD_last]
        have rstep : ∀ x : List Bool, x.length = n →
            (run (gs ++ [g]) x).getD (n + gs.length) false =
              g.op.eval (g.inputs.map fun i => (run gs x).getD i false) := by
          intro x hx
          rw [run_append, run_cons, run_nil]
          have hl : (run gs x).length = n + gs.length := by rw [run_length, hx]
          rw [← hl, step_getD_last]
        have hmono0_rep : ∀ (u : Fin n) i, (run gs (List.replicate n false)).getD i false = true →
            (run gs (List.ofFn fun k : Fin n => decide (k = u))).getD i false = true := by
          intro u i hi
          apply run_mono gs hgs0 (by simp) _ i hi
          intro j hj
          by_cases hjlt : j < n
          · simp [List.getD, hjlt] at hj
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
            cases hj
        have hmono1 : ∀ (u v : Fin n) i, (run gs (List.ofFn fun k : Fin n => decide (k = u))).getD i false = true →
            (run gs (List.ofFn fun k : Fin n => decide (k = u ∨ k = v))).getD i false = true := by
          intro u v
          apply run_mono gs hgs0 (by simp)
          intro j hj
          by_cases hjlt : j < n
          · rw [List.getD, List.getElem?_eq_getElem (by simp [hjlt])] at hj
            rw [List.getD, List.getElem?_eq_getElem (by simp [hjlt])]
            simp only [List.getElem_ofFn, Option.getD_some, decide_eq_true_eq] at hj ⊢
            exact Or.inl hj
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
            cases hj
        have hmono2 : ∀ (u v : Fin n) i, (run gs (List.ofFn fun k : Fin n => decide (k = v))).getD i false = true →
            (run gs (List.ofFn fun k : Fin n => decide (k = u ∨ k = v))).getD i false = true := by
          intro u v
          apply run_mono gs hgs0 (by simp)
          intro j hj
          by_cases hjlt : j < n
          · rw [List.getD, List.getElem?_eq_getElem (by simp [hjlt])] at hj
            rw [List.getD, List.getElem?_eq_getElem (by simp [hjlt])]
            simp only [List.getElem_ofFn, Option.getD_some, decide_eq_true_eq] at hj ⊢
            exact Or.inr hj
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
            cases hj
        have hmono02 : ∀ (u v : Fin n) i, (run gs (List.replicate n false)).getD i false = true →
            (run gs (List.ofFn fun k : Fin n => decide (k = u ∨ k = v))).getD i false = true :=
          fun u v i hi => hmono1 u v i (hmono0_rep u i hi)
        rcases g with ⟨op, ins⟩
        rcases hg with ⟨hop, hlen⟩
        rcases hop with rfl | rfl
        · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
          · dsimp only [evalQuad]
            exact And.intro (fun _ => by rw [rstep _ (by simp)]; rfl)
              (And.intro (fun h => by cases h) (And.intro (fun h => by cases h) (fun h => by cases h)))
          · dsimp only [evalQuad]
            have ha := ih0 a
            constructor
            · intro h; rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]; exact ha.1 h
            constructor
            · intro h; rcases ha.2.1 h with ⟨u, hu1, hu2⟩; exact ⟨u, hu1, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]; exact hu2⟩
            constructor
            · intro h; rcases ha.2.2.1 h with ⟨v, hv1, hv2⟩; exact ⟨v, hv1, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]; exact hv2⟩
            · intro h; rcases ha.2.2.2 h with ⟨u, v, h1, h2, h3⟩; exact ⟨u, v, h1, h2, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]; exact h3⟩
          · dsimp only [evalQuad, andQuad]
            have ha := ih0 a
            have hb := ih0 b
            constructor
            · intro h
              simp only [Bool.and_eq_true] at h
              rw [rstep _ (by simp)]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
              rw [ha.1 h.1, hb.1 h.2]; rfl
            constructor
            · intro h
              simp only [Bool.or_eq_true, Bool.and_eq_true] at h
              rcases h with ⟨ha1, hb2⟩ | ⟨ha2, hb1⟩
              · rcases hb.2.1 hb2 with ⟨u, hu1, hu2⟩
                refine ⟨u, hu1, ?_⟩
                rw [rstep _ (by simp)]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [hmono0_rep u a (ha.1 ha1), hu2]; rfl
              · rcases ha.2.1 ha2 with ⟨u, hu1, hu2⟩
                refine ⟨u, hu1, ?_⟩
                rw [rstep _ (by simp)]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [hu2, hmono0_rep u b (hb.1 hb1)]; rfl
            constructor
            · intro h
              simp only [Bool.or_eq_true, Bool.and_eq_true] at h
              rcases h with ⟨ha1, hb2⟩ | ⟨ha2, hb1⟩
              · rcases hb.2.2.1 hb2 with ⟨v, hv1, hv2⟩
                refine ⟨v, hv1, ?_⟩
                rw [rstep _ (by simp)]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [hmono0_rep v a (ha.1 ha1), hv2]; rfl
              · rcases ha.2.2.1 ha2 with ⟨v, hv1, hv2⟩
                refine ⟨v, hv1, ?_⟩
                rw [rstep _ (by simp)]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [hv2, hmono0_rep v b (hb.1 hb1)]; rfl
            · intro h
              simp only [Bool.or_eq_true, Bool.and_eq_true] at h
              rcases h with (⟨ha1, hb4⟩ | ⟨ha4, hb1⟩) | (⟨ha2, hb3⟩ | ⟨ha3, hb2⟩)
              · rcases hb.2.2.2 hb4 with ⟨u, v, hu, hv, huv⟩
                refine ⟨u, v, hu, hv, ?_⟩
                rw [rstep _ (by simp)]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [hmono02 u v a (ha.1 ha1), huv]; rfl
              · rcases ha.2.2.2 ha4 with ⟨u, v, hu, hv, huv⟩
                refine ⟨u, v, hu, hv, ?_⟩
                rw [rstep _ (by simp)]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [huv, hmono02 u v b (hb.1 hb1)]; rfl
              · rcases ha.2.1 ha2 with ⟨u, hu, hu2⟩
                rcases hb.2.2.1 hb3 with ⟨v, hv, hv2⟩
                refine ⟨u, v, hu, hv, ?_⟩
                rw [rstep _ (by simp)]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [hmono1 u v a hu2, hmono2 u v b hv2]; rfl
              · rcases ha.2.2.1 ha3 with ⟨v, hv, hv2⟩
                rcases hb.2.1 hb2 with ⟨u, hu, hu2⟩
                refine ⟨u, v, hu, hv, ?_⟩
                rw [rstep _ (by simp)]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [hmono2 u v a hv2, hmono1 u v b hu2]; rfl
          · simp at hlen
        · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
          · dsimp only [evalQuad]
            exact And.intro (fun h => by cases h) (And.intro (fun h => by cases h) (And.intro (fun h => by cases h) (fun h => by cases h)))
          · dsimp only [evalQuad]
            have ha := ih0 a
            constructor
            · intro h; rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]; exact ha.1 h
            constructor
            · intro h; rcases ha.2.1 h with ⟨u, hu1, hu2⟩; exact ⟨u, hu1, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]; exact hu2⟩
            constructor
            · intro h; rcases ha.2.2.1 h with ⟨v, hv1, hv2⟩; exact ⟨v, hv1, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]; exact hv2⟩
            · intro h; rcases ha.2.2.2 h with ⟨u, v, h1, h2, h3⟩; exact ⟨u, v, h1, h2, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]; exact h3⟩
          · dsimp only [evalQuad, orQuad]
            have ha := ih0 a
            have hb := ih0 b
            constructor
            · intro h
              rw [rstep _ (by simp)]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq] at h ⊢
              rcases h with h | h
              · exact Or.inl (ha.1 h)
              · exact Or.inr (hb.1 h)
            constructor
            · intro h
              simp only [Bool.or_eq_true] at h
              rcases h with h | h
              · rcases ha.2.1 h with ⟨u, hu1, hu2⟩
                exact ⟨u, hu1, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq]; exact Or.inl hu2⟩
              · rcases hb.2.1 h with ⟨u, hu1, hu2⟩
                exact ⟨u, hu1, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq]; exact Or.inr hu2⟩
            constructor
            · intro h
              simp only [Bool.or_eq_true] at h
              rcases h with h | h
              · rcases ha.2.2.1 h with ⟨v, hv1, hv2⟩
                exact ⟨v, hv1, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq]; exact Or.inl hv2⟩
              · rcases hb.2.2.1 h with ⟨v, hv1, hv2⟩
                exact ⟨v, hv1, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq]; exact Or.inr hv2⟩
            · intro h
              simp only [Bool.or_eq_true] at h
              rcases h with h | h
              · rcases ha.2.2.2 h with ⟨u, v, h1, h2, h3⟩
                exact ⟨u, v, h1, h2, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq]; exact Or.inl h3⟩
              · rcases hb.2.2.2 h with ⟨u, v, h1, h2, h3⟩
                exact ⟨u, v, h1, h2, by rw [rstep _ (by simp)]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq]; exact Or.inr h3⟩
          · simp at hlen
      · have hnot : ¬ w < (semRun n (gs ++ [g]) x10 x11).length := by
          rw [semRun_length, List.length_append, List.length_singleton]; omega
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hnot)]
        exact And.intro (fun h => by cases h) (And.intro (fun h => by cases h) (And.intro (fun h => by cases h) (fun h => by cases h)))

lemma setList_pair {n : ℕ} {p q : Fin n} (hpq : p < q) :
    setList ({p, q} : Finset (Fin n)) = [p.val, q.val] := by
  unfold setList
  set L := (List.finRange n).filter fun i => decide (i ∈ ({p, q} : Finset (Fin n)))
  have hmem : ∀ i : Fin n, i ∈ L ↔ i = p ∨ i = q := by
    intro i
    simp [L, List.mem_filter, List.mem_finRange]
  have hp_mem : p ∈ L := (hmem p).2 (Or.inl rfl)
  have hq_mem : q ∈ L := (hmem q).2 (Or.inr rfl)
  have hpair : L.Pairwise (· < ·) := by
    apply List.Pairwise.filter
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp [Fin.lt_def, hij]
  have hL : L = [p, q] := by
    rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · cases hp_mem
    · have ha : a = p := (List.mem_singleton.1 (by simpa using hp_mem)).symm
      have hb : a = q := (List.mem_singleton.1 (by simpa using hq_mem)).symm
      subst ha; exact (ne_of_lt hpq hb).elim
    · have hpab : a = p ∨ a = q := (hmem a).1 (by simp)
      have hqab : b = p ∨ b = q := (hmem b).1 (by simp)
      have hab : a < b := by
        rw [List.pairwise_cons] at hpair
        exact hpair.1 b (by simp)
      rcases hpab with rfl | rfl <;> rcases hqab with rfl | rfl
      · exact (lt_irrefl _ hab).elim
      · rfl
      · exact (lt_asymm hpq hab).elim
      · exact (lt_irrefl _ hab).elim
    · have hab : a < b := by rw [List.pairwise_cons] at hpair; exact hpair.1 b (by simp)
      have hbc : b < c := by
        rw [List.pairwise_cons] at hpair
        have h2 := hpair.2
        rw [List.pairwise_cons] at h2
        exact h2.1 c (by simp)
      have ha : a = p ∨ a = q := (hmem a).1 (by simp)
      have hb : b = p ∨ b = q := (hmem b).1 (by simp)
      have hc : c = p ∨ c = q := (hmem c).1 (by simp)
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
        first | exact (lt_irrefl _ (lt_trans hab hbc)).elim | exact (lt_irrefl _ hab).elim | exact (lt_irrefl _ hbc).elim | exact (lt_asymm hpq (lt_trans hab hbc)).elim | exact (lt_asymm hpq hab).elim | exact (lt_asymm hpq hbc).elim
  rw [hL]
  rfl

lemma mem_foldl_insertNew (A acc : List (List ℕ)) (v : List ℕ) :
    v ∈ A.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ A := by
  induction A generalizing acc with
  | nil => simp
  | cons a A ih =>
    rw [List.foldl_cons, ih]
    simp only [insertNew]
    split_ifs with h
    · simp only [List.mem_cons]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | rfl | h1)
        · exact Or.inl h1
        · exact Or.inl h
        · exact Or.inr h1
    · simp only [List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h1 | h1) | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | h1 | h1)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) :
    v ∈ andStep k A B ↔ ∃ u1 ∈ A, ∃ u2 ∈ B, v = capAdd k u1 u2 := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u1, hu1, u2, hu2, rfl⟩; exact ⟨u1, hu1, u2, hu2, rfl⟩
  · rintro ⟨u1, hu1, u2, hu2, rfl⟩; exact ⟨u1, hu1, u2, hu2, rfl⟩

lemma readVectors_to_semRun (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (p q : Fin n) (hpq : p < q) (x10 x11 : Fin n → Bool) :
    ∀ w vec, vec ∈ (readVectors ⟨gs, 0⟩ n [p.val, q.val] 1).getD w [] →
      vec.length = 2 ∧
      (vec = [0, 0] → ((semRun n gs x10 x11).getD w (false, false, false, false)).1 = true) ∧
      (vec = [1, 0] →
        (x10 p = true → ((semRun n gs x10 x11).getD w (false, false, false, false)).2.1 = true) ∧
        (x11 p = true → ((semRun n gs x10 x11).getD w (false, false, false, false)).2.2.1 = true)) ∧
      (vec = [0, 1] →
        (x10 q = true → ((semRun n gs x10 x11).getD w (false, false, false, false)).2.1 = true) ∧
        (x11 q = true → ((semRun n gs x10 x11).getD w (false, false, false, false)).2.2.1 = true)) ∧
      (vec = [1, 1] →
        ((x10 p = true ∧ x11 q = true) ∨ (x10 q = true ∧ x11 p = true)) →
          ((semRun n gs x10 x11).getD w (false, false, false, false)).2.2.2 = true) := by
  have hpq_ne : p.val ≠ q.val := Fin.val_ne_of_ne (ne_of_lt hpq)
  induction gs using List.reverseRecOn with
  | nil =>
    intro w vec hvec
    by_cases hw : w < n
    · have hget : (readVectors ⟨[], 0⟩ n [p.val, q.val] 1).getD w [] = leafVectors [p.val, q.val] 1 w := by
        simp [readVectors, List.getD, List.getElem?_map, List.getElem?_range hw]
      rw [hget] at hvec
      unfold leafVectors at hvec
      split_ifs at hvec with hmem
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        simp only [List.mem_singleton] at hvec
        subst hvec
        have hsem : (semRun n [] x10 x11).getD w (false, false, false, false) =
            (false, x10 ⟨w, hw⟩, x11 ⟨w, hw⟩, false) := by
          have hfr : (List.finRange n)[w]? = some ⟨w, hw⟩ := by
            simp [List.getElem?_eq_getElem (by simp [hw] : w < (List.finRange n).length)]
          rw [semRun_nil, semInit, List.getD, List.getElem?_map, hfr]; rfl
        rcases hmem with hwp | hwq
        · have hveq : [p.val, q.val].map (fun j => if j = w then min 1 2 else 0) = [1, 0] := by
            simp [hwp, Ne.symm hpq_ne]
          rw [hveq] at *
          constructor
          · rfl
          constructor
          · intro h; cases h
          constructor
          · intro _; have hfin : (⟨w, hw⟩ : Fin n) = p := Fin.ext hwp; rw [hsem, hfin]; exact ⟨fun h => h, fun h => h⟩
          constructor
          · intro h; cases h
          · intro h; cases h
        · have hveq : [p.val, q.val].map (fun j => if j = w then min 1 2 else 0) = [0, 1] := by
            simp [hwq, hpq_ne]
          rw [hveq] at *
          constructor
          · rfl
          constructor
          · intro h; cases h
          constructor
          · intro h; cases h
          constructor
          · intro _; have hfin : (⟨w, hw⟩ : Fin n) = q := Fin.ext hwq; rw [hsem, hfin]; exact ⟨fun h => h, fun h => h⟩
          · intro h; cases h
      · cases hvec
    · have hnot : ¬ w < (readVectors ⟨[], 0⟩ n [p.val, q.val] 1).length := by
        simp [readVectors]; omega
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hnot)] at hvec
      cases hvec
  | append_singleton gs g ih =>
    have hgs0 : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (by simp [hg'])
    have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hgs g (by simp)
    have ih0 := ih hgs0
    have hrv_len : ∀ l : List Gate, (readVectors ⟨l, 0⟩ n [p.val, q.val] 1).length = n + l.length := by
      intro l
      have hfold : ∀ (stepFn : List (List (List ℕ)) → Gate → List (List (List ℕ)))
          (_ : ∀ R g, (stepFn R g).length = R.length + 1)
          (m : List Gate) (R : List (List (List ℕ))),
          (m.foldl stepFn R).length = R.length + m.length := by
        intro stepFn hstep m
        induction m with
        | nil => intro R; simp
        | cons g' m' ihm =>
          intro R
          rw [List.foldl_cons, ihm, hstep, List.length_cons]
          omega
      unfold readVectors
      dsimp only
      rw [hfold _ (fun R g => by rw [List.length_append, List.length_singleton]), List.length_map, List.length_range]
    have hrv_snoc : readVectors ⟨gs ++ [g], 0⟩ n [p.val, q.val] 1 =
        let R := readVectors ⟨gs, 0⟩ n [p.val, q.val] 1
        let ins := g.inputs.map fun i => R.getD i []
        R ++ [match g.op with
          | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
          | GateOp.and => ins.foldl (andStep 1) [[p.val, q.val].map fun _ => 0]
          | _ => []] := by
      unfold readVectors
      dsimp only
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    intro w vec hvec
    by_cases hw : w < n + gs.length
    · rw [hrv_snoc, List.getD_append _ _ _ _ (by rw [hrv_len]; exact hw)] at hvec
      rw [semRun_snoc_getD_lt n gs g x10 x11 w hw]
      exact ih0 w vec hvec
    · by_cases hweq : w = n + gs.length
      · subst hweq
        rw [hrv_snoc, List.getD_append_right _ _ _ _ (by rw [hrv_len])] at hvec
        rw [hrv_len, Nat.sub_self, List.getD_cons_zero] at hvec
        rw [semRun_snoc_getD_last]
        set R := readVectors ⟨gs, 0⟩ n [p.val, q.val] 1
        rcases g with ⟨op, ins⟩
        rcases hg with ⟨hop, hlen⟩
        rcases hop with rfl | rfl
        · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
          · simp only [List.map_nil, List.foldl_nil, List.map_cons, List.mem_singleton] at hvec
            subst hvec
            exact And.intro rfl (And.intro (fun _ => rfl) (And.intro (fun h => by cases h) (And.intro (fun h => by cases h) (fun h => by cases h))))
          · simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hvec
            rw [mem_andStep] at hvec
            rcases hvec with ⟨u1, hu1, u2, hu2, rfl⟩
            simp only [List.mem_singleton] at hu1
            subst hu1
            have ha := ih0 a u2 hu2
            rcases ha with ⟨hlen2, h00, h10, h01, h11⟩
            rcases u2 with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, l4⟩⟩⟩ <;> simp at hlen2
            have hcap : capAdd 1 [0, 0] [c1, c2] = [min c1 2, min c2 2] := by
              simp [capAdd]
            rw [hcap]
            refine ⟨rfl, ?_, ?_, ?_, ?_⟩
            · intro h
              simp only [List.cons.injEq, and_true] at h
              have hc1 : c1 = 0 := by omega
              have hc2 : c2 = 0 := by omega
              subst hc1; subst hc2
              exact h00 rfl
            · intro h
              simp only [List.cons.injEq, and_true] at h
              have hc1 : c1 = 1 := by omega
              have hc2 : c2 = 0 := by omega
              subst hc1; subst hc2
              exact h10 rfl
            · intro h
              simp only [List.cons.injEq, and_true] at h
              have hc1 : c1 = 0 := by omega
              have hc2 : c2 = 1 := by omega
              subst hc1; subst hc2
              exact h01 rfl
            · intro h
              simp only [List.cons.injEq, and_true] at h
              have hc1 : c1 = 1 := by omega
              have hc2 : c2 = 1 := by omega
              subst hc1; subst hc2
              exact h11 rfl
          · simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hvec
            rw [mem_andStep] at hvec
            rcases hvec with ⟨w1, hw1, u2, hu2, rfl⟩
            rw [mem_andStep] at hw1
            rcases hw1 with ⟨u0, hu0, u1, hu1, rfl⟩
            simp only [List.mem_singleton] at hu0
            subst hu0
            have ha := ih0 a u1 hu1
            have hb := ih0 b u2 hu2
            rcases ha with ⟨hl1, ha00, ha10, ha01, ha11⟩
            rcases hb with ⟨hl2, hb00, hb10, hb01, hb11⟩
            rcases u1 with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, la⟩⟩⟩ <;> simp at hl1
            rcases u2 with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, lb⟩⟩⟩ <;> simp at hl2
            have hcap : capAdd 1 (capAdd 1 [0, 0] [a1, a2]) [b1, b2] =
                [min (min a1 2 + b1) 2, min (min a2 2 + b2) 2] := by
              simp [capAdd]
            rw [hcap]
            dsimp only [evalQuad, andQuad]
            refine ⟨rfl, ?_, ?_, ?_, ?_⟩
            · intro h
              simp only [List.cons.injEq, and_true] at h
              have ha1z : a1 = 0 := by omega
              have ha2z : a2 = 0 := by omega
              have hb1z : b1 = 0 := by omega
              have hb2z : b2 = 0 := by omega
              subst ha1z; subst ha2z; subst hb1z; subst hb2z
              simp only [Bool.and_eq_true]
              exact ⟨ha00 rfl, hb00 rfl⟩
            · intro h
              simp only [List.cons.injEq, and_true] at h
              have ha2z : a2 = 0 := by omega
              have hb2z : b2 = 0 := by omega
              subst ha2z; subst hb2z
              have hsum : a1 + b1 = 1 := by omega
              have hcases : (a1 = 0 ∧ b1 = 1) ∨ (a1 = 1 ∧ b1 = 0) := by omega
              simp only [Bool.or_eq_true, Bool.and_eq_true]
              rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · refine ⟨fun hp => Or.inl ⟨ha00 rfl, (hb10 rfl).1 hp⟩,
                  fun hp => Or.inl ⟨ha00 rfl, (hb10 rfl).2 hp⟩⟩
              · refine ⟨fun hp => Or.inr ⟨(ha10 rfl).1 hp, hb00 rfl⟩,
                  fun hp => Or.inr ⟨(ha10 rfl).2 hp, hb00 rfl⟩⟩
            · intro h
              simp only [List.cons.injEq, and_true] at h
              have ha1z : a1 = 0 := by omega
              have hb1z : b1 = 0 := by omega
              subst ha1z; subst hb1z
              have hsum : a2 + b2 = 1 := by omega
              have hcases : (a2 = 0 ∧ b2 = 1) ∨ (a2 = 1 ∧ b2 = 0) := by omega
              simp only [Bool.or_eq_true, Bool.and_eq_true]
              rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · refine ⟨fun hq => Or.inl ⟨ha00 rfl, (hb01 rfl).1 hq⟩,
                  fun hq => Or.inl ⟨ha00 rfl, (hb01 rfl).2 hq⟩⟩
              · refine ⟨fun hq => Or.inr ⟨(ha01 rfl).1 hq, hb00 rfl⟩,
                  fun hq => Or.inr ⟨(ha01 rfl).2 hq, hb00 rfl⟩⟩
            · intro h hxy
              simp only [List.cons.injEq, and_true] at h
              have h1 : a1 + b1 = 1 := by omega
              have h2 : a2 + b2 = 1 := by omega
              have hc1 : (a1 = 0 ∧ b1 = 1) ∨ (a1 = 1 ∧ b1 = 0) := by omega
              have hc2 : (a2 = 0 ∧ b2 = 1) ∨ (a2 = 1 ∧ b2 = 0) := by omega
              simp only [Bool.or_eq_true, Bool.and_eq_true]
              rcases hc1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hc2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inl (Or.inl ⟨ha00 rfl, hb11 rfl hxy⟩)
              · rcases hxy with ⟨hp, hq⟩ | ⟨hq, hp⟩
                · exact Or.inr (Or.inr ⟨(ha01 rfl).2 hq, (hb10 rfl).1 hp⟩)
                · exact Or.inr (Or.inl ⟨(ha01 rfl).1 hq, (hb10 rfl).2 hp⟩)
              · rcases hxy with ⟨hp, hq⟩ | ⟨hq, hp⟩
                · exact Or.inr (Or.inl ⟨(ha10 rfl).1 hp, (hb01 rfl).2 hq⟩)
                · exact Or.inr (Or.inr ⟨(ha10 rfl).2 hp, (hb01 rfl).1 hq⟩)
              · exact Or.inl (Or.inr ⟨ha11 rfl hxy, hb00 rfl⟩)
          · simp at hlen
        · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
          · simp only [List.map_nil, List.foldl_nil] at hvec
            cases hvec
          · simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hvec
            rw [mem_foldl_insertNew] at hvec
            rcases hvec with hbad | ha
            · cases hbad
            · exact ih0 a vec ha
          · simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hvec
            rw [mem_foldl_insertNew, mem_foldl_insertNew] at hvec
            rcases hvec with (hbad | ha) | hb
            · cases hbad
            · have ha' := ih0 a vec ha
              dsimp only [evalQuad, orQuad]
              simp only [Bool.or_eq_true]
              refine ⟨ha'.1, fun h => Or.inl (ha'.2.1 h),
                fun h => ⟨fun h1 => Or.inl ((ha'.2.2.1 h).1 h1), fun h1 => Or.inl ((ha'.2.2.1 h).2 h1)⟩,
                fun h => ⟨fun h1 => Or.inl ((ha'.2.2.2.1 h).1 h1), fun h1 => Or.inl ((ha'.2.2.2.1 h).2 h1)⟩,
                fun h hxy => Or.inl (ha'.2.2.2.2 h hxy)⟩
            · have hb' := ih0 b vec hb
              dsimp only [evalQuad, orQuad]
              simp only [Bool.or_eq_true]
              refine ⟨hb'.1, fun h => Or.inr (hb'.2.1 h),
                fun h => ⟨fun h1 => Or.inr ((hb'.2.2.1 h).1 h1), fun h1 => Or.inr ((hb'.2.2.1 h).2 h1)⟩,
                fun h => ⟨fun h1 => Or.inr ((hb'.2.2.2.1 h).1 h1), fun h1 => Or.inr ((hb'.2.2.2.1 h).2 h1)⟩,
                fun h hxy => Or.inr (hb'.2.2.2.2 h hxy)⟩
          · simp at hlen
      · have hnot : ¬ w < (readVectors ⟨gs ++ [g], 0⟩ n [p.val, q.val] 1).length := by
          rw [hrv_len, List.length_append, List.length_singleton]; omega
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hnot)] at hvec
        cases hvec

end PEqualNP.Outside.L_meta_4193

theorem PEqualNP.Outside.L_meta_4193 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.ReadK.IsReadK x2 x5 (1 : ℕ) → (∀ (x8 : Fin x2 → Bool), x5.eval (List.ofFn x8) = Decidable.decide (∃ (x9 : Fin x2) (x10 : Fin x2), x3.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size + (1 : ℕ) ≤ x1 * (x5.size + (1 : ℕ)) ∧ ∀ (x10 x11 : Fin x2 → Bool), x9.eval (List.ofFn x10 ++ List.ofFn x11) = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x3.Adj x12 x13 ∧ x10 x12 = Bool.true ∧ x11 x13 = Bool.true) := by
  refine ⟨14, ?_⟩
  intro n G _ C hmono hread heval
  refine ⟨PEqualNP.Outside.L_meta_4193.compileCircuit n C,
    PEqualNP.Outside.L_meta_4193.compileCircuit_mono n C, ?_, ?_⟩
  · rw [PEqualNP.Outside.L_meta_4193.compileCircuit_size]
    omega
  · intro x10 x11
    rw [PEqualNP.Outside.L_meta_4193.compileCircuit_eval]
    apply Bool.eq_iff_iff.2
    constructor
    · intro htrue
      have hsnd := (PEqualNP.Outside.L_meta_4193.semRun_sound n C.gates hmono x10 x11 C.output).2.2.2 htrue
      rcases hsnd with ⟨u, v, hu, hv, huv⟩
      have hce : C.eval (List.ofFn fun i : Fin n => decide (i = u ∨ i = v)) = true := huv
      rw [heval] at hce
      simp only [decide_eq_true_eq] at hce
      rcases hce with ⟨a, b, hab, ha, hb⟩
      have hne : a ≠ b := G.ne_of_adj hab
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hne rfl).elim
      · simp only [decide_eq_true_eq]; exact ⟨a, b, hab, hu, hv⟩
      · simp only [decide_eq_true_eq]; exact ⟨b, a, G.adj_symm hab, hu, hv⟩
      · exact (hne rfl).elim
    · intro hdec
      simp only [decide_eq_true_eq] at hdec
      rcases hdec with ⟨u, v, huv, hu, hv⟩
      have hne : u ≠ v := G.ne_of_adj huv
      have hprime : PEqualNP.ReadK.IsPrimeImplicant n C ({u, v} : Finset (Fin n)) := by
        refine ⟨?_, ?_⟩
        · unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.ReadK.setInput
          rw [heval]
          simp only [decide_eq_true_eq]
          exact ⟨u, v, huv, by simp, by simp⟩
        · intro T hT
          have hcard : T.card < ({u, v} : Finset (Fin n)).card := Finset.card_lt_card (Finset.mem_ssubsets.1 hT)
          have hpair : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair hne
          unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.ReadK.setInput
          rw [heval]
          simp only [decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
          intro a b hab ha hb
          have hab_ne : a ≠ b := G.ne_of_adj hab
          have hsub : ({a, b} : Finset (Fin n)) ⊆ T := by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          have h2 : 2 ≤ T.card := by
            rw [← Finset.card_pair hab_ne]
            exact Finset.card_le_card hsub
          omega
      have hr := hread {u, v} hprime
      set p := if u < v then u else v
      set q := if u < v then v else u
      have hpq : p < q := by
        by_cases hlt : u < v
        · simp [p, q, hlt]
        · have hvlt : v < u := lt_of_le_of_ne (not_lt.1 hlt) hne.symm
          simp [p, q, hlt, hvlt]
      have hset : ({u, v} : Finset (Fin n)) = {p, q} := by
        by_cases hlt : u < v
        · simp [p, q, hlt]
        · simp [p, q, hlt, Finset.pair_comm]
      have hxy : (x10 p = true ∧ x11 q = true) ∨ (x10 q = true ∧ x11 p = true) := by
        by_cases hlt : u < v
        · left; simp [p, q, hlt, hu, hv]
        · right; simp [p, q, hlt, hu, hv]
      rw [hset, PEqualNP.Outside.L_meta_4193.setList_pair hpq] at hr
      unfold PEqualNP.ReadK.readsAtMost at hr
      simp only [List.any_eq_true, List.all_eq_true, decide_eq_true_eq] at hr
      rcases hr with ⟨vec, hvec_mem, hvec_le⟩
      have hrv := PEqualNP.Outside.L_meta_4193.readVectors_to_semRun n C.gates hmono p q hpq x10 x11 C.output vec hvec_mem
      rcases hrv with ⟨hlen2, h00, h10, h01, h11⟩
      rcases vec with _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, l4⟩⟩⟩ <;> simp at hlen2
      have hc1 : c1 ≤ 1 := hvec_le c1 (by simp)
      have hc2 : c2 ≤ 1 := hvec_le c2 (by simp)
      have hcases : (c1 = 0 ∧ c2 = 0) ∨ (c1 = 1 ∧ c2 = 0) ∨ (c1 = 0 ∧ c2 = 1) ∨ (c1 = 1 ∧ c2 = 1) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hs0 := (PEqualNP.Outside.L_meta_4193.semRun_sound n C.gates hmono x10 x11 C.output).1 (h00 rfl)
        have hfalse : C.eval (List.replicate n false) = false := by
          have hrep : List.replicate n false = List.ofFn (fun _ : Fin n => false) := by
            apply List.ext_getElem (by simp)
            intro i hi _
            simp
          change (PEqualNP.Outside.L_meta_4193.run C.gates (List.replicate n false)).getD C.output false = false
          have hev := heval (fun _ : Fin n => false)
          simp only [Bool.false_eq_true, and_false, exists_false] at hev
          change (PEqualNP.Outside.L_meta_4193.run C.gates (List.ofFn fun _ : Fin n => false)).getD C.output false = false at hev
          rw [← hrep] at hev
          exact hev
        change C.eval (List.replicate n false) = true at hs0
        rw [hfalse] at hs0
        cases hs0
      · have hrv' := PEqualNP.Outside.L_meta_4193.readVectors_to_semRun n C.gates hmono p q hpq
          (fun i => decide (i = p)) (fun _ => false) C.output [1, 0] hvec_mem
        have hsem1 : ((PEqualNP.Outside.L_meta_4193.semRun n C.gates (fun i => decide (i = p)) (fun _ => false)).getD C.output (false, false, false, false)).2.1 = true :=
          (hrv'.2.2.1 rfl).1 (by simp)
        have hs1 := (PEqualNP.Outside.L_meta_4193.semRun_sound n C.gates hmono (fun i => decide (i = p)) (fun _ => false) C.output).2.1 hsem1
        rcases hs1 with ⟨z, hz, hz_run⟩
        simp only [decide_eq_true_eq] at hz
        subst hz
        have hce : C.eval (List.ofFn fun i : Fin n => decide (i = p)) = true := hz_run
        rw [heval] at hce
        simp only [decide_eq_true_eq] at hce
        rcases hce with ⟨a, b, hab, ha, hb⟩
        subst ha; subst hb
        exact (G.ne_of_adj hab rfl).elim
      · have hrv' := PEqualNP.Outside.L_meta_4193.readVectors_to_semRun n C.gates hmono p q hpq
          (fun i => decide (i = q)) (fun _ => false) C.output [0, 1] hvec_mem
        have hsem1 : ((PEqualNP.Outside.L_meta_4193.semRun n C.gates (fun i => decide (i = q)) (fun _ => false)).getD C.output (false, false, false, false)).2.1 = true :=
          (hrv'.2.2.2.1 rfl).1 (by simp)
        have hs1 := (PEqualNP.Outside.L_meta_4193.semRun_sound n C.gates hmono (fun i => decide (i = q)) (fun _ => false) C.output).2.1 hsem1
        rcases hs1 with ⟨z, hz, hz_run⟩
        simp only [decide_eq_true_eq] at hz
        subst hz
        have hce : C.eval (List.ofFn fun i : Fin n => decide (i = q)) = true := hz_run
        rw [heval] at hce
        simp only [decide_eq_true_eq] at hce
        rcases hce with ⟨a, b, hab, ha, hb⟩
        subst ha; subst hb
        exact (G.ne_of_adj hab rfl).elim
      · exact h11 rfl hxy
