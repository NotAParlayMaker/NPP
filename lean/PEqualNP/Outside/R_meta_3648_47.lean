import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3648_47
    (hTT : ∀ (D : PEqualNP.MetaComplexity.BinaryCircuit),
      D.size = 13 → D.output = 23 →
      (∀ (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), D.gates[j]? = some g →
        g.left ≤ g.right ∧ g.right < 11 + j ∧
        ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (∀ g : PEqualNP.MetaComplexity.BinaryGate, D.gates[0]? = some g →
        g.op = (fun u v : Bool => u == true && v == true) ∧
        10 * g.left + g.right ∈ ([1, 2, 3, 4, 6, 12, 13, 14, 15, 16, 17, 18, 19, 23, 24, 26, 27, 28, 29, 34, 36, 39, 46, 67, 69] : List ℕ)) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, false]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hTF : ∀ (D : PEqualNP.MetaComplexity.BinaryCircuit),
      D.size = 13 → D.output = 23 →
      (∀ (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), D.gates[j]? = some g →
        g.left ≤ g.right ∧ g.right < 11 + j ∧
        ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (∀ g : PEqualNP.MetaComplexity.BinaryGate, D.gates[0]? = some g →
        g.op = (fun u v : Bool => u == true && v == false) ∧
        10 * g.left + g.right ∈ ([1, 2, 3, 4, 6, 12, 13, 14, 16, 17, 18, 19, 23, 24, 26, 27, 29, 34, 36, 39, 46, 69] : List ℕ)) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, false]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hFT : ∀ (D : PEqualNP.MetaComplexity.BinaryCircuit),
      D.size = 13 → D.output = 23 →
      (∀ (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), D.gates[j]? = some g →
        g.left ≤ g.right ∧ g.right < 11 + j ∧
        ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (∀ g : PEqualNP.MetaComplexity.BinaryGate, D.gates[0]? = some g →
        g.op = (fun u v : Bool => u == false && v == true) ∧
        10 * g.left + g.right ∈ ([1, 2, 3, 4, 6, 12, 13, 14, 15, 16, 17, 18, 19, 23, 24, 26, 27, 28, 29, 34, 36, 39, 46, 67, 69] : List ℕ)) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, false]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hFF : ∀ (D : PEqualNP.MetaComplexity.BinaryCircuit),
      D.size = 13 → D.output = 23 →
      (∀ (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), D.gates[j]? = some g →
        g.left ≤ g.right ∧ g.right < 11 + j ∧
        ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (∀ g : PEqualNP.MetaComplexity.BinaryGate, D.gates[0]? = some g →
        g.op = (fun u v : Bool => u == false && v == false) ∧
        10 * g.left + g.right ∈ ([1, 2, 3, 6, 12, 13, 14, 15, 16, 17, 18, 19, 23, 24, 26, 27, 28, 29, 34, 36, 39, 46, 67, 69] : List ℕ)) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4, false]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit), x1.size = (13 : ℕ) → x1.output < (24 : ℕ) → (∀ (x4 : ℕ) (x5 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[x4]? = Option.some x5 → x5.left < (11 : ℕ) + x4 ∧ x5.right < (11 : ℕ) + x4 ∧ ∃ (x7 : Bool) (x8 : Bool), x5.op = fun (x9 x10 : Bool) => x9 == x7 && x10 == x8) → ∃ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), Bool.false]) != Bool.false) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  intro C0 hsz0 hout0 hgates0
  have hszB : ∀ D : PEqualNP.MetaComplexity.BinaryCircuit, D.size = D.gates.length := fun _ => rfl
  have hevB : ∀ (D : PEqualNP.MetaComplexity.BinaryCircuit) (w : List Bool), D.eval w =
      (D.gates.foldl (fun s g => s ++ [g.op (s.getD g.left false) (s.getD g.right false)]) w).getD
        D.output false := fun _ _ => rfl
  let step := fun (s : List Bool) (g : PEqualNP.MetaComplexity.BinaryGate) =>
    s ++ [g.op (s.getD g.left false) (s.getD g.right false)]
  let run := fun (gs : List PEqualNP.MetaComplexity.BinaryGate) (s : List Bool) => gs.foldl step s
  let F := fun x : Fin 9 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
      x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let inp := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 4, false]
  by_contra hno
  have hne_false : ∀ b : Bool, (b != false) = b := by intro b; cases b <;> rfl
  have hC0 : ∀ x : Fin 9 → Bool, C0.eval (inp x) = F x := by
    intro x
    by_contra hx
    apply hno
    refine ⟨x, ?_⟩
    rw [hne_false]
    exact hx
  have step_len : ∀ (s : List Bool) (g : PEqualNP.MetaComplexity.BinaryGate),
      (step s g).length = s.length + 1 := by
    intro s g; simp [step]
  have step_keep : ∀ (s : List Bool) (g : PEqualNP.MetaComplexity.BinaryGate) (i : ℕ),
      i < s.length → (step s g).getD i false = s.getD i false := by
    intro s g i hi
    exact List.getD_append _ _ _ _ hi
  have step_snoc : ∀ (s : List Bool) (g : PEqualNP.MetaComplexity.BinaryGate),
      (step s g).getD s.length false = g.op (s.getD g.left false) (s.getD g.right false) := by
    intro s g
    dsimp only [step]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl
  have run_len : ∀ (gs : List PEqualNP.MetaComplexity.BinaryGate) (s : List Bool),
      (run gs s).length = s.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro s; simp [run]
    | cons g gs ih =>
      intro s
      change (run gs (step s g)).length = s.length + (g :: gs).length
      rw [ih, step_len]
      simp only [List.length_cons]
      omega
  have run_keep : ∀ (gs : List PEqualNP.MetaComplexity.BinaryGate) (s : List Bool) (i : ℕ),
      i < s.length → (run gs s).getD i false = s.getD i false := by
    intro gs
    induction gs with
    | nil => intro s i _; rfl
    | cons g gs ih =>
      intro s i hi
      change (run gs (step s g)).getD i false = s.getD i false
      rw [ih _ _ (by rw [step_len]; omega), step_keep s g i hi]
  have run_nth : ∀ (gs : List PEqualNP.MetaComplexity.BinaryGate) (s : List Bool)
      (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate),
      gs[j]? = some g → g.left < s.length + j → g.right < s.length + j →
      (run gs s).getD (s.length + j) false =
        g.op ((run gs s).getD g.left false) ((run gs s).getD g.right false) := by
    intro gs
    induction gs with
    | nil =>
      intro s j g hg
      simp at hg
    | cons h gs ih =>
      intro s j g hg hl hr
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
        subst hg
        simp only [Nat.add_zero] at hl hr ⊢
        change (run gs (step s h)).getD s.length false =
          h.op ((run gs (step s h)).getD h.left false) ((run gs (step s h)).getD h.right false)
        rw [run_keep gs (step s h) s.length (by rw [step_len]; omega),
          run_keep gs (step s h) h.left (by rw [step_len]; omega),
          run_keep gs (step s h) h.right (by rw [step_len]; omega),
          step_keep s h h.left hl, step_keep s h h.right hr, step_snoc]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hg
        have heq : s.length + (j + 1) = (step s h).length + j := by rw [step_len]; omega
        rw [heq] at hl hr ⊢
        exact ih (step s h) j g hg hl hr
  have inp_len : ∀ x : Fin 9 → Bool, (inp x).length = 11 := by intro x; simp [inp]
  have inp_0 : ∀ x : Fin 9 → Bool, (inp x).getD 0 false = x 0 := by
    intro x
    dsimp only [inp]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
    simp
  have inp_4 : ∀ x : Fin 9 → Bool, (inp x).getD 4 false = x 4 := by
    intro x
    dsimp only [inp]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
    simp
  have inp_9 : ∀ x : Fin 9 → Bool, (inp x).getD 9 false = (x 0 || x 4) := by
    intro x
    dsimp only [inp]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  have inp_10 : ∀ x : Fin 9 → Bool, (inp x).getD 10 false = false := by
    intro x
    dsimp only [inp]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  let flipGate := fun g : PEqualNP.MetaComplexity.BinaryGate =>
    if g.left ≤ g.right then g
    else { op := fun u v => g.op v u, left := g.right, right := g.left }
  have step_flip : ∀ (s : List Bool) (g : PEqualNP.MetaComplexity.BinaryGate),
      step s (flipGate g) = step s g := by
    intro s g
    dsimp only [step, flipGate]
    split_ifs <;> rfl
  have run_flip : ∀ (gs : List PEqualNP.MetaComplexity.BinaryGate) (s : List Bool),
      run (gs.map flipGate) s = run gs s := by
    intro gs
    induction gs with
    | nil => intro s; rfl
    | cons g gs ih =>
      intro s
      change run (gs.map flipGate) (step s (flipGate g)) = run gs (step s g)
      rw [step_flip, ih]
  have flipGate_props : ∀ (n : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate),
      g.left < n → g.right < n →
      (∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (flipGate g).left ≤ (flipGate g).right ∧ (flipGate g).right < n ∧
      ∃ c d : Bool, (flipGate g).op = fun u v : Bool => u == c && v == d := by
    intro n g hl hr hop
    obtain ⟨c, d, hcd⟩ := hop
    dsimp only [flipGate]
    split_ifs with hle
    · exact ⟨hle, hr, c, d, hcd⟩
    · refine ⟨by dsimp only; omega, hl, d, c, ?_⟩
      funext u v
      rw [hcd]
      exact Bool.and_comm _ _
  let lTT : List ℕ := [1, 2, 3, 4, 6, 12, 13, 14, 15, 16, 17, 18, 19, 23, 24, 26, 27, 28, 29, 34, 36, 39, 46, 67, 69]
  let lTF : List ℕ := [1, 2, 3, 4, 6, 12, 13, 14, 16, 17, 18, 19, 23, 24, 26, 27, 29, 34, 36, 39, 46, 69]
  let lFT : List ℕ := [1, 2, 3, 4, 6, 12, 13, 14, 15, 16, 17, 18, 19, 23, 24, 26, 27, 28, 29, 34, 36, 39, 46, 67, 69]
  let lFF : List ℕ := [1, 2, 3, 6, 12, 13, 14, 15, 16, 17, 18, 19, 23, 24, 26, 27, 28, 29, 34, 36, 39, 46, 67, 69]
  let canonList := fun a b : Bool => if a then (if b then lTT else lTF) else (if b then lFT else lFF)
  have hCanon : ∀ (D : PEqualNP.MetaComplexity.BinaryCircuit) (a b : Bool),
      D.size = 13 → D.output = 23 →
      (∀ (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), D.gates[j]? = some g →
        g.left ≤ g.right ∧ g.right < 11 + j ∧
        ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (∀ g : PEqualNP.MetaComplexity.BinaryGate, D.gates[0]? = some g →
        g.op = (fun u v : Bool => u == a && v == b) ∧
        10 * g.left + g.right ∈ canonList a b) →
      (∀ x : Fin 9 → Bool, D.eval (inp x) = F x) → False := by
    intro D a b hsz hout hg hg0 hev
    cases a <;> cases b
    · obtain ⟨x, hx⟩ := hFF D hsz hout hg hg0; exact hx (hev x)
    · obtain ⟨x, hx⟩ := hFT D hsz hout hg hg0; exact hx (hev x)
    · obtain ⟨x, hx⟩ := hTF D hsz hout hg hg0; exact hx (hev x)
    · obtain ⟨x, hx⟩ := hTT D hsz hout hg hg0; exact hx (hev x)
  let perm := fun i : ℕ => List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] i i
  have hF_perm : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      (b0 && b5 || b5 && b8 || b8 && b3 || b3 && b4 || b4 && b0 || b0 && b1 ||
        b5 && b7 || b8 && b6 || b3 && b2 || b1 && b6 || b7 && b2 || b2 && b1) =
      (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 ||
        b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by
    decide
  have perm_lt9 : ∀ j : ℕ, j < 9 → perm j < 9 := by
    intro j hj; interval_cases j <;> decide
  have perm_ge9 : ∀ j : ℕ, 9 ≤ j → perm j = j := by
    intro j hj
    dsimp only [perm]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl
  have perm_lt : ∀ n j : ℕ, 9 ≤ n → j < n → perm j < n := by
    intro n j hn hj
    by_cases h9 : j < 9
    · have := perm_lt9 j h9; omega
    · rw [perm_ge9 j (by omega)]; exact hj
  have hpre : ∀ (gs : List PEqualNP.MetaComplexity.BinaryGate) (W W' : List Bool),
      W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD (perm j) false = W.getD j false) →
      ∀ j : ℕ,
        (run (gs.map fun g : PEqualNP.MetaComplexity.BinaryGate =>
          { op := g.op, left := perm g.left, right := perm g.right }) W').getD (perm j) false =
        (run gs W).getD j false := by
    intro gs
    induction gs with
    | nil => intro W W' _ _ hW j; exact hW j
    | cons g gs ih =>
      intro W W' hl h9 hW
      dsimp only [run, List.map_cons, List.foldl_cons]
      apply ih
      · rw [step_len, step_len, hl]
      · rw [step_len]; omega
      · have hv : g.op (W'.getD (perm g.left) false) (W'.getD (perm g.right) false) =
            g.op (W.getD g.left false) (W.getD g.right false) := by
          rw [hW g.left, hW g.right]
        intro j
        dsimp only [step]
        rw [hv]
        generalize g.op (W.getD g.left false) (W.getD g.right false) = v
        by_cases hj : j < W.length
        · have hj' : perm j < W'.length := by rw [← hl]; exact perm_lt W.length j h9 hj
          rw [List.getD_append _ _ _ _ hj', List.getD_append _ _ _ _ hj]
          exact hW j
        · rw [perm_ge9 j (by omega)]
          by_cases hj2 : j = W.length
          · subst hj2
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hl,
              List.getElem?_append_right (le_refl _), ← hl,
              List.getElem?_append_right (le_refl _)]
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hcover : ∀ (l r : Fin 10) (a b : Bool),
      l.val < r.val →
      ¬ (l.val = 0 ∧ r.val = 4 ∧ a = false ∧ b = false) →
      ¬ (l.val = 0 ∧ r.val = 9) →
      ¬ (l.val = 4 ∧ r.val = 9) →
      ((canonList a b).contains (10 * l.val + r.val) ||
        if perm l.val ≤ perm r.val
        then (canonList a b).contains (10 * perm l.val + perm r.val)
        else (canonList b a).contains (10 * perm r.val + perm l.val)) = true := by
    decide
  have hNonDeg : ∀ (D : PEqualNP.MetaComplexity.BinaryCircuit)
      (g0 : PEqualNP.MetaComplexity.BinaryGate) (a b : Bool),
      D.size = 13 → D.output = 23 →
      (∀ (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), D.gates[j]? = some g →
        g.left ≤ g.right ∧ g.right < 11 + j ∧
        ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      D.gates[0]? = some g0 →
      g0.op = (fun u v : Bool => u == a && v == b) →
      g0.left < g0.right → g0.right < 10 →
      ¬ (g0.left = 0 ∧ g0.right = 4 ∧ a = false ∧ b = false) →
      ¬ (g0.left = 0 ∧ g0.right = 9) →
      ¬ (g0.left = 4 ∧ g0.right = 9) →
      (∀ x : Fin 9 → Bool, D.eval (inp x) = F x) → False := by
    intro D g0 a b hsz hout hg hg0 hop hlt hr10 hno04 hno09 hno49 hev
    have hc := Bool.or_eq_true_iff.mp
      (hcover ⟨g0.left, by omega⟩ ⟨g0.right, hr10⟩ a b hlt hno04 hno09 hno49)
    rcases hc with hmem | hmem
    · refine hCanon D a b hsz hout hg ?_ hev
      intro g hg'
      rw [hg0] at hg'
      cases hg'
      exact ⟨hop, List.contains_iff_mem.mp hmem⟩
    · let ren := fun g : PEqualNP.MetaComplexity.BinaryGate =>
        ({ op := g.op, left := perm g.left, right := perm g.right } : PEqualNP.MetaComplexity.BinaryGate)
      let D' : PEqualNP.MetaComplexity.BinaryCircuit :=
        { gates := (D.gates.map ren).map flipGate, output := 23 }
      have hsz' : D'.size = 13 := by
        rw [hszB] at hsz ⊢; simp [D', hsz]
      have hg' : ∀ (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), D'.gates[j]? = some g →
          g.left ≤ g.right ∧ g.right < 11 + j ∧
          ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d := by
        intro j g hgj
        simp only [D', List.getElem?_map] at hgj
        cases hd : D.gates[j]? with
        | none => rw [hd] at hgj; simp at hgj
        | some gj =>
          rw [hd] at hgj
          simp only [Option.map_some, Option.some.injEq] at hgj
          subst hgj
          obtain ⟨hjl, hjr, hjop⟩ := hg j gj hd
          exact flipGate_props (11 + j) (ren gj)
            (perm_lt (11 + j) gj.left (by omega) (by omega))
            (perm_lt (11 + j) gj.right (by omega) hjr) hjop
      have hev' : ∀ y : Fin 9 → Bool, D'.eval (inp y) = F y := by
        intro y
        let y' : Fin 9 → Bool := fun i => y (![0, 5, 8, 3, 4, 1, 7, 6, 2] i)
        have hf := hev y'
        rw [hevB] at hf ⊢
        dsimp only [D']
        change (run ((D.gates.map ren).map flipGate) (inp y)).getD 23 false = F y
        rw [run_flip]
        have hp23 : perm 23 = 23 := perm_ge9 23 (by omega)
        rw [← hp23]
        have e := hpre D.gates (inp y') (inp y) (by simp [inp]) (by simp [inp]) ?_ 23
        · rw [e, ← hout]
          change (run D.gates (inp y')).getD D.output false = F y' at hf
          rw [hf]
          exact hF_perm (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
        · intro j
          by_cases hj : j < 11
          · interval_cases j <;> rfl
          · rw [perm_ge9 j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp [inp]; omega),
              List.getElem?_eq_none (by simp [inp]; omega)]
      by_cases hp : perm g0.left ≤ perm g0.right
      · simp only [hp, ↓reduceIte] at hmem
        refine hCanon D' a b hsz' rfl hg' ?_ hev'
        intro g h0
        simp only [D', List.getElem?_map, hg0, Option.map_some, Option.some.injEq] at h0
        subst h0
        simp only [flipGate, ren, hp, ↓reduceIte]
        exact ⟨hop, List.contains_iff_mem.mp hmem⟩
      · simp only [hp, ↓reduceIte] at hmem
        refine hCanon D' b a hsz' rfl hg' ?_ hev'
        intro g h0
        simp only [D', List.getElem?_map, hg0, Option.map_some, Option.some.injEq] at h0
        subst h0
        simp only [flipGate, ren, hp, ↓reduceIte]
        refine ⟨?_, List.contains_iff_mem.mp hmem⟩
        funext u v
        rw [hop]
        exact Bool.and_comm _ _
  have hDeg : ∀ (tail : List PEqualNP.MetaComplexity.BinaryGate)
      (g0 : PEqualNP.MetaComplexity.BinaryGate) (k : ℕ) (p : Bool),
      tail.length = 12 → k < 11 →
      (∀ (m : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), tail[m]? = some g →
        g.left < 12 + m ∧ g.right < 12 + m ∧
        ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) →
      (∀ x : Fin 9 → Bool,
        g0.op ((inp x).getD g0.left false) ((inp x).getD g0.right false) =
          ((inp x).getD k false == p)) →
      (∀ x : Fin 9 → Bool, (run (g0 :: tail) (inp x)).getD 23 false = F x) → False := by
    intro tail g0 k p hlen hk htail hval hev
    let rew := fun g : PEqualNP.MetaComplexity.BinaryGate =>
      flipGate {
        op := fun u v =>
          g.op (if g.left = 11 then u == p else u) (if g.right = 11 then v == p else v),
        left := if g.left = 11 then k else g.left,
        right := if g.right = 11 then k else g.right }
    let g0c : PEqualNP.MetaComplexity.BinaryGate :=
      { op := fun u v : Bool => u == true && v == true, left := 0, right := 1 }
    let D : PEqualNP.MetaComplexity.BinaryCircuit :=
      { gates := g0c :: tail.map rew, output := 23 }
    have hsim : ∀ (rs : List PEqualNP.MetaComplexity.BinaryGate) (s1 s2 : List Bool),
        s1.length = s2.length → 12 ≤ s1.length →
        s1.getD 11 false = (s1.getD k false == p) →
        (∀ i : ℕ, i ≠ 11 → s2.getD i false = s1.getD i false) →
        ∀ i : ℕ, i ≠ 11 → (run (rs.map rew) s2).getD i false = (run rs s1).getD i false := by
      intro rs
      induction rs with
      | nil => intro s1 s2 _ _ _ hs i hi; exact hs i hi
      | cons g rs ih =>
        intro s1 s2 hsl h12 hs11 hs
        change ∀ i : ℕ, i ≠ 11 →
          (run (rs.map rew) (step s2 (rew g))).getD i false = (run rs (step s1 g)).getD i false
        have hstep_rew : step s2 (rew g) =
            s2 ++ [g.op (s1.getD g.left false) (s1.getD g.right false)] := by
          dsimp only [rew]
          rw [step_flip]
          dsimp only [step]
          have hl_eq : (if g.left = 11
              then s2.getD (if g.left = 11 then k else g.left) false == p
              else s2.getD (if g.left = 11 then k else g.left) false) = s1.getD g.left false := by
            by_cases hgl : g.left = 11
            · simp only [hgl, ↓reduceIte]; rw [hs k (by omega)]; exact hs11.symm
            · simp only [hgl, ↓reduceIte]; exact hs g.left hgl
          have hr_eq : (if g.right = 11
              then s2.getD (if g.right = 11 then k else g.right) false == p
              else s2.getD (if g.right = 11 then k else g.right) false) = s1.getD g.right false := by
            by_cases hgr : g.right = 11
            · simp only [hgr, ↓reduceIte]; rw [hs k (by omega)]; exact hs11.symm
            · simp only [hgr, ↓reduceIte]; exact hs g.right hgr
          rw [hl_eq, hr_eq]
        rw [hstep_rew]
        apply ih
        · simp [step, hsl]
        · rw [step_len]; omega
        · rw [step_keep s1 g 11 (by omega), step_keep s1 g k (by omega)]
          exact hs11
        · intro i hi
          dsimp only [step]
          generalize g.op (s1.getD g.left false) (s1.getD g.right false) = v
          by_cases hlt : i < s1.length
          · rw [List.getD_append _ _ _ _ (hsl ▸ hlt), List.getD_append _ _ _ _ hlt]
            exact hs i hi
          · by_cases heq : i = s1.length
            · subst heq
              rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hsl,
                List.getElem?_append_right (le_refl _), ← hsl,
                List.getElem?_append_right (le_refl _)]
            · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    have hszD : D.size = 13 := by
      rw [hszB]; simp [D, hlen]
    have hgD : ∀ (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), D.gates[j]? = some g →
        g.left ≤ g.right ∧ g.right < 11 + j ∧
        ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d := by
      intro j g hgj
      cases j with
      | zero =>
        simp only [D, List.getElem?_cons_zero, Option.some.injEq] at hgj
        subst hgj
        exact ⟨by decide, by decide, true, true, rfl⟩
      | succ m =>
        simp only [D, List.getElem?_cons_succ, List.getElem?_map] at hgj
        cases ht : tail[m]? with
        | none => rw [ht] at hgj; simp at hgj
        | some gm =>
          rw [ht] at hgj
          simp only [Option.map_some, Option.some.injEq] at hgj
          subst hgj
          obtain ⟨hml, hmr, c, d, hcd⟩ := htail m gm ht
          refine flipGate_props (11 + (m + 1)) _ ?_ ?_ ?_
          · dsimp only; split_ifs <;> omega
          · dsimp only; split_ifs <;> omega
          · refine ⟨if gm.left = 11 then (p == c) else c,
              if gm.right = 11 then (p == d) else d, ?_⟩
            funext u v
            dsimp only
            rw [hcd]
            dsimp only
            have hl_b : ((if gm.left = 11 then u == p else u) == c) =
                (u == if gm.left = 11 then p == c else c) := by
              split_ifs <;> cases u <;> cases p <;> cases c <;> rfl
            have hr_b : ((if gm.right = 11 then v == p else v) == d) =
                (v == if gm.right = 11 then p == d else d) := by
              split_ifs <;> cases v <;> cases p <;> cases d <;> rfl
            rw [hl_b, hr_b]
    obtain ⟨x, hx⟩ := hTT D hszD rfl hgD (by
      intro g h0
      simp only [D, List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      exact ⟨rfl, by decide⟩)
    apply hx
    rw [hevB]
    dsimp only [D]
    change (run (tail.map rew) (step (inp x) g0c)).getD 23 false = F x
    have heq23 := hsim tail (step (inp x) g0) (step (inp x) g0c)
      (by rw [step_len, step_len])
      (by rw [step_len, inp_len])
      (by
        have h11 : 11 = (inp x).length := (inp_len x).symm
        rw [h11, step_snoc, step_keep (inp x) g0 k (by rw [inp_len]; exact hk)]
        exact hval x)
      (by
        intro i hi
        by_cases hilt : i < 11
        · rw [step_keep (inp x) g0c i (by rw [inp_len]; exact hilt),
            step_keep (inp x) g0 i (by rw [inp_len]; exact hilt)]
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by rw [step_len, inp_len]; omega),
            List.getElem?_eq_none (by rw [step_len, inp_len]; omega)])
      23 (by omega)
    rw [heq23]
    exact hev x
  have hno_wire : ∀ k : Fin 11, ∃ m : Fin 16,
      (inp (fun i => Nat.testBit m.val i.val)).getD k.val false ≠
        F (fun i => Nat.testBit m.val i.val) := by
    decide
  have ho_ge11 : 11 ≤ C0.output := by
    by_contra hlt
    have hlt' : C0.output < 11 := by omega
    obtain ⟨m, hm⟩ := hno_wire ⟨C0.output, hlt'⟩
    let xm : Fin 9 → Bool := fun i => Nat.testBit m.val i.val
    have hx := hC0 xm
    rw [hevB] at hx
    change (run C0.gates (inp xm)).getD C0.output false = F xm at hx
    rw [run_keep C0.gates (inp xm) C0.output (by rw [inp_len]; exact hlt')] at hx
    exact hm hx
  have hC1_ex : ∃ C1 : PEqualNP.MetaComplexity.BinaryCircuit,
      C1.size = 13 ∧ C1.output = 23 ∧
      (∀ (j : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), C1.gates[j]? = some g →
        g.left ≤ g.right ∧ g.right < 11 + j ∧
        ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d) ∧
      (∀ x : Fin 9 → Bool, C1.eval (inp x) = F x) := by
    have hlen0 : C0.gates.length = 13 := by rwa [← hszB]
    by_cases ho23 : C0.output = 23
    · refine ⟨{ gates := C0.gates.map flipGate, output := 23 }, ?_, rfl, ?_, ?_⟩
      · rw [hszB]; simp [hlen0]
      · intro j g hgj
        simp only [List.getElem?_map] at hgj
        cases hc : C0.gates[j]? with
        | none => rw [hc] at hgj; simp at hgj
        | some gj =>
          rw [hc] at hgj
          simp only [Option.map_some, Option.some.injEq] at hgj
          subst hgj
          obtain ⟨hl, hr, hop⟩ := hgates0 j gj hc
          exact flipGate_props (11 + j) gj hl hr hop
      · intro x
        have hx := hC0 x
        rw [hevB] at hx ⊢
        dsimp only
        change (run (C0.gates.map flipGate) (inp x)).getD 23 false = F x
        rw [run_flip, ← ho23]
        exact hx
    · let k := C0.output - 11
      have hk12 : k < 12 := by omega
      have hk_eq : C0.output = 11 + k := by omega
      have hgk_lt : k < C0.gates.length := by omega
      let gk := C0.gates[k]
      have hgk : C0.gates[k]? = some gk := List.getElem?_eq_getElem hgk_lt
      obtain ⟨hgkl, hgkr, hgkop⟩ := hgates0 k gk hgk
      let rawGates := C0.gates.take 12 ++ [gk]
      refine ⟨{ gates := rawGates.map flipGate, output := 23 }, ?_, rfl, ?_, ?_⟩
      · rw [hszB]; simp [rawGates, hlen0]
      · intro j g hgj
        simp only [List.getElem?_map] at hgj
        cases hrw : rawGates[j]? with
        | none => rw [hrw] at hgj; simp at hgj
        | some gj =>
          rw [hrw] at hgj
          simp only [Option.map_some, Option.some.injEq] at hgj
          subst hgj
          have htakelen : (C0.gates.take 12).length = 12 := by simp [hlen0]
          by_cases hj12 : j < 12
          · simp only [rawGates] at hrw
            rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hj12] at hrw
            obtain ⟨hl, hr, hop⟩ := hgates0 j gj hrw
            exact flipGate_props (11 + j) gj hl hr hop
          · simp only [rawGates] at hrw
            rw [List.getElem?_append_right (by omega), htakelen] at hrw
            have hj_eq : j = 12 := by
              by_contra hne
              have : 1 ≤ j - 12 := by omega
              rw [List.getElem?_eq_none (by simp; omega)] at hrw
              simp at hrw
            subst hj_eq
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hrw
            subst hrw
            exact flipGate_props (11 + 12) gk (by omega) (by omega) hgkop
      · intro x
        have hx := hC0 x
        rw [hevB] at hx ⊢
        dsimp only
        change (run (rawGates.map flipGate) (inp x)).getD 23 false = F x
        rw [run_flip]
        have htakelen : (C0.gates.take 12).length = 12 := by simp [hlen0]
        have hraw12 : rawGates[12]? = some gk := by
          simp only [rawGates]
          rw [List.getElem?_append_right (by omega), htakelen, Nat.sub_self]
          rfl
        have h23 : 23 = (inp x).length + 12 := by rw [inp_len]
        rw [h23, run_nth rawGates (inp x) 12 gk hraw12
          (by rw [inp_len]; omega) (by rw [inp_len]; omega)]
        have hsplit : C0.gates = C0.gates.take 12 ++ C0.gates.drop 12 :=
          (List.take_append_drop 12 C0.gates).symm
        have hpref : ∀ i : ℕ, i < 23 →
            (run rawGates (inp x)).getD i false = (run C0.gates (inp x)).getD i false := by
          intro i hi
          have hplen : (run (C0.gates.take 12) (inp x)).length = 23 := by
            rw [run_len, inp_len, htakelen]
          have hr1 : run rawGates (inp x) = run [gk] (run (C0.gates.take 12) (inp x)) := by
            simp only [run, rawGates, List.foldl_append]
          have hr2 : run C0.gates (inp x) =
              run (C0.gates.drop 12) (run (C0.gates.take 12) (inp x)) := by
            conv_lhs => rw [hsplit]
            simp only [run, List.foldl_append]
          rw [hr1, hr2,
            run_keep [gk] (run (C0.gates.take 12) (inp x)) i (by omega),
            run_keep (C0.gates.drop 12) (run (C0.gates.take 12) (inp x)) i (by omega)]
        rw [hpref gk.left (by omega), hpref gk.right (by omega)]
        have hout_eq : C0.output = (inp x).length + k := by rw [inp_len]; exact hk_eq
        change (run C0.gates (inp x)).getD C0.output false = F x at hx
        rw [hout_eq, run_nth C0.gates (inp x) k gk hgk
          (by rw [inp_len]; exact hgkl) (by rw [inp_len]; exact hgkr)] at hx
        exact hx
  obtain ⟨C1, hsz1, hout1, hg1, hev1⟩ := hC1_ex
  have hlen1 : C1.gates.length = 13 := by rwa [← hszB]
  cases hgs : C1.gates with
  | nil => rw [hgs] at hlen1; simp at hlen1
  | cons g0 tail =>
    have htail_len : tail.length = 12 := by rw [hgs] at hlen1; simp at hlen1; omega
    have hg0_some : C1.gates[0]? = some g0 := by simp [hgs]
    obtain ⟨hg0le, hg0r, a, b, hop0⟩ := hg1 0 g0 hg0_some
    have htail_g : ∀ (m : ℕ) (g : PEqualNP.MetaComplexity.BinaryGate), tail[m]? = some g →
        g.left < 12 + m ∧ g.right < 12 + m ∧
        ∃ c d : Bool, g.op = fun u v : Bool => u == c && v == d := by
      intro m g htm
      have h1m : C1.gates[m + 1]? = some g := by simp [hgs, htm]
      obtain ⟨hle, hr, hop⟩ := hg1 (m + 1) g h1m
      exact ⟨by omega, by omega, hop⟩
    have hev_run : ∀ x : Fin 9 → Bool, (run (g0 :: tail) (inp x)).getD 23 false = F x := by
      intro x
      have hx := hev1 x
      rw [hevB, hout1, hgs] at hx
      exact hx
    have hRepl : ∀ (g0' : PEqualNP.MetaComplexity.BinaryGate) (a' b' : Bool),
        g0'.op = (fun u v : Bool => u == a' && v == b') →
        g0'.left < g0'.right → g0'.right < 10 →
        ¬ (g0'.left = 0 ∧ g0'.right = 4 ∧ a' = false ∧ b' = false) →
        ¬ (g0'.left = 0 ∧ g0'.right = 9) →
        ¬ (g0'.left = 4 ∧ g0'.right = 9) →
        (∀ x : Fin 9 → Bool,
          g0'.op ((inp x).getD g0'.left false) ((inp x).getD g0'.right false) =
            g0.op ((inp x).getD g0.left false) ((inp x).getD g0.right false)) → False := by
      intro g0' a' b' hop' hlt' hr10' h04' h09' h49' hsame
      let D : PEqualNP.MetaComplexity.BinaryCircuit := { gates := g0' :: tail, output := 23 }
      refine hNonDeg D g0' a' b' ?_ rfl ?_ (by simp [D]) hop' hlt' hr10' h04' h09' h49' ?_
      · rw [hszB]; simp [D, htail_len]
      · intro j g hgj
        cases j with
        | zero =>
          simp only [D, List.getElem?_cons_zero, Option.some.injEq] at hgj
          subst hgj
          exact ⟨by omega, by omega, a', b', hop'⟩
        | succ m =>
          simp only [D, List.getElem?_cons_succ] at hgj
          have h1m : C1.gates[m + 1]? = some g := by simp [hgs, hgj]
          exact hg1 (m + 1) g h1m
      · intro x
        rw [hevB]
        dsimp only [D]
        change (run tail (step (inp x) g0')).getD 23 false = F x
        have hs : step (inp x) g0' = step (inp x) g0 := by
          dsimp only [step]; rw [hsame x]
        rw [hs]
        exact hev_run x
    by_cases hsame_lr : g0.left = g0.right
    · by_cases hab : a = b
      · refine hDeg tail g0 g0.left a htail_len (by omega) htail_g ?_ hev_run
        intro x
        rw [hop0, ← hsame_lr, ← hab]
        dsimp only
        cases ((inp x).getD g0.left false == a) <;> rfl
      · refine hDeg tail g0 10 true htail_len (by omega) htail_g ?_ hev_run
        intro x
        rw [hop0, ← hsame_lr, inp_10]
        dsimp only
        cases hd : (inp x).getD g0.left false <;> cases a <;> cases b <;>
          first | rfl | exact absurd rfl hab
    · by_cases hr10 : g0.right = 10
      · cases b
        · refine hDeg tail g0 g0.left a htail_len (by omega) htail_g ?_ hev_run
          intro x
          rw [hop0, hr10, inp_10]
          dsimp only
          cases ((inp x).getD g0.left false == a) <;> rfl
        · refine hDeg tail g0 10 true htail_len (by omega) htail_g ?_ hev_run
          intro x
          rw [hop0, hr10, inp_10]
          dsimp only
          cases ((inp x).getD g0.left false == a) <;> rfl
      · have hlt_lr : g0.left < g0.right := by omega
        have hlt_r10 : g0.right < 10 := by omega
        by_cases h04 : g0.left = 0 ∧ g0.right = 4 ∧ a = false ∧ b = false
        · rcases h04 with ⟨hl0, hr4, ha0, hb0⟩
          refine hDeg tail g0 9 false htail_len (by omega) htail_g ?_ hev_run
          intro x
          rw [hop0, hl0, hr4, ha0, hb0, inp_0, inp_4, inp_9]
          dsimp only
          cases (x 0) <;> cases (x 4) <;> rfl
        · by_cases h09 : g0.left = 0 ∧ g0.right = 9
          · rcases h09 with ⟨hl0, hr9⟩
            cases a <;> cases b
            · refine hDeg tail g0 9 false htail_len (by omega) htail_g ?_ hev_run
              intro x
              rw [hop0, hl0, hr9, inp_0, inp_9]
              dsimp only
              cases (x 0) <;> cases (x 4) <;> rfl
            · refine hRepl { op := fun u v : Bool => u == false && v == true, left := 0, right := 4 }
                false true rfl (by decide) (by decide) (by decide) (by decide) (by decide) ?_
              intro x
              rw [hop0, hl0, hr9]
              dsimp only
              rw [inp_0, inp_4, inp_9]
              cases (x 0) <;> cases (x 4) <;> rfl
            · refine hDeg tail g0 10 true htail_len (by omega) htail_g ?_ hev_run
              intro x
              rw [hop0, hl0, hr9, inp_0, inp_9, inp_10]
              dsimp only
              cases (x 0) <;> cases (x 4) <;> rfl
            · refine hDeg tail g0 0 true htail_len (by omega) htail_g ?_ hev_run
              intro x
              rw [hop0, hl0, hr9, inp_0, inp_9]
              dsimp only
              cases (x 0) <;> cases (x 4) <;> rfl
          · by_cases h49 : g0.left = 4 ∧ g0.right = 9
            · rcases h49 with ⟨hl4, hr9⟩
              cases a <;> cases b
              · refine hDeg tail g0 9 false htail_len (by omega) htail_g ?_ hev_run
                intro x
                rw [hop0, hl4, hr9, inp_4, inp_9]
                dsimp only
                cases (x 0) <;> cases (x 4) <;> rfl
              · refine hRepl { op := fun u v : Bool => u == true && v == false, left := 0, right := 4 }
                  true false rfl (by decide) (by decide) (by decide) (by decide) (by decide) ?_
                intro x
                rw [hop0, hl4, hr9]
                dsimp only
                rw [inp_0, inp_4, inp_9]
                cases (x 0) <;> cases (x 4) <;> rfl
              · refine hDeg tail g0 10 true htail_len (by omega) htail_g ?_ hev_run
                intro x
                rw [hop0, hl4, hr9, inp_4, inp_9, inp_10]
                dsimp only
                cases (x 0) <;> cases (x 4) <;> rfl
              · refine hDeg tail g0 4 true htail_len (by omega) htail_g ?_ hev_run
                intro x
                rw [hop0, hl4, hr9, inp_4, inp_9]
                dsimp only
                cases (x 0) <;> cases (x 4) <;> rfl
            · exact hNonDeg C1 g0 a b hsz1 hout1 hg1 hg0_some hop0 hlt_lr hlt_r10 h04 h09 h49 hev1
