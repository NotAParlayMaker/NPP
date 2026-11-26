import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18193

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (L : List Bool) (b : Bool) (j : ℕ) :
    (L ++ [b]).getD j false = if j = L.length then b else L.getD j false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h1 | h1
    · rw [List.getD_append _ _ _ _ h1]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem run (φ : ℕ → ℕ) :
    ∀ (gs : List Gate) (W W' : List Bool),
      (∀ k, k < gs.length → ∀ i, (φ i = W'.length + k ↔ i = W.length + k)) →
      (∀ i, W.getD i false = W'.getD (φ i) false) →
      ∀ i, (gs.foldl step W).getD i false
        = ((gs.map fun g => ({ op := g.op, inputs := g.inputs.map φ } : Gate)).foldl step W').getD (φ i) false := by
  intro gs
  induction gs with
  | nil => intro W W' _ h; simpa using h
  | cons g gs ih =>
    intro W W' hφ h
    simp only [List.foldl_cons, List.map_cons]
    apply ih
    · intro k hk i
      have := hφ (k + 1) (by simp; omega) i
      simp only [step, List.length_append, List.length_singleton]
      constructor
      · intro hi; exact by have := this.1 (by omega); omega
      · intro hi; exact by have := this.2 (by omega); omega
    · intro i
      simp only [step]
      rw [getD_snoc, getD_snoc]
      have hb : g.op.eval (g.inputs.map fun i => W.getD i false)
          = g.op.eval ((g.inputs.map φ).map fun i => W'.getD i false) := by
        rw [List.map_map]; congr 1; apply List.map_congr_left; intro j _; exact h j
      have h0 := hφ 0 (by simp) i
      simp only [Nat.add_zero] at h0
      by_cases hi : i = W.length
      · rw [if_pos hi, if_pos (h0.2 hi)]; exact hb
      · rw [if_neg hi, if_neg (fun h' => hi (h0.1 h'))]; exact h i

theorem eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map]
    intro hx b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact h i (hx (f i) ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    intro hx
    obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hx
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hb⟩

theorem foldl_mono :
    ∀ (gs : List Gate) (w w' : List Bool), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step w').getD i false = true := by
  intro gs
  induction gs with
  | nil => intro w w' _ _ h; simpa using h
  | cons g gs ih =>
    intro w w' hop hl h
    simp only [List.foldl_cons]
    apply ih
    · intro g' hg'; exact hop g' (by simp [hg'])
    · simp [step, hl]
    · intro i hi
      simp only [step, getD_snoc] at hi ⊢
      rw [← hl]
      split_ifs at hi ⊢ with h1
      · exact eval_mono g (hop g (by simp)) _ _ h hi
      · exact h i hi

theorem eval_mono_circuit (C : Circuit) (hC : Monotone2 C) (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    C.eval x = true → C.eval y = true := by
  intro hx
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  exact foldl_mono C.gates x y hop hl h C.output hx

theorem count_one (l : List Bool) : 1 ≤ l.count true ↔ ∃ j, l.getD j false = true := by
  rw [Nat.one_le_iff_ne_zero, Ne, List.count_eq_zero, not_not]
  constructor
  · intro h
    obtain ⟨j, hj, he⟩ := List.getElem_of_mem h
    exact ⟨j, by rw [List.getD_eq_getElem _ _ hj]; exact he⟩
  · rintro ⟨j, hj⟩
    by_cases h : j < l.length
    · rw [List.getD_eq_getElem _ _ h] at hj; rw [← hj]; exact List.getElem_mem h
    · rw [List.getD_eq_default _ _ (by omega)] at hj; exact absurd hj Bool.false_ne_true

theorem count_two : ∀ (l : List Bool), 2 ≤ l.count true ↔
    ∃ i j, i < j ∧ l.getD i false = true ∧ l.getD j false = true := by
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    cases b with
    | true =>
      simp only [List.count_cons_self]
      constructor
      · intro h
        obtain ⟨j, hj⟩ := (count_one l).1 (by omega)
        exact ⟨0, j + 1, by omega, by simp, by simpa using hj⟩
      · rintro ⟨i, j, hij, hi, hj⟩
        have : 1 ≤ l.count true := (count_one l).2 ⟨j - 1, by
          rcases j with _ | j
          · omega
          · simpa using hj⟩
        omega
    | false =>
      rw [List.count_cons_of_ne (by decide), ih]
      constructor
      · rintro ⟨i, j, hij, hi, hj⟩
        exact ⟨i + 1, j + 1, by omega, by simpa using hi, by simpa using hj⟩
      · rintro ⟨i, j, hij, hi, hj⟩
        rcases i with _ | i
        · simp at hi
        · rcases j with _ | j
          · omega
          · exact ⟨i, j, by omega, by simpa using hi, by simpa using hj⟩

theorem getD_ofFn {N : ℕ} (f : Fin N → Bool) (k : ℕ) (hk : k < N) :
    (List.ofFn f).getD k false = f ⟨k, hk⟩ := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem getD_ofFn_ge {N : ℕ} (f : Fin N → Bool) (k : ℕ) (hk : N ≤ k) :
    (List.ofFn f).getD k false = false := by
  rw [List.getD_eq_default _ _ (by simpa using hk)]

theorem getD_double {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x ++ List.ofFn x).getD i false = (List.ofFn x).getD (if i < n then i else i - n) false := by
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

theorem getD_oneEach {n : ℕ} (u v : Fin n) (i : ℕ) :
    (oneEach u v).getD i false = true ↔ (i = u.val ∨ i = n + v.val) := by
  simp only [oneEach]
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h), getD_ofFn _ i h]
    simp [Fin.ext_iff]
    omega
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    by_cases h2 : i - n < n
    · rw [getD_ofFn _ (i - n) h2]
      simp [Fin.ext_iff]
      omega
    · rw [getD_ofFn_ge _ (i - n) (by omega)]
      simp
      omega

theorem main (n s : ℕ) (C : Circuit) (hmono : Monotone2 C) (hs : C.size ≤ s)
    (hR : Represents (fun u v : Fin n => decide (u ≠ v)) C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (2 ≤ (List.ofFn x).count true) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨⟨[], 0⟩, ?_, ?_, ?_⟩
    · intro g hg; simp at hg
    · simp [Circuit.size]
    · intro x
      simp [Circuit.eval, Circuit.wires]
  let φ : ℕ → ℕ := fun i => if i < n then i else i - n
  refine ⟨⟨C.gates.map fun g => ({ op := g.op, inputs := g.inputs.map φ } : Gate), φ C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hmono g0 hg0
    simpa using this
  · simpa [Circuit.size] using hs
  · intro x
    have key : ∀ i, (C.gates.foldl step (List.ofFn x ++ List.ofFn x)).getD i false
        = ((C.gates.map fun g => ({ op := g.op, inputs := g.inputs.map φ } : Gate)).foldl step
            (List.ofFn x)).getD (φ i) false := by
      apply run φ C.gates (List.ofFn x ++ List.ofFn x) (List.ofFn x)
      · intro k _ i
        simp only [List.length_append, List.length_ofFn, φ]
        split_ifs <;> omega
      · intro i
        rw [getD_double]
    have hD : (⟨C.gates.map fun g => ({ op := g.op, inputs := g.inputs.map φ } : Gate), φ C.output⟩ :
        Circuit).eval (List.ofFn x) = C.eval (List.ofFn x ++ List.ofFn x) := by
      simp only [Circuit.eval, wires_eq]
      rw [key]
    rw [hD]
    have hlen : (List.ofFn x ++ List.ofFn x).length = 2 * n := by simp; omega
    have hlen1 : ∀ u v : Fin n, (oneEach u v).length = 2 * n := by
      intro u v; simp [oneEach]; omega
    by_cases h2 : 2 ≤ (List.ofFn x).count true
    · rw [decide_eq_true h2]
      obtain ⟨i, j, hij, hi, hj⟩ := (count_two _).1 h2
      have hjn : j < n := by
        by_contra hc
        rw [getD_ofFn_ge _ j (by omega)] at hj
        exact Bool.false_ne_true hj
      have hu : C.eval (oneEach (⟨i, by omega⟩ : Fin n) ⟨j, hjn⟩) = true := by
        have := hR ⟨i, by omega⟩ ⟨j, hjn⟩
        rw [this]
        simp [Fin.ext_iff]
        omega
      apply eval_mono_circuit C hmono (oneEach (⟨i, by omega⟩ : Fin n) ⟨j, hjn⟩)
        (List.ofFn x ++ List.ofFn x) (by rw [hlen1, hlen]) _ hu
      intro k hk
      rw [getD_oneEach] at hk
      rcases hk with hk | hk
      · rw [hk, getD_double, if_pos (by omega)]; exact hi
      · rw [hk, getD_double, if_neg (by omega), Nat.add_sub_cancel_left]; exact hj
    · rw [decide_eq_false h2]
      classical
      have huniq : ∀ i j, (List.ofFn x).getD i false = true → (List.ofFn x).getD j false = true → i = j := by
        intro i j hi hj
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · exact h2 ((count_two _).2 ⟨i, j, h, hi, hj⟩)
        · exact h2 ((count_two _).2 ⟨j, i, h, hj, hi⟩)
      let i0 : ℕ := if h : ∃ i, (List.ofFn x).getD i false = true then Classical.choose h else 0
      have hi0 : ∀ k, (List.ofFn x).getD k false = true → k = i0 := by
        intro k hk
        have hex : ∃ i, (List.ofFn x).getD i false = true := ⟨k, hk⟩
        simp only [i0, dif_pos hex]
        exact huniq _ _ hk (Classical.choose_spec hex)
      have hi0n : i0 < n := by
        by_cases hex : ∃ i, (List.ofFn x).getD i false = true
        · obtain ⟨k, hk⟩ := hex
          have := hi0 k hk
          by_contra hc
          rw [getD_ofFn_ge _ k (by omega)] at hk
          exact Bool.false_ne_true hk
        · simp only [i0, dif_neg hex]; exact hn
      have hfalse : C.eval (oneEach (⟨i0, hi0n⟩ : Fin n) ⟨i0, hi0n⟩) = false := by
        have := hR ⟨i0, hi0n⟩ ⟨i0, hi0n⟩
        rw [this]; simp
      by_contra hne
      have ht : C.eval (List.ofFn x ++ List.ofFn x) = true := by simpa using hne
      have hle := eval_mono_circuit C hmono (List.ofFn x ++ List.ofFn x)
        (oneEach (⟨i0, hi0n⟩ : Fin n) ⟨i0, hi0n⟩) (by rw [hlen, hlen1]) (by
        intro k hk
        rw [getD_double] at hk
        rw [getD_oneEach]
        split_ifs at hk with hkn
        · left; exact hi0 k hk
        · right; have := hi0 (k - n) hk; simp only; omega) ht
      rw [hfalse] at hle
      exact Bool.false_ne_true hle

end PEqualNP.Outside.L_meta_18193

theorem PEqualNP.Outside.L_meta_18193 : (∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (2 ≤ (List.ofFn x).count true)) := by
  intro n s h
  obtain ⟨C, hmono, hs, hR⟩ := h
  exact PEqualNP.Outside.L_meta_18193.main n s C hmono hs hR
