import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18193_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- One evaluation step: the gate adds one wire. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (L : List Bool) (a : Bool) (w : ℕ) :
    (L ++ [a]).getD w false = if w = L.length then a else L.getD w false := by
  rcases lt_trichotomy w L.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, Nat.ne_of_lt h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · have h1 : ¬ w = L.length := by omega
    have h2 : L.length ≤ w := by omega
    have h3 : (L ++ [a]).length ≤ w := by simp; omega
    simp [List.getD_eq_getElem?_getD, h1, List.getElem?_eq_none h2, List.getElem?_eq_none h3]

theorem oneEach_getD (N : ℕ) (u v : Fin N) (i : ℕ) :
    (oneEach u v).getD i false = (decide (i = u.val) || decide (i = N + v.val)) := by
  unfold oneEach
  by_cases h : i < N
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
    have h1 : i ≠ N + v.val := by omega
    simp [h, h1, Fin.ext_iff]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using h)]
    have h1 : i ≠ u.val := by have := u.isLt; omega
    by_cases h2 : i - N < N
    · simp [h2, h1, Fin.ext_iff]; omega
    · have h3 : i ≠ N + v.val := by have := v.isLt; omega
      simp [h2, h1, h3]

/-- The new number of a wire: the right copy of the inputs is laid onto the left copy. -/
def phi (n w : ℕ) : ℕ := if w < n then w else w - n

/-- The gate reading the renumbered wires. -/
def fold (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi n)⟩

/-- AND and OR gates keep the order of values. -/
theorem hop (o : GateOp) (l : List ℕ) (f g : ℕ → Bool) (ho : o = GateOp.and ∨ o = GateOp.or)
    (h : ∀ i, f i = true → g i = true) : o.eval (l.map f) = true → o.eval (l.map g) = true := by
  rcases ho with rfl | rfl
  · intro H
    simp [GateOp.eval] at H ⊢
    exact fun i hi => h i (H i hi)
  · intro H
    simp [GateOp.eval] at H ⊢
    obtain ⟨i, hi, H⟩ := H
    exact ⟨i, hi, h i H⟩

/-- A relation between the values of a wire and of its renumbered wire, kept by the gates,
holds on all wires at the end if it holds on the inputs. -/
theorem sim (R : Bool → Bool → Prop)
    (hR : ∀ (o : GateOp) (l : List ℕ) (f g : ℕ → Bool), (o = GateOp.and ∨ o = GateOp.or) →
      (∀ i, R (f i) (g i)) → R (o.eval (l.map f)) (o.eval (l.map g)))
    (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (A B : List Bool) (t : ℕ), A.length = 2 * n + t → B.length = n + t →
      (∀ w, R (A.getD w false) (B.getD (phi n w) false)) →
      ∀ w, R ((gs.foldl step A).getD w false)
        (((gs.map (fold n)).foldl step B).getD (phi n w) false) := by
  induction gs with
  | nil => intro A B t _ _ h; simpa using h
  | cons g gs ih =>
    intro A B t hA hB h
    simp only [List.foldl_cons, List.map_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (step A g) (step B (fold n g)) (t + 1)
    · simp [step, hA]; omega
    · simp [step, hB]; omega
    · intro w
      simp only [step, getD_snoc, hA, hB, fold, List.map_map]
      have e : (phi n w = n + t) ↔ (w = 2 * n + t) := by unfold phi; split_ifs <;> omega
      by_cases hw : w = 2 * n + t
      · rw [ite_cond_eq_true _ _ (eq_true hw), ite_cond_eq_true _ _ (eq_true (e.mpr hw))]
        exact hR g.op g.inputs _ _ (hgs g (by simp)) h
      · rw [ite_cond_eq_false _ _ (eq_false hw), ite_cond_eq_false _ _ (eq_false (fun h' => hw (e.mp h')))]
        exact h w

theorem mono_ops (C : Circuit) (hC : Monotone2 C) :
    ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  simpa using (hC g hg).1

/-- The circuit on `n` inputs obtained by reading input `i` for both copies of vertex `i`. -/
def folded (n : ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (fold n), phi n C.output⟩

theorem ofFn_getD (n : ℕ) (x : Fin n → Bool) (w : ℕ) :
    (List.ofFn x).getD w false = true ↔ ∃ h : w < n, x ⟨w, h⟩ = true := by
  by_cases h : w < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem phi_cases (n w : ℕ) (i : ℕ) (hi : i < n) : phi n w = i ↔ (w = i ∨ w = n + i) := by
  unfold phi; split_ifs <;> omega

theorem main_thm (n s : ℕ)
    (h : RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (2 ≤ (List.ofFn x).count true) := by
  obtain ⟨C, hC, hs, hrep⟩ := h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨⟨[], 0⟩, ?_, ?_, ?_⟩
    · intro g hg; simp at hg
    · simp [Circuit.size]
    · intro x; simp [Circuit.eval, Circuit.wires]
  refine ⟨folded n C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [folded, List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    simpa [fold] using hC g' hg'
  · simpa [folded, Circuit.size] using hs
  intro x
  have hcount : (List.ofFn x).count true = (Finset.univ.filter (fun i => x i = true)).card := by
    rw [List.count, List.countP_ofFn]
    congr 1
  have hops := mono_ops C hC
  by_cases hp : ∃ i j : Fin n, i ≠ j ∧ x i = true ∧ x j = true
  · obtain ⟨i, j, hij, hi, hj⟩ := hp
    have h2 : 2 ≤ (List.ofFn x).count true := by
      rw [hcount]
      exact Finset.one_lt_card.mpr ⟨i, by simp [hi], j, by simp [hj], hij⟩
    have key := sim (fun p q => p = true → q = true)
      (fun o l f g ho hfg => hop o l f g ho hfg) n C.gates hops (oneEach i j) (List.ofFn x) 0
      (by simp [oneEach]; omega) (by simp)
      (by
        intro w hw
        rw [oneEach_getD] at hw
        rw [ofFn_getD]
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hw
        rcases hw with hw | hw
        · have e : phi n w = i.val := (phi_cases n w i.val i.isLt).mpr (Or.inl hw)
          exact ⟨by rw [e]; exact i.isLt, by simpa [e] using hi⟩
        · have e : phi n w = j.val := (phi_cases n w j.val j.isLt).mpr (Or.inr hw)
          exact ⟨by rw [e]; exact j.isLt, by simpa [e] using hj⟩)
      C.output
    have h1 : C.eval (oneEach i j) = true := by rw [hrep i j]; simpa using hij
    have h3 : (folded n C).eval (List.ofFn x) = true := key h1
    rw [h3]; simpa using h2
  · have hle : ¬ 2 ≤ (List.ofFn x).count true := by
      rw [hcount]
      intro h2
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
      exact hp ⟨a, b, hab, by simpa using ha, by simpa using hb⟩
    obtain ⟨i, hi⟩ : ∃ i : Fin n, ∀ j : Fin n, x j = true → j = i := by
      by_cases he : ∃ j : Fin n, x j = true
      · obtain ⟨i, hi⟩ := he
        refine ⟨i, fun j hj => ?_⟩
        by_contra hne
        exact hp ⟨j, i, hne, hj, hi⟩
      · exact ⟨⟨0, hn⟩, fun j hj => (he ⟨j, hj⟩).elim⟩
    have key := sim (fun p q => q = true → p = true)
      (fun o l f g ho hfg => hop o l g f ho hfg) n C.gates hops (oneEach i i) (List.ofFn x) 0
      (by simp [oneEach]; omega) (by simp)
      (by
        intro w hw
        rw [ofFn_getD] at hw
        obtain ⟨hlt, hx⟩ := hw
        have e : phi n w = i.val := by simpa [Fin.ext_iff] using hi ⟨phi n w, hlt⟩ hx
        rw [oneEach_getD]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact (phi_cases n w i.val i.isLt).mp e)
      C.output
    have h1 : C.eval (oneEach i i) = false := by rw [hrep i i]; simp
    have h3 : (folded n C).eval (List.ofFn x) = false := by
      by_contra hne
      have h4 : (folded n C).eval (List.ofFn x) = true := by simpa using hne
      have : C.eval (oneEach i i) = true := key h4
      rw [h1] at this; exact Bool.noConfusion this
    rw [h3]; simpa using hle

end PEqualNP.Outside.L_meta_18193_aux

theorem PEqualNP.Outside.L_meta_18193 : ∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (2 ≤ (List.ofFn x).count true) := by
  intro n s h
  exact PEqualNP.Outside.L_meta_18193_aux.main_thm n s h
