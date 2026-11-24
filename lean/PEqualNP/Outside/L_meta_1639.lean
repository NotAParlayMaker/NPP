import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1639

open PEqualNP.CircuitLowerBounds

-- One evaluation loop over the gates, written so its wire list can be indexed.
def run {α : Type} (d : α) (ev : Gate → List α → α) (L : List Gate) (init : List α) : List α :=
  L.foldl (fun acc g => acc ++ [ev g (g.inputs.map fun i => acc.getD i d)]) init

lemma run_cons {α : Type} (d : α) (ev : Gate → List α → α) (g : Gate) (L : List Gate)
    (init : List α) :
    run d ev (g :: L) init = run d ev L (init ++ [ev g (g.inputs.map fun i => init.getD i d)]) :=
  rfl

lemma run_length {α : Type} (d : α) (ev : Gate → List α → α) (L : List Gate) (init : List α) :
    (run d ev L init).length = init.length + L.length := by
  induction L generalizing init with
  | nil => rfl
  | cons g L ih =>
    rw [run_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma run_snoc {α : Type} (d : α) (ev : Gate → List α → α) (L : List Gate) (g : Gate)
    (init : List α) :
    run d ev (L ++ [g]) init =
      run d ev L init ++ [ev g (g.inputs.map fun i => (run d ev L init).getD i d)] := by
  unfold run
  rw [List.foldl_append]
  rfl

lemma getD_lt {α : Type} (A B : List α) (d : α) (i : ℕ) (h : i < A.length) :
    (A ++ B).getD i d = A.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_len {α : Type} (A : List α) (b d : α) (i : ℕ) (h : i = A.length) :
    (A ++ [b]).getD i d = b := by
  subst h
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

lemma getD_big {α : Type} (A : List α) (d : α) (i : ℕ) (h : A.length ≤ i) : A.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma run_getD_lt {α : Type} (d : α) (ev : Gate → List α → α) (L : List Gate) (init : List α)
    (i : ℕ) (h : i < init.length) : (run d ev L init).getD i d = init.getD i d := by
  induction L generalizing init with
  | nil => rfl
  | cons g L ih =>
    rw [run_cons, ih _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
      getD_lt _ _ _ _ h]

lemma run_getD_big {α : Type} (d : α) (ev : Gate → List α → α) (L : List Gate) (init : List α)
    (i : ℕ) (h : init.length + L.length ≤ i) : (run d ev L init).getD i d = d :=
  getD_big _ _ _ (by rw [run_length]; exact h)

lemma run_gate_if {α : Type} (d : α) (ev : Gate → List α → α) (L : List Gate) (init : List α)
    (j : ℕ) (g : Gate) (hj : L[j]? = some g) :
    (run d ev L init).getD (init.length + j) d =
      ev g (g.inputs.map fun i =>
        if i < init.length + j then (run d ev L init).getD i d else d) := by
  induction L generalizing init j with
  | nil => simp at hj
  | cons g0 L ih =>
    rw [run_cons]
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, run_getD_lt _ _ _ _ _
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
        getD_len _ _ _ _ rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length
      · rw [if_pos hi, run_getD_lt _ _ _ _ _
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          getD_lt _ _ _ _ hi]
      · rw [if_neg hi, getD_big _ _ _ (by omega)]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have h := ih (init ++ [ev g0 (g0.inputs.map fun i => init.getD i d)]) j hj
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      have e : init.length + (j + 1) = init.length + (0 + 1) + j := by omega
      rw [e]
      exact h

lemma run_gate {α : Type} (d : α) (ev : Gate → List α → α) (L : List Gate) (init : List α)
    (j : ℕ) (g : Gate) (hj : L[j]? = some g)
    (hin : ∀ i ∈ g.inputs, i < init.length + j ∨ (run d ev L init).getD i d = d) :
    (run d ev L init).getD (init.length + j) d =
      ev g (g.inputs.map fun i => (run d ev L init).getD i d) := by
  rw [run_gate_if d ev L init j g hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rcases hin i hi with h | h
  · rw [if_pos h]
  · by_cases h' : i < init.length + j
    · rw [if_pos h']
    · rw [if_neg h', h]


-- Truth-value evaluator: the circuit's own wire list is this fold.
def evB (g : Gate) (l : List Bool) : Bool := g.op.eval l

lemma eval_and (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

lemma eval_or (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

lemma or_all_false (l : List ℕ) (f : ℕ → Bool) (h : GateOp.or.eval (l.map f) = false) :
    ∀ e ∈ l, f e = false := by
  intro e he
  cases hfe : f e with
  | false => rfl
  | true =>
    rw [(eval_or l f).mpr ⟨e, he, hfe⟩] at h
    exact absurd h (by simp)

lemma ofFn_getD (N : ℕ) (f : Fin N → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < N then f ⟨i, h⟩ else false := by
  by_cases h : i < N
  · rw [dif_pos h, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact h)]
    simp
  · rw [dif_neg h]
    exact getD_big _ _ _ (by rw [List.length_ofFn]; omega)

lemma inp (N : ℕ) (f : Fin N → Bool) (gates : List Gate) (p : Fin N) :
    (run false evB gates (List.ofFn f)).getD (p : ℕ) false = f p := by
  rw [run_getD_lt _ _ _ _ _ (by rw [List.length_ofFn]; exact p.2), ofFn_getD, dif_pos p.2]

-- An OR gate whose wire is false has all its inputs false.
lemma or_false (N : ℕ) (gates : List Gate) (x : List Bool) (hN : x.length = N)
    (i : Fin gates.length)
    (hin : ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (ho : (gates.get i).op = GateOp.or)
    (hf : (run false evB gates x).getD (N + (i : ℕ)) false = false) :
    ∀ e ∈ (gates.get i).inputs, (run false evB gates x).getD e false = false := by
  subst hN
  have hg := run_gate false evB gates x i (gates.get i) (by simp)
    (fun w hw => Or.inl (hin w hw))
  rw [hg] at hf
  unfold evB at hf
  rw [ho] at hf
  exact or_all_false _ _ hf

-- AND/OR circuits are monotone in the input, wire by wire.
lemma mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hl : a.length = b.length)
    (h : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (run false evB gs a).getD i false = true → (run false evB gs b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    rw [run_cons, run_cons]
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
    · simp only [List.length_append, List.length_cons, List.length_nil, hl]
    · intro i hi
      by_cases hia : i < a.length
      · rw [getD_lt _ _ _ _ hia] at hi
        rw [getD_lt _ _ _ _ (hl ▸ hia)]
        exact h i hi
      · by_cases hie : i = a.length
        · rw [getD_len _ _ _ _ hie] at hi
          rw [getD_len _ _ _ _ (hl ▸ hie)]
          unfold evB at hi ⊢
          rcases hm g List.mem_cons_self with ho | ho
          · rw [ho] at hi ⊢
            rw [eval_and] at hi ⊢
            intro k hk
            exact h k (hi k hk)
          · rw [ho] at hi ⊢
            rw [eval_or] at hi ⊢
            obtain ⟨k, hk, hk'⟩ := hi
            exact ⟨k, hk, h k hk'⟩
        · rw [getD_big _ _ _ (by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega)] at hi
          exact absurd hi (by simp)

lemma main (N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N))
    (hT0 : T0 ⊆ L i0) (gates : List Gate) (u : ℕ)
    (hm : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hin : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (he0 : (run false evB gates (List.ofFn (fun v : Fin N => decide (v ∉ L i0)))).getD u false
      = false)
    (t y : Fin N)
    (het : (run false evB gates (List.ofFn (fun v : Fin N => decide (v ∉ L t)))).getD u false
      = false)
    (hy : L t ∩ L i0 = {y}) :
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S →
        (gates.get i).op = GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (p : ℕ) ∈ S) → p = y) ∧
    (y ∉ T0 → ∀ x ∈ T0,
      (run false evB gates (List.ofFn (fun v : Fin N => decide (v = x)))).getD u false = false) := by
  constructor
  · intro p hp
    have hS := hp {w | (run false evB gates
        (List.ofFn (fun v : Fin N => decide (v ∉ L i0)))).getD w false = false ∧
      (run false evB gates (List.ofFn (fun v : Fin N => decide (v ∉ L t)))).getD w false = false}
      (Set.mem_setOf_eq ▸ ⟨he0, het⟩) (by
        intro i hi ho e hee
        rw [Set.mem_setOf_eq] at hi ⊢
        exact ⟨or_false N gates _ (List.length_ofFn) i (hin i) ho hi.1 e hee,
          or_false N gates _ (List.length_ofFn) i (hin i) ho hi.2 e hee⟩)
    rw [Set.mem_setOf_eq, inp, inp] at hS
    obtain ⟨ha, hb⟩ := hS
    have h0 : p ∈ L i0 := by simpa using ha
    have h1 : p ∈ L t := by simpa using hb
    have hmem : p ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨h1, h0⟩
    rw [hy] at hmem
    exact Finset.mem_singleton.mp hmem
  · intro hyT x hx
    cases hc : (run false evB gates (List.ofFn (fun v : Fin N => decide (v = x)))).getD u false with
    | false => rfl
    | true =>
      have hb := mono gates (fun g hg => (hm g hg).1)
        (List.ofFn (fun v : Fin N => decide (v = x)))
        (List.ofFn (fun v : Fin N => decide (v ∉ L t)))
        (by rw [List.length_ofFn, List.length_ofFn])
        (by
          intro i hi
          rw [ofFn_getD] at hi ⊢
          by_cases h : i < N
          · rw [dif_pos h] at hi ⊢
            have hix : (⟨i, h⟩ : Fin N) = x := by simpa using hi
            have hnt : (⟨i, h⟩ : Fin N) ∉ L t := by
              rw [hix]
              intro hxt
              have hmem : x ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨hxt, hT0 hx⟩
              rw [hy] at hmem
              exact hyT (Finset.mem_singleton.mp hmem ▸ hx)
            simpa using hnt
          · rw [dif_neg h] at hi
            exact absurd hi (by simp))
        u hc
      rw [het] at hb
      exact absurd hb (by simp)

end PEqualNP.Outside.L_meta_1639

theorem PEqualNP.Outside.L_meta_1639 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    ∀ (t : Fin N) (y : Fin N), t ≠ i0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false → L t ∩ L i0 = {y} →
      (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (p : ℕ) ∈ S) → p = y) ∧ (y ∉ T0 → ∀ x ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v = x))) = false) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ hT0 _ gates u hm _ hin he0 t y _ het hy
  exact PEqualNP.Outside.L_meta_1639.main N L i0 T0 hT0 gates u hm hin he0 t y het hy
