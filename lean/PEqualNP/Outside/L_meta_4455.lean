import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4455

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  exact foldl_getD_gate C.gates x j hj

def rs (s : List (Bool ⊕ ℕ)) (i : ℕ) : Bool ⊕ ℕ := s.getD i (Sum.inl false)

def absb (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

def reals (s : List (Bool ⊕ ℕ)) (g : Gate) : List ℕ :=
  g.inputs.filterMap (fun i => (rs s i).getRight?)

def pst (m : ℕ) (s : List (Bool ⊕ ℕ)) (g : Gate) : Bool ⊕ ℕ :=
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => Sum.inl true
    | i :: _ =>
      match rs s i with
      | Sum.inl b => Sum.inl (!b)
      | Sum.inr _ => Sum.inr m
  | _ =>
    if g.inputs.any (fun i => decide (rs s i = Sum.inl (absb g))) then Sum.inl (absb g)
    else if (reals s g).length = 0 then Sum.inl (!absb g)
    else if (reals s g).length = 1 then Sum.inr ((reals s g).headD 0)
    else Sum.inr m

def pgt (m : ℕ) (s : List (Bool ⊕ ℕ)) (g : Gate) : List Gate :=
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => []
    | i :: _ =>
      match rs s i with
      | Sum.inl _ => []
      | Sum.inr k => [⟨GateOp.not, [k]⟩]
  | _ =>
    if g.inputs.any (fun i => decide (rs s i = Sum.inl (absb g))) then []
    else if (reals s g).length ≤ 1 then []
    else [⟨g.op, reals s g⟩]

def eff (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

lemma all_eq (s : List (Bool ⊕ ℕ)) (V W : ℕ → Bool) (l : List ℕ)
    (h : ∀ i ∈ l, (∀ b, rs s i = Sum.inl b → V i = b) ∧ (∀ k, rs s i = Sum.inr k → W k = V i))
    (hn : ∀ i ∈ l, rs s i ≠ Sum.inl false) :
    (l.map V).all id = ((l.filterMap (fun i => (rs s i).getRight?)).map W).all id := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have ih' := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
      (fun j hj => hn j (List.mem_cons_of_mem _ hj))
    have hi := h i (by simp)
    have hni := hn i (by simp)
    cases hs : rs s i with
    | inl b =>
      cases b
      · exact absurd hs hni
      · simp [List.filterMap_cons, hs, hi.1 true hs, ih']
    | inr k =>
      simp [List.filterMap_cons, hs, hi.2 k hs, ih']

lemma any_eq (s : List (Bool ⊕ ℕ)) (V W : ℕ → Bool) (l : List ℕ)
    (h : ∀ i ∈ l, (∀ b, rs s i = Sum.inl b → V i = b) ∧ (∀ k, rs s i = Sum.inr k → W k = V i))
    (hn : ∀ i ∈ l, rs s i ≠ Sum.inl true) :
    (l.map V).any id = ((l.filterMap (fun i => (rs s i).getRight?)).map W).any id := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have ih' := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
      (fun j hj => hn j (List.mem_cons_of_mem _ hj))
    have hi := h i (by simp)
    have hni := hn i (by simp)
    cases hs : rs s i with
    | inl b =>
      cases b
      · simp [List.filterMap_cons, hs, hi.1 false hs, ih']
      · exact absurd hs hni
    | inr k =>
      simp [List.filterMap_cons, hs, hi.2 k hs, ih']

lemma reals_mem (s : List (Bool ⊕ ℕ)) (g : Gate) (k : ℕ) (hk : k ∈ reals s g) :
    ∃ i ∈ g.inputs, rs s i = Sum.inr k := by
  unfold reals at hk
  rw [List.mem_filterMap] at hk
  obtain ⟨i, hi, he⟩ := hk
  refine ⟨i, hi, ?_⟩
  cases h : rs s i with
  | inl b => rw [h] at he; simp at he
  | inr k' => rw [h] at he; simp at he; rw [he]

lemma proc_ok (m : ℕ) (s : List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (V W : ℕ → Bool)
    (h : ∀ i ∈ g.inputs, (∀ b, rs s i = Sum.inl b → V i = b) ∧
      (∀ k, rs s i = Sum.inr k → k < m ∧ W k = V i)) :
    (∀ b, pst m s g = Sum.inl b → g.op.eval (g.inputs.map V) = b) ∧
    (pgt m s g = [] → ∀ k, pst m s g = Sum.inr k → k < m ∧ W k = g.op.eval (g.inputs.map V)) ∧
    (∀ g' ∈ pgt m s g, pst m s g = Sum.inr m ∧
      g'.op.eval (g'.inputs.map W) = g.op.eval (g.inputs.map V) ∧ ∀ i ∈ g'.inputs, i < m) := by
  have hR : ∀ k ∈ reals s g, k < m ∧ ∃ i ∈ g.inputs, rs s i = Sum.inr k ∧ W k = V i := by
    intro k hk
    obtain ⟨i, hi, he⟩ := reals_mem s g k hk
    exact ⟨(h i hi).2 k he |>.1, i, hi, he, (h i hi).2 k he |>.2⟩
  have h' : ∀ i ∈ g.inputs, (∀ b, rs s i = Sum.inl b → V i = b) ∧
      (∀ k, rs s i = Sum.inr k → W k = V i) := fun i hi => ⟨(h i hi).1, fun k hk => ((h i hi).2 k hk).2⟩
  obtain ⟨op, l⟩ := g
  simp only at hop h h' hR
  rcases hop with rfl | rfl | rfl
  · have E : ∀ hn : ∀ i ∈ l, rs s i ≠ Sum.inl false,
        (l.map V).all id = ((reals s ⟨GateOp.and, l⟩).map W).all id :=
      fun hn => all_eq s V W l h' hn
    by_cases hA : l.any (fun i => decide (rs s i = Sum.inl false)) = true
    · have hA' := hA
      simp only [List.any_eq_true, decide_eq_true_eq] at hA'
      obtain ⟨i, hi, hs⟩ := hA'
      have hv := (h i hi).1 false hs
      have hA2 : l.any (fun i => decide (rs s i = Sum.inl (absb ⟨GateOp.and, l⟩))) = true := hA
      simp only [pst, pgt, hA2, ite_true]
      refine ⟨?_, ?_, ?_⟩
      · intro b hb
        simp at hb
        subst hb
        show (l.map V).all id = false
        simp only [List.all_eq_false, List.mem_map]
        exact ⟨V i, ⟨i, hi, rfl⟩, by simp [hv]⟩
      · intro _ k hk; simp at hk
      · intro g' hg'; simp at hg'
    · have hn : ∀ i ∈ l, rs s i ≠ Sum.inl false := by
        intro i hi he
        apply hA
        simp only [List.any_eq_true, decide_eq_true_eq]
        exact ⟨i, hi, he⟩
      have E' := E hn
      have hA2 : l.any (fun i => decide (rs s i = Sum.inl (absb ⟨GateOp.and, l⟩))) = false :=
        Bool.eq_false_iff.mpr hA
      simp only [pst, pgt, hA2]
      rcases hr : reals s ⟨GateOp.and, l⟩ with _ | ⟨k, _ | ⟨k2, t⟩⟩
      · simp [absb, GateOp.eval, E', hr]
      · have hk := hR k (by rw [hr]; simp)
        simp [GateOp.eval, E', hr, hk.1]
      · refine ⟨?_, ?_, ?_⟩
        · intro b hb; simp at hb
        · intro hp; simp at hp
        · intro g' hg'
          simp at hg'
          subst hg'
          refine ⟨by simp, ?_, ?_⟩
          · simp only [GateOp.eval] at E' ⊢
            rw [E', hr]
          · intro i hi
            exact (hR i (by rw [hr]; exact hi)).1
  · have E : ∀ hn : ∀ i ∈ l, rs s i ≠ Sum.inl true,
        (l.map V).any id = ((reals s ⟨GateOp.or, l⟩).map W).any id :=
      fun hn => any_eq s V W l h' hn
    by_cases hA : l.any (fun i => decide (rs s i = Sum.inl true)) = true
    · have hA' := hA
      simp only [List.any_eq_true, decide_eq_true_eq] at hA'
      obtain ⟨i, hi, hs⟩ := hA'
      have hv := (h i hi).1 true hs
      have hA2 : l.any (fun i => decide (rs s i = Sum.inl (absb ⟨GateOp.or, l⟩))) = true := hA
      simp only [pst, pgt, hA2, ite_true]
      refine ⟨?_, ?_, ?_⟩
      · intro b hb
        simp at hb
        subst hb
        show (l.map V).any id = true
        simp only [List.any_eq_true, List.mem_map]
        exact ⟨V i, ⟨i, hi, rfl⟩, by simp [hv]⟩
      · intro _ k hk; simp at hk
      · intro g' hg'; simp at hg'
    · have hn : ∀ i ∈ l, rs s i ≠ Sum.inl true := by
        intro i hi he
        apply hA
        simp only [List.any_eq_true, decide_eq_true_eq]
        exact ⟨i, hi, he⟩
      have E' := E hn
      have hA2 : l.any (fun i => decide (rs s i = Sum.inl (absb ⟨GateOp.or, l⟩))) = false :=
        Bool.eq_false_iff.mpr hA
      simp only [pst, pgt, hA2]
      rcases hr : reals s ⟨GateOp.or, l⟩ with _ | ⟨k, _ | ⟨k2, t⟩⟩
      · simp [absb, GateOp.eval, E', hr]
      · have hk := hR k (by rw [hr]; simp)
        simp [GateOp.eval, E', hr, hk.1]
      · refine ⟨?_, ?_, ?_⟩
        · intro b hb; simp at hb
        · intro hp; simp at hp
        · intro g' hg'
          simp at hg'
          subst hg'
          refine ⟨by simp, ?_, ?_⟩
          · simp only [GateOp.eval] at E' ⊢
            rw [E', hr]
          · intro i hi
            exact (hR i (by rw [hr]; exact hi)).1
  · cases l with
    | nil => simp [pst, pgt, GateOp.eval]
    | cons i t =>
      have hi := h i (by simp)
      cases hs : rs s i with
      | inl b =>
        have hv := hi.1 b hs
        simp [pst, pgt, GateOp.eval, hs, hv]
      | inr k =>
        have hv := hi.2 k hs
        simp [pst, pgt, GateOp.eval, hs, hv.1, hv.2]

lemma pgt_ok (m : ℕ) (s : List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (hl : g.inputs.length ≤ 2) :
    (pgt m s g).length ≤ 1 ∧ ∀ g' ∈ pgt m s g,
      (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  simp only at hop hl
  have hlen : (reals s ⟨op, l⟩).length ≤ 2 := le_trans (List.length_filterMap_le _ _) hl
  rcases hop with rfl | rfl | rfl
  · simp only [pgt]
    split_ifs <;> simp [hlen]
  · simp only [pgt]
    split_ifs <;> simp [hlen]
  · cases l with
    | nil => simp [pgt]
    | cons i t =>
      cases hs : rs s i <;> simp [pgt, hs]

lemma pgt_nil (m : ℕ) (s : List (Bool ⊕ ℕ)) (g : Gate) (v : ℕ)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (hl : g.inputs.length ≤ 2)
    (hv : v ∈ eff g) (hs : rs s v = Sum.inl false) : pgt m s g = [] := by
  obtain ⟨op, l⟩ := g
  simp only at hop hl
  rcases hop with rfl | rfl | rfl
  · simp only [eff] at hv
    have : l.any (fun i => decide (rs s i = Sum.inl (absb ⟨GateOp.and, l⟩))) = true := by
      simp only [List.any_eq_true, decide_eq_true_eq]
      exact ⟨v, hv, by simp [absb, hs]⟩
    simp [pgt, this]
  · simp only [eff] at hv
    have hr : (reals s ⟨GateOp.or, l⟩).length ≤ 1 := by
      rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
      · simp at hv
      · simp only [reals, List.filterMap_cons, List.filterMap_nil]
        cases rs s a <;> simp
      · have e : v = a ∨ v = b := by simpa using hv
        simp only [reals, List.filterMap_cons, List.filterMap_nil]
        rcases e with rfl | rfl
        · cases h2 : rs s b <;> simp_all
        · cases h1 : rs s a <;> simp_all
      · simp at hl
    simp only [pgt]
    split_ifs <;> simp_all
  · rcases l with _ | ⟨a, t⟩
    · simp [pgt]
    · simp [eff] at hv
      subst hv
      simp [pgt, hs]

lemma eval_congr (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (V W : ℕ → Bool) (h : ∀ i ∈ eff g, V i = W i) :
    g.op.eval (g.inputs.map V) = g.op.eval (g.inputs.map W) := by
  obtain ⟨op, l⟩ := g
  simp only at hop
  rcases hop with rfl | rfl | rfl
  · simp only [eff] at h
    simp only [GateOp.eval]
    rw [List.map_congr_left h]
  · simp only [eff] at h
    simp only [GateOp.eval]
    rw [List.map_congr_left h]
  · cases l with
    | nil => rfl
    | cons i t =>
      simp [eff] at h
      simp [GateOp.eval, h]

def step (n : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
  (st.1 ++ [pst (n + st.2.length) st.1 g], st.2 ++ pgt (n + st.2.length) st.1 g)

def init (n v : ℕ) : List (Bool ⊕ ℕ) × List Gate :=
  ((List.range n).map (fun i => if i = v then Sum.inl false else Sum.inr i), [])

def T (n v : ℕ) (gs : List Gate) (j : ℕ) : List (Bool ⊕ ℕ) × List Gate :=
  (gs.take j).foldl (step n) (init n v)

lemma fold_len1 (n : ℕ) (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) :
    (gs.foldl (step n) st).1.length = st.1.length + gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

lemma fold_pre2 (n : ℕ) (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) :
    ∃ r, (gs.foldl (step n) st).2 = st.2 ++ r := by
  induction gs generalizing st with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (step n st g)
    exact ⟨pgt (n + st.2.length) st.1 g ++ r, by rw [List.foldl_cons, hr]; simp [step]⟩

lemma fold_rs (n : ℕ) (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (i : ℕ)
    (hi : i < st.1.length) : rs (gs.foldl (step n) st).1 i = rs st.1 i := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step n st g) (by simp [step]; omega)]
    simp [rs, step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma rs_ge (s : List (Bool ⊕ ℕ)) (i : ℕ) (hi : s.length ≤ i) : rs s i = Sum.inl false := by
  simp [rs, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma fold_mem (n : ℕ) (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (g' : Gate)
    (hg : g' ∈ (gs.foldl (step n) st).2) :
    g' ∈ st.2 ∨ ∃ g ∈ gs, ∃ m s, g' ∈ pgt m s g := by
  induction gs generalizing st with
  | nil => exact Or.inl hg
  | cons g gs ih =>
    rw [List.foldl_cons] at hg
    rcases ih (step n st g) hg with h | ⟨g0, hg0, m, s, hm⟩
    · simp only [step, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨g, by simp, _, _, h⟩
    · exact Or.inr ⟨g0, by simp [hg0], m, s, hm⟩

lemma fold_len2 (n : ℕ) (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate)
    (hF : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl (step n) st).2.length ≤ st.2.length + gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons]
    have h1 := ih (step n st g) (fun g hg => hF g (by simp [hg]))
    have h2 := (pgt_ok (n + st.2.length) st.1 g (hF g (by simp)).1 (hF g (by simp)).2).1
    simp [step] at h1 ⊢
    omega

lemma T_drop (n v : ℕ) (gs : List Gate) (j : ℕ) :
    gs.foldl (step n) (init n v) = (gs.drop j).foldl (step n) (T n v gs j) := by
  unfold T
  rw [← List.foldl_append, List.take_append_drop]

lemma T_succ (n v : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    T n v gs (j + 1) = step n (T n v gs j) gs[j] := by
  unfold T
  rw [← List.take_concat_get' gs j hj, List.foldl_append]
  rfl

lemma T_len1 (n v : ℕ) (gs : List Gate) (j : ℕ) (hj : j ≤ gs.length) :
    (T n v gs j).1.length = n + j := by
  unfold T
  rw [fold_len1]
  simp [init]
  omega

lemma T_mono (n v : ℕ) (gs : List Gate) (j1 j2 : ℕ) (h : j1 ≤ j2) :
    (T n v gs j1).2.length ≤ (T n v gs j2).2.length := by
  have e : T n v gs j2 = ((gs.drop j1).take (j2 - j1)).foldl (step n) (T n v gs j1) := by
    unfold T
    rw [← List.foldl_append, ← List.take_add]
    congr 2
    omega
  obtain ⟨r, hr⟩ := fold_pre2 n ((gs.drop j1).take (j2 - j1)) (T n v gs j1)
  rw [e, hr]
  simp

def Dc (n v : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.foldl (step n) (init n v)).2,
    match rs (C.gates.foldl (step n) (init n v)).1 C.output with
    | Sum.inr k => k
    | Sum.inl _ => n + (C.gates.foldl (step n) (init n v)).2.length⟩

lemma fan_iff (C : Circuit) : FanInTwo C ↔ ∀ g ∈ C.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  unfold FanInTwo
  simp

lemma inv (n v : ℕ) (hv : v < n) (C : Circuit) (hF : FanInTwo C) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ i, i < n → i ≠ v → x.getD i false = y.getD i false)
    (hyv : y.getD v false = false) :
    ∀ w, w < n + C.gates.length →
      (∀ b, rs (C.gates.foldl (step n) (init n v)).1 w = Sum.inl b → val C y w = b) ∧
      (∀ k, rs (C.gates.foldl (step n) (init n v)).1 w = Sum.inr k →
        k < n + (T n v C.gates (w + 1 - n)).2.length ∧ val (Dc n v C) x k = val C y w) := by
  rw [fan_iff] at hF
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  by_cases hwn : w < n
  · have e1 : rs (C.gates.foldl (step n) (init n v)).1 w = rs (init n v).1 w :=
      fold_rs n C.gates _ w (by simp [init]; exact hwn)
    have e2 : rs (init n v).1 w = if w = v then Sum.inl false else Sum.inr w := by
      simp [rs, init, List.getD_eq_getElem?_getD, hwn]
    rw [e1, e2]
    have e3 : w + 1 - n = 0 := by omega
    rw [e3]
    by_cases hwv : w = v
    · subst hwv
      simp only [ite_true]
      refine ⟨?_, ?_⟩
      · intro b hb
        simp at hb
        subst hb
        rw [val_input hy hwn, hyv]
      · intro k hk; simp at hk
    · simp only [hwv, ite_false]
      refine ⟨?_, ?_⟩
      · intro b hb; simp at hb
      · intro k hk
        simp at hk
        subst hk
        refine ⟨by simp [T, init]; omega, ?_⟩
        rw [val_input hx hwn, val_input hy hwn]
        exact hxy w hwn hwv
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have e3 : n + j + 1 - n = j + 1 := by omega
    rw [e3]
    set F := C.gates.foldl (step n) (init n v) with hFdef
    set s := (T n v C.gates j).1 with hs
    set m := n + (T n v C.gates j).2.length with hm
    set g := C.gates[j] with hg
    have hgm : g ∈ C.gates := List.getElem_mem hj
    have hsl : s.length = n + j := T_len1 n v C.gates j hj.le
    have hTs := T_succ n v C.gates j hj
    have hFT : F = (C.gates.drop (j + 1)).foldl (step n) (T n v C.gates (j + 1)) :=
      T_drop n v C.gates (j + 1)
    have hrsF : ∀ i, i < n + j → rs F.1 i = rs s i := by
      intro i hi
      rw [hFdef, T_drop n v C.gates j]
      exact fold_rs n _ _ i (by rw [hsl]; exact hi)
    have hst : rs F.1 (n + j) = pst m s g := by
      rw [hFT, fold_rs n _ _ _ (by rw [T_len1 n v C.gates (j + 1) hj]; omega), hTs]
      simp [step, rs, List.getD_eq_getElem?_getD, ← hs, ← hm, ← hg, hsl]
    have hT2 : (T n v C.gates (j + 1)).2 = (T n v C.gates j).2 ++ pgt m s g := by
      rw [hTs]; rfl
    obtain ⟨r, hr⟩ := fold_pre2 n (C.gates.drop (j + 1)) (T n v C.gates (j + 1))
    have hDg : (Dc n v C).gates = (T n v C.gates j).2 ++ pgt m s g ++ r := by
      show F.2 = _
      rw [hFT, hr, hT2]
    have hxD : x.length = n := hx
    have key := proc_ok m s g (hF g hgm).1
      (fun i => if i < n + j then val C y i else false)
      (fun i => if i < m then val (Dc n v C) x i else false) (by
        intro i _
        by_cases hi : i < n + j
        · have I := ih i hi (by omega)
          rw [← hrsF i hi]
          simp only [hi, ite_true]
          refine ⟨I.1, ?_⟩
          intro k hk
          have I2 := I.2 k hk
          have hmono := T_mono n v C.gates (i + 1 - n) j (by omega)
          have hkm : k < m := by omega
          refine ⟨hkm, ?_⟩
          simp only [hkm, ite_true]
          exact I2.2
        · rw [rs_ge s i (by omega)]
          simp [hi])
    have hval : val C y (n + j) = g.op.eval (g.inputs.map fun i =>
        if i < n + j then val C y i else false) := val_gate hy hj
    rw [hst]
    refine ⟨fun b hb => by rw [hval]; exact key.1 b hb, ?_⟩
    intro k hk
    have hmono := T_mono n v C.gates j (j + 1) (by omega)
    rcases hp : pgt m s g with _ | ⟨g', t⟩
    · have K := key.2.1 hp k hk
      refine ⟨by omega, ?_⟩
      rw [hval, ← K.2]
      simp [K.1]
    · have hmem : g' ∈ pgt m s g := by rw [hp]; simp
      have K := key.2.2 g' hmem
      rw [K.1] at hk
      simp at hk
      subst hk
      have hlen1 := (pgt_ok m s g (hF g hgm).1 (hF g hgm).2).1
      rw [hp] at hlen1
      have ht : t = [] := by
        cases t with
        | nil => rfl
        | cons _ _ => simp at hlen1
      subst ht
      refine ⟨?_, ?_⟩
      · rw [hT2, hp]; simp; omega
      · have hpl : (T n v C.gates j).2.length < (Dc n v C).gates.length := by
          rw [hDg, hp]; simp
        have hDj : (Dc n v C).gates[(T n v C.gates j).2.length] = g' := by
          simp only [hDg, hp]
          simp
        have VD := val_gate (C := Dc n v C) hxD hpl
        rw [hDj] at VD
        rw [hm, VD, hval, ← K.2.1]

lemma upd_getD {n : ℕ} (x : Fin n → Bool) (v : Fin n) (b : Bool) (i : ℕ) (hi : i < n)
    (hiv : i ≠ v) :
    (List.ofFn (Function.update x v b)).getD i false = (List.ofFn x).getD i false := by
  have hne : (⟨i, hi⟩ : Fin n) ≠ v := by intro e; apply hiv; rw [← e]
  simp [List.getD_eq_getElem?_getD, hi, Function.update_of_ne hne]

lemma core (n : ℕ) (v : Fin n) (C : Circuit) (hF : FanInTwo C)
    (hr : ∃ j, ∃ hj : j < C.gates.length, (v : ℕ) ∈ eff C.gates[j])
    (h0 : ∃ x : Fin n → Bool, C.eval (List.ofFn (Function.update x v false)) = false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false)) := by
  have hF' := (fan_iff C).1 hF
  refine ⟨Dc n v C, ?_, ?_, ?_⟩
  · rw [fan_iff]
    intro g' hg'
    rcases fold_mem n C.gates (init n v) g' hg' with h | ⟨g, hg, m, s, hm⟩
    · simp [init] at h
    · exact (pgt_ok m s g (hF' g hg).1 (hF' g hg).2).2 g' hm
  · obtain ⟨j, hj, hjv⟩ := hr
    have hg := hF' _ (List.getElem_mem hj)
    have hFT := T_drop n v C.gates (j + 1)
    have hTs := T_succ n v C.gates j hj
    have hv0 : rs (T n v C.gates j).1 v = Sum.inl false := by
      unfold T
      rw [fold_rs n _ _ _ (by simp [init])]
      simp [rs, init, List.getD_eq_getElem?_getD]
    have hnil := pgt_nil (n + (T n v C.gates j).2.length) (T n v C.gates j).1 _ v hg.1 hg.2 hjv hv0
    have h1 := fold_len2 n (C.gates.drop (j + 1)) (T n v C.gates (j + 1))
      (fun g hg => hF' g (List.mem_of_mem_drop hg))
    have h2 : (T n v C.gates j).2.length ≤ j := by
      have := fold_len2 n (C.gates.take j) (init n v) (fun g hg => hF' g (List.mem_of_mem_take hg))
      have e : (init n v).2.length = 0 := rfl
      rw [e, List.length_take] at this
      unfold T; omega
    have h3 : (T n v C.gates (j + 1)).2 = (T n v C.gates j).2 := by
      rw [hTs]; simp [step, hnil]
    show (C.gates.foldl (step n) (init n v)).2.length + 1 ≤ C.gates.length
    rw [hFT]
    rw [h3] at h1
    simp only [List.length_drop] at h1
    omega
  · intro x
    have hx : (List.ofFn x).length = n := by simp
    have hy : (List.ofFn (Function.update x v false)).length = n := by simp
    have hxy : ∀ i, i < n → i ≠ v → (List.ofFn x).getD i false =
        (List.ofFn (Function.update x v false)).getD i false :=
      fun i hi hiv => (upd_getD x v false i hi hiv).symm
    have hyv : (List.ofFn (Function.update x v false)).getD v false = false := by
      simp [List.getD_eq_getElem?_getD]
    have I := inv n v v.2 C hF (List.ofFn x) _ hx hy hxy hyv
    show val (Dc n v C) (List.ofFn x) (Dc n v C).output =
      val C (List.ofFn (Function.update x v false)) C.output
    have hDl : (Dc n v C).gates.length = (C.gates.foldl (step n) (init n v)).2.length := rfl
    have hF1 : (C.gates.foldl (step n) (init n v)).1.length = n + C.gates.length := by
      rw [fold_len1]; simp [init]
    by_cases ho : C.output < n + C.gates.length
    · cases hs : rs (C.gates.foldl (step n) (init n v)).1 C.output with
      | inl b =>
        have hD : (Dc n v C).output = n + (C.gates.foldl (step n) (init n v)).2.length := by
          simp [Dc, hs]
        rw [hD, val_ge hx (by rw [hDl]), (I _ ho).1 b hs]
        cases b
        · rfl
        · obtain ⟨x0, hx0⟩ := h0
          have I0 := inv n v v.2 C hF (List.ofFn (Function.update x0 v false)) _ (by simp) (by simp)
            (fun _ _ _ => rfl) (by simp [List.getD_eq_getElem?_getD])
          have e0 := (I0 _ ho).1 true hs
          have : C.eval (List.ofFn (Function.update x0 v false)) = true := e0
          rw [hx0] at this
          exact absurd this (by simp)
      | inr k =>
        have hD : (Dc n v C).output = k := by simp [Dc, hs]
        rw [hD]
        exact ((I _ ho).2 k hs).2
    · have hs : rs (C.gates.foldl (step n) (init n v)).1 C.output = Sum.inl false :=
        rs_ge _ _ (by omega)
      have hD : (Dc n v C).output = n + (C.gates.foldl (step n) (init n v)).2.length := by
        simp [Dc, hs]
      rw [hD, val_ge hx (by rw [hDl]), val_ge hy (by omega)]

lemma indep (n v : ℕ) (C : Circuit) (hF : FanInTwo C) (hno : ∀ g ∈ C.gates, v ∉ eff g)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ i, i < n → i ≠ v → x.getD i false = y.getD i false) :
    ∀ w, w ≠ v → val C x w = val C y w := by
  rw [fan_iff] at hF
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hwv
  by_cases hwn : w < n
  · rw [val_input hx hwn, val_input hy hwn]; exact hxy w hwn hwv
  · by_cases hwl : w < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      rw [val_gate hx hj, val_gate hy hj]
      have hgm := List.getElem_mem hj
      apply eval_congr _ (hF _ hgm).1
      intro i hi
      have hiv : i ≠ v := by intro e; subst e; exact hno _ hgm hi
      by_cases h : i < n + j
      · simp only [h, ite_true]; exact ih i h hiv
      · simp [h]
    · rw [val_ge hx (by omega), val_ge hy (by omega)]

lemma reader (n : ℕ) (v : Fin n) (C : Circuit) (hF : FanInTwo C) (f : (Fin n → Bool) → Bool)
    (hC : ∀ x, C.eval (List.ofFn x) = f x) (h1 : ∃ x, f x ≠ x v)
    (h2 : ∃ x, f (Function.update x v true) ≠ f (Function.update x v false)) :
    ∃ j, ∃ hj : j < C.gates.length, (v : ℕ) ∈ eff C.gates[j] := by
  by_contra hne
  have hno : ∀ g ∈ C.gates, (v : ℕ) ∉ eff g := by
    intro g hg hm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact hne ⟨j, hj, hm⟩
  by_cases ho : C.output = v
  · obtain ⟨x, hx⟩ := h1
    apply hx
    rw [← hC]
    show val C (List.ofFn x) C.output = x v
    rw [ho, val_input (by simp) v.2]
    simp [List.getD_eq_getElem?_getD]
  · obtain ⟨x, hx⟩ := h2
    apply hx
    rw [← hC, ← hC]
    exact indep n v C hF hno _ _ (by simp) (by simp)
      (fun i hi hiv => by rw [upd_getD x v true i hi hiv, upd_getD x v false i hi hiv]) _ ho

lemma restrict (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n)
    (A : Finset (Fin n)) (ha : a ∉ A) (hedge : ∀ u w, G.Adj u w → u ≠ a) (x : Fin n → Bool) :
    graphFun G (insert a A) (Function.update x a false) = graphFun G A x := by
  have e1 : (∃ b ∈ insert a A, Function.update x a false b = true) ↔ (∃ b ∈ A, x b = true) := by
    constructor
    · rintro ⟨b, hb, hx⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · simp at hx
      · have : b ≠ a := fun e => ha (e ▸ hb)
        exact ⟨b, hb, by rwa [Function.update_of_ne this] at hx⟩
    · rintro ⟨b, hb, hx⟩
      have : b ≠ a := fun e => ha (e ▸ hb)
      exact ⟨b, Finset.mem_insert_of_mem hb, by rwa [Function.update_of_ne this]⟩
  have e2 : (∃ u w, G.Adj u w ∧ Function.update x a false u = true ∧
      Function.update x a false w = true) ↔ (∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) := by
    constructor
    · rintro ⟨u, w, h, hu, hw⟩
      rw [Function.update_of_ne (hedge u w h)] at hu
      rw [Function.update_of_ne (hedge w u h.symm)] at hw
      exact ⟨u, w, h, hu, hw⟩
    · rintro ⟨u, w, h, hu, hw⟩
      exact ⟨u, w, h, by rwa [Function.update_of_ne (hedge u w h)],
        by rwa [Function.update_of_ne (hedge w u h.symm)]⟩
  simp only [graphFun, e1, e2]

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u0 w0 : Fin n)
    (h0 : G.Adj u0 w0) (A : Finset (Fin n)) :
    (∀ u w, G.Adj u w → u ∉ A) → ∀ s, HasCircuitSize n (graphFun G A) s →
      ∃ t, t + A.card ≤ s ∧ HasCircuitSize n (graphFun G ∅) t := by
  refine Finset.induction_on A ?_ ?_
  · intro _ s hs
    exact ⟨s, by simp, hs⟩
  · intro a A ha ih hA s hs
    have hA' : ∀ u w, G.Adj u w → u ∉ A := fun u w h hu => hA u w h (Finset.mem_insert_of_mem hu)
    have hedge : ∀ u w, G.Adj u w → u ≠ a :=
      fun u w h e => hA u w h (e ▸ Finset.mem_insert_self a A)
    obtain ⟨C, hCF, hCs, hC⟩ := hs
    let y1 : Fin n → Bool := fun i => decide (i = u0 ∨ i = w0)
    have hy1a : y1 a = false := by
      have h1 := hedge u0 w0 h0
      have h2 := hedge w0 u0 h0.symm
      simp only [y1, decide_eq_false_iff_not, not_or]
      exact ⟨fun e => h1 e.symm, fun e => h2 e.symm⟩
    have hfy1 : graphFun G (insert a A) y1 = true := by
      unfold graphFun
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨u0, w0, h0, by simp [y1], by simp [y1]⟩
    have hz : graphFun G (insert a A) (Function.update (fun _ => false) a false) = false := by
      rw [restrict n G a A ha hedge]
      simp [graphFun]
    have hz1 : graphFun G (insert a A) (Function.update (fun _ => false) a true) = true := by
      unfold graphFun
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      left
      exact ⟨a, Finset.mem_insert_self a A, by simp⟩
    have hr := reader n a C hCF _ hC ⟨y1, by rw [hfy1, hy1a]; simp⟩
      ⟨fun _ => false, by rw [hz, hz1]; simp⟩
    obtain ⟨D, hDF, hDs, hD⟩ := core n a C hCF hr ⟨fun _ => false, by rw [hC, hz]⟩
    have hcs : C.size ≤ s := hCs
    obtain ⟨t, ht, htc⟩ := ih hA' (s - 1) ⟨D, hDF, by omega, fun x => by
      rw [hD, hC, restrict n G a A ha hedge]⟩
    refine ⟨t, ?_, htc⟩
    rw [Finset.card_insert_of_notMem ha]
    omega

end PEqualNP.Outside.L_meta_4455

theorem PEqualNP.Outside.L_meta_4455 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∉ x4) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → ∀ (x7 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x7 → ∃ (x9 : ℕ), x9 + x4.card ≤ x7 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 := by
  intro n G _ A hA hE s hs
  obtain ⟨u0, w0, h0⟩ := hE
  exact PEqualNP.Outside.L_meta_4455.main n G u0 w0 h0 A hA s hs
