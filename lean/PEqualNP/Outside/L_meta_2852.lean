import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2852_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_le {w v : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w v) (i : ℕ) :
    w.getD i false ≤ v.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w v : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w v) :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx2
    obtain ⟨i, hi, rfl⟩ := hx2
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w v : List Bool, List.Forall₂ (fun a b => a ≤ b) w v →
      List.Forall₂ (fun a b => a ≤ b) (gs.foldl step w) (gs.foldl step v) := by
  induction gs with
  | nil => intro w v h; simpa using h
  | cons g gs ih =>
    intro w v h
    simp only [List.foldl_cons]
    apply ih (fun g2 hg2 => hgs g2 (List.mem_cons_of_mem _ hg2))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem ext (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem pre_get (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    ∀ i < w.length + j, (gs.foldl step w).getD i false = ((gs.take j).foldl step w).getD i false := by
  have hs : gs = gs.take j ++ gs[j] :: gs.drop (j+1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  obtain ⟨q, hq, hql⟩ := ext (gs.take j) w
  have hQ : ((gs.take j).foldl step w).length = w.length + j := by
    rw [hq]; simp [hql]; omega
  obtain ⟨t, ht, _⟩ := ext (gs.drop (j+1)) (step ((gs.take j).foldl step w) gs[j])
  have hf : gs.foldl step w = step ((gs.take j).foldl step w) gs[j] ++ t := by
    conv_lhs => rw [hs]
    rw [List.foldl_append, List.foldl_cons, ht]
  rw [hf]
  intro i hi
  rw [← hQ] at hi
  have hi2 : i < (step ((gs.take j).foldl step w) gs[j]).length := by simp [step]; omega
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hi2]
  simp only [step]
  rw [List.getElem?_append_left hi]

theorem refl_le (w : List Bool) : List.Forall₂ (fun a b => a ≤ b) w w := by
  induction w with
  | nil => exact List.Forall₂.nil
  | cons a w ih => exact List.Forall₂.cons le_rfl ih

theorem gate_narrow (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (p q b d : ℕ) (hb : b < 2)
    (w : List Bool) (h : w.getD d false ≤ w.getD ([p, q].getD b 0) false) :
    op.eval (([p, q].set b d).map fun i => w.getD i false) ≤
      op.eval ([p, q].map fun i => w.getD i false) := by
  rw [bool_le] at h ⊢
  interval_cases b <;> rcases hop with rfl | rfl <;>
    simp only [GateOp.eval, List.set_cons_zero, List.set_cons_succ, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false,
      List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true, Bool.or_eq_true] at h ⊢ <;> tauto

theorem mono (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (o : ℕ) :
    (gs.foldl step (List.ofFn x)).getD o false ≤ (gs.foldl step (List.ofFn y)).getD o false := by
  have h0 : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact bool_le.mpr (hxy _)
  exact getD_le (fold_le gs hgs _ _ h0) o

theorem exists_min (n : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : f x = true) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ f y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → f z = false := by
  obtain ⟨y, hyx, hy⟩ := exists_minimal_le_of_wellFoundedLT (fun z => f z = true) x hx
  refine ⟨y, fun i => bool_le.mp (hyx i), hy.1, fun z hz hne => ?_⟩
  by_contra hfz
  have hfz2 : f z = true := by simpa using hfz
  have hzy : z ≤ y := fun i => bool_le.mpr (hz i)
  exact hne (le_antisymm hzy (hy.2 hfz2 hzy))

end PEqualNP.Outside.L_meta_2852_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2852_aux in
theorem PEqualNP.Outside.L_meta_2852 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b c d : ℕ), (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = c ∧ d < n + g ∧ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) ∧ (PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ↔ (∀ x : Fin n → Bool, (PEqualNP.MetaComplexity.circuitFun n C x = true ∧ ∀ y : Fin n → Bool, (∀ i, y i = true → x i = true) → y ≠ x → PEqualNP.MetaComplexity.circuitFun n C y = false) → PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true)) := by
  rintro n ⟨gs, out⟩ g b c d ⟨⟨hAO, hRB, hlen⟩, -, hg, hb, hc, hd, himp⟩
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, out⟩ g = gs[g] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hg]
  simp only [hga] at hc ⊢
  simp only at hg himp
  have hmem : gs[g] ∈ gs := List.getElem_mem hg
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (hlen _ hmem)
  have hop := hAO _ hmem
  have hAO2 : ∀ a ∈ gs.set g ⟨gs[g].op, gs[g].inputs.set b d⟩, a.op = GateOp.and ∨ a.op = GateOp.or := by
    intro a ha
    rcases List.mem_or_eq_of_mem_set ha with h | rfl
    · exact hAO a h
    · exact hop
  have hcf : ∀ (l : List Gate) (o : ℕ) (x : Fin n → Bool),
      PEqualNP.MetaComplexity.circuitFun n ⟨l, o⟩ x = (l.foldl step (List.ofFn x)).getD o false :=
    fun _ _ _ => rfl
  have hev : ∀ (o : ℕ) (x : Fin n → Bool),
      Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (gs.foldl step (List.ofFn x)).getD o false :=
    fun _ _ => rfl
  have hdec : gs = gs.take g ++ gs[g] :: gs.drop (g + 1) := by
    rw [← List.drop_eq_getElem_cons hg, List.take_append_drop]
  have hset : gs.set g ⟨gs[g].op, gs[g].inputs.set b d⟩ =
      gs.take g ++ ⟨gs[g].op, gs[g].inputs.set b d⟩ :: gs.drop (g + 1) := by
    simp [List.set_eq_take_append_cons_drop, hg]
  have hcin : c < n + g := by
    have h1 := hRB g hg
    rw [hga, hpq] at h1
    rw [hpq] at hc
    interval_cases b
    · exact h1 c (by simp at hc; simp [hc])
    · exact h1 c (by simp at hc; simp [hc])
  have hle : ∀ x : Fin n → Bool, List.Forall₂ (fun a b => a ≤ b)
      ((gs.set g ⟨gs[g].op, gs[g].inputs.set b d⟩).foldl step (List.ofFn x))
      (gs.foldl step (List.ofFn x)) := by
    intro x
    rw [hset]
    conv_rhs => rw [hdec]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
    apply fold_le _ (fun a ha => hAO a (List.mem_of_mem_drop ha))
    apply List.rel_append (refl_le _)
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    have hpg := pre_get gs (List.ofFn x) g hg
    simp only [List.length_ofFn] at hpg
    have h2 : ((gs.take g).foldl step (List.ofFn x)).getD d false ≤
        ((gs.take g).foldl step (List.ofFn x)).getD ([p, q].getD b 0) false := by
      rw [← hpq, hc, ← hpg d hd, ← hpg c hcin, bool_le, ← hev, ← hev]
      exact himp x
    rw [hpq]
    exact gate_narrow _ hop p q b d hb _ h2
  have hpt : ∀ x : Fin n → Bool,
      PEqualNP.MetaComplexity.circuitFun n ⟨gs.set g ⟨gs[g].op, gs[g].inputs.set b d⟩, out⟩ x = true →
      PEqualNP.MetaComplexity.circuitFun n ⟨gs, out⟩ x = true := by
    intro x
    rw [hcf, hcf]
    exact bool_le.mp (getD_le (hle x) out)
  refine ⟨⟨hAO2, ?_, ?_⟩, ?_, hpt, ?_⟩
  · intro j hj i hi
    simp only [List.length_set] at hj
    by_cases hjg : j = g
    · subst hjg
      have h3 : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs.set j ⟨gs[j].op, gs[j].inputs.set b d⟩, out⟩ j
          = ⟨gs[j].op, gs[j].inputs.set b d⟩ := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
      rw [h3] at hi
      rcases List.mem_or_eq_of_mem_set hi with h | rfl
      · exact hRB j hj i (by rw [hga]; exact h)
      · exact hd
    · have h3 : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs.set g ⟨gs[g].op, gs[g].inputs.set b d⟩, out⟩ j
          = PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, out⟩ j := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, Ne.symm hjg]
      rw [h3] at hi
      exact hRB j hj i hi
  · intro a ha
    rcases List.mem_or_eq_of_mem_set ha with h | rfl
    · exact hlen a h
    · simp [hpq]
  · simp [Circuit.size]
  · constructor
    · intro h x hx
      rw [h]; exact hx.1
    · intro h
      funext x
      cases hx : PEqualNP.MetaComplexity.circuitFun n ⟨gs, out⟩ x
      · by_contra hne
        have := hpt x (by simpa using hne)
        rw [hx] at this
        exact Bool.false_ne_true this
      · obtain ⟨y, hyx, hy, hmin⟩ := exists_min n (PEqualNP.MetaComplexity.circuitFun n ⟨gs, out⟩) x hx
        have hy2 := h y ⟨hy, hmin⟩
        rw [hcf] at hy2 ⊢
        exact bool_le.mp (mono n _ hAO2 y x hyx out) hy2
