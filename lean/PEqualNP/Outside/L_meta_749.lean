import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_749

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_tail (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [wiresFrom_cons, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_tail gs w
  rw [ht, List.length_append, hl]

lemma wiresFrom_prefix_eq (gs : List Gate) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length) (hw : wiresFrom gs w1 = wiresFrom gs w2) : w1 = w2 := by
  obtain ⟨t1, ht1, _⟩ := wiresFrom_tail gs w1
  obtain ⟨t2, ht2, _⟩ := wiresFrom_tail gs w2
  rw [ht1, ht2] at hw
  have htake := congrArg (List.take w1.length) hw
  simpa [List.take_left', hlen] using htake

lemma wires_slot (pre post : List Gate) (g g' : Gate) (xs : List Bool)
    (h : g.op.eval (g.inputs.map fun i => (wiresFrom pre xs).getD i false)
      = g'.op.eval (g'.inputs.map fun i => (wiresFrom pre xs).getD i false)) :
    wiresFrom (pre ++ g :: post) xs = wiresFrom (pre ++ g' :: post) xs := by
  rw [wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_cons, h]

lemma getD_snoc_eq {α : Type} (L : List α) (a d : α) :
    (L ++ [a]).getD L.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_ne {α : Type} (L : List α) (a d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [a]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def Above (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i, v.getD i false = true → v'.getD i false = true

lemma above_snoc {v v' : List Bool} {a a' : Bool} (h : Above v v')
    (ha : a = true → a' = true) : Above (v ++ [a]) (v' ++ [a']) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i = v.length
  · subst hiv
    rw [getD_snoc_eq] at hi
    rw [h.1, getD_snoc_eq]
    exact ha hi
  · rw [getD_snoc_ne _ _ _ _ hiv] at hi
    rw [getD_snoc_ne _ _ _ _ (by rw [← h.1]; exact hiv)]
    exact h.2 i hi

lemma above_wiresFrom (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ v v' : List Bool, Above v v' → Above (wiresFrom gs v) (wiresFrom gs v') := by
  induction gs with
  | nil => intro v v' h; exact h
  | cons g gs ih =>
    intro v v' h
    rw [wiresFrom_cons, wiresFrom_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    apply above_snoc h
    rcases hgs g (by simp) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall b hb
      obtain ⟨j, hj, rfl⟩ := hb
      exact h.2 j (hall _ ⟨j, hj, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
      exact ⟨_, ⟨j, hj, rfl⟩, h.2 j hb⟩

lemma above_ofFn {n : ℕ} (y x : Fin n → Bool) (h : ∀ p : Fin n, y p = true → x p = true) :
    Above (List.ofFn y) (List.ofFn x) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · simp [List.getD_eq_getElem?_getD, hin] at hi ⊢
    exact h ⟨i, hin⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

lemma headD_map_mono {v v' : List Bool} (hab : Above v v') (ins : List ℕ)
    (h : ((ins.map fun i => v.getD i false).headD false) = true) :
    ((ins.map fun i => v'.getD i false).headD false) = true := by
  cases ins with
  | nil => simp at h
  | cons i rest =>
    simp only [List.map_cons, List.headD_cons] at h ⊢
    exact hab.2 i h

lemma c'_and_or (n : ℕ) (C C' : List Gate) (y : Fin n → Bool)
    (hC : ∀ g ∈ C, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hlen : C'.length = C.length)
    (hrel : ∀ (j2 : ℕ) (g2 : Gate), C[j2]? = some g2 →
      (g2.op = GateOp.not →
        (((g2.inputs.map (fun i3 => (Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true →
          C'[j2]? = some ({ op := GateOp.or, inputs := [] } : Gate)) ∧
        (((g2.inputs.map (fun i4 => (Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false →
          C'[j2]? = some ({ op := GateOp.and, inputs := [] } : Gate))) ∧
      (g2.op ≠ GateOp.not → C'[j2]? = some g2)) :
    ∀ g ∈ C', g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hjC : j < C.length := by omega
  obtain ⟨hnot, hne⟩ := hrel j C[j] (List.getElem?_eq_getElem hjC)
  rcases (hC C[j] (List.getElem_mem hjC)).1 with hop | hop | hop
  · have hneq : C[j].op ≠ GateOp.not := by intro h; rw [hop] at h; cases h
    have hsome := hne hneq
    rw [List.getElem?_eq_getElem hj] at hsome
    have heq : C'[j] = C[j] := Option.some.inj hsome
    rw [heq]
    exact Or.inl hop
  · have hneq : C[j].op ≠ GateOp.not := by intro h; rw [hop] at h; cases h
    have hsome := hne hneq
    rw [List.getElem?_eq_getElem hj] at hsome
    have heq : C'[j] = C[j] := Option.some.inj hsome
    rw [heq]
    exact Or.inr hop
  · cases hval : ((C[j].inputs.map (fun i =>
        (Circuit.wires ⟨C.take j, 0⟩ (List.ofFn y)).getD i false)).headD false)
    · have hsome := (hnot hop).2 hval
      rw [List.getElem?_eq_getElem hj] at hsome
      have heq : C'[j] = { op := GateOp.and, inputs := [] } := Option.some.inj hsome
      rw [heq]
      exact Or.inl rfl
    · have hsome := (hnot hop).1 hval
      rw [List.getElem?_eq_getElem hj] at hsome
      have heq : C'[j] = { op := GateOp.or, inputs := [] } := Option.some.inj hsome
      rw [heq]
      exact Or.inr rfl

def mid (C C' : List Gate) (t : ℕ) : List Gate :=
  C'.take t ++ C.drop t

lemma mid_wires_eq (n : ℕ) (C C' : List Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool)
    (hC : ∀ g ∈ C, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hyX : y ∈ X)
    (hmin : ∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true)
    (hfalse : ∀ (j1 : ℕ) (g1 : Gate), C[j1]? = some g1 → g1.op = GateOp.not →
      ((g1.inputs.map (fun i1 => (Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false →
      ∀ z ∈ X, ((g1.inputs.map (fun i2 => (Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false)
    (hlen : C'.length = C.length)
    (hrel : ∀ (j2 : ℕ) (g2 : Gate), C[j2]? = some g2 →
      (g2.op = GateOp.not →
        (((g2.inputs.map (fun i3 => (Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true →
          C'[j2]? = some ({ op := GateOp.or, inputs := [] } : Gate)) ∧
        (((g2.inputs.map (fun i4 => (Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false →
          C'[j2]? = some ({ op := GateOp.and, inputs := [] } : Gate))) ∧
      (g2.op ≠ GateOp.not → C'[j2]? = some g2)) :
    ∀ t ≤ C.length, ∀ z ∈ X, wiresFrom (mid C C' t) (List.ofFn z) = wiresFrom C (List.ofFn z) := by
  have hc' := c'_and_or n C C' y hC hlen hrel
  intro t
  induction t with
  | zero =>
    intro _ z _
    simp [mid]
  | succ t ih =>
    intro ht z hz
    have hIH : ∀ u ∈ X, wiresFrom (mid C C' t) (List.ofFn u) = wiresFrom C (List.ofFn u) :=
      ih (by omega)
    have hpre : ∀ u ∈ X,
        wiresFrom (C'.take t) (List.ofFn u) = wiresFrom (C.take t) (List.ofFn u) := by
      intro u hu
      apply wiresFrom_prefix_eq (C.drop t)
      · simp [length_wiresFrom, hlen]
      · have h1 : wiresFrom (C.drop t) (wiresFrom (C'.take t) (List.ofFn u))
            = wiresFrom (mid C C' t) (List.ofFn u) := by
          rw [← wiresFrom_append]; rfl
        have h2 : wiresFrom (C.drop t) (wiresFrom (C.take t) (List.ofFn u))
            = wiresFrom C (List.ofFn u) := by
          rw [← wiresFrom_append, List.take_append_drop]
        rw [h1, h2, hIH u hu]
    have htC : t < C.length := by omega
    have htC' : t < C'.length := by omega
    have hmid_t : mid C C' t = C'.take t ++ C[t] :: C.drop (t + 1) := by
      simp only [mid]
      rw [← List.drop_eq_getElem_cons htC]
    have hmid_succ : mid C C' (t + 1) = C'.take t ++ C'[t] :: C.drop (t + 1) := by
      simp only [mid]
      rw [List.take_add_one, List.getElem?_eq_getElem htC', Option.toList_some,
        List.append_assoc, List.singleton_append]
    rw [← hIH z hz, hmid_succ, hmid_t]
    apply wires_slot
    obtain ⟨hnot, hne⟩ := hrel t C[t] (List.getElem?_eq_getElem htC)
    by_cases hgn : C[t].op = GateOp.not
    · cases hvy : ((C[t].inputs.map (fun i =>
          (Circuit.wires ⟨C.take t, 0⟩ (List.ofFn y)).getD i false)).headD false)
      · have hsome := (hnot hgn).2 hvy
        rw [List.getElem?_eq_getElem htC'] at hsome
        have hg' : C'[t] = { op := GateOp.and, inputs := [] } := Option.some.inj hsome
        have hfz := hfalse t C[t] (List.getElem?_eq_getElem htC) hgn hvy z hz
        have hpz : wiresFrom (C'.take t) (List.ofFn z) = wiresFrom (C.take t) (List.ofFn z) :=
          hpre z hz
        rw [hg', hgn]
        change GateOp.and.eval [] = GateOp.not.eval
          (C[t].inputs.map fun i => (wiresFrom (C'.take t) (List.ofFn z)).getD i false)
        rw [hpz]
        simp only [GateOp.eval, List.all_nil]
        change true = !((C[t].inputs.map fun i =>
          (Circuit.wires ⟨C.take t, 0⟩ (List.ofFn z)).getD i false).headD false)
        rw [hfz]
        rfl
      · have hsome := (hnot hgn).1 hvy
        rw [List.getElem?_eq_getElem htC'] at hsome
        have hg' : C'[t] = { op := GateOp.or, inputs := [] } := Option.some.inj hsome
        have hpy : wiresFrom (C'.take t) (List.ofFn y) = wiresFrom (C.take t) (List.ofFn y) :=
          hpre y hyX
        have hab : Above (wiresFrom (C'.take t) (List.ofFn y))
            (wiresFrom (C'.take t) (List.ofFn z)) := by
          apply above_wiresFrom (C'.take t)
          · intro g hg
            exact hc' g (List.mem_of_mem_take hg)
          · exact above_ofFn y z (hmin z hz)
        have hvy' : ((C[t].inputs.map fun i =>
            (wiresFrom (C'.take t) (List.ofFn y)).getD i false).headD false) = true := by
          rw [hpy]
          exact hvy
        have hvz' : ((C[t].inputs.map fun i =>
            (wiresFrom (C'.take t) (List.ofFn z)).getD i false).headD false) = true :=
          headD_map_mono hab C[t].inputs hvy'
        rw [hg', hgn]
        change GateOp.or.eval [] = GateOp.not.eval
          (C[t].inputs.map fun i => (wiresFrom (C'.take t) (List.ofFn z)).getD i false)
        simp only [GateOp.eval, List.any_nil]
        rw [hvz']
        rfl
    · have hsome := hne hgn
      rw [List.getElem?_eq_getElem htC'] at hsome
      have hg' : C'[t] = C[t] := Option.some.inj hsome
      rw [hg']

lemma main : ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool),
    (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    y ∈ X →
    (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) →
    (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) →
    C'.length = C.length →
    (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 →
      (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not →
        (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧
        (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧
      (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) →
    ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  intro n C C' X y hC hyX hmin hfalse hlen hrel x hx w
  have hw := mid_wires_eq n C C' X y hC hyX hmin hfalse hlen hrel C.length (le_refl _) x hx
  have hmid : mid C C' C.length = C' := by
    simp only [mid, List.drop_length, List.append_nil]
    rw [← hlen, List.take_length]
  rw [hmid] at hw
  exact congrArg (fun l : List Bool => l.getD w false) hw

end PEqualNP.Outside.L_meta_749

theorem PEqualNP.Outside.L_meta_749 : ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool), (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → y ∈ X → (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) → C'.length = C.length → (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 → (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧ (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧ (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) → ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  exact PEqualNP.Outside.L_meta_749.main
