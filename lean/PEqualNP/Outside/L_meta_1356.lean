import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1356
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma length_step (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma getD_step (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false) else false := by
  simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append]
  by_cases h : i < w.length
  · simp [h]
  · by_cases h2 : i = w.length
    · subst h2; simp
    · have h3 : ¬ i - w.length < 1 := by omega
      simp [h, h2, h3]

lemma fold_inv (P : List Bool → List Bool → Prop) (gs : List Gate)
    (h : ∀ g ∈ gs, ∀ w0 w1, P w0 w1 → P (step w0 g) (step w1 g)) :
    ∀ w0 w1, P w0 w1 → P (gs.foldl step w0) (gs.foldl step w1) := by
  induction gs with
  | nil => intro w0 w1 hp; exact hp
  | cons g gs ih =>
    intro w0 w1 hp
    exact ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) _ _
      (h g List.mem_cons_self _ _ hp)

lemma fold_length (gs : List Gate) (w : List Bool) : w.length ≤ (gs.foldl step w).length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    have := ih (step w g)
    rw [List.foldl_cons]
    have h2 := length_step w g
    omega

lemma fold_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons]
    have h2 := length_step w g
    rw [ih (step w g) (by omega), getD_step]
    simp [hi]

def Peq (p : ℕ) (w0 w1 : List Bool) : Prop :=
  w0.length = w1.length ∧ p < w0.length ∧ ∀ i, i ≠ p → w0.getD i false = w1.getD i false

def Ple (p : ℕ) (w0 w1 : List Bool) : Prop :=
  w0.length = w1.length ∧ p < w0.length ∧ w0.getD p false = false ∧ w1.getD p false = true ∧
    ∀ i, i ≠ p → w1.getD i false = true → w0.getD i false = true

lemma peq_step (p : ℕ) (g : Gate)
    (hg : (∀ i ∈ g.inputs, i ≠ p) ∨ (g.op = GateOp.not ∧ g.inputs.head? ≠ some p))
    (w0 w1 : List Bool) (h : Peq p w0 w1) : Peq p (step w0 g) (step w1 g) := by
  obtain ⟨hl, hp, he⟩ := h
  have hval : g.op.eval (g.inputs.map fun j => w0.getD j false) =
      g.op.eval (g.inputs.map fun j => w1.getD j false) := by
    rcases hg with hg | ⟨hop, hh⟩
    · congr 1
      exact List.map_congr_left fun i hi => he i (hg i hi)
    · rw [hop]
      cases hin : g.inputs with
      | nil => simp [GateOp.eval]
      | cons a r =>
        rw [hin] at hh
        have : a ≠ p := fun h => hh (by simp [h])
        simpa [GateOp.eval, List.getD_eq_getElem?_getD] using he a this
  refine ⟨by rw [length_step, length_step, hl], by rw [length_step]; omega, ?_⟩
  intro i hi
  rw [getD_step, getD_step]
  by_cases h1 : i < w0.length
  · rw [if_pos h1, if_pos (hl ▸ h1)]; exact he i hi
  · by_cases h2 : i = w0.length
    · subst h2
      rw [← hl, if_neg (lt_irrefl _), if_pos rfl, if_neg (lt_irrefl _), if_pos rfl]; exact hval
    · rw [if_neg h1, if_neg h2, if_neg (by omega), if_neg (by omega)]

lemma ple_step (p : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) → ∀ i ∈ g.inputs, i ≠ p)
    (hn : g.op = GateOp.not → g.inputs.head? = some p)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (w0 w1 : List Bool) (h : Ple p w0 w1) : Ple p (step w0 g) (step w1 g) := by
  obtain ⟨hl, hp, h0, h1, he⟩ := h
  have hval : g.op.eval (g.inputs.map fun j => w1.getD j false) = true →
      g.op.eval (g.inputs.map fun j => w0.getD j false) = true := by
    rcases hop with hop | hop | hop
    · have hg' := hg (Or.inl hop)
      rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      rintro H _ ⟨i, hi, rfl⟩
      exact he i (hg' i hi) (H _ ⟨i, hi, rfl⟩)
    · have hg' := hg (Or.inr hop)
      rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨_, ⟨i, hi, rfl⟩, hv⟩
      exact ⟨_, ⟨i, hi, rfl⟩, he i (hg' i hi) hv⟩
    · have hh := hn hop
      rw [hop]
      cases hin : g.inputs with
      | nil => rw [hin] at hh; simp at hh
      | cons a r =>
        rw [hin] at hh
        have : a = p := by simpa using hh
        subst this
        intro H
        simp only [List.map_cons, GateOp.eval, List.headD_cons, h1] at H
        simp at H
  refine ⟨by rw [length_step, length_step, hl], by rw [length_step]; omega, ?_, ?_, ?_⟩
  · rw [getD_step, if_pos hp]; exact h0
  · rw [getD_step, if_pos (hl ▸ hp)]; exact h1
  · intro i hi
    rw [getD_step, getD_step]
    by_cases hi1 : i < w0.length
    · rw [if_pos hi1, if_pos (hl ▸ hi1)]; exact he i hi
    · by_cases hi2 : i = w0.length
      · subst hi2
        rw [← hl, if_neg (lt_irrefl _), if_pos rfl, if_neg (lt_irrefl _), if_pos rfl]; exact hval
      · rw [if_neg hi1, if_neg hi2, if_neg (by omega), if_neg (by omega)]
        intro h; exact absurd h (by simp)


lemma getD_ofFn (n : ℕ) (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

end PEqualNP.Outside.L_meta_1356

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1356

theorem PEqualNP.Outside.L_meta_1356 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i9 : Fin m, 2 ≤ (S i9).card) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → ∀ (p : Fin n) (i0 : Fin m), p ∈ S i0 → ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ p.val ∈ (gates.get a).inputs := by
  intro n m S hS gates out hgates hcirc ι hι p i0 hp
  by_contra hno
  push Not at hno
  have hno' : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) → p.val ∉ g.inputs := by
    intro g hg hop
    obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hg
    exact hno a hop
  have huniq : ∀ g ∈ gates, ∀ g' ∈ gates, g.op = GateOp.not → g'.op = GateOp.not → g = g' := by
    intro g hg g' hg' h h'
    obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hg
    obtain ⟨b, rfl⟩ := List.mem_iff_get.mp hg'
    obtain ⟨ra, hra⟩ := hι a h
    obtain ⟨rb, hrb⟩ := hι b h'
    have : ra = rb := Subsingleton.elim _ _
    subst this
    rw [← hra, ← hrb]
  have hx0 := hcirc i0 (fun _ : Fin n => false)
  have hx1 := hcirc i0 (fun v : Fin n => decide (v = p))
  have hf0 : (gates.foldl step (List.ofFn (fun _ : Fin n => false))).getD (out i0) false = false := by
    have h := hx0
    change (gates.foldl step _).getD (out i0) false = _ at h
    rw [h]; simp
  have hf1 : (gates.foldl step (List.ofFn (fun v : Fin n => decide (v = p)))).getD (out i0) false = true := by
    have h := hx1
    change (gates.foldl step _).getD (out i0) false = _ at h
    rw [h]; simp only [decide_eq_true_eq]
    exact ⟨p, hp, by simp⟩
  by_cases ho : out i0 = p.val
  · obtain ⟨q, hq, hqp⟩ := Finset.exists_mem_ne (hS i0) p
    have hy := hcirc i0 (fun v : Fin n => decide (v = q))
    change (gates.foldl step _).getD (out i0) false = _ at hy
    rw [ho, fold_prefix _ _ _ (by simp)] at hy
    rw [getD_ofFn n _ _ p.isLt] at hy
    have : decide (p = q) = true := by
      rw [hy]; simp only [decide_eq_true_eq]; exact ⟨q, hq, by simp⟩
    simp at this
    exact hqp this.symm
  · by_cases hA : ∀ g ∈ gates, g.op = GateOp.not → g.inputs.head? ≠ some p.val
    · have key := fold_inv (Peq p.val) gates (by
        intro g hg w0 w1 h
        refine peq_step _ g ?_ w0 w1 h
        rcases hgates g hg with ⟨hop, -⟩
        rcases hop with hop | hop | hop
        · exact Or.inl fun i hi hip => hno' g hg (Or.inl hop) (hip ▸ hi)
        · exact Or.inl fun i hi hip => hno' g hg (Or.inr hop) (hip ▸ hi)
        · exact Or.inr ⟨hop, hA g hg hop⟩) (List.ofFn (fun _ : Fin n => false))
        (List.ofFn (fun v : Fin n => decide (v = p))) (by
          refine ⟨by simp, by simp, ?_⟩
          intro i hi
          by_cases h : i < n
          · rw [getD_ofFn n _ _ h, getD_ofFn n _ _ h]
            have : (⟨i, h⟩ : Fin n) ≠ p := fun e => hi (by simpa using congrArg Fin.val e)
            simp [this]
          · simp [List.getD_eq_getElem?_getD, h])
      have := key.2.2 _ ho
      rw [hf0, hf1] at this
      exact absurd this (by simp)
    · push Not at hA
      obtain ⟨N, hN, hNop, hNh⟩ := hA
      have hn : ∀ g ∈ gates, g.op = GateOp.not → g.inputs.head? = some p.val := by
        intro g hg hop
        rw [huniq g hg N hN hop hNop]; exact hNh
      have key := fold_inv (Ple p.val) gates (by
        intro g hg w0 w1 h
        refine ple_step _ g ?_ (hn g hg) ?_ w0 w1 h
        · intro hop i hi hip
          exact hno' g hg hop (hip ▸ hi)
        · exact (hgates g hg).1)
        (List.ofFn (fun _ : Fin n => false))
        (List.ofFn (fun v : Fin n => decide (v = p))) (by
          refine ⟨by simp, by simp, ?_, ?_, ?_⟩
          · rw [getD_ofFn n _ _ p.isLt]
          · rw [getD_ofFn n _ _ p.isLt]; simp
          · intro i hi h1
            by_cases h : i < n
            · rw [getD_ofFn n _ _ h] at h1
              have : (⟨i, h⟩ : Fin n) ≠ p := fun e => hi (by simpa using congrArg Fin.val e)
              simp [this] at h1
            · simp [List.getD_eq_getElem?_getD, h] at h1)
      have := key.2.2.2.2 _ ho hf1
      rw [hf0] at this
      exact absurd this (by simp)
