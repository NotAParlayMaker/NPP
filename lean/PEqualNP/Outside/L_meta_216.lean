import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.MaximalZeros

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def trace : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w => (g.inputs.map (fun i => w.getD i false)).headD false ::
      trace gs (step w g)

def CommonZeros (a b c : List Bool) : Prop :=
  ∀ i, a.getD i false = false → b.getD i false = false → c.getD i false = false

lemma gate_common_zeros {a b c : List Bool} (h : CommonZeros a b c) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2)
    (ht : g.op = .and →
      (g.inputs.map (fun i => a.getD i false)).headD false =
      (g.inputs.map (fun i => b.getD i false)).headD false)
    (ha : g.op.eval (g.inputs.map fun i => a.getD i false) = false)
    (hb : g.op.eval (g.inputs.map fun i => b.getD i false) = false) :
    g.op.eval (g.inputs.map fun i => c.getD i false) = false := by
  rcases g with ⟨op, inputs⟩
  rcases hop with rfl | rfl
  · cases inputs with
    | nil => simp [GateOp.eval] at ha
    | cons i is =>
      cases is with
      | nil =>
        simpa [GateOp.eval] using h i (by simpa [GateOp.eval] using ha)
          (by simpa [GateOp.eval] using hb)
      | cons j js =>
        have hj : js = [] := by simpa using hlen
        subst js
        have ht' : a.getD i false = b.getD i false := by simpa using ht rfl
        have hi := h i
        have hj := h j
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
          List.all_nil, id_eq, Bool.and_true] at ha hb ⊢
        cases hai : a.getD i false <;> simp_all
  · simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq] at ha hb ⊢
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    simpa using h i (by simpa using ha _ ⟨i, hi, rfl⟩)
      (by simpa using hb _ ⟨i, hi, rfl⟩)

lemma common_zeros_append {a b c : List Bool} (h : CommonZeros a b c)
    (hab : a.length = b.length) (hac : a.length = c.length)
    {x y z : Bool} (hz : x = false → y = false → z = false) :
    CommonZeros (a ++ [x]) (b ++ [y]) (c ++ [z]) := by
  intro i hi hj
  by_cases hl : i < a.length
  · rw [List.getD_append _ _ _ _ hl] at hi
    rw [List.getD_append _ _ _ _ (by omega)] at hj
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi hj
  · have hl' : a.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hl'] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hab] at hj
    rw [List.getD_append_right _ _ _ _ (by omega), ← hac]
    cases hd : i - a.length with
    | zero => simp_all
    | succ j => simp

lemma run_common_zeros (gs : List Gate) {a b c : List Bool}
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (h : CommonZeros a b c) (hab : a.length = b.length) (hac : a.length = c.length)
    (ht : ∀ j g, gs[j]? = some g → g.op = .and →
      (trace gs a).getD j false = (trace gs b).getD j false) :
    CommonZeros (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs generalizing a b c with
  | nil => exact h
  | cons g gs ih =>
    have hg := hm g (by simp)
    apply ih
    · intro g' hg'
      exact hm g' (by simp [hg'])
    · apply common_zeros_append h hab hac
      apply gate_common_zeros h g hg.1 hg.2
      intro hgand
      simpa [trace] using ht 0 g (by simp) hgand
    · simp [step, hab]
    · simp [step, hac]
    · intro j g' hj hgand
      simpa [trace] using ht (j + 1) g' (by simpa using hj) hgand

lemma input_common_zeros {n : ℕ} (x y : Fin n → Bool) :
    CommonZeros (List.ofFn x) (List.ofFn y) (List.ofFn fun i => x i || y i) := by
  intro i hx hy
  by_cases hi : i < n
  · simp [hi] at hx hy ⊢
    simp [hx, hy]
  · simp [show n ≤ i by omega]

end PEqualNP.Outside.MaximalZeros

open PEqualNP.Outside.MaximalZeros

theorem PEqualNP.Outside.L_meta_216 :
    ∀ (n k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 C →
    (∃ A : Finset ℕ, A.card ≤ k ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) →
    {x : Fin n → Bool | C.eval (List.ofFn x) = false ∧
      ∀ y : Fin n → Bool, (∀ i : Fin n, x i = true → y i = true) →
        C.eval (List.ofFn y) = false → y = x}.ncard ≤ 2 ^ k := by
  classical
  intro n k C hm hA
  obtain ⟨A, hAk, hA⟩ := hA
  let code : (Fin n → Bool) → (A → Bool) :=
    fun x j => (trace C.gates (List.ofFn x)).getD j false
  have hinj : Set.InjOn code
      {x : Fin n → Bool | C.eval (List.ofFn x) = false ∧
        ∀ y : Fin n → Bool, (∀ i : Fin n, x i = true → y i = true) →
          C.eval (List.ofFn y) = false → y = x} := by
    intro x hx y hy heq
    have hrun := run_common_zeros C.gates
      (a := List.ofFn x) (b := List.ofFn y) (c := List.ofFn fun i => x i || y i)
      (by simpa [PEqualNP.MetaComplexity.Monotone2] using hm)
      (input_common_zeros x y) (by simp) (by simp)
      (fun j g hj hg => congrFun heq ⟨j, hA j g hj hg⟩)
    have hzero : C.eval (List.ofFn fun i => x i || y i) = false :=
      hrun C.output hx.1 hy.1
    have hzx := hx.2 (fun i => x i || y i) (by intros; simp_all) hzero
    have hzy := hy.2 (fun i => x i || y i) (by intros; simp_all) hzero
    exact hzx.symm.trans hzy
  have hcard := Set.ncard_le_ncard_of_injOn code (t := Set.univ)
    (fun _ _ => Set.mem_univ _) hinj
  have hbound : 2 ^ A.card ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hAk
  apply le_trans _ hbound
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using hcard
