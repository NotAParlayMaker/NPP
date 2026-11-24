import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4249

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_sn (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  rcases lt_trichotomy i w.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def rho (n m : ℕ) (a : Fin n) (σ : Fin n → Fin m) (i : ℕ) : ℕ :=
  if h : i < n then (if (⟨i, h⟩ : Fin n) = a then m else (σ ⟨i, h⟩).val) else i - n + m + 1

theorem rho_lt (n m : ℕ) (a : Fin n) (σ : Fin n → Fin m) (i : ℕ) (h : i < n) :
    rho n m a σ i < m + 1 := by
  rw [rho, dif_pos h]
  split
  · omega
  · have := (σ ⟨i, h⟩).isLt
    omega

theorem rho_ge (n m : ℕ) (a : Fin n) (σ : Fin n → Fin m) (i : ℕ) (h : ¬ i < n) :
    rho n m a σ i = i - n + m + 1 := by
  rw [rho, dif_neg h]

def rg (n m : ℕ) (a : Fin n) (σ : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rho n m a σ)⟩

theorem run_rho (n m : ℕ) (a : Fin n) (σ : Fin n → Fin m) (gs : List Gate) (x z : List Bool)
    (hx : x.length = n) (hz : z.length = m + 1)
    (h : ∀ i < n, z.getD (rho n m a σ i) false = x.getD i false) :
    ∀ i, (run (gs.map (rg n m a σ)) z).getD (rho n m a σ i) false = (run gs x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    change z.getD _ false = x.getD i false
    by_cases hi : i < n
    · exact h i hi
    · rw [rho_ge n m a σ i hi, List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    intro i
    have e : (rg n m a σ g).op.eval ((rg n m a σ g).inputs.map fun k =>
        (run (gs.map (rg n m a σ)) z).getD k false) =
        g.op.eval (g.inputs.map fun k => (run gs x).getD k false) := by
      simp only [rg, List.map_map]
      exact congrArg _ (List.map_congr_left fun k _ => ih k)
    rw [List.map_append, List.map_singleton, run_snoc, run_snoc, getD_sn, getD_sn, e, ih,
      run_length, run_length, List.length_map, hx, hz]
    have hiff : rho n m a σ i = m + 1 + gs.length ↔ i = n + gs.length := by
      by_cases hi : i < n
      · have := rho_lt n m a σ i hi
        omega
      · rw [rho_ge n m a σ i hi]
        omega
    simp only [hiff]

theorem main (n m : ℕ) (a : Fin n) (p q : Fin m) (σ : Fin n → Fin m) (C : Circuit)
    (h1 : Monotone2 C) (h2 : NestedCover.ReadsBack n C) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack m D ∧ D.size ≤ C.size + 1 ∧
      ∀ y : Fin m → Bool, circuitFun m D y =
        circuitFun n C fun i => if i = a then y p || y q else y (σ i) := by
  let g0 : Gate := ⟨GateOp.or, [p.val, q.val]⟩
  refine ⟨⟨g0 :: C.gates.map (rg n m a σ), rho n m a σ C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.1 hg with h | h
    · subst h; simp [g0]
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 h
      simpa [rg] using h1 g' hg'
  · intro j hj i hi
    have hp := p.isLt
    have hq := q.isLt
    rcases j with _ | j
    · simp [NestedCover.gateAt, g0] at hi
      omega
    · have hj' : j < C.gates.length := by simpa using hj
      have hi2 : i ∈ (rg n m a σ C.gates[j]).inputs := by
        simpa [NestedCover.gateAt, hj'] using hi
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hi2
      have hk2 : k < n + j := h2 j hj' k (by simpa [NestedCover.gateAt, hj'] using hk)
      by_cases hkn : k < n
      · have := rho_lt n m a σ k hkn
        omega
      · rw [rho_ge n m a σ k hkn]
        omega
  · simp [Circuit.size]
  · intro y
    have hr : run (g0 :: C.gates.map (rg n m a σ)) (List.ofFn y) =
        run (C.gates.map (rg n m a σ)) (List.ofFn y ++ [y p || y q]) := by
      simp [run, g0, GateOp.eval, List.getD_eq_getElem?_getD]
    change (run (g0 :: C.gates.map (rg n m a σ)) (List.ofFn y)).getD _ false = _
    rw [hr]
    refine run_rho n m a σ C.gates (List.ofFn fun i => if i = a then y p || y q else y (σ i)) _
      (by simp) (by simp) (fun i hi => ?_) C.output
    rw [rho, dif_pos hi, getD_sn, List.length_ofFn]
    by_cases h : (⟨i, hi⟩ : Fin n) = a
    · simp [h, hi, List.getD_eq_getElem?_getD]
    · have hlt := (σ ⟨i, hi⟩).isLt
      rw [if_neg h, if_neg (by omega)]
      simp [h, hi, List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_4249

open PEqualNP.Outside.L_meta_4249 in
theorem PEqualNP.Outside.L_meta_4249 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 : ℕ) x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (17 : ℕ) x4 ∧ x4.size ≤ x1.size + (1 : ℕ) ∧ ∀ (x5 : Fin (17 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x4 x5 = PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x1 fun (x6 : Fin (16 : ℕ)) => if ↑x6 = (10 : ℕ) then x5 (10 : Fin (17 : ℕ)) || x5 (15 : Fin (17 : ℕ)) else if ↑x6 = (15 : ℕ) then x5 (16 : Fin (17 : ℕ)) else x5 x6.castSucc := by
  intro C h1 h2
  obtain ⟨D, d1, d2, d3, d4⟩ := main 16 17 10 10 15
    (fun i => if i.val = 15 then 16 else i.castSucc) C h1 h2
  refine ⟨D, d1, d2, d3, fun y => ?_⟩
  rw [d4]
  congr 1
  funext i
  fin_cases i <;> simp
