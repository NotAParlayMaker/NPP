import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2400000 in
set_option maxRecDepth 2048 in
theorem PEqualNP.Outside.R_meta_2917_13
    (baseline : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [Bool.false]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (15 : ℕ) ≤ x1.size)
    (install :
      let rows (v : Fin 9) (mode : Fin 3) (x : Fin 9 → Bool) := List.ofFn x ++ [if mode = 1 then false else !x 0, if mode = 2 then false else !x v]
      (∀ (v : Fin 9) (C : Circuit), FanInTwo C → ∀ mode : Fin 3,
        ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size + (if mode = 0 then 2 else 1) ∧
          ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) = C.eval (rows v mode x)) ∧
      (∀ (σ : Fin 9 → Fin 9) (C : Circuit), FanInTwo C →
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          ∀ (x : Fin 9 → Bool) (a b : Bool),
            D.eval (List.ofFn x ++ [a, b]) = C.eval (List.ofFn (x ∘ σ) ++ [a, b])))
    (highDegree :
      let rows (v : Fin 9) (mode : Fin 3) (x : Fin 9 → Bool) := List.ofFn x ++ [if mode = 1 then false else !x 0, if mode = 2 then false else !x v]
      let graph (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (v : Fin 9), (v.val = 5 ∨ v.val = 8) →
        ∀ C : Circuit, FanInTwo C → C.size = 13 →
          (∃ x : Fin 9 → Bool, x 0 = false ∧ C.eval (rows v 0 x) ≠ C.eval (rows v 1 x)) →
          (∃ x : Fin 9 → Bool, x v = false ∧ C.eval (rows v 0 x) ≠ C.eval (rows v 2 x)) →
          ∃ x : Fin 9 → Bool, C.eval (rows v 0 x) ≠ graph x)
    (lowDegree :
      let rows (v : Fin 9) (mode : Fin 3) (x : Fin 9 → Bool) := List.ofFn x ++ [if mode = 1 then false else !x 0, if mode = 2 then false else !x v]
      let graph (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (v : Fin 9), v = 6 →
        ∀ C : Circuit, FanInTwo C → C.size = 13 →
          (∃ x : Fin 9 → Bool, x 0 = false ∧ C.eval (rows v 0 x) ≠ C.eval (rows v 1 x)) →
          (∃ x : Fin 9 → Bool, x v = false ∧ C.eval (rows v 0 x) ≠ C.eval (rows v 2 x)) →
          ∃ x : Fin 9 → Bool, C.eval (rows v 0 x) ≠ graph x) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     (5 : ℕ) ≤ x1.headD (10 : ℕ) ∧ x1.headD (10 : ℕ) ≤ (8 : ℕ) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro pins _length hhead C fan size
  by_contra! computes
  dsimp only at computes
  push Not at computes
  let graph (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let rows (v : Fin 9) (mode : Fin 3) (x : Fin 9 → Bool) := List.ofFn x ++ [if mode = 1 then false else !x 0, if mode = 2 then false else !x v]
  obtain ⟨installModes, relabel⟩ := install
  cases pins with
  | nil => simp at hhead
  | cons i rest =>
    change 5 ≤ i ∧ i ≤ 8 at hhead
    let v : Fin 9 := ⟨i, by omega⟩
    have hrow (x : Fin 9 → Bool) : C.eval (rows v 0 x) = graph x := by
      have hw : (List.ofFn x ++ [!x 0]).getD i false = x v := by
        have h : i < (List.ofFn x).length := by simp; omega
        rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h, List.getElem_ofFn]
      have h := computes x
      change C.eval ((List.ofFn x ++ [!x 0]) ++ [!((List.ofFn x ++ [!x 0]).getD i false)])
        = graph x at h
      rw [hw, List.append_assoc] at h
      exact h
    obtain ⟨D, hD, hbudget, same⟩ := installModes v C fan 0
    have needed := baseline D hD (fun x => (same x).trans (hrow x))
    have hbudget' : D.size ≤ C.size + 2 := hbudget
    have tight : C.size = 13 := by omega
    have sensitivity (j : Fin 9) (mode : Fin 3) (nonzero : mode ≠ 0)
        (unchanged : ∀ x : Fin 9 → Bool, x j = true → rows v mode x = rows v 0 x) :
        ∃ x : Fin 9 → Bool, x j = false ∧ C.eval (rows v 0 x) ≠ C.eval (rows v mode x) := by
      by_contra absent
      have computesWithOne (x : Fin 9 → Bool) : C.eval (rows v mode x) = graph x := by
        by_cases hx : x j = false
        · have heq : C.eval (rows v 0 x) = C.eval (rows v mode x) := by
            by_contra hn
            exact absent ⟨x, hx, hn⟩
          exact heq.symm.trans (hrow x)
        · have on : x j = true := by cases h : x j <;> simp [h] at hx ⊢
          exact (congrArg C.eval (unchanged x on)).trans (hrow x)
      obtain ⟨T, hT, hcost, hs⟩ := installModes v C fan mode
      rw [ite_eq_right nonzero] at hcost
      have hgate := baseline T hT (fun x => (hs x).trans (computesWithOne x))
      omega
    have leftEssential := sensitivity 0 1 (by decide) (by
      intro x hx
      change (List.ofFn x ++ [false, !x v]) = (List.ofFn x ++ [!x 0, !x v])
      rw [hx]
      rfl)
    have rightEssential := sensitivity v 2 (by decide) (by
      intro x hx
      change (List.ofFn x ++ [!x 0, false]) = (List.ofFn x ++ [!x 0, !x v])
      rw [hx]
      rfl)
    by_cases degree : v.val = 5 ∨ v.val = 8
    · obtain ⟨x, other⟩ := highDegree v degree C fan tight leftEssential rightEssential
      exact other (hrow x)
    · have limits : 5 ≤ v.val ∧ v.val ≤ 8 := hhead
      have small : v.val = 6 ∨ v.val = 7 := by omega
      rcases small with h6 | h7
      · obtain ⟨x, other⟩ := lowDegree v (Fin.ext h6) C fan tight leftEssential rightEssential
        exact other (hrow x)
      let σ : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
      have v7 : v = 7 := Fin.ext h7
      have σ0 : σ 0 = 0 := by decide +kernel
      have σ6 : σ 6 = v := by rw [v7]; decide +kernel
      have σv : σ v = 6 := by rw [v7]; decide +kernel
      have inv : ∀ i : Fin 9, σ (σ i) = i := by decide +kernel
      have graphSym : ∀ x : Fin 9 → Bool, graph (x ∘ σ) = graph x := by
        decide +kernel
      have twice (x : Fin 9 → Bool) : (x ∘ σ) ∘ σ = x := by
        funext i
        exact congrArg x (inv i)
      obtain ⟨U, hU, hsizeU, hcopy⟩ := relabel σ C fan
      have simulated (m : Fin 3) (x : Fin 9 → Bool) :
          U.eval (rows 6 m x) = C.eval (rows v m (x ∘ σ)) := by
        simpa only [rows, Function.comp_apply, σ0, σv] using
          hcopy x (if m = 1 then false else !x 0) (if m = 2 then false else !x 6)
      have leftU : ∃ x : Fin 9 → Bool, x 0 = false ∧
          U.eval (rows 6 0 x) ≠ U.eval (rows 6 1 x) := by
        obtain ⟨x, hx, diff⟩ := leftEssential
        refine ⟨x ∘ σ, ?_, ?_⟩
        · simpa only [Function.comp_apply, σ0] using hx
        · simpa only [simulated, twice] using diff
      have rightU : ∃ x : Fin 9 → Bool, x 6 = false ∧
          U.eval (rows 6 0 x) ≠ U.eval (rows 6 2 x) := by
        obtain ⟨x, hx, diff⟩ := rightEssential
        refine ⟨x ∘ σ, ?_, ?_⟩
        · simpa only [Function.comp_apply, σ6] using hx
        · simpa only [simulated, twice] using diff
      obtain ⟨x, other⟩ := lowDegree 6 rfl U hU (hsizeU.trans tight) leftU rightU
      exact other ((simulated 0 x).trans ((hrow (x ∘ σ)).trans (graphSym x)))
