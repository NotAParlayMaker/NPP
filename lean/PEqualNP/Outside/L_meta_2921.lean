import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2921

private def remap (σ : Fin 9 → Fin 9) (i : ℕ) : ℕ :=
  if h : i < 9 then (σ ⟨i, h⟩).1 else i

private lemma getD_append_single {α : Type*} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  induction l generalizing i with
  | nil =>
    cases i <;> simp [List.getD]
  | cons x xs ih =>
    cases i with
    | zero => simp [List.getD]
    | succ k =>
      simp only [List.cons_append, List.getD_cons_succ, List.length_cons, Nat.succ_lt_succ_iff,
        Nat.succ.injEq]
      exact ih k

private lemma foldl_wires_invariant (σ : Fin 9 → Fin 9) (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length) (h9 : 9 ≤ w2.length)
    (hinv : ∀ i : ℕ, w1.getD (remap σ i) Bool.false = w2.getD i Bool.false) :
    let gs' := gs.map (fun g => { op := g.op, inputs := g.inputs.map (remap σ) : PEqualNP.CircuitLowerBounds.Gate })
    let r1 := gs'.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) w1
    let r2 := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]) w2
    ∀ i : ℕ, r1.getD (remap σ i) Bool.false = r2.getD i Bool.false := by
  induction gs generalizing w1 w2 with
  | nil =>
    exact hinv
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hmap : List.map (fun i => w1.getD i Bool.false) (g.inputs.map (remap σ)) =
        List.map (fun i => w2.getD i Bool.false) g.inputs := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact hinv i
    rw [hmap]
    set b := g.op.eval (g.inputs.map fun i => w2.getD i Bool.false)
    apply ih (w1 ++ [b]) (w2 ++ [b])
    · simp [hlen]
    · simp; omega
    · intro i
      rw [getD_append_single, getD_append_single, hlen]
      by_cases hi : i < 9
      · have hrem : remap σ i < 9 := by
          simp only [remap, dif_pos hi]
          exact (σ ⟨i, hi⟩).isLt
        have h1 : remap σ i < w2.length := lt_of_lt_of_le hrem h9
        have h2 : i < w2.length := lt_of_lt_of_le hi h9
        rw [if_pos h1, if_pos h2]
        exact hinv i
      · have hrem : remap σ i = i := by simp [remap, hi]
        rw [hrem]
        split_ifs with hlt heq
        · have := hinv i
          rwa [hrem] at this
        · rfl
        · rfl

end PEqualNP.Outside.L_meta_2921

theorem PEqualNP.Outside.L_meta_2921 :
  ∀ (x1 : Fin (9 : ℕ) → Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (9 : ℕ) ≤ x4.length → (∀ (x7 : ℕ), x3.getD (if x8 : x7 < (9 : ℕ) then ↑(x1 (⟨x7, x8⟩ : Fin (9 : ℕ))) else x7) Bool.false = x4.getD x7 Bool.false) → { gates := List.map (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => { op := x8.op, inputs := List.map (fun (x9 : ℕ) => if x10 : x9 < (9 : ℕ) then ↑(x1 (⟨x9, x10⟩ : Fin (9 : ℕ))) else x9) x8.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := if x8 : x2.output < (9 : ℕ) then ↑(x1 (⟨x2.output, x8⟩ : Fin (9 : ℕ))) else x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x3 = x2.eval x4 := by
  intro x1 x2 x3 x4 hlen h9 hinv
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
  exact PEqualNP.Outside.L_meta_2921.foldl_wires_invariant x1 x2.gates x3 x4 hlen h9 hinv x2.output
