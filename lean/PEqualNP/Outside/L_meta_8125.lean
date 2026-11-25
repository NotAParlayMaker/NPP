import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8125_aux

open PEqualNP.CircuitLowerBounds

def pairIn : List ℕ → List ℕ
  | [a, b] => if a < b then [a, b] else if b < a then [b, a] else [a]
  | l => l

def normIn : GateOp → List ℕ → List ℕ
  | GateOp.and, l => pairIn l
  | GateOp.or, l => pairIn l
  | GateOp.not, l => l.take 1
  | _, l => l

def gnorm (g : Gate) : Gate := ⟨g.op, normIn g.op g.inputs⟩

theorem pairIn_sub (l : List ℕ) : ∀ x ∈ pairIn l, x ∈ l := by
  intro x hx
  match l with
  | [a, b] =>
    simp only [pairIn] at hx
    split_ifs at hx <;> simp at hx ⊢ <;> omega
  | [] => simpa [pairIn] using hx
  | [a] => simpa [pairIn] using hx
  | a :: b :: c :: t => simpa [pairIn] using hx

theorem normIn_sub (o : GateOp) (l : List ℕ) : ∀ x ∈ normIn o l, x ∈ l := by
  intro x hx
  cases o with
  | and => exact pairIn_sub l x hx
  | or => exact pairIn_sub l x hx
  | not => exact List.mem_of_mem_take hx
  | mod m => exact hx
  | maj => exact hx

theorem pairIn_all (f : ℕ → Bool) (l : List ℕ) :
    ((pairIn l).map f).all id = (l.map f).all id := by
  match l with
  | [a, b] =>
    simp only [pairIn]
    split_ifs with h1 h2
    · rfl
    · simp [Bool.and_comm]
    · have : a = b := by omega
      subst this; simp
  | [] => rfl
  | [a] => rfl
  | a :: b :: c :: t => rfl

theorem pairIn_any (f : ℕ → Bool) (l : List ℕ) :
    ((pairIn l).map f).any id = (l.map f).any id := by
  match l with
  | [a, b] =>
    simp only [pairIn]
    split_ifs with h1 h2
    · rfl
    · simp [Bool.or_comm]
    · have : a = b := by omega
      subst this; simp
  | [] => rfl
  | [a] => rfl
  | a :: b :: c :: t => rfl

theorem norm_eval (g : Gate) (f : ℕ → Bool) :
    (gnorm g).op.eval ((gnorm g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and => exact pairIn_all f l
  | or => exact pairIn_any f l
  | not =>
    cases l with
    | nil => rfl
    | cons a t => rfl
  | mod m => rfl
  | maj => rfl

theorem fold_eq (gs : List Gate) (x : List Bool) :
    (gs.map gnorm).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
      = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g t ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [norm_eval g (fun i => x.getD i false)]
    exact ih _

theorem pairIn_pw (l : List ℕ) (h : l.length ≤ 2) : List.Pairwise (fun x y => x < y) (pairIn l) := by
  match l with
  | [a, b] =>
    simp only [pairIn]
    split_ifs with h1 h2 <;> simp_all
  | [] => simp [pairIn]
  | [a] => simp [pairIn]
  | a :: b :: c :: t => simp at h

end PEqualNP.Outside.L_meta_8125_aux

open PEqualNP.Outside.L_meta_8125_aux in
theorem PEqualNP.Outside.L_meta_8125 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, ∀ x5 ∈ x3.inputs, x5 ≤ (29 : ℕ)) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size = x1.size ∧ x4.output = x1.output ∧ (∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (29 : ℕ)) ∧ (∀ x5 ∈ x4.gates, List.Pairwise (fun (x7 x8 : ℕ) => x7 < x8) x5.inputs ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ))) ∧ ∀ (x5 : List Bool), x4.eval x5 = x1.eval x5 := by
  intro x1 hf hb
  refine ⟨⟨x1.gates.map gnorm, x1.output⟩, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hf g0 hg0
    refine ⟨h1, ?_⟩
    obtain ⟨o, l⟩ := g0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with rfl | rfl | rfl
    · simp only [gnorm, normIn]
      match l with
      | [a, b] => simp only [pairIn]; split_ifs <;> simp
      | [] => simp [pairIn]
      | [a] => simp [pairIn]
      | a :: b :: c :: t => simp at h2
    · simp only [gnorm, normIn]
      match l with
      | [a, b] => simp only [pairIn]; split_ifs <;> simp
      | [] => simp [pairIn]
      | [a] => simp [pairIn]
      | a :: b :: c :: t => simp at h2
    · simp only [gnorm, normIn, List.length_take]; omega
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro g hg x hx
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact hb g0 hg0 x (normIn_sub _ _ x hx)
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hf g0 hg0
    obtain ⟨o, l⟩ := g0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with rfl | rfl | rfl
    · exact ⟨pairIn_pw l h2, fun h => by cases h⟩
    · exact ⟨pairIn_pw l h2, fun h => by cases h⟩
    · refine ⟨?_, fun _ => ?_⟩
      · cases l with
        | nil => simp [gnorm, normIn]
        | cons a t => simp [gnorm, normIn]
      · simp only [gnorm, normIn, List.length_take]; omega
  · intro x
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
    rw [fold_eq]
