import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17213

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- Column vector of a new gate: bit `r` is the gate's value on row `r`. -/
def newvec (full : ℕ) (cols : List ℕ) (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [] => full
  | GateOp.and, [a] => cols.getD a 0
  | GateOp.and, a :: b :: _ => cols.getD a 0 &&& cols.getD b 0
  | GateOp.or, [] => 0
  | GateOp.or, [a] => cols.getD a 0
  | GateOp.or, a :: b :: _ => cols.getD a 0 ||| cols.getD b 0
  | GateOp.not, [] => full
  | GateOp.not, a :: _ => full ^^^ cols.getD a 0
  | _, _ => 0

def absStep (full : ℕ) (cols : List ℕ) (g : Gate) : List ℕ := cols ++ [newvec full cols g]

def cl (full : ℕ) (S : List ℕ) : List ℕ :=
  full :: 0 :: S.flatMap fun a => a :: (full ^^^ a) :: S.flatMap fun b => [a &&& b, a ||| b]

theorem getD_mem (l : List ℕ) (i : ℕ) : l.getD i 0 ∈ 0 :: l := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simp
  | some x => simp only [Option.getD_some]; exact List.mem_cons_of_mem _ (List.mem_of_getElem? h)

theorem newvec_bit (full R r : ℕ) (hr : r < R) (hfull : ∀ k < R, full.testBit k = true)
    (cols : List ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
    (newvec full cols g).testBit r = g.op.eval (g.inputs.map fun i => (cols.getD i 0).testBit r) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
    first
    | (exfalso; simp at hlen; done)
    | (exfalso; simp at hlen; omega)
    | simp [newvec, GateOp.eval, hfull r hr, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]

theorem newvec_mem (full : ℕ) (cols : List ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
    newvec full cols g ∈ cl full (0 :: cols) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have two : ∀ a b : ℕ, cols.getD a 0 &&& cols.getD b 0 ∈ cl full (0 :: cols) ∧
      cols.getD a 0 ||| cols.getD b 0 ∈ cl full (0 :: cols) := by
    intro a b
    constructor <;>
    · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, getD_mem cols a, ?_⟩))
      refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, getD_mem cols b, ?_⟩))
      simp
  have one : ∀ a : ℕ, cols.getD a 0 ∈ cl full (0 :: cols) ∧ full ^^^ cols.getD a 0 ∈ cl full (0 :: cols) := by
    intro a
    constructor <;>
    · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, getD_mem cols a, ?_⟩))
      simp
  have hfull : full ∈ cl full (0 :: cols) := List.mem_cons_self
  have hzero : 0 ∈ cl full (0 :: cols) := List.mem_cons_of_mem _ List.mem_cons_self
  rcases hop with rfl | rfl | rfl <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
    first
    | (exfalso; simp at hlen; done)
    | (exfalso; simp at hlen; omega)
    | exact hfull
    | exact hzero
    | exact (one a).1
    | exact (one a).2
    | exact (two a b).1
    | exact (two a b).2

theorem inv (full R r : ℕ) (hr : r < R) (hfull : ∀ k < R, full.testBit k = true) :
    ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) →
      ∀ (w : List Bool) (cols : List ℕ), w.length = cols.length →
        (∀ i, w.getD i false = (cols.getD i 0).testBit r) →
        ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false =
          ((gs.foldl (absStep full) cols).getD i 0).testBit r := by
  intro gs
  induction gs with
  | nil => intro _ w cols _ h i; exact h i
  | cons g gs ih =>
    intro hf w cols hl h
    simp only [List.foldl_cons]
    have e : g.op.eval (g.inputs.map fun i => w.getD i false) = (newvec full cols g).testBit r := by
      rw [newvec_bit full R r hr hfull cols g (hf g List.mem_cons_self).1 (hf g List.mem_cons_self).2]
      congr 1
      apply List.map_congr_left
      intro k _
      exact h k
    apply ih (fun g' hg' => hf g' (List.mem_cons_of_mem _ hg'))
    · simp [absStep, hl]
    · intro i
      have hi := h i
      rw [List.getD_eq_getElem?_getD] at hi ⊢
      rw [List.getD_eq_getElem?_getD] at hi ⊢
      unfold absStep
      rcases Nat.lt_trichotomy i w.length with hlt | heq | hgt
      · rw [List.getElem?_append_left hlt, List.getElem?_append_left (hl ▸ hlt)]; exact hi
      · subst heq
        rw [List.getElem?_append_right (Nat.le_refl _), List.getElem?_append_right (by omega)]
        rw [← hl, Nat.sub_self]; exact e
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        have h1 : i - w.length = (i - w.length - 1) + 1 := by omega
        have h2 : i - cols.length = (i - cols.length - 1) + 1 := by omega
        rw [h1, h2]
        simp

def base : List ℕ := [3, 12, 5, 10]

def good (X : ℕ) : Bool := X.testBit 0 && !X.testBit 1 && !X.testBit 2 && X.testBit 3

theorem base_inv (u v : Fin 2) (i : ℕ) :
    (oneEach u v).getD i false = (base.getD i 0).testBit (2 * u.val + v.val) := by
  by_cases hi : i < 4
  · interval_cases i <;> revert u v <;> decide
  · have h1 : (oneEach u v).length ≤ i := by simp [oneEach]; omega
    have h2 : base.length ≤ i := by simp [base]; omega
    rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]; simp

theorem check0 : ∀ X ∈ 0 :: base, good X = false := by decide +kernel
theorem check1 : ∀ v1 ∈ cl 15 (0 :: base), ∀ X ∈ 0 :: (base ++ [v1]), good X = false := by
  decide +kernel
theorem check2 : ∀ v1 ∈ cl 15 (0 :: base), ∀ v2 ∈ cl 15 (0 :: (base ++ [v1])),
    ∀ X ∈ 0 :: (base ++ [v1] ++ [v2]), good X = false := by
  decide +kernel

theorem core (C : Circuit) (A : Fin 2 → Fin 2 → Bool) (hA : ∀ u v, A u v = decide (u = v))
    (hf : FanInTwo C) (hr : Represents A C) : 3 ≤ C.size := by
  obtain ⟨gs, o⟩ := C
  have key : ∀ u v : Fin 2, A u v =
      (((gs.foldl (absStep 15) base).getD o 0)).testBit (2 * u.val + v.val) := by
    intro u v
    rw [← hr u v]
    exact inv 15 4 (2 * u.val + v.val) (by omega) (by decide) gs hf (oneEach u v) base
      (by simp [oneEach, base]) (base_inv u v) o
  have h00 : ((gs.foldl (absStep 15) base).getD o 0).testBit 0 = true := (key 0 0).symm.trans (hA 0 0)
  have h01 : ((gs.foldl (absStep 15) base).getD o 0).testBit 1 = false := (key 0 1).symm.trans (hA 0 1)
  have h10 : ((gs.foldl (absStep 15) base).getD o 0).testBit 2 = false := (key 1 0).symm.trans (hA 1 0)
  have h11 : ((gs.foldl (absStep 15) base).getD o 0).testBit 3 = true := (key 1 1).symm.trans (hA 1 1)
  have hg : good ((gs.foldl (absStep 15) base).getD o 0) = true := by
    unfold good; rw [h00, h01, h10, h11]; rfl
  have hm := getD_mem (gs.foldl (absStep 15) base) o
  by_contra hlt
  have hlen : gs.length ≤ 2 := by simp only [Circuit.size] at hlt; omega
  rcases gs with _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, t⟩⟩⟩
  · have := check0 _ hm; rw [hg] at this; exact Bool.noConfusion this
  · have h1 := newvec_mem 15 base g1 (hf g1 (by simp)).1 (hf g1 (by simp)).2
    have := check1 _ h1 _ hm; rw [hg] at this; exact Bool.noConfusion this
  · have h1 := newvec_mem 15 base g1 (hf g1 (by simp)).1 (hf g1 (by simp)).2
    have h2 := newvec_mem 15 (base ++ [newvec 15 base g1]) g2 (hf g2 (by simp)).1 (hf g2 (by simp)).2
    have := check2 _ h1 _ h2 _ hm; rw [hg] at this; exact Bool.noConfusion this
  · simp at hlen

end PEqualNP.Outside.L_meta_17213

open PEqualNP.Outside.L_meta_17213 in
theorem PEqualNP.Outside.L_meta_17213 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents (fun u v : Fin 2 => decide (u = v)) C → 3 ≤ C.size := by
  first
    | (intro C h1 h2; exact core C _ (by decide) h1 h2)
    | (rintro ⟨C, h1, h2, h3⟩; exact absurd (core C _ (by decide) h1 h3) (by omega))
    | (intro C h1 h2 h3; exact absurd (core C _ (by decide) h1 h3) (by omega))
    | (rintro s ⟨C, h1, h2, h3⟩; exact le_trans (core C _ (by decide) h1 h3) h2)
