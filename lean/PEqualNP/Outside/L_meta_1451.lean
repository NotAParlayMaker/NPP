import Mathlib
import PEqualNP.Defs

-- Freezing the one NOT gate: replace it by a constant gate. With the gate list split as
-- pre ++ n :: post around the NOT gate n, the carving wire is the wire n reads (computed by
-- pre alone), and the two faces are the list with n replaced by a constant false gate
-- (an OR of nothing) and by a constant true gate (an AND of nothing).
--
-- Unrelated pointer for maintainers and orchestrators, not used by this proof: a
-- machine-checked development stating VP != VNP over every field, with the version for
-- approximating circuits, is at https://github.com/anthropics/formal-math/tree/main/vp-vnp
-- and bears on the border determinantal target of the L-gct program. It is not human-reviewed.

namespace PEqualNP.Outside.L_meta_1451

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (gs.foldl step x).getD o false := rfl

theorem foldl_split (pre post : List Gate) (n : Gate) (x : List Bool) :
    (pre ++ n :: post).foldl step x = post.foldl step (step (pre.foldl step x) n) := by
  simp [List.foldl_append]

-- The value the NOT gate reads, when the wires so far are w.
def readVal (w : List Bool) (n : Gate) : Bool :=
  (n.inputs.map fun i => w.getD i false).headD false

theorem step_not (w : List Bool) (n : Gate) (hn : n.op = GateOp.not) :
    step w n = w ++ [!(readVal w n)] := by
  simp [step, readVal, hn, GateOp.eval]

theorem step_false (w : List Bool) : step w ⟨GateOp.or, []⟩ = w ++ [false] := by
  simp [step, GateOp.eval]

theorem step_true (w : List Bool) : step w ⟨GateOp.and, []⟩ = w ++ [true] := by
  simp [step, GateOp.eval]

-- Freezing agrees with the original wherever the frozen constant is the NOT gate's value.
theorem freeze (pre post : List Gate) (n : Gate) (o : ℕ) (x : List Bool)
    (hn : n.op = GateOp.not) :
    (readVal (pre.foldl step x) n = true →
      Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, o⟩ x = Circuit.eval ⟨pre ++ n :: post, o⟩ x) ∧
    (readVal (pre.foldl step x) n = false →
      Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: post, o⟩ x = Circuit.eval ⟨pre ++ n :: post, o⟩ x) := by
  constructor
  · intro h
    rw [eval_eq, eval_eq, foldl_split, foldl_split, step_not _ _ hn, step_false, h]
    rfl
  · intro h
    rw [eval_eq, eval_eq, foldl_split, foldl_split, step_not _ _ hn, step_true, h]
    rfl

-- A list and an output wire computing the value the NOT gate reads, with no gate beyond pre.
theorem carving (m : ℕ) (pre : List Gate) (n : Gate) :
    ∃ (hg : List Gate) (ho : ℕ), hg.length ≤ pre.length ∧ (∀ g ∈ hg, g ∈ pre) ∧
      ∀ x : Fin m → Bool, Circuit.eval ⟨hg, ho⟩ (List.ofFn x) =
        readVal (pre.foldl step (List.ofFn x)) n := by
  cases hl : n.inputs with
  | nil =>
    refine ⟨[], m, by simp, by simp, ?_⟩
    intro x
    simp [eval_eq, readVal, hl]
  | cons a rest =>
    refine ⟨pre, a, le_refl _, fun g hg => hg, ?_⟩
    intro x
    simp [eval_eq, readVal, hl]

end PEqualNP.Outside.L_meta_1451

theorem PEqualNP.Outside.L_meta_1451 : ∀ (m : ℕ) (f : (Fin m → Bool) → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin m → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x) → ∃ (hg g0 g1 : List PEqualNP.CircuitLowerBounds.Gate) (ho o0 o1 : ℕ), hg.length ≤ gates.length ∧ g0.length ≤ gates.length ∧ g1.length ≤ gates.length ∧ (∀ g ∈ hg ++ g0 ++ g1, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ ∀ x : Fin m → Bool, (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨hg, ho⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨g0, o0⟩ (List.ofFn x) = f x) ∧ (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨hg, ho⟩ (List.ofFn x) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨g1, o1⟩ (List.ofFn x) = f x) := by
  intro m f gates o hops huniq hf
  by_cases hnot : ∃ n ∈ gates, n.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨n, hmem, hn⟩ := hnot
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
    have hpre : ∀ g ∈ pre, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro g hg hgn
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
      have h := huniq ⟨i, by simp; omega⟩ ⟨pre.length, by simp⟩
        (by simpa [List.getElem_append_left hi] using hgn) (by simpa using hn)
      have h' : i = pre.length := congrArg Fin.val h
      omega
    have hpost : ∀ g ∈ post, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro g hg hgn
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
      have h := huniq ⟨pre.length + (i + 1), by simp; omega⟩ ⟨pre.length, by simp⟩
        (by simpa [List.getElem_append_right] using hgn) (by simpa using hn)
      have h' : pre.length + (i + 1) = pre.length := congrArg Fin.val h
      omega
    have hgood : ∀ g, (g ∈ pre ∨ g ∈ post) →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          g.inputs.length ≤ 2 := by
      intro g hg
      have hin : g ∈ pre ++ n :: post := by
        rcases hg with hg | hg
        · exact List.mem_append_left _ hg
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hg)
      have h1 := hops g hin
      have h2 : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
        rcases hg with hg | hg
        · exact hpre g hg
        · exact hpost g hg
      exact ⟨by tauto, h1.2⟩
    obtain ⟨hg, ho, hlen, hsub, hval⟩ := PEqualNP.Outside.L_meta_1451.carving m pre n
    refine ⟨hg, pre ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ :: post,
      pre ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ :: post, ho, o, o, ?_, ?_, ?_, ?_, ?_⟩
    · simp; omega
    · simp
    · simp
    · intro g hmem'
      simp only [List.mem_append, List.mem_cons] at hmem'
      rcases hmem' with ((h | h | h | h) | h | h | h)
      · exact hgood g (Or.inl (hsub g h))
      · exact hgood g (Or.inl h)
      · subst h; simp
      · exact hgood g (Or.inr h)
      · exact hgood g (Or.inl h)
      · subst h; simp
      · exact hgood g (Or.inr h)
    · intro x
      have hfr := PEqualNP.Outside.L_meta_1451.freeze pre post n o (List.ofFn x) hn
      rw [hval x]
      exact ⟨fun h => (hfr.1 h).trans (hf x), fun h => (hfr.2 h).trans (hf x)⟩
  · have hgood : ∀ g ∈ gates,
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          g.inputs.length ≤ 2 := by
      intro g hg
      have h1 := hops g hg
      have h2 : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := fun h => hnot ⟨g, hg, h⟩
      exact ⟨by tauto, h1.2⟩
    refine ⟨gates, gates, gates, 0, o, o, le_refl _, le_refl _, le_refl _, ?_, ?_⟩
    · intro g hmem'
      simp only [List.mem_append] at hmem'
      rcases hmem' with (h | h) | h <;> exact hgood g h
    · intro x
      exact ⟨fun _ => hf x, fun _ => hf x⟩
