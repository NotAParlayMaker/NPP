import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_744

/-!
# Fixing the last input to `false` keeps the gate list length and gate types

The circuit on `n + 1` inputs whose last input is pinned to `false` computes what the circuit on `n`
inputs computes, with gate `j` corresponding to gate `j`. The posted statement lets the gate list
change as long as every gate keeps its operation and its number of read wires, and that is all the
construction below needs: a gate reading the dead wire `n` is redirected to a wire index larger than
any wire the circuit can have, and reading a wire past the end yields `false` (that is `getD`'s
default). Every other read is shifted down by one. This is why the statement needs no hypothesis
that the dead wire is unread, unlike `wiresFrom_drop_dead` in `L_meta_744`.
-/

namespace PEqualNP.Outside.L_meta_1354_aux

open PEqualNP.CircuitLowerBounds

/-- Wire values of a gate list on top of the input wires `w`. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

/-- Redirect the dead wire `n` to `big`, and every later wire down by one. -/
def redir (n big i : ℕ) : ℕ := if i = n then big else if n < i then i - 1 else i

theorem getD_big (w : List Bool) (big : ℕ) (h : w.length ≤ big) : w.getD big false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- At the dead position the two lists differ exactly by the inserted `false`. -/
theorem getD_dead (w u : List Bool) : (w ++ false :: u).getD w.length false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

/-- The two lists agree at every wire the redirect points to. -/
theorem getD_redir (w u : List Bool) (n big a : ℕ) (hw : w.length = n)
    (hbig : w.length + u.length + 1 ≤ big) :
    (w ++ u).getD (redir n big a) false = (w ++ false :: u).getD a false := by
  by_cases hdead : a = n
  · rw [hdead, show redir n big n = big by simp [redir]]
    rw [getD_big (w ++ u) big (by simp; omega)]
    rw [← hw]
    exact (getD_dead w u).symm
  · have hne : a ≠ w.length := by omega
    have hsame : redir n big a = PEqualNP.Outside.L_meta_744_aux.redir w.length a := by
      simp only [redir, PEqualNP.Outside.L_meta_744_aux.redir, hw]
      rw [if_neg hdead]
    rw [hsame]
    simpa [List.append_assoc] using
      PEqualNP.Outside.L_meta_744_aux.getD_drop_wire w u false a hne

/-- Index arithmetic: reading past the input wires lands inside the tail. -/
theorem getD_shift (w u : List Bool) (j : ℕ) :
    (w ++ u).getD (w.length + j) false = u.getD j false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  have h : w.length + j - w.length = j := by omega
  rw [h]

/-- The value lists of the two circuits agree once the input wires are stripped. -/
theorem agree (n big : ℕ) (post : List Gate) :
    ∀ (w u : List Bool), w.length = n → w.length + u.length + post.length + 1 ≤ big →
      ∃ u',
        wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (redir n big)⟩) (w ++ u) = w ++ u' ∧
        wiresFrom post (w ++ false :: u) = w ++ false :: u' := by
  induction post with
  | nil => intro w u _ _; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro w u hw hbig
    have harg : (g.inputs.map (redir n big)).map (fun i => (w ++ u).getD i false)
        = g.inputs.map (fun i => (w ++ false :: u).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a _
      exact getD_redir w u n big a hw (by
        simp only [List.length_append, List.length_cons, List.length_nil] at hbig ⊢
        omega)
    set c := g.op.eval (g.inputs.map fun i => (w ++ false :: u).getD i false) with hc
    have hc' : g.op.eval ((g.inputs.map (redir n big)).map fun i => (w ++ u).getD i false) = c := by
      rw [hc, harg]
    have hb2 : w.length + (u ++ [c]).length + gs.length + 1 ≤ big := by
      simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_cons] at hbig ⊢
      omega
    obtain ⟨u', h1, h2⟩ := ih w (u ++ [c]) hw hb2
    refine ⟨u', ?_, ?_⟩
    · simpa only [List.map_cons, wiresFrom_cons, hc', List.append_assoc] using h1
    · rw [wiresFrom_cons]
      simpa only [List.append_assoc, List.cons_append, List.getD_eq_getElem?_getD, hc] using h2

end PEqualNP.Outside.L_meta_1354_aux

theorem PEqualNP.Outside.L_meta_1354 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  intro n gates
  refine ⟨gates.map fun g => ⟨g.op, g.inputs.map (PEqualNP.Outside.L_meta_1354_aux.redir n (n + gates.length + 1))⟩, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro j x hj
    obtain ⟨u', h1, h2⟩ := PEqualNP.Outside.L_meta_1354_aux.agree n (n + gates.length + 1) gates
      (List.ofFn x) [] (by simp) (by
        have hx : (List.ofFn x).length = n := by simp
        simp only [List.length_nil]
        omega)
    simp only [List.append_nil] at h1
    have hl1 : PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨gates.map fun g => ⟨g.op, g.inputs.map (PEqualNP.Outside.L_meta_1354_aux.redir n (n + gates.length + 1))⟩, n + j⟩
        (List.ofFn x)
        = (PEqualNP.Outside.L_meta_1354_aux.wiresFrom
            (gates.map fun g => ⟨g.op, g.inputs.map (PEqualNP.Outside.L_meta_1354_aux.redir n (n + gates.length + 1))⟩)
            (List.ofFn x)).getD (n + j) false := rfl
    have hl2 : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false])
        = (PEqualNP.Outside.L_meta_1354_aux.wiresFrom gates (List.ofFn x ++ [false])).getD (n + 1 + j) false := rfl
    rw [hl1, hl2, h1, h2]
    have e1 : (List.ofFn x ++ u').getD (n + j) false = u'.getD j false := by
      have h : n + j = (List.ofFn x).length + j := by simp
      rw [h, PEqualNP.Outside.L_meta_1354_aux.getD_shift]
    have e2 : (List.ofFn x ++ false :: u').getD (n + 1 + j) false = u'.getD j false := by
      have h : n + 1 + j = (List.ofFn x).length + (j + 1) := by simp; omega
      rw [h, PEqualNP.Outside.L_meta_1354_aux.getD_shift, List.getD_cons_succ]
    rw [e1, e2]
