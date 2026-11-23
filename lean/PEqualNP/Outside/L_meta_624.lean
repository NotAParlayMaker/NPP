import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card

namespace PEqualNP.Outside.L_meta_624

open PEqualNP.CircuitLowerBounds

-- The point labels are 0 through 6. Line 7 + j represents the j-th translate
-- of the triple {0, 1, 3} in the cyclic group of order seven.
private def pointOnLine (p l : Nat) : Bool :=
  decide (p < 7 ∧ 7 ≤ l ∧
    (p = l - 7 ∨ p = (l - 7 + 1) % 7 ∨ p = (l - 7 + 3) % 7))

private def adjacent (u v : Fin 14) : Bool :=
  pointOnLine u.val v.val || pointOnLine v.val u.val

private def fano : SimpleGraph (Fin 14) where
  Adj u v := adjacent u v = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

private abbrev decideAdj : DecidableRel fano.Adj := fun u v =>
  inferInstanceAs (Decidable (adjacent u v = true))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fano_noC4 : ∀ a b c e : Fin 14,
    fano.Adj a b → fano.Adj b c → fano.Adj c e → fano.Adj e a → a = c ∨ b = e := by
  have h : ∀ a b : Fin 14, adjacent a b = true →
      ∀ c : Fin 14, adjacent b c = true →
      ∀ e : Fin 14, adjacent c e = true → adjacent e a = true → a = c ∨ b = e := by
    decide
  exact fun a b c e hab hbc hce hea => h a b hab c hbc e hce hea

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fano_edges : fano.edgeSet.ncard = 21 := by
  letI : DecidableRel fano.Adj := decideAdj
  calc fano.edgeSet.ncard = fano.edgeFinset.card := Set.ncard_eq_toFinset_card' _
       _ = 21 := by decide

-- The first six gates select the lines, the next seven mask the points.
-- Two unions per line then compute its masked neighborhood.
private def circ : Circuit where
  gates := [
    ⟨.or, [7, 8]⟩,
    ⟨.or, [14, 9]⟩,
    ⟨.or, [15, 10]⟩,
    ⟨.or, [16, 11]⟩,
    ⟨.or, [17, 12]⟩,
    ⟨.or, [18, 13]⟩,
    ⟨.and, [0, 19]⟩,
    ⟨.and, [1, 19]⟩,
    ⟨.and, [2, 19]⟩,
    ⟨.and, [3, 19]⟩,
    ⟨.and, [4, 19]⟩,
    ⟨.and, [5, 19]⟩,
    ⟨.and, [6, 19]⟩,
    ⟨.or, [20, 21]⟩,
    ⟨.or, [27, 23]⟩,
    ⟨.or, [21, 22]⟩,
    ⟨.or, [29, 24]⟩,
    ⟨.or, [22, 23]⟩,
    ⟨.or, [31, 25]⟩,
    ⟨.or, [23, 24]⟩,
    ⟨.or, [33, 26]⟩,
    ⟨.or, [24, 25]⟩,
    ⟨.or, [35, 20]⟩,
    ⟨.or, [25, 26]⟩,
    ⟨.or, [37, 21]⟩,
    ⟨.or, [26, 20]⟩,
    ⟨.or, [39, 22]⟩,
    ⟨.and, [7, 28]⟩,
    ⟨.and, [8, 30]⟩,
    ⟨.and, [9, 32]⟩,
    ⟨.and, [10, 34]⟩,
    ⟨.and, [11, 36]⟩,
    ⟨.and, [12, 38]⟩,
    ⟨.and, [13, 40]⟩,
    ⟨.or, [41, 42]⟩,
    ⟨.or, [48, 43]⟩,
    ⟨.or, [49, 44]⟩,
    ⟨.or, [50, 45]⟩,
    ⟨.or, [51, 46]⟩,
    ⟨.or, [52, 47]⟩]
  output := 53

private def andSet : Finset ℕ := Finset.Ico 6 13 ∪ Finset.Ico 27 34

private def orSet : Finset ℕ := Finset.range 6

private def binaryAO (g : Gate) : Bool :=
  match g.op with
  | .and | .or => decide (g.inputs.length ≤ 2)
  | _ => false

private lemma circ_mono : PEqualNP.MetaComplexity.Monotone2 circ := by
  have hall : circ.gates.all binaryAO = true := by decide
  intro g hg
  have h := List.all_eq_true.mp hall g hg
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [binaryAO]

private def andTag (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

private lemma cover_and (j : ℕ) (g : Gate) (hg : circ.gates[j]? = some g)
    (ha : g.op = .and) : j ∈ andSet := by
  have hj : j < 40 := (List.getElem?_eq_some_iff.mp hg).1
  have h : ∀ k : Fin 40,
      (circ.gates[k.val]?.map andTag).getD false = true → k.val ∈ andSet := by decide
  apply h ⟨j, hj⟩
  simp [hg, andTag, ha]

set_option maxRecDepth 64000 in
set_option maxHeartbeats 4000000 in
private lemma late_gates_zero :
    ∀ u : Fin 14, ∀ j : Fin 40, 6 ≤ j.val →
      (circ.wires (List.ofFn (fun i : Fin 14 => decide (i = u)))).getD
        (14 + j.val) false = false := by decide +kernel

private lemma cover_or (j : ℕ) (g : Gate) (hg : circ.gates[j]? = some g)
    (_ho : g.op = .or)
    (hs : ∃ u v : Fin 14, u ≠ v ∧
      (circ.wires (List.ofFn (fun i : Fin 14 => decide (i = u)))).getD (14 + j) false = true ∧
      (circ.wires (List.ofFn (fun i : Fin 14 => decide (i = v)))).getD (14 + j) false = true) :
    j ∈ orSet := by
  obtain ⟨u, _, _, hu, _⟩ := hs
  have hj : j < 40 := (List.getElem?_eq_some_iff.mp hg).1
  by_cases h : j < 6
  · exact Finset.mem_range.mpr h
  · have hz := late_gates_zero u ⟨j, hj⟩ (Nat.le_of_not_gt h)
    change (circ.wires (List.ofFn (fun i : Fin 14 => decide (i = u)))).getD (14 + j) false = false at hz
    have htf : true = false := hu.symm.trans hz
    cases htf


private def fanoPairs : List (Fin 14 × Fin 14) :=
  [(0, 7), (1, 7), (3, 7), (1, 8), (2, 8), (4, 8), (2, 9), (3, 9), (5, 9), (3, 10), (4, 10), (6, 10), (4, 11), (5, 11), (0, 11), (5, 12), (6, 12), (1, 12), (6, 13), (0, 13), (2, 13)]

private lemma edge_enumerated : ∀ u v : Fin 14, fano.Adj u v →
    (u, v) ∈ fanoPairs ∨ (v, u) ∈ fanoPairs := by
  letI : DecidableRel fano.Adj := decideAdj
  decide

set_option maxRecDepth 64000 in
set_option maxHeartbeats 10000000 in
private lemma circuit_correct (x : Fin 14 → Bool) :
    circ.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 14, fano.Adj u v ∧ x u = true ∧ x v = true := by
  letI : DecidableRel fano.Adj := decideAdj
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := rfl
  rw [hx]
  simp only [circ, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.getD_cons_succ,
    List.getD_cons_zero, GateOp.eval, List.all_cons, List.any_cons, List.all_nil, List.any_nil,
    id_eq, Bool.or_false, Bool.and_true]
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · intro h
    rcases h with ((((((h0 | h1) | h2) | h3) | h4) | h5) | h6)
    · rcases h0 with ⟨hl, (⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩⟩
      · exact ⟨0, 7, by decide, hp, hl⟩
      · exact ⟨1, 7, by decide, hp, hl⟩
      · exact ⟨3, 7, by decide, hp, hl⟩
    · rcases h1 with ⟨hl, (⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩⟩
      · exact ⟨1, 8, by decide, hp, hl⟩
      · exact ⟨2, 8, by decide, hp, hl⟩
      · exact ⟨4, 8, by decide, hp, hl⟩
    · rcases h2 with ⟨hl, (⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩⟩
      · exact ⟨2, 9, by decide, hp, hl⟩
      · exact ⟨3, 9, by decide, hp, hl⟩
      · exact ⟨5, 9, by decide, hp, hl⟩
    · rcases h3 with ⟨hl, (⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩⟩
      · exact ⟨3, 10, by decide, hp, hl⟩
      · exact ⟨4, 10, by decide, hp, hl⟩
      · exact ⟨6, 10, by decide, hp, hl⟩
    · rcases h4 with ⟨hl, (⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩⟩
      · exact ⟨4, 11, by decide, hp, hl⟩
      · exact ⟨5, 11, by decide, hp, hl⟩
      · exact ⟨0, 11, by decide, hp, hl⟩
    · rcases h5 with ⟨hl, (⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩⟩
      · exact ⟨5, 12, by decide, hp, hl⟩
      · exact ⟨6, 12, by decide, hp, hl⟩
      · exact ⟨1, 12, by decide, hp, hl⟩
    · rcases h6 with ⟨hl, (⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩⟩
      · exact ⟨6, 13, by decide, hp, hl⟩
      · exact ⟨0, 13, by decide, hp, hl⟩
      · exact ⟨2, 13, by decide, hp, hl⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases edge_enumerated u v huv with h | h <;>
      simp only [fanoPairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h <;>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp [hu, hv]


end PEqualNP.Outside.L_meta_624

namespace PEqualNP.Outside

open L_meta_624

theorem L_meta_624 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (A B : Finset ℕ),
    (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a →
      a = c ∨ b = e) →
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
    (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) →
    (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (∃ u v : Fin n, u ≠ v ∧
        (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧
        (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) →
      j ∈ B) →
    G.edgeSet.ncard ≤ A.card + B.card) := by
  intro h
  have hbound := h 14 fano circ andSet orSet fano_noC4 circ_mono
    circuit_correct cover_and cover_or
  rw [fano_edges] at hbound
  exact (by decide : ¬ (21 ≤ andSet.card + orSet.card)) hbound

end PEqualNP.Outside
