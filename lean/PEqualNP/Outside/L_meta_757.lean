import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_757

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def targetFun (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)

def c5 : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩

lemma c5_fanInTwo : FanInTwo c5 := by
  intro g hg
  simp only [c5, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

lemma c5_eval_vec : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    c5.eval [b0, b1, b2, b3, b4, b5] =
      ((b0 && b1) || (b0 && b2) || (b3 && b4) || (b3 && b5)) := by
  decide

lemma c5_eval (x : Fin 6 → Bool) : c5.eval (List.ofFn x) = targetFun x := by
  have hof : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp only [List.ofFn_succ, List.ofFn_zero]
    rfl
  rw [hof]
  exact c5_eval_vec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

lemma upper (s : ℕ) (hs : 5 ≤ s) : HasCircuitSize 6 targetFun s :=
  ⟨c5, c5_fanInTwo, hs, c5_eval⟩

def adjB (i j : Fin 6) : Bool :=
  (i == 0 && (j == 1 || j == 2)) || ((i == 1 || i == 2) && j == 0) ||
  (i == 3 && (j == 4 || j == 5)) || ((i == 4 || i == 5) && j == 3)

def graph6 : SimpleGraph (Fin 6) where
  Adj i j := adjB i j = true
  symm := ⟨fun i j h => by revert i j h; decide⟩
  loopless := ⟨fun i h => by revert i h; decide⟩

lemma graph6_no3 :
    ∀ v u1 u2 u3 : Fin 6, graph6.Adj v u1 → graph6.Adj u1 u2 → graph6.Adj u2 u3 →
      v = u2 ∨ u1 = u3 := by
  intro v u1 u2 u3 h1 h2 h3
  change adjB v u1 = true at h1
  change adjB u1 u2 = true at h2
  change adjB u2 u3 = true at h3
  revert v u1 u2 u3 h1 h2 h3
  decide

lemma graph6_acyclic : graph6.IsAcyclic := by
  intro v c hc
  have hlen : 3 ≤ c.length := hc.three_le_length
  have hnd : c.edges.Nodup := hc.edges_nodup
  cases c with
  | nil => simp at hlen
  | cons h1 p1 =>
    cases p1 with
    | nil => simp at hlen
    | cons h2 p2 =>
      cases p2 with
      | nil => simp at hlen
      | cons h3 p3 =>
        rcases graph6_no3 _ _ _ _ h1 h2 h3 with rfl | rfl
        · simp [SimpleGraph.Walk.edges_cons, Sym2.eq_swap] at hnd
        · simp [SimpleGraph.Walk.edges_cons, Sym2.eq_swap] at hnd

lemma graph6_has_edge : ∃ i j : Fin 6, graph6.Adj i j :=
  ⟨0, 1, rfl⟩

lemma graph6_cover_ge (T : Finset (Fin 6))
    (hT : ∀ i j : Fin 6, graph6.Adj i j → i ∈ T ∨ j ∈ T) : 2 ≤ T.card := by
  have h01 : (0 : Fin 6) ∈ T ∨ (1 : Fin 6) ∈ T := hT 0 1 rfl
  have h34 : (3 : Fin 6) ∈ T ∨ (4 : Fin 6) ∈ T := hT 3 4 rfl
  rcases h01 with h0 | h1 <;> rcases h34 with h3 | h4
  · have hsub : ({0, 3} : Finset (Fin 6)) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc 2 = ({0, 3} : Finset (Fin 6)).card := (Finset.card_pair (by decide)).symm
      _ ≤ T.card := Finset.card_le_card hsub
  · have hsub : ({0, 4} : Finset (Fin 6)) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc 2 = ({0, 4} : Finset (Fin 6)).card := (Finset.card_pair (by decide)).symm
      _ ≤ T.card := Finset.card_le_card hsub
  · have hsub : ({1, 3} : Finset (Fin 6)) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc 2 = ({1, 3} : Finset (Fin 6)).card := (Finset.card_pair (by decide)).symm
      _ ≤ T.card := Finset.card_le_card hsub
  · have hsub : ({1, 4} : Finset (Fin 6)) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc 2 = ({1, 4} : Finset (Fin 6)).card := (Finset.card_pair (by decide)).symm
      _ ≤ T.card := Finset.card_le_card hsub

lemma graph6_edges_eq [DecidableRel graph6.Adj] :
    graph6.edgeFinset = ({s(0, 1), s(0, 2), s(3, 4), s(3, 5)} : Finset (Sym2 (Fin 6))) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_insert,
      Finset.mem_singleton, Sym2.eq_iff]
    change adjB a b = true ↔
      (a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 2 ∨ a = 2 ∧ b = 0) ∨
      (a = 3 ∧ b = 4 ∨ a = 4 ∧ b = 3) ∨ (a = 3 ∧ b = 5 ∨ a = 5 ∧ b = 3)
    revert a b
    decide

lemma graph6_edges_card [DecidableRel graph6.Adj] : graph6.edgeFinset.card = 4 := by
  rw [graph6_edges_eq]
  decide

lemma graph6_fun_eq [DecidableRel graph6.Adj] :
    (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, graph6.Adj i j ∧ x i = true ∧ x j = true)) =
      targetFun := by
  funext x
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    change adjB i j = true at hij
    fin_cases i <;> fin_cases j <;> (try exact absurd hij (by decide)) <;>
      simp_all [targetFun]
  · intro h
    simp only [targetFun, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((⟨h0, h1⟩ | ⟨h0, h2⟩) | ⟨h3, h4⟩) | ⟨h3, h5⟩
    · exact ⟨0, 1, rfl, h0, h1⟩
    · exact ⟨0, 2, rfl, h0, h2⟩
    · exact ⟨3, 4, rfl, h3, h4⟩
    · exact ⟨3, 5, rfl, h3, h5⟩

lemma lower (s : ℕ) (h : HasCircuitSize 6 targetFun s) : 5 ≤ s := by
  let dec : DecidableRel graph6.Adj := fun i j => inferInstanceAs (Decidable (adjB i j = true))
  rw [← @graph6_fun_eq dec] at h
  have hb := @PEqualNP.MetaComplexity.L104 6 2 s graph6 dec graph6_acyclic graph6_has_edge
    graph6_cover_ge h
  rw [@graph6_edges_card dec] at hb
  omega

theorem main :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) s ↔ 5 ≤ s :=
  fun s => ⟨lower s, upper s⟩

end PEqualNP.Outside.L_meta_757

theorem PEqualNP.Outside.L_meta_757 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) s ↔ 5 ≤ s := by
  exact PEqualNP.Outside.L_meta_757.main
