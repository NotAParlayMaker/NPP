import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside

namespace L_meta_753_Aux

open Sym2

def G5adj (i j : Fin 5) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 3 ∧ j = 4) ∨
    (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 0) ∨ (i = 4 ∧ j = 3)

theorem G5adj_symm (i j : Fin 5) (h : G5adj i j) : G5adj j i := by
  rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    simp [G5adj]

theorem G5adj_loopless (i : Fin 5) : ¬ G5adj i i := by
  intro h
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega

theorem G5symm : Std.Symm G5adj := ⟨G5adj_symm⟩

theorem G5loopless : Std.Irrefl G5adj := ⟨G5adj_loopless⟩

def G5 : SimpleGraph (Fin 5) where
  Adj := G5adj
  symm := G5symm
  loopless := G5loopless

instance : DecidableRel G5.Adj := fun i j =>
  inferInstanceAs (Decidable ((i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 3 ∧ j = 4) ∨
    (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 0) ∨ (i = 4 ∧ j = 3)))

theorem adj01 : G5.Adj 0 1 := by simp [G5, G5adj]
theorem adj02 : G5.Adj 0 2 := by simp [G5, G5adj]
theorem adj34 : G5.Adj 3 4 := by simp [G5, G5adj]

theorem aux01 : ∀ (w v : Fin 5) (p : G5.Walk v w), w = 1 → (v = 0 ∨ v = 2) →
    s((0 : Fin 5), (1 : Fin 5)) ∈ p.edges := by
  intro w v p
  induction p with
  | nil => intro hw hv; exfalso; omega
  | @cons a b c h t ih =>
    intro hw hv
    have h' : G5adj a b := h
    rcases hv with rfl | rfl
    · rcases h' with (⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩)
      · subst h2
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inl trivial
      · subst h2
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr (ih hw (Or.inr rfl))
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
    · rcases h' with (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩)
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · subst h2
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr (ih hw (Or.inl rfl))
      · subst h2
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr (ih hw (Or.inl rfl))
      · exfalso; omega

theorem aux02 : ∀ (w v : Fin 5) (p : G5.Walk v w), w = 2 → (v = 0 ∨ v = 1) →
    s((0 : Fin 5), (2 : Fin 5)) ∈ p.edges := by
  intro w v p
  induction p with
  | nil => intro hw hv; exfalso; omega
  | @cons a b c h t ih =>
    intro hw hv
    have h' : G5adj a b := h
    rcases hv with rfl | rfl
    · rcases h' with (⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩)
      · subst h2
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr (ih hw (Or.inr rfl))
      · subst h2
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inl trivial
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
    · rcases h' with (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩)
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · subst h2
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr (ih hw (Or.inl rfl))
      · exfalso; omega
      · exfalso; omega

theorem aux34 : ∀ (w v : Fin 5) (p : G5.Walk v w), w = 4 → v = 3 →
    s((3 : Fin 5), (4 : Fin 5)) ∈ p.edges := by
  intro w v p
  induction p with
  | nil => intro hw hv; exfalso; omega
  | @cons a b c h t ih =>
    intro hw hv
    subst hv
    have h' : G5adj 3 b := h
    rcases h' with (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩)
    · exfalso; omega
    · exfalso; omega
    · subst h2
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
      exact Or.inl trivial
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega

theorem bridge01 : G5.IsBridge s((0 : Fin 5), (1 : Fin 5)) := by
  rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges]
  exact fun p => aux01 1 0 p rfl (Or.inl rfl)

theorem bridge02 : G5.IsBridge s((0 : Fin 5), (2 : Fin 5)) := by
  rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges]
  exact fun p => aux02 2 0 p rfl (Or.inl rfl)

theorem bridge34 : G5.IsBridge s((3 : Fin 5), (4 : Fin 5)) := by
  rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges]
  exact fun p => aux34 4 3 p rfl rfl

theorem G5_acyclic : G5.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge]
  intro e he
  revert he
  refine Sym2.inductionOn e (fun x y hex => ?_)
  rw [SimpleGraph.mem_edgeSet] at hex
  rcases hex with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact bridge01
  · exact bridge02
  · exact bridge34
  · rw [show s((1 : Fin 5), (0 : Fin 5)) = s((0 : Fin 5), (1 : Fin 5)) from by decide]
    exact bridge01
  · rw [show s((2 : Fin 5), (0 : Fin 5)) = s((0 : Fin 5), (2 : Fin 5)) from by decide]
    exact bridge02
  · rw [show s((4 : Fin 5), (3 : Fin 5)) = s((3 : Fin 5), (4 : Fin 5)) from by decide]
    exact bridge34

theorem hcard : G5.edgeFinset.card = 3 := by
  have heq : G5.edgeFinset = {s((0 : Fin 5), (1 : Fin 5)), s((0 : Fin 5), (2 : Fin 5)),
      s((3 : Fin 5), (4 : Fin 5))} := by
    ext e
    refine Sym2.inductionOn e (fun x y => ?_)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    fin_cases x <;> fin_cases y <;> simp [G5, G5adj]
  rw [heq]
  simp

theorem hcov2 : ∀ T : Finset (Fin 5), (∀ i j : Fin 5, G5.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T hT
  have h1 := hT 0 1 adj01
  have h2 := hT 3 4 adj34
  obtain ⟨u, hu⟩ : ∃ u : Fin 5, (u = 0 ∨ u = 1) ∧ u ∈ T := by
    rcases h1 with h | h
    · exact ⟨0, Or.inl rfl, h⟩
    · exact ⟨1, Or.inr rfl, h⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin 5, (v = 3 ∨ v = 4) ∧ v ∈ T := by
    rcases h2 with h | h
    · exact ⟨3, Or.inl rfl, h⟩
    · exact ⟨4, Or.inr rfl, h⟩
  have huv : u ≠ v := by
    rcases hu.1 with rfl | rfl <;> rcases hv.1 with rfl | rfl
    · decide
    · decide
    · decide
    · decide
  have hsub : ({u, v} : Finset (Fin 5)) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu.2
    · exact hv.2
  have hcard' := Finset.card_le_card hsub
  rw [Finset.card_pair huv] at hcard'
  exact hcard'

theorem hcoverT : ∀ i j : Fin 5, G5.Adj i j →
    i ∈ ({0, 3} : Finset (Fin 5)) ∨ j ∈ ({0, 3} : Finset (Fin 5)) := by
  intro i j h
  rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

theorem hfun :
    (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G5.Adj i j ∧ x i = true ∧ x j = true))
      = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) := by
  funext x
  by_cases hex : ∃ i j : Fin 5, G5.Adj i j ∧ x i = true ∧ x j = true
  · have h1 : (decide (∃ i j : Fin 5, G5.Adj i j ∧ x i = true ∧ x j = true)) = true := by
      rw [decide_eq_true_eq]
      exact hex
    rw [h1]
    obtain ⟨i, j, hadj, hi, hj⟩ := hex
    rcases hadj with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [*]
  · have h1 : (decide (∃ i j : Fin 5, G5.Adj i j ∧ x i = true ∧ x j = true)) = false := by
      have h2 : ¬ ((decide (∃ i j : Fin 5, G5.Adj i j ∧ x i = true ∧ x j = true)) = true) := by
        intro hc
        rw [decide_eq_true_eq] at hc
        exact hex hc
      rw [Bool.not_eq_true] at h2
      exact h2
    rw [h1]
    have hor : ¬ (((x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) = true) := by
      intro h
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with (⟨h0, h1'⟩ | ⟨h0, h2'⟩) | ⟨h3, h4'⟩
      · exact hex ⟨0, 1, adj01, by simp [h0], by simp [h1']⟩
      · exact hex ⟨0, 2, adj02, by simp [h0], by simp [h2']⟩
      · exact hex ⟨3, 4, adj34, by simp [h3], by simp [h4']⟩
    rw [Bool.not_eq_true] at hor
    exact hor.symm

end L_meta_753_Aux

open L_meta_753_Aux in
theorem L_meta_753 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) s ↔ 4 ≤ s := by
  intro s
  constructor
  · intro h
    have h' : PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G5.Adj i j ∧ x i = true ∧ x j = true)) s := by
      rw [hfun]
      exact h
    have hlb := PEqualNP.MetaComplexity.L104 5 2 s G5 G5_acyclic ⟨0, 1, adj01⟩ hcov2 h'
    rw [hcard] at hlb
    omega
  · intro hs
    have h4 : PEqualNP.MetaComplexity.HasCircuitSize 5
        (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G5.Adj i j ∧ x i = true ∧ x j = true)) 4 := by
      have hup := PEqualNP.MetaComplexity.L105 5 G5 {0, 3} ⟨0, 1, adj01⟩ hcoverT
      rw [hcard] at hup
      simpa using hup
    rw [hfun] at h4
    obtain ⟨C, hC1, hC2, hC3⟩ := h4
    exact ⟨C, hC1, Nat.le_trans hC2 (by omega), hC3⟩

end PEqualNP.Outside
