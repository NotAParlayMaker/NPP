import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104

namespace PEqualNP.Outside.L_meta_903

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev G (E : List (ℕ × ℕ)) : SimpleGraph (Fin 8) where
  Adj i j := i ≠ j ∧ ((i.val, j.val) ∈ E ∨ (j.val, i.val) ∈ E)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma conn (E : List (ℕ × ℕ)) (hc : ∀ w : Fin 8, w ≠ 0 → ∃ u : Fin 8, u < w ∧ (G E).Adj u w) :
    (G E).Connected := by
  have r : ∀ m : ℕ, ∀ w : Fin 8, w.val = m → (G E).Reachable 0 w := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro w hw
      by_cases h0 : w = 0
      · subst h0; rfl
      · obtain ⟨u, hu, ha⟩ := hc w h0
        exact (ih u.val (by rw [← hw]; exact hu) u rfl).trans ha.reachable
  exact ⟨fun u v => (r _ u rfl).symm.trans (r _ v rfl)⟩

lemma acyc (E : List (ℕ × ℕ)) (hc : ∀ w : Fin 8, w ≠ 0 → ∃ u : Fin 8, u < w ∧ (G E).Adj u w)
    (hcard : (G E).edgeFinset.card = 7) : (G E).IsAcyclic := by
  have ht : (G E).IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨conn E hc, ?_⟩
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hcard]
    simp
  exact ht.isAcyclic

def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

lemma fanin (C : Circuit) (h : C.gates.all (fun g => isAO g.op && decide (g.inputs.length ≤ 2)) = true) :
    FanInTwo C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> simp_all [isAO]

lemma exact_of (f : (Fin 8 → Bool) → Bool) (E : List (ℕ × ℕ)) (k v : ℕ) (C : Circuit)
    (hc : ∀ w : Fin 8, w ≠ 0 → ∃ u : Fin 8, u < w ∧ (G E).Adj u w)
    (hcard : (G E).edgeFinset.card = 7)
    (hcov : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E).Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card)
    (hf : f = fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E).Adj i j ∧ x i = true ∧ x j = true))
    (hv : v + 1 = 7 + k) (hC : FanInTwo C) (hsz : C.size ≤ v)
    (heval : ∀ x, C.eval (List.ofFn x) = f x) :
    ∀ s : ℕ, HasCircuitSize 8 f s ↔ v ≤ s := by
  intro s
  constructor
  · intro hs
    rw [hf] at hs
    obtain ⟨u, -, ha⟩ := hc 1 (by decide)
    have := PEqualNP.MetaComplexity.L104 8 k s (G E) (acyc E hc hcard) ⟨u, 1, ha⟩ hcov hs
    rw [hcard] at this
    omega
  · intro hs
    exact ⟨C, hC, by omega, heval⟩

lemma vec8 (z : Fin 8 → Bool) : z = ![z 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7] := by
  funext i; fin_cases i <;> rfl

def E1 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7)]

def C1 : Circuit := { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.or, [10, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [0, 13]⟩], output := 14 }

lemma ev1 (x : Fin 8 → Bool) : C1.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe1 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E1).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov1 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E1).Adj i j → i ∈ T ∨ j ∈ T) → 1 ≤ T.card := by
  decide +kernel

lemma ex1 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7)) s ↔ 7 ≤ s :=
  exact_of _ E1 1 7 C1 (by decide +kernel) (by decide +kernel) cov1 fe1 rfl
    (fanin C1 rfl) (by decide) ev1

def E2 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 7)]

def C2 : Circuit := { gates := [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [7, 0]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.or, [12, 14]⟩], output := 15 }

lemma ev2 (x : Fin 8 → Bool) : C2.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe2 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E2).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov2 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E2).Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide +kernel

lemma ex2 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)) s ↔ 8 ≤ s :=
  exact_of _ E2 2 8 C2 (by decide +kernel) (by decide +kernel) cov2 fe2 rfl
    (fanin C2 rfl) (by decide) ev2

def E3 : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 7)]

def C3 : Circuit := { gates := [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.or, [12, 14]⟩], output := 15 }

lemma ev3 (x : Fin 8 → Bool) : C3.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe3 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E3).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov3 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E3).Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide +kernel

lemma ex3 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) s ↔ 8 ≤ s :=
  exact_of _ E3 2 8 C3 (by decide +kernel) (by decide +kernel) cov3 fe3 rfl
    (fanin C3 rfl) (by decide) ev3

def E4 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6), (1, 7)]

def C4 : Circuit := { gates := [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [12, 0]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.or, [11, 14]⟩], output := 15 }

lemma ev4 (x : Fin 8 → Bool) : C4.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 1 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe4 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 1 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E4).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov4 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E4).Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide +kernel

lemma ex4 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 1 && x 7)) s ↔ 8 ≤ s :=
  exact_of _ E4 2 8 C4 (by decide +kernel) (by decide +kernel) cov4 fe4 rfl
    (fanin C4 rfl) (by decide) ev4

def E5 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6), (2, 7)]

def C5 : Circuit := { gates := [⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [7, 0]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev5 (x : Fin 8 → Bool) : C5.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe5 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E5).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov5 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E5).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex5 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E5 3 9 C5 (by decide +kernel) (by decide +kernel) cov5 fe5 rfl
    (fanin C5 rfl) (by decide) ev5

def E6 : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 3), (1, 4), (1, 5), (2, 6), (2, 7)]

def C6 : Circuit := { gates := [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.or, [11, 14]⟩], output := 15 }

lemma ev6 (x : Fin 8 → Bool) : C6.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 2 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe6 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 2 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E6).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov6 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E6).Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide +kernel

lemma ex6 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 2 && x 7)) s ↔ 8 ≤ s :=
  exact_of _ E6 2 8 C6 (by decide +kernel) (by decide +kernel) cov6 fe6 rfl
    (fanin C6 rfl) (by decide) ev6

def E7 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (1, 7)]

def C7 : Circuit := { gates := [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [11, 7]⟩, ⟨GateOp.or, [12, 0]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.or, [10, 14]⟩], output := 15 }

lemma ev7 (x : Fin 8 → Bool) : C7.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe7 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E7).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov7 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E7).Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide +kernel

lemma ex7 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 1 && x 7)) s ↔ 8 ≤ s :=
  exact_of _ E7 2 8 C7 (by decide +kernel) (by decide +kernel) cov7 fe7 rfl
    (fanin C7 rfl) (by decide) ev7

def E8 : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 3), (1, 4), (1, 5), (2, 6), (6, 7)]

def C8 : Circuit := { gates := [⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [10, 0]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev8 (x : Fin 8 → Bool) : C8.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 6 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe8 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 6 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E8).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov8 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E8).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex8 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 6 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E8 3 9 C8 (by decide +kernel) (by decide +kernel) cov8 fe8 rfl
    (fanin C8 rfl) (by decide) ev8

def E9 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6), (5, 7)]

def C9 : Circuit := { gates := [⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev9 (x : Fin 8 → Bool) : C9.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe9 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E9).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov9 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E9).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex9 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E9 3 9 C9 (by decide +kernel) (by decide +kernel) cov9 fe9 rfl
    (fanin C9 rfl) (by decide) ev9

def E10 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (1, 6), (2, 7)]

def C10 : Circuit := { gates := [⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [9, 6]⟩, ⟨GateOp.or, [10, 0]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [7, 0]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev10 (x : Fin 8 → Bool) : C10.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe10 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E10).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov10 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E10).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex10 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E10 3 9 C10 (by decide +kernel) (by decide +kernel) cov10 fe10 rfl
    (fanin C10 rfl) (by decide) ev10

def E11 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (2, 7)]

def C11 : Circuit := { gates := [⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [10, 0]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [7, 0]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev11 (x : Fin 8 → Bool) : C11.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe11 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E11).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov11 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E11).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex11 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E11 3 9 C11 (by decide +kernel) (by decide +kernel) cov11 fe11 rfl
    (fanin C11 rfl) (by decide) ev11

def E12 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (2, 6), (3, 7)]

def C12 : Circuit := { gates := [⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [5, 0]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [7, 0]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], output := 17 }

lemma ev12 (x : Fin 8 → Bool) : C12.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe12 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E12).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov12 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E12).Adj i j → i ∈ T ∨ j ∈ T) → 4 ≤ T.card := by
  decide +kernel

lemma ex12 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) s ↔ 10 ≤ s :=
  exact_of _ E12 4 10 C12 (by decide +kernel) (by decide +kernel) cov12 fe12 rfl
    (fanin C12 rfl) (by decide) ev12

def E13 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (6, 7)]

def C13 : Circuit := { gates := [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [10, 0]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev13 (x : Fin 8 → Bool) : C13.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 6 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe13 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 6 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E13).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov13 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E13).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex13 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 6 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E13 3 9 C13 (by decide +kernel) (by decide +kernel) cov13 fe13 rfl
    (fanin C13 rfl) (by decide) ev13

def E14 : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (3, 6), (4, 7)]

def C14 : Circuit := { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [4, 13]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev14 (x : Fin 8 → Bool) : C14.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe14 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E14).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov14 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E14).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex14 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E14 3 9 C14 (by decide +kernel) (by decide +kernel) cov14 fe14 rfl
    (fanin C14 rfl) (by decide) ev14

def E15 : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (5, 6), (5, 7)]

def C15 : Circuit := { gates := [⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [9, 0]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev15 (x : Fin 8 → Bool) : C15.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 5 && x 6) || (x 5 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe15 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 5 && x 6) || (x 5 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E15).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov15 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E15).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex15 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 5 && x 6) || (x 5 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E15 3 9 C15 (by decide +kernel) (by decide +kernel) cov15 fe15 rfl
    (fanin C15 rfl) (by decide) ev15

def E16 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6), (4, 7)]

def C16 : Circuit := { gates := [⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [5, 0]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [4, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev16 (x : Fin 8 → Bool) : C16.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 4 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe16 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 4 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E16).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov16 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E16).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex16 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 4 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E16 3 9 C16 (by decide +kernel) (by decide +kernel) cov16 fe16 rfl
    (fanin C16 rfl) (by decide) ev16

def E17 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (4, 6), (5, 7)]

def C17 : Circuit := { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev17 (x : Fin 8 → Bool) : C17.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe17 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E17).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov17 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E17).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex17 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E17 3 9 C17 (by decide +kernel) (by decide +kernel) cov17 fe17 rfl
    (fanin C17 rfl) (by decide) ev17

def E18 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (2, 7)]

def C18 : Circuit := { gates := [⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [9, 0]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [12, 0]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev18 (x : Fin 8 → Bool) : C18.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 2 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe18 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 2 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E18).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov18 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E18).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex18 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 2 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E18 3 9 C18 (by decide +kernel) (by decide +kernel) cov18 fe18 rfl
    (fanin C18 rfl) (by decide) ev18

def E19 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (3, 7)]

def C19 : Circuit := { gates := [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

lemma ev19 (x : Fin 8 → Bool) : C19.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe19 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E19).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov19 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E19).Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

lemma ex19 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7)) s ↔ 9 ≤ s :=
  exact_of _ E19 3 9 C19 (by decide +kernel) (by decide +kernel) cov19 fe19 rfl
    (fanin C19 rfl) (by decide) ev19

def E20 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6), (4, 7)]

def C20 : Circuit := { gates := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [5, 0]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.and, [4, 13]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], output := 17 }

lemma ev20 (x : Fin 8 → Bool) : C20.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe20 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E20).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov20 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E20).Adj i j → i ∈ T ∨ j ∈ T) → 4 ≤ T.card := by
  decide +kernel

lemma ex20 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 7)) s ↔ 10 ≤ s :=
  exact_of _ E20 4 10 C20 (by decide +kernel) (by decide +kernel) cov20 fe20 rfl
    (fanin C20 rfl) (by decide) ev20

def E21 : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (3, 6), (5, 7)]

def C21 : Circuit := { gates := [⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [4, 0]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [6, 1]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], output := 17 }

lemma ev21 (x : Fin 8 → Bool) : C21.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 5 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe21 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 5 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E21).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov21 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E21).Adj i j → i ∈ T ∨ j ∈ T) → 4 ≤ T.card := by
  decide +kernel

lemma ex21 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 5 && x 7)) s ↔ 10 ≤ s :=
  exact_of _ E21 4 10 C21 (by decide +kernel) (by decide +kernel) cov21 fe21 rfl
    (fanin C21 rfl) (by decide) ev21

def E22 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (4, 7)]

def C22 : Circuit := { gates := [⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [5, 0]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [6, 0]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [7, 1]⟩, ⟨GateOp.and, [4, 13]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], output := 17 }

lemma ev22 (x : Fin 8 → Bool) : C22.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 7)) := by
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma fe22 : (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 7)) =
    fun x : Fin 8 → Bool => decide (∃ i j : Fin 8, (G E22).Adj i j ∧ x i = true ∧ x j = true) := by
  funext x
  rw [vec8 x]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide +kernel

lemma cov22 : ∀ T : Finset (Fin 8), (∀ i j : Fin 8, (G E22).Adj i j → i ∈ T ∨ j ∈ T) → 4 ≤ T.card := by
  decide +kernel

lemma ex22 : ∀ s : ℕ, HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 7)) s ↔ 10 ≤ s :=
  exact_of _ E22 4 10 C22 (by decide +kernel) (by decide +kernel) cov22 fe22 rfl
    (fanin C22 rfl) (by decide) ev22

end PEqualNP.Outside.L_meta_903

theorem PEqualNP.Outside.L_meta_903 : (∀ s1 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x1 : Fin 8 → Bool => (x1 0 && x1 1) || (x1 0 && x1 2) || (x1 0 && x1 3) || (x1 0 && x1 4) || (x1 0 && x1 5) || (x1 0 && x1 6) || (x1 0 && x1 7)) s1 ↔ 7 ≤ s1) ∧ (∀ s2 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x2 : Fin 8 → Bool => (x2 0 && x2 1) || (x2 0 && x2 2) || (x2 0 && x2 3) || (x2 0 && x2 4) || (x2 0 && x2 5) || (x2 0 && x2 6) || (x2 1 && x2 7)) s2 ↔ 8 ≤ s2) ∧ (∀ s3 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x3 : Fin 8 → Bool => (x3 0 && x3 1) || (x3 0 && x3 2) || (x3 1 && x3 3) || (x3 1 && x3 4) || (x3 1 && x3 5) || (x3 1 && x3 6) || (x3 2 && x3 7)) s3 ↔ 8 ≤ s3) ∧ (∀ s4 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x4 : Fin 8 → Bool => (x4 0 && x4 1) || (x4 0 && x4 2) || (x4 0 && x4 3) || (x4 0 && x4 4) || (x4 0 && x4 5) || (x4 1 && x4 6) || (x4 1 && x4 7)) s4 ↔ 8 ≤ s4) ∧ (∀ s5 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x5 : Fin 8 → Bool => (x5 0 && x5 1) || (x5 0 && x5 2) || (x5 0 && x5 3) || (x5 0 && x5 4) || (x5 0 && x5 5) || (x5 1 && x5 6) || (x5 2 && x5 7)) s5 ↔ 9 ≤ s5) ∧ (∀ s6 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x6 : Fin 8 → Bool => (x6 0 && x6 1) || (x6 0 && x6 2) || (x6 1 && x6 3) || (x6 1 && x6 4) || (x6 1 && x6 5) || (x6 2 && x6 6) || (x6 2 && x6 7)) s6 ↔ 8 ≤ s6) ∧ (∀ s7 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x7 : Fin 8 → Bool => (x7 0 && x7 1) || (x7 0 && x7 2) || (x7 0 && x7 3) || (x7 0 && x7 4) || (x7 1 && x7 5) || (x7 1 && x7 6) || (x7 1 && x7 7)) s7 ↔ 8 ≤ s7) ∧ (∀ s8 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x8 : Fin 8 → Bool => (x8 0 && x8 1) || (x8 0 && x8 2) || (x8 1 && x8 3) || (x8 1 && x8 4) || (x8 1 && x8 5) || (x8 2 && x8 6) || (x8 6 && x8 7)) s8 ↔ 9 ≤ s8) ∧ (∀ s9 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x9 : Fin 8 → Bool => (x9 0 && x9 1) || (x9 0 && x9 2) || (x9 0 && x9 3) || (x9 0 && x9 4) || (x9 1 && x9 5) || (x9 2 && x9 6) || (x9 5 && x9 7)) s9 ↔ 9 ≤ s9) ∧ (∀ s10 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x10 : Fin 8 → Bool => (x10 0 && x10 1) || (x10 0 && x10 2) || (x10 0 && x10 3) || (x10 1 && x10 4) || (x10 1 && x10 5) || (x10 1 && x10 6) || (x10 2 && x10 7)) s10 ↔ 9 ≤ s10) ∧ (∀ s11 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x11 : Fin 8 → Bool => (x11 0 && x11 1) || (x11 0 && x11 2) || (x11 0 && x11 3) || (x11 0 && x11 4) || (x11 1 && x11 5) || (x11 1 && x11 6) || (x11 2 && x11 7)) s11 ↔ 9 ≤ s11) ∧ (∀ s12 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x12 : Fin 8 → Bool => (x12 0 && x12 1) || (x12 0 && x12 2) || (x12 0 && x12 3) || (x12 0 && x12 4) || (x12 1 && x12 5) || (x12 2 && x12 6) || (x12 3 && x12 7)) s12 ↔ 10 ≤ s12) ∧ (∀ s13 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x13 : Fin 8 → Bool => (x13 0 && x13 1) || (x13 0 && x13 2) || (x13 0 && x13 3) || (x13 1 && x13 4) || (x13 1 && x13 5) || (x13 2 && x13 6) || (x13 6 && x13 7)) s13 ↔ 9 ≤ s13) ∧ (∀ s14 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x14 : Fin 8 → Bool => (x14 0 && x14 1) || (x14 0 && x14 2) || (x14 1 && x14 3) || (x14 2 && x14 4) || (x14 3 && x14 5) || (x14 3 && x14 6) || (x14 4 && x14 7)) s14 ↔ 9 ≤ s14) ∧ (∀ s15 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x15 : Fin 8 → Bool => (x15 0 && x15 1) || (x15 0 && x15 2) || (x15 1 && x15 3) || (x15 1 && x15 4) || (x15 2 && x15 5) || (x15 5 && x15 6) || (x15 5 && x15 7)) s15 ↔ 9 ≤ s15) ∧ (∀ s16 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x16 : Fin 8 → Bool => (x16 0 && x16 1) || (x16 0 && x16 2) || (x16 0 && x16 3) || (x16 1 && x16 4) || (x16 2 && x16 5) || (x16 4 && x16 6) || (x16 4 && x16 7)) s16 ↔ 9 ≤ s16) ∧ (∀ s17 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x17 : Fin 8 → Bool => (x17 0 && x17 1) || (x17 0 && x17 2) || (x17 0 && x17 3) || (x17 1 && x17 4) || (x17 2 && x17 5) || (x17 4 && x17 6) || (x17 5 && x17 7)) s17 ↔ 9 ≤ s17) ∧ (∀ s18 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x18 : Fin 8 → Bool => (x18 0 && x18 1) || (x18 0 && x18 2) || (x18 0 && x18 3) || (x18 1 && x18 4) || (x18 1 && x18 5) || (x18 2 && x18 6) || (x18 2 && x18 7)) s18 ↔ 9 ≤ s18) ∧ (∀ s19 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x19 : Fin 8 → Bool => (x19 0 && x19 1) || (x19 0 && x19 2) || (x19 0 && x19 3) || (x19 1 && x19 4) || (x19 1 && x19 5) || (x19 2 && x19 6) || (x19 3 && x19 7)) s19 ↔ 9 ≤ s19) ∧ (∀ s20 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x20 : Fin 8 → Bool => (x20 0 && x20 1) || (x20 0 && x20 2) || (x20 0 && x20 3) || (x20 1 && x20 4) || (x20 2 && x20 5) || (x20 3 && x20 6) || (x20 4 && x20 7)) s20 ↔ 10 ≤ s20) ∧ (∀ s21 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x21 : Fin 8 → Bool => (x21 0 && x21 1) || (x21 0 && x21 2) || (x21 1 && x21 3) || (x21 1 && x21 4) || (x21 2 && x21 5) || (x21 3 && x21 6) || (x21 5 && x21 7)) s21 ↔ 10 ≤ s21) ∧ (∀ s22 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x22 : Fin 8 → Bool => (x22 0 && x22 1) || (x22 0 && x22 2) || (x22 0 && x22 3) || (x22 1 && x22 4) || (x22 1 && x22 5) || (x22 2 && x22 6) || (x22 4 && x22 7)) s22 ↔ 10 ≤ s22) :=
  ⟨PEqualNP.Outside.L_meta_903.ex1, PEqualNP.Outside.L_meta_903.ex2, PEqualNP.Outside.L_meta_903.ex3, PEqualNP.Outside.L_meta_903.ex4, PEqualNP.Outside.L_meta_903.ex5, PEqualNP.Outside.L_meta_903.ex6, PEqualNP.Outside.L_meta_903.ex7, PEqualNP.Outside.L_meta_903.ex8, PEqualNP.Outside.L_meta_903.ex9, PEqualNP.Outside.L_meta_903.ex10, PEqualNP.Outside.L_meta_903.ex11, PEqualNP.Outside.L_meta_903.ex12, PEqualNP.Outside.L_meta_903.ex13, PEqualNP.Outside.L_meta_903.ex14, PEqualNP.Outside.L_meta_903.ex15, PEqualNP.Outside.L_meta_903.ex16, PEqualNP.Outside.L_meta_903.ex17, PEqualNP.Outside.L_meta_903.ex18, PEqualNP.Outside.L_meta_903.ex19, PEqualNP.Outside.L_meta_903.ex20, PEqualNP.Outside.L_meta_903.ex21, PEqualNP.Outside.L_meta_903.ex22⟩
