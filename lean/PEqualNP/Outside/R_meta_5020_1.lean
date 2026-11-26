import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5020_1
    (route : ∀ (n : ℕ) (C : Circuit) (v : Fin n),
    IsMinimalCircuit n C →
    (∃ x y, circuitFun n C (Function.update x v false) ≠
      circuitFun n C (Function.update y v false)) →
    let readers := C.gates.filter (fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
    readers.length = 2 → (∃ g ∈ readers, g.op ≠ .or) →
    (∃ t, t + 4 ≤ C.size ∧ HasCircuitSize n
      (fun x => circuitFun n C (Function.update x v false)) t) ∨
    ∃ (p r : ℕ) (gp gr : Gate), C.gates[p]? = some gp ∧ C.gates[r]? = some gr ∧
      v.val ∈ gp.inputs.take (bif gp.op.eval [false] then 1 else 2) ∧
      n + p ∈ gr.inputs.take (bif gr.op.eval [false] then 1 else 2) ∧
      (∀ (s : ℕ) (g : Gate), C.gates[s]? = some g →
        n + p ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2) → s = r) ∧
      ((gp.op = .and ∧ gr.op = .or) ∨ (gp.op = .not ∧ gr.op = .and)))
    (tail : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (C : Circuit),
    let pins := fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2)
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) →
    (∀ i j, G.Adj i j → i ∉ A) →
    (∀ x, circuitFun n C x = true ↔ (∃ a ∈ A, x a = true) ∨
      ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
    IsMinimalCircuit n C →
    (∀ v ∉ A, 2 ≤ (C.gates.filter (fun g =>
      (pins g).contains v.val)).length) →
    (∃ v ∉ A, let readers := C.gates.filter (fun g =>
      (pins g).contains v.val)
      readers.length = 2 ∧ (∃ (p r : ℕ) (gp gr : Gate), C.gates[p]? = some gp ∧ C.gates[r]? = some gr ∧
      v.val ∈ pins gp ∧
      n + p ∈ pins gr ∧
      (∀ (s : ℕ) (g : Gate), C.gates[s]? = some g →
        n + p ∈ pins g → s = r) ∧
      ((gp.op = .and ∧ gr.op = .or) ∨ (gp.op = .not ∧ gr.op = .and)))) →
    ∃ z ∉ A, ∃ t, t + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => circuitFun n C (Function.update x z false)) t)
    (res :
      ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (z : Fin n)
        (g : (Fin n → Bool) → Bool),
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
        (∀ i j : Fin n, G.Adj i j → i ∉ A) →
        (∃ i j : Fin n, G.Adj i j) →
        z ∉ A →
        (∀ x, g x = true ↔ (∃ a ∈ A, x a = true) ∨
          ∃ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j ∧ x i = true ∧ x j = true) →
        (∀ T : Finset (Fin n), (∀ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
        PEqualNP.MetaComplexity.HasCircuitSize n g s →
        A.card + (G.deleteEdges (G.incidenceSet z)).edgeSet.ncard + k ≤ s + 1) :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) →     (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →       (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) →         (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) →           (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) →             (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) →               PEqualNP.MetaComplexity.FanInTwo x6 →                 PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 →                   (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) →                     (∀ x16 ∉ x4, (2 : ℕ) ≤ (List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x16) x6.gates).length) →                       (∃ x17 ∉ x4,                           have x18 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x17) x6.gates;                           x18.length = (2 : ℕ) ∧ ∃ x19 ∈ x18, x19.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) →                         x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  intro n k G A f C hdeg hgirth hA hedge htau hf hfan hfun hleast hreads hnonor
  classical

  obtain ⟨v, hvA, hvread, hvnon⟩ := hnonor
  have hmin : IsMinimalCircuit n C := by
    refine ⟨hfan, ?_⟩
    intro D hD hd
    apply hleast D.size
    refine ⟨D, hD, le_rfl, ?_⟩
    intro x
    exact congrFun (hd.trans hfun) x
  have nbr : ∀ a ∉ A, ∀ b : Fin n, ∃ w, G.Adj a w ∧ w ≠ b := by
    intro a ha b
    by_contra! H
    have hsub : G.neighborSet a ⊆ ({b} : Set (Fin n)) := by
      intro w hw
      exact H w hw
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
    simp [hdeg a ha] at hcard
  obtain ⟨w, hvw, hwv⟩ := nbr v hvA v
  obtain ⟨t, hwt, htv⟩ := nbr w (hA w v hvw.symm) v
  let zero : Fin n → Bool := fun _ => false
  let edge : Fin n → Bool := fun i => decide (i = w ∨ i = t)
  have hzero : Function.update zero v false = zero := by
    exact Function.update_eq_self v zero
  have hEdge : Function.update edge v false = edge := by
    have h : edge v = false := by simp [edge, Ne.symm hwv, Ne.symm htv]
    rw [← h, Function.update_eq_self]
  have hNC : ∃ x y, circuitFun n C (Function.update x v false) ≠
      circuitFun n C (Function.update y v false) := by
    refine ⟨zero, edge, ?_⟩
    rw [hfun, hzero, hEdge]
    have hz : f zero = false := by
      have h : ¬ f zero = true := by simpa [zero] using (hf zero)
      exact Bool.eq_false_of_not_eq_true h
    have he : f edge = true := (hf edge).2
      (Or.inr ⟨w, t, hwt, by simp [edge], by simp [edge]⟩)
    simp [hz, he]
  have hcut : ∃ z ∉ A, ∃ t, t + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => circuitFun n C (Function.update x z false)) t := by
    rcases route n C v hmin hNC hvread hvnon with ⟨s, hs, hcs⟩ | hroute
    · exact ⟨v, hvA, s, hs, hcs⟩
    · refine tail n G A C hdeg hgirth hA ?_ hmin hreads ⟨v, hvA, hvread, hroute⟩
      simpa only [hfun] using hf
  rw [hfun] at hcut
  obtain ⟨z, hzA, t, ht, hCt⟩ := hcut
  have hadj : ∀ i j : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i j ↔
      G.Adj i j ∧ i ≠ z ∧ j ≠ z := fun i j => SimpleGraph.deleteIncidenceSet_adj
  have hg : ∀ x : Fin n → Bool,
      f (Function.update x z false) = true ↔
        (∃ a ∈ A, x a = true) ∨
          ∃ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j ∧ x i = true ∧ x j = true := by
    intro x
    rw [hf]
    constructor
    · rintro (⟨a, haA, ha⟩ | ⟨i, j, hij, hi, hj⟩)
      · have haz : a ≠ z := fun e => hzA (e ▸ haA)
        exact Or.inl ⟨a, haA, by simpa [Function.update_of_ne haz] using ha⟩
      · have hiz : i ≠ z := by intro e; simp [e] at hi
        have hjz : j ≠ z := by intro e; simp [e] at hj
        exact Or.inr ⟨i, j, (hadj i j).2 ⟨hij, hiz, hjz⟩,
          by simpa [Function.update_of_ne hiz] using hi,
          by simpa [Function.update_of_ne hjz] using hj⟩
    · rintro (⟨a, haA, ha⟩ | ⟨i, j, hij, hi, hj⟩)
      · have haz : a ≠ z := fun e => hzA (e ▸ haA)
        exact Or.inl ⟨a, haA, by simpa [Function.update_of_ne haz] using ha⟩
      · obtain ⟨hij, hiz, hjz⟩ := (hadj i j).1 hij
        exact Or.inr ⟨i, j, hij, by simpa [Function.update_of_ne hiz] using hi,
          by simpa [Function.update_of_ne hjz] using hj⟩
  have hk' : ∀ T : Finset (Fin n),
      (∀ i j, (G.deleteEdges (G.incidenceSet z)).Adj i j → i ∈ T ∨ j ∈ T) →
      k - 1 ≤ T.card := by
    intro T hT
    have hcov : ∀ i j : Fin n, G.Adj i j → i ∈ insert z T ∨ j ∈ insert z T := by
      intro i j hij
      by_cases hi : i = z
      · left; rw [hi]; exact Finset.mem_insert_self z T
      · by_cases hj : j = z
        · right; rw [hj]; exact Finset.mem_insert_self z T
        · rcases hT i j ((hadj i j).2 ⟨hij, hi, hj⟩) with h | h
          · left; exact Finset.mem_insert_of_mem h
          · right; exact Finset.mem_insert_of_mem h
    have hle := htau (insert z T) hcov
    have hcard := Finset.card_insert_le z T
    omega
  have hrec := res n (k - 1) t G A z (fun x => f (Function.update x z false))
    hdeg hgirth hA hedge hzA hg hk' hCt
  have hE : G.edgeSet.ncard =
      (G.deleteEdges (G.incidenceSet z)).edgeSet.ncard + 3 := by
    have hsub : G.incidenceSet z ⊆ G.edgeSet := SimpleGraph.incidenceSet_subset G z
    have hinc : (G.incidenceSet z).ncard = 3 := by
      rw [← SimpleGraph.coe_incidenceFinset, Set.ncard_coe_finset,
        SimpleGraph.card_incidenceFinset_eq_degree, ← SimpleGraph.ncard_neighborSet]
      exact hdeg z hzA
    rw [SimpleGraph.edgeSet_deleteEdges]
    have hsum := Set.ncard_sdiff_add_ncard_of_subset hsub (Set.toFinite _)
    omega
  omega
