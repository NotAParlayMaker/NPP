import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- The rows are the sixteen edges, and the columns are the twenty-four maximal independent sets.
-- At an OR gate the edge input chooses a child. At an AND gate the independent input chooses.
-- Unfolding the output therefore gives a partition with one rectangle per raw input occurrence.
theorem PEqualNP.Outside.R_meta_2384_23
    (rectangles : let p := ([513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768] : List Nat)
      let n := ([15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546] : List Nat)
      ∀ rs : List (Fin 11 × (Fin 16 → Bool) × (Fin 24 → Bool)),
        (∀ r ∈ rs, (∀ i, r.2.1 i = true → (p.getD i.val 0).testBit r.1.val = true) ∧
          (∀ j, r.2.2 j = true → (n.getD j.val 0).testBit r.1.val = false)) →
        (∀ i j, (rs.filter (fun r => r.2.1 i && r.2.2 j)).length = 1) → 23 ≤ rs.length)
    (shared : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        23 ≤ (C.gates.foldl (fun (w : List ℕ) (g : Gate) => w ++ [(g.inputs.map fun i => w.getD i 0).sum]) (List.replicate 11 1)).getD C.output 0 →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        U.card ≤ B → B < 2 * U.card → ∃ K X : Finset (Fin 11),
          IsMinCover (G.deleteEdges ↑U) K ∧ G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ B - U.card) :
    let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        U.card ≤ B → B < 2 * U.card → ∃ K X : Finset (Fin 11),
          IsMinCover (G.deleteEdges ↑U) K ∧ G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ B - U.card := by
  dsimp only
  intro C size least top junkCount
  apply shared C size least top junkCount
  let pos (i : Fin 16) (v : Fin 11) := (([513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768] : List Nat).getD i.val 0).testBit v.val
  let neg (j : Fin 24) (v : Fin 11) := (([15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546] : List Nat).getD j.val 0).testBit v.val
  let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  have validRows : (∀ i, graphFun G ∅ (pos i) = true) ∧ (∀ j, graphFun G ∅ (neg j) = false) := by
    decide +kernel
  let R := Fin 11 × (Fin 16 → Bool) × (Fin 24 → Bool)
  let valid (r : R) := (∀ i, r.2.1 i = true → pos i r.1 = true) ∧
    (∀ j, r.2.2 j = true → neg j r.1 = false)
  let count (rs : List R) (i : Fin 16) (j : Fin 24) := (rs.filter (fun r => r.2.1 i && r.2.2 j)).length
  let Rep (k : Nat) (A : (Fin 11 → Bool) → Bool) :=
    ∀ (P : Fin 16 → Bool) (N : Fin 24 → Bool),
      (∀ i, P i = true → A (pos i) = true) → (∀ j, N j = true → A (neg j) = false) →
      ∃ rs : List R, rs.length ≤ k ∧ (∀ r ∈ rs, valid r) ∧ ∀ i j, count rs i j = (P i && N j).toNat
  have empty (k : Nat) (A : (Fin 11 → Bool) → Bool) (c : ∀ x, A x = false) : Rep k A := by
    intro P N hp hn
    refine ⟨[], Nat.zero_le _, by simp, ?_⟩
    intro i j
    cases h : P i
    · rfl
    · exact (Bool.false_ne_true ((c _).symm.trans (hp i h))).elim
  have join (d : Bool) (k l : Nat) (A B : (Fin 11 → Bool) → Bool) (ha : Rep k A) (hb : Rep l B) :
      Rep (k + l) (fun x => if d then A x && B x else A x || B x) := by
    intro P N hp hn
    let P₁ i := if d then P i else P i && A (pos i)
    let P₂ i := if d then P i else P i && !A (pos i)
    let N₁ j := if d then N j && !A (neg j) else N j
    let N₂ j := if d then N j && A (neg j) else N j
    have truths (d p a b : Bool) :
        (p = true → (if d then a && b else a || b) = true) →
        ((if d then p else p && a) = true → a = true) ∧ ((if d then p else p && !a) = true → b = true) := by decide +revert
    have falses (d n a b : Bool) :
        (n = true → (if d then a && b else a || b) = false) →
        ((if d then n && !a else n) = true → a = false) ∧ ((if d then n && a else n) = true → b = false) := by decide +revert
    obtain ⟨xs, xk, xv, xc⟩ := ha P₁ N₁ (fun i => (truths d _ _ _ (hp i)).1) (fun j => (falses d _ _ _ (hn j)).1)
    obtain ⟨ys, yl, yv, yc⟩ := hb P₂ N₂ (fun i => (truths d _ _ _ (hp i)).2) (fun j => (falses d _ _ _ (hn j)).2)
    refine ⟨xs ++ ys, List.length_append ▸ Nat.add_le_add xk yl, ?_, ?_⟩
    · intro r hr
      exact (List.mem_append.mp hr).elim (xv _) (yv _)
    · intro i j
      have split : count (xs ++ ys) i j = count xs i j + count ys i j := by
        simp only [count, List.filter_append, List.length_append]
      rw [split, xc, yc]
      dsimp only [P₁, P₂, N₁, N₂]
      cases d <;> cases P i <;> cases N j <;> cases A (pos i) <;> cases A (neg j) <;> rfl
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let weight (w : List Nat) (g : Gate) := w ++ [(g.inputs.map fun i => w.getD i 0).sum]
  have gate (g : Gate) (hOp : g.op = GateOp.and ∨ g.op = GateOp.or) (hLen : g.inputs.length = 2)
      (w : List Nat) (rows : (Fin 11 → Bool) → List Bool)
      (old : ∀ i, Rep (w.getD i 0) (fun x => (rows x).getD i false)) :
      Rep (g.inputs.map fun i => w.getD i 0).sum (fun x => g.op.eval (g.inputs.map fun i => (rows x).getD i false)) := by
    rcases g with ⟨o, ls⟩
    obtain ⟨i, j, rfl⟩ := List.length_eq_two.mp hLen
    let both := fun d => join d (w.getD i 0) (w.getD j 0)
      (fun x => (rows x).getD i false) (fun x => (rows x).getD j false) (old i) (old j)
    have evalAnd (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by cases a <;> cases b <;> rfl
    have evalOr (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by cases a <;> cases b <;> rfl
    rcases hOp with rfl | rfl
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
          evalAnd, ite_true] using
        both true
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
          evalOr, Bool.false_eq_true, ite_false] using
        both false
  have expand (gs : List Gate)
      (ops : ∀ z ∈ gs, (z.op = GateOp.and ∨ z.op = GateOp.or) ∧ z.inputs.length = 2)
      (w : List Nat) (rows : (Fin 11 → Bool) → List Bool) (lens : ∀ x, (rows x).length = w.length)
      (old : ∀ i, Rep (w.getD i 0) (fun x => (rows x).getD i false))
      (i : Nat) : Rep ((gs.foldl weight w).getD i 0) (fun x => (gs.foldl step (rows x)).getD i false) := by
    induction gs generalizing w rows with
    | nil => exact old i
    | cons z gs ih =>
      have hz := ops z List.mem_cons_self
      apply ih (fun g hg => ops g (List.mem_cons_of_mem z hg)) (weight w z) (fun x => step (rows x) z)
      · intro x
        simp only [step, weight, List.length_append, List.length_cons, List.length_nil, lens]
      · intro j
        by_cases earlier : j < w.length
        · have e : (weight w z).getD j 0 = w.getD j 0 := List.getD_append _ _ _ _ earlier
          have v (x) : (step (rows x) z).getD j false = (rows x).getD j false :=
            List.getD_append _ _ _ _ (by simpa only [lens] using earlier)
          simpa only [e, v] using old j
        · by_cases now : j = w.length
          · subst j
            have e : (weight w z).getD w.length 0 = (z.inputs.map fun j => w.getD j 0).sum := by
              dsimp only [weight]
              rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
              rfl
            have v (x) : (step (rows x) z).getD w.length false = z.op.eval (z.inputs.map fun j => (rows x).getD j false) := by
              dsimp only [step]
              rw [List.getD_append_right _ _ _ _ (by rw [lens]), lens, Nat.sub_self]
              rfl
            simpa only [e, v] using gate z hz.1 hz.2 w rows old
          · apply empty ((weight w z).getD j 0) (fun x => (step (rows x) z).getD j false)
            intro x
            apply List.getD_eq_default
            simp only [step, List.length_append, List.length_cons, List.length_nil, lens]
            omega
  let base := List.replicate 11 (1 : Nat)
  have init (j : Nat) : Rep (base.getD j 0) (fun x => (List.ofFn x).getD j false) := by
    by_cases small : j < 11
    · let v : Fin 11 := ⟨j, small⟩
      have val (x : Fin 11 → Bool) : (List.ofFn x).getD j false = x v := by
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using small), List.getElem_ofFn]
      have cost : base.getD j 0 = 1 := by
        rw [List.getD_eq_getElem _ _ (by simpa only [base, List.length_replicate] using small)]
        simp only [base, List.getElem_replicate]
      intro P N hp hn
      refine ⟨[(v, P, N)], cost ▸ Nat.le_refl 1, ?_, ?_⟩
      · intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨fun i hi => (val _).symm.trans (hp i hi), fun k hk => (val _).symm.trans (hn k hk)⟩
      · intro i k
        change (([(v, P, N)] : List R).filter (fun r => r.2.1 i && r.2.2 k)).length = _
        cases h : P i && N k <;> simp only [List.filter_cons, h, Bool.false_eq_true, ite_false, List.filter_nil, List.length_nil, Bool.toNat_false, ite_true, List.length_cons, Bool.toNat_true]
    · apply empty (base.getD j 0) (fun x => (List.ofFn x).getD j false)
      intro x
      exact List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)
  have expansion := expand C.gates (fun g hg => ⟨least.1.1 g hg, least.1.2.2 g hg⟩) base List.ofFn
    (fun _ => by simp only [base, List.length_ofFn, List.length_replicate]) init C.output
  change Rep ((C.gates.foldl weight base).getD C.output 0) (fun x => C.eval (List.ofFn x)) at expansion
  have computes (x : Fin 11 → Bool) : C.eval (List.ofFn x) = graphFun G ∅ x := congrFun least.2.1 x
  obtain ⟨rs, small, legal, total⟩ := expansion (fun _ => true) (fun _ => true)
    (fun i _ => (computes _).trans (validRows.1 i)) (fun j _ => (computes _).trans (validRows.2 j))
  exact (rectangles rs legal total).trans small
