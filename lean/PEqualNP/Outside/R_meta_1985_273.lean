import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_1985_273
    (count : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (x = (fun _ => false) ∨ (∃ u : Fin n, x = fun z => decide (z = u)) ∨ (∃ u v : Fin n, x = fun z => decide (z = u ∨ z = v))) → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1)
    (dirty : let E : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
      let hit (x : Fin 14 → Bool) : Prop := ∃ u v : Fin 14, (u.val,v.val) ∈ E ∧ x u = true ∧ x v = true
      let small (x : Fin 14 → Bool) : Prop := x = (fun _ => false) ∨
        (∃ u : Fin 14, x = fun z => decide (z = u)) ∨
        (∃ u v : Fin 14, x = fun z => decide (z = u ∨ z = v))
      ∀ C : Circuit, Monotone2 C → ReadsBack 14 C →
      (∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 14 C i j) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x) →
      (∃ i : Fin C.gates.length, (C.gates.get i).op = GateOp.and ∧
        ∃ x : Fin 14 → Bool, small x ∧ ¬hit x ∧ (C.wires (List.ofFn x)).getD (14+i.val) false = true) → 27 ≤ C.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 x5) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (27 : ℕ) ≤ x1.size := by
  classical
  let E : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let hit (x : Fin 14 → Bool) : Prop := ∃ u v : Fin 14, (u.val,v.val) ∈ E ∧ x u = true ∧ x v = true
  let small (x : Fin 14 → Bool) : Prop := x = (fun _ => false) ∨
    (∃ u : Fin 14, x = fun z => decide (z = u)) ∨
    (∃ u v : Fin 14, x = fun z => decide (z = u ∨ z = v))
  let adj (u v : Fin 14) : Bool := decide ((u.val,v.val) ∈ E ∨ (v.val,u.val) ∈ E)
  have symm : ∀ u v : Fin 14, adj u v = adj v u := by decide +kernel
  have irr : ∀ u : Fin 14, adj u u = false := by decide +kernel
  let G : SimpleGraph (Fin 14) := {
    Adj := fun u v => adj u v = true
    symm := by constructor; intro u v h; rw [symm v u]; exact h
    loopless := by constructor; intro u h; rw [irr u] at h; cases h }
  have c4 : ∀ a b c d : Fin 14, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    change ∀ a b c d : Fin 14, a ≠ c → b ≠ d →
      ¬ (adj a b = true ∧ adj b c = true ∧ adj c d = true ∧ adj d a = true)
    decide +kernel
  have edgeIff (x : Fin 14 → Bool) : hit x ↔ ∃ u v : Fin 14, G.Adj u v ∧ x u = true ∧ x v = true := by
    constructor
    · rintro ⟨u,v,he,hu,hv⟩
      refine ⟨u,v,?_,hu,hv⟩
      change decide ((u.val,v.val) ∈ E ∨ (v.val,u.val) ∈ E) = true
      simpa only [decide_eq_true_eq] using (Or.inl he : (u.val,v.val) ∈ E ∨ (v.val,u.val) ∈ E)
    · rintro ⟨u,v,hg,hu,hv⟩
      have hh : (u.val,v.val) ∈ E ∨ (v.val,u.val) ∈ E := of_decide_eq_true hg
      rcases hh with hh | hh
      · exact ⟨u,v,hh,hu,hv⟩
      · exact ⟨v,u,hh,hv,hu⟩
  let P : Finset (Fin 14 × Fin 14) := Finset.univ.filter (fun p => p.1 < p.2 ∧ adj p.1 p.2 = true)
  have pc : P.card = 21 := by decide +kernel
  have edgeCount (inst : Fintype G.edgeSet) : 21 ≤ (@SimpleGraph.edgeFinset _ G inst).card := by
    rw [←pc]
    refine Finset.card_le_card_of_injOn (fun p => s(p.1,p.2)) ?_ ?_
    · intro p hp
      have hh : p.1 < p.2 ∧ adj p.1 p.2 = true := by simpa [P] using hp
      simp only [Finset.mem_coe,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
      exact hh.2
    · intro p hp q hq he
      have hpp : p.1 < p.2 := (Finset.mem_filter.mp hp).2.1
      have hqq : q.1 < q.2 := (Finset.mem_filter.mp hq).2.1
      rw [Sym2.eq_iff] at he
      rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact Prod.ext h1 h2
      · rw [h1,h2] at hpp
        exact False.elim ((not_lt_of_ge hqq.le) hpp)
  let idx : Fin 14 → Fin 7 := ![0,1,2,3,4,5,6,1,2,5,0,6,3,4]
  let left : Fin 7 → Fin 14 := ![0,1,2,3,4,5,6]
  let right : Fin 7 → Fin 14 := ![10,7,8,12,13,9,11]
  have matching : ∀ i : Fin 7, G.Adj (left i) (right i) ∧ idx (left i) = i ∧ idx (right i) = i := by
    change ∀ i : Fin 7, adj (left i) (right i) = true ∧ idx (left i) = i ∧ idx (right i) = i
    decide +kernel
  have coverCount (T : Finset (Fin 14)) (cover : ∀ u v : Fin 14, G.Adj u v → u ∈ T ∨ v ∈ T) : 7 ≤ T.card := by
    have hs : (Finset.univ : Finset (Fin 7)) ⊆ T.image idx := by
      intro i _
      obtain ⟨he,hl,hr⟩ := matching i
      rcases cover _ _ he with ht | ht
      · exact Finset.mem_image.mpr ⟨_,ht,hl⟩
      · exact Finset.mem_image.mpr ⟨_,ht,hr⟩
    have h1 := Finset.card_le_card hs
    have h2 := Finset.card_image_le (s := T) (f := idx)
    rw [Finset.card_univ,Fintype.card_fin] at h1
    omega
  intro C mono back nested correct
  change ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x at correct
  by_cases bad : ∃ i : Fin C.gates.length, (C.gates.get i).op = GateOp.and ∧
      ∃ x : Fin 14 → Bool, small x ∧ ¬ hit x ∧
        (C.wires (List.ofFn x)).getD (14+i.val) false = true
  · exact dirty C mono back nested correct bad
  · have clean (i : Fin C.gates.length) (x : Fin 14 → Bool) (hx : small x)
        (hop : (C.gates.get i).op = GateOp.and)
        (hv : (C.wires (List.ofFn x)).getD (14+i.val) false = true) : hit x := by
      by_contra hn
      exact bad ⟨i,hop,x,hx,hn,hv⟩
    have ops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (mono g hg).1,(mono g hg).2⟩
    have computes : ∀ x : Fin 14 → Bool,
        C.eval (List.ofFn x) = decide (∃ u v : Fin 14, G.Adj u v ∧ x u = true ∧ x v = true) := by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact (correct x).trans (edgeIff x)
    obtain ⟨T,cover,hcard⟩ := @count 14 G inferInstance c4 C.gates C.output ops computes (by
      intro i x hx hop hv
      apply (edgeIff x).mp
      exact clean i x hx hop hv)
    have h28 := le_trans (Nat.add_le_add (edgeCount _) (coverCount T cover)) hcard
    change 27 ≤ C.gates.length
    omega
