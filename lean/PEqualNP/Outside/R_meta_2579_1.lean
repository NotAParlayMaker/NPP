import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.SplitCount

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2579_1
    (births : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ (m : ℕ) (B : Fin m → Finset (Fin n)) (q : Fin m → Fin 2 → Fin n) (E : Finset (Sym2 (Fin n))),
        (∀ e ∈ E, ∃ (j : Fin m) (b : Fin 2) (x : Fin n),
          2 ≤ (B j).card ∧ B j ⊆ G.neighborFinset x ∧ e = s(x, q j b)) → E.card ≤ 2 * m)
    (repairs : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → let S := fun (w : ℕ) => Finset.univ.filter fun u : Fin n => wireVal n C w (unitInput u) = true
      ∀ E ⊆ Ustar G C, (∀ e ∈ E, ∃ (x y : Fin n) (j : ℕ), e = s(x,y) ∧ j < C.gates.length ∧
        (gateAt C j).op = GateOp.and ∧ y ∈ S (n+j) ∧ 2 ≤ (S (n+j)).card ∧
        S (n+j) ⊆ G.neighborFinset x ∧ ∀ i ∈ (gateAt C j).inputs, ¬ S i ⊆ G.neighborFinset x) →
        E.card ≤ k * (C.size + 1))
    (misses : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → ∀ E ⊆ Ustar G C, (∀ (x y : Fin n), s(x,y) ∈ E → ∀ j < C.gates.length,
        (2 ≤ (singletonSet n C j).card → (singletonSet n C j) ⊆ G.neighborFinset x → y ∉ singletonSet n C j) ∧
        (2 ≤ (orIn n C (n+j)).card → orIn n C (n+j) ⊆ G.neighborFinset x → ∀ b : Fin 2, orIn n C (opnd C j b) ≠ {y})) →
        E.card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k,hk⟩ := repairs
  obtain ⟨l,hl⟩ := misses
  refine ⟨k+l+2,?_⟩
  intro n G _ hg hn C hL hT
  have hn' : Nonempty (Fin n) := by
    obtain ⟨e,he⟩ := hn
    induction e using Sym2.ind with | _ a b => exact ⟨a⟩
  letI : Inhabited (Fin n) := Classical.inhabited_of_nonempty hn'
  -- S records actual singleton activations, including those surviving an AND.
  let S (w : ℕ) := Finset.univ.filter fun u : Fin n => wireVal n C w (unitInput u) = true
  let safe (x y : Fin n) (w : ℕ) : Prop := y ∈ S w ∧ 2 ≤ (S w).card ∧ S w ⊆ G.neighborFinset x
  let hit (e : Sym2 (Fin n)) : Prop := ∃ (x y : Fin n) (j : ℕ), e = s(x,y) ∧ j < C.gates.length ∧ safe x y (n+j)
  let repair (e : Sym2 (Fin n)) : Prop := ∃ (x y : Fin n) (j : ℕ), e = s(x,y) ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ safe x y (n+j) ∧ ∀ i ∈ (gateAt C j).inputs, ¬ S i ⊆ G.neighborFinset x
  let E := (Ustar G C).filter fun e => ¬ ∃ x y : Fin n, e = s(x,y) ∧ ∃ j < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n+j)).card ∧ (∀ z ∈ orIn n C (n+j), G.Adj x z) ∧ orIn n C (opnd C j b) = {y}
  change E.card ≤ _
  let R := E.filter repair
  let M := E.filter fun e => ¬ hit e
  let O := E \ (R ∪ M)
  have sub : E ⊆ Ustar G C := Finset.filter_subset _ _
  have rBound := hk n G hg hn C hL hT R ((Finset.filter_subset _ _).trans sub) (by
    intro e he
    obtain ⟨x,y,j,eq,hj,hop,hy,hh⟩ := (Finset.mem_filter.mp he).2
    exact ⟨x,y,j,eq,hj,hop,hy.1,hy.2.1,hy.2.2,hh⟩)
  have mBound := hl n G hg hn C hL hT M ((Finset.filter_subset _ _).trans sub) (by
    intro x y he j hj
    obtain ⟨he',hnHit⟩ := Finset.mem_filter.mp he
    constructor
    · intro hcard hsub hy
      apply hnHit
      exact ⟨x,y,j,rfl,hj,hy,hcard,hsub⟩
    · intro hcard hsub b hb
      apply (Finset.mem_filter.mp he').2
      exact ⟨x,y,rfl,j,hj,b,hcard,fun z hz => (G.mem_neighborFinset x z).mp (hsub hz),hb⟩)
  -- Compute singleton activations from the actual earlier operands of each gate.
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  have inputEq (z : Fin n) (i : ℕ) (hi : i < n) : wireVal n C i (unitInput z) = unitInput z ⟨i,hi⟩ := by
    change (C.wires (List.ofFn _)).getD i false = _
    rw [wires_eq_foldl, foldl_getD_lt _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD,hi]
  have gateEq (j : ℕ) (hj : j < C.gates.length) (z : Fin n) :
      wireVal n C (n+j) (unitInput z) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireVal n C i (unitInput z)) := by
    have h := foldl_getD_gate C.gates (List.ofFn (unitInput z)) j hj
    rw [List.length_ofFn] at h
    change (C.wires _).getD (n+j) false = _
    rw [wires_eq_foldl,h]
    have he : gateAt C j = C.gates[j] := by unfold gateAt; simp [List.getD_eq_getElem?_getD,hj]
    rw [← he]; congr 1
    apply List.map_congr_left
    intro i hi
    rw [if_pos (hL.1.2.1 j hj i hi)]
    rfl
  -- A slot is charged only when its operand has exactly one singleton activation.
  let q (j : Fin C.gates.length) (b : Fin 2) := if h : (S (opnd C j b)).Nonempty then h.choose else default
  have oBound := births n G hg C.gates.length (fun j => S (n+j)) q O (by
    intro e he
    obtain ⟨heE,hNo⟩ := Finset.mem_sdiff.mp he
    have hr : ¬ repair e := fun h => hNo (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heE,h⟩))
    have hh : hit e := by
      by_contra h
      exact hNo (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heE,h⟩))
    obtain ⟨x,y,j,eq,hj,hgood⟩ := hh
    -- Descend while the operand still has a large set contained in this neighborhood.
    have aux (w : ℕ) : w < n+C.gates.length → safe x y w → ∃ (a : Fin C.gates.length) (b : Fin 2), 2 ≤ (S (n+a)).card ∧ S (n+a) ⊆ G.neighborFinset x ∧ e = s(x,q a b) := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw h
        by_cases hinput : w < n
        · have hs : S w ⊆ {⟨w,hinput⟩} := by
            intro z hz
            have hv := (Finset.mem_filter.mp hz).2
            rw [inputEq z w hinput] at hv
            change decide (⟨w,hinput⟩ = z) = true at hv
            simpa [eq_comm] using hv
          have hle := Finset.card_le_card hs
          have := h.2.1
          simp at hle
          omega
        obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ w)
        have ha : a < C.gates.length := by omega
        have hmem : gateAt C a ∈ C.gates := by unfold gateAt; simp [List.getD_eq_getElem?_getD, ha]
        obtain ⟨p,t,hpt⟩ := List.length_eq_two.mp (hL.1.2.2 _ hmem)
        have read (i) (hi : i ∈ (gateAt C a).inputs) : i < n+a := hL.1.2.1 a ha i hi
        rcases hL.1.1 _ hmem with hand | hor
        · by_contra fail
          apply hr
          refine ⟨x,y,a,eq,ha,hand,h,?_⟩
          intro i hi hp
          have hs : S (n+a) ⊆ S i := by
            intro z hz
            apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,?_⟩
            have hv := (Finset.mem_filter.mp hz).2
            rw [gateEq a ha, hand] at hv
            change (((gateAt C a).inputs.map _).all id) = true at hv
            simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at hv
            exact hv i hi
          exact fail (ih i (read i hi) (by have := read i hi; omega) ⟨hs h.1,(h.2.1.trans (Finset.card_le_card hs)),hp⟩)
        · have lift (z : Fin n) : z ∈ S (n+a) ↔ ∃ i ∈ (gateAt C a).inputs, z ∈ S i := by
            simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,gateEq a ha,hor]
            change (((gateAt C a).inputs.map _).any id) = true ↔ _
            simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
          obtain ⟨i,hi,hy⟩ := (lift y).mp h.1
          have hs : S i ⊆ S (n+a) := fun z hz => (lift _).mpr ⟨i,hi,hz⟩
          by_cases large : 2 ≤ (S i).card
          · exact ih i (read i hi) (by have := read i hi; omega) ⟨hy,large,hs.trans h.2.2⟩
          have hb : ∃ b : Fin 2, opnd C a b = i := by
            rw [hpt] at hi
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl | rfl
            · exact ⟨0, by unfold opnd; rw [hpt]; rfl⟩
            · exact ⟨1, by unfold opnd; rw [hpt]; rfl⟩
          obtain ⟨b,hb⟩ := hb
          refine ⟨⟨a,ha⟩,b,h.2.1,h.2.2,?_⟩
          have hne : (S i).Nonempty := ⟨y,hy⟩
          have hq : q ⟨a,ha⟩ b ∈ S i := by simp only [q,hb,dif_pos hne]; exact hne.choose_spec
          rw [eq,(Finset.card_le_one.mp (by omega : (S i).card ≤ 1) y hy _ hq)]
    obtain ⟨a,b,h1,h2,h3⟩ := aux (n+j) (by omega) hgood
    exact ⟨a,b,x,h1,h2,h3⟩)
  have u : E ⊆ O ∪ (R ∪ M) := by
    intro e he
    by_cases h : e ∈ R ∪ M
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he,h⟩)
  have eu := Finset.card_le_card u
  have u1 := Finset.card_union_le O (R ∪ M)
  have u2 := Finset.card_union_le R M
  change O.card ≤ 2 * C.size at oBound
  rw [Nat.add_mul,Nat.add_mul]
  omega
