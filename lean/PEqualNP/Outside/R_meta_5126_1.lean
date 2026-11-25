import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_5126_1
    (patchClean : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {i j a b : ℕ},
      IsLeastAO G C → junk G C = {i,j} → i < j → a < n+j → b < n+j →
      (∀ x, wireVal n C a x = true → wireVal n C b x = true → graphFun G ∅ x = true) →
      (∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = true →
        wireVal n C a (pairInput u v) = true ∧ wireVal n C b (pairInput u v) = true) →
      ∃ D, IsLeastAO G D ∧ junk G D = {i})
    (classify : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  (PEqualNP.TopForm.junk G C).card ≠ 1) →
      ∀ {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
      {i j : ℕ} (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
      junk G C = {i,j} → i < j →
      (∀ k ∈ junk G C, ∀ v : Fin n, gateVal n C k (PEqualNP.SplitCount.unitInput v) = false) →
      (∃ u v : Fin n, u ≠ v ∧ ¬ G.Adj u v ∧ gateVal n C i (pairInput u v) = true) →
      2 ≤ (gammaE G C j).card →
      (2 ≤ (gammaE G C i).card ∨
        ∀ x, graphFun G ∅ x = false → gateVal n C j x = true → gateVal n C i x = true) →
      ∃ a b : ℕ, a < n+j ∧ b < n+j ∧
        (∀ x, wireVal n C a x = true → wireVal n C b x = true → graphFun G ∅ x = true) ∧
        ∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = true →
          wireVal n C a (pairInput u v) = true ∧ wireVal n C b (pairInput u v) = true)
    (early : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {i j : ℕ},
      IsLeastAO G C → junk G C = {i,j} → i < j →
      (∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1) →
      2 ≤ (gammaE G C i).card ∨
        ∀ x, graphFun G ∅ x = false → gateVal n C j x = true → gateVal n C i x = true) :
(∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  (PEqualNP.TopForm.junk G C).card ≠ 1) →
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  (∀ k ∈ PEqualNP.TopForm.junk G C, ∀ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (PEqualNP.SplitCount.unitInput v) = false) →
  (PEqualNP.TopForm.junk G C).card ≠ 2 := by
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

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

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = _
    simp [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    dsimp only [val]; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    dsimp only [val]; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  have val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
      val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    change (List.any _ id) = true ↔ _
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < n + r
      · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
      · rw [if_neg hlt] at h; cases h
    · rintro ⟨i, hi, hlt, h⟩
      exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

  have val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
      (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
      val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
    rw [val_gate hx hr, hop]
    change (List.all _ id) = true ↔ _
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi
      have h' := h i hi
      by_cases hlt : i < n + r
      · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
      · rw [if_neg hlt] at h'; cases h'
    · intro h i hi
      rw [if_pos (h i hi).1]; exact (h i hi).2

  have val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
      val C (List.ofFn x) u.val = x u := by
    rw [val_input (n := n) (by simp) u.isLt]
    simp [List.getD_eq_getElem?_getD]

  have firstSources {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
      {C : Circuit} (hc : IsAO2 n C) {i : ℕ}
      (first : ∀ t < i, t ∉ junk G C) {x : Fin n → Bool}
      (indep : graphFun G ∅ x = false) (w : ℕ) (hw : w < n+i)
      (lit : val C (List.ofFn x) w = true) :
      ∃ u : Fin n, x u = true ∧
        ∀ z : Fin n → Bool, z u = true → val C (List.ofFn z) w = true := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases raw : w < n
      · let u : Fin n := ⟨w, raw⟩
        refine ⟨u, (val_ofFn C x u).symm.trans lit, ?_⟩
        intro z hz
        exact (val_ofFn C z u).trans hz
      · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
        have ji : j < i := by omega
        by_cases existsGate : j < C.gates.length
        · rcases hc.1 _ (gateAt_mem existsGate) with hand|hor
          · have dirty : IsDirtyAnd n G C j := ⟨hand,existsGate,x,lit,indep⟩
            exact False.elim ((first j ji) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr existsGate,dirty⟩))
          · obtain ⟨u,hu,lt,htrue⟩ := (val_or (n := n) (by simp) existsGate hor).mp lit
            obtain ⟨v,hv,suff⟩ := ih u lt (by omega) htrue
            refine ⟨v,hv,fun z hz => ?_⟩
            exact (val_or (n := n) (by simp) existsGate hor).mpr ⟨u,hu,lt,suff z hz⟩
        · have hz := val_ge (C := C) (x := List.ofFn x) (n := n) (by simp)
              (u := n+j) (by omega)
          simp [hz] at lit

  have firstWrongPair {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
      {C : Circuit} (hc : IsAO2 n C) {i : ℕ} (hmem : i ∈ junk G C)
      (first : ∀ t < i, t ∉ junk G C)
      (off : ∀ v : Fin n, gateVal n C i (PEqualNP.SplitCount.unitInput v) = false) :
      ∃ u v : Fin n, u ≠ v ∧ ¬ G.Adj u v ∧ gateVal n C i (pairInput u v) = true := by
    have dirty : IsDirtyAnd n G C i := (Finset.mem_filter.mp hmem).2
    obtain ⟨hand,hi,x,hx,hind⟩ := dirty
    have hx' : val C (List.ofFn x) (n+i) = true := hx
    have both := (val_and (n := n) (by simp) hi hand).mp hx'
    have two := hc.2.2 _ (gateAt_mem hi)
    obtain ⟨a,b,hab⟩ : ∃ a b, (gateAt C i).inputs = [a,b] := by
      rcases he : (gateAt C i).inputs with _|⟨a,bs⟩
      · simp [he] at two
      · cases bs with
        | nil => simp [he] at two
        | cons b rest =>
          cases rest with
          | nil => exact ⟨a,b,rfl⟩
          | cons c cs => simp [he] at two
    have ha := both a (by simp [hab])
    have hb := both b (by simp [hab])
    obtain ⟨u,hu,sa⟩ := firstSources hc first hind a ha.1 ha.2
    obtain ⟨v,hv,sb⟩ := firstSources hc first hind b hb.1 hb.2
    have suff (z : Fin n → Bool) (zu : z u = true) (zv : z v = true) :
        gateVal n C i z = true := by
      apply (val_and (x := List.ofFn z) (n := n) (by simp) hi hand).mpr
      intro k hk
      simp [hab] at hk
      rcases hk with rfl|rfl
      · exact ⟨ha.1, sa z zu⟩
      · exact ⟨hb.1, sb z zv⟩
    refine ⟨u,v,?_,?_,suff _ (decide_eq_true (Or.inl rfl)) (decide_eq_true (Or.inr rfl))⟩
    · intro eq
      subst v
      have h := suff (PEqualNP.SplitCount.unitInput u) (decide_eq_true rfl)
        (decide_eq_true rfl)
      rw [off u] at h
      cases h
    · intro adj
      have edge : graphFun G ∅ x = true := by
        delta graphFun
        simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
          decide_eq_true_eq]
        exact ⟨u,v,adj,hu,hv⟩
      rw [edge] at hind
      cases hind

  have pairWitness : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
      {C : Circuit} {i j : ℕ}, IsLeastAO G C → junk G C = {i,j} → i < j →
      (∀ v : Fin n, gateVal n C i (PEqualNP.SplitCount.unitInput v) = false) →
      ∃ u v : Fin n, u ≠ v ∧ ¬ G.Adj u v ∧ gateVal n C i (pairInput u v) = true := by
    intro n G inst C i j least dirt lt off
    apply firstWrongPair least.1 (i := i) (by rw [dirt]; exact Finset.mem_insert_self ..) _ off
    intro t ht hm
    rw [dirt] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega

  have smallCover : ∀ {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
      {C : Circuit} {i j : ℕ}, IsLeastAO G C → junk G C = {i,j} → i < j →
      (gammaE G C j).card ≤ 1 →
      ∃ a b : ℕ, a < n+j ∧ b < n+j ∧
        (∀ x, wireVal n C a x = true → wireVal n C b x = true → graphFun G ∅ x = true) ∧
        ∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = true →
          wireVal n C a (pairInput u v) = true ∧ wireVal n C b (pairInput u v) = true := by
    intro n G inst C i j least dirt ij small
    classical
    have exedge : ∃ u v, G.Adj u v := by
      by_contra! empty
      let D : Circuit := ⟨[], n⟩
      have arch : IsAO2 n D := by
        refine ⟨?_,?_,?_⟩
        · intro g hg; cases hg
        · intro j hj; exact False.elim (Nat.not_lt_zero j hj)
        · intro g hg; cases hg
      have func : circuitFun n D = graphFun G ∅ := by
        funext x
        have out : circuitFun n D x = false := by
          change (List.ofFn x).getD n false = false
          simp [List.getD_eq_getElem?_getD]
        rw [out]
        delta graphFun
        simp [empty]
      have zero := least.2.2 D arch func
      change C.gates.length ≤ 0 at zero
      have hj : j ∈ junk G C := by rw [dirt]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
      have hlen := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      omega
    have inGamma (u v : Fin n) (adj : G.Adj u v)
        (yes : gateVal n C j (pairInput u v) = true) : s(u,v) ∈ gammaE G C j := by
      apply Finset.mem_filter.mpr
      exact ⟨SimpleGraph.mem_edgeFinset.mpr adj,u,v,rfl,yes⟩
    obtain ⟨u,v,adj,allHits⟩ : ∃ u v, G.Adj u v ∧ ∀ p q, G.Adj p q →
        gateVal n C j (pairInput p q) = true → s(p,q) = s(u,v) := by
      by_cases hit : ∃ u v, G.Adj u v ∧ gateVal n C j (pairInput u v) = true
      · obtain ⟨u,v,adj,val⟩ := hit
        refine ⟨u,v,adj,fun p q hpq hp => ?_⟩
        exact Finset.card_le_one.mp small _ (inGamma p q hpq hp) _ (inGamma u v adj val)
      · obtain ⟨u,v,adj⟩ := exedge
        exact ⟨u,v,adj,fun p q hpq hp => (hit ⟨p,q,hpq,hp⟩).elim⟩
    let flow := fun (buf : List Bool) (g : Gate) =>
      buf ++ [g.op.eval (g.inputs.map fun k => buf.getD k false)]
    have prefixRead (gs : List Gate) (xs : List Bool) (w : ℕ) (hw : w < xs.length) :
        (gs.foldl flow xs).getD w false = xs.getD w false := by
      induction gs generalizing xs with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [flow]; omega)]
        exact List.getD_append _ _ _ _ hw
    have raw (x : Fin n → Bool) (p : Fin n) : wireVal n C p x = x p := by
      change (C.gates.foldl flow (List.ofFn x)).getD p false = x p
      have hp : (p : ℕ) < (List.ofFn x).length := by simp
      rw [prefixRead _ _ _ hp, List.getD_eq_getElem _ _ hp]
      simp
    refine ⟨u.val,v.val,by omega,by omega,?_,?_⟩
    · intro x xu xv
      rw [raw] at xu xv
      delta graphFun
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq]
      exact ⟨u,v,adj,xu,xv⟩
    · intro p q hpq hp
      rw [raw,raw]
      rcases Sym2.eq_iff.mp (allHits p q hpq hp) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> (delta pairInput; simp)
  intro noOne n G inst C s bip noFour least off two
  obtain ⟨p,q,hpq,hpair⟩ := Finset.card_eq_two.mp two
  obtain ⟨i,j,hij,hJ⟩ : ∃ i j : ℕ, i < j ∧ junk G C = {i,j} := by
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact ⟨p,q,hlt,hpair⟩
    · exact ⟨q,p,hgt,hpair.trans (Finset.pair_comm p q)⟩
  have hi : i ∈ junk G C := by
    rw [hJ]
    exact Finset.mem_insert_self ..
  have witness := pairWitness least hJ hij (off i hi)
  have constraints := early least hJ hij (fun D hD => noOne n G D s bip noFour hD)
  obtain ⟨a,b,ha,hb,clean,cover⟩ :=
    if h : 2 ≤ (gammaE G C j).card then classify noOne s bip noFour least hJ hij off witness h constraints
    else smallCover least hJ hij (by omega)
  obtain ⟨D,hD,hd⟩ := patchClean least hJ hij ha hb clean cover
  exact noOne n G D s bip noFour hD ((congrArg Finset.card hd).trans (Finset.card_singleton i))
