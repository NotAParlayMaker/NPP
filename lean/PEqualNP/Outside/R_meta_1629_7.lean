import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reduce L-meta-1629 by proving 2 * N <= C.size + 1 (closing q <= 199), ReadsBack,
-- and minimality inline, then splitting q >= 200 into (1) the HasLineDegree 1 lower
-- bound (from single-line soundness) and (2) line-degree-1 normal-form elimination
-- from q-line dense soundness.
theorem PEqualNP.Outside.R_meta_1629_7 :
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.MetaComplexity.Monotone2 D →
      PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) D 1 →
      (∀ p l : Fin N, I p l →
        PEqualNP.MetaComplexity.circuitFun (N + N) D
          (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 1 →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) D z = false) →
      N * q + N ≤ D.size + 1) →
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.MetaComplexity.IsMinimalMonoCircuit (N + N) C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C →
      (∀ p l : Fin N, I p l →
        PEqualNP.MetaComplexity.circuitFun (N + N) C
          (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) D 1 ∧
        D.size + 1 ≤ 100 * C.size + N ∧
        (∀ p l : Fin N, I p l →
          PEqualNP.MetaComplexity.circuitFun (N + N) D
            (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) ∧
        (∀ z : Fin (N + N) → Bool,
          Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 1 →
          (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
          PEqualNP.MetaComplexity.circuitFun (N + N) D z = false)) →
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → N * q ≤ 100 * C.size := by
  classical
  intro hDeg1 hElim q N I _ C₀ hq hN hcard hline hmono₀ hpos₀ hsound₀
  let stepW : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hfold_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g rest ih =>
      intro w
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp [stepW]
      omega
  have hclean : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      ∃ C' : Circuit, Monotone2 C' ∧ C'.size = C.size ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n C' ∧
        circuitFun n C' = circuitFun n C := by
    intro n C hC
    let cleanGate : ℕ → Gate → Gate := fun bound g =>
      if g.op = GateOp.and ∧ ∃ i ∈ g.inputs, bound ≤ i then
        ⟨GateOp.or, []⟩
      else
        ⟨g.op, g.inputs.filter (fun i => decide (i < bound))⟩
    have hclean_eval : ∀ (bound : ℕ) (g : Gate) (w : List Bool),
        w.length = bound →
        g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) →
        (cleanGate bound g).op.eval ((cleanGate bound g).inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
      intro bound g w hlen hop
      dsimp only [cleanGate]
      split_ifs with h
      · obtain ⟨hand, i, hi, hge⟩ := h
        rw [hand]
        change false = (g.inputs.map fun i => w.getD i false).all id
        symm
        rw [List.all_eq_false]
        refine ⟨false, ?_, by decide⟩
        rw [List.mem_map]
        refine ⟨i, hi, ?_⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hand | hor
        · have hall : ∀ i ∈ g.inputs, i < bound := by
            intro i hi
            by_contra hlt
            exact h ⟨hand, i, hi, by omega⟩
          have hfilt : g.inputs.filter (fun i => decide (i < bound)) = g.inputs := by
            rw [List.filter_eq_self]
            intro i hi
            simp [hall i hi]
          rw [hfilt]
        · rw [hor]
          change ((g.inputs.filter (fun i => decide (i < bound))).map fun i => w.getD i false).any id =
            (g.inputs.map fun i => w.getD i false).any id
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq, id_eq]
          constructor
          · rintro ⟨_, ⟨i, ⟨hi, _⟩, rfl⟩, htrue⟩
            exact ⟨true, ⟨i, hi, htrue⟩, rfl⟩
          · rintro ⟨_, ⟨i, hi, htrue⟩, rfl⟩
            have hlt : i < bound := by
              by_contra hge
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at htrue
              cases htrue
            exact ⟨true, ⟨i, ⟨hi, hlt⟩, htrue⟩, rfl⟩
    let cleanList : ℕ → List Gate → List Gate := fun base gs =>
      (gs.zipIdx base).map (fun p => cleanGate p.2 p.1)
    have hclean_len : ∀ base gs, (cleanList base gs).length = gs.length := by
      intro base gs
      simp [cleanList]
    have hclean_fold : ∀ (base : ℕ) (gs : List Gate) (w : List Bool),
        w.length = base →
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
        (cleanList base gs).foldl stepW w = gs.foldl stepW w := by
      intro base gs
      induction gs generalizing base with
      | nil => intro w _ _; simp [cleanList]
      | cons g rest ih =>
        intro w hlen hop
        simp only [cleanList, List.zipIdx_cons, List.map_cons, List.foldl_cons]
        have hev := hclean_eval base g w hlen (hop g List.mem_cons_self)
        have hstep : stepW w (cleanGate base g) = stepW w g := by
          dsimp only [stepW]
          rw [hev]
        rw [hstep]
        exact ih (base + 1) (stepW w g) (by simp [stepW, hlen])
          (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    let C' : Circuit := ⟨cleanList n C.gates, C.output⟩
    refine ⟨C', ?_, ?_, ?_, ?_⟩
    · intro g' hg'
      simp only [C', cleanList, List.mem_map] at hg'
      obtain ⟨⟨g, idx⟩, hmem, rfl⟩ := hg'
      have hg : g ∈ C.gates := by
        have hmem2 := List.mem_iff_getElem.mp hmem
        obtain ⟨k, hk, hget⟩ := hmem2
        have hlenz : (C.gates.zipIdx n).length = C.gates.length := List.length_zipIdx
        rw [List.getElem_zipIdx] at hget
        have hk1 : C.gates[k]'(by omega) = g := congrArg Prod.fst hget
        rw [← hk1]
        exact List.getElem_mem (by omega)
      obtain ⟨hop, hlen2⟩ := hC g hg
      dsimp only [cleanGate]
      split_ifs
      · exact ⟨Or.inr rfl, by simp⟩
      · exact ⟨hop, (List.length_filter_le _ _).trans hlen2⟩
    · change (cleanList n C.gates).length = C.gates.length
      exact hclean_len n C.gates
    · intro j hj i hi
      simp only [C', cleanList] at hj
      rw [List.length_map, List.length_zipIdx] at hj
      have hlen' : j < C'.gates.length := by simp [C', cleanList]; exact hj
      have hget : PEqualNP.MetaComplexity.NestedCover.gateAt C' j =
          cleanGate (n + j) (C.gates[j]'hj) := by
        change C'.gates.getD j ⟨GateOp.or, []⟩ = cleanGate (n + j) (C.gates[j]'hj)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen']
        simp only [Option.getD_some, C', cleanList, List.getElem_map, List.getElem_zipIdx]
      rw [hget] at hi
      dsimp only [cleanGate] at hi
      split_ifs at hi with hcond
      · simp at hi
      · simp only [List.mem_filter, decide_eq_true_eq] at hi
        exact hi.2
    · funext x
      have hw : (cleanList n C.gates).foldl stepW (List.ofFn x) =
          C.gates.foldl stepW (List.ofFn x) :=
        hclean_fold n C.gates (List.ofFn x) (by simp) (fun g hg => (hC g hg).1)
      change ((cleanList n C.gates).foldl stepW (List.ofFn x)).getD C.output false =
        (C.gates.foldl stepW (List.ofFn x)).getD C.output false
      rw [hw]
  let R : ℕ → Prop := fun s => ∃ D : Circuit, D.size = s ∧ Monotone2 D ∧
    circuitFun (N + N) D = circuitFun (N + N) C₀
  have hex : ∃ s, R s := ⟨C₀.size, C₀, rfl, hmono₀, rfl⟩
  obtain ⟨C₁, hC₁size, hmono₁, hfun₁⟩ := Nat.find_spec hex
  obtain ⟨C, hmono, hCsize, hrb, hfun₂⟩ := hclean (N + N) C₁ hmono₁
  have hfun : circuitFun (N + N) C = circuitFun (N + N) C₀ := hfun₂.trans hfun₁
  have hle : C.size ≤ C₀.size := by
    rw [hCsize, hC₁size]
    exact Nat.find_min' hex ⟨C₀, rfl, hmono₀, rfl⟩
  have hmin : IsMinimalMonoCircuit (N + N) C := by
    refine ⟨hmono, ?_⟩
    intro D hD hDf
    rw [hCsize, hC₁size]
    exact Nat.find_min' hex ⟨D, rfl, hD, hDf.trans hfun⟩
  have hpos : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true := by
    intro p l hI
    rw [hfun]
    exact hpos₀ p l hI
  have hsound : ∀ z : Fin (N + N) → Bool,
      (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false := by
    intro z hq' hno
    rw [hfun]
    exact hsound₀ z hq' hno
  suffices hgoal : N * q ≤ 100 * C.size from hgoal.trans (Nat.mul_le_mul_left 100 hle)
  by_cases hlarge : 200 ≤ q
  · have hcardSub : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1 := fun l => by
      simpa only [Fintype.card_subtype] using hcard l
    have hsoundSub : ∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false := fun z hq' hno =>
      hsound z (by simpa only [Fintype.card_subtype] using hq') hno
    obtain ⟨D, hDmono, hDdeg, hDsize, hDpos, hDsound⟩ :=
      hElim q N I C hlarge hN hcardSub hline hmin hrb hpos hsoundSub
    have hDlb := hDeg1 q N I D hlarge hN hcardSub hline hDmono hDdeg hDpos hDsound
    omega
  · have hNge : 7 ≤ N := by nlinarith
    have hcast_ne_nat : ∀ p l : Fin N, Fin.castAdd N p ≠ Fin.natAdd N l := by
      intro p l h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    have hsens : ∀ k : Fin (N + N), ∃ x y : Fin (N + N) → Bool,
        (∀ j : Fin (N + N), j ≠ k → x j = y j) ∧
        circuitFun (N + N) C x ≠ circuitFun (N + N) C y := by
      intro k
      by_cases hk : k.val < N
      · let p : Fin N := ⟨k.val, hk⟩
        have hkp : k = Fin.castAdd N p := Fin.ext rfl
        let p' : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
        have hne : p ≠ p' := by
          intro h
          have hv := congrArg Fin.val h
          by_cases hp0 : p.val = 0 <;> simp [p', hp0] at hv
        obtain ⟨l, ⟨hIpl, _⟩, _⟩ := hline p p' hne
        let x : Fin (N + N) → Bool := fun j => decide (j = Fin.natAdd N l)
        let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
        refine ⟨x, y, ?_, ?_⟩
        · intro j hjk
          have hjp : j ≠ Fin.castAdd N p := by rwa [← hkp]
          simp [x, y, hjp]
        · have hy : circuitFun (N + N) C y = true := hpos p l hIpl
          have hx : circuitFun (N + N) C x = false := by
            apply hsound x
            · have hsub : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) ⊆ {l} := by
                intro l' hl'
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, decide_eq_true_eq] at hl'
                have : l' = l := Fin.ext (by
                  have := congrArg Fin.val hl'
                  simp only [Fin.val_natAdd] at this
                  omega)
                simp [this]
              exact (Finset.card_le_card hsub).trans (by simp; omega)
            · rintro ⟨p₀, l₀, _, hp₀, _⟩
              simp only [x, decide_eq_true_eq] at hp₀
              exact hcast_ne_nat p₀ l hp₀
          rw [hx, hy]
          decide
      · let l : Fin N := ⟨k.val - N, by omega⟩
        have hkl : k = Fin.natAdd N l := Fin.ext (by simp [l]; omega)
        have hne_l : (Finset.univ.filter (fun p => I p l)).Nonempty := by
          rw [← Finset.card_pos, hcard l]
          omega
        obtain ⟨p, hp⟩ := hne_l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        let x : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p)
        let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
        refine ⟨x, y, ?_, ?_⟩
        · intro j hjk
          have hjl : j ≠ Fin.natAdd N l := by rwa [← hkl]
          simp only [x, y, hjl, or_false]
        · have hy : circuitFun (N + N) C y = true := hpos p l hp
          have hx : circuitFun (N + N) C x = false := by
            apply hsound x
            · have hemp : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) = ∅ := by
                ext l'
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                  iff_false, x, decide_eq_true_eq]
                exact fun h => hcast_ne_nat p l' h.symm
              rw [hemp]
              simp
            · rintro ⟨p₀, l₀, _, _, hl₀⟩
              simp only [x, decide_eq_true_eq] at hl₀
              exact hcast_ne_nat p l₀ hl₀.symm
          rw [hx, hy]
          decide
    have hcone : ∀ (m : ℕ), m ≤ C.gates.length →
        ∃ S : Finset ℕ, S.card ≤ C.gates.length - m + 1 ∧
          (∀ w ∈ S, w < N + N + m ∨ w = C.output) ∧
          ∀ x y : Fin (N + N) → Bool,
            (∀ w ∈ S, ((C.gates.take m).foldl stepW (List.ofFn x)).getD w false =
              ((C.gates.take m).foldl stepW (List.ofFn y)).getD w false) →
            circuitFun (N + N) C x = circuitFun (N + N) C y := by
      intro m hm
      obtain ⟨d, hd⟩ : ∃ d, m = C.gates.length - d ∧ d ≤ C.gates.length :=
        ⟨C.gates.length - m, by omega, by omega⟩
      induction d generalizing m with
      | zero =>
        have hmeq : m = C.gates.length := by omega
        subst hmeq
        refine ⟨{C.output}, by simp, ?_, ?_⟩
        · intro w hw; simp at hw; exact Or.inr hw
        · intro x y hagree
          have h1 := hagree C.output (by simp)
          simp only [List.take_length] at h1
          exact h1
      | succ d ih =>
        have hm1 : m + 1 ≤ C.gates.length := by omega
        obtain ⟨S', hS'card, hS'lt, hS'eq⟩ := ih (m + 1) hm1 ⟨by omega, by omega⟩
        have hlen_take : ∀ x : Fin (N + N) → Bool,
            ((C.gates.take m).foldl stepW (List.ofFn x)).length = N + N + m := by
          intro x
          rw [hfold_len]
          simp [List.length_take]
          omega
        have hstep_take : ∀ x : Fin (N + N) → Bool,
            (C.gates.take (m + 1)).foldl stepW (List.ofFn x) =
              stepW ((C.gates.take m).foldl stepW (List.ofFn x)) (C.gates[m]'(by omega)) := by
          intro x
          rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
            List.foldl_append, List.foldl_cons, List.foldl_nil]
        by_cases hmem : N + N + m ∈ S'
        · let g := C.gates[m]'(by omega)
          let S := S'.erase (N + N + m) ∪ g.inputs.toFinset
          refine ⟨S, ?_, ?_, ?_⟩
          · have h1 : S.card ≤ (S'.erase (N + N + m)).card + g.inputs.toFinset.card :=
              Finset.card_union_le _ _
            have h2 : (S'.erase (N + N + m)).card + 1 = S'.card :=
              Finset.card_erase_add_one hmem
            have h3 : g.inputs.toFinset.card ≤ 2 :=
              (List.toFinset_card_le g.inputs).trans (hmono g (List.getElem_mem _)).2
            omega
          · intro w hw
            simp only [S, Finset.mem_union, Finset.mem_erase, List.mem_toFinset] at hw
            rcases hw with ⟨hne, hw'⟩ | hgin
            · rcases hS'lt w hw' with hlt | hout
              · left; omega
              · exact Or.inr hout
            · left
              have hrbm : w ∈ (C.gates.getD m ⟨GateOp.or, []⟩).inputs → w < N + N + m :=
                hrb m (by omega) w
              rw [List.getD_eq_getElem?_getD,
                List.getElem?_eq_getElem (by omega : m < C.gates.length),
                Option.getD_some] at hrbm
              exact hrbm hgin
          · intro x y hagree
            apply hS'eq x y
            intro w hw
            rw [hstep_take x, hstep_take y]
            have hlenx := hlen_take x
            have hleny := hlen_take y
            set vx := (C.gates.take m).foldl stepW (List.ofFn x)
            set vy := (C.gates.take m).foldl stepW (List.ofFn y)
            by_cases hwm : w = N + N + m
            · subst hwm
              dsimp only [stepW]
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
                List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
              simp only [hlenx, hleny, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              congr 1
              apply List.map_congr_left
              intro i hi
              exact hagree i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
            · have hwS : w ∈ S := Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hw⟩)
              have hwa := hagree w hwS
              dsimp only [stepW]
              by_cases hwlt : w < N + N + m
              · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
                  List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
                simpa only [List.getD_eq_getElem?_getD] using hwa
              · rw [List.getD_eq_getElem?_getD,
                  List.getElem?_eq_none (by simp [hlenx]; omega),
                  List.getD_eq_getElem?_getD,
                  List.getElem?_eq_none (by simp [hleny]; omega)]
        · refine ⟨S', by omega, ?_, ?_⟩
          · intro w hw
            rcases hS'lt w hw with hlt | hout
            · have hne : w ≠ N + N + m := fun heq => hmem (heq ▸ hw)
              left; omega
            · exact Or.inr hout
          · intro x y hagree
            apply hS'eq x y
            intro w hw
            rw [hstep_take x, hstep_take y]
            have hlenx := hlen_take x
            have hleny := hlen_take y
            have hne : w ≠ N + N + m := fun heq => hmem (heq ▸ hw)
            have hwa := hagree w hw
            set vx := (C.gates.take m).foldl stepW (List.ofFn x)
            set vy := (C.gates.take m).foldl stepW (List.ofFn y)
            dsimp only [stepW]
            by_cases hwlt : w < N + N + m
            · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
                List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
              simpa only [List.getD_eq_getElem?_getD] using hwa
            · rw [List.getD_eq_getElem?_getD,
                List.getElem?_eq_none (by simp [hlenx]; omega),
                List.getD_eq_getElem?_getD,
                List.getElem?_eq_none (by simp [hleny]; omega)]
    obtain ⟨S₀, hS₀card, _, hS₀eq⟩ := hcone 0 (Nat.zero_le _)
    have hsub : Finset.range (N + N) ⊆ S₀ := by
      intro i hi
      rw [Finset.mem_range] at hi
      by_contra hnot
      obtain ⟨x, y, hdiff, hneq⟩ := hsens ⟨i, hi⟩
      apply hneq
      apply hS₀eq x y
      intro w hw
      simp only [List.take_zero, List.foldl_nil]
      by_cases hwlt : w < N + N
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
        simp only [Option.getD_some, List.getElem_ofFn]
        exact hdiff ⟨w, hwlt⟩ (fun heq => hnot (by
          have hwi : w = i := congrArg Fin.val heq
          exact hwi ▸ hw))
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    have h2N : N + N ≤ C.size + 1 := by
      have hc := Finset.card_le_card hsub
      rw [Finset.card_range] at hc
      change N + N ≤ C.gates.length + 1
      omega
    have hqle : q ≤ 199 := by omega
    by_cases hq10 : 10 ≤ q
    · have hN100 : 100 ≤ N := by nlinarith
      nlinarith
    · nlinarith
