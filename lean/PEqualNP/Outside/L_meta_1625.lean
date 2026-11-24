import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1625_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

local instance : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq

/-! ### 1. Wire evaluation and line-degree lemmas -/

private def runWires (gs : List Gate) (acc : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc

private lemma runWires_cons (g : Gate) (gs : List Gate) (acc : List Bool) :
    runWires (g :: gs) acc =
      runWires gs (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) := rfl

private lemma runWires_append (gs1 gs2 : List Gate) (acc : List Bool) :
    runWires (gs1 ++ gs2) acc = runWires gs2 (runWires gs1 acc) := by
  simp [runWires, List.foldl_append]

private lemma runWires_length (gs : List Gate) (acc : List Bool) :
    (runWires gs acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [runWires]
  | cons g gs ih => rw [runWires_cons, ih]; simp; omega

private lemma runWires_getD_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (runWires gs acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [runWires_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private def wireVal (N : ℕ) (C : Circuit) (w : ℕ) (x : Fin N → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma circuitFun_eq_wireVal (N : ℕ) (C : Circuit) (x : Fin N → Bool) :
    circuitFun N C x = wireVal N C C.output x := rfl

private lemma wireVal_input {N : ℕ} (C : Circuit) (x : Fin N → Bool) (p : Fin N) :
    wireVal N C p.val x = x p := by
  change (runWires C.gates (List.ofFn x)).getD p.val false = x p
  have hp : p.val < (List.ofFn x).length := by simp
  rw [runWires_getD_prefix _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma wireVal_oob {N : ℕ} (C : Circuit) (x : Fin N → Bool) (w : ℕ)
    (hw : N + C.gates.length ≤ w) : wireVal N C w x = false := by
  change (runWires C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simp [runWires_length]; omega)

private lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ hj

private lemma wireVal_gate {N : ℕ} (C : Circuit) (x : Fin N → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    wireVal N C (N + j) x =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun r => if r < N + j then wireVal N C r x else false) := by
  let g := C.gates[j]
  let pre := runWires (C.gates.take j) (List.ofFn x)
  have hpre_len : pre.length = N + j := by
    simp [pre, runWires_length, Nat.min_eq_left hj.le]
  have hsplit : runWires C.gates (List.ofFn x) = runWires (g :: C.gates.drop (j + 1)) pre := by
    have h1 : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_lhs => rw [h1]
    rw [runWires_append, List.drop_eq_getElem_cons hj]
  have hread (r : ℕ) : pre.getD r false = if r < N + j then wireVal N C r x else false := by
    by_cases hr : r < N + j
    · rw [ite_eq_left hr]
      change pre.getD r false = (runWires C.gates (List.ofFn x)).getD r false
      rw [hsplit]
      exact (runWires_getD_prefix _ pre r (by omega)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (runWires C.gates (List.ofFn x)).getD (N + j) false = _
  rw [gateAt_eq_getElem C j hj]
  change (runWires C.gates (List.ofFn x)).getD (N + j) false =
    g.op.eval (g.inputs.map fun r => if r < N + j then wireVal N C r x else false)
  rw [hsplit, runWires_cons, runWires_getD_prefix _ _ _ (by simp [hpre_len])]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hpre_len, Nat.sub_self, List.getD_cons_zero, hread]

private lemma wireVal_take {N : ℕ} (C : Circuit) (x : Fin N → Bool) (k w : ℕ)
    (hw : w < N + min k C.gates.length) :
    wireVal N ⟨C.gates.take k, 0⟩ w x = wireVal N C w x := by
  change (runWires (C.gates.take k) (List.ofFn x)).getD w false =
    (runWires C.gates (List.ofFn x)).getD w false
  have hsplit : runWires C.gates (List.ofFn x) =
      runWires (C.gates.drop k) (runWires (C.gates.take k) (List.ofFn x)) := by
    have h1 : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    conv_lhs => rw [h1]
    rw [runWires_append]
  rw [hsplit]
  symm
  exact runWires_getD_prefix _ _ _ (by simp [runWires_length]; omega)

private lemma wireVal_append_prefix {N : ℕ} (gs1 gs2 : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : w < N + gs1.length) :
    wireVal N ⟨gs1 ++ gs2, 0⟩ w x = wireVal N ⟨gs1, 0⟩ w x := by
  change (runWires (gs1 ++ gs2) (List.ofFn x)).getD w false =
    (runWires gs1 (List.ofFn x)).getD w false
  rw [runWires_append, runWires_getD_prefix]
  simp [runWires_length]
  omega

private lemma gate_eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f1 f2 : ℕ → Bool) (h : ∀ r ∈ g.inputs, f1 r = true → f2 r = true) :
    g.op.eval (g.inputs.map f1) = true → g.op.eval (g.inputs.map f2) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map]
    rintro h1 b ⟨r, hr, rfl⟩
    exact h r hr (h1 _ ⟨r, hr, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
    rintro ⟨b, ⟨r, hr, rfl⟩, hbt⟩
    exact ⟨_, ⟨r, hr, rfl⟩, h r hr hbt⟩

private lemma wireVal_mono {N : ℕ} (C : Circuit) (hM : Monotone2 C)
    (x y : Fin N → Bool) (hxy : ∀ p : Fin N, x p = true → y p = true) :
    ∀ w : ℕ, wireVal N C w x = true → wireVal N C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwx
    by_cases hlt : w < N
    · have h1 := wireVal_input C x ⟨w, hlt⟩
      have h2 := wireVal_input C y ⟨w, hlt⟩
      rw [h1] at hwx; rw [h2]; exact hxy ⟨w, hlt⟩ hwx
    · by_cases hbd : w < N + C.gates.length
      · let j := w - N
        have hj : j < C.gates.length := by omega
        have hwj : w = N + j := by omega
        rw [hwj] at hwx ⊢
        rw [wireVal_gate C x j hj] at hwx
        rw [wireVal_gate C y j hj]
        have hmem : gateAt C j ∈ C.gates := by
          rw [gateAt_eq_getElem C j hj]; exact List.getElem_mem hj
        have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
          have := (hM (gateAt C j) hmem).1
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
        refine gate_eval_mono (gateAt C j) hop _ _ ?_ hwx
        intro r _ hrt
        by_cases hr : r < N + j
        · simp only [hr, ↓reduceIte] at hrt ⊢
          exact ih r (by omega) hrt
        · simp [hr] at hrt
      · rw [wireVal_oob C x w (by omega)] at hwx
        exact absurd hwx (by decide)

private def runLD (gs : List Gate) (acc : List ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) acc

private lemma runLD_cons (g : Gate) (gs : List Gate) (acc : List ℕ) :
    runLD (g :: gs) acc = runLD gs (acc ++ [g.lineDegree acc]) := rfl

private lemma runLD_append (gs1 gs2 : List Gate) (acc : List ℕ) :
    runLD (gs1 ++ gs2) acc = runLD gs2 (runLD gs1 acc) := by
  simp [runLD, List.foldl_append]

private lemma runLD_length (gs : List Gate) (acc : List ℕ) :
    (runLD gs acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [runLD]
  | cons g gs ih => rw [runLD_cons, ih]; simp; omega

private lemma runLD_getD_prefix (gs : List Gate) (acc : List ℕ) (w : ℕ) (hw : w < acc.length) :
    (runLD gs acc).getD w 0 = acc.getD w 0 := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [runLD_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private def ldVal (n m : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0

private lemma ldVal_input_pt (n m : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    ldVal n m C w = 0 := by
  unfold ldVal Circuit.lineDegrees
  change (runLD C.gates _).getD w 0 = 0
  have hlt : w < ((List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0).length := by
    simp; omega
  rw [runLD_getD_prefix _ _ _ hlt, List.getD_eq_getElem _ _ hlt]
  simp [Finset.mem_Ico]
  omega

private lemma ldVal_input_ln (n m : ℕ) (C : Circuit) (w : ℕ) (hn : n ≤ w) (hw : w < n + m) :
    ldVal n m C w = 1 := by
  unfold ldVal Circuit.lineDegrees
  change (runLD C.gates _).getD w 0 = 1
  have hlt : w < ((List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0).length := by
    simp; omega
  rw [runLD_getD_prefix _ _ _ hlt, List.getD_eq_getElem _ _ hlt]
  simp [Finset.mem_Ico, hn, hw]

private lemma ldVal_gate (n m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    ldVal n m C (n + m + j) =
      if (gateAt C j).op = GateOp.and then
        ((gateAt C j).inputs.map fun r => if r < n + m + j then ldVal n m C r else 0).sum
      else
        ((gateAt C j).inputs.map fun r => if r < n + m + j then ldVal n m C r else 0).foldr max 0 := by
  let g := C.gates[j]
  let init := (List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0
  let pre := runLD (C.gates.take j) init
  have hpre_len : pre.length = n + m + j := by
    simp [pre, init, runLD_length, Nat.min_eq_left hj.le]
  have hsplit : runLD C.gates init = runLD (g :: C.gates.drop (j + 1)) pre := by
    have h1 : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_lhs => rw [h1]
    rw [runLD_append, List.drop_eq_getElem_cons hj]
  have hread (r : ℕ) : pre.getD r 0 = if r < n + m + j then ldVal n m C r else 0 := by
    by_cases hr : r < n + m + j
    · rw [ite_eq_left hr]
      change pre.getD r 0 = (runLD C.gates init).getD r 0
      rw [hsplit]
      exact (runLD_getD_prefix _ pre r (by omega)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (runLD C.gates init).getD (n + m + j) 0 = _
  rw [gateAt_eq_getElem C j hj]
  rw [hsplit, runLD_cons, runLD_getD_prefix _ _ _ (by simp [hpre_len])]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hpre_len, Nat.sub_self, List.getD_cons_zero, Gate.lineDegree, hread, g]

private lemma ldVal_take (n m : ℕ) (C : Circuit) (k w : ℕ)
    (hw : w < n + m + min k C.gates.length) :
    ldVal n m ⟨C.gates.take k, 0⟩ w = ldVal n m C w := by
  let init := (List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0
  change (runLD (C.gates.take k) init).getD w 0 = (runLD C.gates init).getD w 0
  have hsplit : runLD C.gates init = runLD (C.gates.drop k) (runLD (C.gates.take k) init) := by
    have h1 : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
    conv_lhs => rw [h1]
    rw [runLD_append]
  rw [hsplit]
  symm
  exact runLD_getD_prefix _ _ _ (by simp [runLD_length, init]; omega)

private def crossSet (n m : ℕ) (C : Circuit) : Set ℕ :=
  {j : ℕ | j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs.length = 2 ∧
    ∀ i ∈ (gateAt C j).inputs, 0 < ldVal n m C i}

private lemma crossSet_finite (n m : ℕ) (C : Circuit) : (crossSet n m C).Finite := by
  refine (Set.finite_lt_nat C.gates.length).subset ?_
  intro j hj
  exact hj.1

private lemma ldVal_le_one_of_no_cross (n m : ℕ) (C : Circuit) (hM : Monotone2 C)
    (hRB : ReadsBack (n + m) C) (hno : crossSet n m C = ∅) :
    ∀ w < n + m + C.gates.length, ldVal n m C w ≤ 1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hn : w < n
    · rw [ldVal_input_pt n m C w hn]; omega
    · by_cases hnm : w < n + m
      · rw [ldVal_input_ln n m C w (by omega) hnm]
      · let j := w - (n + m)
        have hj : j < C.gates.length := by omega
        have hwj : w = n + m + j := by omega
        rw [hwj, ldVal_gate n m C j hj]
        have hmem : gateAt C j ∈ C.gates := by
          rw [gateAt_eq_getElem C j hj]; exact List.getElem_mem hj
        have hlen := (hM (gateAt C j) hmem).2
        have hrb := hRB j hj
        by_cases hand : (gateAt C j).op = GateOp.and
        · rw [ite_eq_left hand]
          cases hin : (gateAt C j).inputs with
          | nil => simp
          | cons a rest =>
            cases rest with
            | nil =>
              have ha : a < n + m + j := hrb a (by rw [hin]; exact List.mem_cons_self)
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
                ite_eq_left ha]
              exact ih a (by omega) (by omega)
            | cons b rest2 =>
              have hrest2 : rest2 = [] := by
                rw [hin] at hlen
                cases rest2 with
                | nil => rfl
                | cons _ _ => simp at hlen
              subst hrest2
              have ha : a < n + m + j := hrb a (by rw [hin]; exact List.mem_cons_self)
              have hb : b < n + m + j := hrb b (by rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self)
              have hda := ih a (by omega) (by omega)
              have hdb := ih b (by omega) (by omega)
              have hnot : j ∉ crossSet n m C := by rw [hno]; exact Set.notMem_empty j
              have hzero : ldVal n m C a = 0 ∨ ldVal n m C b = 0 := by
                by_contra hpos
                apply hnot
                refine ⟨hj, hand, by rw [hin]; rfl, ?_⟩
                intro r hr
                rw [hin] at hr
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl | rfl <;> omega
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
                ite_eq_left ha, ite_eq_left hb]
              omega
        · rw [ite_eq_right hand]
          have hfold : ∀ l : List ℕ, (∀ r ∈ l, r < n + m + j) →
              (l.map fun r => if r < n + m + j then ldVal n m C r else 0).foldr max 0 ≤ 1 := by
            intro l hl
            induction l with
            | nil => simp
            | cons a t iht =>
              have ha : a < n + m + j := hl a List.mem_cons_self
              simp only [List.map_cons, List.foldr_cons, ite_eq_left ha, max_le_iff]
              exact ⟨ih a (by omega) (by omega), iht (fun r hr => hl r (List.mem_cons_of_mem _ hr))⟩
          exact hfold _ hrb

private lemma ldVal_zero_inputs (n m : ℕ) (C : Circuit) (hRB : ReadsBack (n + m) C)
    (j : ℕ) (hj : j < C.gates.length) (h0 : ldVal n m C (n + m + j) = 0) :
    ∀ r ∈ (gateAt C j).inputs, ldVal n m C r = 0 := by
  intro r hr
  have hrlt := hRB j hj r hr
  rw [ldVal_gate n m C j hj] at h0
  by_cases hand : (gateAt C j).op = GateOp.and
  · rw [ite_eq_left hand] at h0
    have hmem : (if r < n + m + j then ldVal n m C r else 0) ∈
        ((gateAt C j).inputs.map fun i => if i < n + m + j then ldVal n m C i else 0) :=
      List.mem_map.mpr ⟨r, hr, rfl⟩
    have hle := List.le_sum_of_mem hmem
    rw [ite_eq_left hrlt] at hle
    omega
  · rw [ite_eq_right hand] at h0
    have hfold : ∀ l : List ℕ, ∀ x ∈ l, x ≤ l.foldr max 0 := by
      intro l x hx
      induction l with
      | nil => cases hx
      | cons a t iht =>
        simp only [List.mem_cons] at hx
        simp only [List.foldr_cons]
        rcases hx with rfl | hx
        · exact le_max_left _ _
        · exact le_trans (iht hx) (le_max_right _ _)
    have hmem : (if r < n + m + j then ldVal n m C r else 0) ∈
        ((gateAt C j).inputs.map fun i => if i < n + m + j then ldVal n m C i else 0) :=
      List.mem_map.mpr ⟨r, hr, rfl⟩
    have hle := hfold _ _ hmem
    rw [ite_eq_left hrlt] at hle
    omega

private lemma ldVal_zero_indep (n m : ℕ) (C : Circuit) (hRB : ReadsBack (n + m) C)
    (x : Fin n → Bool) (y1 y2 : Fin m → Bool) :
    ∀ w < n + m + C.gates.length, ldVal n m C w = 0 →
      wireVal (n + m) C w (Fin.append x y1) = wireVal (n + m) C w (Fin.append x y2) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw h0
    by_cases hn : w < n
    · have h1 := wireVal_input C (Fin.append x y1) ⟨w, by omega⟩
      have h2 := wireVal_input C (Fin.append x y2) ⟨w, by omega⟩
      rw [h1, h2]
      have heq : (⟨w, by omega⟩ : Fin (n + m)) = Fin.castAdd m ⟨w, hn⟩ := by ext; rfl
      rw [heq, Fin.append_left, Fin.append_left]
    · by_cases hnm : w < n + m
      · rw [ldVal_input_ln n m C w (by omega) hnm] at h0
        omega
      · let j := w - (n + m)
        have hj : j < C.gates.length := by omega
        have hwj : w = n + m + j := by omega
        rw [hwj] at h0 ⊢
        rw [wireVal_gate C _ j hj, wireVal_gate C _ j hj]
        congr 1
        apply List.map_congr_left
        intro r hr
        have hrlt := hRB j hj r hr
        have hr0 := ldVal_zero_inputs n m C hRB j hj h0 r hr
        simp only [ite_eq_left hrlt]
        exact ih r (by omega) (by omega) hr0

/-! ### 2. Monotone cut lemma and point-side bounds -/

private lemma mono_gate_inputs {N : ℕ} (D : Circuit) (hM : Monotone2 D)
    (w : ℕ) (hn : N ≤ w) (hw : w < N + D.gates.length) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ x y : Fin N → Bool, (∀ r ∈ P, wireVal N D r x = true → wireVal N D r y = true) →
        wireVal N D w x = true → wireVal N D w y = true := by
  classical
  let j := w - N
  have hj : j < D.gates.length := by omega
  have hwj : w = N + j := by omega
  let g := gateAt D j
  have hmem : g ∈ D.gates := by rw [show g = D.gates[j] from gateAt_eq_getElem D j hj]; exact List.getElem_mem hj
  have hhop := (hM g hmem).1
  have hlen := (hM g hmem).2
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hhop
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr; exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    rw [hwj] at hx ⊢
    rw [wireVal_gate D x j hj] at hx
    rw [wireVal_gate D y j hj]
    refine gate_eval_mono g hop _ _ ?_ hx
    intro r hr hrt
    by_cases hlt : r < N + j
    · simp only [hlt, ↓reduceIte] at hrt ⊢
      exact hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, by omega⟩) hrt
    · simp [hlt] at hrt

private lemma cut {N : ℕ} (D : Circuit) (hM : Monotone2 D)
    (G : Finset ℕ) (hG : ∀ w ∈ G, N ≤ w ∧ w < N + D.gates.length) :
    ∀ (t : ℕ) (F : Finset ℕ), (∀ w ∈ F, w ∈ G → w < t) →
      ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
        ∀ x y : Fin N → Bool, (∀ w ∈ B, wireVal N D w x = true → wireVal N D w y = true) →
          ∀ w ∈ F, wireVal N D w x = true → wireVal N D w y = true := by
  intro t
  induction t with
  | zero =>
    intro F hF
    exact ⟨F, Finset.disjoint_left.mpr fun w hw hg => by have := hF w hw hg; omega,
      Nat.le_add_right _ _, fun _ _ h => h⟩
  | succ t ih =>
    intro F hF
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := mono_gate_inputs D hM t (hG t hex.2).1 (hG t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have h1 := Finset.mem_erase.mp hw
          have h2 := hF w h1.2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilt : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilt, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst h
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

private def ptSupp {n : ℕ} (D : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => wireVal n D w (fun v => decide (v = p)) = true

private lemma ptSupp_gate {n : ℕ} (D : Circuit) (w : ℕ) (h2 : 2 ≤ (ptSupp (n := n) D w).card) :
    n ≤ w ∧ w < n + D.gates.length := by
  constructor
  · by_contra hlt
    have hlt' : w < n := Nat.not_le.mp hlt
    let p0 : Fin n := ⟨w, hlt'⟩
    have hsub : ptSupp D w ⊆ {p0} := by
      intro q hq
      have hv : wireVal n D p0.val (fun v => decide (v = q)) = true :=
        (Finset.mem_filter.mp hq).2
      rw [wireVal_input] at hv
      exact Finset.mem_singleton.mpr (of_decide_eq_true hv).symm
    have := Finset.card_le_card hsub
    simp at this
    omega
  · by_contra hge
    have hempty : ptSupp (n := n) D w = ∅ := by
      ext q
      simp [ptSupp, wireVal_oob D _ w (Nat.not_lt.mp hge)]
    rw [hempty] at h2
    simp at h2

private lemma point_bound_single {n : ℕ} (D : Circuit) (hM : Monotone2 D)
    (T : Finset (Fin n)) (o : ℕ)
    (hsound : wireVal n D o (fun v => decide (v ∉ T)) = false) :
    (ptSupp (n := n) D o).card ≤ D.gates.length + 1 := by
  classical
  let G := Finset.Ico n (n + D.gates.length)
  have hG : ∀ w ∈ G, n ≤ w ∧ w < n + D.gates.length := fun w hw => Finset.mem_Ico.mp hw
  obtain ⟨B, hd, hBcard, hcut⟩ := cut D hM G hG (n + D.gates.length) {o}
    (fun w _ hw => (hG w hw).2)
  have hBle : B.card ≤ D.gates.length + 1 := by
    have h1 := Finset.card_filter_le G (· < n + D.gates.length)
    have h2 : G.card = D.gates.length := by simp [G]
    simp only [Finset.card_singleton] at hBcard
    omega
  let clean : Finset ℕ := B.filter fun w => wireVal n D w (fun v => decide (v ∉ T)) = false
  have hsub : ptSupp (n := n) D o ⊆ clean.biUnion (ptSupp (n := n) D) := by
    intro p hp
    have hvp : wireVal n D o (fun v => decide (v = p)) = true := (Finset.mem_filter.mp hp).2
    by_contra hno
    have htrue : wireVal n D o (fun v => decide (v ∉ T)) = true := by
      refine hcut (fun v => decide (v = p)) (fun v => decide (v ∉ T)) ?_ o
        (Finset.mem_singleton_self o) hvp
      intro w hw hwp
      by_contra hwf
      have hwf' : wireVal n D w (fun v => decide (v ∉ T)) = false := Bool.eq_false_iff.mpr hwf
      exact hno (Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hwf'⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ p, hwp⟩⟩)
    rw [hsound] at htrue
    exact Bool.false_ne_true htrue
  have hcard1 : ∀ w ∈ clean, (ptSupp (n := n) D w).card ≤ 1 := by
    intro w hw
    by_contra hgt
    have h2 : 2 ≤ (ptSupp (n := n) D w).card := by omega
    have hwg := ptSupp_gate D w h2
    exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hw).1 (Finset.mem_Ico.mpr hwg)
  have hbi := Finset.card_biUnion_le_card_mul clean (ptSupp (n := n) D) 1 hcard1
  have h1 := Finset.card_le_card hsub
  have h2 : clean.card ≤ B.card := Finset.card_filter_le B _
  simp only [mul_one] at hbi
  omega

private lemma point_bound_one_set {n : ℕ} (D : Circuit) (hM : Monotone2 D)
    (T : Finset (Fin n)) (o : ℕ)
    (hsound : wireVal n D o (fun v => decide (v ∉ T)) = false) :
    (T.filter fun p => wireVal n D o (fun v => decide (v = p)) = true).card ≤
      ((Finset.Ico n (n + D.gates.length)).filter fun w =>
        wireVal n D w (fun v => decide (v ∉ T)) = false ∧ 2 ≤ (ptSupp (n := n) D w).card).card + 1 := by
  classical
  let G := (Finset.Ico n (n + D.gates.length)).filter fun w =>
    wireVal n D w (fun v => decide (v ∉ T)) = false ∧ 2 ≤ (ptSupp (n := n) D w).card
  have hG : ∀ w ∈ G, n ≤ w ∧ w < n + D.gates.length := fun w hw =>
    Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut D hM G hG (n + D.gates.length) {o}
    (fun w _ hw => (hG w hw).2)
  have hBle : B.card ≤ G.card + 1 := by
    have h1 := Finset.card_filter_le G (· < n + D.gates.length)
    simp only [Finset.card_singleton] at hBcard
    omega
  let clean : Finset ℕ := B.filter fun w => wireVal n D w (fun v => decide (v ∉ T)) = false
  have hsub : (T.filter fun p => wireVal n D o (fun v => decide (v = p)) = true) ⊆
      clean.biUnion (ptSupp (n := n) D) := by
    intro p hp
    have hvp : wireVal n D o (fun v => decide (v = p)) = true := (Finset.mem_filter.mp hp).2
    by_contra hno
    have htrue : wireVal n D o (fun v => decide (v ∉ T)) = true := by
      refine hcut (fun v => decide (v = p)) (fun v => decide (v ∉ T)) ?_ o
        (Finset.mem_singleton_self o) hvp
      intro w hw hwp
      by_contra hwf
      have hwf' : wireVal n D w (fun v => decide (v ∉ T)) = false := Bool.eq_false_iff.mpr hwf
      exact hno (Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hwf'⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ p, hwp⟩⟩)
    rw [hsound] at htrue
    exact Bool.false_ne_true htrue
  have hcard1 : ∀ w ∈ clean, (ptSupp (n := n) D w).card ≤ 1 := by
    intro w hw
    by_contra hgt
    have h2 : 2 ≤ (ptSupp (n := n) D w).card := by omega
    have hwg := ptSupp_gate D w h2
    have hwf := (Finset.mem_filter.mp hw).2
    exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hw).1
      (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hwg, hwf, h2⟩)
  have hbi := Finset.card_biUnion_le_card_mul clean (ptSupp (n := n) D) 1 hcard1
  have h1 := Finset.card_le_card hsub
  have h2 : clean.card ≤ B.card := Finset.card_filter_le B _
  simp only [mul_one] at hbi
  change _ ≤ G.card + 1
  omega

private lemma point_bound_multi {n m : ℕ} (L : Fin m → Finset (Fin n))
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1)
    (D : Circuit) (hM : Monotone2 D)
    (G : Finset (Fin m)) (o : Fin m → ℕ)
    (hsound : ∀ l ∈ G, wireVal n D (o l) (fun v => decide (v ∉ L l)) = false) :
    (Finset.univ.filter fun e : Fin n × Fin m =>
      e.2 ∈ G ∧ e.1 ∈ L e.2 ∧ wireVal n D (o e.2) (fun v => decide (v = e.1)) = true).card ≤
      D.gates.length + G.card := by
  classical
  let asg (l : Fin m) : Finset ℕ := (Finset.Ico n (n + D.gates.length)).filter fun w =>
    wireVal n D w (fun v => decide (v ∉ L l)) = false ∧ 2 ≤ (ptSupp (n := n) D w).card
  have hdisj : Set.PairwiseDisjoint (G : Set (Fin m)) asg := by
    intro l1 _ l2 _ hne
    show Disjoint (asg l1) (asg l2)
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have h1 := (Finset.mem_filter.mp hw1).2
    have h2 := (Finset.mem_filter.mp hw2).2
    have hsub : ptSupp D w ⊆ L l1 ∩ L l2 := by
      intro p hp
      have hvp : wireVal n D w (fun v => decide (v = p)) = true := (Finset.mem_filter.mp hp).2
      have hpl1 : p ∈ L l1 := by
        by_contra hnot
        have htrue := wireVal_mono D hM (fun v => decide (v = p)) (fun v => decide (v ∉ L l1))
          (fun v hv => by
            simp only [decide_eq_true_eq] at hv ⊢; subst hv; exact hnot) w hvp
        rw [h1.1] at htrue; exact Bool.false_ne_true htrue
      have hpl2 : p ∈ L l2 := by
        by_contra hnot
        have htrue := wireVal_mono D hM (fun v => decide (v = p)) (fun v => decide (v ∉ L l2))
          (fun v hv => by
            simp only [decide_eq_true_eq] at hv ⊢; subst hv; exact hnot) w hvp
        rw [h2.1] at htrue; exact Bool.false_ne_true htrue
      exact Finset.mem_inter.mpr ⟨hpl1, hpl2⟩
    have := Finset.card_le_card hsub
    have := hL l1 l2 hne
    omega
  have hpair_eq : (Finset.univ.filter fun e : Fin n × Fin m =>
      e.2 ∈ G ∧ e.1 ∈ L e.2 ∧ wireVal n D (o e.2) (fun v => decide (v = e.1)) = true).card =
      ∑ l ∈ G, (L l |>.filter fun p => wireVal n D (o l) (fun v => decide (v = p)) = true).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun e _ => ⟨e.2, e.1⟩) ?_ ?_ ?_
    · intro e he
      have hm := (Finset.mem_filter.mp he).2
      exact Finset.mem_sigma.mpr ⟨hm.1, Finset.mem_filter.mpr ⟨hm.2.1, hm.2.2⟩⟩
    · intro e1 _ e2 _ h
      cases e1; cases e2; simp at h; rcases h with ⟨rfl, rfl⟩; rfl
    · intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_sigma.mp hs
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hs2
      exact ⟨(s.2, s.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs1, hp1, hp2⟩, rfl⟩
  rw [hpair_eq]
  have hsum : ∑ l ∈ G, (L l |>.filter fun p => wireVal n D (o l) (fun v => decide (v = p)) = true).card ≤
      ∑ l ∈ G, ((asg l).card + 1) :=
    Finset.sum_le_sum fun l hl => point_bound_one_set D hM (L l) (o l) (hsound l hl)
  have hbi : (G.biUnion asg).card ≤ D.gates.length := by
    have hsub : G.biUnion asg ⊆ Finset.Ico n (n + D.gates.length) := by
      intro w hw
      obtain ⟨l, _, hwl⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hwl).1
    exact (Finset.card_le_card hsub).trans (by simp)
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    ← Finset.card_biUnion hdisj] at hsum
  omega

/-! ### 3. Linear-in-y part and reverse-mode transpose for line-degree-1 circuits -/

private def linStep (n m : ℕ) (C : Circuit) (x : Fin n → Bool) (l : Fin m)
    (acc : List Bool) (j : ℕ) : List Bool :=
  let g := gateAt C j
  let v :=
    if ldVal n m C (n + m + j) = 0 then false
    else if g.op = GateOp.or then
      g.inputs.any fun r => acc.getD r false
    else
      match g.inputs with
      | [a] => acc.getD a false
      | [a, b] =>
        if ldVal n m C a = 0 then
          wireVal (n + m) C a (Fin.append x (fun _ => false)) && acc.getD b false
        else
          acc.getD a false && wireVal (n + m) C b (Fin.append x (fun _ => false))
      | _ => false
  acc ++ [v]

private def runLin (n m : ℕ) (C : Circuit) (x : Fin n → Bool) (l : Fin m) (k : ℕ) : List Bool :=
  (List.range k).foldl (linStep n m C x l)
    ((List.range (n + m)).map fun w => decide (w = n + l.val))

private lemma runLin_length (n m : ℕ) (C : Circuit) (x : Fin n → Bool) (l : Fin m) (k : ℕ) :
    (runLin n m C x l k).length = n + m + k := by
  induction k with
  | zero => simp [runLin]
  | succ k ih =>
    unfold runLin at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [linStep, List.length_append, List.length_singleton]
    omega

private lemma runLin_prefix (n m : ℕ) (C : Circuit) (x : Fin n → Bool) (l : Fin m)
    (k1 k2 w : ℕ) (hle : k1 ≤ k2) (hw : w < n + m + k1) :
    (runLin n m C x l k2).getD w false = (runLin n m C x l k1).getD w false := by
  induction k2 with
  | zero =>
    have : k1 = 0 := by omega
    subst this; rfl
  | succ k2 ih =>
    by_cases h : k1 = k2 + 1
    · subst h; rfl
    · have hle' : k1 ≤ k2 := by omega
      have hstep : runLin n m C x l (k2 + 1) =
          linStep n m C x l (runLin n m C x l k2) k2 := by
        unfold runLin
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hstep]
      unfold linStep
      rw [List.getD_append _ _ _ _ (by rw [runLin_length]; omega)]
      exact ih hle'

private def linVal (n m : ℕ) (C : Circuit) (x : Fin n → Bool) (l : Fin m) (w : ℕ) : Bool :=
  (runLin n m C x l C.gates.length).getD w false

private lemma linVal_input (n m : ℕ) (C : Circuit) (x : Fin n → Bool) (l : Fin m)
    (w : ℕ) (hw : w < n + m) :
    linVal n m C x l w = decide (w = n + l.val) := by
  unfold linVal
  rw [runLin_prefix n m C x l 0 C.gates.length w (Nat.zero_le _) hw]
  unfold runLin
  simp only [List.range_zero, List.foldl_nil]
  have hlt : w < ((List.range (n + m)).map fun i => decide (i = n + l.val)).length := by
    simp; omega
  rw [List.getD_eq_getElem _ _ hlt]
  simp

private lemma linVal_gate (n m : ℕ) (C : Circuit) (x : Fin n → Bool) (l : Fin m)
    (j : ℕ) (hj : j < C.gates.length) :
    linVal n m C x l (n + m + j) =
      if ldVal n m C (n + m + j) = 0 then false
      else if (gateAt C j).op = GateOp.or then
        (gateAt C j).inputs.any fun r => if r < n + m + j then linVal n m C x l r else false
      else
        match (gateAt C j).inputs with
        | [a] => if a < n + m + j then linVal n m C x l a else false
        | [a, b] =>
          if ldVal n m C a = 0 then
            wireVal (n + m) C a (Fin.append x (fun _ => false)) &&
              (if b < n + m + j then linVal n m C x l b else false)
          else
            (if a < n + m + j then linVal n m C x l a else false) &&
              wireVal (n + m) C b (Fin.append x (fun _ => false))
        | _ => false := by
  unfold linVal
  rw [runLin_prefix n m C x l (j + 1) C.gates.length (n + m + j) hj (by omega)]
  have hstep : runLin n m C x l (j + 1) = linStep n m C x l (runLin n m C x l j) j := by
    unfold runLin
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hstep]
  unfold linStep
  have hlen : (runLin n m C x l j).length = n + m + j := runLin_length n m C x l j
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlen, Nat.sub_self, List.getD_cons_zero]
  have hread (r : ℕ) : (runLin n m C x l j).getD r false =
      if r < n + m + j then (runLin n m C x l C.gates.length).getD r false else false := by
    by_cases hr : r < n + m + j
    · rw [ite_eq_left hr]
      exact (runLin_prefix n m C x l j C.gates.length r (le_of_lt hj) hr).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  by_cases h0 : ldVal n m C (n + m + j) = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    by_cases hor : (gateAt C j).op = GateOp.or
    · simp only [hor, ↓reduceIte]
      have hcongr : ∀ ks : List ℕ,
          ks.any (fun r => (runLin n m C x l j).getD r false) =
          ks.any (fun r => if r < n + m + j then (runLin n m C x l C.gates.length).getD r false else false) := by
        intro ks
        induction ks with
        | nil => rfl
        | cons a t iht => simp only [List.any_cons]; rw [hread a, iht]
      exact hcongr _
    · simp only [hor, ↓reduceIte]
      cases (gateAt C j).inputs with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => exact hread a
        | cons b rest2 =>
          cases rest2 with
          | nil =>
            by_cases ha0 : ldVal n m C a = 0
            · simp only [ha0, ↓reduceIte]; rw [hread b]
            · simp only [ha0, ↓reduceIte]; rw [hread a]
          | cons _ _ => rfl

private lemma linVal_zero_of_ld_zero (n m : ℕ) (C : Circuit) (x : Fin n → Bool) (l : Fin m)
    (w : ℕ) (hw : w < n + m + C.gates.length) (h0 : ldVal n m C w = 0) :
    linVal n m C x l w = false := by
  by_cases hn : w < n
  · rw [linVal_input n m C x l w (by omega)]
    exact decide_eq_false (by omega)
  · by_cases hnm : w < n + m
    · rw [ldVal_input_ln n m C w (by omega) hnm] at h0; omega
    · let j := w - (n + m)
      have hj : j < C.gates.length := by omega
      have hwj : w = n + m + j := by omega
      rw [hwj, linVal_gate n m C x l j hj, ite_eq_left (by rwa [← hwj])]

private lemma wireVal_single_line_decomp (n m : ℕ) (C : Circuit) (hM : Monotone2 C)
    (hRB : ReadsBack (n + m) C) (hno : crossSet n m C = ∅)
    (x : Fin n → Bool) (l : Fin m) :
    ∀ w < n + m + C.gates.length,
      wireVal (n + m) C w (Fin.append x (fun l' => decide (l' = l))) =
        (wireVal (n + m) C w (Fin.append x (fun _ => false)) || linVal n m C x l w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases h0 : ldVal n m C w = 0
    · rw [linVal_zero_of_ld_zero n m C x l w hw h0, Bool.or_false]
      exact ldVal_zero_indep n m C hRB x _ _ w hw h0
    · by_cases hn : w < n
      · exact absurd (ldVal_input_pt n m C w hn) h0
      · by_cases hnm : w < n + m
        · let l0 : Fin m := ⟨w - n, by omega⟩
          have hw0 : (⟨w, hnm⟩ : Fin (n + m)) = Fin.natAdd n l0 := by ext; simp [l0]; omega
          rw [wireVal_input C _ ⟨w, hnm⟩, wireVal_input C _ ⟨w, hnm⟩, hw0,
            Fin.append_right, Fin.append_right, linVal_input n m C x l w hnm, Bool.false_or]
          have : (l0 = l) ↔ (w = n + l.val) := by
            constructor
            · intro h; rw [← h]; simp [l0]; omega
            · intro h; ext; simp [l0]; omega
          exact decide_eq_decide.mpr this
        · let j := w - (n + m)
          have hj : j < C.gates.length := by omega
          have hwj : w = n + m + j := by omega
          rw [hwj] at h0 ⊢
          have hmem : gateAt C j ∈ C.gates := by
            rw [gateAt_eq_getElem C j hj]; exact List.getElem_mem hj
          have hhop := (hM (gateAt C j) hmem).1
          have hlen := (hM (gateAt C j) hmem).2
          have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hhop
          have hrb := hRB j hj
          rw [wireVal_gate C _ j hj, wireVal_gate C _ j hj, linVal_gate n m C x l j hj,
            ite_eq_right h0]
          rcases hop with hand | hor
          · have hnor : (gateAt C j).op ≠ GateOp.or := by rw [hand]; decide
            rw [ite_eq_right hnor, hand]
            cases hin : (gateAt C j).inputs with
            | nil =>
              rw [ldVal_gate n m C j hj, ite_eq_left hand, hin] at h0
              simp at h0
            | cons a rest =>
              cases rest with
              | nil =>
                have ha := hrb a (by rw [hin]; exact List.mem_cons_self)
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  id_eq, Bool.and_true, ite_eq_left ha]
                exact ih a (by omega) (by omega)
              | cons b rest2 =>
                have hrest2 : rest2 = [] := by
                  rw [hin] at hlen
                  cases rest2 with
                  | nil => rfl
                  | cons _ _ => simp at hlen
                subst hrest2
                have ha := hrb a (by rw [hin]; exact List.mem_cons_self)
                have hb := hrb b (by rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self)
                have hzero : ldVal n m C a = 0 ∨ ldVal n m C b = 0 := by
                  by_contra hpos
                  have : j ∈ crossSet n m C := by
                    refine ⟨hj, hand, by rw [hin]; rfl, ?_⟩
                    intro r hr; rw [hin] at hr
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                    rcases hr with rfl | rfl <;> omega
                  rw [hno] at this; exact this
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  id_eq, Bool.and_true, ite_eq_left ha, ite_eq_left hb]
                rw [ih a (by omega) (by omega), ih b (by omega) (by omega)]
                by_cases ha0 : ldVal n m C a = 0
                · rw [ite_eq_left ha0, linVal_zero_of_ld_zero n m C x l a (by omega) ha0,
                    Bool.or_false, Bool.and_or_distrib_left]
                · have hb0 : ldVal n m C b = 0 := hzero.resolve_left ha0
                  rw [ite_eq_right ha0, linVal_zero_of_ld_zero n m C x l b (by omega) hb0,
                    Bool.or_false, Bool.and_or_distrib_right]
          · rw [ite_eq_left hor, hor]
            have hor_list : ∀ ks : List ℕ, (∀ r ∈ ks, r < n + m + j) →
                GateOp.eval GateOp.or (ks.map fun r => if r < n + m + j then
                  wireVal (n + m) C r (Fin.append x (fun l' => decide (l' = l))) else false) =
                (GateOp.eval GateOp.or (ks.map fun r => if r < n + m + j then
                  wireVal (n + m) C r (Fin.append x (fun _ => false)) else false) ||
                  ks.any (fun r => if r < n + m + j then linVal n m C x l r else false)) := by
              intro ks hks
              induction ks with
              | nil => simp [GateOp.eval]
              | cons a t iht =>
                have ha := hks a List.mem_cons_self
                have ht := iht (fun r hr => hks r (List.mem_cons_of_mem _ hr))
                simp only [GateOp.eval, List.map_cons, List.any_cons, id_eq, ite_eq_left ha] at ht ⊢
                rw [ih a (by omega) (by omega), ht]
                cases wireVal (n + m) C a (Fin.append x (fun _ => false)) <;>
                cases linVal n m C x l a <;>
                cases (t.map _).any id <;>
                cases t.any _ <;> rfl
            exact hor_list _ hrb

-- Build the point-only subcircuit gs0 containing ONLY deg-0 gates of C
private def ptCopyStep (n m : ℕ) (C : Circuit) (st : List Gate × (ℕ → ℕ)) (j : ℕ) :
    List Gate × (ℕ → ℕ) :=
  if ldVal n m C (n + m + j) = 0 then
    let g := gateAt C j
    let g' : Gate := ⟨g.op, g.inputs.map st.2⟩
    let newW := n + st.1.length
    (st.1 ++ [g'], fun w => if w = n + m + j then newW else st.2 w)
  else
    st

private def ptCopy (n m : ℕ) (C : Circuit) (k : ℕ) : List Gate × (ℕ → ℕ) :=
  (List.range k).foldl (ptCopyStep n m C) ([], id)

private lemma ptCopy_props (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hRB : ReadsBack (n + m) C) :
    ∀ k ≤ C.gates.length,
      Monotone2 ⟨(ptCopy n m C k).1, 0⟩ ∧
      (ptCopy n m C k).1.length = ((Finset.range k).filter fun j => ldVal n m C (n + m + j) = 0).card ∧
      (∀ w < n + m + k, ldVal n m C w = 0 →
        (ptCopy n m C k).2 w < n + (ptCopy n m C k).1.length ∧
        ∀ x : Fin n → Bool,
          wireVal n ⟨(ptCopy n m C k).1, 0⟩ ((ptCopy n m C k).2 w) x =
            wireVal (n + m) C w (Fin.append x (fun _ => false))) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨(by intro g hg; cases hg), (by simp [ptCopy]), ?_⟩
    intro w hw h0
    have hn : w < n := by
      by_contra hge
      rw [ldVal_input_ln n m C w (by omega) hw] at h0
      omega
    refine ⟨by simp [ptCopy]; omega, ?_⟩
    intro x
    have hwnm : w < n + m := by omega
    simp only [ptCopy, List.range_zero, List.foldl_nil, id_eq]
    rw [wireVal_input ⟨[], 0⟩ x ⟨w, hn⟩, wireVal_input C _ ⟨w, hwnm⟩]
    have : (⟨w, hwnm⟩ : Fin (n + m)) = Fin.castAdd m ⟨w, hn⟩ := by ext; rfl
    rw [this, Fin.append_left]
  | succ k ih =>
    intro hk
    obtain ⟨hM0, hlen0, hev0⟩ := ih (by omega)
    have hstep : ptCopy n m C (k + 1) = ptCopyStep n m C (ptCopy n m C k) k := by
      unfold ptCopy
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    unfold ptCopyStep
    have hfilt : (Finset.range (k + 1)).filter (fun j => ldVal n m C (n + m + j) = 0) =
        if ldVal n m C (n + m + k) = 0 then
          insert k ((Finset.range k).filter fun j => ldVal n m C (n + m + j) = 0)
        else (Finset.range k).filter fun j => ldVal n m C (n + m + j) = 0 := by
      rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h0 : ldVal n m C (n + m + k) = 0
    · simp only [h0, ↓reduceIte]
      have hklen : k < C.gates.length := by omega
      have hgk_mem : gateAt C k ∈ C.gates := by
        rw [gateAt_eq_getElem C k hklen]; exact List.getElem_mem hklen
      have hgk := hM (gateAt C k) hgk_mem
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hM0 g hg
        · exact ⟨hgk.1, by simp [hgk.2]⟩
      · rw [hfilt, ite_eq_left h0, Finset.card_insert_of_notMem (by simp)]
        simp [hlen0]
      · intro w hw hw0
        by_cases hwk : w = n + m + k
        · subst hwk
          simp only [↓reduceIte, List.length_append, List.length_singleton]
          refine ⟨by omega, ?_⟩
          intro x
          let gs := (ptCopy n m C k).1
          let idx := (ptCopy n m C k).2
          let g' : Gate := ⟨(gateAt C k).op, (gateAt C k).inputs.map idx⟩
          have hgw := wireVal_gate ⟨gs ++ [g'], 0⟩ x gs.length (by simp)
          have hgat : gateAt ⟨gs ++ [g'], 0⟩ gs.length = g' := by
            rw [gateAt_eq_getElem _ _ (by simp)]
            simp
          rw [hgw, hgat, wireVal_gate C _ k hklen]
          simp only [g', List.map_map]
          congr 1
          apply List.map_congr_left
          intro r hr
          have hrlt := hRB k hklen r hr
          have hr0 := ldVal_zero_inputs n m C hRB k hklen h0 r hr
          obtain ⟨hrbd, hrev⟩ := hev0 r hrlt hr0
          have hrbd' : idx r < n + gs.length := hrbd
          simp only [Function.comp_apply, ite_eq_left hrlt, ite_eq_left hrbd']
          rw [wireVal_append_prefix gs [g'] x (idx r) hrbd', hrev x]
        · simp only [hwk, ↓reduceIte, List.length_append, List.length_singleton]
          have hwlt : w < n + m + k := by omega
          obtain ⟨hbd, hev⟩ := hev0 w hwlt hw0
          refine ⟨by omega, fun x => ?_⟩
          rw [wireVal_append_prefix _ _ x _ hbd, hev x]
    · simp only [h0, ↓reduceIte]
      refine ⟨hM0, ?_, ?_⟩
      · rw [hfilt, ite_eq_right h0]; exact hlen0
      · intro w hw hw0
        have hne : w ≠ n + m + k := fun e => h0 (e ▸ hw0)
        exact hev0 w (by omega) hw0

-- Symbolic wire for backward sweep (avoids adding constant gates)
private inductive DWire where
  | zero
  | one
  | wire (w : ℕ)

private def dEval (n : ℕ) (gs : List Gate) (x : Fin n → Bool) : DWire → Bool
  | DWire.zero => false
  | DWire.one => true
  | DWire.wire w => wireVal n ⟨gs, 0⟩ w x

private def dOk (n : ℕ) (gs : List Gate) : DWire → Prop
  | DWire.zero => True
  | DWire.one => True
  | DWire.wire w => w < n + gs.length

private lemma dEval_append (n : ℕ) (gs1 gs2 : List Gate) (x : Fin n → Bool) (d : DWire)
    (hok : dOk n gs1 d) :
    dEval n (gs1 ++ gs2) x d = dEval n gs1 x d := by
  cases d with
  | zero => rfl
  | one => rfl
  | wire w => exact wireVal_append_prefix gs1 gs2 x w hok

private def dOr (n : ℕ) (gs : List Gate) (d1 d2 : DWire) : List Gate × DWire :=
  match d1, d2 with
  | DWire.zero, d => (gs, d)
  | d, DWire.zero => (gs, d)
  | DWire.one, _ => (gs, DWire.one)
  | _, DWire.one => (gs, DWire.one)
  | DWire.wire u, DWire.wire v => (gs ++ [⟨GateOp.or, [u, v]⟩], DWire.wire (n + gs.length))

private lemma dOr_spec (n : ℕ) (gs : List Gate) (hM : Monotone2 ⟨gs, 0⟩) (d1 d2 : DWire)
    (h1 : dOk n gs d1) (h2 : dOk n gs d2) :
    let res := dOr n gs d1 d2
    (∃ tail, res.1 = gs ++ tail ∧ tail.length ≤ 1) ∧
    Monotone2 ⟨res.1, 0⟩ ∧
    dOk n res.1 res.2 ∧
    ∀ x : Fin n → Bool, dEval n res.1 x res.2 = (dEval n gs x d1 || dEval n gs x d2) := by
  cases d1 with
  | zero =>
    refine ⟨⟨[], by simp [dOr], by simp⟩, hM, h2, fun x => by simp [dOr, dEval]⟩
  | one =>
    cases d2 <;> refine ⟨⟨[], by simp [dOr], by simp⟩, hM, trivial, fun x => by simp [dOr, dEval]⟩
  | wire u =>
    cases d2 with
    | zero => refine ⟨⟨[], by simp [dOr], by simp⟩, hM, h1, fun x => by simp [dOr, dEval]⟩
    | one => refine ⟨⟨[], by simp [dOr], by simp⟩, hM, trivial, fun x => by simp [dOr, dEval]⟩
    | wire v =>
      refine ⟨⟨[⟨GateOp.or, [u, v]⟩], rfl, by simp⟩, ?_, ?_, ?_⟩
      · intro g hg
        simp only [dOr, List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hM g hg
        · exact ⟨by simp, by simp⟩
      · change n + gs.length < n + (gs ++ [(⟨GateOp.or, [u, v]⟩ : Gate)]).length
        simp
      · intro x
        change wireVal n ⟨gs ++ [(⟨GateOp.or, [u, v]⟩ : Gate)], 0⟩ (n + gs.length) x = _
        rw [wireVal_gate ⟨gs ++ [(⟨GateOp.or, [u, v]⟩ : Gate)], 0⟩ x gs.length (by simp)]
        have hgat : gateAt ⟨gs ++ [(⟨GateOp.or, [u, v]⟩ : Gate)], 0⟩ gs.length = ⟨GateOp.or, [u, v]⟩ := by
          rw [gateAt_eq_getElem _ _ (by simp)]; simp
        rw [hgat]
        have hu : u < n + gs.length := h1
        have hv : v < n + gs.length := h2
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
          Bool.or_false, ite_eq_left hu, ite_eq_left hv]
        rw [wireVal_append_prefix gs _ x u hu, wireVal_append_prefix gs _ x v hv]
        rfl

private def dAndWire (n : ℕ) (gs : List Gate) (u : ℕ) (d : DWire) : List Gate × DWire :=
  match d with
  | DWire.zero => (gs, DWire.zero)
  | DWire.one => (gs, DWire.wire u)
  | DWire.wire v => (gs ++ [⟨GateOp.and, [u, v]⟩], DWire.wire (n + gs.length))

private lemma dAndWire_spec (n : ℕ) (gs : List Gate) (hM : Monotone2 ⟨gs, 0⟩) (u : ℕ) (d : DWire)
    (hu : u < n + gs.length) (hd : dOk n gs d) :
    let res := dAndWire n gs u d
    (∃ tail, res.1 = gs ++ tail ∧ tail.length ≤ 1) ∧
    Monotone2 ⟨res.1, 0⟩ ∧
    dOk n res.1 res.2 ∧
    ∀ x : Fin n → Bool, dEval n res.1 x res.2 = (wireVal n ⟨gs, 0⟩ u x && dEval n gs x d) := by
  cases d with
  | zero =>
    refine ⟨⟨[], by simp [dAndWire], by simp⟩, hM, trivial, fun x => by simp [dAndWire, dEval]⟩
  | one =>
    refine ⟨⟨[], by simp [dAndWire], by simp⟩, hM, hu, fun x => by simp [dAndWire, dEval]⟩
  | wire v =>
    refine ⟨⟨[⟨GateOp.and, [u, v]⟩], rfl, by simp⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp only [dAndWire, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hM g hg
      · exact ⟨by simp, by simp⟩
    · change n + gs.length < n + (gs ++ [(⟨GateOp.and, [u, v]⟩ : Gate)]).length
      simp
    · intro x
      change wireVal n ⟨gs ++ [(⟨GateOp.and, [u, v]⟩ : Gate)], 0⟩ (n + gs.length) x = _
      rw [wireVal_gate ⟨gs ++ [(⟨GateOp.and, [u, v]⟩ : Gate)], 0⟩ x gs.length (by simp)]
      have hgat : gateAt ⟨gs ++ [(⟨GateOp.and, [u, v]⟩ : Gate)], 0⟩ gs.length = ⟨GateOp.and, [u, v]⟩ := by
        rw [gateAt_eq_getElem _ _ (by simp)]; simp
      rw [hgat]
      have hv : v < n + gs.length := hd
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true, ite_eq_left hu, ite_eq_left hv]
      rw [wireVal_append_prefix gs _ x u hu, wireVal_append_prefix gs _ x v hv]
      rfl

private def dUpd (D : ℕ → DWire) (w : ℕ) (d : DWire) : ℕ → DWire :=
  fun r => if r = w then d else D r

private def pushOrInputs (n : ℕ) (dw : DWire) :
    List ℕ → List Gate × (ℕ → DWire) → List Gate × (ℕ → DWire)
  | [], st => st
  | r :: rs, st =>
    let p := dOr n st.1 (st.2 r) dw
    pushOrInputs n dw rs (p.1, dUpd st.2 r p.2)

private lemma pushOrInputs_spec (n : ℕ) (dw : DWire) (rs : List ℕ)
    (gs : List Gate) (D : ℕ → DWire) (hM : Monotone2 ⟨gs, 0⟩)
    (hdw : dOk n gs dw) (hD : ∀ w, dOk n gs (D w)) :
    let res := pushOrInputs n dw rs (gs, D)
    (∃ tail, res.1 = gs ++ tail ∧ tail.length ≤ rs.length) ∧
    Monotone2 ⟨res.1, 0⟩ ∧
    (∀ w, dOk n res.1 (res.2 w)) ∧
    ∀ (x : Fin n → Bool) (w : ℕ),
      dEval n res.1 x (res.2 w) = (dEval n gs x (D w) || (decide (w ∈ rs) && dEval n gs x dw)) := by
  induction rs generalizing gs D with
  | nil =>
    refine ⟨⟨[], by simp [pushOrInputs], by simp⟩, hM, hD, fun x w => by simp [pushOrInputs]⟩
  | cons r rs ih =>
    obtain ⟨⟨t1, ht1, ht1len⟩, hM1, hok1, hev1⟩ := dOr_spec n gs hM (D r) dw (hD r) hdw
    let gs1 := (dOr n gs (D r) dw).1
    let d1 := (dOr n gs (D r) dw).2
    let D1 := dUpd D r d1
    have hdw1 : dOk n gs1 dw := by
      cases dw with
      | zero => trivial
      | one => trivial
      | wire u =>
        change u < n + gs1.length
        dsimp only [gs1]
        rw [ht1, List.length_append]
        have : u < n + gs.length := hdw
        omega
    have hD1 : ∀ w, dOk n gs1 (D1 w) := by
      intro w
      by_cases hw : w = r
      · simp [D1, dUpd, hw]; exact hok1
      · simp only [D1, dUpd, hw, ↓reduceIte]
        cases hDw : D w with
        | zero => trivial
        | one => trivial
        | wire u =>
          change u < n + gs1.length
          dsimp only [gs1]
          rw [ht1, List.length_append]
          have : u < n + gs.length := by simpa [hDw, dOk] using hD w
          omega
    obtain ⟨⟨t2, ht2, ht2len⟩, hM2, hD2, hev2⟩ := ih gs1 D1 hM1 hdw1 hD1
    refine ⟨⟨t1 ++ t2, by
      change (pushOrInputs n dw rs (gs1, D1)).1 = _
      rw [ht2]; dsimp only [gs1]; rw [ht1, List.append_assoc],
      by simp; omega⟩, hM2, hD2, ?_⟩
    intro x w
    change dEval n (pushOrInputs n dw rs (gs1, D1)).1 x ((pushOrInputs n dw rs (gs1, D1)).2 w) = _
    rw [hev2 x w]
    have hdw_eq : dEval n gs1 x dw = dEval n gs x dw := by
      dsimp only [gs1]; rw [ht1]; exact dEval_append n gs t1 x dw hdw
    rw [hdw_eq]
    by_cases hw : w = r
    · subst hw
      have h1 : dEval n gs1 x (D1 w) = (dEval n gs x (D w) || dEval n gs x dw) := by
        simp only [D1, dUpd, ↓reduceIte]; exact hev1 x
      rw [h1]
      cases dEval n gs x (D w) <;> cases dEval n gs x dw <;> cases decide (w ∈ rs) <;> simp
    · have h1 : dEval n gs1 x (D1 w) = dEval n gs x (D w) := by
        simp only [D1, dUpd, hw, ↓reduceIte]
        dsimp only [gs1]; rw [ht1]; exact dEval_append n gs t1 x (D w) (hD w)
      rw [h1]
      simp [hw]

private def sweepStep (n m : ℕ) (C : Circuit) (idx0 : ℕ → ℕ)
    (j : ℕ) (st : List Gate × (ℕ → DWire)) : List Gate × (ℕ → DWire) :=
  if ldVal n m C (n + m + j) = 0 then st
  else
    let dw := st.2 (n + m + j)
    let g := gateAt C j
    if g.op = GateOp.or then
      pushOrInputs n dw g.inputs st
    else
      match g.inputs with
      | [a] =>
        let p := dOr n st.1 (st.2 a) dw
        (p.1, dUpd st.2 a p.2)
      | [a, b] =>
        if ldVal n m C a = 0 then
          let p1 := dAndWire n st.1 (idx0 a) dw
          let p2 := dOr n p1.1 (st.2 b) p1.2
          (p2.1, dUpd st.2 b p2.2)
        else
          let p1 := dAndWire n st.1 (idx0 b) dw
          let p2 := dOr n p1.1 (st.2 a) p1.2
          (p2.1, dUpd st.2 a p2.2)
      | _ => st

private def sweepRun (n m : ℕ) (C : Circuit) (idx0 : ℕ → ℕ) :
    ℕ → List Gate × (ℕ → DWire) → List Gate × (ℕ → DWire)
  | 0, st => st
  | k + 1, st => sweepRun n m C idx0 k (sweepStep n m C idx0 k st)

private lemma sweepRun_spec (n m : ℕ) (C : Circuit) (hM : Monotone2 C)
    (hRB : ReadsBack (n + m) C) (hno : crossSet n m C = ∅)
    (gs0 : List Gate) (idx0 : ℕ → ℕ)
    (hidx : ∀ w < n + m + C.gates.length, ldVal n m C w = 0 →
      idx0 w < n + gs0.length ∧
      ∀ x : Fin n → Bool, wireVal n ⟨gs0, 0⟩ (idx0 w) x =
        wireVal (n + m) C w (Fin.append x (fun _ => false))) :
    ∀ (k : ℕ), k ≤ C.gates.length →
    ∀ (gs : List Gate) (D : ℕ → DWire),
      (∃ ext, gs = gs0 ++ ext) →
      Monotone2 ⟨gs, 0⟩ →
      (∀ w, dOk n gs (D w)) →
      let res := sweepRun n m C idx0 k (gs, D)
      Monotone2 ⟨res.1, 0⟩ ∧
      res.1.length ≤ gs.length + 2 * ((Finset.range k).filter fun j => ldVal n m C (n + m + j) ≠ 0).card ∧
      (∀ w, dOk n res.1 (res.2 w)) ∧
      ∀ (x : Fin n → Bool) (l : Fin m),
        dEval n res.1 x (res.2 (n + l.val)) = true ↔
          ∃ w < n + m + k, dEval n gs x (D w) = true ∧ linVal n m C x l w = true := by
  intro k
  induction k with
  | zero =>
    intro _ gs D _ hMg hD
    refine ⟨hMg, by simp [sweepRun], hD, ?_⟩
    intro x l
    simp only [sweepRun, add_zero]
    constructor
    · intro h
      refine ⟨n + l.val, by omega, h, ?_⟩
      rw [linVal_input n m C x l (n + l.val) (by omega)]
      simp
    · rintro ⟨w, hw, hdw, hlin⟩
      rw [linVal_input n m C x l w hw, decide_eq_true_eq] at hlin
      rwa [← hlin]
  | succ k ih =>
    intro hk gs D ⟨ext, hgs_ext⟩ hMg hD
    have hklen : k < C.gates.length := by omega
    have hfilt : ((Finset.range (k + 1)).filter fun j => ldVal n m C (n + m + j) ≠ 0) =
        if ldVal n m C (n + m + k) ≠ 0 then
          insert k ((Finset.range k).filter fun j => ldVal n m C (n + m + j) ≠ 0)
        else (Finset.range k).filter fun j => ldVal n m C (n + m + j) ≠ 0 := by
      rw [Finset.range_add_one, Finset.filter_insert]
    let st1 := sweepStep n m C idx0 k (gs, D)
    have hstep_props :
        (∃ tail, st1.1 = gs ++ tail ∧ tail.length ≤ if ldVal n m C (n + m + k) = 0 then 0 else 2) ∧
        Monotone2 ⟨st1.1, 0⟩ ∧
        (∀ w, dOk n st1.1 (st1.2 w)) ∧
        ∀ (x : Fin n → Bool) (l : Fin m),
          (∃ w < n + m + k, dEval n st1.1 x (st1.2 w) = true ∧ linVal n m C x l w = true) ↔
          (∃ w < n + m + (k + 1), dEval n gs x (D w) = true ∧ linVal n m C x l w = true) := by
      unfold st1 sweepStep
      by_cases h0 : ldVal n m C (n + m + k) = 0
      · simp only [h0, ↓reduceIte]
        refine ⟨⟨[], by simp, by simp⟩, hMg, hD, ?_⟩
        intro x l
        constructor
        · rintro ⟨w, hw, h1, h2⟩; exact ⟨w, by omega, h1, h2⟩
        · rintro ⟨w, hw, h1, h2⟩
          have hne : w ≠ n + m + k := by
            intro e; subst e
            rw [linVal_zero_of_ld_zero n m C x l (n + m + k) (by omega) h0] at h2
            exact Bool.false_ne_true h2
          exact ⟨w, by omega, h1, h2⟩
      · simp only [h0, ↓reduceIte]
        have hgk_mem : gateAt C k ∈ C.gates := by
          rw [gateAt_eq_getElem C k hklen]; exact List.getElem_mem hklen
        have hhop := (hM (gateAt C k) hgk_mem).1
        have hlen := (hM (gateAt C k) hgk_mem).2
        have hop : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hhop
        have hrb := hRB k hklen
        by_cases hor : (gateAt C k).op = GateOp.or
        · simp only [hor, ↓reduceIte]
          obtain ⟨⟨tail, htail, htlen⟩, hM1, hD1, hev1⟩ :=
            pushOrInputs_spec n (D (n + m + k)) (gateAt C k).inputs gs D hMg (hD _) hD
          refine ⟨⟨tail, htail, htlen.trans hlen⟩, hM1, hD1, ?_⟩
          intro x l
          constructor
          · rintro ⟨w, hw, hdw1, hlinw⟩
            rw [hev1 x w, Bool.or_eq_true] at hdw1
            rcases hdw1 with hdw0 | hhit
            · exact ⟨w, by omega, hdw0, hlinw⟩
            · rw [Bool.and_eq_true, decide_eq_true_eq] at hhit
              refine ⟨n + m + k, by omega, hhit.2, ?_⟩
              rw [linVal_gate n m C x l k hklen, ite_eq_right h0, ite_eq_left hor, List.any_eq_true]
              exact ⟨w, hhit.1, by simp [hw, hlinw]⟩
          · rintro ⟨w, hw, hdw0, hlinw⟩
            by_cases hwk : w = n + m + k
            · subst hwk
              rw [linVal_gate n m C x l k hklen, ite_eq_right h0, ite_eq_left hor, List.any_eq_true] at hlinw
              obtain ⟨r, hrin, hrlin⟩ := hlinw
              have hrlt := hrb r hrin
              simp only [ite_eq_left hrlt] at hrlin
              refine ⟨r, hrlt, ?_, hrlin⟩
              rw [hev1 x r, Bool.or_eq_true]
              exact Or.inr (by simp [hrin, hdw0])
            · refine ⟨w, by omega, ?_, hlinw⟩
              rw [hev1 x w, Bool.or_eq_true]
              exact Or.inl hdw0
        · simp only [hor, ↓reduceIte]
          have hand : (gateAt C k).op = GateOp.and := hop.resolve_right hor
          cases hin : (gateAt C k).inputs with
          | nil =>
            rw [ldVal_gate n m C k hklen, ite_eq_left hand, hin] at h0
            simp at h0
          | cons a rest =>
            cases rest with
            | nil =>
              have ha := hrb a (by rw [hin]; exact List.mem_cons_self)
              obtain ⟨⟨tail, htail, htlen⟩, hM1, hok1, hev1⟩ :=
                dOr_spec n gs hMg (D a) (D (n + m + k)) (hD a) (hD _)
              refine ⟨⟨tail, htail, by omega⟩, hM1, ?_, ?_⟩
              · intro w
                by_cases hwa : w = a
                · simp [dUpd, hwa]; exact hok1
                · simp only [dUpd, hwa, ↓reduceIte]
                  cases hDw : D w with
                  | zero => trivial
                  | one => trivial
                  | wire u =>
                    change u < n + (dOr n gs (D a) (D (n + m + k))).1.length
                    rw [htail, List.length_append]
                    have : u < n + gs.length := by simpa [hDw, dOk] using hD w
                    omega
              · intro x l
                have hEvalUpd (w : ℕ) :
                    dEval n (dOr n gs (D a) (D (n + m + k))).1 x
                      (dUpd D a (dOr n gs (D a) (D (n + m + k))).2 w) =
                    if w = a then (dEval n gs x (D a) || dEval n gs x (D (n + m + k)))
                    else dEval n gs x (D w) := by
                  by_cases hwa : w = a
                  · simp [dUpd, hwa, hev1 x]
                  · simp only [dUpd, hwa, ↓reduceIte]
                    rw [htail]; exact dEval_append n gs tail x (D w) (hD w)
                constructor
                · rintro ⟨w, hw, hdw1, hlinw⟩
                  rw [hEvalUpd w] at hdw1
                  by_cases hwa : w = a
                  · subst hwa
                    simp only [↓reduceIte, Bool.or_eq_true] at hdw1
                    rcases hdw1 with h1 | h2
                    · exact ⟨w, by omega, h1, hlinw⟩
                    · refine ⟨n + m + k, by omega, h2, ?_⟩
                      rw [linVal_gate n m C x l k hklen, ite_eq_right h0, ite_eq_right hor, hin]
                      simp [ha, hlinw]
                  · simp only [hwa, ↓reduceIte] at hdw1
                    exact ⟨w, by omega, hdw1, hlinw⟩
                · rintro ⟨w, hw, hdw0, hlinw⟩
                  by_cases hwk : w = n + m + k
                  · subst hwk
                    rw [linVal_gate n m C x l k hklen, ite_eq_right h0, ite_eq_right hor, hin] at hlinw
                    simp only [ite_eq_left ha] at hlinw
                    refine ⟨a, ha, ?_, hlinw⟩
                    rw [hEvalUpd a]; simp [hdw0]
                  · refine ⟨w, by omega, ?_, hlinw⟩
                    rw [hEvalUpd w]
                    by_cases hwa : w = a
                    · subst hwa; simp [hdw0]
                    · simp [hwa, hdw0]
            | cons b rest2 =>
              have hrest2 : rest2 = [] := by
                rw [hin] at hlen
                cases rest2 with
                | nil => rfl
                | cons _ _ => simp at hlen
              subst hrest2
              have ha := hrb a (by rw [hin]; exact List.mem_cons_self)
              have hb := hrb b (by rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self)
              have hzero : ldVal n m C a = 0 ∨ ldVal n m C b = 0 := by
                by_contra hpos
                have : k ∈ crossSet n m C := by
                  refine ⟨hklen, hand, by rw [hin]; rfl, ?_⟩
                  intro r hr; rw [hin] at hr
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                  rcases hr with rfl | rfl <;> omega
                rw [hno] at this; exact this
              have hand_case (p q : ℕ) (hp : p < n + m + k) (hq : q < n + m + k)
                  (hp0 : ldVal n m C p = 0)
                  (hlin_eq : ∀ x l, linVal n m C x l (n + m + k) =
                    (wireVal (n + m) C p (Fin.append x (fun _ => false)) && linVal n m C x l q)) :
                  let p1 := dAndWire n gs (idx0 p) (D (n + m + k))
                  let p2 := dOr n p1.1 (D q) p1.2
                  (∃ tail, p2.1 = gs ++ tail ∧ tail.length ≤ 2) ∧
                  Monotone2 ⟨p2.1, 0⟩ ∧
                  (∀ w, dOk n p2.1 (dUpd D q p2.2 w)) ∧
                  ∀ (x : Fin n → Bool) (l : Fin m),
                    (∃ w < n + m + k, dEval n p2.1 x (dUpd D q p2.2 w) = true ∧ linVal n m C x l w = true) ↔
                    (∃ w < n + m + (k + 1), dEval n gs x (D w) = true ∧ linVal n m C x l w = true) := by
                obtain ⟨hidx_bd, hidx_ev⟩ := hidx p (by omega) hp0
                have hidx_gs : idx0 p < n + gs.length := by rw [hgs_ext, List.length_append]; omega
                obtain ⟨⟨t1, ht1, ht1len⟩, hM1, hok1, hev1⟩ :=
                  dAndWire_spec n gs hMg (idx0 p) (D (n + m + k)) hidx_gs (hD _)
                have hDq1 : dOk n (dAndWire n gs (idx0 p) (D (n + m + k))).1 (D q) := by
                  cases hDq : D q with
                  | zero => trivial
                  | one => trivial
                  | wire u =>
                    change u < n + (dAndWire n gs (idx0 p) (D (n + m + k))).1.length
                    rw [ht1, List.length_append]
                    have : u < n + gs.length := by simpa [hDq, dOk] using hD q
                    omega
                obtain ⟨⟨t2, ht2, ht2len⟩, hM2, hok2, hev2⟩ :=
                  dOr_spec n _ hM1 (D q) _ hDq1 hok1
                let p1 := dAndWire n gs (idx0 p) (D (n + m + k))
                let p2 := dOr n p1.1 (D q) p1.2
                have htail_all : p2.1 = gs ++ (t1 ++ t2) := by
                  change p2.1 = _; rw [ht2, ht1, List.append_assoc]
                refine ⟨⟨t1 ++ t2, htail_all, by simp; omega⟩, hM2, ?_, ?_⟩
                · intro w
                  by_cases hwq : w = q
                  · simp [dUpd, hwq]; exact hok2
                  · simp only [dUpd, hwq, ↓reduceIte]
                    cases hDw : D w with
                    | zero => trivial
                    | one => trivial
                    | wire u =>
                      change u < n + p2.1.length
                      rw [htail_all, List.length_append]
                      have : u < n + gs.length := by simpa [hDw, dOk] using hD w
                      omega
                · intro x l
                  have hp_gs : wireVal n ⟨gs, 0⟩ (idx0 p) x =
                      wireVal (n + m) C p (Fin.append x (fun _ => false)) := by
                    rw [hgs_ext, wireVal_append_prefix gs0 ext x (idx0 p) hidx_bd, hidx_ev x]
                  have hEvalUpd (w : ℕ) :
                      dEval n p2.1 x (dUpd D q p2.2 w) =
                      if w = q then
                        (dEval n gs x (D q) ||
                          (wireVal (n + m) C p (Fin.append x (fun _ => false)) &&
                            dEval n gs x (D (n + m + k))))
                      else dEval n gs x (D w) := by
                    by_cases hwq : w = q
                    · simp only [dUpd, hwq, ↓reduceIte]
                      rw [hev2 x, hev1 x, hp_gs]
                      have : dEval n p1.1 x (D q) = dEval n gs x (D q) := by
                        rw [ht1]; exact dEval_append n gs t1 x (D q) (hD q)
                      rw [this]
                    · simp only [dUpd, hwq, ↓reduceIte]
                      rw [htail_all]; exact dEval_append n gs (t1 ++ t2) x (D w) (hD w)
                  constructor
                  · rintro ⟨w, hw, hdw1, hlinw⟩
                    rw [hEvalUpd w] at hdw1
                    by_cases hwq : w = q
                    · subst hwq
                      simp only [↓reduceIte, Bool.or_eq_true, Bool.and_eq_true] at hdw1
                      rcases hdw1 with h1 | ⟨hpv, hdk⟩
                      · exact ⟨w, by omega, h1, hlinw⟩
                      · exact ⟨n + m + k, by omega, hdk, by rw [hlin_eq x l, hpv, hlinw]; rfl⟩
                    · simp only [hwq, ↓reduceIte] at hdw1
                      exact ⟨w, by omega, hdw1, hlinw⟩
                  · rintro ⟨w, hw, hdw0, hlinw⟩
                    by_cases hwk : w = n + m + k
                    · subst hwk
                      rw [hlin_eq x l, Bool.and_eq_true] at hlinw
                      refine ⟨q, hq, ?_, hlinw.2⟩
                      rw [hEvalUpd q]; simp [hlinw.1, hdw0]
                    · refine ⟨w, by omega, ?_, hlinw⟩
                      rw [hEvalUpd w]
                      by_cases hwq : w = q
                      · subst hwq; simp [hdw0]
                      · simp [hwq, hdw0]
              by_cases ha0 : ldVal n m C a = 0
              · simp only [ha0, ↓reduceIte]
                exact hand_case a b ha hb ha0 (fun x l => by
                  rw [linVal_gate n m C x l k hklen, ite_eq_right h0, ite_eq_right hor, hin]
                  simp [ha0, hb])
              · have hb0 : ldVal n m C b = 0 := hzero.resolve_left ha0
                simp only [ha0, ↓reduceIte]
                exact hand_case b a hb ha hb0 (fun x l => by
                  rw [linVal_gate n m C x l k hklen, ite_eq_right h0, ite_eq_right hor, hin]
                  simp [ha0, ha, Bool.and_comm])
    obtain ⟨⟨tail, htail, htlen⟩, hM1, hD1, hequiv1⟩ := hstep_props
    have hst1_ext : ∃ ext1, st1.1 = gs0 ++ ext1 := ⟨ext ++ tail, by rw [htail, hgs_ext, List.append_assoc]⟩
    obtain ⟨hMres, hlenres, hDres, hequivres⟩ := ih (by omega) st1.1 st1.2 hst1_ext hM1 hD1
    refine ⟨hMres, ?_, hDres, ?_⟩
    · change (sweepRun n m C idx0 k (st1.1, st1.2)).1.length ≤ _
      have hst1_len : st1.1.length = gs.length + tail.length := by rw [htail, List.length_append]
      rw [hfilt]
      by_cases h0 : ldVal n m C (n + m + k) = 0
      · have hne : ¬(ldVal n m C (n + m + k) ≠ 0) := fun h => h h0
        simp only [h0, ↓reduceIte] at htlen
        simp only [hne, ↓reduceIte]
        omega
      · have hne : ldVal n m C (n + m + k) ≠ 0 := h0
        rw [ite_eq_right h0] at htlen
        rw [ite_eq_left hne, Finset.card_insert_of_notMem (by simp)]
        omega
    · intro x l
      exact (hequivres x l).trans (hequiv1 x l)

private lemma deg1_linPart_bound {n m : ℕ} (L : Fin m → Finset (Fin n))
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1)
    (C : Circuit) (hM : Monotone2 C) (hRB : ReadsBack (n + m) C) (hno : crossSet n m C = ∅)
    (outW : ℕ) (hout : outW < n + m + C.gates.length)
    (G : Finset (Fin m))
    (hsound : ∀ l ∈ G, linVal n m C (fun p => decide (p ∉ L l)) l outW = false) :
    (Finset.univ.filter fun e : Fin n × Fin m =>
      e.2 ∈ G ∧ e.1 ∈ L e.2 ∧ linVal n m C (fun v => decide (v = e.1)) e.2 outW = true).card ≤
      2 * C.gates.length + G.card := by
  classical
  obtain ⟨hM0, hlen0, hev0⟩ := ptCopy_props n m C hM hRB C.gates.length le_rfl
  let gs0 := (ptCopy n m C C.gates.length).1
  let idx0 := (ptCopy n m C C.gates.length).2
  let Dinit : ℕ → DWire := fun w => if w = outW then DWire.one else DWire.zero
  have hDinit : ∀ w, dOk n gs0 (Dinit w) := fun w => by
    by_cases h : w = outW <;> simp [Dinit, h, dOk]
  obtain ⟨hMres, hlenres, hDres, hequiv⟩ :=
    sweepRun_spec n m C hM hRB hno gs0 idx0 hev0 C.gates.length le_rfl gs0 Dinit
      ⟨[], by simp⟩ hM0 hDinit
  let res := sweepRun n m C idx0 C.gates.length (gs0, Dinit)
  have hev_lin (x : Fin n → Bool) (l : Fin m) :
      dEval n res.1 x (res.2 (n + l.val)) = linVal n m C x l outW := by
    apply Bool.eq_iff_iff.mpr
    rw [hequiv x l]
    constructor
    · rintro ⟨w, _, hdw, hlin⟩
      by_cases hw : w = outW
      · rwa [← hw]
      · simp [Dinit, hw, dEval] at hdw
    · intro hlin
      exact ⟨outW, hout, by simp [Dinit, dEval], hlin⟩
  let Dcirc : Circuit := ⟨res.1, 0⟩
  let outWire (l : Fin m) : ℕ :=
    match res.2 (n + l.val) with
    | DWire.wire w => w
    | _ => n + res.1.length
  have hout_eq : ∀ l ∈ G, ∀ x : Fin n → Bool,
      wireVal n Dcirc (outWire l) x = linVal n m C x l outW := by
    intro l hl x
    have h1 := hev_lin x l
    have h2 := hev_lin (fun p => decide (p ∉ L l)) l
    rw [hsound l hl] at h2
    cases hresl : res.2 (n + l.val) with
    | zero =>
      simp only [outWire, hresl]
      rw [wireVal_oob Dcirc x _ le_rfl]
      rw [hresl] at h1
      simp only [dEval] at h1
      exact h1
    | one =>
      rw [hresl] at h2
      simp only [dEval] at h2
      exact absurd h2 (by decide)
    | wire w =>
      simp only [outWire, hresl]
      rw [hresl] at h1
      exact h1
  have hbound := point_bound_multi L hL Dcirc hMres G outWire (fun l hl => by
    rw [hout_eq l hl]; exact hsound l hl)
  have hcard_eq : (Finset.univ.filter fun e : Fin n × Fin m =>
      e.2 ∈ G ∧ e.1 ∈ L e.2 ∧ linVal n m C (fun v => decide (v = e.1)) e.2 outW = true) =
      (Finset.univ.filter fun e : Fin n × Fin m =>
        e.2 ∈ G ∧ e.1 ∈ L e.2 ∧ wireVal n Dcirc (outWire e.2) (fun v => decide (v = e.1)) = true) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, by rw [hout_eq e.2 h1]; exact h3⟩
    · exact ⟨h1, h2, by rw [← hout_eq e.2 h1]; exact h3⟩
  rw [hcard_eq]
  have hpart : ((Finset.range C.gates.length).filter fun j => ldVal n m C (n + m + j) = 0).card +
      ((Finset.range C.gates.length).filter fun j => ldVal n m C (n + m + j) ≠ 0).card =
      C.gates.length := by
    have := Finset.card_filter_add_card_filter_not
      (s := Finset.range C.gates.length) (p := fun j => ldVal n m C (n + m + j) = 0)
    simpa only [Finset.card_range] using this
  have hres_len : Dcirc.gates.length ≤ 2 * C.gates.length := by
    change res.1.length ≤ _
    change res.1.length ≤ gs0.length + 2 * ((Finset.range C.gates.length).filter fun j => ldVal n m C (n + m + j) ≠ 0).card at hlenres
    change gs0.length = _ at hlen0
    omega
  omega

-- Zero-line point-only circuit: replace line inputs [n, n+m) by out-of-bounds wire
private def zeroLineCircuit (n m : ℕ) (C : Circuit) (outW : ℕ) : Circuit :=
  let oob := n + C.gates.length
  let remap (w : ℕ) : ℕ := if w < n then w else if w < n + m then oob else w - m
  ⟨C.gates.map fun g => ⟨g.op, g.inputs.map remap⟩, remap outW⟩

private lemma zeroLineCircuit_props (n m : ℕ) (C : Circuit) (hM : Monotone2 C)
    (hRB : ReadsBack (n + m) C) (outW : ℕ) :
    let D := zeroLineCircuit n m C outW
    Monotone2 D ∧ D.gates.length = C.gates.length ∧
    ∀ (x : Fin n → Bool) (w : ℕ), w < n + m + C.gates.length →
      wireVal n D (if w < n then w else if w < n + m then n + C.gates.length else w - m) x =
        wireVal (n + m) C w (Fin.append x (fun _ => false)) := by
  let oob := n + C.gates.length
  let remap (w : ℕ) : ℕ := if w < n then w else if w < n + m then oob else w - m
  let D := zeroLineCircuit n m C outW
  have hMD : Monotone2 D := by
    intro g hg
    simp only [D, zeroLineCircuit, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact ⟨(hM g0 hg0).1, by simp [(hM g0 hg0).2]⟩
  have hlenD : D.gates.length = C.gates.length := by simp [D, zeroLineCircuit]
  refine ⟨hMD, hlenD, ?_⟩
  intro x w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hn : w < n
    · simp only [ite_eq_left hn]
      rw [wireVal_input D x ⟨w, hn⟩, wireVal_input C _ ⟨w, by omega⟩]
      have : (⟨w, by omega⟩ : Fin (n + m)) = Fin.castAdd m ⟨w, hn⟩ := by ext; rfl
      rw [this, Fin.append_left]
    · by_cases hnm : w < n + m
      · simp only [ite_eq_right hn, ite_eq_left hnm]
        rw [wireVal_oob D x oob (by omega), wireVal_input C _ ⟨w, hnm⟩]
        have : (⟨w, hnm⟩ : Fin (n + m)) = Fin.natAdd n ⟨w - n, by omega⟩ := by ext; simp; omega
        rw [this, Fin.append_right]
      · simp only [ite_eq_right hn, ite_eq_right hnm]
        let j := w - (n + m)
        have hj : j < C.gates.length := by omega
        have hwj : w = n + m + j := by omega
        have hwm : w - m = n + j := by omega
        rw [hwm, hwj, wireVal_gate D x j (by omega), wireVal_gate C _ j hj]
        have hgat : gateAt D j = ⟨(gateAt C j).op, (gateAt C j).inputs.map remap⟩ := by
          rw [gateAt_eq_getElem D j (by omega), gateAt_eq_getElem C j hj]
          simp [D, zeroLineCircuit, remap, oob]
        rw [hgat, List.map_map]
        congr 1
        apply List.map_congr_left
        intro r hr
        have hrlt := hRB j hj r hr
        simp only [Function.comp_apply, ite_eq_left hrlt]
        by_cases hrn : r < n
        · have hrm : remap r = r := by simp [remap, hrn]
          rw [hrm, ite_eq_left (by omega)]
          simpa [hrn] using ih r (by omega) (by omega)
        · by_cases hrnm : r < n + m
          · have hrm : remap r = oob := by simp [remap, hrn, hrnm]
            rw [hrm, ite_eq_right (by omega)]
            have h1 := ih r (by omega) (by omega)
            simp only [hrn, hrnm, ↓reduceIte] at h1
            rw [← h1, wireVal_oob D x oob (by omega)]
          · have hrm : remap r = r - m := by simp [remap, hrn, hrnm]
            rw [hrm, ite_eq_left (by omega)]
            simpa [hrn, hrnm] using ih r (by omega) (by omega)

private lemma deg1_full_bound {n m : ℕ} (L : Fin m → Finset (Fin n))
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1)
    (C : Circuit) (hM : Monotone2 C) (hRB : ReadsBack (n + m) C) (hno : crossSet n m C = ∅)
    (outW : ℕ) (hout : outW < n + m + C.gates.length)
    (G : Finset (Fin m))
    (hsound : ∀ l ∈ G, wireVal (n + m) C outW
      (Fin.append (fun p => decide (p ∉ L l)) (fun l' => decide (l' = l))) = false) :
    (Finset.univ.filter fun e : Fin n × Fin m =>
      e.2 ∈ G ∧ e.1 ∈ L e.2 ∧
      wireVal (n + m) C outW (Fin.append (fun v => decide (v = e.1)) (fun l' => decide (l' = e.2))) = true).card ≤
      3 * C.gates.length + 2 * G.card + 1 := by
  classical
  have hlin_sound : ∀ l ∈ G, linVal n m C (fun p => decide (p ∉ L l)) l outW = false := by
    intro l hl
    have hs := hsound l hl
    rw [wireVal_single_line_decomp n m C hM hRB hno _ l outW hout, Bool.or_eq_false_iff] at hs
    exact hs.2
  have h0_sound : ∀ l ∈ G, wireVal (n + m) C outW
      (Fin.append (fun p => decide (p ∉ L l)) (fun _ => false)) = false := by
    intro l hl
    have hs := hsound l hl
    rw [wireVal_single_line_decomp n m C hM hRB hno _ l outW hout, Bool.or_eq_false_iff] at hs
    exact hs.1
  let E0 := Finset.univ.filter fun e : Fin n × Fin m =>
    e.2 ∈ G ∧ e.1 ∈ L e.2 ∧ wireVal (n + m) C outW (Fin.append (fun v => decide (v = e.1)) (fun _ => false)) = true
  let E1 := Finset.univ.filter fun e : Fin n × Fin m =>
    e.2 ∈ G ∧ e.1 ∈ L e.2 ∧ linVal n m C (fun v => decide (v = e.1)) e.2 outW = true
  have hsub : (Finset.univ.filter fun e : Fin n × Fin m =>
      e.2 ∈ G ∧ e.1 ∈ L e.2 ∧
      wireVal (n + m) C outW (Fin.append (fun v => decide (v = e.1)) (fun l' => decide (l' = e.2))) = true) ⊆
      E0 ∪ E1 := by
    intro e he
    obtain ⟨hG, hLmem, hv⟩ := (Finset.mem_filter.mp he).2
    rw [wireVal_single_line_decomp n m C hM hRB hno _ e.2 outW hout, Bool.or_eq_true] at hv
    rcases hv with h0 | h1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG, hLmem, h0⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG, hLmem, h1⟩)
  have hE1 : E1.card ≤ 2 * C.gates.length + G.card :=
    deg1_linPart_bound L hL C hM hRB hno outW hout G hlin_sound
  let P0 : Finset (Fin n) := Finset.univ.filter fun p =>
    wireVal (n + m) C outW (Fin.append (fun v => decide (v = p)) (fun _ => false)) = true
  have hP0_sub : ∀ l ∈ G, P0 ⊆ L l := by
    intro l hl p hp
    have hvp := (Finset.mem_filter.mp hp).2
    by_contra hnot
    have htrue := wireVal_mono C hM
      (Fin.append (fun v => decide (v = p)) (fun _ => false))
      (Fin.append (fun v => decide (v ∉ L l)) (fun _ => false))
      (fun w hw => by
        refine Fin.addCases (fun i hi => ?_) (fun j hj => ?_) w hw
        · simp only [Fin.append_left, decide_eq_true_eq] at hi ⊢; subst hi; exact hnot
        · simp at hj) outW hvp
    rw [h0_sound l hl] at htrue
    exact Bool.false_ne_true htrue
  have hE0_sub : E0 ⊆ P0 ×ˢ G := by
    intro e he
    obtain ⟨hG, _, hv⟩ := (Finset.mem_filter.mp he).2
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, hG⟩
  have hE0 : E0.card ≤ C.gates.length + G.card + 1 := by
    by_cases hP1 : P0.card ≤ 1
    · have h1 := Finset.card_le_card hE0_sub
      rw [Finset.card_product] at h1
      have : P0.card * G.card ≤ 1 * G.card := Nat.mul_le_mul_right G.card hP1
      omega
    · have hP2 : 2 ≤ P0.card := by omega
      have hG1 : G.card ≤ 1 := by
        by_contra hG2
        obtain ⟨l1, hl1, l2, hl2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < G.card)
        have hsub2 : P0 ⊆ L l1 ∩ L l2 := Finset.subset_inter (hP0_sub l1 hl1) (hP0_sub l2 hl2)
        have := Finset.card_le_card hsub2
        have := hL l1 l2 hne
        omega
      by_cases hG0 : G = ∅
      · have : E0 = ∅ := by
          ext e; simp [E0, hG0]
        rw [this]; simp
      · obtain ⟨l0, hl0⟩ := Finset.nonempty_iff_ne_empty.mpr hG0
        obtain ⟨hMD, hlenD, hevD⟩ := zeroLineCircuit_props n m C hM hRB outW
        let D := zeroLineCircuit n m C outW
        let oD := if outW < n then outW else if outW < n + m then n + C.gates.length else outW - m
        have hDsound : wireVal n D oD (fun v => decide (v ∉ L l0)) = false := by
          rw [hevD _ outW hout]; exact h0_sound l0 hl0
        have hP0_eq : P0 = ptSupp D oD := by
          ext p
          simp only [P0, ptSupp, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hevD _ outW hout]
        have hP0_card : P0.card ≤ C.gates.length + 1 := by
          rw [hP0_eq, ← hlenD]
          exact point_bound_single D hMD (L l0) oD hDsound
        have h1 := Finset.card_le_card hE0_sub
        rw [Finset.card_product] at h1
        have : P0.card * G.card ≤ P0.card * 1 := Nat.mul_le_mul_left P0.card hG1
        omega
  have htot := (Finset.card_le_card hsub).trans (Finset.card_union_le E0 E1)
  omega

/-! ### 4. Cross-AND elimination circuit C_B -/

private def orTree (n m : ℕ) : List (Fin m) → List Gate
  | [] => []
  | l :: ls =>
    let pre := orTree n m ls
    match pre with
    | [] => [⟨GateOp.or, [n + l.val]⟩]
    | _ => pre ++ [⟨GateOp.or, [n + m + pre.length - 1, n + l.val]⟩]

private lemma orTree_length (n m : ℕ) (ls : List (Fin m)) :
    (orTree n m ls).length = ls.length := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    unfold orTree
    cases h : orTree n m ls with
    | nil =>
      rw [h] at ih; simp at ih; simp [ih]
    | cons g gs =>
      rw [h] at ih; simp at ih; simp [ih]

private lemma orTree_props (n m : ℕ) (ls : List (Fin m)) :
    Monotone2 ⟨orTree n m ls, 0⟩ ∧
    ReadsBack (n + m) ⟨orTree n m ls, 0⟩ ∧
    (∀ j < (orTree n m ls).length, (gateAt ⟨orTree n m ls, 0⟩ j).op = GateOp.or) ∧
    (∀ w < n + m + (orTree n m ls).length, ldVal n m ⟨orTree n m ls, 0⟩ w ≤ 1) ∧
    (ls ≠ [] → ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      wireVal (n + m) ⟨orTree n m ls, 0⟩ (n + m + (orTree n m ls).length - 1) (Fin.append x y) =
        decide (∃ l ∈ ls, y l = true)) := by
  induction ls with
  | nil =>
    refine ⟨(by intro g hg; cases hg), (by intro j hj; simp [orTree] at hj),
      (by intro j hj; simp [orTree] at hj), ?_, fun h => absurd rfl h⟩
    intro w hw
    by_cases hn : w < n
    · rw [ldVal_input_pt n m _ w hn]; omega
    · rw [ldVal_input_ln n m _ w (by omega) (by simpa [orTree] using hw)]
  | cons l ls ih =>
    obtain ⟨hM, hRB, hor, hld, hev⟩ := ih
    cases hpre : orTree n m ls with
    | nil =>
      have hls : ls = [] := by
        have := orTree_length n m ls; rw [hpre] at this; exact List.eq_nil_of_length_eq_zero this.symm
      subst hls
      have htree : orTree n m [l] = [⟨GateOp.or, [n + l.val]⟩] := rfl
      rw [htree]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact ⟨by simp, by simp⟩
      · intro j hj i hi
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0
        simp only [gateAt, List.getD_cons_zero, List.mem_singleton] at hi
        omega
      · intro j hj
        have hj0 : j = 0 := by simp at hj; omega
        subst hj0; rfl
      · intro w hw
        by_cases hn : w < n
        · rw [ldVal_input_pt n m _ w hn]; omega
        · by_cases hnm : w < n + m
          · rw [ldVal_input_ln n m _ w (by omega) hnm]
          · have hw0 : w = n + m + 0 := by simp at hw; omega
            rw [hw0, ldVal_gate n m _ 0 (by simp)]
            have hln : n + l.val < n + m + 0 := by omega
            simp [gateAt, hln, ldVal_input_ln n m _ (n + l.val) (by omega) (by omega)]
      · intro _ x y
        have hidx : n + m + 1 - 1 = n + m + 0 := by omega
        simp only [List.length_singleton, hidx]
        rw [wireVal_gate _ _ 0 (by simp)]
        have hln : n + l.val < n + m + 0 := by omega
        simp only [gateAt, List.getD_cons_zero, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false, ite_eq_left hln]
        have hfin : (⟨n + l.val, by omega⟩ : Fin (n + m)) = Fin.natAdd n l := by ext; rfl
        rw [wireVal_input _ _ ⟨n + l.val, by omega⟩, hfin, Fin.append_right]
        simp
    | cons g0 gs0 =>
      let pre := g0 :: gs0
      have hls_ne : ls ≠ [] := by
        intro h; rw [h] at hpre; simp [orTree] at hpre
      have htree : orTree n m (l :: ls) = pre ++ [⟨GateOp.or, [n + m + pre.length - 1, n + l.val]⟩] := by
        change (match orTree n m ls with | [] => _ | _ => _) = _
        rw [hpre]
      rw [htree]
      rw [hpre] at hM hRB hor hld hev
      let lastG : Gate := ⟨GateOp.or, [n + m + pre.length - 1, n + l.val]⟩
      have hpre_pos : 0 < pre.length := by simp [pre]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hM g hg
        · exact ⟨by simp, by simp⟩
      · intro j hj i hi
        simp only [List.length_append, List.length_singleton] at hj
        by_cases hjp : j < pre.length
        · have hgat : gateAt ⟨pre ++ [lastG], 0⟩ j = gateAt ⟨pre, 0⟩ j := by
            rw [gateAt_eq_getElem _ j (by simp; omega), gateAt_eq_getElem _ j hjp,
              List.getElem_append_left hjp]
          rw [hgat] at hi
          exact hRB j hjp i hi
        · have hjeq : j = pre.length := by omega
          subst hjeq
          have hgat : gateAt ⟨pre ++ [lastG], 0⟩ pre.length = lastG := by
            rw [gateAt_eq_getElem _ _ (by simp)]; simp
          rw [hgat] at hi
          simp only [lastG, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
      · intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        by_cases hjp : j < pre.length
        · rw [gateAt_eq_getElem _ j (by simp; omega), List.getElem_append_left hjp]
          have := hor j hjp; rwa [gateAt_eq_getElem _ j hjp] at this
        · have hjeq : j = pre.length := by omega
          subst hjeq
          rw [gateAt_eq_getElem _ _ (by simp)]; simp [lastG]
      · intro w hw
        simp only [List.length_append, List.length_singleton] at hw
        by_cases hwp : w < n + m + pre.length
        · have heq := ldVal_take n m ⟨pre ++ [lastG], 0⟩ pre.length w (by simp; omega)
          have htake : (pre ++ [lastG]).take pre.length = pre := by simp
          rw [htake] at heq
          rw [← heq]
          exact hld w hwp
        · have hweq : w = n + m + pre.length := by omega
          rw [hweq, ldVal_gate n m ⟨pre ++ [lastG], 0⟩ pre.length (by simp)]
          have hgat : gateAt ⟨pre ++ [lastG], 0⟩ pre.length = lastG := by
            rw [gateAt_eq_getElem _ _ (by simp)]; simp
          rw [hgat]
          have h1 : n + m + pre.length - 1 < n + m + pre.length := by omega
          have h2 : n + l.val < n + m + pre.length := by omega
          have hnor : lastG.op ≠ GateOp.and := by simp [lastG]
          rw [ite_eq_right hnor]
          simp only [lastG, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            ite_eq_left h1, ite_eq_left h2, max_le_iff]
          have hld1 : ldVal n m ⟨pre ++ [lastG], 0⟩ (n + m + pre.length - 1) ≤ 1 := by
            have heq := ldVal_take n m ⟨pre ++ [lastG], 0⟩ pre.length (n + m + pre.length - 1) (by simp; omega)
            have htake : (pre ++ [lastG]).take pre.length = pre := by simp
            rw [htake] at heq; rw [← heq]
            exact hld _ (by omega)
          have hld2 : ldVal n m ⟨pre ++ [lastG], 0⟩ (n + l.val) ≤ 1 := by
            rw [ldVal_input_ln n m _ (n + l.val) (by omega) (by omega)]
          exact ⟨hld1, hld2, Nat.zero_le 1⟩
      · intro _ x y
        have hidx : n + m + (pre ++ [lastG]).length - 1 = n + m + pre.length := by simp
        rw [hidx, wireVal_gate ⟨pre ++ [lastG], 0⟩ _ pre.length (by simp)]
        have hgat : gateAt ⟨pre ++ [lastG], 0⟩ pre.length = lastG := by
          rw [gateAt_eq_getElem _ _ (by simp)]; simp
        rw [hgat]
        have h1 : n + m + pre.length - 1 < n + m + pre.length := by omega
        have h2 : n + l.val < n + m + pre.length := by omega
        simp only [lastG, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, ite_eq_left h1, ite_eq_left h2]
        rw [wireVal_append_prefix pre [lastG] _ (n + m + pre.length - 1) (by omega),
          hev hls_ne x y]
        have hfin : (⟨n + l.val, by omega⟩ : Fin (n + m)) = Fin.natAdd n l := by ext; rfl
        rw [wireVal_input _ _ ⟨n + l.val, by omega⟩, hfin, Fin.append_right]
        apply Bool.eq_iff_iff.mpr
        simp [or_comm]

private def shiftWire (N d w : ℕ) : ℕ :=
  if w < N then w else w + d

private def buildCB (n m : ℕ) (C : Circuit) (j1 : ℕ) (Blist : List (Fin m)) : Circuit :=
  let tree := orTree n m Blist
  let d := tree.length
  let replG : Gate := if d = 0 then ⟨GateOp.or, []⟩ else ⟨GateOp.or, [n + m + d - 1]⟩
  let shifted := (C.gates.map fun g => ⟨g.op, g.inputs.map (shiftWire (n + m) d)⟩).set j1 replG
  ⟨tree ++ shifted, shiftWire (n + m) d C.output⟩

private lemma buildCB_basic (n m : ℕ) (C : Circuit) (hM : Monotone2 C)
    (hRB : ReadsBack (n + m) C) (j1 : ℕ) (hj1_cross : j1 ∈ crossSet n m C)
    (Blist : List (Fin m)) (hBlen : Blist.length ≤ m) :
    let CB := buildCB n m C j1 Blist
    let d := (orTree n m Blist).length
    Monotone2 CB ∧ ReadsBack (n + m) CB ∧ CB.size ≤ C.size + m ∧
    (∀ j' ∈ crossSet n m CB, d ≤ j' ∧ j' - d ∈ crossSet n m C ∧ j' - d ≠ j1) := by
  have hj1 : j1 < C.gates.length := hj1_cross.1
  let tree := orTree n m Blist
  let d := tree.length
  let replG : Gate := if d = 0 then (⟨GateOp.or, []⟩ : Gate) else (⟨GateOp.or, [n + m + d - 1]⟩ : Gate)
  let mapped := C.gates.map fun g => (⟨g.op, g.inputs.map (shiftWire (n + m) d)⟩ : Gate)
  let shifted := mapped.set j1 replG
  let CB := buildCB n m C j1 Blist
  obtain ⟨hMt, hRBt, hort, hldt, _⟩ := orTree_props n m Blist
  have hd_eq : d = Blist.length := orTree_length n m Blist
  have hsh_len : shifted.length = C.gates.length := by simp [shifted, mapped]
  have hCBlen : CB.gates.length = d + C.gates.length := by simp [CB, buildCB, d, tree]
  have hrepl_M : replG.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ replG.inputs.length ≤ 2 := by
    by_cases hd0 : d = 0 <;> simp [replG, hd0]
  have hMCB : Monotone2 CB := by
    intro g hg
    simp only [CB, buildCB, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hMt g hg
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      by_cases hij : i = j1
      · subst hij
        rw [show (mapped.set i replG)[i] = replG from by simp]
        exact hrepl_M
      · rw [List.getElem_set_ne (Ne.symm hij)]
        simp only [mapped, List.getElem_map]
        have horig := hM C.gates[i] (List.getElem_mem _)
        exact ⟨horig.1, by simp [horig.2]⟩
  have hRBCB : ReadsBack (n + m) CB := by
    intro j hj r hr
    by_cases hjd : j < d
    · have hgat : gateAt CB j = gateAt ⟨tree, 0⟩ j := by
        rw [gateAt_eq_getElem CB j hj, gateAt_eq_getElem ⟨tree, 0⟩ j hjd]
        simp [CB, buildCB, tree, List.getElem_append_left hjd]
      rw [hgat] at hr
      exact hRBt j hjd r hr
    · let i := j - d
      have hi : i < C.gates.length := by omega
      have hgat : gateAt CB j = shifted[i] := by
        rw [gateAt_eq_getElem CB j hj]
        simp [CB, buildCB, tree, shifted, mapped, replG, d, i, List.getElem_append_right (Nat.not_lt.mp hjd)]
      rw [hgat] at hr
      by_cases hij : i = j1
      · subst hij
        simp only [shifted, List.getElem_set_self] at hr
        by_cases hd0 : d = 0
        · simp [replG, hd0] at hr
        · simp only [replG, hd0, ↓reduceIte, List.mem_singleton] at hr
          omega
      · simp only [shifted, List.getElem_set_ne (Ne.symm hij), mapped, List.getElem_map,
          List.mem_map] at hr
        obtain ⟨r0, hr0, rfl⟩ := hr
        have hr0lt : r0 < n + m + i := by
          have := hRB i hi r0
          rw [gateAt_eq_getElem C i hi] at this
          exact this hr0
        unfold shiftWire
        by_cases hlt : r0 < n + m <;> simp [hlt] <;> omega
  have hSizeCB : CB.size ≤ C.size + m := by
    simp only [Circuit.size, CB, buildCB, List.length_append, List.length_set, List.length_map]
    rw [show (orTree n m Blist).length = d from rfl]
    omega
  have hld_tree : ∀ w < n + m + d, ldVal n m CB w ≤ 1 := by
    intro w hw
    have heq := ldVal_take n m CB d w (by simp [CB, buildCB, d, tree]; omega)
    have htake : CB.gates.take d = tree := by simp [CB, buildCB, d, tree]
    rw [htake] at heq; rw [← heq]
    exact hldt w hw
  have hj1_ld_ge2 : 2 ≤ ldVal n m C (n + m + j1) := by
    obtain ⟨_, hand, hlen2, hpos⟩ := hj1_cross
    rw [ldVal_gate n m C j1 hj1, ite_eq_left hand]
    cases hin : (gateAt C j1).inputs with
    | nil => simp [hin] at hlen2
    | cons a rest =>
      cases rest with
      | nil => simp [hin] at hlen2
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          have ha := hRB j1 hj1 a (by rw [hin]; exact List.mem_cons_self)
          have hb := hRB j1 hj1 b (by rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self)
          have hpa := hpos a (by rw [hin]; exact List.mem_cons_self)
          have hpb := hpos b (by rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            ite_eq_left ha, ite_eq_left hb]
          omega
        | cons _ _ => simp [hin] at hlen2
  have hld_le_all : ∀ w < n + m + C.gates.length,
      ldVal n m CB (shiftWire (n + m) d w) ≤ ldVal n m C w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hnm : w < n + m
      · simp only [shiftWire, ite_eq_left hnm]
        by_cases hn : w < n
        · rw [ldVal_input_pt n m CB w hn, ldVal_input_pt n m C w hn]
        · rw [ldVal_input_ln n m CB w (by omega) hnm, ldVal_input_ln n m C w (by omega) hnm]
      · simp only [shiftWire, ite_eq_right hnm]
        let i := w - (n + m)
        have hi : i < C.gates.length := by omega
        have hwi : w = n + m + i := by omega
        have hwdi : w + d = n + m + (d + i) := by omega
        rw [hwdi, hwi]
        have hgatCB : gateAt CB (d + i) = shifted[i] := by
          rw [gateAt_eq_getElem CB (d + i) (by omega)]
          simp [CB, buildCB, tree, shifted, mapped, replG, d, List.getElem_append_right]
        by_cases hij : i = j1
        · subst hij
          have hld_repl : ldVal n m CB (n + m + (d + i)) ≤ 1 := by
            rw [ldVal_gate n m CB (d + i) (by omega), hgatCB]
            simp only [shifted, List.getElem_set_self]
            by_cases hd0 : d = 0
            · simp [replG, hd0]
            · simp only [replG, hd0, ↓reduceIte]
              have hlt : n + m + d - 1 < n + m + (d + i) := by omega
              simp only [show (GateOp.or = GateOp.and) ↔ False from by decide, ↓reduceIte,
                List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                ite_eq_left hlt, max_le_iff]
              exact ⟨hld_tree (n + m + d - 1) (by omega), Nat.zero_le 1⟩
          omega
        · have hgatC : shifted[i] = ⟨(gateAt C i).op, (gateAt C i).inputs.map (shiftWire (n + m) d)⟩ := by
            simp only [shifted, List.getElem_set_ne (Ne.symm hij), mapped, List.getElem_map]
            rw [gateAt_eq_getElem C i hi]
          rw [ldVal_gate n m CB (d + i) (by omega), ldVal_gate n m C i hi, hgatCB, hgatC]
          have hstep (r : ℕ) (hr : r ∈ (gateAt C i).inputs) :
              (if shiftWire (n + m) d r < n + m + (d + i) then ldVal n m CB (shiftWire (n + m) d r) else 0) ≤
              (if r < n + m + i then ldVal n m C r else 0) := by
            have hrlt := hRB i hi r hr
            have hshlt : shiftWire (n + m) d r < n + m + (d + i) := by
              unfold shiftWire; by_cases h : r < n + m <;> simp [h] <;> omega
            rw [ite_eq_left hrlt, ite_eq_left hshlt]
            exact ih r (by omega) (by omega)
          by_cases hand : (gateAt C i).op = GateOp.and
          · simp only [hand, ↓reduceIte, List.map_map]
            have hsum_le : ∀ (ks : List ℕ) (f1 f2 : ℕ → ℕ), (∀ r ∈ ks, f1 r ≤ f2 r) →
                (ks.map f1).sum ≤ (ks.map f2).sum := by
              intro ks f1 f2 hf
              induction ks with
              | nil => simp
              | cons a t iht =>
                simp only [List.map_cons, List.sum_cons]
                exact Nat.add_le_add (hf a List.mem_cons_self) (iht fun r hr => hf r (List.mem_cons_of_mem _ hr))
            exact hsum_le (gateAt C i).inputs _ _ hstep
          · simp only [hand, ↓reduceIte, List.map_map]
            have hmax_le : ∀ (ks : List ℕ) (f1 f2 : ℕ → ℕ), (∀ r ∈ ks, f1 r ≤ f2 r) →
                (ks.map f1).foldr max 0 ≤ (ks.map f2).foldr max 0 := by
              intro ks f1 f2 hf
              induction ks with
              | nil => simp
              | cons a t iht =>
                simp only [List.map_cons, List.foldr_cons]
                exact max_le_max (hf a List.mem_cons_self) (iht fun r hr => hf r (List.mem_cons_of_mem _ hr))
            exact hmax_le (gateAt C i).inputs _ _ hstep
  refine ⟨hMCB, hRBCB, hSizeCB, ?_⟩
  intro j' hj'
  obtain ⟨hj'len, hj'and, hj'len2, hj'pos⟩ := hj'
  have hge : d ≤ j' := by
    by_contra hlt
    have hlt' : j' < d := Nat.not_le.mp hlt
    have hgat : gateAt CB j' = gateAt ⟨tree, 0⟩ j' := by
      rw [gateAt_eq_getElem CB j' hj'len, gateAt_eq_getElem ⟨tree, 0⟩ j' hlt']
      simp [CB, buildCB, tree, List.getElem_append_left hlt']
    have := hort j' hlt'
    rw [← hgat, hj'and] at this
    exact absurd this (by decide)
  let i := j' - d
  change j' < CB.gates.length at hj'len
  have hi : i < C.gates.length := by omega
  have hgatCB : gateAt CB j' = shifted[i] := by
    rw [gateAt_eq_getElem CB j' hj'len]
    simp [CB, buildCB, tree, shifted, mapped, replG, d, i, List.getElem_append_right hge]
  have hne : i ≠ j1 := by
    intro heq; subst heq
    rw [hgatCB] at hj'and
    simp only [shifted, List.getElem_set_self] at hj'and
    by_cases hd0 : d = 0 <;> simp [replG, hd0] at hj'and
  have hgatC : shifted[i] = ⟨(gateAt C i).op, (gateAt C i).inputs.map (shiftWire (n + m) d)⟩ := by
    simp only [shifted, List.getElem_set_ne (Ne.symm hne), mapped, List.getElem_map]
    rw [gateAt_eq_getElem C i hi]
  refine ⟨hge, ?_, hne⟩
  rw [hgatCB, hgatC] at hj'and hj'len2 hj'pos
  refine ⟨hi, hj'and, by simpa using hj'len2, ?_⟩
  intro r hr
  have hpos' : 0 < ldVal n m CB (shiftWire (n + m) d r) :=
    hj'pos (shiftWire (n + m) d r) (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hrlt := hRB i hi r hr
  have hle := hld_le_all r (by omega)
  omega

private lemma buildCB_eval_cmp (n m : ℕ) (C : Circuit) (hM : Monotone2 C)
    (hRB : ReadsBack (n + m) C) (j1 : ℕ) (hj1 : j1 < C.gates.length)
    (Blist : List (Fin m)) (x : Fin n → Bool) (y : Fin m → Bool) :
    let CB := buildCB n m C j1 Blist
    let d := (orTree n m Blist).length
    let tv : Bool := decide (∃ l ∈ Blist, y l = true)
    (tv = true → ∀ w < n + m + C.gates.length,
      wireVal (n + m) C w (Fin.append x y) = true →
      wireVal (n + m) CB (shiftWire (n + m) d w) (Fin.append x y) = true) ∧
    (tv = false → ∀ w < n + m + C.gates.length,
      wireVal (n + m) CB (shiftWire (n + m) d w) (Fin.append x y) = true →
      wireVal (n + m) C w (Fin.append x y) = true) ∧
    (tv = wireVal (n + m) C (n + m + j1) (Fin.append x y) → ∀ w < n + m + C.gates.length,
      wireVal (n + m) CB (shiftWire (n + m) d w) (Fin.append x y) =
        wireVal (n + m) C w (Fin.append x y)) := by
  let tree := orTree n m Blist
  let d := tree.length
  let replG : Gate := if d = 0 then (⟨GateOp.or, []⟩ : Gate) else (⟨GateOp.or, [n + m + d - 1]⟩ : Gate)
  let mapped := C.gates.map fun g => (⟨g.op, g.inputs.map (shiftWire (n + m) d)⟩ : Gate)
  let shifted := mapped.set j1 replG
  let CB := buildCB n m C j1 Blist
  let z := Fin.append x y
  have hCBlen : CB.gates.length = d + C.gates.length := by simp [CB, buildCB, d, tree]
  have hrepl_val : wireVal (n + m) CB (n + m + (d + j1)) z = decide (∃ l ∈ Blist, y l = true) := by
    rw [wireVal_gate CB z (d + j1) (by omega)]
    have hgatCB : gateAt CB (d + j1) = replG := by
      rw [gateAt_eq_getElem CB (d + j1) (by omega)]
      simp [CB, buildCB, tree, shifted, mapped, replG, d, List.getElem_append_right]
    rw [hgatCB]
    by_cases hd0 : d = 0
    · have hBnil : Blist = [] := by
        have := orTree_length n m Blist; rw [show (orTree n m Blist).length = d from rfl, hd0] at this
        exact List.eq_nil_of_length_eq_zero this.symm
      subst hBnil; simp [replG, hd0, GateOp.eval]
    · have hBne : Blist ≠ [] := by
        intro h; subst h; simp [d, tree, orTree] at hd0
      have hlt : n + m + d - 1 < n + m + (d + j1) := by omega
      simp only [replG, hd0, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil,
        List.any_cons, List.any_nil, id_eq, Bool.or_false, ite_eq_left hlt]
      have hpre := wireVal_append_prefix tree shifted z (n + m + d - 1) (by omega)
      change wireVal (n + m) ⟨tree ++ shifted, 0⟩ (n + m + d - 1) z = _ at hpre
      have hCB_eq : wireVal (n + m) CB (n + m + d - 1) z = wireVal (n + m) ⟨tree ++ shifted, 0⟩ (n + m + d - 1) z := rfl
      rw [hCB_eq, hpre]
      exact (orTree_props n m Blist).2.2.2.2 hBne x y
  have hstep_other (i : ℕ) (hi : i < C.gates.length) (hne : i ≠ j1) :
      wireVal (n + m) CB (n + m + (d + i)) z =
        (gateAt C i).op.eval ((gateAt C i).inputs.map fun r =>
          if r < n + m + i then wireVal (n + m) CB (shiftWire (n + m) d r) z else false) := by
    rw [wireVal_gate CB z (d + i) (by omega)]
    have hgatCB : gateAt CB (d + i) = ⟨(gateAt C i).op, (gateAt C i).inputs.map (shiftWire (n + m) d)⟩ := by
      rw [gateAt_eq_getElem CB (d + i) (by omega)]
      simp only [CB, buildCB, tree, shifted, mapped, d, List.getElem_append_right, Nat.le_add_right, add_tsub_cancel_left,
        List.getElem_set_ne (Ne.symm hne), List.getElem_map]
      rw [gateAt_eq_getElem C i hi]
    rw [hgatCB, List.map_map]
    congr 1
    apply List.map_congr_left
    intro r hr
    have hrlt := hRB i hi r hr
    have hshlt : shiftWire (n + m) d r < n + m + (d + i) := by
      unfold shiftWire; by_cases h : r < n + m <;> simp [h] <;> omega
    simp only [Function.comp_apply, ite_eq_left hrlt, ite_eq_left hshlt]
  refine ⟨?_, ?_, ?_⟩
  · intro htv w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hvw
      by_cases hnm : w < n + m
      · simp only [shiftWire, ite_eq_left hnm]
        rw [wireVal_input CB z ⟨w, hnm⟩]; rwa [wireVal_input C z ⟨w, hnm⟩] at hvw
      · simp only [shiftWire, ite_eq_right hnm]
        let i := w - (n + m)
        have hi : i < C.gates.length := by omega
        have hwi : w = n + m + i := by omega
        have hwdi : w + d = n + m + (d + i) := by omega
        rw [hwdi]
        by_cases hij : i = j1
        · subst hij; rw [hrepl_val, htv]
        · rw [hstep_other i hi hij]
          rw [hwi, wireVal_gate C z i hi] at hvw
          have hmem : gateAt C i ∈ C.gates := by rw [gateAt_eq_getElem C i hi]; exact List.getElem_mem hi
          have hop : (gateAt C i).op = GateOp.and ∨ (gateAt C i).op = GateOp.or := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hM _ hmem).1
          refine gate_eval_mono (gateAt C i) hop _ _ ?_ hvw
          intro r hr hrt
          have hrlt := hRB i hi r hr
          simp only [ite_eq_left hrlt] at hrt ⊢
          exact ih r (by omega) (by omega) hrt
  · intro htv w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hvw
      by_cases hnm : w < n + m
      · simp only [shiftWire, ite_eq_left hnm] at hvw
        rw [wireVal_input C z ⟨w, hnm⟩]; rwa [wireVal_input CB z ⟨w, hnm⟩] at hvw
      · simp only [shiftWire, ite_eq_right hnm] at hvw
        let i := w - (n + m)
        have hi : i < C.gates.length := by omega
        have hwi : w = n + m + i := by omega
        have hwdi : w + d = n + m + (d + i) := by omega
        rw [hwdi] at hvw
        by_cases hij : i = j1
        · subst hij; rw [hrepl_val, htv] at hvw; exact absurd hvw (by decide)
        · rw [hstep_other i hi hij] at hvw
          rw [hwi, wireVal_gate C z i hi]
          have hmem : gateAt C i ∈ C.gates := by rw [gateAt_eq_getElem C i hi]; exact List.getElem_mem hi
          have hop : (gateAt C i).op = GateOp.and ∨ (gateAt C i).op = GateOp.or := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hM _ hmem).1
          refine gate_eval_mono (gateAt C i) hop _ _ ?_ hvw
          intro r hr hrt
          have hrlt := hRB i hi r hr
          simp only [ite_eq_left hrlt] at hrt ⊢
          exact ih r (by omega) (by omega) hrt
  · intro htv w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hnm : w < n + m
      · simp only [shiftWire, ite_eq_left hnm]
        rw [wireVal_input CB z ⟨w, hnm⟩, wireVal_input C z ⟨w, hnm⟩]
      · simp only [shiftWire, ite_eq_right hnm]
        let i := w - (n + m)
        have hi : i < C.gates.length := by omega
        have hwi : w = n + m + i := by omega
        have hwdi : w + d = n + m + (d + i) := by omega
        rw [hwdi, hwi]
        by_cases hij : i = j1
        · subst hij; rw [hrepl_val, htv]
        · rw [hstep_other i hi hij, wireVal_gate C z i hi]
          congr 1
          apply List.map_congr_left
          intro r hr
          have hrlt := hRB i hi r hr
          simp only [ite_eq_left hrlt]
          exact ih r (by omega) (by omega)

/-! ### 5. Main induction on k -/

private lemma main_ind (n m : ℕ) (L : Fin m → Finset (Fin n))
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) :
    ∀ (k s : ℕ) (C : Circuit),
      Monotone2 C → ReadsBack (n + m) C → C.size ≤ s →
      Set.ncard (crossSet n m C) ≤ k →
      (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 →
        circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true →
        ∃ j ∈ Y, ∃ p ∈ L j, x p = true) →
      (Finset.univ.filter fun e : Fin n × Fin m =>
        e.1 ∈ L e.2 ∧ circuitFun (n + m) C
          (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true).card ≤
        (6 * k + 2) * s + (3 * k ^ 2 + 3 * k + 1) * m + 2 * k := by
  intro k
  induction k with
  | zero =>
    intro s C hM hRB hSize hK hSound
    have hno : crossSet n m C = ∅ := by
      have hcard0 : Set.ncard (crossSet n m C) = 0 := Nat.eq_zero_of_le_zero hK
      exact (Set.ncard_eq_zero (crossSet_finite n m C)).mp hcard0
    by_cases hout : C.output < n + m + C.gates.length
    · have h0 : ∀ x : Fin n → Bool,
          wireVal (n + m) C C.output (Fin.append x (fun _ => false)) = false := by
        intro x
        by_contra hne
        have ht : circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ (∅ : Finset (Fin m))))) = true := by
          simpa [circuitFun_eq_wireVal] using Bool.eq_true_of_not_eq_false hne
        obtain ⟨j, hj, _⟩ := hSound x ∅ (by simp) ht
        exact Finset.notMem_empty j hj
      have hlin_sound : ∀ l ∈ (Finset.univ : Finset (Fin m)),
          linVal n m C (fun p => decide (p ∉ L l)) l C.output = false := by
        intro l _
        have hfalse : wireVal (n + m) C C.output
            (Fin.append (fun p => decide (p ∉ L l)) (fun l' => decide (l' = l))) = false := by
          by_contra hne
          have ht : circuitFun (n + m) C
              (Fin.append (fun p => decide (p ∉ L l)) (fun l' => decide (l' ∈ ({l} : Finset (Fin m))))) = true := by
            simpa [circuitFun_eq_wireVal] using Bool.eq_true_of_not_eq_false hne
          obtain ⟨j, hj, p, hpL, hpn⟩ := hSound _ {l} (by simp) ht
          rw [Finset.mem_singleton.mp hj] at hpL
          simp [hpL] at hpn
        rw [wireVal_single_line_decomp n m C hM hRB hno _ l C.output hout, Bool.or_eq_false_iff] at hfalse
        exact hfalse.2
      have hbd := deg1_linPart_bound L hL C hM hRB hno C.output hout Finset.univ hlin_sound
      have heq : (Finset.univ.filter fun e : Fin n × Fin m =>
          e.1 ∈ L e.2 ∧ circuitFun (n + m) C
            (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true) =
          (Finset.univ.filter fun e : Fin n × Fin m =>
            e.2 ∈ (Finset.univ : Finset (Fin m)) ∧ e.1 ∈ L e.2 ∧
            linVal n m C (fun v => decide (v = e.1)) e.2 C.output = true) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [circuitFun_eq_wireVal]
        have hdecomp := wireVal_single_line_decomp n m C hM hRB hno (fun i => decide (i = e.1)) e.2 C.output hout
        rw [hdecomp, h0 (fun i => decide (i = e.1)), Bool.false_or]
      rw [heq]
      simp only [Finset.card_univ, Fintype.card_fin] at hbd
      change C.gates.length ≤ s at hSize
      omega
    · have hempty : (Finset.univ.filter fun e : Fin n × Fin m =>
          e.1 ∈ L e.2 ∧ circuitFun (n + m) C
            (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true) = ∅ := by
        ext e
        simp [circuitFun_eq_wireVal, wireVal_oob C _ C.output (Nat.not_lt.mp hout)]
      rw [hempty]; simp
  | succ k ih =>
    intro s C hM hRB hSize hK hSound
    by_cases hne : (crossSet n m C).Nonempty
    · classical
      let j1 := Nat.find hne
      have hj1_cross : j1 ∈ crossSet n m C := Nat.find_spec hne
      have hj1_min : ∀ j < j1, j ∉ crossSet n m C := fun j hj => Nat.find_min hne hj
      have hj1_len : j1 < C.gates.length := hj1_cross.1
      by_cases hout : C.output < n + m + C.gates.length
      · let B : Finset (Fin m) := Finset.univ.filter fun l =>
          wireVal (n + m) C (n + m + j1)
            (Fin.append (fun p => decide (p ∉ L l)) (fun l' => decide (l' = l))) = true
        let Blist : List (Fin m) := B.toList
        have hBmem : ∀ l : Fin m, l ∈ Blist ↔ l ∈ B := fun l => Finset.mem_toList
        have hBlen : Blist.length ≤ m := by
          rw [Finset.length_toList]
          exact (Finset.card_le_univ B).trans (by simp)
        let CB := buildCB n m C j1 Blist
        let d := (orTree n m Blist).length
        obtain ⟨hMCB, hRBCB, hSizeCB, hCrossCB⟩ :=
          buildCB_basic n m C hM hRB j1 hj1_cross Blist hBlen
        have hKCB : Set.ncard (crossSet n m CB) ≤ k := by
          have hfinCB : (crossSet n m CB).Finite := crossSet_finite n m CB
          have hfinC : (crossSet n m C).Finite := crossSet_finite n m C
          have hcard1 : Set.ncard (crossSet n m CB) ≤ Set.ncard (crossSet n m C \ {j1}) := by
            rw [Set.ncard_eq_toFinset_card _ hfinCB, Set.ncard_eq_toFinset_card _ (hfinC.subset Set.sdiff_subset)]
            refine Finset.card_le_card_of_injOn (fun j' => j' - d) ?_ ?_
            · intro j' hj'
              simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hj' ⊢
              exact ⟨(hCrossCB j' hj').2.1, (hCrossCB j' hj').2.2⟩
            · intro a ha b hb hab
              simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at ha hb
              dsimp only at hab
              have h1 : d ≤ a := (hCrossCB a ha).1
              have h2 : d ≤ b := (hCrossCB b hb).1
              omega
          have hcard3 : Set.ncard (crossSet n m C \ {j1}) + 1 = Set.ncard (crossSet n m C) := by
            rw [Set.ncard_sdiff_singleton_add_one hj1_cross hfinC]
          omega
        have hSoundCB : ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 →
            circuitFun (n + m) CB (Fin.append x (fun l => decide (l ∈ Y))) = true →
            ∃ j ∈ Y, ∃ p ∈ L j, x p = true := by
          intro x Y hY hCBt
          by_cases hY0 : Y = ∅
          · subst hY0
            have htv : decide (∃ l ∈ Blist, (fun l' : Fin m => decide (l' ∈ (∅ : Finset (Fin m)))) l = true) = false := by
              simp
            have hCt := (buildCB_eval_cmp n m C hM hRB j1 hj1_len Blist x _).2.1 htv C.output hout hCBt
            exact hSound x ∅ (by simp) hCt
          · obtain ⟨l0, hl0⟩ := Finset.nonempty_iff_ne_empty.mpr hY0
            have hYeq : Y = {l0} := by
              have h1 : 1 ≤ Y.card := Finset.one_le_card.mpr ⟨l0, hl0⟩
              have hcard1 : Y.card = 1 := by omega
              obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
              rw [ha] at hl0
              rw [← Finset.mem_singleton.mp hl0] at ha
              exact ha
            subst hYeq
            by_cases hl0B : l0 ∈ B
            · by_contra hnoP
              have hle_x : ∀ w : Fin (n + m),
                  Fin.append x (fun l => decide (l ∈ ({l0} : Finset (Fin m)))) w = true →
                  Fin.append (fun p => decide (p ∉ L l0)) (fun l => decide (l = l0)) w = true := by
                intro w hw
                refine Fin.addCases (fun p hp => ?_) (fun l hl => ?_) w hw
                · simp only [Fin.append_left] at hp ⊢
                  exact decide_eq_true fun hpL => hnoP ⟨l0, Finset.mem_singleton_self l0, p, hpL, hp⟩
                · simpa using hl
              have hCB_clean := wireVal_mono CB hMCB _ _ hle_x (shiftWire (n + m) d C.output) hCBt
              have htv_eq : decide (∃ l ∈ Blist, (fun l' => decide (l' = l0)) l = true) =
                  wireVal (n + m) C (n + m + j1)
                    (Fin.append (fun p => decide (p ∉ L l0)) (fun l' => decide (l' = l0))) := by
                have h1 : decide (∃ l ∈ Blist, (fun l' => decide (l' = l0)) l = true) = true :=
                  decide_eq_true ⟨l0, (hBmem l0).mpr hl0B, by simp⟩
                have h2 := (Finset.mem_filter.mp hl0B).2
                rw [h1, h2]
              have heq_clean := (buildCB_eval_cmp n m C hM hRB j1 hj1_len Blist
                (fun p => decide (p ∉ L l0)) (fun l' => decide (l' = l0))).2.2 htv_eq C.output hout
              rw [heq_clean] at hCB_clean
              obtain ⟨j, hj, p, hpL, hpn⟩ := hSound (fun p => decide (p ∉ L l0)) {l0} (by simp)
                (by simpa [circuitFun_eq_wireVal] using hCB_clean)
              rw [Finset.mem_singleton.mp hj] at hpL
              simp [hpL] at hpn
            · have htv : decide (∃ l ∈ Blist, (fun l' => decide (l' ∈ ({l0} : Finset (Fin m)))) l = true) = false := by
                apply decide_eq_false
                rintro ⟨l, hlB, hl0eq⟩
                simp only [Finset.mem_singleton, decide_eq_true_eq] at hl0eq
                subst hl0eq
                exact hl0B ((hBmem l).mp hlB)
              have hCt := (buildCB_eval_cmp n m C hM hRB j1 hj1_len Blist x _).2.1 htv C.output hout hCBt
              exact hSound x {l0} (by simp) hCt
        have hIH := ih (s + m) CB hMCB hRBCB (by change CB.size ≤ C.size + m at hSizeCB; omega) hKCB hSoundCB
        -- Now handle the two inputs u, v of j1
        obtain ⟨_, hj1_and, hj1_len2, _⟩ := hj1_cross
        obtain ⟨u, v, huv_eq⟩ : ∃ u v : ℕ, (gateAt C j1).inputs = [u, v] := by
          cases hin : (gateAt C j1).inputs with
          | nil => simp [hin] at hj1_len2
          | cons a rest =>
            cases rest with
            | nil => simp [hin] at hj1_len2
            | cons b rest2 =>
              cases rest2 with
              | nil => exact ⟨a, b, rfl⟩
              | cons _ _ => simp [hin] at hj1_len2
        have hu_lt : u < n + m + j1 := hRB j1 hj1_len u (by rw [huv_eq]; exact List.mem_cons_self)
        have hv_lt : v < n + m + j1 := hRB j1 hj1_len v (by rw [huv_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        let Cpre : Circuit := ⟨C.gates.take j1, 0⟩
        have hCpre_len : Cpre.gates.length = j1 := by simp [Cpre, Nat.min_eq_left hj1_len.le]
        have hMpre : Monotone2 Cpre := fun g hg => hM g (List.mem_of_mem_take hg)
        have hRBpre : ReadsBack (n + m) Cpre := by
          intro j hj r hr
          have hj' : j < j1 := by omega
          have hgat : gateAt Cpre j = gateAt C j := by
            rw [gateAt_eq_getElem Cpre j hj, gateAt_eq_getElem C j (by omega)]
            simp [Cpre, List.getElem_take]
          rw [hgat] at hr
          exact hRB j (by omega) r hr
        have hnopre : crossSet n m Cpre = ∅ := by
          ext j
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hj
          obtain ⟨hjlt, hjand, hjlen2, hjpos⟩ := hj
          have hj1' : j < j1 := by omega
          have hgat : gateAt Cpre j = gateAt C j := by
            rw [gateAt_eq_getElem Cpre j hjlt, gateAt_eq_getElem C j (by omega)]
            simp [Cpre, List.getElem_take]
          apply hj1_min j hj1'
          refine ⟨by omega, by rwa [← hgat], by rwa [← hgat], ?_⟩
          intro r hr
          rw [← hgat] at hr
          have hrlt := hRBpre j hjlt r hr
          have hld := ldVal_take n m C j1 r (by omega)
          have := hjpos r hr
          rwa [hld] at this
        let Gu : Finset (Fin m) := Finset.univ.filter fun l =>
          wireVal (n + m) Cpre u (Fin.append (fun p => decide (p ∉ L l)) (fun l' => decide (l' = l))) = false
        let Gv : Finset (Fin m) := Finset.univ.filter fun l =>
          wireVal (n + m) Cpre v (Fin.append (fun p => decide (p ∉ L l)) (fun l' => decide (l' = l))) = false
        let Eu := Finset.univ.filter fun e : Fin n × Fin m =>
          e.2 ∈ Gu ∧ e.1 ∈ L e.2 ∧
          wireVal (n + m) Cpre u (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true
        let Ev := Finset.univ.filter fun e : Fin n × Fin m =>
          e.2 ∈ Gv ∧ e.1 ∈ L e.2 ∧
          wireVal (n + m) Cpre v (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true
        let ECB := Finset.univ.filter fun e : Fin n × Fin m =>
          e.1 ∈ L e.2 ∧ circuitFun (n + m) CB
            (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true
        have hEu_bd : Eu.card ≤ 3 * Cpre.gates.length + 2 * Gu.card + 1 :=
          deg1_full_bound L hL Cpre hMpre hRBpre hnopre u (by omega) Gu (fun l hl => (Finset.mem_filter.mp hl).2)
        have hEv_bd : Ev.card ≤ 3 * Cpre.gates.length + 2 * Gv.card + 1 :=
          deg1_full_bound L hL Cpre hMpre hRBpre hnopre v (by omega) Gv (fun l hl => (Finset.mem_filter.mp hl).2)
        have hcover : (Finset.univ.filter fun e : Fin n × Fin m =>
            e.1 ∈ L e.2 ∧ circuitFun (n + m) C
              (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true) ⊆
            ECB ∪ (Eu ∪ Ev) := by
          intro e he
          obtain ⟨hpL, hCt⟩ := (Finset.mem_filter.mp he).2
          by_cases hlB : e.2 ∈ B
          · apply Finset.mem_union_left
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpL, ?_⟩
            have htv : decide (∃ l ∈ Blist, (fun l' => decide (l' = e.2)) l = true) = true :=
              decide_eq_true ⟨e.2, (hBmem e.2).mpr hlB, by simp⟩
            exact (buildCB_eval_cmp n m C hM hRB j1 hj1_len Blist _ _).1 htv C.output hout hCt
          · by_cases hj1v : wireVal (n + m) C (n + m + j1)
                (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = false
            · apply Finset.mem_union_left
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpL, ?_⟩
              have htv : decide (∃ l ∈ Blist, (fun l' => decide (l' = e.2)) l = true) = false := by
                apply decide_eq_false
                rintro ⟨l, hlB', hle⟩
                simp only [decide_eq_true_eq] at hle; subst hle
                exact hlB ((hBmem e.2).mp hlB')
              have heq_v := (buildCB_eval_cmp n m C hM hRB j1 hj1_len Blist
                (fun i => decide (i = e.1)) (fun l => decide (l = e.2))).2.2 (by rw [htv, hj1v]) C.output hout
              change wireVal (n + m) CB (shiftWire (n + m) d C.output) _ = true
              rw [heq_v]; exact hCt
            · apply Finset.mem_union_right
              have hj1t : wireVal (n + m) C (n + m + j1)
                  (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true :=
                Bool.eq_true_of_not_eq_false hj1v
              rw [wireVal_gate C _ j1 hj1_len, hj1_and, huv_eq] at hj1t
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, Bool.and_eq_true, ite_eq_left hu_lt, ite_eq_left hv_lt] at hj1t
              have hu_t : wireVal (n + m) Cpre u
                  (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true := by
                rw [wireVal_take C _ j1 u (by omega)]; exact hj1t.1
              have hv_t : wireVal (n + m) Cpre v
                  (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true := by
                rw [wireVal_take C _ j1 v (by omega)]; exact hj1t.2
              have hnotB : wireVal (n + m) C (n + m + j1)
                  (Fin.append (fun p => decide (p ∉ L e.2)) (fun l' => decide (l' = e.2))) = false := by
                have : ¬ (wireVal (n + m) C (n + m + j1)
                    (Fin.append (fun p => decide (p ∉ L e.2)) (fun l' => decide (l' = e.2))) = true) :=
                  fun h => hlB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
                exact Bool.eq_false_iff.mpr this
              rw [wireVal_gate C _ j1 hj1_len, hj1_and, huv_eq] at hnotB
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, Bool.and_eq_false_iff, ite_eq_left hu_lt, ite_eq_left hv_lt] at hnotB
              rcases hnotB with huf | hvf
              · apply Finset.mem_union_left
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hpL, hu_t⟩
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                rw [wireVal_take C _ j1 u (by omega)]; exact huf
              · apply Finset.mem_union_right
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hpL, hv_t⟩
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                rw [wireVal_take C _ j1 v (by omega)]; exact hvf
        have htot := (Finset.card_le_card hcover).trans
          ((Finset.card_union_le ECB (Eu ∪ Ev)).trans (Nat.add_le_add_left (Finset.card_union_le Eu Ev) _))
        have hGu_le : Gu.card ≤ m := (Finset.card_le_univ Gu).trans (by simp)
        have hGv_le : Gv.card ≤ m := (Finset.card_le_univ Gv).trans (by simp)
        have hpre_le : Cpre.gates.length ≤ s := by change C.gates.length ≤ s at hSize; omega
        have halg : (6 * k + 2) * (s + m) + (3 * k ^ 2 + 3 * k + 1) * m + 2 * k +
            (3 * s + 2 * m + 1) + (3 * s + 2 * m + 1) =
            (6 * (k + 1) + 2) * s + (3 * (k + 1) ^ 2 + 3 * (k + 1) + 1) * m + 2 * (k + 1) := by
          ring
        have hIH' : ECB.card ≤ (6 * k + 2) * (s + m) + (3 * k ^ 2 + 3 * k + 1) * m + 2 * k := hIH
        omega
      · have hempty : (Finset.univ.filter fun e : Fin n × Fin m =>
            e.1 ∈ L e.2 ∧ circuitFun (n + m) C
              (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true) = ∅ := by
          ext e
          simp [circuitFun_eq_wireVal, wireVal_oob C _ C.output (Nat.not_lt.mp hout)]
        rw [hempty]; simp
    · have hno : crossSet n m C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hK0 : Set.ncard (crossSet n m C) ≤ k := by rw [hno, Set.ncard_empty]; exact Nat.zero_le k
      have hIH := ih s C hM hRB hSize hK0 hSound
      have h1 : (6 * k + 2) * s ≤ (6 * (k + 1) + 2) * s := Nat.mul_le_mul_right s (by omega)
      have h2 : (3 * k ^ 2 + 3 * k + 1) * m ≤ (3 * (k + 1) ^ 2 + 3 * (k + 1) + 1) * m := by
        apply Nat.mul_le_mul_right m
        nlinarith
      omega

theorem main (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : Circuit)
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1)
    (hM : Monotone2 C) (hRB : ReadsBack (n + m) C) (hSize : C.size ≤ s)
    (hK : Set.ncard {j : ℕ | j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      (gateAt C j).inputs.length = 2 ∧
      ∀ i ∈ (gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k)
    (hSound : ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 →
      circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true →
      ∃ j ∈ Y, ∃ p ∈ L j, x p = true) :
    (Finset.univ.filter fun e : Fin n × Fin m =>
      e.1 ∈ L e.2 ∧ circuitFun (n + m) C
        (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true).card ≤
      (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
  have h := main_ind n m L hL k s C hM hRB hSize hK hSound
  have h1 : (6 * k + 2) * s ≤ (6 * k + 6) * s := Nat.mul_le_mul_right s (by omega)
  have h2 : (3 * k ^ 2 + 3 * k + 1) * m ≤ (12 * k ^ 2 + 13 * k + 2) * m := by
    apply Nat.mul_le_mul_right m
    nlinarith
  have h3 : 2 * k ≤ 6 * k ^ 2 + 5 * k := by nlinarith
  omega

end PEqualNP.Outside.L_meta_1625_aux

theorem PEqualNP.Outside.L_meta_1625 : ∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k :=
  PEqualNP.Outside.L_meta_1625_aux.main

