import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_613

open Classical
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private lemma wires_length_aux (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma wires_getD_prefix (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w).getD k false =
      w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hk']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

private lemma wires_take_getD (C : Circuit) (l : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    let pref := (C.gates.take j).foldl
      (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) l
    (C.wires l).getD (l.length + j) false =
      (C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun i => pref.getD i false) := by
  intro pref
  unfold Circuit.wires
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have hdrop : C.gates[j] :: C.gates.drop (j + 1) = C.gates.drop j :=
      List.cons_getElem_drop_succ (h := hj)
    rw [hdrop, List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  have hlen : pref.length = l.length + j := by
    dsimp only [pref]
    rw [wires_length_aux, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : l.length + j < (pref ++ [(C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun i => pref.getD i false)]).length := by
    simp only [List.length_append, List.length_singleton, hlen]; omega
  rw [wires_getD_prefix _ _ _ hlt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
  rfl

private lemma wires_getD_eq_pref (C : Circuit) (l : List Bool) (j i : ℕ) (hj : j ≤ C.gates.length) :
    let pref := (C.gates.take j).foldl
      (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) l
    pref.getD i false = if i < l.length + j then (C.wires l).getD i false else false := by
  intro pref
  have hlen : pref.length = l.length + j := by
    dsimp only [pref]
    rw [wires_length_aux, List.length_take, Nat.min_eq_left hj]
  split_ifs with hi
  · unfold Circuit.wires
    have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_rhs => rw [hsplit, List.foldl_append]
    have hi' : i < pref.length := by omega
    exact (wires_getD_prefix _ _ _ hi').symm
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega)]
    rfl

private def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val Circuit.wires
  have hw' : w < (List.ofFn x).length := by simpa using hw
  rw [wires_getD_prefix _ _ _ hw']
  simp [List.getD_eq_getElem?_getD, hw]

private lemma val_oob (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : val C n x w = false := by
  unfold val
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    unfold Circuit.wires
    rw [wires_length_aux, List.length_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

private lemma val_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C n x (n + j) =
      (C.gates[j]'hj).op.eval
        ((C.gates[j]'hj).inputs.map fun i => if i < n + j then val C n x i else false) := by
  unfold val
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h1 := wires_take_getD C (List.ofFn x) j hj
  rw [hlen] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i _
  have h2 := wires_getD_eq_pref C (List.ofFn x) j i (Nat.le_of_lt hj)
  rw [hlen] at h2
  exact h2

private lemma val_gate_or_iff (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hop : (C.gates[j]'hj).op = GateOp.or) :
    val C n x (n + j) = true ↔
      ∃ i ∈ (C.gates[j]'hj).inputs, i < n + j ∧ val C n x i = true := by
  rw [val_gate C n x j hj, hop]
  simp [GateOp.eval]

private lemma val_gate_and_iff (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hop : (C.gates[j]'hj).op = GateOp.and) :
    val C n x (n + j) = true ↔
      ∀ i ∈ (C.gates[j]'hj).inputs, i < n + j ∧ val C n x i = true := by
  rw [val_gate C n x j hj, hop]
  simp [GateOp.eval]

private lemma union_card_le_gates_add_outputs {α : Type*} [DecidableEq α] :
    ∀ (k : ℕ) (R : Finset ℕ), R.card = k →
      ∀ (F : ℕ → Finset α),
        (∀ w : ℕ, (F w).card ≤ 1 ∨ (w ∈ R ∧ ∃ a b : ℕ, a < w ∧ b < w ∧ F w ⊆ F a ∪ F b)) →
        ∀ (U : Finset ℕ), (U.biUnion F).card ≤ R.card + U.card := by
  intro k
  induction k with
  | zero =>
    intro R hR F hF U
    have hR0 : R = ∅ := Finset.card_eq_zero.mp hR
    have hle1 : ∀ w ∈ U, (F w).card ≤ 1 := by
      intro w _
      rcases hF w with h1 | ⟨hwR, _⟩
      · exact h1
      · simp [hR0] at hwR
    calc
      (U.biUnion F).card ≤ ∑ w ∈ U, (F w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ U, 1 := Finset.sum_le_sum hle1
      _ = U.card := by simp
      _ = R.card + U.card := by omega
  | succ k ih =>
    intro R hR F hF U
    have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
    let m := R.max' hRne
    have hmR : m ∈ R := Finset.max'_mem R hRne
    let R' := R.erase m
    have hR'card : R'.card = k := by
      rw [Finset.card_erase_of_mem hmR, hR]; omega
    have hlt_m : ∀ r ∈ R', r < m := by
      intro r hr
      have hrR : r ∈ R := Finset.mem_of_mem_erase hr
      have hrne : r ≠ m := (Finset.mem_erase.mp hr).1
      exact lt_of_le_of_ne (Finset.le_max' R r hrR) hrne
    let F' : ℕ → Finset α := fun w => if w = m then ∅ else F w
    have hF' : ∀ w : ℕ, (F' w).card ≤ 1 ∨
        (w ∈ R' ∧ ∃ a b : ℕ, a < w ∧ b < w ∧ F' w ⊆ F' a ∪ F' b) := by
      intro w
      by_cases hwm : w = m
      · left; simp [F', hwm]
      · rcases hF w with h1 | ⟨hwR, a, b, ha, hb, hsub⟩
        · left; simp [F', hwm, h1]
        · right
          have hwR' : w ∈ R' := Finset.mem_erase.mpr ⟨hwm, hwR⟩
          have hwlt : w < m := hlt_m w hwR'
          have ham : a ≠ m := by omega
          have hbm : b ≠ m := by omega
          refine ⟨hwR', a, b, ha, hb, ?_⟩
          simpa [F', hwm, ham, hbm] using hsub
    by_cases hmU : m ∈ U
    · rcases hF m with h1 | ⟨_, a, b, ha, hb, hsub⟩
      · have hUsub : U.biUnion F ⊆ (U.erase m).biUnion F' ∪ F m := by
          intro x hx
          rcases Finset.mem_biUnion.mp hx with ⟨w, hwU, hxw⟩
          by_cases hwm : w = m
          · subst hwm
            exact Finset.mem_union_right _ hxw
          · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hwm, hwU⟩, ?_⟩)
            simpa [F', hwm] using hxw
        have hih := ih R' hR'card F' hF' (U.erase m)
        have hcard_erase : (U.erase m).card + 1 = U.card := by
          rw [Finset.card_erase_of_mem hmU]
          have : 1 ≤ U.card := Finset.one_le_card.mpr ⟨m, hmU⟩
          omega
        calc
          (U.biUnion F).card ≤ ((U.erase m).biUnion F' ∪ F m).card := Finset.card_le_card hUsub
          _ ≤ ((U.erase m).biUnion F').card + (F m).card := Finset.card_union_le _ _
          _ ≤ (R'.card + (U.erase m).card) + 1 := by omega
          _ ≤ R.card + U.card := by omega
      · let U' := (U.erase m) ∪ ({a, b} : Finset ℕ)
        have hUsub : U.biUnion F ⊆ U'.biUnion F' := by
          intro x hx
          rcases Finset.mem_biUnion.mp hx with ⟨w, hwU, hxw⟩
          by_cases hwm : w = m
          · subst hwm
            have hxab := hsub hxw
            rcases Finset.mem_union.mp hxab with hxa | hxb
            · refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_union_right _ (by simp), ?_⟩
              have ham : a ≠ m := by omega
              simpa [F', ham] using hxa
            · refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_union_right _ (by simp), ?_⟩
              have hbm : b ≠ m := by omega
              simpa [F', hbm] using hxb
          · refine Finset.mem_biUnion.mpr ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hwU⟩), ?_⟩
            simpa [F', hwm] using hxw
        have hih := ih R' hR'card F' hF' U'
        have hU'card : U'.card ≤ U.card + 1 := by
          have h1 : U'.card ≤ (U.erase m).card + ({a, b} : Finset ℕ).card := Finset.card_union_le _ _
          have h2 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
          have h3 : (U.erase m).card + 1 = U.card := by
            rw [Finset.card_erase_of_mem hmU]
            have : 1 ≤ U.card := Finset.one_le_card.mpr ⟨m, hmU⟩
            omega
          omega
        calc
          (U.biUnion F).card ≤ (U'.biUnion F').card := Finset.card_le_card hUsub
          _ ≤ R'.card + U'.card := hih
          _ ≤ R.card + U.card := by omega
    · have hUsub : U.biUnion F ⊆ U.biUnion F' := by
        intro x hx
        rcases Finset.mem_biUnion.mp hx with ⟨w, hwU, hxw⟩
        have hwm : w ≠ m := fun h => hmU (h ▸ hwU)
        refine Finset.mem_biUnion.mpr ⟨w, hwU, ?_⟩
        simpa [F', hwm] using hxw
      have hih := ih R' hR'card F' hF' U
      calc
        (U.biUnion F).card ≤ (U.biUnion F').card := Finset.card_le_card hUsub
        _ ≤ R'.card + U.card := hih
        _ ≤ R.card + U.card := by omega

private lemma list_filter_two_union {α : Type*} [DecidableEq α]
    (l : List ℕ) (hl : l.length ≤ 2) (w : ℕ) (F : ℕ → Finset α)
    (hsub : F w ⊆ (l.filter (· < w)).toFinset.biUnion F) :
    (F w).card ≤ 1 ∨ ∃ a b : ℕ, a < w ∧ b < w ∧ F w ⊆ F a ∪ F b := by
  have hlen : (l.filter (· < w)).length ≤ 2 := le_trans (List.length_filter_le _ _) hl
  match hfl : l.filter (· < w) with
  | [] =>
    left
    have h0 : F w = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := hsub hx
      simp [hfl] at this
    simp [h0]
  | [a] =>
    right
    have ha : a < w := by
      have : a ∈ l.filter (· < w) := by simp [hfl]
      simpa using (List.mem_filter.mp this).2
    refine ⟨a, a, ha, ha, ?_⟩
    intro x hx
    have := hsub hx
    simp [hfl] at this
    exact Finset.mem_union_left _ this
  | [a, b] =>
    right
    have ha : a < w := by
      have : a ∈ l.filter (· < w) := by simp [hfl]
      simpa using (List.mem_filter.mp this).2
    have hb : b < w := by
      have : b ∈ l.filter (· < w) := by simp [hfl]
      simpa using (List.mem_filter.mp this).2
    refine ⟨a, b, ha, hb, ?_⟩
    intro x hx
    have := hsub hx
    simp [hfl] at this
    exact Finset.mem_union.mpr this
  | _ :: _ :: _ :: _ =>
    rw [hfl] at hlen
    simp at hlen

private def depStep (C : Circuit) (n : ℕ) (a b : ℕ) : Prop :=
  b < a ∧ ∃ h : Gate, C.gates[a]? = some h ∧ n + b ∈ h.inputs

private def unitVec (n : ℕ) (u : Fin n) : Fin n → Bool :=
  fun w => decide (w = u)

private def varSupp (C : Circuit) (n : ℕ) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n => val C n (unitVec n u) w = true)

private def isBotOr (C : Circuit) (n : ℕ) (A : Finset ℕ) (j : ℕ) : Prop :=
  j < C.gates.length ∧ j ∉ A ∧ ¬ ∃ i ∈ A, Relation.TransGen (depStep C n) j i

private def isTopOr (C : Circuit) (n : ℕ) (A : Finset ℕ) (j : ℕ) : Prop :=
  j < C.gates.length ∧ j ∉ A ∧ ∃ i ∈ A, Relation.TransGen (depStep C n) j i

private def noAnd (C : Circuit) (n : ℕ) (A : Finset ℕ) (w : ℕ) : Prop :=
  ∀ j : ℕ, j < C.gates.length → w = n + j → isBotOr C n A j

private lemma gate_or_of_not_mem_A (C : Circuit) (A : Finset ℕ)
    (hM : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (j : ℕ) (hj : j < C.gates.length) (hjA : j ∉ A) :
    (C.gates[j]'hj).op = GateOp.or := by
  have hmem : C.gates[j]'hj ∈ C.gates := List.getElem_mem hj
  rcases (hM _ hmem).1 with hand | hor
  · exfalso
    exact hjA ((hA j).mpr ⟨C.gates[j]'hj, List.getElem?_eq_getElem hj, hand⟩)
  · exact hor

private lemma noAnd_of_input_of_botOr (C : Circuit) (n : ℕ) (A : Finset ℕ)
    (j : ℕ) (hjbot : isBotOr C n A j)
    (i : ℕ) (hi_mem : i ∈ (C.gates[j]'hjbot.1).inputs) (hi_lt : i < n + j) :
    noAnd C n A i := by
  intro k hk hik
  have hkj : k < j := by omega
  have hstep : depStep C n j k :=
    ⟨hkj, C.gates[j]'hjbot.1, List.getElem?_eq_getElem hjbot.1, hik ▸ hi_mem⟩
  refine ⟨hk, ?_, ?_⟩
  · intro hkA
    exact hjbot.2.2 ⟨k, hkA, Relation.TransGen.single hstep⟩
  · rintro ⟨a, haA, hreach⟩
    exact hjbot.2.2 ⟨a, haA, Relation.TransGen.head hstep hreach⟩

private lemma noAnd_of_input_of_and (C : Circuit) (n : ℕ) (A : Finset ℕ)
    (hflat : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (depStep C n) j i)
    (j : ℕ) (hj : j < C.gates.length) (hjA : j ∈ A)
    (i : ℕ) (hi_mem : i ∈ (C.gates[j]'hj).inputs) (hi_lt : i < n + j) :
    noAnd C n A i := by
  intro k hk hik
  have hkj : k < j := by omega
  have hstep : depStep C n j k :=
    ⟨hkj, C.gates[j]'hj, List.getElem?_eq_getElem hj, hik ▸ hi_mem⟩
  refine ⟨hk, ?_, ?_⟩
  · intro hkA
    exact hflat j hjA k hkA (Relation.TransGen.single hstep)
  · rintro ⟨a, haA, hreach⟩
    exact hflat j hjA a haA (Relation.TransGen.head hstep hreach)

private lemma val_eq_exists_varSupp (C : Circuit) (n : ℕ) (A : Finset ℕ)
    (hM : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and) :
    ∀ w : ℕ, noAnd C n A w →
      ∀ x : Fin n → Bool, val C n x w = true ↔ ∃ u ∈ varSupp C n w, x u = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hna x
    by_cases hw_in : w < n
    · rw [val_input C n x w hw_in]
      constructor
      · intro hx
        refine ⟨⟨w, hw_in⟩, ?_, hx⟩
        simp [varSupp, val_input C n _ w hw_in, unitVec]
      · rintro ⟨u, hu, hxu⟩
        simp only [varSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        rw [val_input C n _ w hw_in] at hu
        simp only [unitVec, decide_eq_true_eq] at hu
        exact hu ▸ hxu
    · by_cases hw_oob : n + C.gates.length ≤ w
      · rw [val_oob C n x w hw_oob]
        constructor
        · intro h; cases h
        · rintro ⟨u, hu, _⟩
          simp [varSupp, val_oob C n _ w hw_oob] at hu
      · have hj : w - n < C.gates.length := by omega
        have hw_eq : w = n + (w - n) := by omega
        set j := w - n
        have hjbot : isBotOr C n A j := hna j hj hw_eq
        have hor : (C.gates[j]'hj).op = GateOp.or :=
          gate_or_of_not_mem_A C A hM hA j hj hjbot.2.1
        rw [hw_eq, val_gate_or_iff C n x j hj hor]
        constructor
        · rintro ⟨i, hi_mem, hi_lt, hval⟩
          have hi_na : noAnd C n A i := noAnd_of_input_of_botOr C n A j hjbot i hi_mem hi_lt
          have hi_lt' : i < w := by omega
          rcases (ih i hi_lt' hi_na x).mp hval with ⟨u, hu, hxu⟩
          refine ⟨u, ?_, hxu⟩
          simp only [varSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          rw [val_gate_or_iff C n _ j hj hor]
          exact ⟨i, hi_mem, hi_lt, hu⟩
        · rintro ⟨u, hu, hxu⟩
          simp only [varSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          rw [val_gate_or_iff C n _ j hj hor] at hu
          rcases hu with ⟨i, hi_mem, hi_lt, hval_u⟩
          have hi_na : noAnd C n A i := noAnd_of_input_of_botOr C n A j hjbot i hi_mem hi_lt
          have hi_lt' : i < w := by omega
          have hu_i : u ∈ varSupp C n i := by
            simp [varSupp, hval_u]
          exact ⟨i, hi_mem, hi_lt, (ih i hi_lt' hi_na x).mpr ⟨u, hu_i, hxu⟩⟩

private lemma varSupp_botOr_subset (C : Circuit) (n : ℕ) (A : Finset ℕ)
    (hM : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (j : ℕ) (hjbot : isBotOr C n A j) :
    varSupp C n (n + j) ⊆
      ((C.gates[j]'hjbot.1).inputs.filter (· < n + j)).toFinset.biUnion (varSupp C n) := by
  intro u hu
  have hor : (C.gates[j]'hjbot.1).op = GateOp.or :=
    gate_or_of_not_mem_A C A hM hA j hjbot.1 hjbot.2.1
  simp only [varSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rw [val_gate_or_iff C n _ j hjbot.1 hor] at hu
  rcases hu with ⟨i, hi_mem, hi_lt, hval⟩
  refine Finset.mem_biUnion.mpr ⟨i, ?_, ?_⟩
  · simp [hi_mem, hi_lt]
  · simp [varSupp, hval]

private lemma varSupp_subset_of_input_botOr (C : Circuit) (n : ℕ) (A : Finset ℕ)
    (hM : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (j : ℕ) (hjbot : isBotOr C n A j)
    (i : ℕ) (hi_mem : i ∈ (C.gates[j]'hjbot.1).inputs) (hi_lt : i < n + j) :
    varSupp C n i ⊆ varSupp C n (n + j) := by
  intro u hu
  have hor : (C.gates[j]'hjbot.1).op = GateOp.or :=
    gate_or_of_not_mem_A C A hM hA j hjbot.1 hjbot.2.1
  simp only [varSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rw [val_gate_or_iff C n _ j hjbot.1 hor]
  exact ⟨i, hi_mem, hi_lt, hu⟩

private lemma exists_leafWire (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit)
    (cen : ℕ → Fin n) (A : Finset ℕ)
    (hM : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (hcen : ∀ j ∈ A, ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + j) false = true →
      (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧ x (cen j) = true)
    (hflat : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (depStep C n) j i)
    (j : ℕ) (hjA : j ∈ A) :
    ∃ lw : ℕ, noAnd C n A lw ∧
      (∀ v ∈ varSupp C n lw, G.Adj (cen j) v) ∧
      (∀ x : Fin n → Bool, val C n x (n + j) = true →
        x (cen j) = true ∧ ∃ v ∈ varSupp C n lw, x v = true) := by
  have dead_case : (∀ x : Fin n → Bool, val C n x (n + j) = false) →
      ∃ lw : ℕ, noAnd C n A lw ∧
        (∀ v ∈ varSupp C n lw, G.Adj (cen j) v) ∧
        (∀ x : Fin n → Bool, val C n x (n + j) = true →
          x (cen j) = true ∧ ∃ v ∈ varSupp C n lw, x v = true) := by
    intro hdead
    refine ⟨n + C.gates.length, ?_, ?_, ?_⟩
    · intro k hk hEq; omega
    · intro v hv
      simp [varSupp, val_oob C n _ (n + C.gates.length) (le_refl _)] at hv
    · intro x hx
      rw [hdead x] at hx; cases hx
  rcases (hA j).mp hjA with ⟨g, hget, hop⟩
  have hj : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hget
    cases hget
  have hgeq : C.gates[j]'hj = g := by
    rw [List.getElem?_eq_getElem hj] at hget
    exact Option.some.inj hget
  have hlen2 : g.inputs.length ≤ 2 := (hM g (hgeq ▸ List.getElem_mem hj)).2
  have hop' : (C.gates[j]'hj).op = GateOp.and := hgeq.symm ▸ hop
  match hinp : (C.gates[j]'hj).inputs with
  | [] =>
    exfalso
    have h0 : val C n (fun _ => false) (n + j) = true := by
      rw [val_gate_and_iff C n _ j hj hop', hinp]
      simp
    rcases (hcen j hjA (fun _ => false) h0).1 with ⟨_, _, _, hf, _⟩
    cases hf
  | [a] =>
    apply dead_case
    intro x
    by_cases hval : val C n x (n + j) = true
    · exfalso
      rw [val_gate_and_iff C n x j hj hop', hinp] at hval
      have ha := hval a (by simp)
      have ha_na : noAnd C n A a := noAnd_of_input_of_and C n A hflat j hj hjA a (by simp [hinp]) ha.1
      rcases (val_eq_exists_varSupp C n A hM hA a ha_na x).mp ha.2 with ⟨u, hu, _⟩
      have hvu : val C n (unitVec n u) (n + j) = true := by
        rw [val_gate_and_iff C n _ j hj hop', hinp]
        intro i hi
        simp only [List.mem_singleton] at hi
        subst hi
        exact ⟨ha.1, (Finset.mem_filter.mp hu).2⟩
      rcases (hcen j hjA (unitVec n u) hvu).1 with ⟨v1, v2, hadj, hv1, hv2⟩
      simp only [unitVec, decide_eq_true_eq] at hv1 hv2
      subst hv1; subst hv2
      exact G.loopless.irrefl _ hadj
    · exact Bool.eq_false_iff.mpr hval
  | [a, b] =>
    by_cases hlt : a < n + j ∧ b < n + j
    · have ha_na : noAnd C n A a :=
        noAnd_of_input_of_and C n A hflat j hj hjA a (by simp [hinp]) hlt.1
      have hb_na : noAnd C n A b :=
        noAnd_of_input_of_and C n A hflat j hj hjA b (by simp [hinp]) hlt.2
      have hiff : ∀ x : Fin n → Bool, val C n x (n + j) = true ↔
          (∃ u ∈ varSupp C n a, x u = true) ∧ (∃ v ∈ varSupp C n b, x v = true) := by
        intro x
        rw [val_gate_and_iff C n x j hj hop', hinp]
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        rw [← val_eq_exists_varSupp C n A hM hA a ha_na x,
            ← val_eq_exists_varSupp C n A hM hA b hb_na x]
        exact ⟨fun h => ⟨h.1.2, h.2.2⟩, fun h => ⟨⟨hlt.1, h.1⟩, ⟨hlt.2, h.2⟩⟩⟩
      by_cases hne : (varSupp C n a).Nonempty ∧ (varSupp C n b).Nonempty
      · have hpair : ∀ u ∈ varSupp C n a, ∀ v ∈ varSupp C n b,
            G.Adj u v ∧ (cen j = u ∨ cen j = v) := by
          intro u hu v hv
          let x : Fin n → Bool := fun z => decide (z = u ∨ z = v)
          have hval : val C n x (n + j) = true :=
            (hiff x).mpr ⟨⟨u, hu, by simp [x]⟩, ⟨v, hv, by simp [x]⟩⟩
          rcases hcen j hjA x hval with ⟨⟨w1, w2, hadj, hw1, hw2⟩, hcx⟩
          simp only [x, decide_eq_true_eq] at hw1 hw2 hcx
          refine ⟨?_, hcx⟩
          rcases hw1 with rfl | rfl <;> rcases hw2 with rfl | rfl
          · exact absurd hadj (G.loopless.irrefl _)
          · exact hadj
          · exact hadj.symm
          · exact absurd hadj (G.loopless.irrefl _)
        by_cases ha_eq : ∀ u ∈ varSupp C n a, u = cen j
        · refine ⟨b, hb_na, ?_, ?_⟩
          · intro v hv
            rcases hne.1 with ⟨u, hu⟩
            have hu_eq : u = cen j := ha_eq u hu
            exact hu_eq ▸ (hpair u hu v hv).1
          · intro x hx
            rcases (hiff x).mp hx with ⟨⟨u, hu, hxu⟩, ⟨v, hv, hxv⟩⟩
            exact ⟨ha_eq u hu ▸ hxu, v, hv, hxv⟩
        · have hb_eq : ∀ v ∈ varSupp C n b, v = cen j := by
            push Not at ha_eq
            rcases ha_eq with ⟨u, hu, hune⟩
            intro v hv
            rcases (hpair u hu v hv).2 with hcu | hcv
            · exact absurd hcu.symm hune
            · exact hcv.symm
          refine ⟨a, ha_na, ?_, ?_⟩
          · intro u hu
            rcases hne.2 with ⟨v, hv⟩
            have hv_eq : v = cen j := hb_eq v hv
            exact (hv_eq ▸ (hpair u hu v hv).1).symm
          · intro x hx
            rcases (hiff x).mp hx with ⟨⟨u, hu, hxu⟩, ⟨v, hv, hxv⟩⟩
            exact ⟨hb_eq v hv ▸ hxv, u, hu, hxu⟩
      · apply dead_case
        intro x
        by_cases hval : val C n x (n + j) = true
        · exfalso
          rcases (hiff x).mp hval with ⟨⟨u, hu, _⟩, ⟨v, hv, _⟩⟩
          exact hne ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
        · exact Bool.eq_false_iff.mpr hval
    · apply dead_case
      intro x
      by_cases hval : val C n x (n + j) = true
      · exfalso
        rw [val_gate_and_iff C n x j hj hop', hinp] at hval
        exact hlt ⟨(hval a (by simp)).1, (hval b (by simp)).1⟩
      · exact Bool.eq_false_iff.mpr hval
  | _ :: _ :: _ :: _ =>
    rw [← hgeq, hinp] at hlen2
    simp at hlen2

private noncomputable def topAnds (C : Circuit) (n : ℕ) (A : Finset ℕ) : ℕ → Finset ℕ :=
  WellFounded.fix Nat.lt_wfRel.wf fun w rec =>
    if hlt : w < n then ∅
    else if hoob : n + C.gates.length ≤ w then ∅
    else
      let j := w - n
      if hjA : j ∈ A then {j}
      else if hjtop : isTopOr C n A j then
        ((C.gates[j]'(by omega)).inputs.filter (· < w)).toFinset.biUnion
          (fun i => if hi : i < w then rec i hi else ∅)
      else ∅

private lemma topAnds_unfold (C : Circuit) (n : ℕ) (A : Finset ℕ) (w : ℕ) :
    topAnds C n A w =
      if w < n then ∅
      else if n + C.gates.length ≤ w then ∅
      else
        let j := w - n
        if j ∈ A then {j}
        else if hjtop : isTopOr C n A j then
          ((C.gates[j]'hjtop.1).inputs.filter (· < w)).toFinset.biUnion (topAnds C n A)
        else ∅ := by
  rw [topAnds, WellFounded.fix_eq]
  split_ifs with h1 h2
  · rfl
  · rfl
  · dsimp only
    split_ifs with h3 h4
    · rfl
    · apply Finset.biUnion_congr rfl
      intro i hi
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hi
      simp [hi.2]
    · rfl

private lemma topAnds_subset_A (C : Circuit) (n : ℕ) (A : Finset ℕ) :
    ∀ w : ℕ, topAnds C n A w ⊆ A := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [topAnds_unfold]
    split_ifs with h1 h2
    · exact Finset.empty_subset _
    · exact Finset.empty_subset _
    · dsimp only
      split_ifs with h3 h4
      · exact Finset.singleton_subset_iff.mpr h3
      · intro k hk
        rcases Finset.mem_biUnion.mp hk with ⟨i, hi, hki⟩
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hi
        exact ih i hi.2 hki
      · exact Finset.empty_subset _

private lemma val_implies_unit_or_topAnds (C : Circuit) (n : ℕ) (A : Finset ℕ)
    (hM : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and) :
    ∀ w : ℕ, ∀ x : Fin n → Bool, val C n x w = true →
      (∃ u : Fin n, x u = true ∧ val C n (unitVec n u) w = true) ∨
      (∃ j ∈ topAnds C n A w, val C n x (n + j) = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro x hval
    by_cases h1 : w < n
    · left
      refine ⟨⟨w, h1⟩, ?_, ?_⟩
      · rwa [val_input C n x w h1] at hval
      · rw [val_input C n _ w h1]; simp [unitVec]
    · by_cases h2 : n + C.gates.length ≤ w
      · rw [val_oob C n x w h2] at hval; cases hval
      · have hj : w - n < C.gates.length := by omega
        have hw_eq : w = n + (w - n) := by omega
        set j := w - n
        by_cases hjA : j ∈ A
        · right
          refine ⟨j, ?_, hw_eq ▸ hval⟩
          rw [topAnds_unfold]
          simp [h1, h2, j, hjA]
        · by_cases hjtop : isTopOr C n A j
          · have hor : (C.gates[j]'hj).op = GateOp.or :=
              gate_or_of_not_mem_A C A hM hA j hj hjA
            rw [hw_eq, val_gate_or_iff C n x j hj hor] at hval
            rcases hval with ⟨i, hi_mem, hi_lt, hvali⟩
            have hi_lt' : i < w := by omega
            rcases ih i hi_lt' x hvali with ⟨u, hxu, hvalu⟩ | ⟨k, hk, hvalk⟩
            · left
              refine ⟨u, hxu, ?_⟩
              rw [hw_eq, val_gate_or_iff C n _ j hj hor]
              exact ⟨i, hi_mem, hi_lt, hvalu⟩
            · right
              refine ⟨k, ?_, hvalk⟩
              have hjA' : w - n ∉ A := hjA
              have hjtop' : isTopOr C n A (w - n) := hjtop
              rw [topAnds_unfold]
              simp only [h1, h2, ↓reduceIte]
              split_ifs
              refine Finset.mem_biUnion.mpr ⟨i, ?_, hk⟩
              simp [hi_lt']
              exact hi_mem
          · have hjbot : isBotOr C n A j := by
              refine ⟨hj, hjA, ?_⟩
              intro hex
              exact hjtop ⟨hj, hjA, hex⟩
            have hna : noAnd C n A w := by
              intro k hk hEq
              have hkj : k = j := by omega
              exact hkj ▸ hjbot
            left
            rcases (val_eq_exists_varSupp C n A hM hA w hna x).mp hval with ⟨u, hu, hxu⟩
            exact ⟨u, hxu, (Finset.mem_filter.mp hu).2⟩

end PEqualNP.Outside.L_meta_613

theorem PEqualNP.Outside.L_meta_613 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (cen : ℕ → Fin n) (A : Finset ℕ),
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool,
        (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      (∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate,
        C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      (∀ j ∈ A, ∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false = true →
        (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧ x (cen j) = true) →
      (∀ j ∈ A, ∀ i ∈ A,
        ¬ Relation.TransGen
          (fun a b : ℕ => b < a ∧ ∃ h : PEqualNP.CircuitLowerBounds.Gate,
            C.gates[a]? = some h ∧ n + b ∈ h.inputs) j i) →
      G.edgeSet.ncard + (A.image cen).card ≤ C.size + 1 := by
  classical
  open PEqualNP.Outside.L_meta_613 in
  intro n G C cen A hC4 hM hC hA hcen hflat
  have hA_sub : A ⊆ Finset.range C.gates.length := by
    intro j hjA
    rcases (hA j).mp hjA with ⟨g, hget, _⟩
    refine Finset.mem_range.mpr ?_
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hget
    cases hget
  let R := (Finset.range C.gates.length) \ A
  let R_top := R.filter (fun r => ∃ i ∈ A, Relation.TransGen (depStep C n) r i)
  let R_bot := R.filter (fun r => ¬ ∃ i ∈ A, Relation.TransGen (depStep C n) r i)
  have hR_sum : R_top.card + R_bot.card = R.card := by
    simpa [R_top, R_bot] using
      Finset.card_filter_add_card_filter_not
        (s := R) (p := fun r => ∃ i ∈ A, Relation.TransGen (depStep C n) r i)
  have hAR_sum : A.card + R.card = C.size := by
    have h1 : R.card + A.card = (Finset.range C.gates.length).card :=
      Finset.card_sdiff_add_card_eq_card hA_sub
    simp only [Finset.card_range] at h1
    change A.card + R.card = C.gates.length
    omega
  let S_top := topAnds C n A C.output
  have hStop_sub : S_top ⊆ A := topAnds_subset_A C n A C.output
  have hStop_card : S_top.card ≤ R_top.card + 1 := by
    let R_top' := R_top.image (n + ·)
    have hRtop'_card : R_top'.card = R_top.card :=
      Finset.card_image_of_injective _ (fun _ _ h => by omega)
    have hcond : ∀ w : ℕ, (topAnds C n A w).card ≤ 1 ∨
        (w ∈ R_top' ∧ ∃ a b : ℕ, a < w ∧ b < w ∧
          topAnds C n A w ⊆ topAnds C n A a ∪ topAnds C n A b) := by
      intro w
      by_cases h1 : w < n
      · left; rw [topAnds_unfold]; simp [h1]
      · by_cases h2 : n + C.gates.length ≤ w
        · left; rw [topAnds_unfold]; simp [h1, h2]
        · set j := w - n
          have hj : j < C.gates.length := by omega
          have hw_eq : w = n + j := by omega
          by_cases hjA : j ∈ A
          · left; rw [topAnds_unfold]; simp [h1, h2, j, hjA]
          · by_cases hjtop : isTopOr C n A j
            · have hsub : topAnds C n A w ⊆
                  ((C.gates[j]'hj).inputs.filter (· < w)).toFinset.biUnion (topAnds C n A) := by
                rw [topAnds_unfold]
                simp [h1, h2, j, hjA, hjtop]
              have hlen : (C.gates[j]'hj).inputs.length ≤ 2 := (hM _ (List.getElem_mem hj)).2
              rcases list_filter_two_union _ hlen w (topAnds C n A) hsub with hle1 | ⟨a, b, ha, hb, hab⟩
              · exact Or.inl hle1
              · refine Or.inr ⟨?_, a, b, ha, hb, hab⟩
                refine Finset.mem_image.mpr ⟨j, ?_, hw_eq.symm⟩
                exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hj, hjA⟩, hjtop.2.2⟩
            · left; rw [topAnds_unfold]; simp [h1, h2, j, hjA, hjtop]
    have hbound := union_card_le_gates_add_outputs R_top'.card R_top' rfl (topAnds C n A) hcond {C.output}
    simpa [S_top, hRtop'_card] using hbound
  have hleaf : ∀ j : ℕ, ∃ lw : ℕ, j ∈ A →
      noAnd C n A lw ∧
      (∀ v ∈ varSupp C n lw, G.Adj (cen j) v) ∧
      (∀ x : Fin n → Bool, val C n x (n + j) = true →
        x (cen j) = true ∧ ∃ v ∈ varSupp C n lw, x v = true) := by
    intro j
    by_cases hjA : j ∈ A
    · rcases exists_leafWire n G C cen A hM hA hcen hflat j hjA with ⟨lw, h1, h2, h3⟩
      exact ⟨lw, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hjA⟩
  choose leafWire hleafWire using hleaf
  let K := A.image cen
  let K1 := S_top.image cen
  let K0 := K \ K1
  let Sc : Fin n → Finset ℕ := fun c => S_top.filter (fun j => cen j = c)
  let Lc : Fin n → Finset (Fin n) := fun c => (Sc c).biUnion (fun j => varSupp C n (leafWire j))
  let Rc : Fin n → Finset ℕ := fun c =>
    R_bot.filter (fun r => 2 ≤ (varSupp C n (n + r)).card ∧ ∀ v ∈ varSupp C n (n + r), G.Adj c v)
  have hedge_cover : G.edgeFinset ⊆ K1.biUnion (fun c => (Lc c).image (fun v => s(c, v))) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : G.Adj u v := G.mem_edgeFinset.mp he
      let x : Fin n → Bool := fun z => decide (z = u ∨ z = v)
      have hval : val C n x C.output = true := by
        exact (hC x).mpr ⟨u, v, hadj, by simp [x], by simp [x]⟩
      rcases val_implies_unit_or_topAnds C n A hM hA C.output x hval with
        ⟨z, _, hz⟩ | ⟨j, hjS, hvalj⟩
      · exfalso
        rcases (hC (unitVec n z)).mp hz with ⟨a, b, hab, ha, hb⟩
        simp only [unitVec, decide_eq_true_eq] at ha hb
        subst ha; subst hb
        exact G.loopless.irrefl _ hab
      · have hjA : j ∈ A := hStop_sub hjS
        rcases (hleafWire j hjA).2.2 x hvalj with ⟨hcx, y, hy, hxy⟩
        have hadj_cy : G.Adj (cen j) y := (hleafWire j hjA).2.1 y hy
        simp only [x, decide_eq_true_eq] at hcx hxy
        have hmem_c : cen j ∈ K1 := Finset.mem_image.mpr ⟨j, hjS, rfl⟩
        have hmem_y : y ∈ Lc (cen j) :=
          Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjS, rfl⟩, hy⟩
        refine Finset.mem_biUnion.mpr ⟨cen j, hmem_c, Finset.mem_image.mpr ⟨y, hmem_y, ?_⟩⟩
        rcases hcx with hcu | hcv <;> rcases hxy with hyu | hyv
        · exact absurd (hcu ▸ hyu ▸ hadj_cy) (G.loopless.irrefl _)
        · rw [hcu, hyv]
        · rw [hcv, hyu, Sym2.eq_swap]
        · exact absurd (hcv ▸ hyv ▸ hadj_cy) (G.loopless.irrefl _)
  have hedge_le : G.edgeSet.ncard ≤ ∑ c ∈ K1, (Lc c).card := by
    have hncard : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
    rw [hncard]
    calc
      G.edgeFinset.card ≤ (K1.biUnion (fun c => (Lc c).image (fun v => s(c, v)))).card :=
        Finset.card_le_card hedge_cover
      _ ≤ ∑ c ∈ K1, ((Lc c).image (fun v => s(c, v))).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ K1, (Lc c).card := Finset.sum_le_sum (fun c _ => Finset.card_image_le)
  have hLc_le : ∀ c ∈ K1, (Lc c).card ≤ (Rc c).card + (Sc c).card := by
    intro c _
    let Fc : ℕ → Finset (Fin n) := fun w =>
      if noAnd C n A w ∧ ∀ v ∈ varSupp C n w, G.Adj c v then varSupp C n w else ∅
    let Rc' := (Rc c).image (n + ·)
    have hRc'_card : Rc'.card = (Rc c).card :=
      Finset.card_image_of_injective _ (fun _ _ h => by omega)
    have hcond : ∀ w : ℕ, (Fc w).card ≤ 1 ∨
        (w ∈ Rc' ∧ ∃ a b : ℕ, a < w ∧ b < w ∧ Fc w ⊆ Fc a ∪ Fc b) := by
      intro w
      by_cases hle1 : (Fc w).card ≤ 1
      · exact Or.inl hle1
      · have h2 : 2 ≤ (Fc w).card := by omega
        have hpred : noAnd C n A w ∧ ∀ v ∈ varSupp C n w, G.Adj c v := by
          by_contra hnp
          simp [Fc, hnp] at h2
        have hFc_w : Fc w = varSupp C n w :=
          ite_eq_left_iff.mpr (fun h => absurd hpred h)
        rw [hFc_w] at h2
        have hnot_lt : ¬ w < n := by
          intro hlt
          have hsub1 : varSupp C n w ⊆ {⟨w, hlt⟩} := by
            intro u hu
            simp only [varSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hu
            rw [val_input C n _ w hlt] at hu
            simp only [unitVec, decide_eq_true_eq] at hu
            simp [hu]
          have : (varSupp C n w).card ≤ 1 := le_trans (Finset.card_le_card hsub1) (by simp)
          omega
        have hnot_oob : ¬ n + C.gates.length ≤ w := by
          intro hoob
          have h0 : varSupp C n w = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro u hu
            simp [varSupp, val_oob C n _ w hoob] at hu
          simp [h0] at h2
        set r := w - n
        have hr : r < C.gates.length := by omega
        have hw_eq : w = n + r := by omega
        have hrbot : isBotOr C n A r := hpred.1 r hr hw_eq
        have hr_mem_Rc : r ∈ Rc c := by
          refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
          · exact Finset.mem_filter.mpr
              ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hr, hrbot.2.1⟩, hrbot.2.2⟩
          · exact hw_eq ▸ h2
          · exact hw_eq ▸ hpred.2
        have hsub_bi : Fc w ⊆ ((C.gates[r]'hr).inputs.filter (· < w)).toFinset.biUnion Fc := by
          intro u hu
          rw [hFc_w, hw_eq] at hu
          have hbi := varSupp_botOr_subset C n A hM hA r hrbot hu
          rcases Finset.mem_biUnion.mp hbi with ⟨i, hi, hui⟩
          simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hi
          have hi_na : noAnd C n A i := noAnd_of_input_of_botOr C n A r hrbot i hi.1 hi.2
          have hi_adj : ∀ v ∈ varSupp C n i, G.Adj c v := by
            intro v hv
            exact hpred.2 v (hw_eq.symm ▸ varSupp_subset_of_input_botOr C n A hM hA r hrbot i hi.1 hi.2 hv)
          refine Finset.mem_biUnion.mpr ⟨i, ?_, ?_⟩
          · simp [hi.1, hw_eq, hi.2]
          · dsimp only [Fc]
            rw [ite_eq_left_iff.mpr (fun h => absurd ⟨hi_na, hi_adj⟩ h)]
            exact hui
        have hlen : (C.gates[r]'hr).inputs.length ≤ 2 := (hM _ (List.getElem_mem hr)).2
        rcases list_filter_two_union _ hlen w Fc hsub_bi with h1 | ⟨a, b, ha, hb, hab⟩
        · exact absurd h1 hle1
        · exact Or.inr ⟨Finset.mem_image.mpr ⟨r, hr_mem_Rc, hw_eq.symm⟩, a, b, ha, hb, hab⟩
    let U := (Sc c).image leafWire
    have hLc_sub : Lc c ⊆ U.biUnion Fc := by
      intro v hv
      rcases Finset.mem_biUnion.mp hv with ⟨j, hjSc, hvj⟩
      have hjS : j ∈ S_top := (Finset.mem_filter.mp hjSc).1
      have hcj : cen j = c := (Finset.mem_filter.mp hjSc).2
      have hjA : j ∈ A := hStop_sub hjS
      have hlw_na : noAnd C n A (leafWire j) := (hleafWire j hjA).1
      have hlw_adj : ∀ y ∈ varSupp C n (leafWire j), G.Adj c y := by
        simpa [hcj] using (hleafWire j hjA).2.1
      refine Finset.mem_biUnion.mpr ⟨leafWire j, Finset.mem_image_of_mem _ hjSc, ?_⟩
      dsimp only [Fc]
      rw [ite_eq_left_iff.mpr (fun h => absurd ⟨hlw_na, hlw_adj⟩ h)]
      exact hvj
    have hbound := union_card_le_gates_add_outputs Rc'.card Rc' rfl Fc hcond U
    have hUcard : U.card ≤ (Sc c).card := Finset.card_image_le
    calc
      (Lc c).card ≤ (U.biUnion Fc).card := Finset.card_le_card hLc_sub
      _ ≤ Rc'.card + U.card := hbound
      _ ≤ (Rc c).card + (Sc c).card := by omega
  have hRc_disj : Set.PairwiseDisjoint (K1 : Set (Fin n)) Rc := by
    intro c1 _ c2 _ hne
    change Disjoint (Rc c1) (Rc c2)
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    have h1 := (Finset.mem_filter.mp hr1).2
    have h2 := (Finset.mem_filter.mp hr2).2
    rcases Finset.one_lt_card.mp (by omega : 1 < (varSupp C n (n + r)).card) with ⟨v1, hv1, v2, hv2, hvne⟩
    have h11 : G.Adj c1 v1 := h1.2 v1 hv1
    have h12 : G.Adj c1 v2 := h1.2 v2 hv2
    have h21 : G.Adj c2 v1 := h2.2 v1 hv1
    have h22 : G.Adj c2 v2 := h2.2 v2 hv2
    have hc1v1 : c1 ≠ v1 := G.ne_of_adj h11
    have hc1v2 : c1 ≠ v2 := G.ne_of_adj h12
    have hv1c2 : v1 ≠ c2 := (G.ne_of_adj h21).symm
    have hc2v2 : c2 ≠ v2 := G.ne_of_adj h22
    exact hC4 c1 v1 c2 v2 hc1v1 hne hc1v2 hv1c2 hvne hc2v2 h11 h21.symm h22 h12.symm
  have hRc_sum : ∑ c ∈ K1, (Rc c).card ≤ R_bot.card := by
    rw [← Finset.card_biUnion hRc_disj]
    apply Finset.card_le_card
    intro r hr
    rcases Finset.mem_biUnion.mp hr with ⟨c, _, hrc⟩
    exact (Finset.mem_filter.mp hrc).1
  have hSc_sum : ∑ c ∈ K1, (Sc c).card = S_top.card := by
    have hpart : S_top = K1.biUnion Sc := by
      ext j
      simp only [Finset.mem_biUnion, Sc, Finset.mem_filter, K1, Finset.mem_image]
      constructor
      · intro hj; exact ⟨cen j, ⟨j, hj, rfl⟩, hj, rfl⟩
      · rintro ⟨_, _, hj, _⟩; exact hj
    have hdisj : Set.PairwiseDisjoint (K1 : Set (Fin n)) Sc := by
      intro c1 _ c2 _ hne
      change Disjoint (Sc c1) (Sc c2)
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      exact hne ((Finset.mem_filter.mp hj1).2.symm.trans (Finset.mem_filter.mp hj2).2)
    rw [← Finset.card_biUnion hdisj, ← hpart]
  have hE_le_Rbot_Stop : G.edgeSet.ncard ≤ R_bot.card + S_top.card := by
    calc
      G.edgeSet.ncard ≤ ∑ c ∈ K1, (Lc c).card := hedge_le
      _ ≤ ∑ c ∈ K1, ((Rc c).card + (Sc c).card) := Finset.sum_le_sum hLc_le
      _ = (∑ c ∈ K1, (Rc c).card) + (∑ c ∈ K1, (Sc c).card) := Finset.sum_add_distrib
      _ ≤ R_bot.card + S_top.card := by omega
  have hK1_sub : K1 ⊆ K := Finset.image_subset_image hStop_sub
  have hK_sum : K0.card + K1.card = K.card := Finset.card_sdiff_add_card_eq_card hK1_sub
  have hK1_le : K1.card ≤ S_top.card := Finset.card_image_le
  have hK0_le : K0.card ≤ (A \ S_top).card := by
    have hsub : K0 ⊆ (A \ S_top).image cen := by
      intro c hc
      rcases Finset.mem_sdiff.mp hc with ⟨hcK, hcK1⟩
      rcases Finset.mem_image.mp hcK with ⟨j, hjA, rfl⟩
      refine Finset.mem_image.mpr ⟨j, Finset.mem_sdiff.mpr ⟨hjA, ?_⟩, rfl⟩
      intro hjS
      exact hcK1 (Finset.mem_image_of_mem cen hjS)
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
  have hAS_sum : (A \ S_top).card + S_top.card = A.card :=
    Finset.card_sdiff_add_card_eq_card hStop_sub
  change G.edgeSet.ncard + K.card ≤ C.size + 1
  omega
