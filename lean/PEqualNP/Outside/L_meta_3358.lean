import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3358

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma isNotOp_eq_true (op : GateOp) : isNotOp op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNotOp]

lemma foldl_wireStep_length (gs : List Gate) (init : List Bool) :
    (gs.foldl wireStep init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (wireStep init g)]
    simp [wireStep]
    omega

lemma getD_append_left {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right_singleton {α : Type} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some]

lemma getD_of_length_le {α : Type} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

def gateDeps (m : ℕ) (g : Gate) : Finset ℕ :=
  match g.op, g.inputs with
  | GateOp.not, [] => ∅
  | GateOp.not, a :: _ => if a < m then {a} else ∅
  | _, l => l.toFinset.filter (· < m)

lemma gateDeps_lt (m : ℕ) (g : Gate) : ∀ i ∈ gateDeps m g, i < m := by
  intro i hi
  cases hop : g.op <;> simp only [gateDeps, hop] at hi
  case not =>
    cases hin : g.inputs with
    | nil => simp [hin] at hi
    | cons a l =>
      simp only [hin] at hi
      by_cases ha : a < m
      · simp only [ha, ↓reduceIte, Finset.mem_singleton] at hi
        rw [hi]
        exact ha
      · simp only [ha, ↓reduceIte, Finset.notMem_empty] at hi
  all_goals
    exact (Finset.mem_filter.mp hi).2

lemma gateDeps_card_not (m : ℕ) (g : Gate) (hnot : g.op = GateOp.not) :
    (gateDeps m g).card ≤ 1 := by
  simp only [gateDeps, hnot]
  cases g.inputs with
  | nil => simp
  | cons a l =>
    by_cases ha : a < m
    · simp [ha]
    · simp [ha]

lemma gateDeps_card_le_two (m : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2) :
    (gateDeps m g).card ≤ 2 := by
  by_cases hnot : g.op = GateOp.not
  · exact le_trans (gateDeps_card_not m g hnot) (by decide)
  · have hsub : gateDeps m g = g.inputs.toFinset.filter (· < m) := by
      cases hop : g.op
      · simp [gateDeps, hop]
      · simp [gateDeps, hop]
      · exact (hnot hop).elim
      · simp [gateDeps, hop]
      · simp [gateDeps, hop]
    rw [hsub]
    have h1 := Finset.card_filter_le g.inputs.toFinset (· < m)
    have h2 := List.toFinset_card_le g.inputs
    omega

lemma gateDeps_eval_eq (m : ℕ) (g : Gate) (w₁ w₂ : List Bool)
    (hl₁ : w₁.length = m) (hl₂ : w₂.length = m)
    (hagree : ∀ i ∈ gateDeps m g, w₁.getD i false = w₂.getD i false) :
    g.op.eval (g.inputs.map fun i => w₁.getD i false) =
      g.op.eval (g.inputs.map fun i => w₂.getD i false) := by
  by_cases hnot : g.op = GateOp.not
  · cases hin : g.inputs with
    | nil => rfl
    | cons a l =>
      simp only [hnot, List.map_cons, GateOp.eval, List.headD_cons]
      by_cases ha : a < m
      · have hmem : a ∈ gateDeps m g := by
          simp only [gateDeps, hnot, hin, ha, ↓reduceIte, Finset.mem_singleton]
        rw [hagree a hmem]
      · have h1 := getD_of_length_le w₁ a false (by omega)
        have h2 := getD_of_length_le w₂ a false (by omega)
        rw [h1, h2]
  · have hdeps : gateDeps m g = g.inputs.toFinset.filter (· < m) := by
      cases hop : g.op <;> simp [gateDeps, hop] at hnot ⊢
    congr 1
    apply List.map_inj_left.mpr
    intro a ha
    by_cases hlt : a < m
    · have hmem : a ∈ gateDeps m g := by
        rw [hdeps, Finset.mem_filter, List.mem_toFinset]
        exact ⟨ha, hlt⟩
      exact hagree a hmem
    · rw [getD_of_length_le w₁ a false (by omega), getD_of_length_le w₂ a false (by omega)]

def stepBack (m : ℕ) (g : Gate) (S : Finset ℕ) : Finset ℕ :=
  if m ∈ S then S.erase m ∪ gateDeps m g else S

def backCone (m : ℕ) : List Gate → Finset ℕ → Finset ℕ
  | [], S => S
  | g :: gs, S => stepBack m g (backCone (m + 1) gs S)

lemma backCone_lt : ∀ (gs : List Gate) (m : ℕ) (S : Finset ℕ),
    (∀ i ∈ S, i < m + gs.length) → ∀ i ∈ backCone m gs S, i < m := by
  intro gs
  induction gs with
  | nil =>
    intro m S hS i hi
    simpa [backCone] using hS i hi
  | cons g gs ih =>
    intro m S hS i hi
    have hS' : ∀ k ∈ S, k < (m + 1) + gs.length := by
      intro k hk
      have := hS k hk
      simp only [List.length_cons] at this
      omega
    have ih_res := ih (m + 1) S hS'
    dsimp only [backCone, stepBack] at hi
    by_cases hm : m ∈ backCone (m + 1) gs S
    · simp only [hm, ↓reduceIte, Finset.mem_union, Finset.mem_erase] at hi
      rcases hi with ⟨hne, hmem⟩ | hdep
      · have := ih_res i hmem
        omega
      · exact gateDeps_lt m g i hdep
    · simp only [hm, ↓reduceIte] at hi
      have hne : i ≠ m := fun h => hm (h ▸ hi)
      have := ih_res i hi
      omega

lemma backCone_card : ∀ (gs : List Gate) (m : ℕ) (S : Finset ℕ),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (backCone m gs S).card ≤ S.card + gs.countP (fun g => !isNotOp g.op) := by
  intro gs
  induction gs with
  | nil =>
    intro m S _
    simp [backCone]
  | cons g gs ih =>
    intro m S hlen
    have hg_len : g.inputs.length ≤ 2 := hlen g (List.mem_cons_self)
    have hgs_len : ∀ g' ∈ gs, g'.inputs.length ≤ 2 :=
      fun g' hg' => hlen g' (List.mem_cons_of_mem g hg')
    have ih_res := ih (m + 1) S hgs_len
    dsimp only [backCone]
    set S₁ := backCone (m + 1) gs S
    dsimp only [stepBack]
    by_cases hm : m ∈ S₁
    · simp only [hm, ↓reduceIte]
      have herase : (S₁.erase m).card + 1 = S₁.card :=
        Finset.card_erase_add_one hm
      have hunion := Finset.card_union_le (S₁.erase m) (gateDeps m g)
      by_cases hnot : isNotOp g.op = true
      · have hcd := gateDeps_card_not m g ((isNotOp_eq_true g.op).mp hnot)
        have hcp : (g :: gs).countP (fun x => !isNotOp x.op) =
            gs.countP (fun x => !isNotOp x.op) := by
          simp [hnot]
        omega
      · have hcd := gateDeps_card_le_two m g hg_len
        have hfalse : isNotOp g.op = false := Bool.eq_false_iff.mpr hnot
        have hcp : (g :: gs).countP (fun x => !isNotOp x.op) =
            gs.countP (fun x => !isNotOp x.op) + 1 := by
          simp [hfalse]
        omega
    · simp only [hm, ↓reduceIte]
      have hcp : gs.countP (fun x => !isNotOp x.op) ≤
          (g :: gs).countP (fun x => !isNotOp x.op) := by
        rw [List.countP_cons]
        split <;> omega
      omega

lemma backCone_sim : ∀ (gs : List Gate) (m : ℕ) (S : Finset ℕ) (w₁ w₂ : List Bool),
    w₁.length = m → w₂.length = m →
    (∀ i ∈ S, i < m + gs.length) →
    (∀ i ∈ backCone m gs S, w₁.getD i false = w₂.getD i false) →
    ∀ i ∈ S, (gs.foldl wireStep w₁).getD i false = (gs.foldl wireStep w₂).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro m S w₁ w₂ _ _ _ hagree i hi
    exact hagree i hi
  | cons g gs ih =>
    intro m S w₁ w₂ hw₁ hw₂ hS hagree i hi
    simp only [List.foldl_cons]
    have hS' : ∀ k ∈ S, k < (m + 1) + gs.length := by
      intro k hk
      have := hS k hk
      simp only [List.length_cons] at this
      omega
    set S₁ := backCone (m + 1) gs S
    have hS₁_lt : ∀ k ∈ S₁, k < m + 1 := backCone_lt gs (m + 1) S hS'
    have hstep_len₁ : (wireStep w₁ g).length = m + 1 := by
      simp [wireStep, hw₁]
    have hstep_len₂ : (wireStep w₂ g).length = m + 1 := by
      simp [wireStep, hw₂]
    have hstep_agree : ∀ k ∈ S₁, (wireStep w₁ g).getD k false = (wireStep w₂ g).getD k false := by
      intro k hk
      have hklt : k < m + 1 := hS₁_lt k hk
      by_cases hkm : k < m
      · have hk_mem : k ∈ stepBack m g S₁ := by
          dsimp only [stepBack]
          by_cases hm : m ∈ S₁
          · simp only [hm, ↓reduceIte, Finset.mem_union, Finset.mem_erase]
            left
            exact ⟨by omega, hk⟩
          · simp only [hm, ↓reduceIte]
            exact hk
        dsimp only [wireStep]
        rw [getD_append_left w₁ _ k false (by omega), getD_append_left w₂ _ k false (by omega)]
        exact hagree k hk_mem
      · have hkeq : k = m := by omega
        rw [hkeq] at hk
        rw [hkeq]
        have hdep_agree : ∀ d ∈ gateDeps m g, w₁.getD d false = w₂.getD d false := by
          intro d hd
          have hd_mem : d ∈ stepBack m g S₁ := by
            dsimp only [stepBack]
            simp only [hk, ↓reduceIte, Finset.mem_union]
            exact Or.inr hd
          exact hagree d hd_mem
        have hev := gateDeps_eval_eq m g w₁ w₂ hw₁ hw₂ hdep_agree
        have h₁ := getD_append_right_singleton w₁
          (g.op.eval (g.inputs.map fun i => w₁.getD i false)) false
        have h₂ := getD_append_right_singleton w₂
          (g.op.eval (g.inputs.map fun i => w₂.getD i false)) false
        rw [hw₁] at h₁
        rw [hw₂] at h₂
        dsimp only [wireStep]
        rw [h₁, h₂]
        exact hev
    exact ih (m + 1) S (wireStep w₁ g) (wireStep w₂ g) hstep_len₁ hstep_len₂ hS' hstep_agree i hi

lemma one_of_mem_countP (l : List Gate) (p : Gate → Bool) (i : Fin l.length)
    (hi : p (l.get i) = true) : 1 ≤ l.countP p := by
  induction l with
  | nil => exact i.elim0
  | cons a as ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero] at hi
      simp only [List.countP_cons, hi, ↓reduceIte]
      omega
    | succ i' =>
      simp only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ] at hi
      have h1 := ih i' hi
      simp only [List.countP_cons]
      split <;> omega

lemma two_of_lt_countP (l : List Gate) (p : Gate → Bool) (i j : Fin l.length) (hij : i < j)
    (hi : p (l.get i) = true) (hj : p (l.get j) = true) : 2 ≤ l.countP p := by
  induction l with
  | nil => exact i.elim0
  | cons a as ih =>
    cases i using Fin.cases with
    | zero =>
      simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero] at hi
      cases j using Fin.cases with
      | zero => exact absurd hij (Nat.lt_irrefl 0)
      | succ j' =>
        simp only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ] at hj
        have h1 := one_of_mem_countP as p j' hj
        simp only [List.countP_cons, hi, ↓reduceIte]
        omega
    | succ i' =>
      cases j using Fin.cases with
      | zero =>
        exfalso
        exact Nat.not_lt_zero _ hij
      | succ j' =>
        simp only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ] at hi hj
        have hlt : i' < j' := by
          change i'.val < j'.val
          have hij' : i'.val + 1 < j'.val + 1 := hij
          omega
        have h2 := ih i' j' hlt hi hj
        simp only [List.countP_cons]
        split <;> omega

lemma countP_not_split (gs : List Gate) :
    gs.countP (fun g => !isNotOp g.op) +
      gs.countP (fun g => isNotOp g.op) = gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    by_cases h : isNotOp g.op = true
    · simp [h]
      omega
    · have hfalse : isNotOp g.op = false := Bool.eq_false_iff.mpr h
      simp [hfalse]
      omega

lemma solve (C : Circuit) (hf : FanInTwo C) (hsz : C.size ≤ 7)
    (i j : Fin C.gates.length) (hij : i < j)
    (hi : (C.gates.get i).op = GateOp.not) (hj : (C.gates.get j).op = GateOp.not) :
    ∃ S ⊆ Finset.range 17, S.card ≤ 6 ∧
      ∀ x₁ x₂ : List Bool, x₁.length = 17 → x₂.length = 17 →
        (∀ a ∈ S, x₁.getD a false = x₂.getD a false) → C.eval x₁ = C.eval x₂ := by
  let Send : Finset ℕ := if C.output < 17 + C.gates.length then {C.output} else ∅
  let S := backCone 17 C.gates Send
  have hSend_lt : ∀ k ∈ Send, k < 17 + C.gates.length := by
    intro k hk
    dsimp only [Send] at hk
    split_ifs at hk with hout
    · rw [Finset.mem_singleton.mp hk]
      exact hout
    · simp at hk
  have hSend_card : Send.card ≤ 1 := by
    dsimp only [Send]
    split_ifs <;> simp
  have hS_lt : ∀ k ∈ S, k < 17 := backCone_lt C.gates 17 Send hSend_lt
  have hS_sub : S ⊆ Finset.range 17 := by
    intro k hk
    exact Finset.mem_range.mpr (hS_lt k hk)
  have hlen2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2 :=
    fun g hg => (hf g hg).2
  have hS_card1 := backCone_card C.gates 17 Send hlen2
  have h2not : 2 ≤ C.gates.countP (fun g => isNotOp g.op) :=
    two_of_lt_countP C.gates (fun g => isNotOp g.op) i j hij
      ((isNotOp_eq_true _).mpr hi) ((isNotOp_eq_true _).mpr hj)
  have hsplit := countP_not_split C.gates
  have hglen : C.gates.length ≤ 7 := hsz
  have hS_card : S.card ≤ 6 := by
    change (backCone 17 C.gates Send).card ≤ 6
    omega
  refine ⟨S, hS_sub, hS_card, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hagree
  by_cases hout : C.output < 17 + C.gates.length
  · have hout_mem : C.output ∈ Send := by
      simp [Send, hout]
    exact backCone_sim C.gates 17 Send x₁ x₂ hx₁ hx₂ hSend_lt hagree C.output hout_mem
  · have hlen_wires₁ : (C.wires x₁).length = 17 + C.gates.length := by
      change (C.gates.foldl wireStep x₁).length = 17 + C.gates.length
      rw [foldl_wireStep_length, hx₁]
    have hlen_wires₂ : (C.wires x₂).length = 17 + C.gates.length := by
      change (C.gates.foldl wireStep x₂).length = 17 + C.gates.length
      rw [foldl_wireStep_length, hx₂]
    dsimp only [Circuit.eval]
    rw [getD_of_length_le (C.wires x₁) C.output false (by omega),
      getD_of_length_le (C.wires x₂) C.output false (by omega)]

end PEqualNP.Outside.L_meta_3358

theorem PEqualNP.Outside.L_meta_3358 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (7 : ℕ) → ∀ (x4 x5 : Fin x1.gates.length), x4 < x5 → (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ x9 ⊆ Finset.range (17 : ℕ), x9.card ≤ (6 : ℕ) ∧ ∀ (x10 x11 : List Bool), x10.length = (17 : ℕ) → x11.length = (17 : ℕ) → (∀ x14 ∈ x9, x10.getD x14 Bool.false = x11.getD x14 Bool.false) → x1.eval x10 = x1.eval x11 := by
  exact PEqualNP.Outside.L_meta_3358.solve
