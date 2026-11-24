import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1619

open PEqualNP.CircuitLowerBounds

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def evalW (gs : List Gate) (w : ℕ) (x : Fin 13 → Bool) : Bool :=
  (wiresOf gs (List.ofFn x)).getD w false

def ept (u : Fin 13) : Fin 13 → Bool :=
  fun k => decide (k = u)

def S (gs : List Gate) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun u : Fin 13 => evalW gs w (ept u) = true)

def Lset (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (l : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun p : Fin 13 => I p l)

lemma wiresOf_nil (x : List Bool) : wiresOf [] x = x := rfl

lemma wiresOf_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wiresOf (g :: gs) x =
      wiresOf gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  simp [wiresOf, List.foldl_append]

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g gs ih =>
    rw [wiresOf_cons, ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (wiresOf gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresOf_cons, ih]
    · exact getD_append_left x _ i false hi
    · simp; omega

lemma evalW_input (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) (hw : w < 13) :
    evalW gs w x = x ⟨w, hw⟩ := by
  dsimp only [evalW]
  rw [wiresOf_getD_lt]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]
  · simp [hw]

lemma evalW_ge_len (gs : List Gate) (x : Fin 13 → Bool) (w : ℕ) (hw : 13 + gs.length ≤ w) :
    evalW gs w x = false := by
  dsimp only [evalW]
  have hlen : (wiresOf gs (List.ofFn x)).length = 13 + gs.length := by
    rw [wiresOf_length, List.length_ofFn]
  have hge : (wiresOf gs (List.ofFn x)).length ≤ w := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]

lemma evalW_gate (gs : List Gate) (x : Fin 13 → Bool) (j : Fin gs.length) :
    evalW gs (13 + (j : ℕ)) x =
      (gs.get j).op.eval
        ((gs.get j).inputs.map fun i => if i < 13 + (j : ℕ) then evalW gs i x else false) := by
  have hsplit : gs = gs.take (j : ℕ) ++ [gs.get j] ++ gs.drop ((j : ℕ) + 1) := by
    have h1 := (List.take_append_drop (j : ℕ) gs).symm
    have h2 : gs.drop (j : ℕ) = gs.get j :: gs.drop ((j : ℕ) + 1) := by
      rw [← List.getElem_cons_drop j.isLt]
      rfl
    exact h1.trans (by rw [h2]; simp)
  set p := gs.take (j : ℕ)
  set g := gs.get j
  set q := gs.drop ((j : ℕ) + 1)
  have hplen : p.length = (j : ℕ) := List.length_take_of_le (Nat.le_of_lt j.isLt)
  have hwp_len : (wiresOf p (List.ofFn x)).length = 13 + (j : ℕ) := by
    rw [wiresOf_length, List.length_ofFn, hplen]
  have hprefix_eq : ∀ i, i < 13 + (j : ℕ) →
      (wiresOf p (List.ofFn x)).getD i false = (wiresOf gs (List.ofFn x)).getD i false := by
    intro i hi
    have hw_eq : wiresOf gs (List.ofFn x) = wiresOf ([g] ++ q) (wiresOf p (List.ofFn x)) := by
      rw [← wiresOf_append, ← List.append_assoc, ← hsplit]
    rw [hw_eq]
    exact (wiresOf_getD_lt ([g] ++ q) (wiresOf p (List.ofFn x)) i (by omega)).symm
  have hmap : (g.inputs.map fun i => (wiresOf p (List.ofFn x)).getD i false) =
      (g.inputs.map fun i => if i < 13 + (j : ℕ) then evalW gs i x else false) := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < 13 + (j : ℕ)
    · simp only [hi, ↓reduceIte, evalW]
      exact hprefix_eq i hi
    · simp only [hi, ↓reduceIte]
      have hge : (wiresOf p (List.ofFn x)).length ≤ i := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
  have hw_eq : wiresOf gs (List.ofFn x) = wiresOf q (wiresOf [g] (wiresOf p (List.ofFn x))) := by
    rw [← wiresOf_append, ← wiresOf_append, ← List.append_assoc, ← hsplit]
  change (wiresOf gs (List.ofFn x)).getD (13 + (j : ℕ)) false = _
  rw [hw_eq, wiresOf_getD_lt q]
  · rw [wiresOf_cons, wiresOf_nil]
    rw [getD_append_right (wiresOf p (List.ofFn x)) _ (13 + (j : ℕ)) false (by omega)]
    rw [hwp_len, Nat.sub_self, hmap]
    rfl
  · rw [wiresOf_cons, wiresOf_nil, List.length_append, hwp_len]
    simp

lemma card_S_lt_13 (gs : List Gate) (w : ℕ) (hw : w < 13) : (S gs w).card = 1 := by
  have heq : S gs w = {⟨w, hw⟩} := by
    ext u
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [evalW_input gs (ept u) w hw]
    simp only [ept, decide_eq_true_eq]
    exact eq_comm
  rw [heq, Finset.card_singleton]

lemma card_S_ge_len (gs : List Gate) (w : ℕ) (hw : 13 + gs.length ≤ w) : (S gs w).card = 0 := by
  have heq : S gs w = ∅ := by
    ext u
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rw [evalW_ge_len gs (ept u) w hw]
    decide
  rw [heq, Finset.card_empty]

-- Plane geometry helpers

lemma line_eq_of_subset_ge2 (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (huniq : ∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1)
    (A : Finset (Fin 13)) (hA : 2 ≤ A.card) (l1 l2 : Fin 13)
    (h1 : A ⊆ Lset I l1) (h2 : A ⊆ Lset I l2) : l1 = l2 := by
  have hlt : 1 < A.card := by omega
  obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.mp hlt
  obtain ⟨l, _, hlu⟩ := huniq p1 p2 hne
  have hl1 : I p1 l1 ∧ I p2 l1 := by
    have m1 := h1 hp1; have m2 := h1 hp2
    simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and] at m1 m2
    exact ⟨m1, m2⟩
  have hl2 : I p1 l2 ∧ I p2 l2 := by
    have m1 := h2 hp1; have m2 := h2 hp2
    simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and] at m1 m2
    exact ⟨m1, m2⟩
  exact (hlu l1 hl1).trans (hlu l2 hl2).symm

lemma inter_lines_le_one (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (huniq : ∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1)
    (l1 l2 : Fin 13) (hne : l1 ≠ l2) : (Lset I l1 ∩ Lset I l2).card ≤ 1 := by
  by_contra h
  have h2 : 2 ≤ (Lset I l1 ∩ Lset I l2).card := by omega
  have heq := line_eq_of_subset_ge2 I huniq (Lset I l1 ∩ Lset I l2) h2 l1 l2
    Finset.inter_subset_left Finset.inter_subset_right
  exact hne heq

lemma union_three_lines_ge_nine (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (hcard4 : ∀ l : Fin 13, (Lset I l).card = 4)
    (huniq : ∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1)
    (l1 l2 l3 : Fin 13) (h12 : l1 ≠ l2) (h13 : l1 ≠ l3) (h23 : l2 ≠ l3) :
    9 ≤ (Lset I l1 ∪ Lset I l2 ∪ Lset I l3).card := by
  have hu12 : 7 ≤ (Lset I l1 ∪ Lset I l2).card := by
    have h1 := Finset.card_union_add_card_inter (Lset I l1) (Lset I l2)
    have hi := inter_lines_le_one I huniq l1 l2 h12
    rw [hcard4 l1, hcard4 l2] at h1
    omega
  have hi3 : ((Lset I l1 ∪ Lset I l2) ∩ Lset I l3).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    have h1 := Finset.card_union_le (Lset I l1 ∩ Lset I l3) (Lset I l2 ∩ Lset I l3)
    have ha := inter_lines_le_one I huniq l1 l3 h13
    have hb := inter_lines_le_one I huniq l2 l3 h23
    omega
  have h2 := Finset.card_union_add_card_inter (Lset I l1 ∪ Lset I l2) (Lset I l3)
  rw [hcard4 l3] at h2
  omega

-- Main proof

lemma main_proof
    (I : Fin 13 → Fin 13 → Prop) [DecidableRel I]
    (gates : List Gate) (out : Fin 13 → ℕ)
    (hcard4 : ∀ l0 : Fin 13, (Finset.univ.filter (fun p0 : Fin 13 => I p0 l0)).card = 4)
    (huniq : ∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1)
    (hgs : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hout : ∀ (l2 u2 : Fin 13),
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin 13 => decide (u2k = u2)))).getD (out l2) false = true ↔ I u2 l2)
    (B : Finset (Fin 13)) (H : Finset (Fin gates.length))
    (hH : ∀ k5 ∈ H,
      2 ≤ (Finset.univ.filter (fun u5 : Fin 13 =>
        (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u5k : Fin 13 => decide (u5k = u5)))).getD (13 + k5.val) false = true)).card ∧
      ∃ l4 : Fin 13, l4 ∉ B ∧ ∀ u6 : Fin 13,
        (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u6k : Fin 13 => decide (u6k = u6)))).getD (13 + k5.val) false = true → I u6 l4) :
    3 * B.card + 2 * H.card ≤ 2 * gates.length := by
  have hcard4 : ∀ l : Fin 13, (Lset I l).card = 4 := hcard4
  have hS_out : ∀ l : Fin 13, S gates (out l) = Lset I l := by
    intro l
    ext u
    simp only [S, Lset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hout l u
  have hexW : ∀ b : Fin 13, ∃ w : ℕ, S gates w = Lset I b := fun b => ⟨out b, hS_out b⟩
  let wMin : Fin 13 → ℕ := fun b => Nat.find (hexW b)
  have hwMin_eq : ∀ b : Fin 13, S gates (wMin b) = Lset I b := fun b => Nat.find_spec (hexW b)
  have hwMin_min : ∀ b : Fin 13, ∀ w < wMin b, S gates w ≠ Lset I b :=
    fun b w hw => Nat.find_min (hexW b) hw
  have hwMin_ge13 : ∀ b : Fin 13, 13 ≤ wMin b := by
    intro b
    by_contra h
    have h1 := card_S_lt_13 gates (wMin b) (by omega)
    rw [hwMin_eq b, hcard4 b] at h1
    omega
  have hwMin_lt : ∀ b : Fin 13, wMin b < 13 + gates.length := by
    intro b
    by_contra h
    have h0 := card_S_ge_len gates (wMin b) (by omega)
    rw [hwMin_eq b, hcard4 b] at h0
    omega
  let jMin : Fin 13 → Fin gates.length := fun b =>
    ⟨wMin b - 13, by have := hwMin_lt b; have := hwMin_ge13 b; omega⟩
  have hjMin_eq : ∀ b : Fin 13, 13 + (jMin b : ℕ) = wMin b := by
    intro b; dsimp [jMin]; have := hwMin_ge13 b; omega
  have hjMin_S : ∀ b : Fin 13, S gates (13 + (jMin b : ℕ)) = Lset I b := by
    intro b; rw [hjMin_eq b]; exact hwMin_eq b
  have hjMin_inj : ∀ b1 b2 : Fin 13, jMin b1 = jMin b2 → b1 = b2 := by
    intro b1 b2 heq
    have hS : Lset I b1 = Lset I b2 := by
      rw [← hjMin_S b1, heq, hjMin_S b2]
    exact line_eq_of_subset_ge2 I huniq (Lset I b1) (by rw [hcard4 b1]; omega) b1 b2
      (Finset.Subset.refl _) (by rw [hS])
  have hjMin_notH : ∀ b ∈ B, jMin b ∉ H := by
    intro b hb hmem
    obtain ⟨_, l4, hl4notB, hl4sub⟩ := hH (jMin b) hmem
    have hsub : Lset I b ⊆ Lset I l4 := by
      intro u hu
      rw [← hjMin_S b] at hu
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hl4sub u hu
    have heq := line_eq_of_subset_ge2 I huniq (Lset I b) (by rw [hcard4 b]; omega) b l4
      (Finset.Subset.refl _) hsub
    subst heq
    exact hl4notB hb
  let OB : Finset (Fin gates.length) := B.image jMin
  have hOB_card : OB.card = B.card :=
    Finset.card_image_of_injective B (fun a b h => hjMin_inj a b h)
  have hOB_disj_H : Disjoint OB H := by
    rw [Finset.disjoint_left]
    intro g hgOB hgH
    rw [Finset.mem_image] at hgOB
    obtain ⟨b, hbB, rfl⟩ := hgOB
    exact hjMin_notH b hbB hgH
  let R : Finset (Fin gates.length) := Finset.univ \ H
  have hOB_sub_R : OB ⊆ R := by
    intro g hg
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ g, Finset.disjoint_left.mp hOB_disj_H hg⟩
  let Rest : Finset (Fin gates.length) := R \ OB
  -- For each b ∈ B, find a helper gate g ∈ Rest witnessing either:
  --   (a) 2 ≤ |S g| ≤ 3 ∧ S g ⊆ Lset I b, OR
  --   (b) 5 ≤ |S g| ≤ 8 ∧ Lset I b ⊆ S g.
  have hexHelper : ∀ b ∈ B, ∃ g ∈ Rest,
      (2 ≤ (S gates (13 + (g : ℕ))).card ∧ (S gates (13 + (g : ℕ))).card ≤ 3 ∧
        S gates (13 + (g : ℕ)) ⊆ Lset I b) ∨
      (5 ≤ (S gates (13 + (g : ℕ))).card ∧ (S gates (13 + (g : ℕ))).card ≤ 8 ∧
        Lset I b ⊆ S gates (13 + (g : ℕ))) := by
    intro b hbB
    let jb := jMin b
    have hjb_eq : 13 + (jb : ℕ) = wMin b := hjMin_eq b
    have hjb_S : S gates (13 + (jb : ℕ)) = Lset I b := hjMin_S b
    have hjb_len : (gates.get jb).inputs.length ≤ 2 := (hgs _ (List.get_mem gates jb)).2
    have hnotOB_of_ne4 : ∀ g : Fin gates.length, (S gates (13 + (g : ℕ))).card ≠ 4 → g ∉ OB := by
      intro g hne hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨b', _, rfl⟩ := hmem
      rw [hjMin_S b', hcard4 b'] at hne
      exact hne rfl
    rcases (hgs _ (List.get_mem gates jb)).1 with hand | hor
    · -- AND gate: inputs must be [u, v] with |S u| ≥ 5, |S v| ≥ 5, and one has |S| ≤ 8!
      cases hinp : (gates.get jb).inputs with
      | nil =>
        exfalso
        have hall : S gates (13 + (jb : ℕ)) = Finset.univ := by
          ext u
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          rw [evalW_gate gates (ept u) jb, hand, hinp]
          simp [GateOp.eval]
        have h13 : (S gates (13 + (jb : ℕ))).card = 13 := by rw [hall]; simp
        rw [hjb_S, hcard4 b] at h13
        omega
      | cons u rest =>
        cases rest with
        | nil =>
          exfalso
          have hu_lt : u < 13 + (jb : ℕ) := by
            by_contra h
            have hemp : S gates (13 + (jb : ℕ)) = ∅ := by
              ext x
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
              rw [evalW_gate gates (ept x) jb, hand, hinp]
              simp [GateOp.eval, h]
            have h0 : (S gates (13 + (jb : ℕ))).card = 0 := by rw [hemp]; simp
            rw [hjb_S, hcard4 b] at h0
            omega
          have hSu : S gates u = Lset I b := by
            rw [← hjb_S]
            ext x
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [evalW_gate gates (ept x) jb, hand, hinp]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, hu_lt, ↓reduceIte]
          exact hwMin_min b u (by omega) hSu
        | cons v rest2 =>
          cases rest2 with
          | nil =>
            have hne_L : (Lset I b).Nonempty := Finset.card_pos.mp (by rw [hcard4 b]; omega)
            obtain ⟨x0, hx0⟩ := hne_L
            have hx0_eval : evalW gates (13 + (jb : ℕ)) (ept x0) = true := by
              rw [← hjb_S] at hx0
              exact (Finset.mem_filter.mp hx0).2
            rw [evalW_gate gates (ept x0) jb, hand, hinp] at hx0_eval
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.and_eq_true] at hx0_eval
            have hu_lt : u < 13 + (jb : ℕ) := by by_contra h; simp [h] at hx0_eval
            have hv_lt : v < 13 + (jb : ℕ) := by by_contra h; simp [h] at hx0_eval
            have hinter : S gates u ∩ S gates v = Lset I b := by
              rw [← hjb_S]
              ext x
              simp only [Finset.mem_inter, S, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [evalW_gate gates (ept x) jb, hand, hinp]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, hu_lt, hv_lt, ↓reduceIte, Bool.and_eq_true]
            have hsub_u : Lset I b ⊆ S gates u := by rw [← hinter]; exact Finset.inter_subset_left
            have hsub_v : Lset I b ⊆ S gates v := by rw [← hinter]; exact Finset.inter_subset_right
            have hne_u : S gates u ≠ Lset I b := hwMin_min b u (by omega)
            have hne_v : S gates v ≠ Lset I b := hwMin_min b v (by omega)
            have hcu_ge5 : 5 ≤ (S gates u).card := by
              have hge4 : 4 ≤ (S gates u).card := by
                rw [← hcard4 b]; exact Finset.card_le_card hsub_u
              by_contra h
              have heq4 : (S gates u).card = 4 := by omega
              exact hne_u (Finset.eq_of_subset_of_card_le hsub_u (by rw [hcard4 b, heq4])).symm
            have hcv_ge5 : 5 ≤ (S gates v).card := by
              have hge4 : 4 ≤ (S gates v).card := by
                rw [← hcard4 b]; exact Finset.card_le_card hsub_v
              by_contra h
              have heq4 : (S gates v).card = 4 := by omega
              exact hne_v (Finset.eq_of_subset_of_card_le hsub_v (by rw [hcard4 b, heq4])).symm
            have hsum_le17 : (S gates u).card + (S gates v).card ≤ 17 := by
              have h1 := Finset.card_union_add_card_inter (S gates u) (S gates v)
              rw [hinter, hcard4 b] at h1
              have h13 : (S gates u ∪ S gates v).card ≤ 13 := by
                calc (S gates u ∪ S gates v).card ≤ (Finset.univ : Finset (Fin 13)).card :=
                      Finset.card_le_card (Finset.subset_univ _)
                  _ = 13 := by simp
              omega
            have mk_and_helper : ∀ w : ℕ, w < 13 + (jb : ℕ) →
                5 ≤ (S gates w).card → (S gates w).card ≤ 8 → Lset I b ⊆ S gates w →
                ∃ g ∈ Rest,
                  (2 ≤ (S gates (13 + (g : ℕ))).card ∧ (S gates (13 + (g : ℕ))).card ≤ 3 ∧
                    S gates (13 + (g : ℕ)) ⊆ Lset I b) ∨
                  (5 ≤ (S gates (13 + (g : ℕ))).card ∧ (S gates (13 + (g : ℕ))).card ≤ 8 ∧
                    Lset I b ⊆ S gates (13 + (g : ℕ))) := by
              intro w hwlt hge5 hle8 hsub
              have hw13 : 13 ≤ w := by
                by_contra h; have := card_S_lt_13 gates w (by omega); omega
              let g : Fin gates.length := ⟨w - 13, by omega⟩
              have hgeq : 13 + (g : ℕ) = w := by dsimp [g]; omega
              have hg_notH : g ∉ H := by
                intro hmem
                obtain ⟨_, l4, _, hl4sub⟩ := hH g hmem
                have hsub4 : S gates w ⊆ Lset I l4 := by
                  intro x hx
                  rw [← hgeq] at hx
                  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
                  simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and]
                  exact hl4sub x hx
                have hle4 : (S gates w).card ≤ 4 := by
                  rw [← hcard4 l4]; exact Finset.card_le_card hsub4
                omega
              have hg_notOB : g ∉ OB := hnotOB_of_ne4 g (by rw [hgeq]; omega)
              have hg_Rest : g ∈ Rest := by
                simp only [Rest, R, Finset.mem_sdiff, Finset.mem_univ, true_and]
                exact ⟨hg_notH, hg_notOB⟩
              exact ⟨g, hg_Rest, Or.inr ⟨by rw [hgeq]; exact hge5, by rw [hgeq]; exact hle8, by rw [hgeq]; exact hsub⟩⟩
            by_cases hu8 : (S gates u).card ≤ 8
            · exact mk_and_helper u hu_lt hcu_ge5 hu8 hsub_u
            · exact mk_and_helper v hv_lt hcv_ge5 (by omega) hsub_v
          | cons _ _ =>
            rw [hinp] at hjb_len; simp at hjb_len
    · -- OR gate: inputs must be [u, v] with one having 2 ≤ |S| ≤ 3 and S ⊆ Lset I b
      have mk_or_helper : ∀ w : ℕ, w < 13 + (jb : ℕ) →
          2 ≤ (S gates w).card → (S gates w).card ≤ 3 → S gates w ⊆ Lset I b →
          ∃ g ∈ Rest,
            (2 ≤ (S gates (13 + (g : ℕ))).card ∧ (S gates (13 + (g : ℕ))).card ≤ 3 ∧
              S gates (13 + (g : ℕ)) ⊆ Lset I b) ∨
            (5 ≤ (S gates (13 + (g : ℕ))).card ∧ (S gates (13 + (g : ℕ))).card ≤ 8 ∧
              Lset I b ⊆ S gates (13 + (g : ℕ))) := by
        intro w hwlt hge2 hle3 hsub
        have hw13 : 13 ≤ w := by
          by_contra h; have := card_S_lt_13 gates w (by omega); omega
        let g : Fin gates.length := ⟨w - 13, by omega⟩
        have hgeq : 13 + (g : ℕ) = w := by dsimp [g]; omega
        have hg_notH : g ∉ H := by
          intro hmem
          obtain ⟨_, l4, hl4notB, hl4sub⟩ := hH g hmem
          have hsub4 : S gates w ⊆ Lset I l4 := by
            intro x hx
            rw [← hgeq] at hx
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hl4sub x hx
          have heq := line_eq_of_subset_ge2 I huniq (S gates w) hge2 b l4 hsub hsub4
          subst heq
          exact hl4notB hbB
        have hg_notOB : g ∉ OB := hnotOB_of_ne4 g (by rw [hgeq]; omega)
        have hg_Rest : g ∈ Rest := by
          simp only [Rest, R, Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact ⟨hg_notH, hg_notOB⟩
        exact ⟨g, hg_Rest, Or.inl ⟨by rw [hgeq]; exact hge2, by rw [hgeq]; exact hle3, by rw [hgeq]; exact hsub⟩⟩
      cases hinp : (gates.get jb).inputs with
      | nil =>
        exfalso
        have hemp : S gates (13 + (jb : ℕ)) = ∅ := by
          ext x
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rw [evalW_gate gates (ept x) jb, hor, hinp]
          simp [GateOp.eval]
        have h0 : (S gates (13 + (jb : ℕ))).card = 0 := by rw [hemp]; simp
        rw [hjb_S, hcard4 b] at h0
        omega
      | cons u rest =>
        cases rest with
        | nil =>
          exfalso
          have hu_lt : u < 13 + (jb : ℕ) := by
            by_contra h
            have hemp : S gates (13 + (jb : ℕ)) = ∅ := by
              ext x
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
              rw [evalW_gate gates (ept x) jb, hor, hinp]
              simp [GateOp.eval, h]
            have h0 : (S gates (13 + (jb : ℕ))).card = 0 := by rw [hemp]; simp
            rw [hjb_S, hcard4 b] at h0
            omega
          have hSu : S gates u = Lset I b := by
            rw [← hjb_S]
            ext x
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [evalW_gate gates (ept x) jb, hor, hinp]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, hu_lt, ↓reduceIte]
          exact hwMin_min b u (by omega) hSu
        | cons v rest2 =>
          cases rest2 with
          | nil =>
            let Su : Finset (Fin 13) := if u < 13 + (jb : ℕ) then S gates u else ∅
            let Sv : Finset (Fin 13) := if v < 13 + (jb : ℕ) then S gates v else ∅
            have hunion : Su ∪ Sv = Lset I b := by
              rw [← hjb_S]
              ext x
              simp only [Finset.mem_union, S, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [evalW_gate gates (ept x) jb, hor, hinp]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                id_eq, Bool.or_false, Bool.or_eq_true]
              constructor
              · rintro (hu | hv)
                · left
                  by_cases hlt : u < 13 + (jb : ℕ)
                  · simp only [Su, hlt, ↓reduceIte, S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
                    simp only [hlt, ↓reduceIte]; exact hu
                  · simp [Su, hlt] at hu
                · right
                  by_cases hlt : v < 13 + (jb : ℕ)
                  · simp only [Sv, hlt, ↓reduceIte, S, Finset.mem_filter, Finset.mem_univ, true_and] at hv
                    simp only [hlt, ↓reduceIte]; exact hv
                  · simp [Sv, hlt] at hv
              · rintro (hu | hv)
                · left
                  have hlt : u < 13 + (jb : ℕ) := by by_contra h; simp [h] at hu
                  simp only [hlt, ↓reduceIte] at hu
                  simp only [Su, hlt, ↓reduceIte, S, Finset.mem_filter, Finset.mem_univ, true_and]
                  exact hu
                · right
                  have hlt : v < 13 + (jb : ℕ) := by by_contra h; simp [h] at hv
                  simp only [hlt, ↓reduceIte] at hv
                  simp only [Sv, hlt, ↓reduceIte, S, Finset.mem_filter, Finset.mem_univ, true_and]
                  exact hv
            have hsum4 : 4 ≤ Su.card + Sv.card := by
              calc 4 = (Lset I b).card := (hcard4 b).symm
                _ = (Su ∪ Sv).card := by rw [hunion]
                _ ≤ Su.card + Sv.card := Finset.card_union_le Su Sv
            by_cases hu2 : 2 ≤ Su.card
            · have hult : u < 13 + (jb : ℕ) := by by_contra h; simp [Su, h] at hu2
              simp only [Su, hult, ↓reduceIte] at hu2
              have hsub : S gates u ⊆ Lset I b := by
                rw [← hunion]; intro x hx; rw [Finset.mem_union]; left
                simp only [Su, hult, ↓reduceIte]; exact hx
              have hle3 : (S gates u).card ≤ 3 := by
                have hle4 : (S gates u).card ≤ 4 := by
                  rw [← hcard4 b]; exact Finset.card_le_card hsub
                by_contra h
                have heq4 : (S gates u).card = 4 := by omega
                exact hwMin_min b u (by omega)
                  (Finset.eq_of_subset_of_card_le hsub (by rw [hcard4 b, heq4]))
              exact mk_or_helper u hult hu2 hle3 hsub
            · have hv2 : 2 ≤ Sv.card := by omega
              have hvlt : v < 13 + (jb : ℕ) := by by_contra h; simp [Sv, h] at hv2
              simp only [Sv, hvlt, ↓reduceIte] at hv2
              have hsub : S gates v ⊆ Lset I b := by
                rw [← hunion]; intro x hx; rw [Finset.mem_union]; right
                simp only [Sv, hvlt, ↓reduceIte]; exact hx
              have hle3 : (S gates v).card ≤ 3 := by
                have hle4 : (S gates v).card ≤ 4 := by
                  rw [← hcard4 b]; exact Finset.card_le_card hsub
                by_contra h
                have heq4 : (S gates v).card = 4 := by omega
                exact hwMin_min b v (by omega)
                  (Finset.eq_of_subset_of_card_le hsub (by rw [hcard4 b, heq4]))
              exact mk_or_helper v hvlt hv2 hle3 hsub
          | cons _ _ =>
            rw [hinp] at hjb_len; simp at hjb_len
  -- Choose helper φ : Fin 13 → Fin gates.length for each b ∈ B
  have hexPhi : ∀ b : Fin 13, ∃ g : Fin gates.length,
      b ∈ B → g ∈ Rest ∧
        ((2 ≤ (S gates (13 + (g : ℕ))).card ∧ (S gates (13 + (g : ℕ))).card ≤ 3 ∧
          S gates (13 + (g : ℕ)) ⊆ Lset I b) ∨
        (5 ≤ (S gates (13 + (g : ℕ))).card ∧ (S gates (13 + (g : ℕ))).card ≤ 8 ∧
          Lset I b ⊆ S gates (13 + (g : ℕ)))) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨g, hgR, hgp⟩ := hexHelper b hb
      exact ⟨g, fun _ => ⟨hgR, hgp⟩⟩
    · exact ⟨jMin 0, fun h => absurd h hb⟩
  choose φ hφ using hexPhi
  -- Every g ∈ Rest has at most 2 preimages in B under φ
  have hfiber_le2 : ∀ g ∈ Rest, (B.filter (fun b => φ b = g)).card ≤ 2 := by
    intro g _
    by_contra hgt
    have hge3 : 3 ≤ (B.filter (fun b => φ b = g)).card := by omega
    have hlt1 : 1 < (B.filter (fun b => φ b = g)).card := by omega
    obtain ⟨b1, hb1, b2, hb2, h12⟩ := Finset.one_lt_card.mp hlt1
    have hcard_er : 1 ≤ (((B.filter (fun b => φ b = g)).erase b1).erase b2).card := by
      have h1 : ((B.filter (fun b => φ b = g)).erase b1).card = (B.filter (fun b => φ b = g)).card - 1 :=
        Finset.card_erase_of_mem hb1
      have hb2_er : b2 ∈ (B.filter (fun b => φ b = g)).erase b1 :=
        Finset.mem_erase.mpr ⟨Ne.symm h12, hb2⟩
      have h2 : (((B.filter (fun b => φ b = g)).erase b1).erase b2).card =
          ((B.filter (fun b => φ b = g)).erase b1).card - 1 :=
        Finset.card_erase_of_mem hb2_er
      omega
    obtain ⟨b3, hb3_er⟩ := Finset.card_pos.mp (by omega : 0 < (((B.filter (fun b => φ b = g)).erase b1).erase b2).card)
    have h23 : b2 ≠ b3 := (Finset.mem_erase.mp hb3_er).1.symm
    have hb3_er1 := (Finset.mem_erase.mp hb3_er).2
    have h13 : b1 ≠ b3 := (Finset.mem_erase.mp hb3_er1).1.symm
    have hb3 := (Finset.mem_erase.mp hb3_er1).2
    rw [Finset.mem_filter] at hb1 hb2 hb3
    have hp1 := (hφ b1 hb1.1).2; rw [hb1.2] at hp1
    have hp2 := (hφ b2 hb2.1).2; rw [hb2.2] at hp2
    have hp3 := (hφ b3 hb3.1).2; rw [hb3.2] at hp3
    rcases hp1 with ⟨hge2, hle3, hsub1⟩ | ⟨hge5, hle8, hsub1⟩
    · rcases hp2 with ⟨_, _, hsub2⟩ | ⟨hge5', _, _⟩
      · exact h12 (line_eq_of_subset_ge2 I huniq (S gates (13 + (g : ℕ))) hge2 b1 b2 hsub1 hsub2)
      · omega
    · rcases hp2 with ⟨_, hle3', _⟩ | ⟨_, _, hsub2⟩
      · omega
      · rcases hp3 with ⟨_, hle3'', _⟩ | ⟨_, _, hsub3⟩
        · omega
        · have hunion_sub : Lset I b1 ∪ Lset I b2 ∪ Lset I b3 ⊆ S gates (13 + (g : ℕ)) := by
            intro x hx
            simp only [Finset.mem_union] at hx
            rcases hx with (h | h) | h
            · exact hsub1 h
            · exact hsub2 h
            · exact hsub3 h
          have h9 := union_three_lines_ge_nine I hcard4 huniq b1 b2 b3 h12 h13 h23
          have hle := Finset.card_le_card hunion_sub
          omega
  -- Double counting: B.card ≤ 2 * Rest.card
  have hB_le_2Rest : B.card ≤ 2 * Rest.card := by
    have hsum_eq : B.card = ∑ g ∈ Rest, (B.filter (fun b => φ b = g)).card := by
      have hmaps : ∀ b ∈ B, φ b ∈ Rest := fun b hb => (hφ b hb).1
      exact Finset.card_eq_sum_card_fiberwise hmaps
    rw [hsum_eq]
    calc ∑ g ∈ Rest, (B.filter (fun b => φ b = g)).card
        ≤ ∑ _g ∈ Rest, 2 := Finset.sum_le_sum hfiber_le2
      _ = 2 * Rest.card := by simp [mul_comm]
  have hRest_add : Rest.card + OB.card = R.card := by
    dsimp [Rest]
    exact Finset.card_sdiff_add_card_eq_card hOB_sub_R
  have hR_add : R.card + H.card = gates.length := by
    dsimp [R]
    have hsub : H ⊆ (Finset.univ : Finset (Fin gates.length)) := Finset.subset_univ H
    have h := Finset.card_sdiff_add_card_eq_card hsub
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  omega

end PEqualNP.Outside.L_meta_1619

theorem PEqualNP.Outside.L_meta_1619 :
    ∀ (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ l0 : Fin 13, (Finset.univ.filter (fun p0 : Fin 13 => I p0 l0)).card = 4) → (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (l2 u2 : Fin 13), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin 13 => decide (u2k = u2)))).getD (out l2) false = true ↔ I u2 l2) → ∀ (B : Finset (Fin 13)) (H : Finset (Fin gates.length)), (∀ k5 ∈ H, 2 ≤ (Finset.univ.filter (fun u5 : Fin 13 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u5k : Fin 13 => decide (u5k = u5)))).getD (13 + k5.val) false = true)).card ∧ ∃ l4 : Fin 13, l4 ∉ B ∧ ∀ u6 : Fin 13, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u6k : Fin 13 => decide (u6k = u6)))).getD (13 + k5.val) false = true → I u6 l4) → 3 * B.card + 2 * H.card ≤ 2 * gates.length :=
  PEqualNP.Outside.L_meta_1619.main_proof
