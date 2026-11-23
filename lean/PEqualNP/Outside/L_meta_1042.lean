import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1042

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_initial (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_initial gs w
  rw [ht]; simp [hl]

theorem initial_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_initial gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (gl : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom gl (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (gl : List Gate) (x : Fin n → Bool) (i : Fin n) :
    val gl x i.val = x i := by
  rw [val, initial_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (gl : List Gate) (x : Fin n → Bool) {i : ℕ}
    (hi : n + gl.length ≤ i) : val gl x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (gl : List Gate) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val gl x i else false

theorem val_gate {n : ℕ} (gl : List Gate) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : gl[p]? = some g) :
    val gl x (n+p) = g.op.eval (g.inputs.map (operand gl x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : gl = (gl.take p ++ [g]) ++ gl.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) gl]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (gl.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand gl x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val gl x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact initial_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand gl x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (gl.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [initial_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def pt (k : Fin 7) : Fin 6 → Bool := fun i => decide (i.val + 1 = k.val)

def T : Fin 4 → Finset (Fin 7) := ![{1, 2, 3}, {1, 4, 5}, {2, 4, 6}, {3, 5, 6}]

def sg (gl : List Gate) (i : ℕ) : Finset (Fin 7) :=
  Finset.univ.filter fun k => val gl (pt k) i = true

def osg (gl : List Gate) (j i : ℕ) : Finset (Fin 7) :=
  if i < j then sg gl i else ∅

theorem T_card : ∀ w : Fin 4, (T w).card = 3 := by decide

theorem T_compl_card : ∀ w : Fin 4, ((T w)ᶜ).card = 4 := by decide

theorem T_inj : ∀ w w' : Fin 4, T w = T w' → w = w' := by decide

theorem T_inter : ∀ w w' : Fin 4, w ≠ w' → (T w ∩ T w').card ≤ 1 := by decide

theorem T_not_sub_compl : ∀ w w' : Fin 4, ¬ T w ⊆ (T w')ᶜ := by decide

theorem pt_card : ∀ i : Fin 6, (Finset.univ.filter fun k : Fin 7 => pt k i = true).card = 1 := by
  decide

theorem line_iff : ∀ (w : Fin 4) (k : Fin 7),
    (∃ va ∈ (![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 4 → Finset (Fin 6)) w,
      pt k va = true) ↔ k ∈ T w := by
  decide

theorem sg_input (gl : List Gate) (i : ℕ) (hi : i < 6) : (sg gl i).card = 1 := by
  have h := pt_card ⟨i, hi⟩
  have e : sg gl i = Finset.univ.filter fun k : Fin 7 => pt k ⟨i, hi⟩ = true := by
    unfold sg
    refine Finset.filter_congr fun k _ => ?_
    rw [← val_input gl (pt k) ⟨i, hi⟩]
  rw [e]; exact h

theorem sg_beyond (gl : List Gate) (i : ℕ) (hi : 6 + gl.length ≤ i) : sg gl i = ∅ := by
  unfold sg
  refine Finset.filter_eq_empty_iff.2 fun k _ => ?_
  rw [val_beyond gl (pt k) hi]; simp

theorem mem_sg (gl : List Gate) (i : ℕ) (k : Fin 7) : k ∈ sg gl i ↔ val gl (pt k) i = true := by
  simp [sg]

theorem mem_osg (gl : List Gate) (j i : ℕ) (k : Fin 7) :
    k ∈ osg gl j i ↔ operand gl (pt k) j i = true := by
  unfold osg operand
  split
  · exact mem_sg gl i k
  · simp

theorem sg_and (gl : List Gate) (p : ℕ) (g : Gate) (hp : gl[p]? = some g)
    (hop : g.op = GateOp.and) (a b : ℕ) (hin : g.inputs = [a, b]) :
    sg gl (6 + p) = osg gl (6 + p) a ∩ osg gl (6 + p) b := by
  ext k
  rw [Finset.mem_inter, mem_sg, mem_osg, mem_osg, val_gate gl (pt k) hp, hop, hin]
  simp [GateOp.eval]

theorem sg_and1 (gl : List Gate) (p : ℕ) (g : Gate) (hp : gl[p]? = some g)
    (hop : g.op = GateOp.and) (a : ℕ) (hin : g.inputs = [a]) :
    sg gl (6 + p) = osg gl (6 + p) a := by
  ext k
  rw [mem_sg, mem_osg, val_gate gl (pt k) hp, hop, hin]
  simp [GateOp.eval]

theorem sg_and0 (gl : List Gate) (p : ℕ) (g : Gate) (hp : gl[p]? = some g)
    (hop : g.op = GateOp.and) (hin : g.inputs = []) :
    sg gl (6 + p) = Finset.univ := by
  ext k
  rw [mem_sg, val_gate gl (pt k) hp, hop, hin]
  simp [GateOp.eval]

theorem sg_or (gl : List Gate) (p : ℕ) (g : Gate) (hp : gl[p]? = some g)
    (hop : g.op = GateOp.or) (a b : ℕ) (hin : g.inputs = [a, b]) :
    sg gl (6 + p) = osg gl (6 + p) a ∪ osg gl (6 + p) b := by
  ext k
  rw [Finset.mem_union, mem_sg, mem_osg, mem_osg, val_gate gl (pt k) hp, hop, hin]
  simp [GateOp.eval]

theorem sg_or1 (gl : List Gate) (p : ℕ) (g : Gate) (hp : gl[p]? = some g)
    (hop : g.op = GateOp.or) (a : ℕ) (hin : g.inputs = [a]) :
    sg gl (6 + p) = osg gl (6 + p) a := by
  ext k
  rw [mem_sg, mem_osg, val_gate gl (pt k) hp, hop, hin]
  simp [GateOp.eval]

theorem sg_or0 (gl : List Gate) (p : ℕ) (g : Gate) (hp : gl[p]? = some g)
    (hop : g.op = GateOp.or) (hin : g.inputs = []) :
    sg gl (6 + p) = ∅ := by
  ext k
  rw [mem_sg, val_gate gl (pt k) hp, hop, hin]
  simp [GateOp.eval]

theorem sg_not (gl : List Gate) (p : ℕ) (g : Gate) (hp : gl[p]? = some g)
    (hop : g.op = GateOp.not) (a : ℕ) (r : List ℕ) (hin : g.inputs = a :: r) :
    sg gl (6 + p) = (osg gl (6 + p) a)ᶜ := by
  ext k
  rw [Finset.mem_compl, mem_sg, mem_osg, val_gate gl (pt k) hp, hop, hin]
  simp [GateOp.eval]

theorem sg_not0 (gl : List Gate) (p : ℕ) (g : Gate) (hp : gl[p]? = some g)
    (hop : g.op = GateOp.not) (hin : g.inputs = []) :
    sg gl (6 + p) = Finset.univ := by
  ext k
  rw [mem_sg, val_gate gl (pt k) hp, hop, hin]
  simp [GateOp.eval]

theorem osg_cases (gl : List Gate) (p a : ℕ) :
    osg gl (6 + p) a = ∅ ∨ (osg gl (6 + p) a).card = 1 ∨
      ∃ j, j < p ∧ osg gl (6 + p) a = sg gl (6 + j) := by
  unfold osg
  split
  · rename_i h
    by_cases h6 : a < 6
    · exact Or.inr (Or.inl (sg_input gl a h6))
    · exact Or.inr (Or.inr ⟨a - 6, by omega, by rw [show 6 + (a - 6) = a by omega]⟩)
  · exact Or.inl rfl

def Alpha (w : Fin 4) (A : Finset (Fin 7)) : Prop :=
  (A ⊆ T w ∧ A.card = 2) ∨ A = (T w)ᶜ

theorem alpha_unique (w w' : Fin 4) (A : Finset (Fin 7)) (h : Alpha w A) (h' : Alpha w' A) :
    w = w' := by
  rcases h with ⟨hs, hc⟩ | rfl
  · rcases h' with ⟨hs', _⟩ | rfl
    · by_contra hne
      have h1 := T_inter w w' hne
      have h2 := Finset.card_le_card (Finset.subset_inter hs hs')
      omega
    · have := T_compl_card w'
      omega
  · rcases h' with ⟨_, hc'⟩ | h'
    · have := T_compl_card w
      omega
    · exact T_inj w w' (compl_injective h')

theorem step (gl : List Gate)
    (hg : ∀ gg ∈ gl, (gg.op = GateOp.and ∨ gg.op = GateOp.or ∨ gg.op = GateOp.not) ∧
      gg.inputs.length ≤ 2)
    (w : Fin 4) (p : ℕ) (hp : p < gl.length) (hT : sg gl (6 + p) = T w)
    (hfirst : ∀ j, j < p → sg gl (6 + j) ≠ T w) :
    (∃ j, j < p ∧ Alpha w (sg gl (6 + j))) ∨
    (∃ j k, j < p ∧ k < p ∧ sg gl (6 + j) ∩ sg gl (6 + k) = T w ∧
      sg gl (6 + j) ≠ T w ∧ sg gl (6 + k) ≠ T w) := by
  have hc3 := T_card w
  have hne : ∀ a, osg gl (6 + p) a ≠ T w := by
    intro a h
    rcases osg_cases gl p a with h0 | h1 | ⟨j, hj, hj'⟩
    · rw [h0] at h; rw [← h] at hc3; simp at hc3
    · rw [h] at h1; omega
    · exact hfirst j hj (hj' ▸ h)
  have big : ∀ a, 2 ≤ (osg gl (6 + p) a).card → ∃ j, j < p ∧ osg gl (6 + p) a = sg gl (6 + j) := by
    intro a h
    rcases osg_cases gl p a with h0 | h1 | h2
    · rw [h0] at h; simp at h
    · omega
    · exact h2
  have hget : gl[p]? = some gl[p] := List.getElem?_eq_getElem hp
  obtain ⟨hop, hlen⟩ := hg gl[p] (List.getElem_mem hp)
  rcases hin : gl[p].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · rcases hop with hop | hop | hop
    · rw [sg_and0 gl p _ hget hop hin] at hT
      rw [← hT] at hc3; simp at hc3
    · rw [sg_or0 gl p _ hget hop hin] at hT
      rw [← hT] at hc3; simp at hc3
    · rw [sg_not0 gl p _ hget hop hin] at hT
      rw [← hT] at hc3; simp at hc3
  · rcases hop with hop | hop | hop
    · exact absurd ((sg_and1 gl p _ hget hop a hin).symm.trans hT) (hne a)
    · exact absurd ((sg_or1 gl p _ hget hop a hin).symm.trans hT) (hne a)
    · rw [sg_not gl p _ hget hop a [] hin] at hT
      have hA : osg gl (6 + p) a = (T w)ᶜ := by rw [← hT, compl_compl]
      have h4 := T_compl_card w
      obtain ⟨j, hj, hj'⟩ := big a (by rw [hA]; omega)
      exact Or.inl ⟨j, hj, Or.inr (hj' ▸ hA)⟩
  · rcases hop with hop | hop | hop
    · rw [sg_and gl p _ hget hop a b hin] at hT
      have ha : T w ⊆ osg gl (6 + p) a := hT ▸ Finset.inter_subset_left
      have hb : T w ⊆ osg gl (6 + p) b := hT ▸ Finset.inter_subset_right
      have ca := Finset.card_le_card ha
      have cb := Finset.card_le_card hb
      obtain ⟨j, hj, hj'⟩ := big a (by omega)
      obtain ⟨k, hk, hk'⟩ := big b (by omega)
      refine Or.inr ⟨j, k, hj, hk, ?_, ?_, ?_⟩
      · rw [← hj', ← hk']; exact hT
      · rw [← hj']; exact hne a
      · rw [← hk']; exact hne b
    · rw [sg_or gl p _ hget hop a b hin] at hT
      have ha : osg gl (6 + p) a ⊆ T w := hT ▸ Finset.subset_union_left
      have hb : osg gl (6 + p) b ⊆ T w := hT ▸ Finset.subset_union_right
      have ca := Finset.card_lt_card (lt_of_le_of_ne ha (hne a))
      have cb := Finset.card_lt_card (lt_of_le_of_ne hb (hne b))
      have cu := Finset.card_union_le (osg gl (6 + p) a) (osg gl (6 + p) b)
      rw [hT] at cu
      rcases (show (osg gl (6 + p) a).card = 2 ∨ (osg gl (6 + p) b).card = 2 by omega) with h2 | h2
      · obtain ⟨j, hj, hj'⟩ := big a (by omega)
        exact Or.inl ⟨j, hj, Or.inl ⟨hj' ▸ ha, hj' ▸ h2⟩⟩
      · obtain ⟨j, hj, hj'⟩ := big b (by omega)
        exact Or.inl ⟨j, hj, Or.inl ⟨hj' ▸ hb, hj' ▸ h2⟩⟩
    · rw [sg_not gl p _ hget hop a [b] hin] at hT
      have hA : osg gl (6 + p) a = (T w)ᶜ := by rw [← hT, compl_compl]
      have h4 := T_compl_card w
      obtain ⟨j, hj, hj'⟩ := big a (by rw [hA]; omega)
      exact Or.inl ⟨j, hj, Or.inr (hj' ▸ hA)⟩
  · rw [hin] at hlen
    simp at hlen

theorem choose_le : ∀ b : ℕ, b ≤ 3 → b.choose 2 ≤ b := by decide

theorem core (L : ℕ) (s : ℕ → Finset (Fin 7))
    (h : ∀ w : Fin 4, ∃ p, p < L ∧ s p = T w ∧
      ((∃ j, j < p ∧ Alpha w (s j)) ∨
       (∃ j k, j < p ∧ k < p ∧ s j ∩ s k = T w ∧ s j ≠ T w ∧ s k ≠ T w))) :
    8 ≤ L := by
  classical
  by_contra hL
  choose g hgL hgT hgc using h
  let B0 := (Finset.range L).filter fun j => ∃ w, s j = T w
  let B1 := (Finset.range L).filter fun j => ∃ w, Alpha w (s j)
  let B2 := (Finset.range L).filter fun j => ∃ w, T w ⊂ s j
  have a_card : ∀ w A, Alpha w A → A.card = 2 ∨ A.card = 4 := by
    intro w A hA
    rcases hA with ⟨_, hc⟩ | rfl
    · exact Or.inl hc
    · exact Or.inr (T_compl_card w)
  have d01 : Disjoint B0 B1 := by
    rw [Finset.disjoint_left]
    intro j h0 h1
    obtain ⟨w, hw⟩ := (Finset.mem_filter.1 h0).2
    obtain ⟨w', hw'⟩ := (Finset.mem_filter.1 h1).2
    have := a_card w' _ hw'
    have := T_card w
    rw [hw] at *
    omega
  have d02 : Disjoint B0 B2 := by
    rw [Finset.disjoint_left]
    intro j h0 h2
    obtain ⟨w, hw⟩ := (Finset.mem_filter.1 h0).2
    obtain ⟨w', hw'⟩ := (Finset.mem_filter.1 h2).2
    have := Finset.card_lt_card hw'
    have := T_card w
    have := T_card w'
    rw [hw] at *
    omega
  have d12 : Disjoint B1 B2 := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    obtain ⟨w, hw⟩ := (Finset.mem_filter.1 h1).2
    obtain ⟨w', hw'⟩ := (Finset.mem_filter.1 h2).2
    have c3 := T_card w'
    have clt := Finset.card_lt_card hw'
    rcases hw with ⟨_, hc⟩ | he
    · omega
    · exact T_not_sub_compl w' w (he ▸ hw'.1)
  have hB0 : 4 ≤ B0.card := by
    have : (Finset.univ : Finset (Fin 4)).card ≤ B0.card := by
      refine Finset.card_le_card_of_injOn g ?_ ?_
      · intro w _
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hgL w), w, hgT w⟩
      · intro w _ w' _ hww
        exact T_inj w w' (by rw [← hgT w, ← hgT w', hww])
    simpa using this
  have hsum : B0.card + B1.card + B2.card ≤ L := by
    have hd : Disjoint (B0 ∪ B1) B2 := Finset.disjoint_union_left.2 ⟨d02, d12⟩
    have hsub : (B0 ∪ B1) ∪ B2 ⊆ Finset.range L := by
      intro j hj
      rcases Finset.mem_union.1 hj with hj | hj
      · rcases Finset.mem_union.1 hj with hj | hj
        · exact (Finset.mem_filter.1 hj).1
        · exact (Finset.mem_filter.1 hj).1
      · exact (Finset.mem_filter.1 hj).1
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint d01,
      Finset.card_range] at this
    exact this
  have hF : ∀ w : Fin 4, ∃ P : Finset ℕ,
      (P ∈ Finset.powersetCard 1 B1 ∧ ∃ j ∈ P, Alpha w (s j)) ∨
      (P ∈ Finset.powersetCard 2 B2 ∧ ∃ j ∈ P, ∃ k ∈ P, j ≠ k ∧ s j ∩ s k = T w) := by
    intro w
    rcases hgc w with ⟨j, hj, ha⟩ | ⟨j, k, hj, hk, hjk, hjn, hkn⟩
    · refine ⟨{j}, Or.inl ⟨?_, j, Finset.mem_singleton_self j, ha⟩⟩
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_singleton j⟩
      intro i hi
      rw [Finset.mem_singleton.1 hi]
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_trans hj (hgL w)), w, ha⟩
    · have hne : j ≠ k := by
        rintro rfl
        rw [Finset.inter_self] at hjk
        exact hjn hjk
      refine ⟨{j, k}, Or.inr ⟨?_, j, by simp, k, by simp, hne, hjk⟩⟩
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair hne⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_trans hj (hgL w)), w, ?_⟩
        exact lt_of_le_of_ne (hjk ▸ Finset.inter_subset_left) (Ne.symm hjn)
      · rw [Finset.mem_singleton.1 hi]
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_trans hk (hgL w)), w, ?_⟩
        exact lt_of_le_of_ne (hjk ▸ Finset.inter_subset_right) (Ne.symm hkn)
  choose F hFp using hF
  have Finj : Function.Injective F := by
    intro w w' hww
    rcases hFp w with ⟨hP, j, hj, ha⟩ | ⟨hP, j, hj, k, hk, hne, hjk⟩
    · rcases hFp w' with ⟨hP', j', hj', ha'⟩ | ⟨hP', _⟩
      · have c1 := (Finset.mem_powersetCard.1 hP).2
        rw [← hww] at hj'
        have : j = j' := Finset.card_le_one.1 (le_of_eq c1) j hj j' hj'
        subst this
        exact alpha_unique w w' _ ha ha'
      · have c1 := (Finset.mem_powersetCard.1 hP).2
        have c2 := (Finset.mem_powersetCard.1 hP').2
        rw [hww] at c1
        omega
    · rcases hFp w' with ⟨hP', _⟩ | ⟨hP', j', hj', k', hk', hne', hjk'⟩
      · have c1 := (Finset.mem_powersetCard.1 hP).2
        have c2 := (Finset.mem_powersetCard.1 hP').2
        rw [hww] at c1
        omega
      · have c2 := (Finset.mem_powersetCard.1 hP).2
        have hpair : F w = {j, k} := by
          symm
          refine Finset.eq_of_subset_of_card_le ?_ ?_
          · intro i hi
            rcases Finset.mem_insert.1 hi with rfl | hi
            · exact hj
            · rw [Finset.mem_singleton.1 hi]; exact hk
          · rw [c2, Finset.card_pair hne]
        rw [← hww, hpair] at hj' hk'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj' hk'
        apply T_inj
        rcases hj' with rfl | rfl <;> rcases hk' with rfl | rfl
        · exact absurd rfl hne'
        · rw [← hjk, ← hjk']
        · rw [← hjk, ← hjk', Finset.inter_comm]
        · exact absurd rfl hne'
  have himg : (Finset.univ.image F) ⊆ Finset.powersetCard 1 B1 ∪ Finset.powersetCard 2 B2 := by
    intro P hP
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hP
    rcases hFp w with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact Finset.mem_union_left _ h1
    · exact Finset.mem_union_right _ h2
  have hc := Finset.card_le_card himg
  rw [Finset.card_image_of_injective _ Finj] at hc
  have hu := Finset.card_union_le (Finset.powersetCard 1 B1) (Finset.powersetCard 2 B2)
  rw [Finset.card_powersetCard, Finset.card_powersetCard, Nat.choose_one_right] at hu
  have hch := choose_le B2.card (by omega)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

theorem main (gl : List Gate) (ol : Fin 4 → ℕ)
    (hg : ∀ gg ∈ gl, (gg.op = GateOp.and ∨ gg.op = GateOp.or ∨ gg.op = GateOp.not) ∧
      gg.inputs.length ≤ 2)
    (hout : ∀ (oa : Fin 4) (xa : Fin 6 → Bool), Circuit.eval ⟨gl, ol oa⟩ (List.ofFn xa) =
      decide (∃ va ∈ (![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 4 → Finset (Fin 6)) oa,
        xa va = true)) :
    8 ≤ gl.length := by
  classical
  have hsig : ∀ w : Fin 4, sg gl (ol w) = T w := by
    intro w
    ext k
    rw [mem_sg, ← line_iff w k]
    have := hout w (pt k)
    change val gl (pt k) (ol w) = _ at this
    rw [this]
    simp
  have hex : ∀ w : Fin 4, ∃ p, p < gl.length ∧ sg gl (6 + p) = T w := by
    intro w
    have hc3 := T_card w
    have h := hsig w
    by_cases h6 : ol w < 6
    · have := sg_input gl (ol w) h6
      rw [h] at this; omega
    · by_cases hb : 6 + gl.length ≤ ol w
      · rw [sg_beyond gl _ hb] at h
        rw [← h] at hc3; simp at hc3
      · exact ⟨ol w - 6, by omega, by rw [show 6 + (ol w - 6) = ol w by omega]; exact h⟩
  refine core gl.length (fun j => sg gl (6 + j)) fun w => ?_
  have hfind := Nat.find_spec (hex w)
  refine ⟨Nat.find (hex w), hfind.1, hfind.2, ?_⟩
  refine step gl hg w _ hfind.1 hfind.2 fun j hj hT => ?_
  exact Nat.find_min (hex w) hj ⟨lt_trans hj hfind.1, hT⟩

end PEqualNP.Outside.L_meta_1042

theorem PEqualNP.Outside.L_meta_1042 : (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin 4 → ℕ), (∀ gg ∈ gl, (gg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gg.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gl.length, ∀ qa : Fin gl.length, (gl.get qa).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ ka : Fin 1, ι ka = qa) → (∀ (oa : Fin 4) (xa : Fin 6 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol oa⟩ (List.ofFn xa) = decide (∃ va ∈ (![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 4 → Finset (Fin 6)) oa, xa va = true)) → 8 ≤ gl.length := by
  intro _ gl ol hg _ hout
  exact PEqualNP.Outside.L_meta_1042.main gl ol hg hout
