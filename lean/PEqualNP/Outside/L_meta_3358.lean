import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3358
open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def isNot (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

def reads (g : Gate) : List ℕ :=
  if isNot g then g.inputs.take 1 else g.inputs

def nonNot (gs : List Gate) : ℕ := gs.countP (fun g => !isNot g)

theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl stepW x = stepW (gs.foldl stepW x) g := by
  simp [List.foldl_append]

theorem wires_len (gs : List Gate) (x : List Bool) :
    (gs.foldl stepW x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => rw [wires_snoc]; simp [stepW, ih]; omega

theorem stepW_lt (w : List Bool) (g : Gate) {i : ℕ} (h : i < w.length) :
    (stepW w g).getD i false = w.getD i false := by
  unfold stepW; exact List.getD_append _ _ _ _ h

theorem stepW_eq (w : List Bool) (g : Gate) :
    (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun j => w.getD j false) := by
  unfold stepW
  simp [List.getD_eq_getElem?_getD]

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ j ∈ reads g, f j = f' j) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  by_cases hn : isNot g = true
  · have hop : g.op = GateOp.not := by
      unfold isNot at hn; split at hn <;> simp_all
    rcases hg : g.inputs with _ | ⟨j, rest⟩
    · simp [hop, GateOp.eval]
    · have hj := h j (by simp [reads, hn, hg])
      simp [hop, GateOp.eval, hj]
  · have : reads g = g.inputs := by
      unfold reads; simp [hn]
    rw [this] at h
    congr 1
    exact List.map_congr_left h

theorem reads_len (g : Gate) (h : g.inputs.length ≤ 2) :
    (reads g).length ≤ 2 ∧ (isNot g = true → (reads g).length ≤ 1) := by
  unfold reads
  by_cases hn : isNot g = true
  · simp [hn]
  · simp [hn]; exact h


theorem nonNot_snoc (gs : List Gate) (g : Gate) :
    nonNot (gs ++ [g]) = nonNot gs + (if isNot g = true then 0 else 1) := by
  unfold nonNot
  rw [List.countP_append]
  by_cases h : isNot g = true <;> simp [h]

theorem dep (L : ℕ) : ∀ (gs : List Gate), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ (W : Finset ℕ), (∀ i ∈ W, i < L + gs.length) →
    ∃ S : Finset ℕ, S ⊆ Finset.range L ∧ S.card ≤ W.card + nonNot gs ∧
      ∀ x y : List Bool, x.length = L → y.length = L →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ W, (gs.foldl stepW x).getD i false = (gs.foldl stepW y).getD i false := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ W hW
    refine ⟨W, ?_, by simp [nonNot], ?_⟩
    · intro i hi; simpa using hW i hi
    · intro x y _ _ hag i hi
      simpa using hag i hi
  | append_singleton gs g ih =>
    intro hfan W hW
    have hfan' : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' h => hfan g' (by simp [h])
    have hg2 : g.inputs.length ≤ 2 := hfan g (by simp)
    set m := L + gs.length with hm
    have hWlen : ∀ i ∈ W, i < m + 1 := by
      intro i hi; have := hW i hi; simp at this; omega
    let R : Finset ℕ := (reads g).toFinset.filter (fun j => j < m)
    let W' : Finset ℕ := W.erase m ∪ (if m ∈ W then R else ∅)
    have hW' : ∀ i ∈ W', i < L + gs.length := by
      intro i hi
      simp only [W', Finset.mem_union, Finset.mem_erase] at hi
      rcases hi with ⟨hne, hiW⟩ | hi
      · have := hWlen i hiW; omega
      · split_ifs at hi
        · simp [R] at hi; omega
        · simp at hi
    obtain ⟨S, hS, hcard, hag⟩ := ih hfan' W' hW'
    refine ⟨S, hS, ?_, ?_⟩
    · rw [nonNot_snoc]
      have hR : R.card ≤ (reads g).length :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans (List.toFinset_card_le _)
      have hrl := reads_len g hg2
      have hW'c : W'.card ≤ (W.erase m).card + (if m ∈ W then R else ∅).card :=
        Finset.card_union_le _ _
      by_cases hmW : m ∈ W
      · have h1 : (W.erase m).card = W.card - 1 := Finset.card_erase_of_mem hmW
        have h2 : 1 ≤ W.card := Finset.card_pos.mpr ⟨m, hmW⟩
        simp only [hmW, if_true] at hW'c
        by_cases hn : isNot g = true
        · have := hrl.2 hn
          rw [if_pos hn]; omega
        · have := hrl.1
          rw [if_neg hn]; omega
      · have h1 : W.erase m = W := Finset.erase_eq_of_notMem hmW
        simp only [hmW, if_false, Finset.card_empty] at hW'c
        rw [h1] at hW'c
        split_ifs <;> omega
    · intro x y hx hy hagxy i hi
      have hlx : (gs.foldl stepW x).length = m := by rw [wires_len, hx]
      have hly : (gs.foldl stepW y).length = m := by rw [wires_len, hy]
      have key := hag x y hx hy hagxy
      rw [wires_snoc, wires_snoc]
      by_cases him : i = m
      · rw [him]
        have hmW : m ∈ W := him ▸ hi
        have e1 := stepW_eq (gs.foldl stepW x) g
        have e2 := stepW_eq (gs.foldl stepW y) g
        rw [hlx] at e1
        rw [hly] at e2
        rw [e1, e2]
        apply eval_congr
        intro j hj
        by_cases hjm : j < m
        · apply key
          simp only [W', Finset.mem_union, hmW, if_true, R, Finset.mem_filter, List.mem_toFinset]
          exact Or.inr ⟨hj, hjm⟩
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · have hlt : i < m := by have := hWlen i hi; omega
        rw [stepW_lt _ _ (by omega), stepW_lt _ _ (by omega)]
        apply key
        simp only [W', Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨him, hi⟩


theorem two_nots : ∀ (l : List Gate) (a b : ℕ) (ha : a < l.length) (hb : b < l.length), a < b →
    isNot l[a] = true → isNot l[b] = true → 2 ≤ l.countP isNot := by
  intro l
  induction l with
  | nil => intro a b ha; simp at ha
  | cons h t ih =>
    intro a b ha hb hab hna hnb
    rcases a with _ | a
    · rcases b with _ | b
      · omega
      · have hbt : b < t.length := by simpa using hb
        have hpos : 0 < t.countP isNot := by
          rw [List.countP_pos_iff]
          exact ⟨t[b]'hbt, by simp, by simpa using hnb⟩
        have hh : isNot h = true := by simpa using hna
        rw [List.countP_cons_of_pos (by simpa using hh)]
        omega
    · rcases b with _ | b
      · omega
      · have := ih a b (by simpa using ha) (by simpa using hb) (by omega)
          (by simpa using hna) (by simpa using hnb)
        rw [List.countP_cons]
        omega

theorem nonNot_le (l : List Gate) (a b : ℕ) (ha : a < l.length) (hb : b < l.length) (hab : a < b)
    (hna : isNot l[a] = true) (hnb : isNot l[b] = true) : nonNot l + 2 ≤ l.length := by
  have h2 := two_nots l a b ha hb hab hna hnb
  have h3 : l.length = l.countP isNot + l.countP (fun a => decide ¬isNot a = true) :=
    List.length_eq_countP_add_countP isNot
  have h4 : l.countP (fun g => !isNot g) = l.countP (fun a => decide ¬isNot a = true) :=
    List.countP_congr (by intro x _; simp)
  unfold nonNot
  omega

end PEqualNP.Outside.L_meta_3358

theorem PEqualNP.Outside.L_meta_3358 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (7 : ℕ) → ∀ (x4 x5 : Fin x1.gates.length), x4 < x5 → (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ x9 ⊆ Finset.range (17 : ℕ), x9.card ≤ (6 : ℕ) ∧ ∀ (x10 x11 : List Bool), x10.length = (17 : ℕ) → x11.length = (17 : ℕ) → (∀ x14 ∈ x9, x10.getD x14 Bool.false = x11.getD x14 Bool.false) → x1.eval x10 = x1.eval x11 := by
  intro C hfan hsize a b hab hna hnb
  have hfan' : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hfan g hg).2
  have hnot : ∀ g : PEqualNP.CircuitLowerBounds.Gate,
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not → PEqualNP.Outside.L_meta_3358.isNot g = true := by
    intro g hg
    unfold PEqualNP.Outside.L_meta_3358.isNot
    rw [hg]
  have hcount := PEqualNP.Outside.L_meta_3358.nonNot_le C.gates a.val b.val a.isLt b.isLt hab
    (hnot _ hna) (hnot _ hnb)
  have hsz : C.gates.length ≤ 7 := hsize
  by_cases ho : C.output < 17 + C.gates.length
  · obtain ⟨S, hS, hcard, hag⟩ := PEqualNP.Outside.L_meta_3358.dep 17 C.gates hfan' {C.output}
      (by simpa using ho)
    refine ⟨S, hS, by simp at hcard; omega, ?_⟩
    intro x y hx hy hagxy
    have := hag x y hx hy hagxy C.output (by simp)
    exact this
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro x y hx hy _
    have h1 : (C.wires x).length = 17 + C.gates.length := by
      have := PEqualNP.Outside.L_meta_3358.wires_len C.gates x
      have e : C.wires x = C.gates.foldl PEqualNP.Outside.L_meta_3358.stepW x := rfl
      rw [e]; simpa [hx] using this
    have h2 : (C.wires y).length = 17 + C.gates.length := by
      have := PEqualNP.Outside.L_meta_3358.wires_len C.gates y
      have e : C.wires y = C.gates.foldl PEqualNP.Outside.L_meta_3358.stepW y := rfl
      rw [e]; simpa [hy] using this
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
