import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2800_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def shift (p i : ℕ) : ℕ := if p < i then i - 1 else i

def ren (p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift p)⟩

def slots (C : Circuit) : List ℕ := C.output :: C.gates.flatMap Gate.inputs

lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then b else false := by
  by_cases h1 : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, h1]
  · by_cases h2 : i = w.length
    · subst h2
      simp [List.getD_eq_getElem?_getD]
    · have h3 : (w ++ [b]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h3, h1, h2]

lemma getD_beyond (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma fold_length (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, step_length]
    simp; omega

lemma ren_value (p : ℕ) (g : Gate) (w w' : List Bool) (hp : p ∉ g.inputs)
    (h : ∀ i, i ≠ p → w'.getD (shift p i) false = w.getD i false) :
    (ren p g).op.eval ((ren p g).inputs.map fun i => w'.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [ren, List.map_map]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  exact h i (fun e => hp (e ▸ hi))

lemma before (p : ℕ) (gs : List Gate) : ∀ w : List Bool, w.length + gs.length ≤ p →
    (∀ g ∈ gs, p ∉ g.inputs) → (gs.map (ren p)).foldl step w = gs.foldl step w := by
  induction gs with
  | nil => intro w _ _; rfl
  | cons g gs ih =>
    intro w hw hg
    simp only [List.length_cons] at hw
    have hv : step w (ren p g) = step w g := by
      unfold step
      rw [ren_value p g w w (hg g (by simp))]
      intro i hi
      unfold shift
      split_ifs with hlt
      · rw [getD_beyond w _ (by omega), getD_beyond w _ (by omega)]
      · rfl
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, hv]
    exact ih _ (by rw [step_length]; omega) (fun g' hg' => hg g' (by simp [hg']))

def Rel (p : ℕ) (w w' : List Bool) : Prop :=
  w'.length + 1 = w.length ∧ p < w.length ∧
    ∀ i, i ≠ p → w'.getD (shift p i) false = w.getD i false

lemma rel_step (p : ℕ) (g : Gate) (w w' : List Bool) (hp : p ∉ g.inputs) (h : Rel p w w') :
    Rel p (step w g) (step w' (ren p g)) := by
  obtain ⟨hl, hpl, hv⟩ := h
  refine ⟨by rw [step_length, step_length]; omega, by rw [step_length]; omega, ?_⟩
  intro i hi
  unfold step
  rw [ren_value p g w w' hp hv, getD_snoc, getD_snoc, hv i hi]
  have e1 : shift p i < w'.length ↔ i < w.length := by
    unfold shift; split_ifs <;> omega
  have e2 : shift p i = w'.length ↔ i = w.length := by
    unfold shift; split_ifs <;> omega
  simp only [e1, e2]

lemma after (p : ℕ) (gs : List Gate) : ∀ w w' : List Bool, (∀ g ∈ gs, p ∉ g.inputs) →
    Rel p w w' → Rel p (gs.foldl step w) ((gs.map (ren p)).foldl step w') := by
  induction gs with
  | nil => intro w w' _ h; exact h
  | cons g gs ih =>
    intro w w' hg h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    exact ih _ _ (fun g' hg' => hg g' (by simp [hg'])) (rel_step p g w w' (hg g (by simp)) h)

lemma remove (n : ℕ) (C : Circuit) (hC : FanInTwo C) (j : ℕ) (hj : j < C.gates.length)
    (hun : n + j ∉ slots C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size < C.size ∧
      ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by simp
  generalize hpre : C.gates.take j = pre at hsplit
  generalize hg : C.gates[j] = g at hsplit
  generalize hpost : C.gates.drop (j + 1) = post at hsplit
  have hprelen : pre.length = j := by rw [← hpre, List.length_take]; omega
  have hout : n + j ≠ C.output := fun e => hun (by simp [slots, e])
  have hin : ∀ g' ∈ C.gates, n + j ∉ g'.inputs := fun g' hg' hm =>
    hun (by
      simp only [slots, List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨g', hg', hm⟩)
  have hinpre : ∀ g' ∈ pre, n + j ∉ g'.inputs := fun g' hg' => hin g' (by rw [hsplit]; simp [hg'])
  have hinpost : ∀ g' ∈ post, n + j ∉ g'.inputs := fun g' hg' => hin g' (by rw [hsplit]; simp [hg'])
  refine ⟨⟨(pre ++ post).map (ren (n + j)), shift (n + j) C.output⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg'
    have hmem : g0 ∈ C.gates := by
      rw [hsplit]
      rcases List.mem_append.mp hg0 with h | h <;> simp [h]
    obtain ⟨h1, h2⟩ := hC g0 hmem
    exact ⟨h1, by simpa [ren] using h2⟩
  · change ((pre ++ post).map (ren (n + j))).length < C.gates.length
    rw [hsplit]
    simp
  · intro x hx
    change (((pre ++ post).map (ren (n + j))).foldl step x).getD (shift (n + j) C.output) false =
      (C.gates.foldl step x).getD C.output false
    rw [hsplit, List.map_append, List.foldl_append, List.foldl_append, List.foldl_cons,
      before (n + j) pre x (by omega) hinpre]
    have hlen : (pre.foldl step x).length = n + j := by rw [fold_length]; omega
    have hrel : Rel (n + j) (step (pre.foldl step x) g) (pre.foldl step x) := by
      refine ⟨by rw [step_length], by rw [step_length]; omega, ?_⟩
      intro i hi
      change _ = (pre.foldl step x ++ [g.op.eval (g.inputs.map fun q =>
        (pre.foldl step x).getD q false)]).getD i false
      rw [getD_snoc, hlen]
      unfold shift
      by_cases hlt : n + j < i
      · rw [if_pos hlt, if_neg (by omega), if_neg (by omega), getD_beyond _ _ (by omega)]
      · rw [if_neg hlt, if_pos (by omega)]
    exact (after (n + j) post _ _ hinpost hrel).2.2 C.output (fun e => hout e.symm)

lemma slots_length (C : Circuit) (hC : FanInTwo C) : (slots C).length ≤ 2 * C.size + 1 := by
  have key : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
    intro gs
    induction gs with
    | nil => intro _; simp
    | cons g gs ih =>
      intro h
      have h1 := h g (by simp)
      have h2 := ih (fun g' hg' => h g' (by simp [hg']))
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have := key C.gates (fun g hg => (hC g hg).2)
  change (C.output :: C.gates.flatMap Gate.inputs).length ≤ 2 * C.gates.length + 1
  rw [List.length_cons]
  omega

lemma full_count (n : ℕ) (C : Circuit) (hC : FanInTwo C)
    (hall : ∀ j < C.gates.length, n + j ∈ slots C) :
    (slots C).countP (fun i => decide (i < n)) ≤ C.size + 1 := by
  have hsum := List.length_eq_countP_add_countP (fun i => decide (i < n)) (l := slots C)
  have hlen := slots_length C hC
  have hsize : C.size = C.gates.length := rfl
  have hge : C.gates.length ≤ ((slots C).filter (fun i => !decide (i < n))).length := by
    have hsub : (List.range C.gates.length).map (n + ·) ⊆
        (slots C).filter (fun i => !decide (i < n)) := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_filter]
      exact ⟨hall j (List.mem_range.mp hj), by simp⟩
    have hnd : ((List.range C.gates.length).map (n + ·)).Nodup :=
      List.Nodup.map (fun a b h => by simpa using h) List.nodup_range
    have := (List.subperm_of_subset hnd hsub).length_le
    simpa using this
  have hc : (slots C).countP (fun a => decide ¬(decide (a < n)) = true) =
      ((slots C).filter (fun i => !decide (i < n))).length := by
    rw [List.countP_eq_length_filter]
    refine congrArg List.length (List.filter_congr fun a _ => ?_)
    by_cases h : a < n <;> simp [h]
  rw [hc] at hsum
  omega

theorem main (n : ℕ) : ∀ (m : ℕ) (C : Circuit), C.size = m → FanInTwo C →
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      (slots D).countP (fun i => decide (i < n)) ≤ D.size + 1 ∧
      ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro C hm hC
    by_cases hall : ∀ j < C.gates.length, n + j ∈ slots C
    · exact ⟨C, hC, le_rfl, full_count n C hC hall, fun _ _ => rfl⟩
    · push Not at hall
      obtain ⟨j, hj, hun⟩ := hall
      obtain ⟨D, hD, hsz, hev⟩ := remove n C hC j hj hun
      obtain ⟨E, hE, hEs, hEc, hEe⟩ := ih D.size (by omega) D rfl hD
      exact ⟨E, hE, by omega, hEc, fun x hx => (hEe x hx).trans (hev x hx)⟩

end PEqualNP.Outside.L_meta_2800_aux

theorem PEqualNP.Outside.L_meta_2800 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size ≤ x2.size ∧ List.countP (fun (x5 : ℕ) => Decidable.decide (x5 < x1)) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ≤ x4.size + (1 : ℕ) ∧ ∀ (x5 : List Bool), x5.length = x1 → x4.eval x5 = x2.eval x5 := by
  intro n C hC
  exact PEqualNP.Outside.L_meta_2800_aux.main n C.size C rfl hC
