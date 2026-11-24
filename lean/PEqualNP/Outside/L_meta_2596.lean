import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2596

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def wiresOf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [step g w]) w

private lemma wiresOf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresOf (g :: gs) w = wiresOf gs (w ++ [step g w]) := rfl

private lemma getD_lt {α : Type*} (l : List α) (d : α) (i : ℕ) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem h]

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_ge {α : Type*} (l : List α) (d : α) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none_iff.2 hi]

private lemma getD_snoc {α : Type*} (l : List α) (x d : α) (i : ℕ) :
    (l ++ [x]).getD i d = if i = l.length then x else l.getD i d := by
  by_cases hi : i = l.length
  · rw [getD_snoc_eq l x d i hi, if_pos hi]
  · rw [if_neg hi]
    by_cases hlt : i < l.length
    · exact getD_snoc_lt l x d i hlt
    · have e : (l ++ [x]).length = l.length + 1 := by simp
      rw [getD_ge _ _ _ (by rw [e]; omega), getD_ge _ _ _ (by omega)]

private lemma map_pointwise {α β : Type*} (l : List α) (f g : α → β)
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h a (by simp), ih (fun b hb => h b (by simp [hb]))⟩

private lemma map_pointwise_getD (ins : List ℕ) (x1 : ℕ) (w w' : List Bool)
    (hww : ∀ i, i ≠ x1 → w'.getD i false = w.getD i false)
    (hx : ∀ i ∈ ins, i = x1 → w'.getD i false = w.getD i false) :
    ins.map (fun i => w.getD i false) = ins.map (fun i => w'.getD i false) := by
  apply map_pointwise
  intro i hi
  by_cases hix : i = x1
  · exact (hx i hi hix).symm
  · exact (hww i hix).symm

-- Rewriting the reads of one input wire keeps every other wire value.
private lemma sim (x1 : ℕ) (z z' : List Bool) (N : ℕ) (gs : List Gate) (T : Gate → Gate)
    (hzlen : z'.length = z.length)
    (hz : ∀ i, i ≠ x1 → z'.getD i false = z.getD i false)
    (hT : ∀ w w' : List Bool,
        w'.length ≤ z'.length + N →
        (∀ i, i < z.length → w.getD i false = z.getD i false) →
        (∀ i, i < z'.length → w'.getD i false = z'.getD i false) →
        (∀ i, i ≠ x1 → w'.getD i false = w.getD i false) →
        ∀ g ∈ gs, step g w = step (T g) w') :
    ∀ w w' : List Bool,
      z.length ≤ w.length → w.length = w'.length → w'.length + gs.length ≤ z'.length + N →
      (∀ i, i < z.length → w.getD i false = z.getD i false) →
      (∀ i, i < z'.length → w'.getD i false = z'.getD i false) →
      (∀ i, i ≠ x1 → w'.getD i false = w.getD i false) →
      ∀ i, i ≠ x1 →
        (wiresOf (gs.map T) w').getD i false = (wiresOf gs w).getD i false := by
  induction gs with
  | nil =>
    intro w w' _ _ _ _ _ hww i hi
    simp only [List.map_nil, wiresOf, List.foldl_nil]
    exact hww i hi
  | cons g gs ih =>
    intro w w' hzw hwlen hwb hpre hpre' hww i hi
    simp only [List.map_cons, wiresOf_cons]
    have hg : g ∈ g :: gs := List.mem_cons_self
    have hval : step g w = step (T g) w' :=
      hT w w' (by omega) hpre hpre' hww g hg
    apply ih (fun w1 w1' h1 h2 h3 h4 g1 hg1 =>
        hT w1 w1' h1 h2 h3 h4 g1 (List.mem_cons_of_mem g hg1))
        (w ++ [step g w]) (w' ++ [step (T g) w'])
        (by rw [List.length_append]; simp; omega)
        (by rw [List.length_append]; simp; omega)
        (by rw [List.length_append]; simp;
            have hd : (g :: gs).length = gs.length + 1 := List.length_cons; omega)
    · intro j hj
      rw [getD_snoc_lt _ _ _ _ (by omega)]
      exact hpre j hj
    · intro j hj
      rw [getD_snoc_lt _ _ _ _ (by omega)]
      exact hpre' j hj
    · intro j hj
      rw [getD_snoc _ _ _ _, getD_snoc _ _ _ _]
      by_cases hj' : j = w'.length
      · subst hj'
        have he : w'.length = w.length := hwlen.symm
        rw [if_pos rfl, if_pos he]
        exact hval.symm
      · rw [if_neg hj', if_neg (by rw [hwlen]; exact hj')]
        exact hww j hj
    exact hi

private lemma all_filter_true (ins : List ℕ) (x1 : ℕ) (w : ℕ → Bool)
    (hx : w x1 = true) :
    (ins.map w).all id = ((ins.filter (fun i => i ≠ x1)).map w).all id := by
  induction ins with
  | nil => rfl
  | cons i rest ih =>
    by_cases hix : i = x1
    · subst hix
      rw [List.filter_cons_of_neg (by simpa using rfl)]
      simp only [List.map_cons, List.all_cons, hx, Bool.true_and, id_eq]
      exact ih
    · rw [List.filter_cons_of_pos (by simpa using hix)]
      simp only [List.map_cons, List.all_cons, id_eq]
      rw [ih]

private def Tt (x1 : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => ⟨GateOp.and, g.inputs.filter (fun i => i ≠ x1)⟩
  | GateOp.or => if x1 ∈ g.inputs then ⟨GateOp.and, []⟩ else g
  | GateOp.not => if g.inputs.head? = some x1 then ⟨GateOp.or, []⟩ else g
  | o => ⟨o, g.inputs⟩

-- Applying `sim` to the output wire: the eval equality.
private lemma eval_eq (x1 : ℕ) (gs : List Gate) (T : Gate → Gate) (z z' : List Bool)
    (hzlen : z'.length = z.length)
    (hz : ∀ i, i ≠ x1 → z'.getD i false = z.getD i false)
    (hT : ∀ w w' : List Bool, w'.length ≤ z'.length + gs.length →
        (∀ i, i < z.length → w.getD i false = z.getD i false) →
        (∀ i, i < z'.length → w'.getD i false = z'.getD i false) →
        (∀ i, i ≠ x1 → w'.getD i false = w.getD i false) →
        ∀ g ∈ gs, step g w = step (T g) w')
    (out : ℕ) (ho : out ≠ x1) :
    (wiresOf (gs.map T) z').getD out false = (wiresOf gs z).getD out false :=
  sim x1 z z' gs.length gs T hzlen hz hT z z' (le_refl _) hzlen.symm
    (le_refl _) (fun i _ => rfl) (fun i _ => rfl) hz out ho

end PEqualNP.Outside.L_meta_2596

theorem PEqualNP.Outside.L_meta_2596 :
    ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : Bool → Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.FanInTwo x4 → x4.output ≠ x1 →
    ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size ≤ x4.size ∧
    ∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8 ++ [!x8 x2]) =
      x4.eval (List.ofFn x8 ++ [x3 (x8 x2)]) := by
  intro x1 x2 x3 x4 hfan hout
  cases h3t : x3 true <;> cases h3f : x3 false
  -- case x3 = constantly false: redirect reads of wire x1 to a nonexistent wire
  · have hv : ∀ b : Bool, x3 b = false := fun b => by cases b <;> simp [h3t, h3f]
    refine ⟨⟨x4.gates.map (fun g =>
        ⟨g.op, g.inputs.map (fun i => if i = x1 then x1 + x4.size + 2 else i)⟩),
      x4.output⟩, ?_, ?_, ?_⟩
    · intro g' hg'
      rw [List.mem_map] at hg'
      rcases hg' with ⟨g, hg, rfl⟩
      have hf := hfan g hg
      refine ⟨hf.1, ?_⟩
      simp only [List.length_map]
      exact hf.2
    · show (x4.gates.map _).length ≤ x4.gates.length
      simp
    · intro x8
      show (PEqualNP.Outside.L_meta_2596.wiresOf (x4.gates.map _)
          (List.ofFn x8 ++ [!x8 x2])).getD x4.output false =
          (PEqualNP.Outside.L_meta_2596.wiresOf x4.gates
          (List.ofFn x8 ++ [x3 (x8 x2)])).getD x4.output false
      have e : (List.ofFn x8 ++ [!x8 x2]).length = x1 + 1 := by simp
      have e' : (List.ofFn x8 ++ [x3 (x8 x2)]).length = x1 + 1 := by simp
      have hz : ∀ i, i ≠ x1 →
          (List.ofFn x8 ++ [!x8 x2]).getD i false =
          (List.ofFn x8 ++ [x3 (x8 x2)]).getD i false := by
        intro i hi
        by_cases hlt : i < x1
        · rw [PEqualNP.Outside.L_meta_2596.getD_snoc_lt _ _ _ _ (by simpa using hlt),
            PEqualNP.Outside.L_meta_2596.getD_snoc_lt _ _ _ _ (by simpa using hlt)]
        · rw [PEqualNP.Outside.L_meta_2596.getD_ge _ _ _ (by rw [e]; omega),
            PEqualNP.Outside.L_meta_2596.getD_ge _ _ _ (by rw [e']; omega)]
      apply PEqualNP.Outside.L_meta_2596.eval_eq x1 x4.gates _ _ _ (by rw [e, e']) hz
        _ x4.output hout
      intro w w' hwb hpre hpre' hww g hg
      have hw1 : w.getD x1 false = x3 (x8 x2) := by
        rw [hpre x1 (by rw [e']; omega)]
        exact PEqualNP.Outside.L_meta_2596.getD_snoc_eq _ _ _ _ (by simp)
      have hB : w'.getD (x1 + x4.size + 2) false = false := by
        apply PEqualNP.Outside.L_meta_2596.getD_ge
        have es : x4.size = x4.gates.length := rfl
        omega
      simp only [PEqualNP.Outside.L_meta_2596.step]
      congr 1
      rw [List.map_map]
      apply PEqualNP.Outside.L_meta_2596.map_pointwise
      intro i hi
      by_cases hix : i = x1
      · subst hix
        simp only [Function.comp_apply, ↓reduceIte]
        rw [hB, hw1, hv (x8 x2)]
      · simp only [hix, Function.comp_apply, ↓reduceIte]
        exact (hww i hix).symm
  -- case x3 = not: nothing to change, the last bit already holds x3 of the bit
  · have hv : ∀ b : Bool, x3 b = !b := fun b => by cases b <;> simp [h3t, h3f]
    refine ⟨⟨x4.gates.map (fun g => g), x4.output⟩, ?_, ?_, ?_⟩
    · intro g' hg'
      rw [List.mem_map] at hg'
      rcases hg' with ⟨g, hg, rfl⟩
      exact hfan g hg
    · show (x4.gates.map _).length ≤ x4.gates.length
      simp
    · intro x8
      show (PEqualNP.Outside.L_meta_2596.wiresOf (x4.gates.map _)
          (List.ofFn x8 ++ [!x8 x2])).getD x4.output false =
          (PEqualNP.Outside.L_meta_2596.wiresOf x4.gates
          (List.ofFn x8 ++ [x3 (x8 x2)])).getD x4.output false
      have e : (List.ofFn x8 ++ [!x8 x2]).length = x1 + 1 := by simp
      have e' : (List.ofFn x8 ++ [x3 (x8 x2)]).length = x1 + 1 := by simp
      have hz : ∀ i, i ≠ x1 →
          (List.ofFn x8 ++ [!x8 x2]).getD i false =
          (List.ofFn x8 ++ [x3 (x8 x2)]).getD i false := by
        intro i hi
        by_cases hlt : i < x1
        · rw [PEqualNP.Outside.L_meta_2596.getD_snoc_lt _ _ _ _ (by simpa using hlt),
            PEqualNP.Outside.L_meta_2596.getD_snoc_lt _ _ _ _ (by simpa using hlt)]
        · rw [PEqualNP.Outside.L_meta_2596.getD_ge _ _ _ (by rw [e]; omega),
            PEqualNP.Outside.L_meta_2596.getD_ge _ _ _ (by rw [e']; omega)]
      apply PEqualNP.Outside.L_meta_2596.eval_eq x1 x4.gates _ _ _ (by rw [e, e']) hz
        _ x4.output hout
      intro w w' hwb hpre hpre' hww g hg
      have hw1 : w.getD x1 false = x3 (x8 x2) := by
        rw [hpre x1 (by rw [e']; omega)]
        exact PEqualNP.Outside.L_meta_2596.getD_snoc_eq _ _ _ _ (by simp)
      have hw1' : w'.getD x1 false = !x8 x2 := by
        rw [hpre' x1 (by rw [e]; omega)]
        exact PEqualNP.Outside.L_meta_2596.getD_snoc_eq _ _ _ _ (by simp)
      simp only [PEqualNP.Outside.L_meta_2596.step]
      congr 1
      apply PEqualNP.Outside.L_meta_2596.map_pointwise
      intro i hi
      by_cases hix : i = x1
      · subst hix
        rw [hw1', hw1, hv (x8 x2)]
      · exact (hww i hix).symm
  -- case x3 = identity: reads of wire x1 are redirected to wire x2, which holds the bit
  · have hv : ∀ b : Bool, x3 b = b := fun b => by cases b <;> simp [h3t, h3f]
    refine ⟨⟨x4.gates.map (fun g =>
        ⟨g.op, g.inputs.map (fun i => if i = x1 then ↑x2 else i)⟩),
      x4.output⟩, ?_, ?_, ?_⟩
    · intro g' hg'
      rw [List.mem_map] at hg'
      rcases hg' with ⟨g, hg, rfl⟩
      have hf := hfan g hg
      refine ⟨hf.1, ?_⟩
      simp only [List.length_map]
      exact hf.2
    · show (x4.gates.map _).length ≤ x4.gates.length
      simp
    · intro x8
      show (PEqualNP.Outside.L_meta_2596.wiresOf (x4.gates.map _)
          (List.ofFn x8 ++ [!x8 x2])).getD x4.output false =
          (PEqualNP.Outside.L_meta_2596.wiresOf x4.gates
          (List.ofFn x8 ++ [x3 (x8 x2)])).getD x4.output false
      have e : (List.ofFn x8 ++ [!x8 x2]).length = x1 + 1 := by simp
      have e' : (List.ofFn x8 ++ [x3 (x8 x2)]).length = x1 + 1 := by simp
      have hz : ∀ i, i ≠ x1 →
          (List.ofFn x8 ++ [!x8 x2]).getD i false =
          (List.ofFn x8 ++ [x3 (x8 x2)]).getD i false := by
        intro i hi
        by_cases hlt : i < x1
        · rw [PEqualNP.Outside.L_meta_2596.getD_snoc_lt _ _ _ _ (by simpa using hlt),
            PEqualNP.Outside.L_meta_2596.getD_snoc_lt _ _ _ _ (by simpa using hlt)]
        · rw [PEqualNP.Outside.L_meta_2596.getD_ge _ _ _ (by rw [e]; omega),
            PEqualNP.Outside.L_meta_2596.getD_ge _ _ _ (by rw [e']; omega)]
      apply PEqualNP.Outside.L_meta_2596.eval_eq x1 x4.gates _ _ _ (by rw [e, e']) hz
        _ x4.output hout
      intro w w' hwb hpre hpre' hww g hg
      have hw1 : w.getD x1 false = x3 (x8 x2) := by
        rw [hpre x1 (by rw [e']; omega)]
        exact PEqualNP.Outside.L_meta_2596.getD_snoc_eq _ _ _ _ (by simp)
      have h2 : (↑x2 : ℕ) < x1 := x2.isLt
      have hx2 : w'.getD (↑x2) false = x8 x2 := by
        rw [hpre' (↑x2) (by rw [e]; omega)]
        rw [PEqualNP.Outside.L_meta_2596.getD_snoc_lt _ _ _ _ (by simpa using h2)]
        rw [PEqualNP.Outside.L_meta_2596.getD_lt _ _ _ (by simpa using h2)]
        simp
      simp only [PEqualNP.Outside.L_meta_2596.step]
      congr 1
      rw [List.map_map]
      apply PEqualNP.Outside.L_meta_2596.map_pointwise
      intro i hi
      by_cases hix : i = x1
      · subst hix
        simp only [Function.comp_apply, ↓reduceIte]
        rw [hx2, hw1, hv (x8 x2)]
      · simp only [hix, Function.comp_apply, ↓reduceIte]
        exact (hww i hix).symm
  -- case x3 = constantly true: patch each gate so a read of x1 becomes true
  · have hv : ∀ b : Bool, x3 b = true := fun b => by cases b <;> simp [h3t, h3f]
    refine ⟨⟨x4.gates.map (PEqualNP.Outside.L_meta_2596.Tt x1), x4.output⟩, ?_, ?_, ?_⟩
    · intro g' hg'
      rw [List.mem_map] at hg'
      rcases hg' with ⟨g, hg, rfl⟩
      obtain ⟨op, ins⟩ := g
      obtain ⟨hop, hlen⟩ := hfan ⟨op, ins⟩ hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with rfl | rfl | rfl
      · simp only [PEqualNP.Outside.L_meta_2596.Tt]
        refine ⟨by simp, ?_⟩
        calc (ins.filter (fun i => i ≠ x1)).length ≤ ins.length :=
              List.length_filter_le _ ins
          _ ≤ 2 := hlen
      · by_cases hm : x1 ∈ ins
        · simp only [PEqualNP.Outside.L_meta_2596.Tt, hm, ite_true]
          refine ⟨by simp, by simp⟩
        · simp only [PEqualNP.Outside.L_meta_2596.Tt, hm, ite_false]
          refine ⟨by simp, hlen⟩
      · by_cases hh : ins.head? = some x1
        · simp only [PEqualNP.Outside.L_meta_2596.Tt, hh, ite_true]
          refine ⟨by simp, by simp⟩
        · simp only [PEqualNP.Outside.L_meta_2596.Tt, hh, ite_false]
          refine ⟨by simp, hlen⟩
    · show (x4.gates.map _).length ≤ x4.gates.length
      simp
    · intro x8
      show (PEqualNP.Outside.L_meta_2596.wiresOf (x4.gates.map _)
          (List.ofFn x8 ++ [!x8 x2])).getD x4.output false =
          (PEqualNP.Outside.L_meta_2596.wiresOf x4.gates
          (List.ofFn x8 ++ [x3 (x8 x2)])).getD x4.output false
      have e : (List.ofFn x8 ++ [!x8 x2]).length = x1 + 1 := by simp
      have e' : (List.ofFn x8 ++ [x3 (x8 x2)]).length = x1 + 1 := by simp
      have hz : ∀ i, i ≠ x1 →
          (List.ofFn x8 ++ [!x8 x2]).getD i false =
          (List.ofFn x8 ++ [x3 (x8 x2)]).getD i false := by
        intro i hi
        by_cases hlt : i < x1
        · rw [PEqualNP.Outside.L_meta_2596.getD_snoc_lt _ _ _ _ (by simpa using hlt),
            PEqualNP.Outside.L_meta_2596.getD_snoc_lt _ _ _ _ (by simpa using hlt)]
        · rw [PEqualNP.Outside.L_meta_2596.getD_ge _ _ _ (by rw [e]; omega),
            PEqualNP.Outside.L_meta_2596.getD_ge _ _ _ (by rw [e']; omega)]
      apply PEqualNP.Outside.L_meta_2596.eval_eq x1 x4.gates _ _ _ (by rw [e, e']) hz
        _ x4.output hout
      intro w w' hwb hpre hpre' hww g hg
      obtain ⟨op, ins⟩ := g
      obtain ⟨hop, hlen⟩ := hfan ⟨op, ins⟩ hg
      have hw1 : w.getD x1 false = true := by
        rw [hpre x1 (by rw [e']; omega)]
        rw [PEqualNP.Outside.L_meta_2596.getD_snoc_eq _ _ _ _ (by simp)]
        exact hv (x8 x2)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with rfl | rfl | rfl
      · simp only [PEqualNP.Outside.L_meta_2596.Tt, PEqualNP.Outside.L_meta_2596.step,
          PEqualNP.CircuitLowerBounds.GateOp.eval]
        rw [PEqualNP.Outside.L_meta_2596.all_filter_true ins x1
            (fun i => w.getD i false) hw1]
        congr 1
        apply PEqualNP.Outside.L_meta_2596.map_pointwise
        intro i hi
        rw [List.mem_filter] at hi
        exact (hww i (of_decide_eq_true hi.2)).symm
      · simp only [PEqualNP.Outside.L_meta_2596.Tt]
        by_cases hm : x1 ∈ ins
        · simp only [hm, ite_true, PEqualNP.Outside.L_meta_2596.step,
            PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_nil, List.all_nil]
          rw [List.any_eq_true]
          exact ⟨w.getD x1 false, List.mem_map.mpr ⟨x1, hm, rfl⟩, hw1⟩
        · simp only [hm, ite_false, PEqualNP.Outside.L_meta_2596.step]
          congr 1
          apply PEqualNP.Outside.L_meta_2596.map_pointwise
          intro i hi
          exact (hww i (fun h => hm (h ▸ hi))).symm
      · simp only [PEqualNP.Outside.L_meta_2596.Tt]
        by_cases hh : ins.head? = some x1
        · simp only [hh, ite_true, PEqualNP.Outside.L_meta_2596.step,
            PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_nil, List.any_nil]
          cases ins with
          | nil => simp at hh
          | cons i rest =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst hh
            simp only [List.map_cons, List.headD_cons, hw1, Bool.not_true]
        · simp only [hh, ite_false, PEqualNP.Outside.L_meta_2596.step,
            PEqualNP.CircuitLowerBounds.GateOp.eval]
          cases ins with
          | nil => rfl
          | cons i rest =>
            simp only [List.map_cons, List.headD_cons]
            congr 1
            simp only [List.head?_cons, Option.some.injEq] at hh
            exact (hww i hh).symm
