import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3166
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def ren (n m p i : ℕ) : ℕ := if i = n + m then p else if n + m < i then i - 1 else i

def rg (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren n m p)⟩

theorem sim (n m p : ℕ) (hp : p < n + m) (B : List Gate) : ∀ U U' : List Bool, U.length = U'.length + 1 →
    n + m < U.length → (∀ i, U.getD i false = U'.getD (ren n m p i) false) →
    ∀ i, (wf B U).getD i false = (wf (B.map (rg n m p)) U').getD (ren n m p i) false := by
  induction B with
  | nil => intro U U' _ _ h i; exact h i
  | cons g B ih =>
    intro U U' hlen hbig h i
    rw [List.map_cons, wf_cons, wf_cons]
    refine ih _ _ (by simp [hlen]) (by simp; omega) ?_ i
    intro t
    have hv : g.op.eval (g.inputs.map fun i => U.getD i false)
        = (rg n m p g).op.eval ((rg n m p g).inputs.map fun i => U'.getD i false) := by
      show _ = g.op.eval ((g.inputs.map (ren n m p)).map fun i => U'.getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    rw [← hv]
    rcases Nat.lt_trichotomy t U.length with ht | ht | ht
    · have h1 : ren n m p t < U'.length := by
        unfold ren
        split
        · omega
        · split <;> omega
      rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ h1]
      exact h t
    · subst ht
      rw [getD_snoc_eq]
      have e : ren n m p U.length = U'.length := by
        unfold ren
        rw [ite_eq_right (by omega), ite_eq_left hbig]
        omega
      rw [e, getD_snoc_eq]
    · rw [getD_snoc_gt _ _ _ ht]
      have e : U'.length < ren n m p t := by
        unfold ren
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        omega
      rw [getD_snoc_gt _ _ _ e]

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

theorem dropin (d : ℕ) (gs : List Gate) : (∀ g ∈ gs, d ∉ g.inputs) → ∀ U U' : List Bool,
    U'.length = U.length + 1 → d < U'.length →
    (∀ i, i ≠ d → U'.getD i false = U.getD (if d < i then i - 1 else i) false) →
    ∀ i, i ≠ d → (wf gs U').getD i false
      = (wf (gs.map fun g => (⟨g.op, g.inputs.map fun i => if d < i then i - 1 else i⟩ : Gate)) U).getD
          (if d < i then i - 1 else i) false := by
  induction gs with
  | nil => intro _ U U' _ _ h i hi; exact h i hi
  | cons g gs ih =>
    intro hno U U' hlen hd h i hi
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : g.op.eval (g.inputs.map fun i => U'.getD i false)
        = g.op.eval ((g.inputs.map fun i => if d < i then i - 1 else i).map fun i => U.getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      exact h t (fun e => hno g (by simp) (e ▸ ht))
    show (wf gs (U' ++ [g.op.eval (g.inputs.map fun i => U'.getD i false)])).getD i false
      = (wf (gs.map fun g => (⟨g.op, g.inputs.map fun i => if d < i then i - 1 else i⟩ : Gate))
          (U ++ [g.op.eval ((g.inputs.map fun i => if d < i then i - 1 else i).map fun i => U.getD i false)])).getD
          (if d < i then i - 1 else i) false
    rw [← hv]
    refine ih (fun g' hg' => hno g' (by simp [hg'])) _ _ (by simp [hlen]) (by simp; omega) ?_ i hi
    intro t ht
    rcases Nat.lt_trichotomy t U'.length with hlt | heq | hgt
    · have h1 : (if d < t then t - 1 else t) < U.length := by split <;> omega
      rw [getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ h1]
      exact h t ht
    · have h1 : (if d < t then t - 1 else t) = U.length := by rw [if_pos (by omega)]; omega
      rw [h1, getD_snoc_eq, heq, getD_snoc_eq]
    · have h1 : U.length < (if d < t then t - 1 else t) := by rw [if_pos (by omega)]; omega
      rw [getD_snoc_gt _ _ _ hgt, getD_snoc_gt _ _ _ h1]

end PEqualNP.Outside.L_meta_3166

open PEqualNP.Outside.L_meta_3166 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3166 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x2 = (0 : ℕ) ∨ x2 = (2 : ℕ) → PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 → x1.output ≠ (9 : ℕ) → List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) x1.gates = [x3] → x3.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3.inputs = [(9 : ℕ), x2] ∨ x3.inputs = [x2, (9 : ℕ)] → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x11 ∧ x11.size + (1 : ℕ) = x1.size ∧ ∀ (x12 : Fin (9 : ℕ) → Bool), x11.eval (List.ofFn x12) = x1.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ))]) := by
  intro C x2 x3 hx2 hC hrb hout hfil hop hin
  have hx3mem : x3 ∈ C.gates := by
    have : x3 ∈ List.filter (fun (x8 : Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) C.gates := by rw [hfil]; simp
    exact (List.mem_filter.mp this).1
  have h9x3 : (9 : ℕ) ∈ x3.inputs := by rcases hin with h | h <;> rw [h] <;> simp
  obtain ⟨m, hm, hgm⟩ := List.getElem_of_mem hx3mem
  have h1 : C.gates = C.gates.take m ++ x3 :: C.gates.drop (m + 1) := by
    rw [← hgm, ← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have hAB : (∀ g ∈ C.gates.take m, (9 : ℕ) ∉ g.inputs) ∧ (∀ g ∈ C.gates.drop (m + 1), (9 : ℕ) ∉ g.inputs) := by
    have hf := hfil
    rw [h1, List.filter_append, List.filter_cons_of_pos (by simpa using h9x3)] at hf
    have hl := congrArg List.length hf
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    have ha : (List.filter (fun (x8 : Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) (C.gates.take m)).length = 0 := by omega
    have hb : (List.filter (fun (x8 : Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) (C.gates.drop (m + 1))).length = 0 := by omega
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at ha hb
    exact ⟨fun g hg => by simpa using ha g hg, fun g hg => by simpa using hb g hg⟩
  have hp : x2 < 10 + m := by rcases hx2 with h | h <;> omega
  have hx29 : x2 ≠ 9 := by rcases hx2 with h | h <;> omega
  have hG : ∀ j (hj : j < C.gates.length), PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] :=
    fun j hj => gateAt_eq C j hj
  have hBlt : ∀ g ∈ C.gates.drop (m + 1), ∀ i ∈ g.inputs, i ≠ 9 := by
    intro g hg i hi e
    exact hAB.2 g hg (e ▸ hi)
  refine ⟨⟨(C.gates.take m ++ (C.gates.drop (m + 1)).map (rg 10 m x2)).map
      (fun g => (⟨g.op, g.inputs.map fun i => if 9 < i then i - 1 else i⟩ : Gate)),
    (if 9 < ren 10 m x2 C.output then ren 10 m x2 C.output - 1 else ren 10 m x2 C.output)⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    rw [List.mem_append] at hg0
    rcases hg0 with hg0 | hg0
    · have := hC g0 (List.mem_of_mem_take hg0)
      exact ⟨this.1, by simpa using this.2⟩
    · obtain ⟨g1, hg1, rfl⟩ := List.mem_map.mp hg0
      have := hC g1 (List.mem_of_mem_drop hg1)
      exact ⟨this.1, by simpa [rg] using this.2⟩
  · simp [Circuit.size]; omega
  · intro x
    have hXlen : (List.ofFn x ++ [x 0 && x 2]).length = 10 := by simp
    have hWlen : (wf (C.gates.take m) (List.ofFn x ++ [x 0 && x 2])).length = 10 + m := by
      rw [wf_len, hXlen, List.length_take, Nat.min_eq_left (le_of_lt hm)]
    have e1 : wf C.gates (List.ofFn x ++ [x 0 && x 2]) = wf (C.gates.drop (m + 1))
        (wf (C.gates.take m) (List.ofFn x ++ [x 0 && x 2]) ++ [x3.op.eval (x3.inputs.map fun i => (wf (C.gates.take m) (List.ofFn x ++ [x 0 && x 2])).getD i false)]) := by
      conv_lhs => rw [h1]
      rw [wf_append, wf_cons]
    have hW9 : (wf (C.gates.take m) (List.ofFn x ++ [x 0 && x 2])).getD 9 false = (x 0 && x 2) := by
      rw [wf_keep _ _ _ (by rw [hXlen]; omega)]
      have : (List.ofFn x ++ [x 0 && x 2]).getD (List.ofFn x).length false = (x 0 && x 2) := getD_snoc_eq _ _
      rw [List.length_ofFn] at this
      exact this
    have hW0 : (wf (C.gates.take m) (List.ofFn x ++ [x 0 && x 2])).getD 0 false = x 0 := by
      rw [wf_keep _ _ _ (by rw [hXlen]; omega), List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    have hW2 : (wf (C.gates.take m) (List.ofFn x ++ [x 0 && x 2])).getD 2 false = x 2 := by
      rw [wf_keep _ _ _ (by rw [hXlen]; omega), List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    have hval : x3.op.eval (x3.inputs.map fun i => (wf (C.gates.take m) (List.ofFn x ++ [x 0 && x 2])).getD i false)
        = (wf (C.gates.take m) (List.ofFn x ++ [x 0 && x 2])).getD x2 false := by
      rw [hop]
      rcases hx2 with h' | h' <;> subst h' <;> rcases hin with h | h <;> rw [h] <;>
        simp only [List.map_cons, List.map_nil] <;> rw [hW9] <;>
        first
          | (rw [hW0]; cases x 0 <;> cases x 2 <;> rfl)
          | (rw [hW2]; cases x 0 <;> cases x 2 <;> rfl)
    show (wf ((C.gates.take m ++ (C.gates.drop (m + 1)).map (rg 10 m x2)).map
        (fun g => (⟨g.op, g.inputs.map fun i => if 9 < i then i - 1 else i⟩ : Gate))) (List.ofFn x)).getD
        (if 9 < ren 10 m x2 C.output then ren 10 m x2 C.output - 1 else ren 10 m x2 C.output) false
      = (wf C.gates (List.ofFn x ++ [x 0 && x 2])).getD C.output false
    rw [e1, hval]
    generalize hWdef : wf (C.gates.take m) (List.ofFn x ++ [x 0 && x 2]) = W at *
    have s1 := sim 10 m x2 hp (C.gates.drop (m + 1)) (W ++ [W.getD x2 false]) W (by simp) (by simp; omega) (by
      intro i
      unfold ren
      split
      · rename_i h; rw [h, ← hWlen, getD_snoc_eq]
      · split
        · rw [getD_snoc_gt _ _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · rw [getD_snoc_lt _ _ _ (by omega)]) C.output
    rw [s1, ← hWdef, ← wf_append]
    have hren9 : ren 10 m x2 C.output ≠ 9 := by
      unfold ren
      split
      · exact hx29
      · split <;> omega
    refine (dropin 9 _ ?_ (List.ofFn x) (List.ofFn x ++ [x 0 && x 2]) (by simp) (by simp) ?_ _ hren9).symm
    · intro g hg
      rw [List.mem_append] at hg
      rcases hg with hg | hg
      · exact hAB.1 g hg
      · obtain ⟨g1, hg1, rfl⟩ := List.mem_map.mp hg
        intro h9
        simp only [rg, List.mem_map] at h9
        obtain ⟨i0, hi0, hi9⟩ := h9
        have hne := hBlt g1 hg1 i0 hi0
        unfold ren at hi9
        split at hi9
        · exact hx29 hi9
        · split at hi9 <;> omega
    · intro i hi
      by_cases h9 : 9 < i
      · rw [if_pos h9, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      · rw [if_neg h9, List.getD_append _ _ _ _ (by simp; omega)]
