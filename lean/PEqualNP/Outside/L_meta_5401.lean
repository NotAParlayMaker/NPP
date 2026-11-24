import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_5401

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (xs : List Bool) : C.wires xs = C.gates.foldl stepW xs := rfl

theorem foldl_length (l : List Gate) (w : List Bool) :
    (l.foldl stepW w).length = w.length + l.length := by
  induction l generalizing w with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    simp only [stepW, List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldl_prefix (l : List Gate) (w : List Bool) : ∃ r, l.foldl stepW w = w ++ r := by
  induction l generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons a l ih =>
    obtain ⟨r, hr⟩ := ih (stepW w a)
    refine ⟨[a.op.eval (a.inputs.map fun i => w.getD i false)] ++ r, ?_⟩
    rw [List.foldl_cons, hr, stepW, List.append_assoc]

theorem getD_foldl_lt (l : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (l.foldl stepW w).getD i false = w.getD i false := by
  obtain ⟨r, hr⟩ := foldl_prefix l w
  rw [hr, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_lt (l : List Bool) (a : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [a]).getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

theorem all_mono (l : List ℕ) (u v : ℕ → Bool) (h : ∀ i, u i = true → v i = true) :
    (l.map u).all id = true → (l.map v).all id = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp, id]
  exact fun hu i hi => h i (hu i hi)

theorem any_mono (l : List ℕ) (u v : ℕ → Bool) (h : ∀ i, u i = true → v i = true) :
    (l.map u).any id = true → (l.map v).any id = true := by
  simp only [List.any_map, List.any_eq_true, Function.comp, id]
  exact fun ⟨i, hi, hu⟩ => ⟨i, hi, h i hu⟩

theorem mono_foldl (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ wx wy : List Bool, wx.length = wy.length →
      (∀ i, wx.getD i false = true → wy.getD i false = true) →
      ∀ i, (gs.foldl stepW wx).getD i false = true → (gs.foldl stepW wy).getD i false = true := by
  induction gs with
  | nil => intro wx wy _ h; exact h
  | cons g gs ih =>
    intro wx wy hl h
    rw [List.foldl_cons, List.foldl_cons]
    have hg := hgs g (by simp)
    apply ih (fun g' hg' => hgs g' (by simp [hg'])) _ _ (by simp [stepW, hl])
    intro i hi
    simp only [stepW] at hi ⊢
    rcases Nat.lt_trichotomy i wx.length with hlt | heq | hgt
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
        ← List.getD_eq_getElem?_getD] at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
      exact h i hi
    · subst heq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)] at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp only [Nat.sub_self, hl, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      rcases hg with hop | hop
      · rw [hop] at hi ⊢
        exact all_mono _ _ _ h hi
      · rw [hop] at hi ⊢
        exact any_mono _ _ _ h hi
    · rw [getD_ge _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)

-- Wire values of an AND/OR circuit only go up with the input.
theorem wire_mono {n : ℕ} (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  rw [wires_eq, wires_eq]
  exact mono_foldl C.gates hC (List.ofFn x) (List.ofFn y) (by simp) (by
    intro i hi
    by_cases hin : i < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
      simp only [hin, dif_pos] at hi ⊢
      exact hxy _ (by simpa using hi)
    · rw [getD_ge _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)) w

-- The value of gate t is its operation on the final values of the wires it reads.
theorem gate_val (gs : List Gate) (xs : List Bool) (t : ℕ) (ht : t < gs.length)
    (hin : ∀ i ∈ (gs[t]).inputs, i < xs.length + t) :
    (gs.foldl stepW xs).getD (xs.length + t) false =
      (gs[t]).op.eval ((gs[t]).inputs.map fun i => (gs.foldl stepW xs).getD i false) := by
  have hsplit : gs.foldl stepW xs =
      (gs.drop (t + 1)).foldl stepW ((gs.take (t + 1)).foldl stepW xs) := by
    rw [← List.foldl_append, List.take_append_drop]
  have htake : (gs.take (t + 1)).foldl stepW xs = stepW ((gs.take t).foldl stepW xs) gs[t] := by
    rw [List.take_succ, List.getElem?_eq_getElem ht, Option.toList_some, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
  have hlen : ((gs.take t).foldl stepW xs).length = xs.length + t := by
    rw [foldl_length, List.length_take]; omega
  have hsplit2 : gs.foldl stepW xs = (gs.drop t).foldl stepW ((gs.take t).foldl stepW xs) := by
    rw [← List.foldl_append, List.take_append_drop]
  rw [hsplit, getD_foldl_lt _ _ _ (by rw [htake]; simp [stepW, hlen]), htake]
  simp only [stepW]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := hin i hi
  conv_rhs => rw [getD_foldl_lt _ _ _ (by rw [List.length_append, hlen]; simp; omega),
    getD_snoc_lt _ _ _ (by rw [hlen]; exact hi')]

end PEqualNP.Outside.L_meta_5401

open PEqualNP.Outside.L_meta_5401

theorem PEqualNP.Outside.L_meta_5401 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (t : ℕ) (b : Fin 2) (u v w : Fin n), PEqualNP.TopForm.IsAO2 n C → t < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C t).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.BelowF G C t → u ≠ v → ¬ G.Adj u v → PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t b) (PEqualNP.EdgeOwnership.pairInput u v) = true → PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t (1 - b)) (PEqualNP.EdgeOwnership.pairInput w w) = true → w ≠ u ∧ w ≠ v ∧ (G.Adj u w ∨ G.Adj v w) := by
  intro n G _ C t b u v w hC ht hand hbelow huv hnadj hA hB
  obtain ⟨hops, hback, h2⟩ := hC
  let z : Fin n → Bool := fun i => decide (i = u ∨ i = v ∨ i = w)
  have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C t = C.gates[t] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, ht]
  have hlen2 : (C.gates[t]).inputs.length = 2 := h2 _ (List.getElem_mem ht)
  obtain ⟨i0, i1, hins⟩ : ∃ i0 i1, (C.gates[t]).inputs = [i0, i1] := by
    match hm : (C.gates[t]).inputs, hlen2 with
    | [i0, i1], _ => exact ⟨i0, i1, rfl⟩
  have hrb : ∀ i ∈ (C.gates[t]).inputs, i < n + t := by
    intro i hi
    have := hback t ht i
    rw [hgate] at this
    exact this hi
  -- both operands are true at the input with exactly u, v and w on
  have hz0 : (C.wires (List.ofFn z)).getD i0 false = true ∧
      (C.wires (List.ofFn z)).getD i1 false = true := by
    have hAu : (C.wires (List.ofFn z)).getD (PEqualNP.TopForm.opnd C t b) false = true :=
      wire_mono C hops _ z (by
        intro i hi
        simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
        simp only [z, decide_eq_true_eq]
        tauto) _ hA
    have hBw : (C.wires (List.ofFn z)).getD (PEqualNP.TopForm.opnd C t (1 - b)) false = true :=
      wire_mono C hops _ z (by
        intro i hi
        simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq, or_self] at hi
        simp only [z, decide_eq_true_eq]
        tauto) _ hB
    simp only [PEqualNP.TopForm.opnd, hgate, hins] at hAu hBw
    fin_cases b
    · exact ⟨by simpa using hAu, by simpa using hBw⟩
    · exact ⟨by simpa using hBw, by simpa using hAu⟩
  have hval : PEqualNP.EdgeOwnership.gateVal n C t z = true := by
    show (C.wires (List.ofFn z)).getD (n + t) false = true
    have hg := gate_val C.gates (List.ofFn z) t ht (by simpa using hrb)
    rw [List.length_ofFn] at hg
    have hand' : (C.gates[t]).op = GateOp.and := by rw [← hgate]; exact hand
    rw [wires_eq] at hz0
    rw [wires_eq, hg, hand', hins]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
      hz0.1, hz0.2, Bool.and_self]
  have hF := hbelow z hval
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty, false_and,
    exists_false, decide_false, Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨p, q, hpq, hp, hq⟩ := hF
  simp only [z, decide_eq_true_eq] at hp hq
  have hne : p ≠ q := hpq.ne
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first | exact absurd rfl hne | exact hnadj hpq | exact hnadj hpq.symm
  · rintro rfl
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first | exact absurd rfl hne | exact hnadj hpq | exact hnadj hpq.symm
  · rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first | exact absurd rfl hne | exact absurd hpq hnadj | exact absurd hpq.symm hnadj |
        exact Or.inl hpq | exact Or.inr hpq | exact Or.inl hpq.symm | exact Or.inr hpq.symm
