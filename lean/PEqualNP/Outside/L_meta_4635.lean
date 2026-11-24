import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4635
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

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def ren2 (q i : ℕ) : ℕ := if q < i then i - 1 else i

def rg2 (q : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren2 q)⟩

theorem sim2 (q : ℕ) (B : List Gate) : ∀ U U' : List Bool, U.length = U'.length + 1 →
    q < U.length → (∀ g ∈ B, q ∉ g.inputs) →
    (∀ i, i ≠ q → U.getD i false = U'.getD (ren2 q i) false) →
    ∀ i, i ≠ q → (wf B U).getD i false = (wf (B.map (rg2 q)) U').getD (ren2 q i) false := by
  induction B with
  | nil => intro U U' _ _ _ h i hi; exact h i hi
  | cons g B ih =>
    intro U U' hlen hq hB h i hi
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : g.op.eval (g.inputs.map fun i => U.getD i false)
        = (rg2 q g).op.eval ((rg2 q g).inputs.map fun i => U'.getD i false) := by
      show _ = g.op.eval ((g.inputs.map (ren2 q)).map fun i => U'.getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      exact h t (fun e => hB g List.mem_cons_self (e ▸ ht))
    refine ih _ _ (by simp [hlen]) (by simp; omega)
      (fun g' hg' => hB g' (List.mem_cons_of_mem _ hg')) ?_ i hi
    intro t ht
    rw [← hv]
    rcases Nat.lt_trichotomy t U.length with h1 | h1 | h1
    · have h2 : ren2 q t < U'.length := by
        unfold ren2
        split <;> omega
      rw [getD_snoc_lt _ _ _ h1, getD_snoc_lt _ _ _ h2]
      exact h t ht
    · have e : ren2 q t = U'.length := by
        unfold ren2
        rw [if_pos (by omega)]
        omega
      rw [e, getD_snoc_eq, h1, getD_snoc_eq]
    · have e : U'.length < ren2 q t := by
        unfold ren2
        rw [if_pos (by omega)]
        omega
      rw [getD_snoc_gt _ _ _ h1, getD_snoc_gt _ _ _ e]

theorem erase_unread (n : ℕ) (C : Circuit) (m : ℕ) (hm : m < C.gates.length)
    (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hun : ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs) (ho : C.output ≠ n + m) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 1 = C.size ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C := by
  refine ⟨⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m)), ren2 (n + m) C.output⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hF g (List.mem_of_mem_take h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hF g0 (List.mem_of_mem_drop hg0)
      refine ⟨this.1, ?_⟩
      show (g0.inputs.map _).length ≤ 2
      rw [List.length_map]; exact this.2
  · show (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m))).length + 1 = C.gates.length
    rw [List.length_append, List.length_map, List.length_take, List.length_drop]
    omega
  · funext x
    have hX : (List.ofFn x).length = n := by simp
    have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
      rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
    have hPl : (wf (C.gates.take m) (List.ofFn x)).length = n + m := by
      rw [wf_len, List.length_take, hX, Nat.min_eq_left (le_of_lt hm)]
    have e1 : wf C.gates (List.ofFn x) = wf (C.gates.drop (m + 1))
        (wf (C.gates.take m) (List.ofFn x) ++ [C.gates[m].op.eval (C.gates[m].inputs.map
          fun i => (wf (C.gates.take m) (List.ofFn x)).getD i false)]) := by
      conv_lhs => rw [hsplit]
      rw [wf_append, wf_cons]
    have e2 : wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m))) (List.ofFn x)
        = wf ((C.gates.drop (m + 1)).map (rg2 (n + m))) (wf (C.gates.take m) (List.ofFn x)) :=
      wf_append _ _ _
    show (wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m))) (List.ofFn x)).getD
        (ren2 (n + m) C.output) false = (wf C.gates (List.ofFn x)).getD C.output false
    rw [e1, e2]
    symm
    apply sim2 (n + m) _ _ _ (by rw [List.length_append, hPl]; rfl)
      (by rw [List.length_append, hPl]; simp) hun ?_ _ ho
    intro i hi
    rcases Nat.lt_or_gt_of_ne hi with h1 | h1
    · have e : ren2 (n + m) i = i := by unfold ren2; rw [if_neg (by omega)]
      rw [e, getD_snoc_lt _ _ _ (by rw [hPl]; exact h1)]
    · have e : ren2 (n + m) i = i - 1 := by unfold ren2; rw [if_pos h1]
      rw [e, getD_snoc_gt _ _ _ (by rw [hPl]; exact h1),
        List.getD_eq_default _ _ (by rw [hPl]; omega)]

end PEqualNP.Outside.L_meta_4635

open PEqualNP.Outside.L_meta_4635 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4635 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → (0 : ℕ) < x2.size → x2.output + (1 : ℕ) = x1 + x2.size ∧ ∀ (x5 : ℕ), x5 + (1 : ℕ) < x2.size → ∃ (x7 : Fin x2.gates.length), x5 < ↑x7 ∧ x1 + x5 ∈ (x2.gates.get x7).inputs := by
  intro n C hmin hpos
  obtain ⟨hF, hle⟩ := hmin
  have hpos' : 0 < C.gates.length := hpos
  have hout : C.output + 1 = n + C.gates.length := by
    by_contra hne
    have hD := hle ⟨C.gates.take (C.gates.length - 1), C.output⟩
      (fun g hg => hF g (List.mem_of_mem_take hg)) (by
        funext x
        have hX : (List.ofFn x).length = n := by simp
        show (wf (C.gates.take (C.gates.length - 1)) (List.ofFn x)).getD C.output false
          = (wf C.gates (List.ofFn x)).getD C.output false
        by_cases h1 : C.output < n + (C.gates.length - 1)
        · exact (wire_take C.gates (List.ofFn x) (C.gates.length - 1) C.output
            (by rw [hX]; exact h1) (by omega)).symm
        · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, hX]; omega),
            List.getD_eq_default _ _ (by rw [wf_len, hX]; omega)])
    have hsz : C.gates.length ≤ (C.gates.take (C.gates.length - 1)).length := hD
    rw [List.length_take] at hsz
    omega
  refine ⟨hout, ?_⟩
  intro m hm
  have hm' : m + 1 < C.gates.length := hm
  by_contra hno
  have hun : ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs := by
    intro g hg hin
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at e
    rw [List.length_drop] at hi
    apply hno
    refine ⟨⟨m + 1 + i, by omega⟩, by show m < m + 1 + i; omega, ?_⟩
    show n + m ∈ (C.gates[m + 1 + i]).inputs
    rw [e]; exact hin
  obtain ⟨D, hDF, hDs, hDf⟩ := erase_unread n C m (by omega) hF hun (by omega)
  have := hle D hDF hDf
  have hDs' : D.size + 1 = C.size := hDs
  omega
