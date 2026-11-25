import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8853
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

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

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

theorem noread (i : ℕ) : ∀ (gs : List Gate) (U U' : List Bool), U.length = U'.length →
    i < U.length → (∀ g ∈ gs, i ∉ g.inputs) →
    (∀ t, t ≠ i → U.getD t false = U'.getD t false) →
    ∀ t, t ≠ i → (wf gs U).getD t false = (wf gs U').getD t false := by
  intro gs
  induction gs with
  | nil => intro U U' _ _ _ h t ht; exact h t ht
  | cons g gs ih =>
    intro U U' hlen hi hg h t ht
    rw [wf_cons, wf_cons]
    have hv : g.op.eval (g.inputs.map fun j => U.getD j false)
        = g.op.eval (g.inputs.map fun j => U'.getD j false) := by
      congr 1
      apply List.map_congr_left
      intro j hj
      exact h j (fun e => hg g List.mem_cons_self (e ▸ hj))
    rw [hv]
    refine ih _ _ (by simp [hlen]) (by simp; omega)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ t ht
    intro s hs
    rcases Nat.lt_trichotomy s U.length with h1 | h1 | h1
    · rw [getD_snoc_lt _ _ _ h1, getD_snoc_lt _ _ _ (by omega)]
      exact h s hs
    · rw [h1, getD_snoc_eq, hlen, getD_snoc_eq]
    · rw [getD_snoc_gt _ _ _ h1, getD_snoc_gt _ _ _ (by omega)]

theorem erase_fun (n : ℕ) (C : Circuit) (m : ℕ) (hm : m < C.gates.length)
    (hun : ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs) (ho : C.output ≠ n + m) :
    PEqualNP.MetaComplexity.circuitFun n
      ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m)), ren2 (n + m) C.output⟩
      = PEqualNP.MetaComplexity.circuitFun n C := by
  funext x
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

theorem erase_ao (n : ℕ) (C : Circuit) (m : ℕ) (hm : m < C.gates.length)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hun : ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs) :
    PEqualNP.TopForm.IsAO2 n
      ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m)), ren2 (n + m) C.output⟩ := by
  obtain ⟨hao, hrb, hl2⟩ := hAO
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hao g (List.mem_of_mem_take h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      exact hao g0 (List.mem_of_mem_drop hg0)
  · intro j hj i hi
    have hj' : j < (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m))).length := hj
    rw [gateAt_eq _ j hj] at hi
    have hi' : i ∈ ((C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m)))[j]'hj').inputs := hi
    have hlen := hj'
    rw [List.length_append, List.length_map, List.length_take, List.length_drop,
      Nat.min_eq_left (le_of_lt hm)] at hlen
    by_cases hjm : j < m
    · rw [List.getElem_append_left (by rw [List.length_take]; omega), List.getElem_take] at hi'
      exact hrb j (by omega) i (by rw [gateAt_eq C j (by omega)]; exact hi')
    · rw [List.getElem_append_right (by rw [List.length_take]; omega), List.getElem_map,
        List.getElem_drop] at hi'
      have hidx : m + 1 + (j - (C.gates.take m).length) = j + 1 := by
        rw [List.length_take, Nat.min_eq_left (le_of_lt hm)]; omega
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi'
      have hmem : C.gates[m + 1 + (j - (C.gates.take m).length)]'(by rw [hidx]; omega)
          ∈ C.gates.drop (m + 1) := by
        rw [← List.getElem_drop (h := by rw [List.length_drop, List.length_take,
          Nat.min_eq_left (le_of_lt hm)]; omega)]
        exact List.getElem_mem _
      have hne : i0 ≠ n + m := fun e => hun _ hmem (e ▸ hi0)
      have hlt := hrb (m + 1 + (j - (C.gates.take m).length)) (by rw [hidx]; omega) i0
        (by rw [gateAt_eq C _ (by rw [hidx]; omega)]; exact hi0)
      rw [hidx] at hlt
      unfold ren2
      split <;> omega
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hl2 g (List.mem_of_mem_take h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      show (g0.inputs.map _).length = 2
      rw [List.length_map]; exact hl2 g0 (List.mem_of_mem_drop hg0)

theorem dep_inc (N : ℕ) (S : Finset (Fin N × Fin N)) (σ : Equiv.Perm (Fin N)) (f : (Fin (N + N) → Bool) → Bool)
    (hmem : ∀ v : Fin N, (v, σ v) ∈ S)
    (hev : ∀ x : Fin (N + N) → Bool, f x = true ↔ ∃ (a : Fin N) (b : Fin N), (a, b) ∈ S ∧
      x (Fin.castAdd N a) = true ∧ x (Fin.natAdd N b) = true) :
    ∀ i : Fin (N + N), ∃ x : Fin (N + N) → Bool, f (Function.update x i (!x i)) ≠ f x := by
  have hcn : ∀ (a b : Fin N), Fin.castAdd N a ≠ Fin.natAdd N b := by
    intro a b e
    have := congrArg Fin.val e
    simp at this
    omega
  intro i
  refine Fin.addCases (fun p => ?_) (fun l => ?_) i
  · refine ⟨fun v => decide (v = Fin.natAdd N (σ p)), ?_⟩
    have hx0 : (decide (Fin.castAdd N p = Fin.natAdd N (σ p))) = false :=
      decide_eq_false (hcn p (σ p))
    intro heq
    have hA : f (Function.update (fun v => decide (v = Fin.natAdd N (σ p))) (Fin.castAdd N p)
        (!decide (Fin.castAdd N p = Fin.natAdd N (σ p)))) = true := by
      rw [hev]
      refine ⟨p, σ p, hmem p, ?_, ?_⟩
      · rw [Function.update_self, hx0]; rfl
      · rw [Function.update_of_ne (fun e => hcn p (σ p) e.symm)]
        exact decide_eq_true rfl
    rw [heq, hev] at hA
    obtain ⟨a, b, _, ha, _⟩ := hA
    exact hcn a (σ p) (of_decide_eq_true ha)
  · refine ⟨fun v => decide (v = Fin.castAdd N (σ.symm l)), ?_⟩
    have hx0 : (decide (Fin.natAdd N l = Fin.castAdd N (σ.symm l))) = false :=
      decide_eq_false (fun e => hcn (σ.symm l) l e.symm)
    intro heq
    have hml : (σ.symm l, l) ∈ S := by
      have := hmem (σ.symm l)
      rw [Equiv.apply_symm_apply] at this
      exact this
    have hA : f (Function.update (fun v => decide (v = Fin.castAdd N (σ.symm l))) (Fin.natAdd N l)
        (!decide (Fin.natAdd N l = Fin.castAdd N (σ.symm l)))) = true := by
      rw [hev]
      refine ⟨σ.symm l, l, hml, ?_, ?_⟩
      · rw [Function.update_of_ne (fun e => hcn (σ.symm l) l e)]
        exact decide_eq_true rfl
      · rw [Function.update_self, hx0]; rfl
    rw [heq, hev] at hA
    obtain ⟨a, b, _, _, hb⟩ := hA
    exact hcn (σ.symm l) b (of_decide_eq_true hb).symm

def eff (g : Gate) : List ℕ :=
  List.take (bif g.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) g.inputs

def tr (g : Gate) : Gate := ⟨g.op, eff g⟩

theorem tr_eval (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (f : ℕ → Bool) : (tr g).op.eval ((tr g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp [tr, eff, GateOp.eval, List.take_of_length_le hlen]
  · simp [tr, eff, GateOp.eval, List.take_of_length_le hlen]
  · cases ins with
    | nil => simp [tr, eff, GateOp.eval]
    | cons a t => simp [tr, eff, GateOp.eval]

theorem tr_wf : ∀ (gs : List Gate) (U : List Bool),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    wf (gs.map tr) U = wf gs U := by
  intro gs
  induction gs with
  | nil => intro U _; rfl
  | cons g gs ih =>
    intro U h
    rw [List.map_cons, wf_cons, wf_cons, tr_eval g (h g (List.mem_cons_self ..))]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

theorem eff_len (g : Gate) : (eff g).length ≤ g.inputs.length := by
  unfold eff
  rw [List.length_take]
  exact Nat.min_le_right _ _

theorem slots_le : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (gs.flatMap eff).length ≤ 2 * gs.length := by
  intro gs
  induction gs with
  | nil => intro _; simp
  | cons g gs ih =>
    intro h
    have h1 := eff_len g
    have h2 := h g (List.mem_cons_self ..)
    have h3 := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem split_len (p : ℕ → Bool) : ∀ l : List ℕ,
    (l.filter p).length + (l.filter fun a => !p a).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases h : p a = true
    · simp only [List.filter_cons, h, if_true, Bool.not_true, List.length_cons]
      simp only [Bool.false_eq_true, if_false]
      omega
    · have h' : p a = false := by simpa using h
      simp only [List.filter_cons, h', Bool.not_false, if_true, List.length_cons]
      simp only [Bool.false_eq_true, if_false]
      omega

theorem one_gate (n : ℕ) (l : List ℕ) :
    (Finset.univ.filter fun v : Fin n => l.contains v.val = true).card
      ≤ (l.filter fun w => decide (w < n)).length := by
  refine le_trans ?_ (List.toFinset_card_le _)
  refine Finset.card_le_card_of_injOn (fun v : Fin n => v.val) ?_ ?_
  · intro v hv
    have hv' : l.contains v.val = true := (Finset.mem_filter.1 hv).2
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨by simpa using hv', v.isLt⟩
  · intro v _ w _ h
    exact Fin.ext h

theorem inputs_cnt (n : ℕ) : ∀ gs : List Gate,
    (∑ v : Fin n, (gs.filter fun g => (eff g).contains v.val).length)
      ≤ ((gs.flatMap eff).filter fun w => decide (w < n)).length := by
  intro gs
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have h1 : ∀ v : Fin n, ((g :: gs).filter fun g => (eff g).contains v.val).length
        = (if (eff g).contains v.val = true then 1 else 0)
          + (gs.filter fun g => (eff g).contains v.val).length := by
      intro v
      rw [List.filter_cons]
      split_ifs
      · rw [List.length_cons]
        omega
      · omega
    simp only [h1, Finset.sum_add_distrib, List.flatMap_cons, List.filter_append, List.length_append]
    have h2 : (∑ v : Fin n, if (eff g).contains v.val = true then 1 else 0)
        = (Finset.univ.filter fun v : Fin n => (eff g).contains v.val = true).card := by
      rw [Finset.card_filter]
    rw [h2]
    exact Nat.add_le_add (one_gate n (eff g)) ih

end PEqualNP.Outside.L_meta_8853

open PEqualNP.Outside.L_meta_8853 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8853 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → (∀ x5 ∈ x3, ∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), (∀ (x9 : Fin x1), x9 ≠ x5 → x7 x9 = x8 x9) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x7 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x8) → x3.card + ∑ x6 ∈ x3ᶜ, (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs).contains ↑x6) x2.gates).length ≤ x2.size + (1 : ℕ) := by
  intro n C S hmin hess
  obtain ⟨hF, hleast⟩ := hmin
  have hok : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := hF
  have hval : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x
      = (wf C.gates (List.ofFn x)).getD C.output false := fun x => rfl
  have hval' : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x
      = (wf (C.gates.map tr) (List.ofFn x)).getD C.output false := fun x => by
    rw [tr_wf C.gates _ hok]; rfl
  have hF' : PEqualNP.MetaComplexity.FanInTwo ⟨C.gates.map tr, C.output⟩ := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(hok g0 hg0).1, le_trans (eff_len g0) (hok g0 hg0).2⟩
  have hfun' : PEqualNP.MetaComplexity.circuitFun n ⟨C.gates.map tr, C.output⟩
      = PEqualNP.MetaComplexity.circuitFun n C := by
    funext x
    exact (hval' x).symm
  -- every gate that is not the output is read
  have hread : ∀ m, m < C.gates.length → n + m ≠ C.output → ∃ g ∈ C.gates, n + m ∈ eff g := by
    intro m hm ho
    by_contra hno
    push_neg at hno
    obtain ⟨D, hD1, hD2, hD3⟩ := erase_unread n ⟨C.gates.map tr, C.output⟩ m (by simpa using hm) hF'
      (fun g hg => by
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 (List.mem_of_mem_drop hg)
        exact hno g0 hg0)
      (fun h => ho h.symm)
    have h1 := hleast D hD1 (hD3.trans hfun')
    have h2 : D.size + 1 = C.gates.length := by
      have : (⟨C.gates.map tr, C.output⟩ : Circuit).size = C.gates.length := by
        show (C.gates.map tr).length = C.gates.length
        simp
      omega
    have h3 : C.size = C.gates.length := rfl
    omega
  -- an essential input is read, or is the output
  have hinp : ∀ v ∈ S, (∃ g ∈ C.gates, v.val ∈ eff g) ∨ C.output = v.val := by
    intro v hv
    by_contra hno
    push_neg at hno
    obtain ⟨hno1, hno2⟩ := hno
    obtain ⟨x7, x8, hag, hne⟩ := hess v hv
    apply hne
    rw [hval', hval']
    exact noread v.val (C.gates.map tr) _ _ (by simp) (by simp) (fun g hg => by
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
        exact hno1 g0 hg0)
      (fun t ht => by
        by_cases htn : t < n
        · have e1 := getD_ofFn x7 ⟨t, htn⟩
          have e2 := getD_ofFn x8 ⟨t, htn⟩
          simp only at e1 e2
          rw [e1, e2]
          exact hag ⟨t, htn⟩ (fun h => ht (by rw [← h]))
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
      C.output hno2
  by_cases hbad : ∃ v ∈ S, ¬ ∃ g ∈ C.gates, v.val ∈ eff g
  · obtain ⟨v, hv, hnr⟩ := hbad
    have hout : C.output = v.val := (hinp v hv).resolve_left hnr
    have hkeep : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = x v := by
      intro x
      rw [hval, hout, wf_keep _ _ _ (by simp)]
      exact getD_ofFn x v
    have h0 := hleast ⟨[], C.output⟩ (by intro g hg; simp at hg) (by
      funext x
      rw [hkeep x]
      show (List.ofFn x).getD C.output false = x v
      rw [hout]
      exact getD_ofFn x v)
    have hnil : C.gates = [] := List.length_eq_zero_iff.mp (by
      have h1 : C.size = C.gates.length := rfl
      have h2 : (⟨[], C.output⟩ : Circuit).size = 0 := rfl
      omega)
    have hS : S ⊆ {v} := by
      intro u hu
      rw [Finset.mem_singleton]
      by_contra huv
      obtain ⟨x7, x8, hag, hne⟩ := hess u hu
      apply hne
      rw [hkeep, hkeep]
      exact hag v (fun h => huv h.symm)
    have hc := Finset.card_le_card hS
    rw [Finset.card_singleton] at hc
    have hsz : C.size = 0 := by show C.gates.length = 0; rw [hnil]; rfl
    rw [hnil, hsz]
    simp only [List.filter_nil, List.length_nil, Finset.sum_const_zero]
    omega
  · push_neg at hbad
    have hge : ∀ v ∈ S, 1 ≤ (C.gates.filter fun g => (eff g).contains v.val).length := by
      intro v hv
      obtain ⟨g, hg, hvg⟩ := hbad v hv
      exact List.length_pos_of_mem (List.mem_filter.2 ⟨hg, by simpa using hvg⟩)
    have h1 : S.card ≤ ∑ v ∈ S, (C.gates.filter fun g => (eff g).contains v.val).length := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum hge
    have h2 := Finset.sum_add_sum_compl S (fun v : Fin n => (C.gates.filter fun g => (eff g).contains v.val).length)
    have h3 := inputs_cnt n C.gates
    have h4 := split_len (fun w => decide (w < n)) (C.gates.flatMap eff)
    have h5 := slots_le C.gates (fun g hg => (hok g hg).2)
    have hW : ((Finset.range C.gates.length).image (fun m => n + m)).card = C.gates.length := by
      rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]
    have hsub : ((Finset.range C.gates.length).image (fun m => n + m)).erase C.output
        ⊆ ((C.gates.flatMap eff).filter fun a => !decide (a < n)).toFinset := by
      intro w hw
      rw [Finset.mem_erase, Finset.mem_image] at hw
      obtain ⟨hwo, m, hm, rfl⟩ := hw
      obtain ⟨g, hg, hmg⟩ := hread m (Finset.mem_range.1 hm) hwo
      simp only [List.mem_toFinset, List.mem_filter, List.mem_flatMap]
      exact ⟨⟨g, hg, hmg⟩, by simp⟩
    have ha := Finset.pred_card_le_card_erase (a := C.output)
      (s := (Finset.range C.gates.length).image (fun m => n + m))
    have hb := Finset.card_le_card hsub
    have hc := List.toFinset_card_le ((C.gates.flatMap eff).filter fun a => !decide (a < n))
    have hsz : C.size = C.gates.length := rfl
    show S.card + ∑ v ∈ Sᶜ, (C.gates.filter fun g => (eff g).contains v.val).length ≤ C.size + 1
    omega
