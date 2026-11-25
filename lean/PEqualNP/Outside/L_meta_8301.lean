import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8301
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

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

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def ren (n m p i : ℕ) : ℕ := if i = n + m then p else if n + m < i then i - 1 else i

def rg (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren n m p)⟩

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

theorem evalT (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (ins.map f) = true → op.eval (ins.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem evalb (b : Bool) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = b → f' i = b) :
    op.eval (ins.map f) = b → op.eval (ins.map f') = b := by
  cases b
  · intro hf
    by_contra hc
    have hc' : op.eval (ins.map f') = true := by simpa using hc
    have h3 := evalT op hop ins f' f (fun i hi => by
      by_contra hn
      have h4 := h i (by simpa using hn)
      rw [h4] at hi
      exact absurd hi (by simp)) hc'
    rw [hf] at h3
    exact absurd h3 (by simp)
  · exact evalT op hop ins f f' h

theorem simb (b : Bool) (n m p : ℕ) (B : List Gate)
    (hB : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ U U' : List Bool, U.length = U'.length + 1 → n + m < U.length →
    (p < n + m ∨ U'.length + B.length < p) →
    (∀ i, U.getD i false = b → U'.getD (ren n m p i) false = b) →
    ∀ i, (wf B U).getD i false = b → (wf (B.map (rg n m p)) U').getD (ren n m p i) false = b := by
  induction B with
  | nil => intro U U' _ _ _ h i; exact h i
  | cons g B ih =>
    intro U U' hlen hbig hp h i
    rw [List.map_cons, wf_cons, wf_cons]
    refine ih (fun g' hg' => hB g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen])
      (by simp; omega) ?_ ?_ i
    · rcases hp with hp | hp
      · exact Or.inl hp
      · right
        simp only [List.length_cons, List.length_append, List.length_nil] at hp ⊢
        omega
    · intro t ht
      have hv : g.op.eval (g.inputs.map fun i => U.getD i false) = b →
          (rg n m p g).op.eval ((rg n m p g).inputs.map fun i => U'.getD i false) = b := by
        intro hb
        show g.op.eval ((g.inputs.map (ren n m p)).map fun i => U'.getD i false) = b
        rw [List.map_map]
        exact evalb b g.op (hB g (List.mem_cons_self ..)) g.inputs _ _ (fun i hi => h i hi) hb
      rcases Nat.lt_trichotomy t U.length with htl | htl | htl
      · rw [getD_snoc_lt _ _ _ htl] at ht
        have h0 := h t ht
        by_cases htm : t = n + m
        · have e : ren n m p t = p := by unfold ren; rw [if_pos htm]
          rw [e] at h0 ⊢
          rcases hp with hp | hp
          · rw [getD_snoc_lt _ _ _ (by omega)]; exact h0
          · simp only [List.length_cons] at hp
            rw [getD_snoc_gt _ _ _ (by omega)]
            rw [List.getD_eq_default _ _ (by omega)] at h0
            exact h0
        · have h1 : ren n m p t < U'.length := by
            unfold ren
            rw [if_neg htm]
            split <;> omega
          rw [getD_snoc_lt _ _ _ h1]; exact h0
      · subst htl
        rw [getD_snoc_eq] at ht
        have e : ren n m p U.length = U'.length := by
          unfold ren
          rw [if_neg (by omega), if_pos hbig]
          omega
        rw [e, getD_snoc_eq]; exact hv ht
      · rw [getD_snoc_gt _ _ _ htl] at ht
        have e : U'.length < ren n m p t := by
          unfold ren
          rw [if_neg (by omega), if_pos (by omega)]
          omega
        rw [getD_snoc_gt _ _ _ e]; exact ht

theorem erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hml : m < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C m p
      = ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p), ren n m p C.output⟩ := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hml]
  rfl

theorem erase_sim (n : ℕ) (C : Circuit) (m p : ℕ) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hml : m < C.gates.length) (hp : p < n + m ∨ p = n + C.gates.length) (x : List Bool)
    (hx : x.length = n) (b : Bool)
    (hb : (wf C.gates x).getD (n + m) false = b → (wf C.gates x).getD p false = b) (w : ℕ)
    (hw : (wf C.gates x).getD w false = b) :
    (wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)) x).getD (ren n m p w) false = b := by
  have h2 : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hml, List.take_append_drop]
  have hWlen : (wf (C.gates.take m) x).length = n + m := by
    rw [wf_len, hx, List.length_take, Nat.min_eq_left (le_of_lt hml)]
  have e1 : wf C.gates x = wf (C.gates.drop (m + 1))
      (wf (C.gates.take m) x ++ [C.gates[m].op.eval (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false)]) := by
    conv_lhs => rw [h2]
    rw [wf_append, wf_cons]
  have hfull : (wf C.gates x).length = n + C.gates.length := by rw [wf_len, hx]
  rw [wf_append]
  rw [e1] at hw hb
  have hdl : (C.gates.drop (m + 1)).length = C.gates.length - (m + 1) := List.length_drop
  refine simb b n m p (C.gates.drop (m + 1))
    (fun g hg => (hm g (List.mem_of_mem_drop hg)).1) _ _ (by simp) (by simp; omega) ?_ ?_ w hw
  · rcases hp with hp | hp
    · exact Or.inl hp
    · right; rw [hWlen, hdl, hp]; omega
  · intro i hi
    unfold ren
    split
    · rename_i hinm
      subst hinm
      rw [wf_keep _ _ _ (by simp; omega)] at hb
      have h3 := hb hi
      rcases hp with hp | hp
      · rw [wf_keep _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)] at h3
        exact h3
      · rw [← e1, List.getD_eq_default _ _ (by rw [hfull, hp])] at h3
        rw [List.getD_eq_default _ _ (by rw [hWlen, hp]; omega)]
        exact h3
    · split
      · rw [getD_snoc_gt _ _ _ (by omega)] at hi
        rw [List.getD_eq_default _ _ (by omega)]
        exact hi
      · rw [getD_snoc_lt _ _ _ (by omega)] at hi
        exact hi

theorem gate_in (n : ℕ) (C : Circuit) (m p : ℕ) (hml : m < C.gates.length)
    (hop : C.gates[m].op = GateOp.and ∨ C.gates[m].op = GateOp.or) (hpin : p ∈ C.gates[m].inputs)
    (hp : p < n + m) (x : List Bool) (hx : x.length = n) :
    (wf C.gates x).getD (n + m) false = C.gates[m].op.eval [] →
    (wf C.gates x).getD p false = C.gates[m].op.eval [] := by
  subst hx
  rw [gate_val C.gates x m hml, wire_take C.gates x m p hp (le_of_lt hml)]
  rcases hop with h | h
  · rw [h]
    show (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).all id = true → _ = true
    intro hall
    exact List.all_eq_true.1 hall _ (List.mem_map.2 ⟨p, hpin, rfl⟩)
  · rw [h]
    show (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).any id = false → _ = false
    intro hany
    cases hq : (wf (C.gates.take m) x).getD p false
    · rfl
    · exfalso
      have h5 : (C.gates[m].inputs.map fun i => (wf (C.gates.take m) x).getD i false).any id = true :=
        List.any_eq_true.2 ⟨true, List.mem_map.2 ⟨p, hpin, hq⟩, rfl⟩
      rw [h5] at hany
      exact absurd hany (by simp)

def restrG (v : ℕ) (g : Gate) : Gate :=
  if v ∈ g.inputs then
    ⟨GateOp.or, match g.op with
      | GateOp.and => []
      | _ => g.inputs.filter (fun i => decide (i ≠ v))⟩
  else g

theorem restr_eval (v : ℕ) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f : ℕ → Bool)
    (hf : f v = false) :
    (restrG v g).op.eval ((restrG v g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, ins⟩ := g
  unfold restrG
  by_cases h : v ∈ ins
  · simp only [if_pos h]
    rcases hop with ho | ho
    · simp only at ho
      subst ho
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [Bool.eq_false_iff]
      intro hall
      rw [List.all_eq_true] at hall
      have := hall (f v) (List.mem_map.2 ⟨v, h, rfl⟩)
      rw [hf] at this
      exact absurd this (by simp)
    · simp only at ho
      subst ho
      simp only [GateOp.eval]
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨b, hb, hb2⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
        exact ⟨f i, List.mem_map.2 ⟨i, (List.mem_filter.1 hi).1, rfl⟩, hb2⟩
      · rintro ⟨b, hb, hb2⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
        refine ⟨f i, List.mem_map.2 ⟨i, List.mem_filter.2 ⟨hi, ?_⟩, rfl⟩, hb2⟩
        have : i ≠ v := by
          rintro rfl
          rw [hf] at hb2
          exact absurd hb2 (by simp)
        simpa using this
  · simp only [if_neg h]

theorem restr_wf (v : ℕ) : ∀ (gs : List Gate) (U : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → v < U.length → U.getD v false = false →
    wf (gs.map (restrG v)) U = wf gs U := by
  intro gs
  induction gs with
  | nil => intro U _ _ _; rfl
  | cons g gs ih =>
    intro U hop hv hU
    rw [List.map_cons, wf_cons, wf_cons, restr_eval v g (hop g (List.mem_cons_self ..)) _ hU]
    refine ih _ (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) (by simp; omega) ?_
    rw [List.getD_append _ _ _ _ hv]
    exact hU

theorem restr_noread (v : ℕ) (g : Gate) : v ∉ (restrG v g).inputs := by
  unfold restrG
  by_cases h : v ∈ g.inputs
  · simp only [if_pos h]
    cases g.op <;> simp
  · simp only [if_neg h]
    exact h

theorem restr_mono (v : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (restrG v g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (restrG v g).inputs.length ≤ 2 := by
  unfold restrG
  by_cases hv : v ∈ g.inputs
  · simp only [if_pos hv]
    refine ⟨by simp, ?_⟩
    have := List.length_filter_le (fun i => decide (i ≠ v)) g.inputs
    cases g.op <;> dsimp only <;> first | omega | (simp only [List.length_nil]; omega)
  · simp only [if_neg hv]
    exact h

theorem restr_short (v : ℕ) (g : Gate) (h : g.inputs.length ≤ 2) (hv : v ∈ g.inputs) :
    (restrG v g).op = GateOp.or ∧ (restrG v g).inputs.length ≤ 1 := by
  unfold restrG
  simp only [if_pos hv]
  refine ⟨trivial, ?_⟩
  have h1 : (g.inputs.filter (fun i => decide (i ≠ v))).length < g.inputs.length :=
    List.length_filter_lt_length_iff_exists.2 ⟨v, hv, by simp⟩
  cases g.op <;> dsimp only <;> first | omega | (simp only [List.length_nil]; omega)

theorem drop_copy (n : ℕ) (C : Circuit) (m p : ℕ) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hml : m < C.gates.length) (hp : p < n + m ∨ p = n + C.gates.length)
    (heq : ∀ x : Fin n → Bool, (wf C.gates (List.ofFn x)).getD (n + m) false
      = (wf C.gates (List.ofFn x)).getD p false) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.gates.length + 1 = C.gates.length ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C := by
  refine ⟨⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p), ren n m p C.output⟩, ?_, ?_, ?_⟩
  · intro g hg'
    simp only [List.mem_append, List.mem_map] at hg'
    rcases hg' with hg' | ⟨g0, hg0, rfl⟩
    · exact hm g (List.mem_of_mem_take hg')
    · have := hm g0 (List.mem_of_mem_drop hg0)
      exact ⟨this.1, by simpa [rg] using this.2⟩
  · simp
    omega
  · funext x
    show (wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p))
      (List.ofFn x)).getD (ren n m p C.output) false
      = (wf C.gates (List.ofFn x)).getD C.output false
    exact erase_sim n C m p hm hml hp (List.ofFn x) (by simp) _
      (fun h => by rw [← heq x, h]) C.output rfl

end PEqualNP.Outside.L_meta_8301

open PEqualNP.Outside.L_meta_8301 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8301 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Fin x1), (∃ (x5 : Fin x1), x2.Adj x4 x5) → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ x9.size < x6.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x9 = PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.Library.Peel.delVerts x2 {x4}) ∅ := by
  intro n G _ a ⟨b, hab⟩ C hm hf
  have hone : ∀ (c : Fin n) (y : Fin n → Bool), (∀ i, y i = true → i = c) →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = false := by
    intro c y hy
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_false_iff_not]
    rintro ⟨u, w, huw, hu, hw⟩
    rw [hy u hu, hy w hw] at huw
    exact G.loopless.irrefl c huw
  have hval : ∀ y : Fin n → Bool, (wf C.gates (List.ofFn y)).getD C.output false
      = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y := fun y => congrFun hf y
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    simpa using (hm g hg).1
  have hout : C.output ≠ a.val := by
    intro h
    have h1 := hval (fun i => decide (i = a))
    rw [hone a _ (by simp), h, wf_keep _ _ _ (by simp), getD_ofFn] at h1
    simp at h1
  -- the restricted circuit
  have hres : ∀ y : Fin n → Bool, (wf (C.gates.map (restrG a.val)) (List.ofFn y)).getD C.output false
      = PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.Library.Peel.delVerts G {a}) ∅ y := by
    intro y
    have h1 := noread a.val (C.gates.map (restrG a.val)) (List.ofFn y)
      (List.ofFn (Function.update y a false)) (by simp) (by simp)
      (fun g hg => by
        obtain ⟨g0, _, rfl⟩ := List.mem_map.1 hg
        exact restr_noread _ _)
      (fun t ht => by
        by_cases htn : t < n
        · have e1 := getD_ofFn y ⟨t, htn⟩
          have e2 := getD_ofFn (Function.update y a false) ⟨t, htn⟩
          simp only at e1 e2
          rw [e1, e2, Function.update_of_ne (fun h => ht (by rw [← h]))]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
      C.output hout
    rw [h1, restr_wf a.val C.gates _ hop (by simp) (by
      have := getD_ofFn (Function.update y a false) a
      rw [this]; simp), hval]
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun PEqualNP.Library.Peel.delVerts
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      Finset.mem_singleton]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    constructor
    · rintro ⟨u, w, huw, hu, hw⟩
      have hua : u ≠ a := by
        rintro rfl
        simp at hu
      have hwa : w ≠ a := by
        rintro rfl
        simp at hw
      rw [Function.update_of_ne hua] at hu
      rw [Function.update_of_ne hwa] at hw
      exact ⟨u, w, ⟨huw, hua, hwa⟩, hu, hw⟩
    · rintro ⟨u, w, ⟨huw, hua, hwa⟩, hu, hw⟩
      exact ⟨u, w, huw, by rw [Function.update_of_ne hua]; exact hu,
        by rw [Function.update_of_ne hwa]; exact hw⟩
  -- some gate reads the vertex
  have hread : ∃ g ∈ C.gates, a.val ∈ g.inputs := by
    by_contra hno
    push_neg at hno
    have h1 := noread a.val C.gates (List.ofFn (fun i => decide (i = a ∨ i = b)))
      (List.ofFn (Function.update (fun i => decide (i = a ∨ i = b)) a false)) (by simp) (by simp)
      hno
      (fun t ht => by
        by_cases htn : t < n
        · have e1 := getD_ofFn (fun i => decide (i = a ∨ i = b)) ⟨t, htn⟩
          have e2 := getD_ofFn (Function.update (fun i => decide (i = a ∨ i = b)) a false) ⟨t, htn⟩
          simp only at e1 e2
          rw [e1, e2, Function.update_of_ne (fun h => ht (by rw [← h]))]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
      C.output hout
    rw [hval, hval, hone b (Function.update (fun i => decide (i = a ∨ i = b)) a false) (by
      intro i hi
      by_cases hia : i = a
      · rw [hia] at hi; simp at hi
      · rw [Function.update_of_ne hia] at hi
        simpa [hia] using hi)] at h1
    have h2 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (fun i => decide (i = a ∨ i = b)) = true := by
      unfold PEqualNP.MetaComplexity.NestedCover.graphFun
      simp only [Bool.or_eq_true, decide_eq_true_iff]
      exact Or.inr ⟨a, b, hab, by simp, by simp⟩
    rw [h2] at h1
    exact absurd h1 (by simp)
  obtain ⟨g, hg, hga⟩ := hread
  obtain ⟨m, hml, rfl⟩ := List.getElem_of_mem hg
  let C1 : Circuit := ⟨C.gates.map (restrG a.val), C.output⟩
  have hm1 : PEqualNP.MetaComplexity.Monotone2 C1 := by
    intro g' hg'
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg'
    exact restr_mono _ _ (hm g0 hg0)
  have hml1 : m < C1.gates.length := by simpa [C1] using hml
  obtain ⟨hor, hlen⟩ := restr_short a.val C.gates[m] (hm _ hg).2 hga
  have hgm : C1.gates[m] = restrG a.val C.gates[m] := by simp [C1]
  have hfin : ∀ p, (p < n + m ∨ p = n + C1.gates.length) →
      (∀ x : Fin n → Bool, (wf C1.gates (List.ofFn x)).getD (n + m) false
        = (wf C1.gates (List.ofFn x)).getD p false) →
      ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size < C.size ∧
        PEqualNP.MetaComplexity.circuitFun n D
          = PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.Library.Peel.delVerts G {a}) ∅ := by
    intro p hp heq
    obtain ⟨D, hD1, hD2, hD3⟩ := drop_copy n C1 m p hm1 hml1 hp heq
    refine ⟨D, hD1, ?_, ?_⟩
    · have : C1.gates.length = C.gates.length := by simp [C1]
      show D.gates.length < C.gates.length
      omega
    · rw [hD3]
      funext y
      exact hres y
  have hgv : ∀ x : Fin n → Bool, (wf C1.gates (List.ofFn x)).getD (n + m) false
      = ((restrG a.val C.gates[m]).inputs.map fun i =>
          (wf (C1.gates.take m) (List.ofFn x)).getD i false).any id := by
    intro x
    have h := gate_val C1.gates (List.ofFn x) m hml1
    rw [List.length_ofFn] at h
    rw [h, hgm, hor]
    rfl
  have hfalse : ∀ x : Fin n → Bool, (wf C1.gates (List.ofFn x)).getD (n + C1.gates.length) false = false :=
    fun x => List.getD_eq_default _ _ (by rw [wf_len]; simp)
  match hI : (restrG a.val C.gates[m]).inputs, hlen with
  | [], _ =>
    exact hfin (n + C1.gates.length) (Or.inr rfl) (fun x => by rw [hgv x, hI, hfalse]; rfl)
  | [y], _ =>
    by_cases hy : y < n + m
    · exact hfin y (Or.inl hy) (fun x => by
        rw [hgv x, hI, wire_take C1.gates (List.ofFn x) m y (by simpa using hy) (le_of_lt hml1)]
        simp)
    · exact hfin (n + C1.gates.length) (Or.inr rfl) (fun x => by
        rw [hgv x, hI, hfalse]
        have : (wf (C1.gates.take m) (List.ofFn x)).getD y false = false :=
          List.getD_eq_default _ _ (by
            rw [wf_len, List.length_take, Nat.min_eq_left (le_of_lt hml1)]; simp; omega)
        show ([y].map fun i => (wf (C1.gates.take m) (List.ofFn x)).getD i false).any id = false
        rw [List.map_cons, this]
        rfl)
  | _ :: _ :: _, h => simp at h
