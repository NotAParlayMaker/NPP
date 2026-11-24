import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3558
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

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

theorem wf_split (gs : List Gate) (m : ℕ) (X : List Bool) :
    wf gs X = wf (gs.drop m) (wf (gs.take m) X) := by
  conv_lhs => rw [← List.take_append_drop m gs]
  rw [wf_append]

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
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

theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

theorem cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    PEqualNP.EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ PEqualNP.EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

theorem inCone_of_read (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length) (hk : k < j)
    (hin : n + k ∈ (gateAt C j).inputs) : PEqualNP.EdgeOwnership.InCone n C k j :=
  (inCone_iff n C k j).mpr ⟨hj, k, hk, hin, Or.inl rfl⟩

theorem inCone_trans (n : ℕ) (C : Circuit) (i k : ℕ) (hik : PEqualNP.EdgeOwnership.InCone n C i k) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C k j → PEqualNP.EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    rw [inCone_iff]
    refine ⟨h0, k', hk', hin, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hik
    · exact ih k' hk' h3

/- New material. -/

def W {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wf C.gates (List.ofFn x)).getD i false

theorem W_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : n + C.gates.length ≤ i) :
    W C x i = false := by
  unfold W
  rw [List.getD_eq_default _ _ (by rw [wf_len]; simp; omega)]

theorem mem_take_gate (C : Circuit) (m : ℕ) (g : Gate) (hg : g ∈ C.gates.take m) :
    ∃ j, j < m ∧ j < C.gates.length ∧ gateAt C j = g := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.1 hg
  rw [List.length_take] at hj
  refine ⟨j, by omega, by omega, ?_⟩
  rw [gateAt_eq C j (by omega), ← he, List.getElem_take]

theorem mem_drop_gate (C : Circuit) (m : ℕ) (g : Gate) (hg : g ∈ C.gates.drop m) :
    ∃ j, m ≤ j ∧ j < C.gates.length ∧ gateAt C j = g := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.1 hg
  rw [List.length_drop] at hj
  refine ⟨m + j, by omega, by omega, ?_⟩
  rw [gateAt_eq C _ (by omega), ← he, List.getElem_drop]

theorem W_gate (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) (k : ℕ) (hk : k < C.gates.length)
    (x : Fin n → Bool) :
    W C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map (W C x)) := by
  have hX : (List.ofFn x).length = n := by simp
  have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hPl : (wf (C.gates.take k) (List.ofFn x)).length = n + k := by
    rw [wf_len, List.length_take, hX, Nat.min_eq_left (le_of_lt hk)]
  have e1 : wf C.gates (List.ofFn x) = wf (C.gates.drop (k + 1))
      (wf (C.gates.take k) (List.ofFn x) ++ [C.gates[k].op.eval (C.gates[k].inputs.map
        fun i => (wf (C.gates.take k) (List.ofFn x)).getD i false)]) := by
    conv_lhs => rw [hsplit]
    rw [wf_append, wf_cons]
  have lhs : (wf C.gates (List.ofFn x)).getD (n + k) false = C.gates[k].op.eval
      (C.gates[k].inputs.map fun i => (wf (C.gates.take k) (List.ofFn x)).getD i false) := by
    rw [e1, wf_keep _ _ _ (by simp [hPl]), show n + k = (wf (C.gates.take k) (List.ofFn x)).length
      from hPl.symm, getD_snoc_eq]
  show (wf C.gates (List.ofFn x)).getD (n + k) false = _
  rw [lhs, gateAt_eq C k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := hrb k hk i (by rw [gateAt_eq C k hk]; exact hi)
  exact (wire_take C.gates (List.ofFn x) k i (by rw [hX]; exact this) (le_of_lt hk)).symm

theorem eval_imp (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (F F' : ℕ → Bool) (h : ∀ i ∈ l, F i = true → F' i = true) :
    op.eval (l.map F) = true → op.eval (l.map F') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map]
    intro H b hb
    obtain ⟨i, hi, rfl⟩ := hb
    have := H (F i) ⟨i, hi, rfl⟩
    simp only [id] at this ⊢
    exact h i hi this
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    simp only [id] at hb
    exact ⟨F' i, ⟨i, hi, rfl⟩, h i hi hb⟩

def rd (q t : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun i => if i = q then t else i)⟩

theorem sim_rd (r : Bool → Bool → Prop)
    (hop : ∀ op : GateOp, (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (F F' : ℕ → Bool),
      (∀ i ∈ l, r (F i) (F' i)) → r (op.eval (l.map F)) (op.eval (l.map F')))
    (hr0 : r false false) (q t : ℕ) (B : List Gate)
    (hB : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ U U' : List Bool, U.length = U'.length → q < U.length → t < U.length →
      (∀ i, r (U.getD i false) (U'.getD i false)) → r (U.getD q false) (U'.getD t false) →
      (∀ i, r ((wf B U).getD i false) ((wf (B.map (rd q t)) U').getD i false)) ∧
        r ((wf B U).getD q false) ((wf (B.map (rd q t)) U').getD t false) := by
  induction B with
  | nil => intro U U' _ _ _ h1 h2; exact ⟨h1, h2⟩
  | cons g B ih =>
    intro U U' hlen hq ht h1 h2
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : r (g.op.eval (g.inputs.map fun i => U.getD i false))
        ((rd q t g).op.eval ((rd q t g).inputs.map fun i => U'.getD i false)) := by
      show r _ (g.op.eval ((g.inputs.map fun i => if i = q then t else i).map
        fun i => U'.getD i false))
      rw [List.map_map]
      apply hop g.op (hB g List.mem_cons_self)
      intro i _
      show r (U.getD i false) (U'.getD (if i = q then t else i) false)
      by_cases hiq : i = q
      · rw [if_pos hiq, hiq]; exact h2
      · rw [if_neg hiq]; exact h1 i
    refine ih (fun g' hg' => hB g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen])
      (by simp; omega) (by simp; omega) ?_ ?_
    · intro i
      rcases Nat.lt_trichotomy i U.length with e | e | e
      · rw [getD_snoc_lt _ _ _ e, getD_snoc_lt _ _ _ (by omega)]
        exact h1 i
      · rw [e, getD_snoc_eq, hlen, getD_snoc_eq]
        exact hv
      · rw [getD_snoc_gt _ _ _ e, getD_snoc_gt _ _ _ (by omega)]
        exact hr0
    · rw [getD_snoc_lt _ _ _ hq, getD_snoc_lt _ _ _ (by omega)]
      exact h2

def redir (n k t : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rd (n + k) t), if C.output = n + k then t else C.output⟩

theorem redir_split (n : ℕ) (C : Circuit) (k t : ℕ) (hrb : ReadsBack n C) (X : List Bool) :
    wf (redir n k t C).gates X =
      wf ((C.gates.drop (k + 1)).map (rd (n + k) t)) (wf (C.gates.take (k + 1)) X) := by
  show wf (C.gates.map (rd (n + k) t)) X = _
  have hid : ∀ g ∈ C.gates.take (k + 1), rd (n + k) t g = g := by
    intro g hg
    obtain ⟨j, hj, hjl, rfl⟩ := mem_take_gate C (k + 1) g hg
    have hm : (gateAt C j).inputs.map (fun i => if i = n + k then t else i) =
        (gateAt C j).inputs := by
      conv_rhs => rw [← List.map_id (gateAt C j).inputs]
      apply List.map_congr_left
      intro i hi
      have := hrb j hjl i hi
      rw [if_neg (by omega)]
      rfl
    unfold rd
    rw [hm]
  have : C.gates.map (rd (n + k) t) =
      C.gates.take (k + 1) ++ (C.gates.drop (k + 1)).map (rd (n + k) t) := by
    conv_lhs => rw [← List.take_append_drop (k + 1) C.gates]
    rw [List.map_append]
    congr 1
    calc (C.gates.take (k + 1)).map (rd (n + k) t) = (C.gates.take (k + 1)).map id :=
          List.map_congr_left hid
      _ = C.gates.take (k + 1) := List.map_id _
  rw [this, wf_append]

theorem redir_cmp (r : Bool → Bool → Prop)
    (hop : ∀ op : GateOp, (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (F F' : ℕ → Bool),
      (∀ i ∈ l, r (F i) (F' i)) → r (op.eval (l.map F)) (op.eval (l.map F')))
    (hr0 : r false false) (hrefl : ∀ a, r a a) (n : ℕ) (C : Circuit) (k t : ℕ)
    (hk : k < C.gates.length) (hrb : ReadsBack n C)
    (hao : PEqualNP.EdgeOwnership.AndOrOnly C) (ht : t < n + k) (x : Fin n → Bool)
    (hqt : r (W C x (n + k)) (W C x t)) :
    (∀ i, r (W C x i) (W (redir n k t C) x i)) ∧ r (W C x (n + k)) (W (redir n k t C) x t) := by
  have hU : (wf (C.gates.take (k + 1)) (List.ofFn x)).length = n + (k + 1) := by
    rw [wf_len, List.length_take]; simp; omega
  have e1 := wf_split C.gates (k + 1) (List.ofFn x)
  have e2 := redir_split n C k t hrb (List.ofFn x)
  have hq : W C x (n + k) = (wf (C.gates.take (k + 1)) (List.ofFn x)).getD (n + k) false := by
    unfold W; rw [e1, wf_keep _ _ _ (by omega)]
  have htt : W C x t = (wf (C.gates.take (k + 1)) (List.ofFn x)).getD t false := by
    unfold W; rw [e1, wf_keep _ _ _ (by omega)]
  unfold W
  rw [e1, e2]
  exact sim_rd r hop hr0 (n + k) t _ (fun g hg => hao g (List.mem_of_mem_drop hg)) _ _ rfl
    (by omega) (by omega) (fun i => hrefl _) (by rw [← hq, ← htt]; exact hqt)

theorem redir_pre (n : ℕ) (C : Circuit) (k t : ℕ) (hk : k < C.gates.length)
    (hrb : ReadsBack n C) (x : Fin n → Bool) (i : ℕ) (hi : i < n + k + 1) :
    W (redir n k t C) x i = W C x i := by
  have hU : (wf (C.gates.take (k + 1)) (List.ofFn x)).length = n + (k + 1) := by
    rw [wf_len, List.length_take]; simp; omega
  unfold W
  rw [wf_split C.gates (k + 1) (List.ofFn x), redir_split n C k t hrb (List.ofFn x),
    wf_keep ((C.gates.drop (k + 1)).map (rd (n + k) t)) _ _ (by omega),
    wf_keep (C.gates.drop (k + 1)) _ _ (by omega)]

theorem redir_ao (n : ℕ) (C : Circuit) (k t : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C)
    (ht : t < n + k) : PEqualNP.TopForm.IsAO2 n (redir n k t C) := by
  obtain ⟨hao, hrb, hl2⟩ := hC
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact hao g0 hg0
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [redir] using hj
    have e : gateAt (redir n k t C) j = rd (n + k) t (gateAt C j) := by
      rw [gateAt_eq _ j hj, gateAt_eq C j hj']
      simp [redir]
    rw [e] at hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
    have := hrb j hj' i0 hi0
    by_cases h : i0 = n + k
    · rw [if_pos h]; omega
    · rw [if_neg h]; exact this
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    show (g0.inputs.map _).length = 2
    rw [List.length_map]; exact hl2 g0 hg0

theorem redir_unread (n : ℕ) (C : Circuit) (k t : ℕ) (ht : t < n + k) :
    ∀ g ∈ (redir n k t C).gates, n + k ∉ g.inputs := by
  intro g hg hin
  obtain ⟨g0, _, rfl⟩ := List.mem_map.1 hg
  obtain ⟨i0, _, he⟩ := List.mem_map.1 hin
  by_cases h : i0 = n + k
  · rw [if_pos h] at he; omega
  · rw [if_neg h] at he; exact h he

theorem redir_out (n : ℕ) (C : Circuit) (k t : ℕ) (ht : t < n + k) :
    (redir n k t C).output ≠ n + k := by
  show (if C.output = n + k then t else C.output) ≠ n + k
  split_ifs with h
  · omega
  · exact h

def ers (n m : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m)), ren2 (n + m) C.output⟩

theorem ers_len (n m : ℕ) (C : Circuit) (hm : m < C.gates.length) :
    (ers n m C).gates.length + 1 = C.gates.length := by
  show (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg2 (n + m))).length + 1 = C.gates.length
  rw [List.length_append, List.length_map, List.length_take, List.length_drop]
  omega

theorem ers_val (n m : ℕ) (C : Circuit) (hm : m < C.gates.length)
    (hun : ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs) (x : Fin n → Bool) (i : ℕ)
    (hi : i ≠ n + m) : W (ers n m C) x (ren2 (n + m) i) = W C x i :=
  congrFun (erase_fun n ⟨C.gates, i⟩ m hm hun hi) x

theorem c_step (n : ℕ) (D : Circuit) (hD : PEqualNP.TopForm.IsAO2 n D)
    (hne : PEqualNP.FactorSubst.liveSize n D ≠ D.size) :
    ∃ E : Circuit, PEqualNP.TopForm.IsAO2 n E ∧
      PEqualNP.MetaComplexity.circuitFun n E = PEqualNP.MetaComplexity.circuitFun n D ∧
      E.size + 1 = D.size := by
  classical
  have hsub : PEqualNP.FactorSubst.liveGates n D ⊆ Finset.range D.gates.length :=
    Finset.filter_subset _ _
  have hle := Finset.card_le_card hsub
  rw [Finset.card_range] at hle
  have hlt : (PEqualNP.FactorSubst.liveGates n D).card < D.gates.length := by
    unfold PEqualNP.FactorSubst.liveSize at hne
    exact lt_of_le_of_ne hle hne
  have hSne : (Finset.range D.gates.length \ PEqualNP.FactorSubst.liveGates n D).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [Finset.sdiff_eq_empty_iff_subset] at h
    have := Finset.card_le_card h
    rw [Finset.card_range] at this
    omega
  obtain ⟨m, hmS, hmax⟩ : ∃ m ∈ Finset.range D.gates.length \ PEqualNP.FactorSubst.liveGates n D,
      ∀ j ∈ Finset.range D.gates.length \ PEqualNP.FactorSubst.liveGates n D, j ≤ m :=
    ⟨_, Finset.max'_mem _ hSne, fun j hj => Finset.le_max' _ j hj⟩
  rw [Finset.mem_sdiff, Finset.mem_range] at hmS
  obtain ⟨hmlen, hmdead⟩ := hmS
  have hlive : ∀ j < D.gates.length, m < j → j ∈ PEqualNP.FactorSubst.liveGates n D := by
    intro j hj hmj
    by_contra hc
    have := hmax j (Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hj, hc⟩)
    omega
  have hun : ∀ g ∈ D.gates.drop (m + 1), n + m ∉ g.inputs := by
    intro g hg hin
    obtain ⟨j, hj1, hj2, rfl⟩ := mem_drop_gate D (m + 1) g hg
    have hl := hlive j hj2 (by omega)
    apply hmdead
    have hc : PEqualNP.EdgeOwnership.InCone n D m j := inCone_of_read n D m j hj2 (by omega) hin
    unfold PEqualNP.FactorSubst.liveGates at hl ⊢
    rw [Finset.mem_filter] at hl ⊢
    obtain ⟨_, h1, h2⟩ := hl
    refine ⟨Finset.mem_range.2 hmlen, h1, Or.inr ?_⟩
    rcases h2 with h2 | h2
    · rw [← h2]; exact hc
    · exact inCone_trans n D m j hc _ h2
  have ho : D.output ≠ n + m := by
    intro h
    apply hmdead
    unfold PEqualNP.FactorSubst.liveGates
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.2 hmlen, by omega, Or.inl (by omega)⟩
  exact ⟨ers n m D, erase_ao n D m hmlen hD hun, erase_fun n D m hmlen hun ho, ers_len n m D hmlen⟩

theorem b_step (n : ℕ) (f : (Fin n → Bool) → Bool) (D : Circuit)
    (hD : PEqualNP.TopForm.IsAO2 n D) (hf : PEqualNP.MetaComplexity.circuitFun n D = f)
    (k : ℕ) (hk : k < D.gates.length) (hand : (gateAt D k).op = GateOp.and)
    (t : ℕ) (ht : t ∈ (gateAt D k).inputs)
    (hbel : ∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true → f x = true) :
    ∃ E : Circuit, PEqualNP.TopForm.IsAO2 n E ∧ PEqualNP.MetaComplexity.circuitFun n E = f ∧
      E.size + 1 = D.size := by
  have hD' := hD
  obtain ⟨hao, hrb, _⟩ := hD'
  have htk : t < n + k := hrb k hk t ht
  have hD1 := redir_ao n D k t hD htk
  have hun1 := redir_unread n D k t htk
  have hk1 : k < (redir n k t D).gates.length := by simpa [redir] using hk
  have hg : ∀ x : Fin n → Bool, W D x (n + k) = true → W D x t = true := by
    intro x
    rw [W_gate n D hrb k hk x, hand]
    intro H
    simp only [GateOp.eval, List.all_eq_true, List.mem_map] at H
    have := H (W D x t) ⟨t, ht, rfl⟩
    simpa using this
  have hfun1 : PEqualNP.MetaComplexity.circuitFun n (redir n k t D) = f := by
    funext x
    rw [← hf]
    show W (redir n k t D) x (redir n k t D).output = W D x D.output
    have hout : (redir n k t D).output = if D.output = n + k then t else D.output := rfl
    have key_le := redir_cmp (fun a b => a = true → b = true)
      (fun op hop l F F' h => eval_imp op hop l F F' h) (fun h => h) (fun _ h => h)
      n D k t hk hrb hao htk x (hg x)
    have A : W D x D.output = true → W (redir n k t D) x (redir n k t D).output = true := by
      intro H
      rw [hout]
      split_ifs with h
      · exact key_le.2 (h ▸ H)
      · exact key_le.1 _ H
    have B : W (redir n k t D) x (redir n k t D).output = true → W D x D.output = true := by
      intro H
      by_cases htx : W D x t = true
      · have := hbel x htx
        rw [← hf] at this
        exact this
      · have key_ge := redir_cmp (fun a b => b = true → a = true)
          (fun op hop l F F' h => eval_imp op hop l F' F h) (fun h => h) (fun _ h => h)
          n D k t hk hrb hao htk x (fun h => absurd h htx)
        rw [hout] at H
        split_ifs at H with h
        · rw [h]; exact key_ge.2 H
        · exact key_ge.1 _ H
    exact Bool.eq_iff_iff.2 ⟨B, A⟩
  have hun1' : ∀ g ∈ (redir n k t D).gates.drop (k + 1), n + k ∉ g.inputs :=
    fun g hg => hun1 g (List.mem_of_mem_drop hg)
  refine ⟨ers n k (redir n k t D), erase_ao n _ k hk1 hD1 hun1', ?_, ?_⟩
  · rw [show ers n k (redir n k t D) = ⟨(redir n k t D).gates.take k ++
      ((redir n k t D).gates.drop (k + 1)).map (rg2 (n + k)),
      ren2 (n + k) (redir n k t D).output⟩ from rfl,
      erase_fun n _ k hk1 hun1' (redir_out n D k t htk)]
    exact hfun1
  · have := ers_len n k (redir n k t D) hk1
    have e : (redir n k t D).gates.length = D.gates.length := by simp [redir]
    show (ers n k (redir n k t D)).gates.length + 1 = D.gates.length
    omega

open Classical in
def pot (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) : ℕ :=
  ((Finset.range C.gates.length).filter (fun j => ¬ ∀ x : Fin n → Bool,
    PEqualNP.EdgeOwnership.gateVal n C j x = true → f x = true)).card

theorem card_lt_of_map (S3 S : Finset ℕ) (h : ℕ) (hhS : h ∈ S) (φ : ℕ → ℕ)
    (hinj : Function.Injective φ) (hmap : ∀ j ∈ S3, φ j ∈ S ∧ φ j ≠ h) : S3.card < S.card := by
  classical
  rw [← Finset.card_image_of_injective S3 hinj]
  calc (S3.image φ).card ≤ (S.erase h).card := Finset.card_le_card (by
        intro y hy
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
        exact Finset.mem_erase.2 ⟨(hmap j hj).2, (hmap j hj).1⟩)
    _ < S.card := Finset.card_erase_lt_of_mem hhS

theorem a_core (n : ℕ) (f : (Fin n → Bool) → Bool) (D : Circuit)
    (hD : PEqualNP.TopForm.IsAO2 n D) (hf : PEqualNP.MetaComplexity.circuitFun n D = f)
    (h : ℕ) (hh : h < D.gates.length) (hor : (gateAt D h).op = GateOp.or)
    (hnb : ¬ ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n D h z = true → f z = true)
    (wa wb : ℕ) (hin : (gateAt D h).inputs = [wa, wb] ∨ (gateAt D h).inputs = [wb, wa])
    (hbb : ∀ x : Fin n → Bool, W D x wb = true → f x = true)
    (hsat : ∃ y : Fin n → Bool, W D y wb = true) :
    ∃ E : Circuit, PEqualNP.TopForm.IsAO2 n E ∧ PEqualNP.MetaComplexity.circuitFun n E = f ∧
      E.size = D.size ∧ pot n f E < pot n f D := by
  have hD' := hD
  obtain ⟨hao, hrb, _⟩ := hD'
  have hwa : wa < n + h := hrb h hh wa (by rcases hin with e | e <;> rw [e] <;> simp)
  have hwb : wb < n + h := hrb h hh wb (by rcases hin with e | e <;> rw [e] <;> simp)
  have hval : ∀ x : Fin n → Bool, W D x (n + h) = (W D x wa || W D x wb) := by
    intro x
    rw [W_gate n D hrb h hh x, hor]
    rcases hin with e | e <;> rw [e] <;> simp [GateOp.eval, Bool.or_comm]
  have hout_ne : D.output ≠ n + h := by
    intro he
    apply hnb
    intro z hz
    rw [← hf]
    show W D z D.output = true
    rw [he]
    exact hz
  have hout_lt : D.output < n + D.gates.length := by
    obtain ⟨y, hy⟩ := hsat
    by_contra hc
    have h1 := hbb y hy
    rw [← hf] at h1
    change W D y D.output = true at h1
    rw [W_ge D y _ (by omega)] at h1
    exact Bool.false_ne_true h1
  have hA1 := redir_ao n D h wa hD hwa
  have hun1 := redir_unread n D h wa hwa
  have hh1 : h < (redir n h wa D).gates.length := by simpa [redir] using hh
  have hlen1 : (redir n h wa D).gates.length = D.gates.length := by simp [redir]
  have hout1 : (redir n h wa D).output = D.output := by
    show (if D.output = n + h then wa else D.output) = D.output
    rw [if_neg hout_ne]
  have ge1 : ∀ (x : Fin n → Bool) (i : ℕ), W (redir n h wa D) x i = true → W D x i = true := by
    intro x i
    exact (redir_cmp (fun a b => b = true → a = true)
      (fun op hop l F F' h => eval_imp op hop l F' F h) (fun h => h) (fun _ h => h)
      n D h wa hh hrb hao hwa x (by intro H; rw [hval x, H]; rfl)).1 i
  have le1 : ∀ x : Fin n → Bool, W D x wb = false → ∀ i, W D x i = true →
      W (redir n h wa D) x i = true := by
    intro x hb i
    exact (redir_cmp (fun a b => a = true → b = true)
      (fun op hop l F F' h => eval_imp op hop l F F' h) (fun h => h) (fun _ h => h)
      n D h wa hh hrb hao hwa x (by intro H; rw [hval x, hb, Bool.or_false] at H; exact H)).1 i
  have pre1 : ∀ x : Fin n → Bool, W (redir n h wa D) x wb = W D x wb :=
    fun x => redir_pre n D h wa hh hrb x wb (by omega)
  have hun1' : ∀ g ∈ (redir n h wa D).gates.drop (h + 1), n + h ∉ g.inputs :=
    fun g hg => hun1 g (List.mem_of_mem_drop hg)
  have hA2 : PEqualNP.TopForm.IsAO2 n (ers n h (redir n h wa D)) :=
    erase_ao n _ h hh1 hA1 hun1'
  have hlen2 : (ers n h (redir n h wa D)).gates.length + 1 = D.gates.length := by
    rw [← hlen1]; exact ers_len n h _ hh1
  have v2 : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ n + h →
      W (ers n h (redir n h wa D)) x (ren2 (n + h) i) = W (redir n h wa D) x i :=
    fun x i hi => ers_val n h _ hh1 hun1' x i hi
  have hout2 : (ers n h (redir n h wa D)).output = ren2 (n + h) D.output := by
    show ren2 (n + h) (redir n h wa D).output = _
    rw [hout1]
  have hout2lt : (ers n h (redir n h wa D)).output < n + (ers n h (redir n h wa D)).gates.length := by
    rw [hout2]; unfold ren2; split_ifs <;> omega
  have hrenb : ren2 (n + h) wb = wb := by unfold ren2; rw [if_neg (by omega)]
  have hw2 : ∀ x : Fin n → Bool, W (ers n h (redir n h wa D)) x wb = W D x wb := by
    intro x
    rw [← pre1, ← v2 x wb (by omega), hrenb]
  obtain ⟨D2, hD2⟩ : ∃ D2, D2 = ers n h (redir n h wa D) := ⟨_, rfl⟩
  rw [← hD2] at hA2 hlen2 v2 hout2lt hw2 hout2
  have hElen : (D2.gates ++ [(⟨GateOp.or, [D2.output, wb]⟩ : Gate)]).length = D2.gates.length + 1 := by
    simp
  have hgE : ∀ j < D2.gates.length,
      gateAt ⟨D2.gates ++ [(⟨GateOp.or, [D2.output, wb]⟩ : Gate)], n + D2.gates.length⟩ j = gateAt D2 j := by
    intro j hj
    unfold gateAt
    exact List.getD_append _ _ _ _ hj
  have hgE3 : gateAt ⟨D2.gates ++ [(⟨GateOp.or, [D2.output, wb]⟩ : Gate)], n + D2.gates.length⟩
      D2.gates.length = ⟨GateOp.or, [D2.output, wb]⟩ := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD]
  obtain ⟨E, hE⟩ : ∃ E : Circuit,
      E = ⟨D2.gates ++ [(⟨GateOp.or, [D2.output, wb]⟩ : Gate)], n + D2.gates.length⟩ := ⟨_, rfl⟩
  rw [← hE] at hgE hgE3
  have hEg : E.gates = D2.gates ++ [(⟨GateOp.or, [D2.output, wb]⟩ : Gate)] := by rw [hE]
  have hEo : E.output = n + D2.gates.length := by rw [hE]
  have hElen' : E.gates.length = D2.gates.length + 1 := by rw [hEg]; exact hElen
  have hAE : PEqualNP.TopForm.IsAO2 n E := by
    obtain ⟨a2, r2, l2⟩ := hA2
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      rw [hEg] at hg
      rcases List.mem_append.1 hg with hg | hg
      · exact a2 g hg
      · rw [List.mem_singleton] at hg
        rw [hg]
        exact Or.inr rfl
    · intro j hj i hi
      rw [hElen'] at hj
      rcases Nat.lt_or_ge j D2.gates.length with hj2 | hj2
      · rw [hgE j hj2] at hi
        exact r2 j hj2 i hi
      · have hjj : j = D2.gates.length := by omega
        rw [hjj, hgE3] at hi
        rw [hjj]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with hi | hi
        · rw [hi]; exact hout2lt
        · rw [hi]; omega
    · intro g hg
      rw [hEg] at hg
      rcases List.mem_append.1 hg with hg | hg
      · exact l2 g hg
      · rw [List.mem_singleton] at hg
        rw [hg]
        rfl
  have hEpre : ∀ (x : Fin n → Bool) (i : ℕ), i < n + D2.gates.length → W E x i = W D2 x i := by
    intro x i hi
    unfold W
    rw [hEg]
    exact wf_prefix _ _ _ _ (by simp; omega)
  have hEval : ∀ x : Fin n → Bool,
      W E x (n + D2.gates.length) = (W (redir n h wa D) x D.output || W D x wb) := by
    intro x
    rw [W_gate n E hAE.2.1 D2.gates.length (by omega) x, hgE3]
    show GateOp.or.eval [W E x D2.output, W E x wb] = _
    rw [hEpre x _ hout2lt, hEpre x wb (by omega), hout2, v2 x _ hout_ne, hw2]
    simp [GateOp.eval]
  have hfE : PEqualNP.MetaComplexity.circuitFun n E = f := by
    funext x
    show W E x E.output = f x
    rw [hEo, hEval x]
    cases hb : W D x wb
    · rw [Bool.or_false, ← hf]
      show W (redir n h wa D) x D.output = W D x D.output
      exact Bool.eq_iff_iff.2 ⟨ge1 x _, le1 x hb _⟩
    · rw [Bool.or_true]
      exact (hbb x hb).symm
  refine ⟨E, hAE, hfE, ?_, ?_⟩
  · show E.gates.length = D.gates.length
    omega
  · unfold pot
    apply card_lt_of_map _ _ h (Finset.mem_filter.2 ⟨Finset.mem_range.2 hh, hnb⟩)
      (fun j => if j < h then j else j + 1)
    · intro a b hab
      simp only at hab
      split_ifs at hab <;> omega
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hjl, hjb⟩ := hj
      rw [hElen'] at hjl
      have hj2 : j < D2.gates.length := by
        by_contra hc
        apply hjb
        have hjj : j = D2.gates.length := by omega
        intro x hx
        rw [← hfE]
        show W E x E.output = true
        rw [hEo, ← hjj]
        exact hx
      refine ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, ?_⟩, ?_⟩
      · show (if j < h then j else j + 1) < D.gates.length
        split_ifs <;> omega
      · intro hb
        apply hjb
        intro x hx
        apply hb x
        have e1 : PEqualNP.EdgeOwnership.gateVal n E j x =
            W (redir n h wa D) x (n + (if j < h then j else j + 1)) := by
          show W E x (n + j) = _
          rw [hEpre x _ (by omega), ← v2 x _ (by split_ifs <;> omega)]
          congr 1
          unfold ren2
          split_ifs <;> omega
        rw [e1] at hx
        exact ge1 x _ hx
      · show (if j < h then j else j + 1) ≠ h
        split_ifs <;> omega

theorem a_step (n : ℕ) (f : (Fin n → Bool) → Bool) (D : Circuit)
    (hD : PEqualNP.TopForm.IsAO2 n D) (hf : PEqualNP.MetaComplexity.circuitFun n D = f)
    (h : ℕ) (hh : h < D.gates.length) (hor : (gateAt D h).op = GateOp.or)
    (hnb : ¬ ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n D h z = true → f z = true)
    (b : Fin 2)
    (hbb : ∀ x : Fin n → Bool,
      PEqualNP.ReadTwo.wval D x (PEqualNP.TopForm.opnd D h b) = true → f x = true)
    (hsat : ∃ y : Fin n → Bool, PEqualNP.ReadTwo.wval D y (PEqualNP.TopForm.opnd D h b) = true) :
    ∃ E : Circuit, PEqualNP.TopForm.IsAO2 n E ∧ PEqualNP.MetaComplexity.circuitFun n E = f ∧
      E.size = D.size ∧ pot n f E < pot n f D := by
  have hl2 : (gateAt D h).inputs.length = 2 :=
    hD.2.2 _ (by rw [gateAt_eq D h hh]; exact List.getElem_mem _)
  obtain ⟨i0, i1, hin⟩ := List.length_eq_two.1 hl2
  have ho0 : PEqualNP.TopForm.opnd D h 0 = i0 := by
    unfold PEqualNP.TopForm.opnd; rw [hin]; rfl
  have ho1 : PEqualNP.TopForm.opnd D h 1 = i1 := by
    unfold PEqualNP.TopForm.opnd; rw [hin]; rfl
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · rw [ho0] at hbb hsat
    exact a_core n f D hD hf h hh hor hnb i1 i0 (Or.inr hin) hbb hsat
  · rw [ho1] at hbb hsat
    exact a_core n f D hD hf h hh hor hnb i0 i1 (Or.inl hin) hbb hsat

theorem main :∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = f → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.TopForm.IsAO2 n D ∧ PEqualNP.MetaComplexity.circuitFun n D = f ∧ ∀ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C2 → PEqualNP.MetaComplexity.circuitFun n C2 = f → D.size ≤ C2.size) ∧ (¬ ∃ h < D.gates.length, ∃ b : Fin 2, PEqualNP.Core.InOutputCone n D h ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D h).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ¬ (∀ z1 : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n D h z1 = true → f z1 = true) ∧ ((∀ x1 : Fin n → Bool, PEqualNP.ReadTwo.wval D x1 (PEqualNP.TopForm.opnd D h b) = true → f x1 = true) ∧ ∃ y1 : Fin n → Bool, PEqualNP.ReadTwo.wval D y1 (PEqualNP.TopForm.opnd D h b) = true)) ∧ (∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true → f x = true)) ∧ PEqualNP.FactorSubst.liveSize n D = D.size := by
  intro n f C hC hCf
  classical
  have hex1 : ∃ s, ∃ C' : Circuit, (PEqualNP.TopForm.IsAO2 n C' ∧
      PEqualNP.MetaComplexity.circuitFun n C' = f) ∧ C'.size = s := ⟨_, C, ⟨hC, hCf⟩, rfl⟩
  obtain ⟨C0, hC0, hC0s⟩ := Nat.find_spec hex1
  have hex2 : ∃ p, ∃ C' : Circuit, ((PEqualNP.TopForm.IsAO2 n C' ∧
      PEqualNP.MetaComplexity.circuitFun n C' = f) ∧ C'.size = Nat.find hex1) ∧
      pot n f C' = p := ⟨_, C0, ⟨hC0, hC0s⟩, rfl⟩
  obtain ⟨D, ⟨⟨hDa, hDf⟩, hDs⟩, hDp⟩ := Nat.find_spec hex2
  have hmin : ∀ C2 : Circuit, PEqualNP.TopForm.IsAO2 n C2 →
      PEqualNP.MetaComplexity.circuitFun n C2 = f → Nat.find hex1 ≤ C2.size :=
    fun C2 h1 h2 => Nat.find_min' hex1 ⟨C2, ⟨h1, h2⟩, rfl⟩
  have hpmin : ∀ C2 : Circuit, PEqualNP.TopForm.IsAO2 n C2 →
      PEqualNP.MetaComplexity.circuitFun n C2 = f → C2.size = Nat.find hex1 →
      Nat.find hex2 ≤ pot n f C2 :=
    fun C2 h1 h2 h3 => Nat.find_min' hex2 ⟨C2, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
  refine ⟨D, ⟨hDa, hDf, fun C2 h1 h2 => by rw [hDs]; exact hmin C2 h1 h2⟩, ?_, ?_, ?_⟩
  · rintro ⟨h, hh, b, _, hor, hnb, hbb, hsat⟩
    obtain ⟨E, hEa, hEf, hEs, hEp⟩ := a_step n f D hDa hDf h hh hor hnb b hbb hsat
    have := hpmin E hEa hEf (hEs.trans hDs)
    omega
  · intro k hk hand t ht hbel
    obtain ⟨E, hEa, hEf, hEs⟩ := b_step n f D hDa hDf k hk hand t ht hbel
    have := hmin E hEa hEf
    omega
  · by_contra hne
    obtain ⟨E, hEa, hEf, hEs⟩ := c_step n D hDa hne
    have := hmin E hEa (hEf.trans hDf)
    omega

end PEqualNP.Outside.L_meta_3558

theorem PEqualNP.Outside.L_meta_3558 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.Core.IsLiftFixedPoint G D ∧ (∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) ∧ PEqualNP.FactorSubst.liveSize n D = D.size := by
  intro n G _ C hC hf
  obtain ⟨D, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_meta_3558.main n
    (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) C hC hf
  exact ⟨D, h1, h2, h3, h4⟩
