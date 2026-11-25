import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8992
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

end PEqualNP.Outside.L_meta_8992

open PEqualNP.Outside.L_meta_8992 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8992 : ∀ (x1 : ℕ) (x2 : Fin (x1 + (1 : ℕ))) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x3.size ∧ ∀ (x6 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x5 x6 = PEqualNP.MetaComplexity.circuitFun (x1 + (1 : ℕ)) x3 (x2.insertNth Bool.false x6) := by
  intro n k C hm
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    simpa using (hm g hg).1
  have hmD : ∀ o, PEqualNP.MetaComplexity.Monotone2 ⟨(C.gates.map (restrG k.val)).map (rg2 k.val), o⟩ := by
    intro o g hg
    obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg1
    have := restr_mono k.val g0 (hm g0 hg0)
    exact ⟨this.1, by simpa [rg2] using this.2⟩
  have hsz : ∀ o, (⟨(C.gates.map (restrG k.val)).map (rg2 k.val), o⟩ : Circuit).size ≤ C.size := by
    intro o
    show ((C.gates.map (restrG k.val)).map (rg2 k.val)).length ≤ C.gates.length
    simp
  have hk0 : ∀ x : Fin n → Bool, (List.ofFn (k.insertNth false x : Fin (n + 1) → Bool)).getD k.val false = false := by
    intro x
    have := getD_ofFn (k.insertNth false x : Fin (n + 1) → Bool) k
    rw [this, Fin.insertNth_apply_same]
  have hrel : ∀ x : Fin n → Bool, ∀ i, i ≠ k.val →
      (List.ofFn (k.insertNth false x : Fin (n + 1) → Bool)).getD i false
        = (List.ofFn x).getD (ren2 k.val i) false := by
    intro x i hik
    by_cases hi : i < n + 1
    · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (x := (⟨i, hi⟩ : Fin (n + 1))) (y := k)
        (fun h => hik (by rw [← h]))
      have e1 := getD_ofFn (k.insertNth false x : Fin (n + 1) → Bool) ⟨i, hi⟩
      simp only at e1
      rw [e1, ← hj, Fin.insertNth_apply_succAbove]
      have hv : ren2 k.val i = j.val := by
        have hji : (k.succAbove j).val = i := by rw [hj]
        unfold ren2
        rw [← hji]
        unfold Fin.succAbove
        split_ifs with h1 h2 h2
        · simp [Fin.lt_def] at h1 h2; omega
        · simp
        · simp
        · simp [Fin.lt_def] at h1 h2; omega
      rw [hv]
      exact (getD_ofFn x j).symm
    · have hr : ren2 k.val i = i - 1 := by
        unfold ren2
        rw [if_pos (by have := k.isLt; omega)]
      rw [hr, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hsim : ∀ x : Fin n → Bool, ∀ i, i ≠ k.val →
      (wf C.gates (List.ofFn (k.insertNth false x : Fin (n + 1) → Bool))).getD i false
        = (wf ((C.gates.map (restrG k.val)).map (rg2 k.val)) (List.ofFn x)).getD (ren2 k.val i) false := by
    intro x i hik
    rw [← restr_wf k.val C.gates _ hop (by rw [List.length_ofFn]; exact k.isLt) (hk0 x)]
    exact sim2 k.val (C.gates.map (restrG k.val)) _ _ (by simp) (by rw [List.length_ofFn]; exact k.isLt) (fun g hg => by
      obtain ⟨g0, _, rfl⟩ := List.mem_map.1 hg
      exact restr_noread _ _) (hrel x) i hik
  by_cases ho : C.output = k.val
  · refine ⟨⟨(C.gates.map (restrG k.val)).map (rg2 k.val), n + C.gates.length⟩, hmD _, hsz _, fun x => ?_⟩
    show (wf ((C.gates.map (restrG k.val)).map (rg2 k.val)) (List.ofFn x)).getD (n + C.gates.length) false
      = (wf C.gates (List.ofFn (k.insertNth false x : Fin (n + 1) → Bool))).getD C.output false
    rw [ho]
    have h1 : (wf C.gates (List.ofFn (k.insertNth false x : Fin (n + 1) → Bool))).getD k.val false = false := by
      rw [wf_keep _ _ _ (by rw [List.length_ofFn]; exact k.isLt)]
      exact hk0 x
    rw [h1]
    exact List.getD_eq_default _ _ (by rw [wf_len]; simp)
  · refine ⟨⟨(C.gates.map (restrG k.val)).map (rg2 k.val), ren2 k.val C.output⟩, hmD _, hsz _, fun x => ?_⟩
    exact (hsim x C.output ho).symm
