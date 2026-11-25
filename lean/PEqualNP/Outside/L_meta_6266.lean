import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6266
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

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

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

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

def cf (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) : List (List ℕ) :=
  gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs

theorem cf_append (n : ℕ) (a b : List Gate) (cs : List (List ℕ)) :
    cf n (a ++ b) cs = cf n b (cf n a cs) := by
  simp [cf, List.foldl_append]

theorem cf_cons (n : ℕ) (g : Gate) (gs : List Gate) (cs : List (List ℕ)) :
    cf n (g :: gs) cs = cf n gs (PEqualNP.EdgeOwnership.coneStep n cs g) := rfl

theorem cs_len (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (PEqualNP.EdgeOwnership.coneStep n cs g).length = cs.length + 1 := by
  unfold PEqualNP.EdgeOwnership.coneStep; simp

theorem cf_len (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)),
    (cf n gs cs).length = cs.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro cs; rfl
  | cons g gs ih =>
    intro cs
    rw [cf_cons, ih, cs_len, List.length_cons]; omega

theorem cf_keep (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ), j < cs.length →
    (cf n gs cs).getD j [] = cs.getD j [] := by
  intro gs
  induction gs with
  | nil => intro cs j _; rfl
  | cons g gs ih =>
    intro cs j hj
    rw [cf_cons, ih _ j (by rw [cs_len]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact List.getD_append _ _ _ _ hj

theorem snocD (L : List (List ℕ)) (v : List ℕ) (j : ℕ) (h : L.length = j) :
    (L ++ [v]).getD j [] = v := by
  subst h; simp [List.getD_eq_getElem?_getD]

theorem cone_iff (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) (i : ℕ) :
    i ∈ (cf n gs []).getD j [] ↔ ∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧
      (i = w - n ∨ i ∈ (cf n gs []).getD (w - n) []) := by
  have hP : (cf n (gs.take j) []).length = j := by
    rw [cf_len, List.length_take, Nat.min_eq_left (le_of_lt hj)]; simp
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have e : cf n gs [] = cf n (gs.drop (j + 1))
      (PEqualNP.EdgeOwnership.coneStep n (cf n (gs.take j) []) gs[j]) := by
    conv_lhs => rw [hsplit]
    rw [cf_append, cf_cons]
  have hfull : ∀ m, m < j → (cf n gs []).getD m [] = (cf n (gs.take j) []).getD m [] := by
    intro m hm
    rw [e, cf_keep _ _ _ m (by rw [cs_len, hP]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact List.getD_append _ _ _ _ (by omega)
  have hj_eq : (cf n gs []).getD j [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cf n (gs.take j) []).length))).flatMap
        (fun w => (w - n) :: (cf n (gs.take j) []).getD (w - n) []) := by
    rw [e, cf_keep _ _ _ j (by rw [cs_len, hP]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact snocD _ _ j hP
  rw [hj_eq, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
    have hw3 := of_decide_eq_true hw2
    rw [hP] at hw3
    refine ⟨w, hw1, hw3.1, hw3.2, ?_⟩
    rcases List.mem_cons.1 hi with h1 | h1
    · exact Or.inl h1
    · right; rw [hfull _ (by omega)]; exact h1
  · rintro ⟨w, hw1, hw2, hw3, hi⟩
    refine ⟨w, List.mem_filter.2 ⟨hw1, decide_eq_true (by rw [hP]; exact ⟨hw2, hw3⟩)⟩, ?_⟩
    rcases hi with h1 | h1
    · exact List.mem_cons.2 (Or.inl h1)
    · rw [hfull _ (by omega)] at h1
      exact List.mem_cons.2 (Or.inr h1)

theorem cone_lt (n : ℕ) (gs : List Gate) (i j : ℕ) (h : i ∈ (cf n gs []).getD j []) :
    j < gs.length := by
  by_contra hc
  rw [List.getD_eq_default _ _ (by rw [cf_len]; simp; omega)] at h
  cases h

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
theorem valf (n : ℕ) (C : Circuit) (y : Fin n → Bool) (m : ℕ) (hm : m < C.gates.length) :
    gateVal n C m y = (C.gates[m]).op.eval
      (C.gates[m].inputs.map fun i => (wf (C.gates.take m) (List.ofFn y)).getD i false) := by
  have h := gate_val C.gates (List.ofFn y) m hm
  rw [List.length_ofFn] at h
  exact h

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
theorem wire_reach (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (e : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (rec : ∀ j, j < k → (gateAt C j).op = GateOp.or → gateVal n C j e = true →
      (∀ i, InCone n C i j → (gateAt C i).op = GateOp.and → gateVal n C i e = false) →
      ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true → gateVal n C j y = true)
    (hown : ∀ i, InCone n C i k → (gateAt C i).op = GateOp.and → gateVal n C i e = false)
    (i : ℕ) (hi : i ∈ C.gates[k].inputs)
    (hv : (wf (C.gates.take k) (List.ofFn e)).getD i false = true) :
    ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true →
      (wf (C.gates.take k) (List.ofFn y)).getD i false = true := by
  have hik : i < n + k := by
    by_contra hge
    rw [List.getD_eq_default _ _ (by
      rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hk)]; omega)] at hv
    exact absurd hv (by decide)
  by_cases hin : i < n
  · refine ⟨⟨i, hin⟩, ?_, ?_⟩
    · rw [wf_keep _ _ i (by rw [List.length_ofFn]; exact hin)] at hv
      rw [← getD_ofFn e ⟨i, hin⟩]
      exact hv
    · intro y hy
      rw [wf_keep _ _ i (by rw [List.length_ofFn]; exact hin)]
      rw [← getD_ofFn y ⟨i, hin⟩] at hy
      exact hy
  · have hj : i - n < k := by omega
    have hjl : i - n < C.gates.length := by omega
    have hw : ∀ y : Fin n → Bool, (wf (C.gates.take k) (List.ofFn y)).getD i false
        = gateVal n C (i - n) y := by
      intro y
      rw [← wire_take C.gates (List.ofFn y) k i (by rw [List.length_ofFn]; exact hik) (le_of_lt hk)]
      show _ = (wf C.gates (List.ofFn y)).getD (n + (i - n)) false
      congr 1
      omega
    have hcone : InCone n C (i - n) k :=
      (cone_iff n C.gates k hk (i - n)).2 ⟨i, hi, by omega, hik, Or.inl rfl⟩
    have hop : (gateAt C (i - n)).op = GateOp.or := by
      rw [gateAt_eq C _ hjl]
      rcases (hC _ (List.getElem_mem hjl)).1 with h | h
      · exfalso
        have := hown (i - n) hcone (by rw [gateAt_eq C _ hjl]; exact h)
        rw [← hw e, hv] at this
        exact absurd this (by decide)
      · exact h
    obtain ⟨u, hu1, hu2⟩ := rec (i - n) hj hop (by rw [← hw e]; exact hv)
      (fun i' hc ha => hown i' ((cone_iff n C.gates k hk i').2 ⟨i, hi, by omega, hik, Or.inr hc⟩) ha)
    exact ⟨u, hu1, fun y hy => by rw [hw y]; exact hu2 y hy⟩

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
theorem or_reach (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (e : Fin n → Bool) : ∀ m, m < C.gates.length → (gateAt C m).op = GateOp.or →
      gateVal n C m e = true →
      (∀ i, InCone n C i m → (gateAt C i).op = GateOp.and → gateVal n C i e = false) →
      ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true → gateVal n C m y = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hop hval hown
    rw [gateAt_eq C m hm] at hop
    have hv2 := hval
    rw [valf n C e m hm, hop] at hv2
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hv2
    obtain ⟨i, hi, hiv⟩ := hv2
    obtain ⟨u, hu1, hu2⟩ := wire_reach n C hC e m hm
      (fun j hj h1 h2 h3 => ih j hj (lt_trans hj hm) h1 h2 h3) hown i hi hiv
    refine ⟨u, hu1, fun y hy => ?_⟩
    rw [valf n C y m hm, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact ⟨i, hi, hu2 y hy⟩

theorem cone_idx (n : ℕ) (gs : List Gate) : ∀ j i, i ∈ (cf n gs []).getD j [] → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i hc
    have hj := cone_lt n gs i j hc
    obtain ⟨w, _, hw1, hw2, hw3⟩ := (cone_iff n gs j hj i).1 hc
    rcases hw3 with e | e
    · omega
    · have := ih (w - n) (by omega) i e
      omega

theorem cone_trans (n : ℕ) (gs : List Gate) : ∀ j k i, k ∈ (cf n gs []).getD j [] →
    i ∈ (cf n gs []).getD k [] → i ∈ (cf n gs []).getD j [] := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro k i hk hi
    have hj := cone_lt n gs k j hk
    obtain ⟨w, hw, hw1, hw2, hw3⟩ := (cone_iff n gs j hj k).1 hk
    refine (cone_iff n gs j hj i).2 ⟨w, hw, hw1, hw2, Or.inr ?_⟩
    rcases hw3 with rfl | h
    · exact hi
    · exact ih (w - n) (by omega) k i h hi

end PEqualNP.Outside.L_meta_6266

open PEqualNP.Outside.L_meta_6266 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ), (∃ (x4 : ℕ), PEqualNP.EdgeOwnership.InCone x1 x2 x4 x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ x5 < x3, PEqualNP.EdgeOwnership.InCone x1 x2 x5 x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (∀ (x6 : ℕ), PEqualNP.EdgeOwnership.InCone x1 x2 x6 x5 → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∀ x6 < x5, ¬(PEqualNP.EdgeOwnership.InCone x1 x2 x6 x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and) := by
  intro n C j hex
  classical
  have hspec := Nat.find_spec hex
  have hmin := fun m (hm : m < Nat.find hex) => Nat.find_min hex hm
  refine ⟨Nat.find hex, cone_idx n C.gates j _ hspec.1, hspec.1, hspec.2, ?_, fun m hm => hmin m hm⟩
  intro m hm hand
  exact hmin m (cone_idx n C.gates _ m hm) ⟨cone_trans n C.gates j _ m hspec.1 hm, hand⟩
