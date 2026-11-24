import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3657
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

theorem gate_full (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length)
    (hrb : ∀ i ∈ gates[k].inputs, i < X.length + k) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf gates X).getD i false) := by
  rw [gate_val gates X k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (wire_take gates X k i (hrb i hi) (le_of_lt hk)).symm

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

end PEqualNP.Outside.L_meta_3657

open PEqualNP.Outside.L_meta_3657 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3657 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.Core.IsLiftFixedPoint G C →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) →
  (∀ k < C.gates.length, ∃ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C k x = true) →
  ∀ h < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op = PEqualNP.CircuitLowerBounds.GateOp.and →
    (PEqualNP.TopForm.BelowF G C h ↔ ∀ k < C.gates.length, PEqualNP.EdgeOwnership.InCone n C h k → (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or) := by
  intro n G _ C hAO hfun hcone hfix hnoand htrue h hh hand
  obtain ⟨hao, hrb, hlen2⟩ := hAO
  have Iff1 : ∀ i j (hj : j < C.gates.length), (PEqualNP.EdgeOwnership.InCone n C i j ↔
      ∃ w ∈ C.gates[j].inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ PEqualNP.EdgeOwnership.InCone n C i (w - n))) :=
    fun i j hj => cone_iff n C.gates j hj i
  have Ilt : ∀ i j, PEqualNP.EdgeOwnership.InCone n C i j → j < C.gates.length :=
    fun i j hc => cone_lt n C.gates i j hc
  have gv : ∀ (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length),
      PEqualNP.EdgeOwnership.gateVal n C k x = (C.gates[k]).op.eval
        (C.gates[k].inputs.map fun i => (wf C.gates (List.ofFn x)).getD i false) := by
    intro x k hk
    have h1 := gate_full C.gates (List.ofFn x) k hk (by
      intro i hi
      rw [List.length_ofFn]
      exact hrb k hk i (by rw [gateAt_eq C k hk]; exact hi))
    rw [List.length_ofFn] at h1
    exact h1
  have or_up : ∀ (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length),
      (C.gates[k]).op = GateOp.or → ∀ w ∈ C.gates[k].inputs,
      (wf C.gates (List.ofFn x)).getD w false = true →
      PEqualNP.EdgeOwnership.gateVal n C k x = true := by
    intro x k hk hop w hw hv
    rw [gv x k hk, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact ⟨w, hw, hv⟩
  have hwv : ∀ (x : Fin n → Bool) (w : ℕ), n ≤ w →
      (wf C.gates (List.ofFn x)).getD w false = PEqualNP.EdgeOwnership.gateVal n C (w - n) x := by
    intro x w hw
    show _ = (wf C.gates (List.ofFn x)).getD (n + (w - n)) false
    congr 1
    omega
  constructor
  · intro hB
    have V : ∀ k, PEqualNP.EdgeOwnership.InCone n C h k →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or ∧
          PEqualNP.TopForm.BelowF G C k := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hc
        have hk := Ilt h k hc
        obtain ⟨w, hw, h1, h2, h3⟩ := (Iff1 h k hk).1 hc
        have hm : w - n < k := by omega
        have hml : w - n < C.gates.length := by omega
        have hBm : PEqualNP.TopForm.BelowF G C (w - n) := by
          rcases h3 with e | e
          · rw [← e]; exact hB
          · exact (ih _ hm e).2
        have hor : (C.gates[k]).op = GateOp.or := by
          rcases hao C.gates[k] (List.getElem_mem hk) with ha | ho
          · exfalso
            apply hnoand k hk (by rw [gateAt_eq C k hk]; exact ha) w
              (by rw [gateAt_eq C k hk]; exact hw)
            intro x hx
            apply hBm x
            rw [← hwv x w h1]
            exact hx
          · exact ho
        refine ⟨by rw [gateAt_eq C k hk]; exact hor, ?_⟩
        by_contra hnb
        apply hfix
        obtain ⟨a0, a1, hin⟩ := List.length_eq_two.1 (hlen2 C.gates[k] (List.getElem_mem hk))
        have hb : ∃ b : Fin 2, PEqualNP.TopForm.opnd C k b = w := by
          unfold PEqualNP.TopForm.opnd
          rw [gateAt_eq C k hk, hin]
          rw [hin] at hw
          rcases List.mem_pair.1 hw with e | e
          · exact ⟨0, e.symm⟩
          · exact ⟨1, e.symm⟩
        obtain ⟨b, hb⟩ := hb
        refine ⟨k, hk, b, hcone k hk, by rw [gateAt_eq C k hk]; exact hor, hnb, ?_⟩
        rw [hb]
        refine ⟨?_, ?_⟩
        · intro x hx
          apply hBm x
          rw [← hwv x w h1]
          exact hx
        · obtain ⟨x, hx⟩ := htrue (w - n) hml
          refine ⟨x, ?_⟩
          show (wf C.gates (List.ofFn x)).getD w false = true
          rw [hwv x w h1]
          exact hx
    intro k hk hc
    exact (V k hc).1
  · intro hall x hx
    have U : ∀ k, PEqualNP.EdgeOwnership.InCone n C h k →
        PEqualNP.EdgeOwnership.gateVal n C k x = true := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hc
        have hk := Ilt h k hc
        obtain ⟨w, hw, h1, h2, h3⟩ := (Iff1 h k hk).1 hc
        have hop := hall k hk hc
        rw [gateAt_eq C k hk] at hop
        apply or_up x k hk hop w hw
        rw [hwv x w h1]
        rcases h3 with e | e
        · rw [← e]; exact hx
        · exact ih _ (by omega) e
    rw [← hfun]
    show (wf C.gates (List.ofFn x)).getD C.output false = true
    rcases hcone h hh with ⟨_, ho | ⟨ho1, ho2⟩⟩
    · rw [ho]; exact hx
    · rw [hwv x C.output ho1]
      exact U _ ho2
