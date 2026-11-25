import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8889
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

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

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

def Has (n : ℕ) (D : Circuit) (w : ℕ) (F : (Fin n → Bool) → Bool) : Prop :=
  w < n + D.gates.length ∧ ∀ x : Fin n → Bool, (wf D.gates (List.ofFn x)).getD w false = F x

theorem has_input (n : ℕ) (D : Circuit) (v : Fin n) : Has n D v.val (fun x => x v) := by
  refine ⟨by have := v.isLt; omega, fun x => ?_⟩
  rw [wf_keep _ _ _ (by simp)]
  exact getD_ofFn x v

theorem has_ext (n : ℕ) (D : Circuit) (extra : List Gate) (o : ℕ) (w : ℕ)
    (F : (Fin n → Bool) → Bool) (h : Has n D w F) : Has n ⟨D.gates ++ extra, o⟩ w F := by
  refine ⟨by have := h.1; simp only [List.length_append]; omega, fun x => ?_⟩
  show (wf (D.gates ++ extra) (List.ofFn x)).getD w false = F x
  rw [wf_prefix _ _ _ _ (by simpa using h.1)]
  exact h.2 x

theorem snoc_gate (n : ℕ) (D : Circuit) (hD : PEqualNP.TopForm.IsAO2 n D) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (Fa Fb : (Fin n → Bool) → Bool)
    (ha : Has n D a Fa) (hb : Has n D b Fb) (o : ℕ) :
    PEqualNP.TopForm.IsAO2 n ⟨D.gates ++ [⟨op, [a, b]⟩], o⟩ ∧
    Has n ⟨D.gates ++ [⟨op, [a, b]⟩], o⟩ (n + D.gates.length) (fun x => op.eval [Fa x, Fb x]) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hD.1 g h
    · rw [List.mem_singleton.1 h]; exact hop
  · intro j hj i hi
    rw [gateAt_eq _ j hj] at hi
    have hj' : j < D.gates.length + 1 := by simpa using hj
    by_cases hjl : j < D.gates.length
    · have e : (D.gates ++ [(⟨op, [a, b]⟩ : Gate)])[j] = D.gates[j] := List.getElem_append_left hjl
      rw [e] at hi
      exact hD.2.1 j hjl i (by rw [gateAt_eq D j hjl]; exact hi)
    · have hje : j = D.gates.length := by omega
      subst hje
      have e : (D.gates ++ [(⟨op, [a, b]⟩ : Gate)])[D.gates.length] = ⟨op, [a, b]⟩ := by simp
      rw [e] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha.1
      · exact hb.1
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hD.2.2 g h
    · rw [List.mem_singleton.1 h]
      rfl
  · show n + D.gates.length < n + (D.gates ++ [(⟨op, [a, b]⟩ : Gate)]).length
    simp
  · intro x
    show (wf (D.gates ++ [(⟨op, [a, b]⟩ : Gate)]) (List.ofFn x)).getD (n + D.gates.length) false = _
    rw [wf_append, wf_cons]
    show ((wf D.gates (List.ofFn x)) ++ [_]).getD (n + D.gates.length) false = _
    have hl : (wf D.gates (List.ofFn x)).length = n + D.gates.length := by rw [wf_len]; simp
    rw [← hl, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, ha.2 x, hb.2 x]

def rhoF (x1 x2 : ℕ) (f : Fin x1 → Fin x2) (i : ℕ) : ℕ :=
  if h : i < x1 then (f ⟨i, h⟩).val else i - x1 + x2

def rgF (x1 x2 : ℕ) (f : Fin x1 → Fin x2) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rhoF x1 x2 f)⟩

theorem rhoF_lt (x1 x2 : ℕ) (f : Fin x1 → Fin x2) (i j : ℕ) (h : i < x1 + j) :
    rhoF x1 x2 f i < x2 + j := by
  unfold rhoF
  by_cases hi : i < x1
  · rw [dif_pos hi]
    have := (f ⟨i, hi⟩).isLt
    omega
  · rw [dif_neg hi]
    omega

theorem keyF (x1 x2 : ℕ) (f : Fin x1 → Fin x2) (x : Fin x2 → Bool) (G : List Bool) (i : ℕ) :
    (List.ofFn (x ∘ f) ++ G).getD i false = (List.ofFn x ++ G).getD (rhoF x1 x2 f i) false := by
  unfold rhoF
  by_cases hi : i < x1
  · rw [dif_pos hi, List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_append _ _ _ _ (by simp)]
    have e1 := getD_ofFn (x ∘ f) ⟨i, hi⟩
    have e2 := getD_ofFn x (f ⟨i, hi⟩)
    simp only at e1 e2
    rw [e1, e2]
    rfl
  · rw [dif_neg hi, List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn]
    congr 1
    omega

theorem simF (x1 x2 : ℕ) (f : Fin x1 → Fin x2) (x : Fin x2 → Bool) : ∀ (gs : List Gate) (G : List Bool),
    ∃ G' : List Bool, wf gs (List.ofFn (x ∘ f) ++ G) = List.ofFn (x ∘ f) ++ G' ∧
      wf (gs.map (rgF x1 x2 f)) (List.ofFn x ++ G) = List.ofFn x ++ G' := by
  intro gs
  induction gs with
  | nil => intro G; exact ⟨G, rfl, rfl⟩
  | cons g gs ih =>
    intro G
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : (rgF x1 x2 f g).op.eval ((rgF x1 x2 f g).inputs.map fun i => (List.ofFn x ++ G).getD i false)
        = g.op.eval (g.inputs.map fun i => (List.ofFn (x ∘ f) ++ G).getD i false) := by
      show g.op.eval ((g.inputs.map (rhoF x1 x2 f)).map fun i => (List.ofFn x ++ G).getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact (keyF x1 x2 f x G a).symm
    rw [hv, List.append_assoc, List.append_assoc]
    exact ih _

theorem renF (x1 x2 : ℕ) (f : Fin x1 → Fin x2) (gs : List Gate) (x : Fin x2 → Bool) (w : ℕ) :
    (wf (gs.map (rgF x1 x2 f)) (List.ofFn x)).getD (rhoF x1 x2 f w) false
      = (wf gs (List.ofFn (x ∘ f))).getD w false := by
  obtain ⟨G', h1, h2⟩ := simF x1 x2 f x gs []
  rw [List.append_nil] at h1 h2
  rw [h1, h2]
  exact (keyF x1 x2 f x G' w).symm

theorem orchain (n : ℕ) : ∀ (bs : List (Fin n)), bs ≠ [] → ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D →
    ∃ (extra : List Gate) (w : ℕ), extra.length + 1 = bs.length ∧
      (∀ o, PEqualNP.TopForm.IsAO2 n ⟨D.gates ++ extra, o⟩) ∧
      (∀ o, Has n ⟨D.gates ++ extra, o⟩ w (fun x => bs.any x)) := by
  intro bs
  induction bs with
  | nil => intro h; exact absurd rfl h
  | cons b t ih =>
    intro _ D hD
    by_cases ht : t = []
    · subst ht
      refine ⟨[], b.val, rfl, fun o => ?_, fun o => ?_⟩
      · rw [List.append_nil]
        exact ⟨hD.1, hD.2.1, hD.2.2⟩
      · have := has_input n ⟨D.gates ++ [], o⟩ b
        simpa using this
    · obtain ⟨extra, w, hlen, hA, hH⟩ := ih ht D hD
      have hs := snoc_gate n ⟨D.gates ++ extra, 0⟩ (hA 0) GateOp.or (Or.inr rfl) b.val w
        (fun x => x b) (fun x => t.any x) (has_input n _ b) (hH 0)
      refine ⟨extra ++ [⟨GateOp.or, [b.val, w]⟩], n + (D.gates ++ extra).length, by simp; omega,
        fun o => ?_, fun o => ?_⟩
      · rw [← List.append_assoc]
        exact (hs o).1
      · rw [← List.append_assoc]
        have := (hs o).2
        simpa [GateOp.eval] using this

theorem terms (n : ℕ) : ∀ (L : List (Fin n × List (Fin n))), (∀ p ∈ L, p.2 ≠ []) →
    ∀ (D : Circuit) (F : (Fin n → Bool) → Bool) (r : Option ℕ), PEqualNP.TopForm.IsAO2 n D →
    (∀ w, r = some w → Has n D w F) → (r = none → F = fun _ => false) →
    ∃ D' : Circuit, PEqualNP.TopForm.IsAO2 n D' ∧
      D'.gates.length ≤ D.gates.length + (L.map fun p => p.2.length + 1).sum ∧
      ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D' x
        = (F x || L.any fun p => x p.1 && p.2.any x) := by
  intro L
  induction L with
  | nil =>
    intro _ D F r hD hs hn
    cases r with
    | none =>
      refine ⟨⟨D.gates, n + D.gates.length⟩, ⟨hD.1, hD.2.1, hD.2.2⟩, by simp, fun x => ?_⟩
      show (wf D.gates (List.ofFn x)).getD (n + D.gates.length) false = _
      rw [List.getD_eq_default _ _ (by rw [wf_len]; simp), hn rfl]
      rfl
    | some w =>
      refine ⟨⟨D.gates, w⟩, ⟨hD.1, hD.2.1, hD.2.2⟩, by simp, fun x => ?_⟩
      show (wf D.gates (List.ofFn x)).getD w false = _
      rw [(hs w rfl).2 x]
      simp
  | cons p L ih =>
    intro hL D F r hD hs hn
    obtain ⟨extra, w, hlen, hA, hH⟩ := orchain n p.2 (hL p (List.mem_cons_self ..)) D hD
    have ha := snoc_gate n ⟨D.gates ++ extra, 0⟩ (hA 0) GateOp.and (Or.inl rfl) p.1.val w
      (fun x => x p.1) (fun x => p.2.any x) (has_input n _ p.1) (hH 0) 0
    have hL' : ∀ q ∈ L, q.2 ≠ [] := fun q hq => hL q (List.mem_cons_of_mem _ hq)
    cases r with
    | none =>
      obtain ⟨D', h1, h2, h3⟩ := ih hL' _ _ (some (n + (D.gates ++ extra).length)) ha.1
        (fun w' hw' => by rw [← Option.some.inj hw']; exact ha.2) (fun h => by simp at h)
      refine ⟨D', h1, ?_, fun x => ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, List.map_cons,
          List.sum_cons] at h2 ⊢
        omega
      · rw [h3 x, hn rfl]
        simp [GateOp.eval]
    | some rw' =>
      have hr := has_ext n D (extra ++ [⟨GateOp.and, [p.1.val, w]⟩]) 0 rw' F (hs rw' rfl)
      rw [← List.append_assoc] at hr
      have ho := snoc_gate n _ ha.1 GateOp.or (Or.inr rfl) rw' (n + (D.gates ++ extra).length)
        F _ hr ha.2 0
      obtain ⟨D', h1, h2, h3⟩ := ih hL' _ _ (some _) ho.1
        (fun w' hw' => by rw [← Option.some.inj hw']; exact ho.2) (fun h => by simp at h)
      refine ⟨D', h1, ?_, fun x => ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, List.map_cons,
          List.sum_cons] at h2 ⊢
        omega
      · rw [h3 x]
        simp [GateOp.eval, Bool.or_assoc]

end PEqualNP.Outside.L_meta_8889

open PEqualNP.Outside.L_meta_8889 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8889 : ∀ {x1 x2 : ℕ} (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x4 → ∀ (x6 : List (Fin x2 × List (Fin x2))), (∀ x7 ∈ x6, x7.2 ≠ []) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x2 x8 ∧ x8.size ≤ x4.size + (List.map (fun (x9 : Fin x2 × List (Fin x2)) => x9.2.length + (1 : ℕ)) x6).sum ∧ ∀ (x9 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x8 x9 = (PEqualNP.MetaComplexity.circuitFun x1 x4 (x9 ∘ x3) || x6.any fun (x10 : Fin x2 × List (Fin x2)) => x9 x10.1 && x10.2.any x9) := by
  intro x1 x2 f C hAO L hL
  have hD0 : PEqualNP.TopForm.IsAO2 x2 ⟨C.gates.map (rgF x1 x2 f), 0⟩ := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact hAO.1 g0 hg0
    · intro j hj i hi
      rw [gateAt_eq _ j hj] at hi
      have hj' : j < C.gates.length := by simpa using hj
      have e : (C.gates.map (rgF x1 x2 f))[j] = rgF x1 x2 f C.gates[j] := by simp
      rw [e] at hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
      exact rhoF_lt x1 x2 f i0 j (hAO.2.1 j hj' i0 (by rw [gateAt_eq C j hj']; exact hi0))
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      show (g0.inputs.map (rhoF x1 x2 f)).length = 2
      rw [List.length_map]
      exact hAO.2.2 g0 hg0
  have hlen0 : (C.gates.map (rgF x1 x2 f)).length = C.gates.length := by simp
  by_cases ho : C.output < x1 + C.gates.length
  · obtain ⟨D', h1, h2, h3⟩ := terms x2 L hL ⟨C.gates.map (rgF x1 x2 f), 0⟩
      (fun x => PEqualNP.MetaComplexity.circuitFun x1 C (x ∘ f)) (some (rhoF x1 x2 f C.output)) hD0
      (fun w hw => by
        rw [← Option.some.inj hw]
        refine ⟨?_, fun x => ?_⟩
        · show rhoF x1 x2 f C.output < x2 + (C.gates.map (rgF x1 x2 f)).length
          rw [hlen0]
          exact rhoF_lt x1 x2 f _ _ ho
        · exact renF x1 x2 f C.gates x C.output)
      (fun h => by simp at h)
    refine ⟨D', h1, ?_, h3⟩
    show D'.gates.length ≤ C.gates.length + _
    rw [← hlen0]
    exact h2
  · obtain ⟨D', h1, h2, h3⟩ := terms x2 L hL ⟨C.gates.map (rgF x1 x2 f), 0⟩
      (fun x => PEqualNP.MetaComplexity.circuitFun x1 C (x ∘ f)) none hD0
      (fun w hw => by simp at hw)
      (fun _ => by
        funext x
        show (wf C.gates (List.ofFn (x ∘ f))).getD C.output false = false
        exact List.getD_eq_default _ _ (by rw [wf_len]; simp; omega))
    refine ⟨D', h1, ?_, h3⟩
    show D'.gates.length ≤ C.gates.length + _
    rw [← hlen0]
    exact h2
