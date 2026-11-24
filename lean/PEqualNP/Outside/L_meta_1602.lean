import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1602_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

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

def val {m : ℕ} (gates : List Gate) (w : ℕ) (x : Fin m → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq {m : ℕ} (gates : List Gate) (x : Fin m → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < m + k ∧ val gates i x = true := by
  by_cases hi : i < m + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and {m : ℕ} (gates : List Gate) (x : Fin m → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (m + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < m + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or {m : ℕ} (gates : List Gate) (x : Fin m → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (m + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < m + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input {m : ℕ} (gates : List Gate) (x : Fin m → Bool) (w : ℕ) (hw : w < m) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simp; exact hw)]
  exact List.getElem_ofFn _

theorem val_big {m : ℕ} (gates : List Gate) (x : Fin m → Bool) (w : ℕ)
    (hw : m + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono {m : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin m → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) :
    val gs w x = true → val gs w y = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < m
    · simpa only [val_input gs _ w hw] using hxy ⟨w, hw⟩
    by_cases hg : w < m + gs.length
    · have hi : w - m < gs.length := by omega
      have he : m + (w - m) = w := by omega
      rcases (legal gs[w - m] (List.getElem_mem hi)).1 with ha | ho
      · intro h
        have hs := (val_and gs x (w - m) hi ha).mp (by simpa only [he] using h)
        rw [← he]
        apply (val_and gs y (w - m) hi ha).mpr
        intro r hr
        obtain ⟨hlt, hit⟩ := hs r hr
        exact ⟨hlt, ih r (by omega) hit⟩
      · intro h
        obtain ⟨r, hr, hlt, hit⟩ := (val_or gs x (w - m) hi ho).mp (by simpa only [he] using h)
        rw [← he]
        exact (val_or gs y (w - m) hi ho).mpr ⟨r, hr, hlt, ih r (by omega) hit⟩
    · simp [val_big gs x w (by omega)]

theorem final_thm : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
  intro hclean m H _ hC4 D hmono hfun hpair
  by_cases hm : m = 0
  · subst hm
    refine ⟨∅, fun y => Fin.elim0 y, ?_⟩
    have hemp : H.edgeFinset = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false]
      induction e using Sym2.ind with
      | _ u v => exact Fin.elim0 u
    rw [hemp]
    simp
  have hmpos : 0 < m := by omega
  let e0 : Fin m := ⟨0, hmpos⟩
  have hleg : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hmono g hg
    exact ⟨by simpa using hop, hlen⟩
  have hgateAt : ∀ k (hk : k < D.gates.length), gateAt D k = D.gates[k] := by
    intro k hk
    unfold gateAt
    exact List.getD_eq_getElem _ _ hk
  have hand_clean : ∀ (k : ℕ) (hk : k < D.gates.length), D.gates[k].op = GateOp.and →
      ∀ x : Fin m → Bool, val D.gates (m + k) x = true → ∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk hop x hval
      by_contra hno
      have hor_trace : ∀ w < m + k, val D.gates w x = true → ∃ u : Fin m, x u = true ∧ val D.gates w (pairInput u u) = true := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ihw =>
          intro hw hvw
          by_cases hwm : w < m
          · refine ⟨⟨w, hwm⟩, ?_, ?_⟩
            · rw [val_input D.gates x w hwm] at hvw; exact hvw
            · rw [val_input D.gates _ w hwm]; simp [pairInput]
          · have hj : w - m < k := by omega
            have hjlen : w - m < D.gates.length := by omega
            have hweq : m + (w - m) = w := by omega
            rcases (hleg D.gates[w - m] (List.getElem_mem hjlen)).1 with handj | horj
            · exact False.elim (hno (ih (w - m) hj hjlen handj x (by simpa only [hweq] using hvw)))
            · obtain ⟨a, ha, halt, hva⟩ := (val_or D.gates x (w - m) hjlen horj).mp (by simpa only [hweq] using hvw)
              obtain ⟨u, hxu, hvau⟩ := ihw a (by omega) (by omega) hva
              refine ⟨u, hxu, ?_⟩
              rw [← hweq]
              exact (val_or D.gates (pairInput u u) (w - m) hjlen horj).mpr ⟨a, ha, halt, hvau⟩
      have hlen := (hleg D.gates[k] (List.getElem_mem hk)).2
      have hop_at : (gateAt D k).op = GateOp.and := by rw [hgateAt k hk]; exact hop
      match hin : D.gates[k].inputs with
      | [] =>
        have htrue : val D.gates (m + k) (pairInput e0 e0) = true :=
          (val_and D.gates (pairInput e0 e0) k hk hop).mpr (by rw [hin]; simp)
        have hfalse := hpair k hk hop_at e0 e0 (H.loopless.irrefl e0)
        change val D.gates (m + k) (pairInput e0 e0) = false at hfalse
        rw [hfalse] at htrue; simp at htrue
      | [a] =>
        have ha := (val_and D.gates x k hk hop).mp hval a (by rw [hin]; simp)
        obtain ⟨u, _, hvau⟩ := hor_trace a ha.1 ha.2
        have htrue : val D.gates (m + k) (pairInput u u) = true := by
          apply (val_and D.gates (pairInput u u) k hk hop).mpr
          intro i hi
          rw [hin, List.mem_singleton] at hi; subst hi
          exact ⟨ha.1, hvau⟩
        have hfalse := hpair k hk hop_at u u (H.loopless.irrefl u)
        change val D.gates (m + k) (pairInput u u) = false at hfalse
        rw [hfalse] at htrue; simp at htrue
      | [a, b] =>
        have ha := (val_and D.gates x k hk hop).mp hval a (by rw [hin]; simp)
        have hb := (val_and D.gates x k hk hop).mp hval b (by rw [hin]; simp)
        obtain ⟨u, hxu, hvau⟩ := hor_trace a ha.1 ha.2
        obtain ⟨v, hxv, hvbv⟩ := hor_trace b hb.1 hb.2
        have hvauv : val D.gates a (pairInput u v) = true :=
          val_mono D.gates hleg (pairInput u u) (pairInput u v)
            (fun z hz => by simp only [pairInput, decide_eq_true_eq] at hz ⊢; rcases hz with rfl | rfl <;> exact Or.inl rfl) a hvau
        have hvbuv : val D.gates b (pairInput u v) = true :=
          val_mono D.gates hleg (pairInput v v) (pairInput u v)
            (fun z hz => by simp only [pairInput, decide_eq_true_eq] at hz ⊢; rcases hz with rfl | rfl <;> exact Or.inr rfl) b hvbv
        have htrue : val D.gates (m + k) (pairInput u v) = true := by
          apply (val_and D.gates (pairInput u v) k hk hop).mpr
          intro i hi
          rw [hin] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨ha.1, hvauv⟩
          · exact ⟨hb.1, hvbuv⟩
        have hnadj : ¬ H.Adj u v := fun hadj => hno ⟨u, v, hadj, hxu, hxv⟩
        have hfalse := hpair k hk hop_at u v hnadj
        change val D.gates (m + k) (pairInput u v) = false at hfalse
        rw [hfalse] at htrue; simp at htrue
      | _ :: _ :: _ :: _ => rw [hin] at hlen; simp at hlen
  have hcomp : ∀ x : Fin m → Bool, Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x) = decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    have hx := congrFun hfun x
    simp only [circuitFun, graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or] at hx
    exact hx
  exact hclean m H hC4 D.gates D.output hleg hcomp (fun i x hi hval => hand_clean i.val i.isLt hi x hval)

end PEqualNP.Outside.L_meta_1602_aux

theorem PEqualNP.Outside.L_meta_1602 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 :=
  PEqualNP.Outside.L_meta_1602_aux.final_thm
