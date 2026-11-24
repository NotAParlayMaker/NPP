import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3724

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

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

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


-- The rewired gate list: every read of wire n + w becomes a read of w2.

def sig (n w w2 : ℕ) (i : ℕ) : ℕ := if i = n + w then w2 else i

def phi (n w w2 : ℕ) (gg : Gate) : Gate :=
  { op := gg.op, inputs := gg.inputs.map (sig n w w2) }

def gates' (C : Circuit) (n w w2 : ℕ) : List Gate := C.gates.map (phi n w w2)

theorem len' (C : Circuit) (n w w2 : ℕ) : (gates' C n w w2).length = C.gates.length := by
  simp [gates']

theorem get' (C : Circuit) (n w w2 k : ℕ) (hk : k < (gates' C n w w2).length) :
    (gates' C n w w2)[k] = phi n w w2 (C.gates[k]'(by rw [len'] at hk; exact hk)) := by
  simp [gates']

theorem legal' (C : Circuit) (n w w2 : ℕ) (hC : IsAO2 n C) :
    ∀ g ∈ gates' C n w w2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [gates', List.mem_map] at hg
  obtain ⟨gg, hgg, rfl⟩ := hg
  refine ⟨hC.1 gg hgg, ?_⟩
  simp [phi, hC.2.2 gg hgg]

theorem legalC (C : Circuit) (n : ℕ) (hC : IsAO2 n C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
  fun g hg => ⟨hC.1 g hg, by rw [hC.2.2 g hg]⟩

theorem rbC (C : Circuit) (n : ℕ) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) :
    ∀ i ∈ C.gates[k].inputs, i < n + k := by
  intro i hi
  exact hC.2.1 k hk i (by rw [gateAt_eq C k hk]; exact hi)

-- On an input where wire n + w implies w2, the new circuit is at least the old one.
theorem up (C : Circuit) (n w w2 : ℕ) (hC : IsAO2 n C) (hw2 : w2 < n + w)
    (x : Fin n → Bool) (hx : val C.gates (n + w) x = true → val C.gates w2 x = true) :
    ∀ i, val C.gates i x = true → val (gates' C n w w2) i x = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro h
    by_cases hin : i < n
    · rw [val_input _ _ i hin] at h ⊢
      exact h
    by_cases hbig : n + C.gates.length ≤ i
    · rw [val_big _ _ i hbig] at h
      exact Bool.noConfusion h
    have hk : i - n < C.gates.length := by omega
    have hk' : i - n < (gates' C n w w2).length := by rw [len']; exact hk
    have he : n + (i - n) = i := by omega
    rw [← he] at h ⊢
    have hg := get' C n w w2 (i - n) hk'
    -- a read j of the old gate becomes sig j; its new value is at least the old one
    have step : ∀ j, j < n + (i - n) → val C.gates j x = true →
        sig n w w2 j < n + (i - n) ∧ val (gates' C n w w2) (sig n w w2 j) x = true := by
      intro j hj hv
      by_cases hjw : j = n + w
      · simp only [sig, hjw, ite_true]
        subst hjw
        exact ⟨by omega, ih w2 (by omega) (hx hv)⟩
      · simp only [sig, hjw, ite_false]
        exact ⟨hj, ih j (by omega) hv⟩
    rcases hC.1 _ (List.getElem_mem hk) with hand | hor
    · have hand' : (gates' C n w w2)[i - n].op = GateOp.and := by rw [hg]; exact hand
      rw [val_and _ x (i - n) hk' hand']
      have hold := (val_and _ x (i - n) hk hand).1 h
      intro j' hj'
      rw [hg] at hj'
      simp only [phi, List.mem_map] at hj'
      obtain ⟨j, hj, rfl⟩ := hj'
      exact step j (hold j hj).1 (hold j hj).2
    · have hor' : (gates' C n w w2)[i - n].op = GateOp.or := by rw [hg]; exact hor
      rw [val_or _ x (i - n) hk' hor']
      obtain ⟨j, hj, hjlt, hv⟩ := (val_or _ x (i - n) hk hor).1 h
      refine ⟨sig n w w2 j, ?_, step j hjlt hv⟩
      rw [hg]
      simp only [phi, List.mem_map]
      exact ⟨j, hj, rfl⟩

-- On an input where w2 implies wire n + w, the new circuit is at most the old one.
theorem down (C : Circuit) (n w w2 : ℕ) (hC : IsAO2 n C) (hw2 : w2 < n + w)
    (x : Fin n → Bool) (hx : val C.gates w2 x = true → val C.gates (n + w) x = true) :
    ∀ i, val (gates' C n w w2) i x = true → val C.gates i x = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro h
    by_cases hin : i < n
    · rw [val_input _ _ i hin] at h ⊢
      exact h
    by_cases hbig : n + C.gates.length ≤ i
    · rw [val_big _ _ i (by rw [len']; exact hbig)] at h
      exact Bool.noConfusion h
    have hk : i - n < C.gates.length := by omega
    have hk' : i - n < (gates' C n w w2).length := by rw [len']; exact hk
    have he : n + (i - n) = i := by omega
    rw [← he] at h ⊢
    have hg := get' C n w w2 (i - n) hk'
    have hrb := rbC C n hC (i - n) hk
    -- an old read j: the new gate reads sig j; the old value is at least the new one
    have step : ∀ j, j < n + (i - n) → val (gates' C n w w2) (sig n w w2 j) x = true →
        val C.gates j x = true := by
      intro j hj hv
      by_cases hjw : j = n + w
      · simp only [sig, hjw, ite_true] at hv
        subst hjw
        exact hx (ih w2 (by omega) hv)
      · simp only [sig, hjw, ite_false] at hv
        exact ih j (by omega) hv
    rcases hC.1 _ (List.getElem_mem hk) with hand | hor
    · have hand' : (gates' C n w w2)[i - n].op = GateOp.and := by rw [hg]; exact hand
      have hnew := (val_and _ x (i - n) hk' hand').1 h
      rw [val_and _ x (i - n) hk hand]
      intro j hj
      refine ⟨hrb j hj, step j (hrb j hj) ?_⟩
      have hmem : sig n w w2 j ∈ (gates' C n w w2)[i - n].inputs := by
        rw [hg]
        simp only [phi, List.mem_map]
        exact ⟨j, hj, rfl⟩
      exact (hnew _ hmem).2
    · have hor' : (gates' C n w w2)[i - n].op = GateOp.or := by rw [hg]; exact hor
      obtain ⟨j', hj', _, hv⟩ := (val_or _ x (i - n) hk' hor').1 h
      rw [hg] at hj'
      simp only [phi, List.mem_map] at hj'
      obtain ⟨j, hj, rfl⟩ := hj'
      rw [val_or _ x (i - n) hk hor]
      exact ⟨j, hj, hrb j hj, step j (hrb j hj) hv⟩

theorem exists_mis {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) :
    ∃ M : Finset (Fin n), S ⊆ M ∧ (∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v) ∧
      (∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v) := by
  classical
  let F := (Finset.univ : Finset (Finset (Fin n))).filter
    (fun M => S ⊆ M ∧ ∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v)
  have hne : F.Nonempty := ⟨S, by simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨le_refl S, hS⟩⟩
  obtain ⟨M, hM, hmax⟩ := F.exists_max_image Finset.card hne
  simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hM hmax
  refine ⟨M, hM.1, hM.2, ?_⟩
  intro v hv
  by_contra hno
  push Not at hno
  have hind : ∀ a ∈ insert v M, ∀ b ∈ insert v M, ¬ G.Adj a b := by
    intro a ha b hb
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact G.irrefl
    · exact fun h => hno b hb h.symm
    · exact hno a ha
    · exact hM.2 a ha b hb
  have := hmax (insert v M) ⟨hM.1.trans (Finset.subset_insert _ _), hind⟩
  rw [Finset.card_insert_of_notMem hv] at this
  omega

theorem graphFun_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
  simp [graphFun]

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w w2 : ℕ)
    (hC : IsAO2 n C) (hf : circuitFun n C = graphFun G ∅) (hw2 : w2 < n + w)
    (hE : ∀ u v : Fin n, G.Adj u v →
      val C.gates (n + w) (fun z : Fin n => decide (z = u ∨ z = v)) = true →
      val C.gates w2 (fun z : Fin n => decide (z = u ∨ z = v)) = true)
    (hM : ∀ M : Finset (Fin n), (∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v) →
      (∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v) →
      val C.gates w2 (fun z : Fin n => decide (z ∈ M)) = true →
      val C.gates (n + w) (fun z : Fin n => decide (z ∈ M)) = true) :
    ∀ x : Fin n → Bool, val (gates' C n w w2) (sig n w w2 C.output) x = graphFun G ∅ x := by
  have legal := legal' C n w w2 hC
  have hold : ∀ x, val C.gates C.output x = graphFun G ∅ x := fun x => congrFun hf x
  -- true at every edge
  have edge : ∀ u v, G.Adj u v →
      val (gates' C n w w2) (sig n w w2 C.output) (fun z : Fin n => decide (z = u ∨ z = v)) = true := by
    intro u v huv
    have h1 : val C.gates C.output (fun z : Fin n => decide (z = u ∨ z = v)) = true := by
      rw [hold, graphFun_eq]
      simp only [decide_eq_true_eq]
      exact ⟨u, v, huv, by simp, by simp⟩
    by_cases ho : C.output = n + w
    · simp only [sig, ho, ite_true]
      rw [ho] at h1
      exact up C n w w2 hC hw2 _ (hE u v huv) w2 (hE u v huv h1)
    · simp only [sig, ho, ite_false]
      exact up C n w w2 hC hw2 _ (hE u v huv) _ h1
  -- false at every maximal independent set
  have mis : ∀ M : Finset (Fin n), (∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v) →
      (∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v) →
      val (gates' C n w w2) (sig n w w2 C.output) (fun z : Fin n => decide (z ∈ M)) = false := by
    intro M hind hmax
    have hfalse : val C.gates C.output (fun z : Fin n => decide (z ∈ M)) = false := by
      rw [hold, graphFun_eq]
      simp only [decide_eq_false_iff_not, decide_eq_true_eq, not_exists, not_and]
      intro u v huv hu hv
      exact hind u hu v hv huv
    cases hnew : val (gates' C n w w2) (sig n w w2 C.output) (fun z : Fin n => decide (z ∈ M))
    · rfl
    exfalso
    have hd := down C n w w2 hC hw2 _ (hM M hind hmax)
    by_cases ho : C.output = n + w
    · simp only [sig, ho, ite_true] at hnew
      have := hM M hind hmax (hd w2 hnew)
      rw [← ho, hfalse] at this
      exact Bool.noConfusion this
    · simp only [sig, ho, ite_false] at hnew
      rw [hd _ hnew] at hfalse
      exact Bool.noConfusion hfalse
  intro x
  rw [graphFun_eq]
  by_cases hx : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  · obtain ⟨u, v, huv, hu, hv⟩ := hx
    rw [decide_eq_true ⟨u, v, huv, hu, hv⟩]
    apply val_mono _ legal _ x _ _ (edge u v huv)
    intro z hz
    simp only [decide_eq_true_eq] at hz
    rcases hz with rfl | rfl
    · exact hu
    · exact hv
  · rw [decide_eq_false hx]
    have hS : ∀ u ∈ Finset.univ.filter (fun z => x z = true),
        ∀ v ∈ Finset.univ.filter (fun z => x z = true), ¬ G.Adj u v := by
      intro u hu v hv huv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      exact hx ⟨u, v, huv, hu, hv⟩
    obtain ⟨M, hSM, hind, hmax⟩ := exists_mis G _ hS
    cases hval : val (gates' C n w w2) (sig n w w2 C.output) x
    · rfl
    exfalso
    have := val_mono _ legal x (fun z : Fin n => decide (z ∈ M)) (by
      intro z hz
      simp only [decide_eq_true_eq]
      exact hSM (by simp [hz])) _ hval
    rw [mis M hind hmax] at this
    exact Bool.noConfusion this

end PEqualNP.Outside.L_meta_3724

theorem PEqualNP.Outside.L_meta_3724 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (w w2 : ℕ),
  PEqualNP.TopForm.IsAO2 n C →
  PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
  w < C.gates.length → w2 < n + w →
  (∀ u v : Fin n, G.Adj u v →
    (C.wires (List.ofFn (fun z : Fin n => decide (z = u ∨ z = v)))).getD (n + w) false = true →
    (C.wires (List.ofFn (fun z : Fin n => decide (z = u ∨ z = v)))).getD w2 false = true) →
  (∀ M : Finset (Fin n), (∀ u ∈ M, ∀ v ∈ M, ¬ G.Adj u v) → (∀ v : Fin n, v ∉ M → ∃ u ∈ M, G.Adj u v) →
    (C.wires (List.ofFn (fun z : Fin n => decide (z ∈ M)))).getD w2 false = true →
    (C.wires (List.ofFn (fun z : Fin n => decide (z ∈ M)))).getD (n + w) false = true) →
  PEqualNP.MetaComplexity.circuitFun n
      ({ gates := C.gates.map (fun gg => ({ op := gg.op, inputs := gg.inputs.map (fun i => if i = n + w then w2 else i) } : PEqualNP.CircuitLowerBounds.Gate)),
         output := if C.output = n + w then w2 else C.output } : PEqualNP.CircuitLowerBounds.Circuit)
    = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C w w2 hC hf _ hw2 hE hM
  funext x
  exact PEqualNP.Outside.L_meta_3724.main n G C w w2 hC hf hw2 hE hM x
