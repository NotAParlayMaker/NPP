import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta201

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (step w g)
    exact ⟨_ :: t, by rw [List.foldl_cons, ht, step, List.append_assoc]; rfl⟩

theorem fold_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

def Le (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

def Bad (wu wv wuv : List Bool) (i : ℕ) : Prop :=
  wu.getD i false = false ∧ wv.getD i false = false ∧ wuv.getD i false = true

def AndOr (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i < w.length then w.getD i false
      else if i = w.length then b else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem eval_mono (g : Gate) (hg : AndOr g) (F F' : ℕ → Bool)
    (h : ∀ i, F i = true → F' i = true) :
    g.op.eval (g.inputs.map F) = true → g.op.eval (g.inputs.map F') = true := by
  rcases hg.1 with h1 | h1 <;> rw [h1] <;> simp only [GateOp.eval, List.all_map, List.any_map,
    List.all_eq_true, List.any_eq_true, Function.comp_apply, id] <;> intro hx
  · exact fun a ha => h a (hx a ha)
  · obtain ⟨a, ha, hfa⟩ := hx
    exact ⟨a, ha, h a hfa⟩

theorem le_step (g : Gate) (hg : AndOr g) (w w' : List Bool) (h : Le w w') :
    Le (step w g) (step w' g) := by
  refine ⟨by simp [step, h.1], fun i hi => ?_⟩
  simp only [step, getD_snoc] at hi ⊢
  rw [← h.1]
  split_ifs at hi ⊢ with h1 h2
  · exact h.2 i hi
  · exact eval_mono g hg _ _ h.2 hi

theorem new_gate (g : Gate) (hg : AndOr g) (wu wv wuv : List Bool)
    (hu : Le wu wuv) (hv : Le wv wuv) (hgood : ∀ i, ¬ Bad wu wv wuv i)
    (h0 : g.op.eval (g.inputs.map fun i => wu.getD i false) = false)
    (h1 : g.op.eval (g.inputs.map fun i => wv.getD i false) = false)
    (h2 : g.op.eval (g.inputs.map fun i => wuv.getD i false) = true) :
    ∃ a b : ℕ, g.op = GateOp.and ∧ g.inputs = [a, b] ∧ a < wuv.length ∧ b < wuv.length ∧
      ((wu.getD a false = true ∧ wv.getD a false = false ∧
        wv.getD b false = true ∧ wu.getD b false = false) ∨
       (wv.getD a false = true ∧ wu.getD a false = false ∧
        wu.getD b false = true ∧ wv.getD b false = false)) := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen h0 h1 h2 ⊢
  have lt_of : ∀ i, wuv.getD i false = true → i < wuv.length := by
    intro i hi
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at hi
    exact Bool.false_ne_true hi
  have gd := fun i => hgood i
  simp only [Bad] at gd
  match l, hlen with
  | [], _ => rcases hop with rfl | rfl <;> simp [GateOp.eval] at h0 h2
  | [a], _ =>
    rcases hop with rfl | rfl <;> simp [GateOp.eval] at h0 h1 h2 <;> exact (gd a ⟨h0, h1, h2⟩).elim
  | [a, b], _ =>
    have ga := gd a
    have gb := gd b
    have mua := hu.2 a
    have mub := hu.2 b
    have mva := hv.2 a
    have mvb := hv.2 b
    simp only [List.map_cons, List.map_nil] at h0 h1 h2
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true,
        Bool.and_eq_true, Bool.and_eq_false_iff] at h0 h1 h2
      refine ⟨a, b, rfl, rfl, lt_of a h2.1, lt_of b h2.2, ?_⟩
      revert ga gb mua mub mva mvb h0 h1 h2
      generalize wu.getD a false = A1
      generalize wu.getD b false = B1
      generalize wv.getD a false = A2
      generalize wv.getD b false = B2
      generalize wuv.getD a false = A3
      generalize wuv.getD b false = B3
      cases A1 <;> cases B1 <;> cases A2 <;> cases B2 <;> cases A3 <;> cases B3 <;> simp
    · exfalso
      simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] at h0 h1 h2
      revert ga gb h0 h1 h2
      generalize wu.getD a false = A1
      generalize wu.getD b false = B1
      generalize wv.getD a false = A2
      generalize wv.getD b false = B2
      generalize wuv.getD a false = A3
      generalize wuv.getD b false = B3
      cases A1 <;> cases B1 <;> cases A2 <;> cases B2 <;> cases A3 <;> cases B3 <;> simp
  | _ :: _ :: _ :: _, h => simp at h

theorem main (gs : List Gate) (hgs : ∀ g ∈ gs, AndOr g) : ∀ wu wv wuv : List Bool,
    Le wu wuv → Le wv wuv → (∀ i, ¬ Bad wu wv wuv i) →
    (∃ i, Bad (gs.foldl step wu) (gs.foldl step wv) (gs.foldl step wuv) i) →
    ∃ j : ℕ, ∃ (g : Gate) (a b : ℕ), gs[j]? = some g ∧ g.op = GateOp.and ∧ g.inputs = [a, b] ∧
      a < wuv.length + j ∧ b < wuv.length + j ∧
      (((gs.foldl step wu).getD a false = true ∧ (gs.foldl step wv).getD a false = false ∧
        (gs.foldl step wv).getD b false = true ∧ (gs.foldl step wu).getD b false = false) ∨
       ((gs.foldl step wv).getD a false = true ∧ (gs.foldl step wu).getD a false = false ∧
        (gs.foldl step wu).getD b false = true ∧ (gs.foldl step wv).getD b false = false)) := by
  induction gs with
  | nil =>
    intro wu wv wuv _ _ hgood hbad
    obtain ⟨i, hi⟩ := hbad
    exact (hgood i hi).elim
  | cons g gs ih =>
    intro wu wv wuv hu hv hgood hbad
    have hg := hgs g (List.mem_cons_self ..)
    have hgs' : ∀ g' ∈ gs, AndOr g' := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    by_cases hnew : Bad (step wu g) (step wv g) (step wuv g) wuv.length
    · have hlu : wu.length = wuv.length := hu.1
      have hlv : wv.length = wuv.length := hv.1
      simp only [Bad, step, getD_snoc, hlu, hlv, lt_irrefl, ite_false, ite_true] at hnew
      obtain ⟨a, b, hop, hin, ha, hb, hpat⟩ :=
        new_gate g hg wu wv wuv hu hv hgood hnew.1 hnew.2.1 hnew.2.2
      refine ⟨0, g, a, b, rfl, hop, hin, by omega, by omega, ?_⟩
      simp only [List.foldl_cons]
      rw [fold_getD gs _ a (by simp [step]; omega), fold_getD gs _ b (by simp [step]; omega),
        fold_getD gs _ a (by simp [step]; omega), fold_getD gs _ b (by simp [step]; omega)]
      simp only [step, getD_snoc, hlu, hlv, ha, hb, ite_true]
      exact hpat
    · have hgood' : ∀ i, ¬ Bad (step wu g) (step wv g) (step wuv g) i := by
        intro i hi
        have hlu : wu.length = wuv.length := hu.1
        have hlv : wv.length = wuv.length := hv.1
        simp only [Bad, step, getD_snoc, hlu, hlv] at hi
        split_ifs at hi with h1 h2
        · exact hgood i hi
        · subst h2
          apply hnew
          simp only [Bad, step, getD_snoc, hlu, hlv, lt_irrefl, ite_false, ite_true]
          exact hi
        · simp at hi
      obtain ⟨j, g', a, b, hj, hop, hin, ha, hb, hpat⟩ :=
        ih hgs' (step wu g) (step wv g) (step wuv g) (le_step g hg _ _ hu) (le_step g hg _ _ hv)
          hgood' hbad
      refine ⟨j + 1, g', a, b, by simpa using hj, hop, hin, ?_, ?_, hpat⟩
      · simp [step] at ha; omega
      · simp [step] at hb; omega

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem le_ofFn {n : ℕ} (p q : Fin n → Bool) (h : ∀ i, p i = true → q i = true) :
    Le (List.ofFn p) (List.ofFn q) := by
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getD_ofFn] at hi ⊢
  by_cases hi' : i < n
  · rw [dif_pos hi'] at hi ⊢
    exact h _ hi
  · rw [dif_neg hi'] at hi
    exact absurd hi Bool.false_ne_true

end PEqualNP.Outside.Meta201

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.Meta201

theorem L_meta_201 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∀ u v : Fin n, G.Adj u v → ∃ j : ℕ, (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧ (((C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = false) ∨ ((C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = false))) := by
  intro n G _ C hfan hnot hf u v huv
  have hand : ∀ g ∈ C.gates, AndOr g := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hnot g hg)
  have huv' : u ≠ v := G.ne_of_adj huv
  have hw : ∀ x : Fin n → Bool, C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) :=
    fun _ => rfl
  have hval := fun x => congrFun hf x
  simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval] at hval
  have eu := hval (fun i => decide (i = u))
  have ev := hval (fun i => decide (i = v))
  have euv := hval (fun i => decide (i = u ∨ i = v))
  have nou : ¬ ∃ i j : Fin n, G.Adj i j ∧ decide (i = u) = true ∧ decide (j = u) = true := by
    rintro ⟨i, j, hij, hi, hj⟩
    simp at hi hj
    subst hi hj
    exact G.irrefl hij
  have nov : ¬ ∃ i j : Fin n, G.Adj i j ∧ decide (i = v) = true ∧ decide (j = v) = true := by
    rintro ⟨i, j, hij, hi, hj⟩
    simp at hi hj
    subst hi hj
    exact G.irrefl hij
  have yuv : ∃ i j : Fin n, G.Adj i j ∧ decide (i = u ∨ i = v) = true ∧
      decide (j = u ∨ j = v) = true := ⟨u, v, huv, by simp, by simp⟩
  rw [decide_eq_false nou] at eu
  rw [decide_eq_false nov] at ev
  rw [decide_eq_true yuv] at euv
  rw [hw] at eu ev euv ⊢
  have hlen : (List.ofFn (fun i : Fin n => decide (i = u ∨ i = v))).length = n := by simp
  have key := main C.gates hand (List.ofFn (fun i : Fin n => decide (i = u)))
    (List.ofFn (fun i : Fin n => decide (i = v)))
    (List.ofFn (fun i : Fin n => decide (i = u ∨ i = v)))
    (le_ofFn _ _ (fun i hi => by
      rw [decide_eq_true_iff] at hi ⊢
      exact Or.inl hi))
    (le_ofFn _ _ (fun i hi => by
      rw [decide_eq_true_iff] at hi ⊢
      exact Or.inr hi))
    (fun i hi => by
      simp only [Bad, getD_ofFn] at hi
      split_ifs at hi with h
      · simp at hi
        obtain ⟨h1, h2, h3⟩ := hi
        rcases h3 with h3 | h3
        · exact h1 h3
        · exact h2 h3
      · simp at hi)
    ⟨C.output, eu, ev, euv⟩
  rw [hlen] at key
  exact key

end PEqualNP.Outside
