import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1604

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def rn (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma rn_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    rn (g :: gs) x = rn gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma rn_length (gs : List Gate) (x : List Bool) :
    (rn gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [rn]
  | cons g gs ih => rw [rn_cons, ih]; simp; omega

lemma rn_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (rn gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [rn_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma rn_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    rn gs x = rn (gs.drop j) (rn (gs.take j) x) := by
  simpa only [rn, List.foldl_append] using
    congrArg (fun l : List Gate => rn l x) (List.take_append_drop j gs).symm

def vl {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma vl_missing {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : vl C x w = false := by
  change (rn C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [rn_length] using hw)

lemma vl_gate0 {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.gates.length) :
    let g := C.gates[w - n]'(by omega)
    vl C x w = g.op.eval (g.inputs.map fun r => if r < w then vl C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j; omega
  let g := C.gates[j]
  let earlier := rn (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, rn_length, Nat.min_eq_left hj.le, j]; omega
  have split : rn C.gates (List.ofFn x) = rn (g :: C.gates.drop (j + 1)) earlier := by
    rw [rn_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then vl C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (rn C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (rn_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (rn C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then vl C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [rn_cons]
  rw [rn_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma vl_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    vl C x w = x ⟨w, hw⟩ := by
  change (rn C.gates (List.ofFn x)).getD w false = x ⟨w, hw⟩
  have hp : w < (List.ofFn x).length := by simpa using hw
  rw [rn_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

lemma vl_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    vl C x (n + j) = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun r => if r < n + j then vl C x r else false) := by
  have h := vl_gate0 C x (n + j) (by omega) (by omega)
  rw [gateAt_eq C j hj]
  simpa only [Nat.add_sub_cancel_left] using h

lemma vl_and {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    vl C x (n + j) = true ↔ ∀ r ∈ (gateAt C j).inputs, r < n + j ∧ vl C x r = true := by
  rw [vl_gate C x j hj, hop]
  simp only [GateOp.eval, List.all_eq_true, id_eq]
  constructor
  · intro h r hr
    have h1 := h _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
    by_cases hlt : r < n + j
    · rw [if_pos hlt] at h1
      exact ⟨hlt, h1⟩
    · rw [if_neg hlt] at h1
      exact Bool.noConfusion h1
  · intro h b hb
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    obtain ⟨h1, h2⟩ := h r hr
    rw [if_pos h1]
    exact h2

lemma vl_or {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    vl C x (n + j) = true ↔ ∃ r ∈ (gateAt C j).inputs, r < n + j ∧ vl C x r = true := by
  rw [vl_gate C x j hj, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq]
  constructor
  · rintro ⟨b, hb, hv⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    by_cases hlt : r < n + j
    · rw [if_pos hlt] at hv
      exact ⟨r, hr, hlt, hv⟩
    · rw [if_neg hlt] at hv
      exact Bool.noConfusion hv
  · rintro ⟨r, hr, h1, h2⟩
    refine ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    rw [if_pos h1]
    exact h2

lemma gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]
  exact List.getElem_mem hj


lemma mono {n : ℕ} (C : Circuit) (hAO : AndOrOnly C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, vl C x w = true → vl C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro ht
    by_cases hn : w < n
    · rw [vl_input C _ w hn] at ht ⊢
      exact hxy _ ht
    by_cases hw : n + C.gates.length ≤ w
    · rw [vl_missing C _ w hw] at ht
      exact Bool.noConfusion ht
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases hAO _ (gate_mem C k hk) with hop | hop
    · rw [vl_and C _ k hk hop] at ht ⊢
      intro r hr
      obtain ⟨h1, h2⟩ := ht r hr
      exact ⟨h1, ih r h1 h2⟩
    · rw [vl_or C _ k hk hop] at ht ⊢
      obtain ⟨r, hr, h1, h2⟩ := ht
      exact ⟨r, hr, h1, ih r h1 h2⟩

lemma adj_of {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a b : Fin n)
    (h : graphFun G ∅ (pairInput a b) = true) : G.Adj a b := by
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨p, q, hpq, hp, hq⟩
  · simp at h
  · simp only [pairInput, decide_eq_true_eq] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd hpq (G.irrefl)
    · exact hpq
    · exact hpq.symm
    · exact absurd hpq (G.irrefl)

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (C : Circuit) (hAO : AndOrOnly C) (h k j : ℕ) (hh : h < C.gates.length)
    (hop : (gateAt C h).op = GateOp.and) (hin : (gateAt C h).inputs = [k, j])
    (hk : k < n + h) (hj : j < n + h)
    (hsub : ∀ x : Fin n → Bool, gateVal n C h x = true → graphFun G ∅ x = true)
    (v w : Fin n) (hvw : G.Adj v w)
    (hkv : vl C (pairInput v v) k = true) (hkw : vl C (pairInput w w) k = true)
    (y : Fin n) : vl C (pairInput y y) j = false := by
  by_contra hne
  have hjy : vl C (pairInput y y) j = true := by
    cases hc : vl C (pairInput y y) j
    · exact absurd hc hne
    · rfl
  have key : ∀ u : Fin n, vl C (pairInput u u) k = true → G.Adj y u := by
    intro u hku
    apply adj_of
    apply hsub
    show vl C (pairInput y u) (n + h) = true
    rw [vl_and C _ h hh hop, hin]
    intro r hr
    have hr' : r = k ∨ r = j := by simpa using hr
    rcases hr' with rfl | rfl
    · refine ⟨hk, mono C hAO _ _ ?_ _ hku⟩
      intro i hi
      simp only [pairInput, decide_eq_true_eq] at hi ⊢
      rcases hi with hi | hi <;> exact Or.inr hi
    · refine ⟨hj, mono C hAO _ _ ?_ _ hjy⟩
      intro i hi
      simp only [pairInput, decide_eq_true_eq] at hi ⊢
      rcases hi with hi | hi <;> exact Or.inl hi
  exact htri y v w (key v hkv) hvw (key w hkw).symm

end PEqualNP.Outside.L_meta_1604

theorem PEqualNP.Outside.L_meta_1604 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.EdgeOwnership.AndOrOnly C → ∀ h k j : ℕ, h < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C h).inputs = [k, j] → k < n + h → j < n + h → (∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C h x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) → ∀ v w : Fin n, G.Adj v w → PEqualNP.CleanedNonEdge.wireVal n C k (PEqualNP.EdgeOwnership.pairInput v v) = true → PEqualNP.CleanedNonEdge.wireVal n C k (PEqualNP.EdgeOwnership.pairInput w w) = true → ∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C j (PEqualNP.EdgeOwnership.pairInput y y) = false := by
  intro n G _ htri C hAO h k j hh hop hin hk hj hsub v w hvw hkv hkw y
  exact PEqualNP.Outside.L_meta_1604.main n G htri C hAO h k j hh hop hin hk hj hsub v w hvw hkv hkw y
