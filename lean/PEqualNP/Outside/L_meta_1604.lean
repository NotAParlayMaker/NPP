import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1604

open PEqualNP.CircuitLowerBounds

-- One evaluation step of the wire list.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc (x : List Bool) (a : Bool) (i : ℕ) :
    (x ++ [a]).getD i false =
      if i < x.length then x.getD i false else if i = x.length then a else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

lemma foldl_length (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl step x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    have hi' : i < (step x g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.foldl_cons, ih _ hi']
    simp only [step]
    rw [getD_snoc, if_pos hi]

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (x y : List Bool) (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    op.eval (ins.map fun i => x.getD i false) = true →
      op.eval (ins.map fun i => y.getD i false) = true := by
  rcases hop with rfl | rfl
  · intro hx
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
    rintro b ⟨i, hi, rfl⟩
    exact h i (hx _ ⟨i, hi, rfl⟩)
  · intro hx
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
    obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hx
    exact ⟨_, ⟨i, hi, rfl⟩, h i hb⟩

lemma foldl_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (gs.foldl step x).getD i false = true → (gs.foldl step y).getD i false = true := by
  induction gs generalizing x y with
  | nil => simpa using h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp only [step, List.length_append, List.length_cons, List.length_nil, hl]
    · intro i
      have hg := eval_mono g.op (hgs g List.mem_cons_self) g.inputs x y h
      simp only [step]
      rw [getD_snoc, getD_snoc, ← hl]
      split_ifs
      · exact h i
      · exact hg
      · exact id

lemma gate_val_aux (pre post : List Gate) (g : Gate) (x : List Bool)
    (hin : ∀ i ∈ g.inputs, i < x.length + pre.length) :
    ((pre ++ g :: post).foldl step x).getD (x.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => ((pre ++ g :: post).foldl step x).getD i false) := by
  have hP : (pre.foldl step x).length = x.length + pre.length := foldl_length _ _
  rw [List.foldl_append, List.foldl_cons]
  have key : ∀ i, i < x.length + pre.length + 1 →
      (post.foldl step (step (pre.foldl step x) g)).getD i false =
        (step (pre.foldl step x) g).getD i false := by
    intro i hi
    apply foldl_getD_lt
    simp only [step, List.length_append, List.length_cons, List.length_nil, hP]
    exact hi
  have hmap : (g.inputs.map fun i => (post.foldl step (step (pre.foldl step x) g)).getD i false)
      = g.inputs.map fun i => (pre.foldl step x).getD i false := by
    apply List.map_congr_left
    intro i hi
    have hi2 := hin i hi
    have hi' : i < (pre.foldl step x).length := by rw [hP]; exact hi2
    rw [key i (by omega)]
    simp only [step]
    rw [getD_snoc, if_pos hi']
  rw [hmap, key (x.length + pre.length) (by omega)]
  have h1 : ¬ (x.length + pre.length < (pre.foldl step x).length) := by omega
  have h2 : x.length + pre.length = (pre.foldl step x).length := hP.symm
  simp only [step]
  rw [getD_snoc, if_neg h1, if_pos h2]

lemma and_val (pre post : List Gate) (g : Gate) (x : List Bool) (k j : ℕ)
    (hop : g.op = GateOp.and) (hin : g.inputs = [k, j])
    (hk : k < x.length + pre.length) (hj : j < x.length + pre.length) :
    ((pre ++ g :: post).foldl step x).getD (x.length + pre.length) false =
      (((pre ++ g :: post).foldl step x).getD k false &&
        ((pre ++ g :: post).foldl step x).getD j false) := by
  have hin' : ∀ i ∈ g.inputs, i < x.length + pre.length := by
    intro i hi
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  rw [gate_val_aux pre post g x hin', hop, hin]
  simp [GateOp.eval]

lemma gateVal_and (n : ℕ) (C : Circuit) (h k j : ℕ) (hh : h < C.gates.length)
    (hop : (C.gates[h]).op = GateOp.and) (hin : (C.gates[h]).inputs = [k, j])
    (hk : k < n + h) (hj : j < n + h) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C h x =
      (PEqualNP.CleanedNonEdge.wireVal n C k x && PEqualNP.CleanedNonEdge.wireVal n C j x) := by
  unfold PEqualNP.EdgeOwnership.gateVal PEqualNP.CleanedNonEdge.wireVal
  have hw : C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
  rw [hw]
  have e : C.gates.take h ++ C.gates[h] :: C.gates.drop (h + 1) = C.gates := by
    rw [← List.drop_eq_getElem_cons hh, List.take_append_drop]
  have hlen : (List.ofFn x).length + (C.gates.take h).length = n + h := by
    rw [List.length_ofFn, List.length_take]
    omega
  have hthis := and_val (C.gates.take h) (C.gates.drop (h + 1)) C.gates[h] (List.ofFn x) k j
    hop hin (by rw [hlen]; exact hk) (by rw [hlen]; exact hj)
  rw [e, hlen] at hthis
  exact hthis

lemma wireVal_mono (n : ℕ) (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    PEqualNP.CleanedNonEdge.wireVal n C w x = true →
      PEqualNP.CleanedNonEdge.wireVal n C w y = true := by
  unfold PEqualNP.CleanedNonEdge.wireVal
  have hw : ∀ z, C.wires z = C.gates.foldl step z := fun _ => rfl
  rw [hw, hw]
  apply foldl_mono C.gates hC _ _ (by simp)
  intro i
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi] using hxy ⟨i, hi⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]

end PEqualNP.Outside.L_meta_1604

theorem PEqualNP.Outside.L_meta_1604 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.EdgeOwnership.AndOrOnly C → ∀ h k j : ℕ, h < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C h).inputs = [k, j] → k < n + h → j < n + h → (∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C h x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) → ∀ v w : Fin n, G.Adj v w → PEqualNP.CleanedNonEdge.wireVal n C k (PEqualNP.EdgeOwnership.pairInput v v) = true → PEqualNP.CleanedNonEdge.wireVal n C k (PEqualNP.EdgeOwnership.pairInput w w) = true → ∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C j (PEqualNP.EdgeOwnership.pairInput y y) = false := by
  intro n G _ htri C hC h k j hh hop hin hk hj hclean v w hvw hkv hkw y
  have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C h = C.gates[h] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    simp [List.getD_eq_getElem?_getD, hh]
  rw [hgate] at hop hin
  by_contra hne
  have hjy : PEqualNP.CleanedNonEdge.wireVal n C j (PEqualNP.EdgeOwnership.pairInput y y)
      = true := by simpa using hne
  have key : ∀ u : Fin n,
      PEqualNP.CleanedNonEdge.wireVal n C k (PEqualNP.EdgeOwnership.pairInput u u) = true →
        G.Adj u y := by
    intro u hu
    have hku : PEqualNP.CleanedNonEdge.wireVal n C k (PEqualNP.EdgeOwnership.pairInput u y)
        = true := by
      refine PEqualNP.Outside.L_meta_1604.wireVal_mono n C hC _ _ ?_ k hu
      intro i hi
      simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi ⊢
      tauto
    have hju : PEqualNP.CleanedNonEdge.wireVal n C j (PEqualNP.EdgeOwnership.pairInput u y)
        = true := by
      refine PEqualNP.Outside.L_meta_1604.wireVal_mono n C hC _ _ ?_ j hjy
      intro i hi
      simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi ⊢
      tauto
    have hg : PEqualNP.EdgeOwnership.gateVal n C h (PEqualNP.EdgeOwnership.pairInput u y)
        = true := by
      simp [PEqualNP.Outside.L_meta_1604.gateVal_and n C h k j hh hop hin hk hj, hku, hju]
    have hf := hclean _ hg
    have hf2 : ∃ a b, G.Adj a b ∧ (a = u ∨ a = y) ∧ (b = u ∨ b = y) := by
      simpa [PEqualNP.MetaComplexity.NestedCover.graphFun, PEqualNP.EdgeOwnership.pairInput]
        using hf
    obtain ⟨a, b, hab, ha, hb⟩ := hf2
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab.ne
    · exact hab
    · exact hab.symm
    · exact absurd rfl hab.ne
  have h1 := key v hkv
  have h2 := key w hkw
  exact htri v w y hvw h2 h1.symm
