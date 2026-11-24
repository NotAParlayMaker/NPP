import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_2792_aux

-- Adapted wire evaluation and monotonicity lemmas from L-meta-2053.
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

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h


private theorem absent {α : Type} (a b : ℕ) (P : ℕ → α → Prop)
    (h : ¬ ∀ w ∈ [a, b], ∃ x, ¬ P w x) :
    (∀ x, P a x) ∨ (∀ x, P b x) := by
  classical
  by_cases ha : ∀ x, P a x
  · exact Or.inl ha
  right
  by_contra hb
  apply h
  intro w hw
  simp at hw
  rcases hw with rfl | rfl
  · exact not_forall.mp ha
  · exact not_forall.mp hb

private theorem constant_of_products {α : Type} (z : α) (S : Set (α × α))
    (hl : ∃ A, S = A ×ˢ Set.univ) (hr : ∃ B, S = Set.univ ×ˢ B) :
    S = ∅ ∨ S = Set.univ := by
  obtain ⟨A, hA⟩ := hl
  obtain ⟨B, hB⟩ := hr
  have equal (p q : α) : (p, q) ∈ S ↔ (z, z) ∈ S := by
    calc
      (p, q) ∈ S ↔ (p, z) ∈ S := by simp [hA]
      _ ↔ (z, z) ∈ S := by simp [hB]
  by_cases h : (z, z) ∈ S
  · right
    ext ⟨p,q⟩
    simp [(equal p q).2 h]
  · left
    ext ⟨p,q⟩
    simp [mt (equal p q).1 h]

end PEqualNP.Outside.L_meta_2792_aux

open PEqualNP.Outside.L_meta_2792_aux in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.L_meta_2792 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5]? = Option.some x6 → ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x1 + x5) →       (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ∉ x3 → ¬((∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.false)).getD x11 Bool.false ≠ (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.true)).getD x11 Bool.false) ∨ ∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x13)).getD x11 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x13)).getD x11 Bool.false)) →         ∃ (x7 : ℕ → Set ((Fin x1 → Bool) × (Fin x1 → Bool))),           (∀ (x8 : Fin x1), x7 ↑x8 = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.1 x8 = Bool.true} ∧ x7 (x1 + ↑x8) = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.2 x8 = Bool.true}) ∧             (∀ x8 < x2.size,                 ∃ x10 < x1 + x1 + x8,                   ∃ x11 < x1 + x1 + x8,                     have x12 : Set ((Fin x1 → Bool) × (Fin x1 → Bool)) := x7 (x1 + x1 + x8);                     x12 = x7 x10 ∪ x7 x11 ∨ x12 = x7 x10 ∨ x12 = ∅ ∨ x12 = x7 x10 ∩ x7 x11 ∧ (x8 ∈ x3 ∨ ∃ (x13 : Set (Fin x1 → Bool)) (x14 : Set (Fin x1 → Bool)), x7 x10 = x13 ×ˢ Set.univ ∧ x7 x11 = Set.univ ×ˢ x14)) ∧               ∀ (x8 x9 : Fin x1 → Bool), (x8, x9) ∈ x7 x2.output ↔ PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 (Fin.append x8 x9) = Bool.true := by
  classical
  intro N C marked hmono hshape hmark
  let value (w : ℕ) (p l : Fin N → Bool) := val C.gates w (Fin.append p l)
  let V (w : ℕ) : Set ((Fin N → Bool) × (Fin N → Bool)) := {z | value w z.1 z.2 = true}
  let zero : Fin N → Bool := fun _ => false
  let one : Fin N → Bool := fun _ => true
  have vm (i : ℕ) (p p' l l' : Fin N → Bool)
      (hp : ∀ j, p j = true → p' j = true) (hl : ∀ j, l j = true → l' j = true) :
      value i p l = true → value i p' l' = true := by
    apply val_mono C.gates (legal_of C hmono)
    intro j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa using hp k
    · simpa only [Fin.append_right] using hl k
  have wire (i : ℕ) (p l : Fin N → Bool) :
      value i p l = (C.wires (List.ofFn p ++ List.ofFn l)).getD i false := by
    change (C.wires (List.ofFn (Fin.append p l))).getD i false = _
    rw [List.ofFn_fin_append]
  have leftForm (i : ℕ) (h : ∀ p, value i p zero = value i p one) :
      ∃ A, V i = A ×ˢ Set.univ := by
    refine ⟨{p | value i p zero = true}, ?_⟩
    ext ⟨p,l⟩
    change (value i p l = true ↔ _)
    simp only [Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true]
    constructor
    · intro hv
      rw [h p]
      exact vm i p p l one (fun _ k => k) (fun _ _ => rfl) hv
    · exact vm i p p zero l (fun _ k => k) (fun _ k => Bool.noConfusion k)
  have rightForm (i : ℕ) (h : ∀ l, value i zero l = value i one l) :
      ∃ B, V i = Set.univ ×ˢ B := by
    refine ⟨{l | value i zero l = true}, ?_⟩
    ext ⟨p,l⟩
    change (value i p l = true ↔ _)
    simp only [Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, true_and]
    constructor
    · intro hv
      rw [h l]
      exact vm i p one l l (fun _ _ => rfl) (fun _ k => k) hv
    · exact vm i zero p l l (fun _ k => Bool.noConfusion k) (fun _ k => k)
  refine ⟨V, ?_, ?_, fun p l => Iff.rfl⟩
  · intro i
    constructor <;> ext ⟨p,l⟩
    · change value i.val p l = true ↔ p i = true
      change val C.gates i.val (Fin.append p l) = true ↔ _
      rw [val_input _ _ _ (by omega)]
      change (Fin.append p l (Fin.castAdd N i) = true) ↔ _
      rw [Fin.append_left]
    · change value (N + i.val) p l = true ↔ l i = true
      change val C.gates (N + i.val) (Fin.append p l) = true ↔ _
      rw [val_input _ _ _ (by omega)]
      change (Fin.append p l (Fin.natAdd N i) = true) ↔ _
      rw [Fin.append_right]
  · intro j hj
    have hj' : j < C.gates.length := hj
    let g := C.gates[j]
    have hg : C.gates[j]? = some g := by simp [g, hj']
    obtain ⟨a,b,hab,hlt,hbound⟩ := hshape j g hg
    have ha : a < N + N + j := lt_trans hlt hbound
    have eqGate (p l : Fin N → Bool) :
        value (N + N + j) p l = g.op.eval [value a p l, value b p l] := by
      have he : ∀ i < N + N + j,
          (wf (C.gates.take j) (List.ofFn (Fin.append p l))).getD i false =
            value i p l := by
        intro i hi
        exact (wire_take C.gates _ j i (by simpa using hi) (by omega)).symm
      change val C.gates (N + N + j) (Fin.append p l) = _
      unfold val
      have h := gate_val C.gates (List.ofFn (Fin.append p l)) j hj'
      rw [List.length_ofFn] at h
      change (wf C.gates _).getD _ false =
        g.op.eval (g.inputs.map fun i => (wf (C.gates.take j) (List.ofFn (Fin.append p l))).getD i false) at h
      rw [h, hab, List.map_cons, List.map_cons, List.map_nil, he a ha, he b hbound]
    rcases (legal_of C hmono g (List.getElem_mem hj')).1 with hop | hop
    · have eqAnd : V (N + N + j) = V a ∩ V b := by
        ext ⟨p,l⟩
        change (value (N + N + j) p l = true) ↔ (value a p l = true ∧ value b p l = true)
        rw [eqGate, hop]
        simp [GateOp.eval]
      by_cases hm : j ∈ marked
      · exact ⟨a,ha,b,hbound,Or.inr (Or.inr (Or.inr ⟨eqAnd, Or.inl hm⟩))⟩
      have hh := hmark j g hg hop hm
      rw [hab] at hh
      have hl : (∃ A, V a = A ×ˢ Set.univ) ∨ (∃ A, V b = A ×ˢ Set.univ) := by
        rcases absent a b (fun w p => value w p zero = value w p one) (fun h => hh (Or.inl
          (by simpa only [wire, zero, one, List.ofFn_const] using h))) with h | h
        · exact Or.inl (leftForm a h)
        · exact Or.inr (leftForm b h)
      have hr : (∃ B, V a = Set.univ ×ˢ B) ∨ (∃ B, V b = Set.univ ×ˢ B) := by
        rcases absent a b (fun w l => value w zero l = value w one l) (fun h => hh (Or.inr
          (by simpa only [wire, zero, one, List.ofFn_const] using h))) with h | h
        · exact Or.inl (rightForm a h)
        · exact Or.inr (rightForm b h)
      rcases hl with hla | hlb <;> rcases hr with hra | hrb
      · rcases constant_of_products zero _ hla hra with e | e
        · exact ⟨a,ha,b,hbound,Or.inr (Or.inr (Or.inl (by simp [eqAnd,e])))⟩
        · exact ⟨b,hbound,a,ha,Or.inr (Or.inl (by simp [eqAnd,e]))⟩
      · obtain ⟨A,hA⟩ := hla
        obtain ⟨B,hB⟩ := hrb
        exact ⟨a,ha,b,hbound,Or.inr (Or.inr (Or.inr ⟨eqAnd,Or.inr ⟨A,B,hA,hB⟩⟩))⟩
      · obtain ⟨A,hA⟩ := hlb
        obtain ⟨B,hB⟩ := hra
        exact ⟨b,hbound,a,ha,Or.inr (Or.inr (Or.inr ⟨eqAnd.trans (Set.inter_comm _ _),Or.inr ⟨A,B,hA,hB⟩⟩))⟩
      · rcases constant_of_products zero _ hlb hrb with e | e
        · exact ⟨a,ha,b,hbound,Or.inr (Or.inr (Or.inl (by simp [eqAnd,e])))⟩
        · exact ⟨a,ha,b,hbound,Or.inr (Or.inl (by simp [eqAnd,e]))⟩
    · refine ⟨a,ha,b,hbound,Or.inl ?_⟩
      ext ⟨p,l⟩
      change (value (N + N + j) p l = true) ↔ (value a p l = true ∨ value b p l = true)
      rw [eqGate, hop]
      simp [GateOp.eval]
