import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2868

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun wr g => wr ++ [g.op.eval (g.inputs.map fun i => wr.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have h := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at h ⊢
    rw [h]
    simp
    omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have h := ih (w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at h ⊢
    rw [h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have h : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [h]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false =
      gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have hlen : (wf (gates.take k) X).length = X.length + k := by
    rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hlen]
  simp [List.getD_eq_getElem?_getD]

def inpBool {N : ℕ} (p l : Fin N → Bool) : Fin (N + N) → Bool :=
  Fin.addCases p l

theorem ofFn_inpBool (N : ℕ) (p l : Fin N → Bool) :
    List.ofFn (inpBool p l) = List.ofFn p ++ List.ofFn l :=
  List.ofFn_fin_append p l

def val (N : ℕ) (C : Circuit) (w : ℕ) (p l : Fin N → Bool) : Bool :=
  (wf C.gates (List.ofFn p ++ List.ofFn l)).getD w false

theorem eval_val (N : ℕ) (C : Circuit) (p l : Fin N → Bool) :
    C.eval (List.ofFn p ++ List.ofFn l) = val N C C.output p l := rfl

theorem val_gate_and (N : ℕ) (C : Circuit) (k : Fin C.gates.length)
    (a b : ℕ) (ha : a < N + N + k.val) (hb : b < N + N + k.val)
    (hin : C.gates[k.val].inputs = [a, b]) (hop : C.gates[k.val].op = GateOp.and)
    (p l : Fin N → Bool) :
    val N C (N + N + k.val) p l = (val N C a p l && val N C b p l) := by
  unfold val
  have hlen : (List.ofFn p ++ List.ofFn l).length = N + N := by simp
  rw [← hlen, gate_val C.gates (List.ofFn p ++ List.ofFn l) k.val k.isLt]
  rw [hop, hin]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
  rw [wire_take C.gates _ k.val a (by omega) (Nat.le_of_lt k.isLt)]
  rw [wire_take C.gates _ k.val b (by omega) (Nat.le_of_lt k.isLt)]

theorem val_gate_or (N : ℕ) (C : Circuit) (k : Fin C.gates.length)
    (a b : ℕ) (ha : a < N + N + k.val) (hb : b < N + N + k.val)
    (hin : C.gates[k.val].inputs = [a, b]) (hop : C.gates[k.val].op = GateOp.or)
    (p l : Fin N → Bool) :
    val N C (N + N + k.val) p l = (val N C a p l || val N C b p l) := by
  unfold val
  have hlen : (List.ofFn p ++ List.ofFn l).length = N + N := by simp
  rw [← hlen, gate_val C.gates (List.ofFn p ++ List.ofFn l) k.val k.isLt]
  rw [hop, hin]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
  rw [wire_take C.gates _ k.val a (by omega) (Nat.le_of_lt k.isLt)]
  rw [wire_take C.gates _ k.val b (by omega) (Nat.le_of_lt k.isLt)]

theorem val_big (N : ℕ) (C : Circuit) (w : ℕ) (hw : N + N + C.gates.length ≤ w)
    (p l : Fin N → Bool) : val N C w p l = false := by
  unfold val
  apply List.getD_eq_default
  rw [wf_len]
  simp
  omega

theorem val_input_left (N : ℕ) (C : Circuit) (u : Fin N) (p l : Fin N → Bool) :
    val N C u.val p l = p u := by
  unfold val
  rw [wf_keep _ _ u.val (by simp; omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
  simp

theorem val_input_right (N : ℕ) (C : Circuit) (v : Fin N) (p l : Fin N → Bool) :
    val N C (N + v.val) p l = l v := by
  unfold val
  rw [wf_keep _ _ (N + v.val) (by simp)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_ofFn, Nat.add_sub_cancel_left]
  simp

theorem val_mono (N : ℕ) (C : Circuit)
    (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (p p' l l' : Fin N → Bool)
    (hp : ∀ u, p u = true → p' u = true)
    (hl : ∀ v, l v = true → l' v = true) :
    ∀ w : ℕ, val N C w p l = true → val N C w p' l' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwN : w < N
    · rw [val_input_left N C ⟨w, hwN⟩] at hw ⊢
      exact hp ⟨w, hwN⟩ hw
    · by_cases hw2N : w < N + N
      · have hwe : w = N + (w - N) := by omega
        have hvlt : w - N < N := by omega
        rw [hwe] at hw ⊢
        rw [val_input_right N C ⟨w - N, hvlt⟩] at hw ⊢
        exact hl ⟨w - N, hvlt⟩ hw
      · by_cases hwbig : N + N + C.gates.length ≤ w
        · rw [val_big N C w hwbig] at hw
          exact Bool.noConfusion hw
        · have hklt : w - (N + N) < C.gates.length := by omega
          let k : Fin C.gates.length := ⟨w - (N + N), hklt⟩
          have hweq : N + N + k.val = w := by simp [k]; omega
          obtain ⟨a, b, hin, hab, hblt⟩ := hord k.val C.gates[k.val] (List.getElem?_eq_getElem k.isLt)
          have hmem : C.gates[k.val] ∈ C.gates := List.getElem_mem k.isLt
          rcases (hm C.gates[k.val] hmem).1 with hop | hop
          · rw [← hweq, val_gate_and N C k a b (by omega) hblt hin hop] at hw ⊢
            simp only [Bool.and_eq_true] at hw ⊢
            exact ⟨ih a (by omega) hw.1, ih b (by omega) hw.2⟩
          · rw [← hweq, val_gate_or N C k a b (by omega) hblt hin hop] at hw ⊢
            simp only [Bool.or_eq_true] at hw ⊢
            rcases hw with ha | hb
            · exact Or.inl (ih a (by omega) ha)
            · exact Or.inr (ih b (by omega) hb)

def ePt {N : ℕ} (p0 : Fin N) (u : Fin N) : Bool := decide (u = p0)
def zFn {N : ℕ} (_ : Fin N) : Bool := false
def oFn {N : ℕ} (_ : Fin N) : Bool := true

def DepL (N : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∃ p : Fin N → Bool, val N C w p zFn ≠ val N C w p oFn

def DepP (N : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∃ l : Fin N → Bool, val N C w zFn l ≠ val N C w oFn l

theorem no_DepL_eq (N : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (w : ℕ) (hnd : ¬ DepL N C w) (p l : Fin N → Bool) :
    val N C w p l = val N C w p zFn := by
  have heq : val N C w p zFn = val N C w p oFn := by
    by_contra hne
    exact hnd ⟨p, hne⟩
  cases h0 : val N C w p zFn with
  | false =>
    cases h1 : val N C w p l with
    | false => rfl
    | true =>
      have h2 := val_mono N C hm hord p p l oFn (fun _ h => h) (fun _ _ => rfl) w h1
      rw [← heq, h0] at h2
      exact Bool.noConfusion h2
  | true =>
    exact val_mono N C hm hord p p zFn l (fun _ h => h) (fun _ h => Bool.noConfusion h) w h0

theorem no_DepP_eq (N : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (w : ℕ) (hnd : ¬ DepP N C w) (p l : Fin N → Bool) :
    val N C w p l = val N C w zFn l := by
  have heq : val N C w zFn l = val N C w oFn l := by
    by_contra hne
    exact hnd ⟨l, hne⟩
  cases h0 : val N C w zFn l with
  | false =>
    cases h1 : val N C w p l with
    | false => rfl
    | true =>
      have h2 := val_mono N C hm hord p oFn l l (fun _ _ => rfl) (fun _ h => h) w h1
      rw [← heq, h0] at h2
      exact Bool.noConfusion h2
  | true =>
    exact val_mono N C hm hord zFn p l l (fun _ h => Bool.noConfusion h) (fun _ h => h) w h0

theorem no_DepLP_const (N : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (w : ℕ) (hnL : ¬ DepL N C w) (hnP : ¬ DepP N C w) (p l : Fin N → Bool) :
    val N C w p l = val N C w zFn zFn := by
  rw [no_DepL_eq N C hm hord w hnL p l, no_DepP_eq N C hm hord w hnP p zFn]

theorem depL_iff_wire (N : ℕ) (C : Circuit) (w : ℕ) :
    DepL N C w ↔ ∃ x : Fin N → Bool,
      (C.wires (List.ofFn x ++ List.replicate N false)).getD w false ≠
      (C.wires (List.ofFn x ++ List.replicate N true)).getD w false := by
  have hf : List.ofFn (zFn (N := N)) = List.replicate N false := List.ofFn_const N false
  have ht : List.ofFn (oFn (N := N)) = List.replicate N true := List.ofFn_const N true
  simp only [DepL, val, wf, Circuit.wires, hf, ht]

theorem depP_iff_wire (N : ℕ) (C : Circuit) (w : ℕ) :
    DepP N C w ↔ ∃ x : Fin N → Bool,
      (C.wires (List.replicate N false ++ List.ofFn x)).getD w false ≠
      (C.wires (List.replicate N true ++ List.ofFn x)).getD w false := by
  have hf : List.ofFn (zFn (N := N)) = List.replicate N false := List.ofFn_const N false
  have ht : List.ofFn (oFn (N := N)) = List.replicate N true := List.ofFn_const N true
  simp only [DepP, val, wf, Circuit.wires, hf, ht]

noncomputable def Pset (N : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun p => val N C w (ePt p) zFn = true

noncomputable def Lset (N : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun l => val N C w zFn (ePt l) = true

theorem mem_Pset (N : ℕ) (C : Circuit) (w : ℕ) (p : Fin N) :
    p ∈ Pset N C w ↔ val N C w (ePt p) zFn = true := by
  classical
  simp [Pset]

theorem mem_Lset (N : ℕ) (C : Circuit) (w : ℕ) (l : Fin N) :
    l ∈ Lset N C w ↔ val N C w zFn (ePt l) = true := by
  classical
  simp [Lset]

theorem Pset_input_left (N : ℕ) (C : Circuit) (u : Fin N) :
    Pset N C u.val = {u} := by
  ext p
  rw [mem_Pset, val_input_left, Finset.mem_singleton]
  simp [ePt, eq_comm]

theorem Pset_input_right (N : ℕ) (C : Circuit) (v : Fin N) :
    Pset N C (N + v.val) = ∅ := by
  ext p
  rw [mem_Pset, val_input_right]
  simp [zFn]

theorem Lset_input_left (N : ℕ) (C : Circuit) (u : Fin N) :
    Lset N C u.val = ∅ := by
  ext l
  rw [mem_Lset, val_input_left]
  simp [zFn]

theorem Lset_input_right (N : ℕ) (C : Circuit) (v : Fin N) :
    Lset N C (N + v.val) = {v} := by
  ext l
  rw [mem_Lset, val_input_right, Finset.mem_singleton]
  simp [ePt, eq_comm]

theorem Pset_or (N : ℕ) (C : Circuit) (k : Fin C.gates.length)
    (a b : ℕ) (ha : a < N + N + k.val) (hb : b < N + N + k.val)
    (hin : C.gates[k.val].inputs = [a, b]) (hop : C.gates[k.val].op = GateOp.or) :
    Pset N C (N + N + k.val) = Pset N C a ∪ Pset N C b := by
  ext p
  simp only [mem_Pset, Finset.mem_union, val_gate_or N C k a b ha hb hin hop, Bool.or_eq_true]

theorem Lset_or (N : ℕ) (C : Circuit) (k : Fin C.gates.length)
    (a b : ℕ) (ha : a < N + N + k.val) (hb : b < N + N + k.val)
    (hin : C.gates[k.val].inputs = [a, b]) (hop : C.gates[k.val].op = GateOp.or) :
    Lset N C (N + N + k.val) = Lset N C a ∪ Lset N C b := by
  ext l
  simp only [mem_Lset, Finset.mem_union, val_gate_or N C k a b ha hb hin hop, Bool.or_eq_true]

theorem overlap_and_cases (N : ℕ) (C : Circuit)
    (k : Fin C.gates.length) (a b : ℕ)
    (hin : C.gates[k.val].inputs = [a, b])
    (hno : ¬ ((∀ w ∈ C.gates[k.val].inputs, DepL N C w) ∨ (∀ w ∈ C.gates[k.val].inputs, DepP N C w))) :
    (¬ DepL N C a ∧ ¬ DepP N C a) ∨
    (¬ DepL N C b ∧ ¬ DepP N C b) ∨
    (¬ DepL N C a ∧ ¬ DepP N C b) ∨
    (¬ DepL N C b ∧ ¬ DepP N C a) := by
  rw [hin] at hno
  push Not at hno
  rcases hno with ⟨⟨wL, hwLm, hwL⟩, ⟨wP, hwPm, hwP⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwLm hwPm
  rcases hwLm with rfl | rfl <;> rcases hwPm with rfl | rfl
  · exact Or.inl ⟨hwL, hwP⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hwL, hwP⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hwL, hwP⟩))
  · exact Or.inr (Or.inl ⟨hwL, hwP⟩)

theorem Pset_and_false (N : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (k : Fin C.gates.length) (a b : ℕ) (ha : a < N + N + k.val) (hb : b < N + N + k.val)
    (hin : C.gates[k.val].inputs = [a, b]) (hop : C.gates[k.val].op = GateOp.and)
    (hno : ¬ ((∀ w ∈ C.gates[k.val].inputs, DepL N C w) ∨ (∀ w ∈ C.gates[k.val].inputs, DepP N C w)))
    (hzA : val N C a zFn zFn = false) (hzB : val N C b zFn zFn = false) :
    Pset N C (N + N + k.val) = ∅ ∧ Lset N C (N + N + k.val) = ∅ := by
  rcases overlap_and_cases N C k a b hin hno with
    ⟨hnLa, hnPa⟩ | ⟨hnLb, hnPb⟩ | ⟨hnLa, hnPb⟩ | ⟨hnLb, hnPa⟩
  · constructor <;> ext p <;> simp [mem_Pset, mem_Lset, val_gate_and N C k a b ha hb hin hop,
      no_DepLP_const N C hm hord a hnLa hnPa, hzA]
  · constructor <;> ext p <;> simp [mem_Pset, mem_Lset, val_gate_and N C k a b ha hb hin hop,
      no_DepLP_const N C hm hord b hnLb hnPb, hzB]
  · constructor
    · ext p
      rw [mem_Pset, val_gate_and N C k a b ha hb hin hop, no_DepP_eq N C hm hord b hnPb, hzB]
      simp
    · ext l
      rw [mem_Lset, val_gate_and N C k a b ha hb hin hop, no_DepL_eq N C hm hord a hnLa, hzA]
      simp
  · constructor
    · ext p
      rw [mem_Pset, val_gate_and N C k a b ha hb hin hop, no_DepP_eq N C hm hord a hnPa, hzA]
      simp
    · ext l
      rw [mem_Lset, val_gate_and N C k a b ha hb hin hop, no_DepL_eq N C hm hord b hnLb, hzB]
      simp

theorem set_and_const_a (N : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (k : Fin C.gates.length) (a b : ℕ) (ha : a < N + N + k.val) (hb : b < N + N + k.val)
    (hin : C.gates[k.val].inputs = [a, b]) (hop : C.gates[k.val].op = GateOp.and)
    (hca : val N C a zFn zFn = true) :
    Pset N C (N + N + k.val) = Pset N C b ∧ Lset N C (N + N + k.val) = Lset N C b ∧
      ∀ p l, val N C (N + N + k.val) p l = val N C b p l := by
  have hall : ∀ p l, val N C a p l = true := fun p l =>
    val_mono N C hm hord zFn p zFn l (fun _ h => Bool.noConfusion h) (fun _ h => Bool.noConfusion h) a hca
  have hveq : ∀ p l, val N C (N + N + k.val) p l = val N C b p l := by
    intro p l
    rw [val_gate_and N C k a b ha hb hin hop, hall p l, Bool.true_and]
  refine ⟨?_, ?_, hveq⟩
  · ext p; simp [mem_Pset, hveq]
  · ext l; simp [mem_Lset, hveq]

theorem set_and_const_b (N : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (k : Fin C.gates.length) (a b : ℕ) (ha : a < N + N + k.val) (hb : b < N + N + k.val)
    (hin : C.gates[k.val].inputs = [a, b]) (hop : C.gates[k.val].op = GateOp.and)
    (hcb : val N C b zFn zFn = true) :
    Pset N C (N + N + k.val) = Pset N C a ∧ Lset N C (N + N + k.val) = Lset N C a ∧
      ∀ p l, val N C (N + N + k.val) p l = val N C a p l := by
  have hall : ∀ p l, val N C b p l = true := fun p l =>
    val_mono N C hm hord zFn p zFn l (fun _ h => Bool.noConfusion h) (fun _ h => Bool.noConfusion h) b hcb
  have hveq : ∀ p l, val N C (N + N + k.val) p l = val N C a p l := by
    intro p l
    rw [val_gate_and N C k a b ha hb hin hop, hall p l, Bool.and_true]
  refine ⟨?_, ?_, hveq⟩
  · ext p; simp [mem_Pset, hveq]
  · ext l; simp [mem_Lset, hveq]

noncomputable def reachStepP (N : ℕ) (C : Circuit) (j : Fin C.gates.length) : Finset ℕ := by
  classical
  exact if 2 ≤ (Lset N C (N + N + j.val)).card then
    if C.gates[j.val].op = GateOp.or then C.gates[j.val].inputs.toFinset
    else
      if val N C (C.gates[j.val].inputs.getD 0 0) zFn zFn = true then {C.gates[j.val].inputs.getD 1 0}
      else {C.gates[j.val].inputs.getD 0 0}
  else ∅

noncomputable def reachStepL (N : ℕ) (C : Circuit) (j : Fin C.gates.length) : Finset ℕ := by
  classical
  exact if 2 ≤ (Pset N C (N + N + j.val)).card then
    if C.gates[j.val].op = GateOp.or then C.gates[j.val].inputs.toFinset
    else
      if val N C (C.gates[j.val].inputs.getD 0 0) zFn zFn = true then {C.gates[j.val].inputs.getD 1 0}
      else {C.gates[j.val].inputs.getD 0 0}
  else ∅

noncomputable def foldReach (N : ℕ) (C : Circuit) (step : Fin C.gates.length → Finset ℕ)
    (gs : List (Fin C.gates.length)) (roots : Finset ℕ) : Finset ℕ := by
  classical
  exact gs.foldr (fun j S => if N + N + j.val ∈ S then S ∪ step j else S) roots

theorem mem_foldReach_roots (N : ℕ) (C : Circuit) (step : Fin C.gates.length → Finset ℕ)
    (gs : List (Fin C.gates.length)) (roots : Finset ℕ) :
    roots ⊆ foldReach N C step gs roots := by
  classical
  induction gs with
  | nil => exact Finset.Subset.refl _
  | cons j rest ih =>
    intro x hx
    simp only [foldReach, List.foldr_cons]
    split_ifs
    · exact Finset.mem_union_left _ (ih hx)
    · exact ih hx

theorem foldReach_upper (N : ℕ) (C : Circuit) (step : Fin C.gates.length → Finset ℕ)
    (gs : List (Fin C.gates.length)) (roots : Finset ℕ)
    (hsort : gs.Pairwise (fun a b => a.val < b.val))
    (hstep_lt : ∀ j : Fin C.gates.length, ∀ u ∈ step j, u < N + N + j.val) :
    ∀ k ∈ gs,
      N + N + k.val ∈ foldReach N C step gs roots →
      step k ⊆ foldReach N C step gs roots := by
  classical
  induction gs with
  | nil => intro k hk; simp at hk
  | cons j rest ih =>
    intro k hk hmem
    have hsort_rest : rest.Pairwise (fun a b => a.val < b.val) := (List.pairwise_cons.1 hsort).2
    have hlt_j : ∀ k' ∈ rest, j.val < k'.val := (List.pairwise_cons.1 hsort).1
    simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · change step k ⊆ if N + N + k.val ∈ foldReach N C step rest roots then foldReach N C step rest roots ∪ step k else foldReach N C step rest roots
      change N + N + k.val ∈ if N + N + k.val ∈ foldReach N C step rest roots then foldReach N C step rest roots ∪ step k else foldReach N C step rest roots at hmem
      split_ifs at hmem ⊢ with h
      · exact Finset.subset_union_right
      · exact False.elim (h hmem)
    · have hne : N + N + k.val ∉ step j := by
        intro hkj
        have h1 := hstep_lt j _ hkj
        have h2 := hlt_j k hk
        omega
      change step k ⊆ if N + N + j.val ∈ foldReach N C step rest roots then foldReach N C step rest roots ∪ step j else foldReach N C step rest roots
      change N + N + k.val ∈ if N + N + j.val ∈ foldReach N C step rest roots then foldReach N C step rest roots ∪ step j else foldReach N C step rest roots at hmem
      split_ifs at hmem ⊢ with h
      · have hmem_rest : N + N + k.val ∈ foldReach N C step rest roots := by
          rcases Finset.mem_union.1 hmem with h1 | h2
          · exact h1
          · exact False.elim (hne h2)
        exact Finset.Subset.trans (ih hsort_rest k hk hmem_rest) Finset.subset_union_left
      · exact ih hsort_rest k hk hmem

theorem foldReach_inv (N : ℕ) (C : Circuit) (step : Fin C.gates.length → Finset ℕ)
    (gs : List (Fin C.gates.length)) (roots : Finset ℕ)
    (Q : ℕ → Prop)
    (hroots : ∀ w ∈ roots, Q w)
    (hstep : ∀ j ∈ gs, Q (N + N + j.val) → ∀ u ∈ step j, Q u) :
    ∀ w ∈ foldReach N C step gs roots, Q w := by
  classical
  induction gs with
  | nil => exact hroots
  | cons j rest ih =>
    intro w hw
    have ih' := ih (fun k hk => hstep k (List.mem_cons_of_mem j hk))
    change w ∈ if N + N + j.val ∈ foldReach N C step rest roots then foldReach N C step rest roots ∪ step j else foldReach N C step rest roots at hw
    split_ifs at hw with h
    · rcases Finset.mem_union.1 hw with h1 | h2
      · exact ih' w h1
      · exact hstep j List.mem_cons_self (ih' _ h) w h2
    · exact ih' w hw

theorem foldReach_decomp (N : ℕ) (C : Circuit) (step : Fin C.gates.length → Finset ℕ)
    (gs : List (Fin C.gates.length)) (roots : Finset ℕ) :
    ∀ w ∈ foldReach N C step gs roots,
      w ∈ roots ∨ ∃ j ∈ gs, N + N + j.val ∈ foldReach N C step gs roots ∧ w ∈ step j := by
  classical
  induction gs with
  | nil =>
    intro w hw
    exact Or.inl hw
  | cons j rest ih =>
    intro w hw
    by_cases h : N + N + j.val ∈ foldReach N C step rest roots
    · have hf : foldReach N C step (j :: rest) roots = foldReach N C step rest roots ∪ step j := by
        change (if N + N + j.val ∈ foldReach N C step rest roots then
            foldReach N C step rest roots ∪ step j
          else foldReach N C step rest roots) = foldReach N C step rest roots ∪ step j
        exact if_pos h
      have hw' : w ∈ foldReach N C step rest roots ∪ step j := hf ▸ hw
      rw [hf]
      rcases Finset.mem_union.1 hw' with h1 | h2
      · rcases ih w h1 with hr | ⟨k, hk, hkm, hwk⟩
        · exact Or.inl hr
        · exact Or.inr ⟨k, List.mem_cons_of_mem j hk, Finset.mem_union_left _ hkm, hwk⟩
      · exact Or.inr ⟨j, List.mem_cons_self, Finset.mem_union_left _ h, h2⟩
    · have hf : foldReach N C step (j :: rest) roots = foldReach N C step rest roots := by
        change (if N + N + j.val ∈ foldReach N C step rest roots then
            foldReach N C step rest roots ∪ step j
          else foldReach N C step rest roots) = foldReach N C step rest roots
        exact if_neg h
      have hw' : w ∈ foldReach N C step rest roots := hf ▸ hw
      rw [hf]
      rcases ih w hw' with hr | ⟨k, hk, hkm, hwk⟩
      · exact Or.inl hr
      · exact Or.inr ⟨k, List.mem_cons_of_mem j hk, hkm, hwk⟩

theorem pairwise_finRange (n : ℕ) : (List.finRange n).Pairwise (fun a b => a.val < b.val) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa using hij

def TopWire (N : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ p l : Fin N → Bool, val N C w p l = true → val N C C.output p l = true

noncomputable def sideP (N : ℕ) (C : Circuit) (k : Fin C.gates.length) : ℕ := by
  classical
  exact if ¬ DepL N C (C.gates[k.val].inputs.getD 0 0) then C.gates[k.val].inputs.getD 0 0
        else C.gates[k.val].inputs.getD 1 0

noncomputable def sideL (N : ℕ) (C : Circuit) (k : Fin C.gates.length) : ℕ := by
  classical
  exact if ¬ DepL N C (C.gates[k.val].inputs.getD 0 0) then C.gates[k.val].inputs.getD 1 0
        else C.gates[k.val].inputs.getD 0 0

def GoodG (N : ℕ) (C : Circuit) (k : Fin C.gates.length) : Prop :=
  C.gates[k.val].op = GateOp.and ∧
  TopWire N C (N + N + k.val) ∧
  val N C (C.gates[k.val].inputs.getD 0 0) zFn zFn = false ∧
  val N C (C.gates[k.val].inputs.getD 1 0) zFn zFn = false ∧
  (∃ p0 l0 : Fin N, val N C (N + N + k.val) (ePt p0) (ePt l0) = true)

theorem descend_good (N : ℕ) (C : Circuit)
    (hm : Monotone2 C)
    (hout_lt : C.output < N + N + C.gates.length)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (hp_out : ∀ p' : Fin N, val N C C.output (ePt p') zFn = false)
    (hl_out : ∀ l' : Fin N, val N C C.output zFn (ePt l') = false)
    (p0 l0 : Fin N)
    (w : ℕ) (htw : TopWire N C w) (hw : val N C w (ePt p0) (ePt l0) = true) :
    ∃ k : Fin C.gates.length, GoodG N C k ∧ val N C (N + N + k.val) (ePt p0) (ePt l0) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwN : w < N
    · have h1 : val N C w (ePt p0) zFn = true := by
        rw [val_input_left N C ⟨w, hwN⟩] at hw ⊢
        exact hw
      have h2 := htw (ePt p0) zFn h1
      rw [hp_out p0] at h2
      exact Bool.noConfusion h2
    · by_cases hw2N : w < N + N
      · have hwe : w = N + (w - N) := by omega
        have hvlt : w - N < N := by omega
        have h1 : val N C w zFn (ePt l0) = true := by
          rw [hwe, val_input_right N C ⟨w - N, hvlt⟩] at hw ⊢
          exact hw
        have h2 := htw zFn (ePt l0) h1
        rw [hl_out l0] at h2
        exact Bool.noConfusion h2
      · by_cases hwbig : N + N + C.gates.length ≤ w
        · rw [val_big N C w hwbig] at hw
          exact Bool.noConfusion hw
        · have hklt : w - (N + N) < C.gates.length := by omega
          let k : Fin C.gates.length := ⟨w - (N + N), hklt⟩
          have hweq : N + N + k.val = w := by simp [k]; omega
          obtain ⟨a, b, hin, hab, hblt⟩ := hord k.val C.gates[k.val] (List.getElem?_eq_getElem k.isLt)
          have hmem : C.gates[k.val] ∈ C.gates := List.getElem_mem k.isLt
          rcases (hm C.gates[k.val] hmem).1 with hop | hop
          · by_cases hca : val N C a zFn zFn = true
            · obtain ⟨_, _, hveq⟩ := set_and_const_a N C hm hord k a b (by omega) hblt hin hop hca
              have htwb : TopWire N C b := fun p l h => htw p l (by rw [← hweq, hveq p l]; exact h)
              have hvb : val N C b (ePt p0) (ePt l0) = true := by
                rw [← hveq (ePt p0) (ePt l0), hweq]; exact hw
              exact ih b (by omega) htwb hvb
            · by_cases hcb : val N C b zFn zFn = true
              · obtain ⟨_, _, hveq⟩ := set_and_const_b N C hm hord k a b (by omega) hblt hin hop hcb
                have htwa : TopWire N C a := fun p l h => htw p l (by rw [← hweq, hveq p l]; exact h)
                have hva : val N C a (ePt p0) (ePt l0) = true := by
                  rw [← hveq (ePt p0) (ePt l0), hweq]; exact hw
                exact ih a (by omega) htwa hva
              · have hfa : val N C a zFn zFn = false := Bool.eq_false_iff.mpr hca
                have hfb : val N C b zFn zFn = false := Bool.eq_false_iff.mpr hcb
                have htwk : TopWire N C (N + N + k.val) := by rw [hweq]; exact htw
                have hvk : val N C (N + N + k.val) (ePt p0) (ePt l0) = true := by rw [hweq]; exact hw
                refine ⟨k, ⟨hop, htwk, ?_, ?_, ⟨p0, l0, hvk⟩⟩, hvk⟩
                · simp [hin, hfa]
                · simp [hin, hfb]
          · have htwa : TopWire N C a := fun p l h =>
              htw p l (by rw [← hweq, val_gate_or N C k a b (by omega) hblt hin hop, h, Bool.true_or])
            have htwb : TopWire N C b := fun p l h =>
              htw p l (by rw [← hweq, val_gate_or N C k a b (by omega) hblt hin hop, h, Bool.or_true])
            rw [← hweq, val_gate_or N C k a b (by omega) hblt hin hop, Bool.or_eq_true] at hw
            rcases hw with ha | hb
            · exact ih a (by omega) htwa ha
            · exact ih b (by omega) htwb hb

theorem good_sides (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (hno_all : ∀ k : Fin C.gates.length, C.gates[k.val].op = GateOp.and →
      ¬ ((∀ w ∈ C.gates[k.val].inputs, DepL N C w) ∨ (∀ w ∈ C.gates[k.val].inputs, DepP N C w)))
    (hsound_pair : ∀ p l : Fin N, val N C C.output (ePt p) (ePt l) = true → I p l)
    (k : Fin C.gates.length) (hg : GoodG N C k) :
    sideP N C k < N + N + k.val ∧
    sideL N C k < N + N + k.val ∧
    val N C (sideP N C k) zFn zFn = false ∧
    val N C (sideL N C k) zFn zFn = false ∧
    ¬ DepL N C (sideP N C k) ∧
    ¬ DepP N C (sideL N C k) ∧
    Lset N C (sideP N C k) = ∅ ∧
    Pset N C (sideL N C k) = ∅ ∧
    (∀ p l : Fin N, val N C (N + N + k.val) (ePt p) (ePt l) = true ↔ p ∈ Pset N C (sideP N C k) ∧ l ∈ Lset N C (sideL N C k)) ∧
    (∀ p ∈ Pset N C (sideP N C k), ∀ l ∈ Lset N C (sideL N C k), I p l) ∧
    (Pset N C (sideP N C k)).Nonempty ∧
    (Lset N C (sideL N C k)).Nonempty := by
  classical
  rcases hg with ⟨hop, htw, hz0, hz1, p0, l0, hv0⟩
  obtain ⟨a, b, hin, hab, hblt⟩ := hord k.val C.gates[k.val] (List.getElem?_eq_getElem k.isLt)
  have hzA : val N C a zFn zFn = false := by simpa [hin] using hz0
  have hzB : val N C b zFn zFn = false := by simpa [hin] using hz1
  have hno := hno_all k hop
  have hnotA : ¬ (¬ DepL N C a ∧ ¬ DepP N C a) := by
    intro h
    have hv := val_gate_and N C k a b (by omega) hblt hin hop (ePt p0) (ePt l0)
    rw [no_DepLP_const N C hm hord a h.1 h.2, hzA, Bool.false_and] at hv
    rw [hv] at hv0
    exact Bool.noConfusion hv0
  have hnotB : ¬ (¬ DepL N C b ∧ ¬ DepP N C b) := by
    intro h
    have hv := val_gate_and N C k a b (by omega) hblt hin hop (ePt p0) (ePt l0)
    rw [no_DepLP_const N C hm hord b h.1 h.2, hzB, Bool.and_false] at hv
    rw [hv] at hv0
    exact Bool.noConfusion hv0
  have hcases : (¬ DepL N C a ∧ ¬ DepP N C b) ∨ (¬ DepL N C b ∧ ¬ DepP N C a) := by
    rcases overlap_and_cases N C k a b hin hno with h | h | h | h
    · exact False.elim (hnotA h)
    · exact False.elim (hnotB h)
    · exact Or.inl h
    · exact Or.inr h
  have hmain : ∀ (sP sL : ℕ), sP < N + N + k.val → sL < N + N + k.val →
      (∀ p l, val N C (N + N + k.val) p l = (val N C sP p l && val N C sL p l)) →
      val N C sP zFn zFn = false → val N C sL zFn zFn = false →
      ¬ DepL N C sP → ¬ DepP N C sL →
      sP < N + N + k.val ∧ sL < N + N + k.val ∧
      val N C sP zFn zFn = false ∧ val N C sL zFn zFn = false ∧
      ¬ DepL N C sP ∧ ¬ DepP N C sL ∧
      Lset N C sP = ∅ ∧ Pset N C sL = ∅ ∧
      (∀ p l : Fin N, val N C (N + N + k.val) (ePt p) (ePt l) = true ↔ p ∈ Pset N C sP ∧ l ∈ Lset N C sL) ∧
      (∀ p ∈ Pset N C sP, ∀ l ∈ Lset N C sL, I p l) ∧
      (Pset N C sP).Nonempty ∧ (Lset N C sL).Nonempty := by
    intro sP sL hsP hsL hmul hzP hzL hnLP hnPL
    have hLempty : Lset N C sP = ∅ := by
      ext l
      rw [mem_Lset, no_DepL_eq N C hm hord sP hnLP, hzP]
      simp
    have hPempty : Pset N C sL = ∅ := by
      ext p
      rw [mem_Pset, no_DepP_eq N C hm hord sL hnPL, hzL]
      simp
    have hiff : ∀ p l : Fin N, val N C (N + N + k.val) (ePt p) (ePt l) = true ↔ p ∈ Pset N C sP ∧ l ∈ Lset N C sL := by
      intro p l
      rw [hmul, Bool.and_eq_true, no_DepL_eq N C hm hord sP hnLP, no_DepP_eq N C hm hord sL hnPL, mem_Pset, mem_Lset]
    have hI : ∀ p ∈ Pset N C sP, ∀ l ∈ Lset N C sL, I p l := by
      intro p hp l hl
      exact hsound_pair p l (htw (ePt p) (ePt l) ((hiff p l).2 ⟨hp, hl⟩))
    obtain ⟨hp0, hl0⟩ := (hiff p0 l0).1 hv0
    exact ⟨hsP, hsL, hzP, hzL, hnLP, hnPL, hLempty, hPempty, hiff, hI, ⟨p0, hp0⟩, ⟨l0, hl0⟩⟩
  rcases hcases with ⟨hnLa, hnPb⟩ | ⟨hnLb, hnPa⟩
  · have hsP : sideP N C k = a := by simp [sideP, hin, hnLa]
    have hsL : sideL N C k = b := by simp [sideL, hin, hnLa]
    rw [hsP, hsL]
    exact hmain a b (by omega) hblt (val_gate_and N C k a b (by omega) hblt hin hop) hzA hzB hnLa hnPb
  · have hda : ¬ (¬ DepL N C a) := fun h => hnotA ⟨h, hnPa⟩
    have hsP : sideP N C k = b := by simp [sideP, hin, hda]
    have hsL : sideL N C k = a := by simp [sideL, hin, hda]
    rw [hsP, hsL]
    exact hmain b a hblt (by omega) (fun p l => by rw [val_gate_and N C k a b (by omega) hblt hin hop, Bool.and_comm]) hzB hzA hnLb hnPa

noncomputable def G_L (N : ℕ) (C : Circuit) (l : Fin N) : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun k =>
    GoodG N C k ∧ 2 ≤ (Pset N C (sideP N C k)).card ∧ Lset N C (sideL N C k) = {l}

noncomputable def G_P (N : ℕ) (C : Circuit) (p : Fin N) : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun k =>
    GoodG N C k ∧ (Pset N C (sideP N C k)).card = 1 ∧ Pset N C (sideP N C k) = {p}

noncomputable def ReachL (N : ℕ) (C : Circuit) (l : Fin N) : Finset ℕ := by
  classical
  exact foldReach N C (reachStepL N C) (List.finRange C.gates.length) ((G_L N C l).image (sideP N C))

noncomputable def ReachP (N : ℕ) (C : Circuit) (p : Fin N) : Finset ℕ := by
  classical
  exact foldReach N C (reachStepP N C) (List.finRange C.gates.length) ((G_P N C p).image (sideL N C))

noncomputable def R_or_L (N : ℕ) (C : Circuit) (l : Fin N) : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun j =>
    C.gates[j.val].op = GateOp.or ∧ N + N + j.val ∈ ReachL N C l ∧ 2 ≤ (Pset N C (N + N + j.val)).card

noncomputable def R_or_P (N : ℕ) (C : Circuit) (p : Fin N) : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun j =>
    C.gates[j.val].op = GateOp.or ∧ N + N + j.val ∈ ReachP N C p ∧ 2 ≤ (Lset N C (N + N + j.val)).card

noncomputable def CoveredL (N : ℕ) (C : Circuit) (l : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun p => ∃ k ∈ G_L N C l, p ∈ Pset N C (sideP N C k)

noncomputable def CoveredP (N : ℕ) (C : Circuit) (p : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun l => ∃ k ∈ G_P N C p, l ∈ Lset N C (sideL N C k)

theorem step_lt_L (N : ℕ) (C : Circuit)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (j : Fin C.gates.length) : ∀ u ∈ reachStepL N C j, u < N + N + j.val := by
  classical
  intro u hu
  obtain ⟨a, b, hin, hab, hblt⟩ := hord j.val C.gates[j.val] (List.getElem?_eq_getElem j.isLt)
  simp only [reachStepL] at hu
  split_ifs at hu with h1 h2 h3
  · rw [hin] at hu
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> omega
  · rw [hin] at hu
    simp only [List.getD_cons_succ, List.getD_cons_zero, Finset.mem_singleton] at hu
    subst hu; omega
  · rw [hin] at hu
    simp only [List.getD_cons_zero, Finset.mem_singleton] at hu
    subst hu; omega
  · simp at hu

theorem step_lt_P (N : ℕ) (C : Circuit)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (j : Fin C.gates.length) : ∀ u ∈ reachStepP N C j, u < N + N + j.val := by
  classical
  intro u hu
  obtain ⟨a, b, hin, hab, hblt⟩ := hord j.val C.gates[j.val] (List.getElem?_eq_getElem j.isLt)
  simp only [reachStepP] at hu
  split_ifs at hu with h1 h2 h3
  · rw [hin] at hu
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> omega
  · rw [hin] at hu
    simp only [List.getD_cons_succ, List.getD_cons_zero, Finset.mem_singleton] at hu
    subst hu; omega
  · rw [hin] at hu
    simp only [List.getD_cons_zero, Finset.mem_singleton] at hu
    subst hu; omega
  · simp at hu

theorem InvL_ReachL (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (hno_all : ∀ k : Fin C.gates.length, C.gates[k.val].op = GateOp.and →
      ¬ ((∀ w ∈ C.gates[k.val].inputs, DepL N C w) ∨ (∀ w ∈ C.gates[k.val].inputs, DepP N C w)))
    (hsound_pair : ∀ p l : Fin N, val N C C.output (ePt p) (ePt l) = true → I p l)
    (l : Fin N) :
    ∀ w ∈ ReachL N C l,
      w < N + N + C.gates.length ∧ val N C w zFn zFn = false ∧ Lset N C w = ∅ ∧ (∀ p ∈ Pset N C w, I p l) := by
  classical
  apply foldReach_inv
  · intro w hw
    simp only [Finset.mem_image, G_L, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases hw with ⟨k, ⟨hg, _, hLset⟩, rfl⟩
    obtain ⟨hsP, _, hzP, _, _, _, hLempty, _, _, hI, _, _⟩ := good_sides N I C hm hord hno_all hsound_pair k hg
    refine ⟨by omega, hzP, hLempty, fun p hp => hI p hp l ?_⟩
    rw [hLset]
    exact Finset.mem_singleton_self l
  · intro j _ hwj u hu
    rcases hwj with ⟨_, hzj, hLj, hIj⟩
    obtain ⟨a, b, hin, hab, hblt⟩ := hord j.val C.gates[j.val] (List.getElem?_eq_getElem j.isLt)
    simp only [reachStepL] at hu
    split_ifs at hu with hcard hop hca
    · rw [hin] at hu
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu
      have hz_or := (val_gate_or N C j a b (by omega) hblt hin hop zFn zFn).symm
      rw [hzj, Bool.or_eq_false_iff] at hz_or
      have hL_or := Lset_or N C j a b (by omega) hblt hin hop
      rw [hLj, eq_comm, Finset.union_eq_empty] at hL_or
      have hP_or := Pset_or N C j a b (by omega) hblt hin hop
      rcases hu with rfl | rfl
      · refine ⟨by omega, hz_or.1, hL_or.1, fun p hp => hIj p ?_⟩
        rw [hP_or]; exact Finset.mem_union_left _ hp
      · refine ⟨by omega, hz_or.2, hL_or.2, fun p hp => hIj p ?_⟩
        rw [hP_or]; exact Finset.mem_union_right _ hp
    · have hmem : C.gates[j.val] ∈ C.gates := List.getElem_mem j.isLt
      have hop_and : C.gates[j.val].op = GateOp.and :=
        Or.resolve_right (hm C.gates[j.val] hmem).1 hop
      rw [hin] at hca hu
      simp only [List.getD_cons_zero, List.getD_cons_succ, Finset.mem_singleton] at hca hu
      obtain ⟨hPa, hLa, hva⟩ := set_and_const_a N C hm hord j a b (by omega) hblt hin hop_and hca
      subst hu
      refine ⟨by omega, ?_, ?_, fun p hp => hIj p ?_⟩
      · rw [← hva zFn zFn]; exact hzj
      · rw [← hLa]; exact hLj
      · rw [hPa]; exact hp
    · have hmem : C.gates[j.val] ∈ C.gates := List.getElem_mem j.isLt
      have hop_and : C.gates[j.val].op = GateOp.and :=
        Or.resolve_right (hm C.gates[j.val] hmem).1 hop
      rw [hin] at hca hu
      simp only [List.getD_cons_zero, Finset.mem_singleton] at hca hu
      have hfa : val N C a zFn zFn = false := Bool.eq_false_iff.mpr hca
      have hcb : val N C b zFn zFn = true := by
        by_contra hnb
        have hfb : val N C b zFn zFn = false := Bool.eq_false_iff.mpr hnb
        have hpe := (Pset_and_false N C hm hord j a b (by omega) hblt hin hop_and (hno_all j hop_and) hfa hfb).1
        rw [hpe] at hcard
        simp at hcard
      obtain ⟨hPb, hLb, hvb⟩ := set_and_const_b N C hm hord j a b (by omega) hblt hin hop_and hcb
      subst hu
      refine ⟨by omega, ?_, ?_, fun p hp => hIj p ?_⟩
      · rw [← hvb zFn zFn]; exact hzj
      · rw [← hLb]; exact hLj
      · rw [hPb]; exact hp
    · simp at hu

theorem InvP_ReachP (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (hno_all : ∀ k : Fin C.gates.length, C.gates[k.val].op = GateOp.and →
      ¬ ((∀ w ∈ C.gates[k.val].inputs, DepL N C w) ∨ (∀ w ∈ C.gates[k.val].inputs, DepP N C w)))
    (hsound_pair : ∀ p l : Fin N, val N C C.output (ePt p) (ePt l) = true → I p l)
    (p : Fin N) :
    ∀ w ∈ ReachP N C p,
      w < N + N + C.gates.length ∧ val N C w zFn zFn = false ∧ Pset N C w = ∅ ∧ (∀ l ∈ Lset N C w, I p l) := by
  classical
  apply foldReach_inv
  · intro w hw
    simp only [Finset.mem_image, G_P, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases hw with ⟨k, ⟨hg, _, hPset⟩, rfl⟩
    obtain ⟨_, hsL, _, hzL, _, _, _, hPempty, _, hI, _, _⟩ := good_sides N I C hm hord hno_all hsound_pair k hg
    refine ⟨by omega, hzL, hPempty, fun l hl => hI p ?_ l hl⟩
    rw [hPset]
    exact Finset.mem_singleton_self p
  · intro j _ hwj u hu
    rcases hwj with ⟨_, hzj, hPj, hIj⟩
    obtain ⟨a, b, hin, hab, hblt⟩ := hord j.val C.gates[j.val] (List.getElem?_eq_getElem j.isLt)
    simp only [reachStepP] at hu
    split_ifs at hu with hcard hop hca
    · rw [hin] at hu
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu
      have hz_or := (val_gate_or N C j a b (by omega) hblt hin hop zFn zFn).symm
      rw [hzj, Bool.or_eq_false_iff] at hz_or
      have hP_or := Pset_or N C j a b (by omega) hblt hin hop
      rw [hPj, eq_comm, Finset.union_eq_empty] at hP_or
      have hL_or := Lset_or N C j a b (by omega) hblt hin hop
      rcases hu with rfl | rfl
      · refine ⟨by omega, hz_or.1, hP_or.1, fun l hl => hIj l ?_⟩
        rw [hL_or]; exact Finset.mem_union_left _ hl
      · refine ⟨by omega, hz_or.2, hP_or.2, fun l hl => hIj l ?_⟩
        rw [hL_or]; exact Finset.mem_union_right _ hl
    · have hmem : C.gates[j.val] ∈ C.gates := List.getElem_mem j.isLt
      have hop_and : C.gates[j.val].op = GateOp.and :=
        Or.resolve_right (hm C.gates[j.val] hmem).1 hop
      rw [hin] at hca hu
      simp only [List.getD_cons_zero, List.getD_cons_succ, Finset.mem_singleton] at hca hu
      obtain ⟨hPa, hLa, hva⟩ := set_and_const_a N C hm hord j a b (by omega) hblt hin hop_and hca
      subst hu
      refine ⟨by omega, ?_, ?_, fun l hl => hIj l ?_⟩
      · rw [← hva zFn zFn]; exact hzj
      · rw [← hPa]; exact hPj
      · rw [hLa]; exact hl
    · have hmem : C.gates[j.val] ∈ C.gates := List.getElem_mem j.isLt
      have hop_and : C.gates[j.val].op = GateOp.and :=
        Or.resolve_right (hm C.gates[j.val] hmem).1 hop
      rw [hin] at hca hu
      simp only [List.getD_cons_zero, Finset.mem_singleton] at hca hu
      have hfa : val N C a zFn zFn = false := Bool.eq_false_iff.mpr hca
      have hcb : val N C b zFn zFn = true := by
        by_contra hnb
        have hfb : val N C b zFn zFn = false := Bool.eq_false_iff.mpr hnb
        have hle := (Pset_and_false N C hm hord j a b (by omega) hblt hin hop_and (hno_all j hop_and) hfa hfb).2
        rw [hle] at hcard
        simp at hcard
      obtain ⟨hPb, hLb, hvb⟩ := set_and_const_b N C hm hord j a b (by omega) hblt hin hop_and hcb
      subst hu
      refine ⟨by omega, ?_, ?_, fun l hl => hIj l ?_⟩
      · rw [← hvb zFn zFn]; exact hzj
      · rw [← hPb]; exact hPj
      · rw [hLb]; exact hl
    · simp at hu

theorem coveredL_bound (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (hno_all : ∀ k : Fin C.gates.length, C.gates[k.val].op = GateOp.and →
      ¬ ((∀ w ∈ C.gates[k.val].inputs, DepL N C w) ∨ (∀ w ∈ C.gates[k.val].inputs, DepP N C w)))
    (hsound_pair : ∀ p l : Fin N, val N C C.output (ePt p) (ePt l) = true → I p l)
    (l : Fin N) :
    (CoveredL N C l).card ≤ (G_L N C l).card + (R_or_L N C l).card := by
  classical
  let R := ReachL N C l
  let S1 := R.filter fun w => (Pset N C w).card = 1
  let Rall : Finset (Fin C.gates.length) := Finset.univ.filter fun j =>
    N + N + j.val ∈ R ∧ 2 ≤ (Pset N C (N + N + j.val)).card
  let Rand := Rall.filter fun j => C.gates[j.val].op = GateOp.and
  have hcov_S1 : CoveredL N C l ⊆ S1.biUnion (Pset N C) := by
    intro p hp
    simp only [CoveredL, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨k, hk, hpP⟩
    have hwR : sideP N C k ∈ R := mem_foldReach_roots N C (reachStepL N C) _ _ (Finset.mem_image_of_mem _ hk)
    have hrec : ∀ w : ℕ, w ∈ R → p ∈ Pset N C w → ∃ s ∈ S1, p ∈ Pset N C s := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hpw
        by_cases hcard : 2 ≤ (Pset N C w).card
        · obtain ⟨hwlt, _, _, _⟩ := InvL_ReachL N I C hm hord hno_all hsound_pair l w hw
          have hge2N : N + N ≤ w := by
            by_contra hlt2N
            by_cases hltN : w < N
            · rw [Pset_input_left N C ⟨w, hltN⟩, Finset.card_singleton] at hcard; omega
            · have hwe : w = N + (w - N) := by omega
              rw [hwe, Pset_input_right N C ⟨w - N, by omega⟩, Finset.card_empty] at hcard; omega
          let j : Fin C.gates.length := ⟨w - (N + N), by omega⟩
          have hjeq : N + N + j.val = w := by simp [j]; omega
          have hjstep := foldReach_upper N C (reachStepL N C) (List.finRange C.gates.length)
            ((G_L N C l).image (sideP N C)) (pairwise_finRange _) (step_lt_L N C hord) j (List.mem_finRange j) (by rwa [hjeq])
          obtain ⟨a, b, hin, hab, hblt⟩ := hord j.val C.gates[j.val] (List.getElem?_eq_getElem j.isLt)
          have hmem : C.gates[j.val] ∈ C.gates := List.getElem_mem j.isLt
          rcases (hm C.gates[j.val] hmem).1 with hop | hop
          · by_cases hca : val N C a zFn zFn = true
            · obtain ⟨hPa, _, _⟩ := set_and_const_a N C hm hord j a b (by omega) hblt hin hop hca
              have hne : GateOp.and ≠ GateOp.or := fun h => GateOp.noConfusion h
              have hbin : b ∈ reachStepL N C j := by
                simp only [reachStepL, hjeq, hcard, ↓reduceIte, hop, hne, hin, List.getD_cons_zero, List.getD_cons_succ, hca]
                exact Finset.mem_singleton_self b
              rw [← hjeq, hPa] at hpw
              exact ih b (by omega) (hjstep hbin) hpw
            · have hfa : val N C a zFn zFn = false := Bool.eq_false_iff.mpr hca
              have hcb : val N C b zFn zFn = true := by
                by_contra hnb
                have hfb : val N C b zFn zFn = false := Bool.eq_false_iff.mpr hnb
                have hpe := (Pset_and_false N C hm hord j a b (by omega) hblt hin hop (hno_all j hop) hfa hfb).1
                rw [← hjeq, hpe] at hcard
                simp at hcard
              obtain ⟨hPb, _, _⟩ := set_and_const_b N C hm hord j a b (by omega) hblt hin hop hcb
              have hne : GateOp.and ≠ GateOp.or := fun h => GateOp.noConfusion h
              have hain : a ∈ reachStepL N C j := by
                simp only [reachStepL, hjeq, hcard, ↓reduceIte, hop, hne, hin, List.getD_cons_zero, hca]
                exact Finset.mem_singleton_self a
              rw [← hjeq, hPb] at hpw
              exact ih a (by omega) (hjstep hain) hpw
          · have hop' : C.gates[j.val].op = GateOp.or := hop
            have hain : a ∈ reachStepL N C j := by
              simp [reachStepL, hjeq, hcard, hin, hop']
            have hbin : b ∈ reachStepL N C j := by
              simp [reachStepL, hjeq, hcard, hin, hop']
            have hPor := Pset_or N C j a b (by omega) hblt hin hop
            rw [← hjeq, hPor, Finset.mem_union] at hpw
            rcases hpw with hpa | hpb
            · exact ih a (by omega) (hjstep hain) hpa
            · exact ih b (by omega) (hjstep hbin) hpb
        · have hpos : 0 < (Pset N C w).card := Finset.card_pos.mpr ⟨p, hpw⟩
          have h1 : (Pset N C w).card = 1 := by omega
          exact ⟨w, Finset.mem_filter.mpr ⟨hw, h1⟩, hpw⟩
    obtain ⟨s, hs, hps⟩ := hrec (sideP N C k) hwR hpP
    exact Finset.mem_biUnion.mpr ⟨s, hs, hps⟩
  have hcov_card : (CoveredL N C l).card ≤ S1.card := by
    refine (Finset.card_le_card hcov_S1).trans ?_
    refine Finset.card_biUnion_le.trans (le_of_eq ?_)
    calc ∑ s ∈ S1, (Pset N C s).card
        = ∑ _ ∈ S1, 1 := Finset.sum_congr rfl fun s hs => (Finset.mem_filter.mp hs).2
      _ = S1.card := by simp
  have hdisj_SR : Disjoint S1 (Rall.image fun j : Fin C.gates.length => N + N + j.val) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [S1, Finset.mem_filter] at hw1
    simp only [Rall, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw2
    rcases hw2 with ⟨j, ⟨_, h2⟩, rfl⟩
    omega
  have hsub_union : S1 ∪ (Rall.image fun j : Fin C.gates.length => N + N + j.val) ⊆ R := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw1 | hw2
    · exact (Finset.mem_filter.mp hw1).1
    · simp only [Rall, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw2
      rcases hw2 with ⟨j, ⟨hj, _⟩, rfl⟩
      exact hj
  have hR_lower : S1.card + Rall.card ≤ R.card := by
    have hinj : (Rall.image fun j : Fin C.gates.length => N + N + j.val).card = Rall.card := by
      apply Finset.card_image_of_injective
      intro a b hab
      dsimp only at hab
      exact Fin.ext (by omega)
    calc S1.card + Rall.card
        = S1.card + (Rall.image fun j : Fin C.gates.length => N + N + j.val).card := by rw [hinj]
      _ = (S1 ∪ (Rall.image fun j : Fin C.gates.length => N + N + j.val)).card := (Finset.card_union_of_disjoint hdisj_SR).symm
      _ ≤ R.card := Finset.card_le_card hsub_union
  have hR_sub : R ⊆ ((G_L N C l).image (sideP N C)) ∪ Rall.biUnion (reachStepL N C) := by
    intro w hw
    rcases foldReach_decomp N C (reachStepL N C) (List.finRange C.gates.length) ((G_L N C l).image (sideP N C)) w hw with
      hr | ⟨j, _, hjR, hwj⟩
    · exact Finset.mem_union_left _ hr
    · have h2 : 2 ≤ (Pset N C (N + N + j.val)).card := by
        by_contra hlt
        simp [reachStepL, hlt] at hwj
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjR, h2⟩, hwj⟩)
  have hRall_split : Rall.card = (R_or_L N C l).card + Rand.card := by
    have hU : Rall = R_or_L N C l ∪ Rand := by
      ext j
      simp only [Rall, R_or_L, Rand, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        have hmem : C.gates[j.val] ∈ C.gates := List.getElem_mem j.isLt
        rcases (hm C.gates[j.val] hmem).1 with hop | hop
        · exact Or.inr ⟨hj, hop⟩
        · exact Or.inl ⟨hop, hj.1, hj.2⟩
      · rintro (h | h)
        · exact ⟨h.2.1, h.2.2⟩
        · exact h.1
    have hD : Disjoint (R_or_L N C l) Rand := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [R_or_L, Rand, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
      have hop1 : C.gates[j.val].op = GateOp.or := hj1.1
      have hop2 : C.gates[j.val].op = GateOp.and := hj2.2
      rw [hop1] at hop2
      exact GateOp.noConfusion hop2
    rw [hU, Finset.card_union_of_disjoint hD]
  have hR_upper : R.card ≤ (G_L N C l).card + 2 * (R_or_L N C l).card + Rand.card := by
    have hsplit : Rall.biUnion (reachStepL N C) = (R_or_L N C l).biUnion (reachStepL N C) ∪ Rand.biUnion (reachStepL N C) := by
      ext x
      simp only [Rall, R_or_L, Rand, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, ⟨h1, h2⟩, hx⟩
        have hmem : C.gates[j.val] ∈ C.gates := List.getElem_mem j.isLt
        rcases (hm C.gates[j.val] hmem).1 with hop | hop
        · exact Or.inr ⟨j, ⟨⟨h1, h2⟩, hop⟩, hx⟩
        · exact Or.inl ⟨j, ⟨hop, h1, h2⟩, hx⟩
      · rintro (⟨j, ⟨hop, h1, h2⟩, hx⟩ | ⟨j, ⟨⟨h1, h2⟩, _⟩, hx⟩)
        · exact ⟨j, ⟨h1, h2⟩, hx⟩
        · exact ⟨j, ⟨h1, h2⟩, hx⟩
    have hstep_or : ∀ j ∈ R_or_L N C l, (reachStepL N C j).card ≤ 2 := by
      intro j hj
      obtain ⟨a, b, hin, _, _⟩ := hord j.val C.gates[j.val] (List.getElem?_eq_getElem j.isLt)
      have hop : C.gates[j.val].op = GateOp.or := (Finset.mem_filter.mp hj).2.1
      simp only [reachStepL, hop, hin, ↓reduceIte]
      split_ifs
      · have hle : [a, b].toFinset.card ≤ [a, b].length := List.toFinset_card_le [a, b]
        simpa using hle
      · simp
    have hstep_and : ∀ j ∈ Rand, (reachStepL N C j).card ≤ 1 := by
      intro j hj
      have hop : C.gates[j.val].op = GateOp.and := (Finset.mem_filter.mp hj).2
      have hne : GateOp.and ≠ GateOp.or := fun h => GateOp.noConfusion h
      simp only [reachStepL, hop, hne, ↓reduceIte]
      split_ifs <;> simp
    calc R.card
        ≤ (((G_L N C l).image (sideP N C)) ∪ Rall.biUnion (reachStepL N C)).card := Finset.card_le_card hR_sub
      _ ≤ ((G_L N C l).image (sideP N C)).card + (Rall.biUnion (reachStepL N C)).card := Finset.card_union_le _ _
      _ ≤ (G_L N C l).card + ((R_or_L N C l).biUnion (reachStepL N C) ∪ Rand.biUnion (reachStepL N C)).card := by
            rw [hsplit]
            exact Nat.add_le_add Finset.card_image_le le_rfl
      _ ≤ (G_L N C l).card + ((R_or_L N C l).biUnion (reachStepL N C)).card + (Rand.biUnion (reachStepL N C)).card := by
            have := Finset.card_union_le ((R_or_L N C l).biUnion (reachStepL N C)) (Rand.biUnion (reachStepL N C))
            omega
      _ ≤ (G_L N C l).card + (∑ j ∈ R_or_L N C l, (reachStepL N C j).card) + (∑ j ∈ Rand, (reachStepL N C j).card) := by
            have h1 := Finset.card_biUnion_le (s := R_or_L N C l) (t := reachStepL N C)
            have h2 := Finset.card_biUnion_le (s := Rand) (t := reachStepL N C)
            omega
      _ ≤ (G_L N C l).card + (∑ _ ∈ R_or_L N C l, 2) + (∑ _ ∈ Rand, 1) := by
            have h1 := Finset.sum_le_sum hstep_or
            have h2 := Finset.sum_le_sum hstep_and
            omega
      _ = (G_L N C l).card + 2 * (R_or_L N C l).card + Rand.card := by
            simp [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

theorem coveredP_bound (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hm : Monotone2 C)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (hno_all : ∀ k : Fin C.gates.length, C.gates[k.val].op = GateOp.and →
      ¬ ((∀ w ∈ C.gates[k.val].inputs, DepL N C w) ∨ (∀ w ∈ C.gates[k.val].inputs, DepP N C w)))
    (hsound_pair : ∀ p l : Fin N, val N C C.output (ePt p) (ePt l) = true → I p l)
    (p : Fin N) :
    (CoveredP N C p).card ≤ (G_P N C p).card + (R_or_P N C p).card := by
  classical
  let R := ReachP N C p
  let S1 := R.filter fun w => (Lset N C w).card = 1
  let Rall : Finset (Fin C.gates.length) := Finset.univ.filter fun j =>
    N + N + j.val ∈ R ∧ 2 ≤ (Lset N C (N + N + j.val)).card
  let Rand := Rall.filter fun j => C.gates[j.val].op = GateOp.and
  have hcov_S1 : CoveredP N C p ⊆ S1.biUnion (Lset N C) := by
    intro l hl
    simp only [CoveredP, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rcases hl with ⟨k, hk, hlL⟩
    have hwR : sideL N C k ∈ R := mem_foldReach_roots N C (reachStepP N C) _ _ (Finset.mem_image_of_mem _ hk)
    have hrec : ∀ w : ℕ, w ∈ R → l ∈ Lset N C w → ∃ s ∈ S1, l ∈ Lset N C s := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hlw
        by_cases hcard : 2 ≤ (Lset N C w).card
        · obtain ⟨hwlt, _, _, _⟩ := InvP_ReachP N I C hm hord hno_all hsound_pair p w hw
          have hge2N : N + N ≤ w := by
            by_contra hlt2N
            by_cases hltN : w < N
            · rw [Lset_input_left N C ⟨w, hltN⟩, Finset.card_empty] at hcard; omega
            · have hwe : w = N + (w - N) := by omega
              rw [hwe, Lset_input_right N C ⟨w - N, by omega⟩, Finset.card_singleton] at hcard; omega
          let j : Fin C.gates.length := ⟨w - (N + N), by omega⟩
          have hjeq : N + N + j.val = w := by simp [j]; omega
          have hjstep := foldReach_upper N C (reachStepP N C) (List.finRange C.gates.length)
            ((G_P N C p).image (sideL N C)) (pairwise_finRange _) (step_lt_P N C hord) j (List.mem_finRange j) (by rwa [hjeq])
          obtain ⟨a, b, hin, hab, hblt⟩ := hord j.val C.gates[j.val] (List.getElem?_eq_getElem j.isLt)
          have hmem : C.gates[j.val] ∈ C.gates := List.getElem_mem j.isLt
          rcases (hm C.gates[j.val] hmem).1 with hop | hop
          · by_cases hca : val N C a zFn zFn = true
            · obtain ⟨_, hLa, _⟩ := set_and_const_a N C hm hord j a b (by omega) hblt hin hop hca
              have hne : GateOp.and ≠ GateOp.or := fun h => GateOp.noConfusion h
              have hbin : b ∈ reachStepP N C j := by
                simp only [reachStepP, hjeq, hcard, ↓reduceIte, hop, hne, hin, List.getD_cons_zero, List.getD_cons_succ, hca]
                exact Finset.mem_singleton_self b
              rw [← hjeq, hLa] at hlw
              exact ih b (by omega) (hjstep hbin) hlw
            · have hfa : val N C a zFn zFn = false := Bool.eq_false_iff.mpr hca
              have hcb : val N C b zFn zFn = true := by
                by_contra hnb
                have hfb : val N C b zFn zFn = false := Bool.eq_false_iff.mpr hnb
                have hle := (Pset_and_false N C hm hord j a b (by omega) hblt hin hop (hno_all j hop) hfa hfb).2
                rw [← hjeq, hle] at hcard
                simp at hcard
              obtain ⟨_, hLb, _⟩ := set_and_const_b N C hm hord j a b (by omega) hblt hin hop hcb
              have hne : GateOp.and ≠ GateOp.or := fun h => GateOp.noConfusion h
              have hain : a ∈ reachStepP N C j := by
                simp only [reachStepP, hjeq, hcard, ↓reduceIte, hop, hne, hin, List.getD_cons_zero, hca]
                exact Finset.mem_singleton_self a
              rw [← hjeq, hLb] at hlw
              exact ih a (by omega) (hjstep hain) hlw
          · have hop' : C.gates[j.val].op = GateOp.or := hop
            have hain : a ∈ reachStepP N C j := by
              simp [reachStepP, hjeq, hcard, hin, hop']
            have hbin : b ∈ reachStepP N C j := by
              simp [reachStepP, hjeq, hcard, hin, hop']
            have hLor := Lset_or N C j a b (by omega) hblt hin hop
            rw [← hjeq, hLor, Finset.mem_union] at hlw
            rcases hlw with hla | hlb
            · exact ih a (by omega) (hjstep hain) hla
            · exact ih b (by omega) (hjstep hbin) hlb
        · have hpos : 0 < (Lset N C w).card := Finset.card_pos.mpr ⟨l, hlw⟩
          have h1 : (Lset N C w).card = 1 := by omega
          exact ⟨w, Finset.mem_filter.mpr ⟨hw, h1⟩, hlw⟩
    obtain ⟨s, hs, hls⟩ := hrec (sideL N C k) hwR hlL
    exact Finset.mem_biUnion.mpr ⟨s, hs, hls⟩
  have hcov_card : (CoveredP N C p).card ≤ S1.card := by
    refine (Finset.card_le_card hcov_S1).trans ?_
    refine Finset.card_biUnion_le.trans (le_of_eq ?_)
    calc ∑ s ∈ S1, (Lset N C s).card
        = ∑ _ ∈ S1, 1 := Finset.sum_congr rfl fun s hs => (Finset.mem_filter.mp hs).2
      _ = S1.card := by simp
  have hdisj_SR : Disjoint S1 (Rall.image fun j : Fin C.gates.length => N + N + j.val) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [S1, Finset.mem_filter] at hw1
    simp only [Rall, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw2
    rcases hw2 with ⟨j, ⟨_, h2⟩, rfl⟩
    omega
  have hsub_union : S1 ∪ (Rall.image fun j : Fin C.gates.length => N + N + j.val) ⊆ R := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw1 | hw2
    · exact (Finset.mem_filter.mp hw1).1
    · simp only [Rall, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw2
      rcases hw2 with ⟨j, ⟨hj, _⟩, rfl⟩
      exact hj
  have hR_lower : S1.card + Rall.card ≤ R.card := by
    have hinj : (Rall.image fun j : Fin C.gates.length => N + N + j.val).card = Rall.card := by
      apply Finset.card_image_of_injective
      intro a b hab
      dsimp only at hab
      exact Fin.ext (by omega)
    calc S1.card + Rall.card
        = S1.card + (Rall.image fun j : Fin C.gates.length => N + N + j.val).card := by rw [hinj]
      _ = (S1 ∪ (Rall.image fun j : Fin C.gates.length => N + N + j.val)).card := (Finset.card_union_of_disjoint hdisj_SR).symm
      _ ≤ R.card := Finset.card_le_card hsub_union
  have hR_sub : R ⊆ ((G_P N C p).image (sideL N C)) ∪ Rall.biUnion (reachStepP N C) := by
    intro w hw
    rcases foldReach_decomp N C (reachStepP N C) (List.finRange C.gates.length) ((G_P N C p).image (sideL N C)) w hw with
      hr | ⟨j, _, hjR, hwj⟩
    · exact Finset.mem_union_left _ hr
    · have h2 : 2 ≤ (Lset N C (N + N + j.val)).card := by
        by_contra hlt
        simp [reachStepP, hlt] at hwj
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjR, h2⟩, hwj⟩)
  have hRall_split : Rall.card = (R_or_P N C p).card + Rand.card := by
    have hU : Rall = R_or_P N C p ∪ Rand := by
      ext j
      simp only [Rall, R_or_P, Rand, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        have hmem : C.gates[j.val] ∈ C.gates := List.getElem_mem j.isLt
        rcases (hm C.gates[j.val] hmem).1 with hop | hop
        · exact Or.inr ⟨hj, hop⟩
        · exact Or.inl ⟨hop, hj.1, hj.2⟩
      · rintro (h | h)
        · exact ⟨h.2.1, h.2.2⟩
        · exact h.1
    have hD : Disjoint (R_or_P N C p) Rand := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [R_or_P, Rand, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
      have hop1 : C.gates[j.val].op = GateOp.or := hj1.1
      have hop2 : C.gates[j.val].op = GateOp.and := hj2.2
      rw [hop1] at hop2
      exact GateOp.noConfusion hop2
    rw [hU, Finset.card_union_of_disjoint hD]
  have hR_upper : R.card ≤ (G_P N C p).card + 2 * (R_or_P N C p).card + Rand.card := by
    have hsplit : Rall.biUnion (reachStepP N C) = (R_or_P N C p).biUnion (reachStepP N C) ∪ Rand.biUnion (reachStepP N C) := by
      ext x
      simp only [Rall, R_or_P, Rand, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, ⟨h1, h2⟩, hx⟩
        have hmem : C.gates[j.val] ∈ C.gates := List.getElem_mem j.isLt
        rcases (hm C.gates[j.val] hmem).1 with hop | hop
        · exact Or.inr ⟨j, ⟨⟨h1, h2⟩, hop⟩, hx⟩
        · exact Or.inl ⟨j, ⟨hop, h1, h2⟩, hx⟩
      · rintro (⟨j, ⟨hop, h1, h2⟩, hx⟩ | ⟨j, ⟨⟨h1, h2⟩, _⟩, hx⟩)
        · exact ⟨j, ⟨h1, h2⟩, hx⟩
        · exact ⟨j, ⟨h1, h2⟩, hx⟩
    have hstep_or : ∀ j ∈ R_or_P N C p, (reachStepP N C j).card ≤ 2 := by
      intro j hj
      obtain ⟨a, b, hin, _, _⟩ := hord j.val C.gates[j.val] (List.getElem?_eq_getElem j.isLt)
      have hop : C.gates[j.val].op = GateOp.or := (Finset.mem_filter.mp hj).2.1
      simp only [reachStepP, hop, hin, ↓reduceIte]
      split_ifs
      · have hle : [a, b].toFinset.card ≤ [a, b].length := List.toFinset_card_le [a, b]
        simpa using hle
      · simp
    have hstep_and : ∀ j ∈ Rand, (reachStepP N C j).card ≤ 1 := by
      intro j hj
      have hop : C.gates[j.val].op = GateOp.and := (Finset.mem_filter.mp hj).2
      have hne : GateOp.and ≠ GateOp.or := fun h => GateOp.noConfusion h
      simp only [reachStepP, hop, hne, ↓reduceIte]
      split_ifs <;> simp
    calc R.card
        ≤ (((G_P N C p).image (sideL N C)) ∪ Rall.biUnion (reachStepP N C)).card := Finset.card_le_card hR_sub
      _ ≤ ((G_P N C p).image (sideL N C)).card + (Rall.biUnion (reachStepP N C)).card := Finset.card_union_le _ _
      _ ≤ (G_P N C p).card + ((R_or_P N C p).biUnion (reachStepP N C) ∪ Rand.biUnion (reachStepP N C)).card := by
            rw [hsplit]
            exact Nat.add_le_add Finset.card_image_le le_rfl
      _ ≤ (G_P N C p).card + ((R_or_P N C p).biUnion (reachStepP N C)).card + (Rand.biUnion (reachStepP N C)).card := by
            have := Finset.card_union_le ((R_or_P N C p).biUnion (reachStepP N C)) (Rand.biUnion (reachStepP N C))
            omega
      _ ≤ (G_P N C p).card + (∑ j ∈ R_or_P N C p, (reachStepP N C j).card) + (∑ j ∈ Rand, (reachStepP N C j).card) := by
            have h1 := Finset.card_biUnion_le (s := R_or_P N C p) (t := reachStepP N C)
            have h2 := Finset.card_biUnion_le (s := Rand) (t := reachStepP N C)
            omega
      _ ≤ (G_P N C p).card + (∑ _ ∈ R_or_P N C p, 2) + (∑ _ ∈ Rand, 1) := by
            have h1 := Finset.sum_le_sum hstep_or
            have h2 := Finset.sum_le_sum hstep_and
            omega
      _ = (G_P N C p).card + 2 * (R_or_P N C p).card + Rand.card := by
            simp [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

theorem main (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 100 < q) (hN : N = q ^ 2 + q + 1)
    (hlines : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    (hm : Monotone2 C) (hout_lt : C.output < N + N + C.gates.length)
    (hord : ∀ i g, C.gates[i]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i)
    (hacc : ∀ p l : Fin N, I p l → circuitFun (N + N) C (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) = true)
    (hrej : ∀ x : Fin (N + N) → Bool,
      Fintype.card { l : Fin N // x (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N + N) C x = false)
    (U : Finset ℕ) (_ : U ⊆ Finset.range C.size) (hU0 : U.card = 0)
    (hUexact : ∀ i g, C.gates[i]? = some g → (i ∈ U ↔
      g.op = GateOp.and ∧
      ((∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
          (C.wires (List.ofFn x ++ List.replicate N false)).getD w false ≠
          (C.wires (List.ofFn x ++ List.replicate N true)).getD w false) ∨
       ∀ w ∈ g.inputs, ∃ x : Fin N → Bool,
          (C.wires (List.replicate N false ++ List.ofFn x)).getD w false ≠
          (C.wires (List.replicate N true ++ List.ofFn x)).getD w false))) :
    N * q ≤ 100 * C.size := by
  classical
  have hUemp : U = ∅ := Finset.card_eq_zero.mp hU0
  have hno_all : ∀ k : Fin C.gates.length, C.gates[k.val].op = GateOp.and →
      ¬ ((∀ w ∈ C.gates[k.val].inputs, DepL N C w) ∨ (∀ w ∈ C.gates[k.val].inputs, DepP N C w)) := by
    intro k hop hdep
    have hkU : k.val ∈ U := (hUexact k.val C.gates[k.val] (List.getElem?_eq_getElem k.isLt)).2 ⟨hop, by
      rcases hdep with hL | hP
      · exact Or.inl fun w hw => (depL_iff_wire N C w).1 (hL w hw)
      · exact Or.inr fun w hw => (depP_iff_wire N C w).1 (hP w hw)⟩
    rw [hUemp] at hkU
    exact Finset.notMem_empty k.val hkU
  have hpair_eq : ∀ p l : Fin N, inpBool (ePt p) (ePt l) =
      fun z : Fin (N + N) => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l) := by
    intro p l
    funext z
    refine Fin.addCases (motive := fun z => inpBool (ePt p) (ePt l) z = decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) ?_ ?_ z
    · intro u
      simp only [inpBool, Fin.addCases_left, ePt, decide_eq_decide]
      constructor
      · intro hu; left; subst hu; rfl
      · rintro (h | h)
        · exact Fin.ext (by have := congrArg Fin.val h; simp at this; exact this)
        · exact False.elim (by have := congrArg Fin.val h; simp at this; omega)
    · intro v
      simp only [inpBool, Fin.addCases_right, ePt, decide_eq_decide]
      constructor
      · intro hv; right; subst hv; rfl
      · rintro (h | h)
        · exact False.elim (by have := congrArg Fin.val h; simp at this; omega)
        · exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
  have hacc_val : ∀ p l : Fin N, I p l → val N C C.output (ePt p) (ePt l) = true := by
    intro p l hI
    rw [← eval_val, ← ofFn_inpBool, hpair_eq]
    exact hacc p l hI
  have hp_out : ∀ p' : Fin N, val N C C.output (ePt p') zFn = false := by
    intro p'
    rw [← eval_val, ← ofFn_inpBool]
    apply hrej (inpBool (ePt p') zFn)
    · have h0 : { l : Fin N // inpBool (ePt p') (zFn (N := N)) (Fin.natAdd N l) = true } → False := by
        rintro ⟨l, hl⟩
        simp only [inpBool, Fin.addCases_right, zFn] at hl
        exact Bool.noConfusion hl
      rw [Fintype.card_eq_zero_iff.mpr ⟨fun x => False.elim (h0 x)⟩]
      omega
    · rintro ⟨p1, l1, _, _, hl1⟩
      simp only [inpBool, Fin.addCases_right, zFn] at hl1
      exact Bool.noConfusion hl1
  have hl_out : ∀ l' : Fin N, val N C C.output zFn (ePt l') = false := by
    intro l'
    rw [← eval_val, ← ofFn_inpBool]
    apply hrej (inpBool zFn (ePt l'))
    · have hc : Fintype.card { l : Fin N // inpBool (zFn (N := N)) (ePt l') (Fin.natAdd N l) = true } ≤ 1 := by
        rw [Fintype.card_le_one_iff_subsingleton]
        refine ⟨fun a b => ?_⟩
        ext1
        have ha : ePt l' a.1 = true := by simpa only [inpBool, Fin.addCases_right] using a.2
        have hb : ePt l' b.1 = true := by simpa only [inpBool, Fin.addCases_right] using b.2
        exact (of_decide_eq_true ha).trans (of_decide_eq_true hb).symm
      omega
    · rintro ⟨p1, _, _, hp1, _⟩
      simp only [inpBool, Fin.addCases_left, zFn] at hp1
      exact Bool.noConfusion hp1
  have hsound_pair : ∀ p l : Fin N, val N C C.output (ePt p) (ePt l) = true → I p l := by
    intro p l hval
    by_contra hnI
    have hfalse : val N C C.output (ePt p) (ePt l) = false := by
      rw [← eval_val, ← ofFn_inpBool]
      apply hrej (inpBool (ePt p) (ePt l))
      · have hc : Fintype.card { l' : Fin N // inpBool (ePt p) (ePt l) (Fin.natAdd N l') = true } ≤ 1 := by
          rw [Fintype.card_le_one_iff_subsingleton]
          refine ⟨fun a b => ?_⟩
          ext1
          have ha : ePt l a.1 = true := by simpa only [inpBool, Fin.addCases_right] using a.2
          have hb : ePt l b.1 = true := by simpa only [inpBool, Fin.addCases_right] using b.2
          exact (of_decide_eq_true ha).trans (of_decide_eq_true hb).symm
        omega
      · rintro ⟨p1, l1, hI1, hp1, hl1⟩
        have hp1' : p1 = p := of_decide_eq_true (by simpa only [inpBool, Fin.addCases_left, ePt] using hp1)
        have hl1' : l1 = l := of_decide_eq_true (by simpa only [inpBool, Fin.addCases_right, ePt] using hl1)
        rw [hp1', hl1'] at hI1
        exact hnI hI1
    rw [hval] at hfalse
    exact Bool.noConfusion hfalse
  have hno_c4 : ∀ p1 p2 l1 l2 : Fin N, p1 ≠ p2 → l1 ≠ l2 → ¬ (I p1 l1 ∧ I p1 l2 ∧ I p2 l1 ∧ I p2 l2) := by
    intro p1 p2 l1 l2 hp hl ⟨h11, h12, h21, h22⟩
    obtain ⟨l0, _, hu⟩ := huniq p1 p2 hp
    have e1 := hu l1 ⟨h11, h21⟩
    have e2 := hu l2 ⟨h12, h22⟩
    exact hl (e1.trans e2.symm)
  have hinc_cov : ∀ p l : Fin N, I p l → p ∈ CoveredL N C l ∨ l ∈ CoveredP N C p := by
    intro p l hI
    obtain ⟨k, hg, hvk⟩ := descend_good N C hm hout_lt hord hp_out hl_out p l C.output
      (fun _ _ h => h) (hacc_val p l hI)
    obtain ⟨_, _, _, _, _, _, _, _, hiff, hrect, hPne, hLne⟩ :=
      good_sides N I C hm hord hno_all hsound_pair k hg
    obtain ⟨hpP, hlL⟩ := (hiff p l).1 hvk
    by_cases h2 : 2 ≤ (Pset N C (sideP N C k)).card
    · have hLle1 : (Lset N C (sideL N C k)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro l1 hl1 l2 hl2
        by_contra hne
        obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Pset N C (sideP N C k)).card)
        exact hno_c4 p1 p2 l1 l2 hpne hne ⟨hrect p1 hp1 l1 hl1, hrect p1 hp1 l2 hl2, hrect p2 hp2 l1 hl1, hrect p2 hp2 l2 hl2⟩
      have hLeq : Lset N C (sideL N C k) = {l} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hlL, fun l' hl' => Finset.card_le_one.mp hLle1 l' hl' l hlL⟩
      left
      simp only [CoveredL, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg, h2, hLeq⟩, hpP⟩
    · have hPpos : 0 < (Pset N C (sideP N C k)).card := Finset.card_pos.mpr hPne
      have hP1 : (Pset N C (sideP N C k)).card = 1 := by omega
      have hPeq : Pset N C (sideP N C k) = {p} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hpP, fun p' hp' => Finset.card_le_one.mp (by omega : (Pset N C (sideP N C k)).card ≤ 1) p' hp' p hpP⟩
      right
      simp only [CoveredP, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg, hP1, hPeq⟩, hlL⟩
  let incSet : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2
  have hinc_lower : N * (q + 1) ≤ incSet.card := by
    have hsplit : incSet = (Finset.univ : Finset (Fin N)).biUnion
        (fun l => (Finset.univ.filter fun p : Fin N => I p l).map
          ⟨fun p => (p, l), fun p1 p2 h => (Prod.mk.inj h).1⟩) := by
      ext ⟨p, l⟩
      simp only [incSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨fun h => ⟨l, p, h, rfl⟩, fun ⟨_, _, h, h1⟩ => by cases h1; exact h⟩
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin N))
        (fun l => (Finset.univ.filter fun p : Fin N => I p l).map
          ⟨fun p => (p, l), fun p1 p2 h => (Prod.mk.inj h).1⟩) := by
      intro l1 _ l2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro ⟨p, l⟩ h1 h2
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with ⟨_, _, h1e⟩
      rcases h2 with ⟨_, _, h2e⟩
      have hle : l1 = l2 := congrArg Prod.snd (h1e.trans h2e.symm)
      exact hne hle
    rw [hsplit, Finset.card_biUnion hdisj]
    have hsum : ∑ l : Fin N, ((Finset.univ.filter fun p : Fin N => I p l).map
        ⟨fun p => (p, l), fun p1 p2 h => (Prod.mk.inj h).1⟩).card = N * (q + 1) := by
      calc ∑ l : Fin N, ((Finset.univ.filter fun p : Fin N => I p l).map
              ⟨fun p => (p, l), fun p1 p2 h => (Prod.mk.inj h).1⟩).card
          = ∑ l : Fin N, (Finset.univ.filter fun p : Fin N => I p l).card := by
            refine Finset.sum_congr rfl fun l _ => Finset.card_map _
        _ = ∑ l : Fin N, Fintype.card { p : Fin N // I p l } := by
            refine Finset.sum_congr rfl fun l _ => (Fintype.card_subtype _).symm
        _ = ∑ _ : Fin N, (q + 1) := Finset.sum_congr rfl fun l _ => hlines l
        _ = N * (q + 1) := by simp
    omega
  have hinc_upper : incSet.card ≤
      (∑ l : Fin N, (CoveredL N C l).card) + (∑ p : Fin N, (CoveredP N C p).card) := by
    have hsub : incSet ⊆
        ((Finset.univ : Finset (Fin N)).biUnion (fun l => (CoveredL N C l).map
          ⟨fun p => (p, l), fun p1 p2 h => (Prod.mk.inj h).1⟩)) ∪
        ((Finset.univ : Finset (Fin N)).biUnion (fun p => (CoveredP N C p).map
          ⟨fun l => (p, l), fun l1 l2 h => (Prod.mk.inj h).2⟩)) := by
      intro ⟨p, l⟩ he
      simp only [incSet, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rcases hinc_cov p l he with hp | hl
      · apply Finset.mem_union_left
        exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, Finset.mem_map.mpr ⟨p, hp, rfl⟩⟩
      · apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, Finset.mem_map.mpr ⟨l, hl, rfl⟩⟩
    calc incSet.card
        ≤ (((Finset.univ : Finset (Fin N)).biUnion (fun l => (CoveredL N C l).map
              ⟨fun p => (p, l), fun p1 p2 h => (Prod.mk.inj h).1⟩)) ∪
            ((Finset.univ : Finset (Fin N)).biUnion (fun p => (CoveredP N C p).map
              ⟨fun l => (p, l), fun l1 l2 h => (Prod.mk.inj h).2⟩))).card := Finset.card_le_card hsub
      _ ≤ ((Finset.univ : Finset (Fin N)).biUnion (fun l => (CoveredL N C l).map
              ⟨fun p => (p, l), fun p1 p2 h => (Prod.mk.inj h).1⟩)).card +
            ((Finset.univ : Finset (Fin N)).biUnion (fun p => (CoveredP N C p).map
              ⟨fun l => (p, l), fun l1 l2 h => (Prod.mk.inj h).2⟩)).card := Finset.card_union_le _ _
      _ ≤ (∑ l : Fin N, ((CoveredL N C l).map ⟨fun p => (p, l), fun p1 p2 h => (Prod.mk.inj h).1⟩).card) +
            (∑ p : Fin N, ((CoveredP N C p).map ⟨fun l => (p, l), fun l1 l2 h => (Prod.mk.inj h).2⟩).card) := by
            exact Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ = (∑ l : Fin N, (CoveredL N C l).card) + (∑ p : Fin N, (CoveredP N C p).card) := by
            simp [Finset.card_map]
  have hcovL_sum : ∑ l : Fin N, (CoveredL N C l).card ≤ ∑ l : Fin N, ((G_L N C l).card + (R_or_L N C l).card) :=
    Finset.sum_le_sum fun l _ => coveredL_bound N I C hm hord hno_all hsound_pair l
  have hcovP_sum : ∑ p : Fin N, (CoveredP N C p).card ≤ ∑ p : Fin N, ((G_P N C p).card + (R_or_P N C p).card) :=
    Finset.sum_le_sum fun p _ => coveredP_bound N I C hm hord hno_all hsound_pair p
  have hd_GL : Set.PairwiseDisjoint (Finset.univ : Finset (Fin N)) (G_L N C) := by
    intro l1 _ l2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [G_L, Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
    have heq : ({l1} : Finset (Fin N)) = {l2} := hk1.2.2.symm.trans hk2.2.2
    exact hne (Finset.singleton_injective heq)
  have hd_GP : Set.PairwiseDisjoint (Finset.univ : Finset (Fin N)) (G_P N C) := by
    intro p1 _ p2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [G_P, Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
    have heq : ({p1} : Finset (Fin N)) = {p2} := hk1.2.2.symm.trans hk2.2.2
    exact hne (Finset.singleton_injective heq)
  have hd_OL : Set.PairwiseDisjoint (Finset.univ : Finset (Fin N)) (R_or_L N C) := by
    intro l1 _ l2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [R_or_L, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
    have h2 : 2 ≤ (Pset N C (N + N + j.val)).card := hj1.2.2
    obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Pset N C (N + N + j.val)).card)
    have hI1 := (InvL_ReachL N I C hm hord hno_all hsound_pair l1 (N + N + j.val) hj1.2.1).2.2.2
    have hI2 := (InvL_ReachL N I C hm hord hno_all hsound_pair l2 (N + N + j.val) hj2.2.1).2.2.2
    exact hno_c4 p1 p2 l1 l2 hpne hne ⟨hI1 p1 hp1, hI2 p1 hp1, hI1 p2 hp2, hI2 p2 hp2⟩
  have hd_OP : Set.PairwiseDisjoint (Finset.univ : Finset (Fin N)) (R_or_P N C) := by
    intro p1 _ p2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [R_or_P, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
    have h2 : 2 ≤ (Lset N C (N + N + j.val)).card := hj1.2.2
    obtain ⟨l1, hl1, l2, hl2, hlne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Lset N C (N + N + j.val)).card)
    have hI1 := (InvP_ReachP N I C hm hord hno_all hsound_pair p1 (N + N + j.val) hj1.2.1).2.2.2
    have hI2 := (InvP_ReachP N I C hm hord hno_all hsound_pair p2 (N + N + j.val) hj2.2.1).2.2.2
    exact hno_c4 p1 p2 l1 l2 hne hlne ⟨hI1 l1 hl1, hI1 l2 hl2, hI2 l1 hl1, hI2 l2 hl2⟩
  let allGL := (Finset.univ : Finset (Fin N)).biUnion (G_L N C)
  let allGP := (Finset.univ : Finset (Fin N)).biUnion (G_P N C)
  let allOL := (Finset.univ : Finset (Fin N)).biUnion (R_or_L N C)
  let allOP := (Finset.univ : Finset (Fin N)).biUnion (R_or_P N C)
  have hd_GL_GP : Disjoint allGL allGP := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [Finset.mem_biUnion] at hk1 hk2
    rcases hk1 with ⟨l, _, hl⟩
    rcases hk2 with ⟨p, _, hp⟩
    have h2 : 2 ≤ (Pset N C (sideP N C k)).card := (Finset.mem_filter.mp hl).2.2.1
    have h1 : (Pset N C (sideP N C k)).card = 1 := (Finset.mem_filter.mp hp).2.2.1
    omega
  have hd_OL_OP : Disjoint allOL allOP := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    rw [Finset.mem_biUnion] at hj1 hj2
    rcases hj1 with ⟨l, _, hl⟩
    rcases hj2 with ⟨p, _, hp⟩
    have hjL : N + N + j.val ∈ ReachL N C l := (Finset.mem_filter.mp hl).2.2.1
    have h2L : 2 ≤ (Lset N C (N + N + j.val)).card := (Finset.mem_filter.mp hp).2.2.2
    have hLe := (InvL_ReachL N I C hm hord hno_all hsound_pair l (N + N + j.val) hjL).2.2.1
    rw [hLe] at h2L
    simp at h2L
  have hd_and_or : Disjoint (allGL ∪ allGP) (allOL ∪ allOP) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have hop_and : C.gates[j.val].op = GateOp.and := by
      rcases Finset.mem_union.1 hj1 with h1 | h2
      · rcases Finset.mem_biUnion.1 h1 with ⟨l, _, hl⟩
        exact (Finset.mem_filter.mp hl).2.1.1
      · rcases Finset.mem_biUnion.1 h2 with ⟨p, _, hp⟩
        exact (Finset.mem_filter.mp hp).2.1.1
    have hop_or : C.gates[j.val].op = GateOp.or := by
      rcases Finset.mem_union.1 hj2 with h1 | h2
      · rcases Finset.mem_biUnion.1 h1 with ⟨l, _, hl⟩
        exact (Finset.mem_filter.mp hl).2.1
      · rcases Finset.mem_biUnion.1 h2 with ⟨p, _, hp⟩
        exact (Finset.mem_filter.mp hp).2.1
    rw [hop_and] at hop_or
    exact GateOp.noConfusion hop_or
  have htotal_gates : (allGL.card + allGP.card) + (allOL.card + allOP.card) ≤ C.size := by
    calc (allGL.card + allGP.card) + (allOL.card + allOP.card)
        = (allGL ∪ allGP).card + (allOL ∪ allOP).card := by
            rw [Finset.card_union_of_disjoint hd_GL_GP, Finset.card_union_of_disjoint hd_OL_OP]
      _ = ((allGL ∪ allGP) ∪ (allOL ∪ allOP)).card := (Finset.card_union_of_disjoint hd_and_or).symm
      _ ≤ (Finset.univ : Finset (Fin C.gates.length)).card := Finset.card_le_univ _
      _ = C.size := by simp [Circuit.size]
  have hallGL_eq : allGL.card = ∑ l : Fin N, (G_L N C l).card := Finset.card_biUnion hd_GL
  have hallGP_eq : allGP.card = ∑ p : Fin N, (G_P N C p).card := Finset.card_biUnion hd_GP
  have hallOL_eq : allOL.card = ∑ l : Fin N, (R_or_L N C l).card := Finset.card_biUnion hd_OL
  have hallOP_eq : allOP.card = ∑ p : Fin N, (R_or_P N C p).card := Finset.card_biUnion hd_OP
  have hsum_L : ∑ l : Fin N, ((G_L N C l).card + (R_or_L N C l).card) = allGL.card + allOL.card := by
    rw [Finset.sum_add_distrib, hallGL_eq, hallOL_eq]
  have hsum_P : ∑ p : Fin N, ((G_P N C p).card + (R_or_P N C p).card) = allGP.card + allOP.card := by
    rw [Finset.sum_add_distrib, hallGP_eq, hallOP_eq]
  have hNq : N * (q + 1) ≤ C.size := by omega
  have hfinal : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (Nat.le_succ q)
  have hfinal2 : C.size ≤ 100 * C.size := Nat.le_mul_of_pos_left C.size (by omega)
  omega

end PEqualNP.Outside.L_meta_2868

theorem PEqualNP.Outside.L_meta_2868 : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, x16.card = (0 : ℕ) → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  dsimp only
  intro q N I _ C hq hN hlines huniq hm hout_lt hord hacc hrej U hUsub hU0 hUexact _
  exact PEqualNP.Outside.L_meta_2868.main q N I C hq hN hlines huniq hm hout_lt hord hacc hrej U hUsub hU0 hUexact
