import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_1657
-- Circuit evaluation and patch identities adapted from the checked L-meta-1513 proof.
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

def patchC (gates : List Gate) (j : ℕ) : Circuit :=
  ⟨gates.set j ⟨GateOp.or, []⟩, 0⟩

lemma patchC_size (gates : List Gate) (j : ℕ) : (patchC gates j).size = gates.length := by
  simp [patchC, Circuit.size]

lemma patchC_false {n : ℕ} (gates : List Gate) (j : Fin gates.length) (x : Fin n → Bool) :
    value (patchC gates j.val) x (n + j.val) = false := by
  have h := gate_value (patchC gates j.val) x (n + j.val) (by omega)
    (by rw [patchC_size]; omega)
  simp only at h
  rw [h]
  simp [patchC, GateOp.eval]

lemma patchC_other {n : ℕ} (gates : List Gate) (j : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + j) :
    value (patchC gates j) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (patchC gates j) x r else false) := by
  have h := gate_value (patchC gates j) x w hn (by rw [patchC_size]; exact hw)
  simp only at h
  rw [h]
  have same : (patchC gates j).gates[w - n]'(by simp [patchC]; omega) =
      gates[w - n]'(by omega) := by
    simp only [patchC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [same]

lemma originalGateValue {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma patchEvalCongr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

lemma patchC_eq {n : ℕ} (gates : List Gate) (j : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (hjFalse : value ⟨gates, o⟩ x (n + j.val) = false) (w : ℕ) :
    value (patchC gates j.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h₁ := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h₂ := input_value (patchC gates j.val) x ⟨w, hn⟩
      simp only at h₁ h₂
      rw [h₁, h₂]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + j.val
      · rw [hne, hjFalse]
        exact patchC_false gates j x
      · rw [originalGateValue gates o x w (by omega) hw,
          patchC_other gates j.val x w (by omega) hw hne]
        apply patchEvalCongr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (patchC gates j.val) x w (by rw [patchC_size]; omega)]

lemma not_false_of_input_true {n : ℕ} (gates : List Gate) (j h : Fin gates.length)
    (o : ℕ) (x : Fin n → Bool)
    (hop : (gates.get j).op = GateOp.not) (hlt : h < j)
    (hread : ∃ r : List ℕ, (gates.get j).inputs = (n + h.val) :: r)
    (hhTrue : value ⟨gates, o⟩ x (n + h.val) = true) :
    value ⟨gates, o⟩ x (n + j.val) = false := by
  obtain ⟨r, hr⟩ := hread
  have hj : n + j.val < n + gates.length := by omega
  have hw : n + h.val < n + j.val := by exact Nat.add_lt_add_left hlt n
  have he := originalGateValue gates o x (n + j.val) (by omega) hj
  simp only [Nat.add_sub_cancel_left] at he
  rw [he]
  change (gates.get j).op.eval ((gates.get j).inputs.map fun w =>
    if w < n + j.val then value ⟨gates, o⟩ x w else false) = false
  rw [hop, hr]
  simp [hw, hhTrue, GateOp.eval]


lemma not_true_of_input_false {n : ℕ} (gates : List Gate) (j h : Fin gates.length)
    (o : ℕ) (x : Fin n → Bool)
    (hop : (gates.get j).op = GateOp.not) (hlt : h < j)
    (hread : ∃ r : List ℕ, (gates.get j).inputs = (n + h.val) :: r)
    (hhTrue : value ⟨gates, o⟩ x (n + h.val) = false) :
    value ⟨gates, o⟩ x (n + j.val) = true := by
  obtain ⟨r, hr⟩ := hread
  have hj : n + j.val < n + gates.length := by omega
  have hw : n + h.val < n + j.val := by exact Nat.add_lt_add_left hlt n
  have he := originalGateValue gates o x (n + j.val) (by omega) hj
  simp only [Nat.add_sub_cancel_left] at he
  rw [he]
  change (gates.get j).op.eval ((gates.get j).inputs.map fun w =>
    if w < n + j.val then value ⟨gates, o⟩ x w else false) = true
  rw [hop, hr]
  simp [hw, hhTrue, GateOp.eval]


lemma op_mono (g : Gate) (op : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f k : ℕ → Bool) (le : ∀ r ∈ g.inputs, f r = true → k r = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map k) = true := by
  rcases op with op | op
  · simp only [op, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hb
    exact le r hm (hx _ (List.mem_map.mpr ⟨r,hm,rfl⟩))
  · simp only [op, GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨_,hb,rfl⟩
    obtain ⟨r,hm,hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r,hm,rfl⟩, le r hm hv⟩

lemma patch_le {n : ℕ} (gs : List Gate) (j : Fin gs.length)
    (good : ∀ i : Fin gs.length, i ≠ j →
      (gs.get i).op = GateOp.and ∨ (gs.get i).op = GateOp.or)
    (x : Fin n → Bool) (w : ℕ) :
    value (patchC gs j) x w = true → value ⟨gs,0⟩ x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · intro lit
      exact ((input_value (patchC gs j) x ⟨w,hn⟩).trans (input_value ⟨gs,0⟩ x ⟨w,hn⟩).symm).symm.trans lit
    by_cases hw : w < n + gs.length
    · by_cases he : w = n + j.val
      · simp [he, patchC_false]
      rw [patchC_other _ _ _ _ (by omega) hw he, originalGateValue _ _ _ _ (by omega) hw]
      apply op_mono
      · exact good ⟨w-n,by omega⟩ (fun e => he (by have := congrArg Fin.val e; simp at this; omega))
      · intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · simp [missing_value (patchC gs j) x w (by rw [patchC_size]; omega)]

lemma reader_off {n : ℕ} (gs : List Gate) (j i : Fin gs.length) (x : Fin n → Bool)
    (ne : j ≠ i) (op : (gs.get i).op = GateOp.and)
    (reads : n + j.val ∈ (gs.get i).inputs) :
    value (patchC gs j) x (n+i.val) = false := by
  have h := patchC_other gs j.val x (n+i.val) (by omega) (by omega)
    (fun e => ne (Fin.ext (by omega)))
  simp only [Nat.add_sub_cancel_left] at h
  rw [h]
  apply Bool.eq_false_iff.mpr
  simp only [List.get_eq_getElem] at op reads
  intro all
  simp only [op, GateOp.eval, List.all_eq_true, id_eq] at all
  have lit := all _ (List.mem_map.mpr ⟨n+j.val,reads,rfl⟩)
  simp [patchC_false] at lit

lemma agree_except {n : ℕ} (gs : List Gate) (j : Fin gs.length) (x : Fin n → Bool)
    (good : ∀ i : Fin gs.length, i ≠ j →
      (gs.get i).op = GateOp.and ∨ (gs.get i).op = GateOp.or)
    (off : ∀ i : Fin gs.length, n+j.val ∈ (gs.get i).inputs →
      value ⟨gs,0⟩ x (n+i.val) = false)
    (w : ℕ) (ne : w ≠ n+j.val) :
    value (patchC gs j) x w = value ⟨gs,0⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · exact (input_value (patchC gs j) x ⟨w,hn⟩).trans (input_value ⟨gs,0⟩ x ⟨w,hn⟩).symm
    by_cases hw : w < n + gs.length
    · let i : Fin gs.length := ⟨w-n,by omega⟩
      have wi : n+i.val = w := by dsimp [i]; omega
      by_cases reads : n+j.val ∈ (gs.get i).inputs
      · have orig := off i reads
        rw [wi] at orig
        have le := patch_le gs j good x w
        rw [orig] at le ⊢
        exact Bool.eq_false_iff.mpr (fun h => Bool.noConfusion (le h))
      rw [patchC_other _ _ _ _ (by omega) hw ne, originalGateValue _ _ _ _ (by omega) hw]
      apply patchEvalCongr
      intro r mem
      by_cases hr : r < w
      · simpa [hr] using ih r hr (fun eq => reads (eq ▸ mem))
      · simp [hr]
    · rw [missing_value _ _ _ (by rw [patchC_size]; omega),
          missing_value _ _ _ (by simp only [Circuit.size]; omega)]

end PEqualNP.Outside.L_meta_1657

open PEqualNP.Outside.L_meta_1657

theorem PEqualNP.Outside.L_meta_1657 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (va vb vc sa sb sc : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    (∀ t : Fin N, ¬ (va ∈ L t ∧ vb ∈ L t ∧ vc ∈ L t)) →
    vb ∈ L sa → vc ∈ L sa → vc ∈ L sb → va ∈ L sb → va ∈ L sc → vb ∈ L sc →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    ∀ ev ev' : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w⟩ (List.ofFn x)) →
    (∀ p : Fin N, ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = true ↔ (p = va ∨ p = vb ∨ p = vc)) →
    (∀ (i : Fin gates.length) (P : Fin N), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true →
      (P ∈ L sa ∨ P ∈ L sb ∨ P ∈ L sc) ∧ P ≠ va ∧ P ≠ vb ∧ P ≠ vc) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = true → ev w x = true) ∧ (∀ (w : ℕ) (x : Fin N → Bool), ev (N + (h : ℕ)) x = true → ev' w x = ev w x) ∧
    (∀ (i : Fin gates.length) (x : Fin N → Bool), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev' (N + (i : ℕ)) x = false) ∧
    (∀ (t P : Fin N), P ∈ L t → ev' (o t) (fun v : Fin N => decide (v = P)) = false → ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true) ∧
    ∀ t : Fin N, ∀ v ∈ ({va, vb, vc} : Finset (Fin N)), v ∈ L t → ev' (o t) (fun uu : Fin N => decide (uu = v)) = true := by
  intro q N L a b c sa sb sc hq hN cards _ _ _ _ _ _ _ _ _ gs o j h law _ jop unique earlier read outputs readers ev ev' he he' stars _
  let s (p : Fin N) := fun v : Fin N => decide (v = p)
  have orig (w : ℕ) (x : Fin N → Bool) : ev w x = value ⟨gs,0⟩ x w := he w x
  have patch (w : ℕ) (x : Fin N → Bool) : ev' w x = value (patchC gs j) x w := he' w x
  have good (i : Fin gs.length) (ne : i ≠ j) :
      (gs.get i).op = GateOp.and ∨ (gs.get i).op = GateOp.or := by
    rcases (law _ (List.get_mem gs i)).1 with v | v | v
    · exact Or.inl v
    · exact Or.inr v
    · exact False.elim (ne (unique i v))
  have line (t P : Fin N) : ev (o t) (s P) = decide (P ∈ L t) := by
    rw [he, outputs]
    simp [s]
  have switch (w : ℕ) (x : Fin N → Bool) (on : ev (N+h.val) x = true) :
      ev' w x = ev w x := by
    rw [patch,orig]
    exact patchC_eq gs j 0 x (not_false_of_input_true gs j h 0 x jop earlier read ((orig _ _).symm.trans on)) w
  have nz (t : Fin N) : o t ≠ N+j.val := by
    intro eq
    let triple : Finset (Fin N) := {a,b,c}
    have small : triple.card ≤ 3 := by
      dsimp [triple]
      calc
        _ ≤ (insert b ({c} : Finset (Fin N))).card + 1 := Finset.card_insert_le _ _
        _ ≤ (({c} : Finset (Fin N)).card + 1) + 1 := by have := Finset.card_insert_le b ({c} : Finset (Fin N)); omega
        _ = 3 := by simp
    have room : ¬ (Finset.univ : Finset (Fin N)) ⊆ L t ∪ triple := by
      intro cover
      have count := Finset.card_le_card cover
      have union := Finset.card_union_le (L t) triple
      simp only [Finset.card_univ,Fintype.card_fin] at count
      rw [cards] at union
      nlinarith
    obtain ⟨P,_,out⟩ := Finset.not_subset.mp room
    have outside : P ∉ L t := fun ht => out (Finset.mem_union_left _ ht)
    have nonvertex : ¬ (P = a ∨ P = b ∨ P = c) := by
      intro hv
      exact out (Finset.mem_union_right _ (by simpa [triple] using hv))
    have off : ev (N+h.val) (s P) = false := Bool.eq_false_iff.mpr (fun hp => nonvertex ((stars P).mp hp))
    have lit := not_true_of_input_false gs j h 0 (s P) jop earlier read ((orig _ _).symm.trans off)
    have dark := line t P
    rw [eq,orig] at dark
    simp [outside,lit] at dark
  refine ⟨?_,switch,?_,?_,?_⟩
  · intro w x
    rw [patch,orig]
    exact patch_le gs j good x w
  · intro i x mem
    rw [patch]
    apply reader_off gs j i x _ (readers i mem) mem
    intro eq
    subst i
    have contra := (readers j mem).symm.trans jop
    cases contra
  · intro t P hp lost
    by_contra none
    have off (i : Fin gs.length) (mem : N+j.val ∈ (gs.get i).inputs) :
        value ⟨gs,0⟩ (s P) (N+i.val) = false := by
      rw [← orig]
      exact Bool.eq_false_iff.mpr (fun hit => none ⟨i,mem,hit⟩)
    have agree := agree_except gs j (s P) good off (o t) (nz t)
    change ev' (o t) (s P) = false at lost
    rw [patch,agree,← orig,line] at lost
    simp [hp] at lost
  · intro t v hv hvline
    have on := (stars v).mpr (by simpa using hv)
    change ev' (o t) (s v) = true
    rw [switch _ _ on,line]
    exact decide_eq_true hvline
