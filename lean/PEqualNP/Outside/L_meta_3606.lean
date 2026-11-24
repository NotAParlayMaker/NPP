import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_3606

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma getD_mono {w1 w2 : List Bool} (h : List.Forall₂ (fun a b : Bool => a ≤ b) w1 w2)
    (i : ℕ) : w1.getD i false ≤ w2.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma headD_map_mono (l : List ℕ) (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i ≤ f2 i) :
    (l.map f1).headD false ≤ (l.map f2).headD false := by
  cases l with
  | nil => simp
  | cons a l => simpa using h a

lemma all_map_mono (l : List ℕ) (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i ≤ f2 i) :
    (l.map f1).all id ≤ (l.map f2).all id := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id]
    have ha := h a
    generalize f1 a = p1 at *
    generalize f2 a = p2 at *
    generalize (l.map f1).all id = r1 at *
    generalize (l.map f2).all id = r2 at *
    revert ha ih
    cases p1 <;> cases p2 <;> cases r1 <;> cases r2 <;> decide

lemma any_map_mono (l : List ℕ) (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i ≤ f2 i) :
    (l.map f1).any id ≤ (l.map f2).any id := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id]
    have ha := h a
    generalize f1 a = p1 at *
    generalize f2 a = p2 at *
    generalize (l.map f1).any id = r1 at *
    generalize (l.map f2).any id = r2 at *
    revert ha ih
    cases p1 <;> cases p2 <;> cases r1 <;> cases r2 <;> decide

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i ≤ f2 i) : op.eval (l.map f1) ≤ op.eval (l.map f2) := by
  rcases hop with rfl | rfl
  · exact all_map_mono l f1 f2 h
  · exact any_map_mono l f1 f2 h

lemma foldl_mono (G : List Gate) (hG : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w1 w2 : List Bool, List.Forall₂ (fun a b : Bool => a ≤ b) w1 w2 →
      List.Forall₂ (fun a b : Bool => a ≤ b) (G.foldl step w1) (G.foldl step w2) := by
  induction G with
  | nil => intro w1 w2 h; exact h
  | cons g G ih =>
    intro w1 w2 h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg'))
    unfold step
    exact List.rel_append h (List.Forall₂.cons
      (eval_mono g.op (hG g List.mem_cons_self) g.inputs _ _ (fun i => getD_mono h i))
      List.Forall₂.nil)

lemma ofFn_le {n : ℕ} (x y : Fin n → Bool) (h : ∀ i, x i ≤ y i) :
    List.Forall₂ (fun a b : Bool => a ≤ b) (List.ofFn x) (List.ofFn y) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, ?_⟩
  intro i h1 h2
  simpa using h ⟨i, by simpa using h1⟩

end PEqualNP.Outside.L_meta_3606

theorem PEqualNP.Outside.L_meta_3606 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin x1.gates.length), PEqualNP.MetaComplexity.FanInTwo x1 → x2 < x3 → ↑x3 + (1 : ℕ) = x1.size → x1.output = (9 : ℕ) + ↑x3 → (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ (x10 : Fin x1.gates.length), (x1.gates.get x10).op = PEqualNP.CircuitLowerBounds.GateOp.not → x10 = x2 ∨ x10 = x3) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x11 : Fin (9 : ℕ)) => Bool.false) = Bool.false → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x12 : Fin (9 : ℕ)) => Bool.true) = Bool.true → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x13 ∧ x13.size ≤ ↑x2 ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x13 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 := by
  intro C kf mf hfan hkm hsize hout hk hm hnot h0 h1
  classical
  have hkm' : kf.val < mf.val := hkm
  have hlen : mf.val + 1 = C.gates.length := hsize
  have hkl : kf.val < C.gates.length := kf.isLt
  have hml : mf.val < C.gates.length := mf.isLt
  have hkgate : C.gates[kf.val].op = GateOp.not := by simpa using hk
  have hmgate : C.gates[mf.val].op = GateOp.not := by simpa using hm
  have hAO : ∀ j (hj : j < C.gates.length), j ≠ kf.val → j ≠ mf.val →
      C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by
    intro j hj hjk hjm
    have hmem := (hfan C.gates[j] (List.getElem_mem hj)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases hnot ⟨j, hj⟩ (by simpa using h) with e | e
      · exact hjk (congrArg Fin.val e)
      · exact hjm (congrArg Fin.val e)
  have hsplit_m : C.gates = C.gates.take mf.val ++ [C.gates[mf.val]] := by
    conv_lhs => rw [← List.take_append_drop mf.val C.gates]
    congr 1
    rw [List.drop_eq_getElem_cons hml]
    simp [List.drop_eq_nil_of_le (show C.gates.length ≤ mf.val + 1 by omega)]
  have htk : (C.gates.take mf.val).take kf.val = C.gates.take kf.val := by
    simp [List.take_take, min_eq_left hkm'.le, min_eq_right hkm'.le]
  have htm_len : kf.val < (C.gates.take mf.val).length := by
    rw [List.length_take_of_le hml.le]; exact hkm'
  have hsplit_k : C.gates.take mf.val =
      C.gates.take kf.val ++ C.gates[kf.val] :: (C.gates.take mf.val).drop (kf.val + 1) := by
    conv_lhs => rw [← List.take_append_drop kf.val (C.gates.take mf.val)]
    rw [htk, List.drop_eq_getElem_cons htm_len]
    simp [List.getElem_take]
  have hG' : ∀ g ∈ (C.gates.take mf.val).drop (kf.val + 1),
      g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    rw [List.length_drop, List.length_take_of_le hml.le] at hi
    rw [List.getElem_drop, List.getElem_take]
    exact hAO _ (by omega) (by omega) (by omega)
  have hGk : ∀ g ∈ C.gates.take kf.val, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    rw [List.length_take_of_le hkl.le] at hi
    rw [List.getElem_take]
    exact hAO i (by omega) (by omega) (by omega)
  obtain ⟨Pk, hPk⟩ : ∃ f : (Fin 9 → Bool) → List Bool, ∀ x,
      f x = (C.gates.take kf.val).foldl PEqualNP.Outside.L_meta_3606.step (List.ofFn x) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ f : (Fin 9 → Bool) → Bool, ∀ x,
      f x = (C.gates[kf.val].inputs.map fun i => (Pk x).getD i false).headD false :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ f : Bool → (Fin 9 → Bool) → List Bool, ∀ z x,
      f z x = ((C.gates.take mf.val).drop (kf.val + 1)).foldl
        PEqualNP.Outside.L_meta_3606.step (Pk x ++ [z]) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨wv, hwv⟩ : ∃ f : Bool → (Fin 9 → Bool) → Bool, ∀ z x,
      f z x = (C.gates[mf.val].inputs.map fun i => (Q z x).getD i false).headD false :=
    ⟨_, fun _ _ => rfl⟩
  have hPk_len : ∀ x, (Pk x).length = 9 + kf.val := by
    intro x
    rw [hPk, PEqualNP.Outside.L_meta_3606.foldl_length, List.length_take_of_le hkl.le]
    simp
  have hQ_len : ∀ z x, (Q z x).length = 9 + mf.val := by
    intro z x
    rw [hQ, PEqualNP.Outside.L_meta_3606.foldl_length, List.length_append, hPk_len,
      List.length_drop, List.length_take_of_le hml.le]
    simp
    omega
  have hF : ∀ x, PEqualNP.MetaComplexity.circuitFun 9 C x = !(wv (!(u x)) x) := by
    intro x
    have hw : C.wires (List.ofFn x) = Q (!(u x)) x ++ [!(wv (!(u x)) x)] := by
      rw [PEqualNP.Outside.L_meta_3606.wires_eq]
      conv_lhs => rw [hsplit_m]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hsplit_k, List.foldl_append,
        List.foldl_cons, ← hPk]
      have hstepk : PEqualNP.Outside.L_meta_3606.step (Pk x) C.gates[kf.val] =
          Pk x ++ [!(u x)] := by
        unfold PEqualNP.Outside.L_meta_3606.step
        rw [hkgate, hu]
        rfl
      rw [hstepk, ← hQ]
      unfold PEqualNP.Outside.L_meta_3606.step
      rw [hmgate, hwv]
      rfl
    show (C.wires (List.ofFn x)).getD C.output false = _
    rw [hw, hout]
    have hl := hQ_len (!(u x)) x
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp [hl]
  have hQmono : ∀ (x y : Fin 9 → Bool) (z1 z2 : Bool), (∀ i, x i ≤ y i) → z1 ≤ z2 →
      List.Forall₂ (fun a b : Bool => a ≤ b) (Q z1 x) (Q z2 y) := by
    intro x y z1 z2 hxy hz
    rw [hQ, hQ]
    apply PEqualNP.Outside.L_meta_3606.foldl_mono _ hG'
    apply List.rel_append
    · rw [hPk, hPk]
      exact PEqualNP.Outside.L_meta_3606.foldl_mono _ hGk _ _
        (PEqualNP.Outside.L_meta_3606.ofFn_le x y hxy)
    · exact List.Forall₂.cons hz List.Forall₂.nil
  have hwmono : ∀ (x y : Fin 9 → Bool) (z1 z2 : Bool), (∀ i, x i ≤ y i) → z1 ≤ z2 →
      wv z1 x ≤ wv z2 y := by
    intro x y z1 z2 hxy hz
    rw [hwv, hwv]
    exact PEqualNP.Outside.L_meta_3606.headD_map_mono _ _ _
      (fun i => PEqualNP.Outside.L_meta_3606.getD_mono (hQmono x y z1 z2 hxy hz) i)
  have h0' : wv (!(u fun _ => false)) (fun _ => false) = true := by
    have e := hF (fun _ => false)
    rw [h0] at e
    simpa using e.symm
  have h1' : wv (!(u fun _ => true)) (fun _ => true) = false := by
    have e := hF (fun _ => true)
    rw [h1] at e
    simpa using e.symm
  have hu0 : u (fun _ => false) = false := by
    by_contra hc
    have hc' : u (fun _ => false) = true := by simpa using hc
    have e0 : wv false (fun _ => false) = true := by simpa [hc'] using h0'
    have := hwmono (fun _ => false) (fun _ => true) false (!(u fun _ => true))
      (fun _ => Bool.false_le _) (Bool.false_le _)
    rw [e0, h1'] at this
    exact absurd this (by decide)
  have hu1 : u (fun _ => true) = true := by
    by_contra hc
    have hc' : u (fun _ => true) = false := by simpa using hc
    have e1 : wv true (fun _ => true) = false := by simpa [hc'] using h1'
    have := hwmono (fun _ => false) (fun _ => true) (!(u fun _ => false)) true
      (fun _ => Bool.false_le _) (Bool.le_true _)
    rw [h0', e1] at this
    exact absurd this (by decide)
  have wf : ∀ x, wv false x = false := by
    intro x
    have e1 : wv false (fun _ => true) = false := by simpa [hu1] using h1'
    have := hwmono x (fun _ => true) false false (fun _ => Bool.le_true _) le_rfl
    rw [e1] at this
    generalize wv false x = b at this ⊢
    revert this
    cases b <;> decide
  have wt : ∀ x, wv true x = true := by
    intro x
    have e0 : wv true (fun _ => false) = true := by simpa [hu0] using h0'
    have := hwmono (fun _ => false) x true true (fun _ => Bool.false_le _) le_rfl
    rw [e0] at this
    generalize wv true x = b at this ⊢
    revert this
    cases b <;> decide
  have hFu : ∀ x, PEqualNP.MetaComplexity.circuitFun 9 C x = u x := by
    intro x
    rw [hF x]
    cases hux : u x <;> simp [wf, wt]
  refine ⟨⟨C.gates.take kf.val, C.gates[kf.val].inputs.headD (9 + kf.val)⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact hfan g (List.mem_of_mem_take hg)
  · show (C.gates.take kf.val).length ≤ kf.val
    simp
  · funext x
    rw [hFu x]
    show ((C.gates.take kf.val).foldl PEqualNP.Outside.L_meta_3606.step (List.ofFn x)).getD
      (C.gates[kf.val].inputs.headD (9 + kf.val)) false = u x
    rw [← hPk, hu]
    cases hin : C.gates[kf.val].inputs with
    | nil =>
      simp only [List.headD_nil, List.map_nil]
      exact List.getD_eq_default _ _ (by rw [hPk_len])
    | cons a l => simp
