import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma foldl_wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_length C.gates x

lemma foldl_wires_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    ((gs₁ ++ gs₂).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) =
      gs₂.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (gs₁.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  rw [List.foldl_append]

lemma getD_append_left {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_singleton_last {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

def remapWire (x1 n w : ℕ) : ℕ :=
  if w < x1 then w else w + n

def remapGate (x1 n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire x1 n)⟩

def liftCircuit (x1 n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (remapGate x1 n), remapWire x1 n C.output⟩

lemma liftCircuit_size (x1 n : ℕ) (C : Circuit) :
    (liftCircuit x1 n C).size = C.size := by
  simp [liftCircuit, Circuit.size]

lemma liftCircuit_isAO2 (x1 x2 : ℕ) (C : Circuit) (hAO : IsAO2 (x1 + x2) C) :
    IsAO2 ((x1 + x2) + (x1 + x2)) (liftCircuit x1 (x1 + x2) C) := by
  rcases hAO with ⟨hOp, hRB, hLen⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rw [liftCircuit, List.mem_map] at hg
    rcases hg with ⟨g', hg', rfl⟩
    exact hOp g' hg'
  · intro j hj i hi
    simp only [liftCircuit, List.length_map] at hj
    have hgate : gateAt (liftCircuit x1 (x1 + x2) C) j = remapGate x1 (x1 + x2) (gateAt C j) := by
      simp [gateAt, liftCircuit, List.getD_eq_getElem?_getD, hj]
    rw [hgate] at hi
    simp only [remapGate, List.mem_map] at hi
    rcases hi with ⟨i', hi', rfl⟩
    have hi'_lt : i' < (x1 + x2) + j := hRB j hj i' hi'
    unfold remapWire
    split_ifs <;> omega
  · intro g hg
    rw [liftCircuit, List.mem_map] at hg
    rcases hg with ⟨g', hg', rfl⟩
    simp [remapGate, hLen g' hg']

lemma foldl_wires_remap (x1 x2 : ℕ) (gs : List Gate) (w1 w2 : List Bool)
    (hw1 : w1.length ≥ x1 + x2)
    (hw2 : w2.length = w1.length + (x1 + x2))
    (hmatch : ∀ i < w1.length, w2.getD (remapWire x1 (x1 + x2) i) false = w1.getD i false)
    (hRB : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w1.length + j) :
    ∀ k < w1.length + gs.length,
      ((gs.map (remapGate x1 (x1 + x2))).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD
        (remapWire x1 (x1 + x2) k) false =
      (gs.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD k false := by
  induction gs generalizing w1 w2 with
  | nil =>
    intro k hk
    simpa using hmatch k hk
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hgRB : ∀ i ∈ g.inputs, i < w1.length := by
      intro i hi
      have h0 := hRB 0 (by simp) i
      simpa [List.getD_eq_getElem?_getD] using h0 hi
    have hval : (remapGate x1 (x1 + x2) g).op.eval
        ((remapGate x1 (x1 + x2) g).inputs.map fun i => w2.getD i false) =
        g.op.eval (g.inputs.map fun i => w1.getD i false) := by
      simp only [remapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hmatch i (hgRB i hi)
    rw [hval]
    set v := g.op.eval (g.inputs.map fun i => w1.getD i false)
    have hmatch' : ∀ i < (w1 ++ [v]).length,
        (w2 ++ [v]).getD (remapWire x1 (x1 + x2) i) false = (w1 ++ [v]).getD i false := by
      intro i hi
      rw [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < w1.length
      · have hlt2 : remapWire x1 (x1 + x2) i < w2.length := by
          unfold remapWire
          split_ifs <;> omega
        rw [getD_append_left w2 [v] _ false hlt2, getD_append_left w1 [v] _ false hlt]
        exact hmatch i hlt
      · have heq : i = w1.length := by omega
        subst heq
        have hge : ¬ (w1.length < x1) := by omega
        have hrem : remapWire x1 (x1 + x2) w1.length = w2.length := by
          unfold remapWire
          simp [hge, hw2]
        rw [hrem, getD_append_singleton_last, getD_append_singleton_last]
    have hRB' : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
        i < (w1 ++ [v]).length + j := by
      intro j hj i hi
      have h1 := hRB (j + 1) (by simp; omega) i
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ] at h1
      have h2 := h1 (by simpa [List.getD_eq_getElem?_getD] using hi)
      rw [List.length_append, List.length_singleton]
      omega
    intro k hk
    have hk' : k < (w1 ++ [v]).length + gs.length := by
      rw [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hk
      omega
    exact ih (w1 ++ [v]) (w2 ++ [v]) (by simp; omega) (by simp; omega) hmatch' hRB' k hk'

def projectInput (x1 x2 : ℕ) (x : Fin ((x1 + x2) + (x1 + x2)) → Bool) : Fin (x1 + x2) → Bool :=
  fun k => if k.val < x1 then x (Fin.castAdd (x1 + x2) k) else x (Fin.natAdd (x1 + x2) k)

lemma liftCircuit_eval (x1 x2 : ℕ) (C : Circuit) (hRB : ReadsBack (x1 + x2) C)
    (hout : C.output < (x1 + x2) + C.gates.length)
    (x : Fin ((x1 + x2) + (x1 + x2)) → Bool) :
    circuitFun ((x1 + x2) + (x1 + x2)) (liftCircuit x1 (x1 + x2) C) x =
      circuitFun (x1 + x2) C (projectInput x1 x2 x) := by
  unfold circuitFun Circuit.eval Circuit.wires
  have hmatch : ∀ i < (List.ofFn (projectInput x1 x2 x)).length,
      (List.ofFn x).getD (remapWire x1 (x1 + x2) i) false =
        (List.ofFn (projectInput x1 x2 x)).getD i false := by
    intro i hi
    rw [List.length_ofFn] at hi
    unfold remapWire projectInput
    by_cases hlt : i < x1
    · simp only [hlt, ↓reduceIte, List.getD_eq_getElem?_getD]
      have hi1 : i < (x1 + x2) + (x1 + x2) := by omega
      simp [hi, hi1, hlt, Fin.castAdd]
    · simp only [hlt, ↓reduceIte, List.getD_eq_getElem?_getD]
      have hi2 : i + (x1 + x2) < (x1 + x2) + (x1 + x2) := by omega
      simp only [List.getElem?_ofFn, hi, hi2, ↓reduceDIte, Option.getD_some, hlt, ↓reduceIte]
      congr 1
      ext
      simp [Fin.natAdd]
      omega
  have hRB' : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs,
      i < (List.ofFn (projectInput x1 x2 x)).length + j := by
    intro j hj i hi
    rw [List.length_ofFn]
    exact hRB j hj i hi
  have hres := foldl_wires_remap x1 x2 C.gates (List.ofFn (projectInput x1 x2 x)) (List.ofFn x)
    (by simp) (by simp) hmatch hRB' C.output (by simpa using hout)
  simpa [liftCircuit] using hres

def addEdgeCircuit (n : ℕ) (C : Circuit) (u v : Fin n) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.and, [u.val, n + v.val]⟩, ⟨GateOp.or, [C.output, (n + n) + C.gates.length]⟩],
    (n + n) + C.gates.length + 1⟩

lemma addEdgeCircuit_size (n : ℕ) (C : Circuit) (u v : Fin n) :
    (addEdgeCircuit n C u v).size = C.size + 2 := by
  simp [addEdgeCircuit, Circuit.size]

lemma addEdgeCircuit_output_lt (n : ℕ) (C : Circuit) (u v : Fin n) :
    (addEdgeCircuit n C u v).output < (n + n) + (addEdgeCircuit n C u v).gates.length := by
  simp [addEdgeCircuit]
  omega

lemma addEdgeCircuit_isAO2 (n : ℕ) (C : Circuit) (u v : Fin n)
    (hAO : IsAO2 (n + n) C) (hout : C.output < (n + n) + C.gates.length) :
    IsAO2 (n + n) (addEdgeCircuit n C u v) := by
  rcases hAO with ⟨hOp, hRB, hLen⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [addEdgeCircuit, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hOp g hg
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro j hj i hi
    simp only [addEdgeCircuit, List.length_append, List.length_cons, List.length_nil] at hj
    by_cases hlt : j < C.gates.length
    · have hg : gateAt (addEdgeCircuit n C u v) j = gateAt C j := by
        simp [gateAt, addEdgeCircuit, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hg] at hi
      exact hRB j hlt i hi
    · by_cases heq : j = C.gates.length
      · subst heq
        have hg : gateAt (addEdgeCircuit n C u v) C.gates.length = ⟨GateOp.and, [u.val, n + v.val]⟩ := by
          simp [gateAt, addEdgeCircuit, List.getD_eq_getElem?_getD]
        rw [hg] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · have heq2 : j = C.gates.length + 1 := by omega
        subst heq2
        have hg : gateAt (addEdgeCircuit n C u v) (C.gates.length + 1) =
            ⟨GateOp.or, [C.output, (n + n) + C.gates.length]⟩ := by
          simp [gateAt, addEdgeCircuit, List.getD_eq_getElem?_getD]
        rw [hg] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
  · intro g hg
    simp only [addEdgeCircuit, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hLen g hg
    · rfl
    · rfl

lemma addEdgeCircuit_eval (n : ℕ) (C : Circuit) (u v : Fin n)
    (hout : C.output < (n + n) + C.gates.length)
    (x : Fin (n + n) → Bool) :
    circuitFun (n + n) (addEdgeCircuit n C u v) x =
      (circuitFun (n + n) C x || (x (Fin.castAdd n u) && x (Fin.natAdd n v))) := by
  unfold circuitFun Circuit.eval Circuit.wires addEdgeCircuit
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set w := C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    (List.ofFn x)
  have hw_len : w.length = (n + n) + C.gates.length := by
    simpa [w, Circuit.wires] using wires_length C (List.ofFn x)
  have hprefix : ∀ i < n + n, w.getD i false = (List.ofFn x).getD i false := by
    intro i hi
    have : ∀ (gs : List Gate) (w0 : List Bool), i < w0.length →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) w0).getD i false =
          w0.getD i false := by
      intro gs
      induction gs with
      | nil => intro w0 _; rfl
      | cons g gs ih =>
        intro w0 hi0
        simp only [List.foldl_cons]
        rw [ih _ (by simp; omega), getD_append_left w0 _ i false hi0]
    exact this C.gates (List.ofFn x) (by simpa using hi)
  have hu : w.getD u.val false = x (Fin.castAdd n u) := by
    rw [hprefix u.val (by omega)]
    simp [List.getD_eq_getElem?_getD, show u.val < n + n by omega]
    rfl
  have hv : w.getD (n + v.val) false = x (Fin.natAdd n v) := by
    rw [hprefix (n + v.val) (by omega)]
    simp [List.getD_eq_getElem?_getD, show n + v.val < n + n by omega, Fin.natAdd]
  set e := x (Fin.castAdd n u) && x (Fin.natAdd n v)
  have hand : GateOp.and.eval ([u.val, n + v.val].map fun i => w.getD i false) = e := by
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, hu, hv, e]
  rw [hand]
  have hout_lt : C.output < w.length := by omega
  have hw1_len : (w ++ [e]).length = (n + n) + C.gates.length + 1 := by
    simp [hw_len]
  have hget_out : (w ++ [e]).getD C.output false = w.getD C.output false :=
    getD_append_left w [e] C.output false hout_lt
  have hget_e : (w ++ [e]).getD ((n + n) + C.gates.length) false = e := by
    rw [← hw_len]
    exact getD_append_singleton_last w e false
  have hor : GateOp.or.eval ([C.output, (n + n) + C.gates.length].map fun i => (w ++ [e]).getD i false) =
      (w.getD C.output false || e) := by
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
      Bool.or_false, hget_out, hget_e]
  rw [hor, ← hw1_len, getD_append_singleton_last]

end PEqualNP.Outside.L_meta_3264_aux

theorem PEqualNP.Outside.L_meta_3264 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.Nonempty →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →         let x8 : ℕ := x1 + x2;         have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) := Finset.image (fun (x9 : Fin x1 × Fin x2) => (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;         ∀ (x10 : Finset (Fin x8 × Fin x8)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧ ∀ (x12 : Fin (x8 + x8) → Bool), PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 = Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)), (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd x8 x13) = Bool.true ∧ x12 (Fin.natAdd x8 x14) = Bool.true) := by
  intro x1 x2 x3 x4 hne hAO hfun
  dsimp only
  set n : ℕ := x1 + x2
  set E0 : Finset (Fin n × Fin n) :=
    Finset.image (fun p : Fin x1 × Fin x2 => (Fin.castAdd x2 p.1, Fin.natAdd x1 p.2)) x3
  have hout4 : x4.output < n + x4.gates.length := by
    by_contra hge
    have hge' : n + x4.gates.length ≤ x4.output := Nat.le_of_not_lt hge
    rcases hne with ⟨⟨i0, j0⟩, hij0⟩
    have ht := hfun (fun _ => true)
    have hfalse : PEqualNP.MetaComplexity.circuitFun n x4 (fun _ => true) = false := by
      unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
      have hlen : (x4.wires (List.ofFn (fun _ : Fin n => true))).length = n + x4.gates.length := by
        simpa using PEqualNP.Outside.L_meta_3264_aux.wires_length x4 (List.ofFn (fun _ : Fin n => true))
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hfalse] at ht
    have htrue : Decidable.decide (∃ (a : Fin x1) (b : Fin x2), (a, b) ∈ x3 ∧ true = true ∧ true = true) = true := by
      rw [decide_eq_true_eq]
      exact ⟨i0, j0, hij0, rfl, rfl⟩
    rw [htrue] at ht
    exact Bool.noConfusion ht
  intro x10
  have hmain : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (n + n) C ∧
      C.output < (n + n) + C.gates.length ∧
      C.size ≤ x4.size + 2 * x10.card ∧
      ∀ (x12 : Fin (n + n) → Bool),
        PEqualNP.MetaComplexity.circuitFun (n + n) C x12 =
          Decidable.decide (∃ (u v : Fin n), (u, v) ∈ E0 ∪ x10 ∧
            x12 (Fin.castAdd n u) = true ∧ x12 (Fin.natAdd n v) = true) := by
    classical
    induction x10 using Finset.induction_on with
    | empty =>
      refine ⟨PEqualNP.Outside.L_meta_3264_aux.liftCircuit x1 n x4, ?_, ?_, ?_, ?_⟩
      · exact PEqualNP.Outside.L_meta_3264_aux.liftCircuit_isAO2 x1 x2 x4 hAO
      · simp only [PEqualNP.Outside.L_meta_3264_aux.liftCircuit, List.length_map]
        unfold PEqualNP.Outside.L_meta_3264_aux.remapWire
        split_ifs <;> omega
      · rw [PEqualNP.Outside.L_meta_3264_aux.liftCircuit_size]
        simp
      · intro x12
        rw [PEqualNP.Outside.L_meta_3264_aux.liftCircuit_eval x1 x2 x4 hAO.2.1 hout4 x12, hfun]
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨a, b, hab, ha, hb⟩
          refine ⟨Fin.castAdd x2 a, Fin.natAdd x1 b, ?_, ?_, ?_⟩
          · rw [Finset.union_empty]
            exact Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩
          · simpa [PEqualNP.Outside.L_meta_3264_aux.projectInput, a.isLt] using ha
          · have hnot : ¬ (x1 + b.val < x1) := by omega
            simpa [PEqualNP.Outside.L_meta_3264_aux.projectInput, hnot] using hb
        · rintro ⟨u, v, huv, hu, hv⟩
          rw [Finset.union_empty, Finset.mem_image] at huv
          rcases huv with ⟨⟨a, b⟩, hab, hpair⟩
          rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
          refine ⟨a, b, hab, ?_, ?_⟩
          · simpa [PEqualNP.Outside.L_meta_3264_aux.projectInput, a.isLt] using hu
          · have hnot : ¬ (x1 + b.val < x1) := by omega
            simpa [PEqualNP.Outside.L_meta_3264_aux.projectInput, hnot] using hv
    | @insert p s hp ih =>
      rcases ih with ⟨C, hCAO, hCout, hCsize, hCfun⟩
      refine ⟨PEqualNP.Outside.L_meta_3264_aux.addEdgeCircuit n C p.1 p.2, ?_, ?_, ?_, ?_⟩
      · exact PEqualNP.Outside.L_meta_3264_aux.addEdgeCircuit_isAO2 n C p.1 p.2 hCAO hCout
      · exact PEqualNP.Outside.L_meta_3264_aux.addEdgeCircuit_output_lt n C p.1 p.2
      · rw [PEqualNP.Outside.L_meta_3264_aux.addEdgeCircuit_size, Finset.card_insert_of_notMem hp]
        omega
      · intro x12
        rw [PEqualNP.Outside.L_meta_3264_aux.addEdgeCircuit_eval n C p.1 p.2 hCout x12, hCfun x12]
        by_cases h1 : ∃ (u v : Fin n), (u, v) ∈ E0 ∪ s ∧
            x12 (Fin.castAdd n u) = true ∧ x12 (Fin.natAdd n v) = true
        · have h2 : ∃ (u v : Fin n), (u, v) ∈ E0 ∪ insert p s ∧
              x12 (Fin.castAdd n u) = true ∧ x12 (Fin.natAdd n v) = true := by
            rcases h1 with ⟨u, v, huv, hu, hv⟩
            refine ⟨u, v, ?_, hu, hv⟩
            simp only [Finset.mem_union, Finset.mem_insert] at huv ⊢
            tauto
          rw [decide_eq_true h1, decide_eq_true h2]
          rfl
        · by_cases h3 : x12 (Fin.castAdd n p.1) = true ∧ x12 (Fin.natAdd n p.2) = true
          · have h2 : ∃ (u v : Fin n), (u, v) ∈ E0 ∪ insert p s ∧
                x12 (Fin.castAdd n u) = true ∧ x12 (Fin.natAdd n v) = true := by
              refine ⟨p.1, p.2, ?_, h3.1, h3.2⟩
              simp
            rw [decide_eq_false h1, h3.1, h3.2, decide_eq_true h2]
            rfl
          · have h2 : ¬ ∃ (u v : Fin n), (u, v) ∈ E0 ∪ insert p s ∧
                x12 (Fin.castAdd n u) = true ∧ x12 (Fin.natAdd n v) = true := by
              rintro ⟨u, v, huv, hu, hv⟩
              simp only [Finset.mem_union, Finset.mem_insert] at huv
              rcases huv with hE0 | rfl | hs
              · exact h1 ⟨u, v, Finset.mem_union_left _ hE0, hu, hv⟩
              · exact h3 ⟨hu, hv⟩
              · exact h1 ⟨u, v, Finset.mem_union_right _ hs, hu, hv⟩
            have h3' : (x12 (Fin.castAdd n p.1) && x12 (Fin.natAdd n p.2)) = false := by
              cases hA : x12 (Fin.castAdd n p.1) <;> cases hB : x12 (Fin.natAdd n p.2) <;> simp_all
            rw [decide_eq_false h1, h3', decide_eq_false h2]
            rfl
  rcases hmain with ⟨C, hCAO, _, hCsize, hCfun⟩
  exact ⟨C, hCAO, hCsize, hCfun⟩
