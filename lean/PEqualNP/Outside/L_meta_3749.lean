import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3749

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.Core

def C0 : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [14, 3] },
      { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.or, inputs := [16, 10] },
      { op := GateOp.and, inputs := [15, 17] }, { op := GateOp.or, inputs := [7, 10] },
      { op := GateOp.and, inputs := [5, 19] }, { op := GateOp.or, inputs := [18, 20] },
      { op := GateOp.or, inputs := [0, 10] }, { op := GateOp.or, inputs := [1, 3] },
      { op := GateOp.or, inputs := [23, 5] }, { op := GateOp.or, inputs := [24, 7] },
      { op := GateOp.and, inputs := [22, 25] }, { op := GateOp.and, inputs := [21, 26] },
      { op := GateOp.or, inputs := [7, 8] }, { op := GateOp.and, inputs := [4, 28] },
      { op := GateOp.or, inputs := [18, 29] }, { op := GateOp.or, inputs := [1, 8] },
      { op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [32, 4] },
      { op := GateOp.or, inputs := [33, 7] }, { op := GateOp.and, inputs := [31, 34] },
      { op := GateOp.and, inputs := [30, 35] }, { op := GateOp.or, inputs := [27, 36] },
      { op := GateOp.and, inputs := [7, 2] }, { op := GateOp.or, inputs := [37, 38] },
      { op := GateOp.or, inputs := [0, 5] }, { op := GateOp.or, inputs := [40, 6] },
      { op := GateOp.and, inputs := [41, 9] }, { op := GateOp.or, inputs := [39, 42] },
      { op := GateOp.or, inputs := [1, 4] }, { op := GateOp.or, inputs := [44, 6] },
      { op := GateOp.and, inputs := [45, 11] }, { op := GateOp.or, inputs := [43, 46] },
      { op := GateOp.or, inputs := [2, 3] }, { op := GateOp.or, inputs := [48, 6] },
      { op := GateOp.and, inputs := [49, 12] }, { op := GateOp.or, inputs := [47, 50] },
      { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.or, inputs := [52, 5] },
      { op := GateOp.and, inputs := [53, 13] }, { op := GateOp.or, inputs := [51, 54] }],
    output := 55 }

def edges : List (Fin 14 × Fin 14) :=
  [(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13),
   (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13),
   (6, 9), (6, 11), (6, 12)]

def bad8 : List (Fin 14 × Fin 14) :=
  [(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)]

lemma h_ao2 : IsAO2 14 C0 := by decide +kernel

lemma h_size : C0.size = 42 := rfl

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def leList (u v : List Bool) : Prop :=
  ∀ i : ℕ, u.getD i false = true → v.getD i false = true

lemma gate_eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : List Bool) (hle : leList u v) :
    g.op.eval (g.inputs.map fun i => u.getD i false) = true →
    g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
  rcases hg with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map]
    intro h b hb
    rcases hb with ⟨i, hi, rfl⟩
    exact hle i (h _ ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨v.getD i false, ⟨i, hi, rfl⟩, hle i hb⟩

lemma wires_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (u v : List Bool), u.length = v.length → leList u v →
      leList (gs.foldl evalStep u) (gs.foldl evalStep v) := by
  induction gs with
  | nil => intro u v _ hle; exact hle
  | cons g gs ih =>
    intro u v hlen hle
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g List.mem_cons_self
    have hrest : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hm => hgs g' (List.mem_cons_of_mem _ hm)
    apply ih hrest (evalStep u g) (evalStep v g)
    · simp [evalStep, hlen]
    · intro i hi
      simp only [evalStep] at hi ⊢
      by_cases hlt : i < u.length
      · have hlt' : i < v.length := hlen ▸ hlt
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt']
        exact hle i (by simpa [List.getD_eq_getElem?_getD] using hi)
      · by_cases heq : i = u.length
        · subst heq
          have hu : (u ++ [g.op.eval (g.inputs.map fun j => u.getD j false)]).getD u.length false =
              g.op.eval (g.inputs.map fun j => u.getD j false) := by
            simp [List.getD_eq_getElem?_getD]
          have hv : (v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]).getD u.length false =
              g.op.eval (g.inputs.map fun j => v.getD j false) := by
            rw [hlen]; simp [List.getD_eq_getElem?_getD]
          rw [hu] at hi
          rw [hv]
          exact gate_eval_mono g hg u v hle hi
        · have hgt : (u ++ [g.op.eval (g.inputs.map fun j => u.getD j false)]).length ≤ i := by
            simp; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hgt] at hi
          exact False.elim (Bool.false_ne_true hi)

lemma circuitFun_mono (x y : Fin 14 → Bool) (hle : ∀ i : Fin 14, x i = true → y i = true) :
    circuitFun 14 C0 x = true → circuitFun 14 C0 y = true := by
  have hgs : ∀ g ∈ C0.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h_ao2.1 g hg
  have hle0 : leList (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases hlt : i < 14
    · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
      simp only [hlt, ↓reduceDIte, Option.getD_some] at hi ⊢
      exact hle ⟨i, hlt⟩ hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi
      simp only [hlt, ↓reduceDIte, Option.getD_none] at hi
      exact False.elim (Bool.false_ne_true hi)
  have hm := wires_mono C0.gates hgs (List.ofFn x) (List.ofFn y) (by simp) hle0
  exact hm C0.output

def edgeInput (e : Fin 14 × Fin 14) : Fin 14 → Bool :=
  fun i => decide (i = e.1 ∨ i = e.2)

def mk7 (b0 b1 b2 b3 b4 b5 b6 : Bool) : BitVec 7 :=
  BitVec.cons b6 (BitVec.cons b5 (BitVec.cons b4
  (BitVec.cons b3 (BitVec.cons b2 (BitVec.cons b1
  (BitVec.cons b0 BitVec.nil))))))

def ptBV (x : Fin 14 → Bool) : BitVec 7 :=
  mk7 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

lemma getLsbD_ptBV (x : Fin 14 → Bool) (k : ℕ) (hk : k < 7) :
    (ptBV x).getLsbD k = x ⟨k, by omega⟩ := by
  interval_cases k <;> (simp only [ptBV, mk7, BitVec.getLsbD_cons]; simp)

def topX (bv : BitVec 7) (i : Fin 14) : Bool :=
  if i.val < 7 then bv.getLsbD i.val
  else edges.all fun e => !(decide (e.2 = i) && bv.getLsbD e.1.val)

lemma edges_first_lt : ∀ e ∈ edges, e.1.val < 7 := by decide +kernel

set_option maxRecDepth 100000 in
lemma h_pos : ∀ e ∈ edges, circuitFun 14 C0 (edgeInput e) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma h_neg : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    circuitFun 14 C0 (topX (mk7 b0 b1 b2 b3 b4 b5 b6)) = false := by
  decide +kernel

lemma h_eval (x : Fin 14 → Bool) :
    circuitFun 14 C0 x = decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true) := by
  by_cases hex : ∃ e ∈ edges, x e.1 = true ∧ x e.2 = true
  · rw [decide_eq_true hex]
    obtain ⟨e, he, h1, h2⟩ := hex
    apply circuitFun_mono (edgeInput e) x _ (h_pos e he)
    intro i hi
    simp only [edgeInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact h1
    · exact h2
  · rw [decide_eq_false hex]
    have hfalse : circuitFun 14 C0 (topX (ptBV x)) = false :=
      h_neg (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
    have hle : ∀ i : Fin 14, x i = true → topX (ptBV x) i = true := by
      intro i hi
      unfold topX
      split_ifs with hlt
      · exact (getLsbD_ptBV x i.val hlt).trans hi
      · simp only [List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
          decide_eq_false_iff_not]
        intro e he
        by_cases he2 : e.2 = i
        · right
          rw [getLsbD_ptBV x e.1.val (edges_first_lt e he)]
          cases hxe1 : x e.1
          · rfl
          · exfalso
            apply hex
            exact ⟨e, he, hxe1, he2 ▸ hi⟩
        · exact Or.inl he2
    cases hcx : circuitFun 14 C0 x
    · rfl
    · exfalso
      have := circuitFun_mono x (topX (ptBV x)) hle hcx
      rw [hfalse] at this
      exact Bool.false_ne_true this

set_option maxRecDepth 100000 in
lemma h_read : ∀ e ∈ edges, ReadTwiceAt 14 C0 (C0.output - 14) e.1 e.2 ↔ e ∈ bad8 := by
  decide +kernel

end PEqualNP.Outside.L_meta_3749

theorem PEqualNP.Outside.L_meta_3749 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [41, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [49, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 50] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 54] }], output := 55 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 42 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14))) := by
  rintro C rfl
  exact ⟨PEqualNP.Outside.L_meta_3749.h_ao2, PEqualNP.Outside.L_meta_3749.h_size,
    PEqualNP.Outside.L_meta_3749.h_eval, PEqualNP.Outside.L_meta_3749.h_read⟩
