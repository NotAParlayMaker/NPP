import PEqualNP.Defs
import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_4791


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour

def ren (n w : ℕ) : ℕ :=
  if w < n then w else n + 3 * (w - n) + 2

def block (n j : ℕ) (g : Gate) : List Gate :=
  [⟨GateOp.and, [ren n (g.inputs.getD 0 0), ren n (g.inputs.getD 0 0)]⟩,
   ⟨GateOp.and, [ren n (g.inputs.getD 1 0), ren n (g.inputs.getD 1 0)]⟩,
   ⟨g.op, [n + 3 * j, n + 3 * j + 1]⟩]

def expand (n : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs => block n j g ++ expand n (j + 1) gs

def shield (n : ℕ) (C : Circuit) : Circuit :=
  ⟨expand n 0 C.gates, ren n C.output⟩



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

@[local simp] theorem block_length (n j : ℕ) (g : Gate) : (block n j g).length = 3 := by
  rfl

@[local simp] theorem expand_length (n j : ℕ) (gs : List Gate) :
    (expand n j gs).length = 3 * gs.length := by
  induction gs generalizing j with
  | nil => simp [expand]
  | cons g gs ih => simp [expand, ih, Nat.mul_add, Nat.add_comm]

@[local simp] theorem shield_size (n : ℕ) (C : Circuit) : (shield n C).size = 3 * C.size := by
  simp [shield, Circuit.size]

-- The exact block containing any expanded gate, including its old gate index.
theorem mem_expand_iff (n j : ℕ) (gs : List Gate) (g : Gate) :
    g ∈ expand n j gs ↔ ∃ k < gs.length,
      g ∈ block n (j + k) (gs.getD k ⟨GateOp.or, []⟩) := by
  induction gs generalizing j with
  | nil => simp [expand]
  | cons a gs ih =>
    constructor
    · intro hg
      rcases List.mem_append.mp hg with hb | ht
      · exact ⟨0, by simp, by simpa using hb⟩
      · obtain ⟨k, hk, hmem⟩ := (ih (j + 1)).mp ht
        refine ⟨k + 1, by simpa using hk, ?_⟩
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmem
    · rintro ⟨k, hk, hmem⟩
      cases k with
      | zero => exact List.mem_append_left _ (by simpa using hmem)
      | succ k =>
        apply List.mem_append_right
        apply (ih (j + 1)).mpr
        refine ⟨k, by simpa using hk, ?_⟩
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmem

-- Index `3*k+r` is position `r` of the block for old gate `k`.
theorem expand_getD (n j : ℕ) (gs : List Gate) (k r : ℕ)
    (hk : k < gs.length) (hr : r < 3) :
    (expand n j gs).getD (3 * k + r) ⟨GateOp.or, []⟩ =
      (block n (j + k) (gs.getD k ⟨GateOp.or, []⟩)).getD r ⟨GateOp.or, []⟩ := by
  induction gs generalizing j k with
  | nil => simp at hk
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, List.getD_cons_zero, expand]
      exact List.getD_append _ _ _ _ (by simpa using hr)
    | succ k =>
      rw [expand, List.getD_append_right _ _ _ _ (by simp; omega)]
      have hidx : 3 * (k + 1) + r - (block n j g).length = 3 * k + r := by
        simp only [block_length]
        omega
      rw [hidx, ih (j + 1) k (by simpa using hk)]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem shield_gateAt (n : ℕ) (C : Circuit) (k r : ℕ)
    (hk : k < C.gates.length) (hr : r < 3) :
    gateAt (shield n C) (3 * k + r) =
      (block n k (gateAt C k)).getD r ⟨GateOp.or, []⟩ := by
  simpa [gateAt, shield] using expand_getD n 0 C.gates k r hk hr

theorem gateAt_mem {C : Circuit} {k : ℕ} (hk : k < C.gates.length) :
    gateAt C k ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem ren_lt (n j w : ℕ) (hw : w < n + j) : ren n w < n + 3 * j := by
  unfold ren
  split_ifs <;> omega

theorem shield_isAO2 (n : ℕ) (C : Circuit) (hC : IsAO2 n C) :
    IsAO2 n (shield n C) := by
  have props : ∀ g ∈ (shield n C).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    obtain ⟨k, hk, hb⟩ := (mem_expand_iff n 0 C.gates g).mp hg
    have hold := hC.1 (gateAt C k) (gateAt_mem hk)
    simp only [Nat.zero_add] at hb
    change g ∈ block n k (gateAt C k) at hb
    simp only [block, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact ⟨Or.inl rfl, rfl⟩
    · exact ⟨Or.inl rfl, rfl⟩
    · exact ⟨hold, rfl⟩
  refine ⟨fun g hg => (props g hg).1, ?_, fun g hg => (props g hg).2⟩
  intro q hq w hw
  change q < (expand n 0 C.gates).length at hq
  rw [expand_length] at hq
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r : ℕ,
      k < C.gates.length ∧ r < 3 ∧ q = 3 * k + r := by
    exact ⟨q / 3, q % 3, by omega, by omega, by omega⟩
  rw [shield_gateAt n C k r hk hr] at hw
  have hlen : (gateAt C k).inputs.length = 2 := hC.2.2 _ (gateAt_mem hk)
  have old_input (s : ℕ) (hs : s < 2) :
      (gateAt C k).inputs.getD s 0 < n + k := by
    apply hC.2.1 k hk
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have cases_r : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases cases_r with rfl | rfl | rfl
  · simp [block] at hw
    subst w
    simpa using ren_lt n k _ (old_input 0 (by omega))
  · simp [block] at hw
    subst w
    have := ren_lt n k _ (old_input 1 (by omega))
    simp only [List.getD_eq_getElem?_getD] at this
    omega
  · simp [block] at hw
    rcases hw with rfl | rfl <;> omega




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour

-- Every operand of every OR gate is a gate wire, rather than a primary input.
def NoPrimaryOrInputs (n : ℕ) (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op = GateOp.or → ∀ w ∈ g.inputs, n ≤ w

theorem reach_gateAt_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k ∈ C.gates := by
  unfold gateAt
  simp only [List.getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

-- An OR closure cannot reach an input unless some OR gate directly reads one.
theorem orIn_empty_of_noPrimaryOrInputs (n : ℕ) (C : Circuit)
    (hC : NoPrimaryOrInputs n C) (w : ℕ) (hw : n ≤ w) : orIn n C w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with hi | ⟨k, hk, _, hop, hin⟩
  · have := i.isLt
    omega
  · have hni := hC (gateAt C k) (reach_gateAt_mem C k hk) hop i.val hin
    have := i.isLt
    omega

theorem tCount_zero_of_noPrimaryOrInputs (n : ℕ) (C : Circuit)
    (hC : NoPrimaryOrInputs n C) (isLine : ℕ → Bool) : tCount n C isLine = 0 := by
  have hnone : ∀ j, ¬ IsTwoColour n C isLine j := by
    intro j hj
    rcases hj.2.2.1 with ⟨i, hi, _⟩
    rw [orIn_empty_of_noPrimaryOrInputs n C hC (n + j) (by omega)] at hi
    exact Finset.notMem_empty i hi
  simp [tCount, twoColour, hnone]

theorem expand_noPrimaryOrInputs (n j : ℕ) (gs : List Gate) :
    ∀ g ∈ expand n j gs, g.op = GateOp.or → ∀ w ∈ g.inputs, n ≤ w := by
  induction gs generalizing j with
  | nil => simp [expand]
  | cons head tail ih =>
    intro g hg hop w hw
    simp only [expand, List.mem_append] at hg
    rcases hg with hg | hg
    · simp only [block, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · cases hop
      · cases hop
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> omega
    · exact ih (j + 1) g hg hop w hw

theorem shield_noPrimaryOrInputs (n : ℕ) (C : Circuit) :
    NoPrimaryOrInputs n (shield n C) := expand_noPrimaryOrInputs n 0 C.gates

theorem shield_tCount_zero (n : ℕ) (C : Circuit) (isLine : ℕ → Bool) :
    tCount n (shield n C) isLine = 0 :=
  tCount_zero_of_noPrimaryOrInputs n (shield n C) (shield_noPrimaryOrInputs n C) isLine

private theorem small_getD_append (n : ℕ) (x : Fin n → Bool) (v : Bool) (out : ℕ) :
    (List.ofFn x ++ [v]).getD out false =
      if h : out < n then x ⟨out, h⟩ else if out = n then v else false := by
  by_cases ho : out < n
  · simp [List.getD, List.getElem?_append, ho]
  · by_cases he : out = n
    · subst out
      simp [List.getD]
    · have hs : 1 ≤ out - n := by omega
      simp only [List.getD, List.getElem?_append, List.length_ofFn, ite_eq_right ho]
      rw [List.getElem?_eq_none (by simpa using hs)]
      simp [ho, he]

private theorem small_singleton_eval (n : ℕ) (op : GateOp) (a b out : ℕ)
    (ha : a < n) (hb : b < n) (x : Fin n → Bool) :
    circuitFun n ⟨[⟨op, [a, b]⟩], out⟩ x =
      if h : out < n then x ⟨out, h⟩ else
      if out = n then op.eval [x ⟨a, ha⟩, x ⟨b, hb⟩] else false := by
  change (List.ofFn x ++
    [op.eval ([a, b].map fun w => (List.ofFn x).getD w false)]).getD out false = _
  rw [small_getD_append]
  simp [List.getD, List.getElem?_ofFn, ha, hb]

private theorem small_or_output_invalid (n a b out : ℕ) (ha : a < n) (hb : b < n)
    (hhot : ∀ i : Fin n,
      circuitFun n ⟨[⟨GateOp.or, [a, b]⟩], out⟩ (fun k => decide (k = i)) = false) :
    n + 1 ≤ out := by
  by_contra hnot
  have hle : out ≤ n := by omega
  by_cases ho : out < n
  · have h := hhot ⟨out, ho⟩
    rw [small_singleton_eval n GateOp.or a b out ha hb] at h
    simp [ho] at h
  · have he : out = n := by omega
    subst out
    have h := hhot ⟨a, ha⟩
    rw [small_singleton_eval n GateOp.or a b n ha hb] at h
    simp [GateOp.eval] at h

-- The size-one case needs no expansion: an AND already has empty OR reach;
-- an OR cannot have a valid output if all one-hot evaluations are false.
theorem small_case (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (hsize : C.size = 1)
    (hhot : ∀ i : Fin n, circuitFun n C (fun k => decide (k = i)) = false)
    (isLine : ℕ → Bool) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 4 ≤ 6 * C.size ∧
      circuitFun n D = circuitFun n C ∧ tCount n D isLine = 0 := by
  rcases C with ⟨gs, out⟩
  obtain ⟨g, rfl⟩ := List.length_eq_one_iff.mp hsize
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 g (by simp))
  rcases g with ⟨op, args⟩
  dsimp at hab
  subst args
  have ha : a < n := by
    have h := hAO.2.1 0 (by simp) a (by simp [gateAt])
    simpa using h
  have hb : b < n := by
    have h := hAO.2.1 0 (by simp) b (by simp [gateAt])
    simpa using h
  rcases hAO.1 ⟨op, [a, b]⟩ (by simp) with hop | hop
  · change op = GateOp.and at hop
    subst op
    refine ⟨⟨[⟨GateOp.and, [a, b]⟩], out⟩, hAO, ?_, rfl, ?_⟩
    · simp only [Circuit.size, List.length_cons, List.length_nil]
      omega
    · apply tCount_zero_of_noPrimaryOrInputs
      intro g hg hop
      simp only [List.mem_singleton] at hg
      subst g
      cases hop
  · change op = GateOp.or at hop
    subst op
    have hout := small_or_output_invalid n a b out ha hb hhot
    refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
    · simp [IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, ReadsBack]
    · simp only [Circuit.size, List.length_cons, List.length_nil]
      omega
    · funext x
      rw [small_singleton_eval n GateOp.or a b out ha hb]
      have ho : ¬out < n := by omega
      have he : out ≠ n := by omega
      simp [circuitFun, Circuit.eval, Circuit.wires, List.getD, ho, he]
    · apply tCount_zero_of_noPrimaryOrInputs
      simp [NoPrimaryOrInputs]




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour

def runStep (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

def simulation (n j : ℕ) (xs ys : List Bool) : Prop :=
  xs.length = n + j ∧ ys.length = n + 3 * j ∧
  ∀ w, ys.getD (ren n w) false = xs.getD w false

lemma ren_lt_eval {n j w : ℕ} (h : w < n + j) : ren n w < n + 3 * j := by
  unfold ren
  split <;> omega

lemma block_eval (n j : ℕ) (g : Gate) (ys : List Bool)
    (hlen : ys.length = n + 3 * j)
    (hb : ∀ w ∈ g.inputs, w < n + j) (hg : g.inputs.length = 2) :
    (block n j g).foldl runStep ys =
      ys ++ [ys.getD (ren n (g.inputs.getD 0 0)) false,
        ys.getD (ren n (g.inputs.getD 1 0)) false,
        g.op.eval [ys.getD (ren n (g.inputs.getD 0 0)) false,
          ys.getD (ren n (g.inputs.getD 1 0)) false]] := by
  rcases g with ⟨op, ins⟩
  rcases ins with _ | ⟨a, ins⟩ <;> simp only [List.length_nil, List.length_cons] at hg
  · omega
  rcases ins with _ | ⟨b, ins⟩ <;> simp only [List.length_nil, List.length_cons] at hg
  · omega
  have he : ins = [] := List.length_eq_zero_iff.mp (by omega)
  subst ins
  have ha : ren n a < ys.length := by rw [hlen]; apply ren_lt_eval; exact hb a (by simp)
  have hb' : ren n b < ys.length := by rw [hlen]; apply ren_lt_eval; exact hb b (by simp)
  simp only [block, List.getD_cons_zero, List.getD_cons_succ, List.foldl_cons,
    List.foldl_nil, runStep, List.map_cons, List.map_nil, GateOp.eval,
    List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_self]
  rw [List.getD_append _ _ _ _ hb']
  have hy0 : ((ys ++ [ys.getD (ren n a) false]) ++
      [ys.getD (ren n b) false]).getD (n + 3 * j) false = ys.getD (ren n a) false := by
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
    simp [hlen]
  have hy1 : ((ys ++ [ys.getD (ren n a) false]) ++
      [ys.getD (ren n b) false]).getD (n + 3 * j + 1) false = ys.getD (ren n b) false := by
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
    simp [hlen]
  rw [hy0, hy1]
  simp [List.append_assoc]

lemma simulation_append {n j : ℕ} {xs ys : List Bool} (hs : simulation n j xs ys)
    (a b v : Bool) : simulation n (j + 1) (xs ++ [v]) (ys ++ [a,b,v]) := by
  rcases hs with ⟨hx, hy, hs⟩
  refine ⟨by simp [hx]; omega, by simp [hy]; omega, ?_⟩
  intro w
  by_cases hw : w < n + j
  · rw [List.getD_append _ _ _ _ (by rw [hy]; exact ren_lt_eval hw),
      List.getD_append _ _ _ _ (by omega)]
    exact hs w
  · by_cases he : w = n + j
    · subst w
      have hr : ren n (n + j) = n + 3 * j + 2 := by simp [ren]
      rw [hr, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      simp [hx, hy]
    · rw [List.getD_eq_default _ _ (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        rw [hy]
        unfold ren
        split <;> omega), List.getD_eq_default _ _ (by simp [hx]; omega)]

lemma simulation_step {n j : ℕ} {xs ys : List Bool} (hs : simulation n j xs ys)
    (g : Gate) (hb : ∀ w ∈ g.inputs, w < n + j) (hg : g.inputs.length = 2) :
    simulation n (j + 1) (runStep xs g) ((block n j g).foldl runStep ys) := by
  rw [block_eval n j g ys hs.2.1 hb hg]
  simp only [hs.2.2]
  have hin : g.inputs = [g.inputs.getD 0 0, g.inputs.getD 1 0] := by
    obtain ⟨a, b, h⟩ := List.length_eq_two.mp hg
    rw [h]
    rfl
  unfold runStep
  have hm : g.inputs.map (fun i => xs.getD i false) =
      [xs.getD (g.inputs.getD 0 0) false, xs.getD (g.inputs.getD 1 0) false] := by
    conv_lhs => rw [hin]
    rfl
  rw [hm]
  exact simulation_append hs _ _ _

lemma simulation_fold (n j : ℕ) (gs : List Gate) (xs ys : List Bool)
    (hs : simulation n j xs ys)
    (hg : ∀ k < gs.length, (gs.getD k ⟨GateOp.or, []⟩).inputs.length = 2 ∧
      ∀ w ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, w < n + (j + k)) :
    simulation n (j + gs.length) (gs.foldl runStep xs)
      ((expand n j gs).foldl runStep ys) := by
  induction gs generalizing j xs ys with
  | nil => simpa [expand] using hs
  | cons g gs ih =>
    have hhead := hg 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at hhead
    have htail : ∀ k < gs.length,
        (gs.getD k ⟨GateOp.or, []⟩).inputs.length = 2 ∧
        ∀ w ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, w < n + (j + 1 + k) := by
      intro k hk
      simpa only [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1 k] using
        hg (k + 1) (by simp; omega)
    have hi := ih (j + 1) (runStep xs g) ((block n j g).foldl runStep ys)
      (simulation_step hs g hhead.2 hhead.1) htail
    simpa only [expand, List.foldl_append, List.foldl_cons, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1 gs.length] using hi

lemma simulation_initial (n : ℕ) (xs : List Bool) (hx : xs.length = n) :
    simulation n 0 xs xs := by
  refine ⟨by simpa using hx, by simpa using hx, ?_⟩
  intro w
  by_cases hw : w < n
  · simp [ren, hw]
  · rw [List.getD_eq_default _ _ (by unfold ren; split <;> omega),
      List.getD_eq_default _ _ (by omega)]

lemma shield_eval (n : ℕ) (C : Circuit) (hC : IsAO2 n C) :
    circuitFun n (shield n C) = circuitFun n C := by
  funext x
  have hg : ∀ k < C.gates.length,
      (C.gates.getD k ⟨GateOp.or, []⟩).inputs.length = 2 ∧
      ∀ w ∈ (C.gates.getD k ⟨GateOp.or, []⟩).inputs, w < n + (0 + k) := by
    intro k hk
    refine ⟨hC.2.2 _ ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    · simpa only [Nat.zero_add, PEqualNP.MetaComplexity.NestedCover.gateAt] using hC.2.1 k hk
  have hs := simulation_fold n 0 C.gates (List.ofFn x) (List.ofFn x)
    (simulation_initial n _ (by simp)) hg
  exact hs.2.2 C.output

end PEqualNP.Outside.L_meta_4791

open PEqualNP.Outside.L_meta_4791

theorem PEqualNP.Outside.L_meta_4791 : ∀ (p l : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (p + l) C → 1 ≤ C.size → (∀ i : Fin (p + l), PEqualNP.MetaComplexity.circuitFun (p + l) C (fun k => decide (k = i)) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (p + l) D ∧ D.size + 4 ≤ 6 * C.size ∧ PEqualNP.MetaComplexity.circuitFun (p + l) D = PEqualNP.MetaComplexity.circuitFun (p + l) C ∧ PEqualNP.TwoColour.tCount (p + l) D (fun i => decide (p ≤ i)) = 0 := by
  intro p l C hAO hpos hhot
  by_cases hs : C.size = 1
  · exact small_case (p + l) C hAO hs hhot (fun i => decide (p ≤ i))
  · refine ⟨shield (p + l) C, shield_isAO2 (p + l) C hAO, ?_,
      shield_eval (p + l) C hAO, shield_tCount_zero (p + l) C _⟩
    rw [shield_size]
    omega
