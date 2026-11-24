import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

-- One evaluation step: the wires so far, then the value of the next gate.
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g t ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g t ih =>
    rw [List.foldl_cons, ih (stepW w g) (by simp [stepW]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma gate_value (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (gs.foldl stepW x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl stepW x).getD i false) := by
  induction gs generalizing x j with
  | nil => simp at hj
  | cons g t ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at hback ⊢
      rw [foldl_getD_lt t (stepW x g) x.length (by simp [stepW])]
      have hval : (stepW x g).getD x.length false =
          g.op.eval (g.inputs.map fun i => x.getD i false) := by
        simp [stepW]
      rw [hval]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [foldl_getD_lt t (stepW x g) i (by simp [stepW]; have := hback i hi; omega)]
      exact (List.getD_append _ _ _ _ (hback i hi)).symm
    | succ k =>
      simp only [List.getElem_cons_succ] at hback ⊢
      have hlen : (stepW x g).length = x.length + 1 := by simp [stepW]
      have hk : k < t.length := by simpa using hj
      have e : x.length + (k + 1) = (stepW x g).length + k := by omega
      rw [e]
      exact ih (stepW x g) k hk (by intro i hi; have := hback i hi; omega)

lemma ofFn_getD (n : ℕ) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

-- The value of wire i of the gate list gs on the input x.
def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl stepW (List.ofFn x)).getD i false

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  unfold val
  rw [foldl_getD_lt gs _ i (by simpa using hi)]
  exact ofFn_getD n x i hi

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  apply List.getD_eq_default
  rw [foldl_length]
  simpa using hi

-- Gate j of gs is the gate op [a, b].
def IsGate (gs : List Gate) (j : ℕ) (op : GateOp) (a b : ℕ) : Prop :=
  gs[j]? = some ⟨op, [a, b]⟩

lemma IsGate.lt {gs : List Gate} {j : ℕ} {op : GateOp} {a b : ℕ} (h : IsGate gs j op a b) :
    j < gs.length := by
  unfold IsGate at h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

lemma IsGate.unique {gs : List Gate} {j : ℕ} {op op' : GateOp} {a b a' b' : ℕ}
    (h : IsGate gs j op a b) (h' : IsGate gs j op' a' b') : op = op' ∧ a = a' ∧ b = b' := by
  unfold IsGate at h h'
  rw [h] at h'
  simp only [Option.some.injEq, Gate.mk.injEq, List.cons.injEq, and_true] at h'
  exact h'

lemma val_isgate {n : ℕ} {gs : List Gate} {j : ℕ} {op : GateOp} {a b : ℕ}
    (h : IsGate gs j op a b) (ha : a < n + j) (hb : b < n + j) (x : Fin n → Bool) :
    val gs x (n + j) = op.eval [val gs x a, val gs x b] := by
  have hj := h.lt
  have hg : gs[j] = ⟨op, [a, b]⟩ := by
    unfold IsGate at h
    rw [List.getElem?_eq_getElem hj] at h
    exact Option.some.inj h
  have hv := gate_value gs (List.ofFn x) j hj (by
    rw [hg]
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> simpa using ‹_›)
  simp only [List.length_ofFn] at hv
  unfold val
  rw [hv, hg]
  rfl

lemma val_and {n : ℕ} {gs : List Gate} {j a b : ℕ}
    (h : IsGate gs j GateOp.and a b) (ha : a < n + j) (hb : b < n + j) (x : Fin n → Bool) :
    val gs x (n + j) = (val gs x a && val gs x b) := by
  rw [val_isgate h ha hb]
  simp [GateOp.eval]

lemma val_or {n : ℕ} {gs : List Gate} {j a b : ℕ}
    (h : IsGate gs j GateOp.or a b) (ha : a < n + j) (hb : b < n + j) (x : Fin n → Bool) :
    val gs x (n + j) = (val gs x a || val gs x b) := by
  rw [val_isgate h ha hb]
  simp [GateOp.eval]

-- Every gate is an AND or an OR of two earlier wires.
def Good (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j, j < gs.length → ∃ op a b, IsGate gs j op a b ∧ (op = GateOp.and ∨ op = GateOp.or) ∧
    a < n + j ∧ b < n + j

lemma isgate_gateAt {C : Circuit} {j : ℕ} {op : GateOp} {a b : ℕ} (h : IsGate C.gates j op a b) :
    gateAt C j = ⟨op, [a, b]⟩ := by
  unfold gateAt
  unfold IsGate at h
  rw [List.getD_eq_getElem?_getD, h]
  rfl

lemma good_of_ao2 {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Good n C.gates := by
  obtain ⟨hao, hrb, h2⟩ := h
  intro j hj
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ hmem)
  have hg : IsGate C.gates j C.gates[j].op a b := by
    unfold IsGate
    rw [List.getElem?_eq_getElem hj, ← hab]
  have hga := isgate_gateAt hg
  refine ⟨C.gates[j].op, a, b, hg, hao _ hmem, ?_, ?_⟩
  · exact hrb j hj a (by rw [hga]; simp)
  · exact hrb j hj b (by rw [hga]; simp)

lemma ao2_of_good {n : ℕ} {gs : List Gate} (h : Good n gs) (o : ℕ) : IsAO2 n ⟨gs, o⟩ := by
  have key : ∀ g ∈ gs, ∃ j op a b, IsGate gs j op a b ∧ g = ⟨op, [a, b]⟩ ∧
      (op = GateOp.and ∨ op = GateOp.or) ∧ a < n + j ∧ b < n + j := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨op, a, b, h1, h2, h3, h4⟩ := h j hj
    refine ⟨j, op, a, b, h1, ?_, h2, h3, h4⟩
    unfold IsGate at h1
    rw [List.getElem?_eq_getElem hj] at h1
    exact Option.some.inj h1
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, op, a, b, _, rfl, h2, _⟩ := key g hg
    exact h2
  · intro j hj i hi
    obtain ⟨op, a, b, h1, _, h3, h4⟩ := h j hj
    rw [isgate_gateAt (C := ⟨gs, o⟩) h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨j, op, a, b, _, rfl, _⟩ := key g hg
    rfl

lemma circuitFun_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C.gates x C.output := rfl

lemma gateVal_eq (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = val C.gates x (n + j) := rfl

lemma mono {n : ℕ} {gs : List Gate} (hG : Good n gs) (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) : ∀ w, val gs x w = true → val gs y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [val_lt _ _ _ h1] at hw ⊢
      exact h _ hw
    · by_cases h2 : n + gs.length ≤ w
      · rw [val_ge _ _ _ h2] at hw
        cases hw
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        obtain ⟨op, a, b, hg, hop, ha, hb⟩ := hG j (by omega)
        rcases hop with rfl | rfl
        · rw [val_and hg ha hb, Bool.and_eq_true] at hw ⊢
          exact ⟨ih a ha hw.1, ih b hb hw.2⟩
        · rw [val_or hg ha hb, Bool.or_eq_true] at hw ⊢
          exact hw.imp (ih a ha) (ih b hb)

lemma ones {n : ℕ} {gs : List Gate} (hG : Good n gs) :
    ∀ w, w < n + gs.length → val gs (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [val_lt _ _ _ h1]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      obtain ⟨op, a, b, hg, hop, ha, hb⟩ := hG j (by omega)
      rcases hop with rfl | rfl
      · rw [val_and hg ha hb, ih a ha (by omega), ih b hb (by omega)]
        rfl
      · rw [val_or hg ha hb, ih a ha (by omega)]
        rfl

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

/-! Cones -/

lemma cs_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g t ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cs_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < cs.length) :
    (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g t ih =>
    rw [List.foldl_cons, ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact List.getD_append _ _ _ _ hj

lemma cs_at (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) cs).getD (cs.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cs.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) cs).getD (w - n) []) := by
  induction gs generalizing cs j with
  | nil => simp at hj
  | cons g t ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero]
      rw [cs_getD_lt n t (coneStep n cs g) cs.length (by simp [coneStep])]
      have hval : (coneStep n cs g).getD cs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => (w - n) :: cs.getD (w - n) []) := by
        simp [coneStep]
      rw [hval, List.flatMap_def, List.flatMap_def]
      congr 1
      apply List.map_congr_left
      intro w hw
      have hw2 : n ≤ w ∧ w < n + cs.length := by simpa using (List.mem_filter.mp hw).2
      rw [cs_getD_lt n t (coneStep n cs g) (w - n) (by simp [coneStep]; omega)]
      congr 1
      exact (List.getD_append _ _ _ _ (by omega)).symm
    | succ k =>
      simp only [List.getElem_cons_succ]
      have hlen : (coneStep n cs g).length = cs.length + 1 := by simp [coneStep]
      have hk : k < t.length := by simpa using hj
      have e : cs.length + (k + 1) = (coneStep n cs g).length + k := by omega
      rw [e]
      exact ih (coneStep n cs g) k hk

lemma cone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (op : GateOp) (a b : ℕ)
    (h : IsGate C.gates j op a b) :
    InCone n C i j ↔ ∃ w, (w = a ∨ w = b) ∧ n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  have hj := h.lt
  have hg : C.gates[j] = ⟨op, [a, b]⟩ := by
    unfold IsGate at h
    rw [List.getElem?_eq_getElem hj] at h
    exact Option.some.inj h
  unfold InCone cones
  have := cs_at n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at this
  rw [this, hg]
  simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
    decide_eq_true_eq]
  constructor
  · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
    exact ⟨w, hw, h1, h2, h3⟩
  · rintro ⟨w, hw, h1, h2, h3⟩
    exact ⟨w, ⟨hw, h1, h2⟩, h3⟩

lemma cone_ge (n : ℕ) (C : Circuit) (i j : ℕ) (hj : C.gates.length ≤ j) : ¬ InCone n C i j := by
  unfold InCone cones
  rw [List.getD_eq_default _ _ (by rw [cs_length]; simpa using hj)]
  simp

-- A gate strictly inside a cone has a smaller index and is read by some gate.
lemma cone_lt_reader (n : ℕ) (C : Circuit) (hG : Good n C.gates) :
    ∀ j i, InCone n C i j → i < j ∧ ∃ k op a b, IsGate C.gates k op a b ∧ (a = n + i ∨ b = n + i) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i hi
    by_cases hj : j < C.gates.length
    · obtain ⟨op, a, b, hg, _, _, _⟩ := hG j hj
      obtain ⟨w, hw, h1, h2, h3⟩ := (cone_iff n C i j op a b hg).mp hi
      rcases h3 with h3 | h3
      · refine ⟨by omega, j, op, a, b, hg, ?_⟩
        rcases hw with rfl | rfl
        · left; omega
        · right; omega
      · obtain ⟨h4, h5⟩ := ih (w - n) (by omega) i h3
        exact ⟨by omega, h5⟩
    · exact absurd hi (cone_ge n C i j (by omega))

-- A sufficient condition for: no AND gate strictly inside the cone of an AND gate.
lemma no_stack (n : ℕ) (D : Circuit) (hG : Good n D.gates) (P : ℕ → Prop)
    (hA : ∀ j a b, IsGate D.gates j GateOp.and a b → P a ∧ P b)
    (hP : ∀ j op a b, IsGate D.gates j op a b → P (n + j) → op = GateOp.or ∧ P a ∧ P b) :
    ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
      (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  have key : ∀ j op a b, IsGate D.gates j op a b → P a → P b → ∀ i, InCone n D i j → P (n + i) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro op a b hg ha hb i hi
      obtain ⟨w, hw, h1, h2, h3⟩ := (cone_iff n D i j op a b hg).mp hi
      have hPw : P w := by rcases hw with rfl | rfl <;> assumption
      rcases h3 with h3 | h3
      · rw [h3, Nat.add_sub_cancel' h1]
        exact hPw
      · have hlt : w - n < D.gates.length := by have := hg.lt; omega
        obtain ⟨op', a', b', hg', _, _, _⟩ := hG (w - n) hlt
        have hPw' : P (n + (w - n)) := by rw [Nat.add_sub_cancel' h1]; exact hPw
        obtain ⟨_, ha', hb'⟩ := hP _ _ _ _ hg' hPw'
        exact ih (w - n) (by omega) op' a' b' hg' ha' hb' i h3
  intro i hi j hj hopi hopj hc
  obtain ⟨op, a, b, hg, _, _, _⟩ := hG j hj
  rw [isgate_gateAt hg] at hopj
  simp only at hopj
  subst hopj
  obtain ⟨ha, hb⟩ := hA j a b hg
  have hPi := key j _ a b hg ha hb i hc
  obtain ⟨op', a', b', hg', _, _, _⟩ := hG i hi
  obtain ⟨h1, _, _⟩ := hP _ _ _ _ hg' hPi
  rw [isgate_gateAt hg'] at hopi
  simp only at hopi
  rw [h1] at hopi
  cases hopi

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

/-! Gate lists given by a function of the slot, and deleting an unread slot -/

def mk (f : ℕ → Gate) (len : ℕ) : List Gate := (List.range len).map f

lemma mk_len (f : ℕ → Gate) (len : ℕ) : (mk f len).length = len := by simp [mk]

lemma mk_isgate (f : ℕ → Gate) (len j : ℕ) (op : GateOp) (a b : ℕ) :
    IsGate (mk f len) j op a b ↔ j < len ∧ f j = ⟨op, [a, b]⟩ := by
  constructor
  · intro h
    have hj : j < len := by have := h.lt; rwa [mk_len] at this
    refine ⟨hj, ?_⟩
    unfold IsGate mk at h
    rw [List.getElem?_eq_getElem (by simpa using hj)] at h
    simpa using h
  · rintro ⟨hj, hf⟩
    unfold IsGate mk
    rw [List.getElem?_eq_getElem (by simpa using hj)]
    simp [hf]

lemma isgate_append_left {gs t : List Gate} {j : ℕ} {op : GateOp} {a b : ℕ} (hj : j < gs.length) :
    IsGate (gs ++ t) j op a b ↔ IsGate gs j op a b := by
  unfold IsGate
  rw [List.getElem?_append_left hj]

-- The wire renaming when slot j0 is deleted, and the old slot behind a new slot.
def rho (n j0 w : ℕ) : ℕ := if w < n + j0 then w else w - 1
def sig (j0 j' : ℕ) : ℕ := if j' < j0 then j' else j' + 1

def delG (n j0 : ℕ) (gs : List Gate) : List Gate :=
  mk (fun j' => ⟨(gs.getD (sig j0 j') ⟨GateOp.or, []⟩).op,
    ((gs.getD (sig j0 j') ⟨GateOp.or, []⟩).inputs).map (rho n j0)⟩) (gs.length - 1)

lemma del_len (n j0 : ℕ) (gs : List Gate) : (delG n j0 gs).length = gs.length - 1 := mk_len _ _

lemma del_isgate {n j0 : ℕ} {gs : List Gate} {j' : ℕ} {op : GateOp} {a b : ℕ}
    (hj' : j' < gs.length - 1) (h : IsGate gs (sig j0 j') op a b) :
    IsGate (delG n j0 gs) j' op (rho n j0 a) (rho n j0 b) := by
  unfold delG
  rw [mk_isgate]
  refine ⟨hj', ?_⟩
  have : gs.getD (sig j0 j') ⟨GateOp.or, []⟩ = ⟨op, [a, b]⟩ := by
    unfold IsGate at h
    rw [List.getD_eq_getElem?_getD, h]
    rfl
  rw [this]
  rfl

lemma del_good {n j0 : ℕ} {gs : List Gate} (hG : Good n gs)
    (hun : ∀ j op a b, IsGate gs j op a b → a ≠ n + j0 ∧ b ≠ n + j0) : Good n (delG n j0 gs) := by
  intro j' hj'
  rw [del_len] at hj'
  obtain ⟨op, a, b, hg, hop, ha, hb⟩ := hG (sig j0 j') (by unfold sig; split_ifs <;> omega)
  obtain ⟨ha2, hb2⟩ := hun _ _ _ _ hg
  refine ⟨op, _, _, del_isgate hj' hg, hop, ?_, ?_⟩ <;>
  · unfold rho sig at *
    split_ifs at * <;> omega

lemma del_val {n j0 : ℕ} {gs : List Gate} (hG : Good n gs)
    (hun : ∀ j op a b, IsGate gs j op a b → a ≠ n + j0 ∧ b ≠ n + j0) (hj0 : j0 < gs.length)
    (x : Fin n → Bool) :
    ∀ w, w < n + gs.length → w ≠ n + j0 → val (delG n j0 gs) x (rho n j0 w) = val gs x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hne
    by_cases h1 : w < n
    · have : rho n j0 w = w := by simp only [rho]; split_ifs <;> omega
      rw [this, val_lt _ _ _ h1, val_lt _ _ _ h1]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < gs.length := by omega
      have hjne : j ≠ j0 := by omega
      obtain ⟨op, a, b, hg, hop, ha, hb⟩ := hG j hj
      obtain ⟨ha2, hb2⟩ := hun _ _ _ _ hg
      obtain ⟨j', hj'1, hj'2, hj'3⟩ : ∃ j', sig j0 j' = j ∧ rho n j0 (n + j) = n + j' ∧
          j' < gs.length - 1 := by
        by_cases hlt : j < j0
        · refine ⟨j, ?_, ?_, by omega⟩ <;> · simp only [sig, rho]; split_ifs <;> omega
        · refine ⟨j - 1, ?_, ?_, by omega⟩ <;> · simp only [sig, rho]; split_ifs <;> omega
      have hg' := del_isgate (n := n) hj'3 (hj'1 ▸ hg)
      have ha' : rho n j0 a < n + j' := by unfold rho sig at *; split_ifs at * <;> omega
      have hb' : rho n j0 b < n + j' := by unfold rho sig at *; split_ifs at * <;> omega
      rw [hj'2, val_isgate hg' ha' hb', val_isgate hg ha hb, ih a ha (by omega) ha2,
        ih b hb (by omega) hb2]

-- Every gate of the shortened list comes from a gate of the old one.
lemma del_gate_inv {n j0 : ℕ} {gs : List Gate} (hG : Good n gs) {j' : ℕ} {op : GateOp} {a' b' : ℕ}
    (h : IsGate (delG n j0 gs) j' op a' b') :
    ∃ a b, IsGate gs (sig j0 j') op a b ∧ a' = rho n j0 a ∧ b' = rho n j0 b := by
  have hj' : j' < gs.length - 1 := by have := h.lt; rwa [del_len] at this
  obtain ⟨op2, a, b, hg, _, _, _⟩ := hG (sig j0 j') (by unfold sig; split_ifs <;> omega)
  obtain ⟨h1, h2, h3⟩ := (del_isgate (n := n) hj' hg).unique h
  subst h1
  exact ⟨a, b, hg, h2.symm, h3.symm⟩

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

/-! The frame: below-F wires, and the facts about the given circuit that the construction uses -/

-- Wire w is below F.
def BW {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val C.gates x w = true → graphFun G ∅ x = true

lemma F_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

lemma F_eof {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    graphFun G ∅ (eof i) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [F_iff] at h
  obtain ⟨u, v, huv, hu, hv⟩ := h
  simp only [eof, decide_eq_true_eq] at hu hv
  rw [hu, hv] at huv
  exact huv.ne rfl

lemma notBW_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ)
    (hw : w < n) : ¬ BW G C w := by
  intro h
  have h2 := h (eof ⟨w, hw⟩) (by rw [val_lt _ _ _ hw]; simp [eof])
  rw [F_eof] at h2
  cases h2

-- The facts about the given circuit that the construction uses.
def Str {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ) : Prop :=
  (Good n C.gates) ∧
  (0 < n) ∧
  (g < C.gates.length) ∧
  (∀ j a b, IsGate C.gates j GateOp.and a b → j ≠ g → BW G C (n + j)) ∧
  (¬ BW G C (n + g)) ∧
  (BW G C (n + (C.gates.length - 1))) ∧
  (∀ j < C.gates.length, BW G C (n + j) → j ≠ C.gates.length - 1 →
      ∃ k a b, IsGate C.gates k GateOp.or a b ∧ BW G C (n + k) ∧ (a = n + j ∨ b = n + j))

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

lemma Str.intro (good : Good n C.gates)
    (npos : 0 < n)
    (glt : g < C.gates.length)
    (top_bw : ∀ j a b, IsGate C.gates j GateOp.and a b → j ≠ g → BW G C (n + j))
    (g_nbw : ¬ BW G C (n + g))
    (out_bw : BW G C (n + (C.gates.length - 1)))
    (reader : ∀ j < C.gates.length, BW G C (n + j) → j ≠ C.gates.length - 1 →
      ∃ k a b, IsGate C.gates k GateOp.or a b ∧ BW G C (n + k) ∧ (a = n + j ∨ b = n + j)) :
    Str G C g := by
  unfold Str
  exact ⟨good, npos, glt, top_bw, g_nbw, out_bw, reader⟩

lemma Str.good (H : Str G C g) :
    Good n C.gates := by
  unfold Str at H
  exact H.1

lemma Str.npos (H : Str G C g) :
    0 < n := by
  unfold Str at H
  exact H.2.1

lemma Str.glt (H : Str G C g) :
    g < C.gates.length := by
  unfold Str at H
  exact H.2.2.1

lemma Str.top_bw (H : Str G C g) :
    ∀ j a b, IsGate C.gates j GateOp.and a b → j ≠ g → BW G C (n + j) := by
  unfold Str at H
  exact H.2.2.2.1

lemma Str.g_nbw (H : Str G C g) :
    ¬ BW G C (n + g) := by
  unfold Str at H
  exact H.2.2.2.2.1

lemma Str.out_bw (H : Str G C g) :
    BW G C (n + (C.gates.length - 1)) := by
  unfold Str at H
  exact H.2.2.2.2.2.1

lemma Str.reader (H : Str G C g) :
    ∀ j < C.gates.length, BW G C (n + j) → j ≠ C.gates.length - 1 →
      ∃ k a b, IsGate C.gates k GateOp.or a b ∧ BW G C (n + k) ∧ (a = n + j ∨ b = n + j) := by
  unfold Str at H
  exact H.2.2.2.2.2.2

end

-- Wires that get a canonical copy: not below F, not the gate g, with a nonempty set.
def Okw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (Sg : ℕ → Finset (Fin n)) (w : ℕ) : Prop :=
  w < n + C.gates.length ∧ ¬ BW G C w ∧ (Sg w).Nonempty ∧ w ≠ n + g

-- The first wire with its set.
def Can {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (Sg : ℕ → Finset (Fin n)) (w : ℕ) : Prop :=
  Okw G C g Sg w ∧ ∀ v < w, Okw G C g Sg v → Sg v ≠ Sg w

lemma exists_rep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (Sg : ℕ → Finset (Fin n)) (w : ℕ) (hw : Okw G C g Sg w) :
    ∃ r, Can G C g Sg r ∧ Sg r = Sg w ∧ r ≤ w := by
  classical
  have h : ∃ v, Okw G C g Sg v ∧ Sg v = Sg w := ⟨w, hw, rfl⟩
  refine ⟨Nat.find h, ⟨(Nat.find_spec h).1, ?_⟩, (Nat.find_spec h).2, Nat.find_min' h ⟨hw, rfl⟩⟩
  intro v hv hOk heq
  exact Nat.find_min h hv ⟨hOk, heq.trans (Nat.find_spec h).2⟩

-- The slots below the tops: the gate g and the OR gates that are not below F.
def LowSlot {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (j : ℕ) : Prop :=
  j = g ∨ ∃ a b, IsGate C.gates j GateOp.or a b ∧ ¬ BW G C (n + j)

def PLow {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (w : ℕ) : Prop :=
  w < n ∨ ∃ j, w = n + j ∧ j < C.gates.length ∧ LowSlot G C g j

open Classical in
noncomputable def newGate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) (Sg : ℕ → Finset (Fin n)) (lo tc : ℕ → ℕ × ℕ) (j : ℕ) : Gate :=
  if Can G C g Sg (n + j) then ⟨GateOp.or, [(lo j).1, (lo j).2]⟩
  else if (gateAt C j).op = GateOp.and ∧ j ≠ g then ⟨GateOp.and, [(tc j).1, (tc j).2]⟩
  else if (gateAt C j).op = GateOp.or ∧ BW G C (n + j) then gateAt C j
  else ⟨GateOp.or, [0, 0]⟩

lemma okw_plow {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}
    (H : Str G C g) {Sg : ℕ → Finset (Fin n)} {w : ℕ} (hw : Okw G C g Sg w) : PLow G C g w := by
  obtain ⟨h1, h2, _, h4⟩ := hw
  by_cases hn : w < n
  · exact Or.inl hn
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    refine Or.inr ⟨j, rfl, by omega, ?_⟩
    obtain ⟨op, a, b, hgt, hop, _, _⟩ := H.good j (by omega)
    rcases hop with rfl | rfl
    · exact absurd (H.top_bw j a b hgt (by omega)) h2
    · exact Or.inr ⟨a, b, hgt, h2⟩

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

lemma bw_or_ops {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}
    (H : Str G C g) {j a b : ℕ} (hgt : IsGate C.gates j GateOp.or a b) (hbw : BW G C (n + j)) :
    a < n + j ∧ b < n + j ∧ BW G C a ∧ BW G C b := by
  obtain ⟨op, a', b', hgt', _, ha, hb⟩ := H.good j hgt.lt
  obtain ⟨_, rfl, rfl⟩ := hgt.unique hgt'
  refine ⟨ha, hb, fun x hx => hbw x ?_, fun x hx => hbw x ?_⟩
  · rw [val_or hgt ha hb, hx]; rfl
  · rw [val_or hgt ha hb, hx]; simp

lemma lowslot_nbw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}
    (H : Str G C g) {j : ℕ} (h : LowSlot G C g j) : ¬ BW G C (n + j) := by
  rcases h with rfl | ⟨a, b, _, h⟩
  · exact H.g_nbw
  · exact h

-- The construction: the lower slots become canonical ORs, the tops read canonical wires.
theorem build_core {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (H : Str G C g) (Sg : ℕ → Finset (Fin n))
    (hv : ∀ i (hi : i < n), Sg i = {⟨i, hi⟩})
    (hl : ∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) → Okw G C g Sg (n + j) →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        Sg y1 ∪ Sg y2 = Sg (n + j))
    (want : ℕ → Finset (Fin n) × Finset (Fin n))
    (ht : ∀ j a b, IsGate C.gates j GateOp.and a b → j ≠ g →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        (∀ u ∈ Sg y1, ∀ v ∈ Sg y2, G.Adj u v) ∧ (want j).1 ⊆ Sg y1 ∧ (want j).2 ⊆ Sg y2) :
    ∃ gs : List Gate, gs.length = C.gates.length ∧ Good n gs ∧
      (∀ x, val gs x (n + (C.gates.length - 1)) = true → graphFun G ∅ x = true) ∧
      (∀ j a b, IsGate C.gates j GateOp.and a b → j ≠ g → ∀ u ∈ (want j).1, ∀ v ∈ (want j).2,
        ∀ x : Fin n → Bool, x u = true → x v = true →
          val gs x (n + (C.gates.length - 1)) = true) ∧
      (∀ w, Okw G C g Sg w → ∃ r, r ≤ w ∧ Can G C g Sg r ∧
        ∀ x : Fin n → Bool, (val gs x r = true ↔ ∃ u ∈ Sg w, x u = true)) ∧
      (∀ j a b, IsGate gs j GateOp.and a b → PLow G C g a ∧ PLow G C g b) ∧
      (∀ j op a b, IsGate gs j op a b → PLow G C g (n + j) →
        op = GateOp.or ∧ PLow G C g a ∧ PLow G C g b) ∧
      (∀ j1, LowSlot G C g j1 → ¬ Can G C g Sg (n + j1) →
        ∀ j op a b, IsGate gs j op a b → a ≠ n + j1 ∧ b ≠ n + j1) := by
  classical
  have hl' : ∀ j, ∃ p : ℕ × ℕ, Can G C g Sg (n + j) →
      Can G C g Sg p.1 ∧ Can G C g Sg p.2 ∧ p.1 < n + j ∧ p.2 < n + j ∧
        Sg p.1 ∪ Sg p.2 = Sg (n + j) := by
    intro j
    by_cases hc : Can G C g Sg (n + j)
    · obtain ⟨h1, h2, h3, h4⟩ := hc.1
      obtain ⟨op, a, b, hgt, hop, _, _⟩ := H.good j (by omega)
      rcases hop with rfl | rfl
      · exact absurd (H.top_bw j a b hgt (by omega)) h2
      · obtain ⟨y1, y2, hy1, hy2, hlt1, hlt2, hu⟩ := hl j a b hgt h2 hc.1
        obtain ⟨r1, hr1, he1, hle1⟩ := exists_rep G C g Sg y1 hy1
        obtain ⟨r2, hr2, he2, hle2⟩ := exists_rep G C g Sg y2 hy2
        refine ⟨(r1, r2), fun _ => ⟨hr1, hr2, by dsimp only; omega, by dsimp only; omega, ?_⟩⟩
        dsimp only
        rw [he1, he2]
        exact hu
    · exact ⟨(0, 0), fun h => absurd h hc⟩
  choose lo hlo using hl'
  have ht' : ∀ j, ∃ p : ℕ × ℕ, (∃ a b, IsGate C.gates j GateOp.and a b) → j ≠ g →
      Can G C g Sg p.1 ∧ Can G C g Sg p.2 ∧ p.1 < n + j ∧ p.2 < n + j ∧
      (∀ u ∈ Sg p.1, ∀ v ∈ Sg p.2, G.Adj u v) ∧ (want j).1 ⊆ Sg p.1 ∧ (want j).2 ⊆ Sg p.2 := by
    intro j
    by_cases hc : (∃ a b, IsGate C.gates j GateOp.and a b) ∧ j ≠ g
    · obtain ⟨⟨a, b, hgt⟩, hne⟩ := hc
      obtain ⟨y1, y2, hy1, hy2, hlt1, hlt2, hadj, hw1, hw2⟩ := ht j a b hgt hne
      obtain ⟨r1, hr1, he1, hle1⟩ := exists_rep G C g Sg y1 hy1
      obtain ⟨r2, hr2, he2, hle2⟩ := exists_rep G C g Sg y2 hy2
      refine ⟨(r1, r2), fun _ _ => ⟨hr1, hr2, by dsimp only; omega, by dsimp only; omega, ?_, ?_, ?_⟩⟩
      · dsimp only; rw [he1, he2]; exact hadj
      · dsimp only; rw [he1]; exact hw1
      · dsimp only; rw [he2]; exact hw2
    · exact ⟨(0, 0), fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose tc htc using ht'
  set gs := mk (newGate G C g Sg lo tc) C.gates.length with hgs
  have glen : gs.length = C.gates.length := mk_len _ _
  have gCan : ∀ j, Can G C g Sg (n + j) → IsGate gs j GateOp.or (lo j).1 (lo j).2 := by
    intro j hc
    rw [hgs, mk_isgate]
    refine ⟨by have := hc.1.1; omega, ?_⟩
    unfold newGate
    rw [ite_eq_left hc]
  have gTop : ∀ j a b, IsGate C.gates j GateOp.and a b → j ≠ g →
      IsGate gs j GateOp.and (tc j).1 (tc j).2 := by
    intro j a b hgt hne
    rw [hgs, mk_isgate]
    refine ⟨hgt.lt, ?_⟩
    have hnc : ¬ Can G C g Sg (n + j) := fun hc => hc.1.2.1 (H.top_bw j a b hgt hne)
    unfold newGate
    rw [ite_eq_right hnc, ite_eq_left ⟨by rw [isgate_gateAt hgt], hne⟩]
  have gUp : ∀ j a b, IsGate C.gates j GateOp.or a b → BW G C (n + j) →
      IsGate gs j GateOp.or a b := by
    intro j a b hgt hbw
    rw [hgs, mk_isgate]
    refine ⟨hgt.lt, ?_⟩
    have hnc : ¬ Can G C g Sg (n + j) := fun hc => hc.1.2.1 hbw
    unfold newGate
    rw [ite_eq_right hnc, ite_eq_right (by rw [isgate_gateAt hgt]; simp),
      ite_eq_left ⟨by rw [isgate_gateAt hgt], hbw⟩, isgate_gateAt hgt]
  have gDum : ∀ j, j < C.gates.length → LowSlot G C g j → ¬ Can G C g Sg (n + j) →
      IsGate gs j GateOp.or 0 0 := by
    intro j hj hls hnc
    rw [hgs, mk_isgate]
    refine ⟨hj, ?_⟩
    have hnbw := lowslot_nbw H hls
    unfold newGate
    rw [ite_eq_right hnc, ite_eq_right ?_, ite_eq_right (fun h => hnbw h.2)]
    rintro ⟨h1, h2⟩
    rcases hls with rfl | ⟨a, b, hgt, _⟩
    · exact h2 rfl
    · rw [isgate_gateAt hgt] at h1
      simp at h1
  have cls : ∀ j, j < C.gates.length →
      (Can G C g Sg (n + j) ∧ IsGate gs j GateOp.or (lo j).1 (lo j).2) ∨
      (∃ a b, IsGate C.gates j GateOp.and a b ∧ j ≠ g ∧ IsGate gs j GateOp.and (tc j).1 (tc j).2) ∨
      (∃ a b, IsGate C.gates j GateOp.or a b ∧ BW G C (n + j) ∧ IsGate gs j GateOp.or a b) ∨
      (LowSlot G C g j ∧ ¬ Can G C g Sg (n + j) ∧ IsGate gs j GateOp.or 0 0) := by
    intro j hj
    by_cases hc : Can G C g Sg (n + j)
    · exact Or.inl ⟨hc, gCan j hc⟩
    · obtain ⟨op, a, b, hgt, hop, _, _⟩ := H.good j hj
      rcases hop with rfl | rfl
      · by_cases hjg : j = g
        · exact Or.inr (Or.inr (Or.inr ⟨Or.inl hjg, hc, gDum j hj (Or.inl hjg) hc⟩))
        · exact Or.inr (Or.inl ⟨a, b, hgt, hjg, gTop j a b hgt hjg⟩)
      · by_cases hbw : BW G C (n + j)
        · exact Or.inr (Or.inr (Or.inl ⟨a, b, hgt, hbw, gUp j a b hgt hbw⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨Or.inr ⟨a, b, hgt, hbw⟩, hc,
            gDum j hj (Or.inr ⟨a, b, hgt, hbw⟩) hc⟩))
  have hgood : Good n gs := by
    intro j hj
    rw [glen] at hj
    rcases cls j hj with ⟨hc, hg1⟩ | ⟨a, b, hgt, hne, hg1⟩ | ⟨a, b, hgt, hbw, hg1⟩ | ⟨_, _, hg1⟩
    · obtain ⟨_, _, h3, h4, _⟩ := hlo j hc
      exact ⟨_, _, _, hg1, Or.inr rfl, h3, h4⟩
    · obtain ⟨_, _, h3, h4, _⟩ := htc j ⟨a, b, hgt⟩ hne
      exact ⟨_, _, _, hg1, Or.inl rfl, h3, h4⟩
    · obtain ⟨h3, h4, _⟩ := bw_or_ops H hgt hbw
      exact ⟨_, _, _, hg1, Or.inr rfl, h3, h4⟩
    · exact ⟨_, _, _, hg1, Or.inr rfl, by have := H.npos; omega, by have := H.npos; omega⟩
  have semCan : ∀ w, Can G C g Sg w → ∀ x : Fin n → Bool,
      (val gs x w = true ↔ ∃ u ∈ Sg w, x u = true) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hc x
      by_cases hw : w < n
      · rw [val_lt _ _ _ hw, hv w hw]
        simp
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        obtain ⟨h1, h2, h3, h4, h5⟩ := hlo j hc
        rw [val_or (gCan j hc) h3 h4, Bool.or_eq_true, ih _ h3 h1, ih _ h4 h2, ← h5]
        simp only [Finset.mem_union]
        constructor
        · rintro (⟨u, hu, hx⟩ | ⟨u, hu, hx⟩)
          · exact ⟨u, Or.inl hu, hx⟩
          · exact ⟨u, Or.inr hu, hx⟩
        · rintro ⟨u, hu | hu, hx⟩
          · exact Or.inl ⟨u, hu, hx⟩
          · exact Or.inr ⟨u, hu, hx⟩
  have sound : ∀ x : Fin n → Bool, ∀ w, w < n + C.gates.length → BW G C w →
      val gs x w = true → graphFun G ∅ x = true := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hbw hval
      by_cases hwn : w < n
      · exact absurd hbw (notBW_input G C w hwn)
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        rcases cls j (by omega) with ⟨hc, _⟩ | ⟨a, b, hgt, hne, hg1⟩ | ⟨a, b, hgt, _, hg1⟩ | ⟨hls, _, _⟩
        · exact absurd hbw hc.1.2.1
        · obtain ⟨h1, h2, h3, h4, hadj, _, _⟩ := htc j ⟨a, b, hgt⟩ hne
          rw [val_and hg1 h3 h4, Bool.and_eq_true, semCan _ h1, semCan _ h2] at hval
          obtain ⟨⟨u, hu, hxu⟩, ⟨v, hv', hxv⟩⟩ := hval
          rw [F_iff]
          exact ⟨u, v, hadj u hu v hv', hxu, hxv⟩
        · obtain ⟨h3, h4, hba, hbb⟩ := bw_or_ops H hgt hbw
          rw [val_or hg1 h3 h4, Bool.or_eq_true] at hval
          rcases hval with hval | hval
          · exact ih a h3 (by omega) hba hval
          · exact ih b h4 (by omega) hbb hval
        · exact absurd hbw (lowslot_nbw H hls)
  have upw : ∀ x : Fin n → Bool, ∀ d j, C.gates.length - j = d → j < C.gates.length →
      BW G C (n + j) → val gs x (n + j) = true →
      val gs x (n + (C.gates.length - 1)) = true := by
    intro x d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hd hj hbw hval
      by_cases hlast : j = C.gates.length - 1
      · rw [← hlast]; exact hval
      · obtain ⟨k, a, b, hgt, hbwk, hab⟩ := H.reader j hj hbw hlast
        obtain ⟨h3, h4, _, _⟩ := bw_or_ops H hgt hbwk
        have hk := hgt.lt
        refine ih (C.gates.length - k) (by rcases hab with rfl | rfl <;> omega) k rfl hk hbwk ?_
        rw [val_or (gUp k a b hgt hbwk) h3 h4, Bool.or_eq_true]
        rcases hab with rfl | rfl
        · exact Or.inl hval
        · exact Or.inr hval
  refine ⟨gs, glen, hgood, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have := H.glt
    exact sound x _ (by omega) H.out_bw hx
  · intro j a b hgt hne u hu v hv' x hxu hxv
    obtain ⟨h1, h2, h3, h4, _, hw1, hw2⟩ := htc j ⟨a, b, hgt⟩ hne
    refine upw x _ j rfl hgt.lt (H.top_bw j a b hgt hne) ?_
    rw [val_and (gTop j a b hgt hne) h3 h4, Bool.and_eq_true, semCan _ h1, semCan _ h2]
    exact ⟨⟨u, hw1 hu, hxu⟩, ⟨v, hw2 hv', hxv⟩⟩
  · intro w hw
    obtain ⟨r, hr, he, hle⟩ := exists_rep G C g Sg w hw
    refine ⟨r, hle, hr, fun x => ?_⟩
    rw [semCan r hr x, he]
  · intro j a b hg1
    have hj : j < C.gates.length := by have := hg1.lt; rwa [glen] at this
    rcases cls j hj with ⟨_, hg2⟩ | ⟨a', b', hgt, hne, hg2⟩ | ⟨_, _, _, _, hg2⟩ | ⟨_, _, hg2⟩
    · exact absurd (hg1.unique hg2).1 (by simp)
    · obtain ⟨_, rfl, rfl⟩ := hg1.unique hg2
      obtain ⟨h1, h2, _⟩ := htc j ⟨a', b', hgt⟩ hne
      exact ⟨okw_plow H h1.1, okw_plow H h2.1⟩
    · exact absurd (hg1.unique hg2).1 (by simp)
    · exact absurd (hg1.unique hg2).1 (by simp)
  · intro j op a b hg1 hP
    have hj : j < C.gates.length := by have := hg1.lt; rwa [glen] at this
    have hls : LowSlot G C g j := by
      rcases hP with hP | ⟨j', hj', _, hls⟩
      · omega
      · have : j = j' := by omega
        rw [this]; exact hls
    have hnbw := lowslot_nbw H hls
    rcases cls j hj with ⟨hc, hg2⟩ | ⟨a', b', hgt, hne, hg2⟩ | ⟨_, _, _, hbw, _⟩ | ⟨_, _, hg2⟩
    · obtain ⟨rfl, rfl, rfl⟩ := hg1.unique hg2
      obtain ⟨h1, h2, _⟩ := hlo j hc
      exact ⟨rfl, okw_plow H h1.1, okw_plow H h2.1⟩
    · exact absurd (H.top_bw j a' b' hgt hne) hnbw
    · exact absurd hbw hnbw
    · obtain ⟨rfl, rfl, rfl⟩ := hg1.unique hg2
      exact ⟨rfl, Or.inl H.npos, Or.inl H.npos⟩
  · intro j1 hls1 hnc1 j op a b hg1
    have hj : j < C.gates.length := by have := hg1.lt; rwa [glen] at this
    have hnbw := lowslot_nbw H hls1
    rcases cls j hj with ⟨hc, hg2⟩ | ⟨a', b', hgt, hne, hg2⟩ | ⟨a', b', hgt, hbw, hg2⟩ | ⟨_, _, hg2⟩
    · obtain ⟨rfl, rfl, rfl⟩ := hg1.unique hg2
      obtain ⟨h1, h2, _⟩ := hlo j hc
      exact ⟨fun h => hnc1 (h ▸ h1), fun h => hnc1 (h ▸ h2)⟩
    · obtain ⟨rfl, rfl, rfl⟩ := hg1.unique hg2
      obtain ⟨h1, h2, _⟩ := htc j ⟨a', b', hgt⟩ hne
      exact ⟨fun h => hnc1 (h ▸ h1), fun h => hnc1 (h ▸ h2)⟩
    · obtain ⟨rfl, rfl, rfl⟩ := hg1.unique hg2
      obtain ⟨_, _, hba, hbb⟩ := bw_or_ops H hgt hbw
      exact ⟨fun h => hnbw (h ▸ hba), fun h => hnbw (h ▸ hbb)⟩
    · obtain ⟨rfl, rfl, rfl⟩ := hg1.unique hg2
      have := H.npos
      exact ⟨by omega, by omega⟩

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

lemma val_append_lt {n : ℕ} (gs t : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + gs.length) : val (gs ++ t) x w = val gs x w := by
  unfold val
  rw [List.foldl_append]
  exact foldl_getD_lt t _ w (by rw [foldl_length]; simpa using hw)

lemma isgate_append_right {gs t : List Gate} {j : ℕ} {op : GateOp} {a b : ℕ}
    (hj : gs.length ≤ j) :
    IsGate (gs ++ t) j op a b ↔ IsGate t (j - gs.length) op a b := by
  unfold IsGate
  rw [List.getElem?_append_right hj]

lemma del_crit {n j0 : ℕ} {gs : List Gate} (hG : Good n gs)
    (hun : ∀ j op a b, IsGate gs j op a b → a ≠ n + j0 ∧ b ≠ n + j0) (P : ℕ → Prop)
    (hA : ∀ j a b, IsGate gs j GateOp.and a b → P a ∧ P b)
    (hP : ∀ j op a b, IsGate gs j op a b → P (n + j) → op = GateOp.or ∧ P a ∧ P b) :
    (∀ j a b, IsGate (delG n j0 gs) j GateOp.and a b →
      P (if a < n + j0 then a else a + 1) ∧ P (if b < n + j0 then b else b + 1)) ∧
    (∀ j op a b, IsGate (delG n j0 gs) j op a b → P (if n + j < n + j0 then n + j else n + j + 1) →
      op = GateOp.or ∧ P (if a < n + j0 then a else a + 1) ∧ P (if b < n + j0 then b else b + 1)) := by
  have back : ∀ a, a ≠ n + j0 → (if rho n j0 a < n + j0 then rho n j0 a else rho n j0 a + 1) = a := by
    intro a ha
    simp only [rho]
    split_ifs <;> omega
  constructor
  · intro j a' b' h
    obtain ⟨a, b, hg, rfl, rfl⟩ := del_gate_inv hG h
    obtain ⟨h1, h2⟩ := hun _ _ _ _ hg
    rw [back a h1, back b h2]
    exact hA _ _ _ hg
  · intro j op a' b' h hPj
    obtain ⟨a, b, hg, rfl, rfl⟩ := del_gate_inv hG h
    obtain ⟨h1, h2⟩ := hun _ _ _ _ hg
    rw [back a h1, back b h2]
    refine hP _ _ _ _ hg ?_
    have : (if n + j < n + j0 then n + j else n + j + 1) = n + sig j0 j := by
      simp only [sig]
      split_ifs <;> omega
    rw [this] at hPj
    exact hPj

lemma del_unread {n j0 j1 : ℕ} {gs : List Gate} (hG : Good n gs) (h10 : j1 < j0)
    (hun0 : ∀ j op a b, IsGate gs j op a b → a ≠ n + j0 ∧ b ≠ n + j0)
    (hun1 : ∀ j op a b, IsGate gs j op a b → a ≠ n + j1 ∧ b ≠ n + j1) :
    ∀ j op a b, IsGate (delG n j0 gs) j op a b → a ≠ n + j1 ∧ b ≠ n + j1 := by
  intro j op a' b' h
  obtain ⟨a, b, hg, rfl, rfl⟩ := del_gate_inv hG h
  obtain ⟨h1, h2⟩ := hun0 _ _ _ _ hg
  obtain ⟨h3, h4⟩ := hun1 _ _ _ _ hg
  constructor <;>
  · simp only [rho]
    split_ifs <;> omega

-- Deleting two unread slots j1 < j2 of a good gate list whose last wire computes f.
lemma del_two {n : ℕ} (gs : List Gate) (f : (Fin n → Bool) → Bool) (hG : Good n gs)
    (j1 j2 : ℕ) (h12 : j1 < j2) (h2 : j2 + 1 < gs.length)
    (hun1 : ∀ j op a b, IsGate gs j op a b → a ≠ n + j1 ∧ b ≠ n + j1)
    (hun2 : ∀ j op a b, IsGate gs j op a b → a ≠ n + j2 ∧ b ≠ n + j2)
    (hf : ∀ x, val gs x (n + (gs.length - 1)) = f x) (P : ℕ → Prop)
    (hA : ∀ j a b, IsGate gs j GateOp.and a b → P a ∧ P b)
    (hP : ∀ j op a b, IsGate gs j op a b → P (n + j) → op = GateOp.or ∧ P a ∧ P b) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 2 = gs.length ∧ circuitFun n D = f ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  have hG2 := del_good hG hun2
  have hun1' := del_unread hG h12 hun2 hun1
  have hG3 := del_good hG2 hun1'
  have hl2 : (delG n j2 gs).length = gs.length - 1 := del_len _ _ _
  have hl3 : (delG n j1 (delG n j2 gs)).length = gs.length - 2 := by
    rw [del_len, hl2]; omega
  refine ⟨⟨delG n j1 (delG n j2 gs), n + (gs.length - 3)⟩, ao2_of_good hG3 _, ?_, ?_, ?_⟩
  · show (delG n j1 (delG n j2 gs)).length + 2 = gs.length
    rw [hl3]; omega
  · funext x
    rw [circuitFun_eq]
    show val (delG n j1 (delG n j2 gs)) x (n + (gs.length - 3)) = f x
    have e1 : n + (gs.length - 3) = rho n j1 (n + (gs.length - 2)) := by
      simp only [rho]; split_ifs <;> omega
    have e2 : n + (gs.length - 2) = rho n j2 (n + (gs.length - 1)) := by
      simp only [rho]; split_ifs <;> omega
    rw [e1, del_val hG2 hun1' (by rw [hl2]; omega) x _ (by rw [hl2]; omega) (by omega), e2,
      del_val hG hun2 (by omega) x _ (by omega) (by omega)]
    exact hf x
  · obtain ⟨hA2, hP2⟩ := del_crit hG hun2 P hA hP
    obtain ⟨hA3, hP3⟩ := del_crit hG2 hun1' (fun w => P (if w < n + j2 then w else w + 1)) hA2 hP2
    exact no_stack n ⟨delG n j1 (delG n j2 gs), n + (gs.length - 3)⟩ hG3 _ hA3 hP3

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

lemma isgate_app2 {gs : List Gate} {g1 g2 : Gate} {j : ℕ} {op : GateOp} {a b : ℕ}
    (h : IsGate (gs ++ [g1, g2]) j op a b) :
    (j < gs.length ∧ IsGate gs j op a b) ∨ (j = gs.length ∧ g1 = ⟨op, [a, b]⟩) ∨
      (j = gs.length + 1 ∧ g2 = ⟨op, [a, b]⟩) := by
  have hlt := h.lt
  simp only [List.length_append, List.length_cons, List.length_nil] at hlt
  by_cases hj : j < gs.length
  · exact Or.inl ⟨hj, (isgate_append_left hj).mp h⟩
  · rw [isgate_append_right (by omega)] at h
    unfold IsGate at h
    obtain hj' | hj' : j - gs.length = 0 ∨ j - gs.length = 1 := by omega
    · rw [hj'] at h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact Or.inr (Or.inl ⟨by omega, h⟩)
    · rw [hj'] at h
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
      exact Or.inr (Or.inr ⟨by omega, h⟩)

lemma isgate_app2_a (gs : List Gate) (g2 : Gate) (op : GateOp) (a b : ℕ) :
    IsGate (gs ++ [⟨op, [a, b]⟩, g2]) gs.length op a b := by
  rw [isgate_append_right (le_refl _)]
  unfold IsGate
  simp

lemma isgate_app2_b (gs : List Gate) (g1 : Gate) (op : GateOp) (a b : ℕ) :
    IsGate (gs ++ [g1, ⟨op, [a, b]⟩]) (gs.length + 1) op a b := by
  rw [isgate_append_right (by omega)]
  unfold IsGate
  simp

-- No extra top: the rebuilt circuit has the size of C.
theorem finish_inplace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (H : Str G C g) (Sg : ℕ → Finset (Fin n))
    (hv : ∀ i (hi : i < n), Sg i = {⟨i, hi⟩})
    (hl : ∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) → Okw G C g Sg (n + j) →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        Sg y1 ∪ Sg y2 = Sg (n + j))
    (want : ℕ → Finset (Fin n) × Finset (Fin n))
    (ht : ∀ j a b, IsGate C.gates j GateOp.and a b → j ≠ g →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        (∀ u ∈ Sg y1, ∀ v ∈ Sg y2, G.Adj u v) ∧ (want j).1 ⊆ Sg y1 ∧ (want j).2 ⊆ Sg y2)
    (hcov : ∀ u v, G.Adj u v → ∃ j a b, IsGate C.gates j GateOp.and a b ∧ j ≠ g ∧
      ((u ∈ (want j).1 ∧ v ∈ (want j).2) ∨ (v ∈ (want j).1 ∧ u ∈ (want j).2))) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  obtain ⟨gs, glen, hgood, hsound, hcomp, _, hA, hP, _⟩ := build_core G C g H Sg hv hl want ht
  refine ⟨⟨gs, n + (C.gates.length - 1)⟩, ao2_of_good hgood _, ?_, ?_, ?_⟩
  · show gs.length ≤ C.gates.length
    omega
  · funext x
    rw [circuitFun_eq]
    show val gs x (n + (C.gates.length - 1)) = graphFun G ∅ x
    apply Bool.eq_iff_iff.mpr
    refine ⟨hsound x, fun hF => ?_⟩
    obtain ⟨u, v, huv, hxu, hxv⟩ := (F_iff G x).mp hF
    obtain ⟨j, a, b, hgt, hne, hc | hc⟩ := hcov u v huv
    · exact hcomp j a b hgt hne u hc.1 v hc.2 x hxu hxv
    · exact hcomp j a b hgt hne v hc.1 u hc.2 x hxv hxu
  · exact no_stack n ⟨gs, n + (C.gates.length - 1)⟩ hgood (PLow G C g) hA hP

-- One extra top (an AND and an OR at the end), paid for by two unread lower slots.
theorem finish_append {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (H : Str G C g) (Sg : ℕ → Finset (Fin n))
    (hv : ∀ i (hi : i < n), Sg i = {⟨i, hi⟩})
    (hl : ∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) → Okw G C g Sg (n + j) →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        Sg y1 ∪ Sg y2 = Sg (n + j))
    (want : ℕ → Finset (Fin n) × Finset (Fin n))
    (ht : ∀ j a b, IsGate C.gates j GateOp.and a b → j ≠ g →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        (∀ u ∈ Sg y1, ∀ v ∈ Sg y2, G.Adj u v) ∧ (want j).1 ⊆ Sg y1 ∧ (want j).2 ⊆ Sg y2)
    (p q : ℕ) (hp : Okw G C g Sg p) (hq : Okw G C g Sg q)
    (hpq : ∀ u ∈ Sg p, ∀ v ∈ Sg q, G.Adj u v)
    (hcov : ∀ u v, G.Adj u v → (∃ j a b, IsGate C.gates j GateOp.and a b ∧ j ≠ g ∧
      ((u ∈ (want j).1 ∧ v ∈ (want j).2) ∨ (v ∈ (want j).1 ∧ u ∈ (want j).2))) ∨
      (u ∈ Sg p ∧ v ∈ Sg q) ∨ (v ∈ Sg p ∧ u ∈ Sg q))
    (j1 j2 : ℕ) (h12 : j1 < j2) (hj2 : j2 < C.gates.length)
    (hs1 : LowSlot G C g j1) (hc1 : ¬ Can G C g Sg (n + j1))
    (hs2 : LowSlot G C g j2) (hc2 : ¬ Can G C g Sg (n + j2)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  obtain ⟨gs, glen, hgood, hsound, hcomp, hrep, hA, hP, hun⟩ :=
    build_core G C g H Sg hv hl want ht
  obtain ⟨rp, hrp1, hrp2, hrp3⟩ := hrep p hp
  obtain ⟨rq, hrq1, hrq2, hrq3⟩ := hrep q hq
  have hpl := hp.1
  have hql := hq.1
  have hpos := H.glt
  set len := C.gates.length with hlen
  set gs' := gs ++ [⟨GateOp.and, [rp, rq]⟩, ⟨GateOp.or, [n + (len - 1), n + len]⟩] with hgs'
  have gl' : gs'.length = len + 2 := by rw [hgs']; simp [glen]
  have gA : IsGate gs' len GateOp.and rp rq := by
    rw [hgs', ← glen]; exact isgate_app2_a gs _ _ _ _
  have gO : IsGate gs' (len + 1) GateOp.or (n + (len - 1)) (n + len) := by
    rw [hgs', ← glen]; exact isgate_app2_b gs _ _ _ _
  have hgood' : Good n gs' := by
    intro j hj
    rw [gl'] at hj
    by_cases hj1 : j < len
    · obtain ⟨op, a, b, h1, h2, h3, h4⟩ := hgood j (by omega)
      exact ⟨op, a, b, (isgate_append_left (by omega)).mpr h1, h2, h3, h4⟩
    · obtain rfl | rfl : j = len ∨ j = len + 1 := by omega
      · exact ⟨_, _, _, gA, Or.inl rfl, by omega, by omega⟩
      · exact ⟨_, _, _, gO, Or.inr rfl, by omega, by omega⟩
  have hold : ∀ x : Fin n → Bool, ∀ w, w < n + len → val gs' x w = val gs x w := by
    intro x w hw
    rw [hgs']
    exact val_append_lt gs _ x w (by omega)
  have hval : ∀ x, val gs' x (n + (gs'.length - 1)) = graphFun G ∅ x := by
    intro x
    have e : n + (gs'.length - 1) = n + (len + 1) := by rw [gl']; rfl
    rw [e, val_or gO (by omega) (by omega), val_and gA (by omega) (by omega),
      hold x _ (by omega), hold x rp (by omega), hold x rq (by omega)]
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true, Bool.and_eq_true, hrp3, hrq3]
    constructor
    · rintro (h | ⟨⟨u, hu, hxu⟩, ⟨v, hv', hxv⟩⟩)
      · exact hsound x h
      · exact (F_iff G x).mpr ⟨u, v, hpq u hu v hv', hxu, hxv⟩
    · intro hF
      obtain ⟨u, v, huv, hxu, hxv⟩ := (F_iff G x).mp hF
      rcases hcov u v huv with ⟨j, a, b, hgt, hne, hc | hc⟩ | hc | hc
      · exact Or.inl (hcomp j a b hgt hne u hc.1 v hc.2 x hxu hxv)
      · exact Or.inl (hcomp j a b hgt hne v hc.1 u hc.2 x hxv hxu)
      · exact Or.inr ⟨⟨u, hc.1, hxu⟩, ⟨v, hc.2, hxv⟩⟩
      · exact Or.inr ⟨⟨v, hc.1, hxv⟩, ⟨u, hc.2, hxu⟩⟩
  have hun' : ∀ j0, LowSlot G C g j0 → ¬ Can G C g Sg (n + j0) → j0 < len →
      ∀ j op a b, IsGate gs' j op a b → a ≠ n + j0 ∧ b ≠ n + j0 := by
    intro j0 hs hc hj0 j op a b hg1
    rcases isgate_app2 hg1 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact hun j0 hs hc j op a b h
    · simp only [Gate.mk.injEq, List.cons.injEq, and_true] at h
      obtain ⟨_, rfl, rfl⟩ := h
      exact ⟨fun e => hc (e ▸ hrp2), fun e => hc (e ▸ hrq2)⟩
    · simp only [Gate.mk.injEq, List.cons.injEq, and_true] at h
      obtain ⟨_, rfl, rfl⟩ := h
      refine ⟨fun e => lowslot_nbw H hs ?_, by omega⟩
      rw [← e]; exact H.out_bw
  have hA' : ∀ j a b, IsGate gs' j GateOp.and a b → PLow G C g a ∧ PLow G C g b := by
    intro j a b hg1
    rcases isgate_app2 hg1 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact hA j a b h
    · simp only [Gate.mk.injEq, List.cons.injEq, and_true] at h
      obtain ⟨_, rfl, rfl⟩ := h
      exact ⟨okw_plow H hrp2.1, okw_plow H hrq2.1⟩
    · simp at h
  have hP' : ∀ j op a b, IsGate gs' j op a b → PLow G C g (n + j) →
      op = GateOp.or ∧ PLow G C g a ∧ PLow G C g b := by
    intro j op a b hg1 hPj
    have hj : j < len := by
      rcases hPj with h | ⟨j', h1, h2, _⟩
      · omega
      · omega
    rcases isgate_app2 hg1 with ⟨_, h⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
    · exact hP j op a b h hPj
    · omega
    · omega
  obtain ⟨D, hD1, hD2, hD3, hD4⟩ := del_two gs' (graphFun G ∅) hgood' j1 j2 h12 (by omega)
    (hun' j1 hs1 hc1 (by omega)) (hun' j2 hs2 hc2 hj2) hval (PLow G C g) hA' hP'
  refine ⟨D, hD1, ?_, hD3, hD4⟩
  show D.size ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

/-! The shape of the given circuit -/

def pr {n : ℕ} (u v : Fin n) : Fin n → Bool := fun c => decide (c = u ∨ c = v)
def tri {n : ℕ} (a b s : Fin n) : Fin n → Bool := fun c => decide (c = a ∨ c = b ∨ c = s)

lemma F_pr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n)
    (h : graphFun G ∅ (pr u v) = true) : G.Adj u v := by
  rw [F_iff] at h
  obtain ⟨p, q, hpq, hp, hq⟩ := h
  simp only [pr, decide_eq_true_eq] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hpq.ne
  · exact hpq
  · exact hpq.symm
  · exact absurd rfl hpq.ne

-- The vertices whose one-hot input turns wire w on.
def supp (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => val C.gates (eof u) w = true

lemma mem_supp {n : ℕ} {C : Circuit} {w : ℕ} {u : Fin n} :
    u ∈ supp n C w ↔ val C.gates (eof u) w = true := by simp [supp]

-- Wire w is an OR of variables.
def Lin (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val C.gates x w = true → ∃ u ∈ supp n C w, x u = true

-- Wire w is the gate g OR-ed with variables.
def GF (n : ℕ) (C : Circuit) (g w : ℕ) : Prop :=
  n + g ≤ w ∧ (∀ x : Fin n → Bool, val C.gates x (n + g) = true → val C.gates x w = true) ∧
    ∀ x : Fin n → Bool, val C.gates x w = true →
      val C.gates x (n + g) = true ∨ ∃ u ∈ supp n C w, x u = true

-- The working form of the hypotheses, with the two operands al, be of the gate g.
def GS {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g al be : ℕ) : Prop :=
  (Str G C g) ∧
  (∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v) ∧
  (∀ a b w1 w2 : Fin n, G.Adj a w1 → G.Adj b w1 → G.Adj a w2 → G.Adj b w2 → a ≠ b → w1 = w2) ∧
  (∀ j a b, IsGate C.gates j GateOp.and a b → ¬ BW G C a ∧ ¬ BW G C b) ∧
  (∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) → ¬ BW G C a ∧ ¬ BW G C b) ∧
  (al < n + g) ∧
  (be < n + g) ∧
  (¬ BW G C al) ∧
  (¬ BW G C be) ∧
  (∀ x : Fin n → Bool, val C.gates x (n + g) = (val C.gates x al && val C.gates x be)) ∧
  (∀ v : Fin n, val C.gates (eof v) (n + g) = false) ∧
  (IsGate C.gates g GateOp.and al be ∨ IsGate C.gates g GateOp.and be al) ∧
  (∀ x : Fin n → Bool, val C.gates x (n + (C.gates.length - 1)) = graphFun G ∅ x) ∧
  (∀ j < C.gates.length, j ≠ C.gates.length - 1 →
      ∃ k op a b, IsGate C.gates k op a b ∧ (a = n + j ∨ b = n + j))

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}

lemma GS.intro (str : Str G C g)
    (bip : ∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v)
    (four : ∀ a b w1 w2 : Fin n, G.Adj a w1 → G.Adj b w1 → G.Adj a w2 → G.Adj b w2 → a ≠ b → w1 = w2)
    (and_ops : ∀ j a b, IsGate C.gates j GateOp.and a b → ¬ BW G C a ∧ ¬ BW G C b)
    (low_ops : ∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) → ¬ BW G C a ∧ ¬ BW G C b)
    (al_lt : al < n + g)
    (be_lt : be < n + g)
    (al_nbw : ¬ BW G C al)
    (be_nbw : ¬ BW G C be)
    (gval : ∀ x : Fin n → Bool, val C.gates x (n + g) = (val C.gates x al && val C.gates x be))
    (gunit : ∀ v : Fin n, val C.gates (eof v) (n + g) = false)
    (ggate : IsGate C.gates g GateOp.and al be ∨ IsGate C.gates g GateOp.and be al)
    (fn : ∀ x : Fin n → Bool, val C.gates x (n + (C.gates.length - 1)) = graphFun G ∅ x)
    (reader_any : ∀ j < C.gates.length, j ≠ C.gates.length - 1 →
      ∃ k op a b, IsGate C.gates k op a b ∧ (a = n + j ∨ b = n + j)) :
    GS G C g al be := by
  unfold GS
  exact ⟨str, bip, four, and_ops, low_ops, al_lt, be_lt, al_nbw, be_nbw, gval, gunit, ggate, fn, reader_any⟩

lemma GS.str (H : GS G C g al be) :
    Str G C g := by
  unfold GS at H
  exact H.1

lemma GS.bip (H : GS G C g al be) :
    ∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v := by
  unfold GS at H
  exact H.2.1

lemma GS.four (H : GS G C g al be) :
    ∀ a b w1 w2 : Fin n, G.Adj a w1 → G.Adj b w1 → G.Adj a w2 → G.Adj b w2 → a ≠ b → w1 = w2 := by
  unfold GS at H
  exact H.2.2.1

lemma GS.and_ops (H : GS G C g al be) :
    ∀ j a b, IsGate C.gates j GateOp.and a b → ¬ BW G C a ∧ ¬ BW G C b := by
  unfold GS at H
  exact H.2.2.2.1

lemma GS.low_ops (H : GS G C g al be) :
    ∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) → ¬ BW G C a ∧ ¬ BW G C b := by
  unfold GS at H
  exact H.2.2.2.2.1

lemma GS.al_lt (H : GS G C g al be) :
    al < n + g := by
  unfold GS at H
  exact H.2.2.2.2.2.1

lemma GS.be_lt (H : GS G C g al be) :
    be < n + g := by
  unfold GS at H
  exact H.2.2.2.2.2.2.1

lemma GS.al_nbw (H : GS G C g al be) :
    ¬ BW G C al := by
  unfold GS at H
  exact H.2.2.2.2.2.2.2.1

lemma GS.be_nbw (H : GS G C g al be) :
    ¬ BW G C be := by
  unfold GS at H
  exact H.2.2.2.2.2.2.2.2.1

lemma GS.gval (H : GS G C g al be) :
    ∀ x : Fin n → Bool, val C.gates x (n + g) = (val C.gates x al && val C.gates x be) := by
  unfold GS at H
  exact H.2.2.2.2.2.2.2.2.2.1

lemma GS.gunit (H : GS G C g al be) :
    ∀ v : Fin n, val C.gates (eof v) (n + g) = false := by
  unfold GS at H
  exact H.2.2.2.2.2.2.2.2.2.2.1

lemma GS.ggate (H : GS G C g al be) :
    IsGate C.gates g GateOp.and al be ∨ IsGate C.gates g GateOp.and be al := by
  unfold GS at H
  exact H.2.2.2.2.2.2.2.2.2.2.2.1

lemma GS.fn (H : GS G C g al be) :
    ∀ x : Fin n → Bool, val C.gates x (n + (C.gates.length - 1)) = graphFun G ∅ x := by
  unfold GS at H
  exact H.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma GS.reader_any (H : GS G C g al be) :
    ∀ j < C.gates.length, j ≠ C.gates.length - 1 →
      ∃ k op a b, IsGate C.gates k op a b ∧ (a = n + j ∨ b = n + j) := by
  unfold GS at H
  exact H.2.2.2.2.2.2.2.2.2.2.2.2.2

end

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}

lemma GS.symm (S : GS G C g al be) : GS G C g be al :=
  GS.intro S.str S.bip S.four S.and_ops S.low_ops S.be_lt S.al_lt S.be_nbw S.al_nbw
    (fun x => by rw [S.gval x, Bool.and_comm]) S.gunit S.ggate.symm S.fn S.reader_any

lemma GS.up (S : GS G C g al be) {w : ℕ} {u : Fin n} {x : Fin n → Bool}
    (hu : u ∈ supp n C w) (hx : x u = true) : val C.gates x w = true := by
  refine mono S.str.good (eof u) x ?_ w (mem_supp.mp hu)
  intro i hi
  simp only [eof, decide_eq_true_eq] at hi
  rw [hi]; exact hx

lemma GS.supp_or (S : GS G C g al be) {j a b : ℕ} (hgt : IsGate C.gates j GateOp.or a b) :
    supp n C (n + j) = supp n C a ∪ supp n C b := by
  obtain ⟨op, a', b', hgt', _, ha, hb⟩ := S.str.good j hgt.lt
  obtain ⟨_, rfl, rfl⟩ := hgt.unique hgt'
  ext u
  simp only [Finset.mem_union, mem_supp]
  rw [val_or hgt ha hb, Bool.or_eq_true]

lemma GS.supp_g (S : GS G C g al be) : supp n C (n + g) = ∅ := by
  ext u
  simp only [mem_supp, Finset.notMem_empty, iff_false]
  rw [S.gunit u]
  simp

-- Every wire is below F, an OR of variables, or g OR-ed with variables.
lemma GS.struct (S : GS G C g al be) :
    ∀ w, w < n + C.gates.length → BW G C w ∨ Lin n C w ∨ GF n C g w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · right; left
      intro x hx
      refine ⟨⟨w, h1⟩, ?_, ?_⟩
      · rw [mem_supp, val_lt _ _ _ h1]; simp [eof]
      · rw [val_lt _ _ _ h1] at hx; exact hx
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      obtain ⟨op, a, b, hgt, hop, ha, hb⟩ := S.str.good j (by omega)
      rcases hop with rfl | rfl
      · by_cases hjg : j = g
        · right; right
          rw [hjg]
          exact ⟨le_refl _, fun x h => h, fun x h => Or.inl h⟩
        · left
          exact S.str.top_bw j a b hgt hjg
      · by_cases hbw : BW G C (n + j)
        · left; exact hbw
        · obtain ⟨hna, hnb⟩ := S.low_ops j a b hgt hbw
          have hsup := S.supp_or hgt
          have hor := fun x : Fin n → Bool => val_or hgt ha hb x
          have ca := (ih a ha (by omega)).resolve_left hna
          have cb := (ih b hb (by omega)).resolve_left hnb
          have sem : ∀ w', (Lin n C w' ∨ GF n C g w') → supp n C w' ⊆ supp n C (n + j) →
              ∀ x : Fin n → Bool, val C.gates x w' = true →
                val C.gates x (n + g) = true ∨ ∃ u ∈ supp n C (n + j), x u = true := by
            intro w' hc hsub x hx
            rcases hc with hc | hc
            · obtain ⟨u, hu, hxu⟩ := hc x hx
              exact Or.inr ⟨u, hsub hu, hxu⟩
            · rcases hc.2.2 x hx with h | ⟨u, hu, hxu⟩
              · exact Or.inl h
              · exact Or.inr ⟨u, hsub hu, hxu⟩
          have sa : supp n C a ⊆ supp n C (n + j) := by rw [hsup]; exact Finset.subset_union_left
          have sb : supp n C b ⊆ supp n C (n + j) := by rw [hsup]; exact Finset.subset_union_right
          have both : ∀ x : Fin n → Bool, val C.gates x (n + j) = true →
              val C.gates x (n + g) = true ∨ ∃ u ∈ supp n C (n + j), x u = true := by
            intro x hx
            rw [hor, Bool.or_eq_true] at hx
            rcases hx with hx | hx
            · exact sem a ca sa x hx
            · exact sem b cb sb x hx
          rcases ca with ca | ca
          · rcases cb with cb | cb
            · right; left
              intro x hx
              rw [hor, Bool.or_eq_true] at hx
              rcases hx with hx | hx
              · obtain ⟨u, hu, hxu⟩ := ca x hx
                exact ⟨u, sa hu, hxu⟩
              · obtain ⟨u, hu, hxu⟩ := cb x hx
                exact ⟨u, sb hu, hxu⟩
            · right; right
              exact ⟨by have := cb.1; omega, fun x hx => by rw [hor, cb.2.1 x hx]; simp, both⟩
          · right; right
            exact ⟨by have := ca.1; omega, fun x hx => by rw [hor, ca.2.1 x hx]; rfl, both⟩

lemma GS.cases (S : GS G C g al be) {w : ℕ} (hw : w < n + C.gates.length) (hn : ¬ BW G C w) :
    Lin n C w ∨ GF n C g w := (S.struct w hw).resolve_left hn

lemma GS.lin_iff (S : GS G C g al be) {w : ℕ} (hL : Lin n C w) (x : Fin n → Bool) :
    val C.gates x w = true ↔ ∃ u ∈ supp n C w, x u = true :=
  ⟨hL x, fun ⟨_, hu, hx⟩ => S.up hu hx⟩

lemma GS.gf_iff (S : GS G C g al be) {w : ℕ} (hF : GF n C g w) (x : Fin n → Bool) :
    val C.gates x w = true ↔ val C.gates x (n + g) = true ∨ ∃ u ∈ supp n C w, x u = true := by
  constructor
  · exact hF.2.2 x
  · rintro (h | ⟨u, hu, hx⟩)
    · exact hF.2.1 x h
    · exact S.up hu hx

lemma GS.lin_al (S : GS G C g al be) : Lin n C al := by
  have hlt : al < n + C.gates.length := by have := S.al_lt; have := S.str.glt; omega
  rcases S.cases hlt S.al_nbw with h | h
  · exact h
  · have := h.1; have := S.al_lt; omega

lemma GS.lin_be (S : GS G C g al be) : Lin n C be := S.symm.lin_al

lemma GS.gval' (S : GS G C g al be) (x : Fin n → Bool) :
    val C.gates x (n + g) = true ↔
      (∃ a ∈ supp n C al, x a = true) ∧ (∃ b ∈ supp n C be, x b = true) := by
  rw [S.gval x, Bool.and_eq_true, S.lin_iff S.lin_al, S.lin_iff S.lin_be]

lemma GS.disj (S : GS G C g al be) {v : Fin n} (ha : v ∈ supp n C al) (hb : v ∈ supp n C be) :
    False := by
  have h := S.gunit v
  have h2 : val C.gates (eof v) (n + g) = true :=
    (S.gval' (eof v)).mpr ⟨⟨v, ha, by simp [eof]⟩, ⟨v, hb, by simp [eof]⟩⟩
  rw [h] at h2
  cases h2

lemma GS.lin_nonempty (S : GS G C g al be) {w : ℕ} (hw : w < n + C.gates.length)
    (hL : Lin n C w) : (supp n C w).Nonempty := by
  obtain ⟨u, hu, _⟩ := hL (fun _ => true) (ones S.str.good w hw)
  exact ⟨u, hu⟩

lemma GS.junk (S : GS G C g al be) :
    ∃ a0 ∈ supp n C al, ∃ b0 ∈ supp n C be, ¬ G.Adj a0 b0 := by
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  apply S.str.g_nbw
  intro x hx
  obtain ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩ := (S.gval' x).mp hx
  exact (F_iff G x).mpr ⟨a, b, hc a ha b hb, hxa, hxb⟩

end

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

-- Gate j is a below-F AND gate (a top) reading the wires om and si, in either order.
def TopP (C : Circuit) (g j om si : ℕ) : Prop :=
  j ≠ g ∧ (IsGate C.gates j GateOp.and om si ∨ IsGate C.gates j GateOp.and si om)

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}

lemma TopP.symm {j om si : ℕ} (h : TopP C g j om si) : TopP C g j si om := ⟨h.1, h.2.symm⟩

lemma GS.top_lt (S : GS G C g al be) {j om si : ℕ} (h : TopP C g j om si) :
    j < C.gates.length ∧ om < n + j ∧ si < n + j := by
  rcases h.2 with hgt | hgt
  · obtain ⟨op, a', b', hgt', _, ha, hb⟩ := S.str.good j hgt.lt
    obtain ⟨_, rfl, rfl⟩ := hgt.unique hgt'
    exact ⟨hgt.lt, ha, hb⟩
  · obtain ⟨op, a', b', hgt', _, ha, hb⟩ := S.str.good j hgt.lt
    obtain ⟨_, rfl, rfl⟩ := hgt.unique hgt'
    exact ⟨hgt.lt, hb, ha⟩

lemma GS.top_val (S : GS G C g al be) {j om si : ℕ} (h : TopP C g j om si) (x : Fin n → Bool) :
    val C.gates x (n + j) = (val C.gates x om && val C.gates x si) := by
  obtain ⟨_, h1, h2⟩ := S.top_lt h
  rcases h.2 with hgt | hgt
  · exact val_and hgt h1 h2 x
  · rw [val_and hgt h2 h1 x, Bool.and_comm]

lemma GS.top_bw (S : GS G C g al be) {j om si : ℕ} (h : TopP C g j om si) : BW G C (n + j) := by
  rcases h.2 with hgt | hgt
  · exact S.str.top_bw j _ _ hgt h.1
  · exact S.str.top_bw j _ _ hgt h.1

lemma GS.top_nbw (S : GS G C g al be) {j om si : ℕ} (h : TopP C g j om si) :
    ¬ BW G C om ∧ ¬ BW G C si := by
  rcases h.2 with hgt | hgt
  · exact S.and_ops j _ _ hgt
  · exact (S.and_ops j _ _ hgt).symm

lemma GS.top_cases (S : GS G C g al be) {j om si : ℕ} (h : TopP C g j om si) :
    (Lin n C om ∨ GF n C g om) ∧ (Lin n C si ∨ GF n C g si) := by
  obtain ⟨h0, h1, h2⟩ := S.top_lt h
  obtain ⟨h3, h4⟩ := S.top_nbw h
  exact ⟨S.cases (by omega) h3, S.cases (by omega) h4⟩

lemma GS.top_prod (S : GS G C g al be) {j om si : ℕ} (h : TopP C g j om si) :
    ∀ u ∈ supp n C om, ∀ v ∈ supp n C si, G.Adj u v := by
  intro u hu v hv
  apply F_pr
  apply S.top_bw h
  rw [S.top_val h, S.up hu (by simp [pr]), S.up hv (by simp [pr])]
  rfl

lemma GS.top_notboth (S : GS G C g al be) {j om si : ℕ} (h : TopP C g j om si)
    (h1 : GF n C g om) (h2 : GF n C g si) : False := by
  apply S.str.g_nbw
  intro x hx
  apply S.top_bw h
  rw [S.top_val h, h1.2.1 x hx, h2.2.1 x hx]
  rfl

-- A below-F wire that is on has a top that is on.
lemma GS.down (S : GS G C g al be) (x : Fin n → Bool) :
    ∀ w, w < n + C.gates.length → BW G C w → val C.gates x w = true →
      ∃ j om si, TopP C g j om si ∧ val C.gates x om = true ∧ val C.gates x si = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hbw hval
    by_cases hwn : w < n
    · exact absurd hbw (notBW_input G C w hwn)
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      obtain ⟨op, a, b, hgt, hop, ha, hb⟩ := S.str.good j (by omega)
      rcases hop with rfl | rfl
      · have hne : j ≠ g := fun e => S.str.g_nbw (e ▸ hbw)
        rw [val_and hgt ha hb, Bool.and_eq_true] at hval
        exact ⟨j, a, b, ⟨hne, Or.inl hgt⟩, hval.1, hval.2⟩
      · obtain ⟨_, _, hba, hbb⟩ := bw_or_ops S.str hgt hbw
        rw [val_or hgt ha hb, Bool.or_eq_true] at hval
        rcases hval with hval | hval
        · exact ih a ha (by omega) hba hval
        · exact ih b hb (by omega) hbb hval

lemma GS.pr_lin (S : GS G C g al be) {w : ℕ} (hL : Lin n C w) {u v : Fin n}
    (h : val C.gates (pr u v) w = true) : u ∈ supp n C w ∨ v ∈ supp n C w := by
  obtain ⟨c, hc, hx⟩ := hL _ h
  simp only [pr, decide_eq_true_eq] at hx
  rcases hx with rfl | rfl
  · exact Or.inl hc
  · exact Or.inr hc

lemma GS.pr_g (S : GS G C g al be) {u v : Fin n} (h : val C.gates (pr u v) (n + g) = true) :
    (u ∈ supp n C al ∧ v ∈ supp n C be) ∨ (v ∈ supp n C al ∧ u ∈ supp n C be) := by
  obtain ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩ := (S.gval' _).mp h
  simp only [pr, decide_eq_true_eq] at hxa hxb
  rcases hxa with rfl | rfl <;> rcases hxb with rfl | rfl
  · exact absurd hb (fun hb => S.disj ha hb)
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact absurd hb (fun hb => S.disj ha hb)

-- The pair u v is accepted by a top through the variable sets of its two operands.
def ResCov (n : ℕ) (C : Circuit) (g : ℕ) (u v : Fin n) : Prop :=
  ∃ j om si, TopP C g j om si ∧ u ∈ supp n C om ∧ v ∈ supp n C si

-- Every edge is accepted through variable sets, or through g by a top whose other operand
-- holds one end of the edge.
lemma GS.edge_cases (S : GS G C g al be) {u v : Fin n} (h : G.Adj u v) :
    ResCov n C g u v ∨ ∃ j om si a0 b0, TopP C g j om si ∧ GF n C g om ∧ Lin n C si ∧
      ((a0 = u ∧ b0 = v) ∨ (a0 = v ∧ b0 = u)) ∧ a0 ∈ supp n C al ∧ b0 ∈ supp n C be ∧
      (a0 ∈ supp n C si ∨ b0 ∈ supp n C si) := by
  have hF : graphFun G ∅ (pr u v) = true := (F_iff G _).mpr ⟨u, v, h, by simp [pr], by simp [pr]⟩
  have hlen := S.str.glt
  rw [← S.fn] at hF
  obtain ⟨j, om, si, hT, hom, hsi⟩ := S.down (pr u v) _ (by omega) S.str.out_bw hF
  -- a helper: what an operand being on at the pair means
  have key : ∀ j om si, TopP C g j om si → val C.gates (pr u v) om = true →
      (u ∈ supp n C si ∨ v ∈ supp n C si) → ¬ (u ∈ supp n C om ∨ v ∈ supp n C om) →
      ∃ j om si a0 b0, TopP C g j om si ∧ GF n C g om ∧ Lin n C si ∧
      ((a0 = u ∧ b0 = v) ∨ (a0 = v ∧ b0 = u)) ∧ a0 ∈ supp n C al ∧ b0 ∈ supp n C be ∧
      (a0 ∈ supp n C si ∨ b0 ∈ supp n C si) := by
    intro j om si hT hom hsi hno
    have hgf : GF n C g om := by
      rcases (S.top_cases hT).1 with hl | hg
      · exact absurd (S.pr_lin hl hom) hno
      · exact hg
    have hls : Lin n C si := by
      rcases (S.top_cases hT).2 with hl | hg
      · exact hl
      · exact absurd hg (fun hg => S.top_notboth hT hgf hg)
    have hgv : val C.gates (pr u v) (n + g) = true := by
      rcases (S.gf_iff hgf _).mp hom with hg | ⟨c, hc, hx⟩
      · exact hg
      · simp only [pr, decide_eq_true_eq] at hx
        rcases hx with rfl | rfl
        · exact absurd (Or.inl hc) hno
        · exact absurd (Or.inr hc) hno
    rcases S.pr_g hgv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨j, om, si, u, v, hT, hgf, hls, Or.inl ⟨rfl, rfl⟩, h1, h2, hsi⟩
    · exact ⟨j, om, si, v, u, hT, hgf, hls, Or.inr ⟨rfl, rfl⟩, h1, h2, hsi.symm⟩
  have hit : ∀ w, (Lin n C w ∨ GF n C g w) → val C.gates (pr u v) w = true →
      (u ∈ supp n C w ∨ v ∈ supp n C w) ∨ GF n C g w := by
    intro w hc hw
    rcases hc with hl | hg
    · exact Or.inl (S.pr_lin hl hw)
    · exact Or.inr hg
  by_cases ho : u ∈ supp n C om ∨ v ∈ supp n C om
  · by_cases hs : u ∈ supp n C si ∨ v ∈ supp n C si
    · left
      have hp := S.top_prod hT
      rcases ho with ho | ho <;> rcases hs with hs | hs
      · exact absurd (hp u ho u hs) (fun e => e.ne rfl)
      · exact ⟨j, om, si, hT, ho, hs⟩
      · exact ⟨j, si, om, hT.symm, hs, ho⟩
      · exact absurd (hp v ho v hs) (fun e => e.ne rfl)
    · right
      exact key j si om hT.symm hsi ho hs
  · right
    by_cases hs : u ∈ supp n C si ∨ v ∈ supp n C si
    · exact key j om si hT hom hs ho
    · exfalso
      have h1 : GF n C g om := by
        rcases hit om (S.top_cases hT).1 hom with h | h
        · exact absurd h ho
        · exact h
      have h2 : GF n C g si := by
        rcases hit si (S.top_cases hT).2 hsi with h | h
        · exact absurd h hs
        · exact h
      exact S.top_notboth hT h1 h2

-- A top reading through g whose other operand holds a vertex of A: that vertex sees all of B.
lemma GS.gtop_A (S : GS G C g al be) {j om si : ℕ} (hT : TopP C g j om si) (hF : GF n C g om)
    {a0 : Fin n} (ha0 : a0 ∈ supp n C al) (hs : a0 ∈ supp n C si) :
    ∀ b' ∈ supp n C be, G.Adj a0 b' := by
  intro b' hb'
  apply F_pr
  apply S.top_bw hT
  have hg : val C.gates (pr a0 b') (n + g) = true :=
    (S.gval' _).mpr ⟨⟨a0, ha0, by simp [pr]⟩, ⟨b', hb', by simp [pr]⟩⟩
  rw [S.top_val hT, hF.2.1 _ hg, S.up hs (by simp [pr])]
  rfl

-- The same top: each vertex of its other operand is adjacent to an end of every junk pair.
lemma GS.gtop_J (S : GS G C g al be) {j om si : ℕ} (hT : TopP C g j om si) (hF : GF n C g om)
    {s a0 b0 : Fin n} (hs : s ∈ supp n C si) (ha0 : a0 ∈ supp n C al) (hb0 : b0 ∈ supp n C be)
    (hna : ¬ G.Adj a0 b0) : G.Adj s a0 ∨ G.Adj s b0 := by
  have hg : val C.gates (tri a0 b0 s) (n + g) = true :=
    (S.gval' _).mpr ⟨⟨a0, ha0, by simp [tri]⟩, ⟨b0, hb0, by simp [tri]⟩⟩
  have hFx : graphFun G ∅ (tri a0 b0 s) = true := by
    apply S.top_bw hT
    rw [S.top_val hT, hF.2.1 _ hg, S.up hs (by simp [tri])]
    rfl
  obtain ⟨p, q, hpq, hp, hq⟩ := (F_iff G _).mp hFx
  simp only [tri, decide_eq_true_eq] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact absurd rfl hpq.ne
  · exact absurd hpq hna
  · exact Or.inl hpq.symm
  · exact absurd hpq.symm hna
  · exact absurd rfl hpq.ne
  · exact Or.inr hpq.symm
  · exact Or.inl hpq
  · exact Or.inr hpq
  · exact absurd rfl hpq.ne

end

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

-- The hypotheses of the statement, put in the working form.
theorem gs_of_hyps (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (g : ℕ)
    (hbip : ∀ u v : Fin n, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G) (hao : IsAO2 n C)
    (hfn : circuitFun n C = graphFun G ∅) (hlift : IsLiftFixedPoint G C)
    (h5 : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ t ∈ (gateAt C k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
        graphFun G ∅ x = true))
    (h6 : ∀ k < C.gates.length, InOutputCone n C k)
    (h7 : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ v : Fin n, gateVal n C k (PEqualNP.SplitCount.unitInput v) = false)
    (hg : g < C.gates.length) (hgop : (gateAt C g).op = GateOp.and) (hgd : ¬ BelowF G C g)
    (hclean : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k) :
    ∃ al be, GS G C g al be := by
  have good := good_of_ao2 hao
  obtain ⟨op, al, be, hgt, _, hal, hbe⟩ := good g hg
  have hop : op = GateOp.and := by
    rw [isgate_gateAt hgt] at hgop; exact hgop
  subst hop
  have npos : 0 < n := by
    by_contra hc
    obtain ⟨_, a, _, _, _, ha, _⟩ := good 0 (by omega)
    omega
  have and_ops : ∀ j a b, IsGate C.gates j GateOp.and a b → ¬ BW G C a ∧ ¬ BW G C b := by
    intro j a b hj
    have e := isgate_gateAt hj
    exact ⟨h5 j hj.lt (by rw [e]) a (by rw [e]; simp), h5 j hj.lt (by rw [e]) b (by rw [e]; simp)⟩
  have low_ops : ∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) →
      ¬ BW G C a ∧ ¬ BW G C b := by
    intro j a b hj hn
    have e := isgate_gateAt hj
    obtain ⟨op', a', b', hj', _, ha, hb⟩ := good j hj.lt
    obtain ⟨_, rfl, rfl⟩ := hj.unique hj'
    have lift : ∀ (c : Fin 2) (w : ℕ), opnd C j c = w → w < n + j → ¬ BW G C w := by
      intro c w hc hw hbw
      apply hlift
      refine ⟨j, hj.lt, c, h6 j hj.lt, by rw [e], hn, ?_⟩
      rw [hc]
      exact ⟨hbw, fun _ => true, ones good w (by have := hj.lt; omega)⟩
    exact ⟨lift 0 a (by simp [opnd, e]) ha, lift 1 b (by simp [opnd, e]) hb⟩
  -- the output is the last gate, and every other gate is read
  have hout : n ≤ C.output := by
    rcases (h6 g hg).2 with h | ⟨h, _⟩
    · omega
    · exact h
  have hk : ∀ k < C.gates.length, k = C.output - n ∨ InCone n C k (C.output - n) := by
    intro k hk
    rcases (h6 k hk).2 with h | ⟨_, h⟩
    · left; omega
    · right; exact h
  have ho : C.output - n < C.gates.length := by
    by_contra hc
    rcases hk g hg with h | h
    · omega
    · exact cone_ge n C g _ (by omega) h
  have hmax : ∀ k < C.gates.length, k ≤ C.output - n := by
    intro k hk'
    rcases hk k hk' with h | h
    · omega
    · exact le_of_lt (cone_lt_reader n C good _ k h).1
  have ho' : C.output = n + (C.gates.length - 1) := by
    have := hmax (C.gates.length - 1) (by omega)
    omega
  have fn : ∀ x : Fin n → Bool, val C.gates x (n + (C.gates.length - 1)) = graphFun G ∅ x := by
    intro x
    rw [← ho', ← circuitFun_eq, hfn]
  have reader_any : ∀ j < C.gates.length, j ≠ C.gates.length - 1 →
      ∃ k op a b, IsGate C.gates k op a b ∧ (a = n + j ∨ b = n + j) := by
    intro j hj hne
    rcases hk j hj with h | h
    · omega
    · exact (cone_lt_reader n C good _ j h).2
  have hreader : ∀ j < C.gates.length, BW G C (n + j) → j ≠ C.gates.length - 1 →
      ∃ k a b, IsGate C.gates k GateOp.or a b ∧ BW G C (n + k) ∧ (a = n + j ∨ b = n + j) := by
        intro j hj hbw hne
        obtain ⟨k, op, a, b, hkg, hab⟩ := reader_any j hj hne
        obtain ⟨op', a', b', hkg', hop, _, _⟩ := good k hkg.lt
        obtain ⟨rfl, rfl, rfl⟩ := hkg.unique hkg'
        rcases hop with rfl | rfl
        · obtain ⟨h1, h2⟩ := and_ops k a b hkg
          rcases hab with rfl | rfl
          · exact absurd hbw h1
          · exact absurd hbw h2
        · refine ⟨k, a, b, hkg, ?_, hab⟩
          by_contra hn
          obtain ⟨h1, h2⟩ := low_ops k a b hkg hn
          rcases hab with rfl | rfl
          · exact absurd hbw h1
          · exact absurd hbw h2
  have str : Str G C g :=
    Str.intro good npos hg (fun j a b hj hne => hclean j hj.lt (by rw [isgate_gateAt hj]) hne) hgd
      (fun x hx => by rw [fn] at hx; exact hx) hreader
  refine ⟨al, be, ?_⟩
  have hfour : ∀ a b w1 w2 : Fin n, G.Adj a w1 → G.Adj b w1 → G.Adj a w2 → G.Adj b w2 → a ≠ b →
      w1 = w2 := by
    intro a b w1 w2 h1 h2 h3 h4' hab
    have hc := h4 a b hab
    exact Finset.card_le_one.mp hc w1 (by simp [h1, h2]) w2 (by simp [h3, h4'])
  exact GS.intro str ⟨s, hbip⟩ hfour and_ops low_ops hal hbe (and_ops g al be hgt).1
    (and_ops g al be hgt).2 (fun x => val_and hgt hal hbe x) (fun v => h7 g hg hgop v) (Or.inl hgt)
    fn reader_any

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

def opA (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 0 0
def opB (C : Circuit) (j : ℕ) : ℕ := (gateAt C j).inputs.getD 1 0

lemma opA_eq {C : Circuit} {j : ℕ} {op : GateOp} {a b : ℕ} (h : IsGate C.gates j op a b) :
    opA C j = a := by simp [opA, isgate_gateAt h]

lemma opB_eq {C : Circuit} {j : ℕ} {op : GateOp} {a b : ℕ} (h : IsGate C.gates j op a b) :
    opB C j = b := by simp [opB, isgate_gateAt h]

-- A top one of whose operands is on at no one-hot input (it is g, up to ORs of g with itself).
def Drop (n : ℕ) (C : Circuit) (g j : ℕ) : Prop :=
  ∃ om si, TopP C g j om si ∧ supp n C om = ∅

open Classical in
noncomputable def wantF (n : ℕ) (C : Circuit) (g : ℕ) (Sg : ℕ → Finset (Fin n))
    (sp : ℕ → ℕ × ℕ) (j : ℕ) : Finset (Fin n) × Finset (Fin n) :=
  if Drop n C g j then (Sg (sp j).1, Sg (sp j).2) else (supp n C (opA C j), supp n C (opB C j))

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}

lemma topP_unique {j om si om' si' : ℕ} (h : TopP C g j om si) (h' : TopP C g j om' si') :
    (om' = om ∧ si' = si) ∨ (om' = si ∧ si' = om) := by
  rcases h.2 with h1 | h1 <;> rcases h'.2 with h2 | h2
  · obtain ⟨_, e1, e2⟩ := h1.unique h2
    exact Or.inl ⟨e1.symm, e2.symm⟩
  · obtain ⟨_, e1, e2⟩ := h1.unique h2
    exact Or.inr ⟨e2.symm, e1.symm⟩
  · obtain ⟨_, e1, e2⟩ := h1.unique h2
    exact Or.inr ⟨e1.symm, e2.symm⟩
  · obtain ⟨_, e1, e2⟩ := h1.unique h2
    exact Or.inl ⟨e2.symm, e1.symm⟩

-- An operand of a top with no one-hot input is g with ORs: it comes after g.
lemma GS.empty_gf (S : GS G C g al be) {j om si : ℕ} (hT : TopP C g j om si)
    (he : supp n C om = ∅) : GF n C g om ∧ Lin n C si ∧ g < j := by
  obtain ⟨h0, h1, h2⟩ := S.top_lt hT
  have hgf : GF n C g om := by
    rcases (S.top_cases hT).1 with hl | hg
    · have := S.lin_nonempty (by omega) hl
      rw [he] at this
      exact absurd this (by simp)
    · exact hg
  refine ⟨hgf, ?_, by have := hgf.1; omega⟩
  rcases (S.top_cases hT).2 with hl | hg
  · exact hl
  · exact absurd hg (fun hg => S.top_notboth hT hgf hg)

lemma GS.drop_gt (S : GS G C g al be) {j : ℕ} (h : Drop n C g j) : g < j := by
  obtain ⟨om, si, hT, he⟩ := h
  exact (S.empty_gf hT he).2.2

lemma GS.gen_ht (S : GS G C g al be) (Sg : ℕ → Finset (Fin n)) (sp : ℕ → ℕ × ℕ)
    (hsp : ∀ j, Drop n C g j → Okw G C g Sg (sp j).1 ∧ Okw G C g Sg (sp j).2 ∧
      (sp j).1 < n + g ∧ (sp j).2 < n + g ∧ ∀ u ∈ Sg (sp j).1, ∀ v ∈ Sg (sp j).2, G.Adj u v)
    (hnd : ∀ j om si, TopP C g j om si → ¬ Drop n C g j →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        (∀ u ∈ Sg y1, ∀ v ∈ Sg y2, G.Adj u v) ∧ supp n C om ⊆ Sg y1 ∧ supp n C si ⊆ Sg y2) :
    ∀ j a b, IsGate C.gates j GateOp.and a b → j ≠ g →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        (∀ u ∈ Sg y1, ∀ v ∈ Sg y2, G.Adj u v) ∧ (wantF n C g Sg sp j).1 ⊆ Sg y1 ∧
        (wantF n C g Sg sp j).2 ⊆ Sg y2 := by
  intro j a b hgt hne
  have hT : TopP C g j a b := ⟨hne, Or.inl hgt⟩
  by_cases hd : Drop n C g j
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hsp j hd
    have := S.drop_gt hd
    refine ⟨(sp j).1, (sp j).2, h1, h2, by omega, by omega, h5, ?_, ?_⟩ <;>
    · unfold wantF; rw [ite_eq_left hd]
  · obtain ⟨y1, y2, h1, h2, h3, h4, h5, h6, h7⟩ := hnd j a b hT hd
    refine ⟨y1, y2, h1, h2, h3, h4, h5, ?_, ?_⟩
    · unfold wantF; rw [ite_eq_right hd, opA_eq hgt]; exact h6
    · unfold wantF; rw [ite_eq_right hd, opB_eq hgt]; exact h7

lemma GS.gen_cov_res (S : GS G C g al be) (Sg : ℕ → Finset (Fin n)) (sp : ℕ → ℕ × ℕ)
    {u v : Fin n} (h : ResCov n C g u v) :
    ∃ j a b, IsGate C.gates j GateOp.and a b ∧ j ≠ g ∧
      ((u ∈ (wantF n C g Sg sp j).1 ∧ v ∈ (wantF n C g Sg sp j).2) ∨
        (v ∈ (wantF n C g Sg sp j).1 ∧ u ∈ (wantF n C g Sg sp j).2)) := by
  obtain ⟨j, om, si, hT, hu, hv⟩ := h
  have hd : ¬ Drop n C g j := by
    rintro ⟨om', si', hT', he⟩
    rcases topP_unique hT hT' with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rw [he] at hu; simp at hu
    · rw [he] at hv; simp at hv
  rcases hT.2 with hgt | hgt
  · refine ⟨j, om, si, hgt, hT.1, Or.inl ?_⟩
    unfold wantF; rw [ite_eq_right hd, opA_eq hgt, opB_eq hgt]; exact ⟨hu, hv⟩
  · refine ⟨j, si, om, hgt, hT.1, Or.inr ?_⟩
    unfold wantF; rw [ite_eq_right hd, opA_eq hgt, opB_eq hgt]; exact ⟨hv, hu⟩

lemma GS.gen_cov_drop (S : GS G C g al be) (Sg : ℕ → Finset (Fin n)) (sp : ℕ → ℕ × ℕ)
    {j : ℕ} (hd : Drop n C g j) {u v : Fin n}
    (h : (u ∈ Sg (sp j).1 ∧ v ∈ Sg (sp j).2) ∨ (v ∈ Sg (sp j).1 ∧ u ∈ Sg (sp j).2)) :
    ∃ j a b, IsGate C.gates j GateOp.and a b ∧ j ≠ g ∧
      ((u ∈ (wantF n C g Sg sp j).1 ∧ v ∈ (wantF n C g Sg sp j).2) ∨
        (v ∈ (wantF n C g Sg sp j).1 ∧ u ∈ (wantF n C g Sg sp j).2)) := by
  obtain ⟨om, si, hT, _⟩ := id hd
  have hw : wantF n C g Sg sp j = (Sg (sp j).1, Sg (sp j).2) := by unfold wantF; rw [ite_eq_left hd]
  rcases hT.2 with hgt | hgt
  · exact ⟨j, om, si, hgt, hT.1, by rw [hw]; exact h⟩
  · exact ⟨j, si, om, hgt, hT.1, by rw [hw]; exact h⟩

-- The rebuilt circuit when the tops with a g-only operand can hold the extra tops.
theorem GS.gen_inplace (S : GS G C g al be) (Sg : ℕ → Finset (Fin n))
    (hv : ∀ i (hi : i < n), Sg i = {⟨i, hi⟩})
    (hl : ∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) → Okw G C g Sg (n + j) →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        Sg y1 ∪ Sg y2 = Sg (n + j))
    (sp : ℕ → ℕ × ℕ)
    (hsp : ∀ j, Drop n C g j → Okw G C g Sg (sp j).1 ∧ Okw G C g Sg (sp j).2 ∧
      (sp j).1 < n + g ∧ (sp j).2 < n + g ∧ ∀ u ∈ Sg (sp j).1, ∀ v ∈ Sg (sp j).2, G.Adj u v)
    (hnd : ∀ j om si, TopP C g j om si → ¬ Drop n C g j →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        (∀ u ∈ Sg y1, ∀ v ∈ Sg y2, G.Adj u v) ∧ supp n C om ⊆ Sg y1 ∧ supp n C si ⊆ Sg y2)
    (hcov : ∀ u v, G.Adj u v → ResCov n C g u v ∨ ∃ j, Drop n C g j ∧
      ((u ∈ Sg (sp j).1 ∧ v ∈ Sg (sp j).2) ∨ (v ∈ Sg (sp j).1 ∧ u ∈ Sg (sp j).2))) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  refine finish_inplace G C g S.str Sg hv hl (wantF n C g Sg sp) (S.gen_ht Sg sp hsp hnd) ?_
  intro u v huv
  rcases hcov u v huv with h | ⟨j, hd, h⟩
  · exact S.gen_cov_res Sg sp h
  · exact S.gen_cov_drop Sg sp hd h

-- The rebuilt circuit with one extra top at the end, paid for by two unread lower slots.
theorem GS.gen_append (S : GS G C g al be) (Sg : ℕ → Finset (Fin n))
    (hv : ∀ i (hi : i < n), Sg i = {⟨i, hi⟩})
    (hl : ∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) → Okw G C g Sg (n + j) →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        Sg y1 ∪ Sg y2 = Sg (n + j))
    (sp : ℕ → ℕ × ℕ)
    (hsp : ∀ j, Drop n C g j → Okw G C g Sg (sp j).1 ∧ Okw G C g Sg (sp j).2 ∧
      (sp j).1 < n + g ∧ (sp j).2 < n + g ∧ ∀ u ∈ Sg (sp j).1, ∀ v ∈ Sg (sp j).2, G.Adj u v)
    (hnd : ∀ j om si, TopP C g j om si → ¬ Drop n C g j →
      ∃ y1 y2, Okw G C g Sg y1 ∧ Okw G C g Sg y2 ∧ y1 < n + j ∧ y2 < n + j ∧
        (∀ u ∈ Sg y1, ∀ v ∈ Sg y2, G.Adj u v) ∧ supp n C om ⊆ Sg y1 ∧ supp n C si ⊆ Sg y2)
    (p q : ℕ) (hp : Okw G C g Sg p) (hq : Okw G C g Sg q)
    (hpq : ∀ u ∈ Sg p, ∀ v ∈ Sg q, G.Adj u v)
    (hcov : ∀ u v, G.Adj u v → ResCov n C g u v ∨ (∃ j, Drop n C g j ∧
      ((u ∈ Sg (sp j).1 ∧ v ∈ Sg (sp j).2) ∨ (v ∈ Sg (sp j).1 ∧ u ∈ Sg (sp j).2))) ∨
      (u ∈ Sg p ∧ v ∈ Sg q) ∨ (v ∈ Sg p ∧ u ∈ Sg q))
    (j2 : ℕ) (hgj : j2 ≠ g) (hj2 : j2 < C.gates.length)
    (hs2 : LowSlot G C g j2) (hc2 : ¬ Can G C g Sg (n + j2)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  have hcov' : ∀ u v, G.Adj u v → (∃ j a b, IsGate C.gates j GateOp.and a b ∧ j ≠ g ∧
      ((u ∈ (wantF n C g Sg sp j).1 ∧ v ∈ (wantF n C g Sg sp j).2) ∨
        (v ∈ (wantF n C g Sg sp j).1 ∧ u ∈ (wantF n C g Sg sp j).2))) ∨
      (u ∈ Sg p ∧ v ∈ Sg q) ∨ (v ∈ Sg p ∧ u ∈ Sg q) := by
    intro u v huv
    rcases hcov u v huv with h | ⟨j, hd, h⟩ | h
    · exact Or.inl (S.gen_cov_res Sg sp h)
    · exact Or.inl (S.gen_cov_drop Sg sp hd h)
    · exact Or.inr h
  have hgc : ¬ Can G C g Sg (n + g) := fun hc => hc.1.2.2.2 rfl
  rcases Nat.lt_or_gt_of_ne hgj with h | h
  · exact finish_append G C g S.str Sg hv hl (wantF n C g Sg sp) (S.gen_ht Sg sp hsp hnd)
      p q hp hq hpq hcov' j2 g h S.str.glt hs2 hc2 (Or.inl rfl) hgc
  · exact finish_append G C g S.str Sg hv hl (wantF n C g Sg sp) (S.gen_ht Sg sp hsp hnd)
      p q hp hq hpq hcov' g j2 h hj2 (Or.inl rfl) hgc hs2 hc2

end

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

-- An edge that no top accepts through the variable sets of its operands.
def MEdge {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) (u v : Fin n) : Prop :=
  G.Adj u v ∧ ¬ ResCov n C g u v

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}

lemma rescov_symm {u v : Fin n} (h : ResCov n C g u v) : ResCov n C g v u := by
  obtain ⟨j, om, si, hT, hu, hv⟩ := h
  exact ⟨j, si, om, hT.symm, hv, hu⟩

lemma GS.lin_or (S : GS G C g al be) {j a b : ℕ} (hgt : IsGate C.gates j GateOp.or a b)
    (ha : Lin n C a) (hb : Lin n C b) : Lin n C (n + j) := by
  obtain ⟨op, a', b', hgt', _, hla, hlb⟩ := S.str.good j hgt.lt
  obtain ⟨_, rfl, rfl⟩ := hgt.unique hgt'
  intro x hx
  rw [val_or hgt hla hlb, Bool.or_eq_true] at hx
  rw [S.supp_or hgt]
  rcases hx with hx | hx
  · obtain ⟨u, hu, hxu⟩ := ha x hx
    exact ⟨u, Finset.mem_union_left _ hu, hxu⟩
  · obtain ⟨u, hu, hxu⟩ := hb x hx
    exact ⟨u, Finset.mem_union_right _ hu, hxu⟩

-- The first wire after g that is not an OR of variables reads g itself.
lemma GS.h0 (S : GS G C g al be)
    (h : ∃ w, n + g < w ∧ w < n + C.gates.length ∧ ¬ BW G C w ∧ ¬ Lin n C w) :
    ∃ j2 b, g < j2 ∧ j2 < C.gates.length ∧ LowSlot G C g j2 ∧ b < n + j2 ∧ ¬ BW G C b ∧
      supp n C (n + j2) = supp n C b ∧ ¬ Lin n C (n + j2) := by
  classical
  have hmin : ∀ m, m < Nat.find h →
      ¬ (n + g < m ∧ m < n + C.gates.length ∧ ¬ BW G C m ∧ ¬ Lin n C m) :=
    fun m hm => Nat.find_min h hm
  obtain ⟨h1, h2, h3, h4⟩ := Nat.find_spec h
  obtain ⟨j, hj⟩ : ∃ j, Nat.find h = n + j := ⟨Nat.find h - n, by omega⟩
  rw [hj] at h1 h2 h3 h4 hmin
  obtain ⟨op, a, b, hgt, hop, ha, hb⟩ := S.str.good j (by omega)
  rcases hop with rfl | rfl
  · exact absurd (S.str.top_bw j a b hgt (by omega)) h3
  · obtain ⟨hna, hnb⟩ := S.low_ops j a b hgt h3
    have hsup := S.supp_or hgt
    have isg : ∀ c, c < n + j → ¬ BW G C c → ¬ Lin n C c → c = n + g := by
      intro c hc hnc hlc
      have hgf := (S.cases (by omega) hnc).resolve_left hlc
      have := hgf.1
      by_contra hne
      exact hmin c (by omega) ⟨by omega, by omega, hnc, hlc⟩
    by_cases hla : Lin n C a
    · have hlb : ¬ Lin n C b := fun hlb => h4 (S.lin_or hgt hla hlb)
      have hbg := isg b hb hnb hlb
      refine ⟨j, a, by omega, by omega, Or.inr ⟨a, b, hgt, h3⟩, ha, hna, ?_, h4⟩
      rw [hsup, hbg, S.supp_g, Finset.union_empty]
    · have hag := isg a ha hna hla
      refine ⟨j, b, by omega, by omega, Or.inr ⟨a, b, hgt, h3⟩, hb, hnb, ?_, h4⟩
      rw [hsup, hag, S.supp_g, Finset.empty_union]

-- A wire after g that is at least g and not below F: its variables have a common neighbour.
lemma GS.cn (S : GS G C g al be) :
    ∀ d j, C.gates.length - j = d → g < j → j < C.gates.length → ¬ BW G C (n + j) →
      (∀ x : Fin n → Bool, val C.gates x (n + g) = true → val C.gates x (n + j) = true) →
      ∃ c, ∀ u ∈ supp n C (n + j), G.Adj c u := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro j hd hgj hj hnbw hge
    have hlast : j ≠ C.gates.length - 1 := fun e => hnbw (e ▸ S.str.out_bw)
    obtain ⟨k, op, a, b, hkg, hab⟩ := S.reader_any j hj hlast
    obtain ⟨op', a', b', hkg', hop, ha, hb⟩ := S.str.good k hkg.lt
    obtain ⟨rfl, rfl, rfl⟩ := hkg.unique hkg'
    have hjk : j < k := by rcases hab with rfl | rfl <;> omega
    rcases hop with rfl | rfl
    · have hkne : k ≠ g := by omega
      -- the top k reads the wire n + j and another wire si
      have key : ∀ si, TopP C g k (n + j) si → ∃ c, ∀ u ∈ supp n C (n + j), G.Adj c u := by
        intro si hT
        by_cases hne : (supp n C si).Nonempty
        · obtain ⟨c, hc⟩ := hne
          exact ⟨c, fun u hu => (S.top_prod hT u hu c hc).symm⟩
        · exfalso
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          obtain ⟨hgf, _, _⟩ := S.empty_gf hT.symm hne
          apply S.str.g_nbw
          intro x hx
          apply S.top_bw hT
          rw [S.top_val hT, hge x hx, hgf.2.1 x hx]
          rfl
      rcases hab with rfl | rfl
      · exact key b ⟨hkne, Or.inl hkg⟩
      · exact key a ⟨hkne, Or.inr hkg⟩
    · have hnk : ¬ BW G C (n + k) := by
        intro hbk
        obtain ⟨_, _, hba, hbb⟩ := bw_or_ops S.str hkg hbk
        rcases hab with rfl | rfl
        · exact hnbw hba
        · exact hnbw hbb
      have hgek : ∀ x : Fin n → Bool, val C.gates x (n + g) = true →
          val C.gates x (n + k) = true := by
        intro x hx
        rw [val_or hkg ha hb, Bool.or_eq_true]
        rcases hab with rfl | rfl
        · exact Or.inl (hge x hx)
        · exact Or.inr (hge x hx)
      obtain ⟨c, hc⟩ := ih (C.gates.length - k) (by have := hkg.lt; omega) k rfl (by omega)
        hkg.lt hnk hgek
      refine ⟨c, fun u hu => hc u ?_⟩
      rw [S.supp_or hkg]
      rcases hab with rfl | rfl
      · exact Finset.mem_union_left _ hu
      · exact Finset.mem_union_right _ hu

-- An OR of variables that is at least g holds all of A or all of B.
lemma GS.lin_ge (S : GS G C g al be) {w : ℕ} (hL : Lin n C w)
    (hge : ∀ x : Fin n → Bool, val C.gates x (n + g) = true → val C.gates x w = true) :
    (∀ a ∈ supp n C al, a ∈ supp n C w) ∨ (∀ b ∈ supp n C be, b ∈ supp n C w) := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  simp only [not_forall] at h1 h2
  obtain ⟨a, ha, hna⟩ := h1
  obtain ⟨b, hb, hnb⟩ := h2
  have hg : val C.gates (pr a b) (n + g) = true :=
    (S.gval' _).mpr ⟨⟨a, ha, by simp [pr]⟩, ⟨b, hb, by simp [pr]⟩⟩
  rcases S.pr_lin hL (hge _ hg) with h | h
  · exact hna h
  · exact hnb h

-- The normal form of an edge accepted only through g.
lemma GS.medge_norm (S : GS G C g al be) {u v : Fin n} (h : MEdge G C g u v) :
    ∃ a0 b0 j om si, ((a0 = u ∧ b0 = v) ∨ (a0 = v ∧ b0 = u)) ∧ a0 ∈ supp n C al ∧
      b0 ∈ supp n C be ∧ G.Adj a0 b0 ∧ ¬ ResCov n C g a0 b0 ∧ TopP C g j om si ∧ GF n C g om ∧
      ¬ Lin n C om ∧ Lin n C si ∧
      ((a0 ∈ supp n C si ∧ ∀ b' ∈ supp n C be, G.Adj a0 b') ∨
        (b0 ∈ supp n C si ∧ ∀ a' ∈ supp n C al, G.Adj a' b0)) := by
  obtain ⟨hadj, hnr⟩ := h
  rcases S.edge_cases hadj with hr | ⟨j, om, si, a0, b0, hT, hgf, hls, hab, ha0, hb0, hsi⟩
  · exact absurd hr hnr
  · have hadj' : G.Adj a0 b0 := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact hadj.symm
    have hnr' : ¬ ResCov n C g a0 b0 := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnr
      · exact fun hc => hnr (rescov_symm hc)
    refine ⟨a0, b0, j, om, si, hab, ha0, hb0, hadj', hnr', hT, hgf, ?_, hls, ?_⟩
    · intro hlo
      have hg : val C.gates (pr a0 b0) (n + g) = true :=
        (S.gval' _).mpr ⟨⟨a0, ha0, by simp [pr]⟩, ⟨b0, hb0, by simp [pr]⟩⟩
      have hp := S.top_prod hT
      rcases S.pr_lin hlo (hgf.2.1 _ hg) with ho | ho <;> rcases hsi with hs | hs
      · exact (hp a0 ho a0 hs).ne rfl
      · exact hnr' ⟨j, om, si, hT, ho, hs⟩
      · exact hnr' (rescov_symm ⟨j, om, si, hT, ho, hs⟩)
      · exact (hp b0 ho b0 hs).ne rfl
    · rcases hsi with hs | hs
      · exact Or.inl ⟨hs, S.gtop_A hT hgf ha0 hs⟩
      · exact Or.inr ⟨hs, fun a' ha' => (S.symm.gtop_A hT hgf hb0 hs a' ha').symm⟩

end

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

/-! First family of sets: an OR of variables that is not inside the common neighbours of B but
holds two of them is cut down to those common neighbours. -/

-- The common neighbours of the variable set of the wire be.
def NB (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (be : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter fun v => ∀ b ∈ supp n C be, G.Adj v b

def BadN (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (be w : ℕ) : Prop :=
  Lin n C w ∧ ¬ (supp n C w ⊆ NB n G C be) ∧ 2 ≤ (supp n C w ∩ NB n G C be).card

open Classical in
noncomputable def SgN (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (be w : ℕ) : Finset (Fin n) :=
  if BadN n G C be w then supp n C w ∩ NB n G C be else supp n C w

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}

lemma mem_NB {v : Fin n} : v ∈ NB n G C be ↔ ∀ b ∈ supp n C be, G.Adj v b := by simp [NB]

lemma sgN_bad {w : ℕ} (h : BadN n G C be w) : SgN n G C be w = supp n C w ∩ NB n G C be := by
  unfold SgN; rw [ite_eq_left h]

lemma sgN_good {w : ℕ} (h : ¬ BadN n G C be w) : SgN n G C be w = supp n C w := by
  unfold SgN; rw [ite_eq_right h]

lemma GS.supp_var (S : GS G C g al be) (i : ℕ) (hi : i < n) : supp n C i = {⟨i, hi⟩} := by
  ext u
  rw [mem_supp, val_lt _ _ _ hi]
  simp [eof, eq_comm]

-- A set with two common neighbours of B and a common neighbour of its own lies inside them.
lemma GS.two_nb (S : GS G C g al be) {X : Finset (Fin n)} (h2 : 2 ≤ (X ∩ NB n G C be).card)
    {c : Fin n} (hc : ∀ u ∈ X, G.Adj c u) : X ⊆ NB n G C be := by
  obtain ⟨x1, hx1, x2, hx2, hne⟩ := Finset.one_lt_card.mp h2
  rw [Finset.mem_inter] at hx1 hx2
  have hb : ∀ b ∈ supp n C be, c = b := by
    intro b hb
    exact S.four x1 x2 c b (hc x1 hx1.1).symm (hc x2 hx2.1).symm (mem_NB.mp hx1.2 b hb)
      (mem_NB.mp hx2.2 b hb) hne
  intro u hu
  rw [mem_NB]
  intro b hb'
  rw [← hb b hb']
  exact (hc u hu).symm

lemma GS.bad_no_cn (S : GS G C g al be) {w : ℕ} (hb : BadN n G C be w) {c : Fin n}
    (hc : ∀ u ∈ supp n C w, G.Adj c u) : False :=
  hb.2.1 (S.two_nb hb.2.2 hc)

lemma GS.sgN_var (S : GS G C g al be) (i : ℕ) (hi : i < n) : SgN n G C be i = {⟨i, hi⟩} := by
  rw [sgN_good, S.supp_var i hi]
  rintro ⟨_, _, h⟩
  rw [S.supp_var i hi] at h
  have : ({⟨i, hi⟩} ∩ NB n G C be : Finset (Fin n)).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  omega

lemma GS.okwN (S : GS G C g al be) {w : ℕ} (hw : w < n + C.gates.length) (hn : ¬ BW G C w)
    (hne : (supp n C w).Nonempty) : Okw G C g (SgN n G C be) w := by
  refine ⟨hw, hn, ?_, ?_⟩
  · by_cases hb : BadN n G C be w
    · rw [sgN_bad hb]
      exact Finset.card_pos.mp (by have := hb.2.2; omega)
    · rw [sgN_good hb]; exact hne
  · rintro rfl
    rw [S.supp_g] at hne
    simp at hne

lemma GS.okwN_var (S : GS G C g al be) (v : Fin n) : Okw G C g (SgN n G C be) v.val := by
  refine S.okwN (by have := v.isLt; omega) (notBW_input G C _ v.isLt) ?_
  rw [S.supp_var v.val v.isLt]
  simp

-- A gate after g that is at least g and not below F is not cut.
lemma GS.ge_not_bad (S : GS G C g al be) {j : ℕ} (hgj : g < j) (hj : j < C.gates.length)
    (hn : ¬ BW G C (n + j))
    (hge : ∀ x : Fin n → Bool, val C.gates x (n + g) = true → val C.gates x (n + j) = true)
    {X : Finset (Fin n)} (hX : X ⊆ supp n C (n + j)) (h2 : 2 ≤ (X ∩ NB n G C be).card) :
    X ⊆ NB n G C be := by
  obtain ⟨c, hc⟩ := S.cn _ j rfl hgj hj hn hge
  exact S.two_nb h2 (fun u hu => hc u (hX hu))

lemma GS.hlN (S : GS G C g al be) : ∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) →
    Okw G C g (SgN n G C be) (n + j) →
    ∃ y1 y2, Okw G C g (SgN n G C be) y1 ∧ Okw G C g (SgN n G C be) y2 ∧ y1 < n + j ∧
      y2 < n + j ∧ SgN n G C be y1 ∪ SgN n G C be y2 = SgN n G C be (n + j) := by
  intro j a b hgt hnbw hok
  obtain ⟨op, a', b', hgt', _, ha, hb⟩ := S.str.good j hgt.lt
  obtain ⟨_, rfl, rfl⟩ := hgt.unique hgt'
  obtain ⟨hna, hnb⟩ := S.low_ops j a b hgt hnbw
  have hsup := S.supp_or hgt
  have hlen := hgt.lt
  have hza : ∀ x : Fin n → Bool, val C.gates x a = true → val C.gates x (n + j) = true :=
    fun x hx => by rw [val_or hgt ha hb, hx]; rfl
  have hzb : ∀ x : Fin n → Bool, val C.gates x b = true → val C.gates x (n + j) = true :=
    fun x hx => by rw [val_or hgt ha hb, hx]; simp
  have hsa : supp n C a ⊆ supp n C (n + j) := by rw [hsup]; exact Finset.subset_union_left
  have hsb : supp n C b ⊆ supp n C (n + j) := by rw [hsup]; exact Finset.subset_union_right
  by_cases hbad : BadN n G C be (n + j)
  · have hlin : ∀ z, z < n + j → ¬ BW G C z →
        (∀ x : Fin n → Bool, val C.gates x z = true → val C.gates x (n + j) = true) →
        (supp n C z ∩ NB n G C be = ∅) ∨ ∃ y, Okw G C g (SgN n G C be) y ∧ y < n + j ∧
          SgN n G C be y = supp n C z ∩ NB n G C be := by
      intro z hz hnz hzv
      by_cases hemp : supp n C z ∩ NB n G C be = ∅
      · exact Or.inl hemp
      · right
        have hzne : (supp n C z).Nonempty := by
          obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
          exact ⟨u, (Finset.mem_inter.mp hu).1⟩
        by_cases hbz : BadN n G C be z
        · exact ⟨z, S.okwN (by omega) hnz hzne, hz, sgN_bad hbz⟩
        · by_cases hsubN : supp n C z ⊆ NB n G C be
          · exact ⟨z, S.okwN (by omega) hnz hzne, hz, by
              rw [sgN_good hbz, Finset.inter_eq_left.mpr hsubN]⟩
          · have hlz : Lin n C z := by
              rcases S.cases (by omega) hnz with h | h
              · exact h
              · exfalso
                have hgj : g < j := by have := h.1; omega
                exact hbad.2.1 (S.ge_not_bad hgj hlen hnbw (fun x hx => hzv x (h.2.1 x hx))
                  (le_refl _) hbad.2.2)
            have hcard : (supp n C z ∩ NB n G C be).card = 1 := by
              have h1 : ¬ 2 ≤ (supp n C z ∩ NB n G C be).card := fun h2 => hbz ⟨hlz, hsubN, h2⟩
              have h0 : 0 < (supp n C z ∩ NB n G C be).card :=
                Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hemp)
              omega
            obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
            refine ⟨x.val, S.okwN_var x, by have := x.isLt; omega, ?_⟩
            rw [S.sgN_var x.val x.isLt, hx]
    have htarget : SgN n G C be (n + j) =
        supp n C a ∩ NB n G C be ∪ supp n C b ∩ NB n G C be := by
      rw [sgN_bad hbad, hsup, Finset.union_inter_distrib_right]
    have hne := hok.2.2.1
    rw [htarget] at hne ⊢
    rcases hlin a ha hna hza with ea | ⟨ya, hya, hlta, hea⟩ <;>
      rcases hlin b hb hnb hzb with eb | ⟨yb, hyb, hltb, heb⟩
    · rw [ea, eb] at hne
      simp at hne
    · exact ⟨yb, yb, hyb, hyb, hltb, hltb, by rw [heb, ea]; simp⟩
    · exact ⟨ya, ya, hya, hya, hlta, hlta, by rw [hea, eb]; simp⟩
    · exact ⟨ya, yb, hya, hyb, hlta, hltb, by rw [hea, heb]⟩
  · have hop : ∀ z, z < n + j → ¬ BW G C z → supp n C z ⊆ supp n C (n + j) →
        (supp n C z = ∅) ∨ ∃ y, Okw G C g (SgN n G C be) y ∧ y < n + j ∧
          SgN n G C be y = supp n C z := by
      intro z hz hnz hsub
      by_cases hemp : supp n C z = ∅
      · exact Or.inl hemp
      · right
        have hzne : (supp n C z).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
        have hbz : ¬ BadN n G C be z := by
          intro hbz
          have h2 : 2 ≤ (supp n C (n + j) ∩ NB n G C be).card :=
            hbz.2.2.trans (Finset.card_le_card (Finset.inter_subset_inter hsub (le_refl _)))
          have hns : ¬ supp n C (n + j) ⊆ NB n G C be := fun h => hbz.2.1 (hsub.trans h)
          by_cases hl : Lin n C (n + j)
          · exact hbad ⟨hl, hns, h2⟩
          · have hgf := (S.cases (by omega) hnbw).resolve_left hl
            have hne_g : n + j ≠ n + g := hok.2.2.2
            exact hns (S.ge_not_bad (by have := hgf.1; omega) hlen hnbw hgf.2.1 (le_refl _) h2)
        exact ⟨z, S.okwN (by omega) hnz hzne, hz, sgN_good hbz⟩
    have hne := hok.2.2.1
    rw [sgN_good hbad, hsup] at hne ⊢
    rcases hop a ha hna hsa with ea | ⟨ya, hya, hlta, hea⟩ <;>
      rcases hop b hb hnb hsb with eb | ⟨yb, hyb, hltb, heb⟩
    · rw [ea, eb] at hne
      simp at hne
    · exact ⟨yb, yb, hyb, hyb, hltb, hltb, by rw [heb, ea]; simp⟩
    · exact ⟨ya, ya, hya, hya, hlta, hlta, by rw [hea, eb]; simp⟩
    · exact ⟨ya, yb, hya, hyb, hlta, hltb, by rw [hea, heb]⟩

lemma GS.hndN (S : GS G C g al be) : ∀ j om si, TopP C g j om si → ¬ Drop n C g j →
    ∃ y1 y2, Okw G C g (SgN n G C be) y1 ∧ Okw G C g (SgN n G C be) y2 ∧ y1 < n + j ∧
      y2 < n + j ∧ (∀ u ∈ SgN n G C be y1, ∀ v ∈ SgN n G C be y2, G.Adj u v) ∧
      supp n C om ⊆ SgN n G C be y1 ∧ supp n C si ⊆ SgN n G C be y2 := by
  intro j om si hT hd
  obtain ⟨hj, hlo, hls⟩ := S.top_lt hT
  obtain ⟨hno, hns⟩ := S.top_nbw hT
  have hneo : (supp n C om).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun e => hd ⟨om, si, hT, e⟩
  have hnes : (supp n C si).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun e => hd ⟨si, om, hT.symm, e⟩
  have hp := S.top_prod hT
  have hbo : ¬ BadN n G C be om := by
    intro hb
    obtain ⟨c, hc⟩ := hnes
    exact S.bad_no_cn hb (fun u hu => (hp u hu c hc).symm)
  have hbs : ¬ BadN n G C be si := by
    intro hb
    obtain ⟨c, hc⟩ := hneo
    exact S.bad_no_cn hb (fun v hv => hp c hc v hv)
  refine ⟨om, si, S.okwN (by omega) hno hneo, S.okwN (by omega) hns hnes, hlo, hls, ?_, ?_, ?_⟩
  · rw [sgN_good hbo, sgN_good hbs]; exact hp
  · rw [sgN_good hbo]
  · rw [sgN_good hbs]

lemma GS.h0N (S : GS G C g al be)
    (h : ∃ w, n + g < w ∧ w < n + C.gates.length ∧ ¬ BW G C w ∧ ¬ Lin n C w) :
    ∃ j2, g < j2 ∧ j2 < C.gates.length ∧ LowSlot G C g j2 ∧
      ¬ Can G C g (SgN n G C be) (n + j2) := by
  obtain ⟨j2, b, hgj, hj, hls, hb, hnb, hsup, hnl⟩ := S.h0 h
  refine ⟨j2, hgj, hj, hls, fun hcan => ?_⟩
  have hnbw := lowslot_nbw S.str hls
  have hgf := (S.cases (by omega) hnbw).resolve_left hnl
  have hb2 : ¬ BadN n G C be (n + j2) := fun hb2 => hnl hb2.1
  have hne := hcan.1.2.2.1
  rw [sgN_good hb2, hsup] at hne
  have hbb : ¬ BadN n G C be b := by
    intro hbb
    exact hbb.2.1 (S.ge_not_bad hgj hj hnbw hgf.2.1 (by rw [hsup]) hbb.2.2)
  refine hcan.2 b hb (S.okwN (by omega) hnb hne) ?_
  rw [sgN_good hbb, sgN_good hb2, hsup]

lemma GS.sgN_be (S : GS G C g al be) : SgN n G C be be = supp n C be := by
  apply sgN_good
  rintro ⟨_, _, h2⟩
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (supp n C be ∩ NB n G C be).card)
  rw [Finset.mem_inter] at hb
  exact (mem_NB.mp hb.2 b hb.1).ne rfl

lemma GS.okwN_be (S : GS G C g al be) : Okw G C g (SgN n G C be) be :=
  S.okwN (by have := S.be_lt; have := S.str.glt; omega) S.be_nbw
    (S.lin_nonempty (by have := S.be_lt; have := S.str.glt; omega) S.lin_be)

-- One extra top p AND q is enough.
theorem GS.one_specialN (S : GS G C g al be) (p q : ℕ)
    (hp : Okw G C g (SgN n G C be) p) (hq : Okw G C g (SgN n G C be) q)
    (hpl : p < n + g) (hql : q < n + g)
    (hpq : ∀ u ∈ SgN n G C be p, ∀ v ∈ SgN n G C be q, G.Adj u v)
    (hcov : ∀ u v, MEdge G C g u v → (u ∈ SgN n G C be p ∧ v ∈ SgN n G C be q) ∨
      (v ∈ SgN n G C be p ∧ u ∈ SgN n G C be q)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  have hsp : ∀ j, Drop n C g j → Okw G C g (SgN n G C be) p ∧ Okw G C g (SgN n G C be) q ∧
      p < n + g ∧ q < n + g ∧ ∀ u ∈ SgN n G C be p, ∀ v ∈ SgN n G C be q, G.Adj u v :=
    fun _ _ => ⟨hp, hq, hpl, hql, hpq⟩
  by_cases hd : ∃ j, Drop n C g j
  · obtain ⟨d, hd⟩ := hd
    refine S.gen_inplace (SgN n G C be) S.sgN_var S.hlN (fun _ => (p, q)) hsp S.hndN ?_
    intro u v huv
    by_cases hr : ResCov n C g u v
    · exact Or.inl hr
    · exact Or.inr ⟨d, hd, hcov u v ⟨huv, hr⟩⟩
  · by_cases hM : ∃ u v, MEdge G C g u v
    · obtain ⟨u, v, hm⟩ := hM
      obtain ⟨a0, b0, j, om, si, _, _, _, _, _, hT, hgf, hnl, _, _⟩ := S.medge_norm hm
      obtain ⟨hj, hlo, _⟩ := S.top_lt hT
      have hog : om ≠ n + g := by
        rintro rfl
        exact hd ⟨j, n + g, si, hT, S.supp_g⟩
      obtain ⟨j2, hgj, hj2, hls, hnc⟩ := S.h0N
        ⟨om, by have := hgf.1; omega, by omega, (S.top_nbw hT).1, hnl⟩
      refine S.gen_append (SgN n G C be) S.sgN_var S.hlN (fun _ => (p, q)) hsp S.hndN p q hp hq
        hpq ?_ j2 (by omega) hj2 hls hnc
      intro u' v' huv
      by_cases hr : ResCov n C g u' v'
      · exact Or.inl hr
      · exact Or.inr (Or.inr (hcov u' v' ⟨huv, hr⟩))
    · refine S.gen_inplace (SgN n G C be) S.sgN_var S.hlN (fun _ => (p, q)) hsp S.hndN ?_
      intro u v huv
      left
      by_contra hr
      exact hM ⟨u, v, huv, hr⟩

end

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}

lemma GS.edge_exists (S : GS G C g al be) : ∃ u v : Fin n, G.Adj u v := by
  have hlen := S.str.glt
  have h := S.fn (fun _ => true)
  rw [ones S.str.good _ (by omega)] at h
  obtain ⟨u, v, huv, _, _⟩ := (F_iff G _).mp h.symm
  exact ⟨u, v, huv⟩

-- Every edge accepted only through g has its end in A adjacent to all of B: one extra top.
theorem GS.case01 (S : GS G C g al be)
    (hA : ∀ u v, MEdge G C g u v → ∀ a0 b0, ((a0 = u ∧ b0 = v) ∨ (a0 = v ∧ b0 = u)) →
      a0 ∈ supp n C al → b0 ∈ supp n C be → ∀ b' ∈ supp n C be, G.Adj a0 b') :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  have hlen := S.str.glt
  have hall := S.al_lt
  by_cases hM : ∃ u v, MEdge G C g u v
  · obtain ⟨u, v, hm⟩ := hM
    obtain ⟨a0, b0, j, om, si, hab, ha0, hb0, hadj, hnr, hT, hgf, hnl, hls, _⟩ := S.medge_norm hm
    have hA0 := hA u v hm a0 b0 hab ha0 hb0
    have hmemN : ∀ u' v', MEdge G C g u' v' → ∃ a0' b0',
        ((a0' = u' ∧ b0' = v') ∨ (a0' = v' ∧ b0' = u')) ∧ a0' ∈ supp n C al ∧
        a0' ∈ NB n G C be ∧ b0' ∈ supp n C be := by
      intro u' v' hm'
      obtain ⟨a0', b0', _, _, _, hab', ha0', hb0', _⟩ := S.medge_norm hm'
      exact ⟨a0', b0', hab', ha0', mem_NB.mpr (hA u' v' hm' a0' b0' hab' ha0' hb0'), hb0'⟩
    by_cases hbad : BadN n G C be al
    · refine S.one_specialN al be (S.okwN (by omega) S.al_nbw
        (S.lin_nonempty (by omega) S.lin_al)) S.okwN_be S.al_lt S.be_lt ?_ ?_
      · intro x hx y hy
        rw [sgN_bad hbad, Finset.mem_inter] at hx
        rw [S.sgN_be] at hy
        exact mem_NB.mp hx.2 y hy
      · intro u' v' hm'
        obtain ⟨a0', b0', hab', h1, h2, h3⟩ := hmemN u' v' hm'
        rw [sgN_bad hbad, S.sgN_be]
        rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨Finset.mem_inter.mpr ⟨h1, h2⟩, h3⟩
        · exact Or.inr ⟨Finset.mem_inter.mpr ⟨h1, h2⟩, h3⟩
    · have hone : ∀ a', a' ∈ supp n C al → a' ∈ NB n G C be → a' = a0 := by
        intro a' h1 h2
        have hns : ¬ supp n C al ⊆ NB n G C be := by
          obtain ⟨aj, haj, bj, hbj, hnadj⟩ := S.junk
          exact fun hsub => hnadj (mem_NB.mp (hsub haj) bj hbj)
        have hc : (supp n C al ∩ NB n G C be).card ≤ 1 := by
          by_contra hc
          exact hbad ⟨S.lin_al, hns, by omega⟩
        exact Finset.card_le_one.mp hc a' (Finset.mem_inter.mpr ⟨h1, h2⟩) a0
          (Finset.mem_inter.mpr ⟨ha0, mem_NB.mpr hA0⟩)
      refine S.one_specialN a0.val be (S.okwN_var a0) S.okwN_be (by have := a0.isLt; omega)
        S.be_lt ?_ ?_
      · intro x hx y hy
        rw [S.sgN_var a0.val a0.isLt, Finset.mem_singleton] at hx
        rw [S.sgN_be] at hy
        rw [hx]
        exact hA0 y hy
      · intro u' v' hm'
        obtain ⟨a0', b0', hab', h1, h2, h3⟩ := hmemN u' v' hm'
        have he := hone a0' h1 h2
        rw [S.sgN_var a0.val a0.isLt, S.sgN_be]
        rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨by rw [he]; simp, h3⟩
        · exact Or.inr ⟨by rw [he]; simp, h3⟩
  · obtain ⟨u0, v0, h0⟩ := S.edge_exists
    refine S.one_specialN u0.val v0.val (S.okwN_var u0) (S.okwN_var v0)
      (by have := u0.isLt; omega) (by have := v0.isLt; omega) ?_ ?_
    · intro x hx y hy
      rw [S.sgN_var u0.val u0.isLt, Finset.mem_singleton] at hx
      rw [S.sgN_var v0.val v0.isLt, Finset.mem_singleton] at hy
      rw [hx, hy]
      exact h0
    · intro u v hm
      exact absurd ⟨u, v, hm⟩ hM

end

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

/-! The case of two stars: a vertex `as` of A adjacent to all of B, a vertex `bs` of B adjacent
to all of A, and edges at each of them that are accepted only through g. -/

def K3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g al be : ℕ)
    (as bs a1 b2 : Fin n) : Prop :=
  (as ∈ supp n C al) ∧
  (bs ∈ supp n C be) ∧
  (a1 ∈ supp n C al) ∧
  (b2 ∈ supp n C be) ∧
  (∀ b' ∈ supp n C be, G.Adj as b') ∧
  (∀ a' ∈ supp n C al, G.Adj a' bs) ∧
  (¬ ∀ b' ∈ supp n C be, G.Adj a1 b') ∧
  (¬ ∀ a' ∈ supp n C al, G.Adj a' b2) ∧
  (¬ ResCov n C g a1 bs) ∧
  (¬ ResCov n C g as b2)

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}
  {as bs a1 b2 : Fin n}

lemma K3.intro (has : as ∈ supp n C al)
    (hbs : bs ∈ supp n C be)
    (ha1 : a1 ∈ supp n C al)
    (hb2 : b2 ∈ supp n C be)
    (hA : ∀ b' ∈ supp n C be, G.Adj as b')
    (hB : ∀ a' ∈ supp n C al, G.Adj a' bs)
    (hna1 : ¬ ∀ b' ∈ supp n C be, G.Adj a1 b')
    (hnb2 : ¬ ∀ a' ∈ supp n C al, G.Adj a' b2)
    (hnr1 : ¬ ResCov n C g a1 bs)
    (hnr2 : ¬ ResCov n C g as b2) :
    K3 G C g al be as bs a1 b2 := by
  unfold K3
  exact ⟨has, hbs, ha1, hb2, hA, hB, hna1, hnb2, hnr1, hnr2⟩

lemma K3.has (H : K3 G C g al be as bs a1 b2) :
    as ∈ supp n C al := by
  unfold K3 at H
  exact H.1

lemma K3.hbs (H : K3 G C g al be as bs a1 b2) :
    bs ∈ supp n C be := by
  unfold K3 at H
  exact H.2.1

lemma K3.ha1 (H : K3 G C g al be as bs a1 b2) :
    a1 ∈ supp n C al := by
  unfold K3 at H
  exact H.2.2.1

lemma K3.hb2 (H : K3 G C g al be as bs a1 b2) :
    b2 ∈ supp n C be := by
  unfold K3 at H
  exact H.2.2.2.1

lemma K3.hA (H : K3 G C g al be as bs a1 b2) :
    ∀ b' ∈ supp n C be, G.Adj as b' := by
  unfold K3 at H
  exact H.2.2.2.2.1

lemma K3.hB (H : K3 G C g al be as bs a1 b2) :
    ∀ a' ∈ supp n C al, G.Adj a' bs := by
  unfold K3 at H
  exact H.2.2.2.2.2.1

lemma K3.hna1 (H : K3 G C g al be as bs a1 b2) :
    ¬ ∀ b' ∈ supp n C be, G.Adj a1 b' := by
  unfold K3 at H
  exact H.2.2.2.2.2.2.1

lemma K3.hnb2 (H : K3 G C g al be as bs a1 b2) :
    ¬ ∀ a' ∈ supp n C al, G.Adj a' b2 := by
  unfold K3 at H
  exact H.2.2.2.2.2.2.2.1

lemma K3.hnr1 (H : K3 G C g al be as bs a1 b2) :
    ¬ ResCov n C g a1 bs := by
  unfold K3 at H
  exact H.2.2.2.2.2.2.2.2.1

lemma K3.hnr2 (H : K3 G C g al be as bs a1 b2) :
    ¬ ResCov n C g as b2 := by
  unfold K3 at H
  exact H.2.2.2.2.2.2.2.2.2

end

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}
  {as bs a1 b2 : Fin n}

lemma cov_norm {X Y : Finset (Fin n)} {u v a0 b0 : Fin n}
    (hab : (a0 = u ∧ b0 = v) ∨ (a0 = v ∧ b0 = u)) (ha : a0 ∈ X) (hb : b0 ∈ Y) :
    (u ∈ X ∧ v ∈ Y) ∨ (v ∈ X ∧ u ∈ Y) := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩

lemma K3.ne_b (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) : bs ≠ b2 := by
  rintro rfl
  exact K.hnb2 K.hB

lemma K3.ne_a (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) : as ≠ a1 := by
  rintro rfl
  exact K.hna1 K.hA

-- A vertex adjacent to all of B is `as`.
lemma K3.nb_eq (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) {v : Fin n}
    (hv : ∀ b' ∈ supp n C be, G.Adj v b') : v = as := by
  by_contra hne
  exact K.ne_b S (S.four v as bs b2 (hv bs K.hbs) (K.hA bs K.hbs) (hv b2 K.hb2) (K.hA b2 K.hb2) hne)

lemma K3.na_eq (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) {v : Fin n}
    (hv : ∀ a' ∈ supp n C al, G.Adj a' v) : v = bs := by
  by_contra hne
  exact K.ne_a S (S.four v bs as a1 (hv as K.has).symm (K.hB as K.has).symm (hv a1 K.ha1).symm
    (K.hB a1 K.ha1).symm hne)

lemma K3.no_cn (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) {c : Fin n}
    (h1 : G.Adj c as) (h2 : G.Adj c bs) : False := by
  obtain ⟨s, hs⟩ := S.bip
  have e1 := hs c as h1
  have e2 := hs c bs h2
  have e3 := hs as bs (K.hA bs K.hbs)
  revert e1 e2 e3
  cases s c <;> cases s as <;> cases s bs <;> simp

lemma K3.medge (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) {u v : Fin n}
    (h : MEdge G C g u v) :
    ∃ a0 b0, ((a0 = u ∧ b0 = v) ∨ (a0 = v ∧ b0 = u)) ∧ a0 ∈ supp n C al ∧ b0 ∈ supp n C be ∧
      (a0 = as ∨ b0 = bs) := by
  obtain ⟨a0, b0, _, _, _, hab, ha0, hb0, _, _, _, _, _, _, hd⟩ := S.medge_norm h
  refine ⟨a0, b0, hab, ha0, hb0, ?_⟩
  rcases hd with ⟨_, h1⟩ | ⟨_, h1⟩
  · exact Or.inl (K.nb_eq S h1)
  · exact Or.inr (K.na_eq S h1)

lemma K3.sgN_al (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) :
    SgN n G C be al = supp n C al := by
  apply sgN_good
  rintro ⟨_, _, h2⟩
  obtain ⟨x1, hx1, x2, hx2, hne⟩ := Finset.one_lt_card.mp h2
  rw [Finset.mem_inter] at hx1 hx2
  exact hne ((K.nb_eq S (mem_NB.mp hx1.2)).trans (K.nb_eq S (mem_NB.mp hx2.2)).symm)

lemma K3.okw_al (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) :
    Okw G C g (SgN n G C be) al :=
  S.okwN (by have := S.al_lt; have := S.str.glt; omega) S.al_nbw ⟨as, K.has⟩

-- The two extra tops: x_as AND OR(B), and OR(A) AND x_bs.
lemma K3.sp_a (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) :
    Okw G C g (SgN n G C be) as.val ∧ Okw G C g (SgN n G C be) be ∧ as.val < n + g ∧
      be < n + g ∧ ∀ u ∈ SgN n G C be as.val, ∀ v ∈ SgN n G C be be, G.Adj u v := by
  refine ⟨S.okwN_var as, S.okwN_be, by have := as.isLt; omega, S.be_lt, ?_⟩
  intro u hu v hv
  rw [S.sgN_var as.val as.isLt, Finset.mem_singleton] at hu
  rw [S.sgN_be] at hv
  rw [hu]; exact K.hA v hv

lemma K3.sp_b (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) :
    Okw G C g (SgN n G C be) al ∧ Okw G C g (SgN n G C be) bs.val ∧ al < n + g ∧
      bs.val < n + g ∧ ∀ u ∈ SgN n G C be al, ∀ v ∈ SgN n G C be bs.val, G.Adj u v := by
  refine ⟨K.okw_al S, S.okwN_var bs, S.al_lt, by have := bs.isLt; omega, ?_⟩
  intro u hu v hv
  rw [K.sgN_al S] at hu
  rw [S.sgN_var bs.val bs.isLt, Finset.mem_singleton] at hv
  rw [hv]; exact K.hB u hu

lemma K3.cov (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) {u v : Fin n}
    (h : MEdge G C g u v) :
    ((u ∈ SgN n G C be as.val ∧ v ∈ SgN n G C be be) ∨
      (v ∈ SgN n G C be as.val ∧ u ∈ SgN n G C be be)) ∨
    ((u ∈ SgN n G C be al ∧ v ∈ SgN n G C be bs.val) ∨
      (v ∈ SgN n G C be al ∧ u ∈ SgN n G C be bs.val)) := by
  obtain ⟨a0, b0, hab, ha0, hb0, hd⟩ := K.medge S h
  rcases hd with rfl | rfl
  · left
    exact cov_norm hab (by rw [S.sgN_var a0.val a0.isLt]; simp) (by rw [S.sgN_be]; exact hb0)
  · right
    exact cov_norm hab (by rw [K.sgN_al S]; exact ha0) (by rw [S.sgN_var b0.val b0.isLt]; simp)

-- Two tops with a g-only operand: each holds one extra top.
theorem K3.case_two (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) (d1 d2 : ℕ)
    (h1 : Drop n C g d1) (h2 : Drop n C g d2) (hne : d1 ≠ d2) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  refine S.gen_inplace (SgN n G C be) S.sgN_var S.hlN
    (fun j => if j = d1 then (as.val, be) else (al, bs.val)) ?_ S.hndN ?_
  · intro j _
    by_cases hj : j = d1
    · simp only [hj, if_true]; exact K.sp_a S
    · simp only [hj, if_false]; exact K.sp_b S
  · intro u v huv
    by_cases hr : ResCov n C g u v
    · exact Or.inl hr
    · right
      rcases K.cov S ⟨huv, hr⟩ with h | h
      · exact ⟨d1, h1, by simp only [if_true]; exact h⟩
      · exact ⟨d2, h2, by simp only [hne.symm, if_false]; exact h⟩

-- One top with a g-only operand, and a wire after g that is not an OR of variables.
theorem K3.case_one_gs (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) (d : ℕ)
    (hd : Drop n C g d)
    (hgs : ∃ w, n + g < w ∧ w < n + C.gates.length ∧ ¬ BW G C w ∧ ¬ Lin n C w) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  obtain ⟨j2, hgj, hj2, hls, hnc⟩ := S.h0N hgs
  obtain ⟨hp, hq, _, _, hpq⟩ := K.sp_b S
  refine S.gen_append (SgN n G C be) S.sgN_var S.hlN (fun _ => (as.val, be))
    (fun _ _ => K.sp_a S) S.hndN al bs.val hp hq hpq ?_ j2 (by omega) hj2 hls hnc
  intro u v huv
  by_cases hr : ResCov n C g u v
  · exact Or.inl hr
  · right
    rcases K.cov S ⟨huv, hr⟩ with h | h
    · exact Or.inl ⟨d, hd, h⟩
    · exact Or.inr h

end

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

/-! Second family of sets: a wire holding both `as` and `bs` is useless for a top (they have no
common neighbour); it is given the set `{as}`, so that its slot is free. -/

open Classical in
noncomputable def SgC (n : ℕ) (C : Circuit) (as bs : Fin n) (w : ℕ) : Finset (Fin n) :=
  if as ∈ supp n C w ∧ bs ∈ supp n C w then {as} else supp n C w

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}
  {as bs a1 b2 : Fin n}

lemma sgC_two {w : ℕ} (h : as ∈ supp n C w ∧ bs ∈ supp n C w) : SgC n C as bs w = {as} := by
  unfold SgC; rw [ite_eq_left h]

lemma sgC_not {w : ℕ} (h : ¬ (as ∈ supp n C w ∧ bs ∈ supp n C w)) :
    SgC n C as bs w = supp n C w := by
  unfold SgC; rw [ite_eq_right h]

lemma K3.ne_ab (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) : as ≠ bs := by
  intro e
  exact S.disj K.has (e ▸ K.hbs)

lemma K3.sgC_var (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) (i : ℕ) (hi : i < n) :
    SgC n C as bs i = {⟨i, hi⟩} := by
  rw [sgC_not, S.supp_var i hi]
  rw [S.supp_var i hi]
  rintro ⟨h1, h2⟩
  rw [Finset.mem_singleton] at h1 h2
  exact K.ne_ab S (h1.trans h2.symm)

lemma K3.okwC (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) {w : ℕ}
    (hw : w < n + C.gates.length) (hn : ¬ BW G C w) (hne : (supp n C w).Nonempty) :
    Okw G C g (SgC n C as bs) w := by
  refine ⟨hw, hn, ?_, ?_⟩
  · by_cases h : as ∈ supp n C w ∧ bs ∈ supp n C w
    · rw [sgC_two h]; simp
    · rw [sgC_not h]; exact hne
  · rintro rfl
    rw [S.supp_g] at hne
    simp at hne

lemma K3.okwC_var (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) (v : Fin n) :
    Okw G C g (SgC n C as bs) v.val := by
  refine K.okwC S (by have := v.isLt; omega) (notBW_input G C _ v.isLt) ?_
  rw [S.supp_var v.val v.isLt]
  simp

lemma K3.hlC (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) :
    ∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) →
    Okw G C g (SgC n C as bs) (n + j) →
    ∃ y1 y2, Okw G C g (SgC n C as bs) y1 ∧ Okw G C g (SgC n C as bs) y2 ∧ y1 < n + j ∧
      y2 < n + j ∧ SgC n C as bs y1 ∪ SgC n C as bs y2 = SgC n C as bs (n + j) := by
  intro j a b hgt hnbw hok
  obtain ⟨op, a', b', hgt', _, ha, hb⟩ := S.str.good j hgt.lt
  obtain ⟨_, rfl, rfl⟩ := hgt.unique hgt'
  obtain ⟨hna, hnb⟩ := S.low_ops j a b hgt hnbw
  have hsup := S.supp_or hgt
  have hlen := hgt.lt
  by_cases htwo : as ∈ supp n C (n + j) ∧ bs ∈ supp n C (n + j)
  · refine ⟨as.val, as.val, K.okwC_var S as, K.okwC_var S as, by have := as.isLt; omega,
      by have := as.isLt; omega, ?_⟩
    rw [K.sgC_var S as.val as.isLt, sgC_two htwo]
    simp
  · have hop : ∀ z, z < n + j → ¬ BW G C z → supp n C z ⊆ supp n C (n + j) →
        (supp n C z = ∅) ∨ ∃ y, Okw G C g (SgC n C as bs) y ∧ y < n + j ∧
          SgC n C as bs y = supp n C z := by
      intro z hz hnz hsub
      by_cases hemp : supp n C z = ∅
      · exact Or.inl hemp
      · exact Or.inr ⟨z, K.okwC S (by omega) hnz (Finset.nonempty_iff_ne_empty.mpr hemp), hz,
          sgC_not (fun h => htwo ⟨hsub h.1, hsub h.2⟩)⟩
    have hne := hok.2.2.1
    rw [sgC_not htwo, hsup] at hne ⊢
    rcases hop a ha hna (by rw [hsup]; exact Finset.subset_union_left) with
        ea | ⟨ya, hya, hlta, hea⟩ <;>
      rcases hop b hb hnb (by rw [hsup]; exact Finset.subset_union_right) with
        eb | ⟨yb, hyb, hltb, heb⟩
    · rw [ea, eb] at hne
      simp at hne
    · exact ⟨yb, yb, hyb, hyb, hltb, hltb, by rw [heb, ea]; simp⟩
    · exact ⟨ya, ya, hya, hya, hlta, hlta, by rw [hea, eb]; simp⟩
    · exact ⟨ya, yb, hya, hyb, hlta, hltb, by rw [hea, heb]⟩

lemma K3.hndC (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) :
    ∀ j om si, TopP C g j om si → ¬ Drop n C g j →
    ∃ y1 y2, Okw G C g (SgC n C as bs) y1 ∧ Okw G C g (SgC n C as bs) y2 ∧ y1 < n + j ∧
      y2 < n + j ∧ (∀ u ∈ SgC n C as bs y1, ∀ v ∈ SgC n C as bs y2, G.Adj u v) ∧
      supp n C om ⊆ SgC n C as bs y1 ∧ supp n C si ⊆ SgC n C as bs y2 := by
  intro j om si hT hd
  obtain ⟨hj, hlo, hls⟩ := S.top_lt hT
  obtain ⟨hno, hns⟩ := S.top_nbw hT
  have hneo : (supp n C om).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun e => hd ⟨om, si, hT, e⟩
  have hnes : (supp n C si).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun e => hd ⟨si, om, hT.symm, e⟩
  have hp := S.top_prod hT
  have hto : ¬ (as ∈ supp n C om ∧ bs ∈ supp n C om) := by
    rintro ⟨h1, h2⟩
    obtain ⟨c, hc⟩ := hnes
    exact K.no_cn S (hp as h1 c hc).symm (hp bs h2 c hc).symm
  have hts : ¬ (as ∈ supp n C si ∧ bs ∈ supp n C si) := by
    rintro ⟨h1, h2⟩
    obtain ⟨c, hc⟩ := hneo
    exact K.no_cn S (hp c hc as h1) (hp c hc bs h2)
  refine ⟨om, si, K.okwC S (by omega) hno hneo, K.okwC S (by omega) hns hnes, hlo, hls, ?_, ?_, ?_⟩
  · rw [sgC_not hto, sgC_not hts]; exact hp
  · rw [sgC_not hto]
  · rw [sgC_not hts]

-- One top with a g-only operand and no wire after g that is not an OR of variables: that top
-- reads g and a wire holding both `as` and `bs`, whose slot is free.
theorem K3.case_one_join (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2)
    (huniq : ∀ j j', Drop n C g j → Drop n C g j' → j = j')
    (hngs : ¬ ∃ w, n + g < w ∧ w < n + C.gates.length ∧ ¬ BW G C w ∧ ¬ Lin n C w) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  have hlen := S.str.glt
  -- an edge accepted only through g is accepted by a top that reads g itself
  have wit : ∀ a0 b0, a0 ∈ supp n C al → b0 ∈ supp n C be → MEdge G C g a0 b0 →
      ∃ j si, TopP C g j (n + g) si ∧ Lin n C si ∧
        ((a0 ∈ supp n C si ∧ ∀ b' ∈ supp n C be, G.Adj a0 b') ∨
          (b0 ∈ supp n C si ∧ ∀ a' ∈ supp n C al, G.Adj a' b0)) := by
    intro a0 b0 ha0 hb0 hm
    obtain ⟨a0', b0', j, om, si, hab, ha0', hb0', _, _, hT, hgf, hnl, hls, hd⟩ := S.medge_norm hm
    obtain ⟨rfl, rfl⟩ : a0' = a0 ∧ b0' = b0 := by
      rcases hab with h | ⟨rfl, rfl⟩
      · exact h
      · exact absurd hb0 (fun h => S.disj ha0' h)
    obtain ⟨hj, hlo, _⟩ := S.top_lt hT
    have hog : om = n + g := by
      by_contra hne
      exact hngs ⟨om, by have := hgf.1; omega, by omega, (S.top_nbw hT).1, hnl⟩
    subst hog
    exact ⟨j, si, hT, hls, hd⟩
  obtain ⟨j2, si2, hT2, hl2, hd2⟩ := wit as b2 K.has K.hb2 ⟨K.hA b2 K.hb2, K.hnr2⟩
  obtain ⟨j1, si1, hT1, hl1, hd1⟩ := wit a1 bs K.ha1 K.hbs ⟨K.hB a1 K.ha1, K.hnr1⟩
  have has2 : as ∈ supp n C si2 := by
    rcases hd2 with h | h
    · exact h.1
    · exact absurd h.2 K.hnb2
  have hbs1 : bs ∈ supp n C si1 := by
    rcases hd1 with h | h
    · exact absurd h.2 K.hna1
    · exact h.1
  have hD2 : Drop n C g j2 := ⟨n + g, si2, hT2, S.supp_g⟩
  have hD1 : Drop n C g j1 := ⟨n + g, si1, hT1, S.supp_g⟩
  have hjj := huniq j1 j2 hD1 hD2
  subst hjj
  have hsi : si1 = si2 := by
    rcases topP_unique hT2 hT1 with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · rw [← h, S.supp_g] at has2
      simp at has2
  subst hsi
  -- the slot of that wire
  obtain ⟨_, _, hsl⟩ := S.top_lt hT1
  have hnsi := (S.top_nbw hT1).2
  have hsn : n ≤ si1 := by
    by_contra hc
    rw [S.supp_var si1 (by omega), Finset.mem_singleton] at has2 hbs1
    exact K.ne_ab S (has2.trans hbs1.symm)
  obtain ⟨k, rfl⟩ : ∃ k, si1 = n + k := ⟨si1 - n, by omega⟩
  have hkg : k ≠ g := by
    rintro rfl
    rw [S.supp_g] at has2
    simp at has2
  have hls : LowSlot G C g k := by
    obtain ⟨op, a, b, hgt, hop, _, _⟩ := S.str.good k (by omega)
    rcases hop with rfl | rfl
    · exact absurd (S.str.top_bw k a b hgt hkg) hnsi
    · exact Or.inr ⟨a, b, hgt, hnsi⟩
  have hnc : ¬ Can G C g (SgC n C as bs) (n + k) := by
    intro hc
    refine hc.2 as.val (by have := as.isLt; omega) (K.okwC_var S as) ?_
    rw [K.sgC_var S as.val as.isLt, sgC_two ⟨has2, hbs1⟩]
  have hbe : SgC n C as bs be = supp n C be :=
    sgC_not (fun h => S.disj K.has h.1)
  have hal : SgC n C as bs al = supp n C al :=
    sgC_not (fun h => S.disj h.2 K.hbs)
  have hspa : Okw G C g (SgC n C as bs) as.val ∧ Okw G C g (SgC n C as bs) be ∧
      as.val < n + g ∧ be < n + g ∧
      ∀ u ∈ SgC n C as bs as.val, ∀ v ∈ SgC n C as bs be, G.Adj u v := by
    refine ⟨K.okwC_var S as, K.okwC S (by have := S.be_lt; omega) S.be_nbw ⟨bs, K.hbs⟩,
      by have := as.isLt; omega, S.be_lt, ?_⟩
    intro u hu v hv
    rw [K.sgC_var S as.val as.isLt, Finset.mem_singleton] at hu
    rw [hbe] at hv
    rw [hu]; exact K.hA v hv
  refine S.gen_append (SgC n C as bs) (K.sgC_var S) (K.hlC S) (fun _ => (as.val, be))
    (fun _ _ => hspa) (K.hndC S) al bs.val
    (K.okwC S (by have := S.al_lt; omega) S.al_nbw ⟨as, K.has⟩) (K.okwC_var S bs) ?_ ?_
    k hkg (by omega) hls hnc
  · intro u hu v hv
    rw [hal] at hu
    rw [K.sgC_var S bs.val bs.isLt, Finset.mem_singleton] at hv
    rw [hv]; exact K.hB u hu
  · intro u v huv
    by_cases hr : ResCov n C g u v
    · exact Or.inl hr
    · right
      obtain ⟨a0, b0, hab, ha0, hb0, hd⟩ := K.medge S ⟨huv, hr⟩
      rcases hd with rfl | rfl
      · left
        exact ⟨j1, hD1, cov_norm hab (by rw [K.sgC_var S a0.val a0.isLt]; simp)
          (by rw [hbe]; exact hb0)⟩
      · right
        exact cov_norm hab (by rw [hal]; exact ha0) (by rw [K.sgC_var S b0.val b0.isLt]; simp)

end

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

/-! Third family of sets: a wire through g whose variables are all neighbours of `as` gets B
added (g is replaced by OR(B) below it), one whose variables are neighbours of `bs` gets A. -/

-- Wire w is not an OR of variables, and its variables are neighbours of t.
def TB (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (t : Fin n) (w : ℕ) :
    Prop :=
  ¬ Lin n C w ∧ (supp n C w).Nonempty ∧ ∀ u ∈ supp n C w, G.Adj t u

open Classical in
noncomputable def SgT (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (al be : ℕ) (as bs : Fin n) (w : ℕ) : Finset (Fin n) :=
  if TB n G C as w then supp n C w ∪ supp n C be
  else if TB n G C bs w then supp n C w ∪ supp n C al
  else supp n C w

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}
  {as bs a1 b2 : Fin n}

lemma K3.symm (K : K3 G C g al be as bs a1 b2) : K3 G C g be al bs as b2 a1 :=
  K3.intro K.hbs K.has K.hb2 K.ha1 (fun b' hb' => (K.hB b' hb').symm)
    (fun a' ha' => (K.hA a' ha').symm) (fun h => K.hnb2 (fun a' ha' => (h a' ha').symm))
    (fun h => K.hna1 (fun b' hb' => (h b' hb').symm)) (fun h => K.hnr2 (rescov_symm h))
    (fun h => K.hnr1 (rescov_symm h))

lemma K3.tb_excl (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) {w : ℕ}
    (h1 : TB n G C as w) (h2 : TB n G C bs w) : False := by
  obtain ⟨u, hu⟩ := h1.2.1
  exact K.no_cn S (h1.2.2 u hu).symm (h2.2.2 u hu).symm

lemma sgT_B {w : ℕ} (h : TB n G C as w) :
    SgT n G C al be as bs w = supp n C w ∪ supp n C be := by
  unfold SgT; rw [ite_eq_left h]

lemma K3.sgT_A (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) {w : ℕ}
    (h : TB n G C bs w) : SgT n G C al be as bs w = supp n C w ∪ supp n C al := by
  unfold SgT; rw [ite_eq_right (fun h1 => K.tb_excl S h1 h), ite_eq_left h]

lemma sgT_0 {w : ℕ} (h1 : ¬ TB n G C as w) (h2 : ¬ TB n G C bs w) :
    SgT n G C al be as bs w = supp n C w := by
  unfold SgT; rw [ite_eq_right h1, ite_eq_right h2]

lemma sgT_lin {w : ℕ} (h : Lin n C w) : SgT n G C al be as bs w = supp n C w :=
  sgT_0 (fun h1 => h1.1 h) (fun h1 => h1.1 h)

lemma sub_sgT (w : ℕ) : supp n C w ⊆ SgT n G C al be as bs w := by
  unfold SgT
  split_ifs
  · exact Finset.subset_union_left
  · exact Finset.subset_union_left
  · exact le_refl _

lemma GS.lin_var (S : GS G C g al be) (i : ℕ) (hi : i < n) : Lin n C i := by
  have hlen := S.str.glt
  rcases S.cases (by omega) (notBW_input G C i hi) with h | h
  · exact h
  · have := h.1; omega

lemma GS.sgT_var (S : GS G C g al be) (i : ℕ) (hi : i < n) :
    SgT n G C al be as bs i = {⟨i, hi⟩} := by
  rw [sgT_lin (S.lin_var i hi), S.supp_var i hi]

lemma GS.okwT (S : GS G C g al be) {w : ℕ} (hw : w < n + C.gates.length) (hn : ¬ BW G C w)
    (hne : (supp n C w).Nonempty) : Okw G C g (SgT n G C al be as bs) w := by
  refine ⟨hw, hn, hne.mono (sub_sgT w), ?_⟩
  rintro rfl
  rw [S.supp_g] at hne
  simp at hne

lemma GS.okwT_var (S : GS G C g al be) (v : Fin n) :
    Okw G C g (SgT n G C al be as bs) v.val := by
  refine S.okwT (by have := v.isLt; omega) (notBW_input G C _ v.isLt) ?_
  rw [S.supp_var v.val v.isLt]
  simp

-- A gate of type t: its two operands, with g replaced by the wire wx.
lemma GS.typed_gate (S : GS G C g al be) (t : Fin n) (wx : ℕ) (hwx : wx < n + g)
    (hLx : Lin n C wx) (hnx : ¬ BW G C wx)
    (hsg : ∀ z, TB n G C t z → SgT n G C al be as bs z = supp n C z ∪ supp n C wx)
    {j a b : ℕ} (hgt : IsGate C.gates j GateOp.or a b) (hnbw : ¬ BW G C (n + j))
    (hT : TB n G C t (n + j)) :
    ∃ y1 y2, Okw G C g (SgT n G C al be as bs) y1 ∧ Okw G C g (SgT n G C al be as bs) y2 ∧
      y1 < n + j ∧ y2 < n + j ∧
      SgT n G C al be as bs y1 ∪ SgT n G C al be as bs y2 = supp n C (n + j) ∪ supp n C wx := by
  obtain ⟨op, a', b', hgt', _, ha, hb⟩ := S.str.good j hgt.lt
  obtain ⟨_, rfl, rfl⟩ := hgt.unique hgt'
  obtain ⟨hna, hnb⟩ := S.low_ops j a b hgt hnbw
  have hsup := S.supp_or hgt
  have hlen := hgt.lt
  have hgf := (S.cases (by omega) hnbw).resolve_left hT.1
  have hgj : n + g ≤ n + j := hgf.1
  have hop : ∀ z, z < n + j → ¬ BW G C z → supp n C z ⊆ supp n C (n + j) →
      ∃ y, Okw G C g (SgT n G C al be as bs) y ∧ y < n + j ∧
        ((Lin n C z ∧ SgT n G C al be as bs y = supp n C z) ∨
          (¬ Lin n C z ∧ SgT n G C al be as bs y = supp n C z ∪ supp n C wx)) := by
    intro z hz hnz hsub
    by_cases hl : Lin n C z
    · exact ⟨z, S.okwT (by omega) hnz (S.lin_nonempty (by omega) hl), hz, Or.inl ⟨hl, sgT_lin hl⟩⟩
    · by_cases hemp : supp n C z = ∅
      · refine ⟨wx, S.okwT (by omega) hnx (S.lin_nonempty (by omega) hLx), by omega,
          Or.inr ⟨hl, ?_⟩⟩
        rw [sgT_lin hLx, hemp, Finset.empty_union]
      · have hzT : TB n G C t z :=
          ⟨hl, Finset.nonempty_iff_ne_empty.mpr hemp, fun u hu => hT.2.2 u (hsub hu)⟩
        exact ⟨z, S.okwT (by omega) hnz hzT.2.1, hz, Or.inr ⟨hl, hsg z hzT⟩⟩
  obtain ⟨ya, hya, hlta, hca⟩ := hop a ha hna (by rw [hsup]; exact Finset.subset_union_left)
  obtain ⟨yb, hyb, hltb, hcb⟩ := hop b hb hnb (by rw [hsup]; exact Finset.subset_union_right)
  refine ⟨ya, yb, hya, hyb, hlta, hltb, ?_⟩
  rw [hsup]
  rcases hca with ⟨hla, ea⟩ | ⟨hla, ea⟩ <;> rcases hcb with ⟨hlb, eb⟩ | ⟨hlb, eb⟩
  · exact absurd (S.lin_or hgt hla hlb) hT.1
  · rw [ea, eb]; ext x; simp only [Finset.mem_union]; tauto
  · rw [ea, eb]; ext x; simp only [Finset.mem_union]; tauto
  · rw [ea, eb]; ext x; simp only [Finset.mem_union]; tauto

-- An operand of type t under a gate that is not of type t: its plain set is still available.
lemma GS.zero_operand (S : GS G C g al be) (t : Fin n) (wx wx' : ℕ)
    (hsg : ∀ z, TB n G C t z → SgT n G C al be as bs z = supp n C z ∪ supp n C wx)
    (ht : t ∈ supp n C wx') {j : ℕ} (hj : j < C.gates.length) (hnbw : ¬ BW G C (n + j))
    (hnt : ¬ TB n G C t (n + j))
    (halt : Lin n C (n + j) → (∀ x ∈ supp n C wx', x ∈ supp n C (n + j)) ∨
      (∀ x ∈ supp n C wx, x ∈ supp n C (n + j)))
    {z : ℕ} (hz : z < n + j) (hnz : ¬ BW G C z) (hsub : supp n C z ⊆ supp n C (n + j))
    (hge : ∀ x : Fin n → Bool, val C.gates x z = true → val C.gates x (n + j) = true)
    (hTz : TB n G C t z) :
    ∃ y, Okw G C g (SgT n G C al be as bs) y ∧ y < n + j ∧
      supp n C z ⊆ SgT n G C al be as bs y ∧ SgT n G C al be as bs y ⊆ supp n C (n + j) := by
  by_cases hX : ∀ x ∈ supp n C wx, x ∈ supp n C (n + j)
  · refine ⟨z, S.okwT (by omega) hnz hTz.2.1, hz, sub_sgT z, ?_⟩
    rw [hsg z hTz]
    exact Finset.union_subset hsub hX
  · have hgfz := (S.cases (by omega) hnz).resolve_left hTz.1
    have hgj : g < j := by have := hgfz.1; omega
    obtain ⟨x, hx⟩ := hTz.2.1
    have hall : ∀ u ∈ supp n C z, u = x := by
      intro u hu
      by_contra hne
      obtain ⟨c, hc⟩ := S.cn _ j rfl hgj hj hnbw (fun y hy => hge y (hgfz.2.1 y hy))
      have hct : c = t := S.four u x c t (hc u (hsub hu)).symm (hc x (hsub hx)).symm
        (hTz.2.2 u hu).symm (hTz.2.2 x hx).symm hne
      subst hct
      by_cases hl : Lin n C (n + j)
      · rcases halt hl with h | h
        · exact (hc c (h c ht)).ne rfl
        · exact hX h
      · exact hnt ⟨hl, ⟨x, hsub hx⟩, hc⟩
    refine ⟨x.val, S.okwT_var x, by have := x.isLt; omega, ?_, ?_⟩
    · rw [S.sgT_var x.val x.isLt]
      intro u hu
      rw [Finset.mem_singleton]
      exact hall u hu
    · rw [S.sgT_var x.val x.isLt]
      intro u hu
      rw [Finset.mem_singleton] at hu
      rw [hu]; exact hsub hx

lemma K3.hlT (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) :
    ∀ j a b, IsGate C.gates j GateOp.or a b → ¬ BW G C (n + j) →
    Okw G C g (SgT n G C al be as bs) (n + j) →
    ∃ y1 y2, Okw G C g (SgT n G C al be as bs) y1 ∧ Okw G C g (SgT n G C al be as bs) y2 ∧
      y1 < n + j ∧ y2 < n + j ∧
      SgT n G C al be as bs y1 ∪ SgT n G C al be as bs y2 = SgT n G C al be as bs (n + j) := by
  intro j a b hgt hnbw hok
  by_cases hB : TB n G C as (n + j)
  · rw [sgT_B hB]
    exact S.typed_gate as be S.be_lt S.lin_be S.be_nbw (fun z hz => sgT_B hz) hgt hnbw hB
  · by_cases hA : TB n G C bs (n + j)
    · rw [K.sgT_A S hA]
      exact S.typed_gate bs al S.al_lt S.lin_al S.al_nbw (fun z hz => K.sgT_A S hz) hgt hnbw hA
    · obtain ⟨op, a', b', hgt', _, ha, hb⟩ := S.str.good j hgt.lt
      obtain ⟨_, rfl, rfl⟩ := hgt.unique hgt'
      obtain ⟨hna, hnb⟩ := S.low_ops j a b hgt hnbw
      have hsup := S.supp_or hgt
      have hlen := hgt.lt
      have hop : ∀ z, z < n + j → ¬ BW G C z → supp n C z ⊆ supp n C (n + j) →
          (∀ x : Fin n → Bool, val C.gates x z = true → val C.gates x (n + j) = true) →
          (supp n C z = ∅) ∨ ∃ y, Okw G C g (SgT n G C al be as bs) y ∧ y < n + j ∧
            supp n C z ⊆ SgT n G C al be as bs y ∧
            SgT n G C al be as bs y ⊆ supp n C (n + j) := by
        intro z hz hnz hsub hge
        by_cases hemp : supp n C z = ∅
        · exact Or.inl hemp
        · right
          have hzne := Finset.nonempty_iff_ne_empty.mpr hemp
          by_cases hzB : TB n G C as z
          · refine S.zero_operand as be al (fun z hz => sgT_B hz) K.has hlen hnbw hB ?_ hz hnz
              hsub hge hzB
            intro hl
            have hgfz := (S.cases (by omega) hnz).resolve_left hzB.1
            exact S.lin_ge hl (fun y hy => hge y (hgfz.2.1 y hy))
          · by_cases hzA : TB n G C bs z
            · refine S.zero_operand bs al be (fun z hz => K.sgT_A S hz) K.hbs hlen hnbw hA ?_ hz
                hnz hsub hge hzA
              intro hl
              have hgfz := (S.cases (by omega) hnz).resolve_left hzA.1
              exact (S.lin_ge hl (fun y hy => hge y (hgfz.2.1 y hy))).symm
            · exact ⟨z, S.okwT (by omega) hnz hzne, hz, by rw [sgT_0 hzB hzA], by
                rw [sgT_0 hzB hzA]; exact hsub⟩
      have hsa : supp n C a ⊆ supp n C (n + j) := by rw [hsup]; exact Finset.subset_union_left
      have hsb : supp n C b ⊆ supp n C (n + j) := by rw [hsup]; exact Finset.subset_union_right
      have hza : ∀ x : Fin n → Bool, val C.gates x a = true → val C.gates x (n + j) = true :=
        fun x hx => by rw [val_or hgt ha hb, hx]; rfl
      have hzb : ∀ x : Fin n → Bool, val C.gates x b = true → val C.gates x (n + j) = true :=
        fun x hx => by rw [val_or hgt ha hb, hx]; simp
      have hne : (supp n C (n + j)).Nonempty := by
        have := hok.2.2.1
        rwa [sgT_0 hB hA] at this
      rw [sgT_0 hB hA]
      rcases hop a ha hna hsa hza with ea | ⟨ya, hya, hlta, h1a, h2a⟩ <;>
        rcases hop b hb hnb hsb hzb with eb | ⟨yb, hyb, hltb, h1b, h2b⟩
      · rw [hsup, ea, eb] at hne
        simp at hne
      · refine ⟨yb, yb, hyb, hyb, hltb, hltb, Finset.Subset.antisymm
          (Finset.union_subset h2b h2b) ?_⟩
        rw [hsup, ea, Finset.empty_union]
        exact h1b.trans Finset.subset_union_left
      · refine ⟨ya, ya, hya, hya, hlta, hlta, Finset.Subset.antisymm
          (Finset.union_subset h2a h2a) ?_⟩
        rw [hsup, eb, Finset.union_empty]
        exact h1a.trans Finset.subset_union_left
      · refine ⟨ya, yb, hya, hyb, hlta, hltb, Finset.Subset.antisymm
          (Finset.union_subset h2a h2b) ?_⟩
        rw [hsup]
        exact Finset.union_subset_union h1a h1b

end

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

-- What the rebuilt top must accept on the side of its operand om, the other operand being si.
open Classical in
noncomputable def WT (n : ℕ) (C : Circuit) (al be : ℕ) (as bs : Fin n) (om si : ℕ) :
    Finset (Fin n) :=
  if ¬ Lin n C om ∧ supp n C si = {as} then supp n C om ∪ supp n C be
  else if ¬ Lin n C om ∧ supp n C si = {bs} then supp n C om ∪ supp n C al
  else supp n C om

noncomputable def wantT (n : ℕ) (C : Circuit) (al be : ℕ) (as bs : Fin n) (j : ℕ) :
    Finset (Fin n) × Finset (Fin n) :=
  (WT n C al be as bs (opA C j) (opB C j), WT n C al be as bs (opB C j) (opA C j))

section
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g al be : ℕ}
  {as bs a1 b2 : Fin n}

lemma sub_WT (om si : ℕ) : supp n C om ⊆ WT n C al be as bs om si := by
  unfold WT
  split_ifs
  · exact Finset.subset_union_left
  · exact Finset.subset_union_left
  · exact le_refl _

lemma WT_lin {om si : ℕ} (h : Lin n C om) : WT n C al be as bs om si = supp n C om := by
  unfold WT
  rw [ite_eq_right (fun h1 => h1.1 h), ite_eq_right (fun h1 => h1.1 h)]

-- The operand of a top that is not an OR of variables: a wire for its side.
lemma K3.top_side (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) {j om si : ℕ}
    (hT : TopP C g j om si) (hnl : ¬ Lin n C om) (hneo : (supp n C om).Nonempty)
    (hnes : (supp n C si).Nonempty) :
    ∃ y1, Okw G C g (SgT n G C al be as bs) y1 ∧ y1 < n + j ∧
      (∀ u ∈ SgT n G C al be as bs y1, ∀ v ∈ supp n C si, G.Adj u v) ∧
      WT n C al be as bs om si ⊆ SgT n G C al be as bs y1 := by
  obtain ⟨hj, hlo, hls⟩ := S.top_lt hT
  obtain ⟨hno, hns⟩ := S.top_nbw hT
  have hp := S.top_prod hT
  have hok : Okw G C g (SgT n G C al be as bs) om := S.okwT (by omega) hno hneo
  -- if all of the operand is adjacent to t and it holds two variables, the other side is {t}
  have single : ∀ t : Fin n, TB n G C t om → supp n C si ≠ {t} → ∃ r, supp n C om = {r} := by
    intro t hTt hne
    obtain ⟨r, hr⟩ := hneo
    refine ⟨r, Finset.eq_singleton_iff_unique_mem.mpr ⟨hr, fun u hu => ?_⟩⟩
    by_contra hur
    apply hne
    obtain ⟨v0, hv0⟩ := hnes
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun v hv => ?_⟩
    · have : v0 = t := S.four u r v0 t (hp u hu v0 hv0) (hp r hr v0 hv0) (hTt.2.2 u hu).symm
        (hTt.2.2 r hr).symm hur
      rw [← this]; exact hv0
    · exact S.four u r v t (hp u hu v hv) (hp r hr v hv) (hTt.2.2 u hu).symm
        (hTt.2.2 r hr).symm hur
  have var_case : ∀ r, supp n C om = {r} → supp n C om ⊆ SgT n G C al be as bs r.val ∧
      ∀ u ∈ SgT n G C al be as bs r.val, ∀ v ∈ supp n C si, G.Adj u v := by
    intro r hr
    rw [S.sgT_var r.val r.isLt]
    refine ⟨by rw [hr], fun u hu v hv => ?_⟩
    rw [Finset.mem_singleton] at hu
    rw [hu]
    exact hp r (by rw [hr]; simp) v hv
  by_cases e1 : supp n C si = {as}
  · have hB : TB n G C as om := ⟨hnl, hneo, fun u hu => (hp u hu as (by rw [e1]; simp)).symm⟩
    refine ⟨om, hok, hlo, ?_, ?_⟩
    · intro u hu v hv
      rw [e1, Finset.mem_singleton] at hv
      rw [sgT_B hB, Finset.mem_union] at hu
      rw [hv]
      rcases hu with hu | hu
      · exact hp u hu as (by rw [e1]; simp)
      · exact (K.hA u hu).symm
    · unfold WT
      rw [ite_eq_left ⟨hnl, e1⟩, sgT_B hB]
  · by_cases e2 : supp n C si = {bs}
    · have hA : TB n G C bs om := ⟨hnl, hneo, fun u hu => (hp u hu bs (by rw [e2]; simp)).symm⟩
      refine ⟨om, hok, hlo, ?_, ?_⟩
      · intro u hu v hv
        rw [e2, Finset.mem_singleton] at hv
        rw [K.sgT_A S hA, Finset.mem_union] at hu
        rw [hv]
        rcases hu with hu | hu
        · exact hp u hu bs (by rw [e2]; simp)
        · exact K.hB u hu
      · unfold WT
        rw [ite_eq_right (fun h => e1 h.2), ite_eq_left ⟨hnl, e2⟩, K.sgT_A S hA]
    · have hW : WT n C al be as bs om si = supp n C om := by
        unfold WT
        rw [ite_eq_right (fun h => e1 h.2), ite_eq_right (fun h => e2 h.2)]
      rw [hW]
      by_cases hB : TB n G C as om
      · obtain ⟨r, hr⟩ := single as hB e1
        obtain ⟨h1, h2⟩ := var_case r hr
        exact ⟨r.val, S.okwT_var r, by have := r.isLt; omega, h2, h1⟩
      · by_cases hA : TB n G C bs om
        · obtain ⟨r, hr⟩ := single bs hA e2
          obtain ⟨h1, h2⟩ := var_case r hr
          exact ⟨r.val, S.okwT_var r, by have := r.isLt; omega, h2, h1⟩
        · exact ⟨om, hok, hlo, by rw [sgT_0 hB hA]; exact hp, by rw [sgT_0 hB hA]⟩

lemma K3.top_pair (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) {j om si : ℕ}
    (hT : TopP C g j om si) (hd : ¬ Drop n C g j) :
    ∃ y1 y2, Okw G C g (SgT n G C al be as bs) y1 ∧ Okw G C g (SgT n G C al be as bs) y2 ∧
      y1 < n + j ∧ y2 < n + j ∧
      (∀ u ∈ SgT n G C al be as bs y1, ∀ v ∈ SgT n G C al be as bs y2, G.Adj u v) ∧
      WT n C al be as bs om si ⊆ SgT n G C al be as bs y1 ∧
      WT n C al be as bs si om ⊆ SgT n G C al be as bs y2 := by
  obtain ⟨hj, hlo, hls⟩ := S.top_lt hT
  obtain ⟨hno, hns⟩ := S.top_nbw hT
  have hneo : (supp n C om).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun e => hd ⟨om, si, hT, e⟩
  have hnes : (supp n C si).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun e => hd ⟨si, om, hT.symm, e⟩
  have hp := S.top_prod hT
  by_cases hlo' : Lin n C om
  · by_cases hls' : Lin n C si
    · refine ⟨om, si, S.okwT (by omega) hno hneo, S.okwT (by omega) hns hnes, hlo, hls, ?_, ?_, ?_⟩
      · rw [sgT_lin hlo', sgT_lin hls']; exact hp
      · rw [WT_lin hlo', sgT_lin hlo']
      · rw [WT_lin hls', sgT_lin hls']
    · obtain ⟨y, hy, hlt, hpr, hsub⟩ := K.top_side S hT.symm hls' hnes hneo
      refine ⟨om, y, S.okwT (by omega) hno hneo, hy, hlo, hlt, ?_, ?_, hsub⟩
      · rw [sgT_lin hlo']
        exact fun u hu v hv => (hpr v hv u hu).symm
      · rw [WT_lin hlo', sgT_lin hlo']
  · have hls' : Lin n C si := by
      rcases (S.top_cases hT).2 with h | h
      · exact h
      · exact absurd h (fun h => S.top_notboth hT ((S.cases (by omega) hno).resolve_left hlo') h)
    obtain ⟨y, hy, hlt, hpr, hsub⟩ := K.top_side S hT hlo' hneo hnes
    refine ⟨y, si, hy, S.okwT (by omega) hns hnes, hlt, hls, ?_, hsub, ?_⟩
    · rw [sgT_lin hls']; exact hpr
    · rw [WT_lin hls', sgT_lin hls']

-- A top reading through g (with variables) whose other operand holds `as`: that operand is x_as.
lemma K3.claimT (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2) {j om si : ℕ}
    (hT : TopP C g j om si) (hgf : GF n C g om) (hneo : (supp n C om).Nonempty)
    (has : as ∈ supp n C si) : supp n C si = {as} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨has, fun s hs => ?_⟩
  by_contra hne
  obtain ⟨r, hr⟩ := hneo
  have hp := S.top_prod hT
  have hnb := K.hnb2
  simp only [not_forall] at hnb
  obtain ⟨a, ha, hna⟩ := hnb
  have hsb2 : G.Adj s b2 := by
    rcases S.gtop_J hT hgf hs ha K.hb2 hna with h | h
    · exfalso
      obtain ⟨c, hc⟩ := S.bip
      have e1 := hc r s (hp r hr s hs)
      have e2 := hc r as (hp r hr as has)
      have e3 := hc a bs (K.hB a ha)
      have e4 := hc as bs (K.hA bs K.hbs)
      have e5 := hc s a h
      revert e1 e2 e3 e4 e5
      cases c r <;> cases c s <;> cases c as <;> cases c a <;> cases c bs <;> simp
    · exact h
  have hrb : r = b2 := S.four as s r b2 (hp r hr as has).symm (hp r hr s hs).symm (K.hA b2 K.hb2)
    hsb2 (fun e => hne e.symm)
  exact K.hnr2 (rescov_symm ⟨j, om, si, hT, hrb ▸ hr, has⟩)

lemma topP_want {j om si : ℕ} (hT : TopP C g j om si) {x y : Fin n}
    (hx : x ∈ WT n C al be as bs om si) (hy : y ∈ WT n C al be as bs si om) :
    ∃ j a b, IsGate C.gates j GateOp.and a b ∧ j ≠ g ∧
      ((x ∈ (wantT n C al be as bs j).1 ∧ y ∈ (wantT n C al be as bs j).2) ∨
        (y ∈ (wantT n C al be as bs j).1 ∧ x ∈ (wantT n C al be as bs j).2)) := by
  rcases hT.2 with hgt | hgt
  · refine ⟨j, om, si, hgt, hT.1, Or.inl ?_⟩
    unfold wantT
    rw [opA_eq hgt, opB_eq hgt]
    exact ⟨hx, hy⟩
  · refine ⟨j, si, om, hgt, hT.1, Or.inr ?_⟩
    unfold wantT
    rw [opA_eq hgt, opB_eq hgt]
    exact ⟨hy, hx⟩

-- No top with a g-only operand: the chains above g carry B or A.
theorem K3.case_none (S : GS G C g al be) (K : K3 G C g al be as bs a1 b2)
    (hnd : ¬ ∃ j, Drop n C g j) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  refine finish_inplace G C g S.str (SgT n G C al be as bs) S.sgT_var (K.hlT S)
    (wantT n C al be as bs) ?_ ?_
  · intro j a b hgt hne
    have hT : TopP C g j a b := ⟨hne, Or.inl hgt⟩
    obtain ⟨y1, y2, h1, h2, h3, h4, h5, h6, h7⟩ := K.top_pair S hT (fun h => hnd ⟨j, h⟩)
    refine ⟨y1, y2, h1, h2, h3, h4, h5, ?_, ?_⟩
    · unfold wantT; rw [opA_eq hgt, opB_eq hgt]; exact h6
    · unfold wantT; rw [opA_eq hgt, opB_eq hgt]; exact h7
  · intro u v huv
    have flip : ∀ {x y : Fin n}, (∃ j a b, IsGate C.gates j GateOp.and a b ∧ j ≠ g ∧
        ((x ∈ (wantT n C al be as bs j).1 ∧ y ∈ (wantT n C al be as bs j).2) ∨
          (y ∈ (wantT n C al be as bs j).1 ∧ x ∈ (wantT n C al be as bs j).2))) →
        ∃ j a b, IsGate C.gates j GateOp.and a b ∧ j ≠ g ∧
        ((y ∈ (wantT n C al be as bs j).1 ∧ x ∈ (wantT n C al be as bs j).2) ∨
          (x ∈ (wantT n C al be as bs j).1 ∧ y ∈ (wantT n C al be as bs j).2)) := by
      rintro x y ⟨j, a, b, h1, h2, h3⟩
      exact ⟨j, a, b, h1, h2, h3.symm⟩
    by_cases hr : ResCov n C g u v
    · obtain ⟨j, om, si, hT, hu, hv⟩ := hr
      exact topP_want hT (sub_WT om si hu) (sub_WT si om hv)
    · obtain ⟨a0, b0, j, om, si, hab, ha0, hb0, _, _, hT, hgf, hnl, hls, hd⟩ :=
        S.medge_norm ⟨huv, hr⟩
      have hneo : (supp n C om).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        exact fun e => hnd ⟨j, om, si, hT, e⟩
      -- the top j accepts the pair b0 (on the side of om) and a0 (on the side of si)
      have hcov : b0 ∈ WT n C al be as bs om si ∧ a0 ∈ WT n C al be as bs si om ∨
          a0 ∈ WT n C al be as bs om si ∧ b0 ∈ WT n C al be as bs si om := by
        rcases hd with ⟨hs, hall⟩ | ⟨hs, hall⟩
        · have e := K.nb_eq S hall
          subst e
          have hsi := K.claimT S hT hgf hneo hs
          left
          refine ⟨?_, sub_WT si om hs⟩
          unfold WT
          rw [ite_eq_left ⟨hnl, hsi⟩]
          exact Finset.mem_union_right _ hb0
        · have e := K.na_eq S hall
          subst e
          have hsi := K.symm.claimT S.symm hT hgf hneo hs
          right
          refine ⟨?_, sub_WT si om hs⟩
          unfold WT
          rw [ite_eq_right (fun h => K.ne_ab S ((Finset.singleton_injective (hsi.symm.trans h.2)).symm)),
            ite_eq_left ⟨hnl, hsi⟩]
          exact Finset.mem_union_right _ ha0
      rcases hcov with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact flip (topP_want hT h1 h2)
        · exact topP_want hT h1 h2
      · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact topP_want hT h1 h2
        · exact flip (topP_want hT h1 h2)

end

end PEqualNP.Outside.L_meta_3700

namespace PEqualNP.Outside.L_meta_3700

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

-- When one extra top on the side of A is not enough: an edge at a vertex of B adjacent to all
-- of A, accepted only through g, whose end in A is not adjacent to all of B.
lemma GS.not_case01 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {g al be : ℕ} (S : GS G C g al be)
    (h : ¬ ∀ u v, MEdge G C g u v → ∀ a0 b0, ((a0 = u ∧ b0 = v) ∨ (a0 = v ∧ b0 = u)) →
      a0 ∈ supp n C al → b0 ∈ supp n C be → ∀ b' ∈ supp n C be, G.Adj a0 b') :
    ∃ a1 bs, a1 ∈ supp n C al ∧ bs ∈ supp n C be ∧ ¬ ResCov n C g a1 bs ∧
      (∀ a' ∈ supp n C al, G.Adj a' bs) ∧ ¬ ∀ b' ∈ supp n C be, G.Adj a1 b' := by
  by_contra hc
  apply h
  intro u v hm a0 b0 hab ha0 hb0
  by_contra hna
  apply hc
  obtain ⟨a0', b0', _, _, _, hab', ha0', hb0', _, hnr, _, _, _, _, hd⟩ := S.medge_norm hm
  obtain ⟨rfl, rfl⟩ : a0' = a0 ∧ b0' = b0 := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact absurd hb0 (fun h => S.disj ha0' h)
    · exact absurd hb0 (fun h => S.disj ha0' h)
    · exact ⟨rfl, rfl⟩
  rcases hd with ⟨_, hall⟩ | ⟨_, hall⟩
  · exact absurd hall hna
  · exact ⟨a0', b0', ha0, hb0, hnr, hall, hna⟩

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (g : ℕ)
    (hbip : ∀ u v : Fin n, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G) (hao : IsAO2 n C)
    (hfn : circuitFun n C = graphFun G ∅) (hlift : IsLiftFixedPoint G C)
    (h5 : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ t ∈ (gateAt C k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
        graphFun G ∅ x = true))
    (h6 : ∀ k < C.gates.length, InOutputCone n C k)
    (h7 : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ v : Fin n, gateVal n C k (PEqualNP.SplitCount.unitInput v) = false)
    (hg : g < C.gates.length) (hgop : (gateAt C g).op = GateOp.and) (hgd : ¬ BelowF G C g)
    (hclean : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ i < D.gates.length, ∀ j < D.gates.length, (gateAt D i).op = GateOp.and →
        (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  obtain ⟨al, be, S⟩ := gs_of_hyps n G C s g hbip h4 hao hfn hlift h5 h6 h7 hg hgop hgd hclean
  by_cases hc1 : ∀ u v, MEdge G C g u v → ∀ a0 b0, ((a0 = u ∧ b0 = v) ∨ (a0 = v ∧ b0 = u)) →
      a0 ∈ supp n C al → b0 ∈ supp n C be → ∀ b' ∈ supp n C be, G.Adj a0 b'
  · exact S.case01 hc1
  by_cases hc2 : ∀ u v, MEdge G C g u v → ∀ a0 b0, ((a0 = u ∧ b0 = v) ∨ (a0 = v ∧ b0 = u)) →
      a0 ∈ supp n C be → b0 ∈ supp n C al → ∀ b' ∈ supp n C al, G.Adj a0 b'
  · exact S.symm.case01 hc2
  obtain ⟨a1, bs, ha1, hbs, hnr1, hB, hna1⟩ := S.not_case01 hc1
  obtain ⟨b2, as, hb2, has, hnr2, hA, hnb2⟩ := S.symm.not_case01 hc2
  have K : K3 G C g al be as bs a1 b2 :=
    K3.intro has hbs ha1 hb2 (fun b' hb' => (hA b' hb').symm) hB hna1
      (fun h => hnb2 (fun b' hb' => (h b' hb').symm)) hnr1 (fun h => hnr2 (rescov_symm h))
  by_cases hd : ∃ j, Drop n C g j
  · obtain ⟨d, hd⟩ := hd
    by_cases hd2 : ∃ d', Drop n C g d' ∧ d' ≠ d
    · obtain ⟨d', hd', hne⟩ := hd2
      exact K.case_two S d d' hd hd' (fun e => hne e.symm)
    · by_cases hgs : ∃ w, n + g < w ∧ w < n + C.gates.length ∧ ¬ BW G C w ∧ ¬ Lin n C w
      · exact K.case_one_gs S d hd hgs
      · refine K.case_one_join S (fun j j' hj hj' => ?_) hgs
        have e1 : j = d := by
          by_contra h
          exact hd2 ⟨j, hj, h⟩
        have e2 : j' = d := by
          by_contra h
          exact hd2 ⟨j', hj', h⟩
        rw [e1, e2]
  · exact K.case_none S hd

end PEqualNP.Outside.L_meta_3700

theorem PEqualNP.Outside.L_meta_3700 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.Core.IsLiftFixedPoint G C →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) →
  (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (PEqualNP.SplitCount.unitInput v) = false) →
  g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size ∧
    PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
    ∀ i < D.gates.length, ∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ¬ PEqualNP.EdgeOwnership.InCone n D i j := by
  intro n G _ C s g hbip h4 hleast hlift h5 h6 h7 hg hgop hgd hclean
  exact PEqualNP.Outside.L_meta_3700.main n G C s g hbip h4 hleast.1 hleast.2.1 hlift h5 h6 h7 hg hgop
    hgd hclean
