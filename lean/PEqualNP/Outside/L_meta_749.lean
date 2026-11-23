import Mathlib
import PEqualNP.Defs

/-!
-- L-meta-749: on a set of inputs `X` with a least element `y`, replacing every NOT gate by the
-- constant value it takes at `y` changes no wire on `X`.
--/

namespace PEqualNP.Outside.L_meta_749

open PEqualNP.CircuitLowerBounds

-- AND of a list of bits.
theorem eval_and_eq (l : List Bool) : GateOp.and.eval l = l.all id := rfl

-- OR of a list of bits.
theorem eval_or_eq (l : List Bool) : GateOp.or.eval l = l.any id := rfl

-- NOT is the negation of the first bit it reads.
theorem eval_not_eq (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl

-- The value a gate writes on a wire list.
def val (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

-- The value a gate reads on a wire list.
def rdW (g : Gate) (w : List Bool) : Bool :=
  (g.inputs.map fun i => w.getD i false).headD false

-- One gate step of the wire list.
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [val g w]

-- The wire list after a list of gates.
def wireL (G : List Gate) (z : List Bool) : List Bool :=
  Circuit.wires ⟨G, 0⟩ z

-- The wire list is the fold of the steps.
theorem wireL_foldl (G : List Gate) (z : List Bool) :
    wireL G z = G.foldl stp z := rfl

-- A NOT gate writes the negation of what it reads.
theorem val_not (g : Gate) (h : g.op = GateOp.not) (w : List Bool) :
    val g w = !(rdW g w) := by
  rw [val, rdW, h, eval_not_eq]

-- Reading a gate whose input list starts with a wire.
theorem rdW_eq_head (g : Gate) (a : ℕ) (t : List ℕ) (w : List Bool)
    (h : g.inputs = a :: t) : rdW g w = w.getD a false := by
  rw [rdW, h]
  rfl

-- A constant OR gate is the constant false.
theorem val_or_nil (w : List Bool) : val (⟨GateOp.or, []⟩ : Gate) w = false := by
  rw [val, eval_or_eq]
  rfl

-- A constant AND gate is the constant true.
theorem val_and_nil (w : List Bool) : val (⟨GateOp.and, []⟩ : Gate) w = true := by
  rw [val, eval_and_eq]
  rfl

-- One step adds exactly one wire.
theorem stp_length (w : List Bool) (g : Gate) : (stp w g).length = w.length + 1 := by
  simp [stp]

-- The length of a wire list.
theorem wireL_length (G : List Gate) (z : List Bool) :
    (wireL G z).length = z.length + G.length := by
  induction G generalizing z with
  | nil => simp [wireL, Circuit.wires]
  | cons g G ih =>
    have hstep : wireL (g :: G) z = wireL G (stp z g) := rfl
    rw [hstep, ih (stp z g), stp_length, List.length_cons]
    omega

-- One step keeps the earlier wires.
theorem stp_getD_lt (w : List Bool) (g : Gate) {i : ℕ} (h : i < w.length) :
    (stp w g).getD i false = w.getD i false := by
  rw [stp, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

-- The new wire of one step.
theorem stp_getD_self (w : List Bool) (g : Gate) :
    (stp w g).getD w.length false = val g w := by
  rw [stp, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
  rfl

-- A fold of one more gate is one more step.
theorem foldl_cons' (g : Gate) (G : List Gate) (z : List Bool) :
    (g :: G).foldl stp z = G.foldl stp (stp z g) := rfl

-- A prefix of one more gate is one more step, for wire lists.
theorem wireL_take_succ (G : List Gate) (z : List Bool) (j : ℕ) (g : Gate)
    (hj : G[j]? = some g) :
    wireL (G.take (j + 1)) z = stp (wireL (G.take j) z) g := by
  unfold wireL Circuit.wires
  rw [List.take_add_one, hj, List.foldl_append]
  rfl

-- Pointwise true maps to pointwise true.
theorem headD_map_imp {α : Type} (l : List α) (f f' : α → Bool)
    (h : ∀ a ∈ l, f a = true → f' a = true) :
    (l.map f).headD false = true → (l.map f').headD false = true := by
  cases l with
  | nil => intro h0; simp at h0
  | cons a t => intro h0; simpa using h a (by simp) (by simpa using h0)

-- A true head of a mapped list comes from a true value at a member.
theorem headD_map_split {α : Type} (l : List α) (f : α → Bool)
    (h : (l.map f).headD false = true) :
    ∃ a t, l = a :: t ∧ f a = true := by
  cases l with
  | nil => simp at h
  | cons a t => exact ⟨a, t, rfl, by simpa using h⟩

-- Reading is monotone in the wire list.
theorem rdW_mono {g : Gate} {w w' : List Bool}
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    rdW g w = true → rdW g w' = true := by
  intro h0
  exact headD_map_imp g.inputs _ _ (fun a _ => h a) h0

-- One AND or OR step preserves pointwise truth.
theorem stp_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    {v v' : List Bool} (hlen : v.length = v'.length)
    (hv : ∀ (i : ℕ), v.getD i false = true → v'.getD i false = true) :
    ∀ (i : ℕ), (stp v g).getD i false = true → (stp v' g).getD i false = true := by
  intro i hi
  by_cases hlt : i < v.length
  · have hlt' : i < v'.length := by omega
    rw [stp_getD_lt v g hlt] at hi
    rw [stp_getD_lt v' g hlt']
    exact hv i hi
  · have hge : v.length ≤ i := by omega
    have hieq : i = v.length := by
      by_contra hne
      have h0 : i - v.length ≠ 0 := by omega
      have h1 : (stp v g).getD i false = false := by
        rw [stp, List.getD_eq_getElem?_getD, List.getElem?_append_right hge,
          List.getElem?_singleton]
        simp [h0]
      rw [h1] at hi
      exact Bool.false_ne_true hi
    subst hieq
    rw [stp_getD_self v g] at hi
    rw [hlen, stp_getD_self v' g]
    rcases hg with h | h
    · rw [val, h, eval_and_eq] at hi ⊢
      rw [List.all_eq_true] at hi ⊢
      intro b hb
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
      exact hv k (hi _ (List.mem_map_of_mem hk))
    · rw [val, h, eval_or_eq] at hi ⊢
      rw [List.any_eq_true] at hi ⊢
      obtain ⟨b, hb, hbv⟩ := hi
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map_of_mem hk, hv k hbv⟩

-- A monotone circuit is monotone on its wires.
theorem foldl_mono (G : List Gate) (hG : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or)
    {v v' : List Bool} (hlen : v.length = v'.length)
    (hv : ∀ (i : ℕ), v.getD i false = true → v'.getD i false = true) :
    ∀ (i : ℕ), (G.foldl stp v).getD i false = true → (G.foldl stp v').getD i false = true := by
  induction G generalizing v v' with
  | nil => intro i hi; exact hv i hi
  | cons g G ih =>
    intro i hi
    rw [foldl_cons'] at hi ⊢
    have hvlen : (stp v g).length = (stp v' g).length := by
      rw [stp_length, stp_length, hlen]
    have hv' : ∀ (i : ℕ), (stp v g).getD i false = true → (stp v' g).getD i false = true :=
      stp_mono g (hG g List.mem_cons_self) hlen hv
    exact ih (fun q hq => hG q (List.mem_cons_of_mem g hq)) hvlen hv' i hi

-- The input list of the least element is pointwise below that of any element of the set.
theorem ofFn_mono {n : ℕ} {X : Set (Fin n → Bool)} {y : Fin n → Bool}
    (hleast : ∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true)
    {z : Fin n → Bool} (hz : z ∈ X) (i : ℕ) :
    (List.ofFn y).getD i false = true → (List.ofFn z).getD i false = true := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    List.getElem?_ofFn]
  split_ifs with hi
  · simp only [Option.getD_some]
    exact hleast z hz ⟨i, hi⟩
  · simp

-- The two input lists of length `n` have one length.
theorem ofFn_length_eq {n : ℕ} (y z : Fin n → Bool) :
    (List.ofFn y).length = (List.ofFn z).length := by
  simp [List.length_ofFn]

end PEqualNP.Outside.L_meta_749

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_749

theorem PEqualNP.Outside.L_meta_749 :
    ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate)
      (X : Set (Fin n → Bool)) (y : Fin n → Bool),
      (∀ g ∈ C,
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
      y ∈ X →
      (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) →
      (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate),
        C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not →
        ((g1.inputs.map (fun i1 =>
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩
            (List.ofFn y)).getD i1 false)).headD false) = false →
        ∀ z ∈ X,
        ((g1.inputs.map (fun i2 =>
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩
            (List.ofFn z)).getD i2 false)).headD false) = false) →
      C'.length = C.length →
      (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate),
        C[j2]? = some g2 →
        (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not →
          (((g2.inputs.map (fun i3 =>
            (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩
              (List.ofFn y)).getD i3 false)).headD false) = true →
            C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧
          (((g2.inputs.map (fun i4 =>
            (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩
              (List.ofFn y)).getD i4 false)).headD false) = false →
            C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧
        (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) →
      ∀ x ∈ X, ∀ w : ℕ,
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩
          (List.ofFn x)).getD w false =
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩
          (List.ofFn x)).getD w false := by
  intro n C C' X y hC hyX hleast hnotfalse hlen hC'
  -- A NOT gate of the original list is replaced by the constant gate it evaluates to at `y`.
  have hgate : ∀ (j : ℕ) (g : Gate), C[j]? = some g → g.op = GateOp.not →
      ((rdW g (wireL (C.take j) (List.ofFn y)) = true →
          C'[j]? = some (⟨GateOp.or, []⟩ : Gate)) ∧
        (rdW g (wireL (C.take j) (List.ofFn y)) = false →
          C'[j]? = some (⟨GateOp.and, []⟩ : Gate))) := by
    intro j g hj hnot
    have h := (hC' j g hj).1 hnot
    constructor
    · intro htrue
      have := h.1 htrue
      rwa [show ({ op := GateOp.or, inputs := [] } : Gate) = (⟨GateOp.or, []⟩ : Gate) from rfl]
    · intro hfalse
      have := h.2 hfalse
      rwa [show ({ op := GateOp.and, inputs := [] } : Gate) = (⟨GateOp.and, []⟩ : Gate) from rfl]
  have hgate' : ∀ (j : ℕ) (g : Gate), C[j]? = some g → g.op ≠ GateOp.not →
      C'[j]? = some g := by
    intro j g hj
    exact (hC' j g hj).2
  -- Every gate of the replaced list is an AND or OR gate.
  have handOr : ∀ (j : ℕ) (g : Gate), C'[j]? = some g →
      g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro j g hj'
    have hjC' : j < C'.length := (List.getElem?_eq_some_iff.mp hj').1
    have hjC : j < C.length := by omega
    have hget : C[j]? = some C[j] := List.getElem?_eq_getElem hjC
    have hgin := (hC C[j] (List.getElem_mem hjC)).1
    have hself : C'[j]? = some C'[j] := List.getElem?_eq_getElem hjC'
    rw [hself] at hj'
    rw [(Option.some.inj hj').symm]
    by_cases hnot : C[j].op = GateOp.not
    · rcases Bool.eq_false_or_eq_true (rdW C[j] (wireL (C.take j) (List.ofFn y))) with h | h
      · have hh := (hgate j C[j] hget hnot).1 h
        rw [hself] at hh
        rw [Option.some.inj hh]
        exact Or.inr rfl
      · have hh := (hgate j C[j] hget hnot).2 h
        rw [hself] at hh
        rw [Option.some.inj hh]
        exact Or.inl rfl
    · have hh := hgate' j C[j] hget hnot
      rw [hself] at hh
      rw [Option.some.inj hh]
      rcases hgin with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd h1 hnot
  -- The prefixes of the two wire lists agree on the set.
  have hpref : ∀ (j : ℕ), j ≤ C.length → ∀ x ∈ X,
      wireL (C'.take j) (List.ofFn x) = wireL (C.take j) (List.ofFn x) := by
    intro j
    induction j with
    | zero => intro _ x _; rfl
    | succ j ih =>
      intro hj1 x hx
      have hj : j < C.length := by omega
      have hjC' : j < C'.length := by omega
      have hget : C[j]? = some C[j] := List.getElem?_eq_getElem hj
      have hself : C'[j]? = some C'[j] := List.getElem?_eq_getElem hjC'
      have hIHx : wireL (C'.take j) (List.ofFn x) = wireL (C.take j) (List.ofFn x) :=
        ih (by omega) x hx
      have hIHy : wireL (C'.take j) (List.ofFn y) = wireL (C.take j) (List.ofFn y) :=
        ih (by omega) y hyX
      have hmono : ∀ g ∈ C'.take j, g.op = GateOp.and ∨ g.op = GateOp.or := by
        intro g hg
        obtain ⟨k, hk, hgv⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_take hg)
        exact handOr k g (by rw [← hgv, List.getElem?_eq_getElem hk])
      have hval : val C'[j] (wireL (C.take j) (List.ofFn x)) =
          val C[j] (wireL (C.take j) (List.ofFn x)) := by
        by_cases hnot : C[j].op = GateOp.not
        · -- the gate is a NOT gate, replaced by a constant
          rcases Bool.eq_false_or_eq_true (rdW C[j] (wireL (C.take j) (List.ofFn y))) with hY | hY
          · -- it reads true at the least element, so it becomes the constant false
            have hh := (hgate j C[j] hget hnot).1 hY
            rw [hself] at hh
            rw [Option.some.inj hh, val_or_nil, val_not C[j] hnot]
            obtain ⟨a, t, hins, hfa⟩ := headD_map_split C[j].inputs
              (fun i => (wireL (C.take j) (List.ofFn y)).getD i false) hY
            have hYa : (wireL (C'.take j) (List.ofFn y)).getD a false = true := by
              rw [hIHy]; exact hfa
            have hlen' : (List.ofFn y).length = (List.ofFn x).length := ofFn_length_eq y x
            have hxa : (wireL (C'.take j) (List.ofFn x)).getD a false = true :=
              foldl_mono (C'.take j) hmono hlen' (ofFn_mono hleast hx) a hYa
            have hxread : rdW C[j] (wireL (C.take j) (List.ofFn x)) = true := by
              rw [rdW_eq_head C[j] a t _ hins, ← hIHx]
              exact hxa
            rw [hxread]
            rfl
          · -- it reads false at the least element, so it becomes the constant true
            have hh := (hgate j C[j] hget hnot).2 hY
            rw [hself] at hh
            rw [Option.some.inj hh, val_and_nil, val_not C[j] hnot]
            have hxread : rdW C[j] (wireL (C.take j) (List.ofFn x)) = false :=
              hnotfalse j C[j] hget hnot hY x hx
            rw [hxread]
            rfl
        · -- the gate is not a NOT gate, so the two gates are equal outright
          have hh := hgate' j C[j] hget hnot
          rw [hself] at hh
          rw [Option.some.inj hh]
      rw [wireL_take_succ C' _ j C'[j] (List.getElem?_eq_getElem hjC'),
        wireL_take_succ C _ j C[j] hget, hIHx]
      rw [stp, stp, hval]
  intro x hx w
  have hfin := hpref C.length le_rfl x hx
  have ht1 : C'.take C.length = C' := by
    rw [← hlen]
    exact List.take_length
  have ht2 : C.take C.length = C := List.take_length
  rw [ht1, ht2] at hfin
  exact congrArg (fun l => l.getD w false) hfin
