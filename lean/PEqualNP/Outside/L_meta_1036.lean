import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1036_aux

open PEqualNP.CircuitLowerBounds

def spec (j : Fin 15) (x : Fin 6 → Bool) : Bool :=
  ![(x 0 || x 1),
    (x 0 || x 2),
    (x 0 || x 3),
    (x 0 || x 4),
    (x 0 || x 5),
    (x 0 || (x 1 && x 2)),
    (x 0 || ((x 1 && x 2) && x 3)),
    (x 0 || (((x 1 && x 2) && x 3) && x 4)),
    (x 0 || ((((x 1 && x 2) && x 3) && x 4) && x 5)),
    (x 0 && x 1),
    (x 0 && (x 1 && x 2)),
    (x 0 && ((x 1 && x 2) && x 3)),
    (x 0 && (((x 1 && x 2) && x 3) && x 4)),
    (x 0 && ((((x 1 && x 2) && x 3) && x 4) && x 5)),
    ((((x 1 && x 2) && x 3) && x 4) && x 5)] j

def oneGates : List Gate :=
  [⟨.or, [0,1]⟩, ⟨.or, [0,2]⟩, ⟨.or, [0,3]⟩, ⟨.or, [0,4]⟩, ⟨.or, [0,5]⟩,
   ⟨.and, [6,7]⟩, ⟨.and, [11,8]⟩, ⟨.and, [12,9]⟩, ⟨.and, [13,10]⟩,
   ⟨.and, [0,1]⟩, ⟨.and, [15,2]⟩, ⟨.and, [16,3]⟩, ⟨.and, [17,4]⟩, ⟨.and, [18,5]⟩,
   ⟨.not, [0]⟩, ⟨.and, [14,20]⟩, ⟨.or, [21,19]⟩]

def oneOut (j : Fin 15) : Nat :=
  if j.val < 14 then j.val + 6 else 22

theorem one_length : oneGates.length = 17 := rfl

theorem mono_and : ∀ {a b c d : Bool}, a ≤ b → c ≤ d → (a && c) ≤ (b && d) := by decide

theorem mono_or : ∀ {a b c d : Bool}, a ≤ b → c ≤ d → (a || c) ≤ (b || d) := by decide

theorem spec_monotone (j : Fin 15) (x y : Fin 6 → Bool) (h : ∀ i, x i ≤ y i) :
    spec j x ≤ spec j y := by
  fin_cases j
  · exact mono_or (h 0) (h 1)
  · exact mono_or (h 0) (h 2)
  · exact mono_or (h 0) (h 3)
  · exact mono_or (h 0) (h 4)
  · exact mono_or (h 0) (h 5)
  · exact mono_or (h 0) (mono_and (h 1) (h 2))
  · exact mono_or (h 0) (mono_and (mono_and (h 1) (h 2)) (h 3))
  · exact mono_or (h 0) (mono_and (mono_and (mono_and (h 1) (h 2)) (h 3)) (h 4))
  · exact mono_or (h 0) (mono_and (mono_and (mono_and (mono_and (h 1) (h 2)) (h 3)) (h 4)) (h 5))
  · exact mono_and (h 0) (h 1)
  · exact mono_and (h 0) (mono_and (h 1) (h 2))
  · exact mono_and (h 0) (mono_and (mono_and (h 1) (h 2)) (h 3))
  · exact mono_and (h 0) (mono_and (mono_and (mono_and (h 1) (h 2)) (h 3)) (h 4))
  · exact mono_and (h 0) (mono_and (mono_and (mono_and (mono_and (h 1) (h 2)) (h 3)) (h 4)) (h 5))
  · exact (mono_and (mono_and (mono_and (mono_and (h 1) (h 2)) (h 3)) (h 4)) (h 5))

theorem one_arity : ∀ g ∈ oneGates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [oneGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem one_location (i : Fin oneGates.length) (h : (oneGates.get i).op = GateOp.not) : i.val = 14 := by
  change Fin 17 at i
  fin_cases i <;> first | rfl | cases h

theorem one_unique (i j : Fin oneGates.length)
    (hi : (oneGates.get i).op = GateOp.not) (hj : (oneGates.get j).op = GateOp.not) : i = j := by
  exact Fin.ext ((one_location i hi).trans (one_location j hj).symm)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem one_eval : ∀ (j : Fin 15) (x : Fin 6 → Bool),
    Circuit.eval ⟨oneGates, oneOut j⟩ (List.ofFn x) = spec j x := by decide +kernel

end PEqualNP.Outside.L_meta_1036_aux

namespace PEqualNP.Outside.L_meta_1036_aux

def pool (zs : List (BitVec 5)) : List (BitVec 5) :=
  [0, 1, 2, 4, 8, 16] ++ zs

def Wf : List (BitVec 5) → Prop
  | [] => True
  | z :: zs => Wf zs ∧ ∃ x ∈ pool zs, ∃ y ∈ pool zs, z = x ||| y

def stepsSafe : Nat → List (BitVec 5) → Bool
  | 0, _ => true
  | k+1, zs => (pool zs).all fun x => (pool zs).all fun y =>
    let z := x ||| y
    (z != -1) && stepsSafe k (z :: zs)

theorem safeStep {k : Nat} {zs : List (BitVec 5)} {x y : BitVec 5}
    (hs : stepsSafe (k+1) zs = true) (hx : x ∈ pool zs) (hy : y ∈ pool zs) :
    (x ||| y ≠ -1) ∧ stepsSafe k ((x ||| y) :: zs) = true := by
  have hh := List.all_eq_true.mp (List.all_eq_true.mp hs x hx) y hy
  simpa using hh

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
theorem safeThree : stepsSafe 3 [] = true := by decide +kernel

theorem noFullThree {z u w v : BitVec 5}
    (hw : Wf [z,u,w]) (hv : v ∈ pool [z,u,w]) : v ≠ -1 := by
  obtain ⟨⟨⟨_, a, ha, b, hb, rfl⟩, c, hc, d, hd, rfl⟩, e, he, f, hf, rfl⟩ := hw
  obtain ⟨h1, s1⟩ := safeStep safeThree ha hb
  obtain ⟨h2, s2⟩ := safeStep s1 hc hd
  obtain ⟨h3, _⟩ := safeStep s2 he hf
  intro eqn
  subst v
  simp [pool] at hv
  rcases hv with h | h | h
  · exact h3 h.symm
  · exact h2 h.symm
  · exact h1 h.symm

theorem padZero {zs : List (BitVec 5)} (hw : Wf zs) : Wf (0 :: zs) :=
  ⟨hw, 0, by simp [pool], 0, by simp [pool], rfl⟩

theorem poolTail {zs : List (BitVec 5)} {t v : BitVec 5} (hv : v ∈ pool zs) :
    v ∈ pool (t :: zs) := by
  rcases List.mem_append.mp hv with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_cons_of_mem t h)

theorem noFull (zs : List (BitVec 5)) (hw : Wf zs) (hlen : zs.length ≤ 3) :
    ∀ v ∈ pool zs, v ≠ -1 := by
  intro v hv
  rcases zs with _ | ⟨w, zs⟩
  · exact noFullThree (padZero (padZero (padZero hw))) (poolTail (poolTail (poolTail hv)))
  rcases zs with _ | ⟨u, zs⟩
  · exact noFullThree (padZero (padZero hw)) (poolTail (poolTail hv))
  rcases zs with _ | ⟨z, zs⟩
  · exact noFullThree (padZero hw) (poolTail hv)
  rcases zs with _ | ⟨t, zs⟩
  · exact noFullThree hw hv
  · simp only [List.length_cons] at hlen
    omega

end PEqualNP.Outside.L_meta_1036_aux

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1036_aux

-- Wire evaluation facts adapted from the project's L_meta_616.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

def positiveInput (k : Fin 6) : Bool := decide (k.val ≠ 0)

def negativeInput (i : Fin 5) (k : Fin 6) : Bool := decide (k.val ≠ i.val + 1)

def Separates (gs : List Gate) (w : ℕ) (i : Fin 5) : Prop :=
  Circuit.eval ⟨gs, w⟩ (List.ofFn positiveInput) = true ∧
    Circuit.eval ⟨gs, w⟩ (List.ofFn (negativeInput i)) = false

lemma wire_input (gs : List Gate) (x : Fin 6 → Bool) (w : ℕ) (hw : w < 6) :
    Circuit.eval ⟨gs, w⟩ (List.ofFn x) = x ⟨w, hw⟩ :=
  wires_input ⟨gs, w⟩ x w hw

lemma wire_oob (gs : List Gate) (x : Fin 6 → Bool) (w : ℕ) (hw : 6 + gs.length ≤ w) :
    Circuit.eval ⟨gs, w⟩ (List.ofFn x) = false :=
  wires_oob ⟨gs, w⟩ x w hw

lemma cover_ports (l : List ℕ) (hl : l.length ≤ 2) (N : ℕ) (hN : 0 < N) :
    ∃ a b : ℕ, a < N ∧ b < N ∧ ∀ j ∈ l, j < N → j = a ∨ j = b := by
  let cap (j : ℕ) := if j < N then j else 0
  have small (j : ℕ) : cap j < N := by simp [cap]; split <;> omega
  cases l with
  | nil => exact ⟨0, 0, hN, hN, by simp⟩
  | cons u rest =>
    cases rest with
    | nil =>
      exact ⟨cap u, 0, small u, hN, by
        intro j hj hjn
        have : j = u := by simpa using hj
        subst j
        exact Or.inl (by simp [cap, hjn])⟩
    | cons v rest =>
      have he : rest = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst rest
      exact ⟨cap u, cap v, small u, small v, by
        intro j hj hjn
        rcases List.mem_cons.mp hj with hu | hv
        · subst j; exact Or.inl (by simp [cap, hjn])
        · have : j = v := by simpa using hv
          subst j
          exact Or.inr (by simp [cap, hjn])⟩

lemma parents (gs : List Gate)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (t : ℕ) (ht : t < gs.length) :
    ∃ a b : ℕ, a < 6 + t ∧ b < 6 + t ∧
      ∀ i, Separates gs (6 + t) i → Separates gs a i ∨ Separates gs b i := by
  classical
  let g := gs[t]
  have hg : g ∈ gs := List.getElem_mem ht
  obtain ⟨hop, hlen⟩ := hmono g hg
  obtain ⟨a, b, ha, hb, hports⟩ := cover_ports g.inputs hlen (6+t) (by omega)
  refine ⟨a, b, ha, hb, ?_⟩
  intro i hsep
  let read (x : Fin 6 → Bool) (w : ℕ) :=
    if w < 6 + t then Circuit.eval ⟨gs, w⟩ (List.ofFn x) else false
  have eqn (x : Fin 6 → Bool) :
      Circuit.eval ⟨gs, 6+t⟩ (List.ofFn x) = g.op.eval (g.inputs.map (read x)) := by
    exact wires_gate_ofFn ⟨gs, 6+t⟩ x t g (by simp [g, ht])
  by_contra! hn
  obtain ⟨hyes, hno⟩ := hsep
  rw [eqn] at hyes hno
  have inc : ∀ j ∈ g.inputs, read positiveInput j = true → read (negativeInput i) j = true := by
    intro j hj hp
    by_cases hjn : j < 6 + t
    · simp only [read, hjn, if_true] at hp ⊢
      by_contra! hf
      have hs : Separates gs j i := ⟨hp, by simpa using hf⟩
      rcases hports j hj hjn with rfl | rfl
      · exact hn.1 hs
      · exact hn.2 hs
    · simp [read, hjn] at hp
  have htrue := gateOp_mono g.op hop g.inputs _ _ inc hyes
  rw [hno] at htrue
  contradiction

end PEqualNP.Outside.L_meta_1036_aux

namespace PEqualNP.Outside.L_meta_1036_aux

open PEqualNP.CircuitLowerBounds

def markedIndex (j : Fin 14) : Fin 15 := ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩

def marked (out : Fin 15 → ℕ) : Finset ℕ :=
  Finset.univ.image fun j : Fin 14 => out (markedIndex j)

def markedSample (r : Fin 12) (i : Fin 6) : Bool :=
  Nat.testBit (![(1 : ℕ), 54, 14, 15, 26, 3, 30, 31, 4, 7, 62, 63] r) i.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma marked_samples_distinct : ∀ j k : Fin 14, j ≠ k →
    ∃ r : Fin 12, spec (markedIndex j) (markedSample r) ≠ spec (markedIndex k) (markedSample r) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma marked_samples_noninput : ∀ (j : Fin 14) (i : Fin 6),
    ∃ r : Fin 12, spec (markedIndex j) (markedSample r) ≠ markedSample r i := by
  decide +kernel

lemma marked_spec_true : ∀ j : Fin 14, spec (markedIndex j) (fun _ => true) = true := by
  decide

lemma marked_spec_no_sep : ∀ (j : Fin 14) (i : Fin 5),
    ¬ (spec (markedIndex j) positiveInput = true ∧
      spec (markedIndex j) (negativeInput i) = false) := by
  decide

lemma marked_card (gs : List Gate) (out : Fin 15 → ℕ)
    (he : ∀ (j : Fin 15) (x : Fin 6 → Bool), Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = spec j x) :
    (marked out).card = 14 := by
  have hinj : Function.Injective (fun j : Fin 14 => out (markedIndex j)) := by
    intro j k h
    change out (markedIndex j) = out (markedIndex k) at h
    by_contra hne
    obtain ⟨r, hr⟩ := marked_samples_distinct j k hne
    apply hr
    rw [← he (markedIndex j), ← he (markedIndex k)]
    rw [h]
  rw [marked, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

lemma marked_between (gs : List Gate) (out : Fin 15 → ℕ)
    (he : ∀ (j : Fin 15) (x : Fin 6 → Bool), Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = spec j x) :
    ∀ w ∈ marked out, 6 ≤ w ∧ w < 6 + gs.length := by
  intro w hw
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
  constructor
  · by_contra! h
    obtain ⟨r, hr⟩ := marked_samples_noninput j ⟨_, h⟩
    exact hr ((he _ _).symm.trans (wire_input gs _ _ h))
  · by_contra! h
    have hf : spec (markedIndex j) (fun _ => true) = false :=
      (he (markedIndex j) _).symm.trans (wire_oob gs (fun _ => true) _ h)
    exact Bool.noConfusion ((marked_spec_true j).symm.trans hf)

lemma marked_empty (gs : List Gate) (out : Fin 15 → ℕ)
    (he : ∀ (j : Fin 15) (x : Fin 6 → Bool), Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = spec j x) :
    ∀ w ∈ marked out, ∀ i, ¬ Separates gs w i := by
  intro w hw i hs
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
  exact marked_spec_no_sep j i
    ⟨(he _ _).symm.trans hs.1, (he _ _).symm.trans hs.2⟩

end PEqualNP.Outside.L_meta_1036_aux

namespace PEqualNP.Outside.L_meta_1036_aux

def freshWires (K : Finset Nat) (t : Nat) := Finset.Ico 6 (6+t) \ K

theorem freshMarked (K : Finset Nat) (t : Nat) (hk : 6+t ∈ K) :
    freshWires K (t+1) = freshWires K t := by
  unfold freshWires
  rw [← Nat.add_assoc, Nat.Ico_succ_right_eq_insert_Ico (by omega), Finset.insert_sdiff_of_mem _ hk]

theorem freshNew (K : Finset Nat) (t : Nat) (hk : 6+t ∉ K) :
    (freshWires K (t+1)).card = (freshWires K t).card + 1 := by
  unfold freshWires
  rw [← Nat.add_assoc, Nat.Ico_succ_right_eq_insert_Ico (by omega), Finset.insert_sdiff_of_notMem _ hk,
    Finset.card_insert_of_notMem]
  simp

theorem historyCover (N : Nat) (K : Finset Nat) (sep : Nat → Fin 5 → Prop)
    (input : ∀ w < 6, ∃ v ∈ pool [], ∀ i, sep w i → v.getLsbD i = true)
    (blocked : ∀ w ∈ K, ∀ i, ¬sep w i)
    (parent : ∀ t < N, ∃ a b : Nat, a < 6+t ∧ b < 6+t ∧
       ∀ i, sep (6+t) i → sep a i ∨ sep b i)
    (t : Nat) (ht : t ≤ N) :
    ∃ zs : List (BitVec 5), Wf zs ∧ zs.length = (freshWires K t).card ∧
      ∀ w < 6+t, ∃ v ∈ pool zs, ∀ i, sep w i → v.getLsbD i = true := by
  induction t with
  | zero =>
    exact ⟨[], trivial, by simp [freshWires], by simpa using input⟩
  | succ t ih =>
    obtain ⟨zs, hwf, hlen, cover⟩ := ih (by omega)
    by_cases hm : 6+t ∈ K
    · refine ⟨zs, hwf, ?_, ?_⟩
      · rw [freshMarked K t hm]; exact hlen
      · intro w hw
        by_cases h : w = 6+t
        · subst w
          exact ⟨0, by simp [pool], fun i hi => (blocked _ hm i hi).elim⟩
        · exact cover w (by omega)
    · obtain ⟨a,b,ha,hb,hp⟩ := parent t (by omega)
      obtain ⟨x,hx,hxs⟩ := cover a ha
      obtain ⟨y,hy,hys⟩ := cover b hb
      refine ⟨(x ||| y) :: zs, ⟨hwf, x, hx, y, hy, rfl⟩, ?_, ?_⟩
      · rw [freshNew K t hm]; simp [hlen]
      · intro w hw
        by_cases h : w = 6+t
        · subst w
          refine ⟨x ||| y, by simp [pool], ?_⟩
          intro i hi
          rcases hp i hi with hs | hs
          · simp [hxs i hs]
          · simp [hys i hs]
        · obtain ⟨v,hv,hs⟩ := cover w (by omega)
          refine ⟨v, ?_, hs⟩
          simpa [pool, List.mem_append, or_assoc, or_left_comm, or_comm] using
            (show v ∈ pool zs ∨ v = x ||| y from Or.inl hv)

theorem abstractBound (N : Nat) (K : Finset Nat) (sep : Nat → Fin 5 → Prop)
    (input : ∀ w < 6, ∃ v ∈ pool [], ∀ i, sep w i → v.getLsbD i = true)
    (blocked : ∀ w ∈ K, ∀ i, ¬sep w i)
    (parent : ∀ t < N, ∃ a b : Nat, a < 6+t ∧ b < 6+t ∧
       ∀ i, sep (6+t) i → sep a i ∨ sep b i)
    (kcard : K.card = 14) (ksub : K ⊆ Finset.Ico 6 (6+N))
    (last : Nat) (hlast : last < 6+N) (hall : ∀ i, sep last i) :
    17 < N := by
  by_contra! hn
  obtain ⟨zs, hwf, hlen, cover⟩ := historyCover N K sep input blocked parent N (by omega)
  obtain ⟨v,hv,hbits⟩ := cover last hlast
  have hl : zs.length ≤ 3 := by
    rw [hlen, freshWires, Finset.card_sdiff_of_subset ksub, Nat.card_Ico, kcard]
    omega
  apply noFull zs hwf hl v hv
  have ones : ∀ q : BitVec 5, (∀ i : Fin 5, q.getLsbD i = true) → q = -1 := by decide
  exact ones v (fun i => hbits i (hall i))

end PEqualNP.Outside.L_meta_1036_aux

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1036_aux

theorem input_masks (gs : List Gate) (w : Nat) (hw : w < 6) :
    ∃ v ∈ pool [], ∀ i, Separates gs w i → v.getLsbD i = true := by
  have data : ∀ j : Fin 6, ∃ v ∈ pool [], ∀ i : Fin 5,
      positiveInput j = true ∧ negativeInput i j = false → v.getLsbD i = true := by decide
  obtain ⟨v, hv, h⟩ := data ⟨w,hw⟩
  exact ⟨v, hv, fun i hs => h i ⟨(wire_input gs _ w hw).symm.trans hs.1,
    (wire_input gs _ w hw).symm.trans hs.2⟩⟩

theorem seventeen_lt (gs : List Gate) (out : Fin 15 → Nat)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (he : ∀ (j : Fin 15) (x : Fin 6 → Bool), Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = spec j x) :
    17 < gs.length := by
  have hall : ∀ i : Fin 5, Separates gs (out 14) i := by
    intro i
    constructor
    · rw [he]; decide
    · rw [he]; exact (by decide : ∀ j : Fin 5, spec 14 (negativeInput j) = false) i
  have hl : out 14 < 6+gs.length := by
    by_contra! h
    have heq := (hall 0).1
    rw [wire_oob gs positiveInput (out 14) h] at heq
    contradiction
  exact abstractBound gs.length (marked out) (Separates gs) (input_masks gs)
    (marked_empty gs out he) (parents gs hm)
    (marked_card gs out he) (fun w hw => Finset.mem_Ico.mpr (marked_between gs out he w hw))
    (out 14) hl hall

end PEqualNP.Outside.L_meta_1036_aux

open PEqualNP.Outside.L_meta_1036_aux

theorem PEqualNP.Outside.L_meta_1036 : ∃ (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool), n ≤ 7 ∧ (∀ (j : Fin m) (x y : Fin n → Bool), (∀ i : Fin n, x i ≤ y i) → f j x ≤ f j y) ∧ ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out j⟩ (List.ofFn x) = f j x) ∧ ∀ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' j⟩ (List.ofFn x) = f j x) → gates.length < gates'.length := by
  refine ⟨6, 15, spec, by decide, spec_monotone, oneGates, oneOut, one_arity, one_unique, one_eval, ?_⟩
  intro gs out hm he
  rw [one_length]
  exact seventeen_lt gs out hm he
