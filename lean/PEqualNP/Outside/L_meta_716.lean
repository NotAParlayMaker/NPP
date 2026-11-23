import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_716

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One gate evaluated on a wire list: the step of the fold inside Circuit.wires.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h
  simp

lemma length_fold (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

-- The renaming of wires: input wire w < n goes to the input wire pi w, gate wire w to w - n + m.
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

-- A circuit for h on n inputs: either h is constantly false, or there is a circuit on n + 1
-- inputs (the last one ignored) of the same size whose output wire exists.
lemma lift (n s : ℕ) (h : (Fin n → Bool) → Bool) (hc : HasCircuitSize n h s) :
    (∀ y : Fin n → Bool, h y = false) ∨
    ∃ C : Circuit, FanInTwo C ∧ C.gates.length ≤ s ∧ C.output < n + 1 + C.gates.length ∧
      ∀ x : Fin (n + 1) → Bool,
        (C.gates.foldl step (List.ofFn x)).getD C.output false = h (fun i : Fin n => x i.castSucc) := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  by_cases ho : C.output < n + C.gates.length
  · right
    refine ⟨relabel n (n + 1) Fin.castSucc C, ?_, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
    · simpa [relabel, Circuit.size] using hsz
    · simp only [relabel, List.length_map]
      unfold wmap
      split
      · simp
        omega
      · omega
    · intro x
      show _ = h (x ∘ Fin.castSucc)
      rw [← hev (x ∘ Fin.castSucc)]
      exact (rel_fold n (n + 1) Fin.castSucc C.gates _ _ (rel_init n (n + 1) Fin.castSucc x)).2.2
        C.output
  · left
    intro y
    rw [← hev y]
    unfold Circuit.eval
    rw [wires_eq]
    apply List.getD_eq_default
    rw [length_fold]
    simp only [List.length_ofFn]
    omega

-- OR, AND, NOT, AND above the wires k and o computes their exclusive or.
lemma gad_xor (W : List Bool) (k o : ℕ) (hk : k < W.length) (ho : o < W.length) :
    (([⟨GateOp.or, [k, o]⟩, ⟨GateOp.and, [k, o]⟩, ⟨GateOp.not, [W.length + 1]⟩,
      ⟨GateOp.and, [W.length, W.length + 2]⟩] : List Gate).foldl step W).getD (W.length + 3) false
      = xor (W.getD k false) (W.getD o false) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < W.length → (W ++ t)[i]?.getD false = W[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [step, GateOp.eval, A _ _ hk, A _ _ ho]
  cases W[k]?.getD false <;> cases W[o]?.getD false <;> rfl

-- AND, OR, NOT, OR above the wires k and o computes the negation of their exclusive or.
lemma gad_xnor (W : List Bool) (k o : ℕ) (hk : k < W.length) (ho : o < W.length) :
    (([⟨GateOp.and, [k, o]⟩, ⟨GateOp.or, [k, o]⟩, ⟨GateOp.not, [W.length + 1]⟩,
      ⟨GateOp.or, [W.length, W.length + 2]⟩] : List Gate).foldl step W).getD (W.length + 3) false
      = !(xor (W.getD k false) (W.getD o false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < W.length → (W ++ t)[i]?.getD false = W[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [step, GateOp.eval, A _ _ hk, A _ _ ho]
  cases W[k]?.getD false <;> cases W[o]?.getD false <;> rfl

lemma input_last (n : ℕ) (gs : List Gate) (x : Fin (n + 1) → Bool) :
    (gs.foldl step (List.ofFn x)).getD n false = x (Fin.last n) := by
  have hp : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ i (by simp [step]; omega)]
      simp only [step]
      rw [List.getD_append _ _ _ _ hi]
  rw [hp gs _ n (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  rfl

-- Four gates on top of a lifted circuit, with the gadget of the given operations.
lemma build (n s : ℕ) (C : Circuit) (ok : FanInTwo C) (hsz : C.gates.length ≤ s)
    (ho : C.output < n + 1 + C.gates.length) (o1 o2 : GateOp)
    (h1 : o1 = GateOp.and ∨ o1 = GateOp.or) (h2 : o2 = GateOp.and ∨ o2 = GateOp.or) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ s + 4 ∧ ∀ x : Fin (n + 1) → Bool,
      D.eval (List.ofFn x) = ((([⟨o1, [n, C.output]⟩, ⟨o2, [n, C.output]⟩,
        ⟨GateOp.not, [n + 1 + C.gates.length + 1]⟩,
        ⟨o2, [n + 1 + C.gates.length, n + 1 + C.gates.length + 2]⟩] : List Gate).foldl step
          (C.gates.foldl step (List.ofFn x))).getD (n + 1 + C.gates.length + 3) false) := by
  refine ⟨⟨C.gates ++ [⟨o1, [n, C.output]⟩, ⟨o2, [n, C.output]⟩,
      ⟨GateOp.not, [n + 1 + C.gates.length + 1]⟩,
      ⟨o2, [n + 1 + C.gates.length, n + 1 + C.gates.length + 2]⟩],
      n + 1 + C.gates.length + 3⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl | rfl | rfl
    · exact ok g hg
    · rcases h1 with h | h <;> simp [h]
    · rcases h2 with h | h <;> simp [h]
    · simp
    · rcases h2 with h | h <;> simp [h]
  · simp [Circuit.size]
    omega
  · intro x
    unfold Circuit.eval
    rw [wires_eq, List.foldl_append]

end PEqualNP.Outside.L_meta_716

theorem PEqualNP.Outside.L_meta_716 : ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool), (PEqualNP.MetaComplexity.HasCircuitSize n g s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) := by
  intro n s g
  constructor
  · intro hc
    rcases PEqualNP.Outside.L_meta_716.lift n s g hc with hF | ⟨C, ok, hsz, ho, hev⟩
    · refine ⟨⟨[], n⟩, ?_, ?_, ?_⟩
      · intro g' hg'
        simp at hg'
      · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
      · intro x
        have e := PEqualNP.Outside.L_meta_716.input_last n [] x
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval
        rw [PEqualNP.Outside.L_meta_716.wires_eq]
        beta_reduce
        rw [e, hF]
        cases x (Fin.last n) <;> rfl
    · obtain ⟨D, hD, hDs, hDe⟩ := PEqualNP.Outside.L_meta_716.build n s C ok hsz ho
        PEqualNP.CircuitLowerBounds.GateOp.or PEqualNP.CircuitLowerBounds.GateOp.and
        (Or.inr rfl) (Or.inl rfl)
      refine ⟨D, hD, hDs, ?_⟩
      intro x
      have hl : (C.gates.foldl PEqualNP.Outside.L_meta_716.step (List.ofFn x)).length
          = n + 1 + C.gates.length := by
        rw [PEqualNP.Outside.L_meta_716.length_fold]
        simp
      have key := PEqualNP.Outside.L_meta_716.gad_xor
        (C.gates.foldl PEqualNP.Outside.L_meta_716.step (List.ofFn x)) n C.output
        (by rw [hl]; omega) (by rw [hl]; exact ho)
      rw [hl] at key
      rw [hDe x, key, hev x, PEqualNP.Outside.L_meta_716.input_last]
  · intro hc
    rcases PEqualNP.Outside.L_meta_716.lift n s _ hc with hF | ⟨C, ok, hsz, ho, hev⟩
    · refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [n]⟩], n + 1⟩, ?_, ?_, ?_⟩
      · intro g' hg'
        simp at hg'
        subst hg'
        simp
      · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
      · intro x
        have hg1 : g (fun i : Fin n => x i.castSucc) = true := by
          have := hF (fun i : Fin n => x i.castSucc)
          simpa using this
        have e : (List.ofFn x).getD n false = x (Fin.last n) :=
          PEqualNP.Outside.L_meta_716.input_last n [] x
        show ((List.ofFn x) ++ [PEqualNP.CircuitLowerBounds.GateOp.eval
          PEqualNP.CircuitLowerBounds.GateOp.not
          ([n].map fun i => (List.ofFn x).getD i false)]).getD (n + 1) false
          = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))
        rw [PEqualNP.Outside.L_meta_716.getD_snoc_len _ _ _ _ (by simp), hg1]
        show (!((List.ofFn x).getD n false)) = xor (x (Fin.last n)) true
        rw [e]
        cases x (Fin.last n) <;> rfl
    · obtain ⟨D, hD, hDs, hDe⟩ := PEqualNP.Outside.L_meta_716.build n s C ok hsz ho
        PEqualNP.CircuitLowerBounds.GateOp.and PEqualNP.CircuitLowerBounds.GateOp.or
        (Or.inl rfl) (Or.inr rfl)
      refine ⟨D, hD, hDs, ?_⟩
      intro x
      have hl : (C.gates.foldl PEqualNP.Outside.L_meta_716.step (List.ofFn x)).length
          = n + 1 + C.gates.length := by
        rw [PEqualNP.Outside.L_meta_716.length_fold]
        simp
      have key := PEqualNP.Outside.L_meta_716.gad_xnor
        (C.gates.foldl PEqualNP.Outside.L_meta_716.step (List.ofFn x)) n C.output
        (by rw [hl]; omega) (by rw [hl]; exact ho)
      rw [hl] at key
      rw [hDe x, key, hev x, PEqualNP.Outside.L_meta_716.input_last]
      beta_reduce
      cases x (Fin.last n) <;> cases g (fun i : Fin n => x i.castSucc) <;> rfl
