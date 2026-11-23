import Mathlib
import PEqualNP.Defs

-- Wire and relabelling helpers adapted from the project's Shannon and PermInputs
-- modules under Apache-2.0; moved into this proof's own namespace.
namespace PEqualNP.Outside.L_meta_716
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]


theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

/-- A gate with its wires renamed. -/
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

/-- A circuit with its wires renamed. -/
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

/-- One gate evaluated on a wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The invariant: the wire lists match along the renaming. -/
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
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

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
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

/-- Renaming inputs along any map keeps the circuit size. -/
theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem output_lt_of_nonconstant {n : ℕ} {f : (Fin n → Bool) → Bool}
    (C : Circuit) (ev : ∀ x, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) : C.output < n + C.gates.length := by
  by_contra h
  have hz : ∀ x : Fin n → Bool, f x = false := by
    intro x
    rw [← ev x, Circuit.eval, wires_eq]
    exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simpa using Nat.le_of_not_gt h)
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy ((hz x).trans (hz y).symm)

def xorGates (m i j : ℕ) : List Gate :=
  [⟨GateOp.or, [i,j]⟩, ⟨GateOp.and, [i,j]⟩,
   ⟨GateOp.not, [m+1]⟩, ⟨GateOp.and, [m,m+2]⟩]

def xnorGates (m i j : ℕ) : List Gate :=
  [⟨GateOp.and, [i,j]⟩, ⟨GateOp.or, [i,j]⟩,
   ⟨GateOp.not, [m+1]⟩, ⟨GateOp.or, [m,m+2]⟩]

theorem xorStep' (v : List Bool) (i j : ℕ) (hi : i < v.length) (hj : j < v.length) :
    (wiresFrom (xorGates v.length i j) v).getD (v.length+3) false
      = xor (v.getD i false) (v.getD j false) := by
  have A : ∀ (t : List Bool) (a : ℕ), a < v.length →
      (v ++ t)[a]?.getD false = v[a]?.getD false := by
    intro t a h; rw [List.getElem?_append_left h]
  simp [xorGates, wiresFrom, GateOp.eval, A _ _ hi, A _ _ hj]
  cases v[i]?.getD false <;> cases v[j]?.getD false <;> rfl

theorem xnorStep' (v : List Bool) (i j : ℕ) (hi : i < v.length) (hj : j < v.length) :
    (wiresFrom (xnorGates v.length i j) v).getD (v.length+3) false
      = xor (v.getD i false) (!(v.getD j false)) := by
  have A : ∀ (t : List Bool) (a : ℕ), a < v.length →
      (v ++ t)[a]?.getD false = v[a]?.getD false := by
    intro t a h; rw [List.getElem?_append_left h]
  simp [xnorGates, wiresFrom, GateOp.eval, A _ _ hi, A _ _ hj]
  cases v[i]?.getD false <;> cases v[j]?.getD false <;> rfl

theorem xor_upper {n s : ℕ} {f : (Fin n → Bool) → Bool}
    (h : HasCircuitSize n f s) (hnc : ∃ x y, f x ≠ f y) (i : Fin n) :
    HasCircuitSize n (fun x => xor (x i) (f x)) (s+4) := by
  obtain ⟨C, ok, hs, ev⟩ := h
  have ho := output_lt_of_nonconstant C ev hnc
  let m := n+C.gates.length
  refine ⟨⟨C.gates ++ xorGates m i C.output, m+3⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact ok g hg
    · simp only [xorGates, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp
  · simpa [Circuit.size, xorGates] using Nat.add_le_add_right hs 4
  · intro x
    change (wiresFrom (C.gates ++ xorGates m i C.output) (List.ofFn x)).getD (m+3) false = _
    rw [wiresFrom_append]
    have hl : (wiresFrom C.gates (List.ofFn x)).length = m := by
      simp [length_wiresFrom, m]
    rw [← hl]
    rw [xorStep' _ _ _ (by rw [hl]; exact lt_of_lt_of_le i.isLt (Nat.le_add_right _ _))
      (by rw [hl]; exact ho)]
    rw [getD_wiresFrom _ _ _ (by simpa using i.isLt)]
    change xor ((List.ofFn x).getD i false) (C.eval (List.ofFn x)) = _
    simp [ev x]

theorem xnor_upper {n s : ℕ} {f : (Fin n → Bool) → Bool}
    (h : HasCircuitSize n f s) (hnc : ∃ x y, f x ≠ f y) (i : Fin n) :
    HasCircuitSize n (fun x => xor (x i) (!(f x))) (s+4) := by
  obtain ⟨C, ok, hs, ev⟩ := h
  have ho := output_lt_of_nonconstant C ev hnc
  let m := n+C.gates.length
  refine ⟨⟨C.gates ++ xnorGates m i C.output, m+3⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact ok g hg
    · simp only [xnorGates, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp
  · simpa [Circuit.size, xnorGates] using Nat.add_le_add_right hs 4
  · intro x
    change (wiresFrom (C.gates ++ xnorGates m i C.output) (List.ofFn x)).getD (m+3) false = _
    rw [wiresFrom_append]
    have hl : (wiresFrom C.gates (List.ofFn x)).length = m := by
      simp [length_wiresFrom, m]
    rw [← hl]
    rw [xnorStep' _ _ _ (by rw [hl]; exact lt_of_lt_of_le i.isLt (Nat.le_add_right _ _))
      (by rw [hl]; exact ho)]
    rw [getD_wiresFrom _ _ _ (by simpa using i.isLt)]
    change xor ((List.ofFn x).getD i false) (!(C.eval (List.ofFn x))) = _
    simp [ev x]

theorem upper {n s : ℕ} {g : (Fin n → Bool) → Bool}
    (hnc : ∃ y y', g y ≠ g y')
    (h : HasCircuitSize n g s ∨ HasCircuitSize n (fun y => !(g y)) s) :
    HasCircuitSize (n+1)
      (fun x : Fin (n+1) → Bool => xor (x (Fin.last n)) (g (fun i => x i.castSucc))) (s+4) := by
  have nc : ∃ x y : Fin (n+1) → Bool,
      g (fun i => x i.castSucc) ≠ g (fun i => y i.castSucc) := by
    obtain ⟨x,y,hxy⟩ := hnc
    refine ⟨Fin.snoc x false, Fin.snoc y false, ?_⟩
    simpa only [Fin.snoc_castSucc] using hxy
  rcases h with h | h
  · exact xor_upper (relabel_size Fin.castSucc g s h) nc (Fin.last n)
  · have nc' : ∃ x y : Fin (n+1) → Bool,
        (!(g (fun i => x i.castSucc))) ≠ (!(g (fun i => y i.castSucc))) := by
      obtain ⟨x,y,hxy⟩ := nc
      refine ⟨x,y, ?_⟩
      cases h1 : g (fun i => x i.castSucc) <;>
        cases h2 : g (fun i => y i.castSucc) <;> simp_all
    simpa only [Bool.not_not, Function.comp_def] using
      xnor_upper (relabel_size Fin.castSucc (fun y => !(g y)) s h) nc' (Fin.last n)


theorem constant_upper {n s : ℕ} (g : (Fin n → Bool) → Bool)
    (h : ∀ y, g y = g (fun _ => false)) :
    HasCircuitSize (n+1) (fun x => xor (x (Fin.last n)) (g (fun i => x i.castSucc))) (s+4) := by
  cases hv : g (fun _ => false) with
  | false =>
    refine ⟨⟨[],n⟩, ?_, by simp [Circuit.size], ?_⟩
    · intro a ha; simp at ha
    · intro x
      simp [Circuit.eval,Circuit.wires,h,hv,List.getD,Fin.last]
      simpa only [List.ofFn_succ] using (List.getElem_ofFn (f := x) (i := n) (by simp))
  | true =>
    refine ⟨⟨[⟨GateOp.not,[n]⟩],n+1⟩, ?_, ?_, ?_⟩
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      simp
    · simp [Circuit.size]
    · intro x
      simp [Circuit.eval,Circuit.wires,GateOp.eval,h,hv,List.getD,Fin.last]
      simpa only [List.ofFn_succ] using (List.getElem_ofFn (f := x) (i := n) (by simp))

end PEqualNP.Outside.L_meta_716

theorem PEqualNP.Outside.L_meta_716 : ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool), (PEqualNP.MetaComplexity.HasCircuitSize n g s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) := by
  intro n s g
  by_cases hnc : ∃ y y', g y ≠ g y'
  · constructor
    · intro h
      exact PEqualNP.Outside.L_meta_716.upper hnc (Or.inl h)
    · intro h
      exact PEqualNP.Outside.L_meta_716.upper hnc (Or.inr h)
  · have hc : ∀ y, g y = g (fun _ => false) := by
      intro y
      by_contra he
      exact hnc ⟨y, fun _ => false, he⟩
    exact ⟨fun _ => PEqualNP.Outside.L_meta_716.constant_upper g hc,
      fun _ => PEqualNP.Outside.L_meta_716.constant_upper g hc⟩
