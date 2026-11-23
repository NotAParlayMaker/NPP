import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_716

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append,
      List.length_cons, List.length_nil]; omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

def old (k o : ℕ) : ℕ := if o < k then o else o + 1

theorem read_old (w : List Bool) (o : ℕ) (v : Bool) :
    (w ++ [v]).getD (old w.length o) false = w.getD o false := by
  unfold old
  split
  · exact List.getD_append _ _ _ _ (by assumption)
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def tailGates (b : Bool) (i k o : ℕ) : List Gate :=
  [⟨if b then GateOp.and else GateOp.or, [i, o]⟩,
   ⟨if b then GateOp.or else GateOp.and, [i, old k o]⟩,
   ⟨GateOp.not, [k + 1]⟩,
   ⟨if b then GateOp.or else GateOp.and, [k, k + 2]⟩]

lemma tail_eval (b : Bool) (w : List Bool) (i o : ℕ) (hi : i < w.length) :
    ((tailGates b i w.length o).foldl step w).getD (w.length + 3) false =
      xor (w.getD i false) (if b then !w.getD o false else w.getD o false) := by
  let z := w.getD i false
  let v := w.getD o false
  let a := if b then z && v else z || v
  let c := if b then z || v else z && v
  let w1 := w ++ [a]
  let w2 := w1 ++ [c]
  let w3 := w2 ++ [!c]
  have l1 : w1.length = w.length + 1 := by simp [w1]
  have l2 : w2.length = w.length + 2 := by simp [w2, l1]
  have l3 : w3.length = w.length + 3 := by simp [w3, l2]
  have h1i : w1.getD i false = z := List.getD_append _ _ _ _ hi
  have h1o : w1.getD (old w.length o) false = v := read_old _ _ _
  have h2c : w2.getD (w.length + 1) false = c := by rw [← l1]; exact getD_snoc_eq _ _ _
  have h3a : w3.getD w.length false = a := by
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    exact getD_snoc_eq _ _ _
  have h3c : w3.getD (w.length + 2) false = !c := by rw [← l2]; exact getD_snoc_eq _ _ _
  have e1 : step w ⟨if b then GateOp.and else GateOp.or, [i, o]⟩ = w1 := by
    cases b <;> simp [step, w1, a, z, v, GateOp.eval]
  have e2 : step w1 ⟨if b then GateOp.or else GateOp.and, [i, old w.length o]⟩ = w2 := by
    cases b <;> simp only [step, w2, c, Bool.false_eq_true, ↓reduceIte, GateOp.eval,
      List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons,
      List.all_nil, id_eq, Bool.or_false, Bool.and_true, h1i, h1o]
  have e3 : step w2 ⟨GateOp.not, [w.length + 1]⟩ = w3 := by
    change w2 ++ [!w2.getD (w.length + 1) false] = w2 ++ [!c]
    rw [h2c]
  change (step (step (step (step w _) _) _) _).getD (w.length + 3) false = _
  rw [e1, e2, e3]
  unfold step
  rw [← l3, getD_snoc_eq]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, GateOp.eval, List.map_cons,
    List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq,
    Bool.or_false, Bool.and_true, h3a, h3c]
  · change ((z || v) && !(z && v)) = xor z v
    cases z <;> cases v <;> rfl
  · change ((z && v) || !(z || v)) = xor z (!v)
    cases z <;> cases v <;> rfl

lemma input_read {m : ℕ} (x : Fin m → Bool) (i : Fin m) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

lemma add_xor (b : Bool) (n s : ℕ) (h : (Fin n → Bool) → Bool)
    (hs : HasCircuitSize n h s) :
    HasCircuitSize (n + 1) (fun x => xor (x (Fin.last n))
      (if b then !(h (fun i => x i.castSucc)) else h (fun i => x i.castSucc))) (s + 4) := by
  obtain ⟨C, hok, hsz, hev⟩ := relabel_size Fin.castSucc h s hs
  let k := n + 1 + C.gates.length
  refine ⟨⟨C.gates ++ tailGates b n k C.output, k + 3⟩, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hok a h
    · simp only [tailGates, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> cases b <;> simp
  · change (C.gates ++ tailGates b n k C.output).length ≤ s + 4
    have : C.gates.length ≤ s := hsz
    simp [tailGates]; omega
  · intro x
    let w := C.gates.foldl step (List.ofFn x)
    have hk : w.length = k := by simp [w, run_length, k]
    have hlast : w.getD n false = x (Fin.last n) := by
      rw [show w.getD n false = (List.ofFn x).getD n false from run_keep _ _ _ (by simp)]
      exact input_read x (Fin.last n)
    have hout : w.getD C.output false = h (fun i => x i.castSucc) := hev x
    change ((C.gates ++ tailGates b n k C.output).foldl step (List.ofFn x)).getD (k + 3) false = _
    rw [List.foldl_append]
    change ((tailGates b n k C.output).foldl step w).getD (k + 3) false = _
    rw [← hk, tail_eval b w n C.output (by rw [hk]; dsimp [k]; omega), hlast, hout]

end PEqualNP.Outside.L_meta_716

theorem PEqualNP.Outside.L_meta_716 : ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool), (PEqualNP.MetaComplexity.HasCircuitSize n g s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) := by
  intro n s g
  constructor
  · intro hg
    simpa using PEqualNP.Outside.L_meta_716.add_xor false n s g hg
  · intro hg
    simpa using PEqualNP.Outside.L_meta_716.add_xor true n s (fun y => !(g y)) hg
