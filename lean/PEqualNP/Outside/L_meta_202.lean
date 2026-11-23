import Mathlib
import PEqualNP.Defs

-- Circuit reduction adapted from the checked L-meta-193 proof.
namespace PEqualNP.Outside.L_meta_202

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

private theorem split_at {α : Type} (xs : List α) (j : ℕ) (u v : α) (hj : xs[j]? = some u) :
    ∃ p t : List α, xs = p ++ u :: t ∧ xs.set j v = p ++ v :: t ∧ p.length = j := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp at hj
      subst u
      exact ⟨[],gs,rfl,rfl,rfl⟩
    | succ j =>
      obtain ⟨p,t,h1,h2,h3⟩ := ih j (by simpa using hj)
      exact ⟨g::p,t,congrArg (g :: ·) h1,congrArg (g :: ·) h2,by simp [h3]⟩

private lemma read_last (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by simp

private theorem cons_or (t : List Gate) (ids : List ℕ) (w : List Bool) :
    wiresFrom (⟨.or,ids⟩ :: t) w =
      wiresFrom t (w ++ [(ids.map fun i => w.getD i false).any id]) := rfl

end PEqualNP.Outside.L_meta_202

open PEqualNP.Outside.L_meta_202 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_202 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.FanInTwo { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } ∧ PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } = PEqualNP.MetaComplexity.circuitFun n C := by
  intro n j a h C hf hj hh himp
  obtain ⟨p,t,horig,hmod,hjlen⟩ := split_at C.gates j _ ⟨GateOp.or,[a]⟩ hj
  constructor
  · intro g hg
    simp only [hmod,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with (hg | rfl | hg) | rfl
    · exact hf _ (by simp [horig,hg])
    · simp
    · exact hf _ (by simp [horig,hg])
    · simp
  · funext x
    let w := wiresFrom p (List.ofFn x)
    let old := wiresFrom (⟨.or,[a,h]⟩ :: t) w
    let new := wiresFrom (⟨.or,[a]⟩ :: t) w
    have wh : h < w.length := by simpa [w,length_wiresFrom,hjlen] using hh
    have H : C.wires (List.ofFn x) = old := by rw [wires_eq,horig,wiresFrom_append]
    have hread (ids : List ℕ) :
        (wiresFrom (⟨.or,ids⟩ :: t) w).getD h false = w.getD h false :=
      getD_wiresFrom _ _ _ wh
    have hl : new.length = n + C.size := by
      simp [new,length_wiresFrom,w,Circuit.size,horig]; omega
    have hw : wiresFrom (C.gates.set j ⟨.or,[a]⟩) (List.ofFn x) = new := by
      rw [hmod,wiresFrom_append]
    change (wiresFrom (_ ++ [_]) (List.ofFn x)).getD _ false = _
    rw [wiresFrom_append,hw]
    change (new ++ [new.getD C.output false || (new.getD h false || false)]).getD (n+C.size) false = _
    rw [← hl]
    simp only [read_last, Bool.or_false]
    have hn : new.getD h false = w.getD h false := hread _
    rw [hn]
    cases e : w.getD h false with
    | true =>
      simpa using (himp x (by rw [H]; exact (hread _).trans e)).symm
    | false =>
      have hs : old = new := by simp only [List.getD_eq_getElem?_getD] at e; simp [old,new,cons_or,e]
      change _ = (C.wires (List.ofFn x)).getD C.output false
      simp [H,hs]
