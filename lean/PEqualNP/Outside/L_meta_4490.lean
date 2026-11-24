import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4490
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- Every subsequent gate appends a wire. The preservation of earlier wires follows L-meta-3586.
private lemma keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g tail ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

-- Index 13 is just past the end of the 13 wires visible to the first NOT.
private def pin (inputs : List ℕ) : Fin 14 :=
  if h : inputs.headD 13 < 13 then ⟨inputs.headD 13,by omega⟩ else 13

private lemma pin_spec (ins : List ℕ) (w : List Bool) (hl : w.length = 13) :
    GateOp.not.eval (ins.map fun i => w.getD i false) = !w.getD (pin ins).val false := by
  cases ins with
  | nil =>
    change true = !(w.getD 13 false)
    rw [List.getD_eq_default _ _ (by omega)]
    rfl
  | cons i is =>
    by_cases h : i < 13
    · simp [pin,h,GateOp.eval]
    · have hp : (pin (i::is)).val = 13 := by simp [pin,h]
      change (!(w.getD i false)) = !(w.getD (pin (i::is)).val false)
      rw [hp,List.getD_eq_default _ _ (by omega : w.length ≤ i),
        List.getD_eq_default _ _ (by omega : w.length ≤ 13)]

private lemma five (gs : List Gate) (h : 4 < gs.length) :
    ∃ a b c d n tail, gs = a::b::c::d::n::tail := by
  cases gs with | nil => simp at h | cons a gs =>
   cases gs with | nil => simp at h | cons b gs =>
    cases gs with | nil => simp at h | cons c gs =>
     cases gs with | nil => simp at h | cons d gs =>
      cases gs with | nil => simp at h | cons n tail => exact ⟨a,b,c,d,n,tail,rfl⟩

private theorem splitCircuit :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (4 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) →       (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) →         ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Fin (14 : ℕ)),           x5.size = (3 : ℕ) ∧             PEqualNP.MetaComplexity.Monotone2 x5 ∧               x6.size + (5 : ℕ) = x1.size ∧                 PEqualNP.MetaComplexity.FanInTwo x6 ∧                   (∃! x8 : Fin x6.gates.length, (x6.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧                     ∀ (x8 : Fin (9 : ℕ) → Bool),                       have x9 : List Bool := x5.wires (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ))]);                       x6.eval (x9 ++ [!x9.getD (↑x7) Bool.false]) = x1.eval (List.ofFn x8) := by
  intro ⟨gs,out⟩ fan ⟨first,last,lt,at4,fnot,lnot,exhaust⟩ wire
  change (first : ℕ) = 4 at at4
  obtain ⟨a,b,c,d,n,tail,rfl⟩ := five gs (by have hi : first.val < gs.length := first.isLt; omega)
  let whole := a::b::c::d::n::tail
  change Fin whole.length at first last
  have last_gt : 4 < last.val := by change first.val < last.val at lt; omega
  have notAt (j : ℕ) (hj : j < whole.length) :
      (whole.get ⟨j,hj⟩).op = .not ↔ j = 4 ∨ j = last.val := by
    constructor
    · intro hit
      rcases exhaust ⟨j,hj⟩ hit with h|h
      · exact Or.inl ((congrArg Fin.val h).trans at4)
      · exact Or.inr (congrArg Fin.val h)
    · rintro (h|h)
      · have e : (⟨j,hj⟩ : Fin whole.length) = first := Fin.ext (h.trans at4.symm)
        exact e ▸ fnot
      · exact (Fin.ext h : (⟨j,hj⟩ : Fin whole.length) = last) ▸ lnot
  have hn : n.op = .not := (notAt 4 (by simp [whole])).2 (Or.inl rfl)
  refine ⟨⟨[b,c,d],0⟩,⟨tail,out⟩,pin n.inputs,rfl,?_,?_,?_,?_,?_⟩
  · intro g hg
    change g ∈ [b,c,d] at hg
    have full : g ∈ whole := by simp only [List.mem_cons,List.mem_nil_iff,or_false] at hg; simp only [whole,List.mem_cons]; tauto
    obtain ⟨allowed,arity⟩ := fan g full
    refine ⟨?_,arity⟩
    have ex : g.op ≠ .not := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hg
      rcases hg with rfl|rfl|rfl
      · exact fun h => by have := (notAt 1 (by simp [whole])).1 h; omega
      · exact fun h => by have := (notAt 2 (by simp [whole])).1 h; omega
      · exact fun h => by have := (notAt 3 (by simp [whole])).1 h; omega
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at allowed ⊢
    tauto
  · simp [Circuit.size]
  · intro g hg
    exact fan g (by simp [hg])
  · let j : Fin tail.length := ⟨last.val-5,by have := last.isLt; simp [whole] at this; omega⟩
    have tag (p : Fin tail.length) : (tail.get p).op = .not ↔ p.val+5 = last.val := by
      have rhs := notAt (p.val+5) (by simp [whole])
      have eq : whole.get ⟨p.val+5,by simp [whole]⟩ = tail.get p := by rfl
      rw [eq] at rhs
      exact rhs.trans (by omega)
    exact ⟨j,(tag j).2 (by dsimp [j]; omega),fun p hp => Fin.ext (by have := (tag p).1 hp; dsimp [j]; omega)⟩
  · intro x
    let xs := List.ofFn x
    let pre := [b,c,d].foldl step (xs ++ [x 0 || x 2])
    have seen := wire x
    change ((b::c::d::n::tail).foldl step (step xs a)).getD 9 false = _ at seen
    rw [keep _ _ _ (by simp [step,xs])] at seen
    have firstValue : step xs a = xs ++ [x 0 || x 2] := by
      have hxs : xs.length = 9 := by simp [xs]
      have : a.op.eval (a.inputs.map fun i => xs.getD i false) = (x 0 || x 2) := by
        simpa [step,List.getD_eq_getElem?_getD,List.getElem?_append_right,hxs] using seen
      simp only [step,this]
    have hpre : pre.length = 13 := by simp [pre,step,xs]
    change (tail.foldl step (pre ++ [!pre.getD (pin n.inputs).val false])).getD out false =
      (tail.foldl step (step ([b,c,d].foldl step (step xs a)) n)).getD out false
    rw [firstValue]
    congr 2
    change pre ++ _ = pre ++ _
    rw [hn,pin_spec _ _ hpre]

end PEqualNP.Outside.L_meta_4490

theorem PEqualNP.Outside.L_meta_4490 :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (4 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) →       (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) →         ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Fin (14 : ℕ)),           x5.size = (3 : ℕ) ∧             PEqualNP.MetaComplexity.Monotone2 x5 ∧               x6.size + (5 : ℕ) = x1.size ∧                 PEqualNP.MetaComplexity.FanInTwo x6 ∧                   (∃! x8 : Fin x6.gates.length, (x6.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧                     ∀ (x8 : Fin (9 : ℕ) → Bool),                       have x9 : List Bool := x5.wires (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ))]);                       x6.eval (x9 ++ [!x9.getD (↑x7) Bool.false]) = x1.eval (List.ofFn x8) := PEqualNP.Outside.L_meta_4490.splitCircuit
