import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17573

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

private def value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD i false

private theorem run_prefix (gs : List Gate) (w : List Bool) :
    ∃ tail : List Bool, run gs w = w ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨tail, he, hl⟩ := ih (step w g)
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    refine ⟨b :: tail, ?_, by simp [hl]⟩
    change run gs (step w g) = w ++ b :: tail
    rw [he]
    simp [step, b]

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  simp [ht, hl]

private theorem run_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

private theorem value_far {n : ℕ} (gs : List Gate) (x : Fin n → Bool) {i : ℕ}
    (hi : n + gs.length ≤ i) : value gs x i = false := by
  rw [value, List.getD_eq_default _ _ (by simpa [run_length] using hi)]

private theorem value_raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    value gs x i.val = x i := by
  rw [value, run_old _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

private theorem value_keep {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool)
    {i : ℕ} (hi : i < n + gs.length) :
    value (gs ++ [g]) x i = value gs x i := by
  change (run (gs ++ [g]) (List.ofFn x)).getD i false = _
  rw [show run (gs ++ [g]) (List.ofFn x) = run [g] (run gs (List.ofFn x)) by
    simp [run, List.foldl_append]]
  exact run_old _ _ _ (by simpa [run_length] using hi)

private theorem value_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    value (gs ++ [g]) x (n + gs.length) =
      g.op.eval (g.inputs.map (value gs x)) := by
  let w := run gs (List.ofFn x)
  have hl : w.length = n + gs.length := by simp [w, run_length]
  have he : run (gs ++ [g]) (List.ofFn x) = step w g := by
    simp [run, List.foldl_append, w]
  have hread : (g.inputs.map fun i => w.getD i false) = g.inputs.map (value gs x) :=
    List.map_congr_left fun _ _ => rfl
  change (run (gs ++ [g]) (List.ofFn x)).getD _ false = _
  rw [he, ← hl]
  calc
    (step w g).getD w.length false =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp [step, List.getD_eq_getElem?_getD]
    _ = _ := congrArg g.op.eval hread

private def operand {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then value gs x i else false

private theorem value_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) {j : ℕ} {g : Gate}
    (hg : gs[j]? = some g) :
    value gs x (n + j) = g.op.eval (g.inputs.map (operand gs x (n + j))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hg
  have hsplit : gs = (gs.take j ++ [g]) ++ gs.drop (j+1) := by
    conv_lhs => rw [← List.take_append_drop (j+1) gs]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := run (gs.take j) (List.ofFn x)
  have hw : w.length = n+j := by
    simp [w, run_length, List.length_take, Nat.min_eq_left hb.le]
  have hfull : run gs (List.ofFn x) = run (gs.drop (j+1)) (step w g) := by
    conv_lhs => rw [hsplit]
    simp [run, List.foldl_append, w]
  have hread (i : ℕ) : w.getD i false = operand gs x (n+j) i := by
    by_cases hi : i < n+j
    · have hv : value gs x i = w.getD i false := by
        rw [value, hfull, run_old _ _ _ (by simp [step, hw]; omega)]
        change (run [g] w).getD i false = _
        exact run_old _ _ _ (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand gs x (n+j)) :=
    List.map_congr_left fun i _ => hread i
  rw [value, hfull, run_old _ _ _ (by simp [step, hw])]
  calc
    (step w g).getD (n+j) false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      rw [← hw]
      simp [step, List.getD_eq_getElem?_getD]
    _ = _ := congrArg g.op.eval he

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem filter_succ (S : Finset ℕ) (j : ℕ) :
    S.filter (fun i => i < j + 1) =
      if j ∈ S then insert j (S.filter fun i => i < j) else S.filter fun i => i < j := by
  ext i
  by_cases hj : j ∈ S <;> by_cases hi : i ∈ S <;>
    simp only [Finset.mem_filter, hj, hi, ite_true, ite_false, true_and, false_and, Finset.mem_insert]
  all_goals grind

private theorem compact_prefix {n : ℕ} (gs : List Gate) (D : Set (Fin n → Bool)) (S : Finset ℕ)
    (hG : ∀ g ∈ gs, legal g)
    (hS : ∀ j ∈ S, j < gs.length ∧
      ∃ i < n+j, ∀ x ∈ D, value gs x (n+j) = value gs x i) :
    ∀ j ≤ gs.length, ∃ (out : List Gate) (r : ℕ → ℕ),
      out.length + (S.filter fun i => i < j).card = j ∧
      (∀ g ∈ out, legal g) ∧
      (∀ i < n+j, r i < n+out.length ∨ r i = n+gs.length) ∧
      ∀ x ∈ D, ∀ i, i < n+j → value out x (r i) = value gs x i := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨[], id, by simp, by simp, ?_, ?_⟩
    · intro i hi
      exact Or.inl (by simpa using hi)
    · intro x _ i hi
      let k : Fin n := ⟨i, by omega⟩
      change value [] x k.val = value gs x k.val
      rw [value_raw, value_raw]
  | succ j ih =>
    intro hj
    obtain ⟨out, r, hcount, hlegal, hmap, hval⟩ := ih (by omega)
    have hlen : out.length ≤ j := by omega
    let z := n + gs.length
    by_cases hmem : j ∈ S
    · obtain ⟨a, ha, hcopy⟩ := (hS j hmem).2
      have hEq (x : Fin n → Bool) (hx : x ∈ D) :
          value out x (r a) = value gs x (n+j) := (hval x hx a ha).trans (hcopy x hx).symm
      refine ⟨out, Function.update r (n+j) (r a), ?_, hlegal, ?_, ?_⟩
      · rw [filter_succ, ite_eq_left hmem, Finset.card_insert_of_notMem]
        · omega
        · simp
      · intro i hi
        by_cases ei : i = n+j
        · subst i
          simpa [z] using hmap a ha
        · simpa [Function.update_of_ne ei] using hmap i (by omega)
      · intro x hx i hi
        by_cases ei : i = n+j
        · subst i
          simpa using hEq x hx
        · simpa [Function.update_of_ne ei] using hval x hx i (by omega)
    · let g := gs[j]'(by omega)
      have hg : gs[j]? = some g := List.getElem?_eq_some_iff.2 ⟨by omega, rfl⟩
      let ins (i : ℕ) := if i < n+j then r i else z
      let g' : Gate := ⟨g.op, g.inputs.map ins⟩
      let next := out ++ [g']
      have hz : n + next.length ≤ z := by
        dsimp [next,z]
        simp only [List.length_append, List.length_singleton]
        omega
      refine ⟨next, Function.update r (n+j) (n+out.length), ?_, ?_, ?_, ?_⟩
      · rw [filter_succ, ite_eq_right hmem]
        simp only [next, List.length_append, List.length_singleton]
        omega
      · intro t ht
        simp only [next, List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · exact hlegal t ht
        · have hGg := hG g (List.mem_of_getElem? hg)
          simpa [legal, g'] using hGg
      · intro i hi
        by_cases ei : i = n+j
        · subst i
          left
          simp [next]
        · rw [Function.update_of_ne ei]
          rcases hmap i (by omega) with h | h
          · left
            simp only [next, List.length_append, List.length_singleton]
            omega
          · exact Or.inr h
      · intro x hx i hi
        by_cases ei : i = n+j
        · subst i
          simp only [Function.update_self]
          rw [value_gate gs _ hg]
          change value (out ++ [g']) x (n+out.length) = _
          rw [value_snoc]
          simp only [g', List.map_map]
          congr 1
          apply List.map_congr_left
          intro a _
          by_cases ha : a < n+j
          · simpa [ins, operand, ha] using hval x hx a ha
          · simp only [Function.comp_apply, ins, operand, ite_eq_right ha]
            exact value_far _ _ (by omega)
        · rw [Function.update_of_ne ei]
          have hi' : i < n+j := by omega
          rcases hmap i hi' with hlo | hhi
          · rw [value_keep _ _ _ hlo, hval x hx i hi']
          · exact (value_far next x (hhi.symm ▸ hz)).trans
              ((value_far out x (hhi.symm ▸ (show n+out.length ≤ z by omega))).symm.trans (hval x hx i hi'))

private theorem compact {n : ℕ} (C : Circuit) (D : Set (Fin n → Bool)) (S : Finset ℕ)
    (hG : FanInTwo C)
    (hS : ∀ j ∈ S, j < C.size ∧ ∃ i < n+j, ∀ x ∈ D, value C.gates x (n+j) = value C.gates x i) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size + S.card ≤ C.size ∧
      ∀ x ∈ D, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨gs, r, hs, hlegal, _, hval⟩ :=
    compact_prefix C.gates D S hG hS C.gates.length le_rfl
  have hfilter : S.filter (fun i => i < C.gates.length) = S :=
    Finset.filter_eq_self.2 fun j hj => (hS j hj).1
  rw [hfilter] at hs
  let o := if C.output < n+C.size then r C.output else n+C.size
  refine ⟨⟨gs,o⟩, hlegal, hs.le, ?_⟩
  intro x hx
  change value gs x o = value C.gates x C.output
  by_cases ho : C.output < n+C.size
  · simpa [o, ho] using hval x hx C.output ho
  · simp only [o, ite_eq_right ho]
    rw [value_far _ _ (by change n+gs.length ≤ n+C.gates.length; omega),
      value_far _ _ (by simpa [Circuit.size] using Nat.le_of_not_gt ho)]

end PEqualNP.Outside.L_meta_17573

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_17573 in
theorem PEqualNP.Outside.L_meta_17573 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Set (List Bool)) (x4 : Finset (Fin x1.size)), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x6 ∈ x3, x6.length = x2) → (∀ x7 ∈ x4, ∃ x9 < x2 + ↑x7, ∀ x10 ∈ x3, (x1.wires x10).getD (x2 + ↑x7) Bool.false = (x1.wires x10).getD x9 Bool.false) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + x4.card ≤ x1.size ∧ ∀ x9 ∈ x3, x8.eval x9 = x1.eval x9 := by
  intro C n X gates shape len hAlias
  let S : Finset ℕ := gates.image Fin.val
  let D : Set (Fin n → Bool) := {x | List.ofFn x ∈ X}
  have cardS : S.card = gates.card := Finset.card_image_of_injective _ Fin.val_injective
  have aliases : ∀ j ∈ S, j < C.size ∧
      ∃ i < n+j, ∀ x ∈ D, value C.gates x (n+j) = value C.gates x i := by
    intro j hj
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨i, hi, h⟩ := hAlias g hg
    exact ⟨g.isLt, i, hi, fun x hx => h (List.ofFn x) (show List.ofFn x ∈ X from hx)⟩
  obtain ⟨C', hfit, hb, hEq⟩ := compact C D S shape aliases
  refine ⟨C', hfit, by simpa [cardS] using hb, ?_⟩
  intro xs hxs
  have hl := len xs hxs
  subst n
  have found : List.ofFn (fun i : Fin xs.length => xs.get i) = xs := List.ofFn_get xs
  have hxD : (fun i : Fin xs.length => xs.get i) ∈ D := by
    change List.ofFn (fun i : Fin xs.length => xs.get i) ∈ X
    rwa [found]
  have result := hEq (fun i : Fin xs.length => xs.get i) hxD
  simpa only [found] using result
