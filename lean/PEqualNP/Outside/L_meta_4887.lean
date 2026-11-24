import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4887

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) x).getD i false) := by
  have hsplit : run gs x = run (gs.drop (j + 1)) (step (run (gs.take j) x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [run_append, run_cons]
  have hl : (run (gs.take j) x).length = x.length + j := by
    rw [run_length, List.length_take]; omega
  rw [hsplit, run_getD _ _ _ (by rw [step_length]; omega), ← hl, step_getD_last]

lemma run_prefix_getD (gs : List Gate) (x : List Bool) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < x.length + j) :
    (run (gs.take j) x).getD i false = (run gs x).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  exact (run_getD _ _ _ (by rw [run_length, List.length_take]; omega)).symm

lemma gate_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hr : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs x).getD i false) := by
  rw [run_gate gs x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact run_prefix_getD gs x j i hj.le (hr i hi)


lemma main (n : ℕ) (fs : List ((Fin n → Bool) → Bool)) (specs : List (Bool → Set (Fin n → Bool)))
    (target : Bool → Set (Fin n → Bool))
    (hmem : target ∈ fs.map (fun f bb => {x | f x = bb}) ++ specs)
    (hstep : ∀ k : Fin specs.length,
      ∃ a ∈ fs.map (fun f bb => {x | f x = bb}) ++ specs.take k,
      ∃ b ∈ fs.map (fun f bb => {x | f x = bb}) ++ specs.take k,
      ∃ c : Bool, ∀ bb : Bool, specs.get k bb ⊆ if bb = c then a bb ∪ b bb else a bb ∩ b bb) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ specs.length ∧
      ∀ (x : Fin n → Bool) (bb : Bool), x ∈ target bb → D.eval (fs.map fun f => f x) = bb := by
  set S := fs.map (fun f bb => {x : Fin n → Bool | f x = bb}) with hS
  have hpre : ∀ k : Fin specs.length, ∀ i, i < S.length + k →
      (S ++ specs.take k)[i]? = (S ++ specs)[i]? := by
    intro k i hi
    have e : S ++ specs.take k = (S ++ specs).take (S.length + k) := by
      rw [List.take_append, List.take_of_length_le (l := S) (by omega),
        Nat.add_sub_cancel_left]
    rw [e, List.getElem?_take_of_lt hi]
  have idx : ∀ k : Fin specs.length, ∀ s ∈ S ++ specs.take k,
      ∃ i, i < S.length + k ∧ (S ++ specs)[i]? = some s := by
    intro k s hs
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hs
    have hlen : (S ++ specs.take k).length = S.length + k := by
      simp only [List.length_append, List.length_take]
      have := k.isLt
      omega
    refine ⟨i, by omega, ?_⟩
    rw [← hpre k i (by omega), List.getElem?_eq_getElem hi, he]
  choose a ha b hb c hc using hstep
  choose ia hia using fun k => idx k (a k) (ha k)
  choose ib hib using fun k => idx k (b k) (hb k)
  obtain ⟨io, hio⟩ : ∃ i, (S ++ specs)[i]? = some target := by
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨i, by rw [List.getElem?_eq_getElem hi, he]⟩
  let gs : List Gate := List.ofFn fun k : Fin specs.length =>
    (⟨if c k = true then GateOp.or else GateOp.and, [ia k, ib k]⟩ : Gate)
  have hgs : gs.length = specs.length := by simp [gs]
  refine ⟨⟨gs, io⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    refine ⟨?_, by simp⟩
    split_ifs <;> simp
  · show gs.length ≤ specs.length
    omega
  · intro x bb hx
    have hinp : (fs.map fun f => f x).length = S.length := by simp [S]
    have claim : ∀ w s, (S ++ specs)[w]? = some s → ∀ bb, x ∈ s bb →
        (run gs (fs.map fun f => f x)).getD w false = bb := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro s hs bb hxs
        by_cases hw : w < S.length
        · rw [List.getElem?_append_left hw] at hs
          rw [run_getD gs _ w (by omega)]
          simp only [S, List.getElem?_map] at hs
          obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hs
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hf, Option.map_some,
            Option.getD_some]
          exact hxs
        · have hwl := (List.getElem?_eq_some_iff.mp hs).1
          simp only [List.length_append] at hwl
          have hk : w - S.length < specs.length := by omega
          rw [List.getElem?_append_right (by omega)] at hs
          rw [List.getElem?_eq_getElem hk] at hs
          have hsk : s = specs.get ⟨w - S.length, hk⟩ := by
            simp only [Option.some.injEq] at hs
            rw [← hs]
            rfl
          have hgk : gs[w - S.length]'(by omega) =
              ⟨if c ⟨w - S.length, hk⟩ = true then GateOp.or else GateOp.and,
                [ia ⟨w - S.length, hk⟩, ib ⟨w - S.length, hk⟩]⟩ := by
            simp [gs]
          have hiak := (hia ⟨w - S.length, hk⟩).1
          have hibk := (hib ⟨w - S.length, hk⟩).1
          have hval := gate_val gs (fs.map fun f => f x) (w - S.length) (by omega) (by
            intro i hi
            rw [hgk] at hi
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
            rw [hinp]
            rcases hi with rfl | rfl
            · exact hiak
            · exact hibk)
          rw [hinp, show S.length + (w - S.length) = w by omega, hgk] at hval
          rw [hval]
          have va := fun bb h => ih (ia ⟨w - S.length, hk⟩) (by simp at hiak; omega) _
            (hia ⟨w - S.length, hk⟩).2 bb h
          have vb := fun bb h => ih (ib ⟨w - S.length, hk⟩) (by simp at hibk; omega) _
            (hib ⟨w - S.length, hk⟩).2 bb h
          have hck := hc ⟨w - S.length, hk⟩ bb (hsk ▸ hxs)
          simp only [List.map_cons, List.map_nil]
          cases hcb : c ⟨w - S.length, hk⟩ <;> cases bb
          · simp only [hcb, ite_true] at hck
            rcases hck with h | h
            · rw [va false h]
              simp [GateOp.eval]
            · rw [vb false h]
              simp [GateOp.eval]
          · simp only [hcb, Bool.true_eq_false, ite_false] at hck
            rw [va true hck.1, vb true hck.2]
            simp [GateOp.eval]
          · simp only [hcb, Bool.false_eq_true, ite_false] at hck
            rw [va false hck.1, vb false hck.2]
            simp [GateOp.eval]
          · simp only [hcb, ite_true] at hck
            rcases hck with h | h
            · rw [va true h]
              simp [GateOp.eval]
            · rw [vb true h]
              simp [GateOp.eval]
    exact claim io target hio bb hx

end PEqualNP.Outside.L_meta_4887

theorem PEqualNP.Outside.L_meta_4887 : ∀ (x1 : ℕ) (x2 : List ((Fin x1 → Bool) → Bool)) (x3 : List (Bool → Set (Fin x1 → Bool))) (x4 : Bool → Set (Fin x1 → Bool)),   have x5 : List (Bool → Set (Fin x1 → Bool)) := List.map (fun (x5 : (Fin x1 → Bool) → Bool) (x6 : Bool) => {x7 : Fin x1 → Bool | x5 x7 = x6}) x2;   x4 ∈ x5 ++ x3 →     (∀ (x7 : Fin x3.length),         have x8 : List (Bool → Set (Fin x1 → Bool)) := x5 ++ List.take (↑x7) x3;         ∃ x9 ∈ x8, ∃ x10 ∈ x8, ∃ (x11 : Bool), ∀ (x12 : Bool), x3.get x7 x12 ⊆ if x12 = x11 then x9 x12 ∪ x10 x12 else x9 x12 ∩ x10 x12) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x3.length ∧ ∀ (x9 : Fin x1 → Bool) (x10 : Bool), x9 ∈ x4 x10 → x8.eval (List.map (fun (x12 : (Fin x1 → Bool) → Bool) => x12 x9) x2) = x10 := by
  intro n fs specs target
  exact PEqualNP.Outside.L_meta_4887.main n fs specs target
