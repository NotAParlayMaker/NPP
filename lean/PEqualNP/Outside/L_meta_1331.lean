import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1331
open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_nil (w : List Bool) : run [] w = w := rfl

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w =
      run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma getD_append_left {α : Type} (l₁ l₂ : List α) (d : α) (i : ℕ) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d :=
  List.getD_append _ _ _ _ h

lemma getD_append_right_eq {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp

lemma getD_append_out {α : Type} (l : List α) (a d : α) (i : ℕ) (h : l.length < i) :
    (l ++ [a]).getD i d = d :=
  List.getD_eq_default _ _ (by simp; omega)

/-- If every gate of `gs` reads only wires at least `n`, and two wire lists of equal length
at least `n` already agree on every index ≥ `n`, then after running `gs` they still do. -/
lemma run_agree (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, ∀ u ∈ g.inputs, n ≤ u)
    (wx wy : List Bool) (hlen : wx.length = wy.length) (hge : n ≤ wx.length)
    (hagree : ∀ u, n ≤ u → wx.getD u false = wy.getD u false) :
    ∀ u, n ≤ u → (run gs wx).getD u false = (run gs wy).getD u false := by
  induction gs generalizing wx wy with
  | nil =>
    intro u hu
    simpa [run_nil] using hagree u hu
  | cons g gs ih =>
    intro u hu
    have hg : ∀ v ∈ g.inputs, n ≤ v := fun v hv => hgs g (List.mem_cons_self) v hv
    have hgs' : ∀ g' ∈ gs, ∀ v ∈ g'.inputs, n ≤ v :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    have hbit :
        g.op.eval (g.inputs.map fun i => wx.getD i false) =
          g.op.eval (g.inputs.map fun i => wy.getD i false) := by
      congr 1
      refine List.map_congr_left ?_
      intro i hi
      exact hagree i (hg i hi)
    set bx := g.op.eval (g.inputs.map fun i => wx.getD i false)
    set byb := g.op.eval (g.inputs.map fun i => wy.getD i false)
    have hlen' : (wx ++ [bx]).length = (wy ++ [byb]).length := by
      simp [hlen, hbit]
    have hge' : n ≤ (wx ++ [bx]).length := by simp; omega
    have hagree' :
        ∀ v, n ≤ v → (wx ++ [bx]).getD v false = (wy ++ [byb]).getD v false := by
      intro v hv
      by_cases hlt : v < wx.length
      · rw [getD_append_left _ _ _ _ hlt, getD_append_left _ _ _ _ (by omega)]
        exact hagree v hv
      · by_cases heq : v = wx.length
        · subst heq
          have hwx : (wx ++ [bx]).getD wx.length false = bx := getD_append_right_eq _ _ _
          have hwy : (wy ++ [byb]).getD wx.length false = byb := by
            rw [hlen]; exact getD_append_right_eq _ _ _
          rw [hwx, hwy, hbit]
        · have : wx.length < v := by omega
          rw [getD_append_out _ _ _ _ this,
            getD_append_out _ _ _ _ (by omega)]
    rw [run_cons, run_cons]
    exact ih hgs' (wx ++ [bx]) (wy ++ [byb]) hlen' hge' hagree' u hu

lemma ofFn_agree (n : ℕ) (x y : Fin n → Bool) :
    ∀ u, n ≤ u → (List.ofFn x).getD u false = (List.ofFn y).getD u false := by
  intro u hu
  have hx : (List.ofFn x).length = n := by simp
  have hy : (List.ofFn y).length = n := by simp
  rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma take_inputs_ge (n : ℕ) (gates : List Gate) (G : Finset (Fin gates.length))
    (hG : ∀ j : Fin gates.length, j ∉ G → ∀ u ∈ (gates.get j).inputs, n ≤ u)
    (k : Fin gates.length) (_hk : k ∈ G) (hmin : ∀ i ∈ G, k ≤ i) :
    ∀ g ∈ gates.take k.val, ∀ u ∈ g.inputs, n ≤ u := by
  intro g hg u hu
  obtain ⟨j, hj, rfl⟩ := (List.mem_iff_getElem).1 hg
  have hjk : j < k.val := by
    have : (gates.take k.val).length = k.val := by simp
    omega
  have hjgates : j < gates.length := lt_trans hjk k.isLt
  let jf : Fin gates.length := ⟨j, hjgates⟩
  have hjf : jf ∉ G := by
    intro hmem
    have := hmin jf hmem
    exact Nat.lt_irrefl _ (lt_of_lt_of_le hjk this)
  have htake : (gates.take k.val)[j] = gates[j] := List.getElem_take
  have hget : gates.get jf = gates[j] := by
    simp [List.get_eq_getElem, jf]
  have hu' : u ∈ gates[j].inputs := by
    simpa [htake] using hu
  simpa [hget] using hG jf hjf u hu'

lemma eval_run (gs : List Gate) (out : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, out⟩ x = (run gs x).getD out false :=
  rfl

lemma wire_indep (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, ∀ u ∈ g.inputs, n ≤ u)
    (w : ℕ) (hw : n ≤ w) (x y : Fin n → Bool) :
    Circuit.eval ⟨gs, w⟩ (List.ofFn x) = Circuit.eval ⟨gs, w⟩ (List.ofFn y) := by
  simp only [eval_run]
  refine run_agree n gs hgs (List.ofFn x) (List.ofFn y) (by simp) (by simp) ?_ w hw
  exact ofFn_agree n x y

end PEqualNP.Outside.L_meta_1331

theorem PEqualNP.Outside.L_meta_1331 :
    ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate)
      (G : Finset (Fin gates.length)),
      (∀ j : Fin gates.length, j ∉ G → ∀ u ∈ (gates.get j).inputs, n ≤ u) →
      ∀ k ∈ G, (∀ i ∈ G, k ≤ i) →
        ∀ w ∈ (gates.get k).inputs, n ≤ w →
          ∀ x y : Fin n → Bool,
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn x) =
              PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.take k.val, w⟩ (List.ofFn y) := by
  intro n gates G hG k hk hmin w hw hn x y
  refine PEqualNP.Outside.L_meta_1331.wire_indep n (gates.take k.val) ?_ w hn x y
  exact PEqualNP.Outside.L_meta_1331.take_inputs_ge n gates G hG k hk hmin
