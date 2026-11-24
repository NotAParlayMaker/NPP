import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4556

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The wires accumulated while evaluating gates `gs` on initial wires `w`
(`Circuit.wires` on a circuit made of `gs`). -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    show (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]; simp; omega

/-- Remap gate reads: wires `0..8` stay, wire `9` (which the padded input fixes to
`false`) is redirected to the dead index `dead`, later wires shift down by one. -/
def remap (dead i : ℕ) : ℕ := if i < 9 then i else if i = 9 then dead else i - 1

/-- The rewired gate: same operation, remapped reads. -/
def rgate (dead : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (remap dead)⟩

/-- Reading `remap dead i` from `u ++ t` equals reading `i` from `u ++ false :: t`. -/
lemma getD_rm (u t : List Bool) (dead i : ℕ)
    (hu : u.length = 9) (hd : (u ++ t).length ≤ dead) :
    (u ++ t).getD (remap dead i) false = (u ++ false :: t).getD i false := by
  unfold remap
  split_ifs with h1 h2
  · -- i < 9 : both sides read `u`
    rw [List.getD_append _ _ _ _ (by omega : i < u.length),
        List.getD_append _ _ _ _ (by omega : i < u.length)]
  · -- i = 9 : left is out of range (`dead`), right is the `false` cons head
    subst h2
    rw [List.getD_eq_default _ _ (by simpa using hd), List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega : u.length ≤ 9)]
    rw [hu]; simp
  · -- i ≥ 10 : both sides read `t[i - 10]?`
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega : u.length ≤ i - 1),
        List.getElem?_append_right (by omega : u.length ≤ i)]
    rw [show i - 1 - u.length = i - 10 by omega,
        show i - u.length = (i - 10) + 1 by omega, List.getElem?_cons_succ]

/-- Gate-by-gate correspondence: removing wire 9 of the padded input. -/
lemma wires_rm (dead : ℕ) (gs : List Gate) : ∀ u t : List Bool,
    u.length = 9 → (u ++ t).length + gs.length ≤ dead →
    ∃ t' : List Bool,
      wiresFrom gs (u ++ false :: t) = u ++ false :: t' ∧
      wiresFrom (gs.map (rgate dead)) (u ++ t) = u ++ t' := by
  induction gs with
  | nil => intro u t _ _; exact ⟨t, rfl, rfl⟩
  | cons g gs ih =>
    intro u t hu hd
    simp only [List.length_append, List.length_cons] at hd
    have hlen : (u ++ t).length ≤ dead := by
      simp only [List.length_append]; omega
    set v := g.op.eval (g.inputs.map fun i => (u ++ false :: t).getD i false) with hv
    have hval :
        (rgate dead g).op.eval ((rgate dead g).inputs.map fun i => (u ++ t).getD i false)
          = v := by
      simp only [rgate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_rm u t dead i hu hlen
    obtain ⟨t', h1, h2⟩ := ih u (t ++ [v]) hu (by simp; omega)
    refine ⟨t', ?_, ?_⟩
    · have hrw : wiresFrom (g :: gs) (u ++ false :: t)
          = wiresFrom gs ((u ++ false :: t) ++ [v]) := rfl
      rw [hrw, show (u ++ false :: t) ++ [v] = u ++ (false :: (t ++ [v])) by simp]
      exact h1
    · have h3 : wiresFrom ((g :: gs).map (rgate dead)) (u ++ t)
          = wiresFrom (gs.map (rgate dead)) ((u ++ t) ++
              [(rgate dead g).op.eval
                ((rgate dead g).inputs.map fun i => (u ++ t).getD i false)]) := rfl
      rw [h3, hval, List.append_assoc]
      exact h2

end PEqualNP.Outside.L_meta_4556

theorem PEqualNP.Outside.L_meta_4556 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) (fun (x4 : Fin (10 : ℕ) → Bool) => x1.eval (List.ofFn (Fin.init x4) ++ [Bool.false, x4 (9 : Fin (10 : ℕ))])) (13 : ℕ) := by
  intro C hft hsz
  set dead := 10 + C.gates.length with hdead
  have key : ∀ x : Fin 10 → Bool,
      List.ofFn x = List.ofFn (Fin.init x) ++ [x (9 : Fin 10)] := by
    intro x
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      rw [List.getElem_ofFn]
      by_cases h : i < 9
      · rw [List.getElem_append_left (by simp [h])]
        rw [List.getElem_ofFn]
        rfl
      · have hi : i = 9 := by simp at hi1 hi2; omega
        subst hi
        rw [List.getElem_append_right (by simp)]
        simp
  refine ⟨⟨C.gates.map (PEqualNP.Outside.L_meta_4556.rgate dead),
      PEqualNP.Outside.L_meta_4556.remap dead C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(hft g0 hg0).1, by simpa [PEqualNP.Outside.L_meta_4556.rgate] using (hft g0 hg0).2⟩
  · simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hsz
  · intro x
    obtain ⟨t', h1, h2⟩ := PEqualNP.Outside.L_meta_4556.wires_rm dead C.gates
      (List.ofFn (Fin.init x)) [x (9 : Fin 10)] (by simp) (by simp [dead])
    have hu : (List.ofFn (Fin.init x)).length = 9 := by simp
    have ht' : t'.length = 1 + C.gates.length := by
      have hlen := congrArg List.length h1
      rw [PEqualNP.Outside.L_meta_4556.length_wiresFrom] at hlen
      simp at hlen
      omega
    show (PEqualNP.Outside.L_meta_4556.wiresFrom (C.gates.map
        (PEqualNP.Outside.L_meta_4556.rgate dead)) (List.ofFn x)).getD
          (PEqualNP.Outside.L_meta_4556.remap dead C.output) false
      = (PEqualNP.Outside.L_meta_4556.wiresFrom C.gates
          (List.ofFn (Fin.init x) ++ [false, x (9 : Fin 10)])).getD C.output false
    rw [key x, h2]
    rw [show List.ofFn (Fin.init x) ++ [false, x (9 : Fin 10)]
        = List.ofFn (Fin.init x) ++ false :: [x (9 : Fin 10)] from rfl, h1]
    exact PEqualNP.Outside.L_meta_4556.getD_rm _ _ _ _ hu (by rw [List.length_append, hu, ht', hdead]; omega)
