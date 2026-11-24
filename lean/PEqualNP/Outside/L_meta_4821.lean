import Mathlib
import PEqualNP.Defs

-- Take a least circuit of the model for the function. A gate that is neither read nor the output
-- can be erased, so every gate but the output is read; then the output is the last gate. Every
-- input is read: the perfect matching makes the function depend on every input.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4821

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem run_app (gs hs : List Gate) (w : List Bool) : run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

theorem run_len : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length
  | [], w => by simp [run]
  | g :: gs, w => by rw [run_cons, run_len gs]; simp; omega

theorem run_pre : ∀ (gs : List Gate) (w : List Bool) (r : ℕ), r < w.length →
    (run gs w).getD r false = w.getD r false
  | [], _, _, _ => rfl
  | g :: gs, w, r, hr => by
    rw [run_cons, run_pre gs _ r (by simp; omega), List.getD_append _ _ _ _ hr]

theorem wires_run (C : Circuit) (w : List Bool) : C.wires w = run C.gates w := rfl

def substWire (k a i : ℕ) : ℕ := if i < k then i else if i = k then a else i - 1

-- Runs that agree away from an unread wire k agree away from k.
theorem run_away (k : ℕ) : ∀ (gs : List Gate) (w1 w2 : List Bool),
    w1.length = w2.length → (∀ g ∈ gs, k ∉ g.inputs) →
    (∀ i, i ≠ k → w2.getD i false = w1.getD i false) →
    ∀ i, i ≠ k → (run gs w2).getD i false = (run gs w1).getD i false
  | [], _, _, _, _, h => h
  | g :: gs, w1, w2, hl, hk, h => by
    rw [run_cons, run_cons]
    have hval : (g.inputs.map fun r => w2.getD r false) = g.inputs.map fun r => w1.getD r false :=
      List.map_congr_left (fun r hr => h r (fun e => hk g (by simp) (e ▸ hr)))
    rw [hval]
    apply run_away k gs _ _ (by simp [hl]) (fun g' hg' => hk g' (by simp [hg']))
    intro i hi
    by_cases hlt : i < w1.length
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hlt]; exact h i hi
    · by_cases he : i = w1.length
      · subst he
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ le_rfl, hl]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

-- Erasing an unread wire k shifts the later wires down by one.
theorem run_drop (k a : ℕ) : ∀ (gs : List Gate) (w1 w2 : List Bool),
    w1.length = w2.length + 1 → k < w1.length → (∀ g ∈ gs, k ∉ g.inputs) →
    (∀ i < w1.length, i ≠ k → w2.getD (substWire k a i) false = w1.getD i false) →
    ∀ i, i ≠ k → (run (gs.map fun g => ⟨g.op, g.inputs.map (substWire k a)⟩) w2).getD
      (substWire k a i) false = (run gs w1).getD i false
  | [], w1, w2, hl, hk, _, h => by
    intro i hi
    by_cases hi' : i < w1.length
    · exact h i hi' hi
    · have : substWire k a i = i - 1 := by unfold substWire; split_ifs <;> omega
      rw [this]
      simp only [run, List.map_nil, List.foldl_nil]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | g :: gs, w1, w2, hl, hk, hread, h => by
    simp only [List.map_cons, run_cons]
    have hval : ((g.inputs.map (substWire k a)).map fun r => w2.getD r false) =
        g.inputs.map (fun r => w1.getD r false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro r hr
      have hrk : r ≠ k := fun e => hread g (by simp) (e ▸ hr)
      by_cases hr' : r < w1.length
      · exact h r hr' hrk
      · have : substWire k a r = r - 1 := by unfold substWire; split_ifs <;> omega
        simp only [Function.comp_apply, this]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    apply run_drop k a gs _ _ (by simp; omega) (by simp; omega) (fun g' hg' => hread g' (by simp [hg']))
    intro i hi hik
    simp only [List.length_append, List.length_singleton] at hi
    rw [hval]
    by_cases hi' : i < w1.length
    · have hs : substWire k a i < w2.length := by unfold substWire; split_ifs <;> omega
      rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ hi']
      exact h i hi' hik
    · have he : i = w1.length := by omega
      have hs : substWire k a i = w2.length := by unfold substWire; split_ifs <;> omega
      rw [hs, he]
      simp [List.getD_append_right]

section
variable (N : ℕ) (E : Finset (Fin N × Fin N))

def fE (z : Fin (N + N) → Bool) : Bool :=
  decide (∃ (p : Fin N) (l : Fin N), (p, l) ∈ E ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

def Good (D : Circuit) : Prop :=
  PEqualNP.TopForm.IsAO2 (N + N) D ∧ ∀ z, circuitFun (N + N) D z = fE N E z

end

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt; rw [List.getD_eq_getElem _ _ hj]

-- One true input: no edge.
theorem fE_single (N : ℕ) (E : Finset (Fin N × Fin N)) (w : Fin (N + N)) :
    fE N E (fun k => decide (k = w)) = false := by
  unfold fE
  simp only [decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
  intro p l _ h1 h2
  rw [← h2] at h1
  exact absurd h1 (by
    intro h; have := congrArg Fin.val h; simp at this; omega)

theorem fE_pair (N : ℕ) (E : Finset (Fin N × Fin N)) (p l : Fin N) (h : (p, l) ∈ E) :
    fE N E (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true := by
  unfold fE; simp only [decide_eq_true_eq]; exact ⟨p, l, h, by simp, by simp⟩

-- Erasing an unread gate that is not the output.
theorem erase_good (N : ℕ) (E : Finset (Fin N × Fin N)) (D : Circuit) (hD : Good N E D)
    (j : ℕ) (hj : j < D.gates.length) (hread : ∀ g ∈ D.gates, N + N + j ∉ g.inputs)
    (hout : D.output ≠ N + N + j) :
    ∃ D' : Circuit, Good N E D' ∧ D'.size + 1 = D.size := by
  obtain ⟨⟨hand, hback, htwo⟩, hf⟩ := hD
  let n := N + N
  let ren : ℕ → ℕ := substWire (n + j) 0
  let D' : Circuit := ⟨D.gates.take j ++ (D.gates.drop (j + 1)).map
    (fun g => ⟨g.op, g.inputs.map ren⟩), ren D.output⟩
  have hlen : D'.gates.length + 1 = D.gates.length := by simp [D']; omega
  refine ⟨D', ⟨⟨?_, ?_, ?_⟩, ?_⟩, by simpa [Circuit.size] using hlen⟩
  · intro g hg
    rcases List.mem_append.1 hg with h1 | h1
    · exact hand g (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
      exact hand g0 (List.mem_of_mem_drop hg0)
  · intro j' hj' i hi
    have hj'' : j' < D.gates.length - 1 := by omega
    rw [gateAt_eq _ _ hj'] at hi
    by_cases hlt : j' < j
    · have e : D'.gates[j'] = D.gates[j'] := by
        simp only [D']
        rw [List.getElem_append_left (by simp; omega), List.getElem_take]
      rw [e] at hi
      exact hback j' (by omega) i (by rw [gateAt_eq _ _ (by omega)]; exact hi)
    · have e : D'.gates[j'] = ⟨D.gates[j' + 1].op, D.gates[j' + 1].inputs.map ren⟩ := by
        simp only [D']
        rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_map, List.getElem_drop, List.length_take]
        simp only [show j + 1 + (j' - min j D.gates.length) = j' + 1 by omega]
      rw [e] at hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi
      have hb := hback (j' + 1) (by omega) i0 (by rw [gateAt_eq _ _ (by omega)]; exact hi0)
      have hne : i0 ≠ n + j := fun e => hread _ (List.getElem_mem (by omega)) (e ▸ hi0)
      simp only [ren, substWire]; split_ifs <;> omega
  · intro g hg
    rcases List.mem_append.1 hg with h1 | h1
    · exact htwo g (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
      simpa using htwo g0 (List.mem_of_mem_drop hg0)
  · intro z
    rw [← hf z]
    show (run D'.gates (List.ofFn z)).getD (ren D.output) false =
      (run D.gates (List.ofFn z)).getD D.output false
    have hsplit : D.gates = D.gates.take (j + 1) ++ D.gates.drop (j + 1) :=
      (List.take_append_drop _ _).symm
    have htk : D.gates.take (j + 1) = D.gates.take j ++ [D.gates[j]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hj]; rfl
    set v := List.ofFn z
    have hv : v.length = n := List.length_ofFn
    set w2 := run (D.gates.take j) v with hw2
    set w1 := run (D.gates.take (j + 1)) v with hw1
    have hl2 : w2.length = n + j := by rw [hw2, run_len, hv, List.length_take]; omega
    have hw12 : w1 = w2 ++ [D.gates[j].op.eval (D.gates[j].inputs.map fun i => w2.getD i false)] := by
      rw [hw1, htk, run_app, run_cons]; rfl
    have hl1 : w1.length = n + j + 1 := by rw [hw12]; simp [hl2]
    have e1 : run D.gates v = run (D.gates.drop (j + 1)) w1 := by
      conv_lhs => rw [hsplit]
      rw [run_app]
    have e2 : run D'.gates v = run ((D.gates.drop (j + 1)).map
        (fun g => ⟨g.op, g.inputs.map ren⟩)) w2 := by
      simp only [D']; rw [run_app]
    rw [e1, e2]
    apply run_drop (n + j) 0 _ w1 w2 (by omega) (by omega)
      (fun g hg => hread g (List.mem_of_mem_drop hg))
    · intro i hi hik
      have : i < n + j := by omega
      simp only [substWire, this, if_true]
      rw [hw12, List.getD_append _ _ _ _ (by omega)]
    · exact hout

-- An input read by no gate, and not the output, does not change the output.
theorem input_free (N : ℕ) (D : Circuit) (i : Fin (N + N)) (hread : ∀ g ∈ D.gates, i.val ∉ g.inputs)
    (hout : D.output ≠ i.val) (z : Fin (N + N) → Bool) :
    circuitFun (N + N) D (Function.update z i (!z i)) = circuitFun (N + N) D z := by
  show (run D.gates _).getD D.output false = (run D.gates _).getD D.output false
  apply run_away i.val D.gates _ _ (by simp) hread _ D.output hout
  intro k hk
  by_cases hkn : k < N + N
  · rw [List.getD_eq_getElem _ _ (by simpa using hkn), List.getD_eq_getElem _ _ (by simpa using hkn),
      List.getElem_ofFn, List.getElem_ofFn]
    rw [Function.update_of_ne (by intro e; apply hk; rw [← e])]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem main (N : ℕ) (E : Finset (Fin N × Fin N)) (σ : Equiv.Perm (Fin N)) (C : Circuit)
    (hcard : N < E.card) (hσ : ∀ x, (x, σ x) ∈ E) (hC : Good N E C) :
    ∃ D : Circuit, Good N E D ∧ D.size ≤ C.size ∧ D.output + 1 = N + N + D.size ∧
      (D.gates.flatMap Gate.inputs).toFinset = Finset.range (N + N + D.size - 1) := by
  classical
  have hex : ∃ s, ∃ D : Circuit, Good N E D ∧ D.size = s := ⟨C.size, C, hC, rfl⟩
  obtain ⟨D, hD, hDs⟩ := Nat.find_spec hex
  have hmin : ∀ D' : Circuit, Good N E D' → D.size ≤ D'.size := by
    intro D' hD'; rw [hDs]; exact Nat.find_min' hex ⟨D', hD', rfl⟩
  have hle : D.size ≤ C.size := hmin C hC
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      exfalso
      obtain ⟨⟨q, _⟩, _⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
      exact q.elim0
    · exact h
  have hf := hD.2
  obtain ⟨⟨_, hback, _⟩, _⟩ := hD
  -- the output is a gate
  have hgate : N + N ≤ D.output ∧ D.output < N + N + D.gates.length := by
    constructor
    · by_contra hlt
      push_neg at hlt
      have h := hf (fun k => decide (k = ⟨D.output, hlt⟩))
      rw [fE_single] at h
      have : circuitFun (N + N) D (fun k => decide (k = ⟨D.output, hlt⟩)) = true := by
        show (run D.gates _).getD D.output false = true
        rw [run_pre _ _ _ (by simpa using hlt), List.getD_eq_getElem _ _ (by simpa using hlt),
          List.getElem_ofFn]
        simp
      rw [this] at h; exact absurd h (by decide)
    · by_contra hge
      push_neg at hge
      let p : Fin N := ⟨0, hN⟩
      have h := hf (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N (σ p)))
      rw [fE_pair N E p (σ p) (hσ p)] at h
      have : circuitFun (N + N) D (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N (σ p))) =
          false := by
        show (run D.gates _).getD D.output false = false
        exact List.getD_eq_default _ _ (by rw [run_len]; simpa using hge)
      rw [this] at h; exact absurd h (by decide)
  -- every gate other than the output is read
  have hreadG : ∀ j < D.gates.length, N + N + j ≠ D.output → ∃ g ∈ D.gates, N + N + j ∈ g.inputs := by
    intro j hj hne
    by_contra hno
    push_neg at hno
    obtain ⟨D', hD', hs⟩ := erase_good N E D ⟨⟨‹_›, hback, ‹_›⟩, hf⟩ j hj hno (Ne.symm hne)
    have := hmin D' hD'
    omega
  -- the output is the last gate
  have hlast : D.output + 1 = N + N + D.gates.length := by
    by_contra hne
    have hj : D.gates.length - 1 < D.gates.length := by omega
    obtain ⟨g, hg, hgi⟩ := hreadG (D.gates.length - 1) hj (by omega)
    obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hg
    have := hback j' hj' _ (by rw [gateAt_eq _ _ hj']; exact hgi)
    omega
  -- every input is read
  have hreadI : ∀ i < N + N, ∃ g ∈ D.gates, i ∈ g.inputs := by
    intro i hi
    by_contra hno
    push_neg at hno
    have hfree := input_free N D ⟨i, hi⟩ hno (by omega)
    by_cases hp : i < N
    · let p : Fin N := ⟨i, hp⟩
      let z : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N (σ p))
      have h1 := hf z
      rw [fE_pair N E p (σ p) (hσ p)] at h1
      have h2 := hf (Function.update z ⟨i, hi⟩ (!z ⟨i, hi⟩))
      rw [hfree z, h1] at h2
      have : Function.update z ⟨i, hi⟩ (!z ⟨i, hi⟩) = fun k => decide (k = Fin.natAdd N (σ p)) := by
        funext k
        by_cases hk : k = ⟨i, hi⟩
        · subst hk; simp [z, p, Fin.ext_iff]; omega
        · rw [Function.update_of_ne hk]
          simp only [z]
          have : k ≠ Fin.castAdd N p := by intro e; apply hk; rw [e]; ext; simp [p]
          simp only [this, false_or]
      rw [this, fE_single] at h2
      exact absurd h2 (by decide)
    · let l : Fin N := ⟨i - N, by omega⟩
      let p : Fin N := σ.symm l
      let z : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
      have hpl : (p, l) ∈ E := by have := hσ p; simpa [p] using this
      have h1 := hf z
      rw [fE_pair N E p l hpl] at h1
      have h2 := hf (Function.update z ⟨i, hi⟩ (!z ⟨i, hi⟩))
      rw [hfree z, h1] at h2
      have hil : (⟨i, hi⟩ : Fin (N + N)) = Fin.natAdd N l := by ext; simp [l]; omega
      have : Function.update z ⟨i, hi⟩ (!z ⟨i, hi⟩) = fun k => decide (k = Fin.castAdd N p) := by
        funext k
        by_cases hk : k = ⟨i, hi⟩
        · subst hk
          rw [Function.update_self]
          simp only [z, hil]
          have hne : Fin.natAdd N l ≠ Fin.castAdd N p := by
            intro e; have := congrArg Fin.val e; simp at this; omega
          simp only [hne, false_or, decide_true, Bool.not_true]
          rfl
        · rw [Function.update_of_ne hk]
          simp only [z]
          have hkl : k ≠ Fin.natAdd N l := by rw [← hil]; exact hk
          simp only [hkl, or_false]
      rw [this, fE_single] at h2
      exact absurd h2 (by decide)
  refine ⟨D, ⟨⟨‹_›, hback, ‹_›⟩, hf⟩, hle, by simpa [Circuit.size] using hlast, ?_⟩
  ext w
  simp only [List.mem_toFinset, List.mem_flatMap, Finset.mem_range]
  constructor
  · rintro ⟨g, hg, hw⟩
    obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hg
    have := hback j' hj' w (by rw [gateAt_eq _ _ hj']; exact hw)
    simp only [Circuit.size]; omega
  · intro hw
    simp only [Circuit.size] at hw
    by_cases hwn : w < N + N
    · exact hreadI w hwn
    · obtain ⟨g, hg, hgi⟩ := hreadG (w - (N + N)) (by omega) (by omega)
      exact ⟨g, hg, by rwa [show N + N + (w - (N + N)) = w by omega] at hgi⟩

end PEqualNP.Outside.L_meta_4821

theorem PEqualNP.Outside.L_meta_4821 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x6 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 x6 = Decidable.decide (∃ (x7 : Fin x1) (x8 : Fin x1), (x7, x8) ∈ x2 ∧ x6 (Fin.castAdd x1 x7) = Bool.true ∧ x6 (Fin.natAdd x1 x8) = Bool.true);   x1 < x2.card → (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → x5 x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x10 ∧ x5 x10 ∧ x10.size ≤ x4.size ∧ x10.output + (1 : ℕ) = x1 + x1 + x10.size ∧ (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x10.gates).toFinset = Finset.range (x1 + x1 + x10.size - (1 : ℕ)) := by
  intro N E σ C _ hcard hσ hao hf
  obtain ⟨D, ⟨hDao, hDf⟩, hle, hout, hin⟩ :=
    PEqualNP.Outside.L_meta_4821.main N E σ C hcard hσ ⟨hao, hf⟩
  exact ⟨D, hDao, hDf, hle, hout, hin⟩
