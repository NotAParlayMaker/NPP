import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2776

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pts : List ℕ :=
  [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402]

def pos : List ℕ :=
  [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]

def initVecs : List (BitVec 24) :=
  [4358697, 8397251, 662022, 304212, 8980632, 1068256, 2199296, 12709888, 16646144, 13339321]

def seeds : List (BitVec 24) :=
  [0, 16777215, 4358697, 8397251, 662022, 304212, 8980632, 1068256, 2199296, 12709888, 16646144, 13339321]

def rowIn (m : ℕ) : List Bool :=
  let x : Fin 9 → Bool := fun i => m.testBit i.val
  List.ofFn x ++ [x 0 || x 4]

def gateVec (g : Gate) (W : List (BitVec 24)) : BitVec 24 :=
  match g.op, g.inputs with
  | GateOp.and, [] => 16777215
  | GateOp.and, [a] => W.getD a 0
  | GateOp.and, [a, b] => W.getD a 0 &&& W.getD b 0
  | GateOp.or, [] => 0
  | GateOp.or, [a] => W.getD a 0
  | GateOp.or, [a, b] => W.getD a 0 ||| W.getD b 0
  | _, _ => 0

theorem allOnes_bit : ∀ j : Fin 24, (16777215 : BitVec 24).getLsbD j.val = true := by
  decide

theorem pts_mem : ∀ j : Fin 24, pts.getD j.val 0 ∈ pts := by
  decide

theorem target_bit :
    ∀ j : Fin 24, decide (pts.getD j.val 0 ∈ pos) = (3428671 : BitVec 24).getLsbD j.val := by
  decide

theorem init_bit_lt :
    ∀ (j : Fin 24) (i : Fin 10),
      (initVecs.getD i.val 0).getLsbD j.val = (rowIn (pts.getD j.val 0)).getD i.val false := by
  decide

theorem init_len (j : Fin 24) : (rowIn (pts.getD j.val 0)).length = initVecs.length := by
  simp [rowIn, initVecs]

theorem init_bit (j : Fin 24) (i : ℕ) :
    (initVecs.getD i 0).getLsbD j.val = (rowIn (pts.getD j.val 0)).getD i false := by
  by_cases hi : i < 10
  · exact init_bit_lt j ⟨i, hi⟩
  · have h1 : initVecs.getD i 0 = 0 :=
      List.getD_eq_default initVecs 0 (by simp [initVecs]; omega)
    have h2 : (rowIn (pts.getD j.val 0)).getD i false = false :=
      List.getD_eq_default (rowIn (pts.getD j.val 0)) false (by simp [rowIn]; omega)
    rw [h1, h2]
    simp

theorem zero_mem_seeds : (0 : BitVec 24) ∈ seeds := by
  decide

theorem allOnes_mem_seeds : (16777215 : BitVec 24) ∈ seeds := by
  decide

theorem getD_mem_seeds_append (W acc : List (BitVec 24))
    (hmem : ∀ v ∈ W, v ∈ seeds ++ acc) (a : ℕ) :
    W.getD a 0 ∈ seeds ++ acc := by
  by_cases ha : a < W.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]
    exact hmem W[a] (List.getElem_mem ha)
  · rw [List.getD_eq_default W 0 (Nat.le_of_not_lt ha)]
    exact List.mem_append_left acc zero_mem_seeds

theorem gateVec_bit (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (W : List (BitVec 24)) (w : List Bool) (j : Fin 24)
    (hbit : ∀ i : ℕ, (W.getD i 0).getLsbD j.val = w.getD i false) :
    (gateVec g W).getLsbD j.val = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  rcases hg with ⟨hop, hlen⟩
  rcases hop with hop | hop
  · subst hop
    rcases ins with _ | ⟨a, _ | ⟨b, _ | c⟩⟩
    · simp only [gateVec, GateOp.eval, List.map_nil, List.all_nil]
      exact allOnes_bit j
    · simp only [gateVec, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
      exact hbit a
    · simp only [gateVec, GateOp.eval, BitVec.getLsbD_and, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
      rw [hbit a, hbit b]
    · simp at hlen
  · subst hop
    rcases ins with _ | ⟨a, _ | ⟨b, _ | c⟩⟩
    · simp [gateVec, GateOp.eval]
    · simp only [gateVec, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
      exact hbit a
    · simp only [gateVec, GateOp.eval, BitVec.getLsbD_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
      rw [hbit a, hbit b]
    · simp at hlen

theorem gateVec_step (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (W acc : List (BitVec 24)) (hmem : ∀ v ∈ W, v ∈ seeds ++ acc)
    (hnv : gateVec g W ∉ seeds ++ acc) :
    ∃ x8 ∈ seeds ++ acc, ∃ x9 ∈ seeds ++ acc,
      gateVec g W = x8 &&& x9 ∨ gateVec g W = x8 ||| x9 := by
  obtain ⟨op, ins⟩ := g
  rcases hg with ⟨hop, hlen⟩
  rcases hop with hop | hop
  · subst hop
    rcases ins with _ | ⟨a, _ | ⟨b, _ | c⟩⟩
    · simp only [gateVec] at hnv
      exact False.elim (hnv (List.mem_append_left acc allOnes_mem_seeds))
    · simp only [gateVec] at hnv
      exact False.elim (hnv (getD_mem_seeds_append W acc hmem a))
    · exact ⟨W.getD a 0, getD_mem_seeds_append W acc hmem a,
        W.getD b 0, getD_mem_seeds_append W acc hmem b, Or.inl rfl⟩
    · simp at hlen
  · subst hop
    rcases ins with _ | ⟨a, _ | ⟨b, _ | c⟩⟩
    · simp only [gateVec] at hnv
      exact False.elim (hnv (List.mem_append_left acc zero_mem_seeds))
    · simp only [gateVec] at hnv
      exact False.elim (hnv (getD_mem_seeds_append W acc hmem a))
    · exact ⟨W.getD a 0, getD_mem_seeds_append W acc hmem a,
        W.getD b 0, getD_mem_seeds_append W acc hmem b, Or.inr rfl⟩
    · simp at hlen

theorem getD_append_bit (W : List (BitVec 24)) (w : List Bool) (v : BitVec 24) (b : Bool) (j : Fin 24)
    (hlen : w.length = W.length)
    (hbit : ∀ i : ℕ, (W.getD i 0).getLsbD j.val = w.getD i false)
    (hv : v.getLsbD j.val = b) :
    ∀ i : ℕ, ((W ++ [v]).getD i 0).getLsbD j.val = (w ++ [b]).getD i false := by
  intro i
  by_cases hlt : i < W.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
    simpa [List.getD_eq_getElem?_getD] using hbit i
  · by_cases heq : i = W.length
    · subst heq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simpa [hlen] using hv
    · rw [List.getD_eq_default (W ++ [v]) 0 (by simp; omega)]
      rw [List.getD_eq_default (w ++ [b]) false (by simp; omega)]
      simp

theorem sim_gates :
    ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (W acc : List (BitVec 24)) (w : Fin 24 → List Bool),
        (∀ j : Fin 24, (w j).length = W.length) →
        (∀ (j : Fin 24) (i : ℕ), (W.getD i 0).getLsbD j.val = (w j).getD i false) →
        (∀ v ∈ W, v ∈ seeds ++ acc) →
        (∀ (k : ℕ) (hk : k < acc.length),
          acc[k] ∉ seeds ++ acc.take k ∧
          ∃ x8 ∈ seeds ++ acc.take k, ∃ x9 ∈ seeds ++ acc.take k,
            acc[k] = x8 &&& x9 ∨ acc[k] = x8 ||| x9) →
        ∃ (W' acc' : List (BitVec 24)),
          acc'.length ≤ acc.length + gs.length ∧
          (∀ (j : Fin 24) (i : ℕ),
            (W'.getD i 0).getLsbD j.val =
              (gs.foldl (fun wr (g : Gate) => wr ++ [g.op.eval (g.inputs.map fun idx => wr.getD idx false)]) (w j)).getD i false) ∧
          (∀ v ∈ W', v ∈ seeds ++ acc') ∧
          (∀ (k : ℕ) (hk : k < acc'.length),
            acc'[k] ∉ seeds ++ acc'.take k ∧
            ∃ x8 ∈ seeds ++ acc'.take k, ∃ x9 ∈ seeds ++ acc'.take k,
              acc'[k] = x8 &&& x9 ∨ acc'[k] = x8 ||| x9) := by
  intro gs
  induction gs with
  | nil =>
    intro _ W acc w _ hbit hmem hstep
    exact ⟨W, acc, Nat.le_refl _, hbit, hmem, hstep⟩
  | cons g rest ih =>
    intro hgs W acc w hlen hbit hmem hstep
    have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hgs g List.mem_cons_self
    have hrest : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    let v : BitVec 24 := gateVec g W
    let W1 : List (BitVec 24) := W ++ [v]
    let w1 : Fin 24 → List Bool := fun j => w j ++ [g.op.eval (g.inputs.map fun idx => (w j).getD idx false)]
    have hlen1 : ∀ j : Fin 24, (w1 j).length = W1.length := by
      intro j
      simp [w1, W1, hlen j]
    have hbit1 : ∀ (j : Fin 24) (i : ℕ), (W1.getD i 0).getLsbD j.val = (w1 j).getD i false := by
      intro j
      exact getD_append_bit W (w j) v (g.op.eval (g.inputs.map fun idx => (w j).getD idx false)) j
        (hlen j) (hbit j) (gateVec_bit g hg W (w j) j (hbit j))
    by_cases hv : v ∈ seeds ++ acc
    · have hmem1 : ∀ u ∈ W1, u ∈ seeds ++ acc := by
        intro u hu
        rcases List.mem_append.1 hu with huW | huv
        · exact hmem u huW
        · rcases List.mem_singleton.1 huv with rfl
          exact hv
      obtain ⟨W', acc', hlen', hbit', hmem', hstep'⟩ := ih hrest W1 acc w1 hlen1 hbit1 hmem1 hstep
      refine ⟨W', acc', ?_, hbit', hmem', hstep'⟩
      simp only [List.length_cons] at hlen' ⊢
      omega
    · have hmem1 : ∀ u ∈ W1, u ∈ seeds ++ (acc ++ [v]) := by
        intro u hu
        rcases List.mem_append.1 hu with huW | huv
        · rcases List.mem_append.1 (hmem u huW) with hus | hua
          · exact List.mem_append_left _ hus
          · exact List.mem_append_right _ (List.mem_append_left _ hua)
        · rcases List.mem_singleton.1 huv with rfl
          exact List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _))
      have hstep1 : ∀ (k : ℕ) (hk : k < (acc ++ [v]).length),
          (acc ++ [v])[k] ∉ seeds ++ (acc ++ [v]).take k ∧
          ∃ x8 ∈ seeds ++ (acc ++ [v]).take k, ∃ x9 ∈ seeds ++ (acc ++ [v]).take k,
            (acc ++ [v])[k] = x8 &&& x9 ∨ (acc ++ [v])[k] = x8 ||| x9 := by
        intro k hk
        simp only [List.length_append, List.length_singleton] at hk
        by_cases hklt : k < acc.length
        · have htake : (acc ++ [v]).take k = acc.take k := List.take_append_of_le_length (Nat.le_of_lt hklt)
          have hget : (acc ++ [v])[k] = acc[k] := List.getElem_append_left hklt
          rw [hget, htake]
          exact hstep k hklt
        · have hkeq : k = acc.length := by omega
          subst hkeq
          have htake : (acc ++ [v]).take acc.length = acc := by
            rw [List.take_append_of_le_length (le_refl _), List.take_length]
          have hget : (acc ++ [v])[acc.length] = v := by simp
          rw [hget, htake]
          exact ⟨hv, gateVec_step g hg W acc hmem hv⟩
      obtain ⟨W', acc', hlen', hbit', hmem', hstep'⟩ := ih hrest W1 (acc ++ [v]) w1 hlen1 hbit1 hmem1 hstep1
      refine ⟨W', acc', ?_, hbit', hmem', hstep'⟩
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen' ⊢
      omega

theorem main (x1 : Circuit) (hmono : Monotone2 x1)
    (hrows : ∀ x3 ∈ pts,
      let x5 : Fin 9 → Bool := fun i => x3.testBit i.val
      x1.eval (List.ofFn x5 ++ [x5 0 || x5 4]) = decide (x3 ∈ pos)) :
    ∃ x5 : List (BitVec 24), x5.length ≤ x1.size ∧
      (∀ (x6 : ℕ) (x7 : x6 < x5.length),
        x5[x6] ∉ seeds ++ List.take x6 x5 ∧
        ∃ x8 ∈ seeds ++ List.take x6 x5, ∃ x9 ∈ seeds ++ List.take x6 x5,
          x5[x6] = x8 &&& x9 ∨ x5[x6] = x8 ||| x9) ∧
      (3428671 : BitVec 24) ∈ seeds ++ x5 := by
  have hinitmem : ∀ v ∈ initVecs, v ∈ seeds ++ ([] : List (BitVec 24)) := by
    intro v hv
    simp only [List.append_nil, seeds, initVecs] at hv ⊢
    right
    right
    exact hv
  have hinitstep : ∀ (k : ℕ) (hk : k < ([] : List (BitVec 24)).length),
      ([] : List (BitVec 24))[k] ∉ seeds ++ ([] : List (BitVec 24)).take k ∧
      ∃ x8 ∈ seeds ++ ([] : List (BitVec 24)).take k,
        ∃ x9 ∈ seeds ++ ([] : List (BitVec 24)).take k,
          ([] : List (BitVec 24))[k] = x8 &&& x9 ∨ ([] : List (BitVec 24))[k] = x8 ||| x9 := by
    intro k hk
    simp at hk
  obtain ⟨W', acc', hlen', hbit', hmem', hstep'⟩ :=
    sim_gates x1.gates hmono initVecs [] (fun j => rowIn (pts.getD j.val 0))
      init_len init_bit hinitmem hinitstep
  have hout : W'.getD x1.output 0 = (3428671 : BitVec 24) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let j : Fin 24 := ⟨i, hi⟩
    have hb := hbit' j x1.output
    have hr := hrows (pts.getD j.val 0) (pts_mem j)
    have htb := target_bit j
    change (W'.getD x1.output 0).getLsbD j.val = (3428671 : BitVec 24).getLsbD j.val
    rw [hb, ← htb]
    exact hr
  refine ⟨acc', ?_, hstep', ?_⟩
  · simpa [Circuit.size] using hlen'
  · rw [← hout]
    exact getD_mem_seeds_append W' acc' hmem' x1.output

end PEqualNP.Outside.L_meta_2776

theorem PEqualNP.Outside.L_meta_2776 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       have x4 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))];       ∃ (x5 : List (BitVec (24 : ℕ))), x5.length ≤ x1.size ∧ (∀ (x6 : ℕ) (x7 : x6 < x5.length), x5[x6] ∉ x4 ++ List.take x6 x5 ∧ ∃ x8 ∈ x4 ++ List.take x6 x5, ∃ x9 ∈ x4 ++ List.take x6 x5, x5[x6] = x8 &&& x9 ∨ x5[x6] = x8 ||| x9) ∧ (3428671 : BitVec (24 : ℕ)) ∈ x4 ++ x5 := by
  intro x1 hmono hrows
  exact PEqualNP.Outside.L_meta_2776.main x1 hmono hrows
