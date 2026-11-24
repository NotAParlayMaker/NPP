import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3141

-- The wire list of a gate list started on the list w.
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

theorem run_high (gs : List Gate) (w : List Bool) (r : ℕ) (hr : w.length + gs.length ≤ r) :
    (run gs w).getD r false = false :=
  List.getD_eq_default _ _ (by rw [run_len]; omega)

theorem run_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs w).getD (w.length + j) false = gs[j].op.eval (gs[j].inputs.map fun r =>
      if r < w.length + j then (run gs w).getD r false else false) := by
  have hsplit : gs = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hul : (run (gs.take j) w).length = w.length + j := by
    rw [run_len, List.length_take]; omega
  have hall : run gs w = run (gs.drop (j + 1)) (run (gs.take j) w ++
      [gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) w).getD i false)]) := by
    conv_lhs => rw [hsplit]
    rw [run_app, run_cons]
  have key : ∀ r, (if r < w.length + j then (run gs w).getD r false else false) =
      (run (gs.take j) w).getD r false := by
    intro r
    split_ifs with h
    · rw [hall, run_pre _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
    · exact (List.getD_eq_default _ _ (by omega)).symm
  simp only [key]
  rw [hall, run_pre _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega)]
  simp only [hul, Nat.sub_self, List.getD_cons_zero]

-- Moving a circuit on the nine inputs to the eleven wires: the eight inputs other than x_4,
-- a free literal, true and false. Wire 4 becomes the false wire 10, gates move up by two.
def inMap (r : ℕ) : ℕ := if r < 4 then r else if r = 4 then 10 else r - 1

def tau (r : ℕ) : ℕ := if r < 9 then inMap r else r + 2

def remap (C : Circuit) : Circuit :=
  ⟨C.gates.map fun g => ⟨g.op, g.inputs.map tau⟩, tau C.output⟩

theorem remap_run : ∀ (gs : List Gate) (wo wn : List Bool), 9 ≤ wo.length →
    wn.length = wo.length + 2 → (∀ i, wn.getD (tau i) false = wo.getD i false) →
    ∀ i, (run (gs.map fun g => ⟨g.op, g.inputs.map tau⟩) wn).getD (tau i) false =
      (run gs wo).getD i false
  | [], _, _, _, _, h => h
  | g :: gs, wo, wn, h9, hl, h => by
    simp only [List.map_cons, run_cons]
    apply remap_run gs _ _ (by simp; omega) (by simp; omega)
    intro i
    have hv : (g.inputs.map tau).map (fun r => wn.getD r false) =
        g.inputs.map (fun r => wo.getD r false) := by
      rw [List.map_map]; exact List.map_congr_left (fun r _ => h r)
    simp only [hv]
    by_cases hi : i < wo.length
    · have ht : tau i < wn.length := by unfold tau inMap; split_ifs <;> omega
      rw [List.getD_append _ _ _ _ ht, List.getD_append _ _ _ _ hi]
      exact h i
    · by_cases he : i = wo.length
      · have ht : tau i = wn.length := by unfold tau; split_ifs <;> omega
        rw [ht, he]
        simp [List.getD_append_right]
      · have ht : wn.length + 1 ≤ tau i := by unfold tau; split_ifs <;> omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

-- Deleting gate j whose wire equals the earlier wire a on the input v.
def substWire (k a i : ℕ) : ℕ := if i < k then i else if i = k then a else i - 1

def delete (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map
      (fun g => ⟨g.op, g.inputs.map (substWire (m + j) a)⟩), substWire (m + j) a C.output⟩

theorem delete_inv (k a : ℕ) (ha : a < k) : ∀ (gs : List Gate) (w1 w2 : List Bool),
    w1.length = w2.length + 1 → k < w1.length →
    (∀ i < w1.length, w2.getD (substWire k a i) false = w1.getD i false) →
    ∀ i, (run (gs.map fun g => ⟨g.op, g.inputs.map (substWire k a)⟩) w2).getD
      (substWire k a i) false = (run gs w1).getD i false
  | [], w1, w2, hl, hk, h => by
    intro i
    by_cases hi : i < w1.length
    · exact h i hi
    · have : substWire k a i = i - 1 := by unfold substWire; split_ifs <;> omega
      rw [this]
      simp only [run, List.map_nil, List.foldl_nil]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | g :: gs, w1, w2, hl, hk, h => by
    simp only [List.map_cons, run_cons]
    have hval : ((g.inputs.map (substWire k a)).map fun r => w2.getD r false) =
        g.inputs.map (fun r => w1.getD r false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro r _
      by_cases hr : r < w1.length
      · exact h r hr
      · have : substWire k a r = r - 1 := by unfold substWire; split_ifs <;> omega
        simp only [Function.comp_apply, this]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    apply delete_inv k a ha gs _ _ (by simp; omega) (by simp; omega)
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    rw [hval]
    by_cases hi' : i < w1.length
    · have hs : substWire k a i < w2.length := by unfold substWire; split_ifs <;> omega
      rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ hi']
      exact h i hi'
    · have he : i = w1.length := by omega
      have hs : substWire k a i = w2.length := by unfold substWire; split_ifs <;> omega
      rw [hs, he]
      simp [List.getD_append_right]

theorem delete_run (m : ℕ) (C : Circuit) (j a : ℕ) (v : List Bool) (hv : v.length = m)
    (hj : j < C.gates.length) (ha : a < m + j)
    (heq : (run C.gates v).getD (m + j) false = (run C.gates v).getD a false) :
    ∀ i, (run (delete m C j a).gates v).getD (substWire (m + j) a i) false =
      (run C.gates v).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  set w2 := run (C.gates.take j) v with hw2
  have hl2 : w2.length = m + j := by rw [hw2, run_len, List.length_take]; omega
  set w1 := w2 ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => w2.getD i false)] with hw1
  have hall : run C.gates v = run (C.gates.drop (j + 1)) w1 := by
    conv_lhs => rw [hsplit]
    rw [run_app, run_cons]
  have hnew : run (delete m C j a).gates v =
      run ((C.gates.drop (j + 1)).map fun g => ⟨g.op, g.inputs.map (substWire (m + j) a)⟩) w2 := by
    simp only [delete]; rw [run_app]
  rw [hnew, hall]
  apply delete_inv (m + j) a ha _ w1 w2 (by simp [hw1]) (by simp [hw1, hl2])
  intro i hi
  by_cases hlt : i < m + j
  · have : substWire (m + j) a i = i := by unfold substWire; simp [hlt]
    rw [this, hw1, List.getD_append _ _ _ _ (by omega)]
  · have hie : i = m + j := by simp [hw1, hl2] at hi; omega
    have : substWire (m + j) a i = a := by unfold substWire; simp [hie]
    rw [this]
    have e1 : (run C.gates v).getD (m + j) false = w1.getD (m + j) false := by
      rw [hall, run_pre _ _ _ (by simp [hw1, hl2])]
    have e2 : (run C.gates v).getD a false = w1.getD a false := by
      rw [hall, run_pre _ _ _ (by simp [hw1, hl2]; omega)]
    rw [hie, ← e1, heq, e2, hw1, List.getD_append _ _ _ _ (by omega)]

theorem delete_fan (m : ℕ) (C : Circuit) (j a : ℕ) (h : FanInTwo C) : FanInTwo (delete m C j a) := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact h g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    obtain ⟨hop, hlen⟩ := h g0 (List.mem_of_mem_drop hg0)
    exact ⟨hop, by simpa using hlen⟩

theorem delete_size (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
    (delete m C j a).size = C.size - 1 := by
  simp only [delete, Circuit.size, List.length_append, List.length_take, List.length_map,
    List.length_drop]
  omega


-- The restricted input on nine wires and the eleven-wire input of the smaller circuit.
def U (x9 : Fin 8 → Bool) : List Bool := List.ofFn (Fin.insertNth (4 : Fin 9) false x9)

def V (x7 : Fin 8) (x9 : Fin 8 → Bool) : List Bool := List.ofFn x9 ++ [!x9 x7, true, false]

theorem U_len (x9 : Fin 8 → Bool) : (U x9).length = 9 := by simp [U]

theorem V_len (x7 : Fin 8) (x9 : Fin 8 → Bool) : (V x7 x9).length = 11 := by simp [V]

theorem UV_base (x7 : Fin 8) (x9 : Fin 8 → Bool) :
    ∀ i, (V x7 x9).getD (tau i) false = (U x9).getD i false := by
  intro i
  by_cases hi : i < 9
  · interval_cases i <;> simp [tau, inMap, U, V, Fin.insertNth, Fin.lt_def, Fin.castLT, List.getD_eq_getElem?_getD] <;> rfl
  · rw [List.getD_eq_default _ _ (by rw [V_len]; unfold tau; split_ifs <;> omega),
      List.getD_eq_default _ _ (by rw [U_len]; omega)]

theorem remap_wire (C : Circuit) (x7 : Fin 8) (x9 : Fin 8 → Bool) (i : ℕ) :
    (run (remap C).gates (V x7 x9)).getD (tau i) false = (run C.gates (U x9)).getD i false :=
  remap_run C.gates (U x9) (V x7 x9) (by simp [U_len]) (by simp [U_len, V_len]) (UV_base x7 x9) i

-- The old wire i after the remap and the first two deletions.
def rho (a1 i : ℕ) : ℕ := substWire 11 a1 (substWire 11 0 (tau i))

theorem rho_lt (a1 : ℕ) (ha1 : a1 < 11) (t y : ℕ) (ht : 2 ≤ t) (hy : y < 9 + t) : rho a1 y < 9 + t := by
  unfold rho substWire tau inMap; split_ifs <;> omega

-- After the remap, delete gate 0 (by wire 0) and then the old gate 1 (by wire a1).
def D2 (C : Circuit) (a1 : ℕ) : Circuit := delete 11 (delete 11 (remap C) 0 0) 0 a1

theorem D2_wire (C : Circuit) (hl : 2 ≤ C.gates.length) (x7 : Fin 8) (a1 : ℕ) (ha1 : a1 < 11)
    (h9 : ∀ x9, (run C.gates (U x9)).getD 9 false = (U x9).getD 0 false)
    (h1 : ∀ x9, (run C.gates (U x9)).getD 10 false = (V x7 x9).getD a1 false) (x9 : Fin 8 → Bool) :
    ∀ i, (run (D2 C a1).gates (V x7 x9)).getD (rho a1 i) false = (run C.gates (U x9)).getD i false := by
  have hrl : (remap C).gates.length = C.gates.length := by simp [remap]
  have hD1l : (delete 11 (remap C) 0 0).gates.length = C.gates.length - 1 := by
    have := delete_size 11 (remap C) 0 0 (by omega); simp [Circuit.size, hrl] at this; exact this
  have c1 : ∀ i, (run (delete 11 (remap C) 0 0).gates (V x7 x9)).getD (substWire 11 0 (tau i)) false =
      (run C.gates (U x9)).getD i false := by
    intro i
    rw [← remap_wire C x7 x9 i]
    apply delete_run 11 (remap C) 0 0 (V x7 x9) (V_len x7 x9) (by omega) (by omega)
    have e0 : (run (remap C).gates (V x7 x9)).getD 0 false = (run C.gates (U x9)).getD 0 false :=
      remap_wire C x7 x9 0
    have e9 : (run (remap C).gates (V x7 x9)).getD 11 false = (run C.gates (U x9)).getD 9 false :=
      remap_wire C x7 x9 9
    show (run (remap C).gates (V x7 x9)).getD 11 false = (run (remap C).gates (V x7 x9)).getD 0 false
    rw [e9, e0, h9 x9, run_pre _ _ _ (by simp [U_len])]
  intro i
  rw [← c1 i]
  apply delete_run 11 _ 0 a1 (V x7 x9) (V_len x7 x9) (by omega) (by omega)
  have e10 : (run (delete 11 (remap C) 0 0).gates (V x7 x9)).getD 11 false =
      (run C.gates (U x9)).getD 10 false := c1 10
  show (run (delete 11 (remap C) 0 0).gates (V x7 x9)).getD 11 false =
    (run (delete 11 (remap C) 0 0).gates (V x7 x9)).getD a1 false
  rw [e10, h1 x9, run_pre _ _ _ (by simp [V_len]; omega)]

theorem D2_size (C : Circuit) (hl : 2 ≤ C.gates.length) (a1 : ℕ) :
    (D2 C a1).gates.length = C.gates.length - 2 := by
  have hrl : (remap C).gates.length = C.gates.length := by simp [remap]
  have h1 := delete_size 11 (remap C) 0 0 (by omega)
  have h2 := delete_size 11 (delete 11 (remap C) 0 0) 0 a1 (by simp [Circuit.size] at h1; omega)
  simp only [Circuit.size, hrl] at h1 h2
  simp only [D2]; omega

theorem D2_fan (C : Circuit) (hC : FanInTwo C) (a1 : ℕ) : FanInTwo (D2 C a1) := by
  apply delete_fan; apply delete_fan
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
  obtain ⟨hop, hlen⟩ := hC g0 hg0
  exact ⟨hop, by simpa using hlen⟩

-- The third deletion: gate t by the wire a3 of D2 that carries the same value.
theorem three (C : Circuit) (hC : FanInTwo C) (hs : C.size ≤ 15) (x7 : Fin 8) (a1 : ℕ)
    (ha1 : a1 < 11) (t : ℕ) (ht : 2 ≤ t) (htl : t < C.gates.length) (a3 : ℕ) (ha3 : a3 < 9 + t)
    (h9 : ∀ x9, (run C.gates (U x9)).getD 9 false = (U x9).getD 0 false)
    (h1 : ∀ x9, (run C.gates (U x9)).getD 10 false = (V x7 x9).getD a1 false)
    (h3 : ∀ x9, (run C.gates (U x9)).getD (9 + t) false =
      (run (D2 C a1).gates (V x7 x9)).getD a3 false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 12 ∧ ∀ x9, D.eval (V x7 x9) = C.eval (U x9) := by
  have hl := D2_size C (by omega) a1
  refine ⟨delete 11 (D2 C a1) (t - 2) a3, delete_fan _ _ _ _ (D2_fan C hC a1), ?_, ?_⟩
  · have := delete_size 11 (D2 C a1) (t - 2) a3 (by omega)
    simp only [Circuit.size] at this hs ⊢
    omega
  · intro x9
    have c2 := D2_wire C (by omega) x7 a1 ha1 h9 h1 x9
    have key := delete_run 11 (D2 C a1) (t - 2) a3 (V x7 x9) (V_len x7 x9) (by omega) (by omega) (by
      have e := c2 (9 + t)
      have hr : rho a1 (9 + t) = 11 + (t - 2) := by unfold rho substWire tau; split_ifs <;> omega
      rw [hr] at e
      rw [e, h3 x9])
    have o2 : (run (D2 C a1).gates (V x7 x9)).getD (D2 C a1).output false =
        (run C.gates (U x9)).getD C.output false := by
      have := c2 C.output
      simpa [D2, delete, remap, rho] using this
    show (run (delete 11 (D2 C a1) (t - 2) a3).gates (V x7 x9)).getD
      (substWire (11 + (t - 2)) a3 (D2 C a1).output) false = _
    rw [key, o2]
    rfl

-- Two inputs that differ only on bad wires agree on every wire whose gate reads no bad wire.
theorem agree (C : Circuit) (hC : FanInTwo C) (y1 y2 : List Bool) (hl1 : y1.length = 9)
    (hl2 : y2.length = 9) (B : ℕ → Prop)
    (h9 : (run C.gates y1).getD 9 false = (run C.gates y2).getD 9 false)
    (hin : ∀ i < 9, ¬B i → y1.getD i false = y2.getD i false)
    (hg : ∀ k (hk : k < C.gates.length), 1 ≤ k → ¬B (9 + k) →
      ∀ r ∈ C.gates[k].inputs.take (bif C.gates[k].op.eval [false] then 1 else 2), ¬B r) :
    ∀ w, ¬B w → (run C.gates y1).getD w false = (run C.gates y2).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < 9
    · rw [run_pre _ _ _ (by omega), run_pre _ _ _ (by omega)]; exact hin w h1 hw
    by_cases he : w = 9
    · subst he; exact h9
    by_cases h2 : w < 9 + C.gates.length
    · have hk : w - 9 < C.gates.length := by omega
      have g1 := run_gate C.gates y1 (w - 9) hk
      have g2 := run_gate C.gates y2 (w - 9) hk
      rw [hl1] at g1; rw [hl2] at g2
      rw [show w = 9 + (w - 9) by omega, g1, g2]
      have hsame : ∀ r ∈ C.gates[w - 9].inputs.take (bif C.gates[w - 9].op.eval [false] then 1 else 2),
          (if r < 9 + (w - 9) then (run C.gates y1).getD r false else false) =
          (if r < 9 + (w - 9) then (run C.gates y2).getD r false else false) := by
        intro r hr
        have hb := hg (w - 9) hk (by omega) (by rw [show 9 + (w - 9) = w by omega]; exact hw) r hr
        split_ifs with hlt
        · exact ih r (by omega) hb
        · rfl
      obtain ⟨hop, hlen⟩ := hC _ (List.getElem_mem hk)
      generalize C.gates[w - 9] = g at hop hlen hsame
      obtain ⟨op, ins⟩ := g
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      simp only at hlen hsame ⊢
      rcases hop with rfl | rfl | rfl
      · simp only [show GateOp.and.eval [false] = false from rfl, cond_false,
          List.take_of_length_le hlen] at hsame
        rw [List.map_congr_left hsame]
      · simp only [show GateOp.or.eval [false] = false from rfl, cond_false,
          List.take_of_length_le hlen] at hsame
        rw [List.map_congr_left hsame]
      · simp only [show GateOp.not.eval [false] = true from rfl, cond_true] at hsame
        match ins, hsame with
        | [], _ => rfl
        | r :: rs, hs =>
          simp only [GateOp.eval, List.map_cons, List.headD_cons]
          rw [hs r (by simp)]
    · rw [run_high _ _ _ (by omega), run_high _ _ _ (by omega)]


theorem V8 (x7 : Fin 8) (x9 : Fin 8 → Bool) : (V x7 x9).getD 8 false = !x9 x7 := by simp [V]
theorem V9 (x7 : Fin 8) (x9 : Fin 8 → Bool) : (V x7 x9).getD 9 false = true := by simp [V]
theorem V10 (x7 : Fin 8) (x9 : Fin 8 → Bool) : (V x7 x9).getD 10 false = false := by simp [V]

theorem Uget (x7 : Fin 8) (x9 : Fin 8 → Bool) (r : ℕ) (hr : r < 9) (h4 : r ≠ 4) :
    (U x9).getD r false = x9 ⟨tau r, by unfold tau inMap; split_ifs <;> omega⟩ := by
  rw [← UV_base x7 x9 r]
  have ht : tau r < 8 := by unfold tau inMap; split_ifs <;> omega
  show (List.ofFn x9 ++ [!x9 x7, true, false]).getD (tau r) false = _
  rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact ht),
    List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact ht), List.getElem_ofFn]

theorem U4 (x9 : Fin 8 → Bool) : (U x9).getD 4 false = false := by
  rw [← UV_base 0 x9 4]; exact V10 0 x9

theorem gval (C : Circuit) (x9 : Fin 8 → Bool) (k : ℕ) (hk : k < C.gates.length) :
    (run C.gates (U x9)).getD (9 + k) false = C.gates[k].op.eval (C.gates[k].inputs.map fun r =>
      if r < 9 + k then (run C.gates (U x9)).getD r false else false) := by
  have := run_gate C.gates (U x9) k hk; rw [U_len] at this; exact this

-- Gate 1 is an inverter; after x_4 is fixed it is a free literal or true.
theorem gate1 (C : Circuit) (hl : 2 ≤ C.gates.length) (hop : C.gates[1].op = GateOp.not)
    (h9 : ∀ x9, (run C.gates (U x9)).getD 9 false = (U x9).getD 0 false) :
    ∃ x7 : Fin 8, ∃ a1, a1 < 11 ∧ ∀ x9, (run C.gates (U x9)).getD 10 false = (V x7 x9).getD a1 false := by
  have g := fun x9 => gval C x9 1 (by omega)
  rw [hop] at g
  match hins : C.gates[1].inputs with
  | [] => exact ⟨0, 9, by omega, fun x9 => by rw [g x9, hins, V9]; rfl⟩
  | r :: rs =>
    simp only [hins, GateOp.eval, List.map_cons, List.headD_cons] at g
    by_cases hr10 : r < 10
    · by_cases hr9 : r = 9
      · subst hr9
        refine ⟨0, 8, by omega, fun x9 => ?_⟩
        rw [g x9, if_pos (by omega), h9 x9, V8, Uget 0 x9 0 (by omega) (by omega)]
        rfl
      · by_cases hr4 : r = 4
        · subst hr4
          refine ⟨0, 9, by omega, fun x9 => ?_⟩
          rw [g x9, if_pos (by omega), run_pre _ _ _ (by rw [U_len]; omega), U4, V9]; rfl
        · refine ⟨⟨tau r, by unfold tau inMap; split_ifs <;> omega⟩, 8, by omega, fun x9 => ?_⟩
          rw [g x9, if_pos (by omega), run_pre _ _ _ (by rw [U_len]; omega), V8,
            Uget 0 x9 r (by omega) hr4]
    · refine ⟨0, 9, by omega, fun x9 => ?_⟩
      rw [g x9, if_neg (by omega), V9]; rfl

-- The third gate: a constant wire of the eleven inputs, or an earlier old wire.
theorem third_const (C : Circuit) (x7 : Fin 8) (a1 t c : ℕ) (ht : 2 ≤ t) (hc : c < 11)
    (h : ∀ x9, (run C.gates (U x9)).getD (9 + t) false = (V x7 x9).getD c false) :
    ∃ a3, a3 < 9 + t ∧ ∀ x9, (run C.gates (U x9)).getD (9 + t) false =
      (run (D2 C a1).gates (V x7 x9)).getD a3 false :=
  ⟨c, by omega, fun x9 => by rw [h x9, run_pre _ _ _ (by rw [V_len]; omega)]⟩

theorem third_old (C : Circuit) (hl : 2 ≤ C.gates.length) (x7 : Fin 8) (a1 : ℕ) (ha1 : a1 < 11)
    (t y : ℕ) (ht : 2 ≤ t) (hy : y < 9 + t)
    (h9 : ∀ x9, (run C.gates (U x9)).getD 9 false = (U x9).getD 0 false)
    (h1 : ∀ x9, (run C.gates (U x9)).getD 10 false = (V x7 x9).getD a1 false)
    (h : ∀ x9, (run C.gates (U x9)).getD (9 + t) false = (run C.gates (U x9)).getD y false) :
    ∃ a3, a3 < 9 + t ∧ ∀ x9, (run C.gates (U x9)).getD (9 + t) false =
      (run (D2 C a1).gates (V x7 x9)).getD a3 false :=
  ⟨rho a1 y, rho_lt a1 ha1 t y ht hy, fun x9 => by rw [h x9, D2_wire C hl x7 a1 ha1 h9 h1 x9 y]⟩


-- A gate that reads a wire with a known constant value on U becomes a constant or a copy.
theorem third (C : Circuit) (hC : FanInTwo C) (hl : 2 ≤ C.gates.length) (x7 : Fin 8) (a1 : ℕ)
    (ha1 : a1 < 11) (t : ℕ) (ht : 2 ≤ t) (htl : t < C.gates.length) (z : ℕ) (hz : z < 9 + t)
    (cz : Bool) (hcz : ∀ x9, (run C.gates (U x9)).getD z false = cz)
    (hread : z ∈ C.gates[t].inputs.take (bif C.gates[t].op.eval [false] then 1 else 2))
    (h9 : ∀ x9, (run C.gates (U x9)).getD 9 false = (U x9).getD 0 false)
    (h1 : ∀ x9, (run C.gates (U x9)).getD 10 false = (V x7 x9).getD a1 false) :
    ∃ a3, a3 < 9 + t ∧ ∀ x9, (run C.gates (U x9)).getD (9 + t) false =
      (run (D2 C a1).gates (V x7 x9)).getD a3 false := by
  have g := fun x9 => gval C x9 t htl
  have cst : ∀ b : Bool, (∀ x9, (run C.gates (U x9)).getD (9 + t) false = b) →
      ∃ a3, a3 < 9 + t ∧ ∀ x9, (run C.gates (U x9)).getD (9 + t) false =
        (run (D2 C a1).gates (V x7 x9)).getD a3 false := by
    intro b hb
    cases b
    · exact third_const C x7 a1 t 10 ht (by omega) (fun x9 => by rw [hb x9, V10])
    · exact third_const C x7 a1 t 9 ht (by omega) (fun x9 => by rw [hb x9, V9])
  have old : ∀ y, y < 9 + t → (∀ x9, (run C.gates (U x9)).getD (9 + t) false =
      (run C.gates (U x9)).getD y false) →
      ∃ a3, a3 < 9 + t ∧ ∀ x9, (run C.gates (U x9)).getD (9 + t) false =
        (run (D2 C a1).gates (V x7 x9)).getD a3 false :=
    fun y hy h => third_old C hl x7 a1 ha1 t y ht hy h9 h1 h
  obtain ⟨hop, hlen⟩ := hC _ (List.getElem_mem htl)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  generalize hg : C.gates[t] = gt at g hop hlen hread
  obtain ⟨op, ins⟩ := gt
  simp only at g hop hlen hread
  have F : ∀ x9, (if z < 9 + t then (run C.gates (U x9)).getD z false else false) = cz := by
    intro x9; rw [if_pos hz, hcz]
  rcases hop with rfl | rfl | rfl
  · -- AND reading z
    simp only [show GateOp.and.eval [false] = false from rfl, cond_false,
      List.take_of_length_le hlen] at hread
    match ins, hlen, hread with
    | [r], _, hr =>
      simp only [List.mem_singleton] at hr; subst hr
      exact cst cz (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9])
    | [r, r'], _, hr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · cases cz
        · exact cst false (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9])
        · by_cases hr' : r' < 9 + t
          · exact old r' hr' (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9, if_pos hr'])
          · exact cst false (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9, if_neg hr'])
      · cases cz
        · exact cst false (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9])
        · by_cases hr' : r < 9 + t
          · exact old r hr' (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9, if_pos hr'])
          · exact cst false (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9, if_neg hr'])
  · -- OR reading z
    simp only [show GateOp.or.eval [false] = false from rfl, cond_false,
      List.take_of_length_le hlen] at hread
    match ins, hlen, hread with
    | [r], _, hr =>
      simp only [List.mem_singleton] at hr; subst hr
      exact cst cz (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9])
    | [r, r'], _, hr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · cases cz
        · by_cases hr' : r' < 9 + t
          · exact old r' hr' (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9, if_pos hr'])
          · exact cst false (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9, if_neg hr'])
        · exact cst true (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9])
      · cases cz
        · by_cases hr' : r < 9 + t
          · exact old r hr' (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9, if_pos hr'])
          · exact cst false (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9, if_neg hr'])
        · exact cst true (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9])
  · -- NOT reading z
    simp only [show GateOp.not.eval [false] = true from rfl, cond_true] at hread
    match ins, hread with
    | r :: rs, hr =>
      simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hr; subst hr
      exact cst (!cz) (fun x9 => by rw [g x9]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, F x9])

theorem main (C : Circuit) (hC : FanInTwo C)
    (h9w : ∀ x3 : Fin 9 → Bool, (C.wires (List.ofFn x3)).getD 9 false = (x3 0 || x3 4))
    (h1op : Option.map Gate.op C.gates[1]? = some GateOp.not) (hs : C.size ≤ 15)
    (hsens : C.eval [true, false, false, false, true, false, false, false, false] ≠
      C.eval [true, false, false, false, false, false, false, false, false]) :
    ∃ (x7 : Fin 8) (D : Circuit), FanInTwo D ∧ D.size ≤ 12 ∧ ∀ x9, D.eval (V x7 x9) = C.eval (U x9) := by
  have hl : 2 ≤ C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at h1op
    simp at h1op
  have hop1 : C.gates[1].op = GateOp.not := by
    rw [List.getElem?_eq_getElem (by omega)] at h1op
    simpa using h1op
  have h9 : ∀ x9, (run C.gates (U x9)).getD 9 false = (U x9).getD 0 false := by
    intro x9
    have e := h9w (Fin.insertNth (4 : Fin 9) false x9)
    simp only [Fin.insertNth_apply_same, Bool.or_false] at e
    show (C.wires (List.ofFn _)).getD 9 false = _
    rw [e]
    simp [U]
  have W4 : ∀ x9, (run C.gates (U x9)).getD 4 false = false := fun x9 => by
    rw [run_pre _ _ _ (by rw [U_len]; omega), U4]
  have triv : ∀ c : ℕ, c < 11 → (∀ x9, (V 0 x9).getD c false = C.eval (U x9)) →
      ∃ (x7 : Fin 8) (D : Circuit), FanInTwo D ∧ D.size ≤ 12 ∧ ∀ x9, D.eval (V x7 x9) = C.eval (U x9) :=
    fun c _ h => ⟨0, ⟨[], c⟩, fun g hg => by simp at hg, by simp [Circuit.size],
      fun x9 => by rw [← h x9]; rfl⟩
  -- The two inputs of the hypothesis agree off wire 4 and on wire 9.
  let y1 := [true, false, false, false, true, false, false, false, false]
  let y2 := [true, false, false, false, false, false, false, false, false]
  have hy9 : (run C.gates y1).getD 9 false = (run C.gates y2).getD 9 false := by
    have a := h9w (fun i => y1.getD i false)
    have b := h9w (fun i => y2.getD i false)
    have ea : List.ofFn (fun i : Fin 9 => y1.getD i false) = y1 := by decide
    have eb : List.ofFn (fun i : Fin 9 => y2.getD i false) = y2 := by decide
    rw [ea] at a; rw [eb] at b
    show (C.wires y1).getD 9 false = (C.wires y2).getD 9 false
    rw [a, b]; decide
  have hin : ∀ (B : ℕ → Prop), B 4 → ∀ i < 9, ¬B i → y1.getD i false = y2.getD i false := by
    intro B hB4 i hi hb
    by_cases h4 : i = 4
    · subst h4; exact absurd hB4 hb
    · interval_cases i <;> first | rfl | (exfalso; exact h4 rfl)
  by_cases hA : ∃ t, 2 ≤ t ∧ ∃ ht : t < C.gates.length,
      4 ∈ C.gates[t].inputs.take (bif C.gates[t].op.eval [false] then 1 else 2)
  · obtain ⟨t, ht2, htl, h4⟩ := hA
    obtain ⟨x7, a1, ha1, h1⟩ := gate1 C hl hop1 h9
    obtain ⟨a3, ha3, h3⟩ := third C hC hl x7 a1 ha1 t ht2 htl 4 (by omega) false W4 h4 h9 h1
    obtain ⟨D, hD⟩ := three C hC hs x7 a1 ha1 t ht2 htl a3 ha3 h9 h1 h3
    exact ⟨x7, D, hD⟩
  push_neg at hA
  by_cases ho4 : C.output = 4
  · exact triv 10 (by omega) (fun x9 => by
      rw [V10]; show false = (run C.gates (U x9)).getD C.output false; rw [ho4, W4])
  by_cases hg1 : 4 ∈ C.gates[1].inputs.take 1
  · have h1v : ∀ x9, (run C.gates (U x9)).getD 10 false = true := by
      intro x9
      have g := gval C x9 1 (by omega)
      rw [hop1] at g
      match hins : C.gates[1].inputs, hg1 with
      | r :: rs, hr =>
        simp only [hins, List.take_succ_cons, List.take_zero, List.mem_singleton] at hr
        subst hr
        rw [g, hins]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or, List.headD_cons, Bool.not_false, Bool.not_true, if_pos (show 4 < 9 + 1 by omega), W4]
    have h1 : ∀ x9, (run C.gates (U x9)).getD 10 false = (V 0 x9).getD 9 false :=
      fun x9 => by rw [h1v, V9]
    by_cases ho10 : C.output = 10
    · exact triv 9 (by omega) (fun x9 => by
        rw [V9]; show true = (run C.gates (U x9)).getD C.output false; rw [ho10, h1v])
    by_cases hB : ∃ h, 2 ≤ h ∧ ∃ hh : h < C.gates.length,
        10 ∈ C.gates[h].inputs.take (bif C.gates[h].op.eval [false] then 1 else 2)
    · obtain ⟨h, hh2, hhl, h10⟩ := hB
      obtain ⟨a3, ha3, h3⟩ := third C hC hl 0 9 (by omega) h hh2 hhl 10 (by omega) true h1v h10 h9 h1
      obtain ⟨D, hD⟩ := three C hC hs 0 9 (by omega) h hh2 hhl a3 ha3 h9 h1 h3
      exact ⟨0, D, hD⟩
    · exfalso
      push_neg at hB
      apply hsens
      have := agree C hC y1 y2 rfl rfl (fun w => w = 4 ∨ w = 10) hy9
        (fun i hi hb => hin (fun w => w = 4 ∨ w = 10) (Or.inl rfl) i hi hb)
        (fun k hk hk1 hb r hr => by
          rintro (rfl | rfl)
          · by_cases hk2 : 2 ≤ k
            · exact hA k hk2 hk hr
            · have : k = 1 := by omega
              subst this; exact hb (Or.inr rfl)
          · by_cases hk2 : 2 ≤ k
            · exact hB k hk2 hk hr
            · have : k = 1 := by omega
              subst this; exact hb (Or.inr rfl))
        C.output (by rintro (h | h) <;> contradiction)
      exact this
  · exfalso
    apply hsens
    have := agree C hC y1 y2 rfl rfl (fun w => w = 4) hy9
      (fun i hi hb => hin (fun w => w = 4) rfl i hi hb)
      (fun k hk hk1 hb r hr => by
        rintro rfl
        by_cases hk2 : 2 ≤ k
        · exact hA k hk2 hk hr
        · have : k = 1 := by omega
          subst this
          simp only [hop1, show GateOp.not.eval [false] = true from rfl, cond_true] at hr
          exact hg1 hr)
      C.output ho4
    exact this

end PEqualNP.Outside.L_meta_3141

theorem PEqualNP.Outside.L_meta_3141 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → Option.map PEqualNP.CircuitLowerBounds.Gate.op x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → x1.size ≤ (15 : ℕ) → x1.eval [Bool.true, Bool.false, Bool.false, Bool.false, Bool.true, Bool.false, Bool.false, Bool.false, Bool.false] ≠ x1.eval [Bool.true, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false] → ∃ (x7 : Fin (8 : ℕ)) (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size ≤ (12 : ℕ) ∧ ∀ (x9 : Fin (8 : ℕ) → Bool), x8.eval (List.ofFn x9 ++ [!x9 x7, Bool.true, Bool.false]) = x1.eval (List.ofFn (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.false x9)) := by
  intro C hC h9 h1 hs hsens
  exact PEqualNP.Outside.L_meta_3141.main C hC h9 h1 hs hsens
