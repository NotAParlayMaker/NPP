import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1586

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlen]
    exact getD_append_left_lt w _ i hi

lemma wires_eq_foldl (gates : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gates, o⟩ x = gates.foldl step x := rfl

lemma eval_input_lt (gates : List Gate) (N : ℕ) (f : Fin N → Bool) (p : Fin N) :
    Circuit.eval ⟨gates, p.val⟩ (List.ofFn f) = f p := by
  unfold Circuit.eval
  rw [wires_eq_foldl]
  have hlt : p.val < (List.ofFn f).length := by simp
  rw [foldl_step_getD_lt gates (List.ofFn f) p.val hlt]
  simp [List.getD_eq_getElem?_getD]

lemma eval_ge_len (gates : List Gate) (N : ℕ) (f : Fin N → Bool) (w : ℕ)
    (hw : N + gates.length ≤ w) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn f) = false := by
  unfold Circuit.eval
  rw [wires_eq_foldl]
  apply getD_ge_len
  rw [foldl_step_len, List.length_ofFn]
  exact hw

lemma eval_gate (gates : List Gate) (x : List Bool) (i : Fin gates.length)
    (hacyc : ∀ a ∈ (gates.get i).inputs, a < x.length + i.val) :
    Circuit.eval ⟨gates, x.length + i.val⟩ x =
      (gates.get i).op.eval
        ((gates.get i).inputs.map fun a => Circuit.eval ⟨gates, a⟩ x) := by
  unfold Circuit.eval
  rw [wires_eq_foldl]
  have hsplit : gates = gates.take i.val ++ gates.get i :: gates.drop (i.val + 1) := by
    have h1 := List.take_append_drop i.val gates
    have h2 : gates.drop i.val = gates.get i :: gates.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons i.isLt]
      rfl
    rw [h2] at h1
    exact h1.symm
  set pref := (gates.take i.val).foldl step x with hpref_def
  have hpref_len : pref.length = x.length + i.val := by
    rw [hpref_def, foldl_step_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  have hfold : gates.foldl step x = (gates.drop (i.val + 1)).foldl step (step pref (gates.get i)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons, ← hpref_def]
  have hlt_step : x.length + i.val < (step pref (gates.get i)).length := by
    simp only [step, List.length_append, List.length_cons, List.length_nil, hpref_len]
    omega
  rw [hfold, foldl_step_getD_lt _ _ _ hlt_step]
  have hself : (step pref (gates.get i)).getD (x.length + i.val) false =
      (gates.get i).op.eval ((gates.get i).inputs.map fun a => pref.getD a false) := by
    rw [← hpref_len]
    exact getD_append_self pref _
  rw [hself]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < pref.length := by
    rw [hpref_len]
    exact hacyc a ha
  have ha_eq : (gates.foldl step x).getD a false = pref.getD a false := by
    rw [hfold]
    have ha_lt2 : a < (step pref (gates.get i)).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [foldl_step_getD_lt _ _ _ ha_lt2]
    exact getD_append_left_lt pref _ a halt
  exact ha_eq.symm

lemma eval_or_false_imp (gates : List Gate) (x : List Bool) (i : Fin gates.length)
    (hop : (gates.get i).op = GateOp.or)
    (hacyc : ∀ a ∈ (gates.get i).inputs, a < x.length + i.val)
    (hfalse : Circuit.eval ⟨gates, x.length + i.val⟩ x = false)
    (a : ℕ) (ha : a ∈ (gates.get i).inputs) :
    Circuit.eval ⟨gates, a⟩ x = false := by
  rw [eval_gate gates x i hacyc, hop] at hfalse
  simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq] at hfalse
  have h1 := hfalse (Circuit.eval ⟨gates, a⟩ x) ⟨a, ha, rfl⟩
  cases hb : Circuit.eval ⟨gates, a⟩ x
  · rfl
  · exact absurd hb h1

lemma eval_or_true_imp (gates : List Gate) (x : List Bool) (i : Fin gates.length)
    (hop : (gates.get i).op = GateOp.or)
    (hacyc : ∀ a ∈ (gates.get i).inputs, a < x.length + i.val)
    (htrue : Circuit.eval ⟨gates, x.length + i.val⟩ x = true) :
    ∃ a ∈ (gates.get i).inputs, Circuit.eval ⟨gates, a⟩ x = true := by
  rw [eval_gate gates x i hacyc, hop] at htrue
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at htrue
  obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := htrue
  exact ⟨a, ha, hb⟩

lemma eval_and_true_imp (gates : List Gate) (x : List Bool) (i : Fin gates.length)
    (hop : (gates.get i).op = GateOp.and)
    (hacyc : ∀ a ∈ (gates.get i).inputs, a < x.length + i.val)
    (htrue : Circuit.eval ⟨gates, x.length + i.val⟩ x = true)
    (c : ℕ) (hc : c ∈ (gates.get i).inputs) :
    Circuit.eval ⟨gates, c⟩ x = true := by
  rw [eval_gate gates x i hacyc, hop] at htrue
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at htrue
  exact htrue (Circuit.eval ⟨gates, c⟩ x) ⟨c, hc, rfl⟩

def InOrTop (N : ℕ) (gates : List Gate) (u Y : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S →
    (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or →
      ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S

lemma inOrTop_self (N : ℕ) (gates : List Gate) (u : ℕ) :
    InOrTop N gates u u :=
  fun _ hu _ => hu

lemma inOrTop_step (N : ℕ) (gates : List Gate) (u : ℕ) (i : Fin gates.length) (a : ℕ)
    (hmem : InOrTop N gates u (N + i.val))
    (hop : (gates.get i).op = GateOp.or)
    (ha : a ∈ (gates.get i).inputs) :
    InOrTop N gates u a :=
  fun S hu hcl => hcl i (hmem S hu hcl) hop a ha

lemma part1 (N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N)
    (gates : List Gate) (u : ℕ)
    (hacyc : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (hfalse : Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false)
    (Y : ℕ) (hY : InOrTop N gates u Y) :
    Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false := by
  let x0 := List.ofFn (fun v : Fin N => decide (v ∉ L i0))
  have hx0_len : x0.length = N := List.length_ofFn
  exact hY {w : ℕ | Circuit.eval ⟨gates, w⟩ x0 = false} hfalse (fun i hi hop a ha => by
    have hi' : Circuit.eval ⟨gates, x0.length + i.val⟩ x0 = false := by rw [hx0_len]; exact hi
    have hacyc' : ∀ b ∈ (gates.get i).inputs, b < x0.length + i.val := by
      rw [hx0_len]; exact (hacyc i).2
    exact eval_or_false_imp gates x0 i hop hacyc' hi' a ha)

lemma part2 (N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N)
    (gates : List Gate) (u : ℕ)
    (hacyc : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (hfalse : Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false)
    (p : Fin N) (hp : InOrTop N gates u p.val) :
    p ∈ L i0 := by
  have hf := part1 N L i0 gates u hacyc hfalse p.val hp
  rw [eval_input_lt] at hf
  by_contra hnot
  simp [hnot] at hf

lemma part3_aux (N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N)
    (gates : List Gate) (u : ℕ) (r : Fin N)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hacyc : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ))
    (hfalse : Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false)
    (w : ℕ) :
    InOrTop N gates u w →
    Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
    InOrTop N gates u r.val ∨
      ∃ a : ℕ, InOrTop N gates u a ∧
        (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
        Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hltN : w < N
    · let p : Fin N := ⟨w, hltN⟩
      have hpL : p ∈ L i0 := part2 N L i0 gates u hacyc hfalse p hw
      have hev : Circuit.eval ⟨gates, p.val⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true := htrue
      rw [eval_input_lt] at hev
      simp only [decide_eq_true_eq] at hev
      rcases hev with hnot | hpr
      · exact absurd hpL hnot
      · left
        have hwr : w = r.val := by rw [← hpr]
        rwa [← hwr]
    · by_cases hltG : w < N + gates.length
      · let i : Fin gates.length := ⟨w - N, by omega⟩
        have hwi : w = N + i.val := by simp [i]; omega
        have hmem : gates.get i ∈ gates := List.get_mem gates i
        rcases (hgates (gates.get i) hmem).1 with hand | hor
        · right
          exact ⟨w, hw, ⟨i, hwi, hand⟩, htrue⟩
        · let xr := List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))
          have hxr_len : xr.length = N := List.length_ofFn
          have htrue' : Circuit.eval ⟨gates, xr.length + i.val⟩ xr = true := by
            rw [hxr_len, ← hwi]; exact htrue
          have hacyc' : ∀ b ∈ (gates.get i).inputs, b < xr.length + i.val := by
            rw [hxr_len]; exact (hacyc i).2
          obtain ⟨c, hc_in, hc_true⟩ := eval_or_true_imp gates xr i hor hacyc' htrue'
          have hclt : c < w := by
            rw [hwi]
            exact (hacyc i).2 c hc_in
          have hcw : InOrTop N gates u (N + i.val) := by rw [← hwi]; exact hw
          have hc_top : InOrTop N gates u c := inOrTop_step N gates u i c hcw hor hc_in
          exact ih c hclt hc_top hc_true
      · have hge : N + gates.length ≤ w := by omega
        have hf := eval_ge_len gates N (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) w hge
        rw [hf] at htrue
        exact absurd htrue (by decide)

end PEqualNP.Outside.L_meta_1586

theorem PEqualNP.Outside.L_meta_1586 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ _ _ gates u hgates hacyc hfalse
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y hY
    exact PEqualNP.Outside.L_meta_1586.part1 N L i0 gates u hacyc hfalse Y hY
  · intro p hp
    exact PEqualNP.Outside.L_meta_1586.part2 N L i0 gates u hacyc hfalse p hp
  · intro r _ htrue
    exact PEqualNP.Outside.L_meta_1586.part3_aux N L i0 gates u r hgates hacyc hfalse u
      (PEqualNP.Outside.L_meta_1586.inOrTop_self N gates u) htrue
  · intro a c hand _ hc _ r _ htrue
    let xr := List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))
    have hxr_len : xr.length = N := List.length_ofFn
    have htrue' : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, xr.length + a.val⟩ xr = true := by
      rw [hxr_len]; exact htrue
    have hacyc' : ∀ b ∈ (gates.get a).inputs, b < xr.length + a.val := by
      rw [hxr_len]; exact (hacyc a).2
    exact PEqualNP.Outside.L_meta_1586.eval_and_true_imp gates xr a hand hacyc' htrue' c hc
