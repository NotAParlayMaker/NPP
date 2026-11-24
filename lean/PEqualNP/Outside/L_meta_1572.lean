import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1572

open PEqualNP.CircuitLowerBounds

def stepW (W : List Bool) (g : Gate) : List Bool :=
  W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

def run (gs : List Gate) (W : List Bool) : List Bool := gs.foldl stepW W

theorem run_append (gs gs' : List Gate) (W : List Bool) :
    run (gs ++ gs') W = run gs' (run gs W) := by
  simp [run, List.foldl_append]

theorem run_prefix (gs : List Gate) : ∀ W : List Bool,
    ∃ t : List Bool, run gs W = W ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro W; exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    intro W
    obtain ⟨t, ht, hl⟩ := ih (stepW W g)
    refine ⟨g.op.eval (g.inputs.map fun i => W.getD i false) :: t, ?_, by simp [hl]⟩
    have e : run (g :: gs) W = run gs (stepW W g) := rfl
    rw [e, ht]; simp [stepW]

theorem run_length (gs : List Gate) (W : List Bool) :
    (run gs W).length = W.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs W
  rw [ht]; simp [hl]

theorem run_getD_lt (gs : List Gate) (W : List Bool) (i : ℕ) (h : i < W.length) :
    (run gs W).getD i false = W.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs W
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem run_getD_ge (gs : List Gate) (W : List Bool) (i : ℕ) (h : W.length + gs.length ≤ i) :
    (run gs W).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [run_length]; exact h

theorem run_snoc (gs : List Gate) (g : Gate) (W : List Bool) :
    run (gs ++ [g]) W = stepW (run gs W) g := by
  rw [run_append]; rfl

def gateAt (gates : List Gate) (i : ℕ) : Gate := gates.getD i ⟨GateOp.and, []⟩

theorem old_gate (gates : List Gate) (x' : List Bool) (i : ℕ) (hi : i < gates.length) :
    (run gates x').getD (x'.length + i) false =
      (gateAt gates i).op.eval ((gateAt gates i).inputs.map fun q => (run (gates.take i) x').getD q false) := by
  have e1 : gates = gates.take (i + 1) ++ gates.drop (i + 1) := (List.take_append_drop _ _).symm
  have e2 : gates.take (i + 1) = gates.take i ++ [gateAt gates i] := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hi, List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  have hlen : (run (gates.take i) x').length = x'.length + i := by
    rw [run_length, List.length_take]; congr 1; omega
  conv => lhs; rw [e1, run_append]
  rw [run_getD_lt _ _ _ (by rw [run_length, List.length_take]; omega), e2, run_snoc]
  unfold stepW
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
  simp

theorem old_take (gates : List Gate) (x' : List Bool) (i q : ℕ) (hi : i ≤ gates.length) :
    (run (gates.take i) x').getD q false = if q < x'.length + i then (run gates x').getD q false else false := by
  have hlen : (run (gates.take i) x').length = x'.length + i := by
    rw [run_length, List.length_take]; congr 1; omega
  split_ifs with hq
  · rw [show run gates x' = run (gates.drop i) (run (gates.take i) x') by
      rw [← run_append, List.take_append_drop]]
    rw [run_getD_lt (gates.drop i) _ q (by omega)]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem gateAt_get (gates : List Gate) (i : Fin gates.length) : gateAt gates i.val = gates.get i := by
  unfold gateAt; rw [List.getD_eq_getElem _ _ i.isLt]; rfl

abbrev E (gates : List Gate) (w : ℕ) (f : Fin 13 → Bool) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn f)

theorem E_eq (gates : List Gate) (w : ℕ) (f : Fin 13 → Bool) :
    E gates w f = (run gates (List.ofFn f)).getD w false := rfl

theorem E_gate (gates : List Gate) (hlt : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (i : Fin gates.length) (f : Fin 13 → Bool) :
    E gates (13 + (i : ℕ)) f = (gates.get i).op.eval ((gates.get i).inputs.map fun a => E gates a f) := by
  have h := old_gate gates (List.ofFn f) i.val i.isLt
  rw [List.length_ofFn, gateAt_get] at h
  rw [E_eq, h]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [old_take _ _ _ _ (le_of_lt i.isLt), List.length_ofFn]
  simp only [hlt i a ha, ↓reduceIte]
  rfl

theorem E_input (gates : List Gate) (w : ℕ) (hw : w < 13) (f : Fin 13 → Bool) :
    E gates w f = f ⟨w, hw⟩ := by
  rw [E_eq, run_getD_lt _ _ _ (by simpa using hw), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hw]

theorem E_big (gates : List Gate) (w : ℕ) (hw : 13 + gates.length ≤ w) (f : Fin 13 → Bool) :
    E gates w f = false := by
  rw [E_eq, run_getD_ge _ _ _ (by simpa using hw)]

def Reach (gates : List Gate) (u Y : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S

theorem descend (gates : List Gate)
    (hop : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hlt : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ))
    (u B : ℕ) (x xl xm : Fin 13 → Bool) : ∀ w : ℕ, Reach gates u w → w < B →
    E gates w x = true → E gates w xl = false → E gates w xm = false →
    (∃ w' : Fin 13, x w' = true ∧ xl w' = false ∧ xm w' = false) ∨
    ∃ Y : ℕ, Reach gates u Y ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧ Y < B ∧
      E gates Y xl = false ∧ E gates Y xm = false ∧ E gates Y x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hR hB hx hl hm
    by_cases h13 : w < 13
    · left
      refine ⟨⟨w, h13⟩, ?_, ?_, ?_⟩
      · rw [E_input gates w h13 x] at hx; exact hx
      · rw [E_input gates w h13 xl] at hl; exact hl
      · rw [E_input gates w h13 xm] at hm; exact hm
    · by_cases hbig : 13 + gates.length ≤ w
      · rw [E_big gates w hbig] at hx; exact absurd hx (by simp)
      · let i : Fin gates.length := ⟨w - 13, by omega⟩
        have hw : w = 13 + (i : ℕ) := by simp [i]; omega
        rcases (hop (gates.get i) (List.get_mem _ _)).1 with ha | ho
        · right
          exact ⟨w, hR, ⟨i, hw, ha⟩, hB, hl, hm, hx⟩
        · rw [hw, E_gate gates hlt i, ho] at hx hl hm
          simp only [GateOp.eval, List.any_eq_true, List.any_eq_false, List.mem_map, id] at hx hl hm
          obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hx
          have hal : a < w := by have := hlt i a ha; omega
          have hR' : Reach gates u a := by
            intro S hu hS
            exact hS i (hw ▸ hR S hu hS) ho a ha
          have hla : E gates a xl = false := by
            cases h : E gates a xl
            · rfl
            · exact absurd (hl _ ⟨a, ha, h⟩) (by simp)
          have hma : E gates a xm = false := by
            cases h : E gates a xm
            · rfl
            · exact absurd (hm _ ⟨a, ha, h⟩) (by simp)
          exact ih a hal hR' (by omega) hb hla hma

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (run gs U).getD i false = true → (run gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [run, stepW] using this

theorem up (gates : List Gate) (g : ℕ)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin 13 → Bool) (hxy : ∀ v, x v = true → y v = true)
    (h : Circuit.eval ⟨gates, g⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, g⟩ (List.ofFn y) = true := by
  change E gates g x = true at h
  change E gates g y = true
  rw [E_eq] at h ⊢
  exact mono2 gates hleg _ _ (by simp) (ofFn_mono 13 x y hxy) g h

theorem one_notin : ∀ l : Fin 13, l ∈ ({4, 10, 12} : Finset (Fin 13)) →
    (1 : Fin 13) ∉ ({l, l + 1, l + 3, l + 9} : Finset (Fin 13)) := by decide

theorem zero_notin : ∀ m : Fin 13, m ∈ ({1, 5, 11} : Finset (Fin 13)) →
    (0 : Fin 13) ∉ ({m, m + 1, m + 3, m + 9} : Finset (Fin 13)) := by decide

theorem main : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gates g l m c hop hin hl hm hc hul hum
  have hlt : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ) :=
    fun i a ha => (hin i).2 a ha
  have h1l : (1 : Fin 13) ∉ L l := by rw [hL]; exact one_notin l hl
  have h0m : (0 : Fin 13) ∉ L m := by rw [hL]; exact zero_notin m hm
  have hR : Reach gates g g := fun S hu _ => hu
  constructor
  · intro hcard
    set Alive := (L l).filter (fun p =>
      Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)
      with hAlive_def
    have hcardA : 2 ≤ Alive.card := by simpa [Alive, hAlive_def] using hcard
    have no0 : ∀ p ∈ Alive, p ≠ 0 := by
      intro p hp
      intro hp0
      subst hp0
      have htrue : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = (0 : Fin 13) ∨ ((0 : Fin 13) ≠ 0 ∧ v = 1)))) = true :=
        (Finset.mem_filter.mp hp).2
      have : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = (0 : Fin 13)))) = true := by
        convert htrue using 3
        simp
      have := up gates g hop (fun v : Fin 13 => decide (v = (0 : Fin 13)))
        (fun v : Fin 13 => decide (v ∉ L m)) (fun v hv => by
          have hv' : v = 0 := by simpa using hv
          subst hv'
          simpa using h0m) this
      rw [this] at hum
      exact absurd hum (by simp)
    have ex : ∃ p ∈ Alive, p ≠ 0 ∧ p ≠ c := by
      by_cases hcA : c ∈ Alive
      · have : ∃ p ∈ Alive, p ≠ c := by
          by_contra h
          push Not at h
          have sub : Alive ⊆ ({c} : Finset (Fin 13)) := fun p hp => Finset.mem_singleton.mpr (h p hp)
          have : Alive.card ≤ ({c} : Finset (Fin 13)).card := Finset.card_le_card sub
          simp at this
          omega
        obtain ⟨p, hp, hpc⟩ := this
        exact ⟨p, hp, no0 p hp, hpc⟩
      · have hpos : 0 < Alive.card := Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hcardA
        obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
        exact ⟨p, hp, no0 p hp, fun e => hcA (e ▸ hp)⟩
    obtain ⟨p, hpA, hp0, hpc⟩ := ex
    have hp : p ∈ L l := (Finset.mem_filter.mp hpA).1
    have htrue : E gates g (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1))) = true :=
      (Finset.mem_filter.mp hpA).2
    have hbound : g < 13 + gates.length := by
      by_contra hge
      push Not at hge
      have := E_big gates g hge (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))
      rw [this] at htrue
      exact absurd htrue (by simp)
    rcases descend gates hop hlt g (13 + gates.length)
        (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))
        (fun v : Fin 13 => decide (v ∉ L l))
        (fun v : Fin 13 => decide (v ∉ L m))
        g hR hbound htrue hul hum with ⟨w', hx, hxl, hxm⟩ | ⟨Y, hRY, hAnd, _, _, _, hYx⟩
    · exfalso
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_not] at hx hxl hxm
      have hmem : w' ∈ L l ∩ L m := Finset.mem_inter.2 ⟨hxl, hxm⟩
      rw [hc, Finset.mem_singleton] at hmem
      rcases hx with hx | ⟨_, hx⟩
      · exact hpc (hx ▸ hmem)
      · exact h1l (hx ▸ hxl)
    · exact ⟨Y, hRY, hAnd, p, hp, hp0, hpc, hYx⟩
  · intro hcard
    set Alive := (L m).filter (fun p =>
      Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)
      with hAlive_def
    have hcardA : 2 ≤ Alive.card := by simpa [Alive, hAlive_def] using hcard
    have no1 : ∀ p ∈ Alive, p ≠ 1 := by
      intro p hp
      intro hp1
      subst hp1
      have htrue : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = (1 : Fin 13) ∨ ((1 : Fin 13) ≠ 1 ∧ v = 0)))) = true :=
        (Finset.mem_filter.mp hp).2
      have : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = (1 : Fin 13)))) = true := by
        convert htrue using 3
        simp
      have := up gates g hop (fun v : Fin 13 => decide (v = (1 : Fin 13)))
        (fun v : Fin 13 => decide (v ∉ L l)) (fun v hv => by
          have hv' : v = 1 := by simpa using hv
          subst hv'
          simpa using h1l) this
      rw [this] at hul
      exact absurd hul (by simp)
    have ex : ∃ p ∈ Alive, p ≠ 1 ∧ p ≠ c := by
      by_cases hcA : c ∈ Alive
      · have : ∃ p ∈ Alive, p ≠ c := by
          by_contra h
          push Not at h
          have sub : Alive ⊆ ({c} : Finset (Fin 13)) := fun p hp => Finset.mem_singleton.mpr (h p hp)
          have : Alive.card ≤ ({c} : Finset (Fin 13)).card := Finset.card_le_card sub
          simp at this
          omega
        obtain ⟨p, hp, hpc⟩ := this
        exact ⟨p, hp, no1 p hp, hpc⟩
      · have hpos : 0 < Alive.card := Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hcardA
        obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
        exact ⟨p, hp, no1 p hp, fun e => hcA (e ▸ hp)⟩
    obtain ⟨p, hpA, hp1, hpc⟩ := ex
    have hp : p ∈ L m := (Finset.mem_filter.mp hpA).1
    have htrue : E gates g (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0))) = true :=
      (Finset.mem_filter.mp hpA).2
    have hbound : g < 13 + gates.length := by
      by_contra hge
      push Not at hge
      have := E_big gates g hge (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))
      rw [this] at htrue
      exact absurd htrue (by simp)
    rcases descend gates hop hlt g (13 + gates.length)
        (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))
        (fun v : Fin 13 => decide (v ∉ L l))
        (fun v : Fin 13 => decide (v ∉ L m))
        g hR hbound htrue hul hum with ⟨w', hx, hxl, hxm⟩ | ⟨Y, hRY, hAnd, _, _, _, hYx⟩
    · exfalso
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_not] at hx hxl hxm
      have hmem : w' ∈ L l ∩ L m := Finset.mem_inter.2 ⟨hxl, hxm⟩
      rw [hc, Finset.mem_singleton] at hmem
      rcases hx with hx | ⟨_, hx⟩
      · exact hpc (hx ▸ hmem)
      · exact h0m (hx ▸ hxm)
    · exact ⟨Y, hRY, hAnd, p, hp, hp1, hpc, hYx⟩

end PEqualNP.Outside.L_meta_1572

theorem PEqualNP.Outside.L_meta_1572 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) :=
  PEqualNP.Outside.L_meta_1572.main
