import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1637

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w
      = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_append (gs gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs2) w = wiresFrom gs2 (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [wiresFrom_cons, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_take (gates : List Gate) (x : List Bool) (g : ℕ) (i : ℕ)
    (hi : i < x.length + g) (hg : g ≤ gates.length) :
    (wiresFrom (gates.take g) x).getD i false = (wiresFrom gates x).getD i false := by
  have hs : wiresFrom gates x = wiresFrom (gates.drop g) (wiresFrom (gates.take g) x) := by
    rw [← wiresFrom_append, List.take_append_drop]
  rw [hs]
  refine (getD_wiresFrom _ _ _ ?_).symm
  rw [length_wiresFrom, List.length_take]
  omega

theorem getD_gate (gates : List Gate) (x : List Bool) (g : ℕ) (hg : g < gates.length)
    (hin : ∀ i ∈ (gates[g]).inputs, i < x.length + g) :
    (wiresFrom gates x).getD (x.length + g) false
      = (gates[g]).op.eval ((gates[g]).inputs.map fun i => (wiresFrom gates x).getD i false) := by
  have hs : gates = gates.take g ++ (gates[g] :: gates.drop (g + 1)) := by
    conv_lhs => rw [← List.take_append_drop g gates]
    rw [List.drop_eq_getElem_cons hg]
  have hW : (wiresFrom (gates.take g) x).length = x.length + g := by
    rw [length_wiresFrom, List.length_take]
    omega
  have hmap : ((gates[g]).inputs.map fun i => (wiresFrom (gates.take g) x).getD i false)
      = ((gates[g]).inputs.map fun i => (wiresFrom gates x).getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact getD_take gates x g i (hin i hi) (le_of_lt hg)
  conv_lhs => rw [hs]
  rw [wiresFrom_append, wiresFrom_cons, getD_wiresFrom _ _ _ (by simp [hW]), hmap, ← hW]
  simp

end PEqualNP.Outside.L_meta_1637

theorem PEqualNP.Outside.L_meta_1637 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ TS : Fin N → Fin N → ℕ → Prop,
    (∀ (l m : Fin N) (w : ℕ), TS l m w ↔ (ev w (fun v : Fin N => decide (v ∉ L l)) = false ∧ ev w (fun v : Fin N => decide (v ∉ L m)) = false ∧ (∃ p ∈ L l, ev w (T l p) = true) ∧ ∃ p ∈ L m, ev w (T m p) = true)) →
    ∀ Hg : Fin N → Fin N → Fin gates.length → Prop,
    (∀ (l m : Fin N) (g : Fin gates.length), Hg l m g ↔ (TS l m (N + (g : ℕ)) ∧ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ e ∈ (gates.get g).inputs, ¬ TS l m e)))) →
    ∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) →
      (∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m)) ∧
      (∀ p : Fin N, p ∈ L l → p ∈ L m → (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧ (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p)) ∧
      ∀ w : ℕ, TS l m w → ∃ ν : ℕ, (∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → ν ∈ Zs) ∧
        ((∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ ν = (c : ℕ)) ∨ ∃ h : Fin gates.length, ν = (N + (h : ℕ)) ∧ Hg l m h) ∧
        (∀ s ∈ L l, ev ν (T l s) = true → ev w (T l s) = true) ∧ (∀ s ∈ L m, ev ν (T m s) = true → ev w (T m s) = true) ∧
        (∃ s ∈ L l, ev ν (T l s) = true) ∧ ∃ s ∈ L m, ev ν (T m s) = true := by
  intro q N L i0 p0 p1 hq hN hcard hint hcol hp hp0 hp1 T hT gates hgates hne hlt ev hev0 TS hTS
    Hg hHg l m hl hm
  have hev : ∀ (w : ℕ) (x : Fin N → Bool),
      ev w x = (PEqualNP.Outside.L_meta_1637.wiresFrom gates (List.ofFn x)).getD w false :=
    fun w x => hev0 w x
  have hin : ∀ (p : Fin N) (x : Fin N → Bool), ev (p : ℕ) x = x p := by
    intro p x
    rw [hev, PEqualNP.Outside.L_meta_1637.getD_wiresFrom _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have hbig : ∀ (w : ℕ) (x : Fin N → Bool), N + gates.length ≤ w → ev w x = false := by
    intro w x hw
    rw [hev, List.getD_eq_default]
    rw [PEqualNP.Outside.L_meta_1637.length_wiresFrom]
    simp
    omega
  have hor : ∀ (g : Fin gates.length) (x : Fin N → Bool) (e : ℕ),
      (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or → e ∈ (gates.get g).inputs →
      ev e x = true → ev (N + (g : ℕ)) x = true := by
    intro g x e hop he hx
    have hlen : (List.ofFn x).length = N := by simp
    have hin2 : ∀ i ∈ (gates[(g : ℕ)]).inputs, i < (List.ofFn x).length + (g : ℕ) := by
      intro i hi
      rw [hlen]
      exact hlt g i (by simpa using hi)
    have hgate := PEqualNP.Outside.L_meta_1637.getD_gate gates (List.ofFn x) g g.isLt hin2
    rw [hlen] at hgate
    rw [hev, hgate]
    have hop2 : (gates[(g : ℕ)]).op = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using hop
    rw [hop2]
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map, List.any_eq_true]
    refine ⟨e, by simpa using he, ?_⟩
    simpa [hev] using hx
  have part1 : ∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m) := by
    intro p
    rw [hTS]
    simp only [hin]
    constructor
    · rintro ⟨h1, h2, _, _⟩
      exact ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by simpa using h1, by simpa using h2, ⟨p, h1, (hT l p p).2 (Or.inl rfl)⟩,
        ⟨p, h2, (hT m p p).2 (Or.inl rfl)⟩⟩
  refine ⟨part1, ?_, ?_⟩
  · intro p hpl hpm
    constructor
    · intro s hs
      rw [hin, hT]
      constructor
      · rintro (h | h | h | h)
        · exact h.symm
        · exact absurd hl.1 h.1
        · exact absurd (h.2.2.2 ▸ hpl) hl.2
        · exact absurd h.2.1 hl.2
      · intro h
        exact Or.inl h.symm
    · intro s hs
      rw [hin, hT]
      constructor
      · rintro (h | h | h | h)
        · exact h.symm
        · exact absurd (h.2.2 ▸ hpm) h.1
        · exact absurd h.1 hm.2
        · exact absurd h.1 hm.2
      · intro h
        exact Or.inl h.symm
  · intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
    intro hw
    have hw2 := (hTS l m w).1 hw
    rcases lt_or_ge w N with hwN | hwN
    · have hc := (part1 ⟨w, hwN⟩).1 hw
      exact ⟨w, fun Zs h _ => h, Or.inl ⟨⟨w, hwN⟩, hc.1, hc.2, rfl⟩, fun s _ h => h,
        fun s _ h => h, hw2.2.2.1, hw2.2.2.2⟩
    rcases lt_or_ge w (N + gates.length) with hwg | hwg
    · let g : Fin gates.length := ⟨w - N, by omega⟩
      have hwg2 : w = N + (g : ℕ) := by
        show w = N + (w - N)
        omega
      by_cases hH : Hg l m g
      · exact ⟨w, fun Zs h _ => h, Or.inr ⟨g, hwg2, hH⟩, fun s _ h => h, fun s _ h => h,
          hw2.2.2.1, hw2.2.2.2⟩
      · have hTSg : TS l m (N + (g : ℕ)) := hwg2 ▸ hw
        rw [hHg] at hH
        have hnot : ¬ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
              ∀ e ∈ (gates.get g).inputs, ¬ TS l m e)) := fun h => hH ⟨hTSg, h⟩
        have hop : (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
          rcases (hgates (gates.get g) (List.get_mem _ _)).1 with h | h
          · exact absurd (Or.inl h) hnot
          · exact h
        have hex : ∃ e ∈ (gates.get g).inputs, TS l m e := by
          by_contra hc
          push_neg at hc
          exact hnot (Or.inr ⟨hop, hc⟩)
        obtain ⟨e, he, hTSe⟩ := hex
        have hel : e < w := by
          have := hlt g e he
          omega
        obtain ⟨ν, hcone, hkind, hsl, hsm, hnl, hnm⟩ := ih e hel hTSe
        refine ⟨ν, ?_, hkind, ?_, ?_, hnl, hnm⟩
        · intro Zs hwZ hcl
          exact hcone Zs (hcl g (hwg2 ▸ hwZ) e he) hcl
        · intro s hs h
          rw [hwg2]
          exact hor g _ e hop he (hsl s hs h)
        · intro s hs h
          rw [hwg2]
          exact hor g _ e hop he (hsm s hs h)
    · exfalso
      obtain ⟨_, _, ⟨s, _, hs⟩, _⟩ := hw2
      rw [hbig _ _ hwg] at hs
      exact Bool.false_ne_true hs
