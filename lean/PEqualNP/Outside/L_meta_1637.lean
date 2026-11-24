import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1637

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def val {N : ℕ} (gates : List Gate) (w : ℕ) (x : Fin N → Bool) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn x)

lemma val_input {N : ℕ} (gates : List Gate) (p : Fin N) (x : Fin N → Bool) :
    val gates p.val x = x p := by
  change (run gates (List.ofFn x)).getD p.val false = x p
  have hp : p.val < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp only [List.getElem_ofFn, Fin.eta]

lemma val_out {N : ℕ} (gates : List Gate) (w : ℕ) (x : Fin N → Bool)
    (hw : N + gates.length ≤ w) : val gates w x = false := by
  change (run gates (List.ofFn x)).getD w false = false
  apply List.getD_eq_default
  rw [run_length, List.length_ofFn]
  exact hw

lemma val_gate {N : ℕ} (gates : List Gate) (i : Fin gates.length) (x : Fin N → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < N + i.val) :
    val gates (N + i.val) x =
      (gates.get i).op.eval ((gates.get i).inputs.map fun a => val gates a x) := by
  let j := i.val
  have hj : j < gates.length := i.isLt
  let g := gates[j]
  let earlier := run (gates.take j) (List.ofFn x)
  have plen : earlier.length = N + j := by
    simp [earlier, run_length, j]
  have split : run gates (List.ofFn x) = run (g :: gates.drop (j + 1)) earlier := by
    rw [run_split gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (a : ℕ) (ha : a < N + j) : earlier.getD a false = val gates a x := by
    change earlier.getD a false = (run gates (List.ofFn x)).getD a false
    rw [split]
    exact (run_getD _ earlier a (by simpa only [plen] using ha)).symm
  change (run gates (List.ofFn x)).getD (N + j) false =
    g.op.eval (g.inputs.map fun a => val gates a x)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact read a (hwf a ha)

lemma val_or_of_input {N : ℕ} (gates : List Gate) (i : Fin gates.length) (x : Fin N → Bool)
    (hwf : ∀ a ∈ (gates.get i).inputs, a < N + i.val)
    (hop : (gates.get i).op = GateOp.or) {a : ℕ} (ha : a ∈ (gates.get i).inputs)
    (h : val gates a x = true) : val gates (N + i.val) x = true := by
  rw [val_gate gates i x hwf, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨a, ha, h⟩

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
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _ T hT gates hG _ hwf ev hev TS hTS Hg hHg l m hl hm
  have ev_in : ∀ (p : Fin N) (x : Fin N → Bool), ev (p : ℕ) x = x p := by
    intro p x
    rw [hev]
    exact PEqualNP.Outside.L_meta_1637.val_input gates p x
  have hTl : ∀ s v : Fin N, T l s v = true ↔ (v = s ∨ (s ≠ p0 ∧ v = p1)) := by
    intro s v
    rw [hT]
    constructor
    · rintro (h | ⟨h, _⟩ | ⟨_, _, h1, h2⟩ | ⟨_, h, _⟩)
      · exact Or.inl h
      · exact absurd hl.1 h
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd h hl.2
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl ⟨hl.1, hl.2, h1, h2⟩))
  have hTm : ∀ s v : Fin N, T m s v = true ↔ (v = s ∨ (s ≠ p1 ∧ v = p0)) := by
    intro s v
    rw [hT]
    constructor
    · rintro (h | ⟨_, h1, h2⟩ | ⟨h, _⟩ | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd h hm.2
      · exact absurd h hm.2
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨hm.2, h1, h2⟩)
  have part1 : ∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m) := by
    intro p
    rw [hTS]
    constructor
    · rintro ⟨h1, h2, _, _⟩
      rw [ev_in] at h1 h2
      exact ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_, ⟨p, h1, ?_⟩, ⟨p, h2, ?_⟩⟩
      · rw [ev_in]
        simpa using h1
      · rw [ev_in]
        simpa using h2
      · rw [ev_in]
        exact (hTl p p).mpr (Or.inl rfl)
      · rw [ev_in]
        exact (hTm p p).mpr (Or.inl rfl)
  have part2 : ∀ p : Fin N, p ∈ L l → p ∈ L m →
      (∀ s ∈ L l, ev (p : ℕ) (T l s) = true ↔ s = p) ∧
        (∀ s ∈ L m, ev (p : ℕ) (T m s) = true ↔ s = p) := by
    intro p hpl hpm
    refine ⟨?_, ?_⟩
    · intro s _
      rw [ev_in, hTl]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact h.symm
        · exact absurd (h ▸ hpl) hl.2
      · intro h
        exact Or.inl h.symm
    · intro s _
      rw [ev_in, hTm]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact h.symm
        · exact absurd (h ▸ hpm) hm.2
      · intro h
        exact Or.inl h.symm
  refine ⟨part1, part2, ?_⟩
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hTSw
    have hTSw' := (hTS l m w).mp hTSw
    by_cases hw : w < N
    · have hc := (part1 ⟨w, hw⟩).mp hTSw
      exact ⟨w, fun Zs hwZ _ => hwZ, Or.inl ⟨⟨w, hw⟩, hc.1, hc.2, rfl⟩,
        fun s _ h => h, fun s _ h => h, hTSw'.2.2.1, hTSw'.2.2.2⟩
    · by_cases hw2 : w < N + gates.length
      · obtain ⟨k, hk⟩ : ∃ k : Fin gates.length, N + (k : ℕ) = w :=
          ⟨⟨w - N, by omega⟩, by show N + (w - N) = w; omega⟩
        by_cases hh : Hg l m k
        · exact ⟨w, fun Zs hwZ _ => hwZ, Or.inr ⟨k, hk.symm, hh⟩,
            fun s _ h => h, fun s _ h => h, hTSw'.2.2.1, hTSw'.2.2.2⟩
        · have hTSk : TS l m (N + (k : ℕ)) := by
            rw [hk]
            exact hTSw
          have hnot : ¬ (TS l m (N + (k : ℕ)) ∧
              ((gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
                ((gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
                  ∀ e ∈ (gates.get k).inputs, ¬ TS l m e))) :=
            fun hx => hh ((hHg l m k).mpr hx)
          have hop : (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
            rcases (hG (gates.get k) (List.get_mem _ _)).1 with h | h
            · exact absurd ⟨hTSk, Or.inl h⟩ hnot
            · exact h
          have hex : ∃ e ∈ (gates.get k).inputs, TS l m e := by
            by_contra hcon
            exact hnot ⟨hTSk, Or.inr ⟨hop, fun e he hTSe => hcon ⟨e, he, hTSe⟩⟩⟩
          obtain ⟨e, he, hTSe⟩ := hex
          have helt : e < w := by
            have := hwf k e he
            omega
          obtain ⟨ν, hcone, hkind, hsubl, hsubm, hnel, hnem⟩ := ih e helt hTSe
          have hor : ∀ x : Fin N → Bool, ev e x = true → ev w x = true := by
            intro x hx
            rw [hev] at hx ⊢
            rw [← hk]
            exact PEqualNP.Outside.L_meta_1637.val_or_of_input gates k x (hwf k) hop he hx
          refine ⟨ν, ?_, hkind, fun s hs h => hor _ (hsubl s hs h),
            fun s hs h => hor _ (hsubm s hs h), hnel, hnem⟩
          intro Zs hwZ hclosed
          exact hcone Zs (hclosed k (by rw [hk]; exact hwZ) e he) hclosed
      · exfalso
        obtain ⟨p, _, hp⟩ := hTSw'.2.2.1
        rw [hev] at hp
        have hfalse := PEqualNP.Outside.L_meta_1637.val_out gates w (T l p) (by omega)
        exact Bool.noConfusion (hp.symm.trans hfalse)
