import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1637
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

-- The value of wire `w` on input `x`.
def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]


end PEqualNP.Outside.L_meta_1637

open PEqualNP.Outside.L_meta_1637 in

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
  classical
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _ T hT gates hleg _ hread ev hev TS hTS Hg hHg l m hl hm
  have hval : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = val gates w x := by
    intro w x
    rw [hev]
    exact eval_eq gates w (List.ofFn x)
  have hin : ∀ (p : Fin N) (x : Fin N → Bool), ev (p : ℕ) x = x p := by
    intro p x
    rw [hval]
    exact val_input gates x p.val p.isLt
  have hTSp : ∀ p : Fin N, TS l m (p : ℕ) ↔ (p ∈ L l ∧ p ∈ L m) := by
    intro p
    rw [hTS]
    constructor
    · rintro ⟨h1, h2, _, _⟩
      rw [hin] at h1 h2
      exact ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_, ⟨p, h1, ?_⟩, ⟨p, h2, ?_⟩⟩
      · rw [hin]; simpa using h1
      · rw [hin]; simpa using h2
      · rw [hin]; exact (hT l p p).2 (Or.inl rfl)
      · rw [hin]; exact (hT m p p).2 (Or.inl rfl)
  refine ⟨hTSp, ?_, ?_⟩
  · intro p hpl hpm
    constructor
    · intro s hs
      rw [hin, hT]
      constructor
      · rintro (h | ⟨h, _, _⟩ | ⟨_, _, _, h⟩ | ⟨_, h, _⟩)
        · exact h.symm
        · exact absurd hl.1 h
        · exact absurd (by rw [← h]; exact hpl) hl.2
        · exact absurd h hl.2
      · intro h
        exact Or.inl h.symm
    · intro s hs
      rw [hin, hT]
      constructor
      · rintro (h | ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · exact h.symm
        · exact absurd (by rw [← h]; exact hpm) hm.2
        · exact absurd h hm.2
        · exact absurd h hm.2
      · intro h
        exact Or.inl h.symm
  · intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      have hw' := (hTS l m w).1 hw
      by_cases hlt : w < N
      · have hp := (hTSp ⟨w, hlt⟩).1 hw
        exact ⟨w, fun Zs hz _ => hz, Or.inl ⟨⟨w, hlt⟩, hp.1, hp.2, rfl⟩,
          fun s _ h => h, fun s _ h => h, hw'.2.2.1, hw'.2.2.2⟩
      · by_cases hbig : N + gates.length ≤ w
        · exfalso
          obtain ⟨s, _, hs⟩ := hw'.2.2.1
          rw [hval, val_big gates _ w hbig] at hs
          exact absurd hs (by simp)
        · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
          have hk : k < gates.length := by omega
          rcases (hleg (gates.get ⟨k, hk⟩) (List.get_mem _ _)).1 with hand | hor
          · exact ⟨N + k, fun Zs hz _ => hz,
              Or.inr ⟨⟨k, hk⟩, rfl, (hHg l m ⟨k, hk⟩).2 ⟨hw, Or.inl hand⟩⟩,
              fun s _ h => h, fun s _ h => h, hw'.2.2.1, hw'.2.2.2⟩
          · by_cases hall : ∀ e ∈ (gates.get ⟨k, hk⟩).inputs, ¬ TS l m e
            · exact ⟨N + k, fun Zs hz _ => hz,
                Or.inr ⟨⟨k, hk⟩, rfl, (hHg l m ⟨k, hk⟩).2 ⟨hw, Or.inr ⟨hor, hall⟩⟩⟩,
                fun s _ h => h, fun s _ h => h, hw'.2.2.1, hw'.2.2.2⟩
            · push_neg at hall
              obtain ⟨e, he, hTe⟩ := hall
              have helt : e < N + k := hread ⟨k, hk⟩ e he
              obtain ⟨ν, hcone, hkind, hWl, hWm, hnl, hnm⟩ := ih e helt hTe
              have hup : ∀ x : Fin N → Bool, ev e x = true → ev (N + k) x = true := by
                intro x hx
                rw [hval] at hx ⊢
                exact (val_or gates x k hk hor).2 ⟨e, he, helt, hx⟩
              exact ⟨ν, fun Zs hz hcl => hcone Zs (hcl ⟨k, hk⟩ hz e he) hcl, hkind,
                fun s hs h => hup _ (hWl s hs h), fun s hs h => hup _ (hWm s hs h), hnl, hnm⟩
