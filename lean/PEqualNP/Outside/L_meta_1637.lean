import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1637_aux

open PEqualNP.CircuitLowerBounds

-- The fold evaluation identities are adapted from the accepted L-meta-1602 proof.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp


end PEqualNP.Outside.L_meta_1637_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1637_aux in
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
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _ T hT gates hOps _ hBack ev hEv TS hTS Hg hHg l m hl hm
  have ev_eq (w : ℕ) (x : Fin N → Bool) :
      ev w x = (wiresFrom gates (List.ofFn x)).getD w false := hEv _ _
  have raw (p : Fin N) (x : Fin N → Bool) : ev p.val x = x p := by
    rw [ev_eq, getD_wiresFrom_lt _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
    simp
  have outside (w : ℕ) (hw : N + gates.length ≤ w) (x : Fin N → Bool) :
      ev w x = false := by
    rw [ev_eq, List.getD_eq_default]
    simpa [length_wiresFrom] using hw
  have evalGate (g : Fin gates.length) (x : Fin N → Bool) :
      ev (N + g.val) x = (gates.get g).op.eval ((gates.get g).inputs.map fun e => ev e x) := by
    rw [ev_eq]
    have he := getD_wiresFrom_gate gates (List.ofFn x) g.val g.isLt
    rw [List.length_ofFn] at he
    rw [he]
    congr 1
    apply List.map_congr_left
    intro e hem
    rw [ite_eq_left (hBack g e hem), ev_eq]
  have rawTS (p : Fin N) : TS l m p.val ↔ p ∈ L l ∧ p ∈ L m := by
    rw [hTS]
    constructor
    · intro h
      exact ⟨by simpa [raw] using h.1, by simpa [raw] using h.2.1⟩
    · rintro ⟨hpl,hpm⟩
      refine ⟨by simp [raw, hpl], by simp [raw, hpm], ?_, ?_⟩
      · exact ⟨p, hpl, by rw [raw]; exact (hT _ _ _).mpr (Or.inl rfl)⟩
      · exact ⟨p, hpm, by rw [raw]; exact (hT _ _ _).mpr (Or.inl rfl)⟩
  have rawTests (p : Fin N) (hpl : p ∈ L l) (hpm : p ∈ L m) :
      (∀ s ∈ L l, ev p.val (T l s) = true ↔ s = p) ∧
      (∀ s ∈ L m, ev p.val (T m s) = true ↔ s = p) := by
    constructor
    · intro s _
      have hp : p ≠ p1 := fun e => hl.2 (e ▸ hpl)
      rw [raw, hT]
      simp [hl.1, hl.2, hp, eq_comm]
    · intro s _
      have hp : p ≠ p0 := fun e => hm.2 (e ▸ hpm)
      rw [raw, hT]
      simp [hm.2, hp, eq_comm]
  refine ⟨rawTS, rawTests, ?_⟩
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    have endpoint :
        ((∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ w = c.val) ∨
          ∃ g : Fin gates.length, w = N + g.val ∧ Hg l m g) →
        ∃ ν : ℕ, (∀ Zs : Set ℕ, w ∈ Zs →
          (∀ k : Fin gates.length, N + k.val ∈ Zs → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) →
          ν ∈ Zs) ∧
          ((∃ c : Fin N, c ∈ L l ∧ c ∈ L m ∧ ν = c.val) ∨
            ∃ g : Fin gates.length, ν = N + g.val ∧ Hg l m g) ∧
          (∀ s ∈ L l, ev ν (T l s) = true → ev w (T l s) = true) ∧
          (∀ s ∈ L m, ev ν (T m s) = true → ev w (T m s) = true) ∧
          (∃ s ∈ L l, ev ν (T l s) = true) ∧ ∃ s ∈ L m, ev ν (T m s) = true := by
      intro hout
      obtain ⟨_,_,hleft,hright⟩ := (hTS l m w).mp hw
      exact ⟨w, fun _ h _ => h, hout, fun _ _ h => h, fun _ _ h => h, hleft, hright⟩
    by_cases hp : w < N
    · let p : Fin N := ⟨w,hp⟩
      obtain ⟨hpl,hpm⟩ := (rawTS p).mp hw
      exact endpoint (Or.inl ⟨p,hpl,hpm,rfl⟩)
    have hsmall : w < N + gates.length := by
      by_contra! hlarge
      obtain ⟨_,_,⟨p,_,ht⟩,_⟩ := (hTS l m w).mp hw
      simp [outside w hlarge] at ht
    let g : Fin gates.length := ⟨w-N, by omega⟩
    have hwire : w = N + g.val := by dsimp [g]; omega
    have gw : TS l m (N + g.val) := hwire ▸ hw
    have hgmem : gates.get g ∈ gates := List.get_mem _ _
    obtain hop | hop := (hOps _ hgmem).1
    · exact endpoint (Or.inr ⟨g,hwire,(hHg l m g).mpr ⟨gw,Or.inl hop⟩⟩)
    by_cases child : ∃ e ∈ (gates.get g).inputs, TS l m e
    · obtain ⟨e, hem, he⟩ := child
      have hew : e < w := by rw [hwire]; exact hBack g e hem
      obtain ⟨v,hcone,hkind,hleft,hright,hltest,hrtest⟩ := ih e hew he
      have passes (x : Fin N → Bool) (hx : ev e x = true) : ev w x = true := by
        rw [hwire, evalGate, hop]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
        exact ⟨e,hem,hx⟩
      exact ⟨v, fun Z hz hclose => hcone Z (hclose g (hwire ▸ hz) e hem) hclose,
        hkind, fun s hs h => passes _ (hleft s hs h),
        fun s hs h => passes _ (hright s hs h), hltest, hrtest⟩
    · have hno : ∀ e ∈ (gates.get g).inputs, ¬ TS l m e :=
        fun e hem he => child ⟨e,hem,he⟩
      exact endpoint (Or.inr ⟨g,hwire,(hHg l m g).mpr ⟨gw,Or.inr ⟨hop,hno⟩⟩⟩)
