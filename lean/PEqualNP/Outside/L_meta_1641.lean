import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1641

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_stepW_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

theorem foldl_stepW_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_take_getD (gs : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((gs.take t).foldl stepW w).length) :
    (gs.foldl stepW w).getD i false = ((gs.take t).foldl stepW w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t gs, List.foldl_append]
  exact foldl_stepW_getD _ _ _ hi

theorem gate_val (N : ℕ) (gs : List Gate) (x : Fin N → Bool) (t : ℕ) (ht : t < gs.length)
    (hin : ∀ c ∈ (gs[t]).inputs, c < N + t) :
    (gs.foldl stepW (List.ofFn x)).getD (N + t) false =
      (gs[t]).op.eval ((gs[t]).inputs.map fun i => (gs.foldl stepW (List.ofFn x)).getD i false) := by
  have hsplit : gs = gs.take t ++ gs[t] :: gs.drop (t + 1) := by
    simp [List.take_append_drop]
  have hlen : ((gs.take t).foldl stepW (List.ofFn x)).length = N + t := by
    rw [foldl_stepW_length, List.length_ofFn, List.length_take, Nat.min_eq_left ht.le]
  have hlhs : (gs.foldl stepW (List.ofFn x)).getD (N + t) false =
      (gs[t]).op.eval ((gs[t]).inputs.map fun i =>
        ((gs.take t).foldl stepW (List.ofFn x)).getD i false) := by
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [foldl_stepW_getD _ _ _ (by simp only [stepW, List.length_append, List.length_singleton, hlen]; omega)]
    simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ((gs.take t).foldl stepW (List.ofFn x)).length ≤ N + t), hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hlhs]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (foldl_take_getD gs (List.ofFn x) t i (by rw [hlen]; exact hin i hi)).symm

theorem input_val (N : ℕ) (gs : List Gate) (x : Fin N → Bool) (i : Fin N) :
    (gs.foldl stepW (List.ofFn x)).getD i.val false = x i := by
  rw [foldl_stepW_getD _ _ _ (by simp)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem big_val (N : ℕ) (gs : List Gate) (x : Fin N → Bool) (w : ℕ) (hw : N + gs.length ≤ w) :
    (gs.foldl stepW (List.ofFn x)).getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [foldl_stepW_length]; simp; omega)]
  rfl

theorem any_map_iff (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ c ∈ l, f c = true := by
  simp

theorem all_map_iff (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ c ∈ l, f c = true := by
  simp

def Closed (N : ℕ) (gates : List Gate) (Zs : Set ℕ) : Prop :=
  ∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = GateOp.or →
    ∀ e ∈ (gates.get k).inputs, e ∈ Zs

section Ctx

variable {N : ℕ} (gates : List Gate) (ev : ℕ → (Fin N → Bool) → Bool) (St : ℕ → Fin N → Prop)

theorem or_val (evG : ∀ (k : Fin gates.length) (x : Fin N → Bool),
      ev (N + (k : ℕ)) x = (gates.get k).op.eval ((gates.get k).inputs.map fun c => ev c x))
    (k : Fin gates.length) (hk : (gates.get k).op = GateOp.or) (x : Fin N → Bool) :
    ev (N + (k : ℕ)) x = true ↔ ∃ c ∈ (gates.get k).inputs, ev c x = true := by
  rw [evG, hk]
  exact any_map_iff _ _

theorem and_val (evG : ∀ (k : Fin gates.length) (x : Fin N → Bool),
      ev (N + (k : ℕ)) x = (gates.get k).op.eval ((gates.get k).inputs.map fun c => ev c x))
    (k : Fin gates.length) (hk : (gates.get k).op = GateOp.and) (x : Fin N → Bool) :
    ev (N + (k : ℕ)) x = true ↔ ∀ c ∈ (gates.get k).inputs, ev c x = true := by
  rw [evG, hk]
  exact all_map_iff _ _

theorem st_self (hSt : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gates Zs → (p : ℕ) ∈ Zs)
    (p : Fin N) : St p p :=
  (hSt p p).2 (fun _ h _ => h)

theorem st_input (hSt : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gates Zs → (p : ℕ) ∈ Zs)
    (w : ℕ) (hw : w < N) (p : Fin N) (h : St w p) : (p : ℕ) = w := by
  have := (hSt w p).1 h {w} rfl (by
    intro k hk _ _ _
    simp at hk
    omega)
  simpa using this

theorem st_and (hSt : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gates Zs → (p : ℕ) ∈ Zs)
    (k : Fin gates.length) (hk : (gates.get k).op = GateOp.and) (p : Fin N) :
    ¬ St (N + (k : ℕ)) p := by
  intro h
  have := (hSt _ p).1 h {N + (k : ℕ)} rfl (by
    intro k' hk' hor _ _
    simp at hk'
    have : k' = k := Fin.ext (by omega)
    subst this
    rw [hk] at hor
    cases hor)
  simp at this
  omega

theorem st_or_intro (hSt : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gates Zs → (p : ℕ) ∈ Zs)
    (k : Fin gates.length) (hk : (gates.get k).op = GateOp.or) (p : Fin N)
    (c : ℕ) (hc : c ∈ (gates.get k).inputs) (h : St c p) : St (N + (k : ℕ)) p := by
  rw [hSt]
  intro Zs hw hcl
  exact (hSt c p).1 h Zs (hcl k hw hk c hc) hcl

theorem st_or (hSt : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gates Zs → (p : ℕ) ∈ Zs)
    (hlt : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (k : Fin gates.length) (hk : (gates.get k).op = GateOp.or) (p : Fin N)
    (h : St (N + (k : ℕ)) p) : ∃ c ∈ (gates.get k).inputs, St c p := by
  by_contra hno
  push_neg at hno
  have hmem := (hSt _ p).1 h {w | w = N + (k : ℕ) ∨ ¬ St w p} (Or.inl rfl) (by
    intro k' hk' hor e he
    rcases hk' with hk' | hk'
    · have : k' = k := Fin.ext (by omega)
      subst this
      exact Or.inr (hno e he)
    · exact Or.inr (fun he' => hk' (st_or_intro gates St hSt k' hor p e he he')))
  rcases hmem with hm | hm
  · have := p.isLt
    omega
  · exact hm (st_self gates St hSt p)

theorem st_true (hSt : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gates Zs → (p : ℕ) ∈ Zs)
    (evI : ∀ (i : Fin N) (x : Fin N → Bool), ev i x = x i)
    (evG : ∀ (k : Fin gates.length) (x : Fin N → Bool),
      ev (N + (k : ℕ)) x = (gates.get k).op.eval ((gates.get k).inputs.map fun c => ev c x))
    (w : ℕ) (s : Fin N) (x : Fin N → Bool) (h : St w s) (hx : x s = true) : ev w x = true := by
  by_contra hf
  have hmem := (hSt w s).1 h {w' | ev w' x = false} (by simpa using hf) (by
    intro k hk hor e he
    simp only [Set.mem_setOf_eq] at hk ⊢
    by_contra he'
    have : ev (N + (k : ℕ)) x = true :=
      (or_val gates ev evG k hor x).2 ⟨e, he, by simpa using he'⟩
    rw [this] at hk
    cases hk)
  simp only [Set.mem_setOf_eq] at hmem
  rw [evI] at hmem
  rw [hmem] at hx
  cases hx

theorem ev_mono (hops : ∀ gt ∈ gates, gt.op = GateOp.and ∨ gt.op = GateOp.or)
    (hlt : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (evI : ∀ (i : Fin N) (x : Fin N → Bool), ev i x = x i)
    (evG : ∀ (k : Fin gates.length) (x : Fin N → Bool),
      ev (N + (k : ℕ)) x = (gates.get k).op.eval ((gates.get k).inputs.map fun c => ev c x))
    (evB : ∀ (w : ℕ) (x : Fin N → Bool), N + gates.length ≤ w → ev w x = false)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w, ev w x = true → ev w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < N
    · have e1 := evI ⟨w, h1⟩ x
      have e2 := evI ⟨w, h1⟩ y
      simp only at e1 e2
      rw [e1] at hw
      rw [e2]
      exact hxy _ hw
    by_cases h2 : w < N + gates.length
    · obtain ⟨k, hk⟩ : ∃ k : Fin gates.length, w = N + (k : ℕ) := ⟨⟨w - N, by omega⟩, by simp; omega⟩
      subst hk
      have hmem : gates.get k ∈ gates := List.get_mem gates k
      rcases hops _ hmem with hop | hop
      · rw [and_val gates ev evG k hop] at hw ⊢
        intro c hc
        exact ih c (by have := hlt k c hc; omega) (hw c hc)
      · rw [or_val gates ev evG k hop] at hw ⊢
        obtain ⟨c, hc, hcv⟩ := hw
        exact ⟨c, hc, ih c (by have := hlt k c hc; omega) hcv⟩
    · rw [evB w x (by omega)] at hw
      cases hw

end Ctx

end PEqualNP.Outside.L_meta_1641

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1641

theorem PEqualNP.Outside.L_meta_1641 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o0 : ℕ, ev o0 (fun v : Fin N => decide (v ∉ L i0)) = false → ev o0 (fun v : Fin N => decide (v = p0)) = true → ev o0 (fun v : Fin N => decide (v = p1)) = true →
    (∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → ev o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
    ∀ St : ℕ → Fin N → Prop,
    (∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs) →
    ∀ UB : ℕ → Finset (Finset (Fin N)),
    (∀ (j : ℕ) (b : Finset (Fin N)), b ∈ UB j ↔ ((∃ r ∈ L i0, ∀ r' : Fin N, r' ∈ b ↔ (r' ∈ L i0 ∧ ∀ X : Finset (Fin N), (∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
          ∀ s ∈ L i0, ∀ s' ∈ L i0, St (N + (i : ℕ)) s → St (N + (i : ℕ)) s' → (s ∈ X ↔ s' ∈ X)) → (r ∈ X ↔ r' ∈ X))) ∧
        p0 ∉ b ∧ p1 ∉ b ∧ ∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
        (ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p1)) = true) → ∀ s ∈ b, ¬ St (N + (i : ℕ)) s)) →
    ∀ Xs : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ Xs ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ (∀ t : Fin N, t ≠ i0 → ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
        ¬ ∀ e ∈ (gates.get g).inputs, (ev e (fun v : Fin N => decide (v = p0)) = true ∨ ev e (fun v : Fin N => decide (v = p1)) = true))) →
      (∀ j : Fin gates.length, (UB ((j : ℕ) + 1)).card ≤ (UB j).card ∧ (UB j).card ≤ (UB ((j : ℕ) + 1)).card + 1 ∧
        (j ∉ Xs → (UB j).card = (UB ((j : ℕ) + 1)).card)) ∧
      (UB 0).card = q - 1 ∧ q - 1 ≤ Xs.card + (UB gates.length).card := by
  classical
  intro q N L i0 p0 p1 hq hN hcard hinter hpair hp01 hp0 hp1 gates hops hne hlt ev hev o0 _ _ _ _ St hSt UB hUB Xs hXs
  have hops' : ∀ gt ∈ gates, gt.op = GateOp.and ∨ gt.op = GateOp.or := fun gt h => (hops gt h).1
  have evI : ∀ (i : Fin N) (x : Fin N → Bool), ev i x = x i := by
    intro i x
    rw [hev]
    exact input_val N gates x i
  have evG : ∀ (k : Fin gates.length) (x : Fin N → Bool),
      ev (N + (k : ℕ)) x = (gates.get k).op.eval ((gates.get k).inputs.map fun c => ev c x) := by
    intro k x
    have h1 := gate_val N gates x k k.isLt (fun c hc => hlt k c (by simpa using hc))
    have h2 : ev (N + (k : ℕ)) x = (gates.foldl stepW (List.ofFn x)).getD (N + (k : ℕ)) false := hev _ x
    rw [h2, h1]
    simp only [List.get_eq_getElem]
    congr 1
    apply List.map_congr_left
    intro c _
    exact (hev c x).symm
  have evB : ∀ (w : ℕ) (x : Fin N → Bool), N + gates.length ≤ w → ev w x = false := by
    intro w x hw
    rw [hev]
    exact big_val N gates x w hw
  -- local predicates
  obtain ⟨Cl, hCl⟩ : ∃ Cl : ℕ → Finset (Fin N) → Prop, ∀ j X, Cl j X ↔
      (∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = GateOp.or →
        ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
        ∀ s ∈ L i0, ∀ s' ∈ L i0, St (N + (i : ℕ)) s → St (N + (i : ℕ)) s' → (s ∈ X ↔ s' ∈ X)) :=
    ⟨_, fun _ _ => Iff.rfl⟩
  obtain ⟨Sp, hSp⟩ : ∃ Sp : ℕ → Fin N → Fin N → Prop, ∀ j r r', Sp j r r' ↔
      ∀ X : Finset (Fin N), Cl j X → (r ∈ X ↔ r' ∈ X) := ⟨_, fun _ _ _ => Iff.rfl⟩
  obtain ⟨Un, hUn⟩ : ∃ Un : ℕ → Finset (Fin N) → Prop, ∀ j b, Un j b ↔
      (∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = GateOp.or →
        ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
        (ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨
          ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p1)) = true) →
        ∀ s ∈ b, ¬ St (N + (i : ℕ)) s) := ⟨_, fun _ _ => Iff.rfl⟩
  have hUB' : ∀ j b, b ∈ UB j ↔ ((∃ r ∈ L i0, b = (L i0).filter (fun r' => Sp j r r')) ∧
      p0 ∉ b ∧ p1 ∉ b ∧ Un j b) := by
    intro j b
    rw [hUB j b, hUn j b]
    constructor
    · rintro ⟨⟨r, hr, hb⟩, h2⟩
      refine ⟨⟨r, hr, ?_⟩, h2⟩
      ext r'
      rw [hb r', Finset.mem_filter, hSp]
      simp only [hCl]
    · rintro ⟨⟨r, hr, hb⟩, h2⟩
      refine ⟨⟨r, hr, ?_⟩, h2⟩
      intro r'
      rw [hb, Finset.mem_filter, hSp]
      simp only [hCl]
  -- the equivalence
  have Sp_refl : ∀ j r, Sp j r r := fun j r => (hSp j r r).2 (fun X _ => Iff.rfl)
  have Sp_symm : ∀ j r r', Sp j r r' → Sp j r' r := fun j r r' h =>
    (hSp j r' r).2 (fun X hX => ((hSp j r r').1 h X hX).symm)
  have Sp_trans : ∀ j r r' r'', Sp j r r' → Sp j r' r'' → Sp j r r'' := fun j r r' r'' h1 h2 =>
    (hSp j r r'').2 (fun X hX => ((hSp j r r').1 h1 X hX).trans ((hSp j r' r'').1 h2 X hX))
  have Srel : ∀ (i : Fin gates.length), ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
      ∀ s, St (N + (i : ℕ)) s → s ∈ L i0 := by
    intro i hi s hs
    by_contra hns
    have := st_true gates ev St hSt evI evG (N + (i : ℕ)) s (fun v : Fin N => decide (v ∉ L i0)) hs (by simpa using hns)
    rw [this] at hi
    cases hi
  have Sp_gen : ∀ (j : ℕ) (i : Fin gates.length), (i : ℕ) < j → (gates.get i).op = GateOp.or →
      ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
      ∀ s s', St (N + (i : ℕ)) s → St (N + (i : ℕ)) s' → Sp j s s' := by
    intro j i hij hor hc s s' hs hs'
    exact (hSp j s s').2 (fun X hX => (hCl j X).1 hX i hij hor hc s (Srel i hc s hs) s'
      (Srel i hc s' hs') hs hs')
  have Cl_mono : ∀ j X, Cl (j + 1) X → Cl j X := fun j X h =>
    (hCl j X).2 (fun i hi => (hCl (j + 1) X).1 h i (by omega))
  have Sp_mono : ∀ j r r', Sp j r r' → Sp (j + 1) r r' := fun j r r' h =>
    (hSp _ _ _).2 (fun X hX => (hSp j r r').1 h X (Cl_mono j X hX))
  have cls_eq : ∀ j r r', Sp j r r' →
      (L i0).filter (fun x => Sp j r x) = (L i0).filter (fun x => Sp j r' x) := by
    intro j r r' h
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, h'⟩
      exact ⟨hx, Sp_trans _ _ _ _ (Sp_symm _ _ _ h) h'⟩
    · rintro ⟨hx, h'⟩
      exact ⟨hx, Sp_trans _ _ _ _ h h'⟩
  have Un_sub : ∀ j b b', b ⊆ b' → Un j b' → Un j b := by
    intro j b b' hsub h
    rw [hUn] at h ⊢
    intro i hi hor hc ha s hs
    exact h i hi hor hc ha s (hsub hs)
  -- one gate
  have step : ∀ j : Fin gates.length, (UB ((j : ℕ) + 1)).card ≤ (UB j).card ∧
      (UB j).card ≤ (UB ((j : ℕ) + 1)).card + 1 ∧ (j ∉ Xs → (UB j).card = (UB ((j : ℕ) + 1)).card) := by
    intro j
    by_cases hrel : (gates.get j).op = GateOp.or ∧
        ev (N + (j : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false
    · obtain ⟨hor, hcm⟩ := hrel
      have inp_cm : ∀ c ∈ (gates.get j).inputs, ev c (fun v : Fin N => decide (v ∉ L i0)) = false := by
        intro c hc
        by_contra h
        have : ev (N + (j : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = true :=
          (or_val gates ev evG j hor _).2 ⟨c, hc, by simpa using h⟩
        rw [this] at hcm
        cases hcm
      have inp_cases : ∀ c ∈ (gates.get j).inputs,
          c < N ∨ ∃ k : Fin gates.length, (k : ℕ) < j ∧ c = N + (k : ℕ) := by
        intro c hc
        have := hlt j c hc
        by_cases h : c < N
        · exact Or.inl h
        · right
          exact ⟨⟨c - N, by have := j.isLt; omega⟩, by simp; omega, by simp; omega⟩
      have unif : ∀ c ∈ (gates.get j).inputs, ∀ s s', St c s → St c s' → Sp j s s' := by
        intro c hc s s' hs hs'
        rcases inp_cases c hc with hcN | ⟨k, hkj, rfl⟩
        · have e1 := st_input gates St hSt c hcN s hs
          have e2 := st_input gates St hSt c hcN s' hs'
          have : s = s' := Fin.ext (by omega)
          subst this
          exact Sp_refl _ _
        · rcases hops' _ (List.get_mem gates k) with hk | hk
          · exact absurd hs (st_and gates St hSt k hk s)
          · exact Sp_gen j k hkj hk (inp_cm _ hc) s s' hs hs'
      have Sj : ∀ s, St (N + (j : ℕ)) s ↔ ∃ c ∈ (gates.get j).inputs, St c s := fun s =>
        ⟨st_or gates St hSt hlt j hor s, fun ⟨c, hc, h⟩ => st_or_intro gates St hSt j hor s c hc h⟩
      have SjL : ∀ s, St (N + (j : ℕ)) s → s ∈ L i0 := Srel j hcm
      have StL : ∀ c ∈ (gates.get j).inputs, ∀ s, St c s → s ∈ L i0 :=
        fun c hc s hs => SjL s ((Sj s).2 ⟨c, hc, hs⟩)
      -- inputs are not anchored when they reach a good block
      have noAnch : ∀ c ∈ (gates.get j).inputs, ∀ F : Finset (Fin N), p0 ∉ F → p1 ∉ F → Un j F →
          ∀ s, St c s → s ∈ F →
          ev c (fun v : Fin N => decide (v = p0)) = false ∧ ev c (fun v : Fin N => decide (v = p1)) = false := by
        intro c hc F h0 h1 hu s hs hsF
        rcases inp_cases c hc with hcN | ⟨k, hkj, rfl⟩
        · have e1 := st_input gates St hSt c hcN s hs
          have hcs : (⟨c, hcN⟩ : Fin N) = s := Fin.ext (by simp; omega)
          have v0 := evI ⟨c, hcN⟩ (fun v : Fin N => decide (v = p0))
          have v1 := evI ⟨c, hcN⟩ (fun v : Fin N => decide (v = p1))
          simp only at v0 v1
          rw [v0, v1, hcs]
          constructor
          · simp only [decide_eq_false_iff_not]
            intro e
            rw [e] at hsF
            exact h0 hsF
          · simp only [decide_eq_false_iff_not]
            intro e
            rw [e] at hsF
            exact h1 hsF
        · rcases hops' _ (List.get_mem gates k) with hk | hk
          · exact absurd hs (st_and gates St hSt k hk s)
          · have hU := (hUn j F).1 hu k hkj hk (inp_cm _ hc)
            constructor
            · by_contra h
              exact hU (Or.inl (by simpa using h)) s hsF hs
            · by_contra h
              exact hU (Or.inr (by simpa using h)) s hsF hs
      obtain ⟨Aj, hAj⟩ : ∃ P : Prop, P ↔ (ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨
          ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)) = true) := ⟨_, Iff.rfl⟩
      obtain ⟨M, hM⟩ : ∃ M : Finset (Fin N), ∀ r, r ∈ M ↔ (r ∈ L i0 ∧ ∃ s, St (N + (j : ℕ)) s ∧ Sp j r s) :=
        ⟨(L i0).filter (fun r => ∃ s, St (N + (j : ℕ)) s ∧ Sp j r s), fun r => Finset.mem_filter⟩
      have SjM : ∀ s, St (N + (j : ℕ)) s → s ∈ M := fun s hs => (hM s).2 ⟨SjL s hs, s, hs, Sp_refl _ _⟩
      have M_cl : ∀ r r', r' ∈ L i0 → Sp j r r' → r ∈ M → r' ∈ M := by
        intro r r' hr' h hr
        obtain ⟨_, s, hs, hrs⟩ := (hM r).1 hr
        exact (hM r').2 ⟨hr', s, hs, Sp_trans _ _ _ _ (Sp_symm _ _ _ h) hrs⟩
      have hSp1 : ∀ r r', r ∈ L i0 → r' ∈ L i0 →
          (Sp ((j : ℕ) + 1) r r' ↔ (Sp j r r' ∨ (r ∈ M ∧ r' ∈ M))) := by
        intro r r' hr hr'
        constructor
        · intro h
          by_cases hrM : r ∈ M
          · have hClM : Cl ((j : ℕ) + 1) M := by
              rw [hCl]
              intro i hi hor' hc' s hs s' hs' hst hst'
              rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
              · have := Sp_gen j i hi hor' hc' s s' hst hst'
                exact ⟨M_cl s s' hs' this, M_cl s' s hs (Sp_symm _ _ _ this)⟩
              · have hij : i = j := Fin.ext hi
                rw [hij] at hst hst'
                exact ⟨fun _ => SjM s' hst', fun _ => SjM s hst⟩
            exact Or.inr ⟨hrM, ((hSp _ r r').1 h M hClM).1 hrM⟩
          · have hClX : Cl ((j : ℕ) + 1) ((L i0).filter (fun x => Sp j r x)) := by
              rw [hCl]
              intro i hi hor' hc' s hs s' hs' hst hst'
              simp only [Finset.mem_filter]
              rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
              · have := Sp_gen j i hi hor' hc' s s' hst hst'
                exact ⟨fun h1 => ⟨hs', Sp_trans _ _ _ _ h1.2 this⟩,
                  fun h1 => ⟨hs, Sp_trans _ _ _ _ h1.2 (Sp_symm _ _ _ this)⟩⟩
              · have hij : i = j := Fin.ext hi
                rw [hij] at hst hst'
                exact ⟨fun h1 => absurd (M_cl s r hr (Sp_symm _ _ _ h1.2) (SjM s hst)) hrM,
                  fun h1 => absurd (M_cl s' r hr (Sp_symm _ _ _ h1.2) (SjM s' hst')) hrM⟩
            have := ((hSp _ r r').1 h _ hClX).1 (Finset.mem_filter.2 ⟨hr, Sp_refl _ _⟩)
            exact Or.inl (Finset.mem_filter.1 this).2
        · rintro (h | ⟨hrM, hr'M⟩)
          · exact Sp_mono _ _ _ h
          · obtain ⟨_, t, ht, hrt⟩ := (hM r).1 hrM
            obtain ⟨_, t', ht', hrt'⟩ := (hM r').1 hr'M
            refine (hSp _ r r').2 (fun X hX => ?_)
            have e1 := (hSp _ r t).1 (Sp_mono _ _ _ hrt) X hX
            have e2 := (hSp _ r' t').1 (Sp_mono _ _ _ hrt') X hX
            have e3 := (hCl _ X).1 hX j (Nat.lt_succ_self _) hor hcm t (SjL t ht) t' (SjL t' ht') ht ht'
            exact e1.trans (e3.trans e2.symm)
      have cls1 : ∀ r, r ∈ L i0 → (L i0).filter (fun x => Sp ((j : ℕ) + 1) r x) =
          if r ∈ M then M else (L i0).filter (fun x => Sp j r x) := by
        intro r hr
        by_cases hrM : r ∈ M
        · rw [if_pos hrM]
          ext x
          rw [Finset.mem_filter]
          constructor
          · rintro ⟨hx, h⟩
            rcases (hSp1 r x hr hx).1 h with h | ⟨_, hxM⟩
            · exact M_cl r x hx h hrM
            · exact hxM
          · intro hxM
            have hx := ((hM x).1 hxM).1
            exact ⟨hx, (hSp1 r x hr hx).2 (Or.inr ⟨hrM, hxM⟩)⟩
        · rw [if_neg hrM]
          ext x
          rw [Finset.mem_filter, Finset.mem_filter]
          constructor
          · rintro ⟨hx, h⟩
            rcases (hSp1 r x hr hx).1 h with h | ⟨h', _⟩
            · exact ⟨hx, h⟩
            · exact absurd h' hrM
          · rintro ⟨hx, h⟩
            exact ⟨hx, (hSp1 r x hr hx).2 (Or.inl h)⟩
      have hUn1 : ∀ b, Un ((j : ℕ) + 1) b ↔ (Un j b ∧ (Aj → ∀ s ∈ b, ¬ St (N + (j : ℕ)) s)) := by
        intro b
        rw [hUn, hUn, hAj]
        constructor
        · intro h
          exact ⟨fun i hi => h i (by omega), fun ha => h j (Nat.lt_succ_self _) hor hcm ha⟩
        · rintro ⟨h, h'⟩ i hi hor' hc' ha
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
          · exact h i hi hor' hc' ha
          · have hij : i = j := Fin.ext hi
            subst hij
            exact h' ha
      have memcls : ∀ (k : ℕ) r, r ∈ L i0 → r ∈ (L i0).filter (fun x => Sp k r x) :=
        fun k r hr => Finset.mem_filter.2 ⟨hr, Sp_refl _ _⟩
      set K := (UB j).filter (fun b => ¬ ∀ x ∈ b, x ∉ M) with hKdef
      set K' := (UB ((j : ℕ) + 1)).filter (fun b => ¬ ∀ x ∈ b, x ∉ M) with hK'def
      have hsplitj : ((UB j).filter (fun b => ∀ x ∈ b, x ∉ M)).card + K.card = (UB j).card :=
        Finset.card_filter_add_card_filter_not _
      have hsplit1 : ((UB ((j : ℕ) + 1)).filter (fun b => ∀ x ∈ b, x ∉ M)).card + K'.card =
          (UB ((j : ℕ) + 1)).card :=
        Finset.card_filter_add_card_filter_not _
      have hA : (UB ((j : ℕ) + 1)).filter (fun b => ∀ x ∈ b, x ∉ M) =
          (UB j).filter (fun b => ∀ x ∈ b, x ∉ M) := by
        ext b
        rw [Finset.mem_filter, Finset.mem_filter, hUB', hUB']
        constructor
        · rintro ⟨⟨⟨r, hr, hb⟩, h0, h1, hu⟩, hd⟩
          have hrM : r ∉ M := hd r (by rw [hb]; exact memcls _ r hr)
          rw [cls1 r hr, if_neg hrM] at hb
          exact ⟨⟨⟨r, hr, hb⟩, h0, h1, ((hUn1 b).1 hu).1⟩, hd⟩
        · rintro ⟨⟨⟨r, hr, hb⟩, h0, h1, hu⟩, hd⟩
          have hrM : r ∉ M := hd r (by rw [hb]; exact memcls _ r hr)
          refine ⟨⟨⟨r, hr, ?_⟩, h0, h1, (hUn1 b).2 ⟨hu, fun _ s hs hst => hd s hs (SjM s hst)⟩⟩, hd⟩
          rw [cls1 r hr, if_neg hrM]
          exact hb
      have hK1 : ∀ b ∈ K', b = M := by
        intro b hb
        rw [hK'def, Finset.mem_filter, hUB'] at hb
        obtain ⟨⟨⟨r, hr, hb'⟩, _, _, _⟩, hnd⟩ := hb
        push_neg at hnd
        obtain ⟨x, hxb, hxM⟩ := hnd
        rw [cls1 r hr] at hb'
        by_cases hrM : r ∈ M
        · rw [if_pos hrM] at hb'
          exact hb'
        · rw [if_neg hrM] at hb'
          rw [hb', Finset.mem_filter] at hxb
          exact absurd (M_cl x r hr (Sp_symm _ _ _ hxb.2) hxM) hrM
      have hK1card : K'.card ≤ 1 :=
        Finset.card_le_one.2 (fun a ha b hb => (hK1 a ha).trans (hK1 b hb).symm)
      have hKmem : ∀ b ∈ K, ∃ r ∈ M, b = (L i0).filter (fun x => Sp j r x) ∧
          p0 ∉ b ∧ p1 ∉ b ∧ Un j b := by
        intro b hb
        rw [hKdef, Finset.mem_filter, hUB'] at hb
        obtain ⟨⟨⟨r, hr, hb'⟩, h0, h1, hu⟩, hnd⟩ := hb
        push_neg at hnd
        obtain ⟨x, hxb, hxM⟩ := hnd
        have hx' := hxb
        rw [hb', Finset.mem_filter] at hx'
        exact ⟨r, M_cl x r hr (Sp_symm _ _ _ hx'.2) hxM, hb', h0, h1, hu⟩
      have fdef : ∀ c : ℕ, ∃ F : Finset (Fin N), ∀ r, r ∈ F ↔ (r ∈ L i0 ∧ ∃ s, St c s ∧ Sp j r s) :=
        fun c => ⟨(L i0).filter (fun r => ∃ s, St c s ∧ Sp j r s), fun r => Finset.mem_filter⟩
      choose f hf using fdef
      have fsub : ∀ c ∈ (gates.get j).inputs, ∀ s, St c s → s ∈ f c :=
        fun c hc s hs => (hf c s).2 ⟨StL c hc s hs, s, hs, Sp_refl _ _⟩
      have hKf : ∀ b ∈ K, ∃ c ∈ (gates.get j).inputs, b = f c := by
        intro b hb
        obtain ⟨r, hrM, hb', _⟩ := hKmem b hb
        obtain ⟨_, s, hs, hrs⟩ := (hM r).1 hrM
        obtain ⟨c, hc, hcs⟩ := (Sj s).1 hs
        refine ⟨c, hc, ?_⟩
        rw [hb']
        ext x
        rw [Finset.mem_filter, hf]
        constructor
        · rintro ⟨hx, hrx⟩
          exact ⟨hx, s, hcs, Sp_trans _ _ _ _ (Sp_symm _ _ _ hrx) hrs⟩
        · rintro ⟨hx, s', hs', hxs'⟩
          exact ⟨hx, Sp_trans _ _ _ _ hrs (Sp_trans _ _ _ _ (unif c hc s s' hcs hs') (Sp_symm _ _ _ hxs'))⟩
      have hKsub : K ⊆ (gates.get j).inputs.toFinset.image f := by
        intro b hb
        obtain ⟨c, hc, rfl⟩ := hKf b hb
        exact Finset.mem_image.2 ⟨c, List.mem_toFinset.2 hc, rfl⟩
      have hinpcard : (gates.get j).inputs.toFinset.card ≤ 2 :=
        (List.toFinset_card_le _).trans ((hops _ (List.get_mem gates j)).2)
      have himgcard : ((gates.get j).inputs.toFinset.image f).card ≤ 2 :=
        Finset.card_image_le.trans hinpcard
      have hKcard : K.card ≤ 2 := (Finset.card_le_card hKsub).trans himgcard
      have Kne : ∀ b ∈ K, ∃ r ∈ M, r ∈ b := by
        intro b hb
        obtain ⟨r, hrM, hb', _⟩ := hKmem b hb
        exact ⟨r, hrM, by rw [hb']; exact memcls _ r ((hM r).1 hrM).1⟩
      have MU_r : M ∈ UB ((j : ℕ) + 1) → ∃ r ∈ M, True := by
        intro hMU
        rw [hUB'] at hMU
        obtain ⟨⟨r, hr, hb⟩, _⟩ := hMU
        exact ⟨r, by rw [hb]; exact memcls _ r hr, trivial⟩
      have hMnotAn : M ∈ UB ((j : ℕ) + 1) → ¬ Aj := by
        intro hMU ha
        obtain ⟨r, hrM, _⟩ := MU_r hMU
        rw [hUB'] at hMU
        obtain ⟨_, _, _, hu⟩ := hMU
        obtain ⟨_, s, hs, _⟩ := (hM r).1 hrM
        exact ((hUn1 M).1 hu).2 ha s (SjM s hs) hs
      have hI : M ∈ UB ((j : ℕ) + 1) → 1 ≤ K.card := by
        intro hMU
        obtain ⟨r, hrM, _⟩ := MU_r hMU
        have hr := ((hM r).1 hrM).1
        rw [hUB'] at hMU
        obtain ⟨_, h0, h1, hu⟩ := hMU
        have hsub : (L i0).filter (fun x => Sp j r x) ⊆ M := fun x hx =>
          M_cl r x (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx).2 hrM
        apply Finset.card_pos.2
        refine ⟨(L i0).filter (fun x => Sp j r x), ?_⟩
        rw [hKdef, Finset.mem_filter, hUB']
        refine ⟨⟨⟨r, hr, rfl⟩, fun h => h0 (hsub h), fun h => h1 (hsub h),
          Un_sub j _ M hsub ((hUn1 M).1 hu).1⟩, ?_⟩
        intro hall
        exact hall r (memcls _ r hr) hrM
      have hMK' : M ∈ UB ((j : ℕ) + 1) → 1 ≤ K'.card := by
        intro hMU
        obtain ⟨r, hrM, _⟩ := MU_r hMU
        apply Finset.card_pos.2
        refine ⟨M, ?_⟩
        rw [hK'def, Finset.mem_filter]
        exact ⟨hMU, fun hall => hall r hrM hrM⟩
      have hK'M : 1 ≤ K'.card → M ∈ UB ((j : ℕ) + 1) := by
        intro h
        obtain ⟨b, hb⟩ := Finset.card_pos.1 h
        have hbM := hK1 b hb
        rw [hK'def, Finset.mem_filter] at hb
        rw [← hbM]
        exact hb.1
      have hII : K.card = 2 → M ∈ UB ((j : ℕ) + 1) := by
        intro h2
        have hKeq : K = (gates.get j).inputs.toFinset.image f :=
          Finset.eq_of_subset_of_card_le hKsub (by omega)
        have fK : ∀ c ∈ (gates.get j).inputs, f c ∈ K := fun c hc => by
          rw [hKeq]
          exact Finset.mem_image.2 ⟨c, List.mem_toFinset.2 hc, rfl⟩
        have Kgood : ∀ b ∈ K, p0 ∉ b ∧ p1 ∉ b ∧ Un j b := fun b hb => by
          obtain ⟨_, _, _, h⟩ := hKmem b hb
          exact h
        have Mf : ∀ x ∈ M, ∃ c ∈ (gates.get j).inputs, x ∈ f c := fun x hx => by
          obtain ⟨hxL, s, hs, hxs⟩ := (hM x).1 hx
          obtain ⟨c, hc, hcs⟩ := (Sj s).1 hs
          exact ⟨c, hc, (hf c x).2 ⟨hxL, s, hcs, hxs⟩⟩
        obtain ⟨b0, hb0⟩ := Finset.card_pos.1 (by omega : 0 < K.card)
        obtain ⟨r, hrM, _⟩ := Kne b0 hb0
        have hrL := ((hM r).1 hrM).1
        rw [hUB']
        refine ⟨⟨r, hrL, ?_⟩, ?_, ?_, ?_⟩
        · rw [cls1 r hrL, if_pos hrM]
        · intro hp
          obtain ⟨c, hc, hpc⟩ := Mf p0 hp
          exact (Kgood _ (fK c hc)).1 hpc
        · intro hp
          obtain ⟨c, hc, hpc⟩ := Mf p1 hp
          exact (Kgood _ (fK c hc)).2.1 hpc
        · rw [hUn1]
          constructor
          · rw [hUn]
            intro i hi hor' hc' ha s hs hst
            obtain ⟨c, hc, hsc⟩ := Mf s hs
            exact ((hUn j _).1 (Kgood _ (fK c hc)).2.2) i hi hor' hc' ha s hsc hst
          · intro ha
            exfalso
            rw [hAj] at ha
            have anyin : ∀ x : Fin N → Bool, ev (N + (j : ℕ)) x = true →
                ∃ c ∈ (gates.get j).inputs, ev c x = true := fun x hx => (or_val gates ev evG j hor x).1 hx
            have finish : ∀ c ∈ (gates.get j).inputs, (ev c (fun v : Fin N => decide (v = p0)) = true ∨
                ev c (fun v : Fin N => decide (v = p1)) = true) → False := by
              intro c hc hcv
              obtain ⟨g0, g1, gu⟩ := Kgood _ (fK c hc)
              obtain ⟨r', hr'M, hr'⟩ := Kne _ (fK c hc)
              obtain ⟨_, s, hs, _⟩ := (hf c r').1 hr'
              have := noAnch c hc (f c) g0 g1 gu s hs (fsub c hc s hs)
              rcases hcv with h | h
              · rw [this.1] at h
                cases h
              · rw [this.2] at h
                cases h
            rcases ha with h | h
            · obtain ⟨c, hc, hcv⟩ := anyin _ h
              exact finish c hc (Or.inl hcv)
            · obtain ⟨c, hc, hcv⟩ := anyin _ h
              exact finish c hc (Or.inr hcv)
      -- two points of the first line meet any other line in at most one point
      have oneL : ∀ t : Fin N, t ≠ i0 → ∀ a b : Fin N, a ∈ L i0 → b ∈ L i0 → a ∈ L t → b ∈ L t → a = b := by
        intro t ht a b ha hb hat hbt
        have hc1 := hinter t i0 ht
        exact Finset.card_le_one.1 (by omega) a (Finset.mem_inter.2 ⟨hat, ha⟩) b (Finset.mem_inter.2 ⟨hbt, hb⟩)
      have trueAt : ∀ (t : Fin N) (s : Fin N), St (N + (j : ℕ)) s → s ∉ L t →
          ev (N + (j : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true := by
        intro t s hs hst
        exact st_true gates ev St hSt evI evG _ s _ hs (by simpa using hst)
      have hIII : (K.card = 2 ∨ (K.card = 1 ∧ K'.card = 0)) → j ∈ Xs := by
        intro hcase
        rw [hXs]
        refine ⟨hor, hcm, ?_, ?_⟩
        · intro t ht
          rcases hcase with h2 | ⟨h1, h0⟩
          · obtain ⟨b1, hb1, b2, hb2, hne12⟩ := Finset.one_lt_card.1 (by omega : 1 < K.card)
            obtain ⟨r1, hr1M, hb1', _⟩ := hKmem b1 hb1
            obtain ⟨r2, hr2M, hb2', _⟩ := hKmem b2 hb2
            obtain ⟨_, s1, hs1, hrs1⟩ := (hM r1).1 hr1M
            obtain ⟨_, s2, hs2, hrs2⟩ := (hM r2).1 hr2M
            by_cases h1t : s1 ∈ L t
            · by_cases h2t : s2 ∈ L t
              · exfalso
                have e := oneL t ht s1 s2 (SjL s1 hs1) (SjL s2 hs2) h1t h2t
                apply hne12
                rw [hb1', hb2', cls_eq j r1 s1 hrs1, cls_eq j r2 s2 hrs2, e]
              · exact trueAt t s2 hs2 h2t
            · exact trueAt t s1 hs1 h1t
          · obtain ⟨b, hbK⟩ := Finset.card_eq_one.1 h1
            have hb : b ∈ K := by rw [hbK]; exact Finset.mem_singleton_self b
            obtain ⟨r, hrM, hb', g0, g1, gu⟩ := hKmem b hb
            obtain ⟨hrL, s, hs, hrs⟩ := (hM r).1 hrM
            have hsb : s ∈ b := by rw [hb']; exact Finset.mem_filter.2 ⟨SjL s hs, hrs⟩
            by_cases hst : s ∈ L t
            · have hMnot : M ∉ UB ((j : ℕ) + 1) := fun h => by have := hMK' h; omega
              by_cases hA : Aj
              · rw [hAj] at hA
                rcases hA with h | h
                · have hp0t : p0 ∉ L t := by
                    intro hp
                    have := oneL t ht p0 s hp0 (SjL s hs) hp hst
                    rw [this] at g0
                    exact g0 hsb
                  exact ev_mono gates ev hops' hlt evI evG evB _ _ (fun v hv => by
                    simp only [decide_eq_true_eq] at hv ⊢
                    rw [hv]
                    exact hp0t) _ h
                · have hp1t : p1 ∉ L t := by
                    intro hp
                    have := oneL t ht p1 s hp1 (SjL s hs) hp hst
                    rw [this] at g1
                    exact g1 hsb
                  exact ev_mono gates ev hops' hlt evI evG evB _ _ (fun v hv => by
                    simp only [decide_eq_true_eq] at hv ⊢
                    rw [hv]
                    exact hp1t) _ h
              · have hex : ∃ x ∈ M, x ∉ b := by
                  by_contra hno
                  push_neg at hno
                  apply hMnot
                  rw [hUB']
                  refine ⟨⟨r, hrL, ?_⟩, fun h => g0 (hno _ h), fun h => g1 (hno _ h),
                    (hUn1 M).2 ⟨Un_sub j M b hno gu, fun ha => absurd ha hA⟩⟩
                  rw [cls1 r hrL, if_pos hrM]
                obtain ⟨x, hxM, hxb⟩ := hex
                obtain ⟨hxL, s2, hs2, hxs2⟩ := (hM x).1 hxM
                have hs2b : s2 ∉ b := by
                  intro h
                  rw [hb', Finset.mem_filter] at h
                  apply hxb
                  rw [hb']
                  exact Finset.mem_filter.2 ⟨hxL, Sp_trans _ _ _ _ h.2 (Sp_symm _ _ _ hxs2)⟩
                by_cases h2t : s2 ∈ L t
                · exfalso
                  have e := oneL t ht s s2 (SjL s hs) (SjL s2 hs2) hst h2t
                  rw [← e] at hs2b
                  exact hs2b hsb
                · exact trueAt t s2 hs2 h2t
            · exact trueAt t s hs hst
        · intro hall
          rcases hcase with h2 | ⟨h1, h0⟩
          · have hnA := hMnotAn (hII h2)
            obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos (l := (gates.get j).inputs) (by have := hne j; omega)
            apply hnA
            rw [hAj]
            rcases hall c hc with h | h
            · exact Or.inl ((or_val gates ev evG j hor _).2 ⟨c, hc, h⟩)
            · exact Or.inr ((or_val gates ev evG j hor _).2 ⟨c, hc, h⟩)
          · obtain ⟨b, hbK⟩ := Finset.card_eq_one.1 h1
            have hb : b ∈ K := by rw [hbK]; exact Finset.mem_singleton_self b
            obtain ⟨r, hrM, hb', g0, g1, gu⟩ := hKmem b hb
            obtain ⟨hrL, s, hs, hrs⟩ := (hM r).1 hrM
            have hsb : s ∈ b := by rw [hb']; exact Finset.mem_filter.2 ⟨SjL s hs, hrs⟩
            obtain ⟨c, hc, hcs⟩ := (Sj s).1 hs
            have := noAnch c hc b g0 g1 gu s hcs hsb
            rcases hall c hc with h | h
            · rw [this.1] at h
              cases h
            · rw [this.2] at h
              cases h
      rw [hA] at hsplit1
      have f3 : 1 ≤ K'.card → 1 ≤ K.card := fun h => hI (hK'M h)
      have f4 : K.card = 2 → 1 ≤ K'.card := fun h => hMK' (hII h)
      refine ⟨by omega, by omega, fun hj => ?_⟩
      by_contra hne'
      exact hj (hIII (by omega))
    · have hCl' : ∀ X, Cl ((j : ℕ) + 1) X ↔ Cl j X := by
        intro X
        rw [hCl, hCl]
        constructor
        · intro h i hi
          exact h i (by omega)
        · intro h i hi hor hc
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
          · exact h i hi hor hc
          · exfalso
            have : i = j := Fin.ext hi
            subst this
            exact hrel ⟨hor, hc⟩
      have hSp' : ∀ r r', Sp ((j : ℕ) + 1) r r' ↔ Sp j r r' := by
        intro r r'
        rw [hSp, hSp]
        exact forall_congr' fun X => by rw [hCl' X]
      have hUn' : ∀ b, Un ((j : ℕ) + 1) b ↔ Un j b := by
        intro b
        rw [hUn, hUn]
        constructor
        · intro h i hi
          exact h i (by omega)
        · intro h i hi hor hc
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
          · exact h i hi hor hc
          · exfalso
            have : i = j := Fin.ext hi
            subst this
            exact hrel ⟨hor, hc⟩
      have hEq : UB ((j : ℕ) + 1) = UB j := by
        ext b
        rw [hUB', hUB']
        simp only [hSp', hUn']
      rw [hEq]
      exact ⟨le_refl _, Nat.le_succ _, fun _ => rfl⟩
  -- the start
  have ub0 : (UB 0).card = q - 1 := by
    have hSp0 : ∀ r r', Sp 0 r r' ↔ r = r' := by
      intro r r'
      constructor
      · intro h
        have hX : Cl 0 {r} := (hCl 0 {r}).2 (fun i hi => absurd hi (Nat.not_lt_zero _))
        have := ((hSp 0 r r').1 h {r} hX).1 (Finset.mem_singleton_self r)
        exact (Finset.mem_singleton.1 this).symm
      · rintro rfl
        exact Sp_refl 0 r
    have hUn0 : ∀ b, Un 0 b := fun b => (hUn 0 b).2 (fun i hi => absurd hi (Nat.not_lt_zero _))
    have hEq : UB 0 = (L i0 \ {p0, p1}).image (fun r => ({r} : Finset (Fin N))) := by
      ext b
      rw [hUB', Finset.mem_image]
      constructor
      · rintro ⟨⟨r, hr, hb⟩, h0, h1, _⟩
        have hb' : b = {r} := by
          rw [hb]
          ext x
          simp only [Finset.mem_filter, hSp0, Finset.mem_singleton]
          constructor
          · rintro ⟨_, h⟩
            exact h.symm
          · rintro rfl
            exact ⟨hr, rfl⟩
        subst hb'
        refine ⟨r, ?_, rfl⟩
        simp only [Finset.mem_singleton] at h0 h1
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hr, fun e => h0 e.symm, fun e => h1 e.symm⟩
      · rintro ⟨r, hr, rfl⟩
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hr
        refine ⟨⟨r, hr.1, ?_⟩, ?_, ?_, hUn0 _⟩
        · ext x
          simp only [Finset.mem_filter, hSp0, Finset.mem_singleton]
          constructor
          · rintro rfl
            exact ⟨hr.1, rfl⟩
          · rintro ⟨_, h⟩
            exact h.symm
        · simp only [Finset.mem_singleton]
          exact fun e => hr.2.1 e.symm
        · simp only [Finset.mem_singleton]
          exact fun e => hr.2.2 e.symm
    rw [hEq, Finset.card_image_of_injective _ Finset.singleton_injective]
    have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L i0 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hp0
      · exact hp1
    have h1 := Finset.card_sdiff_add_card_eq_card hsub
    rw [Finset.card_pair hp01, hcard i0] at h1
    omega
  -- telescoping
  have tele : ∀ m, m ≤ gates.length →
      (UB 0).card ≤ (Xs.filter (fun g : Fin gates.length => (g : ℕ) < m)).card + (UB m).card := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      obtain ⟨_, h2, h3⟩ := step ⟨m, by omega⟩
      by_cases hx : (⟨m, by omega⟩ : Fin gates.length) ∈ Xs
      · have hf : Xs.filter (fun g : Fin gates.length => (g : ℕ) < m + 1) =
            insert (⟨m, by omega⟩ : Fin gates.length) (Xs.filter (fun g : Fin gates.length => (g : ℕ) < m)) := by
          ext g
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hg, hlt'⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt' with h | h
            · exact Or.inr ⟨hg, h⟩
            · exact Or.inl (Fin.ext h)
          · rintro (h | ⟨hg, h⟩)
            · subst h
              exact ⟨hx, Nat.lt_succ_self m⟩
            · exact ⟨hg, by omega⟩
        have hnot : (⟨m, by omega⟩ : Fin gates.length) ∉ Xs.filter (fun g : Fin gates.length => (g : ℕ) < m) := by
          simp
        rw [hf, Finset.card_insert_of_notMem hnot]
        simp only at h2
        omega
      · have hf : Xs.filter (fun g : Fin gates.length => (g : ℕ) < m + 1) = Xs.filter (fun g : Fin gates.length => (g : ℕ) < m) := by
          ext g
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hg, hlt'⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hlt' with h | h
            · exact ⟨hg, h⟩
            · exfalso
              have hgm : g = ⟨m, by omega⟩ := Fin.ext h
              rw [hgm] at hg
              exact hx hg
          · rintro ⟨hg, h⟩
            exact ⟨hg, by omega⟩
        rw [hf]
        have := h3 hx
        simp only at this
        omega
  refine ⟨step, ub0, ?_⟩
  have hfin := tele gates.length le_rfl
  have hall : Xs.filter (fun g : Fin gates.length => (g : ℕ) < gates.length) = Xs := by
    ext g
    simp [g.isLt]
  rw [hall, ub0] at hfin
  exact hfin
