import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (gateAt ReadsBack)

namespace PEqualNP.Outside.L_meta_1950

def gf {α : Type} (f : List α → Gate → α) (gs : List Gate) (x : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) x

lemma gf_cons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate) (x : List α) :
    gf f (g :: gs) x = gf f gs (x ++ [f x g]) := rfl

lemma gf_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (x : List α) :
    (gf f gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [gf]
  | cons g gs ih => rw [gf_cons, ih]; simp; omega

lemma gf_getD {α : Type} (f : List α → Gate → α) (gs : List Gate) (x : List α) (d : α) (w : ℕ)
    (hw : w < x.length) : (gf f gs x).getD w d = x.getD w d := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [gf_cons, ih _ (by simp only [List.length_append, List.length_singleton]; omega),
      List.getD_append _ _ _ _ hw]

lemma gf_split {α : Type} (f : List α → Gate → α) (gs : List Gate) (x : List α) (j : ℕ) :
    gf f gs x = gf f (gs.drop j) (gf f (gs.take j) x) := by
  simpa only [gf, List.foldl_append] using
    congrArg (fun l : List Gate => gf f l x) (List.take_append_drop j gs).symm

lemma gf_out {α : Type} (f : List α → Gate → α) (gs : List Gate) (x : List α) (d : α) (w : ℕ)
    (hw : x.length + gs.length ≤ w) : (gf f gs x).getD w d = d :=
  List.getD_eq_default _ _ (by rw [gf_length]; omega)

lemma gf_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (x : List α) (d : α) (k : ℕ)
    (hk : k < gs.length) :
    (gf f gs x).getD (x.length + k) d = f (gf f (gs.take k) x) gs[k] ∧
    ∀ r, r < x.length + k → (gf f (gs.take k) x).getD r d = (gf f gs x).getD r d := by
  have plen : (gf f (gs.take k) x).length = x.length + k := by
    rw [gf_length, List.length_take]; omega
  have split : gf f gs x = gf f (gs[k] :: gs.drop (k + 1)) (gf f (gs.take k) x) := by
    rw [gf_split f gs x k, List.drop_eq_getElem_cons hk]
  constructor
  · rw [split, gf_cons, gf_getD f (gs.drop (k + 1)) _ d (x.length + k)
      (by simp only [List.length_append, List.length_singleton, plen]; omega)]
    rw [List.getD_append_right _ _ _ _ (by omega), plen, Nat.sub_self]
    rfl
  · intro r hr
    rw [split, gf_cons, gf_getD f (gs.drop (k + 1)) _ d r
      (by simp only [List.length_append, List.length_singleton, plen]; omega),
      List.getD_append _ _ _ _ (by omega)]

lemma wires_eq (C : Circuit) (z : List Bool) :
    C.wires z = gf (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates z := rfl

lemma deg_eq (C : Circuit) (n : ℕ) (m : Finset ℕ) :
    C.lineDegrees n m =
      gf (fun d g => g.lineDegree d) C.gates ((List.range n).map fun i => if i ∈ m then 1 else 0) :=
  rfl

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hk

abbrev V (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (Fin.append x y))).getD w false

abbrev pd (N : ℕ) (C : Circuit) (w : ℕ) : ℕ := (C.lineDegrees (N + N) (Finset.range N)).getD w 0

abbrev ld (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0

lemma gateV (N : ℕ) (C : Circuit) (hRB : ReadsBack (N + N) C) (x y : Fin N → Bool) (k : ℕ)
    (hk : k < C.gates.length) :
    V N C x y (N + N + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map (V N C x y)) := by
  have hl : (List.ofFn (Fin.append x y)).length = N + N := by simp
  obtain ⟨h1, h2⟩ := gf_gate (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn (Fin.append x y)) false k hk
  rw [hl] at h1 h2
  have hin : ∀ r ∈ (gateAt C k).inputs, r < N + N + k := hRB k hk
  rw [gateAt_eq C k hk] at hin ⊢
  change (gf _ C.gates (List.ofFn (Fin.append x y))).getD (N + N + k) false = _
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro r hr
  exact h2 r (hin r hr)

lemma and_iff (N : ℕ) (C : Circuit) (hRB : ReadsBack (N + N) C) (x y : Fin N → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) :
    V N C x y (N + N + k) = true ↔ ∀ r ∈ (gateAt C k).inputs, V N C x y r = true := by
  rw [gateV N C hRB x y k hk, hop]
  simp [GateOp.eval]

lemma or_iff (N : ℕ) (C : Circuit) (hRB : ReadsBack (N + N) C) (x y : Fin N → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) :
    V N C x y (N + N + k) = true ↔ ∃ r ∈ (gateAt C k).inputs, V N C x y r = true := by
  rw [gateV N C hRB x y k hk, hop]
  simp [GateOp.eval]

lemma deg_in (N : ℕ) (C : Circuit) (m : Finset ℕ) (r : ℕ) (hr : r < N + N) :
    (C.lineDegrees (N + N) m).getD r 0 = if r ∈ m then 1 else 0 := by
  rw [deg_eq, gf_getD _ _ _ _ _ (by simp; exact hr)]
  rw [List.getD_eq_getElem _ _ (by simp; exact hr)]
  simp

lemma deg_out (N : ℕ) (C : Circuit) (m : Finset ℕ) (r : ℕ) (hr : N + N + C.gates.length ≤ r) :
    (C.lineDegrees (N + N) m).getD r 0 = 0 := by
  rw [deg_eq]
  exact gf_out _ _ _ _ _ (by simp; omega)

lemma deg_and (N : ℕ) (C : Circuit) (hRB : ReadsBack (N + N) C) (m : Finset ℕ) (k : ℕ)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) :
    (C.lineDegrees (N + N) m).getD (N + N + k) 0 =
      ((gateAt C k).inputs.map (fun i => (C.lineDegrees (N + N) m).getD i 0)).sum := by
  have hl : ((List.range (N + N)).map fun i => if i ∈ m then 1 else 0).length = N + N := by simp
  obtain ⟨h1, h2⟩ := gf_gate (fun d g => g.lineDegree d) C.gates
    ((List.range (N + N)).map fun i => if i ∈ m then 1 else 0) 0 k hk
  rw [hl] at h1 h2
  have hin : ∀ r ∈ (gateAt C k).inputs, r < N + N + k := hRB k hk
  rw [gateAt_eq C k hk] at hin hop ⊢
  rw [deg_eq, h1]
  unfold Gate.lineDegree
  rw [if_pos hop]
  congr 1
  apply List.map_congr_left
  intro r hr
  exact h2 r (hin r hr)

lemma mixed_gate (N : ℕ) (C : Circuit) (r : ℕ) (hp : 0 < pd N C r) (hl : 0 < ld N C r) :
    N + N ≤ r ∧ r < N + N + C.gates.length := by
  constructor
  · by_contra h
    have h' : r < N + N := by omega
    have e1 := deg_in N C (Finset.range N) r h'
    have e2 := deg_in N C (Finset.Ico N (N + N)) r h'
    simp only [pd, ld] at hp hl
    rw [e1] at hp
    rw [e2] at hl
    by_cases h1 : r ∈ Finset.range N
    · by_cases h2 : r ∈ Finset.Ico N (N + N)
      · simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2
        omega
      · rw [if_neg h2] at hl
        omega
    · rw [if_neg h1] at hp
      omega
  · by_contra h
    have := deg_out N C (Finset.range N) r (by omega)
    simp only [pd] at hp
    omega

lemma two_in (l : List ℕ) (hl : l.length = 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∀ r ∈ l, r = a ∨ r = b := by
  match l, hl with
  | [u, v], _ =>
    intro r hr
    simp at ha hb hr
    omega

lemma gop (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (k : ℕ) (hk : k < C.gates.length) :
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2 := by
  rw [gateAt_eq C k hk]
  exact hg _ (List.getElem_mem hk)

def edgeR (N : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ f : Fin C.gates.length, b = N + N + f.val ∧ a ∈ (C.gates.get f).inputs

def coneP (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (0 < pd N C (N + N + j) ∧ 0 < ld N C (N + N + j)) ∧
    Relation.ReflTransGen (edgeR N C) (N + N + j) C.output

def gokP (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.or ∨
    ∃ i ∈ (gateAt C j).inputs, ld N C i = 0 ∧ V N C x (fun _ => false) i = true

def stepP (N : ℕ) (C : Circuit) (x : Fin N → Bool) (a b : ℕ) : Prop :=
  coneP N C b ∧ N + N + a ∈ (gateAt C b).inputs ∧ gokP N C x b

def lvxP (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j : ℕ) : Prop :=
  coneP N C j ∧ gokP N C x j ∧ ∃ j6 : ℕ, N + N + j6 = C.output ∧
    Relation.ReflTransGen (stepP N C x) j j6

def slotP (N : ℕ) (C : Circuit) (h j : ℕ) : Prop :=
  coneP N C j ∧ h ∈ (gateAt C j).inputs ∧ pd N C h = 0

lemma pass (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hRB : ReadsBack (N + N) C)
    (hY : ∀ (w : ℕ) (xa ya yb : Fin N → Bool), ld N C w = 0 → V N C xa ya w = V N C xa yb w)
    (x y : Fin N → Bool) (k : ℕ) (hk : k < C.gates.length) (hgok : gokP N C x k) (u : ℕ)
    (hu : u ∈ (gateAt C k).inputs) (hne : 0 < ld N C u) (hv : V N C x y u = true) :
    V N C x y (N + N + k) = true := by
  obtain ⟨hop, hlen⟩ := gop C hg k hk
  rcases hop with hop | hop
  · rcases hgok with h | ⟨i, hi, hli, hvi⟩
    · rw [hop] at h
      cases h
    · have hiy : V N C x y i = true := by
        rw [hY i x y (fun _ => false) hli]
        exact hvi
      have hne' : u ≠ i := by
        intro h
        rw [h] at hne
        omega
      rw [and_iff N C hRB x y k hk hop]
      intro r hr
      rcases two_in _ hlen u i hu hi hne' r hr with h | h
      · rw [h]; exact hv
      · rw [h]; exact hiy
  · rw [or_iff N C hRB x y k hk hop]
    exact ⟨u, hu, hv⟩

lemma up (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hRB : ReadsBack (N + N) C)
    (hY : ∀ (w : ℕ) (xa ya yb : Fin N → Bool), ld N C w = 0 → V N C xa ya w = V N C xa yb w)
    (hX : ∀ (w : ℕ) (xa xb ya : Fin N → Bool), pd N C w = 0 → V N C xa ya w = V N C xb ya w)
    (hZ : ∀ w : ℕ, V N C (fun _ => false) (fun _ => false) w = false)
    (x y : Fin N → Bool) (h j : ℕ) (hs : slotP N C h j) (hl : lvxP N C x j)
    (hv : V N C (fun _ => false) y h = true) : V N C x y C.output = true := by
  obtain ⟨hc, hin, hpd⟩ := hs
  obtain ⟨_, hgok, j6, ho, hpath⟩ := hl
  have hld : 0 < ld N C h := by
    by_contra h0
    have := hY h (fun _ => false) y (fun _ => false) (by omega)
    rw [hZ] at this
    rw [this] at hv
    cases hv
  have hxy : V N C x y h = true := by
    rw [hX h x (fun _ => false) y hpd]
    exact hv
  have hstart : V N C x y (N + N + j) = true :=
    pass N C hg hRB hY x y j hc.1 hgok h hin hld hxy
  have key : ∀ b, Relation.ReflTransGen (stepP N C x) j b →
      coneP N C b ∧ V N C x y (N + N + b) = true := by
    intro b hb
    induction hb with
    | refl => exact ⟨hc, hstart⟩
    | tail _ hst ih =>
      obtain ⟨hcb, hinb, hgokb⟩ := hst
      exact ⟨hcb, pass N C hg hRB hY x y _ hcb.1 hgokb _ hinb ih.1.2.1.2 ih.2⟩
  have := (key j6 hpath).2
  rw [ho] at this
  exact this

lemma down (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hRB : ReadsBack (N + N) C)
    (hKM : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, ld N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, pd N C h = 0))
    (hY : ∀ (w : ℕ) (xa ya yb : Fin N → Bool), ld N C w = 0 → V N C xa ya w = V N C xa yb w)
    (hX : ∀ (w : ℕ) (xa xb ya : Fin N → Bool), pd N C w = 0 → V N C xa ya w = V N C xb ya w)
    (x y : Fin N → Bool) (j9 : ℕ) (ho : N + N + j9 = C.output) :
    ∀ j, coneP N C j → V N C x y (N + N + j) = true →
      V N C x (fun _ => false) (N + N + j) = false →
      Relation.ReflTransGen (stepP N C x) j j9 →
      ∃ h j', slotP N C h j' ∧ lvxP N C x j' ∧ V N C (fun _ => false) y h = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hc hv1 hv0 hpath
  have hk := hc.1
  obtain ⟨hop, hlen⟩ := gop C hg j hk
  obtain ⟨r, hr, hr1, hr0, hgok⟩ : ∃ r ∈ (gateAt C j).inputs, V N C x y r = true ∧
      V N C x (fun _ => false) r = false ∧ gokP N C x j := by
    rcases hop with hop | hop
    · rcases hKM j hk hop with ⟨i0, hi0, hl0⟩ | hall
      · have hall1 := (and_iff N C hRB x y j hk hop).mp hv1
        have hi0v : V N C x (fun _ => false) i0 = true := by
          rw [← hY i0 x y (fun _ => false) hl0]
          exact hall1 i0 hi0
        have hnot : ¬ ∀ r ∈ (gateAt C j).inputs, V N C x (fun _ => false) r = true := by
          intro h
          rw [(and_iff N C hRB x _ j hk hop).mpr h] at hv0
          cases hv0
        push Not at hnot
        obtain ⟨r, hr, hr0⟩ := hnot
        exact ⟨r, hr, hall1 r hr, Bool.eq_false_iff.mpr hr0, Or.inr ⟨i0, hi0, hl0, hi0v⟩⟩
      · exfalso
        have e := deg_and N C hRB (Finset.range N) j hk hop
        have hz : ((gateAt C j).inputs.map
            (fun i => (C.lineDegrees (N + N) (Finset.range N)).getD i 0)).sum = 0 := by
          apply List.sum_eq_zero
          intro a ha
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
          exact hall i hi
        have hp := hc.2.1.1
        simp only [pd] at hp
        omega
    · obtain ⟨r, hr, hr1⟩ := (or_iff N C hRB x y j hk hop).mp hv1
      have hr0 : V N C x (fun _ => false) r = false := by
        cases hb : V N C x (fun _ => false) r
        · rfl
        · have := (or_iff N C hRB x _ j hk hop).mpr ⟨r, hr, hb⟩
          rw [hv0] at this
          cases this
      exact ⟨r, hr, hr1, hr0, Or.inl hop⟩
  by_cases hpr : pd N C r = 0
  · refine ⟨r, j, ⟨hc, hr, hpr⟩, ⟨hc, hgok, j9, ho, hpath⟩, ?_⟩
    rw [← hX r x (fun _ => false) y hpr]
    exact hr1
  · have hlr : 0 < ld N C r := by
      by_contra h0
      have := hY r x y (fun _ => false) (by omega)
      rw [hr1, hr0] at this
      cases this
    have hmg := mixed_gate N C r (by omega) hlr
    have hrlt : r < N + N + j := hRB j hk r hr
    have hr' : r ∈ (C.gates.get ⟨j, hk⟩).inputs := by
      rw [gateAt_eq C j hk] at hr
      simpa using hr
    obtain ⟨j', rfl⟩ : ∃ j', r = N + N + j' := ⟨r - (N + N), by omega⟩
    have hj'k : j' < C.gates.length := by omega
    have hcone' : coneP N C j' :=
      ⟨hj'k, ⟨by omega, hlr⟩, Relation.ReflTransGen.head ⟨hrlt, ⟨j, hk⟩, rfl, hr'⟩ hc.2.2⟩
    exact ih j' (by omega) hcone' hr1 hr0 (Relation.ReflTransGen.head ⟨hc, hr, hgok⟩ hpath)

lemma outgate (N : ℕ) (C : Circuit)
    (hY : ∀ (w : ℕ) (xa ya yb : Fin N → Bool), ld N C w = 0 → V N C xa ya w = V N C xa yb w)
    (hX : ∀ (w : ℕ) (xa xb ya : Fin N → Bool), pd N C w = 0 → V N C xa ya w = V N C xb ya w)
    (xp yw : Fin N → Bool) (hacc : V N C xp yw C.output = true)
    (hs0 : V N C xp (fun _ => false) C.output = false)
    (hs1 : V N C (fun _ => false) yw C.output = false) :
    ∃ j9, N + N + j9 = C.output ∧ coneP N C j9 := by
  have hl : 0 < ld N C C.output := by
    by_contra h0
    rw [hY _ xp yw (fun _ => false) (by omega), hs0] at hacc
    cases hacc
  have hp : 0 < pd N C C.output := by
    by_contra h0
    rw [hX _ xp (fun _ => false) yw (by omega), hs1] at hacc
    cases hacc
  have hmg := mixed_gate N C _ hp hl
  obtain ⟨j9, hj9⟩ : ∃ j9, C.output = N + N + j9 := ⟨C.output - (N + N), by omega⟩
  refine ⟨j9, hj9.symm, by omega, ⟨by rw [← hj9]; exact hp, by rw [← hj9]; exact hl⟩, ?_⟩
  rw [← hj9]

end PEqualNP.Outside.L_meta_1950

theorem PEqualNP.Outside.L_meta_1950 : (∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → ∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14) := by
  intro H N I _ C hgr hKM hC4 hex hacc hsnd mixed hmixed cone hcone gok hgok step hstep lvx hlvx
    slot hslot ap hap lh hlh lpw hlpw ppw hppw lps hlps pps hpps
  subst hmixed hcone hgok hstep hlvx hslot hap hlh hlpw hppw hlps hpps
  obtain ⟨hg, hRB⟩ := hgr
  have HC := H N C hg hRB hKM
  have hY : ∀ (w : ℕ) (xa ya yb : Fin N → Bool), PEqualNP.Outside.L_meta_1950.ld N C w = 0 →
      PEqualNP.Outside.L_meta_1950.V N C xa ya w = PEqualNP.Outside.L_meta_1950.V N C xa yb w :=
    fun w xa ya yb => (HC.1 w xa xa ya yb).1
  have hX : ∀ (w : ℕ) (xa xb ya : Fin N → Bool), PEqualNP.Outside.L_meta_1950.pd N C w = 0 →
      PEqualNP.Outside.L_meta_1950.V N C xa ya w = PEqualNP.Outside.L_meta_1950.V N C xb ya w :=
    fun w xa xb ya => (HC.1 w xa xb ya ya).2.1
  have hZ : ∀ w : ℕ, PEqualNP.Outside.L_meta_1950.V N C (fun _ => false) (fun _ => false) w = false :=
    fun w => (HC.1 w (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)).2.2
  have c0 : (Finset.univ.filter (fun l : Fin N => (fun _ : Fin N => false) l = true)).card ≤ 1 := by
    simp
  have c1 : ∀ w : Fin N,
      (Finset.univ.filter (fun l : Fin N => (fun a : Fin N => decide (a = w)) l = true)).card ≤ 1 := by
    intro w
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hb
    rw [ha, hb]
  have s0 : ∀ x : Fin N → Bool,
      PEqualNP.Outside.L_meta_1950.V N C x (fun _ => false) C.output = false := by
    intro x
    apply hsnd x (fun _ => false) c0
    rintro ⟨p, w, _, _, h⟩
    cases h
  have s1 : ∀ w : Fin N, PEqualNP.Outside.L_meta_1950.V N C (fun _ => false)
      (fun a : Fin N => decide (a = w)) C.output = false := by
    intro w
    apply hsnd (fun _ => false) (fun a : Fin N => decide (a = w)) (c1 w)
    rintro ⟨p, w', _, h, _⟩
    cases h
  obtain ⟨p0, w0, hpw0⟩ := hex
  have O := PEqualNP.Outside.L_meta_1950.outgate N C hY hX (fun a : Fin N => decide (a = p0))
    (fun a : Fin N => decide (a = w0)) (hacc p0 w0 hpw0) (s0 _) (s1 w0)
  have UP := PEqualNP.Outside.L_meta_1950.up N C hg hRB hY hX hZ
  have DOWN : ∀ x y : Fin N → Bool, PEqualNP.Outside.L_meta_1950.V N C x y C.output = true →
      PEqualNP.Outside.L_meta_1950.V N C x (fun _ => false) C.output = false →
      ∃ h j', PEqualNP.Outside.L_meta_1950.slotP N C h j' ∧
        PEqualNP.Outside.L_meta_1950.lvxP N C x j' ∧
        PEqualNP.Outside.L_meta_1950.V N C (fun _ => false) y h = true := by
    intro x y h1 h0
    obtain ⟨j9, ho, hc⟩ := O
    apply PEqualNP.Outside.L_meta_1950.down N C hg hRB hKM hY hX x y j9 ho j9 hc
    · rw [ho]; exact h1
    · rw [ho]; exact h0
    · exact Relation.ReflTransGen.refl
  have FIVE : ∀ (h : ℕ) (p w : Fin N), (∃ j, PEqualNP.Outside.L_meta_1950.slotP N C h j ∧
      PEqualNP.Outside.L_meta_1950.lvxP N C (fun a : Fin N => decide (a = p)) j) →
      PEqualNP.Outside.L_meta_1950.V N C (fun _ => false) (fun a : Fin N => decide (a = w)) h = true →
      I p w := by
    rintro h p w ⟨j, hs, hl⟩ hv
    by_contra hn
    have hup := UP _ _ h j hs hl hv
    have hs' := hsnd (fun a : Fin N => decide (a = p)) (fun a : Fin N => decide (a = w)) (c1 w)
      (by
        rintro ⟨p', w', hI, hx, hy⟩
        simp only [decide_eq_true_eq] at hx hy
        subst hx hy
        exact hn hI)
    change PEqualNP.Outside.L_meta_1950.V N C _ _ C.output = false at hs'
    rw [hup] at hs'
    cases hs'
  refine ⟨O, fun x y h j hs hl hv => UP x y h j hs hl hv, fun x y h1 h0 => DOWN x y h1 h0, ?_,
    FIVE, ?_⟩
  · intro h j w hs hlh hl
    have hup := UP (fun a : Fin N => decide (¬ I a w)) (fun a : Fin N => decide (a = w)) h j hs hl hlh
    have hs' := hsnd (fun a : Fin N => decide (¬ I a w)) (fun a : Fin N => decide (a = w)) (c1 w)
      (by
        rintro ⟨p', w', hI, hx, hy⟩
        simp only [decide_eq_true_eq] at hx hy
        subst hy
        exact hx hI)
    change PEqualNP.Outside.L_meta_1950.V N C _ _ C.output = false at hs'
    rw [hup] at hs'
    cases hs'
  · intro p w hpw
    obtain ⟨h, j, hs, hl, hv⟩ := DOWN (fun a : Fin N => decide (a = p))
      (fun a : Fin N => decide (a = w)) (hacc p w hpw) (s0 _)
    have hap : ∃ j, PEqualNP.Outside.L_meta_1950.slotP N C h j ∧
        PEqualNP.Outside.L_meta_1950.lvxP N C (fun a : Fin N => decide (a = p)) j := ⟨j, hs, hl⟩
    rcases Classical.em (∃ w' : Fin N, w' ≠ w ∧ PEqualNP.Outside.L_meta_1950.V N C (fun _ => false)
        (fun a : Fin N => decide (a = w')) h = true) with ⟨w', hne, hw'⟩ | hno
    · right
      refine ⟨h, ⟨⟨w', w, hne, hw', hv⟩, ?_⟩, hv⟩
      intro p'
      constructor
      · intro hap'
        by_contra hne'
        exact hC4 p p' w w' (Ne.symm hne') (Ne.symm hne) hpw (FIVE h p' w hap' hv)
          (FIVE h p w' hap hw') (FIVE h p' w' hap' hw')
      · rintro rfl
        exact hap
    · left
      refine ⟨h, ?_, hap⟩
      intro w'
      constructor
      · intro hw'
        by_contra hne
        exact hno ⟨w', hne, hw'⟩
      · rintro rfl
        exact hv
