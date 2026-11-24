import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3694

open PEqualNP.CircuitLowerBounds

def isAnd (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => true
  | _ => false

def gv {α : Type} (z : α) (A O : α → α → α) (g : Gate) (w : List α) : α :=
  if isAnd g = true then A (w.getD (g.inputs.getD 0 0) z) (w.getD (g.inputs.getD 1 0) z)
  else O (w.getD (g.inputs.getD 0 0) z) (w.getD (g.inputs.getD 1 0) z)

def grun {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) : List α :=
  gs.foldl (fun w g => w ++ [gv z A O g w]) x

theorem grun_snoc {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (g : Gate) (x : List α) :
    grun z A O (gs ++ [g]) x = grun z A O gs x ++ [gv z A O g (grun z A O gs x)] := by
  simp [grun, List.foldl_append]

theorem grun_length {α : Type} (z : α) (A O : α → α → α) (gs : List Gate) (x : List α) :
    (grun z A O gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [grun]
  | append_singleton gs g ih => rw [grun_snoc]; simp [ih]; omega

theorem getD_lt {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

structure Laws {α : Type} (A O : α → α → α) (R : α → α → Prop) (Z : α → Prop) : Prop where
  andR : ∀ d1 c1 d2 c2, R d1 c1 → R d2 c2 → R (A d1 d2) (A c1 c2)
  orR : ∀ d1 c1 d2 c2, R d1 c1 → R d2 c2 → R (O d1 d2) (O c1 c2)
  zl : ∀ c1 c2, Z c1 → Z (A c1 c2)
  zr : ∀ c1 c2, Z c2 → Z (A c1 c2)
  zo : ∀ c1 c2, Z c1 → Z c2 → Z (O c1 c2)
  al : ∀ d c1 c2, Z c1 → R d c2 → R d (O c1 c2)
  ar : ∀ d c1 c2, Z c2 → R d c1 → R d (O c1 c2)

def Link {α : Type} (R : α → α → Prop) (Z : α → Prop) (z : α) (D : List α) (c : α) :
    Option ℕ → Prop
  | none => Z c
  | some k => R (D.getD k z) c

def Good (n : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (hj : j < gs.length), (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) ∧
    ∃ a b, gs[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j

theorem good_snoc {n : ℕ} {gs : List Gate} {g : Gate} (h : Good n gs)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a, b] ∧ a < n + gs.length ∧ b < n + gs.length) :
    Good n (gs ++ [g]) := by
  intro j hj
  rcases Nat.lt_or_ge j gs.length with h1 | h1
  · rw [List.getElem_append_left h1]; exact h j h1
  · have : j = gs.length := by simp at hj; omega
    subst this
    simpa using hg

theorem good_init {n : ℕ} {gs : List Gate} {g : Gate} (h : Good n (gs ++ [g])) :
    Good n gs ∧ ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a, b] ∧ a < n + gs.length ∧ b < n + gs.length) := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have := h j (by simp; omega)
    rwa [List.getElem_append_left hj] at this
  · simpa using h gs.length (by simp)

theorem build (n v : ℕ) (hv : v < n) (gs : List Gate) (hgs : Good n gs) :
    ∃ (ds : List Gate) (s : ℕ → Option ℕ), Good n ds ∧ s v = none ∧ ds.length ≤ gs.length ∧
      ds.length + gs.countP (fun g => decide (v ∈ g.inputs)) ≤ gs.length ∧
      (∀ w < n + gs.length, ∀ k, s w = some k → k < n + ds.length) ∧
      ∀ (α : Type) (z : α) (A O : α → α → α) (R : α → α → Prop) (Z : α → Prop), Laws A O R Z →
        ∀ x : List α, x.length = n → Z (x.getD v z) →
          (∀ i < n, i ≠ v → R (x.getD i z) (x.getD i z)) →
          ∀ w < n + gs.length, Link R Z z (grun z A O ds x) ((grun z A O gs x).getD w z) (s w) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], fun w => if w = v then none else some w, hgs, by simp, le_rfl, by simp, ?_, ?_⟩
    · intro w hw k hk
      dsimp only at hk
      split_ifs at hk with h
      · cases hk; simpa using hw
    · intro α z A O R Z hL x hx hz hR w hw
      by_cases h : w = v
      · subst h; simpa [Link, grun] using hz
      · simpa [Link, grun, h] using hR w (by simpa using hw) h
  | append_singleton gs g ih =>
    obtain ⟨hg0, hop, a, b, hab, ha, hb⟩ := good_init hgs
    obtain ⟨ds, s, h1, h2, h3, h4, h5, h6⟩ := ih hg0
    have hvK : v ≠ n + gs.length := by omega
    have keep : ∀ (o : Option ℕ), (∀ k, o = some k → k < n + ds.length) →
        (∀ (α : Type) (z : α) (A O : α → α → α) (R : α → α → Prop) (Z : α → Prop), Laws A O R Z →
          ∀ D C : List α, Link R Z z D (C.getD a z) (s a) → Link R Z z D (C.getD b z) (s b) →
            Link R Z z D (gv z A O g C) o) →
        ∃ (ds : List Gate) (s : ℕ → Option ℕ), Good n ds ∧ s v = none ∧
          ds.length ≤ (gs ++ [g]).length ∧
          ds.length + (gs ++ [g]).countP (fun g => decide (v ∈ g.inputs)) ≤ (gs ++ [g]).length ∧
          (∀ w < n + (gs ++ [g]).length, ∀ k, s w = some k → k < n + ds.length) ∧
          ∀ (α : Type) (z : α) (A O : α → α → α) (R : α → α → Prop) (Z : α → Prop),
            Laws A O R Z → ∀ x : List α, x.length = n → Z (x.getD v z) →
              (∀ i < n, i ≠ v → R (x.getD i z) (x.getD i z)) →
              ∀ w < n + (gs ++ [g]).length,
                Link R Z z (grun z A O ds x) ((grun z A O (gs ++ [g]) x).getD w z) (s w) := by
      intro o ho hlink
      refine ⟨ds, fun w => if w = n + gs.length then o else s w, h1, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only; rw [if_neg hvK]; exact h2
      · simp; omega
      · rw [List.countP_append, List.countP_singleton, List.length_append, List.length_singleton]
        split_ifs <;> omega
      · intro w hw k hk
        dsimp only at hk
        split_ifs at hk with h
        · exact ho k hk
        · exact h5 w (by simp at hw; omega) k hk
      · intro α z A O R Z hL x hx hz hR w hw
        have hlen : (grun z A O gs x).length = n + gs.length := by rw [grun_length, hx]
        dsimp only
        rw [grun_snoc]
        split_ifs with h
        · rw [h, ← hlen, getD_at]
          exact hlink α z A O R Z hL _ _ (h6 α z A O R Z hL x hx hz hR a ha)
            (h6 α z A O R Z hL x hx hz hR b hb)
        · rw [getD_lt z _ _ _ (by rw [hlen]; simp at hw; omega)]
          exact h6 α z A O R Z hL x hx hz hR w (by simp at hw; omega)
    have gva : ∀ (α : Type) (z : α) (A O : α → α → α) (C : List α), g.op = GateOp.and →
        gv z A O g C = A (C.getD a z) (C.getD b z) := by
      intro α z A O C h
      simp [gv, isAnd, h, hab]
    have gvo : ∀ (α : Type) (z : α) (A O : α → α → α) (C : List α), g.op = GateOp.or →
        gv z A O g C = O (C.getD a z) (C.getD b z) := by
      intro α z A O C h
      simp [gv, isAnd, h, hab]
    rcases hsa : s a with _ | k
    · rcases hop with h | h
      · refine keep none (by simp) fun α z A O R Z hL D C la lb => ?_
        rw [hsa] at la
        rw [gva α z A O C h]
        exact hL.zl _ _ la
      · refine keep (s b) (fun k hk => h5 b hb k hk) fun α z A O R Z hL D C la lb => ?_
        rw [hsa] at la
        rw [gvo α z A O C h]
        rcases hsb : s b with _ | l
        · rw [hsb] at lb; exact hL.zo _ _ la lb
        · rw [hsb] at lb; exact hL.al _ _ _ la lb
    · rcases hsb : s b with _ | l
      · rcases hop with h | h
        · refine keep none (by simp) fun α z A O R Z hL D C la lb => ?_
          rw [hsb] at lb
          rw [gva α z A O C h]
          exact hL.zr _ _ lb
        · refine keep (some k) (fun k' hk => by cases hk; exact h5 a ha k hsa)
            fun α z A O R Z hL D C la lb => ?_
          rw [hsa] at la
          rw [hsb] at lb
          rw [gvo α z A O C h]
          exact hL.ar _ _ _ lb la
      · have hkl : k < n + ds.length := h5 a ha k hsa
        have hll : l < n + ds.length := h5 b hb l hsb
        refine ⟨ds ++ [⟨g.op, [k, l]⟩],
          fun w => if w = n + gs.length then some (n + ds.length) else s w,
          good_snoc h1 ⟨hop, k, l, rfl, hkl, hll⟩, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp only; rw [if_neg hvK]; exact h2
        · simp; omega
        · have hvn : decide (v ∈ g.inputs) = false := by
            rw [decide_eq_false_iff_not, hab]
            intro hvg
            have hva : v = a ∨ v = b := by simpa using hvg
            rcases hva with rfl | rfl
            · rw [h2] at hsa; cases hsa
            · rw [h2] at hsb; cases hsb
          rw [List.countP_append, List.countP_singleton, List.length_append, List.length_append,
            List.length_singleton, List.length_singleton, hvn]
          simp
          omega
        · intro w hw k' hk
          dsimp only at hk
          split_ifs at hk with h
          · cases hk; simp
          · have := h5 w (by simp at hw; omega) k' hk
            simp; omega
        · intro α z A O R Z hL x hx hz hR w hw
          have hlen : (grun z A O gs x).length = n + gs.length := by rw [grun_length, hx]
          have hlenD : (grun z A O ds x).length = n + ds.length := by rw [grun_length, hx]
          dsimp only
          rw [grun_snoc, grun_snoc]
          split_ifs with h
          · have la := h6 α z A O R Z hL x hx hz hR a ha
            have lb := h6 α z A O R Z hL x hx hz hR b hb
            rw [hsa] at la
            rw [hsb] at lb
            rw [h, ← hlen, getD_at]
            change R ((grun z A O ds x ++ _).getD (n + ds.length) z) _
            rw [← hlenD, getD_at]
            rcases hop with h | h
            · rw [gva α z A O _ h]
              have : gv z A O ⟨g.op, [k, l]⟩ (grun z A O ds x) =
                  A ((grun z A O ds x).getD k z) ((grun z A O ds x).getD l z) := by
                simp [gv, isAnd, h]
              rw [this]
              exact hL.andR _ _ _ _ la lb
            · rw [gvo α z A O _ h]
              have : gv z A O ⟨g.op, [k, l]⟩ (grun z A O ds x) =
                  O ((grun z A O ds x).getD k z) ((grun z A O ds x).getD l z) := by
                simp [gv, isAnd, h]
              rw [this]
              exact hL.orR _ _ _ _ la lb
          · have hw' : w < n + gs.length := by simp at hw; omega
            rw [getD_lt z _ _ _ (by rw [hlen]; exact hw')]
            have hlk := h6 α z A O R Z hL x hx hz hR w hw'
            rcases hsw : s w with _ | k'
            · rw [hsw] at hlk; exact hlk
            · rw [hsw] at hlk
              change R ((grun z A O ds x ++ _).getD k' z) _
              rw [getD_lt z _ _ _ (by rw [hlenD]; exact h5 w hw' k' hsw)]
              exact hlk

theorem fold_congr {α : Type} (f g : List α → Gate → List α) (gs : List Gate)
    (h : ∀ q ∈ gs, ∀ w, f w q = g w q) : ∀ x, gs.foldl f x = gs.foldl g x := by
  induction gs with
  | nil => intro x; rfl
  | cons q gs ih =>
    intro x
    simp only [List.foldl_cons]
    rw [h q (by simp), ih (fun q' hq' => h q' (by simp [hq']))]

def bA (p q : Bool × Bool) : Bool × Bool := (p.1 && q.1, (p.1 && q.2) || (p.2 && q.1))
def bO (p q : Bool × Bool) : Bool × Bool := (p.1 || q.1, p.2 || q.2)

theorem mem_good {n : ℕ} {gs : List Gate} (h : Good n gs) {q : Gate} (hq : q ∈ gs) :
    (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ ∃ a b, q.inputs = [a, b] := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
  obtain ⟨h1, a, b, h2, -, -⟩ := h j hj
  exact ⟨h1, a, b, h2⟩

theorem wires_eq {n : ℕ} (C : Circuit) (h : Good n C.gates) (x : List Bool) :
    C.wires x = grun false (· && ·) (· || ·) C.gates x := by
  unfold Circuit.wires grun
  refine fold_congr _ _ _ (fun q hq w => ?_) x
  obtain ⟨hop, a, b, hab⟩ := mem_good h hq
  rcases hop with ho | ho <;> simp [gv, isAnd, ho, hab, GateOp.eval]

theorem lin_eq {n : ℕ} (C : Circuit) (h : Good n C.gates) (L : ℕ → Bool) (x : List Bool) :
    PEqualNP.ReadK.linearParts C L x = grun (false, false) bA bO C.gates
      ((x.zipIdx).map fun (b, i) => if L i then (false, b) else (b, false)) := by
  unfold PEqualNP.ReadK.linearParts grun
  refine fold_congr _ _ _ (fun q hq w => ?_) _
  obtain ⟨hop, a, b, hab⟩ := mem_good h hq
  rcases hop with ho | ho <;> simp [gv, isAnd, ho, hab, bA, bO]

theorem lawsEqBool : Laws (· && ·) (· || ·) (fun a b : Bool => a = b) (fun c => c = false) := by
  constructor <;> decide

theorem lawsLe : Laws (· && ·) (· || ·) (fun a b : Bool => a = true → b = true)
    (fun _ => True) := by
  constructor <;> decide

theorem lawsPair : Laws bA bO (fun a b : Bool × Bool => a = b) (fun c => c = (false, false)) := by
  constructor
  · rintro _ _ _ _ rfl rfl; rfl
  · rintro _ _ _ _ rfl rfl; rfl
  · rintro _ ⟨c, d⟩ rfl; simp [bA]
  · rintro ⟨c, d⟩ _ rfl; simp [bA]
  · rintro _ _ rfl rfl; rfl
  · rintro _ _ ⟨c, d⟩ rfl rfl; simp [bO]
  · rintro _ ⟨c, d⟩ _ rfl rfl; simp [bO]

theorem indep {n v : ℕ} (gs : List Gate) (hgs : Good n gs) (hno : ∀ g ∈ gs, v ∉ g.inputs)
    (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (grun false (· && ·) (· || ·) gs x).getD i false =
      (grun false (· && ·) (· || ·) gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [grun] using hxy
  | append_singleton gs g ih =>
    obtain ⟨hg0, hop, a, b, hab, -, -⟩ := good_init hgs
    have ih' := ih hg0 (fun g' hg' => hno g' (by simp [hg']))
    have hv : v ∉ g.inputs := hno g (by simp)
    rw [hab] at hv
    have hva : a ≠ v := fun h => hv (by simp [h])
    have hvb : b ≠ v := fun h => hv (by simp [h])
    intro i hi
    rw [grun_snoc, grun_snoc]
    have e : gv false (· && ·) (· || ·) g (grun false (· && ·) (· || ·) gs x) =
        gv false (· && ·) (· || ·) g (grun false (· && ·) (· || ·) gs y) := by
      unfold gv
      simp only [hab, List.getD_cons_zero, List.getD_cons_succ]
      rw [ih' a hva, ih' b hvb]
    rw [e]
    have hlen : (grun false (· && ·) (· || ·) gs x).length =
        (grun false (· && ·) (· || ·) gs y).length := by rw [grun_length, grun_length, hl]
    rcases lt_trichotomy i (grun false (· && ·) (· || ·) gs x).length with h | h | h
    · rw [getD_lt _ _ _ _ h, getD_lt _ _ _ _ (hlen ▸ h)]; exact ih' i hi
    · rw [h, getD_at, hlen, getD_at]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem ao2_iff (n : ℕ) (C : Circuit) : PEqualNP.TopForm.IsAO2 n C ↔ Good n C.gates := by
  constructor
  · rintro ⟨h1, h2, h3⟩ j hj
    have hm := List.getElem_mem hj
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (h3 _ hm)
    have hr := h2 j hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hr
    rw [List.getD_eq_getElem _ _ hj, hab] at hr
    exact ⟨h1 _ hm, a, b, hab, hr a (by simp), hr b (by simp)⟩
  · intro h
    refine ⟨fun g hg => (mem_good h hg).1, fun j hj => ?_, fun g hg => ?_⟩
    · unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      obtain ⟨-, a, b, hab, ha, hb⟩ := h j hj
      rw [List.getD_eq_getElem _ _ hj, hab]
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact ha
      · rw [List.mem_singleton.1 hi]; exact hb
    · obtain ⟨-, a, b, hab⟩ := mem_good h hg
      rw [hab]; rfl

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (v : Fin n) : (List.ofFn f).getD v false = f v := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]


theorem zero (n : ℕ) (C : Circuit) (v : ℕ) (hv : v < n) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hout : C.output < n + C.gates.length) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      D.size + C.gates.countP (fun g => decide (v ∈ g.inputs)) ≤ C.size ∧
      (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D x = true →
        PEqualNP.MetaComplexity.circuitFun n C x = true) ∧
      (∀ x : Fin n → Bool, x ⟨v, hv⟩ = false →
        PEqualNP.MetaComplexity.circuitFun n D x = PEqualNP.MetaComplexity.circuitFun n C x) ∧
      ∀ (L : ℕ → Bool) (p l : ℕ), v ≠ p → v ≠ l →
        PEqualNP.ReadK.lineSingle D n L p l = PEqualNP.ReadK.lineSingle C n L p l := by
  have hG := (ao2_iff n C).1 hC
  have hfun : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x =
      (grun false (· && ·) (· || ·) C.gates (List.ofFn x)).getD C.output false := by
    intro x
    rw [← wires_eq C hG]; rfl
  obtain ⟨ds, s, h1, h2, -, h4, h5, h6⟩ := build n v hv C.gates hG
  obtain ⟨D, hDg, hDo⟩ : ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.gates = ds ∧
      ((∃ k, s C.output = some k ∧ D.output = k) ∨
        (s C.output = none ∧ D.output = n + ds.length)) := by
    rcases h : s C.output with _ | k
    · exact ⟨⟨ds, n + ds.length⟩, rfl, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨⟨ds, k⟩, rfl, Or.inl ⟨k, rfl, rfl⟩⟩
  have hGD : Good n D.gates := by rw [hDg]; exact h1
  have hfunD : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D x =
      (grun false (· && ·) (· || ·) ds (List.ofFn x)).getD D.output false := by
    intro x
    rw [← hDg, ← wires_eq D hGD]; rfl
  refine ⟨D, (ao2_iff n D).2 hGD, ?_, ?_, ?_, ?_⟩
  · change D.gates.length + _ ≤ C.gates.length
    rw [hDg]; exact h4
  · intro x hx
    rw [hfunD] at hx
    rw [hfun]
    have hl := h6 Bool false _ _ _ _ lawsLe (List.ofFn x) (by simp) trivial
      (fun i _ _ h => h) C.output hout
    rcases hDo with ⟨k, hk, hDk⟩ | ⟨hk, hDk⟩
    · rw [hk] at hl
      rw [hDk] at hx
      exact hl hx
    · rw [hDk, List.getD_eq_default _ _ (by rw [grun_length, List.length_ofFn])] at hx
      exact absurd hx (by simp)
  · intro x hx
    rw [hfunD, hfun]
    have hl := h6 Bool false _ _ _ _ lawsEqBool (List.ofFn x) (by simp)
      (by have := ofFn_getD x ⟨v, hv⟩; simp only at this; rw [this]; exact hx) (fun i _ _ => rfl) C.output hout
    rcases hDo with ⟨k, hk, hDk⟩ | ⟨hk, hDk⟩
    · rw [hk] at hl
      rw [hDk]
      exact hl
    · rw [hk] at hl
      rw [hDk, List.getD_eq_default _ _ (by rw [grun_length, List.length_ofFn])]
      exact hl.symm
  · intro L p l hp hq
    unfold PEqualNP.ReadK.lineSingle
    rw [lin_eq C hG, lin_eq D hGD, hDg]
    set X : List (Bool × Bool) := (((List.range n).map fun i => i == p || i == l).zipIdx).map
      (fun (b, i) => if L i then (false, b) else (b, false)) with hX
    have hXl : X.length = n := by simp [hX]
    have hXv : X.getD v (false, false) = (false, false) := by
      rw [List.getD_eq_getElem _ _ (by rw [hXl]; exact hv)]
      have hb : ((v == p) || (v == l)) = false := by simp [hp, hq]
      have hx : X[v]'(by rw [hXl]; exact hv) =
          (fun (b : Bool) (i : ℕ) => if L i = true then (false, b) else (b, false))
            ((v == p) || (v == l)) v := by
        simp [hX]
      rw [hx, hb]
      simp
    have hl := h6 (Bool × Bool) (false, false) _ _ _ _ lawsPair X hXl hXv
      (fun i _ _ => rfl) C.output hout
    rcases hDo with ⟨k, hk, hDk⟩ | ⟨hk, hDk⟩
    · rw [hk] at hl
      rw [hDk]
      exact congrArg Prod.snd hl
    · rw [hk] at hl
      rw [hDk, List.getD_eq_default _ _ (by rw [grun_length, hXl])]
      exact (congrArg Prod.snd hl).symm

theorem card_count (l : List Gate) (p : Gate → Prop) [DecidablePred p] :
    Fintype.card { i : Fin l.length // p (l.get i) } = l.countP (fun g => decide (p g)) := by
  rw [Fintype.card_subtype, Finset.card_filter]
  induction l with
  | nil => simp
  | cons g l ih =>
    rw [List.countP_cons, ← ih]
    change (∑ i : Fin (l.length + 1), if p ((g :: l).get i) then 1 else 0) = _
    rw [Fin.sum_univ_succ, Nat.add_comm]
    congr 1
    by_cases h : p g <;> simp [h]

variable {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def DR (C : Circuit) : Finset (Fin N × Fin N) :=
  {x7 : Fin N × Fin N | I x7.1 x7.2 ∧
    (PEqualNP.MetaComplexity.circuitFun (N + N) C fun (x8 : Fin (N + N)) =>
      decide (x8 = Fin.castAdd N x7.1 ∨ x8 = Fin.natAdd N x7.2)) = true ∧
    PEqualNP.ReadK.lineSingle C (N + N) (fun x8 => decide (N ≤ x8)) (x7.1 : ℕ) (N + (x7.2 : ℕ)) =
      false ∧
    PEqualNP.ReadK.lineSingle C (N + N) (fun x8 => decide (x8 < N)) (x7.1 : ℕ) (N + (x7.2 : ℕ)) =
      false}

def Snd (q : ℕ) (C : Circuit) : Prop := ∀ (x8 : Fin (N + N) → Bool),
  Fintype.card { x9 : Fin N // x8 (Fin.natAdd N x9) = true } ≤ q →
  (¬ ∃ (x10 : Fin N) (x11 : Fin N), I x10 x11 ∧ x8 (Fin.castAdd N x10) = true ∧
    x8 (Fin.natAdd N x11) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C x8 = false

def Cln (C : Circuit) : Prop := ∀ (x9 : Fin (N + N)),
  have x10 : ℕ := {x10 ∈ DR I C | x9 = Fin.castAdd N x10.1 ∨ x9 = Fin.natAdd N x10.2}.card
  0 < x10 → 24 * max 1 (Fintype.card { x12 : Fin C.size // (x9 : ℕ) ∈ (C.gates.get x12).inputs }) <
    x10

theorem single_false {C : Circuit} (hq : 1 ≤ q) (hS : Snd I q C) (v : Fin (N + N)) :
    PEqualNP.MetaComplexity.circuitFun (N + N) C (fun x => decide (x = v)) = false := by
  refine hS _ ?_ ?_
  · refine le_trans ?_ hq
    rw [Fintype.card_subtype]
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    have h1 := of_decide_eq_true (Finset.mem_filter.1 ha).2
    have h2 := of_decide_eq_true (Finset.mem_filter.1 hb).2
    have h3 := congrArg Fin.val (h1.trans h2.symm)
    simp at h3
    exact Fin.ext h3
  · rintro ⟨a, b, -, ha, hb⟩
    have h3 := congrArg Fin.val ((of_decide_eq_true ha).trans (of_decide_eq_true hb).symm)
    simp at h3
    have := a.2
    omega

theorem main (hq : 1 ≤ q) : ∀ (s : ℕ) (C : Circuit), C.size = s → PEqualNP.TopForm.IsAO2 (N + N) C →
    Snd I q C → 24 * C.size < (DR I C).card → ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      Snd I q D ∧ 24 * D.size < (DR I D).card ∧ Cln I D := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C hs hC hS hD
    by_cases hcl : Cln I C
    · exact ⟨C, hC, hS, hD, hcl⟩
    unfold Cln at hcl
    rw [not_forall] at hcl
    obtain ⟨v, hv0⟩ := hcl
    have hv1 : ¬ (0 < {x10 ∈ DR I C | v = Fin.castAdd N x10.1 ∨ v = Fin.natAdd N x10.2}.card →
      24 * max 1 (Fintype.card { x12 : Fin C.size // (v : ℕ) ∈ (C.gates.get x12).inputs }) <
        {x10 ∈ DR I C | v = Fin.castAdd N x10.1 ∨ v = Fin.natAdd N x10.2}.card) := hv0
    rw [Classical.not_imp, not_lt] at hv1
    obtain ⟨hpos, hle⟩ := hv1
    set A := {x10 ∈ DR I C | v = Fin.castAdd N x10.1 ∨ v = Fin.natAdd N x10.2} with hA
    have hcount : Fintype.card { x12 : Fin C.size // (v : ℕ) ∈ (C.gates.get x12).inputs } =
        C.gates.countP (fun g => decide ((v : ℕ) ∈ g.inputs)) :=
      card_count C.gates fun g => (v : ℕ) ∈ g.inputs
    rw [hcount] at hle
    set r := C.gates.countP (fun g => decide ((v : ℕ) ∈ g.inputs)) with hr
    have hG := (ao2_iff (N + N) C).1 hC
    have hfun : ∀ x : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C x =
        (grun false (· && ·) (· || ·) C.gates (List.ofFn x)).getD C.output false := by
      intro x
      rw [← wires_eq C hG]; rfl
    obtain ⟨e, he⟩ := Finset.card_pos.1 hpos
    obtain ⟨heD, hev⟩ := Finset.mem_filter.1 he
    have heT := (Finset.mem_filter.1 heD).2.2.1
    have hout : C.output < N + N + C.gates.length := by
      by_contra hcon
      rw [hfun, List.getD_eq_default _ _ (by rw [grun_length, List.length_ofFn]; omega)] at heT
      cases heT
    have hov : C.output ≠ v := by
      intro h
      have h1 := single_false I hq hS v
      rw [hfun, h] at h1
      have hin : ∀ (gs : List Gate) (l : List Bool) (i : ℕ),
          i < l.length → (grun false (· && ·) (· || ·) gs l).getD i false = l.getD i false := by
        intro gs l i hi
        induction gs using List.reverseRecOn with
        | nil => rfl
        | append_singleton gs g ih => rw [grun_snoc, getD_lt _ _ _ _ (by rw [grun_length]; omega), ih]
      rw [hin _ _ _ (by simp), ofFn_getD] at h1
      simp at h1
    have hr1 : 1 ≤ r := by
      by_contra hcon
      have hno : ∀ g ∈ C.gates, (v : ℕ) ∉ g.inputs := by
        intro g hg hvg
        have : 0 < r := List.countP_pos_iff.2 ⟨g, hg, decide_eq_true hvg⟩
        omega
      have other : ∃ w : Fin (N + N), (fun x8 : Fin (N + N) =>
          decide (x8 = Fin.castAdd N e.1 ∨ x8 = Fin.natAdd N e.2)) =
          fun x => decide (x = w ∨ x = v) := by
        rcases hev with h | h
        · exact ⟨Fin.natAdd N e.2, funext fun x => by rw [h]; exact decide_eq_decide.2 or_comm⟩
        · exact ⟨Fin.castAdd N e.1, funext fun x => by rw [h]⟩
      obtain ⟨w, hw⟩ := other
      rw [hw, hfun] at heT
      have h1 := single_false I hq hS w
      rw [hfun] at h1
      have h2 := indep C.gates hG hno (List.ofFn fun x : Fin (N + N) => decide (x = w ∨ x = v))
        (List.ofFn fun x : Fin (N + N) => decide (x = w)) (by simp) (fun i hi => by
          by_cases h : i < N + N
          · have e1 := ofFn_getD (fun x : Fin (N + N) => decide (x = w ∨ x = v)) ⟨i, h⟩
            have e2 := ofFn_getD (fun x : Fin (N + N) => decide (x = w)) ⟨i, h⟩
            simp only at e1 e2
            rw [e1, e2]
            have hne : (⟨i, h⟩ : Fin (N + N)) ≠ v := fun hc => hi (by rw [← hc])
            exact decide_eq_decide.2 ⟨fun h => h.resolve_right hne, Or.inl⟩
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]) C.output hov
      rw [h2, h1] at heT
      cases heT
    obtain ⟨D, d1, d2, d3, d4, d5⟩ := zero (N + N) C v v.2 hC hout
    have hSD : Snd I q D := by
      intro x h1 h2
      have h3 := hS x h1 h2
      by_contra hc
      rw [d3 x (by simpa using hc)] at h3
      cases h3
    have hsub : DR I C \ A ⊆ DR I D := by
      intro x hx
      obtain ⟨hxD, hxA⟩ := Finset.mem_sdiff.1 hx
      have hne : ¬ (v = Fin.castAdd N x.1 ∨ v = Fin.natAdd N x.2) := fun h =>
        hxA (Finset.mem_filter.2 ⟨hxD, h⟩)
      rw [not_or] at hne
      obtain ⟨hu, g1, g2, g3, g4⟩ := Finset.mem_filter.1 hxD
      have n1 : (v : ℕ) ≠ (x.1 : ℕ) := fun h => hne.1 (Fin.ext h)
      have n2 : (v : ℕ) ≠ N + (x.2 : ℕ) := fun h => hne.2 (Fin.ext h)
      refine Finset.mem_filter.2 ⟨hu, g1, ?_, ?_, ?_⟩
      · rw [d4]
        · exact g2
        · simpa using hne
      · rw [d5 _ _ _ n1 n2]; exact g3
      · rw [d5 _ _ _ n1 n2]; exact g4
    have hAs : A ⊆ DR I C := Finset.filter_subset _ _
    have c1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hAs] at c1
    have hmax : max 1 r = r := max_eq_right hr1
    rw [hmax] at hle
    exact ih D.size (by omega) D rfl d1 hSD (by omega)

end PEqualNP.Outside.L_meta_3694

theorem PEqualNP.Outside.L_meta_3694 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (1 : ℕ) ≤ x1 →     have x6 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x2 × Fin x2) := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => {x7 : Fin x2 × Fin x2 | x3 x7.1 x7.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x6 fun (x8 : Fin (x2 + x2)) => Decidable.decide (x8 = Fin.castAdd x2 x7.1 ∨ x8 = Fin.natAdd x2 x7.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x6 (x2 + x2) (fun (x8 : ℕ) => Decidable.decide (x2 ≤ x8)) (↑x7.1) (x2 + ↑x7.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x6 (x2 + x2) (fun (x8 : ℕ) => Decidable.decide (x8 < x2)) (↑x7.1) (x2 + ↑x7.2) = Bool.false};     have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x8 : Fin (x2 + x2) → Bool), Fintype.card { x9 : Fin x2 // x8 (Fin.natAdd x2 x9) = Bool.true } ≤ x1 → (¬∃ (x10 : Fin x2) (x11 : Fin x2), x3 x10 x11 ∧ x8 (Fin.castAdd x2 x10) = Bool.true ∧ x8 (Fin.natAdd x2 x11) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x7 x8 = Bool.false;     have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) =>       ∀ (x9 : Fin (x2 + x2)),         have x10 : ℕ := {x10 ∈ x6 x8 | x9 = Fin.castAdd x2 x10.1 ∨ x9 = Fin.natAdd x2 x10.2}.card;         (0 : ℕ) < x10 → (24 : ℕ) * Max.max (1 : ℕ) (Fintype.card { x12 : Fin x8.size // ↑x9 ∈ (x8.gates.get x12).inputs }) < x10;     ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x9 → x7 x9 → (24 : ℕ) * x9.size < (x6 x9).card → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x13 ∧ x7 x13 ∧ (24 : ℕ) * x13.size < (x6 x13).card ∧ x8 x13 := by
  intro q N I _ hq _ _ _ C hC hS hD
  exact PEqualNP.Outside.L_meta_3694.main I hq C.size C rfl hC hS hD
