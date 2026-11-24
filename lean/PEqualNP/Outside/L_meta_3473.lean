import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3473

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
      ((∃ g ∈ gs, v ∈ g.inputs) → ds.length < gs.length) ∧
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
          ((∃ g' ∈ gs ++ [g], v ∈ g'.inputs) → ds.length < (gs ++ [g]).length) ∧
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
      · intro _; simp; omega
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
        · rintro ⟨g', hg', hvg⟩
          rcases List.mem_append.1 hg' with h | h
          · have := h4 ⟨g', h, hvg⟩
            simp; omega
          · rw [List.mem_singleton.1 h, hab] at hvg
            have hva : v = a ∨ v = b := by simpa using hvg
            rcases hva with rfl | rfl
            · rw [h2] at hsa; cases hsa
            · rw [h2] at hsb; cases hsb
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

end PEqualNP.Outside.L_meta_3473

theorem PEqualNP.Outside.L_meta_3473 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → (∃ (x5 : Fin x1 → Bool) (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x7 ≠ x3 → x5 x7 = x6 x7) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x6) → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x6 : Fin x1) => Decidable.decide (x6 = x3)) = Bool.false → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size < x2.size ∧ (∀ (x8 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x8 = Bool.true) ∧ (∀ (x8 : Fin x1 → Bool), x8 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = PEqualNP.MetaComplexity.circuitFun x1 x2 x8) ∧ ∀ (x8 : ℕ → Bool) (x9 x10 : ℕ), ↑x3 ≠ x9 → ↑x3 ≠ x10 → PEqualNP.ReadK.lineSingle x7 x1 x8 x9 x10 = PEqualNP.ReadK.lineSingle x2 x1 x8 x9 x10 := by
  intro n C v hC hdep hone
  have hG := (PEqualNP.Outside.L_meta_3473.ao2_iff n C).1 hC
  have hfun : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x =
      (PEqualNP.Outside.L_meta_3473.grun false (· && ·) (· || ·) C.gates (List.ofFn x)).getD C.output false := by
    intro x
    rw [← PEqualNP.Outside.L_meta_3473.wires_eq C hG]; rfl
  have hout : C.output < n + C.gates.length := by
    by_contra hcon
    obtain ⟨x, y, -, hne⟩ := hdep
    apply hne
    rw [hfun, hfun, List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_3473.grun_length, List.length_ofFn]; omega),
      List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_3473.grun_length, List.length_ofFn]; omega)]
  have hov : C.output ≠ v := by
    intro h
    rw [hfun, h] at hone
    have hlt : (v : ℕ) < (List.ofFn fun i : Fin n => decide (i = v)).length := by simp
    have hin : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) (i : ℕ),
        i < l.length → (PEqualNP.Outside.L_meta_3473.grun false (· && ·) (· || ·) gs l).getD i false = l.getD i false := by
      intro gs l i hi
      induction gs using List.reverseRecOn with
      | nil => rfl
      | append_singleton gs g ih =>
        rw [PEqualNP.Outside.L_meta_3473.grun_snoc, PEqualNP.Outside.L_meta_3473.getD_lt _ _ _ _ (by rw [PEqualNP.Outside.L_meta_3473.grun_length]; omega), ih]
    rw [hin _ _ _ hlt, PEqualNP.Outside.L_meta_3473.ofFn_getD] at hone
    simp at hone
  have hread : ∃ g ∈ C.gates, (v : ℕ) ∈ g.inputs := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, y, hxy, hne⟩ := hdep
    apply hne
    rw [hfun, hfun]
    refine PEqualNP.Outside.L_meta_3473.indep C.gates hG hcon _ _ (by simp) (fun i hi => ?_) _ hov
    by_cases h : i < n
    · rw [PEqualNP.Outside.L_meta_3473.ofFn_getD x ⟨i, h⟩, PEqualNP.Outside.L_meta_3473.ofFn_getD y ⟨i, h⟩]
      exact hxy ⟨i, h⟩ fun h' => hi (by rw [← h'])
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  obtain ⟨ds, s, h1, h2, -, h4, h5, h6⟩ := PEqualNP.Outside.L_meta_3473.build n v v.2 C.gates hG
  have hlt := h4 hread
  obtain ⟨D, hDg, hDo⟩ : ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.gates = ds ∧
      ((∃ k, s C.output = some k ∧ D.output = k) ∨
        (s C.output = none ∧ D.output = n + ds.length)) := by
    rcases h : s C.output with _ | k
    · exact ⟨⟨ds, n + ds.length⟩, rfl, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨⟨ds, k⟩, rfl, Or.inl ⟨k, rfl, rfl⟩⟩
  have hGD : PEqualNP.Outside.L_meta_3473.Good n D.gates := by rw [hDg]; exact h1
  have hfunD : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D x =
      (PEqualNP.Outside.L_meta_3473.grun false (· && ·) (· || ·) ds (List.ofFn x)).getD D.output false := by
    intro x
    rw [← hDg, ← PEqualNP.Outside.L_meta_3473.wires_eq D hGD]; rfl
  refine ⟨D, (PEqualNP.Outside.L_meta_3473.ao2_iff n D).2 hGD, ?_, ?_, ?_, ?_⟩
  · change D.gates.length < C.gates.length
    rw [hDg]; exact hlt
  · intro x hx
    rw [hfunD] at hx
    rw [hfun]
    have hl := h6 Bool false _ _ _ _ PEqualNP.Outside.L_meta_3473.lawsLe (List.ofFn x) (by simp) trivial
      (fun i _ _ h => h) C.output hout
    rcases hDo with ⟨k, hk, hDk⟩ | ⟨hk, hDk⟩
    · rw [hk] at hl
      rw [hDk] at hx
      exact hl hx
    · rw [hDk, List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_3473.grun_length, List.length_ofFn])] at hx
      exact absurd hx (by simp)
  · intro x hx
    rw [hfunD, hfun]
    have hl := h6 Bool false _ _ _ _ PEqualNP.Outside.L_meta_3473.lawsEqBool (List.ofFn x) (by simp)
      (by rw [PEqualNP.Outside.L_meta_3473.ofFn_getD]; exact hx) (fun i _ _ => rfl) C.output hout
    rcases hDo with ⟨k, hk, hDk⟩ | ⟨hk, hDk⟩
    · rw [hk] at hl
      rw [hDk]
      exact hl
    · rw [hk] at hl
      rw [hDk, List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_3473.grun_length, List.length_ofFn])]
      exact hl.symm
  · intro L p l hp hq
    unfold PEqualNP.ReadK.lineSingle
    rw [PEqualNP.Outside.L_meta_3473.lin_eq C hG, PEqualNP.Outside.L_meta_3473.lin_eq D hGD, hDg]
    set X : List (Bool × Bool) := (((List.range n).map fun i => i == p || i == l).zipIdx).map
      (fun (b, i) => if L i then (false, b) else (b, false)) with hX
    have hXl : X.length = n := by simp [hX]
    have hXv : X.getD v (false, false) = (false, false) := by
      rw [List.getD_eq_getElem _ _ (by rw [hXl]; exact v.2)]
      have hb : (((v : ℕ) == p) || ((v : ℕ) == l)) = false := by simp [hp, hq]
      have hx : X[(v : ℕ)]'(by rw [hXl]; exact v.2) =
          (fun (b : Bool) (i : ℕ) => if L i = true then (false, b) else (b, false))
            (((v : ℕ) == p) || ((v : ℕ) == l)) (v : ℕ) := by
        simp [hX]
      rw [hx, hb]
      simp
    have hl := h6 (Bool × Bool) (false, false) _ _ _ _ PEqualNP.Outside.L_meta_3473.lawsPair X hXl hXv
      (fun i _ _ => rfl) C.output hout
    rcases hDo with ⟨k, hk, hDk⟩ | ⟨hk, hDk⟩
    · rw [hk] at hl
      rw [hDk]
      exact congrArg Prod.snd hl
    · rw [hk] at hl
      rw [hDk, List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_3473.grun_length, hXl])]
      exact (congrArg Prod.snd hl).symm
