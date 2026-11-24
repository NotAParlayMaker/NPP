import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4253

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ### Section 1: Zero-Normalized U2 Trace Calculus -/

inductive Op where
  | conj | disj | diffL | diffR
deriving DecidableEq

def evalOp : Op → Bool → Bool → Bool
  | .conj, a, b => a && b
  | .disj, a, b => a || b
  | .diffL, a, b => a && !b
  | .diffR, a, b => !a && b

def opOfNat : Nat → Op
  | 0 => .conj
  | 1 => .disj
  | 2 => .diffL
  | _ => .diffR

def natOfOp : Op → Nat
  | .conj => 0
  | .disj => 1
  | .diffL => 2
  | .diffR => 3

def phase (sign bit : Bool) : Bool := if sign then !bit else bit

def normOp : Bool → Bool → Bool → Op
  | false, false, false => .conj
  | false, false, true  => .diffL
  | false, true,  false => .diffR
  | false, true,  true  => .disj
  | true,  false, false => .disj
  | true,  false, true  => .diffR
  | true,  true,  false => .diffL
  | true,  true,  true  => .conj

theorem norm_bin_table : ∀ (isOr a0 b0 a b : Bool),
    phase (if isOr then a0 || b0 else a0 && b0) (if isOr then a || b else a && b) =
    evalOp (normOp isOr a0 b0) (phase a0 a) (phase b0 b) := by decide

theorem norm_not_table : ∀ (a0 a : Bool), phase (!a0) (!a) = phase a0 a := by decide

def normFn {ρ : Type} (z : ρ) (f : ρ → Bool) : ρ → Bool := fun r => phase (f z) (f r)

def constF {ρ : Type} : ρ → Bool := fun _ => false

theorem evalOp_false_both (op : Op) : evalOp op false false = false := by
  cases op <;> rfl

theorem op_masks_left (op : Op) : ∃ b : Bool, ∀ a1 a2 : Bool, evalOp op a1 b = evalOp op a2 b := by
  cases op
  · exact ⟨false, by decide⟩
  · exact ⟨true, by decide⟩
  · exact ⟨true, by decide⟩
  · exact ⟨false, by decide⟩

structure TGate (ρ : Type) where
  op : Op
  lhs : ρ → Bool
  rhs : ρ → Bool

def TGate.val {ρ : Type} (g : TGate ρ) : ρ → Bool :=
  fun r => evalOp g.op (g.lhs r) (g.rhs r)

def reads {ρ : Type} (g : TGate ρ) (w : ρ → Bool) : Prop :=
  g.lhs = w ∨ g.rhs = w

def ValidTrace {ρ : Type} (raw : List (ρ → Bool)) : List (TGate ρ) → Prop
  | [] => True
  | g :: gs => g.lhs ∈ raw ∧ g.rhs ∈ raw ∧ ValidTrace (g.val :: raw) gs

def traceBank {ρ : Type} (raw : List (ρ → Bool)) : List (TGate ρ) → List (ρ → Bool)
  | [] => raw
  | g :: gs => traceBank (g.val :: raw) gs

def Sufficient {ρ : Type} (raw : List (ρ → Bool)) (out : ρ → Bool) (gs : List (TGate ρ)) : Prop :=
  ValidTrace raw gs ∧ out ∈ traceBank raw gs

def FreshTrace {ρ : Type} (raw : List (ρ → Bool)) : List (TGate ρ) → Prop
  | [] => True
  | g :: gs => g.val ∉ raw ∧ FreshTrace (g.val :: raw) gs

theorem mem_traceBank_of_mem {ρ : Type} {raw : List (ρ → Bool)} {gs : List (TGate ρ)}
    {w : ρ → Bool} (hw : w ∈ raw) : w ∈ traceBank raw gs := by
  induction gs generalizing raw with
  | nil => exact hw
  | cons g gs ih => exact ih (List.mem_cons_of_mem _ hw)

theorem valid_sub {ρ : Type} {r1 r2 : List (ρ → Bool)} {gs : List (TGate ρ)}
    (hsub : ∀ w, w ∈ r1 → w ∈ r2) (hv : ValidTrace r1 gs) :
    ValidTrace r2 gs ∧ ∀ w, w ∈ traceBank r1 gs → w ∈ traceBank r2 gs := by
  induction gs generalizing r1 r2 with
  | nil => exact ⟨trivial, hsub⟩
  | cons g gs ih =>
    rcases hv with ⟨hl, hr, hv'⟩
    have hsub' : ∀ w, w ∈ g.val :: r1 → w ∈ g.val :: r2 := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub _ hw)
    obtain ⟨hv2, hbank⟩ := ih hsub' hv'
    exact ⟨⟨hsub _ hl, hsub _ hr, hv2⟩, hbank⟩

theorem simplify_trace {ρ : Type} {raw : List (ρ → Bool)} {out : ρ → Bool}
    {gs : List (TGate ρ)} (hs : Sufficient raw out gs) :
    ∃ ts, ts.length ≤ gs.length ∧ Sufficient raw out ts ∧ FreshTrace raw ts := by
  classical
  induction gs generalizing raw with
  | nil => exact ⟨[], Nat.le_refl _, hs, trivial⟩
  | cons g gs ih =>
    rcases hs with ⟨⟨hl, hr, hv⟩, hout⟩
    by_cases hm : g.val ∈ raw
    · have hsub : ∀ w, w ∈ g.val :: raw → w ∈ raw := by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hm
        · exact hw
      obtain ⟨hv', hbank⟩ := valid_sub hsub hv
      obtain ⟨ts, hlen, hs', hf⟩ := ih ⟨hv', hbank _ hout⟩
      exact ⟨ts, Nat.le_trans hlen (Nat.le_succ _), hs', hf⟩
    · obtain ⟨ts, hlen, hs', hf⟩ := ih ⟨hv, hout⟩
      exact ⟨g :: ts, Nat.succ_le_succ hlen, ⟨⟨hl, hr, hs'.1⟩, hs'.2⟩, ⟨hm, hf⟩⟩

theorem fresh_val_not_raw {ρ : Type} {raw : List (ρ → Bool)} {gs : List (TGate ρ)}
    (hf : FreshTrace raw gs) : ∀ g ∈ gs, g.val ∉ raw := by
  induction gs generalizing raw with
  | nil => intro g hg; cases hg
  | cons a gs ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hf.1
    · intro hr
      exact ih hf.2 g hg (List.mem_cons_of_mem _ hr)

theorem fresh_head_ne_tail {ρ : Type} {raw : List (ρ → Bool)} {g : TGate ρ}
    {gs : List (TGate ρ)} (hf : FreshTrace raw (g :: gs)) {h : TGate ρ} (hh : h ∈ gs) :
    g ≠ h := by
  intro heq
  subst heq
  exact fresh_val_not_raw hf.2 g hh List.mem_cons_self

theorem fresh_nodup {ρ : Type} {raw : List (ρ → Bool)} {gs : List (TGate ρ)}
    (hf : FreshTrace raw gs) : gs.Nodup := by
  induction gs generalizing raw with
  | nil => exact List.nodup_nil
  | cons a gs ih =>
    exact List.nodup_cons.mpr ⟨fun ha => fresh_val_not_raw hf.2 a ha List.mem_cons_self, ih hf.2⟩

theorem fresh_head_distinct_inputs {ρ : Type} {raw : List (ρ → Bool)} {g : TGate ρ}
    {gs : List (TGate ρ)} (h0 : constF ∈ raw)
    (hv : ValidTrace raw (g :: gs)) (hf : FreshTrace raw (g :: gs)) :
    g.lhs ≠ constF ∧ g.rhs ≠ constF ∧ g.lhs ≠ g.rhs := by
  rcases hv with ⟨hl, hr, _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    cases hop : g.op
    · have h1 : g.val = constF := funext fun r => by simp [TGate.val, hop, heq, evalOp, constF]
      exact hf.1 (h1 ▸ h0)
    · have h1 : g.val = g.rhs := funext fun r => by simp [TGate.val, hop, heq, evalOp, constF]
      exact hf.1 (h1 ▸ hr)
    · have h1 : g.val = constF := funext fun r => by simp [TGate.val, hop, heq, evalOp, constF]
      exact hf.1 (h1 ▸ h0)
    · have h1 : g.val = g.rhs := funext fun r => by simp [TGate.val, hop, heq, evalOp, constF]
      exact hf.1 (h1 ▸ hr)
  · intro heq
    cases hop : g.op
    · have h1 : g.val = constF := funext fun r => by simp [TGate.val, hop, heq, evalOp, constF]
      exact hf.1 (h1 ▸ h0)
    · have h1 : g.val = g.lhs := funext fun r => by simp [TGate.val, hop, heq, evalOp, constF]
      exact hf.1 (h1 ▸ hl)
    · have h1 : g.val = g.lhs := funext fun r => by simp [TGate.val, hop, heq, evalOp, constF]
      exact hf.1 (h1 ▸ hl)
    · have h1 : g.val = constF := funext fun r => by simp [TGate.val, hop, heq, evalOp, constF]
      exact hf.1 (h1 ▸ h0)
  · intro heq
    cases hop : g.op
    · have h1 : g.val = g.lhs := funext fun r => by simp [TGate.val, hop, heq, evalOp]
      exact hf.1 (h1 ▸ hl)
    · have h1 : g.val = g.lhs := funext fun r => by simp [TGate.val, hop, heq, evalOp]
      exact hf.1 (h1 ▸ hl)
    · have h1 : g.val = constF := funext fun r => by simp [TGate.val, hop, heq, evalOp, constF]
      exact hf.1 (h1 ▸ h0)
    · have h1 : g.val = constF := funext fun r => by simp [TGate.val, hop, heq, evalOp, constF]
      exact hf.1 (h1 ▸ h0)

/-! ### Section 2: Restriction, Disappearance, FreeSafe, UsePath, Sensitivity -/

def restrict {ρ σ : Type} (lift : σ → ρ) (f : ρ → Bool) : σ → Bool :=
  fun s => f (lift s)

def disappears {ρ σ : Type} (lift : σ → ρ) (g : TGate ρ) : Prop :=
  restrict lift g.val = constF ∨
  restrict lift g.val = restrict lift g.lhs ∨
  restrict lift g.val = restrict lift g.rhs

theorem reading_zero_disappears {ρ σ : Type} (lift : σ → ρ) {g : TGate ρ} {w : ρ → Bool}
    (hw : restrict lift w = constF) (hr : reads g w) : disappears lift g := by
  rcases hr with hl | hr
  · have h0 : ∀ s, g.lhs (lift s) = false := fun s => by simpa [hl, restrict, constF] using congrFun hw s
    cases hop : g.op
    · left; funext s; simp [restrict, TGate.val, hop, h0 s, evalOp, constF]
    · right; right; funext s; simp [restrict, TGate.val, hop, h0 s, evalOp]
    · left; funext s; simp [restrict, TGate.val, hop, h0 s, evalOp, constF]
    · right; right; funext s; simp [restrict, TGate.val, hop, h0 s, evalOp]
  · have h0 : ∀ s, g.rhs (lift s) = false := fun s => by simpa [hr, restrict, constF] using congrFun hw s
    cases hop : g.op
    · left; funext s; simp [restrict, TGate.val, hop, h0 s, evalOp, constF]
    · right; left; funext s; simp [restrict, TGate.val, hop, h0 s, evalOp]
    · right; left; funext s; simp [restrict, TGate.val, hop, h0 s, evalOp]
    · left; funext s; simp [restrict, TGate.val, hop, h0 s, evalOp, constF]

theorem both_zero_val_zero {ρ σ : Type} (lift : σ → ρ) {g : TGate ρ}
    (hl : restrict lift g.lhs = constF) (hr : restrict lift g.rhs = constF) :
    restrict lift g.val = constF := by
  funext s
  have h1 : g.lhs (lift s) = false := by simpa [restrict, constF] using congrFun hl s
  have h2 : g.rhs (lift s) = false := by simpa [restrict, constF] using congrFun hr s
  simp [restrict, TGate.val, h1, h2, evalOp_false_both, constF]

inductive FreeSafe {ρ : Type} (raw : List (ρ → Bool)) (forbid : (ρ → Bool) → Prop) :
    Nat → List (ρ → Bool) → Prop where
  | base : FreeSafe raw forbid 0 raw
  | step (op : Op) {n ws} {a b : ρ → Bool} :
      FreeSafe raw forbid n ws → a ∈ ws → b ∈ ws →
      ¬ forbid (fun r => evalOp op (a r) (b r)) →
      FreeSafe raw forbid (n + 1) ((fun r => evalOp op (a r) (b r)) :: ws)

abbrev Free {ρ : Type} (raw : List (ρ → Bool)) := FreeSafe raw (fun _ => False)

theorem free_mono {ρ : Type} {r1 r2 : List (ρ → Bool)} {forbid : (ρ → Bool) → Prop}
    {n ws} (hsub : ∀ w, w ∈ r1 → w ∈ r2) (h : FreeSafe r1 forbid n ws) :
    ∃ ws', FreeSafe r2 forbid n ws' ∧ ∀ w, w ∈ ws → w ∈ ws' := by
  induction h with
  | base => exact ⟨r2, FreeSafe.base, hsub⟩
  | step op _ ha hb hnf ih =>
    obtain ⟨ws', hr', hsub'⟩ := ih
    refine ⟨_, FreeSafe.step op hr' (hsub' _ ha) (hsub' _ hb) hnf, ?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hsub' _ hw)

theorem free_compose {ρ : Type} {raw ws1 ws2 : List (ρ → Bool)} {forbid : (ρ → Bool) → Prop}
    {n1 n2 : Nat} (h1 : FreeSafe raw forbid n1 ws1) (h2 : FreeSafe ws1 forbid n2 ws2) :
    FreeSafe raw forbid (n1 + n2) ws2 := by
  induction h2 with
  | base => simpa using h1
  | step op _ ha hb hnf ih =>
    simpa [Nat.add_assoc] using FreeSafe.step op ih ha hb hnf

theorem free_of_trace {ρ : Type} {raw : List (ρ → Bool)} {forbid : (ρ → Bool) → Prop}
    {gs : List (TGate ρ)} (hv : ValidTrace raw gs) (hnf : ∀ g ∈ gs, ¬ forbid g.val) :
    FreeSafe raw forbid gs.length (traceBank raw gs) := by
  induction gs generalizing raw with
  | nil => exact FreeSafe.base
  | cons g gs ih =>
    rcases hv with ⟨hl, hr, hv'⟩
    have h1 : FreeSafe raw forbid 1 (g.val :: raw) :=
      FreeSafe.step g.op FreeSafe.base hl hr (hnf g List.mem_cons_self)
    have h2 := ih hv' (fun t ht => hnf t (List.mem_cons_of_mem _ ht))
    simpa [traceBank, Nat.add_comm] using free_compose h1 h2

theorem free_map_restrict {ρ σ : Type} (lift : σ → ρ) {raw ws : List (ρ → Bool)}
    {forbid1 : (ρ → Bool) → Prop} {forbid2 : (σ → Bool) → Prop} {n : Nat}
    (h : FreeSafe raw forbid1 n ws)
    (hfb : ∀ f, forbid2 (restrict lift f) → forbid1 f) :
    FreeSafe (raw.map (restrict lift)) forbid2 n (ws.map (restrict lift)) := by
  induction h with
  | base => exact FreeSafe.base
  | @step op n ws a b _ ha hb hnf ih =>
    have hv : restrict lift (fun r => evalOp op (a r) (b r)) =
        fun s => evalOp op (restrict lift a s) (restrict lift b s) := rfl
    rw [List.map_cons, hv]
    exact FreeSafe.step op ih (List.mem_map.mpr ⟨a, ha, rfl⟩) (List.mem_map.mpr ⟨b, hb, rfl⟩)
      (fun h2 => hnf (hfb _ (hv ▸ h2)))

theorem trace_of_free {ρ : Type} {raw ws : List (ρ → Bool)} {forbid : (ρ → Bool) → Prop}
    {n : Nat} (h : FreeSafe raw forbid n ws) :
    ∃ gs : List (TGate ρ), gs.length = n ∧ ValidTrace raw gs ∧ ∀ w ∈ ws, w ∈ traceBank raw gs := by
  induction h with
  | base => exact ⟨[], rfl, trivial, fun _ hw => hw⟩
  | @step op n ws a b _ ha hb _ ih =>
    obtain ⟨gs, hlen, hv, hsub⟩ := ih
    refine ⟨gs ++ [⟨op, a, b⟩], by simp [hlen], ?_, ?_⟩
    · have hval : ∀ (r : List (ρ → Bool)) (l : List (TGate ρ)),
          ValidTrace r l → (∀ w ∈ ws, w ∈ traceBank r l) → ValidTrace r (l ++ [⟨op, a, b⟩]) := by
        intro r l hvl hsubl
        induction l generalizing r with
        | nil => exact ⟨hsubl a ha, hsubl b hb, trivial⟩
        | cons g gs ihg =>
          rcases hvl with ⟨hl, hr, hv'⟩
          exact ⟨hl, hr, ihg (g.val :: r) hv' hsubl⟩
      exact hval raw gs hv hsub
    · intro w hw
      have hbank_app : ∀ (r : List (ρ → Bool)) (l : List (TGate ρ)) (t : TGate ρ),
          traceBank r (l ++ [t]) = t.val :: traceBank r l := by
        intro r l t
        induction l generalizing r with
        | nil => rfl
        | cons x xs ihx => exact ihx (x.val :: r)
      rw [hbank_app]
      rcases List.mem_cons.mp hw with rfl | hw
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub _ hw)

theorem free_move_raw_front {ρ : Type} {raw : List (ρ → Bool)} {out : ρ → Bool}
    {gs : List (TGate ρ)} {t : TGate ρ}
    (hs : Sufficient raw out gs) (ht : t ∈ gs) (hl : t.lhs ∈ raw) (hr : t.rhs ∈ raw) :
    ∃ ts, ts.length + 1 ≤ gs.length ∧ Sufficient (t.val :: raw) out ts := by
  induction gs generalizing raw with
  | nil => cases ht
  | cons g gs ih =>
    rcases hs with ⟨⟨gl, gr, hv⟩, hout⟩
    rcases List.mem_cons.mp ht with rfl | htin
    · exact ⟨gs, Nat.le_refl _, ⟨hv, hout⟩⟩
    · obtain ⟨ts, hlen, hts⟩ := ih ⟨hv, hout⟩ htin (List.mem_cons_of_mem _ hl) (List.mem_cons_of_mem _ hr)
      have hsub : ∀ w, w ∈ t.val :: g.val :: raw → w ∈ g.val :: t.val :: raw := by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)
      obtain ⟨hv2, hb2⟩ := valid_sub hsub hts.1
      refine ⟨g :: ts, by simp; omega, ⟨⟨List.mem_cons_of_mem _ gl, List.mem_cons_of_mem _ gr, hv2⟩, hb2 _ hts.2⟩⟩

theorem free_restrict {ρ σ : Type} (lift : σ → ρ) {raw : List (ρ → Bool)} {out : ρ → Bool}
    {gs : List (TGate ρ)} (h0 : constF ∈ raw) (hs : Sufficient raw out gs) :
    ∃ m ws, m + (gs.filter (fun g => @decide (disappears lift g) (Classical.propDecidable _))).length = gs.length ∧
      Free (raw.map (restrict lift)) m ws ∧ restrict lift out ∈ ws := by
  classical
  induction gs generalizing raw with
  | nil =>
    exact ⟨0, raw.map (restrict lift), by simp, FreeSafe.base, List.mem_map.mpr ⟨out, hs.2, rfl⟩⟩
  | cons g gs ih =>
    rcases hs with ⟨⟨hl, hr, hv⟩, hout⟩
    obtain ⟨m, ws, heq, hrun, hin⟩ := ih (List.mem_cons_of_mem _ h0) ⟨hv, hout⟩
    by_cases hd : disappears lift g
    · have hmem : restrict lift g.val ∈ raw.map (restrict lift) := by
        rcases hd with h1 | h2 | h3
        · rw [h1]; exact List.mem_map.mpr ⟨constF, h0, rfl⟩
        · rw [h2]; exact List.mem_map.mpr ⟨g.lhs, hl, rfl⟩
        · rw [h3]; exact List.mem_map.mpr ⟨g.rhs, hr, rfl⟩
      have hsub : ∀ w, w ∈ (g.val :: raw).map (restrict lift) → w ∈ raw.map (restrict lift) := by
        intro w hw
        rw [List.map_cons] at hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hmem
        · exact hw
      obtain ⟨ws', hrun', hsub'⟩ := free_mono hsub hrun
      refine ⟨m, ws', ?_, hrun', hsub' _ hin⟩
      simp [hd]; omega
    · have h1 : Free (raw.map (restrict lift)) 1 (restrict lift g.val :: raw.map (restrict lift)) := by
        have hv_eq : restrict lift g.val = fun s => evalOp g.op (restrict lift g.lhs s) (restrict lift g.rhs s) := rfl
        rw [hv_eq]
        exact FreeSafe.step g.op FreeSafe.base
          (List.mem_map.mpr ⟨g.lhs, hl, rfl⟩)
          (List.mem_map.mpr ⟨g.rhs, hr, rfl⟩)
          (fun h => h)
      refine ⟨1 + m, ws, ?_, free_compose h1 hrun, hin⟩
      simp [hd]; omega

theorem three_saved {ρ σ : Type} (lift : σ → ρ) {gs : List (TGate ρ)}
    {a b c : TGate ρ} (ha : a ∈ gs) (hb : b ∈ gs) (hc : c ∈ gs)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (da : disappears lift a) (db : disappears lift b) (dc : disappears lift c) :
    3 ≤ (gs.filter (fun g => @decide (disappears lift g) (Classical.propDecidable _))).length := by
  classical
  let L := gs.filter (fun g => @decide (disappears lift g) (Classical.propDecidable _))
  have haL : a ∈ L := List.mem_filter.mpr ⟨ha, by simp [da]⟩
  have hbL : b ∈ L := List.mem_filter.mpr ⟨hb, by simp [db]⟩
  have hcL : c ∈ L := List.mem_filter.mpr ⟨hc, by simp [dc]⟩
  have hsub : [a, b, c] ⊆ L := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hnd : ([a, b, c] : List (TGate ρ)).Nodup := by simp [hab, hac, hbc]
  have hle : ([a, b, c] : List (TGate ρ)).toFinset.card ≤ L.toFinset.card :=
    Finset.card_le_card (fun x hx => List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp hx)))
  have hc1 : ([a, b, c] : List (TGate ρ)).toFinset.card = 3 := by
    rw [List.toFinset_card_of_nodup hnd]; rfl
  have hc2 : L.toFinset.card ≤ L.length := List.toFinset_card_le L
  have hres : 3 ≤ L.length := by omega
  exact hres

theorem trace_agrees_outside {ρ : Type} {raw : List (ρ → Bool)} {gs : List (TGate ρ)}
    (x : ρ → Bool) (r s : ρ) (hv : ValidTrace raw gs)
    (hraw : ∀ w ∈ raw, w ≠ x → w r = w s)
    (hno : ∀ g ∈ gs, ¬ reads g x) :
    ∀ w ∈ traceBank raw gs, w ≠ x → w r = w s := by
  induction gs generalizing raw with
  | nil => exact hraw
  | cons g gs ih =>
    rcases hv with ⟨hl, hr, hv'⟩
    apply ih hv'
    · intro w hw hwx
      rcases List.mem_cons.mp hw with rfl | hw
      · have hgx := hno g List.mem_cons_self
        have h1 : g.lhs r = g.lhs s := hraw _ hl (fun e => hgx (Or.inl e))
        have h2 : g.rhs r = g.rhs s := hraw _ hr (fun e => hgx (Or.inr e))
        simp [TGate.val, h1, h2]
      · exact hraw w hw hwx
    · intro t ht; exact hno t (List.mem_cons_of_mem _ ht)

theorem exists_reader {ρ : Type} {raw : List (ρ → Bool)} {out x : ρ → Bool}
    {gs : List (TGate ρ)} (hs : Sufficient raw out gs) (hne : out ≠ x)
    (r s : ρ) (hout : out r ≠ out s) (hraw : ∀ w ∈ raw, w ≠ x → w r = w s) :
    ∃ g ∈ gs, reads g x := by
  by_contra hno
  exact hout (trace_agrees_outside x r s hs.1 hraw (fun g hg h => hno ⟨g, hg, h⟩) out hs.2 hne)

theorem second_reader {ρ : Type} {raw : List (ρ → Bool)} {out x : ρ → Bool}
    {g : TGate ρ} {gs : List (TGate ρ)} (hs : Sufficient raw out (g :: gs))
    (hne : out ≠ x) (r s : ρ) (hout : out r ≠ out s) (hg : g.val r = g.val s)
    (hraw : ∀ w ∈ raw, w ≠ x → w r = w s) :
    ∃ h ∈ gs, reads h x := by
  apply exists_reader ⟨hs.1.2.2, hs.2⟩ hne r s hout
  intro w hw hwx
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hg
  · exact hraw w hw hwx

inductive UsePath {ρ : Type} : List (TGate ρ) → (ρ → Bool) → (ρ → Bool) → Prop where
  | hit {g gs w out} : reads g w → g.val = out → UsePath (g :: gs) w out
  | chain {g gs w out} : reads g w → UsePath gs g.val out → UsePath (g :: gs) w out
  | skip {g gs w out} : UsePath gs w out → UsePath (g :: gs) w out

theorem boundary_gate {ρ σ : Type} (lift : σ → ρ) {gs : List (TGate ρ)} {w out : ρ → Bool}
    (hp : UsePath gs w out) (hw : restrict lift w = constF) (hout : restrict lift out ≠ constF) :
    ∃ u ∈ gs, disappears lift u ∧ restrict lift u.val ≠ constF ∧
      ∃ z, reads u z ∧ restrict lift z = constF ∧ (z = w ∨ ∃ t ∈ gs, t.val = z) := by
    induction hp with
  | @hit g gs w out hr heq =>
    exact ⟨g, List.mem_cons_self, reading_zero_disappears lift hw hr, heq ▸ hout, w, hr, hw, Or.inl rfl⟩
  | @chain g gs w out hr hp' ih =>
    by_cases hz : restrict lift g.val = constF
    · obtain ⟨u, hu, hdu, hnz, z, hrz, hz0, hzw⟩ := ih hz hout
      refine ⟨u, List.mem_cons_of_mem _ hu, hdu, hnz, z, hrz, hz0, ?_⟩
      rcases hzw with rfl | ⟨t, ht, rfl⟩
      · exact Or.inr ⟨g, List.mem_cons_self, rfl⟩
      · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, rfl⟩
    · exact ⟨g, List.mem_cons_self, reading_zero_disappears lift hw hr, hz, w, hr, hw, Or.inl rfl⟩
  | @skip g gs w out _ ih =>
    obtain ⟨u, hu, hdu, hnz, z, hrz, hz0, hzw⟩ := ih hw hout
    refine ⟨u, List.mem_cons_of_mem _ hu, hdu, hnz, z, hrz, hz0, ?_⟩
    rcases hzw with rfl | ⟨t, ht, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, rfl⟩

theorem omit_dead_set {ρ : Type} {raw : List (ρ → Bool)} {out : ρ → Bool}
    {gs : List (TGate ρ)} (D : (ρ → Bool) → Prop)
    (hs : Sufficient raw out gs) (hnd : ¬ D out)
    (hdead : ∀ w, D w → ¬ UsePath gs w out) :
    ∃ ts, ts.length ≤ gs.length ∧
      Sufficient (raw.filter (fun w => @decide (¬ D w) (Classical.propDecidable _))) out ts := by
  classical
  induction gs generalizing raw D with
  | nil =>
    refine ⟨[], Nat.le_refl _, trivial, List.mem_filter.mpr ⟨hs.2, by simp [hnd]⟩⟩
  | cons g gs ih =>
    rcases hs with ⟨⟨hl, hr, hv⟩, hout⟩
    by_cases hkill : D g.lhs ∨ D g.rhs
    · have hg_ne : g.val ≠ out := by
        intro heq
        rcases hkill with hdl | hdr
        · exact hdead _ hdl (UsePath.hit (Or.inl rfl) heq)
        · exact hdead _ hdr (UsePath.hit (Or.inr rfl) heq)
      let D' : (ρ → Bool) → Prop := fun w => D w ∨ w = g.val
      have hnd' : ¬ D' out := fun h => h.elim hnd (fun e => hg_ne e.symm)
      have hdead' : ∀ w, D' w → ¬ UsePath gs w out := by
        intro w hw hp
        rcases hw with hw | rfl
        · exact hdead w hw (UsePath.skip hp)
        · rcases hkill with hdl | hdr
          · exact hdead _ hdl (UsePath.chain (Or.inl rfl) hp)
          · exact hdead _ hdr (UsePath.chain (Or.inr rfl) hp)
      obtain ⟨ts, hlen, hs'⟩ := ih D' ⟨hv, hout⟩ hnd' hdead'
      have hsub : ∀ w, w ∈ (g.val :: raw).filter (fun w => @decide (¬ D' w) (Classical.propDecidable _)) →
          w ∈ raw.filter (fun w => @decide (¬ D w) (Classical.propDecidable _)) := by
        intro w hw
        obtain ⟨hm, hp⟩ := List.mem_filter.mp hw
        have hnp : ¬ D' w := by simpa using hp
        rcases List.mem_cons.mp hm with rfl | hm
        · exact (hnp (Or.inr rfl)).elim
        · have hndw : ¬ D w := fun hd => hnp (Or.inl hd); exact List.mem_filter.mpr ⟨hm, by simp [hndw]⟩
      obtain ⟨hv2, hb2⟩ := valid_sub hsub hs'.1
      exact ⟨ts, Nat.le_trans hlen (Nat.le_succ _), hv2, hb2 _ hs'.2⟩
    · have hnl : ¬ D g.lhs := fun h => hkill (Or.inl h)
      have hnr : ¬ D g.rhs := fun h => hkill (Or.inr h)
      have hdead' : ∀ w, D w → ¬ UsePath gs w out := fun w hw hp => hdead w hw (UsePath.skip hp)
      obtain ⟨ts, hlen, hs'⟩ := ih D ⟨hv, hout⟩ hnd hdead'
      have hl' : g.lhs ∈ raw.filter (fun w => @decide (¬ D w) (Classical.propDecidable _)) :=
        List.mem_filter.mpr ⟨hl, by simp [hnl]⟩
      have hr' : g.rhs ∈ raw.filter (fun w => @decide (¬ D w) (Classical.propDecidable _)) :=
        List.mem_filter.mpr ⟨hr, by simp [hnr]⟩
      have hsub : ∀ w, w ∈ (g.val :: raw).filter (fun w => @decide (¬ D w) (Classical.propDecidable _)) →
          w ∈ g.val :: raw.filter (fun w => @decide (¬ D w) (Classical.propDecidable _)) := by
        intro w hw
        obtain ⟨hm, hp⟩ := List.mem_filter.mp hw
        rcases List.mem_cons.mp hm with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hm, hp⟩)
      obtain ⟨hv2, hb2⟩ := valid_sub hsub hs'.1
      exact ⟨g :: ts, Nat.succ_le_succ hlen, ⟨hl', hr', hv2⟩, hb2 _ hs'.2⟩

theorem omit_dead_head {ρ : Type} {raw : List (ρ → Bool)} {out : ρ → Bool}
    {g : TGate ρ} {gs : List (TGate ρ)}
    (hs : Sufficient raw out (g :: gs))
    (hne : g.val ≠ out) (hdead : ¬ UsePath gs g.val out) :
    ∃ ts, ts.length ≤ gs.length ∧ Sufficient raw out ts := by
  classical
  obtain ⟨ts, hlen, hs'⟩ := omit_dead_set (fun w => w = g.val) ⟨hs.1.2.2, hs.2⟩ (Ne.symm hne)
    (fun w hw => hw ▸ hdead)
  have hsub : ∀ w, w ∈ (g.val :: raw).filter (fun w => @decide (¬ (w = g.val)) (Classical.propDecidable _)) →
      w ∈ raw := by
    intro w hw
    obtain ⟨hm, hp⟩ := List.mem_filter.mp hw
    have hne' : w ≠ g.val := by simpa using hp
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (hne' rfl).elim
    · exact hm
  obtain ⟨hv2, hb2⟩ := valid_sub hsub hs'.1
  exact ⟨ts, hlen, hv2, hb2 _ hs'.2⟩

theorem omit_dead_mid {ρ : Type} {raw : List (ρ → Bool)} {out : ρ → Bool}
    {pre post : List (TGate ρ)} {h : TGate ρ}
    (hs : Sufficient raw out (pre ++ h :: post))
    (hne : h.val ≠ out) (hdead : ¬ UsePath post h.val out) :
    ∃ ts, ts.length ≤ pre.length + post.length ∧ Sufficient raw out ts := by
  induction pre generalizing raw with
  | nil => simpa using omit_dead_head hs hne hdead
  | cons g pre ih =>
    rcases hs with ⟨⟨hl, hr, hv⟩, hout⟩
    obtain ⟨ts, hlen, hs'⟩ := ih ⟨hv, hout⟩
    exact ⟨g :: ts, by simp; omega, ⟨hl, hr, hs'.1⟩, hs'.2⟩

/-! ### Section 3: Live-Set Width-Cover Search Engine -/

def P58 : Nat := 288230376151711744

structure Wire where
  t : Nat
  f : Nat
  s : Nat
deriving DecidableEq

inductive BST where
  | leaf
  | node (kt kf rk wa wb wop : Nat) (l r : BST)

def BST.lookup (t f : Nat) : BST → Nat
  | .leaf => 99
  | .node kt kf rk _ _ _ l r =>
    if t < kt then l.lookup t f
    else if t > kt then r.lookup t f
    else if f == kf then rk else 99

def rankBST : BST := (BST.node (76882874446530964 * P58 + 154389024727892031) 31 8 0 1 0 (BST.node (554153872982496 * P58 + 1970428308447236) 153966984594317312 0 3 4 3 (BST.node (1069547520 * P58 + 287949416821161988) 144959785339453440 0 4 5 2 (BST.node (32767 * P58 + 1649267502824) 16906640544628704 0 5 6 2 (BST.node (28951 * P58 + 272432601136950849) 2955489939947008 0 2 6 2 (BST.node (27094 * P58 + 231583646610375919) 1200739711975935 3 1 6 2 (BST.node (23997 * P58 + 192987957555110447) 282592741949471 5 0 6 2 BST.leaf BST.leaf) BST.leaf) (BST.node (32736 * P58 + 287949416571136132) 9851795983687680 0 4 6 2 (BST.node (32280 * P58 + 286225305029349090) 4714989327753184 0 3 6 2 BST.leaf BST.leaf) BST.leaf)) (BST.node (950239232 * P58 + 272432601376882689) 36732487650377728 0 2 5 2 (BST.node (922419200 * P58 + 231590243749593111) 74839805132831 5 1 5 2 (BST.node (750157824 * P58 + 192986308336025623) 18296991282888735 3 0 5 2 BST.leaf BST.leaf) BST.leaf) (BST.node (1060896768 * P58 + 286225305172836354) 72268983740268544 0 3 5 2 BST.leaf BST.leaf))) (BST.node (8795019280415 * P58 + 28037547562856) 7899441289764832 0 4 5 3 (BST.node (7256351113238 * P58 + 217709745014139) 1200739711975935 3 1 4 2 (BST.node (6413463486493 * P58 + 177598508433979) 18015516274720799 5 0 4 2 (BST.node (1073709056 * P58 + 6597320245264) 270226973295247360 0 5 6 3 BST.leaf BST.leaf) BST.leaf) (BST.node (8658658000920 * P58 + 246316375873378) 76772583367647200 0 3 4 2 (BST.node (7825432739863 * P58 + 246298659132993) 38421337007332864 0 2 4 2 BST.leaf BST.leaf) BST.leaf)) (BST.node (475098557645254 * P58 + 1695556520919069) 1130370967797791 5 1 3 2 (BST.node (387119369585061 * P58 + 1409025818239005) 18296991282888735 3 0 3 2 (BST.node (8795023441920 * P58 + 32985350279440) 126111784684617728 0 4 6 3 BST.leaf BST.leaf) BST.leaf) (BST.node (492710066880775 * P58 + 1970333263421441) 38843549973864448 0 2 3 2 BST.leaf BST.leaf)))) (BST.node (28711959604237832 * P58 + 56330617945233920) 76702214623469056 0 1 3 3 (BST.node (8505822074113760 * P58 + 15763114119135364) 153404034137456640 0 2 4 3 (BST.node (5665513977154728 * P58 + 11260674132934718) 18296991282888735 4 0 2 2 (BST.node (554290238423040 * P58 + 32985741066256) 198169379255353344 0 3 6 3 (BST.node (554290225611239 * P58 + 28037831811080) 12403040917250048 0 3 5 3 BST.leaf BST.leaf) BST.leaf) (BST.node (8445211493273096 * P58 + 15763036790849954) 76631845877318112 0 2 3 3 (BST.node (6808732303886528 * P58 + 13517499033190846) 1200739711975935 4 1 2 2 BST.leaf BST.leaf) BST.leaf)) (BST.node (19212059938165801 * P58 + 38598932892361216) 18296991282888704 12 0 1 2 (BST.node (8506791664812032 * P58 + 32985376096528) 234198175771000832 0 2 6 3 (BST.node (8506791541346024 * P58 + 28037563285928) 14654840730812896 0 2 5 3 BST.leaf BST.leaf) BST.leaf) (BST.node (27093091924086785 * P58 + 54359856930077184) 38984287464193536 0 1 2 3 BST.leaf BST.leaf))) (BST.node (45178976003497986 * P58 + 90705318159178816) 38984287464193536 0 0 2 3 (BST.node (28791151285010432 * P58 + 26388746407936) 270226973295247360 0 1 6 3 (BST.node (28791151133726249 * P58 + 28037832882688) 15780740637785600 0 1 5 3 (BST.node (28789612612687392 * P58 + 56576883101902848) 153966984594317312 0 1 4 3 BST.leaf BST.leaf) BST.leaf) (BST.node (38441162344308802 * P58 + 77201219021718976) 1200739711975904 12 1 0 2 BST.leaf BST.leaf)) (BST.node (48020253367607874 * P58 + 26388548672960) 16906640544628704 0 0 5 3 (BST.node (48017872131203648 * P58 + 95139057994680448) 153685509586149376 0 0 4 3 (BST.node (47853082822320640 * P58 + 94646373371911616) 76772583367647200 0 0 3 3 BST.leaf BST.leaf) BST.leaf) (BST.node (48020253691150336 * P58 + 32985820500224) 252212574754308096 0 0 6 3 BST.leaf BST.leaf))))) (BST.node (143948017207017405 * P58 + 287634330992164863) 95069574650535935 7 0 3 1 (BST.node (134536096729005567 * P58 + 270189176641972223) 19497730994864639 13 0 1 1 (BST.node (108515304486953238 * P58 + 218072744716420161) 0 0 1 2 0 (BST.node (96088520921210272 * P58 + 192810359111819268) 281475008167936 0 0 4 0 (BST.node (95707815015111704 * P58 + 191578931802014242) 0 0 0 3 0 (BST.node (90429420407542037 * P58 + 181727283487318529) 0 0 0 2 0 BST.leaf BST.leaf) BST.leaf) (BST.node (96094934384672768 * P58 + 65142800) 18014398540939264 0 0 6 0 (BST.node (96094933634538941 * P58 + 1649284227624) 0 0 0 5 0 BST.leaf BST.leaf) BST.leaf)) (BST.node (115324035868420566 * P58 + 17896) 1125899906843104 0 1 5 0 (BST.node (115316780439726528 * P58 + 231372534004596868) 0 0 1 4 0 (BST.node (114848938233194512 * P58 + 229894687228691938) 70368744178144 0 1 3 0 BST.leaf BST.leaf) BST.leaf) (BST.node (115324036790812672 * P58 + 6597139235088) 0 0 1 6 0 BST.leaf BST.leaf))) (BST.node (141273910388194751 * P58 + 283693275779432063) 57281278747082271 9 0 2 1 (BST.node (135608395460800791 * P58 + 269614656) 2251799813815808 0 2 5 0 (BST.node (135600570978300160 * P58 + 272186302987364352) 562950456860672 0 2 4 0 (BST.node (135115686344159248 * P58 + 270462268383075904) 140737490329088 0 2 3 0 BST.leaf BST.leaf) BST.leaf) (BST.node (135608396411011072 * P58 + 509546496) 36028797524246528 0 2 6 0 BST.leaf BST.leaf)) (BST.node (143560896776535576 * P58 + 1089504) 4503599627378656 0 3 5 0 (BST.node (143552239179431424 * P58 + 285978988798052480) 0 0 3 4 0 (BST.node (142417128714926551 * P58 + 285950100679688191) 40185027176169471 9 1 2 1 BST.leaf BST.leaf) BST.leaf) (BST.node (143560897837400064 * P58 + 144576768) 72057594039894016 0 3 6 0 BST.leaf BST.leaf)))) (BST.node (144115187924566015 * P58 + 231618281582493695) 16981480349761535 11 1 5 1 (BST.node (144113649403527158 * P58 + 288167126851513855) 155167724306293247 7 1 4 1 (BST.node (144106391982866400 * P58 + 285337728) 9007199254863872 0 4 5 0 (BST.node (144053607904313119 * P58 + 288195638437347299) 115616133341511648 10 2 3 1 (BST.node (144035996395077598 * P58 + 287920861694844927) 77902954335444991 11 1 3 1 BST.leaf BST.leaf) BST.leaf) (BST.node (144112806515900413 * P58 + 288127015614933695) 171982500869038111 11 0 4 1 (BST.node (144106393052381184 * P58 + 535363584) 144115188610629632 0 4 6 0 BST.leaf BST.leaf) BST.leaf)) (BST.node (144115187002114048 * P58 + 26388565397760) 0 0 5 6 0 (BST.node (144115051710414840 * P58 + 288195733482373094) 230739567961964512 6 3 4 1 (BST.node (144114218485153783 * P58 + 288195715765632709) 192388321601650176 10 2 4 1 BST.leaf BST.leaf) BST.leaf) (BST.node (144115187752304639 * P58 + 193014346168926207) 35203631827517439 7 0 5 1 BST.leaf BST.leaf))) (BST.node (144115188075850198 * P58 + 231616632496018943) 271427713007223295 7 1 6 1 (BST.node (144115188071694335 * P58 + 287977454654062572) 161866425884082144 1 5 4 1 (BST.node (144115188063043583 * P58 + 286253343005736938) 89175624284897248 2 3 5 1 (BST.node (144115187952386047 * P58 + 272460639209783273) 53639128195006432 10 2 5 1 BST.leaf BST.leaf) BST.leaf) (BST.node (144115188075847101 * P58 + 193020943440753471) 270509566037196831 11 0 6 1 BST.leaf BST.leaf)) (BST.node (144115188075855840 * P58 + 287982402456779156) 280078769278935040 2 4 6 1 (BST.node (144115188075855384 * P58 + 286258290914992114) 274941962623000544 1 3 6 1 (BST.node (144115188075852055 * P58 + 272465587022593873) 273182463235194368 10 2 6 1 BST.leaf BST.leaf) BST.leaf) (BST.node (144115188075855871 * P58 + 34635153145848) 287133613839876064 6 5 6 1 BST.leaf BST.leaf))))))

def op0 (a b : Wire) : Nat × Nat := (a.t &&& b.t, a.f &&& b.f)
def op1 (a b : Wire) : Nat × Nat := (a.t ||| b.t, a.f ||| b.f)
def op2 (all : Nat) (a b : Wire) : Nat × Nat := (a.t &&& (all - b.t), a.f &&& (all - b.f))
def op3 (all : Nat) (a b : Wire) : Nat × Nat := ((all - a.t) &&& b.t, (all - a.f) &&& b.f)

def mults : List Wire → Nat × Nat
  | [] => (0, 0)
  | w :: ws => let p := mults ws; (w.s ||| p.1, (w.s &&& p.1) ||| p.2)

def hasTF (t f : Nat) : List Wire → Bool
  | [] => false
  | w :: ws => (w.t == t && w.f == f) || hasTF t f ws

def coverSep : List Wire → Nat
  | [] => 0
  | w :: ws => w.s ||| coverSep ws

def dropOne (x : Wire) : List Wire → List Wire
  | [] => []
  | w :: ws => if w.t == x.t && w.f == x.f then ws else w :: dropOne x ws

def dropTwo (x y : Wire) (ws : List Wire) : List Wire :=
  dropOne x (dropOne y ws)

def isTgtTF (all t f : Nat) : Bool := t == all && f == 0

def pairsGo {α : Type} (f : α → α → Bool) : List α → Bool
  | [] => false
  | a :: rest => rest.any (fun b => f a b) || pairsGo f rest

def unateOk : List (Wire × Nat) → Bool
  | [] => true
  | (w, p) :: rest =>
    if p == 0 then unateOk rest
    else let pt := p &&& w.t; (pt == 0 || pt == p) && unateOk rest

def searchD2 (all bound : Nat) : Nat → List Wire → Bool
  | 0, [a] => isTgtTF all a.t a.f
  | 0, _ => false
  | 1, [a] => isTgtTF all a.t a.f
  | 1, [a, b] =>
    (let p := op0 a b; isTgtTF all p.1 p.2) ||
    (let p := op1 a b; isTgtTF all p.1 p.2) ||
    (let p := op2 all a b; isTgtTF all p.1 p.2) ||
    (let p := op3 all a b; isTgtTF all p.1 p.2)
  | 1, _ => false
  | _ + 1, [a] => isTgtTF all a.t a.f
  | k + 1, S =>
    let m := mults S
    if m.1 != all then false
    else
      let once := m.1 - m.2
      let cols := S.map fun w => (w, w.s &&& once)
      if !unateOk cols then false
      else
        pairsGo (fun a b =>
          let ab := if a.2 == 0 then 0 else a.2 &&& b.1.t
          let a0 := ab == 0
          let a1 := ab == a.2
          if !a0 && !a1 then false
          else
            let ba := if b.2 == 0 then 0 else b.2 &&& a.1.t
            let b0 := ba == 0
            let b1 := ba == b.2
            if !b0 && !b1 then false
            else
              let tryOp (mk : Unit → Nat × Nat) : Bool :=
                let tf := mk ()
                let t := tf.1; let f := tf.2
                if (t == 0 && f == 0) || hasTF t f S || (bound != 0 && rankBST.lookup t f < bound) then false
                else if isTgtTF all t f then true
                else
                  let rest2 := dropTwo a.1 b.1 S
                  let sv := t ^^^ f
                  if (coverSep rest2 ||| sv) == all then searchD2 all bound k (⟨t, f, sv⟩ :: rest2)
                  else false
              (if a1 && b1 then tryOp (fun _ => op0 a.1 b.1) else false) ||
              (if a0 && b0 then tryOp (fun _ => op1 a.1 b.1) else false) ||
              (if a0 && b1 then tryOp (fun _ => op2 all a.1 b.1) else false) ||
              (if a1 && b0 then tryOp (fun _ => op3 all a.1 b.1) else false)
        ) cols

def search (all bound : Nat) : Nat → List Wire → Bool
  | 0, [a] => isTgtTF all a.t a.f
  | 0, _ => false
  | 1, [a] => isTgtTF all a.t a.f
  | 1, [a, b] => searchD2 all bound 1 [a, b]
  | 1, _ => false
  | _ + 1, [a] => isTgtTF all a.t a.f
  | k + 1, S =>
    let n := S.length
    if n > k + 2 then false
    else if n == k + 2 then searchD2 all bound (k + 1) S
    else
      let m := mults S
      if m.1 != all then false
      else
        let once := m.1 - m.2
        let cols := S.map fun w => (w, w.s &&& once)
        let allow0 := decide (n ≤ k)
        pairsGo (fun a b =>
          let ab := if a.2 == 0 then 0 else a.2 &&& b.1.t
          let a0 := ab == 0
          let a1 := ab == a.2
          let ba := if b.2 == 0 then 0 else b.2 &&& a.1.t
          let b0 := ba == 0
          let b1 := ba == b.2
          let tryOp (da db : Bool) (mk : Unit → Nat × Nat) : Bool :=
            if !(allow0 || da || db) then false
            else
              let tf := mk ()
              let t := tf.1; let f := tf.2
              if (t == 0 && f == 0) || hasTF t f S || (bound != 0 && rankBST.lookup t f < bound) then false
              else if isTgtTF all t f then true
              else
                let v : Wire := ⟨t, f, t ^^^ f⟩
                (if da && db then
                  let rest2 := dropTwo a.1 b.1 S
                  if (coverSep rest2 ||| v.s) == all then search all bound k (v :: rest2) else false
                 else false) ||
                (if da then search all bound k (v :: dropOne a.1 S) else false) ||
                (if db then search all bound k (v :: dropOne b.1 S) else false) ||
                (if allow0 then search all bound k (v :: S) else false)
          tryOp a1 b1 (fun _ => op0 a.1 b.1) ||
          tryOp a0 b0 (fun _ => op1 a.1 b.1) ||
          tryOp a0 b1 (fun _ => op2 all a.1 b.1) ||
          tryOp a1 b0 (fun _ => op3 all a.1 b.1)
        ) cols

/-! ### Section 4: Soundness of `LiveSafe`, `unateOk`, `searchD2`, and `search` -/

inductive LiveSafe {ρ : Type} (target : ρ → Bool) (forbid : (ρ → Bool) → Prop) :
    Nat → ((ρ → Bool) → Prop) → Prop where
  | stop : LiveSafe target forbid 0 (fun w => w = target)
  | step (op : Op) {k S'} (a b : ρ → Bool) (S : (ρ → Bool) → Prop) :
      S a → S b → a ≠ b →
      (let v := fun r => evalOp op (a r) (b r)
       ¬ forbid v ∧ v ≠ constF ∧ ¬ S v ∧ S' v ∧
       (∀ w, S' w → w = v ∨ S w) ∧
       (∀ w, S w → w = a ∨ w = b ∨ (S' w ∧ w ≠ v))) →
      LiveSafe target forbid k S' →
      LiveSafe target forbid (k + 1) S

theorem rewind_aux {ρ : Type} {raw : List (ρ → Bool)} {target : ρ → Bool}
    {forbid : (ρ → Bool) → Prop} (h0 : constF ∈ raw) :
    ∀ {n ws}, FreeSafe raw forbid n ws →
    ∀ {k S'}, LiveSafe target forbid k S' → (∀ w, S' w → w ∈ ws) →
    ∃ m S, m ≤ n + k ∧ LiveSafe target forbid m S ∧ (∀ w, S w → w ∈ raw) := by
  intro n ws hrun
  induction hrun with
  | base =>
    intro k S' hl hsub
    exact ⟨k, S', by omega, hl, hsub⟩
  | @step op n ws a b hrun ha hb hnf ih =>
    intro k S' hl hsub
    let v : ρ → Bool := fun r => evalOp op (a r) (b r)
    by_cases hv : S' v
    · by_cases hvin : v ∈ ws
      · have hsub' : ∀ w, S' w → w ∈ ws := by
          intro w hw
          rcases List.mem_cons.mp (hsub w hw) with rfl | hw'
          · exact hvin
          · exact hw'
        obtain ⟨m, S, hle, hl', hsr⟩ := ih hl hsub'
        exact ⟨m, S, by omega, hl', hsr⟩
      · have hv0 : v ≠ constF := by
          intro heq
          apply hvin
          rw [heq]
          clear hvin hv hsub hl heq v hnf ha hb ih
          induction hrun with
          | base => exact h0
          | step _ _ _ _ _ ih0 => exact List.mem_cons_of_mem _ ih0
        have hab : a ≠ b := by
          intro heq
          subst heq
          cases op with
          | conj => exact hvin ((funext fun r => by simp [v, evalOp] : v = a) ▸ ha)
          | disj => exact hvin ((funext fun r => by simp [v, evalOp] : v = a) ▸ ha)
          | diffL => exact hv0 (funext fun r => by simp [v, evalOp, constF])
          | diffR => exact hv0 (funext fun r => by simp [v, evalOp, constF])
        let S : (ρ → Bool) → Prop := fun w => w = a ∨ w = b ∨ (S' w ∧ w ≠ v)
        have hsubS : ∀ w, S w → w ∈ ws := by
          intro w hw
          rcases hw with rfl | rfl | ⟨hw', hne⟩
          · exact ha
          · exact hb
          · rcases List.mem_cons.mp (hsub w hw') with rfl | hw''
            · exact (hne rfl).elim
            · exact hw''
        have hnSv : ¬ S v := fun h => hvin (hsubS v h)
        have hstep : LiveSafe target forbid (k + 1) S :=
          LiveSafe.step op a b S (Or.inl rfl) (Or.inr (Or.inl rfl)) hab
            ⟨hnf, hv0, hnSv, hv,
             fun w hw => by
               by_cases hwe : w = v
               · exact Or.inl hwe
               · exact Or.inr (Or.inr (Or.inr ⟨hw, hwe⟩)),
             fun w hw => hw⟩
            hl
        obtain ⟨m, S0, hle, hl0, hsr⟩ := ih hstep hsubS
        exact ⟨m, S0, by omega, hl0, hsr⟩
    · have hsub' : ∀ w, S' w → w ∈ ws := by
        intro w hw
        rcases List.mem_cons.mp (hsub w hw) with rfl | hw'
        · exact (hv hw).elim
        · exact hw'
      obtain ⟨m, S, hle, hl', hsr⟩ := ih hl hsub'
      exact ⟨m, S, by omega, hl', hsr⟩

theorem rewind {ρ : Type} {raw ws : List (ρ → Bool)} {target : ρ → Bool}
    {forbid : (ρ → Bool) → Prop} {n : Nat}
    (h0 : constF ∈ raw) (hrun : FreeSafe raw forbid n ws) (htgt : target ∈ ws) :
    ∃ m S, m ≤ n ∧ LiveSafe target forbid m S ∧ (∀ w, S w → w ∈ raw) := by
  have h := rewind_aux h0 hrun LiveSafe.stop (fun w hw => hw ▸ htgt)
  simpa using h

theorem free_of_live {ρ : Type} {target : ρ → Bool} {forbid : (ρ → Bool) → Prop}
    {k : Nat} {S : (ρ → Bool) → Prop} (hl : LiveSafe target forbid k S) :
    ∀ {raw : List (ρ → Bool)}, (∀ w, S w → w ∈ raw) →
    ∃ ws, FreeSafe raw forbid k ws ∧ target ∈ ws := by
  induction hl with
  | stop =>
    intro raw hsub
    exact ⟨raw, FreeSafe.base, hsub target rfl⟩
  | @step op k S' a b S ha hb _ hcond _ ih =>
    intro raw hsub
    have h1 : FreeSafe raw forbid 1 ((fun r => evalOp op (a r) (b r)) :: raw) :=
      FreeSafe.step op FreeSafe.base (hsub a ha) (hsub b hb) hcond.1
    have hsub' : ∀ w, S' w → w ∈ (fun r => evalOp op (a r) (b r)) :: raw := by
      intro w hw
      rcases hcond.2.2.2.2.1 w hw with rfl | hwS
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub w hwS)
    obtain ⟨ws, hrun, htgt⟩ := ih hsub'
    exact ⟨ws, by simpa [Nat.add_comm] using free_compose h1 hrun, htgt⟩

theorem LiveSafe.separates {ρ : Type} {target : ρ → Bool} {forbid : (ρ → Bool) → Prop}
    {k : Nat} {S : (ρ → Bool) → Prop} (hl : LiveSafe target forbid k S)
    {r s : ρ} (hd : target r ≠ target s) : ∃ w, S w ∧ w r ≠ w s := by
  induction hl with
  | stop => exact ⟨target, rfl, hd⟩
  | @step op k S' a b S ha hb _ hcond _ ih =>
    obtain ⟨w, hw', hwd⟩ := ih
    rcases hcond.2.2.2.2.1 w hw' with rfl | hwS
    · by_cases hae : a r = a s
      · refine ⟨b, hb, fun hbe => hwd ?_⟩
        simp [hae, hbe]
      · exact ⟨a, ha, hae⟩
    · exact ⟨w, hwS, hwd⟩

theorem LiveSafe.no_constF {ρ : Type} {target : ρ → Bool} {forbid : (ρ → Bool) → Prop}
    {k : Nat} {S : (ρ → Bool) → Prop} (hl : LiveSafe target forbid k S)
    (ht : target ≠ constF) : ¬ S constF := by
  induction hl with
  | stop => exact Ne.symm ht
  | @step op k S' a b S ha hb _ hcond _ ih =>
    intro h0
    rcases hcond.2.2.2.2.2 constF h0 with hca | hcb | ⟨hS0, _⟩
    · subst hca
      have hcases : (fun r => evalOp op (constF r) (b r)) = constF ∨
          (fun r => evalOp op (constF r) (b r)) = b := by
        cases op <;> [left; right; left; right] <;> funext r <;> simp [evalOp, constF]
      rcases hcases with h1 | h2
      · exact hcond.2.1 h1
      · apply hcond.2.2.1; rw [h2]; exact hb
    · subst hcb
      have hcases : (fun r => evalOp op (a r) (constF r)) = constF ∨
          (fun r => evalOp op (a r) (constF r)) = a := by
        cases op <;> [left; right; right; left] <;> funext r <;> simp [evalOp, constF]
      rcases hcases with h1 | h2
      · exact hcond.2.1 h1
      · apply hcond.2.2.1; rw [h2]; exact ha
    · exact ih hS0

-- Bit-level helpers:
theorem xor_add_eq_of_submask : ∀ a b : Nat,
    (∀ i, b.testBit i = true → a.testBit i = true) → (a ^^^ b) + b = a := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b hsub
    by_cases ha0 : a = 0
    · subst ha0
      have hb0 : b = 0 := by
        apply Nat.eq_of_testBit_eq; intro i
        cases hb : b.testBit i
        · simp
        · have := hsub i hb; simp at this
      simp [hb0]
    · have hdiv : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha0) (by decide)
      have hih : ((a / 2) ^^^ (b / 2)) + (b / 2) = a / 2 := by
        apply ih (a / 2) hdiv (b / 2)
        intro i hi
        have := hsub (i + 1) (by simpa [Nat.testBit_succ] using hi)
        simpa [Nat.testBit_succ] using this
      have h0 : b.testBit 0 = true → a.testBit 0 = true := hsub 0
      have hxd : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := Nat.xor_div_two
      have hxm : (a ^^^ b).testBit 0 = xor (a.testBit 0) (b.testBit 0) := Nat.testBit_xor a b 0
      have hm (x : Nat) : x % 2 = if x.testBit 0 then 1 else 0 := by
        rw [Nat.testBit_zero]
        rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
      have hae := Nat.div_add_mod a 2
      have hbe := Nat.div_add_mod b 2
      have hxe := Nat.div_add_mod (a ^^^ b) 2
      rw [hxd, hm (a ^^^ b), hxm] at hxe
      rw [hm a] at hae; rw [hm b] at hbe
      cases hta : a.testBit 0 <;> cases htb : b.testBit 0
      · simp [hta, htb] at hae hbe hxe; omega
      · have := h0 htb; rw [hta] at this; cases this
      · simp [hta, htb] at hae hbe hxe; omega
      · simp [hta, htb] at hae hbe hxe; omega

theorem sub_eq_xor_of_submask (a b : Nat) (h : ∀ i, b.testBit i = true → a.testBit i = true) :
    a - b = a ^^^ b := by
  have := xor_add_eq_of_submask a b h; omega

theorem testBit_all_mask (W i : Nat) (hi : i < W) : (2 ^ W - 1).testBit i = true := by
  rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hi

theorem testBit_all_mask_ge (W i : Nat) (hi : W ≤ i) : (2 ^ W - 1).testBit i = false := by
  rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_false (Nat.not_lt.mpr hi)

theorem testBit_ge_of_lt_two_pow (W x i : Nat) (hx : x < 2 ^ W) (hi : W ≤ i) :
    x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

theorem lt_two_pow_of_testBit (W x : Nat) (h : ∀ i ≥ W, x.testBit i = false) : x < 2 ^ W := by
  by_contra hge
  have hge' : 2 ^ W ≤ x := Nat.not_lt.mp hge
  have hpos : x ≠ 0 := fun h0 => Nat.not_le.mpr (Nat.two_pow_pos W) (h0 ▸ hge')
  have hlog : W ≤ Nat.log2 x := (Nat.le_log2 hpos).mpr hge'
  have htb : x.testBit (Nat.log2 x) = true := Nat.testBit_log2 hpos
  have hf := h (Nat.log2 x) hlog
  rw [htb] at hf; cases hf

theorem testBit_sub_all (W x i : Nat) (hx : x < 2 ^ W) (hi : i < W) :
    ((2 ^ W - 1) - x).testBit i = !x.testBit i := by
  rw [sub_eq_xor_of_submask (2 ^ W - 1) x (fun j hj => by
    have hlt : j < W := by
      by_contra hge
      rw [testBit_ge_of_lt_two_pow W x j hx (Nat.not_lt.mp hge)] at hj; cases hj
    exact testBit_all_mask W j hlt)]
  rw [Nat.testBit_xor, testBit_all_mask W i hi]
  cases x.testBit i <;> rfl

def GoodWire (W : Nat) (w : Wire) : Prop :=
  w.t < 2 ^ W ∧ w.f < 2 ^ W ∧ w.s = w.t ^^^ w.f

instance instDecidableGoodWire (W : Nat) (w : Wire) : Decidable (GoodWire W w) := by
  unfold GoodWire; infer_instance

def den (W : Nat) (w : Wire) : Bool × Fin W → Bool :=
  fun r => if r.1 then w.t.testBit r.2.val else w.f.testBit r.2.val

def targetDen (W : Nat) : Bool × Fin W → Bool := fun r => r.1

theorem good_op0 {W : Nat} {a b : Wire} (ha : GoodWire W a) (_hb : GoodWire W b) :
    let tf := op0 a b
    let v : Wire := ⟨tf.1, tf.2, tf.1 ^^^ tf.2⟩
    GoodWire W v ∧ den W v = fun r => evalOp .conj (den W a r) (den W b r) := by
  refine ⟨⟨lt_two_pow_of_testBit W _ fun i hi => by
      simp [op0, Nat.testBit_and, testBit_ge_of_lt_two_pow W _ i ha.1 hi],
    lt_two_pow_of_testBit W _ fun i hi => by
      simp [op0, Nat.testBit_and, testBit_ge_of_lt_two_pow W _ i ha.2.1 hi], rfl⟩, ?_⟩
  funext ⟨bl, idx⟩; cases bl <;> simp [den, op0, evalOp, Nat.testBit_and]

theorem good_op1 {W : Nat} {a b : Wire} (ha : GoodWire W a) (hb : GoodWire W b) :
    let tf := op1 a b
    let v : Wire := ⟨tf.1, tf.2, tf.1 ^^^ tf.2⟩
    GoodWire W v ∧ den W v = fun r => evalOp .disj (den W a r) (den W b r) := by
  refine ⟨⟨lt_two_pow_of_testBit W _ fun i hi => by
      simp [op1, Nat.testBit_or, testBit_ge_of_lt_two_pow W _ i ha.1 hi, testBit_ge_of_lt_two_pow W _ i hb.1 hi],
    lt_two_pow_of_testBit W _ fun i hi => by
      simp [op1, Nat.testBit_or, testBit_ge_of_lt_two_pow W _ i ha.2.1 hi, testBit_ge_of_lt_two_pow W _ i hb.2.1 hi], rfl⟩, ?_⟩
  funext ⟨bl, idx⟩; cases bl <;> simp [den, op1, evalOp, Nat.testBit_or]

theorem good_op2 {W : Nat} {a b : Wire} (ha : GoodWire W a) (hb : GoodWire W b) :
    let tf := op2 (2 ^ W - 1) a b
    let v : Wire := ⟨tf.1, tf.2, tf.1 ^^^ tf.2⟩
    GoodWire W v ∧ den W v = fun r => evalOp .diffL (den W a r) (den W b r) := by
  refine ⟨⟨lt_two_pow_of_testBit W _ fun i hi => by
      simp [op2, Nat.testBit_and, testBit_ge_of_lt_two_pow W _ i ha.1 hi],
    lt_two_pow_of_testBit W _ fun i hi => by
      simp [op2, Nat.testBit_and, testBit_ge_of_lt_two_pow W _ i ha.2.1 hi], rfl⟩, ?_⟩
  funext ⟨bl, idx⟩
  cases bl
  · simp [den, op2, evalOp, Nat.testBit_and, testBit_sub_all W b.f idx.val hb.2.1 idx.isLt]
  · simp [den, op2, evalOp, Nat.testBit_and, testBit_sub_all W b.t idx.val hb.1 idx.isLt]

theorem good_op3 {W : Nat} {a b : Wire} (ha : GoodWire W a) (hb : GoodWire W b) :
    let tf := op3 (2 ^ W - 1) a b
    let v : Wire := ⟨tf.1, tf.2, tf.1 ^^^ tf.2⟩
    GoodWire W v ∧ den W v = fun r => evalOp .diffR (den W a r) (den W b r) := by
  refine ⟨⟨lt_two_pow_of_testBit W _ fun i hi => by
      simp [op3, Nat.testBit_and, testBit_ge_of_lt_two_pow W _ i hb.1 hi],
    lt_two_pow_of_testBit W _ fun i hi => by
      simp [op3, Nat.testBit_and, testBit_ge_of_lt_two_pow W _ i hb.2.1 hi], rfl⟩, ?_⟩
  funext ⟨bl, idx⟩
  cases bl
  · simp [den, op3, evalOp, Nat.testBit_and, testBit_sub_all W a.f idx.val ha.2.1 idx.isLt]
  · simp [den, op3, evalOp, Nat.testBit_and, testBit_sub_all W a.t idx.val ha.1 idx.isLt]

theorem den_inj {W : Nat} {a b : Wire} (ha : GoodWire W a) (hb : GoodWire W b)
    (heq : den W a = den W b) : a = b := by
  have ht : a.t = b.t := by
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < W
    · exact congrFun heq (true, ⟨i, hi⟩)
    · rw [testBit_ge_of_lt_two_pow W _ i ha.1 (Nat.not_lt.mp hi),
          testBit_ge_of_lt_two_pow W _ i hb.1 (Nat.not_lt.mp hi)]
  have hf : a.f = b.f := by
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < W
    · exact congrFun heq (false, ⟨i, hi⟩)
    · rw [testBit_ge_of_lt_two_pow W _ i ha.2.1 (Nat.not_lt.mp hi),
          testBit_ge_of_lt_two_pow W _ i hb.2.1 (Nat.not_lt.mp hi)]
  cases a; cases b
  simp only [GoodWire] at ha hb
  simp only [Wire.mk.injEq] at ht hf ⊢
  exact ⟨ht, hf, by rw [ha.2.2, hb.2.2, ht, hf]⟩

theorem isTgtTF_iff {W : Nat} {w : Wire} (hw : GoodWire W w) :
    isTgtTF (2 ^ W - 1) w.t w.f = true ↔ den W w = targetDen W := by
  constructor
  · intro h
    simp only [isTgtTF, Bool.and_eq_true, beq_iff_eq] at h
    funext ⟨bl, idx⟩
    cases bl
    · simp [den, targetDen, h.2]
    · simp [den, targetDen, h.1, testBit_all_mask W idx.val idx.isLt]
  · intro h
    simp only [isTgtTF, Bool.and_eq_true, beq_iff_eq]
    constructor
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < W
      · rw [testBit_all_mask W i hi]; exact congrFun h (true, ⟨i, hi⟩)
      · rw [testBit_ge_of_lt_two_pow W _ i hw.1 (Nat.not_lt.mp hi),
            testBit_all_mask_ge W i (Nat.not_lt.mp hi)]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < W
      · simpa [den, targetDen] using congrFun h (false, ⟨i, hi⟩)
      · rw [testBit_ge_of_lt_two_pow W _ i hw.2.1 (Nat.not_lt.mp hi), Nat.zero_testBit]

theorem isZeroTF_iff {W : Nat} {w : Wire} (hw : GoodWire W w) :
    (w.t == 0 && w.f == 0) = true ↔ den W w = constF := by
  constructor
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    funext ⟨bl, idx⟩; cases bl <;> simp [den, constF, h.1, h.2]
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < W
      · simpa [den, constF] using congrFun h (true, ⟨i, hi⟩)
      · rw [testBit_ge_of_lt_two_pow W _ i hw.1 (Nat.not_lt.mp hi), Nat.zero_testBit]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < W
      · simpa [den, constF] using congrFun h (false, ⟨i, hi⟩)
      · rw [testBit_ge_of_lt_two_pow W _ i hw.2.1 (Nat.not_lt.mp hi), Nat.zero_testBit]

def Rep (W : Nat) (ws : List Wire) (S : (Bool × Fin W → Bool) → Prop) : Prop :=
  ws.Nodup ∧ (∀ w ∈ ws, GoodWire W w) ∧ (∀ f, S f ↔ ∃ w ∈ ws, den W w = f)

theorem wire_sep_testBit {W : Nat} {w : Wire} (hw : GoodWire W w) (i : Fin W) :
    w.s.testBit i.val = (den W w (true, i) != den W w (false, i)) := by
  rw [hw.2.2, Nat.testBit_xor]; simp [den]

theorem wire_sep_ge_false {W : Nat} {w : Wire} (hw : GoodWire W w) (i : Nat) (hi : W ≤ i) :
    w.s.testBit i = false := by
  rw [hw.2.2, Nat.testBit_xor, testBit_ge_of_lt_two_pow W _ i hw.1 hi,
      testBit_ge_of_lt_two_pow W _ i hw.2.1 hi]; rfl

theorem coverSep_testBit (ws : List Wire) (i : Nat) :
    (coverSep ws).testBit i = true ↔ ∃ w ∈ ws, w.s.testBit i = true := by
  induction ws with
  | nil => simp [coverSep]
  | cons a ws ih =>
    simp only [coverSep, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨w, hw, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨w, Or.inr hw, h⟩
    · rintro ⟨w, rfl | hw, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨w, hw, h⟩

theorem coverSep_eq_all_of_live {W k : Nat} {forbid : (Bool × Fin W → Bool) → Prop}
    {S : (Bool × Fin W → Bool) → Prop} {ws : List Wire}
    (hl : LiveSafe (targetDen W) forbid k S) (hr : Rep W ws S) :
    coverSep ws = 2 ^ W - 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < W
  · rw [testBit_all_mask W i hi]
    apply (coverSep_testBit ws i).mpr
    obtain ⟨f, hf, hsep⟩ := hl.separates (r := (true, ⟨i, hi⟩)) (s := (false, ⟨i, hi⟩)) (fun h => Bool.noConfusion h)
    obtain ⟨w, hw, rfl⟩ := (hr.2.2 f).mp hf
    refine ⟨w, hw, ?_⟩
    rw [wire_sep_testBit (hr.2.1 w hw) ⟨i, hi⟩]
    cases h1 : den W w (true, ⟨i, hi⟩) <;> cases h2 : den W w (false, ⟨i, hi⟩) <;> simp_all
  · rw [testBit_all_mask_ge W i (Nat.not_lt.mp hi)]
    cases hc : (coverSep ws).testBit i
    · rfl
    · exfalso
      obtain ⟨w, hw, hwt⟩ := (coverSep_testBit ws i).mp hc
      rw [wire_sep_ge_false (hr.2.1 w hw) i (Nat.not_lt.mp hi)] at hwt
      cases hwt

theorem mults_fst_eq_cover (ws : List Wire) : (mults ws).1 = coverSep ws := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [mults, coverSep, ih]

theorem mults_snd_sub_fst (ws : List Wire) (i : Nat) :
    (mults ws).2.testBit i = true → (mults ws).1.testBit i = true := by
  induction ws with
  | nil => simp [mults]
  | cons a ws ih =>
    simp only [mults, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true]
    rintro (⟨h1, _⟩ | h2)
    · exact Or.inl h1
    · exact Or.inr (ih h2)

theorem mults_snd_of_two {ws : List Wire} (hnd : ws.Nodup) {a b : Wire}
    (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) (i : Nat)
    (h1 : a.s.testBit i = true) (h2 : b.s.testBit i = true) :
    (mults ws).2.testBit i = true := by
  induction ws with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    simp only [mults, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true]
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact (hab rfl).elim
    · left; exact ⟨h1, by rw [mults_fst_eq_cover]; exact (coverSep_testBit xs i).mpr ⟨b, hb', h2⟩⟩
    · left; exact ⟨h2, by rw [mults_fst_eq_cover]; exact (coverSep_testBit xs i).mpr ⟨a, ha', h1⟩⟩
    · right; exact ih hnd.2 ha' hb'

theorem mults_snd_iff {ws : List Wire} (hnd : ws.Nodup) (i : Nat) :
    (mults ws).2.testBit i = true ↔ ∃ a ∈ ws, ∃ b ∈ ws, a ≠ b ∧ a.s.testBit i = true ∧ b.s.testBit i = true := by
  constructor
  · intro h
    induction ws with
    | nil => simp [mults] at h
    | cons x xs ih =>
      rw [List.nodup_cons] at hnd
      simp only [mults, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨h1, h2⟩ | h3
      · rw [mults_fst_eq_cover] at h2
        obtain ⟨b, hb, hbt⟩ := (coverSep_testBit xs i).mp h2
        exact ⟨x, List.mem_cons_self, b, List.mem_cons_of_mem _ hb, fun e => hnd.1 (e ▸ hb), h1, hbt⟩
      · obtain ⟨a, ha, b, hb, hab, h1, h2⟩ := ih hnd.2 h3
        exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, hab, h1, h2⟩
  · rintro ⟨a, ha, b, hb, hab, h1, h2⟩
    exact mults_snd_of_two hnd ha hb hab i h1 h2

theorem priv_testBit_iff {ws : List Wire} (hnd : ws.Nodup)
    {a : Wire} (ha : a ∈ ws) (i : Nat) :
    (a.s &&& ((mults ws).1 - (mults ws).2)).testBit i = true ↔
    a.s.testBit i = true ∧ ∀ b ∈ ws, b ≠ a → b.s.testBit i = false := by
  rw [sub_eq_xor_of_submask _ _ (mults_snd_sub_fst ws)]
  simp only [Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true]
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro b hb hba
    cases hbi : b.s.testBit i
    · rfl
    · have h2 := mults_snd_of_two hnd hb ha hba i hbi hp.1
      have h1 := mults_snd_sub_fst ws i h2
      rw [h1, h2] at hp; simp at hp
  · rintro ⟨h1, hall⟩
    refine ⟨h1, ?_⟩
    have hm1 : (mults ws).1.testBit i = true := by
      rw [mults_fst_eq_cover]; exact (coverSep_testBit ws i).mpr ⟨a, ha, h1⟩
    have hm2 : (mults ws).2.testBit i = false := by
      cases h2 : (mults ws).2.testBit i
      · rfl
      · exfalso
        obtain ⟨u, hu, v, hv, huv, hu1, hv1⟩ := (mults_snd_iff hnd i).mp h2
        by_cases hua : u = a
        · subst hua; rw [hall v hv (Ne.symm huv)] at hv1; cases hv1
        · rw [hall u hu hua] at hu1; cases hu1
    simp [hm1, hm2]

theorem hasTF_iff {W : Nat} {ws : List Wire} (hg : ∀ w ∈ ws, GoodWire W w)
    {v : Wire} (hv : GoodWire W v) :
    hasTF v.t v.f ws = true ↔ v ∈ ws := by
  induction ws with
  | nil => simp [hasTF]
  | cons w ws ih =>
    have hgw := hg w List.mem_cons_self
    have hgws : ∀ u ∈ ws, GoodWire W u := fun u hu => hg u (List.mem_cons_of_mem _ hu)
    simp only [hasTF, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ih hgws, List.mem_cons]
    constructor
    · rintro (⟨ht, hf⟩ | hm)
      · left; cases v; cases w; simp only [GoodWire] at hv hgw; simp_all
      · exact Or.inr hm
    · rintro (rfl | hm)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr hm

theorem dropOne_spec {W : Nat} {ws : List Wire} (hnd : ws.Nodup) (hg : ∀ w ∈ ws, GoodWire W w)
    {x : Wire} (hx : x ∈ ws) :
    (dropOne x ws).Nodup ∧ (∀ w, w ∈ dropOne x ws ↔ w ∈ ws ∧ w ≠ x) ∧ (dropOne x ws).length + 1 = ws.length := by
  induction ws with
  | nil => cases hx
  | cons a ws ih =>
    rw [List.nodup_cons] at hnd
    have hga := hg a List.mem_cons_self
    have hgws : ∀ u ∈ ws, GoodWire W u := fun u hu => hg u (List.mem_cons_of_mem _ hu)
    have hgx := hg x hx
    by_cases hax : a = x
    · subst hax
      simp only [dropOne, beq_self_eq_true, Bool.and_self, ↓reduceIte]
      refine ⟨hnd.2, ?_, rfl⟩
      intro w; constructor
      · intro hw; exact ⟨List.mem_cons_of_mem _ hw, fun e => hnd.1 (e ▸ hw)⟩
      · rintro ⟨hw, hne⟩; rcases List.mem_cons.mp hw with rfl | hw
        · exact (hne rfl).elim
        · exact hw
    · have hcond : (a.t == x.t && a.f == x.f) = false := by
        cases hc : (a.t == x.t && a.f == x.f)
        · rfl
        · exfalso; simp only [Bool.and_eq_true, beq_iff_eq] at hc
          apply hax; cases a; cases x; simp only [GoodWire] at hga hgx; simp_all
      have hxws : x ∈ ws := by
        rcases List.mem_cons.mp hx with rfl | h
        · exact (hax rfl).elim
        · exact h
      obtain ⟨hnd', hmem', hlen'⟩ := ih hnd.2 hgws hxws
      simp only [dropOne, hcond, Bool.false_eq_true, ↓reduceIte]
      refine ⟨List.nodup_cons.mpr ⟨fun ha => hnd.1 (hmem' a |>.mp ha).1, hnd'⟩, ?_, by simp; omega⟩
      intro w; simp only [List.mem_cons, hmem']
      constructor
      · rintro (rfl | ⟨hw, hne⟩)
        · exact ⟨Or.inl rfl, hax⟩
        · exact ⟨Or.inr hw, hne⟩
      · rintro ⟨rfl | hw, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hw, hne⟩

theorem dropTwo_spec {W : Nat} {ws : List Wire} (hnd : ws.Nodup) (hg : ∀ w ∈ ws, GoodWire W w)
    {x y : Wire} (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) :
    (dropTwo x y ws).Nodup ∧ (∀ w, w ∈ dropTwo x y ws ↔ w ∈ ws ∧ w ≠ x ∧ w ≠ y) ∧
    (dropTwo x y ws).length + 2 = ws.length := by
  obtain ⟨hnd1, hmem1, hlen1⟩ := dropOne_spec hnd hg hy
  have hg1 : ∀ w ∈ dropOne y ws, GoodWire W w := fun w hw => hg w ((hmem1 w).mp hw).1
  have hx1 : x ∈ dropOne y ws := (hmem1 x).mpr ⟨hx, hxy⟩
  obtain ⟨hnd2, hmem2, hlen2⟩ := dropOne_spec hnd1 hg1 hx1
  refine ⟨hnd2, ?_, by unfold dropTwo; omega⟩
  intro w; unfold dropTwo; rw [hmem2, hmem1]
  tauto

theorem pairsGo_of_mem {α : Type} {f : α → α → Bool} {l : List α} {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y)
    (h1 : f x y = true) (h2 : f y x = true) : pairsGo f l = true := by
  induction l with
  | nil => cases hx
  | cons a rest ih =>
    simp only [pairsGo, Bool.or_eq_true, List.any_eq_true]
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · exact (hxy rfl).elim
    · exact Or.inl ⟨y, hy', h1⟩
    · exact Or.inl ⟨x, hx', h2⟩
    · exact Or.inr (ih hx' hy')

-- Helper: construct the concrete `ws'` representing `S'` from `LiveSafe.step`:
theorem step_wire_rep {W : Nat} {ws : List Wire} {S S' : (Bool × Fin W → Bool) → Prop}
    {op : Op} {a b : Bool × Fin W → Bool}
    (hr : Rep W ws S) (ha : S a) (hb : S b) (hab : a ≠ b)
    (hnsv : ¬ S (fun r => evalOp op (a r) (b r)))
    (hsv : S' (fun r => evalOp op (a r) (b r)))
    (hsub : ∀ w, S' w → w = (fun r => evalOp op (a r) (b r)) ∨ S w)
    (hcov : ∀ w, S w → w = a ∨ w = b ∨ (S' w ∧ w ≠ (fun r => evalOp op (a r) (b r)))) :
    ∃ wa wb wv : Wire, wa ∈ ws ∧ wb ∈ ws ∧ wa ≠ wb ∧ den W wa = a ∧ den W wb = b ∧
      GoodWire W wv ∧ den W wv = (fun r => evalOp op (a r) (b r)) ∧ wv ∉ ws ∧
      (¬ S' a ∧ ¬ S' b → Rep W (wv :: dropTwo wa wb ws) S') ∧
      (¬ S' a ∧ S' b → Rep W (wv :: dropOne wa ws) S') ∧
      (S' a ∧ ¬ S' b → Rep W (wv :: dropOne wb ws) S') ∧
      (S' a ∧ S' b → Rep W (wv :: ws) S') := by
  obtain ⟨wa, hwa, rfl⟩ := (hr.2.2 a).mp ha
  obtain ⟨wb, hwb, rfl⟩ := (hr.2.2 b).mp hb
  have hwab : wa ≠ wb := fun e => hab (congrArg (den W) e)
  have hga := hr.2.1 wa hwa; have hgb := hr.2.1 wb hwb
  obtain ⟨wv, hgwv, hdwv⟩ : ∃ wv, GoodWire W wv ∧ den W wv = fun r => evalOp op (den W wa r) (den W wb r) := by
    cases op
    · exact ⟨_, good_op0 hga hgb⟩
    · exact ⟨_, good_op1 hga hgb⟩
    · exact ⟨_, good_op2 hga hgb⟩
    · exact ⟨_, good_op3 hga hgb⟩
  have hnwv : wv ∉ ws := fun hm => hnsv ((hr.2.2 _).mpr ⟨wv, hm, hdwv⟩)
  refine ⟨wa, wb, wv, hwa, hwb, hwab, rfl, rfl, hgwv, hdwv, hnwv, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hna, hnb⟩
    obtain ⟨hnd2, hmem2, _⟩ := dropTwo_spec hr.1 hr.2.1 hwa hwb hwab
    refine ⟨List.nodup_cons.mpr ⟨fun h => hnwv ((hmem2 wv).mp h).1, hnd2⟩, ?_, ?_⟩
    · intro w hw; rcases List.mem_cons.mp hw with rfl | hw
      · exact hgwv
      · exact hr.2.1 w ((hmem2 w).mp hw).1
    · intro f; constructor
      · intro hf
        rcases hsub f hf with rfl | hfS
        · exact ⟨wv, List.mem_cons_self, hdwv⟩
        · obtain ⟨w, hw, rfl⟩ := (hr.2.2 f).mp hfS
          refine ⟨w, List.mem_cons_of_mem _ ((hmem2 w).mpr ⟨hw, ?_, ?_⟩), rfl⟩
          · intro e; subst e; exact hna hf
          · intro e; subst e; exact hnb hf
      · rintro ⟨w, hw, rfl⟩
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hdwv ▸ hsv
        · obtain ⟨hws, hne1, hne2⟩ := (hmem2 w).mp hw
          rcases hcov _ ((hr.2.2 _).mpr ⟨w, hws, rfl⟩) with heq | heq | ⟨hS', _⟩
          · exact (hne1 (den_inj (hr.2.1 w hws) hga heq)).elim
          · exact (hne2 (den_inj (hr.2.1 w hws) hgb heq)).elim
          · exact hS'
  · rintro ⟨hna, hsb⟩
    obtain ⟨hnd1, hmem1, _⟩ := dropOne_spec hr.1 hr.2.1 hwa
    refine ⟨List.nodup_cons.mpr ⟨fun h => hnwv ((hmem1 wv).mp h).1, hnd1⟩, ?_, ?_⟩
    · intro w hw; rcases List.mem_cons.mp hw with rfl | hw
      · exact hgwv
      · exact hr.2.1 w ((hmem1 w).mp hw).1
    · intro f; constructor
      · intro hf
        rcases hsub f hf with rfl | hfS
        · exact ⟨wv, List.mem_cons_self, hdwv⟩
        · obtain ⟨w, hw, rfl⟩ := (hr.2.2 f).mp hfS
          refine ⟨w, List.mem_cons_of_mem _ ((hmem1 w).mpr ⟨hw, ?_⟩), rfl⟩
          intro e; subst e; exact hna hf
      · rintro ⟨w, hw, rfl⟩
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hdwv ▸ hsv
        · obtain ⟨hws, hne1⟩ := (hmem1 w).mp hw
          rcases hcov _ ((hr.2.2 _).mpr ⟨w, hws, rfl⟩) with heq | heq | ⟨hS', _⟩
          · exact (hne1 (den_inj (hr.2.1 w hws) hga heq)).elim
          · exact heq ▸ hsb
          · exact hS'
  · rintro ⟨hsa, hnb⟩
    obtain ⟨hnd1, hmem1, _⟩ := dropOne_spec hr.1 hr.2.1 hwb
    refine ⟨List.nodup_cons.mpr ⟨fun h => hnwv ((hmem1 wv).mp h).1, hnd1⟩, ?_, ?_⟩
    · intro w hw; rcases List.mem_cons.mp hw with rfl | hw
      · exact hgwv
      · exact hr.2.1 w ((hmem1 w).mp hw).1
    · intro f; constructor
      · intro hf
        rcases hsub f hf with rfl | hfS
        · exact ⟨wv, List.mem_cons_self, hdwv⟩
        · obtain ⟨w, hw, rfl⟩ := (hr.2.2 f).mp hfS
          refine ⟨w, List.mem_cons_of_mem _ ((hmem1 w).mpr ⟨hw, ?_⟩), rfl⟩
          intro e; subst e; exact hnb hf
      · rintro ⟨w, hw, rfl⟩
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hdwv ▸ hsv
        · obtain ⟨hws, hne2⟩ := (hmem1 w).mp hw
          rcases hcov _ ((hr.2.2 _).mpr ⟨w, hws, rfl⟩) with heq | heq | ⟨hS', _⟩
          · exact heq ▸ hsa
          · exact (hne2 (den_inj (hr.2.1 w hws) hgb heq)).elim
          · exact hS'
  · rintro ⟨hsa, hsb⟩
    refine ⟨List.nodup_cons.mpr ⟨hnwv, hr.1⟩, ?_, ?_⟩
    · intro w hw; rcases List.mem_cons.mp hw with rfl | hw
      · exact hgwv
      · exact hr.2.1 w hw
    · intro f; constructor
      · intro hf
        rcases hsub f hf with rfl | hfS
        · exact ⟨wv, List.mem_cons_self, hdwv⟩
        · obtain ⟨w, hw, rfl⟩ := (hr.2.2 f).mp hfS
          exact ⟨w, List.mem_cons_of_mem _ hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hdwv ▸ hsv
        · rcases hcov _ ((hr.2.2 _).mpr ⟨w, hw, rfl⟩) with heq | heq | ⟨hS', _⟩
          · exact heq ▸ hsa
          · exact heq ▸ hsb
          · exact hS'

theorem LiveSafe.card_le {W k : Nat} {forbid : (Bool × Fin W → Bool) → Prop}
    {S : (Bool × Fin W → Bool) → Prop} (hl : LiveSafe (targetDen W) forbid k S) :
    ∀ ws, Rep W ws S → ws.length ≤ k + 1 := by
  classical
  induction hl with
  | stop =>
    intro ws hr
    cases ws with
    | nil => simp
    | cons a rest =>
      cases rest with
      | nil => simp
      | cons b rest' =>
        exfalso
        have ha : den W a = targetDen W := (hr.2.2 (den W a)).mpr ⟨a, List.mem_cons_self, rfl⟩
        have hb : den W b = targetDen W := (hr.2.2 (den W b)).mpr ⟨b, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
        have hab := den_inj (hr.2.1 a List.mem_cons_self) (hr.2.1 b (List.mem_cons_of_mem _ List.mem_cons_self)) (ha.trans hb.symm)
        exact (List.nodup_cons.mp hr.1).1 (hab ▸ List.mem_cons_self)
  | @step op k S' a b S ha hb hab hcond _ ih =>
    intro ws hr
    obtain ⟨wa, wb, wv, hwa, hwb, hwab, _, _, _, _, _, h00, h01, h10, h11⟩ :=
      step_wire_rep hr ha hb hab hcond.2.2.1 hcond.2.2.2.1 hcond.2.2.2.2.1 hcond.2.2.2.2.2
    by_cases hsa : S' a <;> by_cases hsb : S' b
    · have := ih _ (h11 ⟨hsa, hsb⟩); simp at this; omega
    · have := ih _ (h10 ⟨hsa, hsb⟩)
      have hl1 := (dropOne_spec hr.1 hr.2.1 hwb).2.2
      simp at this; omega
    · have := ih _ (h01 ⟨hsa, hsb⟩)
      have hl1 := (dropOne_spec hr.1 hr.2.1 hwa).2.2
      simp at this; omega
    · have := ih _ (h00 ⟨hsa, hsb⟩)
      have hl2 := (dropTwo_spec hr.1 hr.2.1 hwa hwb hwab).2.2
      simp at this; omega

-- Read-once Unate theorem (10 lines!):
theorem unate_bool_step (op : Op) : ∀ (at1 af1 at2 af2 b1 b2 : Bool),
    at1 ≠ af1 → at2 ≠ af2 →
    evalOp op at1 b1 ≠ evalOp op af1 b1 →
    evalOp op at2 b2 ≠ evalOp op af2 b2 →
    evalOp op at1 b1 = evalOp op at2 b2 →
    at1 = at2 := by cases op <;> decide

theorem unate_bool_step_right (op : Op) : ∀ (bt1 bf1 bt2 bf2 a1 a2 : Bool),
    bt1 ≠ bf1 → bt2 ≠ bf2 →
    evalOp op a1 bt1 ≠ evalOp op a1 bf1 →
    evalOp op a2 bt2 ≠ evalOp op a2 bf2 →
    evalOp op a1 bt1 = evalOp op a2 bt2 →
    bt1 = bt2 := by cases op <;> decide

theorem LiveSafe.unate_tight {W k : Nat} {forbid : (Bool × Fin W → Bool) → Prop}
    {S : (Bool × Fin W → Bool) → Prop} (hl : LiveSafe (targetDen W) forbid k S) :
    ∀ ws, Rep W ws S → ws.length = k + 1 →
    ∀ w ∈ ws, ∀ i j : Fin W,
      (w.s &&& ((mults ws).1 - (mults ws).2)).testBit i.val = true →
      (w.s &&& ((mults ws).1 - (mults ws).2)).testBit j.val = true →
      w.t.testBit i.val = w.t.testBit j.val := by
  classical
  induction hl with
  | stop =>
    intro ws hr hlen w hw i j _ _
    have hwt : den W w = targetDen W := (hr.2.2 _).mpr ⟨w, hw, rfl⟩
    have h1 : w.t.testBit i.val = true := congrFun hwt (true, i)
    have h2 : w.t.testBit j.val = true := congrFun hwt (true, j)
    rw [h1, h2]
  | @step op k S' a b S ha hb hab hcond hl' ih =>
    intro ws hr hlen w hw i j hi hj
    obtain ⟨wa, wb, wv, hwa, hwb, hwab, rfl, rfl, hgwv, hdwv, hnwv, h00, h01, h10, h11⟩ :=
      step_wire_rep hr ha hb hab hcond.2.2.1 hcond.2.2.2.1 hcond.2.2.2.2.1 hcond.2.2.2.2.2
    have hna : ¬ S' (den W wa) := by
      intro hsa
      by_cases hsb : S' (den W wb)
      · have := hl'.card_le _ (h11 ⟨hsa, hsb⟩); simp at this; omega
      · have := hl'.card_le _ (h10 ⟨hsa, hsb⟩)
        have hl1 := (dropOne_spec hr.1 hr.2.1 hwb).2.2; simp at this; omega
    have hnb : ¬ S' (den W wb) := by
      intro hsb
      have := hl'.card_le _ (h01 ⟨hna, hsb⟩)
      have hl1 := (dropOne_spec hr.1 hr.2.1 hwa).2.2; simp at this; omega
    have hr' := h00 ⟨hna, hnb⟩
    obtain ⟨hnd2, hmem2, hlen2⟩ := dropTwo_spec hr.1 hr.2.1 hwa hwb hwab
    have hlen' : (wv :: dropTwo wa wb ws).length = k + 1 := by simp; omega
    have hcov' := coverSep_eq_all_of_live hl' hr'
    obtain ⟨hi1, hi_other⟩ := (priv_testBit_iff hr.1 hw i.val).mp hi
    obtain ⟨hj1, hj_other⟩ := (priv_testBit_iff hr.1 hw j.val).mp hj
    have hgw := hr.2.1 w hw
    by_cases hwa' : w = wa
    · subst hwa'
      have hbi : wb.s.testBit i.val = false := hi_other wb hwb (Ne.symm hwab)
      have hbj : wb.s.testBit j.val = false := hj_other wb hwb (Ne.symm hwab)
      have hvi : wv.s.testBit i.val = true := by
        have hci : (coverSep (wv :: dropTwo w wb ws)).testBit i.val = true := by
          rw [hcov']; exact testBit_all_mask W i.val i.isLt
        obtain ⟨u, hu, hus⟩ := (coverSep_testBit _ _).mp hci
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hus
        · obtain ⟨huw, hne1, _⟩ := (hmem2 u).mp hu
          rw [hi_other u huw hne1] at hus; cases hus
      have hvj : wv.s.testBit j.val = true := by
        have hcj : (coverSep (wv :: dropTwo w wb ws)).testBit j.val = true := by
          rw [hcov']; exact testBit_all_mask W j.val j.isLt
        obtain ⟨u, hu, hus⟩ := (coverSep_testBit _ _).mp hcj
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hus
        · obtain ⟨huw, hne1, _⟩ := (hmem2 u).mp hu
          rw [hj_other u huw hne1] at hus; cases hus
      have hvpi : (wv.s &&& ((mults (wv :: dropTwo w wb ws)).1 - (mults (wv :: dropTwo w wb ws)).2)).testBit i.val = true := by
        apply (priv_testBit_iff hr'.1 List.mem_cons_self i.val).mpr
        refine ⟨hvi, fun u hu hne => ?_⟩
        rcases List.mem_cons.mp hu with rfl | hu
        · exact (hne rfl).elim
        · exact hi_other u ((hmem2 u).mp hu).1 ((hmem2 u).mp hu).2.1
      have hvpj : (wv.s &&& ((mults (wv :: dropTwo w wb ws)).1 - (mults (wv :: dropTwo w wb ws)).2)).testBit j.val = true := by
        apply (priv_testBit_iff hr'.1 List.mem_cons_self j.val).mpr
        refine ⟨hvj, fun u hu hne => ?_⟩
        rcases List.mem_cons.mp hu with rfl | hu
        · exact (hne rfl).elim
        · exact hj_other u ((hmem2 u).mp hu).1 ((hmem2 u).mp hu).2.1
      have hv_eq := ih _ hr' hlen' wv List.mem_cons_self i j hvpi hvpj
      have hbi_eq : wb.t.testBit i.val = wb.f.testBit i.val := by
        have := wire_sep_testBit (hr.2.1 wb hwb) i; rw [hbi] at this; simpa [den] using this.symm
      have hbj_eq : wb.t.testBit j.val = wb.f.testBit j.val := by
        have := wire_sep_testBit (hr.2.1 wb hwb) j; rw [hbj] at this; simpa [den] using this.symm
      have hai_ne : w.t.testBit i.val ≠ w.f.testBit i.val := by
        have := wire_sep_testBit hgw i; rw [hi1] at this; simpa [den] using this.symm
      have haj_ne : w.t.testBit j.val ≠ w.f.testBit j.val := by
        have := wire_sep_testBit hgw j; rw [hj1] at this; simpa [den] using this.symm
      have hvt_i : wv.t.testBit i.val = evalOp op (w.t.testBit i.val) (wb.t.testBit i.val) := by
        simpa [den] using congrFun hdwv (true, i)
      have hvf_i : wv.f.testBit i.val = evalOp op (w.f.testBit i.val) (wb.t.testBit i.val) := by
        have := congrFun hdwv (false, i); simpa [den, hbi_eq] using this
      have hvt_j : wv.t.testBit j.val = evalOp op (w.t.testBit j.val) (wb.t.testBit j.val) := by
        simpa [den] using congrFun hdwv (true, j)
      have hvf_j : wv.f.testBit j.val = evalOp op (w.f.testBit j.val) (wb.t.testBit j.val) := by
        have := congrFun hdwv (false, j); simpa [den, hbj_eq] using this
      have hvi_ne : evalOp op (w.t.testBit i.val) (wb.t.testBit i.val) ≠ evalOp op (w.f.testBit i.val) (wb.t.testBit i.val) := by
        rw [← hvt_i, ← hvf_i]; have := wire_sep_testBit hgwv i; rw [hvi] at this; simpa [den] using this.symm
      have hvj_ne : evalOp op (w.t.testBit j.val) (wb.t.testBit j.val) ≠ evalOp op (w.f.testBit j.val) (wb.t.testBit j.val) := by
        rw [← hvt_j, ← hvf_j]; have := wire_sep_testBit hgwv j; rw [hvj] at this; simpa [den] using this.symm
      exact unate_bool_step op _ _ _ _ _ _ hai_ne haj_ne hvi_ne hvj_ne (by rw [← hvt_i, ← hvt_j, hv_eq])
    · by_cases hwb' : w = wb
      · subst hwb'
        have hai : wa.s.testBit i.val = false := hi_other wa hwa hwab
        have haj : wa.s.testBit j.val = false := hj_other wa hwa hwab
        have hvi : wv.s.testBit i.val = true := by
          have hci : (coverSep (wv :: dropTwo wa w ws)).testBit i.val = true := by
            rw [hcov']; exact testBit_all_mask W i.val i.isLt
          obtain ⟨u, hu, hus⟩ := (coverSep_testBit _ _).mp hci
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hus
          · obtain ⟨huw, _, hne2⟩ := (hmem2 u).mp hu
            rw [hi_other u huw hne2] at hus; cases hus
        have hvj : wv.s.testBit j.val = true := by
          have hcj : (coverSep (wv :: dropTwo wa w ws)).testBit j.val = true := by
            rw [hcov']; exact testBit_all_mask W j.val j.isLt
          obtain ⟨u, hu, hus⟩ := (coverSep_testBit _ _).mp hcj
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hus
          · obtain ⟨huw, _, hne2⟩ := (hmem2 u).mp hu
            rw [hj_other u huw hne2] at hus; cases hus
        have hvpi : (wv.s &&& ((mults (wv :: dropTwo wa w ws)).1 - (mults (wv :: dropTwo wa w ws)).2)).testBit i.val = true := by
          apply (priv_testBit_iff hr'.1 List.mem_cons_self i.val).mpr
          refine ⟨hvi, fun u hu hne => ?_⟩
          rcases List.mem_cons.mp hu with rfl | hu
          · exact (hne rfl).elim
          · exact hi_other u ((hmem2 u).mp hu).1 ((hmem2 u).mp hu).2.2
        have hvpj : (wv.s &&& ((mults (wv :: dropTwo wa w ws)).1 - (mults (wv :: dropTwo wa w ws)).2)).testBit j.val = true := by
          apply (priv_testBit_iff hr'.1 List.mem_cons_self j.val).mpr
          refine ⟨hvj, fun u hu hne => ?_⟩
          rcases List.mem_cons.mp hu with rfl | hu
          · exact (hne rfl).elim
          · exact hj_other u ((hmem2 u).mp hu).1 ((hmem2 u).mp hu).2.2
        have hv_eq := ih _ hr' hlen' wv List.mem_cons_self i j hvpi hvpj
        have hai_eq : wa.t.testBit i.val = wa.f.testBit i.val := by
          have := wire_sep_testBit (hr.2.1 wa hwa) i; rw [hai] at this; simpa [den] using this.symm
        have haj_eq : wa.t.testBit j.val = wa.f.testBit j.val := by
          have := wire_sep_testBit (hr.2.1 wa hwa) j; rw [haj] at this; simpa [den] using this.symm
        have hbi_ne : w.t.testBit i.val ≠ w.f.testBit i.val := by
          have := wire_sep_testBit hgw i; rw [hi1] at this; simpa [den] using this.symm
        have hbj_ne : w.t.testBit j.val ≠ w.f.testBit j.val := by
          have := wire_sep_testBit hgw j; rw [hj1] at this; simpa [den] using this.symm
        have hvt_i : wv.t.testBit i.val = evalOp op (wa.t.testBit i.val) (w.t.testBit i.val) := by
          simpa [den] using congrFun hdwv (true, i)
        have hvf_i : wv.f.testBit i.val = evalOp op (wa.t.testBit i.val) (w.f.testBit i.val) := by
          have := congrFun hdwv (false, i); simpa [den, hai_eq] using this
        have hvt_j : wv.t.testBit j.val = evalOp op (wa.t.testBit j.val) (w.t.testBit j.val) := by
          simpa [den] using congrFun hdwv (true, j)
        have hvf_j : wv.f.testBit j.val = evalOp op (wa.t.testBit j.val) (w.f.testBit j.val) := by
          have := congrFun hdwv (false, j); simpa [den, haj_eq] using this
        have hvi_ne : evalOp op (wa.t.testBit i.val) (w.t.testBit i.val) ≠ evalOp op (wa.t.testBit i.val) (w.f.testBit i.val) := by
          rw [← hvt_i, ← hvf_i]; have := wire_sep_testBit hgwv i; rw [hvi] at this; simpa [den] using this.symm
        have hvj_ne : evalOp op (wa.t.testBit j.val) (w.t.testBit j.val) ≠ evalOp op (wa.t.testBit j.val) (w.f.testBit j.val) := by
          rw [← hvt_j, ← hvf_j]; have := wire_sep_testBit hgwv j; rw [hvj] at this; simpa [den] using this.symm
        exact unate_bool_step_right op _ _ _ _ _ _ hbi_ne hbj_ne hvi_ne hvj_ne (by rw [← hvt_i, ← hvt_j, hv_eq])
      · have hwin : w ∈ wv :: dropTwo wa wb ws :=
          List.mem_cons_of_mem _ ((hmem2 w).mpr ⟨hw, hwa', hwb'⟩)
        have hvi_f : wv.s.testBit i.val = false := by
          have ha_eq : wa.t.testBit i.val = wa.f.testBit i.val := by
            have := wire_sep_testBit (hr.2.1 wa hwa) i; rw [hi_other wa hwa (Ne.symm hwa')] at this; simpa [den] using this.symm
          have hb_eq : wb.t.testBit i.val = wb.f.testBit i.val := by
            have := wire_sep_testBit (hr.2.1 wb hwb) i; rw [hi_other wb hwb (Ne.symm hwb')] at this; simpa [den] using this.symm
          rw [wire_sep_testBit hgwv i, hdwv]; simp [den, ha_eq, hb_eq]
        have hvj_f : wv.s.testBit j.val = false := by
          have ha_eq : wa.t.testBit j.val = wa.f.testBit j.val := by
            have := wire_sep_testBit (hr.2.1 wa hwa) j; rw [hj_other wa hwa (Ne.symm hwa')] at this; simpa [den] using this.symm
          have hb_eq : wb.t.testBit j.val = wb.f.testBit j.val := by
            have := wire_sep_testBit (hr.2.1 wb hwb) j; rw [hj_other wb hwb (Ne.symm hwb')] at this; simpa [den] using this.symm
          rw [wire_sep_testBit hgwv j, hdwv]; simp [den, ha_eq, hb_eq]
        have hwpi : (w.s &&& ((mults (wv :: dropTwo wa wb ws)).1 - (mults (wv :: dropTwo wa wb ws)).2)).testBit i.val = true := by
          apply (priv_testBit_iff hr'.1 hwin i.val).mpr
          refine ⟨hi1, fun u hu hne => ?_⟩
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hvi_f
          · exact hi_other u ((hmem2 u).mp hu).1 hne
        have hwpj : (w.s &&& ((mults (wv :: dropTwo wa wb ws)).1 - (mults (wv :: dropTwo wa wb ws)).2)).testBit j.val = true := by
          apply (priv_testBit_iff hr'.1 hwin j.val).mpr
          refine ⟨hj1, fun u hu hne => ?_⟩
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hvj_f
          · exact hj_other u ((hmem2 u).mp hu).1 hne
        exact ih _ hr' hlen' w hwin i j hwpi hwpj

theorem unateOk_of_tight {W k : Nat} {forbid : (Bool × Fin W → Bool) → Prop}
    {S : (Bool × Fin W → Bool) → Prop} {ws : List Wire}
    (hl : LiveSafe (targetDen W) forbid k S) (hr : Rep W ws S) (hlen : ws.length = k + 1) :
    unateOk (ws.map fun w => (w, w.s &&& ((mults ws).1 - (mults ws).2))) = true := by
  have hall : ∀ l : List Wire, (∀ w ∈ l, w ∈ ws) →
      unateOk (l.map fun w => (w, w.s &&& ((mults ws).1 - (mults ws).2))) = true := by
    intro l hlsub
    induction l with
    | nil => rfl
    | cons w rest ih =>
      simp only [List.map_cons, unateOk]
      have hw : w ∈ ws := hlsub w List.mem_cons_self
      have hrest := ih (fun u hu => hlsub u (List.mem_cons_of_mem _ hu))
      set p := w.s &&& ((mults ws).1 - (mults ws).2)
      by_cases hp0 : p == 0
      · simp [hp0, hrest]
      · simp only [hp0, Bool.false_eq_true, ↓reduceIte, hrest, Bool.and_true, Bool.or_eq_true, beq_iff_eq]
        have hp_ne : p ≠ 0 := fun e => hp0 (beq_iff_eq.mpr e)
        have hex : ∃ i0 : Nat, p.testBit i0 = true := by
          by_contra hno
          apply hp_ne; apply Nat.eq_of_testBit_eq; intro i
          cases hpi : p.testBit i
          · simp
          · exact (hno ⟨i, hpi⟩).elim
        obtain ⟨i0, hi0⟩ := hex
        have hi0_lt : i0 < W := by
          by_contra hge
          have : p.testBit i0 = false := by
            simp [p, Nat.testBit_and, wire_sep_ge_false (hr.2.1 w hw) i0 (Nat.not_lt.mp hge)]
          rw [this] at hi0; cases hi0
        cases ht0 : w.t.testBit i0
        · left
          apply Nat.eq_of_testBit_eq; intro i
          simp only [Nat.testBit_and, Nat.zero_testBit]
          cases hpi : p.testBit i
          · simp
          · have hilt : i < W := by
              by_contra hge
              have : p.testBit i = false := by
                simp [p, Nat.testBit_and, wire_sep_ge_false (hr.2.1 w hw) i (Nat.not_lt.mp hge)]
              rw [this] at hpi; cases hpi
            have heq := hl.unate_tight ws hr hlen w hw ⟨i, hilt⟩ ⟨i0, hi0_lt⟩ hpi hi0
            simp [heq, ht0]
        · right
          apply Nat.eq_of_testBit_eq; intro i
          simp only [Nat.testBit_and]
          cases hpi : p.testBit i
          · simp
          · have hilt : i < W := by
              by_contra hge
              have : p.testBit i = false := by
                simp [p, Nat.testBit_and, wire_sep_ge_false (hr.2.1 w hw) i (Nat.not_lt.mp hge)]
              rw [this] at hpi; cases hpi
            have heq := hl.unate_tight ws hr hlen w hw ⟨i, hilt⟩ ⟨i0, hi0_lt⟩ hpi hi0
            simp [heq, ht0]
  exact hall ws (fun _ h => h)

-- Private-drop necessary conditions: when wire `a` is dropped and replaced by `op a b`,
-- `b` MUST be constant (0 or 1) on `priv a`!
theorem drop_left_cond {W k : Nat} {forbid : (Bool × Fin W → Bool) → Prop}
    {S S' : (Bool × Fin W → Bool) → Prop} {ws : List Wire}
    {wa wb wv : Wire} {op : Op}
    (hr : Rep W ws S) (hl' : LiveSafe (targetDen W) forbid k S')
    (hwa : wa ∈ ws) (hwb : wb ∈ ws) (hwab : wa ≠ wb) (_hgwv : GoodWire W wv)
    (hdwv : den W wv = fun r => evalOp op (den W wa r) (den W wb r))
    (hdrop : ∀ f, S' f → f = den W wv ∨ (∃ w ∈ ws, w ≠ wa ∧ den W w = f)) :
    let p := wa.s &&& ((mults ws).1 - (mults ws).2)
    let ab := if p == 0 then 0 else p &&& wb.t
    match op with
    | .conj => ab == p
    | .disj => ab == 0
    | .diffL => ab == 0
    | .diffR => ab == p := by
  intro p ab
  have hbit : ∀ i : Nat, p.testBit i = true →
      wb.t.testBit i = match op with | .conj => true | .disj => false | .diffL => false | .diffR => true := by
    intro i hpi
    have hilt : i < W := by
      by_contra hge
      have : p.testBit i = false := by
        simp [p, Nat.testBit_and, wire_sep_ge_false (hr.2.1 wa hwa) i (Nat.not_lt.mp hge)]
      rw [this] at hpi; cases hpi
    obtain ⟨ha1, hother⟩ := (priv_testBit_iff hr.1 hwa i).mp hpi
    have hb_eq : wb.t.testBit i = wb.f.testBit i := by
      have := wire_sep_testBit (hr.2.1 wb hwb) ⟨i, hilt⟩
      rw [hother wb hwb (Ne.symm hwab)] at this; simpa [den] using this.symm
    obtain ⟨f, hfS', hsep⟩ := hl'.separates (r := (true, ⟨i, hilt⟩)) (s := (false, ⟨i, hilt⟩)) (fun h => Bool.noConfusion h)
    have hvsep : den W wv (true, ⟨i, hilt⟩) ≠ den W wv (false, ⟨i, hilt⟩) := by
      rcases hdrop f hfS' with rfl | ⟨w, hw, hne, rfl⟩
      · exact hsep
      · exfalso
        have := wire_sep_testBit (hr.2.1 w hw) ⟨i, hilt⟩
        rw [hother w hw hne] at this
        exact hsep (by simpa [den] using this.symm)
    rw [hdwv] at hvsep
    simp only [den, hb_eq] at hvsep
    cases op <;> cases hbt : wb.f.testBit i <;> simp_all [evalOp]
  by_cases hp0 : p == 0
  · have hp0' : p = 0 := beq_iff_eq.mp hp0
    cases op <;> simp [ab, hp0']
  · cases op
    · simp only [ab, hp0, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_and]
      cases hpi : p.testBit i
      · simp
      · simp [hbit i hpi]
    · simp only [ab, hp0, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_and, Nat.zero_testBit]
      cases hpi : p.testBit i
      · simp
      · simp [hbit i hpi]
    · simp only [ab, hp0, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_and, Nat.zero_testBit]
      cases hpi : p.testBit i
      · simp
      · simp [hbit i hpi]
    · simp only [ab, hp0, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_and]
      cases hpi : p.testBit i
      · simp
      · simp [hbit i hpi]

theorem drop_right_cond {W k : Nat} {forbid : (Bool × Fin W → Bool) → Prop}
    {S S' : (Bool × Fin W → Bool) → Prop} {ws : List Wire}
    {wa wb wv : Wire} {op : Op}
    (hr : Rep W ws S) (hl' : LiveSafe (targetDen W) forbid k S')
    (hwa : wa ∈ ws) (hwb : wb ∈ ws) (hwab : wa ≠ wb) (hgwv : GoodWire W wv)
    (hdwv : den W wv = fun r => evalOp op (den W wa r) (den W wb r))
    (hdrop : ∀ f, S' f → f = den W wv ∨ (∃ w ∈ ws, w ≠ wb ∧ den W w = f)) :
    let p := wb.s &&& ((mults ws).1 - (mults ws).2)
    let ba := if p == 0 then 0 else p &&& wa.t
    match op with
    | .conj => ba == p
    | .disj => ba == 0
    | .diffL => ba == p
    | .diffR => ba == 0 := by
  have hsw : den W wv = fun r => evalOp (match op with | .conj => .conj | .disj => .disj | .diffL => .diffR | .diffR => .diffL) (den W wb r) (den W wa r) := by
    rw [hdwv]; funext r; cases op <;> cases den W wa r <;> cases den W wb r <;> rfl
  have h := drop_left_cond hr hl' hwb hwa (Ne.symm hwab) hgwv hsw hdrop
  cases op <;> exact h

theorem searchD2_complete {W bound : Nat} {forbid : (Bool × Fin W → Bool) → Prop}
    (hfb : ∀ w : Wire, GoodWire W w → bound ≠ 0 → rankBST.lookup w.t w.f < bound → forbid (den W w)) :
    ∀ {k : Nat} {S : (Bool × Fin W → Bool) → Prop} {ws : List Wire},
    LiveSafe (targetDen W) forbid k S → Rep W ws S → ws.length = k + 1 →
    searchD2 (2 ^ W - 1) bound k ws = true := by
  classical
  intro k S ws hl
  induction hl generalizing ws with
  | stop =>
    intro hr hlen
    rcases ws with _ | ⟨a, _ | _⟩ <;> simp at hlen
    have ha : den W a = targetDen W := (hr.2.2 _).mpr ⟨a, List.mem_cons_self, rfl⟩
    exact (isTgtTF_iff (hr.2.1 a List.mem_cons_self)).mpr ha
  | @step op k S' a b S ha hb hab hcond hl' ih =>
    intro hr hlen
    obtain ⟨wa, wb, wv, hwa, hwb, hwab, rfl, rfl, hgwv, hdwv, hnwv, h00, h01, h10, h11⟩ :=
      step_wire_rep hr ha hb hab hcond.2.2.1 hcond.2.2.2.1 hcond.2.2.2.2.1 hcond.2.2.2.2.2
    have hna : ¬ S' (den W wa) := by
      intro hsa
      by_cases hsb : S' (den W wb)
      · have := hl'.card_le _ (h11 ⟨hsa, hsb⟩); simp at this; omega
      · have := hl'.card_le _ (h10 ⟨hsa, hsb⟩); have := (dropOne_spec hr.1 hr.2.1 hwb).2.2; simp at *; omega
    have hnb : ¬ S' (den W wb) := by
      intro hsb
      have := hl'.card_le _ (h01 ⟨hna, hsb⟩); have := (dropOne_spec hr.1 hr.2.1 hwa).2.2; simp at *; omega
    have hr' := h00 ⟨hna, hnb⟩
    have hlen2 := (dropTwo_spec hr.1 hr.2.1 hwa hwb hwab).2.2
    have hlen' : (wv :: dropTwo wa wb ws).length = k + 1 := by simp; omega
    have hih := ih hr' hlen'
    cases k with
    | zero =>
      have hws2 : ∃ x y : Wire, ws = [x, y] := by
        rcases ws with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
        · simp at hlen
        · simp at hlen
        · exact ⟨x, y, rfl⟩
        · simp at hlen
      obtain ⟨x, y, rfl⟩ := hws2
      have htgt : den W wv = targetDen W := by
        cases hl'
        have := hcond.2.2.2.1
        simpa [hdwv] using this
      have hxy : (wa = x ∧ wb = y) ∨ (wa = y ∧ wb = x) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwa hwb
        rcases hwa with rfl | rfl <;> rcases hwb with rfl | rfl
        · exact (hwab rfl).elim
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact (hwab rfl).elim
      have hgxy : GoodWire W x ∧ GoodWire W y := ⟨hr.2.1 x List.mem_cons_self, hr.2.1 y (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      change searchD2 (2 ^ W - 1) bound 1 [x, y] = true
      simp only [searchD2]
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · cases op
        · have hok : isTgtTF (2 ^ W - 1) (op0 wa wb).1 (op0 wa wb).2 = true :=
            (isTgtTF_iff (good_op0 hgxy.1 hgxy.2).1).mpr ((good_op0 hgxy.1 hgxy.2).2.trans (hdwv ▸ htgt))
          simp only [hok, Bool.true_or]
        · have hok : isTgtTF (2 ^ W - 1) (op1 wa wb).1 (op1 wa wb).2 = true :=
            (isTgtTF_iff (good_op1 hgxy.1 hgxy.2).1).mpr ((good_op1 hgxy.1 hgxy.2).2.trans (hdwv ▸ htgt))
          simp only [hok, Bool.or_true, Bool.true_or]
        · have hok : isTgtTF (2 ^ W - 1) (op2 (2 ^ W - 1) wa wb).1 (op2 (2 ^ W - 1) wa wb).2 = true :=
            (isTgtTF_iff (good_op2 hgxy.1 hgxy.2).1).mpr ((good_op2 hgxy.1 hgxy.2).2.trans (hdwv ▸ htgt))
          simp only [hok, Bool.or_true, Bool.true_or]
        · have hok : isTgtTF (2 ^ W - 1) (op3 (2 ^ W - 1) wa wb).1 (op3 (2 ^ W - 1) wa wb).2 = true :=
            (isTgtTF_iff (good_op3 hgxy.1 hgxy.2).1).mpr ((good_op3 hgxy.1 hgxy.2).2.trans (hdwv ▸ htgt))
          simp only [hok, Bool.or_true]
      · cases op
        · have heq : den W ⟨(op0 wb wa).1, (op0 wb wa).2, (op0 wb wa).1 ^^^ (op0 wb wa).2⟩ = targetDen W := by
            rw [(good_op0 hgxy.1 hgxy.2).2, ← htgt, hdwv]; funext r; simp [evalOp, Bool.and_comm]
          have hok : isTgtTF (2 ^ W - 1) (op0 wb wa).1 (op0 wb wa).2 = true := (isTgtTF_iff (good_op0 hgxy.1 hgxy.2).1).mpr heq
          simp only [hok, Bool.true_or]
        · have heq : den W ⟨(op1 wb wa).1, (op1 wb wa).2, (op1 wb wa).1 ^^^ (op1 wb wa).2⟩ = targetDen W := by
            rw [(good_op1 hgxy.1 hgxy.2).2, ← htgt, hdwv]; funext r; simp [evalOp, Bool.or_comm]
          have hok : isTgtTF (2 ^ W - 1) (op1 wb wa).1 (op1 wb wa).2 = true := (isTgtTF_iff (good_op1 hgxy.1 hgxy.2).1).mpr heq
          simp only [hok, Bool.or_true, Bool.true_or]
        · have heq : den W ⟨(op3 (2 ^ W - 1) wb wa).1, (op3 (2 ^ W - 1) wb wa).2, (op3 (2 ^ W - 1) wb wa).1 ^^^ (op3 (2 ^ W - 1) wb wa).2⟩ = targetDen W := by
            rw [(good_op3 hgxy.1 hgxy.2).2, ← htgt, hdwv]; funext r; simp [evalOp, Bool.and_comm]
          have hok : isTgtTF (2 ^ W - 1) (op3 (2 ^ W - 1) wb wa).1 (op3 (2 ^ W - 1) wb wa).2 = true := (isTgtTF_iff (good_op3 hgxy.1 hgxy.2).1).mpr heq
          simp only [hok, Bool.or_true]
        · have heq : den W ⟨(op2 (2 ^ W - 1) wb wa).1, (op2 (2 ^ W - 1) wb wa).2, (op2 (2 ^ W - 1) wb wa).1 ^^^ (op2 (2 ^ W - 1) wb wa).2⟩ = targetDen W := by
            rw [(good_op2 hgxy.1 hgxy.2).2, ← htgt, hdwv]; funext r; simp [evalOp, Bool.and_comm]
          have hok : isTgtTF (2 ^ W - 1) (op2 (2 ^ W - 1) wb wa).1 (op2 (2 ^ W - 1) wb wa).2 = true := (isTgtTF_iff (good_op2 hgxy.1 hgxy.2).1).mpr heq
          simp only [hok, Bool.or_true, Bool.true_or]
    | succ k' =>
      -- ws.length = k' + 3 >= 3, so ws cannot be [] or [x]
      have hlen_ge : ws.length ≥ 3 := by omega
      have hws_match : searchD2 (2 ^ W - 1) bound (k' + 2) ws =
          (let m := mults ws
           if m.1 != 2 ^ W - 1 then false
           else
             let once := m.1 - m.2
             let cols := ws.map fun w => (w, w.s &&& once)
             if !unateOk cols then false
             else
               pairsGo (fun a b =>
                 let ab := if a.2 == 0 then 0 else a.2 &&& b.1.t
                 let a0 := ab == 0
                 let a1 := ab == a.2
                 if !a0 && !a1 then false
                 else
                   let ba := if b.2 == 0 then 0 else b.2 &&& a.1.t
                   let b0 := ba == 0
                   let b1 := ba == b.2
                   if !b0 && !b1 then false
                   else
                     let tryOp (mk : Unit → Nat × Nat) : Bool :=
                       let tf := mk ()
                       let t := tf.1; let f := tf.2
                       if (t == 0 && f == 0) || hasTF t f ws || (bound != 0 && rankBST.lookup t f < bound) then false
                       else if isTgtTF (2 ^ W - 1) t f then true
                       else
                         let rest2 := dropTwo a.1 b.1 ws
                         let sv := t ^^^ f
                         if (coverSep rest2 ||| sv) == 2 ^ W - 1 then searchD2 (2 ^ W - 1) bound (k' + 1) (⟨t, f, sv⟩ :: rest2)
                         else false
                     (if a1 && b1 then tryOp (fun _ => op0 a.1 b.1) else false) ||
                     (if a0 && b0 then tryOp (fun _ => op1 a.1 b.1) else false) ||
                     (if a0 && b1 then tryOp (fun _ => op2 (2 ^ W - 1) a.1 b.1) else false) ||
                     (if a1 && b0 then tryOp (fun _ => op3 (2 ^ W - 1) a.1 b.1) else false)) cols) := by
        rcases ws with _ | ⟨_, _ | ⟨_, _⟩⟩
        · simp at hlen_ge
        · simp at hlen_ge
        · rfl
      rw [hws_match]
      have hm1 : (mults ws).1 = 2 ^ W - 1 := by
        rw [mults_fst_eq_cover]
        exact coverSep_eq_all_of_live (LiveSafe.step op _ _ S ha hb hab hcond hl') hr
      have hun := unateOk_of_tight (LiveSafe.step op _ _ S ha hb hab hcond hl') hr hlen
      simp only [hm1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      have hun' : unateOk (ws.map fun w => (w, w.s &&& (2 ^ W - 1 - (mults ws).2))) = true := by
        simpa [hm1] using hun
      simp only [hun', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      let once := 2 ^ W - 1 - (mults ws).2
      let ca : Wire × Nat := (wa, wa.s &&& once)
      let cb : Wire × Nat := (wb, wb.s &&& once)
      have hca : ca ∈ ws.map fun w => (w, w.s &&& once) := List.mem_map.mpr ⟨wa, hwa, rfl⟩
      have hcb : cb ∈ ws.map fun w => (w, w.s &&& once) := List.mem_map.mpr ⟨wb, hwb, rfl⟩
      have hcab : ca ≠ cb := fun e => hwab (congrArg Prod.fst e)
      have hdropA : ∀ f, S' f → f = den W wv ∨ (∃ w ∈ ws, w ≠ wa ∧ den W w = f) := by
        intro f hf
        rcases hcond.2.2.2.2.1 f hf with rfl | hfS
        · exact Or.inl hdwv.symm
        · obtain ⟨w, hw, rfl⟩ := (hr.2.2 f).mp hfS
          exact Or.inr ⟨w, hw, fun e => hna (e ▸ hf), rfl⟩
      have hdropB : ∀ f, S' f → f = den W wv ∨ (∃ w ∈ ws, w ≠ wb ∧ den W w = f) := by
        intro f hf
        rcases hcond.2.2.2.2.1 f hf with rfl | hfS
        · exact Or.inl hdwv.symm
        · obtain ⟨w, hw, rfl⟩ := (hr.2.2 f).mp hfS
          exact Or.inr ⟨w, hw, fun e => hnb (e ▸ hf), rfl⟩
      have hda := drop_left_cond hr hl' hwa hwb hwab hgwv hdwv hdropA
      have hdb := drop_right_cond hr hl' hwa hwb hwab hgwv hdwv hdropB
      have hnot0 : (wv.t == 0 && wv.f == 0) = false := by
        cases h : (wv.t == 0 && wv.f == 0)
        · rfl
        · exact (hcond.2.1 (hdwv ▸ (isZeroTF_iff hgwv).mp h)).elim
      have hnotdup : hasTF wv.t wv.f ws = false := by
        cases h : hasTF wv.t wv.f ws
        · rfl
        · exact (hnwv ((hasTF_iff hr.2.1 hgwv).mp h)).elim
      have hnotfb : (bound != 0 && decide (rankBST.lookup wv.t wv.f < bound)) = false := by
        cases h : (bound != 0 && decide (rankBST.lookup wv.t wv.f < bound))
        · rfl
        · simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
          exact (hcond.1 (hdwv ▸ hfb wv hgwv h.1 h.2)).elim
      have hcov2 : coverSep (dropTwo wa wb ws) ||| wv.s = 2 ^ W - 1 := by
        have := coverSep_eq_all_of_live hl' hr'
        simpa [coverSep, Nat.or_comm] using this
      have hdrop_symm : dropTwo wb wa ws = dropTwo wa wb ws := by
        -- prove by showing same elements? Wait: `dropOne wb (dropOne wa ws) = dropOne wa (dropOne wb ws)`!
        have hcomm : ∀ (l : List Wire), l.Nodup → (∀ w ∈ l, GoodWire W w) → wa ∈ l → wb ∈ l →
            dropOne wb (dropOne wa l) = dropOne wa (dropOne wb l) := by
          intro l hndl hgl h1 h2
          induction l with
          | nil => cases h1
          | cons u us ihu =>
            rw [List.nodup_cons] at hndl
            have hgu := hgl u List.mem_cons_self
            have hgus : ∀ z ∈ us, GoodWire W z := fun z hz => hgl z (List.mem_cons_of_mem _ hz)
            have hga := hgl wa h1; have hgb := hgl wb h2
            by_cases hua : u = wa
            · subst hua
              have hub : (u.t == wb.t && u.f == wb.f) = false := by
                cases hc : (u.t == wb.t && u.f == wb.f)
                · rfl
                · exfalso; simp only [Bool.and_eq_true, beq_iff_eq] at hc
                  apply hwab; cases u; cases wb; simp only [GoodWire] at hgu hgb; simp_all
              simp [dropOne, hub]
            · by_cases hub : u = wb
              · subst hub
                have hua' : (u.t == wa.t && u.f == wa.f) = false := by
                  cases hc : (u.t == wa.t && u.f == wa.f)
                  · rfl
                  · exfalso; simp only [Bool.and_eq_true, beq_iff_eq] at hc
                    apply hwab; cases u; cases wa; simp only [GoodWire] at hgu hga; simp_all
                simp [dropOne, hua']
              · have hua' : (u.t == wa.t && u.f == wa.f) = false := by
                  cases hc : (u.t == wa.t && u.f == wa.f)
                  · rfl
                  · exfalso; simp only [Bool.and_eq_true, beq_iff_eq] at hc
                    apply hua; cases u; cases wa; simp only [GoodWire] at hgu hga; simp_all
                have hub' : (u.t == wb.t && u.f == wb.f) = false := by
                  cases hc : (u.t == wb.t && u.f == wb.f)
                  · rfl
                  · exfalso; simp only [Bool.and_eq_true, beq_iff_eq] at hc
                    apply hub; cases u; cases wb; simp only [GoodWire] at hgu hgb; simp_all
                have h1' : wa ∈ us := (List.mem_cons.mp h1).resolve_left (Ne.symm hua)
                have h2' : wb ∈ us := (List.mem_cons.mp h2).resolve_left (Ne.symm hub)
                simp [dropOne, hua', hub', ihu hndl.2 hgus h1' h2']
        exact hcomm ws hr.1 hr.2.1 hwa hwb
      have htry_ok (tf : Nat × Nat) (htf : (⟨tf.1, tf.2, tf.1 ^^^ tf.2⟩ : Wire) = wv) (rest : List Wire) (hrest : rest = dropTwo wa wb ws) :
          (if (tf.1 == 0 && tf.2 == 0) || hasTF tf.1 tf.2 ws || (bound != 0 && decide (rankBST.lookup tf.1 tf.2 < bound)) then false
           else if isTgtTF (2 ^ W - 1) tf.1 tf.2 then true
           else
             if (coverSep rest ||| (tf.1 ^^^ tf.2)) == 2 ^ W - 1 then
               searchD2 (2 ^ W - 1) bound (k' + 1) (⟨tf.1, tf.2, tf.1 ^^^ tf.2⟩ :: rest)
             else false) = true := by
        have ht : tf.1 = wv.t := by rw [← htf]
        have hf : tf.2 = wv.f := by rw [← htf]
        have hs : tf.1 ^^^ tf.2 = wv.s := by rw [← htf]
        have hmk : (⟨tf.1, tf.2, tf.1 ^^^ tf.2⟩ : Wire) = wv := htf
        rw [hmk, hrest, hs, ht, hf, hnot0, hnotdup, hnotfb]
        simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte]
        by_cases htgt : isTgtTF (2 ^ W - 1) wv.t wv.f = true
        · simp [htgt]
        · simp only [htgt, ↓reduceIte, hcov2, beq_self_eq_true]
          exact hih
      apply pairsGo_of_mem hca hcb hcab
      · dsimp only [ca, cb, once] at hda hdb ⊢
        rw [hm1] at hda hdb
        cases op
        · have htf : (⟨(op0 wa wb).1, (op0 wa wb).2, (op0 wa wb).1 ^^^ (op0 wa wb).2⟩ : Wire) = wv :=
            den_inj (good_op0 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).1 hgwv ((good_op0 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).2.trans hdwv.symm)
          have hok := htry_ok (op0 wa wb) htf (dropTwo wa wb ws) rfl
          simp only [hda, hdb, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.and_self, hok, Bool.true_or]
        · have htf : (⟨(op1 wa wb).1, (op1 wa wb).2, (op1 wa wb).1 ^^^ (op1 wa wb).2⟩ : Wire) = wv :=
            den_inj (good_op1 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).1 hgwv ((good_op1 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).2.trans hdwv.symm)
          have hok := htry_ok (op1 wa wb) htf (dropTwo wa wb ws) rfl
          simp only [hda, hdb, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.and_self, hok, Bool.or_true, Bool.true_or]
        · have htf : (⟨(op2 (2 ^ W - 1) wa wb).1, (op2 (2 ^ W - 1) wa wb).2, (op2 (2 ^ W - 1) wa wb).1 ^^^ (op2 (2 ^ W - 1) wa wb).2⟩ : Wire) = wv :=
            den_inj (good_op2 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).1 hgwv ((good_op2 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).2.trans hdwv.symm)
          have hok := htry_ok (op2 (2 ^ W - 1) wa wb) htf (dropTwo wa wb ws) rfl
          simp only [hda, hdb, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.and_self, hok, Bool.or_true, Bool.true_or]
        · have htf : (⟨(op3 (2 ^ W - 1) wa wb).1, (op3 (2 ^ W - 1) wa wb).2, (op3 (2 ^ W - 1) wa wb).1 ^^^ (op3 (2 ^ W - 1) wa wb).2⟩ : Wire) = wv :=
            den_inj (good_op3 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).1 hgwv ((good_op3 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).2.trans hdwv.symm)
          have hok := htry_ok (op3 (2 ^ W - 1) wa wb) htf (dropTwo wa wb ws) rfl
          simp only [hda, hdb, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.and_self, hok, Bool.or_true]
      · dsimp only [ca, cb, once] at hda hdb ⊢
        rw [hm1] at hda hdb
        cases op
        · have htf : (⟨(op0 wb wa).1, (op0 wb wa).2, (op0 wb wa).1 ^^^ (op0 wb wa).2⟩ : Wire) = wv :=
            den_inj (good_op0 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).1 hgwv
              ((good_op0 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).2.trans (by rw [hdwv]; funext r; simp [evalOp, Bool.and_comm]))
          have hok := htry_ok (op0 wb wa) htf (dropTwo wb wa ws) hdrop_symm
          simp only [hda, hdb, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.and_self, hok, Bool.true_or]
        · have htf : (⟨(op1 wb wa).1, (op1 wb wa).2, (op1 wb wa).1 ^^^ (op1 wb wa).2⟩ : Wire) = wv :=
            den_inj (good_op1 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).1 hgwv
              ((good_op1 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).2.trans (by rw [hdwv]; funext r; simp [evalOp, Bool.or_comm]))
          have hok := htry_ok (op1 wb wa) htf (dropTwo wb wa ws) hdrop_symm
          simp only [hda, hdb, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.and_self, hok, Bool.or_true, Bool.true_or]
        · have htf : (⟨(op3 (2 ^ W - 1) wb wa).1, (op3 (2 ^ W - 1) wb wa).2, (op3 (2 ^ W - 1) wb wa).1 ^^^ (op3 (2 ^ W - 1) wb wa).2⟩ : Wire) = wv :=
            den_inj (good_op3 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).1 hgwv
              ((good_op3 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).2.trans (by rw [hdwv]; funext r; simp [evalOp, Bool.and_comm]))
          have hok := htry_ok (op3 (2 ^ W - 1) wb wa) htf (dropTwo wb wa ws) hdrop_symm
          simp only [hda, hdb, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.and_self, hok, Bool.or_true]
        · have htf : (⟨(op2 (2 ^ W - 1) wb wa).1, (op2 (2 ^ W - 1) wb wa).2, (op2 (2 ^ W - 1) wb wa).1 ^^^ (op2 (2 ^ W - 1) wb wa).2⟩ : Wire) = wv :=
            den_inj (good_op2 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).1 hgwv
              ((good_op2 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).2.trans (by rw [hdwv]; funext r; simp [evalOp, Bool.and_comm]))
          have hok := htry_ok (op2 (2 ^ W - 1) wb wa) htf (dropTwo wb wa ws) hdrop_symm
          simp only [hda, hdb, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.and_self, hok, Bool.or_true, Bool.true_or]

theorem search_complete {W bound : Nat} {forbid : (Bool × Fin W → Bool) → Prop}
    (hfb : ∀ w : Wire, GoodWire W w → bound ≠ 0 → rankBST.lookup w.t w.f < bound → forbid (den W w)) :
    ∀ {k_live k_cap : Nat} {S : (Bool × Fin W → Bool) → Prop} {ws : List Wire},
    k_live ≤ k_cap → LiveSafe (targetDen W) forbid k_live S → Rep W ws S →
    search (2 ^ W - 1) bound k_cap ws = true := by
  classical
  intro k_live k_cap S ws hk hl
  induction hl generalizing k_cap ws with
  | stop =>
    intro hr
    have hlen : ws.length ≤ 1 := @LiveSafe.card_le W 0 forbid _ LiveSafe.stop ws hr
    have hne : ws ≠ [] := by
      intro hnil; subst hnil
      obtain ⟨w, hw, _⟩ := (hr.2.2 (targetDen W)).mp rfl; cases hw
    rcases ws with _ | ⟨a, _ | _⟩
    · exact (hne rfl).elim
    · have ha : isTgtTF (2 ^ W - 1) a.t a.f = true :=
        (isTgtTF_iff (hr.2.1 a List.mem_cons_self)).mpr ((hr.2.2 _).mpr ⟨a, List.mem_cons_self, rfl⟩)
      cases k_cap with
      | zero => exact ha
      | succ c => cases c <;> exact ha
    · simp at hlen
  | @step op k S' a b S ha hb hab hcond hl' ih =>
    intro hr
    cases k_cap with
    | zero => omega
    | succ c =>
      have hkc : k ≤ c := by omega
      have hcard := (LiveSafe.step op a b S ha hb hab hcond hl').card_le ws hr
      by_cases htight : ws.length = c + 2
      · have hkeq : k = c := by omega
        subst hkeq
        have hd2 := searchD2_complete hfb (LiveSafe.step op a b S ha hb hab hcond hl') hr htight
        cases k with
        | zero =>
          rcases ws with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
          · simp at htight
          · simp at htight
          · exact hd2
          · simp at htight
        | succ c' =>
          have hge : ws.length ≥ 3 := by omega
          rcases ws with _ | ⟨x, _ | ⟨y, rest⟩⟩
          · simp at hge
          · simp at hge
          · have hng : ¬ ((x :: y :: rest).length > c' + 3) := by omega
            have heq3 : ((x :: y :: rest).length == c' + 3) = true := beq_iff_eq.mpr htight
            simp only [search, hng, ↓reduceIte, heq3]
            exact hd2
      · have hlen_le : ws.length ≤ c + 1 := by omega
        obtain ⟨wa, wb, wv, hwa, hwb, hwab, rfl, rfl, hgwv, hdwv, hnwv, h00, h01, h10, h11⟩ :=
          step_wire_rep hr ha hb hab hcond.2.2.1 hcond.2.2.2.1 hcond.2.2.2.2.1 hcond.2.2.2.2.2
        have hlen_ge2 : ws.length ≥ 2 := by
          rcases ws with _ | ⟨x, _ | _⟩
          · cases hwa
          · simp at hwa hwb; exact (hwab (hwa.trans hwb.symm)).elim
          · simp
        cases c with
        | zero => omega
        | succ c' =>
          have hws_unfold : search (2 ^ W - 1) bound (c' + 2) ws =
              (let n := ws.length
               if n > c' + 3 then false
               else if n == c' + 3 then searchD2 (2 ^ W - 1) bound (c' + 2) ws
               else
                 let m := mults ws
                 if m.1 != 2 ^ W - 1 then false
                 else
                   let once := m.1 - m.2
                   let cols := ws.map fun w => (w, w.s &&& once)
                   let allow0 := decide (n ≤ c' + 1)
                   pairsGo (fun a b =>
                     let ab := if a.2 == 0 then 0 else a.2 &&& b.1.t
                     let a0 := ab == 0
                     let a1 := ab == a.2
                     let ba := if b.2 == 0 then 0 else b.2 &&& a.1.t
                     let b0 := ba == 0
                     let b1 := ba == b.2
                     let tryOp (da db : Bool) (mk : Unit → Nat × Nat) : Bool :=
                       if !(allow0 || da || db) then false
                       else
                         let tf := mk ()
                         let t := tf.1; let f := tf.2
                         if (t == 0 && f == 0) || hasTF t f ws || (bound != 0 && rankBST.lookup t f < bound) then false
                         else if isTgtTF (2 ^ W - 1) t f then true
                         else
                           let v : Wire := ⟨t, f, t ^^^ f⟩
                           (if da && db then
                             let rest2 := dropTwo a.1 b.1 ws
                             if (coverSep rest2 ||| v.s) == 2 ^ W - 1 then search (2 ^ W - 1) bound (c' + 1) (v :: rest2) else false
                            else false) ||
                           (if da then search (2 ^ W - 1) bound (c' + 1) (v :: dropOne a.1 ws) else false) ||
                           (if db then search (2 ^ W - 1) bound (c' + 1) (v :: dropOne b.1 ws) else false) ||
                           (if allow0 then search (2 ^ W - 1) bound (c' + 1) (v :: ws) else false)
                     tryOp a1 b1 (fun _ => op0 a.1 b.1) ||
                     tryOp a0 b0 (fun _ => op1 a.1 b.1) ||
                     tryOp a0 b1 (fun _ => op2 (2 ^ W - 1) a.1 b.1) ||
                     tryOp a1 b0 (fun _ => op3 (2 ^ W - 1) a.1 b.1)) cols) := by
            rcases ws with _ | ⟨_, _ | _⟩
            · simp at hlen_ge2
            · simp at hlen_ge2
            · rfl
          rw [hws_unfold]
          have hng : ¬ (ws.length > c' + 3) := by omega
          have hne3 : (ws.length == c' + 3) = false := beq_false_of_ne (by omega)
          have hm1 : (mults ws).1 = 2 ^ W - 1 := by
            rw [mults_fst_eq_cover]
            exact coverSep_eq_all_of_live (LiveSafe.step op _ _ S ha hb hab hcond hl') hr
          simp only [hng, ↓reduceIte, hne3, Bool.false_eq_true, hm1, bne_self_eq_false]
          let once := 2 ^ W - 1 - (mults ws).2
          let ca : Wire × Nat := (wa, wa.s &&& once)
          let cb : Wire × Nat := (wb, wb.s &&& once)
          have hca : ca ∈ ws.map fun w => (w, w.s &&& once) := List.mem_map.mpr ⟨wa, hwa, rfl⟩
          have hcb : cb ∈ ws.map fun w => (w, w.s &&& once) := List.mem_map.mpr ⟨wb, hwb, rfl⟩
          have hcab : ca ≠ cb := fun e => hwab (congrArg Prod.fst e)
          have hnot0 : (wv.t == 0 && wv.f == 0) = false := by
            cases h : (wv.t == 0 && wv.f == 0)
            · rfl
            · exact (hcond.2.1 (hdwv ▸ (isZeroTF_iff hgwv).mp h)).elim
          have hnotdup : hasTF wv.t wv.f ws = false := by
            cases h : hasTF wv.t wv.f ws
            · rfl
            · exact (hnwv ((hasTF_iff hr.2.1 hgwv).mp h)).elim
          have hnotfb : (bound != 0 && decide (rankBST.lookup wv.t wv.f < bound)) = false := by
            cases h : (bound != 0 && decide (rankBST.lookup wv.t wv.f < bound))
            · rfl
            · simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
              exact (hcond.1 (hdwv ▸ hfb wv hgwv h.1 h.2)).elim
          have hdrop_symm : dropTwo wb wa ws = dropTwo wa wb ws := by
            have hcomm : ∀ (l : List Wire), l.Nodup → (∀ w ∈ l, GoodWire W w) → wa ∈ l → wb ∈ l →
                dropOne wb (dropOne wa l) = dropOne wa (dropOne wb l) := by
              intro l hndl hgl h1 h2
              induction l with
              | nil => cases h1
              | cons u us ihu =>
                rw [List.nodup_cons] at hndl
                have hgu := hgl u List.mem_cons_self
                have hgus : ∀ z ∈ us, GoodWire W z := fun z hz => hgl z (List.mem_cons_of_mem _ hz)
                have hga := hgl wa h1; have hgb := hgl wb h2
                by_cases hua : u = wa
                · subst hua
                  have hub : (u.t == wb.t && u.f == wb.f) = false := by
                    cases hc : (u.t == wb.t && u.f == wb.f)
                    · rfl
                    · exfalso; simp only [Bool.and_eq_true, beq_iff_eq] at hc
                      apply hwab; cases u; cases wb; simp only [GoodWire] at hgu hgb; simp_all
                  simp [dropOne, hub]
                · by_cases hub : u = wb
                  · subst hub
                    have hua' : (u.t == wa.t && u.f == wa.f) = false := by
                      cases hc : (u.t == wa.t && u.f == wa.f)
                      · rfl
                      · exfalso; simp only [Bool.and_eq_true, beq_iff_eq] at hc
                        apply hwab; cases u; cases wa; simp only [GoodWire] at hgu hga; simp_all
                    simp [dropOne, hua']
                  · have hua' : (u.t == wa.t && u.f == wa.f) = false := by
                      cases hc : (u.t == wa.t && u.f == wa.f)
                      · rfl
                      · exfalso; simp only [Bool.and_eq_true, beq_iff_eq] at hc
                        apply hua; cases u; cases wa; simp only [GoodWire] at hgu hga; simp_all
                    have hub' : (u.t == wb.t && u.f == wb.f) = false := by
                      cases hc : (u.t == wb.t && u.f == wb.f)
                      · rfl
                      · exfalso; simp only [Bool.and_eq_true, beq_iff_eq] at hc
                        apply hub; cases u; cases wb; simp only [GoodWire] at hgu hgb; simp_all
                    have h1' : wa ∈ us := (List.mem_cons.mp h1).resolve_left (Ne.symm hua)
                    have h2' : wb ∈ us := (List.mem_cons.mp h2).resolve_left (Ne.symm hub)
                    simp [dropOne, hua', hub', ihu hndl.2 hgus h1' h2']
            exact hcomm ws hr.1 hr.2.1 hwa hwb
          -- Core step checker for either `(wa, wb)` or `(wb, wa)`:
          have hbranch (da db : Bool) (tf : Nat × Nat) (htf : (⟨tf.1, tf.2, tf.1 ^^^ tf.2⟩ : Wire) = wv)
              (x y : Wire) (hxy_case : (x = wa ∧ y = wb ∧ (¬ S' (den W wa) → da = true) ∧ (¬ S' (den W wb) → db = true)) ∨
                                       (x = wb ∧ y = wa ∧ (¬ S' (den W wb) → da = true) ∧ (¬ S' (den W wa) → db = true))) :
              (let allow0 := decide (ws.length ≤ c' + 1)
               if !(allow0 || da || db) then false
               else
                 let t := tf.1; let f := tf.2
                 if (t == 0 && f == 0) || hasTF t f ws || (bound != 0 && decide (rankBST.lookup t f < bound)) then false
                 else if isTgtTF (2 ^ W - 1) t f then true
                 else
                   let v : Wire := ⟨t, f, t ^^^ f⟩
                   (if da && db then
                     let rest2 := dropTwo x y ws
                     if (coverSep rest2 ||| v.s) == 2 ^ W - 1 then search (2 ^ W - 1) bound (c' + 1) (v :: rest2) else false
                    else false) ||
                   (if da then search (2 ^ W - 1) bound (c' + 1) (v :: dropOne x ws) else false) ||
                   (if db then search (2 ^ W - 1) bound (c' + 1) (v :: dropOne y ws) else false) ||
                   (if allow0 then search (2 ^ W - 1) bound (c' + 1) (v :: ws) else false)) = true := by
            have ht : tf.1 = wv.t := by rw [← htf]
            have hf : tf.2 = wv.f := by rw [← htf]
            have hs : tf.1 ^^^ tf.2 = wv.s := by rw [← htf]
            have hwv_eta : (⟨wv.t, wv.f, wv.t ^^^ wv.f⟩ : Wire) = wv := by
              cases wv; simp only [GoodWire] at hgwv; simp [hgwv.2.2]
            by_cases hsa : S' (den W wa) <;> by_cases hsb : S' (den W wb)
            · have hall0 : ws.length ≤ c' + 1 := by
                have := hl'.card_le _ (h11 ⟨hsa, hsb⟩); simp at this; omega
              have hih0 := ih hkc (h11 ⟨hsa, hsb⟩)
              dsimp only
              simp only [hall0, decide_true, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                         ht, hf, hnot0, hnotdup, hnotfb, Bool.or_false]
              by_cases htgt : isTgtTF (2 ^ W - 1) wv.t wv.f = true
              · simp [htgt]
              · simp only [htgt, Bool.false_eq_true, ↓reduceIte, hwv_eta, hih0, Bool.or_true]
            · have hih1 := ih hkc (h10 ⟨hsa, hsb⟩)
              rcases hxy_case with ⟨rfl, rfl, _, hdb_t⟩ | ⟨rfl, rfl, hda_t, _⟩
              · have hdb' : db = true := hdb_t hsb
                dsimp only
                simp only [hdb', Bool.or_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                           ht, hf, hnot0, hnotdup, hnotfb, Bool.or_false]
                by_cases htgt : isTgtTF (2 ^ W - 1) wv.t wv.f = true
                · simp [htgt]
                · simp only [htgt, Bool.false_eq_true, ↓reduceIte, hwv_eta, hih1, Bool.or_true, Bool.true_or]
              · have hda' : da = true := hda_t hsb
                dsimp only
                simp only [hda', Bool.or_true, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                           ht, hf, hnot0, hnotdup, hnotfb, Bool.or_false]
                by_cases htgt : isTgtTF (2 ^ W - 1) wv.t wv.f = true
                · simp [htgt]
                · simp only [htgt, Bool.false_eq_true, ↓reduceIte, hwv_eta, hih1, Bool.or_true, Bool.true_or]
            · have hih1 := ih hkc (h01 ⟨hsa, hsb⟩)
              rcases hxy_case with ⟨rfl, rfl, hda_t, _⟩ | ⟨rfl, rfl, _, hdb_t⟩
              · have hda' : da = true := hda_t hsa
                dsimp only
                simp only [hda', Bool.or_true, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                           ht, hf, hnot0, hnotdup, hnotfb, Bool.or_false]
                by_cases htgt : isTgtTF (2 ^ W - 1) wv.t wv.f = true
                · simp [htgt]
                · simp only [htgt, Bool.false_eq_true, ↓reduceIte, hwv_eta, hih1, Bool.or_true, Bool.true_or]
              · have hdb' : db = true := hdb_t hsa
                dsimp only
                simp only [hdb', Bool.or_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                           ht, hf, hnot0, hnotdup, hnotfb, Bool.or_false]
                by_cases htgt : isTgtTF (2 ^ W - 1) wv.t wv.f = true
                · simp [htgt]
                · simp only [htgt, Bool.false_eq_true, ↓reduceIte, hwv_eta, hih1, Bool.or_true, Bool.true_or]
            · have hih2 := ih hkc (h00 ⟨hsa, hsb⟩)
              have hcov2 : coverSep (dropTwo wa wb ws) ||| wv.s = 2 ^ W - 1 := by
                have := coverSep_eq_all_of_live hl' (h00 ⟨hsa, hsb⟩)
                simpa [coverSep, Nat.or_comm] using this
              rcases hxy_case with ⟨rfl, rfl, hda_t, hdb_t⟩ | ⟨rfl, rfl, hda_t, hdb_t⟩
              · have hda' := hda_t hsa; have hdb' := hdb_t hsb
                dsimp only
                simp only [hda', hdb', Bool.or_true, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                           ht, hf, hnot0, hnotdup, hnotfb, Bool.or_false]
                by_cases htgt : isTgtTF (2 ^ W - 1) wv.t wv.f = true
                · simp [htgt]
                · have hws_eq : wv.t ^^^ wv.f = wv.s := hgwv.2.2.symm
                  simp only [htgt, Bool.false_eq_true, ↓reduceIte, hws_eq, hcov2, beq_self_eq_true, hih2, Bool.true_or]
              · have hda' := hda_t hsb; have hdb' := hdb_t hsa
                dsimp only
                simp only [hda', hdb', Bool.or_true, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                           ht, hf, hnot0, hnotdup, hnotfb, Bool.or_false]
                by_cases htgt : isTgtTF (2 ^ W - 1) wv.t wv.f = true
                · simp [htgt]
                · have hws_eq : wv.t ^^^ wv.f = wv.s := hgwv.2.2.symm
                  simp only [htgt, Bool.false_eq_true, ↓reduceIte, hws_eq, hdrop_symm, hcov2, beq_self_eq_true, hih2, Bool.true_or]
          have hda_imp : ¬ S' (den W wa) →
              (match op with
               | .conj => (if (wa.s &&& once) == 0 then 0 else (wa.s &&& once) &&& wb.t) == (wa.s &&& once)
               | .disj => (if (wa.s &&& once) == 0 then 0 else (wa.s &&& once) &&& wb.t) == 0
               | .diffL => (if (wa.s &&& once) == 0 then 0 else (wa.s &&& once) &&& wb.t) == 0
               | .diffR => (if (wa.s &&& once) == 0 then 0 else (wa.s &&& once) &&& wb.t) == (wa.s &&& once)) = true := by
            intro hna
            have hdropA : ∀ f, S' f → f = den W wv ∨ (∃ w ∈ ws, w ≠ wa ∧ den W w = f) := by
              intro f hf; rcases hcond.2.2.2.2.1 f hf with rfl | hfS
              · exact Or.inl hdwv.symm
              · obtain ⟨w, hw, rfl⟩ := (hr.2.2 f).mp hfS
                exact Or.inr ⟨w, hw, fun e => hna (e ▸ hf), rfl⟩
            have h := drop_left_cond hr hl' hwa hwb hwab hgwv hdwv hdropA
            cases op <;> simpa only [once, hm1] using h
          have hdb_imp : ¬ S' (den W wb) →
              (match op with
               | .conj => (if (wb.s &&& once) == 0 then 0 else (wb.s &&& once) &&& wa.t) == (wb.s &&& once)
               | .disj => (if (wb.s &&& once) == 0 then 0 else (wb.s &&& once) &&& wa.t) == 0
               | .diffL => (if (wb.s &&& once) == 0 then 0 else (wb.s &&& once) &&& wa.t) == (wb.s &&& once)
               | .diffR => (if (wb.s &&& once) == 0 then 0 else (wb.s &&& once) &&& wa.t) == 0) = true := by
            intro hnb
            have hdropB : ∀ f, S' f → f = den W wv ∨ (∃ w ∈ ws, w ≠ wb ∧ den W w = f) := by
              intro f hf; rcases hcond.2.2.2.2.1 f hf with rfl | hfS
              · exact Or.inl hdwv.symm
              · obtain ⟨w, hw, rfl⟩ := (hr.2.2 f).mp hfS
                exact Or.inr ⟨w, hw, fun e => hnb (e ▸ hf), rfl⟩
            have h := drop_right_cond hr hl' hwa hwb hwab hgwv hdwv hdropB
            cases op <;> simpa only [once, hm1] using h
          apply pairsGo_of_mem hca hcb hcab
          · dsimp only [ca, cb]
            cases op
            · have hok := hbranch _ _ _ (den_inj (good_op0 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).1 hgwv ((good_op0 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).2.trans hdwv.symm)) wa wb (Or.inl ⟨rfl, rfl, hda_imp, hdb_imp⟩)
              dsimp only at hok ⊢; simp only [hok, Bool.true_or]
            · have hok := hbranch _ _ _ (den_inj (good_op1 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).1 hgwv ((good_op1 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).2.trans hdwv.symm)) wa wb (Or.inl ⟨rfl, rfl, hda_imp, hdb_imp⟩)
              dsimp only at hok ⊢; simp only [hok, Bool.or_true, Bool.true_or]
            · have hok := hbranch _ _ _ (den_inj (good_op2 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).1 hgwv ((good_op2 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).2.trans hdwv.symm)) wa wb (Or.inl ⟨rfl, rfl, hda_imp, hdb_imp⟩)
              dsimp only at hok ⊢; simp only [hok, Bool.or_true, Bool.true_or]
            · have hok := hbranch _ _ _ (den_inj (good_op3 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).1 hgwv ((good_op3 (hr.2.1 wa hwa) (hr.2.1 wb hwb)).2.trans hdwv.symm)) wa wb (Or.inl ⟨rfl, rfl, hda_imp, hdb_imp⟩)
              dsimp only at hok ⊢; simp only [hok, Bool.or_true]
          · dsimp only [ca, cb]
            cases op
            · have hok := hbranch _ _ _ (den_inj (good_op0 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).1 hgwv ((good_op0 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).2.trans (by rw [hdwv]; funext r; simp [evalOp, Bool.and_comm]))) wb wa (Or.inr ⟨rfl, rfl, hdb_imp, hda_imp⟩)
              dsimp only at hok ⊢; simp only [hok, Bool.true_or]
            · have hok := hbranch _ _ _ (den_inj (good_op1 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).1 hgwv ((good_op1 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).2.trans (by rw [hdwv]; funext r; simp [evalOp, Bool.or_comm]))) wb wa (Or.inr ⟨rfl, rfl, hdb_imp, hda_imp⟩)
              dsimp only at hok ⊢; simp only [hok, Bool.or_true, Bool.true_or]
            · have hok := hbranch _ _ _ (den_inj (good_op3 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).1 hgwv ((good_op3 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).2.trans (by rw [hdwv]; funext r; simp [evalOp, Bool.and_comm]))) wb wa (Or.inr ⟨rfl, rfl, hdb_imp, hda_imp⟩)
              dsimp only at hok ⊢; simp only [hok, Bool.or_true]
            · have hok := hbranch _ _ _ (den_inj (good_op2 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).1 hgwv ((good_op2 (hr.2.1 wb hwb) (hr.2.1 wa hwa)).2.trans (by rw [hdwv]; funext r; simp [evalOp, Bool.and_comm]))) wb wa (Or.inr ⟨rfl, rfl, hdb_imp, hda_imp⟩)
              dsimp only at hok ⊢; simp only [hok, Bool.or_true, Bool.true_or]

/-! ### Section 5: C6, C5+pendant, and Theta(2,3,3) ≥ 11 -/

def c6Pairs : List (Nat × Nat) := [(11, 9), (13, 9), (25, 9), (41, 9), (19, 18), (22, 18), (26, 18), (50, 18), (23, 21), (29, 21), (53, 21), (37, 36), (38, 36), (44, 36), (52, 36), (43, 42), (46, 42), (58, 42), (3, 2), (3, 1), (6, 4), (6, 2), (12, 8), (12, 4), (24, 16), (24, 8), (33, 32), (33, 1), (48, 32), (48, 16), (3, 36), (6, 9), (12, 18), (24, 36), (33, 18), (48, 9), (3, 9), (3, 18), (3, 21), (3, 42), (6, 18), (6, 21), (6, 36), (6, 42), (12, 9), (12, 21), (12, 36), (12, 42)]
def c5pPairs : List (Nat × Nat) := [(7, 3), (11, 3), (19, 3), (35, 3), (27, 25), (29, 25), (57, 25), (29, 28), (30, 28), (60, 28), (35, 34), (38, 34), (42, 34), (50, 34), (45, 44), (46, 44), (60, 44), (5, 4), (5, 1), (6, 4), (6, 2), (10, 8), (10, 2), (18, 16), (18, 2), (33, 32), (33, 1), (48, 32), (48, 16), (5, 34), (6, 25), (18, 44), (33, 28), (48, 3), (5, 3), (5, 25), (5, 28), (5, 44), (6, 3), (6, 28), (6, 34), (6, 44), (10, 3), (10, 25), (10, 28), (10, 34), (10, 44), (18, 3)]
def thPairs : List (Nat × Nat) := [(7, 3), (11, 3), (19, 3), (35, 3), (67, 3), (43, 42), (46, 42), (58, 42), (106, 42), (45, 44), (46, 44), (60, 44), (108, 44), (53, 52), (54, 52), (60, 52), (116, 52), (77, 76), (78, 76), (92, 76), (108, 76), (83, 81), (85, 81), (89, 81), (113, 81), (85, 84), (86, 84), (92, 84), (116, 84), (5, 4), (5, 1), (6, 4), (6, 2), (9, 8), (9, 1), (18, 16), (18, 2), (24, 16), (24, 8), (33, 32), (33, 1), (66, 64), (66, 2), (96, 64), (96, 32), (13, 0), (14, 10), (15, 12), (21, 17), (22, 20), (23, 34), (25, 36), (26, 40), (27, 48), (28, 65), (29, 68), (30, 72), (31, 80), (37, 0), (38, 0), (39, 0), (41, 0), (47, 0), (49, 0), (50, 0), (51, 0), (55, 0), (56, 0), (57, 0), (59, 0), (61, 0), (62, 0), (63, 0), (69, 0), (70, 0), (71, 0), (73, 0), (74, 0), (75, 0), (79, 0), (82, 0), (87, 0), (88, 0), (90, 0), (91, 0), (93, 0), (94, 0), (95, 0), (97, 0), (98, 0), (99, 0), (100, 0), (101, 0), (102, 0), (103, 0), (104, 0), (105, 0), (107, 0), (109, 0), (110, 0), (111, 0), (112, 0), (114, 0), (115, 0), (117, 0), (118, 0), (119, 0), (120, 0), (121, 0), (122, 0), (123, 0), (124, 0), (125, 0), (126, 0), (127, 0)]

def c6All : Nat := 281474976710655
def c5pAll : Nat := 281474976710655
def thAll : Nat := (144115188075855871 * P58 + 288230376151711743)

def c6Ws : List Wire := [⟨1049247911711, 55355820738319, 55717604395024⟩, ⟨17526691959281, 151341765198064, 147702853144833⟩, ⟨280381923360546, 112434737086208, 168516269441058⟩, ⟨263895738720847, 167780787912719, 115017101877824⟩, ⟨43805460468, 38917252319216, 38959950479364⟩, ⟨52546501768, 224860127361024, 224912002253960⟩]
def c5pWs : List Wire := [⟨262630950143, 154267776450687, 154427193443456⟩, ⟨281203353107743, 181720625200143, 99535341256976⟩, ⟨4382479338401, 90922310943616, 89394913740833⟩, ⟨136339448255474, 99753838887920, 42579236229122⟩, ⟨140748653667316, 27046759629808, 167794859646980⟩, ⟨13388349000, 108991942360064, 109004994904648⟩]
def thWs : List Wire := [⟨(96094934384696765 * P58 + 192987957620253247), 18296991282888735, (96094934384696765 * P58 + 210719763356328480)⟩, ⟨(115324036790839766 * P58 + 231590243749611007), 1200739711975935, (115324036790839766 * P58 + 230389504037635072)⟩, ⟨(135608396411040023 * P58 + 272432601646497345), 38984287464193536, (135608396411040023 * P58 + 237951913809674305)⟩, ⟨(143560897837432344 * P58 + 286225305173925858), 76772583367647200, (143560897837432344 * P58 + 209452721806278658)⟩, ⟨(144106393052413920 * P58 + 287949417106499716), 153966984594317312, (144106393052413920 * P58 + 133982432512182404)⟩, ⟨(144115187002146815 * P58 + 28037832900584), 16906640544628704, (144115187002146815 * P58 + 16898394493550600)⟩, ⟨(144115188075823104 * P58 + 32985885643024), 270226973295247360, (144115188075823104 * P58 + 270237967874855184)⟩]

theorem c6All_eq : c6All = 2 ^ 48 - 1 := by decide +kernel
theorem c5pAll_eq : c5pAll = 2 ^ 48 - 1 := by decide +kernel
theorem thAll_eq : thAll = 2 ^ 115 - 1 := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem c6_search_false : search c6All 0 7 c6Ws = false := by decide +kernel
set_option maxHeartbeats 2000000 in
theorem c5p_search_false : search c5pAll 0 7 c5pWs = false := by decide +kernel

def evalEdges (es : List (Nat × Nat)) (m : Nat) : Bool :=
  es.any fun (u, v) => m.testBit u && m.testBit v

def c6Ans (r : Fin 64) : Bool := evalEdges [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0)] r.val
def c5pAns (r : Fin 64) : Bool := evalEdges [(0,2),(2,1),(0,5),(5,4),(4,1),(1,3)] r.val
def thAns (r : Fin 128) : Bool := evalEdges [(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)] r.val
def p9Ans (r : Fin 512) : Bool := evalEdges [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] r.val

def bit6 (i : Fin 6) (r : Fin 64) : Bool := r.val.testBit i.val
def bit7 (i : Fin 7) (r : Fin 128) : Bool := r.val.testBit i.val
def bit9 (i : Fin 9) (r : Fin 512) : Bool := r.val.testBit i.val

def verts6 : List (Fin 64 → Bool) := constF :: List.ofFn bit6
def verts7 : List (Fin 128 → Bool) := constF :: List.ofFn bit7
def verts9 : List (Fin 512 → Bool) := constF :: List.ofFn bit9

def c6Row (r : Bool × Fin 48) : Fin 64 :=
  let p := c6Pairs.getD r.2.val (0, 0)
  ⟨(if r.1 then p.1 else p.2) % 64, Nat.mod_lt _ (by decide)⟩

def c5pRow (r : Bool × Fin 48) : Fin 64 :=
  let p := c5pPairs.getD r.2.val (0, 0)
  ⟨(if r.1 then p.1 else p.2) % 64, Nat.mod_lt _ (by decide)⟩

def thRow (r : Bool × Fin 115) : Fin 128 :=
  let p := thPairs.getD r.2.val (0, 0)
  ⟨(if r.1 then p.1 else p.2) % 128, Nat.mod_lt _ (by decide)⟩

theorem c6_row_ans (r : Bool × Fin 48) : c6Ans (c6Row r) = r.1 := by
  rcases r with ⟨b, j⟩; revert b j; decide +kernel
theorem c5p_row_ans (r : Bool × Fin 48) : c5pAns (c5pRow r) = r.1 := by
  rcases r with ⟨b, j⟩; revert b j; decide +kernel
theorem th_row_ans (r : Bool × Fin 115) : thAns (thRow r) = r.1 := by
  rcases r with ⟨b, j⟩; revert b j; decide +kernel

theorem c6_ws_good (i : Fin 6) : GoodWire 48 (c6Ws.getD i.val ⟨0,0,0⟩) ∧
    ∀ r : Bool × Fin 48, den 48 (c6Ws.getD i.val ⟨0,0,0⟩) r = bit6 i (c6Row r) := by
  have h1 : ∀ k : Fin 6, GoodWire 48 (c6Ws.getD k.val ⟨0,0,0⟩) := by decide +kernel
  have h2 : ∀ (k : Fin 6) (b : Bool) (j : Fin 48), den 48 (c6Ws.getD k.val ⟨0,0,0⟩) (b, j) = bit6 k (c6Row (b, j)) := by decide +kernel
  exact ⟨h1 i, fun ⟨b, j⟩ => h2 i b j⟩

theorem c5p_ws_good (i : Fin 6) : GoodWire 48 (c5pWs.getD i.val ⟨0,0,0⟩) ∧
    ∀ r : Bool × Fin 48, den 48 (c5pWs.getD i.val ⟨0,0,0⟩) r = bit6 i (c5pRow r) := by
  have h1 : ∀ k : Fin 6, GoodWire 48 (c5pWs.getD k.val ⟨0,0,0⟩) := by decide +kernel
  have h2 : ∀ (k : Fin 6) (b : Bool) (j : Fin 48), den 48 (c5pWs.getD k.val ⟨0,0,0⟩) (b, j) = bit6 k (c5pRow (b, j)) := by decide +kernel
  exact ⟨h1 i, fun ⟨b, j⟩ => h2 i b j⟩

theorem th_ws_good (i : Fin 7) : GoodWire 115 (thWs.getD i.val ⟨0,0,0⟩) ∧
    ∀ r : Bool × Fin 115, den 115 (thWs.getD i.val ⟨0,0,0⟩) r = bit7 i (thRow r) := by
  have h1 : ∀ k : Fin 7, GoodWire 115 (thWs.getD k.val ⟨0,0,0⟩) := by decide +kernel
  have h2 : ∀ (k : Fin 7) (b : Bool) (j : Fin 115), den 115 (thWs.getD k.val ⟨0,0,0⟩) (b, j) = bit7 k (thRow (b, j)) := by decide +kernel
  exact ⟨h1 i, fun ⟨b, j⟩ => h2 i b j⟩

def c6Priv : List Nat := [4, 0, 1, 6, 2, 3]
def c5pPriv : List Nat := [7, 4, 0, 1, 2, 3]

theorem c6_priv_spec : ∀ i : Fin 6,
    let idx : Fin 48 := ⟨c6Priv.getD i.val 0 % 48, Nat.mod_lt _ (by decide)⟩
    bit6 i (c6Row (true, idx)) ≠ bit6 i (c6Row (false, idx)) ∧
    ∀ j : Fin 6, j ≠ i → bit6 j (c6Row (true, idx)) = bit6 j (c6Row (false, idx)) := by decide +kernel

theorem c5p_priv_spec : ∀ i : Fin 6,
    let idx : Fin 48 := ⟨c5pPriv.getD i.val 0 % 48, Nat.mod_lt _ (by decide)⟩
    bit6 i (c5pRow (true, idx)) ≠ bit6 i (c5pRow (false, idx)) ∧
    ∀ j : Fin 6, j ≠ i → bit6 j (c5pRow (true, idx)) = bit6 j (c5pRow (false, idx)) := by decide +kernel

theorem c6_ws_nodup : c6Ws.Nodup := by decide +kernel
theorem c5p_ws_nodup : c5pWs.Nodup := by decide +kernel

theorem c6_ws_mem (w : Wire) (hw : w ∈ c6Ws) : ∃ i : Fin 6, c6Ws.getD i.val ⟨0,0,0⟩ = w := by
  have : ∀ x ∈ c6Ws, ∃ i : Fin 6, c6Ws.getD i.val ⟨0,0,0⟩ = x := by decide +kernel
  exact this w hw

theorem c5p_ws_mem (w : Wire) (hw : w ∈ c5pWs) : ∃ i : Fin 6, c5pWs.getD i.val ⟨0,0,0⟩ = w := by
  have : ∀ x ∈ c5pWs, ∃ i : Fin 6, c5pWs.getD i.val ⟨0,0,0⟩ = x := by decide +kernel
  exact this w hw

theorem c6_ws_getD_mem (i : Fin 6) : c6Ws.getD i.val ⟨0,0,0⟩ ∈ c6Ws := by
  revert i; decide +kernel

theorem c5p_ws_getD_mem (i : Fin 6) : c5pWs.getD i.val ⟨0,0,0⟩ ∈ c5pWs := by
  revert i; decide +kernel

theorem c6_lower {n ws} (hrun : Free verts6 n ws) (hout : c6Ans ∈ ws) : 8 ≤ n := by
  by_contra hlt
  have hn : n ≤ 7 := by omega
  have hr := free_map_restrict c6Row hrun (forbid2 := fun _ => False) (fun _ h => h)
  have h0 : constF ∈ verts6.map (restrict c6Row) := List.mem_map.mpr ⟨constF, List.mem_cons_self, rfl⟩
  have htgt : targetDen 48 ∈ ws.map (restrict c6Row) := by
    have : restrict c6Row c6Ans = targetDen 48 := funext c6_row_ans
    rw [← this]; exact List.mem_map.mpr ⟨c6Ans, hout, rfl⟩
  obtain ⟨m, S, hmn, hl, hsub⟩ := rewind h0 hr htgt
  have hno0 : ¬ S constF := hl.no_constF (fun e => by have := congrFun e (true, ⟨0, by decide⟩); simp [targetDen, constF] at this)
  have hrep : Rep 48 c6Ws S := by
    refine ⟨c6_ws_nodup, fun w hw => by obtain ⟨i, rfl⟩ := c6_ws_mem w hw; exact (c6_ws_good i).1, ?_⟩
    intro f; constructor
    · intro hf
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (hsub f hf)
      rcases List.mem_cons.mp hg with rfl | hg
      · exact (hno0 hf).elim
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
        exact ⟨c6Ws.getD i.val ⟨0,0,0⟩, c6_ws_getD_mem i, funext (c6_ws_good i).2⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨i, rfl⟩ := c6_ws_mem w hw
      let idx : Fin 48 := ⟨c6Priv.getD i.val 0 % 48, Nat.mod_lt _ (by decide)⟩
      obtain ⟨hdiff, hsame⟩ := c6_priv_spec i
      obtain ⟨g, hgS, hgsep⟩ := hl.separates (r := (true, idx)) (s := (false, idx)) (fun h => Bool.noConfusion h)
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (hsub g hgS)
      rcases List.mem_cons.mp hu with rfl | hu
      · exact (hgsep rfl).elim
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
        by_cases hji : j = i
        · subst hji
          have heq : den 48 (c6Ws.getD j.val ⟨0,0,0⟩) = restrict c6Row (bit6 j) := funext (c6_ws_good j).2
          rw [heq]; exact hgS
        · exact (hgsep (hsame j hji)).elim
  have hs := search_complete (W := 48) (bound := 0) (fun _ _ h => (h rfl).elim) (Nat.le_trans hmn hn) hl hrep
  rw [← c6All_eq, c6_search_false] at hs; cases hs

theorem c5p_lower {n ws} (hrun : Free verts6 n ws) (hout : c5pAns ∈ ws) : 8 ≤ n := by
  by_contra hlt
  have hn : n ≤ 7 := by omega
  have hr := free_map_restrict c5pRow hrun (forbid2 := fun _ => False) (fun _ h => h)
  have h0 : constF ∈ verts6.map (restrict c5pRow) := List.mem_map.mpr ⟨constF, List.mem_cons_self, rfl⟩
  have htgt : targetDen 48 ∈ ws.map (restrict c5pRow) := by
    have : restrict c5pRow c5pAns = targetDen 48 := funext c5p_row_ans
    rw [← this]; exact List.mem_map.mpr ⟨c5pAns, hout, rfl⟩
  obtain ⟨m, S, hmn, hl, hsub⟩ := rewind h0 hr htgt
  have hno0 : ¬ S constF := hl.no_constF (fun e => by have := congrFun e (true, ⟨0, by decide⟩); simp [targetDen, constF] at this)
  have hrep : Rep 48 c5pWs S := by
    refine ⟨c5p_ws_nodup, fun w hw => by obtain ⟨i, rfl⟩ := c5p_ws_mem w hw; exact (c5p_ws_good i).1, ?_⟩
    intro f; constructor
    · intro hf
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (hsub f hf)
      rcases List.mem_cons.mp hg with rfl | hg
      · exact (hno0 hf).elim
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
        exact ⟨c5pWs.getD i.val ⟨0,0,0⟩, c5p_ws_getD_mem i, funext (c5p_ws_good i).2⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨i, rfl⟩ := c5p_ws_mem w hw
      let idx : Fin 48 := ⟨c5pPriv.getD i.val 0 % 48, Nat.mod_lt _ (by decide)⟩
      obtain ⟨hdiff, hsame⟩ := c5p_priv_spec i
      obtain ⟨g, hgS, hgsep⟩ := hl.separates (r := (true, idx)) (s := (false, idx)) (fun h => Bool.noConfusion h)
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (hsub g hgS)
      rcases List.mem_cons.mp hu with rfl | hu
      · exact (hgsep rfl).elim
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
        by_cases hji : j = i
        · subst hji
          have heq : den 48 (c5pWs.getD j.val ⟨0,0,0⟩) = restrict c5pRow (bit6 j) := funext (c5p_ws_good j).2
          rw [heq]; exact hgS
        · exact (hgsep (hsame j hji)).elim
  have hs := search_complete (W := 48) (bound := 0) (fun _ _ h => (h rfl).elim) (Nat.le_trans hmn hn) hl hrep
  rw [← c5pAll_eq, c5p_search_false] at hs; cases hs

-- Theta(2,3,3) minors (deleting vertex x in 2..6):
def thMinorEmbs : List (List Nat) := [[0, 3, 4, 1, 6, 5], [0, 1, 2, 4, 6, 5], [1, 0, 2, 3, 5, 6], [0, 1, 2, 6, 4, 3], [1, 0, 2, 5, 3, 4]]

def plantBits (emb : List Nat) (m : Nat) : Nat :=
  (List.range emb.length).foldl (fun acc i => if m.testBit i then acc ||| (1 <<< emb.getD i 0) else acc) 0

def minorLift (x : Fin 7) (r : Fin 64) : Fin 128 :=
  ⟨plantBits (thMinorEmbs.getD (x.val - 2) []) r.val % 128, Nat.mod_lt _ (by decide)⟩

theorem minor_off : ∀ x : Fin 7, 2 ≤ x.val → ∀ r : Fin 64, bit7 x (minorLift x r) = false := by decide +kernel
theorem minor_ans_c6 : ∀ r : Fin 64, thAns (minorLift 2 r) = c6Ans r := by decide +kernel
theorem minor_ans_c5p : ∀ x : Fin 7, 3 ≤ x.val → ∀ r : Fin 64, thAns (minorLift x r) = c5pAns r := by decide +kernel

theorem minor_bit_in : ∀ x : Fin 7, 2 ≤ x.val → ∀ y : Fin 7,
    (fun r => bit7 y (minorLift x r)) = constF ∨ ∃ j : Fin 6, ∀ r : Fin 64, bit7 y (minorLift x r) = bit6 j r := by
  intro x hx y
  by_cases hyx : y = x
  · left; subst hyx; exact funext (minor_off y hx)
  · right
    have htbl : ∀ x y : Fin 7, 2 ≤ x.val → y ≠ x →
        ∃ j : Fin 6, ∀ r : Fin 64, bit7 y (minorLift x r) = bit6 j r := by decide +kernel
    exact htbl x y hx hyx

theorem th_minor_lower (x : Fin 7) (hx : 2 ≤ x.val) {m ws}
    (hrun : Free (verts7.map (restrict (minorLift x))) m ws) (hout : restrict (minorLift x) thAns ∈ ws) :
    8 ≤ m := by
  have hsub : ∀ w, w ∈ verts7.map (restrict (minorLift x)) → w ∈ verts6 := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    rcases List.mem_cons.mp hu with rfl | hu
    · exact List.mem_cons_self
    · obtain ⟨y, rfl⟩ := List.mem_ofFn.mp hu
      rcases minor_bit_in x hx y with h0 | ⟨j, hj⟩
      · have : restrict (minorLift x) (bit7 y) = constF := h0
        rw [this]; exact List.mem_cons_self
      · have : restrict (minorLift x) (bit7 y) = bit6 j := funext hj
        rw [this]; exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  obtain ⟨ws', hrun', hsub'⟩ := free_mono hsub hrun
  by_cases hx2 : x = 2
  · subst hx2
    have h1 : restrict (minorLift 2) thAns = c6Ans := funext minor_ans_c6
    exact c6_lower hrun' (h1 ▸ hsub' _ hout)
  · have hx3 : 3 ≤ x.val := by omega
    have h1 : restrict (minorLift x) thAns = c5pAns := funext (minor_ans_c5p x hx3)
    exact c5p_lower hrun' (h1 ▸ hsub' _ hout)

-- Theta(2,3,3) sensitivity & absorbing-head lemma:
def thSensSeeds : List Nat := [0, 0, 4, 10, 8, 4, 4, 8, 4, 20, 4, 32, 4, 68, 4, 17, 0, 0, 16, 4, 4, 12, 4, 16, 4, 36, 4, 64, 2, 1, 1, 2, 0, 0, 1, 10, 1, 17, 1, 34, 1, 65, 16, 1, 1, 3, 1, 20, 0, 0, 1, 16, 1, 48, 1, 65, 2, 3, 8, 2, 2, 12, 2, 8, 0, 0, 2, 34, 2, 72, 64, 1, 1, 3, 1, 68, 1, 72, 1, 17, 0, 0, 1, 64, 2, 3, 32, 2, 2, 36, 2, 10, 2, 48, 2, 32, 0, 0]
def thLo (x y : Fin 7) (b : Bool) : Fin 128 :=
  ⟨thSensSeeds.getD (2 * (7 * x.val + y.val) + b.toNat) 0 % 128, Nat.mod_lt _ (by decide)⟩
def thHi (x y : Fin 7) (b : Bool) : Fin 128 :=
  ⟨((thLo x y b).val ||| (1 <<< x.val)) % 128, Nat.mod_lt _ (by decide)⟩

theorem th_sens_spec : ∀ (x y : Fin 7), x ≠ y → ∀ b : Bool,
    bit7 x (thLo x y b) = false ∧ bit7 x (thHi x y b) = true ∧
    bit7 y (thLo x y b) = b ∧ bit7 y (thHi x y b) = b ∧
    thAns (thLo x y b) ≠ thAns (thHi x y b) ∧
    ∀ z : Fin 7, z ≠ x → bit7 z (thLo x y b) = bit7 z (thHi x y b) := by decide +kernel

theorem th_bit_inj : ∀ x y : Fin 7, bit7 x = bit7 y → x = y := by
  intro x y h
  by_contra hne

  have h2 : ∀ a b : Fin 7, a ≠ b → ∃ r : Fin 128, bit7 a r ≠ bit7 b r := by decide +kernel
  obtain ⟨r, hr⟩ := h2 x y hne
  exact hr (congrFun h r)

theorem th_ans_ne_bit (x : Fin 7) : thAns ≠ bit7 x := by
  have h : ∀ a : Fin 7, ∃ r : Fin 128, thAns r ≠ bit7 a r := by decide +kernel
  obtain ⟨r, hr⟩ := h x
  exact fun e => hr (congrFun e r)

theorem th_ans_not_raw : thAns ∉ verts7 := by
  intro h
  rcases List.mem_cons.mp h with h0 | h1
  · have := congrFun h0 ⟨5, by decide⟩; revert this; decide
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp h1; exact th_ans_ne_bit i hi.symm

theorem th_read_twice {g : TGate (Fin 128)} {tail : List (TGate (Fin 128))}
    {x y : Fin 7} (hxy : x ≠ y)
    (hlhs : g.lhs = bit7 x) (hrhs : g.rhs = bit7 y)
    (hs : Sufficient verts7 thAns (g :: tail)) :
    ∃ h ∈ tail, reads h (bit7 x) := by
  obtain ⟨b, hmask⟩ := op_masks_left g.op
  obtain ⟨lx, hx, ly, hy, hout, hfix⟩ := th_sens_spec x y hxy b
  apply second_reader hs (th_ans_ne_bit x) (thLo x y b) (thHi x y b) hout
  · simp [TGate.val, hlhs, hrhs, lx, hx, ly, hy, hmask false true]
  · intro w hw hne
    rcases List.mem_cons.mp hw with rfl | hw
    · rfl
    · obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hw
      exact hfix z (fun e => hne (congrArg bit7 e))

theorem th_read_twice_right {g : TGate (Fin 128)} {tail : List (TGate (Fin 128))}
    {x y : Fin 7} (hxy : x ≠ y)
    (hlhs : g.lhs = bit7 x) (hrhs : g.rhs = bit7 y)
    (hs : Sufficient verts7 thAns (g :: tail)) :
    ∃ h ∈ tail, reads h (bit7 y) := by
  have hmask : ∃ b : Bool, ∀ c1 c2 : Bool, evalOp g.op b c1 = evalOp g.op b c2 := by
    cases g.op
    · exact ⟨false, by decide⟩
    · exact ⟨true, by decide⟩
    · exact ⟨false, by decide⟩
    · exact ⟨true, by decide⟩
  obtain ⟨b, hm⟩ := hmask
  obtain ⟨ly, hy, lx, hx, hout, hfix⟩ := th_sens_spec y x (Ne.symm hxy) b
  apply second_reader hs (th_ans_ne_bit y) (thLo y x b) (thHi y x b) hout
  · simp [TGate.val, hlhs, hrhs, lx, hx, ly, hy, hm false true]
  · intro w hw hne
    rcases List.mem_cons.mp hw with rfl | hw
    · rfl
    · obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hw
      exact hfix z (fun e => hne (congrArg bit7 e))

theorem th_absorbing_head {g : TGate (Fin 128)} {tail : List (TGate (Fin 128))}
    {x y : Fin 7} (hxy : x ≠ y) (hx2 : 2 ≤ x.val)
    (hreads : (g.lhs = bit7 x ∧ g.rhs = bit7 y ∧ (g.op = .conj ∨ g.op = .diffL)) ∨
              (g.lhs = bit7 y ∧ g.rhs = bit7 x ∧ (g.op = .conj ∨ g.op = .diffR)))
    (hs : Sufficient verts7 thAns (g :: tail)) (hf : FreshTrace verts7 (g :: tail))
    (hlen : (g :: tail).length ≤ 10) :
    ∃ ts, ts.length ≤ tail.length ∧ Sufficient verts7 thAns ts := by
  classical
  have hoff : restrict (minorLift x) (bit7 x) = constF := funext (minor_off x hx2)
  have hgz : restrict (minorLift x) g.val = constF := by
    funext r
    have hx0 : bit7 x (minorLift x r) = false := minor_off x hx2 r
    rcases hreads with ⟨hl, hr, hop⟩ | ⟨hl, hr, hop⟩ <;> rcases hop with h1 | h1 <;>
      simp [restrict, TGate.val, hl, hr, h1, hx0, evalOp, constF]
  have hout_nz : restrict (minorLift x) thAns ≠ constF := by
    intro heq
    by_cases hx2' : x = 2
    · subst hx2'
      have := congrFun heq ⟨3, by decide⟩
      rw [restrict, minor_ans_c6] at this; revert this; decide
    · have hx3 : 3 ≤ x.val := by omega
      have := congrFun heq ⟨5, by decide⟩
      rw [restrict, minor_ans_c5p x hx3] at this; revert this; decide
  have hgv_ne : g.val ≠ thAns := fun e => hout_nz (e ▸ hgz)
  by_cases hpath : UsePath tail g.val thAns
  · exfalso
    obtain ⟨h, hh, hrh⟩ : ∃ h ∈ tail, reads h (bit7 x) := by
      rcases hreads with ⟨hl, hr, _⟩ | ⟨hl, hr, _⟩
      · exact th_read_twice hxy hl hr hs
      · exact th_read_twice_right (Ne.symm hxy) hl hr hs
    obtain ⟨u, hu, hdu, hunz, z, hruz, hz0, hzw⟩ := boundary_gate (minorLift x) hpath hgz hout_nz
    have hgu : g ≠ u := fresh_head_ne_tail hf hu
    have hgh : g ≠ h := fresh_head_ne_tail hf hh
    have huh : h ≠ u := by
      intro heq; subst heq
      have hzx : z ≠ bit7 x := by
        rcases hzw with rfl | ⟨t, ht, rfl⟩
        · exact fun e => hf.1 (e ▸ List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨x, rfl⟩))
        · exact fun e => fresh_val_not_raw hf.2 t ht (List.mem_cons_of_mem _ (e ▸ List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨x, rfl⟩)))
      rcases hrh with hl1 | hr1 <;> rcases hruz with hl2 | hr2
      · exact hzx (hl2.symm.trans hl1)
      · exact hunz (both_zero_val_zero (minorLift x) (hl1.symm ▸ hoff) (hr2.symm ▸ hz0))
      · exact hunz (both_zero_val_zero (minorLift x) (hl2.symm ▸ hz0) (hr1.symm ▸ hoff))
      · exact hzx (hr2.symm.trans hr1)
    have hdg : disappears (minorLift x) g := Or.inl hgz
    have hdh : disappears (minorLift x) h := reading_zero_disappears (minorLift x) hoff hrh
    have h3 := three_saved (minorLift x) List.mem_cons_self (List.mem_cons_of_mem _ hh) (List.mem_cons_of_mem _ hu)
      hgh hgu huh hdg hdh hdu
    obtain ⟨m, ws, hsum, hrun, hin⟩ := free_restrict (minorLift x) List.mem_cons_self hs
    have hlo := th_minor_lower x hx2 hrun hin
    omega
  · exact omit_dead_head hs hgv_ne hpath

-- Theta(2,3,3) symmetries, 13 orbits, BST soundness, and rank induction:
def thPerms : List (List Nat) := [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 5, 6, 3, 4], [1, 0, 2, 4, 3, 6, 5], [1, 0, 2, 6, 5, 4, 3]]
def thCasesA : List Nat := [3, 3, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0]
def thCasesB : List Nat := [6, 5, 3, 2, 4, 4, 3, 1, 2, 3, 4, 1, 1]
def thCasesOp : List Nat := [1, 1, 2, 2, 2, 1, 1, 0, 1, 1, 1, 2, 1]
def thDispatchTbl : List Nat := [0, 0, 0, 0, 30, 50, 46, 48, 1, 34, 14, 1, 1, 26, 10, 1, 1, 42, 18, 1, 1, 27, 11, 1, 1, 43, 19, 1, 30, 50, 48, 46, 0, 0, 0, 0, 1, 36, 16, 1, 1, 44, 20, 1, 1, 28, 12, 1, 1, 45, 21, 1, 1, 29, 13, 1, 0, 34, 0, 14, 0, 36, 0, 16, 0, 0, 0, 0, 0, 38, 0, 1, 0, 40, 0, 1, 0, 39, 0, 1, 0, 41, 0, 1, 0, 26, 0, 10, 0, 44, 0, 20, 0, 38, 0, 1, 0, 0, 0, 0, 0, 22, 0, 1, 0, 6, 0, 1, 0, 2, 0, 1, 0, 42, 0, 18, 0, 28, 0, 12, 0, 40, 0, 1, 0, 22, 0, 1, 0, 0, 0, 0, 0, 3, 0, 1, 0, 8, 0, 1, 0, 27, 0, 11, 0, 45, 0, 21, 0, 39, 0, 1, 0, 6, 0, 1, 0, 3, 0, 1, 0, 0, 0, 0, 0, 23, 0, 1, 0, 43, 0, 19, 0, 29, 0, 13, 0, 41, 0, 1, 0, 2, 0, 1, 0, 8, 0, 1, 0, 23, 0, 1, 0, 0, 0, 0]

def permPos (s : Fin 4) (j : Fin 7) : Fin 7 :=
  ⟨(thPerms.getD s.val []).getD j.val 0 % 7, Nat.mod_lt _ (by decide)⟩

def pack7 (f : Fin 7 → Bool) : Fin 128 :=
  ⟨(List.range 7).foldl (fun acc i => if f ⟨i % 7, Nat.mod_lt _ (by decide)⟩ then acc ||| (1 <<< i) else acc) 0 % 128,
   Nat.mod_lt _ (by decide)⟩

def rowPerm (s : Fin 4) (r : Fin 128) : Fin 128 :=
  pack7 (fun j => bit7 (permPos s j) r)

theorem rowPerm_ans : ∀ (s : Fin 4) (r : Fin 128), thAns (rowPerm s r) = thAns r := by decide +kernel
theorem rowPerm_bit : ∀ (s : Fin 4) (j : Fin 7) (r : Fin 128), bit7 j (rowPerm s r) = bit7 (permPos s j) r := by decide +kernel

def caseWireVal (ci : Fin 13) : Fin 128 → Bool :=
  let a : Fin 7 := ⟨thCasesA.getD ci.val 0 % 7, Nat.mod_lt _ (by decide)⟩
  let b : Fin 7 := ⟨thCasesB.getD ci.val 0 % 7, Nat.mod_lt _ (by decide)⟩
  let op := opOfNat (thCasesOp.getD ci.val 0)
  fun r => evalOp op (bit7 a r) (bit7 b r)

def thCaseWires : List Wire := [⟨(144115188075855384 * P58 + 286258290914992114), 274941962623000544, (144115188075855384 * P58 + 11316328291991570)⟩, ⟨(144115188063043583 * P58 + 286253343005736938), 89175624284897248, (144115188063043583 * P58 + 199329518534524938)⟩, ⟨(387119369585061 * P58 + 1409025818239005), 18296991282888735, (387119369585061 * P58 + 19140865930829826)⟩, ⟨(5665513977154728 * P58 + 11260674132934718), 18296991282888735, (5665513977154728 * P58 + 29555431978303521)⟩, ⟨(6413463486493 * P58 + 177598508433979), 18015516274720799, (6413463486493 * P58 + 18190879252677156)⟩, ⟨(144115051710414840 * P58 + 288195733482373094), 230739567961964512, (144115051710414840 * P58 + 57456165520408582)⟩, ⟨(143948017207017405 * P58 + 287634330992164863), 95069574650535935, (143948017207017405 * P58 + 192564756341628928)⟩, ⟨(76882874446530964 * P58 + 154389024727892031), 31, (76882874446530964 * P58 + 154389024727892000)⟩, ⟨(141273910388194751 * P58 + 283693275779432063), 57281278747082271, (141273910388194751 * P58 + 226411997032349792)⟩, ⟨(144053607904313119 * P58 + 288195638437347299), 115616133341511648, (144053607904313119 * P58 + 172579505095835651)⟩, ⟨(144112806515900413 * P58 + 288127015614933695), 171982500869038111, (144112806515900413 * P58 + 116144514745895584)⟩, ⟨(19212059938165801 * P58 + 38598932892361216), 18296991282888704, (19212059938165801 * P58 + 56330738632630784)⟩, ⟨(134536096729005567 * P58 + 270189176641972223), 19497730994864639, (134536096729005567 * P58 + 286720242666071552)⟩]
def thetaStart (ci : Fin 13) : List Wire := thCaseWires.getD ci.val ⟨0,0,0⟩ :: thWs


set_option maxHeartbeats 4000000 in
theorem theta_case_0 : search thAll 1 9 (thetaStart ⟨0, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_1 : search thAll 2 9 (thetaStart ⟨1, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_2 : search thAll 3 9 (thetaStart ⟨2, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_3 : search thAll 4 9 (thetaStart ⟨3, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_4 : search thAll 5 9 (thetaStart ⟨4, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_5 : search thAll 6 9 (thetaStart ⟨5, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_6 : search thAll 7 9 (thetaStart ⟨6, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_7 : search thAll 8 9 (thetaStart ⟨7, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_8 : search thAll 9 9 (thetaStart ⟨8, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_9 : search thAll 10 9 (thetaStart ⟨9, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_10 : search thAll 11 9 (thetaStart ⟨10, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_11 : search thAll 12 9 (thetaStart ⟨11, by decide⟩) = false := by
  decide +kernel
set_option maxHeartbeats 4000000 in
theorem theta_case_12 : search thAll 13 9 (thetaStart ⟨12, by decide⟩) = false := by
  decide +kernel

theorem theta_case_all (ci : Fin 13) : search thAll (ci.val + 1) 9 (thetaStart ci) = false := by
  rcases ci with ⟨v, hv⟩
  match v with
  | 0 => exact theta_case_0
  | 1 => exact theta_case_1
  | 2 => exact theta_case_2
  | 3 => exact theta_case_3
  | 4 => exact theta_case_4
  | 5 => exact theta_case_5
  | 6 => exact theta_case_6
  | 7 => exact theta_case_7
  | 8 => exact theta_case_8
  | 9 => exact theta_case_9
  | 10 => exact theta_case_10
  | 11 => exact theta_case_11
  | 12 => exact theta_case_12
  | _ + 13 => omega

-- Injectivity of `thRow` (covers all 128 rows of Fin 128!):
def thInvB : List Bool := [false, false, false, false, false, true, true, true, false, true, false, true, false, true, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, false, true, false, true, true, true, false, true, false, true, false, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
def thInvI : List Nat := [45, 30, 32, 0, 29, 29, 31, 0, 33, 33, 46, 1, 47, 45, 46, 47, 35, 48, 35, 2, 49, 48, 49, 50, 37, 51, 52, 53, 54, 55, 56, 57, 39, 39, 50, 3, 51, 58, 59, 60, 52, 61, 5, 5, 9, 9, 6, 62, 53, 63, 64, 65, 13, 13, 14, 66, 67, 68, 7, 69, 11, 70, 71, 72, 41, 54, 41, 4, 55, 73, 74, 75, 56, 76, 77, 78, 17, 17, 18, 79, 57, 21, 80, 21, 25, 22, 26, 81, 82, 23, 83, 84, 19, 85, 86, 87, 43, 88, 89, 90, 91, 92, 93, 94, 95, 96, 8, 97, 12, 98, 99, 100, 101, 24, 102, 103, 16, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114]

def thInv (r : Fin 128) : Bool × Fin 115 :=
  (thInvB.getD r.val false, ⟨thInvI.getD r.val 0 % 115, Nat.mod_lt _ (by decide)⟩)

theorem thRow_inv : ∀ r : Fin 128, thRow (thInv r) = r := by decide +kernel

theorem th_restrict_inj {f g : Fin 128 → Bool} (h : restrict thRow f = restrict thRow g) : f = g := by
  funext r
  have := congrFun h (thInv r)
  simpa [restrict, thRow_inv] using this

theorem th_case_wire_spec (ci : Fin 13) :
    GoodWire 115 (thCaseWires.getD ci.val ⟨0,0,0⟩) ∧
    (∀ r : Bool × Fin 115, den 115 (thCaseWires.getD ci.val ⟨0,0,0⟩) r = caseWireVal ci (thRow r)) ∧
    (thetaStart ci).Nodup := by
  have h1 : ∀ c : Fin 13, GoodWire 115 (thCaseWires.getD c.val ⟨0,0,0⟩) := by decide +kernel
  have h2 : ∀ (c : Fin 13) (b : Bool) (j : Fin 115), den 115 (thCaseWires.getD c.val ⟨0,0,0⟩) (b, j) = caseWireVal c (thRow (b, j)) := by decide +kernel
  have h3 : ∀ c : Fin 13, (thetaStart c).Nodup := by decide +kernel
  exact ⟨h1 ci, fun ⟨b, j⟩ => h2 ci b j, h3 ci⟩

theorem th_ws_mem (w : Wire) (hw : w ∈ thWs) : ∃ i : Fin 7, thWs.getD i.val ⟨0,0,0⟩ = w := by
  have : ∀ x ∈ thWs, ∃ i : Fin 7, thWs.getD i.val ⟨0,0,0⟩ = x := by decide +kernel
  exact this w hw

theorem th_ws_getD_mem (i : Fin 7) : thWs.getD i.val ⟨0,0,0⟩ ∈ thWs := by
  revert i; decide +kernel

-- Dispatch table soundness:
def dispatchTag (a b : Fin 7) (op : Op) : Nat :=
  thDispatchTbl.getD (4 * (7 * a.val + b.val) + natOfOp op) 0

theorem dispatch_spec : ∀ (a b : Fin 7) (op : Op), a ≠ b →
    let tag := dispatchTag a b op
    if tag = 0 then 2 ≤ a.val ∧ (op = .conj ∨ op = .diffL)
    else if tag = 1 then 2 ≤ b.val ∧ (op = .conj ∨ op = .diffR)
    else
      let ci : Fin 13 := ⟨((tag - 2) / 4) % 13, Nat.mod_lt _ (by decide)⟩
      let s : Fin 4 := ⟨(tag - 2) % 4, Nat.mod_lt _ (by decide)⟩
      ∀ r : Fin 128, evalOp op (bit7 a (rowPerm s r)) (bit7 b (rowPerm s r)) = caseWireVal ci r := by
  intro a b op hab
  cases op <;> revert a b hab <;> decide +kernel

-- BST soundness: every entry `(kt, kf, rk, wa, wb, wop)` in `rankBST` satisfies
-- `(kt, kf)` is the exact `W_th`-bit projection of `evalOp (opOfNat wop) (bit7 wa) (bit7 wb)`
-- AND its `dispatchTag` matches `rk` (`rk = 0` -> absorbing; `rk = ci + 1` -> orbit `ci`)!
def BST.valid : BST → Bool
  | .leaf => true
  | .node kt kf rk wa wb wop l r =>
    if wa >= 7 || wb >= 7 || wa == wb || wop >= 4 then false
    else
      let wA := thWs.getD wa ⟨0,0,0⟩
      let wB := thWs.getD wb ⟨0,0,0⟩
      let tf := match wop with
        | 0 => op0 wA wB
        | 1 => op1 wA wB
        | 2 => op2 thAll wA wB
        | _ => op3 thAll wA wB
      let tag := thDispatchTbl.getD (4 * (7 * wa + wb) + wop) 0
      let rkOk := if rk == 0 then tag < 2 else (tag >= 2 && ((tag - 2) / 4) % 13 + 1 == rk)
      (tf.1 == kt) && (tf.2 == kf) && rkOk && l.valid && r.valid

theorem rankBST_valid : rankBST.valid = true := by decide +kernel

theorem bst_lookup_witness : ∀ (tree : BST) (t f : Nat),
    tree.valid = true → tree.lookup t f < 99 →
    ∃ wa wb : Fin 7, ∃ op : Op, wa ≠ wb ∧
      (let wA := thWs.getD wa.val ⟨0,0,0⟩
       let wB := thWs.getD wb.val ⟨0,0,0⟩
       let tf := match op with
         | .conj => op0 wA wB
         | .disj => op1 wA wB
         | .diffL => op2 thAll wA wB
         | .diffR => op3 thAll wA wB
       tf.1 = t ∧ tf.2 = f) ∧
      (if tree.lookup t f = 0 then dispatchTag wa wb op < 2
       else 2 ≤ dispatchTag wa wb op ∧ ((dispatchTag wa wb op - 2) / 4) % 13 + 1 = tree.lookup t f) := by
  intro tree t f hval hlt
  induction tree with
  | leaf => simp [BST.lookup] at hlt
  | node kt kf rk wa wb wop l r ihl ihr =>
    simp only [BST.valid] at hval
    split at hval
    · cases hval
    · rename_i hok
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or, not_le] at hok
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hval
      rcases hval with ⟨⟨⟨⟨hteq, hfeq⟩, hrkok⟩, hlval⟩, hrval⟩
      simp only [BST.lookup] at hlt ⊢
      split at hlt
      · rename_i h1; simp only [h1, ↓reduceIte]; exact ihl hlval hlt
      · split at hlt
        · rename_i h1 h2; simp only [h1, h2, ↓reduceIte]; exact ihr hrval hlt
        · split at hlt
          · rename_i h1 h2 h3
            simp only [h1, h2, h3, ↓reduceIte]
            have htk : t = kt := by omega
            have hfk : f = kf := beq_iff_eq.mp h3
            refine ⟨⟨wa, hok.1.1.1⟩, ⟨wb, hok.1.1.2⟩, opOfNat wop, fun e => hok.1.2 (congrArg Fin.val e), ?_, ?_⟩
            · have hw4 : wop < 4 := hok.2
              rcases wop with _ | _ | _ | _ | k
              · exact ⟨hteq.trans htk.symm, hfeq.trans hfk.symm⟩
              · exact ⟨hteq.trans htk.symm, hfeq.trans hfk.symm⟩
              · exact ⟨hteq.trans htk.symm, hfeq.trans hfk.symm⟩
              · exact ⟨hteq.trans htk.symm, hfeq.trans hfk.symm⟩
              · omega
            · have hnop : natOfOp (opOfNat wop) = wop := by
                have hw4 : wop < 4 := hok.2
                rcases wop with _ | _ | _ | _ | k
                · rfl
                · rfl
                · rfl
                · rfl
                · omega
              simp only [dispatchTag, hnop]
              by_cases hr0 : rk = 0
              · simp only [hr0, ↓reduceIte]
                simpa [hr0] using hrkok
              · simp only [hr0, ↓reduceIte]
                simpa [hr0] using hrkok
          · simp at hlt

-- MAIN THEOREM OF SECTION 5: U2(Theta(2,3,3)) ≥ 11!
theorem theta_lower : ∀ n ≤ 10, ∀ ws, Free verts7 n ws → thAns ∈ ws → False := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihN =>
    intro hn10 ws hrun hout
    -- Helper: prove no trace of length <= n starts with caseWireVal ci (by strong induction on ci):
    have hnoCase : ∀ (ci : Nat) (hci : ci < 13),
        ¬ ∃ tail : List (TGate (Fin 128)), tail.length + 1 ≤ n ∧
            Sufficient (caseWireVal ⟨ci, hci⟩ :: verts7) thAns tail := by
      intro ci
      induction ci using Nat.strongRecOn with
      | ind ci ihC =>
        intro hci ⟨tail, hlen, hs⟩
        let fci : Fin 13 := ⟨ci, hci⟩
        -- Step 1: check if any gate in tail has rankBST.lookup < ci + 1
        let forbid128 : (Fin 128 → Bool) → Prop := fun f =>
          ∃ w : Wire, GoodWire 115 w ∧ den 115 w = restrict thRow f ∧ rankBST.lookup w.t w.f < ci + 1
        by_cases hbad : ∃ t ∈ tail, forbid128 t.val
        · obtain ⟨t, ht, w, hgw, hdw, hrk⟩ := hbad
          obtain ⟨wa, wb, op, hwab, htf, htag⟩ := bst_lookup_witness rankBST w.t w.f rankBST_valid (by omega)
          have htval : t.val = fun r => evalOp op (bit7 wa r) (bit7 wb r) := by
            apply th_restrict_inj
            rw [← hdw]
            have hA := th_ws_good wa; have hB := th_ws_good wb
            let wA := thWs.getD wa.val ⟨0,0,0⟩
            let wB := thWs.getD wb.val ⟨0,0,0⟩
            cases op
            · have h0 := good_op0 hA.1 hB.1
              have heq : (⟨(op0 wA wB).1, (op0 wA wB).2, (op0 wA wB).1 ^^^ (op0 wA wB).2⟩ : Wire) = w := by
                cases w; simp only [GoodWire] at hgw; simp only [Wire.mk.injEq]; exact ⟨htf.1, htf.2, by rw [hgw.2.2, htf.1, htf.2]⟩
              rw [← heq, h0.2]; funext r; simp only [restrict]; rw [hA.2 r, hB.2 r]
            · have h1 := good_op1 hA.1 hB.1
              have heq : (⟨(op1 wA wB).1, (op1 wA wB).2, (op1 wA wB).1 ^^^ (op1 wA wB).2⟩ : Wire) = w := by
                cases w; simp only [GoodWire] at hgw; simp only [Wire.mk.injEq]; exact ⟨htf.1, htf.2, by rw [hgw.2.2, htf.1, htf.2]⟩
              rw [← heq, h1.2]; funext r; simp only [restrict]; rw [hA.2 r, hB.2 r]
            · have h2 := good_op2 hA.1 hB.1
              have heq : (⟨(op2 (2 ^ 115 - 1) wA wB).1, (op2 (2 ^ 115 - 1) wA wB).2, (op2 (2 ^ 115 - 1) wA wB).1 ^^^ (op2 (2 ^ 115 - 1) wA wB).2⟩ : Wire) = w := by
                cases w; simp only [GoodWire] at hgw; simp only [Wire.mk.injEq]; rw [← thAll_eq]; exact ⟨htf.1, htf.2, by rw [hgw.2.2, htf.1, htf.2]⟩
              rw [← heq, h2.2]; funext r; simp only [restrict]; rw [hA.2 r, hB.2 r]
            · have h3 := good_op3 hA.1 hB.1
              have heq : (⟨(op3 (2 ^ 115 - 1) wA wB).1, (op3 (2 ^ 115 - 1) wA wB).2, (op3 (2 ^ 115 - 1) wA wB).1 ^^^ (op3 (2 ^ 115 - 1) wA wB).2⟩ : Wire) = w := by
                cases w; simp only [GoodWire] at hgw; simp only [Wire.mk.injEq]; rw [← thAll_eq]; exact ⟨htf.1, htf.2, by rw [hgw.2.2, htf.1, htf.2]⟩
              rw [← heq, h3.2]; funext r; simp only [restrict]; rw [hA.2 r, hB.2 r]
          -- Build a full trace of length <= n starting with `caseWireVal fci` and moving `t` (replaced by raw gate `t0`) to front!
          let g0 : TGate (Fin 128) :=
            ⟨opOfNat (thCasesOp.getD ci 0), bit7 ⟨thCasesA.getD ci 0 % 7, Nat.mod_lt _ (by decide)⟩,
             bit7 ⟨thCasesB.getD ci 0 % 7, Nat.mod_lt _ (by decide)⟩⟩
          have hs_full : Sufficient verts7 thAns (g0 :: tail) :=
            ⟨⟨List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨_, rfl⟩),
              List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨_, rfl⟩), hs.1⟩, hs.2⟩
          -- Replace `t` inside `g0 :: tail` with `t0 := ⟨op, bit7 wa, bit7 wb⟩`? No, move `t` directly?
          -- Wait: `t` itself might not have `t.lhs = bit7 wa`, it only has `t.val = t0.val`!
          -- Even cleaner: prepend `t0` to `verts7` and drop `t` from `tail`!
          -- Since `t.val = t0.val ∈ t0.val :: verts7`, `valid_sub` replaces `t.val` by `t0.val` AND drops `t`!
          let t0 : TGate (Fin 128) := ⟨op, bit7 wa, bit7 wb⟩
          have ht0_val : t0.val = t.val := htval.symm
          have hdrop_t : ∃ rest : List (TGate (Fin 128)), rest.length + 1 ≤ (g0 :: tail).length ∧
              Sufficient (t0.val :: verts7) thAns rest := by
            -- prove by deleting `t` from `g0 :: tail` (since `t ∈ tail`, `t.val = t0.val` is already in `t0.val :: verts7`!)
            have hdel : ∀ (raw : List (Fin 128 → Bool)) (gs : List (TGate (Fin 128))),
                Sufficient raw thAns gs → t ∈ gs →
                ∃ rs, rs.length + 1 ≤ gs.length ∧ Sufficient (t.val :: raw) thAns rs := by
              intro raw gs hsg htg
              induction gs generalizing raw with
              | nil => cases htg
              | cons q qs ihq =>
                rcases hsg with ⟨⟨ql, qr, qv⟩, qout⟩
                rcases List.mem_cons.mp htg with rfl | htg'
                · exact ⟨qs, Nat.le_refl _, ⟨qv, qout⟩⟩
                · obtain ⟨rs, hrlen, hrs⟩ := ihq (q.val :: raw) ⟨qv, qout⟩ htg'
                  have hsub : ∀ u, u ∈ t.val :: q.val :: raw → u ∈ q.val :: t.val :: raw := by
                    intro u hu
                    rcases List.mem_cons.mp hu with rfl | hu
                    · exact List.mem_cons_of_mem _ List.mem_cons_self
                    · rcases List.mem_cons.mp hu with rfl | hu
                      · exact List.mem_cons_self
                      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu)
                  obtain ⟨hv2, hb2⟩ := valid_sub hsub hrs.1
                  exact ⟨q :: rs, by simp; omega, ⟨⟨List.mem_cons_of_mem _ ql, List.mem_cons_of_mem _ qr, hv2⟩, hb2 _ hrs.2⟩⟩
            obtain ⟨rs, hrlen, hrs⟩ := hdel verts7 (g0 :: tail) hs_full (List.mem_cons_of_mem _ ht)
            exact ⟨rs, hrlen, ht0_val ▸ hrs⟩
          obtain ⟨rest, hrest_len, hrest_s⟩ := hdrop_t
          have hrest_n : rest.length + 1 ≤ n := by simp at hrest_len; omega
          have ht0_s : Sufficient verts7 thAns (t0 :: rest) :=
            ⟨⟨List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨wa, rfl⟩),
              List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨wb, rfl⟩), hrest_s.1⟩, hrest_s.2⟩
          by_cases hrk0 : rankBST.lookup w.t w.f = 0
          · -- Absorbing raw gate!
            simp only [hrk0, ↓reduceIte] at htag
            obtain ⟨ts, hts_len, hts_s, hts_f⟩ := simplify_trace ht0_s
            by_cases hlt_n : ts.length < n
            · exact ihN ts.length hlt_n (by omega) _ (free_of_trace hts_s.1 (fun _ _ h => h)) hts_s.2
            · -- Wait: `ts` might have dropped `t0` ONLY if `t0.val ∈ verts7` (which shrinks length < n!).
              -- So if `ts.length ≥ n`, then `t0.val ∉ verts7`, so `ts = t0 :: ts'`!
              -- Even simpler: simplify `rest` under `t0.val :: verts7`!
              obtain ⟨ts', hts'_len, hts'_s, hts'_f⟩ := simplify_trace hrest_s
              by_cases ht0_in : t0.val ∈ verts7
              · have hsub : ∀ u, u ∈ t0.val :: verts7 → u ∈ verts7 := fun u hu => by
                  rcases List.mem_cons.mp hu with rfl | hu; exact ht0_in; exact hu
                obtain ⟨hv2, hb2⟩ := valid_sub hsub hts'_s.1
                exact ihN ts'.length (by omega) (by omega) _ (free_of_trace hv2 (fun _ _ h => h)) (hb2 _ hts'_s.2)
              · have hfull_s : Sufficient verts7 thAns (t0 :: ts') :=
                  ⟨⟨List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨wa, rfl⟩),
                    List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨wb, rfl⟩), hts'_s.1⟩, hts'_s.2⟩
                have hfull_f : FreshTrace verts7 (t0 :: ts') := ⟨ht0_in, hts'_f⟩
                have hspec := dispatch_spec wa wb op hwab
                by_cases ht00 : dispatchTag wa wb op = 0
                · simp only [ht00, ↓reduceIte] at hspec
                  obtain ⟨sh, hsh_len, hsh_s⟩ := th_absorbing_head hwab hspec.1 (Or.inl ⟨rfl, rfl, hspec.2⟩) hfull_s hfull_f (by simp; omega)
                  exact ihN sh.length (by omega) (by omega) _ (free_of_trace hsh_s.1 (fun _ _ h => h)) hsh_s.2
                · have ht01 : dispatchTag wa wb op = 1 := by omega
                  simp only [ht01, ↓reduceIte] at hspec
                  obtain ⟨sh, hsh_len, hsh_s⟩ := th_absorbing_head (Ne.symm hwab) hspec.1 (Or.inr ⟨rfl, rfl, hspec.2⟩) hfull_s hfull_f (by simp; omega)
                  exact ihN sh.length (by omega) (by omega) _ (free_of_trace hsh_s.1 (fun _ _ h => h)) hsh_s.2
          · -- Orbit rank `rk' = rankBST.lookup w.t w.f - 1 < ci`!
            simp only [hrk0, ↓reduceIte] at htag
            have hspec := dispatch_spec wa wb op hwab
            have hne0 : dispatchTag wa wb op ≠ 0 := by omega
            have hne1 : dispatchTag wa wb op ≠ 1 := by omega
            simp only [hne0, hne1, ↓reduceIte] at hspec
            let ci' : Nat := ((dispatchTag wa wb op - 2) / 4) % 13
            let s : Fin 4 := ⟨(dispatchTag wa wb op - 2) % 4, Nat.mod_lt _ (by decide)⟩
            have hci'_lt : ci' < ci := by omega
            have hci'_13 : ci' < 13 := Nat.mod_lt _ (by decide)
            -- Permute `rest` by `rowPerm s`!
            have hperm_run := free_map_restrict (rowPerm s) (free_of_trace hrest_s.1 (fun _ _ h => h)) (forbid2 := fun _ => False) (fun _ h => h)
            have hsub_p : ∀ u, u ∈ (t0.val :: verts7).map (restrict (rowPerm s)) →
                u ∈ caseWireVal ⟨ci', hci'_13⟩ :: verts7 := by
              intro u hu
              rw [List.map_cons] at hu
              rcases List.mem_cons.mp hu with rfl | hu
              · have heq : restrict (rowPerm s) t0.val = caseWireVal ⟨ci', hci'_13⟩ := funext hspec
                rw [heq]; exact List.mem_cons_self
              · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
                rcases List.mem_cons.mp hv with rfl | hv
                · exact List.mem_cons_of_mem _ List.mem_cons_self
                · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
                  have heq : restrict (rowPerm s) (bit7 j) = bit7 (permPos s j) := funext (rowPerm_bit s j)
                  rw [heq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨permPos s j, rfl⟩))
            obtain ⟨ws', hrun', hsub'⟩ := free_mono hsub_p hperm_run
            obtain ⟨ts', hts'_len, hts'_v, hts'_b⟩ := trace_of_free hrun'
            have hans_in : thAns ∈ traceBank (caseWireVal ⟨ci', hci'_13⟩ :: verts7) ts' := by
              have heq : restrict (rowPerm s) thAns = thAns := funext (rowPerm_ans s)
              apply hts'_b; rw [← heq]; exact hsub' _ (List.mem_map.mpr ⟨thAns, hrest_s.2, rfl⟩)
            exact ihC ci' hci'_lt hci'_13 ⟨ts', by omega, hts'_v, hans_in⟩
        · -- Step 2: NO gate in `tail` has `rankBST.lookup < ci + 1`! Run `rewind` + `search_complete`!
          have hnf : ∀ t ∈ tail, ¬ forbid128 t.val := fun t ht h => hbad ⟨t, ht, h⟩
          have hfr := free_of_trace hs.1 hnf
          let forbidRow : (Bool × Fin 115 → Bool) → Prop := fun f =>
            ∃ w : Wire, GoodWire 115 w ∧ den 115 w = f ∧ rankBST.lookup w.t w.f < ci + 1
          have hmap := free_map_restrict thRow hfr (forbid2 := forbidRow) (fun f ⟨w, hgw, hdw, hrk⟩ => ⟨w, hgw, hdw, hrk⟩)
          have h0 : constF ∈ (caseWireVal fci :: verts7).map (restrict thRow) :=
            List.mem_map.mpr ⟨constF, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
          have htgt : targetDen 115 ∈ (traceBank (caseWireVal fci :: verts7) tail).map (restrict thRow) := by
            have : restrict thRow thAns = targetDen 115 := funext th_row_ans
            rw [← this]; exact List.mem_map.mpr ⟨thAns, hs.2, rfl⟩
          obtain ⟨m, S, hmlen, hl, hsub⟩ := rewind h0 hmap htgt
          have hno0 : ¬ S constF := hl.no_constF (fun e => by have := congrFun e (true, ⟨0, by decide⟩); simp [targetDen, constF] at this)
          by_cases hcase_in : S (restrict thRow (caseWireVal fci))
          · -- All 7 primary variables MUST also be in S!
            have hraw_in : ∀ i : Fin 7, S (restrict thRow (bit7 i)) := by
              intro i
              let a0 : Fin 7 := ⟨thCasesA.getD ci 0 % 7, Nat.mod_lt _ (by decide)⟩
              let b0 : Fin 7 := ⟨thCasesB.getD ci 0 % 7, Nat.mod_lt _ (by decide)⟩
              let op0_c := opOfNat (thCasesOp.getD ci 0)
              have hne_ab : a0 ≠ b0 := by
                have : ∀ c : Fin 13, thCasesA.getD c.val 0 % 7 ≠ thCasesB.getD c.val 0 % 7 := by decide +kernel
                intro e; exact this fci (congrArg Fin.val e)
              -- Find a pair `(lo, hi)` where ONLY `bit7 i` flips AND `caseWireVal fci` agrees!
              have hpair : ∃ r s : Fin 128, thAns r ≠ thAns s ∧ caseWireVal fci r = caseWireVal fci s ∧
                  ∀ z : Fin 7, z ≠ i → bit7 z r = bit7 z s := by
                have hcw (r : Fin 128) : caseWireVal fci r = evalOp op0_c (bit7 a0 r) (bit7 b0 r) := rfl
                by_cases hia : i = a0
                · obtain ⟨bv, hmask⟩ := op_masks_left op0_c
                  obtain ⟨lx, hx, ly, hy, hout, hfix⟩ := th_sens_spec a0 b0 hne_ab bv
                  exact ⟨thLo a0 b0 bv, thHi a0 b0 bv, hout, by rw [hcw, hcw, lx, hx, ly, hy]; exact hmask false true, fun z hz => hfix z (hia ▸ hz)⟩
                · by_cases hib : i = b0
                  · have hmask : ∃ bv : Bool, ∀ c1 c2 : Bool, evalOp op0_c bv c1 = evalOp op0_c bv c2 := by
                      cases op0_c <;> [exact ⟨false, by decide⟩; exact ⟨true, by decide⟩; exact ⟨false, by decide⟩; exact ⟨true, by decide⟩]
                    obtain ⟨bv, hm⟩ := hmask
                    obtain ⟨ly, hy, lx, hx, hout, hfix⟩ := th_sens_spec b0 a0 (Ne.symm hne_ab) bv
                    exact ⟨thLo b0 a0 bv, thHi b0 a0 bv, hout, by rw [hcw, hcw, lx, hx, ly, hy]; exact hm false true, fun z hz => hfix z (hib ▸ hz)⟩
                  · obtain ⟨_, _, _, _, hout, hfix⟩ := th_sens_spec i a0 hia false
                    refine ⟨thLo i a0 false, thHi i a0 false, hout, ?_, hfix⟩
                    rw [hcw, hcw, hfix a0 (Ne.symm hia), hfix b0 (Ne.symm hib)]
              obtain ⟨r, s, hout, hc_eq, hfix⟩ := hpair
              have htd : targetDen 115 (thInv r) ≠ targetDen 115 (thInv s) := by
                have h1 := th_row_ans (thInv r); have h2 := th_row_ans (thInv s)
                rw [thRow_inv] at h1 h2
                simpa [targetDen, ← h1, ← h2] using hout
              obtain ⟨g, hgS, hgsep⟩ := hl.separates htd
              obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (hsub g hgS)
              rcases List.mem_cons.mp hu with rfl | hu
              · exact (hgsep (by simpa [restrict, thRow_inv] using hc_eq)).elim
              · rcases List.mem_cons.mp hu with rfl | hu
                · exact (hgsep rfl).elim
                · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
                  by_cases hji : j = i
                  · subst hji; exact hgS
                  · exact (hgsep (by simpa [restrict, thRow_inv] using hfix j hji)).elim
            -- Now `Rep W_th (thetaStart fci) S` holds!
            have hrep : Rep 115 (thetaStart fci) S := by
              obtain ⟨hcg, hcd, hcnd⟩ := th_case_wire_spec fci
              refine ⟨hcnd, ?_, ?_⟩
              · intro w hw
                rcases List.mem_cons.mp hw with rfl | hw
                · exact hcg
                · obtain ⟨i, rfl⟩ := th_ws_mem w hw; exact (th_ws_good i).1
              · intro f; constructor
                · intro hf
                  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (hsub f hf)
                  rcases List.mem_cons.mp hu with rfl | hu
                  · exact ⟨thCaseWires.getD ci ⟨0,0,0⟩, List.mem_cons_self, funext hcd⟩
                  · rcases List.mem_cons.mp hu with rfl | hu
                    · exact (hno0 hf).elim
                    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
                      exact ⟨thWs.getD i.val ⟨0,0,0⟩, List.mem_cons_of_mem _ (th_ws_getD_mem i), funext (th_ws_good i).2⟩
                · rintro ⟨w, hw, rfl⟩
                  rcases List.mem_cons.mp hw with rfl | hw
                  · rw [funext hcd]; exact hcase_in
                  · obtain ⟨i, rfl⟩ := th_ws_mem w hw
                    rw [funext (th_ws_good i).2]; exact hraw_in i
            have hs_true := search_complete (W := 115) (bound := ci + 1)
              (fun w hgw _ hrk => ⟨w, hgw, rfl, hrk⟩) (by omega : m ≤ 9) hl hrep
            rw [← thAll_eq] at hs_true
            have hfalse := theta_case_all fci
            rw [hfalse] at hs_true; cases hs_true
          · -- `caseWireVal fci` is NOT in `S`! Pull back via `thInv` to a `Free verts7 m` with `m < n` -> `ihN`!
            obtain ⟨ws_row, hrun_row, htgt_row⟩ := free_of_live hl (raw := verts7.map (restrict thRow)) (by
              intro w hw
              obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (hsub w hw)
              rcases List.mem_cons.mp hu with rfl | hu
              · exact (hcase_in hw).elim
              · exact List.mem_map.mpr ⟨u, hu, rfl⟩)
            have hback := free_map_restrict thInv hrun_row (forbid2 := fun _ => False) (fun _ h => h.elim)
            have hsub_back : ∀ u, u ∈ (verts7.map (restrict thRow)).map (restrict thInv) → u ∈ verts7 := by
              intro u hu
              obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
              obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
              have heq : restrict thInv (restrict thRow w) = w := funext fun r => by simp [restrict, thRow_inv]
              rw [heq]; exact hw
            obtain ⟨ws_128, hrun_128, hsub_128⟩ := free_mono hsub_back hback
            have hans_128 : thAns ∈ ws_128 := by
              have heq : restrict thInv (targetDen 115) = thAns := funext fun r => by
                have := th_row_ans (thInv r); rw [thRow_inv] at this; simpa [restrict, targetDen] using this.symm
              rw [← heq]; exact hsub_128 _ (List.mem_map.mpr ⟨targetDen 115, htgt_row, rfl⟩)
            exact ihN m (by omega) (by omega) ws_128 hrun_128 hans_128
    -- Now main body of `theta_lower` for size `n ≤ 10`:
    obtain ⟨gs, hglen, hgv, hgb⟩ := trace_of_free hrun
    obtain ⟨ts, hts_len, hts_s, hts_f⟩ := simplify_trace ⟨hgv, hgb _ hout⟩
    cases ts with
    | nil => exact th_ans_not_raw hts_s.2
    | cons g tail =>
      obtain ⟨hnl, hnr, hneq⟩ := fresh_head_distinct_inputs List.mem_cons_self hts_s.1 hts_f
      have hgl : ∃ a : Fin 7, g.lhs = bit7 a := by
        rcases List.mem_cons.mp hts_s.1.1 with h0 | h1
        · exact (hnl h0).elim
        · obtain ⟨a, ha⟩ := List.mem_ofFn.mp h1; exact ⟨a, ha.symm⟩
      have hgr : ∃ b : Fin 7, g.rhs = bit7 b := by
        rcases List.mem_cons.mp hts_s.1.2.1 with h0 | h1
        · exact (hnr h0).elim
        · obtain ⟨b, hb⟩ := List.mem_ofFn.mp h1; exact ⟨b, hb.symm⟩
      obtain ⟨a, ha⟩ := hgl; obtain ⟨b, hb⟩ := hgr
      have hab : a ≠ b := fun e => hneq (by rw [ha, hb, e])
      have hspec := dispatch_spec a b g.op hab
      by_cases ht0 : dispatchTag a b g.op = 0
      · simp only [ht0, ↓reduceIte] at hspec
        obtain ⟨sh, hsh_len, hsh_s⟩ := th_absorbing_head hab hspec.1 (Or.inl ⟨ha, hb, hspec.2⟩) hts_s hts_f (by omega)
        exact ihN sh.length (by simp at hts_len; omega) (by simp at hts_len; omega) _ (free_of_trace hsh_s.1 (fun _ _ h => h)) hsh_s.2
      · by_cases ht1 : dispatchTag a b g.op = 1
        · simp only [ht1, ↓reduceIte] at hspec
          obtain ⟨sh, hsh_len, hsh_s⟩ := th_absorbing_head (Ne.symm hab) hspec.1 (Or.inr ⟨ha, hb, hspec.2⟩) hts_s hts_f (by omega)
          exact ihN sh.length (by simp at hts_len; omega) (by simp at hts_len; omega) _ (free_of_trace hsh_s.1 (fun _ _ h => h)) hsh_s.2
        · simp only [ht0, ht1, ↓reduceIte] at hspec
          let ci : Nat := ((dispatchTag a b g.op - 2) / 4) % 13
          let s : Fin 4 := ⟨(dispatchTag a b g.op - 2) % 4, Nat.mod_lt _ (by decide)⟩
          have hci13 : ci < 13 := Nat.mod_lt _ (by decide)
          have hperm := free_map_restrict (rowPerm s) (free_of_trace hts_s.1.2.2 (fun _ _ h => h)) (forbid2 := fun _ => False) (fun _ h => h)
          have hsub_p : ∀ u, u ∈ (g.val :: verts7).map (restrict (rowPerm s)) →
              u ∈ caseWireVal ⟨ci, hci13⟩ :: verts7 := by
            intro u hu
            rw [List.map_cons] at hu
            rcases List.mem_cons.mp hu with rfl | hu
            · have heq : restrict (rowPerm s) g.val = caseWireVal ⟨ci, hci13⟩ := funext fun r => by
                simpa [restrict, TGate.val, ha, hb] using hspec r
              rw [heq]; exact List.mem_cons_self
            · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
              rcases List.mem_cons.mp hv with rfl | hv
              · exact List.mem_cons_of_mem _ List.mem_cons_self
              · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
                have heq : restrict (rowPerm s) (bit7 j) = bit7 (permPos s j) := funext (rowPerm_bit s j)
                rw [heq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨permPos s j, rfl⟩))
          obtain ⟨ws', hrun', hsub'⟩ := free_mono hsub_p hperm
          obtain ⟨ts', hts'_len, hts'_v, hts'_b⟩ := trace_of_free hrun'
          have hans_in : thAns ∈ traceBank (caseWireVal ⟨ci, hci13⟩ :: verts7) ts' := by
            have heq : restrict (rowPerm s) thAns = thAns := funext (rowPerm_ans s)
            apply hts'_b; rw [← heq]; exact hsub' _ (List.mem_map.mpr ⟨thAns, hts_s.2, rfl⟩)
          exact hnoCase ci hci13 ⟨ts', by simp at hts_len; omega, hts'_v, hans_in⟩

/-! ### Section 6: P9 ≥ 14 (`p9_lower`) -/

def p9Partners : List Nat := [4, 6, 7, 4, 0, 7, 1, 2, 6]
def p9Embs : List (List Nat) := [[2, 8, 3, 1, 6, 7, 5], [3, 5, 8, 2, 7, 4, 0], [0, 8, 5, 1, 6, 4, 3], [1, 5, 0, 2, 7, 6, 8], [2, 8, 3, 1, 6, 7, 5], [1, 3, 2, 0, 4, 6, 8], [3, 5, 8, 2, 7, 4, 0], [0, 8, 5, 1, 6, 4, 3], [0, 2, 1, 4, 3, 5, 7]]
def p9SensSeeds : List Nat := [0, 0, 16, 2, 2, 20, 2, 10, 2, 16, 2, 32, 2, 80, 2, 130, 2, 258, 4, 1, 0, 0, 1, 4, 1, 9, 1, 20, 1, 36, 1, 64, 1, 129, 1, 257, 2, 9, 8, 2, 0, 0, 2, 8, 2, 18, 2, 34, 2, 72, 2, 128, 2, 258, 4, 5, 4, 18, 16, 4, 0, 0, 4, 16, 4, 36, 4, 68, 4, 144, 4, 256, 8, 1, 1, 10, 1, 5, 1, 8, 0, 0, 1, 40, 1, 65, 1, 129, 1, 257, 128, 1, 1, 130, 1, 5, 1, 9, 1, 144, 0, 0, 1, 65, 1, 128, 1, 256, 2, 257, 256, 2, 2, 260, 2, 10, 2, 18, 2, 34, 0, 0, 2, 130, 2, 256, 4, 5, 4, 34, 32, 4, 4, 40, 4, 20, 4, 32, 4, 68, 0, 0, 4, 260, 8, 9, 8, 10, 8, 36, 32, 8, 8, 48, 8, 32, 8, 64, 8, 136, 0, 0]

def p9Partner (a : Fin 9) : Fin 9 :=
  ⟨p9Partners.getD a.val 0 % 9, Nat.mod_lt _ (by decide)⟩

def p9Lift (a : Fin 9) (r : Fin 128) : Fin 512 :=
  ⟨plantBits (p9Embs.getD a.val []) r.val % 512, Nat.mod_lt _ (by decide)⟩

theorem p9_partner_ne : ∀ a : Fin 9, a ≠ p9Partner a := by decide +kernel
theorem p9_lift_off_a : ∀ (a : Fin 9) (r : Fin 128), bit9 a (p9Lift a r) = false := by decide +kernel
theorem p9_lift_off_c : ∀ (a : Fin 9) (r : Fin 128), bit9 (p9Partner a) (p9Lift a r) = false := by decide +kernel
theorem p9_lift_ans : ∀ (a : Fin 9) (r : Fin 128), p9Ans (p9Lift a r) = thAns r := by decide +kernel

theorem p9_lift_bit_in : ∀ (a y : Fin 9),
    (∀ r : Fin 128, bit9 y (p9Lift a r) = false) ∨
    ∃ j : Fin 7, ∀ r : Fin 128, bit9 y (p9Lift a r) = bit7 j r := by decide +kernel

def p9Lo (x y : Fin 9) (b : Bool) : Fin 512 :=
  ⟨p9SensSeeds.getD (2 * (9 * x.val + y.val) + b.toNat) 0 % 512, Nat.mod_lt _ (by decide)⟩
def p9Hi (x y : Fin 9) (b : Bool) : Fin 512 :=
  ⟨((p9Lo x y b).val ||| (1 <<< x.val)) % 512, Nat.mod_lt _ (by decide)⟩

theorem p9_sens_spec : ∀ (x y : Fin 9), x ≠ y → ∀ b : Bool,
    bit9 x (p9Lo x y b) = false ∧ bit9 x (p9Hi x y b) = true ∧
    bit9 y (p9Lo x y b) = b ∧ bit9 y (p9Hi x y b) = b ∧
    p9Ans (p9Lo x y b) ≠ p9Ans (p9Hi x y b) ∧
    ∀ z : Fin 9, z ≠ x → bit9 z (p9Lo x y b) = bit9 z (p9Hi x y b) := by decide +kernel

theorem p9_bit_inj (x y : Fin 9) (h : bit9 x = bit9 y) : x = y := by
  by_contra hne
  have hex : ∀ a b : Fin 9, a ≠ b → ∃ r : Fin 512, bit9 a r ≠ bit9 b r := by decide +kernel
  obtain ⟨r, hr⟩ := hex x y hne
  exact hr (congrFun h r)

theorem p9_ans_ne_bit (x : Fin 9) : p9Ans ≠ bit9 x := by
  have hex : ∀ a : Fin 9, ∃ r : Fin 512, p9Ans r ≠ bit9 a r := by decide +kernel
  obtain ⟨r, hr⟩ := hex x
  exact fun e => hr (congrFun e r)

theorem p9_ans_not_raw : p9Ans ∉ verts9 := by
  intro h
  rcases List.mem_cons.mp h with h0 | h1
  · have := congrFun h0 ⟨3, by decide⟩; revert this; decide
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp h1; exact p9_ans_ne_bit i hi.symm

theorem p9_read_twice {g : TGate (Fin 512)} {tail : List (TGate (Fin 512))}
    {x y : Fin 9} (hxy : x ≠ y)
    (hlhs : g.lhs = bit9 x) (hrhs : g.rhs = bit9 y)
    (hs : Sufficient verts9 p9Ans (g :: tail)) :
    ∃ h ∈ tail, reads h (bit9 x) := by
  obtain ⟨b, hmask⟩ := op_masks_left g.op
  obtain ⟨lx, hx, ly, hy, hout, hfix⟩ := p9_sens_spec x y hxy b
  apply second_reader hs (p9_ans_ne_bit x) (p9Lo x y b) (p9Hi x y b) hout
  · simp [TGate.val, hlhs, hrhs, lx, hx, ly, hy, hmask false true]
  · intro w hw hne
    rcases List.mem_cons.mp hw with rfl | hw
    · rfl
    · obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hw
      exact hfix z (fun e => hne (congrArg bit9 e))

theorem p9_exists_reader (c : Fin 9) {gs : List (TGate (Fin 512))}
    (hs : Sufficient verts9 p9Ans gs) : ∃ r ∈ gs, reads r (bit9 c) := by
  let other : Fin 9 := if c = 0 then 1 else 0
  have hne : c ≠ other := by by_cases hc : c = 0 <;> simp [other, hc]
  obtain ⟨_, _, _, _, hout, hfix⟩ := p9_sens_spec c other hne false
  apply exists_reader hs (p9_ans_ne_bit c) (p9Lo c other false) (p9Hi c other false) hout
  intro w hw hne'
  rcases List.mem_cons.mp hw with rfl | hw
  · rfl
  · obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hw
    exact hfix z (fun e => hne' (congrArg bit9 e))

theorem p9_lift_lower (a : Fin 9) {m ws}
    (hrun : Free (verts9.map (restrict (p9Lift a))) m ws)
    (hout : restrict (p9Lift a) p9Ans ∈ ws) : 11 ≤ m := by
  by_contra hlt
  have hsub : ∀ w, w ∈ verts9.map (restrict (p9Lift a)) → w ∈ verts7 := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    rcases List.mem_cons.mp hu with rfl | hu
    · exact List.mem_cons_self
    · obtain ⟨y, rfl⟩ := List.mem_ofFn.mp hu
      rcases p9_lift_bit_in a y with h0 | ⟨j, hj⟩
      · have : restrict (p9Lift a) (bit9 y) = constF := funext h0
        rw [this]; exact List.mem_cons_self
      · have : restrict (p9Lift a) (bit9 y) = bit7 j := funext hj
        rw [this]; exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  obtain ⟨ws', hrun', hsub'⟩ := free_mono hsub hrun
  have heq : restrict (p9Lift a) p9Ans = thAns := funext (p9_lift_ans a)
  exact theta_lower m (by omega) ws' hrun' (heq ▸ hsub' _ hout)

theorem p9_lower : ∀ n ≤ 13, ∀ ws, Free verts9 n ws → p9Ans ∈ ws → False := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihN =>
    intro hn13 ws hrun hout
    obtain ⟨gs, hglen, hgv, hgb⟩ := trace_of_free hrun
    obtain ⟨ts, hts_len, hts_s, hts_f⟩ := simplify_trace ⟨hgv, hgb _ hout⟩
    cases ts with
    | nil => exact p9_ans_not_raw hts_s.2
    | cons g tail =>
      obtain ⟨hnl, hnr, hneq⟩ := fresh_head_distinct_inputs List.mem_cons_self hts_s.1 hts_f
      have hgl : ∃ a : Fin 9, g.lhs = bit9 a := by
        rcases List.mem_cons.mp hts_s.1.1 with h0 | h1
        · exact (hnl h0).elim
        · obtain ⟨a, ha⟩ := List.mem_ofFn.mp h1; exact ⟨a, ha.symm⟩
      have hgr : ∃ b : Fin 9, g.rhs = bit9 b := by
        rcases List.mem_cons.mp hts_s.1.2.1 with h0 | h1
        · exact (hnr h0).elim
        · obtain ⟨b, hb⟩ := List.mem_ofFn.mp h1; exact ⟨b, hb.symm⟩
      obtain ⟨a, ha⟩ := hgl; obtain ⟨b, hb⟩ := hgr
      have hab : a ≠ b := fun e => hneq (by rw [ha, hb, e])
      let c := p9Partner a
      have hac : a ≠ c := p9_partner_ne a
      have hoff_a : restrict (p9Lift a) (bit9 a) = constF := funext (p9_lift_off_a a)
      have hoff_c : restrict (p9Lift a) (bit9 c) = constF := funext (p9_lift_off_c a)
      have hout_nz : restrict (p9Lift a) p9Ans ≠ constF := by
        intro heq
        have := congrFun heq ⟨5, by decide⟩
        rw [restrict, p9_lift_ans] at this; revert this; decide
      obtain ⟨h, hh, hrh⟩ := p9_read_twice hab ha hb hts_s
      have hgh : g ≠ h := fresh_head_ne_tail hts_f hh
      have hdg : disappears (p9Lift a) g := reading_zero_disappears (p9Lift a) hoff_a (Or.inl ha)
      have hdh : disappears (p9Lift a) h := reading_zero_disappears (p9Lift a) hoff_a hrh
      by_cases hbc : b = c
      · subst hbc
        have hgz : restrict (p9Lift a) g.val = constF :=
          both_zero_val_zero (p9Lift a) (ha.symm ▸ hoff_a) (hb.symm ▸ hoff_c)
        have hgv_ne : g.val ≠ p9Ans := fun e => hout_nz (e ▸ hgz)
        by_cases hpath : UsePath tail g.val p9Ans
        · obtain ⟨u, hu, hdu, hunz, z, hruz, hz0, hzw⟩ := boundary_gate (p9Lift a) hpath hgz hout_nz
          have hgu : g ≠ u := fresh_head_ne_tail hts_f hu
          have huh : h ≠ u := by
            intro heq; subst heq
            have hza : z ≠ bit9 a := by
              rcases hzw with rfl | ⟨t, ht, rfl⟩
              · exact fun e => hts_f.1 (e ▸ List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨a, rfl⟩))
              · exact fun e => fresh_val_not_raw hts_f.2 t ht (List.mem_cons_of_mem _ (e ▸ List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨a, rfl⟩)))
            rcases hrh with hl1 | hr1 <;> rcases hruz with hl2 | hr2
            · exact hza (hl2.symm.trans hl1)
            · exact hunz (both_zero_val_zero (p9Lift a) (hl1.symm ▸ hoff_a) (hr2.symm ▸ hz0))
            · exact hunz (both_zero_val_zero (p9Lift a) (hl2.symm ▸ hz0) (hr1.symm ▸ hoff_a))
            · exact hza (hr2.symm.trans hr1)
          have h3 := three_saved (p9Lift a) List.mem_cons_self (List.mem_cons_of_mem _ hh) (List.mem_cons_of_mem _ hu)
            hgh hgu huh hdg hdh hdu
          obtain ⟨m, ws', hsum, hrun', hin'⟩ := free_restrict (p9Lift a) List.mem_cons_self hts_s
          have hlo := p9_lift_lower a hrun' hin'
          omega
        · obtain ⟨sh, hsh_len, hsh_s⟩ := omit_dead_head hts_s hgv_ne hpath
          exact ihN sh.length (by simp at hts_len; omega) (by simp at hts_len; omega) _ (free_of_trace hsh_s.1 (fun _ _ h => h)) hsh_s.2
      · -- b ≠ c: find a reader r of bit9 c in g :: tail (must be in tail!)
        obtain ⟨r, hr_mem, hrc⟩ := p9_exists_reader c hts_s
        have hrg : r ≠ g := by
          intro heq; subst heq
          rcases hrc with hl | hr
          · exact hac (p9_bit_inj a c (ha.symm.trans hl))
          · exact hbc (p9_bit_inj b c (hb.symm.trans hr))
        have hr_tail : r ∈ tail := (List.mem_cons.mp hr_mem).resolve_left hrg
        by_cases hrh_ne : h ≠ r
        · have hdr : disappears (p9Lift a) r := reading_zero_disappears (p9Lift a) hoff_c hrc
          have h3 := three_saved (p9Lift a) List.mem_cons_self (List.mem_cons_of_mem _ hh) (List.mem_cons_of_mem _ hr_tail)
            hgh (Ne.symm hrg) hrh_ne hdg hdh hdr
          obtain ⟨m, ws', hsum, hrun', hin'⟩ := free_restrict (p9Lift a) List.mem_cons_self hts_s
          have hlo := p9_lift_lower a hrun' hin'
          omega
        · -- r = h: h reads BOTH bit9 a and bit9 c!
          have hreq : h = r := Classical.not_not.mp hrh_ne
          subst hreq
          have hhz : restrict (p9Lift a) h.val = constF := by
            rcases hrh with hl1 | hr1 <;> rcases hrc with hl2 | hr2
            · exact (hac (p9_bit_inj a c (hl1.symm.trans hl2))).elim
            · exact both_zero_val_zero (p9Lift a) (hl1.symm ▸ hoff_a) (hr2.symm ▸ hoff_c)
            · exact both_zero_val_zero (p9Lift a) (hl2.symm ▸ hoff_c) (hr1.symm ▸ hoff_a)
            · exact (hac (p9_bit_inj a c (hr1.symm.trans hr2))).elim
          have hhv_ne : h.val ≠ p9Ans := fun e => hout_nz (e ▸ hhz)
          obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hh
          by_cases hpath : UsePath post h.val p9Ans
          · obtain ⟨u, hu_post, hdu, _, _, _, _, _⟩ := boundary_gate (p9Lift a) hpath hhz hout_nz
            have hu_tail : u ∈ tail := by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hu_post)
            have hgu : g ≠ u := fresh_head_ne_tail hts_f hu_tail
            have hnd : (g :: tail).Nodup := fresh_nodup hts_f
            have hnd_tail : tail.Nodup := (List.nodup_cons.mp hnd).2
            rw [hsplit] at hnd_tail
            have hhu : h ≠ u := by
              have hnd2 := (List.nodup_append.mp hnd_tail).2.1
              have hnot := (List.nodup_cons.mp hnd2).1
              intro heq; subst heq; exact hnot hu_post
            have h3 := three_saved (p9Lift a) List.mem_cons_self (List.mem_cons_of_mem _ hh) (List.mem_cons_of_mem _ hu_tail)
              hgh hgu hhu hdg hdh hdu
            obtain ⟨m, ws', hsum, hrun', hin'⟩ := free_restrict (p9Lift a) List.mem_cons_self hts_s
            have hlo := p9_lift_lower a hrun' hin'
            omega
          · have hs_app : Sufficient verts9 p9Ans ((g :: pre) ++ h :: post) := by simpa [hsplit] using hts_s
            obtain ⟨sh, hsh_len, hsh_s⟩ := omit_dead_mid hs_app hhv_ne hpath
            have hlen_split : tail.length = pre.length + 1 + post.length := by rw [hsplit]; simp; omega
            exact ihN sh.length (by simp at hts_len hsh_len; omega) (by simp at hts_len hsh_len; omega) _
              (free_of_trace hsh_s.1 (fun _ _ h => h)) hsh_s.2

/-! ### Section 7: Bridge to `PEqualNP.Outside.L_meta_4253` -/

def binCost (gates : List Gate) : Nat :=
  (gates.filter fun g => match g.op with | .not => false | _ => true).length

def rawInitFns (v : Fin 9) : List (Fin 512 → Bool) :=
  List.ofFn (fun i : Fin 9 => bit9 i) ++ [fun r => !bit9 0 r, fun r => !bit9 v r]

def runFns (gates : List Gate) (acc : List (Fin 512 → Bool)) : List (Fin 512 → Bool) :=
  gates.foldl (fun cur g => cur ++ [fun r => g.op.eval (g.inputs.map fun i => (cur.getD i constF) r)]) acc

theorem runFns_eval (gates : List Gate) (acc : List (Fin 512 → Bool)) (r : Fin 512) :
    (runFns gates acc).map (fun f => f r) =
    gates.foldl (fun cur g => cur ++ [g.op.eval (g.inputs.map fun i => cur.getD i false)]) (acc.map fun f => f r) := by
  induction gates generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    change (runFns gs (acc ++ [fun r => g.op.eval (g.inputs.map fun i => (acc.getD i constF) r)])).map (fun f => f r) = _
    rw [ih]
    simp only [List.foldl_cons]
    congr 1
    rw [List.map_append, List.map_cons, List.map_nil]
    congr 1; congr 1; dsimp only; congr 1
    apply List.map_congr_left
    intro i _
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases acc[i]? <;> rfl

theorem normFn_bit9_mem (i : Fin 9) : normFn (0 : Fin 512) (bit9 i) ∈ verts9 := by
  have heq : normFn (0 : Fin 512) (bit9 i) = bit9 i := by
    funext r; simp [normFn, phase, bit9]
  rw [heq]; exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem normFn_not_bit9_mem (i : Fin 9) : normFn (0 : Fin 512) (fun r => !bit9 i r) ∈ verts9 := by
  have heq : normFn (0 : Fin 512) (fun r => !bit9 i r) = bit9 i := by
    funext r; simp [normFn, phase, bit9]
  rw [heq]; exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem normFn_init_mem (v : Fin 9) (f : Fin 512 → Bool) (hf : f ∈ rawInitFns v) :
    normFn (0 : Fin 512) f ∈ verts9 := by
  rcases List.mem_append.mp hf with h1 | h2
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h1
    exact normFn_bit9_mem i
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    rcases h2 with rfl | rfl
    · exact normFn_not_bit9_mem 0
    · exact normFn_not_bit9_mem v

theorem runFns_to_free (gates : List Gate)
    (hfan : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (acc : List (Fin 512 → Bool)) (ws : List (Fin 512 → Bool)) (n : Nat),
    Free verts9 n ws →
    constF ∈ ws →
    (∀ f ∈ acc, normFn (0 : Fin 512) f ∈ ws) →
    ∃ m ws', m ≤ n + binCost gates ∧ Free verts9 m ws' ∧
      ∀ f ∈ runFns gates acc, normFn (0 : Fin 512) f ∈ ws' := by
  induction gates with
  | nil =>
    intro acc ws n hrun _ hcov
    exact ⟨n, ws, by simp [binCost], hrun, hcov⟩
  | cons g gs ih =>
    intro acc ws n hrun h0 hcov
    obtain ⟨hop, hlen⟩ := hfan g List.mem_cons_self
    have hfan' : ∀ q ∈ gs, q.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ q.inputs.length ≤ 2 :=
      fun q hq => hfan q (List.mem_cons_of_mem _ hq)
    let fn : Fin 512 → Bool := fun r => g.op.eval (g.inputs.map fun i => (acc.getD i constF) r)
    have hget_in (i : Nat) : normFn (0 : Fin 512) (acc.getD i constF) ∈ ws := by
      rw [List.getD_eq_getElem?_getD]
      cases h : acc[i]? with
      | none =>
        have : normFn (0 : Fin 512) constF = constF := funext fun _ => rfl
        simpa [this] using h0
      | some f => exact hcov f (List.mem_of_getElem? h)
    have hconst_in (b : Bool) : normFn (0 : Fin 512) (fun _ => b) ∈ ws := by
      have : normFn (0 : Fin 512) (fun _ => b) = constF := funext fun _ => by cases b <;> rfl
      simpa [this] using h0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    by_cases hnot : g.op = .not
    · have hfn_in : normFn (0 : Fin 512) fn ∈ ws := by
        cases hgi : g.inputs with
        | nil =>
          have : fn = fun _ => GateOp.not.eval [] := funext fun _ => by simp [fn, hnot, hgi]
          rw [this]; exact hconst_in (GateOp.not.eval [])
        | cons i rest =>
          have : fn = fun r => !((acc.getD i constF) r) := funext fun r => by simp [fn, hnot, hgi, GateOp.eval]
          have hnorm : normFn (0 : Fin 512) fn = normFn (0 : Fin 512) (acc.getD i constF) := by
            rw [this]; funext r; exact norm_not_table ((acc.getD i constF) 0) ((acc.getD i constF) r)
          rw [hnorm]; exact hget_in i
      have hcov' : ∀ f ∈ acc ++ [fn], normFn (0 : Fin 512) f ∈ ws := by
        intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hcov f hf
        · simp at hf; subst hf; exact hfn_in
      obtain ⟨m, ws', hm, hrun', hcov''⟩ := ih hfan' (acc ++ [fn]) ws n hrun h0 hcov'
      refine ⟨m, ws', ?_, hrun', hcov''⟩
      simp only [binCost, List.filter_cons, hnot, Bool.false_eq_true, ↓reduceIte]
      exact hm
    · have hbin : g.op = .and ∨ g.op = .or := by
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (hnot h).elim
      have hstep : ∃ d ws1, d ≤ 1 ∧ Free verts9 (n + d) ws1 ∧ constF ∈ ws1 ∧
          (∀ f ∈ acc ++ [fn], normFn (0 : Fin 512) f ∈ ws1) := by
        cases hgi : g.inputs with
        | nil =>
          refine ⟨0, ws, by omega, hrun, h0, fun f hf => ?_⟩
          rcases List.mem_append.mp hf with hf | hf
          · exact hcov f hf
          · simp at hf; subst hf
            rcases hbin with h | h
            · have : fn = fun _ => true := funext fun _ => by simp [fn, h, hgi, GateOp.eval]
              rw [this]; exact hconst_in true
            · have : fn = fun _ => false := funext fun _ => by simp [fn, h, hgi, GateOp.eval]
              rw [this]; exact hconst_in false
        | cons i rest =>
          cases rest with
          | nil =>
            refine ⟨0, ws, by omega, hrun, h0, fun f hf => ?_⟩
            rcases List.mem_append.mp hf with hf | hf
            · exact hcov f hf
            · simp at hf; subst hf
              have : fn = acc.getD i constF := funext fun r => by rcases hbin with h | h <;> simp [fn, h, hgi, GateOp.eval]
              rw [this]; exact hget_in i
          | cons j rest2 =>
            cases rest2 with
            | nil =>
              let fa := acc.getD i constF
              let fb := acc.getD j constF
              let isOr : Bool := match g.op with | .or => true | _ => false
              let op := normOp isOr (fa 0) (fb 0)
              have hfn_eq : normFn (0 : Fin 512) fn = fun r => evalOp op (normFn (0 : Fin 512) fa r) (normFn (0 : Fin 512) fb r) := by
                funext r
                have hfev : fn r = if isOr then fa r || fb r else fa r && fb r := by
                  rcases hbin with h | h <;> simp [fn, isOr, h, hgi, GateOp.eval, fa, fb]
                have hfev0 : fn 0 = if isOr then fa 0 || fb 0 else fa 0 && fb 0 := by
                  rcases hbin with h | h <;> simp [fn, isOr, h, hgi, GateOp.eval, fa, fb]
                simp only [normFn, hfev, hfev0]
                exact norm_bin_table isOr (fa 0) (fb 0) (fa r) (fb r)
              refine ⟨1, normFn (0 : Fin 512) fn :: ws, Nat.le_refl _, ?_, List.mem_cons_of_mem _ h0, ?_⟩
              · rw [hfn_eq]
                exact FreeSafe.step op hrun (hget_in i) (hget_in j) (fun h => h)
              · intro f hf
                rcases List.mem_append.mp hf with hf | hf
                · exact List.mem_cons_of_mem _ (hcov f hf)
                · simp at hf; subst hf; exact List.mem_cons_self
            | cons _ _ =>
              simp [hgi] at hlen
      obtain ⟨d, ws1, hd, hrun1, h01, hcov1⟩ := hstep
      obtain ⟨m, ws', hm, hrun', hcov''⟩ := ih hfan' (acc ++ [fn]) ws1 (n + d) hrun1 h01 hcov1
      refine ⟨m, ws', ?_, hrun', hcov''⟩
      have hbc_step : binCost (g :: gs) = binCost gs + 1 := by
        cases hgop : g.op <;> simp_all [binCost]
      omega

theorem constF_mem_free {m ws} (hrun : Free verts9 m ws) : constF ∈ ws := by
  induction hrun with
  | base => exact List.mem_cons_self
  | step _ _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem p9_formula_eq (r : Fin 512) :
    let x := fun i : Fin 9 => bit9 i r
    (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
     x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
     x 6 && x 8 || x 8 && x 5) = p9Ans r := by
  revert r; decide +kernel

end PEqualNP.Outside.L_meta_4253

theorem PEqualNP.Outside.L_meta_4253 : ∀ (x1 : Fin (9 : ℕ)), (1 : ℕ) ≤ ↑x1 → ↑x1 ≤ (4 : ℕ) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → x4.size = (13 : ℕ) → (11 : ℕ) ≤ x4.output → Option.map PEqualNP.CircuitLowerBounds.Gate.op x4.gates[x4.output - (11 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ)), !x9 x1]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  classical
  open PEqualNP.Outside.L_meta_4253 in
  intro v _ _ C hmono hsize _ _
  by_contra hcontra
  have hall : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [!x 0, !x v]) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
       x 6 && x 8 || x 8 && x 5) := fun x => Classical.not_not.mp fun hne => hcontra ⟨x, hne⟩
  have hfan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hmono g hg
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hbc : binCost C.gates ≤ 13 := by
    have h1 := List.length_filter_le (fun q : PEqualNP.CircuitLowerBounds.Gate => match q.op with | .not => false | _ => true) C.gates
    change C.gates.length = 13 at hsize
    change (C.gates.filter _).length ≤ 13
    omega
  obtain ⟨m, ws, hm, hrun, hcov⟩ := runFns_to_free C.gates hfan (rawInitFns v) verts9 0 FreeSafe.base List.mem_cons_self (normFn_init_mem v)
  let outFn : Fin 512 → Bool := (runFns C.gates (rawInitFns v)).getD C.output constF
  have hout_eq : outFn = p9Ans := by
    funext r
    have hev := runFns_eval C.gates (rawInitFns v) r
    have hinit : (rawInitFns v).map (fun f => f r) = List.ofFn (fun i : Fin 9 => bit9 i r) ++ [!bit9 0 r, !bit9 v r] := by
      simp [rawInitFns]
    have hget : outFn r = C.eval (List.ofFn (fun i : Fin 9 => bit9 i r) ++ [!bit9 0 r, !bit9 v r]) := by
      have h1 : outFn r = ((runFns C.gates (rawInitFns v)).map fun f => f r).getD C.output false := by
        simp only [outFn, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (runFns C.gates (rawInitFns v))[C.output]? <;> rfl
      rw [h1, hev, hinit]
      rfl
    rw [hget]
    exact (hall (fun i => bit9 i r)).trans (p9_formula_eq r)
  have hnorm_p9 : normFn (0 : Fin 512) p9Ans = p9Ans := by
    funext r; simp [normFn, phase, p9Ans, evalEdges]
  have hp9_in : p9Ans ∈ ws := by
    rw [← hnorm_p9, ← hout_eq]
    simp only [outFn, List.getD_eq_getElem?_getD]
    cases h : (runFns C.gates (rawInitFns v))[C.output]? with
    | none =>
      have hcf0 : normFn (0 : Fin 512) constF = constF := funext fun _ => rfl
      dsimp only [Option.getD]
      rw [hcf0]
      exact constF_mem_free hrun
    | some f => exact hcov f (List.mem_of_getElem? h)
  exact p9_lower m (by omega) ws hrun hp9_in
