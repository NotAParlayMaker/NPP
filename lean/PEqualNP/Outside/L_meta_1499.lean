import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1499

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def val (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  ((Circuit.mk gs 0).wires (List.ofFn x)).getD w false

def ancestors (n : ℕ) (gs : List Gate) (w k : ℕ) : Prop :=
  n ≤ w ∧ w < n + gs.length ∧ (w = n + k ∨ InCone n ⟨gs, 0⟩ k (w - n))

lemma length_wires (gs : List Gate) (x : List Bool) :
    ((Circuit.mk gs 0).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp_all [Circuit.wires, List.foldl_append, Nat.add_assoc]

lemma length_cones (gs : List Gate) (n : ℕ) :
    (cones n (Circuit.mk gs 0)).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    simpa [cones, List.foldl_append, coneStep] using congrArg Nat.succ ih

lemma wires_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires xs = (Circuit.mk gs 0).wires xs ++
      [g.op.eval (g.inputs.map fun w => ((Circuit.mk gs 0).wires xs).getD w false)] := by
  simp [Circuit.wires, List.foldl_append]

lemma cones_snoc (gs : List Gate) (g : Gate) (n : ℕ) :
    cones n ⟨gs ++ [g], 0⟩ = coneStep n (cones n ⟨gs, 0⟩) g := by
  simp [cones, List.foldl_append]

lemma val_old (gs : List Gate) (g : Gate) {n w : ℕ} (x : Fin n → Bool)
    (hw : w < n + gs.length) : val (gs ++ [g]) x w = val gs x w := by
  have h : w < ((Circuit.mk gs 0).wires (List.ofFn x)).length := by
    simpa [length_wires] using hw
  unfold val
  rw [wires_snoc]
  exact List.getD_append _ _ _ _ h

lemma val_last (gs : List Gate) (g : Gate) {n : ℕ} (x : Fin n → Bool) :
    val (gs ++ [g]) x (n + gs.length) = g.op.eval (g.inputs.map (val gs x)) := by
  have h := length_wires gs (List.ofFn x)
  simp only [List.length_ofFn] at h
  unfold val
  rw [wires_snoc]
  rw [← h, List.getD_eq_getElem?_getD, List.getElem?_append]
  simp

lemma anc_old {n w k : ℕ} (gs : List Gate) (g : Gate) (hw : w < n + gs.length) :
    ancestors n (gs ++ [g]) w k ↔ ancestors n gs w k := by
  by_cases hn : n ≤ w
  · have hidx : w-n < (cones n ⟨gs,0⟩).length := by rw [length_cones]; omega
    have stable : InCone n ⟨gs ++ [g],0⟩ k (w-n) ↔ InCone n ⟨gs,0⟩ k (w-n) := by
      unfold InCone
      rw [cones_snoc]
      unfold coneStep
      rw [List.getD_append _ _ _ _ hidx]
    simp [ancestors, hn, hw, stable, show w < n + (gs.length + 1) by omega]
  · simp [ancestors, hn]

lemma cone_last {n k : ℕ} (gs : List Gate) (g : Gate) : InCone n ⟨gs ++ [g],0⟩ k gs.length ↔ ∃ w ∈ g.inputs, ancestors n gs w k := by
    have h := length_cones gs n
    unfold InCone
    rw [cones_snoc]
    unfold coneStep
    rw [List.getD_eq_getElem?_getD, List.getElem?_append, h]
    simp only [lt_self_iff_false, ↓reduceIte, Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
      List.mem_cons]
    simp only [ancestors, InCone]
    constructor
    · rintro ⟨w, ⟨hw, hn, hlt⟩, he | he⟩
      · exact ⟨w, hw, hn, hlt, Or.inl (by omega)⟩
      · exact ⟨w, hw, hn, hlt, Or.inr he⟩
    · rintro ⟨w, hw, hn, hlt, he | he⟩
      · exact ⟨w, ⟨hw, hn, hlt⟩, Or.inl (by omega)⟩
      · exact ⟨w, ⟨hw, hn, hlt⟩, Or.inr he⟩

lemma anc_last {n k : ℕ} (gs : List Gate) (g : Gate) :
    ancestors n (gs ++ [g]) (n + gs.length) k ↔
      k = gs.length ∨ ∃ w ∈ g.inputs, ancestors n gs w k := by
  have last := cone_last (n := n) (k := k) gs g
  simpa [ancestors, Nat.add_assoc, eq_comm] using
    (or_congr (Iff.rfl : k = gs.length ↔ k = gs.length) last)


lemma anc_bound {n k w : ℕ} (gs : List Gate) (ha : ancestors n gs w k) : n + k ≤ w := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    obtain ⟨_,_,_⟩ := ha
    simp_all
    omega
  | append_singleton gs g ih =>
    by_cases old : w < n + gs.length
    · exact ih ((anc_old gs g old).mp ha)
    · have endw : w = n + gs.length := by
        have := ha.2.1
        simp only [List.length_append, List.length_singleton] at this
        omega
      subst w
      obtain he | ⟨v,_,hv⟩ := (anc_last gs g).mp ha
      · omega
      · have := ih hv
        have := hv.2.1
        omega

def nested (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < C.gates.length ∧ b < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
    (gateAt C b).op = GateOp.and ∧ InCone n C a b

def pairSet (n : ℕ) (C : Circuit) : Finset (ℕ × ℕ) :=
  letI := gateOpDecEq
  (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter fun p =>
    (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧
      InCone n C p.1 p.2

lemma pairSet_card (n : ℕ) (C : Circuit) : (pairSet n C).card = andPairs n C := by
  rfl

lemma pairSet_mem (n : ℕ) (C : Circuit) (a b : ℕ) :
    (a,b) ∈ pairSet n C ↔ nested n C a b := by
  simp [pairSet, nested, and_assoc]

lemma pairs_decrease {n i j : ℕ} {C D : Circuit} (source : ℕ → ℕ)
    (hinj : ∀ a < D.gates.length, ∀ b < D.gates.length, source a = source b → a = b)
    (hmaps : ∀ a b, nested n D a b → nested n C (source a) (source b))
    (hlost : ∀ a b, nested n D a b → source a ≠ i)
    (hij : nested n C i j) : andPairs n D < andPairs n C := by
  classical
  let f : ℕ × ℕ → ℕ × ℕ := fun p => (source p.1, source p.2)
  have hlt : (pairSet n D).card ≤ ((pairSet n C).erase (i,j)).card := by
    apply Finset.card_le_card_of_injOn f
    · rintro ⟨a,b⟩ h
      have hn := (pairSet_mem n D a b).mp h
      apply Finset.mem_erase.mpr
      exact ⟨fun eq => hlost a b hn (congrArg Prod.fst eq),
        (pairSet_mem n C _ _).mpr (hmaps a b hn)⟩
    · rintro ⟨a,b⟩ h₁ ⟨c,d⟩ h₂ eq
      have h₁' := (pairSet_mem n D a b).mp h₁
      have h₂' := (pairSet_mem n D c d).mp h₂
      exact Prod.ext (hinj a h₁'.1 c h₂'.1 (congrArg Prod.fst eq))
        (hinj b h₁'.2.1 d h₂'.2.1 (congrArg Prod.snd eq))
  rw [← pairSet_card, ← pairSet_card]
  exact lt_of_le_of_lt hlt (Finset.card_erase_lt_of_mem ((pairSet_mem n C i j).mpr hij))

def put {α : Type} (f : ℕ → α) (k : ℕ) (v : α) (w : ℕ) : α :=
  if w = k then v else f w

def shortcut (op : GateOp) (a b : Option ℕ) : Option ℕ :=
  if op matches .and then none else a.or b

def ao (op : GateOp) := op = GateOp.and ∨ op = GateOp.or

-- Cut the chosen gate from subsequent reads, keeping its value for the final OR.
-- A missing wire represents false. A gate with a missing operand can be bypassed.
inductive Trace (n i : ℕ) (base : List Gate) :
    List Gate → List Gate → (ℕ → Option ℕ) → (ℕ → ℕ) → Prop where
  | start : Trace n i base base base (put some (n+i) none) id
  | keep {gs ds r s op a b p q} (old : Trace n i base gs ds r s)
      (hop : ao op) (ha : a < n + gs.length) (hb : b < n + gs.length)
      (hp : r a = some p) (hq : r b = some q) :
      Trace n i base (gs ++ [⟨op,[a,b]⟩]) (ds ++ [⟨op,[p,q]⟩])
        (put r (n + gs.length) (some (n + ds.length))) (put s ds.length gs.length)
  | skip {gs ds r s op a b} (old : Trace n i base gs ds r s)
      (hop : ao op) (ha : a < n + gs.length) (hb : b < n + gs.length)
      (hz : r a = none ∨ r b = none) :
      Trace n i base (gs ++ [⟨op,[a,b]⟩]) ds
        (put r (n + gs.length) (shortcut op (r a) (r b))) s

lemma shortcut_mem {op : GateOp} {a b : Option ℕ} {w : ℕ}
    (h : shortcut op a b = some w) : a = some w ∨ b = some w := by
  cases op <;> cases a <;> cases b <;> simp_all [shortcut, Option.or]

lemma trace_lengths {n i base gs ds r s} (tr : Trace n i base gs ds r s) :
    base.length ≤ ds.length ∧ ds.length ≤ gs.length := by
  induction tr with
  | start => simp
  | keep _ _ _ _ _ _ ih => simp_all; omega
  | skip _ _ _ _ _ ih => simp_all; omega

lemma snoc_bound {α : Type} {xs : List α} {z : α} {w n : ℕ}
    (h : w < n + (xs ++ [z]).length) : w < n + xs.length ∨ w = n + xs.length := by
  simp at h
  omega

lemma trace_ref {n i base gs ds r s} (tr : Trace n i base gs ds r s)
    {w u : ℕ} (hw : w < n + gs.length) (hu : r w = some u) : u < n + ds.length := by
  induction tr generalizing w u with
  | start =>
    simp only [put] at hu
    split at hu <;> simp_all
  | @keep gs ds r s op a b p q tr hop ha hb hp hq ih =>
    rcases snoc_bound hw with hw | rfl
    · simp only [put, ite_eq_right (Nat.ne_of_lt hw)] at hu
      have := ih hw hu
      simp
      omega
    · simp [put] at hu
      subst u
      simp
  | @skip gs ds r s op a b tr hop ha hb hz ih =>
    rcases snoc_bound hw with hw | rfl
    · exact ih hw (by simpa [put, Nat.ne_of_lt hw] using hu)
    · simp only [put] at hu
      rcases shortcut_mem hu with h | h
      · exact ih ha h
      · exact ih hb h

lemma trace_source {n i base gs ds r s} (tr : Trace n i base gs ds r s) :
    (∀ k < ds.length, s k < gs.length) ∧
    ∀ a < ds.length, ∀ b < ds.length, s a = s b → a = b := by
  induction tr with
  | start => simp
  | @keep gs ds r s op a b p q tr hop ha hb hp hq ih =>
    obtain ⟨bound,inj⟩ := ih
    simp only [List.length_append,List.length_singleton]
    constructor
    · intro k hk
      by_cases h : k = ds.length
      · simp [put,h]
      · simp [put,h]; have := bound k (by omega); omega
    · intro k hk l hl he
      by_cases h : k = ds.length <;> by_cases g : l = ds.length
      · omega
      · have := bound l (by omega); simp_all [put]
      · have := bound k (by omega); simp_all [put]
      · exact inj _ (by omega) _ (by omega) (by simpa [put,h,g] using he)
  | skip _ _ _ _ _ ih =>
    exact ⟨fun k hk => by have := ih.1 k hk; simp; omega, ih.2⟩

def oval {n : ℕ} (ds : List Gate) (x : Fin n → Bool) (v : Option ℕ) : Bool :=
  v.elim false (val ds x)

lemma shortcut_val {n : ℕ} (ds : List Gate) (x : Fin n → Bool) {op : GateOp} (hop : ao op)
    {a b : Option ℕ} (hz : a = none ∨ b = none) :
    oval ds x (shortcut op a b) = op.eval [oval ds x a, oval ds x b] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [shortcut, oval, Option.or, GateOp.eval]

lemma trace_eval {n i base gs ds r s} (tr : Trace n i base gs ds r s)
    (x : Fin n → Bool) (cut : val base x (n+i) = false) (w : ℕ) (hw : w < n + gs.length) :
    oval ds x (r w) = val gs x w := by
  induction tr generalizing w with
  | start =>
    by_cases eq : w = n+i <;> simp [put,eq,oval,cut]
  | @keep gs ds r s op a b p q tr hop ha hb hp hq ih =>
    rcases snoc_bound hw with hw | rfl
    · simp only [put, if_neg (Nat.ne_of_lt hw), val_old gs _ x hw]
      rw [← ih w hw]
      cases eq : r w with
      | none => rfl
      | some u => exact val_old ds _ x (trace_ref tr hw eq)
    · simp only [put]
      change val _ x _ = val _ x _
      rw [val_last, val_last]
      have h₁ := ih a ha
      have h₂ := ih b hb
      simp only [hp,hq,oval,Option.elim_some] at h₁ h₂
      simp [h₁,h₂]
  | @skip gs ds r s op a b tr hop ha hb hz ih =>
    rcases snoc_bound hw with hw | rfl
    · simpa [put, Nat.ne_of_lt hw, val_old gs _ x hw] using ih w hw
    · simp [put, val_last, shortcut_val ds x hop hz, ih a ha, ih b hb]

def opAt (gs : List Gate) (k : ℕ) := (gateAt ⟨gs,0⟩ k).op

lemma op_old (gs : List Gate) (g : Gate) {k : ℕ} (hk : k < gs.length) :
    opAt (gs ++ [g]) k = opAt gs k := by
  simp [opAt,gateAt,List.getElem?_append,hk]

lemma op_last (gs : List Gate) (g : Gate) : opAt (gs ++ [g]) gs.length = g.op := by
  simp [opAt,gateAt,List.getD_eq_getElem?_getD]

lemma trace_gate {n i base gs ds r s} (tr : Trace n i base gs ds r s)
    {u : ℕ} (hu : u < ds.length) :
    opAt ds u = opAt gs (s u) ∧ ∀ x : Fin n → Bool, val base x (n+i) = false →
      val ds x (n+u) = val gs x (n+s u) := by
  induction tr generalizing u with
  | start => simp
  | @keep gs ds r s op a b p q tr hop ha hb hp hq ih =>
    simp only [List.length_append,List.length_singleton] at hu
    by_cases h : u < ds.length
    · have hs := (trace_source tr).1 u h
      obtain ⟨h₁,h₂⟩ := ih h
      simp [put,Nat.ne_of_lt h,op_old _ _ h, op_old _ _ hs,
        val_old ds _ _ (Nat.add_lt_add_left h n),val_old gs _ _ (Nat.add_lt_add_left hs n),h₁]
      exact h₂
    · have : u = ds.length := by omega
      subst u
      simp [put, op_last]
      intro x hx
      have h₁ := trace_eval tr x hx a ha
      have h₂ := trace_eval tr x hx b hb
      simp only [hp,hq,oval,Option.elim_some] at h₁ h₂
      simp [val_last,h₁,h₂]
  | @skip gs ds r s op a b tr hop ha hb hz ih =>
    have hs := (trace_source tr).1 u hu
    simpa [op_old _ _ hs,val_old gs _ _ (Nat.add_lt_add_left hs n)] using ih hu

-- On assignments where the cut gate is false, every true AND survives.
lemma trace_kept {n i base gs ds r s} (tr : Trace n i base gs ds r s)
    {k : ℕ} (hk : k < gs.length) (hand : opAt gs k = GateOp.and)
    (x : Fin n → Bool) (hx : val base x (n+i) = false) (ht : val gs x (n+k) = true) :
    ∃ u < ds.length, s u = k := by
  induction tr generalizing k with
  | start => exact ⟨k,hk,rfl⟩
  | @keep gs ds r s op a b p q tr hop ha hb hp hq ih =>
    simp only [List.length_append,List.length_singleton] at hk ⊢
    by_cases h : k < gs.length
    · obtain ⟨u,hu,he⟩ := ih h (by rwa [op_old _ _ h] at hand)
        (by rwa [val_old _ _ _ (Nat.add_lt_add_left h n)] at ht)
      exact ⟨u,by omega,by simpa [put,Nat.ne_of_lt hu] using he⟩
    · exact ⟨ds.length,by omega,by simp [put]; omega⟩
  | @skip gs ds r s op a b tr hop ha hb hz ih =>
    simp only [List.length_append,List.length_singleton] at hk
    by_cases h : k < gs.length
    · exact ih h (by rwa [op_old _ _ h] at hand)
        (by rwa [val_old _ _ _ (Nat.add_lt_add_left h n)] at ht)
    · have : k = gs.length := by omega
      subst k
      rw [op_last] at hand
      change op = GateOp.and at hand
      subst op
      rw [val_last] at ht
      have h₁ := trace_eval tr x hx a ha
      have h₂ := trace_eval tr x hx b hb
      rcases hz with hz | hz <;> simp_all [oval,GateOp.eval]

lemma cone_old {n k b : ℕ} (gs : List Gate) (g : Gate) (hb : b < gs.length) :
    InCone n ⟨gs ++ [g],0⟩ k b ↔ InCone n ⟨gs,0⟩ k b := by
  have hh : b < (cones n ⟨gs,0⟩).length := by rwa [length_cones]
  unfold InCone
  rw [cones_snoc]
  unfold coneStep
  rw [List.getD_append _ _ _ _ hh]

lemma cone_before {n a b : ℕ} (gs : List Gate) (hb : b < gs.length)
    (hc : InCone n ⟨gs,0⟩ a b) : a < b := by
  induction gs using List.reverseRecOn with
  | nil => simp at hb
  | append_singleton gs g ih =>
    by_cases h : b < gs.length
    · exact ih h ((cone_old gs g h).mp hc)
    · simp at hb
      have he : b = gs.length := by omega
      subst b
      obtain ⟨w,_,hw⟩ := (cone_last gs g).mp hc
      have := anc_bound gs hw
      have := hw.2.1
      omega

lemma trace_anc {n i base gs ds r s} (hbase : base.length = i+1)
    (tr : Trace n i base gs ds r s) {w u k : ℕ} (hw : w < n+gs.length)
    (hu : r w = some u) (hk : ancestors n ds u k) :
    ancestors n gs w (s k) ∧ s k ≠ i := by
  induction tr generalizing w u k with
  | start =>
    by_cases he : w = n+i
    · simp [put,he] at hu
    · simp [put,he] at hu
      subst u
      have := anc_bound _ hk
      exact ⟨hk,by simp; omega⟩
  | @keep gs ds r s op a b p q tr hop ha hb hp hq ih =>
    have len := trace_lengths tr
    rcases snoc_bound hw with old | rfl
    · simp [put,Nat.ne_of_lt old] at hu
      have bound := trace_ref tr old hu
      have anc := (anc_old _ _ bound).mp hk
      have := anc_bound ds anc
      have lt : k < ds.length := by omega
      simpa [put, Nat.ne_of_lt lt, anc_old _ _ old] using ih old hu anc
    · simp [put] at hu
      subst u
      rcases (anc_last _ _).mp hk with eq | ⟨v,hv,hv'⟩
      · subst k
        exact ⟨by simp [put,anc_last],by simp [put]; omega⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        have transport (z v : ℕ) (hz : z < n+gs.length) (hm : r z = some v)
            (ha' : ancestors n ds v k) (hin : z ∈ [a,b]) :
            ancestors n (gs ++ [⟨op,[a,b]⟩]) (n+gs.length) (put s ds.length gs.length k) ∧
            put s ds.length gs.length k ≠ i := by
          have bound := trace_ref tr hz hm
          have := anc_bound ds ha'
          have lt : k < ds.length := by omega
          obtain ⟨hc,hn⟩ := ih hz hm ha'
          simpa [put,Nat.ne_of_lt lt] using
            And.intro ((anc_last gs ⟨op,[a,b]⟩).mpr (Or.inr ⟨z,hin,hc⟩)) hn
        rcases hv with rfl | rfl
        · exact transport a v ha hp hv' (by simp)
        · exact transport b v hb hq hv' (by simp)
  | @skip gs ds r s op a b tr hop ha hb hz ih =>
    rcases snoc_bound hw with old | rfl
    · simpa [anc_old _ _ old] using ih old (by simpa [put,Nat.ne_of_lt old] using hu) hk
    · simp [put] at hu
      rcases shortcut_mem hu with hm | hm
      · obtain ⟨hc,hn⟩ := ih ha hm hk
        exact ⟨(anc_last gs _).mpr (Or.inr ⟨a,by simp,hc⟩),hn⟩
      · obtain ⟨hc,hn⟩ := ih hb hm hk
        exact ⟨(anc_last gs _).mpr (Or.inr ⟨b,by simp,hc⟩),hn⟩

lemma trace_cone {n i base gs ds r s} (hbase : base.length = i+1)
    (tr : Trace n i base gs ds r s) {k t : ℕ} (ht : t < ds.length)
    (hcone : InCone n ⟨ds,0⟩ k t) : InCone n ⟨gs,0⟩ (s k) (s t) ∧ s k ≠ i := by
  induction tr generalizing k t with
  | start =>
    have := cone_before _ ht hcone
    exact ⟨hcone,by simp; omega⟩
  | @keep gs ds r s op a b p q tr hop ha hb hp hq ih =>
    have hk := cone_before _ ht hcone
    by_cases old : t < ds.length
    · have oldk : k < ds.length := by omega
      have hs := (trace_source tr).1 _ old
      simpa [put,Nat.ne_of_lt old,Nat.ne_of_lt oldk,cone_old _ _ hs] using
        ih old ((cone_old _ _ old).mp hcone)
    · simp at ht
      have : t = ds.length := by omega
      subst t
      obtain ⟨w,hw,hanc⟩ := (cone_last _ _).mp hcone
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      simp [put,Nat.ne_of_lt hk,cone_last]
      rcases hw with rfl | rfl
      · obtain ⟨h₁,h₂⟩ := trace_anc hbase tr ha hp hanc
        exact ⟨Or.inl h₁,h₂⟩
      · obtain ⟨h₁,h₂⟩ := trace_anc hbase tr hb hq hanc
        exact ⟨Or.inr h₁,h₂⟩
  | @skip gs ds r s op a b tr hop ha hb hz ih =>
    have hs := (trace_source tr).1 _ ht
    simpa [cone_old _ _ hs] using ih ht hcone

lemma trace_cut {n i base gs ds r s} (hbase : base.length = i+1)
    (tr : Trace n i base gs ds r s) :
    r (n+i) = none ∧ ∀ x : Fin n → Bool,
      val ds x (n+i) = val base x (n+i) ∧ val gs x (n+i) = val base x (n+i) := by
  induction tr with
  | start => simp [put]
  | keep tr hop ha hb hp hq ih =>
    have h := trace_lengths tr
    rename_i gs ds _ _ _ _ _ _ _
    have hg : n+i < n+gs.length := by omega
    have hd : n+i < n+ds.length := by omega
    simpa [put, show i ≠ gs.length by omega, val_old _ _ _ hg, val_old _ _ _ hd] using ih
  | skip tr hop ha hb hz ih =>
    have h := trace_lengths tr
    rename_i gs ds _ _ _ _ _
    have hg : n+i < n+gs.length := by omega
    simpa [put, show i ≠ gs.length by omega, val_old _ _ _ hg] using ih

-- Equal lengths would mean no reader of the cut gate was bypassed.
lemma trace_full {n i base gs ds r s} (hbase : base.length = i+1)
    (tr : Trace n i base gs ds r s) (heq : ds.length = gs.length) {w : ℕ}
    (hw : ancestors n gs w i) : w = n+i := by
  induction tr generalizing w with
  | start =>
    have := anc_bound _ hw
    have := hw.2.1
    omega
  | @keep gs ds r s op a b p q tr hop ha hb hp hq ih =>
    simp at heq
    by_cases hold : w < n+gs.length
    · exact ih heq ((anc_old _ _ hold).mp hw)
    · have upper := hw.2.1
      simp at upper
      have : w = n+gs.length := by omega
      subst w
      have sizes := trace_lengths tr
      obtain he | ⟨v,hv,hanc⟩ := (anc_last _ _).mp hw
      · omega
      · have he := ih heq hanc
        have cut := (trace_cut hbase tr).1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl <;> simp_all
  | skip tr _ _ _ _ _ =>
    have := trace_lengths tr
    simp at heq
    omega

def good (n : ℕ) (gs : List Gate) : Prop := ∀ k < gs.length,
  ∃ op a b, gateAt ⟨gs,0⟩ k = ⟨op,[a,b]⟩ ∧ ao op ∧ a < n+k ∧ b < n+k

lemma at_old (gs : List Gate) (g : Gate) {k : ℕ} (hk : k < gs.length) :
    gateAt ⟨gs ++ [g],0⟩ k = gateAt ⟨gs,0⟩ k := by
  unfold gateAt
  exact List.getD_append _ _ _ _ hk

lemma at_last (gs : List Gate) (g : Gate) : gateAt ⟨gs ++ [g],0⟩ gs.length = g := by
  simp [gateAt]

lemma good_snoc {n : ℕ} (gs : List Gate) (g : Gate) :
    good n (gs ++ [g]) ↔ good n gs ∧
      ∃ op a b, g = ⟨op,[a,b]⟩ ∧ ao op ∧ a < n+gs.length ∧ b < n+gs.length := by
  constructor
  · intro h
    constructor
    · intro k hk
      simpa [at_old _ _ hk] using h k (by simp; omega)
    · simpa [at_last] using h gs.length (by simp)
  · rintro ⟨h,hg⟩ k hk
    by_cases old : k < gs.length
    · simpa [at_old _ _ old] using h k old
    · simp at hk
      have : k = gs.length := by omega
      simpa [this,at_last] using hg

lemma good_iff {n : ℕ} (C : Circuit) : good n C.gates ↔ IsAO2 n C := by
  have mem (k : ℕ) (hk : k < C.gates.length) : gateAt C k ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have get (g : Gate) (hg : g ∈ C.gates) : ∃ k < C.gates.length, gateAt C k = g := by
    obtain ⟨k,hk,eq⟩ := List.getElem_of_mem hg
    exact ⟨k,hk,by unfold gateAt; rwa [List.getD_eq_getElem _ _ hk]⟩
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨k,hk,rfl⟩ := get g hg
      obtain ⟨op,a,b,he,ho,_⟩ := h k hk
      change gateAt C k = _ at he
      rw [he]
      exact ho
    · intro k hk w hw
      obtain ⟨op,a,b,he,_,ha,hb⟩ := h k hk
      change gateAt C k = _ at he
      rw [he] at hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨k,hk,rfl⟩ := get g hg
      obtain ⟨op,a,b,he,_⟩ := h k hk
      change gateAt C k = _ at he
      rw [he]
      rfl
  · rintro ⟨ops,back,two⟩ k hk
    have hm := mem k hk
    generalize hgate : gateAt C k = gate at *
    obtain ⟨op,inputs⟩ := gate
    have len := two _ hm
    obtain ⟨a,b,he⟩ : ∃ a b, inputs = [a,b] := by
      cases inputs with
      | nil => simp at len
      | cons a l =>
        cases l with
        | nil => simp at len
        | cons b l => cases l <;> simp_all
    subst inputs
    exact ⟨op,a,b,hgate,by simpa [hgate,ao] using ops _ hm,
      back k hk a (by simp [hgate]),back k hk b (by simp [hgate])⟩

lemma trace_exists {n i : ℕ} (gs : List Gate) (hi : i < gs.length) (hg : good n gs) :
    ∃ base ds r s, base.length = i+1 ∧ Trace n i base gs ds r s := by
  induction gs using List.reverseRecOn with
  | nil => simp at hi
  | append_singleton gs g ih =>
    by_cases h : i < gs.length
    · obtain ⟨prev,op,a,b,rfl,hop,ha,hb⟩ := (good_snoc _ _).mp hg
      obtain ⟨base,ds,r,s,len,tr⟩ := ih h prev
      cases hp : r a with
      | none => exact ⟨_,_,_,_,len,tr.skip hop ha hb (Or.inl hp)⟩
      | some p =>
        cases hq : r b with
        | none => exact ⟨_,_,_,_,len,tr.skip hop ha hb (Or.inr hq)⟩
        | some q => exact ⟨_,_,_,_,len,tr.keep hop ha hb hp hq⟩
    · exact ⟨_,_,_,_,by simp at hi ⊢; omega,Trace.start⟩

lemma trace_good {n i base gs ds r s} (tr : Trace n i base gs ds r s)
    (hg : good n gs) : good n ds := by
  induction tr with
  | start => exact hg
  | keep tr hop ha hb hp hq ih =>
    exact (good_snoc _ _).mpr ⟨ih ((good_snoc _ _).mp hg).1,
      _,_,_,rfl,hop,trace_ref tr ha hp,trace_ref tr hb hq⟩
  | skip tr _ _ _ _ ih => exact ih ((good_snoc _ _).mp hg).1

lemma nested_as {n k j : ℕ} (C : Circuit) : nested n C k j ↔
    k < C.gates.length ∧ j < C.gates.length ∧ opAt C.gates k = GateOp.and ∧
    opAt C.gates j = GateOp.and ∧ InCone n ⟨C.gates,0⟩ k j := Iff.rfl

lemma dirty_as {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    k ∈ junk G C ↔ k < C.gates.length ∧ opAt C.gates k = GateOp.and ∧
    ∃ x : Fin n → Bool, val C.gates x (n+k) = true ∧ graphFun G ∅ x = false := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold IsDirtyAnd IsDirty
  constructor
  · rintro ⟨h,ha,_,hx⟩
    exact ⟨h,ha,hx⟩
  · rintro ⟨h,ha,hx⟩
    exact ⟨h,ha,h,hx⟩

lemma before_or {gs : List Gate} {xs : List ℕ} {k : ℕ}
    (hk : k < (gs ++ [Gate.mk GateOp.or xs]).length)
    (hop : opAt (gs ++ [⟨GateOp.or,xs⟩]) k = GateOp.and) : k < gs.length := by
  simp at hk
  by_contra! h
  have he : k = gs.length := by omega
  simp [he,op_last] at hop

lemma append_counts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (xs : List ℕ) (out : ℕ) :
    andPairs n ⟨gs ++ [⟨GateOp.or,xs⟩],out⟩ = andPairs n ⟨gs,0⟩ ∧
    junk G ⟨gs ++ [⟨GateOp.or,xs⟩],out⟩ = junk G ⟨gs,0⟩ := by
  constructor
  · rw [← pairSet_card, ← pairSet_card]
    congr 1
    ext ⟨a,b⟩
    rw [pairSet_mem,pairSet_mem,nested_as,nested_as]
    constructor
    · rintro ⟨ha,hb,oa,ob,hcone⟩
      have h₁ := before_or ha oa
      have h₂ := before_or hb ob
      exact ⟨h₁,h₂,(op_old _ _ h₁).symm.trans oa,(op_old _ _ h₂).symm.trans ob,
        (cone_old _ _ h₂).mp hcone⟩
    · rintro ⟨ha,hb,oa,ob,hcone⟩
      change a < gs.length at ha
      change b < gs.length at hb
      exact ⟨by simp; omega,by simp; omega,(op_old _ _ ha).trans oa,(op_old _ _ hb).trans ob,
        (cone_old _ _ hb).mpr hcone⟩
  · ext k
    rw [dirty_as,dirty_as]
    constructor
    · rintro ⟨hk,ha,x,hx,hf⟩
      have h₁ := before_or hk ha
      exact ⟨h₁,(op_old _ _ h₁).symm.trans ha,x,
        (val_old _ _ _ (Nat.add_lt_add_left h₁ n)).symm.trans hx,hf⟩
    · rintro ⟨hk,ha,x,hx,hf⟩
      change k < gs.length at hk
      exact ⟨by simp; omega,(op_old _ _ hk).trans ha,x,
        (val_old _ _ _ (Nat.add_lt_add_left hk n)).trans hx,hf⟩

lemma trace_junk {n i base gs ds r s} (tr : Trace n i base gs ds r s)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (out : ℕ)
    (cut : ∀ x : Fin n → Bool, graphFun G ∅ x = false → val base x (n+i) = false) :
    (junk G ⟨ds,0⟩).card = (junk G ⟨gs,out⟩).card := by
  classical
  apply Finset.card_bij (fun k _ => s k)
  · intro k hk
    obtain ⟨hb,ha,x,hx,hf⟩ := (dirty_as _ _).mp hk
    obtain ⟨op,sem⟩ := trace_gate tr hb
    exact (dirty_as _ _).mpr ⟨(trace_source tr).1 _ hb,op.symm.trans ha,x,
      (sem x (cut x hf)).symm.trans hx,hf⟩
  · intro k hk l hl he
    exact (trace_source tr).2 _ ((dirty_as _ _).mp hk).1 _ ((dirty_as _ _).mp hl).1 he
  · intro j hj
    obtain ⟨hb,ha,x,hx,hf⟩ := (dirty_as _ _).mp hj
    obtain ⟨k,hk,eq⟩ := trace_kept tr hb ha x (cut x hf) hx
    subst j
    obtain ⟨op,sem⟩ := trace_gate tr hk
    exact ⟨k,(dirty_as _ _).mpr ⟨hk,op.trans ha,x,(sem x (cut x hf)).trans hx,hf⟩,rfl⟩

lemma trace_pairs {n i j base gs ds r s} (hb : base.length = i+1)
    (tr : Trace n i base gs ds r s) (out : ℕ) (hij : nested n ⟨gs,out⟩ i j) :
    andPairs n ⟨ds,0⟩ < andPairs n ⟨gs,out⟩ := by
  apply pairs_decrease s (trace_source tr).2 _ _ hij
  · intro a b h
    obtain ⟨ha,hb',oa,ob,hc⟩ := (nested_as _).mp h
    exact ⟨(trace_source tr).1 _ ha,(trace_source tr).1 _ hb',
      (trace_gate tr ha).1.symm.trans oa,(trace_gate tr hb').1.symm.trans ob,
      (trace_cone hb tr hb' hc).1⟩
  · intro a b h
    obtain ⟨_,hb',_,_,hc⟩ := (nested_as _).mp h
    exact (trace_cone hb tr hb' hc).2

def projected (n : ℕ) (gs : List Gate) (r : ℕ → Option ℕ) (out : ℕ) :=
  if out < n+gs.length then r out else none

lemma projected_val {n i base gs ds r s} (tr : Trace n i base gs ds r s)
    (out : ℕ) (x : Fin n → Bool) (hx : val base x (n+i) = false) :
    oval ds x (projected n gs r out) = val gs x out := by
  unfold projected
  split
  · exact trace_eval tr x hx out ‹_›
  · rename_i h
    have bound : ((Circuit.mk gs 0).wires (List.ofFn x)).length ≤ out := by
      simp [length_wires]; omega
    simp [oval,val,List.getD_eq_getElem?_getD,List.getElem?_eq_none bound]

lemma projected_bound {n i base gs ds r s} (tr : Trace n i base gs ds r s)
    (out : ℕ) {p : ℕ} (hp : projected n gs r out = some p) : p < n + ds.length := by
  unfold projected at hp
  split at hp
  · exact trace_ref tr ‹_› hp
  · contradiction

lemma solved {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) {i j : ℕ} (hij : nested n C i j) (below : BelowF G C i) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧ andPairs n D < andPairs n C ∧
      (junk G D).card = (junk G C).card := by
  obtain ⟨hi,hj,_,_,hc⟩ := (nested_as C).mp hij
  have hg := (good_iff C).mpr least.1
  obtain ⟨base,ds,r,s,hbase,tr⟩ := trace_exists C.gates hi hg
  have lens := trace_lengths tr
  have cut := trace_cut hbase tr
  have hsmall : ds.length < C.gates.length := by
    by_contra! h
    have he : ds.length = C.gates.length := by omega
    have ha : ancestors n C.gates (n+j) i := by
      refine ⟨by omega,by omega,Or.inr ?_⟩
      simpa using hc
    have eq := trace_full hbase tr he ha
    have lt := cone_before _ hj hc
    omega
  let q := projected n C.gates r C.output
  let lastGate : Gate := ⟨GateOp.or,[n+i,q.getD (n+i)]⟩
  let D : Circuit := ⟨ds ++ [lastGate],n+ds.length⟩
  have hw : n+i < n+ds.length := by omega
  have hq : q.getD (n+i) < n+ds.length := by
    cases he : q with
    | none => exact hw
    | some p => exact projected_bound tr C.output he
  have hgood : IsAO2 n D := by
    exact (good_iff D).mp ((good_snoc ds lastGate).mpr
      ⟨trace_good tr hg,_,_,_,rfl,Or.inr rfl,hw,hq⟩)
  have hbelow (x : Fin n → Bool) (hx : val base x (n+i) = true) : graphFun G ∅ x = true :=
    below x ((cut.2 x).2.trans hx)
  have hfun : circuitFun n D = graphFun G ∅ := by
    funext x
    change val (ds ++ [lastGate]) x (n+ds.length) = _
    rw [val_last]
    simp only [lastGate,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,
      id_eq,Bool.or_false]
    rw [(cut.2 x).1]
    cases hx : val base x (n+i) with
    | true => simp [hbelow x hx]
    | false =>
      have hold : val C.gates x C.output = graphFun G ∅ x := congrFun least.2.1 x
      have residual := (projected_val tr C.output x hx).trans hold
      change oval ds x q = _ at residual
      cases eq : q with
      | none => simpa [eq,oval,(cut.2 x).1,hx] using residual
      | some p => simpa [eq,oval] using residual
  have same : D.size = C.size := by
    have := least.2.2 D hgood hfun
    change (ds ++ [lastGate]).length = C.gates.length
    change C.gates.length ≤ (ds ++ [lastGate]).length at this
    simp at this ⊢
    omega
  have counts := append_counts G ds lastGate.inputs D.output
  refine ⟨D,⟨hgood,hfun,?_⟩,same,?_,?_⟩
  · intro E hE eq
    exact same.trans_le (least.2.2 E hE eq)
  · exact counts.1.trans_lt (trace_pairs hbase tr C.output hij)
  · have hzero (x : Fin n → Bool) (hx : graphFun G ∅ x = false) : val base x (n+i) = false := by
      cases h : val base x (n+i)
      · rfl
      · have := hbelow x h
        simp_all
    exact (congrArg Finset.card counts.2).trans (trace_junk tr G C.output hzero)

end PEqualNP.Outside.L_meta_1499

theorem PEqualNP.Outside.L_meta_1499 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  ∀ (i j : ℕ), i < C.gates.length → j < C.gates.length →
    (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
    PEqualNP.TopForm.BelowF G C i →
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
    PEqualNP.EdgeOwnership.InCone n C i j →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
      PEqualNP.TopForm.andPairs n C' < PEqualNP.TopForm.andPairs n C ∧
      (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card := by
  intro n G inst C _ least i j hi hj oi below oj cone
  exact PEqualNP.Outside.L_meta_1499.solved G C least ⟨hi,hj,oi,oj,cone⟩ below
