import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3493_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm
inductive Kind | point | line | mixed deriving DecidableEq
abbrev Inputs (n m : ℕ) := Fin (n+m) → Bool
structure State where
  gs : List Gate
  ps : Finset ℕ
  ls : Finset ℕ

def State.tag (s : State) : Kind → ℕ → Prop
  | .point, i => i ∈ s.ps
  | .line, i => i ∈ s.ls
  | .mixed, _ => True

def Closed (n : ℕ) (gs : List Gate) (raw : ℕ → Prop) (A : Finset ℕ) :=
  ∀ i ∈ A, raw i ∨ ∃ j < gs.length, i = n+j ∧ (gateAt ⟨gs,0⟩ j).op = .or ∧
    ∀ k ∈ (gateAt ⟨gs,0⟩ j).inputs, k ∈ A

structure Valid (n m : ℕ) (s : State) : Prop where
  ao : IsAO2 (n+m) ⟨s.gs,0⟩
  point : Closed (n+m) s.gs (· < n) s.ps
  line : Closed (n+m) s.gs (fun i => n ≤ i ∧ i < n+m) s.ls
  cross : ∀ j < s.gs.length, (gateAt ⟨s.gs,0⟩ j).op = .and →
    ∃ a b, (gateAt ⟨s.gs,0⟩ j).inputs = [a,b] ∧ a ∈ s.ls ∧ b ∈ s.ps

def wires (gs : List Gate) (w : List Bool) := (Circuit.mk gs 0).wires w
def val (n m : ℕ) (s : State) (i : ℕ) (x : Inputs n m) := (wires s.gs (List.ofFn x)).getD i false
theorem wires_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wires (gs++[g]) w = wires gs w ++ [g.op.eval (g.inputs.map fun i => (wires gs w).getD i false)] := by
  simp [wires,Circuit.wires,List.foldl_append]
theorem wires_len (gs : List Gate) (w : List Bool) : (wires gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires, Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_snoc]
    simp [ih, Nat.add_assoc]

def addTag (yes : Bool) (i : ℕ) (A : Finset ℕ) := if yes then insert i A else A
theorem tag_sub (yes : Bool) (i : ℕ) (A : Finset ℕ) : A ⊆ addTag yes i A := by
  cases yes <;> simp [addTag]
theorem oldGate (gs : List Gate) (g : Gate) {j : ℕ} (h : j < gs.length) :
    gateAt ⟨gs ++ [g],0⟩ j = gateAt ⟨gs,0⟩ j := List.getD_append _ _ _ _ h
theorem lastGate (gs : List Gate) (g : Gate) : gateAt ⟨gs ++ [g],0⟩ gs.length = g := by simp [gateAt]

theorem closed_append {n gs raw A} (h : Closed n gs raw A) (g : Gate) (mark : Bool)
    (hg : mark = true → g.op = .or ∧ ∀ k ∈ g.inputs, k ∈ A) :
    Closed n (gs ++ [g]) raw (addTag mark (n+gs.length) A) := by
  intro i hi
  by_cases ho : i ∈ A
  · rcases h i ho with r | ⟨j,hj,e,op,ins⟩
    · exact Or.inl r
    · refine Or.inr ⟨j,by simp; omega,e,by rwa [oldGate _ _ hj],?_⟩
      rw [oldGate _ _ hj]
      exact fun k hk => tag_sub _ _ _ (ins k hk)
  · cases mark with
    | false => exact False.elim (ho (by simpa [addTag] using hi))
    | true =>
      have e : i = n + gs.length := by simpa [addTag,ho] using hi
      obtain ⟨op,ins⟩ := hg rfl
      refine Or.inr ⟨gs.length,by simp,e,by rwa [lastGate],?_⟩
      rw [lastGate]
      exact fun k hk => tag_sub _ _ _ (ins k hk)

def push (N : ℕ) (s : State) (g : Gate) (k : Kind) : State :=
  ⟨s.gs ++ [g], addTag (decide (k=.point)) (N+s.gs.length) s.ps,
    addTag (decide (k=.line)) (N+s.gs.length) s.ls⟩

theorem push_valid {n m s} (h : Valid n m s) (op : GateOp) (a b : ℕ) (k : Kind)
    (ok : op = .and ∨ op = .or) (ha : a < n+m+s.gs.length) (hb : b < n+m+s.gs.length)
    (hp : k=.point → op=.or ∧ a∈s.ps ∧ b∈s.ps)
    (hl : k=.line → op=.or ∧ a∈s.ls ∧ b∈s.ls)
    (hc : op=.and → a∈s.ls ∧ b∈s.ps) :
    Valid n m (push (n+m) s ⟨op,[a,b]⟩ k) := by
  let g : Gate := ⟨op,[a,b]⟩
  have back : ReadsBack (n+m) ⟨s.gs ++ [g],0⟩ := by
    intro j hj i hi
    change j < (s.gs ++ [g]).length at hj
    by_cases old : j < s.gs.length
    · rw [oldGate _ _ old] at hi
      exact h.ao.2.1 j old i hi
    · have e : j = s.gs.length := by simp at hj; omega
      subst j
      rw [lastGate] at hi
      simp [g] at hi
      rcases hi with rfl | rfl <;> assumption
  constructor
  · refine ⟨?_,back,?_⟩
    · intro z hz
      change z ∈ s.gs ++ [g] at hz
      simp only [List.mem_append,List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact h.ao.1 _ hz
      · exact ok
    · intro z hz
      change z ∈ s.gs ++ [g] at hz
      simp only [List.mem_append,List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact h.ao.2.2 _ hz
      · rfl
  · apply closed_append h.point
    intro eq
    obtain ⟨o,pa,pb⟩ := hp (of_decide_eq_true eq)
    exact ⟨o,by simpa using And.intro pa pb⟩
  · apply closed_append h.line
    intro eq
    obtain ⟨o,la,lb⟩ := hl (of_decide_eq_true eq)
    exact ⟨o,by simpa using And.intro la lb⟩
  · intro j hj opj
    change j < (s.gs ++ [g]).length at hj
    change (gateAt ⟨s.gs ++ [g],0⟩ j).op = .and at opj
    by_cases old : j < s.gs.length
    · rw [oldGate _ _ old] at opj
      obtain ⟨u,v,ins,hu,hv⟩ := h.cross j old opj
      exact ⟨u,v,(congrArg Gate.inputs (oldGate _ _ old)).trans ins,tag_sub _ _ _ hu,tag_sub _ _ _ hv⟩
    · have e : j = s.gs.length := by simp at hj; omega
      subst j
      rw [lastGate] at opj
      obtain ⟨la,pb⟩ := hc opj
      exact ⟨a,b,congrArg Gate.inputs (lastGate _ g),tag_sub _ _ _ la,tag_sub _ _ _ pb⟩

def start (n m : ℕ) : State := ⟨[],Finset.range n, (Finset.range (n+m)).filter (n ≤ ·)⟩
structure Ext (s u : State) : Prop where
  tailWitness : ∃ tail, u.gs = s.gs ++ tail
  ps : s.ps ⊆ u.ps
  ls : s.ls ⊆ u.ls
theorem Ext.refl (s : State) : Ext s s := ⟨⟨[], by simp⟩,fun _ h => h,fun _ h => h⟩
theorem Ext.trans {s t u : State} (h : Ext s t) (k : Ext t u) : Ext s u := by
  obtain ⟨a,ha⟩ := h.tailWitness
  obtain ⟨b,hb⟩ := k.tailWitness
  exact ⟨⟨a++b,by rw [hb,ha,List.append_assoc]⟩,h.ps.trans k.ps,h.ls.trans k.ls⟩
theorem Ext.len {s u} (e : Ext s u) : s.gs.length ≤ u.gs.length := by
  obtain ⟨a,ha⟩ := e.tailWitness
  simp [ha]
theorem Ext.tag {s u} (e : Ext s u) {k i} (h : s.tag k i) : u.tag k i := by
  cases k
  exacts [e.ps h,e.ls h,True.intro]
theorem push_ext (N s g k) : Ext s (push N s g k) :=
  ⟨⟨[g],rfl⟩,tag_sub _ _ _,tag_sub _ _ _⟩
theorem Ext.val {s u} (e : Ext s u) {n m i} (hi : i < n+m+s.gs.length) (x : Inputs n m) :
    val n m u i x = val n m s i x := by
  obtain ⟨tail,ht⟩ := e.tailWitness
  unfold PEqualNP.Outside.L_meta_3493_aux.val
  rw [ht]
  clear ht
  induction tail using List.reverseRecOn with
  | nil => simp
  | append_singleton l g ih =>
    rw [← List.append_assoc]
    rw [wires_snoc]
    rw [List.getD_append]
    · exact ih
    · simp [wires_len]; omega

def Build (n m : ℕ) (k : Kind) (f : Inputs n m → Bool) (cost : ℕ) : Prop :=
  ∀ s, Valid n m s → Ext (start n m) s → ∃ u i,
    Valid n m u ∧ Ext s u ∧ u.gs.length ≤ s.gs.length+cost ∧
    i < n+m+u.gs.length ∧ u.tag k i ∧ ∀ x, val n m u i x = f x

theorem morph {n m k f c d} {h : Inputs n m → Bool} (b : Build n m k f c) (size : c ≤ d)
    (eq : ∀ x, f x = h x) : Build n m k h d := by
  intro s hs es
  obtain ⟨u,i,hu,eu,len,hi,tag,ev⟩ := b s hs es
  exact ⟨u,i,hu,eu,by omega,hi,tag,fun x => (ev x).trans (eq x)⟩

theorem leaf {n m} (i : Fin (n+m)) (k : Kind) (ht : (start n m).tag k i) :
    Build n m k (fun x => x i) 0 := by
  intro s hs es
  refine ⟨s,i,hs,Ext.refl s,by simp,by have := i.isLt; omega,es.tag ht,?_⟩
  intro x
  rw [es.val (by simp [start])]
  simp [val,start,wires,Circuit.wires]

theorem point {n m} (p : Fin n) : Build n m .point (fun x => x (Fin.castAdd m p)) 0 :=
  leaf _ _ (by simp [State.tag,start])
theorem line {n m} (l : Fin m) : Build n m .line (fun x => x (Fin.natAdd n l)) 0 :=
  leaf _ _ (by simp [State.tag,start,Fin.natAdd])

theorem combine {n m j k t f h a b} (A : Build n m j f a) (B : Build n m k h b)
    (op : GateOp) (ok : op=.and ∨ op=.or)
    (pc : t=.point → op=.or ∧ j=.point ∧ k=.point)
    (lc : t=.line → op=.or ∧ j=.line ∧ k=.line)
    (ac : op=.and → j=.line ∧ k=.point) :
    Build n m t (fun x => op.eval [f x,h x]) (a+b+1) := by
  intro s hs es
  obtain ⟨u,i,hu,eu,cu,hi,ti,vi⟩ := A s hs es
  obtain ⟨v,z,hv,ev,cv,hz,tz,vz⟩ := B u hu (es.trans eu)
  let g : Gate := ⟨op,[i,z]⟩
  let w := push (n+m) v g t
  have ti' := ev.tag ti
  have len := ev.len
  have hw : Valid n m w := by
    apply push_valid hv op i z t ok (by omega) hz
    · intro eq
      obtain ⟨o,rfl,rfl⟩ := pc eq
      exact ⟨o,ti',tz⟩
    · intro eq
      obtain ⟨o,rfl,rfl⟩ := lc eq
      exact ⟨o,ti',tz⟩
    · intro eq
      obtain ⟨rfl,rfl⟩ := ac eq
      exact ⟨ti',tz⟩
  refine ⟨w,n+m+v.gs.length,hw,(eu.trans ev).trans (push_ext _ _ _ _),?_,?_,?_,?_⟩
  · simp [w,push]; omega
  · simp [w,push]
  · cases t <;> simp [State.tag,w,push,addTag]
  · intro x
    have vl : (wires v.gs (List.ofFn x)).length = n+m+v.gs.length := by simp [wires_len]
    change (wires (v.gs ++ [g]) (List.ofFn x)).getD (n+m+v.gs.length) false = _
    rw [wires_snoc]
    change (wires v.gs (List.ofFn x) ++ [op.eval [val n m v i x,val n m v z x]]).getD (n+m+v.gs.length) false = _
    rw [← vl]
    simp [ev.val hi x,vi,vz]

theorem join {n m k f h a b} (A : Build n m k f a) (B : Build n m k h b) :
    Build n m k (fun x => f x || h x) (a+b+1) := by
  apply morph (combine A B .or (Or.inr rfl) (fun e => ⟨rfl,e,e⟩)
    (fun e => ⟨rfl,e,e⟩) (by simp)) le_rfl
  intro x; simp [GateOp.eval]
theorem pair {n m f h a b} (A : Build n m .line f a) (B : Build n m .point h b) :
    Build n m .mixed (fun x => f x && h x) (a+b+1) := by
  apply morph (combine A B .and (Or.inl rfl) (by simp) (by simp) (fun _ => ⟨rfl,rfl⟩)) le_rfl
  intro x; simp [GateOp.eval]


open Classical in
theorem aggregate {α : Type} [DecidableEq α] {n m k} (S : Finset α)
    (f : α → Inputs n m → Bool) (c : α → ℕ)
    (h : ∀ i ∈ S, Build n m k (f i) (c i)) (hn : S.Nonempty) :
    Build n m k (fun x => decide (∃ i ∈ S, f i x = true)) ((∑ i ∈ S, (c i+1))-1) := by
  induction S using Finset.induction_on with
  | empty => simp at hn
  | @insert i S fresh ih =>
    have A := h i (by simp)
    by_cases non : S.Nonempty
    · have B := ih (fun j hj => h j (by simp [hj])) non
      have pos : 0 < ∑ j ∈ S, (c j+1) := Finset.sum_pos (by intros; omega) non
      apply morph (join A B)
      · rw [Finset.sum_insert fresh]; omega
      · intro x
        rw [Bool.eq_iff_iff]
        simp
    · have e : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp non
      subst S
      apply morph A <;> simp

open Classical in
theorem star {n m} (w : Fin (n+m)) (D : Finset (Fin n × Fin m)) (hn : D.Nonempty)
    (covered : ∀ e ∈ D, Fin.castAdd m e.1 = w ∨ Fin.natAdd n e.2 = w) :
    Build n m .mixed (fun x => decide (∃ e ∈ D,
      x (Fin.castAdd m e.1)=true ∧ x (Fin.natAdd n e.2)=true)) D.card := by
  by_cases side : w.val < n
  · let p : Fin n := ⟨w,side⟩
    have same : ∀ e ∈ D, e.1 = p := by
      intro e he
      rcases covered e he with hp | hl
      · exact Fin.ext (congrArg (fun a : Fin (n+m) => a.val) hp)
      · have eq := congrArg Fin.val hl
        simp [Fin.natAdd] at eq
        omega
    have B := aggregate (k:=.line) D (fun e x => x (Fin.natAdd n e.2)) (fun _ => 0)
      (fun e _ => line e.2) hn
    apply morph (pair B (point p))
    · simp; have := Finset.card_pos.mpr hn; omega
    · intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true,decide_eq_true_iff]
      constructor
      · rintro ⟨⟨e,he,hl⟩,hp⟩
        exact ⟨e,he,same e he ▸ hp,hl⟩
      · rintro ⟨e,he,hp,hl⟩
        exact ⟨⟨e,he,hl⟩,same e he ▸ hp⟩
  · let l : Fin m := ⟨w.val-n,by have := w.isLt; omega⟩
    have same : ∀ e ∈ D, e.2 = l := by
      intro e he
      rcases covered e he with hp | hl
      · have eq := congrArg Fin.val hp
        have := e.1.isLt
        change e.1.val = w.val at eq
        omega
      · have eq := congrArg Fin.val hl
        apply Fin.ext
        change n+e.2.val = w.val at eq
        change e.2.val = w.val-n
        omega
    have B := aggregate (k:=.point) D (fun e x => x (Fin.castAdd m e.1)) (fun _ => 0)
      (fun e _ => point e.1) hn
    apply morph (pair (line l) B)
    · simp; have := Finset.card_pos.mpr hn; omega
    · intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true,decide_eq_true_iff]
      constructor
      · rintro ⟨hl,⟨e,he,hp⟩⟩
        exact ⟨e,he,hp,same e he ▸ hl⟩
      · rintro ⟨e,he,hp,hl⟩
        exact ⟨same e he ▸ hl,⟨e,he,hp⟩⟩

open Classical in
theorem cover {n m} (E : Finset (Fin n × Fin m)) (T : Finset (Fin (n+m))) (hn : E.Nonempty)
    (hc : ∀ e ∈ E, Fin.castAdd m e.1 ∈ T ∨ Fin.natAdd n e.2 ∈ T) :
    Build n m .mixed (fun x => decide (∃ e ∈ E,
      x (Fin.castAdd m e.1)=true ∧ x (Fin.natAdd n e.2)=true)) (E.card+T.card-1) := by
  let own (e : Fin n × Fin m) := if Fin.castAdd m e.1 ∈ T then Fin.castAdd m e.1 else Fin.natAdd n e.2
  let D (w : Fin (n+m)) := E.filter (fun e => own e = w)
  let U := E.image own
  have sub : U ⊆ T := by
    intro w hw
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hw
    unfold own
    split <;> grind
  have stars (w) (hw : w ∈ U) : Build n m .mixed (fun x => decide (∃ e ∈ D w, x (Fin.castAdd m e.1)=true ∧ x (Fin.natAdd n e.2)=true)) (D w).card := by
    obtain ⟨e,he,eq⟩ := Finset.mem_image.mp hw
    have ne : (D w).Nonempty := ⟨e,Finset.mem_filter.mpr ⟨he,eq⟩⟩
    apply star w (D w) ne
    intro a ha
    have eq := (Finset.mem_filter.mp ha).2
    change (if _ then _ else _) = w at eq
    split at eq <;> simp [eq]
  have total := aggregate U _ _ stars (hn.image own)
  apply morph total
  · have sum : E.card = ∑ w ∈ U, (D w).card := Finset.card_eq_sum_card_image own E
    have le := Finset.card_le_card sub
    simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, ← sum]
    omega
  · intro x
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_iff]
    constructor
    · rintro ⟨w,_,e,he,ends⟩
      exact ⟨e,(Finset.mem_filter.mp he).1,ends⟩
    · rintro ⟨e,he,ends⟩
      exact ⟨own e,Finset.mem_image_of_mem _ he,e,Finset.mem_filter.mpr ⟨he,rfl⟩,ends⟩


theorem valid_start (n m) : Valid n m (start n m) := by
  constructor
  · exact ⟨by simp [PEqualNP.EdgeOwnership.AndOrOnly,start],by simp [ReadsBack,start],by simp [start]⟩
  · intro i hi
    exact Or.inl (by simpa [start] using hi)
  · intro i hi
    exact Or.inl (by simpa [start,and_comm] using hi)
  · simp [start]

end PEqualNP.Outside.L_meta_3493_aux

open PEqualNP.Outside.L_meta_3493_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
theorem PEqualNP.Outside.L_meta_3493 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [_x4 : DecidableRel x3] (x5 : Finset (Fin (x1 + x2))), (∀ (x6 : Fin x1) (x7 : Fin x2), x3 x6 x7 → Fin.castAdd x2 x6 ∈ x5 ∨ Fin.natAdd x1 x7 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x7.size ≤ (PEqualNP.ReadTwo.incid x3).card + x5.card - (1 : ℕ) ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x1 + x2 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).inputs = [x13, x14] ∧ x13 ∈ x9 ∧ x14 ∈ x8 := by
  intro n m I decI T hc
  classical
  let E := PEqualNP.ReadTwo.incid I
  have mem (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by simp [E,PEqualNP.ReadTwo.incid]
  have eq (x : Inputs n m) : (∃ e ∈ E, x (Fin.castAdd m e.1)=true ∧ x (Fin.natAdd n e.2)=true) ↔
      ∃ p l, I p l ∧ x (Fin.castAdd m p)=true ∧ x (Fin.natAdd n l)=true := by
    constructor
    · rintro ⟨⟨p,l⟩,he,hp,hl⟩
      exact ⟨p,l,(mem p l).mp he,hp,hl⟩
    · rintro ⟨p,l,hI,hp,hl⟩
      exact ⟨(p,l),(mem p l).mpr hI,hp,hl⟩
  by_cases hn : E.Nonempty
  · have B := cover E T hn (fun e he => hc _ _ ((mem _ _).mp he))
    obtain ⟨u,i,hv,_,cost,_,_,ev⟩ := B (start n m) (valid_start n m) (Ext.refl _)
    refine ⟨⟨u.gs,i⟩,u.ps,u.ls,hv.ao,?_,?_,hv.point,hv.line,hv.cross⟩
    · intro x
      apply (ev x).trans
      exact decide_eq_decide.mpr (eq x)
    · simpa [start,Circuit.size,E] using cost
  · refine ⟨⟨[],n+m⟩,∅,∅,(valid_start n m).ao,?_,by simp [Circuit.size],by simp,by simp,by simp⟩
    intro x
    have no : ¬ ∃ p l, I p l ∧ x (Fin.castAdd m p)=true ∧ x (Fin.natAdd n l)=true := by
      rintro ⟨p,l,hI,_,_⟩
      exact hn ⟨(p,l),(mem p l).mpr hI⟩
    simp [no,circuitFun,Circuit.eval,Circuit.wires]
