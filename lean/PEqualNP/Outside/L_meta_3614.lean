import PEqualNP.Defs
import Mathlib.Data.Fin.Basic

-- The graph bounds and restriction checker are adapted from PressF10's L-meta-1667.
-- Each wire carries a 512-row truth table. We supply the extra input as x₀ ∨ x₆.
-- The promise fixes three endpoint assignments. Correctness on the fourth would
-- make the circuit compute the full edge function with 14 more gates.
-- The finite certificate excludes those circuits by restriction and by counting live wires.
-- A suffix with one more wire than gates partitions separating row pairs into rectangles.
-- With one wire reused, splitting at that wire gives two classes and a shared separator.
-- The final six layers test every remaining gate choice. Hash lookups are checked by
-- comparing the actual wire tables before using the next layer's lower bound.
-- This direct proof adapts the public seeded certificate of JLDC (#7546), based on
-- PressF10 (L-meta-1667), and the wire redirection of #7428 to a 13-gate suffix.
namespace PEqualNP.Outside.L_meta_3614.Seed

open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega

def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h

def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def repeated (w x : Nat) : Bits := BitVec.ofNat 768 (x*(((1 <<< 768)-1)/((1 <<< w)-1)))
def g15samples : Array (Bits × Bits) := #[(repeated 12 0x99d,repeated 12 0x919),(repeated 12 0xed5,repeated 12 0x4c4),(repeated 12 0xf6a,repeated 12 0xa0a),(repeated 12 0x5ba,repeated 12 0x5b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(repeated 96 0xf9ce2bb554a3bac97b2a9d65,repeated 96 0x60e048740030a88143281c44),(repeated 96 0x97ad1ab5bd2d547d6793334b,repeated 96 0x10183680184d04682483210b),(repeated 96 0x65219778a6bd6e36bfd946ac,repeated 96 0x4d60802686b04210115006a4),(repeated 96 0xc213c5eb8bdea95bf6ee7492,repeated 96 0x12934541000824c322ae5002),(repeated 96 0x6a5ee88a4d6be3f71c64aa3f,repeated 96 0xc04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(repeated 6 0x35,repeated 6 0x4),(repeated 6 0x19,repeated 6 0x19),(repeated 6 0x2e,repeated 6 0x24),(repeated 6 0x12,repeated 6 0x12),(0,0),(repeated 6 0x3f,repeated 6 0x3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(repeated 6 0x2b,repeated 6 0x8),(repeated 6 0x35,repeated 6 0x31),(repeated 6 0x1e,repeated 6 0xe),(0,0),(repeated 6 0x26,repeated 6 0x26),(repeated 6 0x39,repeated 6 0x31),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(repeated 6 0x9,repeated 6 0x8),(repeated 6 0x27,repeated 6 0x25),(repeated 6 0x32,repeated 6 0x12),(repeated 6 0x34,repeated 6 0x24),(repeated 6 0x15,repeated 6 0x11),(repeated 6 0x3a,repeated 6 0x32),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(repeated 24 0x727465,repeated 24 0x504444),(repeated 24 0xc6d9cb,repeated 24 0x821909),(repeated 24 0x3d2e52,repeated 24 0x352452),(repeated 24 0x8912bc,repeated 24 0x8812ac),(0,0),(repeated 24 0x3c3ebd,repeated 24 0x2c3ab9),(repeated 24 0xf881fe,repeated 24 0x7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(repeated 6 0xd,repeated 6 0x8),(repeated 6 0x33,repeated 6 0x21),(repeated 6 0x16,repeated 6 0x16),(0,0),(repeated 6 0x3c,repeated 6 0x34),(repeated 6 0x21,repeated 6 0x21),(repeated 6 0x2a,repeated 6 0xa),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(repeated 192 0x1cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,repeated 192 0xb4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(repeated 192 0xd370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,repeated 192 0x5548f0845c253042044cc0e02091152804424943044214c9),(repeated 192 0xe10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,repeated 192 0x201609100358082de8010e0a0c4e080169249024018caa32),(repeated 192 0xb88d0790fae9d8d74f74351d5187af7a955e769667c1914c,repeated 192 0xd049060038a0e052051c011422a1a0780618649266411108),(repeated 192 0x662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,repeated 192 0x550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(repeated 192 0x2d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,repeated 192 0x214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(repeated 6 0x29,repeated 6 0x20),(repeated 6 0x13,repeated 6 0x11),(repeated 6 0x26,repeated 6 0x22),(repeated 6 0x14,repeated 6 0x14),(repeated 6 0x19,repeated 6 0x9),(repeated 6 0x22,repeated 6 0x2),(repeated 6 0x2c,repeated 6 0x2c),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(repeated 6 0x21,0),(repeated 6 0x3b,repeated 6 0x39),(0,0),(repeated 6 0x16,repeated 6 0x12),(repeated 6 0x3c,repeated 6 0x2c),(repeated 6 0x9,repeated 6 0x9),(repeated 6 0x2,repeated 6 0x2),(repeated 6 0x3c,repeated 6 0x34),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(repeated 6 0x31,repeated 6 0x20),(repeated 6 0x23,repeated 6 0x1),(repeated 6 0x6,repeated 6 0x2),(repeated 6 0xc,repeated 6 0x4),(repeated 6 0x19,repeated 6 0x19),(repeated 6 0x2,repeated 6 0x2),(repeated 6 0x14,repeated 6 0x14),(repeated 6 0x28,repeated 6 0x28),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

def initialRows (sampled : Nat → Signals) : List Decor :=
  let v := fun (i : Nat) => (inputs.getD i zero,sampled i)
  [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,dbin true (v 0) (v 6)]
def appendUnion (l : List Decor) := l ++ [dbin true (l.getD 0 defaultDecor) (l.getD 6 defaultDecor)]
lemma appendUnion_faith {l r n} (h : ∀ w∈l, faithful r n w) :
    ∀ w∈appendUnion l, faithful r n w := by
  intro w mem
  rcases List.mem_append.mp mem with old | last
  · exact h w old
  · obtain rfl := List.mem_singleton.mp last
    exact faithful_bin true (faithful_get h _) (faithful_get h _)

def base2303 := initialRows dead.samples
lemma base_faith : ∀ w∈base2303, faithful (asRow fun i => (dead.samples i).1)
    (asRow fun i => (dead.samples i).2) w := by
  have e : base2303=appendUnion (wiresOf dead) := by decide +kernel
  rw [e]
  exact appendUnion_faith (wires_faithful dead)

def ordinaryCut (i : Nat) : Option (Sig × Nat) :=
  if i=0 then some (one,15) else (dead.cols.read (i-1)).map fun c =>
    (subcube c.1 c.2.1,c.2.2.2.2)

theorem ordinaryLower : Lower inputs graph 15 := by
  apply lower_impossible graph_proper _ (dead_start (before_sound known383 valid383) geomdead tablesdead)
  have es : checkEssential graph inputs (graphPairs 511 13438558465)=true := by decide +kernel
  have eq : (graphPairs 511 13438558465).map Prod.fst=inputs := by decide +kernel
  intro a ha
  apply essential_ok es
  rw [eq]
  exact List.mem_toFinset.mpr ha

theorem ordinaryCut_ok {i d lb} (h : ordinaryCut i=some (d,lb)) : Slice inputs graph d lb := by
  have valid := geomdead
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at valid
  unfold ordinaryCut at h
  split at h
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨id,inputs,?_,?_,observe_proper graph_proper,ordinaryLower⟩
    · exact (by decide +kernel : ∀ r : Row, bit r one = true)
    · exact fun w hw => Or.inl (List.mem_map_of_mem hw)
  · obtain ⟨c,e,eq⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    have col := col_sound c (boundsBefore known383) (before_sound known383 valid383)
      (valid.1.2 c (dead.cols.read_mem e))
    have inEq : vars dead.mask = inputs := by decide +kernel
    have tgtEq : chartGoal dead.mask = graph := by decide +kernel
    rw [inEq,tgtEq] at col
    exact col

def pool2303 (bank : List Decor) (depth ops : Nat) (r : Nat × Nat) :=
  (ordinaryCut r.1).bind fun (d,lb) =>
    materialize inputs (chosenSteps bank ops r.2 depth) d lb

theorem pool2303_ok {bank depth ops r p} (h : pool2303 bank depth ops r=some p) :
    ValidPool inputs graph p := by
  obtain ⟨⟨d,lb⟩,hc,hm⟩ := Option.bind_eq_some_iff.mp h
  exact materialize_sound (ordinaryCut_ok hc) hm

abbrev Prefix := Nat × Nat
abbrev Layer := Nat × (Nat → Prefix)
def live2303 (depth : Nat) (s : Prefix) :=
  selectLive s.2 (decodeBank (depth-1) (s.1 >>> 10) base2303)
def bank2303 (depth : Nat) (s : Prefix) := (live2303 depth s).map Prod.fst
def excluded (k depth : Nat) (l : Layer) :=
  ∀ i, i<l.1 → Impossible graph k (bank2303 depth (l.2 i)).toFinset

abbrev Hints := Nat → List (Nat × Nat)
abbrev Index := Nat → Option Nat
def links2303 (depth : Nat) (next : Layer) (idx : Index) (tag : Nat) :=
  ((idx tag).bind fun i => if i<next.1 then some (bank2303 (depth+1) (next.2 i)) else none).toList
def ctx2303 (l next : Layer) (hs : Hints) (idx : Index) (k depth i : Nat) : NodeContext :=
  let s := l.2 i
  let bank := decodeBank (depth-1) (s.1 >>> 10) base2303
  let ws := selectLive s.2 bank
  let pools := (hs i).filterMap (pool2303 bank depth s.1)
  (k,ws.length,ws,preCov ws,pools,links2303 depth next idx)

theorem ctx2303_ok {l next hs idx k depth i} (prior : excluded (k-1) (depth+1) next)
    (h : let c := ctx2303 l next hs idx k depth i
      prelim graph c && testAll c c.2.2.1 = true) :
    Impossible graph k (bank2303 depth (l.2 i)).toFinset := by
  let bank := decodeBank (depth-1) ((l.2 i).1 >>> 10) base2303
  let ws := selectLive (l.2 i).2 bank
  let pools := (hs i).filterMap (pool2303 bank depth (l.2 i).1)
  let ctx := ctx2303 l next hs idx k depth i
  change (prelim graph ctx && testAll ctx ws)=true at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨a,b⟩ := h
  change (decide (ws.map Prod.fst).Nodup && !((ws.map Prod.fst).contains graph)) = true at a
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at a
  have geom := geomdead
  simp only [graphValid,Bool.and_eq_true,beq_iff_eq] at geom
  have prs := chart_pairs geom.1.1.1 geom.1.1.2
  have tgtEq : chartGoal dead.mask = graph := by decide +kernel
  rw [tgtEq] at prs
  apply node_sound (raw:=inputs) (ws:=ws) (pools:=pools) (links:=links2303 depth next idx)
    (T:=graph) (r:=asRow fun j => (dead.samples j).1) (s:=asRow fun j => (dead.samples j).2) prs _ a.1 (by simpa using a.2) _ _ b
  · intro v hv
    exact decode_faithful _ _ _ _ _ base_faith v ((selectLive_sub _ _).subset hv)
  · intro p hp
    obtain ⟨r,_,e⟩ := List.mem_filterMap.mp hp
    exact pool2303_ok e
  · intro tag xs hx
    have e : ((idx tag).bind fun j => if j<next.1 then some (bank2303 (depth+1) (next.2 j)) else none)=some xs := by
      simpa [links2303] using hx
    obtain ⟨j,_,e⟩ := Option.bind_eq_some_iff.mp e
    split at e
    next hj => exact Option.some.inj e ▸ prior j hj
    next => cases e

def span (p : Nat → Bool) : Nat → Nat → Bool
  | 0,_ => true
  | n+1,i => p i && span p n (i+1)
theorem span2303_at {p n i} (h : span p n i=true) (j : Nat) (l : i ≤ j) (u : j < i+n) :
    p j=true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h
    by_cases e : j=i
    · simpa [e] using h.1
    · exact ih h.2 (by omega) (by omega)

def check2303 (l next : Layer) (hs : Hints) (idx : Index) (k depth i : Nat) :=
  let c := ctx2303 l next hs idx k depth i
  prelim graph c && testAll c c.2.2.1

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def unionSeed := bin true (inputs.getD 0 zero) (inputs.getD 6 zero)
def start2303 := inputs ++ [unionSeed]

def probes : List (Sig × Row × Row) := List.ofFn (fun i : Fin 9 =>
  let r : Row := [80,4,2,4,8,1,257,4,8].getD i.val 0
  (inputs.getD i.val zero, r, Fin.ofNat 512 (r.val ||| (1 <<< i.val))))

theorem rootCases {k t S} (run : Live graph k t S) (sub : ∀ v ∈ S, v ∈ start2303) :
    S = inputs.toFinset ∨ S = start2303.toFinset := by
  have checks : checkEssential graph start2303 probes=true := by decide +kernel
  have eq : probes.map Prod.fst=inputs := rfl
  have needed : inputs.toFinset ⊆ S := by
    intro w hw
    rw [←eq] at hw
    obtain ⟨r,s,h,hs⟩ := essential_ok checks w hw
    exact raw_required run start2303 w sub r s h hs
  by_cases use : unionSeed ∈ S
  · right
    apply Finset.Subset.antisymm (fun a h => List.mem_toFinset.mpr (sub a h))
    intro a h
    rcases List.mem_append.mp (List.mem_toFinset.mp h) with old | last
    · exact needed (List.mem_toFinset.mpr old)
    · exact List.mem_singleton.mp last ▸ use
  · left
    refine Finset.Subset.antisymm ?_ needed
    intro a h
    rcases List.mem_append.mp (sub a h) with old | last
    · exact List.mem_toFinset.mpr old
    · exact False.elim (use (List.mem_singleton.mp last ▸ h))

theorem noSeeded (no : Impossible graph 14 start2303.toFinset) (C : Circuit)
    (fan : FanInTwo C) (size : C.size ≤ 14)
    (full : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6]) = edge x) : False := by
  have eq : (execute C.gates start2303).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r _ = bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (fan g hg).1),edge_table]
    have hs : start2303.map (bit r) =
        List.ofFn (sample r) ++ [sample r 0 || sample r 6] := by
      simp only [start2303,List.map_append,List.map_singleton,←sampled,unionSeed,bit_bin]
      rfl
    rw [hs]
    exact full (sample r)
  have out := get_rep (execute C.gates start2303) C.output
  rw [eq] at out
  obtain ⟨k,t,S,hk,h,sub⟩ := extract _ _ fan graph_proper (out.resolve_right (· graph_proper))
  have cap : k ≤ 14 := hk.trans size
  rcases rootCases h sub with rfl | rfl
  · exact dead_start (before_sound known383 valid383) geomdead tablesdead k t cap h
  · exact no k t cap h

def separates (w : Sig) (p q : Row) := bit p w = true ∧ bit q w = false

def rectProtocol (T : Sig) (S : Finset Sig) : Prop :=
  ∃ f : Row → Row → Sig, (∀ p q, f p q ∈ S) ∧
    (∀ p q, separates T p q → separates (f p q) p q) ∧
    ∀ p q r s, f p q = f r s → f p s = f p q

def forkPick (d : Bool) (a b : Sig) (p q : Row) :=
  if (if d then bit p a else !(bit q a)) then a else b

lemma forkPick_mem (d a b p q) : forkPick d a b p q=a ∨ forkPick d a b p q=b := by
  cases d <;> cases hp : bit p a <;> cases hq : bit q a <;> simp [forkPick,hp,hq]

lemma forkPick_sep {d a b p q} (h : separates (bin d a b) p q) :
    separates (forkPick d a b p q) p q := by
  simp only [separates,bit_bin] at h
  cases d <;> cases hp : bit p a <;> cases hq : bit q a <;>
    simp_all [forkPick,separates]

lemma refine_protocol {T U a b d} (an : a ∉ U) (bn : b ∉ U)
    (h : rectProtocol T (insert (bin d a b) U)) :
    rectProtocol T (insert a (insert b U)) := by
  obtain ⟨f,mem,sep,rect⟩ := h
  let z := bin d a b
  let g := fun p q => if f p q=z then forkPick d a b p q else f p q
  have undo (p q) : (if g p q=a ∨ g p q=b then z else g p q) = f p q := by
    by_cases hz : f p q=z
    · simp only [g,hz,ite_true,if_pos (forkPick_mem d a b p q)]
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      have ha : f p q ≠ a := fun e => an (e ▸ hu)
      have hb : f p q ≠ b := fun e => bn (e ▸ hu)
      simp [g,hz,ha,hb]
  refine ⟨g,?_,?_,?_⟩
  · intro p q
    by_cases hz : f p q=z
    · rcases forkPick_mem d a b p q with e|e <;> simp [g,hz,e]
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      simp only [g,if_neg hz]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
  · intro p q st
    by_cases hz : f p q=z
    · have hh : separates z p q := by rw [←hz]; exact sep p q st
      simpa [g,hz] using forkPick_sep (d:=d) (a:=a) (b:=b) hh
    · simpa [g,hz] using sep p q st
  · intro p q r s e
    have eo : f p q=f r s := by rw [← undo p q,← undo r s,e]
    have ec := rect p q r s eo
    by_cases hz : f p q=z
    · have ht : f r s=z := eo.symm.trans hz
      have ep : forkPick d a b p q=forkPick d a b r s := by simpa only [g,hz,ht,ite_true] using e
      simp only [g,ec,hz,ite_true]
      cases d
      · exact ep.symm
      · rfl
    · simp [g,ec,hz]

theorem tight_protocol {T k t S} (h : Live T k t S) (tight : k+1 ≤ S.card) :
    rectProtocol T S := by
  induction h with
  | stop hp => exact ⟨fun _ _ => T,fun _ _ => Finset.mem_singleton_self _,fun _ _ => id,fun _ _ _ _ _ => rfl⟩
  | @unary k t U a hp hf tail ih =>
    have sz := (live_size (Live.unary hp hf tail)).2
    omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    have zu : bin d a b ∉ U := fun m => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have sz := (live_size tail).2
    rw [Finset.card_insert_of_notMem zu] at sz
    have x := Finset.card_insert_le (a:=a) (s:=insert b U)
    have y := Finset.card_insert_le (a:=b) (s:=U)
    have an : a ∉ U := by
      intro am
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem am)] at tight
      omega
    have bn : b ∉ U := by
      intro bm
      rw [Finset.insert_eq_of_mem bm] at tight x
      omega
    apply refine_protocol an bn
    apply ih
    rw [Finset.card_insert_of_notMem zu]
    omega

def forcedPick (T : Sig) (S : Finset Sig) (w : Sig) (p q : Row) :=
  separates T p q ∧ ∀ v ∈ S, separates v p q → v=w

theorem cross_excluded {T S a b p u v q r s} (hne : a ≠ b)
    (w₁ : forcedPick T S a p u) (w₂ : forcedPick T S b p v)
    (w₃ : forcedPick T S a r q) (w₄ : forcedPick T S b s q)
    {k t} (h : Live T k t S) (tight : k+1 ≤ S.card) : False := by
  obtain ⟨f,mem,sep,rect⟩ := tight_protocol h tight
  have pick {z x y} (w : forcedPick T S z x y) := w.2 _ (mem x y) (sep x y w.1)
  have A := rect p u r q ((pick w₁).trans (pick w₃).symm)
  have B := rect p v s q ((pick w₂).trans (pick w₄).symm)
  exact hne ((A.trans (pick w₁)).symm.trans (B.trans (pick w₂)))

def orient (s : Bool) (a : Sig) := if s then neg a else a

def directedSelection (T : Sig) (S : Finset Sig) (sg : Sig → Bool) :=
  ∃ f : Row → Row → Sig, (∀ p q, f p q ∈ S) ∧
    (∀ p q, separates T p q → separates (orient (sg (f p q)) (f p q)) p q) ∧
    ∀ p q r s, f p q=f r s → f p s=f p q

lemma orient_neg (sg : Bool) (a : Sig) : orient sg (neg a) = orient (!sg) a := by
  cases sg <;> simp [orient,neg]

lemma oriented_join (sg d : Bool) (a b : Sig) :
    orient sg (bin d a b) = bin (d != sg) (orient sg a) (orient sg b) := by
  cases sg <;> cases d <;> simp [orient,bin,neg,BitVec.not_or,BitVec.not_and]

def chooseLeft (d : Bool) (a : Sig) (p q : Row) := if d then bit p a else !(bit q a)

lemma split_rect {f : Row → Row → Sig} {U : Finset Sig} {a b z : Sig}
    (an : a∉U) (bn : b∉U) (d : Bool) (w : Sig)
    (mem : ∀ p q, f p q ∈ insert z U)
    (rect : ∀ p q r s, f p q=f r s → f p s=f p q) :
    let g := fun p q => if f p q=z then if chooseLeft d w p q then a else b else f p q
    (∀ p q, g p q ∈ insert a (insert b U)) ∧
    ∀ p q r s, g p q=g r s → g p s=g p q := by
  let g := fun p q => if f p q=z then if chooseLeft d w p q then a else b else f p q
  change (∀ p q, g p q ∈ _) ∧ _
  have undo (p q) : (if g p q=a ∨ g p q=b then z else g p q)=f p q := by
    by_cases hz : f p q=z
    · cases ht : chooseLeft d w p q <;> simp [g,hz,ht]
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      have ha : f p q ≠ a := fun e => an (e ▸ hu)
      have hb : f p q ≠ b := fun e => bn (e ▸ hu)
      simp [g,hz,ha,hb]
  constructor
  · intro p q
    by_cases hz : f p q=z
    · cases ht : chooseLeft d w p q <;> simp [g,hz,ht]
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      simp only [g,if_neg hz]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
  · intro p q r s e
    change g p q=g r s at e
    change g p s=g p q
    have eo : f p q=f r s := by rw [← undo p q,← undo r s,e]
    have ec := rect p q r s eo
    by_cases hz : f p q=z
    · have ht : f r s=z := eo.symm.trans hz
      simp only [g,hz,ht,ite_true] at e
      simp only [g,ec,hz,ite_true]
      cases d
      · exact e.symm
      · rfl
    · simp [g,ec,hz]

theorem signed_formula {T k t S} (h : Live T k t S) (linear : k+1≤S.card+t) :
    ∃ sg : Sig → Bool, directedSelection T S sg := by
  induction h with
  | stop hp => exact ⟨fun _ => false,fun _ _ => T,fun _ _ => Finset.mem_singleton_self _,fun _ _ => id,fun _ _ _ _ _ => rfl⟩
  | @unary k t U a hp hf tail ih =>
    let z := neg a
    have zu : z ∉ U := fun m => hf (Finset.mem_insert_of_mem m)
    have sz := (live_size tail).2
    rw [Finset.card_insert_of_notMem zu] at sz
    have xu := Finset.card_insert_le (a:=a) (s:=U)
    have an : a ∉ U := by
      intro am
      rw [Finset.insert_eq_of_mem am] at linear
      omega
    have st : k+1 ≤ (insert z U).card+t := by rw [Finset.card_insert_of_notMem zu]; omega
    obtain ⟨sg,f,mem,sep,rect⟩ := ih st
    let g := fun p q => if f p q=z then a else f p q
    let sg' := fun x => if x=a then !(sg z) else sg x
    have sm := split_rect an an false a mem rect
    simp only [ite_self,Finset.insert_idem] at sm
    refine ⟨sg',g,sm.1,?_,sm.2⟩
    intro p q hT
    have hit := sep p q hT
    by_cases hz : f p q=z
    · simp only [hz] at hit
      simpa [g,hz,sg',z,orient_neg] using hit
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      have ha : f p q ≠ a := fun e => an (e ▸ hu)
      simpa [g,hz,sg',ha] using hit
  | @binary k t U a b d ha hb hab hf tail ih =>
    let z := bin d a b
    have zu : z ∉ U := fun m => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have sz := (live_size tail).2
    rw [Finset.card_insert_of_notMem zu] at sz
    have x := Finset.card_insert_le (a:=a) (s:=insert b U)
    have y := Finset.card_insert_le (a:=b) (s:=U)
    have an : a ∉ U := by
      intro am
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem am)] at linear
      omega
    have bn : b ∉ U := by
      intro bm
      rw [Finset.insert_eq_of_mem bm] at linear x
      omega
    have st : k+1 ≤ (insert z U).card+t := by rw [Finset.card_insert_of_notMem zu]; omega
    obtain ⟨sg,f,mem,sep,rect⟩ := ih st
    let e := d != sg z
    let x' := orient (sg z) a
    let g := fun p q => if f p q=z then if chooseLeft e x' p q then a else b else f p q
    let sg' := fun x => if x=a ∨ x=b then sg z else sg x
    have sm := split_rect an bn e x' mem rect
    refine ⟨sg',g,sm.1,?_,sm.2⟩
    intro p q hT
    have hit := sep p q hT
    by_cases hz : f p q=z
    · have hgate : separates (bin e x' (orient (sg z) b)) p q := by
        rw [hz] at hit
        exact (oriented_join (sg z) d a b) ▸ hit
      have yes := forkPick_sep hgate
      change separates (if chooseLeft e x' p q then x' else orient (sg z) b) p q at yes
      cases hsel : chooseLeft e x' p q <;> simpa [g,hz,hsel,sg',x',hab,Ne.symm hab] using yes
    · have hu := (Finset.mem_insert.mp (mem p q)).resolve_left hz
      have neA : f p q≠a := fun e => an (e ▸ hu)
      have neB : f p q≠b := fun e => bn (e ▸ hu)
      simpa [g,hz,sg',neA,neB] using hit

def clash (T : Sig) (S : Finset Sig) (a b : Sig) : Prop :=
  a∈S ∧ b∈S ∧ a≠b ∧ ∃ p u v q r s,
    forcedPick T S a p u ∧ forcedPick T S b p v ∧ forcedPick T S a r q ∧ forcedPick T S b s q

lemma protocol_consistent {T S a b} (h : rectProtocol T S) (c : clash T S a b) : False := by
  obtain ⟨f,mem,sep,rect⟩ := h
  obtain ⟨_,_,ne,p,u,v,q,r,s,w₁,w₂,w₃,w₄⟩ := c
  have pick {z x y} (w : forcedPick T S z x y) := w.2 _ (mem x y) (sep x y w.1)
  have A := rect p u r q ((pick w₁).trans (pick w₃).symm)
  have B := rect p v s q ((pick w₂).trans (pick w₄).symm)
  exact ne ((A.trans (pick w₁)).symm.trans (B.trans (pick w₂)))

lemma join_separates {a b d p q} (h : separates (bin d a b) p q) :
    separates a p q ∨ separates b p q := by
  rcases forkPick_mem d a b p q with e | e
  · exact Or.inl (e ▸ forkPick_sep h)
  · exact Or.inr (e ▸ forkPick_sep h)

def carrier (a b z w : Sig) := if w=a ∨ w=b then z else w

lemma transfer_forced {T U a b d w p q}
    (safe : w∈U → w≠a ∧ w≠b) (h : forcedPick T (insert a (insert b U)) w p q) :
    forcedPick T (insert (bin d a b) U) (carrier a b (bin d a b) w) p q := by
  refine ⟨h.1,?_⟩
  intro x hx sp
  rcases Finset.mem_insert.mp hx with rfl | hu
  · rcases join_separates sp with x | x
    · have eq := h.2 a (by simp) x
      simp [carrier,eq.symm]
    · have eq := h.2 b (by simp) x
      simp [carrier,eq.symm]
  · have eq := h.2 x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) sp
    subst x
    simp [carrier,(safe hu).1,(safe hu).2]

lemma forced_on_run {T k t S w p q} (run : Live T k t S) (m : t=0) (h : forcedPick T S w p q) :
    w∈S ∧ separates w p q := by
  obtain ⟨v,hv,sp⟩ := mono_row_difference run m h.1.1 h.1.2
  exact h.2 v hv sp ▸ And.intro hv sp

lemma gate_protocol (d : Bool) (a b : Sig) : rectProtocol (bin d a b) {a,b} := by
  refine ⟨forkPick d a b,?_,fun _ _ => forkPick_sep,?_⟩
  · intro p q
    rcases forkPick_mem d a b p q with e | e <;> simp [e]
  · intro p q r s eq
    cases d
    · exact eq.symm
    · rfl

lemma transfer_clash {T k t U a b d i j}
    (fresh : bin d a b∉insert a (insert b U)) (tail : Live T k t (insert (bin d a b) U)) (m : t=0)
    (si : i∈U → i≠a ∧ i≠b) (sj : j∈U → j≠a ∧ j≠b)
    (c : clash T (insert a (insert b U)) i j) :
    clash T (insert (bin d a b) U) (carrier a b (bin d a b) i) (carrier a b (bin d a b) j) := by
  let z := bin d a b
  obtain ⟨im,jm,ne,p,u,v,q,r,s,w₁,w₂,w₃,w₄⟩ := c
  have a₁ := transfer_forced (d:=d) si w₁
  have a₂ := transfer_forced (d:=d) sj w₂
  have a₃ := transfer_forced (d:=d) si w₃
  have a₄ := transfer_forced (d:=d) sj w₄
  refine ⟨(forced_on_run tail m a₁).1,(forced_on_run tail m a₂).1,?_,p,u,v,q,r,s,a₁,a₂,a₃,a₄⟩
  intro same
  by_cases hI : i=a ∨ i=b <;> by_cases hJ : j=a ∨ j=b
  · have gateForced {w x y} (sw : w∈U → w≠a ∧ w≠b) (old : forcedPick T (insert a (insert b U)) w x y)
        (ab : w=a ∨ w=b) : forcedPick z {a,b} w x y := by
      have sp := (forced_on_run tail m (transfer_forced (d:=d) sw old)).2
      refine ⟨by simpa [carrier,ab,z] using sp,?_⟩
      intro v hv sv
      apply old.2 v _ sv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · simp
      · simp [Finset.mem_singleton.mp hv]
    apply protocol_consistent (gate_protocol d a b) (a:=i) (b:=j)
    exact ⟨by simpa using hI,by simpa using hJ,ne,p,u,v,q,r,s,
      gateForced si w₁ hI,gateForced sj w₂ hJ,gateForced si w₃ hI,gateForced sj w₄ hJ⟩
  · simp only [carrier,if_pos hI,if_neg hJ] at same
    exact fresh (same ▸ jm)
  · simp only [carrier,if_neg hI,if_pos hJ] at same
    exact fresh (same ▸ im)
  · exact ne (by simpa [carrier,hI,hJ] using same)

def divides (T : Sig) (S : Finset Sig) :=
  ∃ (color : Sig → Bool) (h : Sig),
    (∀ p q, separates h p q → ∃ v∈S, color v=true ∧ separates v p q) ∧
    (∀ p q, separates T p q → separates h p q ∨ ∃ v∈S, color v=false ∧ separates v p q) ∧
    ∀ i j, clash T S i j → color i≠color j

lemma divides_gate {T k t U a b d}
    (an : a∉U) (bn : b∉U) (fresh : bin d a b∉insert a (insert b U))
    (tail : Live T k t (insert (bin d a b) U)) (m : t=0)
    (rest : divides T (insert (bin d a b) U)) : divides T (insert a (insert b U)) := by
  obtain ⟨c,h,inside,outside,ok⟩ := rest
  let f := carrier a b (bin d a b)
  refine ⟨fun w => c (f w),h,?_,?_,?_⟩
  · intro p q hit
    obtain ⟨v,mem,clr,sp⟩ := inside p q hit
    rcases Finset.mem_insert.mp mem with rfl | hu
    · rcases join_separates sp with left | right
      · exact ⟨a,by simp,by simpa [f,carrier] using clr,left⟩
      · exact ⟨b,by simp,by simpa [f,carrier] using clr,right⟩
    · have na : v≠a := fun e => an (e ▸ hu)
      have nb : v≠b := fun e => bn (e ▸ hu)
      exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),by simpa [f,carrier,na,nb] using clr,sp⟩
  · intro p q hit
    rcases outside p q hit with sp | ⟨v,mem,clr,sp⟩
    · exact Or.inl sp
    · right
      rcases Finset.mem_insert.mp mem with rfl | hu
      · rcases join_separates sp with left | right
        · exact ⟨a,by simp,by simpa [f,carrier] using clr,left⟩
        · exact ⟨b,by simp,by simpa [f,carrier] using clr,right⟩
      · have na : v≠a := fun e => an (e ▸ hu)
        have nb : v≠b := fun e => bn (e ▸ hu)
        exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),by simpa [f,carrier,na,nb] using clr,sp⟩
  · intro i j bad
    apply ok _ _ (transfer_clash fresh tail m _ _ bad)
    all_goals intro hu; exact ⟨fun e => an (e ▸ hu),fun e => bn (e ▸ hu)⟩

lemma divides_retained {T k t U a b d}
    (ha : proper a) (hb : proper b) (hab : a≠b) (fresh : bin d a b∉insert a (insert b U))
    (tail : Live T k t (insert (bin d a b) U)) (m : t=0) (prot : rectProtocol T (insert (bin d a b) U))
    (shared : Sig) (ha' : a∈U → a=shared) (hb' : b∈U → b=shared) (mem : shared∈insert a (insert b U)) :
    divides T (insert a (insert b U)) := by
  refine ⟨fun w => decide (w=shared),shared,?_,?_,?_⟩
  · intro p q h
    exact ⟨shared,mem,by simp,h⟩
  · intro p q h
    obtain ⟨v,hv,sp⟩ := mono_row_difference (Live.binary ha hb hab fresh tail) m h.1 h.2
    by_cases eq : v=shared
    · exact Or.inl (eq ▸ sp)
    · exact Or.inr ⟨v,hv,by simpa using eq,sp⟩
  · intro i j c same
    by_cases iS : i=shared <;> by_cases jS : j=shared
    · exact c.2.2.1 (iS.trans jS.symm)
    · simp [iS,jS] at same
    · simp [iS,jS] at same
    · have safe (v) (ns : v≠shared) (hu : v∈U) : v≠a ∧ v≠b :=
        ⟨fun e => ns (e.trans (ha' (e ▸ hu))),fun e => ns (e.trans (hb' (e ▸ hu)))⟩
      exact protocol_consistent prot (transfer_clash fresh tail m (safe i iS) (safe j jS) c)

theorem one_fork {T k t S} (run : Live T k t S) (m : t=0) (budget : k≤S.card) : divides T S := by
  induction run with
  | stop hp =>
    exact ⟨fun _ => true,T,fun p q h => ⟨T,by simp,rfl,h⟩,fun _ _ h => Or.inl h,
      fun _ _ c => False.elim (c.2.2.1 ((Finset.mem_singleton.mp c.1).trans (Finset.mem_singleton.mp c.2.1).symm))⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    have zu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have sz := (live_size tail).2
    rw [Finset.card_insert_of_notMem zu] at sz
    have x := Finset.card_insert_le (a:=a) (s:=insert b U)
    have y := Finset.card_insert_le (a:=b) (s:=U)
    by_cases am : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem am)] at budget
      have tight : k+1≤(insert (bin d a b) U).card := by rw [Finset.card_insert_of_notMem zu]; omega
      apply divides_retained ha hb hab hf tail m (tight_protocol tail tight) a (fun _ => rfl) _ (by simp)
      intro bm
      rw [Finset.insert_eq_of_mem bm] at budget
      omega
    · by_cases bm : b∈U
      · rw [Finset.insert_eq_of_mem bm] at budget x
        have tight : k+1≤(insert (bin d a b) U).card := by rw [Finset.card_insert_of_notMem zu]; omega
        exact divides_retained ha hb hab hf tail m (tight_protocol tail tight) b (fun hm => False.elim (am hm)) (fun _ => rfl) (by simp)
      · apply divides_gate am bm hf tail m (ih m ?_)
        rw [Finset.card_insert_of_notMem zu]
        omega

abbrev Cell := BitVec 768
abbrev Square := Fin 27
def pRow (j : Nat) : Row := (#[3,6,12,24,17,33,66,132,264,160,320,288,41,394,21,11,292,44,265,152,77,74,212,105,101,262,38] : Array Row)[j]?.getD 0
def nRow (j : Nat) : Row := (#[42,50,69,104,116,138,201,208,261,276,385,402,10,84,73,5,200,400,258,100,146,274,112,386,260,137,36] : Array Row)[j]?.getD 0
def gridP (i : Fin 768) := pRow (i.val/27 % 27)
def gridN (i : Fin 768) := nRow (i.val % 27)

lemma gridYes : ∀ i : Square, bit (pRow i.val) graph=true := by decide +kernel
lemma gridNo : ∀ i : Square, bit (nRow i.val) graph=false := by decide +kernel

def uniq2303 {α : Type} (c : α → Cell) : List α → Cell × Cell
  | [] => (0,0)
  | a::l => let u := uniq2303 c l
            (c a ||| u.1,(c a &&& ~~~u.1) ||| (u.2 &&& ~~~(c a)))

lemma marked {α : Type} (c : α → Cell) (xs : List α) (i : Fin 768) :
    ((uniq2303 c xs).1.getLsbD i.val=true ↔ ∃ a∈xs, (c a).getLsbD i.val=true) ∧
    ((uniq2303 c xs).2.getLsbD i.val=true → ∀ a∈xs, ∀ b∈xs,
      (c a).getLsbD i.val=true → (c b).getLsbD i.val=true → a=b) := by
  induction xs with
  | nil => simp [uniq2303]
  | cons x xs ih =>
    obtain ⟨exist,uniq⟩ := ih
    simp only [uniq2303,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,
      i.isLt,decide_true,Bool.true_and,Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',
      List.mem_cons,exists_eq_or_imp]
    refine ⟨by rw [exist],?_⟩
    rintro (first|later) a (rfl|am) b (rfl|bm) aa bb
    all_goals first | rfl | exact uniq later.1 _ am _ bm aa bb |
      exact False.elim (Bool.noConfusion (later.2.symm.trans aa)) |
      exact False.elim (Bool.noConfusion (later.2.symm.trans bb)) |
      exact False.elim (Bool.noConfusion (first.2.symm.trans (exist.mpr ⟨_,am,aa⟩))) |
      exact False.elim (Bool.noConfusion (first.2.symm.trans (exist.mpr ⟨_,bm,bb⟩)))

lemma nonzero_cell {b : Cell} (h : b≠0) : ∃ i : Fin 768, b.getLsbD i.val=true := by
  by_contra! hh
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa using hh ⟨i,hi⟩

abbrev View := Sig × Signals × Signals
def views (ws gs : List Decor) : List View :=
  ws.zipWith (fun w g => (w.1,w.2,g.2)) gs
def validViews (r s : Fin 768 → Row) (xs : List View) :=
  ∀ x∈xs, x.2.1=pairSig r s x.1 ∧ x.2.2=pairSig gridP gridN x.1
def cellDiff (v : View) := v.2.1.1 ^^^ v.2.1.2
def marks (xs : List View) := (uniq2303 cellDiff xs).2
def req2303 (u : Cell) (v : View) (rev : Bool) :=
  let (p,n) := v.2.1
  if rev then (u &&& n &&& ~~~p)!=0 else (u &&& p &&& ~~~n)!=0

lemma selected_sign {r s xs sg} (ok : validViews r s xs) (good : properPairs graph r s)
    (sel : directedSelection graph (xs.map Prod.fst).toFinset sg)
    {v} (mem : v∈xs) (rev : Bool) (req : req2303 (marks xs) v rev=true) : sg v.1=rev := by
  obtain ⟨f,fm,sep,rect⟩ := sel
  have locate (i : Fin 768) (u : (marks xs).getLsbD i.val=true)
      (different : (cellDiff v).getLsbD i.val=true) :
      separates (orient (sg v.1) v.1) (r i) (s i) := by
    have yes := sep (r i) (s i) (good i)
    obtain ⟨w,wm,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp (fm (r i) (s i)))
    rw [←eq] at yes
    have wn : (cellDiff w).getLsbD i.val=true := by
      simp only [cellDiff,(ok w wm).1,pairSig,BitVec.getLsbD_xor,ofRows_bit]
      cases hm : sg w.1 <;> cases hp : bit (r i) w.1 <;> cases hq : bit (s i) w.1 <;>
        simp_all [separates,orient,bit_neg]
    have e := (marked cellDiff xs i).2 u w wm v mem wn different
    simpa [e] using yes
  have vals (i : Fin 768) : v.2.1.1.getLsbD i.val=bit (r i) v.1 ∧ v.2.1.2.getLsbD i.val=bit (s i) v.1 := by
    rw [(ok v mem).1]
    exact ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩
  cases rev
  · have hn : marks xs &&& v.2.1.1 &&& ~~~v.2.1.2 ≠ 0 := by simpa [req2303] using req
    obtain ⟨i,hb⟩ := nonzero_cell hn
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and,
      Bool.and_eq_true,Bool.not_eq_true'] at hb
    have ht := locate i hb.1.1 (by simp only [cellDiff,BitVec.getLsbD_xor,hb.1.2,hb.2]; rfl)
    have p := (vals i).1.symm.trans hb.1.2
    cases hh : sg v.1 <;> simp_all [separates,orient,bit_neg]
  · have hn : marks xs &&& v.2.1.2 &&& ~~~v.2.1.1 ≠ 0 := by simpa [req2303] using req
    obtain ⟨i,hb⟩ := nonzero_cell hn
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and,
      Bool.and_eq_true,Bool.not_eq_true'] at hb
    have ht := locate i hb.1.1 (by simp only [cellDiff,BitVec.getLsbD_xor,hb.1.2,hb.2]; rfl)
    have p := (vals i).1.symm.trans hb.2
    cases hh : sg v.1 <;> simp_all [separates,orient,bit_neg]

def monoCell (v : View) := v.2.2.1 &&& ~~~v.2.2.2
def revCell (v : View) := ~~~v.2.2.1 &&& v.2.2.2
def withSigns (u : Cell) (v : View) :=
  if req2303 u v false then monoCell v else if req2303 u v true then revCell v else
    v.2.2.1 ^^^ v.2.2.2

def gridSound (xs : List View) (col : View → Cell) (val : Sig → Sig) :=
  ∀ w ∈ xs, ∀ p q : Square, separates (val w.1) (pRow p.val) (nRow q.val) →
     (col w).getLsbD (27*p.val+q.val)=true

lemma grid_vals {r s xs} (ok : validViews r s xs) {w} (mem : w∈xs) (p q : Square) :
    w.2.2.1.getLsbD (27*p.val+q.val)=bit (pRow p.val) w.1 ∧
    w.2.2.2.getLsbD (27*p.val+q.val)=bit (nRow q.val) w.1 := by
  let i : Fin 768 := ⟨27*p.val+q.val,by omega⟩
  have hP : gridP i=pRow p.val := by simp only [gridP,i]; congr 1; omega
  have hN : gridN i=nRow q.val := by simp only [gridN,i]; congr 1; omega
  rw [(ok w mem).2]
  exact ⟨(ofRows_bit _ _ i).trans (hP ▸ rfl),(ofRows_bit _ _ i).trans (hN ▸ rfl)⟩

lemma mono_grid {r s xs} (ok : validViews r s xs) : gridSound xs monoCell id := by
  intro w mem p q h
  obtain ⟨hp,hn⟩ := grid_vals ok mem p q
  have lt : 27*p.val+q.val<768 := by omega
  change separates w.1 (pRow p.val) (nRow q.val) at h
  simp only [monoCell,BitVec.getLsbD_and,BitVec.getLsbD_not,lt,decide_true,Bool.true_and,hp,hn,h.1,h.2,Bool.not_false,Bool.and_self]

lemma signed_grid {r s xs sg} (ok : validViews r s xs) (good : properPairs graph r s)
    (sel : directedSelection graph (xs.map Prod.fst).toFinset sg) :
    gridSound xs (withSigns (marks xs)) (fun a => orient (sg a) a) := by
  intro w mem p q h
  obtain ⟨hp,hn⟩ := grid_vals ok mem p q
  have lt : 27*p.val+q.val<768 := by omega
  have determine := selected_sign ok good sel mem
  unfold withSigns
  split
  next eq =>
    have hh := determine false eq
    simpa [hh,orient] using (mono_grid ok w mem p q (by simpa [hh,orient] using h))
  next eq =>
    split
    next ei =>
      have hh := determine true ei
      simp only [hh,orient,ite_true,separates,bit_neg,Bool.not_eq_true',Bool.not_eq_false'] at h
      simp only [revCell,BitVec.getLsbD_and,BitVec.getLsbD_not,lt,decide_true,Bool.true_and,hp,hn,h.1,h.2,Bool.not_false,Bool.and_self]
    next ei =>
      cases hh : sg w.1 <;> cases a : bit (pRow p.val) w.1 <;> cases b : bit (nRow q.val) w.1 <;>
        simp_all [separates,orient,bit_neg]

def marg (v : Nat) : Nat × Nat :=
  let rows := ((1 <<< 729)-1)/134217727
  let x := v &&& ((1 <<< 729)-1)
  let high := (x ||| ((x &&& (rows*67108863))+rows*67108863)) &&& (rows <<< 26)
  let occupied := (((high >>> 26)*(((1 <<< 702)-1)/67108863)) >>> 676) &&& 134217727
  let cols := x
  let cols := cols ||| (cols >>> 27)
  let cols := cols ||| (cols >>> 54)
  let cols := cols ||| (cols >>> 108)
  let cols := cols ||| (cols >>> 216)
  let cols := cols ||| (cols >>> 432)
  (occupied,cols &&& 134217727)

abbrev Info := Sig × Cell × Cell × Nat × Nat
def infos2303 (xs : List View) (c : View → Cell) : List Info :=
  let all := (uniq2303 c xs).2
  xs.map fun w =>
    let u := all &&& c w
    let pq := marg u.toNat
    (w.1,c w,u,pq)
def validXY (v : Cell) (p q : Nat) :=
  decide (p<27 ∧ q<27) && v.getLsbD (27*p+q)

def inRow (v : Cell) (p : Nat) := ((v.toNat >>> (27*p))%134217728).log2
def gridUnit := ((1 <<< 729)-1)/134217727
def inCol (v : Cell) (q : Nat) := (v.toNat &&& (gridUnit <<< q)).log2/27

def edgeGrid (a b : Info) :=
  let mp := a.2.2.2.1 &&& b.2.2.2.1
  let mq := a.2.2.2.2 &&& b.2.2.2.2
  if mp==0 || mq==0 || a.1==b.1 then false else
    let p := mp.log2
    let q := mq.log2
    let x := a.2.2.1
    let y := b.2.2.1
    validXY x p (inRow x p) && validXY y p (inRow y p) &&
      validXY x (inCol x q) q && validXY y (inCol y q) q

def forcedValue (S : Finset Sig) (val : Sig → Sig) (w : Sig) (p q : Row) :=
  separates graph p q ∧ ∀ v∈S, separates (val v) p q → v=w
def valueClash (S : Finset Sig) (val : Sig → Sig) (a b : Sig) :=
  a∈S ∧ b∈S ∧ a≠b ∧ ∃ p u v q r s, forcedValue S val a p u ∧ forcedValue S val b p v ∧
    forcedValue S val a r q ∧ forcedValue S val b s q

lemma forced_cell {xs c val} (h : gridSound xs c val) {a p q}
    (mem : a∈infos2303 xs c) (test : validXY a.2.2.1 p q=true) :
    forcedValue (xs.map Prod.fst).toFinset val a.1 (pRow p) (nRow q) := by
  obtain ⟨w,wm,rfl⟩ := List.mem_map.mp mem
  simp only [validXY,Bool.and_eq_true,decide_eq_true_eq] at test
  obtain ⟨⟨hp,hq⟩,v⟩ := test
  let i : Fin 768 := ⟨27*p+q,by omega⟩
  change (((uniq2303 c xs).2 &&& c w).getLsbD i.val)=true at v
  simp only [BitVec.getLsbD_and,Bool.and_eq_true] at v
  refine ⟨⟨gridYes ⟨p,hp⟩,gridNo ⟨q,hq⟩⟩,?_⟩
  intro a am sp
  obtain ⟨b,bm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp am)
  exact congrArg Prod.fst ((marked c xs i).2 v.1 b bm w wm (h b bm ⟨p,hp⟩ ⟨q,hq⟩ sp) v.2)

lemma info_mem {xs c a} (h : a∈infos2303 xs c) : a.1∈(xs.map Prod.fst).toFinset := by
  obtain ⟨w,wm,rfl⟩ := List.mem_map.mp h
  exact List.mem_toFinset.mpr (List.mem_map_of_mem wm)

lemma edge_grid_sound {xs c val} (h : gridSound xs c val) {a b}
    (am : a∈infos2303 xs c) (bm : b∈infos2303 xs c) (test : edgeGrid a b=true) :
    valueClash (xs.map Prod.fst).toFinset val a.1 b.1 := by
  simp only [edgeGrid] at test
  split at test
  next => contradiction
  next ok =>
    have ne : a.1≠b.1 := fun e => ok (by simp [e])
    simp only [Bool.and_eq_true] at test
    exact ⟨info_mem am,info_mem bm,ne,_,_,_,_,_,_,forced_cell h am test.1.1.1,
      forced_cell h bm test.1.1.2,forced_cell h am test.1.2,forced_cell h bm test.2⟩

lemma signed_edge_bad {S sg a b} (h : directedSelection graph S sg)
    (e : valueClash S (fun w => orient (sg w) w) a b) : False := by
  obtain ⟨f,mem,sep,rect⟩ := h
  obtain ⟨_,_,ne,p,u,v,q,r,s,w₁,w₂,w₃,w₄⟩ := e
  have pick {z x y} (w : forcedValue S (fun w => orient (sg w) w) z x y) :=
    w.2 _ (mem x y) (sep x y w.1)
  have A := rect p u r q ((pick w₁).trans (pick w₃).symm)
  have B := rect p v s q ((pick w₂).trans (pick w₄).symm)
  exact ne ((A.trans (pick w₁)).symm.trans (B.trans (pick w₂)))

def allGrid : Cell := BitVec.ofNat 768 ((1 <<< 729)-1)
def missingGrid (seen : Cell) :=
  let j := (allGrid &&& ~~~seen).toNat.log2
  decide (j<729) && !(seen.getLsbD j)
def miss2303 (xs : List View) (c : View → Cell) :=
  missingGrid (uniq2303 c xs).1

lemma seen_of_cell {xs : List View} {c j} (lt : j<768)
    {b} (mem : b∈xs) (hit : (c b : Cell).getLsbD j=true) :
    (uniq2303 c xs).1.getLsbD j=true :=
  (marked c xs ⟨j,lt⟩).1.mpr ⟨b,mem,hit⟩

lemma grid_total {xs c val} (gd : gridSound xs c val)
    (complete : ∀ p q, separates graph p q → ∃ w ∈ (xs.map Prod.fst).toFinset, separates (val w) p q)
    (h : miss2303 xs c=true) : False := by
  let seen := (uniq2303 c xs).1
  let j := (allGrid &&& ~~~seen).toNat.log2
  change (decide (j<729) && !(seen.getLsbD j))=true at h
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
  let p : Square := ⟨j/27,by omega⟩
  let q : Square := ⟨j % 27,by omega⟩
  obtain ⟨a,am,sp⟩ := complete (pRow p.val) (nRow q.val) ⟨gridYes p,gridNo q⟩
  obtain ⟨b,bm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp am)
  have idx : 27*p.val+q.val=j := by dsimp [p,q]; omega
  have hit := gd b bm p q sp
  rw [idx] at hit
  have jl : j<768 := Nat.lt_trans h.1 (by decide : 729<768)
  have reached : seen.getLsbD j=true := seen_of_cell (c:=c) jl bm hit
  exact Bool.noConfusion (h.2.symm.trans reached)

def findEdge : List Info → Bool
  | [] => false
  | a::l => l.any (edgeGrid a) || findEdge l
lemma findEdge_found {l : List Info} (h : findEdge l=true) :
    ∃ a∈l, ∃ b∈l, edgeGrid a b=true := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    simp only [findEdge,Bool.or_eq_true,List.any_eq_true] at h
    rcases h with ⟨b,bm,e⟩ | tail
    · exact ⟨a,by simp,b,List.mem_cons_of_mem _ bm,e⟩
    · obtain ⟨x,xm,y,ym,e⟩ := ih tail
      exact ⟨x,List.mem_cons_of_mem _ xm,y,List.mem_cons_of_mem _ ym,e⟩

def rectCut (xs : List View) (c : View → Cell) :=
  miss2303 xs c || findEdge (infos2303 xs c)

lemma rectCut_bad {xs c sg} (sel : directedSelection graph (xs.map Prod.fst).toFinset sg)
    (gd : gridSound xs c (fun w => orient (sg w) w)) (h : rectCut xs c=true) : False := by
  simp only [rectCut,Bool.or_eq_true] at h
  rcases h with miss | hit
  · apply grid_total gd _ miss
    obtain ⟨f,fm,sep,rect⟩ := sel
    exact fun p q h => ⟨f p q,fm p q,sep p q h⟩
  · obtain ⟨a,am,b,bm,e⟩ := findEdge_found hit
    exact signed_edge_bad sel (edge_grid_sound gd am bm e)

def cols2303 : List Info → Cell
  | [] => 0
  | v::l => v.2.1 ||| cols2303 l
lemma cols_hit {xs : List Info} {v j} (mem : v∈xs) (hit : v.2.1.getLsbD j=true) :
    (cols2303 xs).getLsbD j=true := by
  induction xs with
  | nil => contradiction
  | cons a l ih =>
    simp only [cols2303,BitVec.getLsbD_or,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl | hm
    · exact Or.inl hit
    · exact Or.inr (ih hm)

def lacks (v : Cell) (p q : Nat) :=
  decide (p<27 ∧ q<27) && !(v.getLsbD (27*p+q))
def noPart (within outside : Cell) :=
  let need := allGrid &&& ~~~outside
  let x := need.toNat
  let units := gridUnit
  let low := units*67108863
  let rows := ((x ||| ((x &&& low)+low)) &&& (units <<< 26)) >>> 26
  let cols := (marg x).2
  let missing := (rows*cols) &&& (~~~within).toNat
  if missing==0 then false else
    let j := missing.log2
    let p := j/27
    let q := j % 27
    lacks outside p (inRow need p) && lacks outside (inCol need q) q &&
      lacks within p q

lemma noPart_witness {within outside} (h : noPart within outside=true) :
    ∃ p u v q : Square, outside.getLsbD (27*p.val+u.val)=false ∧
      outside.getLsbD (27*v.val+q.val)=false ∧ within.getLsbD (27*p.val+q.val)=false := by
  unfold noPart at h
  dsimp only at h
  split at h
  next => contradiction
  next =>
    simp only [lacks,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
    exact ⟨⟨_,h.1.1.1.1⟩,⟨_,h.1.1.1.2⟩,⟨_,h.1.2.1.1⟩,⟨_,h.2.1.2⟩,h.1.1.2,h.1.2.2,h.2.2⟩

lemma joint_hit {a b : List Info} {v j} (mem : v∈a ∨ v∈b) (hit : v.2.1.getLsbD j=true) :
    (cols2303 a ||| cols2303 b).getLsbD j=true := by
  rw [BitVec.getLsbD_or,Bool.or_eq_true]
  exact mem.imp (fun h => cols_hit h hit) (fun h => cols_hit h hit)

def area (v : Info) :=
  let count := fun (x : Nat) =>
    let x := x - ((x >>> 1) &&& 1431655765)
    let x := (x &&& 858993459) + ((x >>> 2) &&& 858993459)
    ((((x+(x >>> 4)) &&& 252645135)*16843009) >>> 24) % 256
  count v.2.2.2.1 * count v.2.2.2.2
def order (l : List Info) := l.insertionSort (fun a b => area b≤area a)

def scanPart (inside outside : List Info) : List Info → Bool
  | [] => noPart (cols2303 inside ||| cols2303 []) (cols2303 outside ||| cols2303 [])
  | v::l =>
    let free := cols2303 (v::l)
    (decide (l.length<4) && noPart (cols2303 inside ||| free) (cols2303 outside ||| free)) ||
    ((inside.any (edgeGrid v) || scanPart (v::inside) outside l) &&
    (outside.any (edgeGrid v) || scanPart inside (v::outside) l))

lemma scanPart_bad {xs} (g : gridSound xs monoCell id)
    (D : divides graph (xs.map Prod.fst).toFinset)
    (pass : scanPart [] [] (order (infos2303 xs monoCell))=true) : False := by
  obtain ⟨color,h,inner,outer,proper⟩ := D
  let infos := infos2303 xs monoCell
  have close (l inside outside : List Info) (covered : ∀ a∈infos, a∈l ∨ a∈inside ∨ a∈outside)
      (inOK : ∀ a∈inside, a∈infos ∧ color a.1=true)
      (outOK : ∀ a∈outside, a∈infos ∧ color a.1=false)
      (test : noPart (cols2303 inside ||| cols2303 l) (cols2303 outside ||| cols2303 l)=true) : False := by
    obtain ⟨p,u,v,q,pu,vq,pq⟩ := noPart_witness test
    have force (p q : Square) (missing : (cols2303 outside ||| cols2303 l).getLsbD (27*p.val+q.val)=false) :
        separates h (pRow p.val) (nRow q.val) := by
      rcases outer _ _ ⟨gridYes p,gridNo q⟩ with hit | ⟨a,am,clr,sp⟩
      · exact hit
      · obtain ⟨w,wm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp am)
        let z : Info := (w.1,monoCell w,(uniq2303 monoCell xs).2 &&& monoCell w,
          marg ((uniq2303 monoCell xs).2 &&& monoCell w).toNat)
        have zm : z∈infos := List.mem_map_of_mem wm
        rcases covered z zm with bad | ins | outs
        · exact False.elim (Bool.noConfusion (missing.symm.trans (joint_hit (Or.inr bad) (g w wm p q sp))))
        · exact False.elim (Bool.noConfusion (clr.symm.trans (inOK z ins).2))
        · exact False.elim (Bool.noConfusion (missing.symm.trans (joint_hit (Or.inl outs) (g w wm p q sp))))
    have x := force p u pu
    have y := force v q vq
    obtain ⟨a,am,clr,sp⟩ := inner _ _ ⟨x.1,y.2⟩
    obtain ⟨w,wm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp am)
    let z : Info := (w.1,monoCell w,(uniq2303 monoCell xs).2 &&& monoCell w,
      marg ((uniq2303 monoCell xs).2 &&& monoCell w).toNat)
    have zm : z∈infos := List.mem_map_of_mem wm
    rcases covered z zm with bad | ins | outs
    · exact Bool.noConfusion (pq.symm.trans (joint_hit (Or.inr bad) (g w wm p q sp)))
    · exact Bool.noConfusion (pq.symm.trans (joint_hit (Or.inl ins) (g w wm p q sp)))
    · exact Bool.noConfusion (clr.symm.trans (outOK z outs).2)
  have go (l inside outside : List Info) (covered : ∀ a∈infos, a∈l ∨ a∈inside ∨ a∈outside)
      (sub : ∀ a∈l, a∈infos)
      (inOK : ∀ a∈inside, a∈infos ∧ color a.1=true)
      (outOK : ∀ a∈outside, a∈infos ∧ color a.1=false)
      (test : scanPart inside outside l=true) : False := by
    induction l generalizing inside outside with
    | nil =>
      apply close [] inside outside covered inOK outOK
      exact test
    | cons x l ih =>
      have xm := sub x (by simp)
      have sm (a) (am : a∈l) := sub a (List.mem_cons_of_mem _ am)
      have dis (v) (vm : v∈infos) (e : edgeGrid x v=true) : color x.1≠color v.1 :=
        proper _ _ (edge_grid_sound g xm vm e)
      simp only [scanPart,Bool.and_eq_true,Bool.or_eq_true,List.any_eq_true] at test
      rcases test with stop | test
      · exact close (x::l) inside outside covered inOK outOK stop.2
      cases cx : color x.1
      · rcases test.2 with ⟨v,vm,e⟩ | tail
        · exact dis v (outOK v vm).1 e (cx.trans (outOK v vm).2.symm)
        · apply ih inside (x::outside) _ sm inOK _ tail
          · intro a am
            rcases covered a am with first | si | so
            · rcases List.mem_cons.mp first with rfl | mem
              · exact Or.inr (Or.inr (by simp))
              · exact Or.inl mem
            · exact Or.inr (Or.inl si)
            · exact Or.inr (Or.inr (List.mem_cons_of_mem _ so))
          · intro a am
            rcases List.mem_cons.mp am with rfl | mem
            · exact ⟨xm,cx⟩
            · exact outOK a mem
      · rcases test.1 with ⟨v,vm,e⟩ | tail
        · exact dis v (inOK v vm).1 e (cx.trans (inOK v vm).2.symm)
        · apply ih (x::inside) outside _ sm _ outOK tail
          · intro a am
            rcases covered a am with first | si | so
            · rcases List.mem_cons.mp first with rfl | mem
              · exact Or.inr (Or.inl (by simp))
              · exact Or.inl mem
            · exact Or.inr (Or.inl (List.mem_cons_of_mem _ si))
            · exact Or.inr (Or.inr so)
          · intro a am
            rcases List.mem_cons.mp am with rfl | mem
            · exact ⟨xm,cx⟩
            · exact inOK a mem
  exact go (order infos) [] [] (fun _ hm => Or.inl ((List.mem_insertionSort _).mpr hm))
    (fun _ hm => (List.mem_insertionSort _).mp hm) (by simp) (by simp) pass

def terminal (cap : Nat) (xs : List View) :=
  if xs.length>cap then rectCut xs monoCell else
    decide (cap≤xs.length) && rectCut xs (withSigns (marks xs)) &&
    (miss2303 xs monoCell || scanPart [] [] (order (infos2303 xs monoCell)))

theorem terminal_ok {r s xs cap} (ok : validViews r s xs) (pairs : properPairs graph r s)
    (nd : (xs.map Prod.fst).Nodup) (test : terminal cap xs=true) :
    Impossible graph cap (xs.map Prod.fst).toFinset := by
  intro k t bound run
  have len : (xs.map Prod.fst).toFinset.card=xs.length := by
    rw [List.toFinset_card_of_nodup nd,List.length_map]
  have g := mono_grid ok
  have sz := (live_size run).2
  unfold terminal at test
  split at test
  next hi =>
    obtain ⟨f,mem,sep,rect⟩ := tight_protocol run (by omega)
    exact rectCut_bad (sg:=fun _ => false) ⟨f,mem,sep,rect⟩ g test
  next le =>
    simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true] at test
    by_cases m : t=0
    · rcases test.2 with miss | part
      · apply grid_total g _ miss
        exact fun p q hit => mono_row_difference run m hit.1 hit.2
      · exact scanPart_bad g (one_fork run m (by omega)) part
    · obtain ⟨sg,sel⟩ := signed_formula run (by omega)
      exact rectCut_bad sel (signed_grid ok pairs sel) test.1.2

def pCols (j : Nat) : Bits := (#[0xffffffe00000000000007ffffffffffffe00000000000007ffffff0000001ffffffc0000000000000fffffffffffffc0000007ffffff00000000000000000000000000000000000000003fffffffffffff000000000000000000007ffffff,0xfffffffffffffffffffffff800000000000000000003ffffff8000000000000000000000000000000000ffffffe0000003ffffff80000000000000000000000000000000000000001ffffffc000000000000000000000000003fffffffffffff,0xfff0000001ffffffffffffffffffff0000001ffffffc0000007ffffff00000000000003fffffffffffff0000001ffffffc0000000000000000000000000000000000000000ffffffe000000000000000000000000001fffffffffffff8000000,0xffffffe0000003fffffffffffffffffffffffffffffffff8000000ffffffe0000003fffffffffffff000000000000000000007ffffff000000000000000000000000000fffffffffffffc0000000000000,0x1ffffffc0000000000000ffffffe000000000000000000000000001ffffffc0000000000000000000000000000000000000000000000000000000000007ffffffffffffe00000000000000000000,0x1ffffffc0000007ffffffffffffe0000000000000000000000000000000003fffffffffffff000000000000000000007ffffffffffffe0000003ffffff800000000000000000003ffffff8000000000000000000000000000000000,0x7fffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000001ffffffc00000000000000000001ffffffc0000000000000000000000000000000000000000,0x1ffffffc0000000000000ffffffe0000000000000000000000000000000003ffffff800000000000000000003ffffff8000000ffffffe00000000000000000000000000000000000000000000000,0x3ffffff80000000000000000000000000000000000000001ffffffc0000007ffffff00000000000003ffffff8000000fffffffffffffc0000007ffffff000000000000000000000000000000000000000000000000000000] : Array Bits)[j]?.getD 0
def nCols (j : Nat) : Bits := (#[0x5444018a8880315110062a2200c5444018a8880315110062a2200c5444018a8880315110062a2200c5444018a8880315110062a2200c5444018a8880315110062a2200c5444018a8880315110062a2200c5444018a8880315110062a2200c544,0x82316830462d0608c5a0c118b4182316830462d0608c5a0c118b4182316830462d0608c5a0c118b4182316830462d0608c5a0c118b4182316830462d0608c5a0c118b4182316830462d0608c5a0c118b4182316830462d0608c5a0c118b41823,0x314a1146294228c5284518a508a314a1146294228c5284518a508a314a1146294228c5284518a508a314a1146294228c5284518a508a314a1146294228c5284518a508a314a1146294228c5284518a508a314a1146294228c5284518a508a314,0x69402a0d280541a500a834a015069402a0d280541a500a834a015069402a0d280541a500a834a015069402a0d280541a500a834a015069402a0d280541a500a834a015069402a0d280541a500a834a015069402a0d280541a500a834a015069,0xa920e455241c8aa483915490722a920e455241c8aa483915490722a920e455241c8aa483915490722a920e455241c8aa483915490722a920e455241c8aa483915490722a920e455241c8aa483915490722a920e455241c8aa483915490722a92,0x1b8900037120006e24000dc48001b8900037120006e24000dc48001b8900037120006e24000dc48001b8900037120006e24000dc48001b8900037120006e24000dc48001b8900037120006e24000dc48001b8900037120006e24000dc48001b,0xdc092c1b8125837024b06e04960dc092c1b8125837024b06e04960dc092c1b8125837024b06e04960dc092c1b8125837024b06e04960dc092c1b8125837024b06e04960dc092c1b8125837024b06e04960dc092c1b8125837024b06e04960dc,0xce052619c0a4c33814986702930ce052619c0a4c33814986702930ce052619c0a4c33814986702930ce052619c0a4c33814986702930ce052619c0a4c33814986702930ce052619c0a4c33814986702930ce052619c0a4c33814986702930ce0,0xf0034c1e006983c00d307801a60f0034c1e006983c00d307801a60f0034c1e006983c00d307801a60f0034c1e006983c00d307801a60f0034c1e006983c00d307801a60f0034c1e006983c00d307801a60f0034c1e006983c00d307801a60f00] : Array Bits)[j]?.getD 0
def gridBase := initialRows (fun i => (pCols i,nCols i))
lemma gridBaseFaith : ∀ v∈gridBase, faithful gridP gridN v := by
  have hp : asRow pCols=gridP := by funext i; revert i; decide +kernel
  have hn : asRow nCols=gridN := by funext i; revert i; decide +kernel
  have e : gridBase=appendUnion (rawDecor 511 pCols nCols) := by decide +kernel
  rw [e,←hp,←hn]
  exact appendUnion_faith (raw_faithful _ _ _)

lemma zip_cert {r s : Fin 768 → Row} {ws gs : List Decor}
    (same : ws.map Prod.fst = gs.map Prod.fst)
    (aw : ∀ w∈ws, faithful r s w) (ag : ∀ w∈gs, faithful gridP gridN w) :
    (views ws gs).map Prod.fst = ws.map Prod.fst ∧ validViews r s (views ws gs) := by
  induction ws generalizing gs with
  | nil => cases gs <;> simp_all [views,validViews]
  | cons w ws ih =>
    cases gs with
    | nil => simp at same
    | cons g gs =>
      simp only [List.map_cons,List.cons.injEq] at same
      have past := ih same.2 (fun _ hm => aw _ (List.mem_cons_of_mem _ hm))
        (fun _ hm => ag _ (List.mem_cons_of_mem _ hm))
      constructor
      · simp only [views,List.zipWith_cons_cons,List.map_cons,List.cons.injEq,true_and]
        exact past.1
      · intro v vm
        rcases List.mem_cons.mp vm with rfl | hm
        · exact ⟨aw w (by simp),by rw [same.1]; exact ag g (by simp)⟩
        · exact past.2 v hm

def gridLive (depth : Nat) (s : Prefix) :=
  selectLive s.2 (decodeBank (depth-1) (s.1 >>> 10) gridBase)
def verifiedTerminal (cap depth : Nat) (s : Prefix) :=
  let ws := live2303 depth s
  let gs := gridLive depth s
  ws.map Prod.fst == gs.map Prod.fst && decide (ws.map Prod.fst).Nodup &&
    terminal cap (views ws gs)

lemma verifiedTerminal_ok {cap depth s} (pass : verifiedTerminal cap depth s=true) :
    Impossible graph cap (bank2303 depth s).toFinset := by
  simp only [verifiedTerminal,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at pass
  let r := asRow fun j => (dead.samples j).1
  let n := asRow fun j => (dead.samples j).2
  have ow (v) (hm : v∈live2303 depth s) : faithful r n v :=
    decode_faithful _ _ _ _ _ base_faith v ((selectLive_sub _ _).subset hm)
  have og (v) (hm : v∈gridLive depth s) : faithful gridP gridN v :=
    decode_faithful _ _ _ _ _ gridBaseFaith v ((selectLive_sub _ _).subset hm)
  obtain ⟨eq,ok⟩ := zip_cert pass.1.1 ow og
  have geom := geomdead
  simp only [graphValid,Bool.and_eq_true,beq_iff_eq] at geom
  have prs := chart_pairs geom.1.1.1 geom.1.1.2
  have tgtEq : chartGoal dead.mask=graph := by decide +kernel
  rw [tgtEq] at prs
  have ans := terminal_ok ok prs (eq ▸ pass.1.2) pass.2
  rwa [eq] at ans

def pc2303 (x : Nat) : Nat := let x := x - ((x >>> 1) &&& 1431655765); let x := (x &&& 858993459) + ((x >>> 2) &&& 858993459); let x := (x+(x >>> 4)) &&& 252645135; ((x*16843009) >>> 24)%256
def selectedRules (w : Nat) : Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | n+1,x,m => if m==0 then [] else let tail := selectedRules w n (x >>> w) (m >>> 1); if m.testBit 0 then let a := x &&& ((1 <<< w)-1); (a % 128,a/128)::tail else tail
def a0shiftb0 : Array Nat := #[0x0]
def a0shift (i : Nat) : Nat := a0shiftb0[i % 16]?.getD 0
def a0idx : Index := fun x => let v := x*(x+701)%618970019642690137449562111; let h := v ^^^ (v >>> 37); let j := (h/1+packedAt a0shift ((h % 1)*1) 1)%1; some j
def a0book0 : Array Nat := #[0x1,0x12a0f07c675371b39]
def a0book (i : Nat) : Nat := a0book0[i % 8]?.getD 1
def a0ranksb0 : Array Nat := #[0x0]
def a0ranks (i : Nat) : Nat := a0ranksb0[i % 16]?.getD 0
def a0tbitsb0 : Array Nat := #[0x1]
def a0tbits (i : Nat) : Nat := a0tbitsb0[i % 16]?.getD 0
def a0expanded (i : Nat) := packedAt a0tbits i 1==1
def a0rank (i : Nat) := packedAt a0ranks (i/32*1) 1 + pc2303 (packedAt a0tbits (i/32*32) (i % 32))
def a0gidb0 : Array Nat := #[0x1]
def a0gid (i : Nat) : Nat := a0gidb0[i % 16]?.getD 0
def a0pickb0 : Array Nat := #[0xff]
def a0pick (i : Nat) : Nat := a0pickb0[i % 16]?.getD 0
def a0hints : Hints := fun i => let g := packedAt a0gid ((a0rank i)*1) 1; selectedRules 8 8 (a0book g) (packedAt a0pick ((a0rank i)*8) 8)
def a0layer : Layer := (1,fun _ => (352,1023))
def a1shiftb0 : Array Nat := #[0x802d60c08ef203081010200082281182]
def a1shift (i : Nat) : Nat := a1shiftb0[i % 16]?.getD 0
def a1idx : Index := fun x => let v := x*(x+701)%618970019642690137449562111; let h := v ^^^ (v >>> 37); let j := (h/22+packedAt a1shift ((h % 22)*6) 6)%71; some j
def a1book0 : Array Nat := #[0x1,0x1348a81e3380a3c470f6b2aa5487839da722450dd4ea3be34dc841b,0x12513cc65a35a8654c61c21f8c8f838ed547687dd5ac7564ce63737,0x1250e0260743a858d07554a91fc687b5993379c8eaea5f1d86e3639,0x15541c3301634a81e389c9684860038a80775e306e36c99ba84f042,0x15521dac996489054a10781c761b9ccdeea766a0e0ebc61d46c8439,0x1302aa0e381523c0f01ba80d93c69c83cea013b0e66e3a6b2863678,0x1952aa1ec69b8920e391b86eeac943a3c027520b5b8c788d9d8843a]
def a1book8 : Array Nat := #[0x201cc9daebc69ca84ea3b]
def a1book (i : Nat) : Nat := (if i<8 then a1book0 else a1book8)[i % 8]?.getD 1
def a1ranksb0 : Array Nat := #[0xf8f80]
def a1ranks (i : Nat) : Nat := a1ranksb0[i % 16]?.getD 0
def a1tbitsb0 : Array Nat := #[0x7f7ffffffffffffffe]
def a1tbits (i : Nat) : Nat := a1tbitsb0[i % 16]?.getD 0
def a1expanded (i : Nat) := packedAt a1tbits i 1==1
def a1rank (i : Nat) := packedAt a1ranks (i/32*7) 7 + pc2303 (packedAt a1tbits (i/32*32) (i % 32))
def a1gidb0 : Array Nat := #[0x132111713645127812421364245416825322416432331352147224551752223717726]
def a1gid (i : Nat) : Nat := a1gidb0[i % 16]?.getD 0
def a1pickb0 : Array Nat := #[0x807fab092c6b002ac7559a55012a5d012a5da3003800014a64c3aa4420f2001ecf00207500050bc5846f0440b2000135012a5d266f160001110216cf002acf00102d08034b02163a02179e4581cd2c1ec285a15d227a5d82442b0000da005ce70001130dd06b0080ef085db60a5e2a087adc001747021eab822e7b0260c701586b10ebac012a5d022facd1051c1194ef012a5d15811c400d2904cc67023847201eae02e25500021b057e3900822602c8740082cf0229960080ef00ea7b002242012a5d10144d080c4d0100ef31882c]
def a1pick (i : Nat) : Nat := a1pickb0[i % 16]?.getD 0
def a1hints : Hints := fun i => let g := packedAt a1gid ((a1rank i)*4) 4; selectedRules 9 24 (a1book g) (packedAt a1pick ((a1rank i)*24) 24)
def a1codesb0 : Array Nat := #[0xe99e88e77e55e44e33e22e11e00995994993992991965964963961589580579510299255233222195194193192191189187185184183182181180179175174173172171170154153152151150143142141132131130121120110095093092053052032]
def a1codes (i : Nat) : Nat := a1codesb0[i % 16]?.getD 0
def a1rowsb0 : Array Nat := #[0x1f103e0f39391c130c0b24373026173204391e03283d0633351d0e180d09382e2a230a19202d293141153b3a0739142511390022123c36342c1b2b2f0140160805391a273f0221]
def a1rows (i : Nat) : Nat := a1rowsb0[i % 16]?.getD 0
def a1layer : Layer := (71,fun i => let v := packedAt a1rows (i*8) 8; let p := a0layer.2 (v/128); let v := packedAt a1codes (v % 128*12) 12; let op := v % 1024; let a := op % 16; let b := op/16 % 16; let mask := if v.testBit 10 then p.2 ^^^ (1 <<< a) else p.2; let mask := if v.testBit 11 && a != b then mask ^^^ (1 <<< b) else mask; (p.1+(op <<< 10),mask+(1 <<< 10)))
def a2shiftb0 : Array Nat := #[0x19014010bc012643622c410080001c265500011c03010010e4020340314c4d00007000550103500091120040c40f3717802e3820c10254000400c0bc087d8020001103c041840232c020981f0c43e0042f0c40629801aec2d00c760340b2d8b5008591b8010b80900c0103a33208000040000003030050000e0011f47dd9020060040367de02516b01434044010107c020101e808050240ec9508c5c0008a0386419c07000071385f1e93c18c1302c7a24c250140012007014031ac051e48a0140607c58018001a80c054853ec010005f2b84d02800018000109244c360642509026000bf0001a09c0401c03068a44940d2180738413004590fc1900800000020102204c070040413c0f19c1c0e402008170180003c003280000c023300006c0b00000158000740302c08024060fc0f00c2502453010990f8160dc0402004000850000100400178ee0606401c020102702c530183c02c3d000250003803832044030b037044000e0120001305c0c30c090340f18c03000151444214c1d0a46301c0d09c010081e0740000004000030440000c0002816098060442e00404000050080207c0f0240b0000d00027008070241303403014660105c010000006700002040020d005000030204b0043303c000d8040002003803088160400100c0e004030740100c000bc1301846000150f83b00014018000d8010ac3409023024353f4010000c01807008230380401c0302c260100a000000700803001000250040000040048040104307c1c0105a01c060280500c060385108804078000300303c280000d008000240d0000300c250740003c1307426004040600800000040590a8000286e010080000002c020040110c0300804008030140001000008640d0080200c000010000000c040000101402068040040e040000981c00000004000081900006]
def a2shift (i : Nat) : Nat := a2shiftb0[i % 16]?.getD 0
def a2idx : Index := fun x => let v := x*(x+701)%618970019642690137449562111; let h := v ^^^ (v >>> 37); let j := (h/539+packedAt a2shift ((h % 539)*10) 10)%1661; some j
def a2book0 : Array Nat := #[0x1,0x18e2998ef2a0918f021e02a999c3f60367191648f04c7bc0d384edaacdcc9,0x136a9921c24c3f607818f0ff19665878e9aa3655a0f9c60e8170ec7b56639,0x1781c66672ab80aad83460eeaa0f7198eec616a990e90f0fa0a8e87b09239,0x136b035a53b4e11a969c61da870f98f366c69642e1a073090785d47b46c42,0x1d1ac6718740d18fc0d3b168790cd9961da14cc761edd60912446c3510a75,0x5c66645ab1a871e746c1c24a653bc6476c0e381c12a2a86798c7b8ee75,0x1b82c6a1c12d83467823ac0caa0b3070e8100c83b71987cdca108e1b8e63b]
def a2book8 : Array Nat := #[0x1d1ac6568da43caad820f23de081f0308e837185a564d90f8020ec7bcde1b,0x1a3eaa464931a855518224a90f5804a36a87f19031f073c6d78cdd4214c29,0x163cca4e21a6a81faaa8f0217612b07ca86a8ec24c3f0332476b504286d75,0x1369c6a665ad18e3b198758d99c1e3bc647683f034e0d95ae594ec7b09175,0x171b60666e083f465acebb1a3bc66990fa2ac1e870fd0f0ee3a1ec241e239,0x1d82c6caa997830fa3f466aa01c645a719871e5990e98f0bd131ec3b1e239,0x1d82c6ca9e0aab1966476d19c618c106ab038ed3863c8704c5a5d7372853b,0x1b82991ede06648f0930f2a852057604e3198e3038ec5a16d3b0f8d6cdec9]
def a2book16 : Array Nat := #[0x1aaa8f665c6c6468d186a63c3e6ab2a46842c0d6321d3881d694eec946d75,0x1d81e071b19a674607d388e036c0ca184caa1aae0b1a8f8ec5aa1c24cdc42,0x1b1aaaa1e0118f6004b2a8e513d1b074e303285e0719aa61c78cdd8f0ee1b,0x1d81e0aaa8332a0f1f15aca80263c23c3daa529874e159c0f370edc65d61b,0x1a3e870c83013f01aa84a08838a850f0eec658103b5b1b16b37b25781ed42,0x1c64daa670f4e07b09d0fa1f608ef0396ae08e024aaa8fb19a19651bcdc42,0x1aab2ac1de066760b824a61e9983c3bc650f9303fa1e3a0bc248eec675a39,0x1ca9aac3d8fc1c5c2a987c0c8f1d8878ec38e67398046886fc60d47b16275]
def a2book24 : Array Nat := #[0x1d82e0d19e096a8fa1f0786814c0ec64ed2a8e2592aa693663b9d7376861b,0x1ca9aa3182e2a85ac3f07f18870fed6b2438a8424dd71b0ee3a0f8351ee39,0x1c052a467c6a3c38aa85a0edd6129031f16004c221bb1ba8737b246a50978,0x1464300ec381644243c4a5d6c64e56006903407370911bb59a1c6d42b2578,0x1caaaaa1e4fd1a1a92887d822a2ab0fb828f8e042c0ec68eca11691b86f37,0x1ca92ac1d754e4aaa3c5a21c430e3c6406a109276b243b75b393a71b5e275,0x1cab0f23e0712a3b0377501caaa3daa5810f0e10315f1bcdd781603e86ec9,0x18292ad1ac6c0c598e087d820fc1caac3e87b8319a3e9916b378ea3b35a39]
def a2book32 : Array Nat := #[0x1d831963ee012a99528303283b0903e7183a0e05883f758ee38c6dd672639,0x1aaa834e12aa3c7b583c643f01a1c740bf1b0e33741c3540d785d53ba86d6,0x1b8360cab034e04b52aaa53c4e1ec027803fb183e6a9871e3377193986c3b,0x1aaa87a0d2aa3d601eed67244a63d0f0e0071682ab2633cdd035e17586c58,0x1d8346ca92aa3ee043ec640c384e3030f907dd6aa21e3bc6e0f4ef37b261b,0x171b2ad1aaa6671943d8f81f0f0ef754e16bb270308d3b06c8716b375d458,0x1781c6c1d874e32ad82e02aa1321ec6d1a3b0caaa46e381093b04f03cdca1,0x1c3e8f2aa38ca812d1b6016aaa8ab07a1ee02860743c8fc0ec68e63b86f37]
def a2book40 : Array Nat := #[0x1d8346c64360ca99b8238aa86fb1a39a3f07c0e3ba1f375d4a146c7635842,0x1a671986ac69a74681d87c3e63a3e87aa8a1c1f2a10a3846f038edc686e75,0x1d1b6096b2ab830fa1ec6c6459146138e2aaa3e991da59c0cd6cdcc98ed75,0x1a3d875d432c6f03088090e043113754de3816ac98edd66843b86c588e578,0x1c3c6f0ca768e9763add6dd70721f3709339c6e755d6390e03bb583ea847b,0x1d831bd1b2a09038c66e0b1aaaa64aa8eea1dd5c621ca105a3a3683e0ee39,0x1b82aaa654ad1a8753e0f63d998ede0cab60c67076a9878e83a0eda171a39,0x1d1ae08e2aa0ba0fd830716b2ab1a8fa663b80719a1e4cc3e3a17cd61e239]
def a2book48 : Array Nat := #[0x1f1b2aaab1b0598fa1d9923ec6cdf750b2c9e643b0f4d90e8245d9a10f93a,0x1b18321f45904c2216a8ff184a4aaa1a1ed60e10faa8744e3391ef1bb2575,0x1128c6aa8aa168e3092c90e32ac3d760ef0136775c6f3735975ce4a13247b,0x1ca9aa8a8aa0584f091d60ec137184a8e822c6ec90e238dd63b685c90fa39,0x16a975ca999c0539c64ca0c94a8e6aa0f9011ed4ff18240eea15e1c69e073,0x141c2213c3b0b301aa8244646a368525813b40c350e31bb5b3735aa15e2c9,0x1a3e8312e87727c610c38aa90f4a96041c0f759750bd0388f373257886c58,0x19805a0c82280c38b271ba0f600ef2ab81d6c3eaaa3e3b687039e33786cc9]
def a2book56 : Array Nat := #[0x1c65991ad6318d076a842cab467198fc3d6b358a161d3bc1f030ed3886d75,0x163d87d8138a3ee052b0fd184281ec6caaaac1daaa1dc683f038ef375d61b,0x1ca9aac6699aaad6f1a8f8e033c3c7b9ac238ec3bc1e87c0cd606e7516175,0x1d1ac60da4fa6719d8307b80aac3e8f10a877521b8e30316a3bcde75090d6,0x1cab0fa1d75c1caa10c8f12c448ee2308f03dd47b5e03b75b370bcc986c58,0x13185a6a999c647b1884a23caadd72a4e18f8ef0fc0d3bcdec93261b5d458,0x1d1aaaa6719c0e382a8878ef0f8e466b183bcab0736aa19d71b0fbc609078,0x112b2ac3c872a87932a7616239093750e2a1b243bce7371ee75358d10fb1b]
def a2book64 : Array Nat := #[0x18e20f81f1bdd5aacab467196b58e3b41c35c3d9963f07c658775a390ec78,0x1d82c6aa9e0a1f2a5283fc663a28599c3d1b6a82463d877183b8e5c910878,0x1d19c631b0fc659916b079d6aa0fb750e2a11c31bce4243683bcdec99e07b,0x12aa8f10fc6ca90f19b014a8246aaaace4386843b4e5764071ba85785d6c9,0x16a90f9812a8abc6c6d3aa1e0340c38aab010ec53dd6780d43ecdea1686c9,0x1c1e8721d0746458dd4e30b976cdc240e2d624c3b687010d739358785d4a1,0x1d1ac6c66990fd38c3eaaa3f074ab398e507f187d14a2aa1d7528701a8478,0x1d1b2a4a8b0c66c60ec38aa8d6a670fdd430c6e8fcdf012860ace4c91e07b]
def a2book72 : Array Nat := #[0x14a88714c4b048075828f189030083eaa90f0a61b00d78cdfc650b1b1e05a,0x1aa842049c60c803a1ea1b59604a97556a8f40d0746fc6c6d420eb3708978,0x14640f88c1ac044a7182f46fc66871b41d60a1d2a40f375794256a1ba8578,0x10ed191081a04d8f15d0f1a8386852aaa960c6d1b40cd6b5822cdd7850ac9,0x1a1d878e027a86608ab3781e03069aa46e4275a398ee1b9e03bf1b7568442,0x1c3d8fc1f0323c871e4638eed66a87b6860f0a61b8aa03160c9b271b5d478,0x1d82e075aaaa1c7b0bf2af18aac1dc65d4da21f03dd68f8ec23a873786c58,0x1ca9e0d8187aaae08ab0fd1a8f63daac1ec6c0f37a1d7575aa18ec3b9d61b]
def a2book80 : Array Nat := #[0x1c3ec6aab468e18f5d83bc1f607823b4edaa71b2aa1d75c0dc96861bcdea1,0x183c3bdd7607272a08f0f5d98fb82aac65aa06e8fc0d7571a998ec2fcdec9,0x16aa99666e063c620ec428ee8fc6760aab2ac0f37c3c789d6383243d46ec9,0x1c0c8f2a85a0b824f185921f75c1e39c3f37c6ed61ec3386c3e0ee3b16078,0x1cab1b0b82f1bc38dd43ec1caa35aa1ce57621d754e7c61ee421d8242843b,0x1caaaaa1d2a41c6603c5af188f0931b1da2321f7515f3986da11eec90ef37,0x1465031483ba1d2a0ba8f1d107b587d1a85543e750d7c61ed751683ac6c78,0x1b82c6c3dc6c0c3e63c3fd823a0cf071ee8f7813b4e79961e39cde1b0edd6]
def a2book88 : Array Nat := #[0x1caaaac3c384a91923ceb8e61b02a42ce5a10ed76b24aa97cc9c6c7809175,0x16aa8fb258f43ed61284c0efc6b1a2a83e5f5d5878e3751623bc6dc90ea39,0x1d1b3935b2a3270f13daadd719cdc24665c61ed5944d8f36a390ee3b86e78,0x16872a129768ec9332ad60f838cddd61630f0ec242aa3add575ce71b3245f,0x14a90f10c33b258f8ce80891a116ad6a850110bc64e6875d5d6c6c3b5e21b,0x1b26758e42486439806d6981a183e03b1901a873717dc975a4271b1b1e278,0x19812a41e030e01ab243b0b2240516035903c0678f1a1b75b375e2d4684a1,0x171a8fa1c5a0b939dd5aa759a163d870087bb59c96658386c5c1603b9d435]
def a2book96 : Array Nat := #[0x10685af1924cab6012b0f98303719aa80ea13253846dd6cde7886dd472642,0x1c3d87a8799d1a87ca9e01093b0ee0763f074e11b21f60c0c2386da1cddd6,0x1d186ba3c3ba1d7675b0fd83998e07b8ef074a975b24aac0e1b162d6cdea1,0x13832a63f0fc0c4b31b372a88f0b81b8e487dd4787582f15c3e1ecc986c3b,0x1a3e8743c8fb1976b5b398e7371edc641caa5d63386f7510887908da0ec24,0x1aa84d4a86818c22a3e750ace90be8743e391bbc60811b41c58c6dd686c78,0x1d1b2a8ab0771a0718c3f4a9074646a0ec4e6a9879e242687c6c6e391d878,0x18a822a1e070ef990902c0e187dd63a6a98f75a76f1a758ee387271b68639]
def a2book104 : Array Nat := #[0x1c1c4ace6c90da7546fc6cde23036c650939a3f75aaa871ec760921b15c3b,0x1519390253741d8f0282cc6e5ea3f75aaa5f4a90f5d457b25780f83a86c3b,0x143ceb16a2a0ae0f18b759d47d8ea3b63daa1d03bf1b990fb1b726391e076,0x1718aa0585a0918fb243add5aacab99c3e3a0ee76ce6758e71b0f87b1e1c9,0x1c3f1b61c4a4ec1a0e0190d0206a8aa75a390e835490c96843d72424dd442,0x1a86d64a90f0901f40c4cb181a467750d4385d624aa8741625f68478b2442,0x10918fa860f0bb390fc2d0be3b0e501719d60804e68638f1a757271b8e478,0x16a9600a81940c2e00f01dd4380098f61d78cdc1b75a39c6ec90ec3aa8476]
def a2book112 : Array Nat := #[0x10484a0f41300d5e34687725c64aaa143d6041dd6cdd031695ac6c785e21b,0x108a07c1fc66858fc672aaa8a198238d822a43e037531bc0c24cde7846ec9,0x5e010c428e04a8931983c5a324245e0d6c3f6052938c0ed40ce1bcddd6,0x1719466a8380890f61c7406d8fa3e39c6c574a93841fc6ce6a11e03b86d75,0x16aa0f9d85a8ea381ac3e0edc66647bdd63bc6d8f61c2c9d4351da39109d6,0x17832ac3f391794a4e7375d83edd58f8e5aa15dc6f19870ed3a8ee1b1e042,0x11a1c6cab0f08f0715d998ec1b6858f6a9879d4580ee3af184290b1bdd639,0x1cab0f168705d438dd5aac6d1b61e76a1dd6f1942ce6a1cdc769d47b6843b]
def a2book120 : Array Nat := #[0x10883ba86756aaaac3d8fca91bc1f75a1ca11e3398efc65db37c6e1b5d542,0x11286f0683b0872a6ab37c1f755db39c6ed6a861b1ec3a5d424f187690842,0x12a88f36810023390b3c66aa1b63f991683a035c672639dd4571ec3e06c3b,0x10e37515c4cce5390b2aa1f4dab190f03a8f3584eb2575c6e1b16078b583b,0x1169398e0570e1870b20f0ee3bdd7c663cc96a8d6c6f37759c9e66395d93a,0x1aaa4c5d458b18da0be99b273771b1b0e5c913a8fe661b359d69d83b8e878,0x1b829961c15092a105b0fce71b0e9a1cde3b6a9c60fb7575a3a86dc98e642,0x13584fdd4430f53846c4a893390ed4286ed6b241acdd7536b1b1dad40903a]
def a2book128 : Array Nat := #[0x10cf2ace5240c3750b11b50aa186c38cdf1b0d6aa75978504760ea42b2424,0x1ca84a170aa00c6b727c6e64011dac9a84d60ef3975a42dd4c907542cdc24,0x116ac90c803053750feaaa1d011d83ec6c39c045f0b8a10903a687c61e042,0x1aab07c052aa1f030e00300b3909870f1b375d53b08878b277535823a8442,0x160dc94a9aa4658f43d07e65c6667c65da754ed03dd4d6325424e83528737,0x14df0f9803503dd6c6c06b25c950b0380dd40f9a1dd7379e0763243a0cc24,0x1d183edd58fc67070bcaac3cc9d821bca8764e1d608ca1b27035d737a85c9,0x1b1aaa0642aa868fdd40fa1d390b97501807f1ad60fb1b160388e61b1d83b]
def a2book136 : Array Nat := #[0x14ee878ec590485771b99a848f568874a907359d67250f8e61b1ef1b0ec78,0x16645a1ac7210d7671aa11ee75170356a93963c3b75a1b61fc65d7994e878,0x17818f7183b0b87b6a9760f824cdc782861b61da1f1b7575a390ea3b4e842,0x1b82a181c3b06a4ab269906c58b1aaaa3f998e624a1f371d975f1a7610a3a,0x14dc2f092235d43a63c7b5e3c6b82d6686aa0f858b1a8f4e6871e21b1083b,0x1d832a43e395d9c90b80a759aac3fc6dd43bc1e5fa3f391e1750ccd6cdf1b,0x17822a71a3a6640b9d4388ec3b4691b6a80d63c57dd43a9e239724420f9a1,0x10f7394e7753271ba3daa57c3be657663dd686dc68eb377253a8e4789da42]
def a2book144 : Array Nat := #[0x1168d6b1b19a3c4a3243b8e7031da7517f395daaab58dac3c7bc6ec91e175,0x14e03204c7046c200edc666457490241edaae67c60e9d6ce6766844272675,0x1b192a1883889175758d668539b585f10aaa86ed4a8524505425e11b1e2c9,0x14dc325d53904c430b1aa1623b0ec300e07b1d02f5e275c6e3986dc97583a,0x11504a4e85cc0401759c9f18384ec03b2739ca8d605b37dd4c90f4a110824,0x11292ae642a41c0f1eda1a1d011bea19d42400435b5bc60e5d6c6c7610878,0x1b190118c5aaa82316c3e00b2a0da1bc053b0ec59dd737ce5781bc42324a1,0x1c672ac3c0f86e4ad802ac1f1b00cd6b24c94e337c0c7608aa1b59750e9a1]
def a2book152 : Array Nat := #[0x1d18c6ca83ec6575c3caa3442a8e42401c872861bdd4769e3c60e83b08842,0x1780e06a8871c1d67192a1ed2463d07b5bc60e93828575dd5870e03ba8442,0x171aaa8aa0fa1daa0520761e758e5a172642c6fc68907b0ee781da1b75a41,0x1b1b2a4df0f09b46aa8e92ab194eb0749142a1c7b5e23946fc69e14109078,0x1ca92a03775c670f405d60f827c1e8f7193943c5a86e39c6e781603b1e05f,0x1aab2ae658f1edd68f5750fb60a3dc60e319c3daa1e2750eac98ea39109c9,0x11a84ac6413aaaa1c3f071754acdf6007c190931b1d85a724428e5a17583a,0x15d4694e73706a1b0ed99dd476285789d639491d6f19c99e02346dd409042]
def a2book160 : Array Nat := #[0x10cc220e3378df0f03fc6ce42cdd42f092a19d4aac6dd68e43a8ecc968476,0x1dd4e04e12a8923b367c62a85c0a43a1e2396a8241ec76326750d5d472442,0x17823a0b901724430045735a4212bc65e239286d6058037584c0cc3bdd442,0x1ca8878045e61c380a80763cc9dd799c045af1a7635b39684a10e8429d476,0x163e41dd4eb8e53921c760f9c66a82490aa1687c6891d65d8d686d871e042,0x10e62a5083581d414918fa85a1286c6f1aaa5e11ba1ed686e760ec2410878,0x1128aa9788ff181524c2a0687b9d5c9325aa63e3903f75c6c3ab245a1d842,0x1d805a75833f1a37ca868b59c62847ba871bce6768e51b9d43b0e9c91d9a1]
def a2book168 : Array Nat := #[0x1b584a03c030046fb24071983a8901ba1f7518ed408bc6a3c78091d61d842,0x12aa1b067750d5879d73771a765082212876f1a39b243a1e05a1982490842,0x112ac91bec6719aaa3ed69d46b80424a1da14de787593ba85015da3b10942,0x11d44a10487806376a8aac6f9963e761a4d96847b0ed39093c6b24781da42,0x1dd466b59463185190842]
def a2book (i : Nat) : Nat := (if i<88 then (if i<40 then (if i<16 then (if i<8 then a2book0 else a2book8) else (if i<24 then a2book16 else (if i<32 then a2book24 else a2book32))) else (if i<64 then (if i<48 then a2book40 else (if i<56 then a2book48 else a2book56)) else (if i<72 then a2book64 else (if i<80 then a2book72 else a2book80)))) else (if i<128 then (if i<104 then (if i<96 then a2book88 else a2book96) else (if i<112 then a2book104 else (if i<120 then a2book112 else a2book120))) else (if i<152 then (if i<136 then a2book128 else (if i<144 then a2book136 else a2book144)) else (if i<160 then a2book152 else (if i<168 then a2book160 else a2book168)))))[i % 8]?.getD 1
def a2ranksb0 : Array Nat := #[0xf0faee7b8bddf62d3b3cca314c12f0b8ad0afaaaa668a9e66292e3a89e13815f0775ca6d5a264d7f5b15a50d2b455023ccde338b72989721c701704a0dc2704000]
def a2ranks (i : Nat) : Nat := a2ranksb0[i % 16]?.getD 0
def a2tbitsb0 : Array Nat := #[0x4e4472bb33fef25eb6221cded8bb33ae40ffd75f39a7e791733cdfdaccf8d4bfc7e26b35b7ee5e120568fed1f75fbc28846eb4631ff2a27f2ff450ab376a7ec8be8b71602db2b5a0d6ef61c5f6a75ffff87d7b68b4b20ff7bba543d9d9baafa21e20cfa7fd5b0ee54cadf3eff44635dfafb1739c659fdc9bc1e3151c33b0fef0afdecb3cddaca47f197fdddef67fd5779afdf274e7ec9ce7be24a06f5af35b96ab363a43fdfe68f2fe1743c41fe18ac5633c4b3bc7bdf374fdc957e86cfadccd4bbd62de98d05cbfa373bfb2f361e49]
def a2tbits (i : Nat) : Nat := a2tbitsb0[i % 16]?.getD 0
def a2expanded (i : Nat) := packedAt a2tbits i 1==1
def a2rank (i : Nat) := packedAt a2ranks (i/32*10) 10 + pc2303 (packedAt a2tbits (i/32*32) (i % 32))
def a2gidb0 : Array Nat := #[0x9e7a36811b806e61583b4a4cac4c92744c4c7d124c4c4c3aa38c3357a767a6539f1b8c639139847e7097399244723c0949a761a9a7a112911050469b5097776394915f8f75987678508f48879f803f7ea954609961516216827248918f9141a1328ca4955c409d945ca66c5ba94e9da68f0f799e0e8d69291f4b110f9b8f365f3d4b57aa93a35fa84b389a5a517b2b718f5913733e048a486830226175126779774c7ca32a4c494c915c896e2a4f674a4c725635a0ab932d4e5a9c7c23aa2f159aa3225836799527836728420d5f2c29ab8953a83751147e1a21aa513d9c05157e27476a7ba2aa5baa0a6e87208f99a69790647e49713ea9309488028da86e66273841564dab77109b2c559843a7018277a96ca29c32647d52a3770f6b1432374c921c90111b761f094b8ea59095944c6845611a8eab8952864c4c525c75318a8e812998674c6b2ea525a48744a47d470b9599855b4c4f4ca11c8532226c87922e924c4c4c79a84c280a72934c7239ab4c754c3b79674c1e4c4c37954c70794c4caa4ba298968648a03a74983d8e846a9daa9a99801b4778079d6b4c1d568ca5704c4c12aa43699ba2218895979688404c9ba2ab675b7f7c0e4a093f16ac44547a794c84a4815b4c4c5e3a4c966223074c4c4c4c864c4c4c7f248b31a67a7e6e4ca3294c602ea89213a0067141434e866053958f70048e5a4c5e77775e76999f6c25a057a98201aba875968baa8929a468274a750320a15d4c66535c66126c237631a93e12547c75816e862d99aa28a42f6343420c89227c2c7782a68c928e234d4c6e38719e530a91688b8a32a36a644e54457c4b6d15a5338c919f38349a96a205275a1fa9a175371f415b80959f1f8b42075378316265569054116c6f149eaa646a2f2e814b736f885d6c7ca8749b7d480820678448a39b015d8778a641794aa74c28754f0e10666b678d7e6b199c89a894a36a2b4c8c7d7a399d982aa6769a794c67786e011352606582a64054764f774c9c17782870a49586561a1b9f6da69b1f8a961467209a88693f8b39323d8378ab2360580ca249848674938f3d874f0b618921314d65853524283852716d184a3c34a014a3593b733e3688985295667e7ea08a7643850a467a759f8c672f64a48f934c2f637183158f26a5468c6f06ab6a734008ac73055c746f07264390a772868c1768695083663e94a1928f4c825d761c9b1973a060a57c8718294f6562453374898f81708d643e54693b6d9e898f1e3297917b6967354d912655a1026556490d35787b6678703f82558d7f6a56752d4e03a09197828a2c792a89319a596ba38c217f1d38787d637c66312b80a13c76895da6989c4c198b606e1e8b36]
def a2gid (i : Nat) : Nat := a2gidb0[i % 16]?.getD 0
def a2pickb0 : Array Nat := #[0x4b6777b7208e270018e10013740425c1042024e229c200001d6b1da5081def9013278306af082be132023700057308936d00022104124b82250152038d14d0480045aa018407335edf294aff2d1d81211383024c7d0813420a02331155bf00b17d11165802896a5208410006e304b32a8477c1204816000021000007861564249f9869ff6bc5fe5f26033e8453c5d024b582260e0145760453c189e7f900148f020b6a000827110563024819e8c2925a96f262919e41125a000091119465d3495382a0920000532787e300440b00106b000c9700040600000d00027d000421140c5c00343700afaf00179300ac7bac516100002720803601c3f7489d6c24906788ae8b00349f00200f8c2850aadc7706216a00000720acc3229011000843000c3a0b62b63b1dd5455d7700854749a03e0001a60008310ae7564882710440e364ebb700807b0002ff000897022c5302afa4123de94811aa009ebb00454ec4a3b532522202a1e600804a452b7b028c7b825bc354f755022143106f2714b809002a558149c600c87600357000d39704b90501de8bb6dddf0012e700083e9363b60007370128cf000c2d8a89149c0eb61aeb2ed326d912e0bf00349c031a39a45583d87bb604e7d1080f73b369664904910da79d0108990259d9cc70f40403e300431554ad6348852500005340eeb800d03900033e04896d001257000409a4061c1488678a4d5b4112ca000034f2c06500a2f300857408834525289202087f956b8300147513101100000b0814654dc661429df500209b84254d44851ca1ffaa815b10fa8a178108290537360004dd04b9c87b7fb7400890160d1d40568ef8149ecef73f00001a1102f3ffe3bb000ab30425b5c946120eb7ec0759e760a1b70d110e82008d05236309a2150024b55523df50278700001b7291e18928c100001e00035f4490a20081e100046700020300000f28a21c000426308467f28bd5000eb41355ff0003f320126a609c394888210b6294026a8527b6d9c05b5d712b25031a3780a6735c94e49a8bab20b1b10040850002030003f3410dca4812d11094d6036c9b80cf558803c71e84f900009fc08e10002e3521a824f742a782abeb42078100941f432591017b230204f5602adf4226d702043b073d4f01735d00025a0f756b12121719212b0063c7a9add5019af30040211056ac00e03d00f5511214ea483fc50386467a85a23181a1e250a2013d6c449743007f414c179f01e3b5e7b7ff90a90400110d11680600040f025391926f3900000d9397a380d2a19143bf80c06c6d262a4a2a3a100c290024e56cb4e904cf44a6b35d007cbf0a31d45499215d124500095b0000550121b7a56b1d64380784160ac5a61e00223100041562226d00460b004b5800032300005c660dfb010ccd908af4004c5e003d71843a8209b477,0x1d7700086bb09bed00f73c081d9d00003b0034928006b9220b1420623c00005cab8928022b5961846bc2b73ba03a4480021400023eae24cc04235400005c00005c115f8328aab300008300e935132a82000f9c04e38200bb1f04491a0078a300005c118c3de52f23005412ad4d5a00018ac48027423ab9880846000855105e8d496bab0002ac011423244c618463ae00010f0c448500005c0000d30cbeeb1030cb6bb8990137ef1560ab38064a80207d08d7db164a8800005c00005c00005c00000d44824100005c64efa48bcef7720c2cb4208a00005c08473609bc1b20003400005c00008300005c238ecb03d30a02c27700005c08ef3b00005c00005c00fb9700126c00005c88721cb10a4c00005c00005c001502106d8f0032064186840009e3088c3800009604019531aaf400106b1114910076b54580990b01d1000c1d190912a1400231230801142b11136302a2bbccb15201b1d400004740462521a43900005c594ee6a4d94300465a1201c10017c300005c00005c0535ef0008910413b7003b6b0004961010c3004aab0408f301c4890928628992100008e507a17700005c0302170000d30020090008f513471e092399a1728496cdd5120dcfbdb7bbb0f90bc74edd00004511369d37a28302a1e30cb03900005c2a01b104230649482a4807e500005c00005c065c5c0571eb00005c20486300a2e3946cbb00008700005c00005c00005c00005c841c1a00005c00005c00005c112599e515d500012a670e5d88a0302d39080011770000b100005c00032716a9f100005c0d412a125edb00082700047dc12dfd0012430dab6b08250f069af90456b72423e76248940f43a404bb99480543000d2d042e53fe9eef0a4a2a915c9900000f98a33200021f824ba26116994a4c83082859000f4500000f52b3b5020195089769900085945085ebdffb0c1001210405001d0e000184000ecd020091000a1e145ff10064250012d7095cf7020dcf0895741b5d5b0008ff4281a1954c8600005c01f41db14caa4145ea0003750001a700242fb8549700046b0281b5401450fc9a220001c700004b000c6b005f43000014404c5e103a150013ca82621151800202b0914000ce107be3228e331a485a221dddafbbaf0e03627a88db408e4b20fe3b638aa000000f0101aa0020f50d43091004db0c9b7bbcd12297682a002025017cb7029a3922500b00003b7f2bf70007310055c732d8100001d914dc5e0093420005e60008180257e600426ba1495b1960b4203d8f122ec210deef2402c405367d8ac02500811d002ca90ae1f54c96d9040595522448000153003de70b45f700005670f74d04c1021928097120cc005bd7318bed69236b218f65008163942282000d6600afcf0016cdcda253ff5fd34aec46f40a480c72b72d4d2440ada90000531061250000,0x1100fc042f1a0f0de22076322e2bb8a4499099325954863310b5b03b559610dad00005c0000a500005c001447082d9500005c00005caa8344043def00005c00005c00005cca05eb44a0840013da6056fdd528a644840a080c7d04060b0010255140839955bb00191a806c9b804a632493bdd4c404000177006a1c0080dc240efd00206dacc54a0191e3325ce3426f7ba7316818204a0a247a088026011324001005056def0002733a33e9856536092ead44504a08c3270293811d224502c533000e670c240f8150db100da9000d4eaa2420c12f10019958106faa560560e81a9601054aa610900000166d2b91018d6c01288800001405512a2201530a13e6112d9b53143a3ef9ab41492a0003e717656103007b00000b01027300000f2041170023eb1805950044250000331610e7078ba700472508027c0001250110c1ca115600342e000b2101eb6324304900020b01082d01174700000d1821a1000003005ac37408b315a91b0f8bd60000420001c9dcbdbb00001700000b111e7700b4db391dca0146cd22d27300021942126303a2040121db1010d0449e8de01af54a11286aa06eea06a6a890e200001950650e0a24ca9098dd3ed72fa2d40c03275f0175b70020690000870412f7a74b59855f87000e6b000083fbb2f20040f540bca401328b00005c04894b2013424ccb3e00005c00677700005c7009898124fa0004150010a558ad2e03cec911a2230a0dcb0011c00003e703028b07cb9300607a020009014974b3e8b1d9312c044f79404263001a4b6b13570820240241384e5f3f0084978048190008cf4ca4ae025a560040190005431f5e1c0000190048f3af0fc21059fd577b6f7e0a24446ebb283b5f1105007100e1002b9108404a005bd714789b001bdd2030730477790aa7f5000c500599d93a1dca30848c000c770004e1da2284e38537230ced0000c6050cd949442200120900d5650002190018db804cde0240a5d6b5a500000b54808c0000c5a400cc2006ad0d061f0000774ac3872108b800000720064458b5b6820473b15208f6ebff042847000027223325d80ba4033cf706f81f94da9c0442560004cf00405200129e12bafba0270209ea77847a5500489601a4af00032705f63b000027000455020889000043a4880c03102300454e01545f01659a001b930008990024553a5f7700283b935f5f0023eaff042c00005c608c0709dceb42886a9cadfa00]
def a2pick (i : Nat) : Nat := a2pickb0[i % 16]?.getD 0
def a2hints : Hints := fun i => let g := packedAt a2gid ((a2rank i)*8) 8; selectedRules 10 24 (a2book g) (packedAt a2pick ((a2rank i)*24) 24)
def a2codesb0 : Array Nat := #[0xeaae99e88e77e55e44e33e22e11da1da0d9ad95d94d93d92d8ad89d7ad79d6ad65d64d63d5ad4aca9c9a9a39a29a19a099a99599499399299198798598498398298197597497397297196a96596496396195495395295194394293293192189a89589387a5a959559359258a58958758558458358258158057a57957557457357257157055a55455355255155054a54254153a53253153052a52051a4a94a44a14a04954932aa2992552332221a91a71a51a41a31a21a11a019a19519419319218a18918718518418318218117a17917517417317217115a15415315215114a14314214113a13213112a1210a90a50a30a209a09509309205a05305203a03202a]
def a2codes (i : Nat) : Nat := a2codesb0[i % 16]?.getD 0
def a2parentsb0 : Array Nat := #[0x8d1624380fdf3d78edd3970ddb3568cd93160bd72d58ad529509d325488d121407cf1d386cd182e58a13244480f1c3460b14203860608080]
def a2parents (i : Nat) : Nat := a2parentsb0[i % 16]?.getD 0
def a2rowsb0 : Array Nat := #[0x551c28c5f198012432e09fcaabea786286a3e8a66a07a8e49e589b4b319c9467996a080b1a342b5275d64d5ac69bca9d61bea658e784cc21dea9398b89f909eb89369d6159564e2e9aa4c27ee9bc330e9e8599060c185c7b71939af81af0a7da98a8df77b5219a7318d7a8b925626f046ca8f08978760e715948a3ba5a8fb01cec0dba6e096d263095a28a03221832939a6f299a5e5a9e2387ea8a1cc0a776aa0c7a57467dd673064c39fc2a90cfaa7329a98a2787c6ec2850c85a9f05e586e67d2a8b9e281f969cba4ca9c4a82eab51d38b7e01229d70548bca3cc0a371ef8a06a5da9ef88147d5392dddcaa589fc1dc4a0f605a90aa48865a0c3057ba72aabda81279b2e3ca5320c21b91ef08448d549daaa8aa733546a14629cbb73a9478f2c2a1be623e2a8844a20b1f621cc5ac481677a21cfa72c6d21e4683c243ea75013077220f0c6038ad6456254b0f5ae0c3fa992a1aa64661552458bd59e4e30a89ca2940f21d22dd880d63958d4a8fa92d07fa3ce591458a325cb0e00bc68b22d482129e0b4f1a3885563f1d4f2e2a98f0aac75225144652c48aea3f5c10e296ea4662a495689a5d81a97e72da93e97025168c6a496a52395e2280da966450ec7a5526aa5f1e14e5127cea419f328e8a6bc2b377c18be305aa24627e276aaa29df78d497b3ae4e9a3a18eeca7e158b11c6a2b19ac9d6a618a6d27d0e943ce18c78bba6fea88e9e421e07ab443c9d222946241c606302c307fe15d445fa8e5684638290f899042a28b4e480ad8ebe95509f330629ad2dad3867ca69018b30a382e69892a490bb02b48a9b50addb82850b953a6d88aa2dce7e9ead36819fe40c24a89ee04e016b873cc9b7830e9f1d54679a72828d259d8a81ab1e291ed4e918990678a5f0679a8f0aed78a2a56015c83f59f4024a288f1585e5495236ea1f88d6a1f5c60a945b7e3ee6318ba877d298ca5b89690b90a7e1959e16a3ce95777faaac6294af504da9b6a851e9f28300da20b89fc716067fa6ac82fa734eb03a2a267a6fa1c54988ebc1c8a2662e78a7b20a56b4a7956a0395e24ea8e88513aad698639d8eb62ce9b3a81621d0b95ae231a82e20e56a925a50e6a605c0a214e08795f52154a9bc375a4cc6b38968ff82fa493c3888478a449ccd27880d61829e1da9e480e88f0a16111a1fc27cde28155cb6d9b6225687ccd0ea5e1678aa7dd952292a7325a0cc589cdf640ef0e4d202ce2867285cb1244ec61a74c5a885411f5a7c524aa1464791ec77a5fd45550ea58cb762c99daa32ab8a8885d42a498be39bcc462d28658625094563702d5a21c57886858a662beaa804c09f0a661e1553f484ba8b58a42455e25aadc107072c0cf31556b5a58a89aa77c44f78ba2679fbc30559c28853a28d6aa8a49c5524e9a91fd69db89bd66d891455a1a6295e63949e486,0x91865f22ee033374aa64389ce9255a4670a2a223ca36184527e298688689732d2e9a505bcd583316994a65ea7888ec053a54974625883283ae08ad044631a0ac288f74954418db0eb8a978ecda81411614f88a276f4a58159480a1e5408f2abc8181a149067838170a2e0830a2b69473b95e16a9bcd91295d8a83c6d9733c2c3e2833c78aa751e36632ce5224c28b8266ca3918e58cc26f9c9fa794bb7a52875727caa1d3029d47a92c9db20ade1268389fe964c7eca9347ff20e62732a54807492e954a2280e417ac7b085dc7e206969874c498ca10fe24c147e7fe1149ddb3b5867c0ea02e778c28b0a2f0630a228e5963be430a23ea2524e9e3078c28a6a656a325fc288ba9c288f1fb29b519c289d841ce79787c69589c28b0a2568df96a4eb0a21c95f5936ab0a2c289517ec547883d59b8fc637361464a88948b95181aa3e38ee647969691da7549732688212317d315494c6ba293006b018d8fc1ee025a27f5af524b989d9032a27a91ddc6767d285a8c292ba35876f827dbb0a2e1e0f96bd9dfa9f9de35ab22460754f30a23c970a2908b039b4a73885487c255c22d7656a4e77a0d5f6b058912ea022b86f9da59f95da4235a1a420e06d625c289209bddc58fba9391dd69b808198eb11a6a855432997199d6788af96baa86293f783e1eb04e23d71a9c82425f0b11a90632b539d7e839e16951ec288f096222d2e8c9ef305dae210bce8e28e63c5aac28b0a29a24a38f16ee3a50630a246691a6561eba7c28b0a2c28b0a2306a7a87c170a2eaa70a2c28b13a8eaa4a36e4e75274d187bcaa4f6222a8a0c48ccb1e8a1f715ccef0a2906e21572a28a5e98c639c28b01dec50a5958794244dab925b5df018f87e204be9a9a558a0776518eb28914918b5c7fe63e61d4332ca3059489bb38ec456a5a4122077ce17a5800771af875b9c29da629ea9ab461189d0abc22928d47f96f6d59546f89479f38e854ce053e6be0609a7654ab244a3f127de9a42a3821729be96c212a14f2f5292c59e21e13be56702150a45a4329ee522883e1861db0a27e2872dea2554f5dd8b25609ce8980770172c50d1af08d5626878ba3f58a19550d765aa29300e68f57212ca97097cf3518c00715aac6221c58694194a240907e96b03c89d8a8ad2785d50b05283c8b83c14978527c9f02ec07a92018b382bb590faa4421f2490c57a64c79688f89c59fe0e8da6a49bca299e0b01e4a3e33fce9886f21bc63689b420a45755cb09fe541e916207c7f327f007e7829fe5288a9a485556cb15458fc328a91f2ae68e45a9485aa81448a0ec58d20b058ca873082d881d892a53ddcc1e74f30768a95aa56d798773de72a604a79193dad431624221a80e8a015692ba47e9a0193ca152ee61b0a348ed5a7fa8df26f4a18aae1df6283e3f831687fea754a5d36de92f1fec6,0x3b04ccc5604508e978ad15486e96be0b90ad27650aef7854c4d0c28da5a8d4a3e795ce87631c9aaa7f29fa9f9165b27c28b390c28a01815dcb3a5491811c28b0a234a381f51d7019c28b0a2c28a45b12398a93047faaf042aa9d4e2e87521e003aea39626052282189d287fa22b52888201e929852688d8ba700c965906a330da0c382a929fe346c229a619dfa62e12e41194969393882478546e9a74a29f62146cd419293924882b876587f011e44621d5c959283cc2d1ac0e332e7e1fba49e9e727f40b162cd8d40bad8e570a1e1826d4522332c6051eac94729ee8e2345e9152854a9739f82bc2a3e7e52994ea30b3a9df86fa7e476baa28aac29e842e6930035226c295039715b698a83a469f3a48d0576b081559887a0a64a185188a9cb86887d824b42125891d6f3cb0bb3321cb0b78f1d9624580d1a1c1d6627e0919451e317a7ee41b294a7e463b8e583079850a7ea5ae762c906a63899b3ad6a630ad498f2d3824ea655d8aa3282ff0c4a9bd094887ea5b466277829e48988d5728ec7c68958ebe1af4ef82c2031949349b82988cb99d166f83bb61e160dda547c914f2287e4c520798b023628cda59e277a79588a1830e151190a2b5b7d8fe262d398972aa522cace15103c99410c0119437c975a33d7a8763cf062688e5835907b0a2859921f8aa8a114a9f0a2aceb9033aa70a248c080b504577889fc13b59db8a77437ca83011b59ae9b020f967c531e1cb04ba9ad25be275034ce9fa36e9fb18162b3aa867947eb4ed72e3cd1417f18aa0a1855834718ce1aace71a7961c5a75449215c8ea403465ad4b6c87e3cc040587c224b4a884dfa4863ed3ad4e4fa628cd2aa1618a041453e24f214f63fe9d23c8083627f9727969c854a3a0dada41aa4b19e2261a95c1cf21b6a2d5d55b351aa07ba2ebccbe861695d597c0e729489e3a8569be32fa254aa74c915249e1d3339e0b6355d78192c80e3b15694765cefaa79aa351e486a46daaa8f76a0d1f20828df30347b720c54995a48a68076095ea80aa26632c74f88387f99435dc5479075f16955e3284867c5a7c615057c2af34f69f362e89da087de7b39f29302458e1662b866011a6a3c5989d620b5c98f3b7d4a88165311783d66201e967e2a7ccad4f963f97628e9207146a43ac5e052aa242d15b63fb1af1e0578f878530464675af8513a71e94196e05b18]
def a2rows (i : Nat) : Nat := a2rowsb0[i % 16]?.getD 0
def a2layer : Layer := (1661,fun i => let v := packedAt a2rows (i*14) 14; let p := a1layer.2 (packedAt a2parents (v/256*7) 7); let v := packedAt a2codes (v % 256*12) 12; let op := v % 1024; let a := op % 16; let b := op/16 % 16; let mask := if v.testBit 10 then p.2 ^^^ (1 <<< a) else p.2; let mask := if v.testBit 11 && a != b then mask ^^^ (1 <<< b) else mask; (p.1+(op <<< 20),mask+(1 <<< 11)))
def a3shiftb0 : Array Nat := #[0x2202400000400800700900903100b00006600101000200300001600000200400300000000e00000100000107d02103c00c00000100104000b00200003400f00100600001101401400401400004000002f00200302300400600800700d00100000000600400001200100200000200f00002f02d00300c01000000600400900803600600100100f03500400001b00006300000900000900101c00600a00100401500004c00d00000300e01700b00305b01101a00402100000000f00000900a09300002100100000400000700203d00000301d00a00200900001103a00400002300401800300000000e00602f00100d00000000400d00100303b00000801500800a00c00201a00001900000701f01700c00600500002200001500e01300a00604600404d00300d00204b00000004200800100101600200700600100500100101a00200102800c00500000100000801401301300800203400200200001e02001900501e00600600900400506300200a00000000300502201200400300000a00a00400001501a00300100500100e02b00e04301d00000400000e00001c01200700000100400200100000500000000d00201000600000500301400400100200003a00205200a00f02b00500202901300300900300e00500b02900800202300000200201800002000100404f00b00d00d00500100000201c00d03301800800400000100001700502004100200100e00100101900102c00000100000401f00600e00101900c02e00000600000000f00a00600505002800300200c00b01900201800300901a00e00000000100000c01501300000e00001a00600c00200000000105200100100400300900001202800000400700000100000003d00000000800100005f09100600100a00b00100301a02a00001400300300600500000000000200501201a01c00000000801300a00100300401600900f00102f05101100400102900602500100100500600000000200901a00200000000e00301a00e07400200401600601a02700000000002701500400607300500201500600800001400301e00300100800703f01000200001102e01e00000e00901500300300201700301900201a00600400a01504800f01b00000200f00200300205e00600000300000000100200000f02e00000001f00101b00200500500f02e00800303606a00100300000a00000900100000701400400000000000b00000500301d00e00a00403b00800000701100000c00701a00001600c00300600600000400702000102200001a00600400200300000000000700000601600100e01300000000000c00300300800100d00300500000603200404501e00200406a00000000500400001200200102801900800c00000000500f01000a00000100802e00000300000f01500002a00400300800a004,0xa07300003a00201400c09500000b00000400400000917401f00000100a01000000001100100500001400000600200100000901416004f00503400000200201f00000100600000b00c01801500000600d00500504301200200000100500500f02302200000000000800300500000301900d1120020020b502a00104100406e01601c12e00100201400001f00002000900900600403901200300e00100002700001800000401300000001f00a01e00000000200401300a00c04500f00801901205100400201a00000000000002600c00103900000201204400200300400b00002e00300000e00300000b03900c03b00200100000009205901206c00600402600400601700014400000501800500a00000603200600c0020200830120180a702500003200101a00200702004a00a00000200003000801100500102600000000302400004500100200f04b00400c00000c00101802e00600c00d00200400100200000000000000000500b03101200d01700001200000101600302000006401100000200a00206d00806d00200f00100300100200202d00003300000000402000600102604a00000600300200200304300001701000402000400800100200100401100201600c00300000000f00b00501400103700502c01401400100501200001500100200300400600500300400301000100200b00200009505200901b00100501a00a00d00200000100000507100f02a00002f0030230070020030bb02902d00800b00100000400000200400005a0010a000804203b00403000200f00000601c02d00200b00302f05a03300b00e01700100000000202000100700200003500900001a00b00000c03f00a00200400102703a05900300f03300200000200001d00501400000900201400c00100c00501802e03203e01900200900000500601d02900a01f00100700303200000100100001100200000000300b00b00507804102300300500200201b00000001303f00401101200600000001b01602900900800000101301200e00002400000f00100701700000b00000c02900404600e00101500400b00100700601a08201c00900000b00400a00400300a00b00000400000200700100000801000401304500d00701903100600200000003100001800102100000e00100000100800101300000500200301800004100000000a00000601a01600a00c01f02100500d00603d02b00600301e06700000801200000d00702701400200305900a00906700300100008e00401900f00a02200000000c00700300100a00104d00000704f00901700100100000300503b00400600300300700302003a0ec01a00800701f00300501501d00001600200000300500200000201500b00500106600a00000f04000100f00100600403000104708100200700900200f0020200100,0xe00b06d00902301107900100c00400501310c00601200b06d02501100100100001205800100c0540020520050000030841a209a00000c00101a00400402600000202800300401403c00001302000000400805c00100000600500000f0010120120630000010190110200000070380480060000300630070030000010180020070031260110000040020020003af00c0bf00501b00000b03302e04900100308f00502c00a01c1ae00000001100005700201501100e01200401602701602a02101000700706202e00000a1c200026022300400100000000204012700000000105301600800001610500a00509f00201302100b00000b02300c0100a401f00d00200004303400d00c00201100606300402000102a0010a40080080020010050003b302700000701301b00000400201002400200500400006801800101001d00001201e1b400001f00400800504501102200a00f13800018600a01c00100e01702b02202004903d06a0ed00800f00f00d0ef01d04c14f01600100000000800000000603c01d07e00a00600500100301a00000007f00900100000003700002400904600d01c0000750080070090000040bf00000200300100900a00405e06b01b00002104b00e00100e01102101003000100800302900b04403800d02800002201203000100500200a00f01203b00e0000130000020040a500700900204d0000000200b710500000100301700000003200900700300000001600004000000402900100000000e00d03e00100004e00905e01500c01800008b01100001900403903700600100c03f02900002807400501204802a00002b01b00103a01000002100000300100202e0550040620030000000010560000080000000000141be01100000000505902a02902c01000000f00000200001201c00a04a00600902100200701400003900604500200900d00100101603b00500f00100600900f00000300009200301b00a00501d01600200000701901d00300300001400200500000900300c00a04204200006300000001900000200000a0b301004200001903500a00100904003804c00103b02a00f00e00700000000000000a00100300400901203f01602d00100701809300400b00600302900c03900101701000000002c00006200000103101308902f00900000000f00000e0040ed05600000003d00800100000302200000000c00800002500600415f00000100d00300800000704900d05700400000500c00201b08702401005c02e01300100901f00201d00800501400002000400502004300a03502c01501000b04300300a00601003e00100b05a00400500201400400100600000700300000600700600a00000200600000000900200100b00001c00301900500200500001800400300601000702c00c01304a04100700702d00500,0x705a02f01100023600300e03001d0010a200004a03400b00b0031b200010700d07101900600780a00102200904d00305501300301510c00000149d05a80900100303f0a60c002f01c04600805903901a03f04c03302500001000600001901000102c03600000503d00b00000102a00004100000000202800000903201b0000300000710780070270000001b800502e0006aa06100100b00c00001400200001500673212100100900207501e0b801602701c02502100302f0312ff46900a00800108800202404b1cd00f07a0c001200e02002800500100702200600800002001000916a00a01202800404d01407102801101700300401c00d03a0000000c500501b00008001f03300201b01b00500501100007000d09300c0040150000000000280033b100000601c0130b500001801101d06501c00200302601201301d00b01c00403900500b04d0450040120200dd00f0a001000c00602106701708428d01501f01800c0030040030070200240570e909c00900000000f02300500400102500001400000601a00f01b55000000700e0030001840130a303c01902b00e00207802d00000800c0b915700102310100301200e02e00400000006605a00001100000005f00f00007f0890570080050ba00a01024500c00002100301200200200000003000504f02400900102b1b500100000000005802503800701c00b00103600600f2c506200f00f0020460000c900e00208d00c0e800105104b00000207e06b00000d0040c300700800000201503000e05200409000c00107500c00700000e00100902300505f03409500e02700a05a00001102500000201d00901700903500906800100502202e02902501300004a0fd04a02f02400000902300300200600116101507b00204f00802c06a00700f08a0520000050370a307b0270030160000030900000d400102700400c04801f00900000200702200200800701600000000500008300102701400105f00100307701001600502301b00100102c01400400800500700703f00400b02b01900400102a02f02600100400a0020040e000003402c03f03200200900600d1bc02d00701102000000800000100001000002101a0020d400200002d09702f04000300304600000202501200001c00e00300a00001600100002000500600001e00000006700b06a00600e03100300600103508a13502100d00203500200a07600000201400003101101600e00601f02600104000101807300500f09401905901000a00402301f00003400000001300302e00000400000101702b0000210ad01008400601201709805005500001f02f00200300000700f0f700101700200300400200900001d00000f00700400d00c00102c01600006c01f00100000300201301f02e02900f0061ea00103900000b08200701a00d015,0x200013725a03b11a00a7a700801300300a0420020090800000cc05e0330001ef00100009516201c0000110a60db0090001e80781a019000000001a00200400e01f07600002302705c02300602421d0420170fb00000f00200001809003a01502000305b0e50011571f607914e00101001507600100300500405d00803600e05000000e00124e00200203900f02300e01400000005b00816912a02b08601e06401200000001c0370040000000cf03a00000701504901300501706e01815804413a1e904006400100801600104102c00100800800001700400700200607e00900700c09c02000000102200b00000400a00000304300f00e06e00004000e01b00101900103003d0780000560530393f100a00607500701100220103900501301803f0c902700501000a0000010000010f013700400000004801126a00b02400904f0540040b50090008aa0040c800c00b01000900d0840010b90291080b800901509100a02302106c00101111d3440df1370070060000f00000120cb00900005100002d00d00000201100300103339005801f00900804d02408401800005400500002700500401d03100000003d02c00001900600000200800c0990b002200100c01b01e00600700000a13d00d0050000000f018d01a00000005f00300b09600200008c05100902701e00802f03203200500301702301c00000e02d0400031450140060050060190250080c200008c00c00600701401801a0100e706b09502804100300000005c00900203509007d05100d0a412a00f25501d03801e00100601a05100000500900700406c03a01a00200700000e08400d07a02200400400205302301707b02401a56f02c02f01e0ea00700702600001c08701108600800403b00002c04700501411100004c07901600002800c00000702c0d31f501001501e00311a00000e02c03000300f01400200602607103e00c00000002f05e0cd00600b00605b71800002205d01f00001600005a0ad00f00a0480010050000b80160e705708703602d00c00401a00f05e0120120450030020000051f502b00000006a00000000500602d06a00004301c01701600100005501700531a00000400200e01c0a889f00b00900b00000208900001400504c00900006900900803400100d02109402d0380140010211b000352407300000a0140db0110260010030d302906100c03d00d00002f00d0d300600102801501700b00700300709d08200204b0000eb00601001e0020001180123e803a01117119101a11100400b0000bb00501605a01702302f00017f00900200303000500000000500500607806e01400800100200e1100020000a200900500100000300600100714a00002102302681a00801b00300606900000700000000301a03207900000f0010ce00e0000120390060010040160,0x200000706501700000338605806f00e0040600dd00d00011c0160e50020000050cb1b908b0000d709700407e0010090000bb01b12000201701700a02a11100002200000e00a01202309909f01503e00005100a17a05a00101006200657201305400500000e0140840d200902601200c2540894db17702303b00f0120180980430b10e403205271b05834500006002500005201b00000066c0000c200224500302a0020d90010611281dc0d11ed00003ec8809800114201f02a01900d00205200004507001101500500406402b00200002506b01802505e0001880230aa00d14d00003d00001007201903804c02406f03700d02000f00201f00215900000500003208a02707c20d02320e00000612e00200500d0ea02106504d48201000400e02902456407800102906a00201a01500600004d00100300a03202100000003e08000c08000000100000004200001700f2341f601400700202b02004401334020e09b05809103100200800508a06907601b0fd02803102002700001b05406200700f11000006f7413370420180430050470ed01e0320010001e802202704f06902e0ac0120db03700001901c03319b05b0000080010a300b0210100230eb00316d00c00013d00800012901507b00000a05502500100000f08c00909001908801500102902d00800c07015c05301105a10001505e00807a0c801001020e01410e00000900300004a03401033f03500400002100803600900400d00003032908601000658500300400508400004e01702704500500400a00a00400100300300900000109700810a03500300100300201100302e0270132d80f10054d500304400704b05c14200003d01f0240870012ad0290880da13a00a03f00000c07200500003900200a00e12a00504c01102400005502500a0300d50000020280100490003d90150012e201400c01500600200b00b00d00]
def a3shift (i : Nat) : Nat := a3shiftb0[i % 16]?.getD 0
def a3idx : Index := fun x => let v := x*(x+701)%618970019642690137449562111; let h := v ^^^ (v >>> 37); let j := (h/3873+packedAt a3shift ((h % 3873)*12) 12)%11943; some j
def a3book0 : Array Nat := #[0x1,0x13c071a2d1aa33260c6507005602315124021918016604b40cb0c83ec0708964f37,0x1b8d66643d01495c0dbaa1a20210d1e82b846ca80a02f058de0084c94749da50a3b,0x1532a3f00aaae035e2231d608e0f4160731954a8bb2d6ac143c14806a3340f9bac9,0x131ee1c2183f07a61f64846e6e03c1504a0d5b580a83b0341543df1b0ec0e814e75,0x135417015007f8c1289c03a03400c1c02b01e1f41487be375d43a6755ac0d564c42,0x10c063c328030a41180b84ae6e0691c0380f85e01571b07c0e81486a0f6b24d0e75,0x1270ea81c2870cac079cd7508c051c782acea0b3e307b0dfe64252a10a54e421476]
def a3book8 : Array Nat := #[0x168cce431307602d801f83beeace8c7b38754de181b75655c070df3707b3241f4a1,0x17c0ce46cb3887ac07ba85961eca89570168cd818cb780dcc0c1f12249532650f37,0x16c01281c0300ea0fa8785be7346664d2aac0b581b422e0341de35030f61be50f37,0x103f08da303d65410e5530f4860be1277560ed80eb1c994243c1dcc9e6ec0c1f61b,0x1095d1b8df2a05423e1e80fe0ff1812703c7602b6486aeea16029f3707c1e00e811,0x178d6a9c7b9901e0f81c375e6e1281d17804c093e301a053c6c3d878aeab240b02e,0x1d540e077ec90864e2eb539e360ec0d036d420f79b84af8c7801f0260f61e037816,0x16ea1aec3f75e721803b2750109d81482af8d6842304ae6f0ee5087b0481f00e83b]
def a3book16 : Array Nat := #[0x17c17181c703d0160033f012f04ec9222268cc65b032a2b492950b0160696b9b9a1,0x1792f19d502e6c000d9c02feea0ed8383e87ac0f80b2a0b9ce68d86de6e1e264ca1,0x168c0ce552a1806de121c0788dcde1530f6c052a64b1b60656a1d02403586e3b639,0x134310c951c987a43ceb44a6374aa87d4678d5d683d602b508a8df379430ee81e1b,0x1cc18a98db0fc06caa83dc6a55d8287e07343c3de3746e55c1e50d1be07cdf0db75,0x1ec011b8cf0f081c0c36057160dd43806519201e6b4c9e6ec6c1500f1ac0fc3b042,0x178d5d52342a45506507903c7303d03d1b80e4a8a310f6ea41e1c2382704ea9ce1b,0x1e6e23d2521a07a8ef64a3d08c0ab8d87b09414c0783e0fa0591d7c60489d83c042]
def a3book24 : Array Nat := #[0x1b8dc3cc7f75b555d72f1c60ec12b9c8240d5cdd0e81a0742c38d8780f60b81485a,0x103e09075f3905c4907182f06a6a81d82c3ac0371d737041dd43f1c93429d81f639,0x187b4e41f5d6e1e0ef9cf01655c1c3dcaa0e1d81ba87806bc0ceb737c3728664824,0x14020ef8096319a013ba82dc020b81018fe54cabb0078343c0ce4f3707b86e64ca1,0x1ec1f1b9cf1beea17ba301200700b8087405c1f437e07e6e1681f07806c0be0d83b,0x1b8cd199514a60ec0fe361baeab5a50aa120fcdc95160234dd4879199ad32564903,0x14c083c87a2ae6ed812324a65586d01b4640ed78d0b19606c3d83a223ad46dbaa3a,0x18672aa123606f052b9b92a632c1d8db0f27586da302f494caa8d922992c0e50b75]
def a3book32 : Array Nat := #[0x1ac0aaa150ca8071d8953c607f41e8cd2aa073240350f5930ef0df378450eaba978,0x1c8d5189531bc0e48b1560fcc1581bac4aa5586e87d193ac68681e0359346e64f37,0x17c0752c3e034a836819746e540d816e07e0f7181dc38a55c6687e0fe0649011b75,0x12b210c1ff077c056b07f46e540ecc7d0fe327259bf0f4b5d81649d6a37c0f0df37,0x1c54013ba94f2152a99530f31e568a53e0e07cdfb0337e5490c1ee393928ecd0e1b,0x16c15d65088700dcdde341b6eb0ab1cc761948ab0da4680e83d0c82c84481e1d238,0x1cc141fb0646b8ccaa1130fc0783e87f0fe8cf1b9562ac0f86783f196ea9db1ca78,0x10940c0068624740280467507cb2407e2a0f814c05ed6eea0f71c820c76108e49a1]
def a3book40 : Array Nat := #[0x1cc0b5830646755864098590b1f1b0786c0a60ad1500fdad9d42644a0958e437842,0x1ceb9802543bc8d0e80d03bc55e65e4e198950e41afc6444076d087b07d8e417078,0x13c0f24343c6e3210c374339540cdeb073837006508349930e8bc078a375063b424,0x1060ea83286035412892375f8c1b264e76c718ec1dca105fce41007b3939d71c9a1,0x10d78ec156750e28ec1f7750a60b0127c63540d76482b0947241e83bc7219821069,0x10e81ef4007d701f18172c906ac0da35e061fc0c1f15aa6f43c1dd016ea1e21de1b,0x107b20c2c23a049a3c1df01bac13006c030eddd4018027420fbe34d6e6e0583c042,0x120e43eba80fe6edd52502a2c04a950a0328c528819c92ed9d650e1b2b44e93c242]
def a3book48 : Array Nat := #[0x168c91a15360454c6601ac995486587a22407cdcad4c9a36c0e0ca5a4751da1d375,0x15550aa03c03a3232a235759ad4aaa350f5ac0be83d03c371da50b758450ee1d178,0x1e8d91b154631c783f83f2ac06f822d25ae33cdf87b2a9adc0d3c4a1992dd68d942,0x18674dc181aa8872ab83de0e33c3fb072ae6e7241202384875b0df03992dd71cca1,0x1cc058003ed6c3383f6360731e19f1caa121e5189513b20e4ea9c842cea75b0d976,0x185503db03c65ad2850cc0748d06507a07c72d1a8db2a60e9e23b30f4ed86ca1178,0x190f580258da0890a9e31a180f51a8782f8374668db1ba551821dc22a0e5e221478,0x1ec171806f75d8d8a99568fc1e02e05058e6f81f4384dc361e26483e07b28421278]
def a3book56 : Array Nat := #[0x1094ea88d04605757b6482a2ed9d42986002c1e035ad69924e83806c2b403c26042,0x1cc1ca895446c550ab0cf0fc1e464c7c0f8746a887caac733258de1b2747263b176,0x1ec0182253d6095d1b0c87bf8dc660b016e1f9183c06c2b586f07c5a4f09db1c842,0x1cc0183e3799b9391b9b82ab8c06b0c8170c86aa110a1cea96a6491b4f010b1c835,0x1f8c928a371b0f050c9992a0b446a5081aabc9d98d84a0cc96a8da3a3424ecbb13a,0x16ea174b051b543687e314607c1d89531b0745289d83b0f17249c824c36488bb13a,0x11c60cf153aaeebce71c337355cdc160244958e417cc907c0f650e753928ec3f1a1,0x1ec016819fc66724ce551246f19d4d537505e170eb4c93920fb1c87b04810817078]
def a3book64 : Array Nat := #[0x1bac4e66b03e94243cd512af334a825537c373243c1010f79d4d09d606a4e8a1176,0x1b3300e0090108c0d80794a4953581241d02c12a50a034d61bc9da1d4028ed21737,0x189521e81e014940ec9161b80351b1b82aa030e887c030054dc6d4222745da3b442,0x17c0b258dc59c367589512220fc0e81b7502703f01f379ac4ea3b4c93432861d176,0x16c0181e30070ceb589db2a9acc3d64b4648410895319244c1c879072c05193c142,0x1e55467bad0f81405283cd601f03e154606eb11a50c193ad32603c760858e621478,0x16ea52a235398544690790f0cb86e8dc0f2ec1daba859c7203cad0422749d92d442,0x18c01281742a249287baa4c07703e879c967363f6b537f8d86e2107802c5d89d042]
def a3book72 : Array Nat := #[0x1295518a34160f65812352a2348a81551902d5d50c919c731e03c2762ed1302113a,0x14950691d82974386c2c04605d46d8dfc64ec138120780768ea9cc3943b0ee1d476,0x1cedd809c72a0f658c2d959f8c0f89e87e0f80d6508783921bf1c824cea0ec211a1,0x1a54eab3ab750e61afe31240f61baeb53705c5da64f370ec890160352741e0eb042,0x15adf181d9386eaf58360530814e43e0760a3324326d60c0128378660980d40b042,0x10ec1fac007b0de75a1d836064c65c046961f80c21238b329e081e1b871cdcad178,0x13c080c2322401e1bd2612420312a0193a66e0b100ad605b0e4bb4018ed1093b242,0x1bc106c07f03a06930a1be0a369d81544c84468601c78444c6d01a5a99310921278]
def a3book80 : Array Nat := #[0x1dc161e4383be6e0aa5090fe0603c03dc680a1b81ae1ba360551dd753ad0e4a1478,0x1c734648ca1903343e0790f01e9d8bb57529586dba96b2ea96a211422491689d178,0x14764e50d11a8329a4257c608d0ea3b575f32e650d83f0f08eb9b9768498049d675,0x12c67811c9395421a2e492a04013b8dc1b6370e63b1750770ec9d1768eb86cbc078,0x1eea170a083b1d61a0303c9f8d0e4150293ad12a1d1a10f12863af3704810a1dc78,0x12ec0d81746bac135815a694c61441df370590ec150664941ec378424770e4eb242,0x10da9ae6b04a08c8ef1b87e0d61452603b0cc7581f0784eb10821278c734e521478,0x10c01902cc4c89510687e3740a0ba80b016548073c0780849d81f4244731e221278]
def a3book88 : Array Nat := #[0x1392c3f43b07a02804bc4753ac0ef0d806a0700d80e804f050a1df3766f8049c478,0x128c0b9951a163766407a592944900b2392f09d834242a37906a0e75c370ed3c478,0x12ed9d6648c6283284bc4514a34e45802a0f71e13b1226820922124228410892278,0x10c6582649370ec5ae349690cc58cad03608d1ac3404a0de4ee3ac428779d421142,0x62544608d18e2ccd68a2d192340fa0f004304782f0dd71ca244c09093c442]
def a3book (i : Nat) : Nat := (if i<48 then (if i<24 then (if i<8 then a3book0 else (if i<16 then a3book8 else a3book16)) else (if i<32 then a3book24 else (if i<40 then a3book32 else a3book40))) else (if i<72 then (if i<56 then a3book48 else (if i<64 then a3book56 else a3book64)) else (if i<80 then a3book72 else (if i<88 then a3book80 else a3book88))))[i % 8]?.getD 1
def a3ranksb0 : Array Nat := #[0xf83def6fd9f5bd4f47cff27c6f13c4f0fc1f03bfefbbbeebb8ed7b4ed3b0ec3aeeafa9ea3a5e879be5f97e5b95e4b8ee2b86e0b81df77bde377dd370db76cdaf66d8f60d7b5cd6f5bd5f54d5352d474ed374ad1f45d0f40cfb3cceb36ccf32ccb31cbf2dcb328c9723c8f1fc731bc6317c4f0fc3b0cc1f03bfefebf2f9bdaf1bc6efbaae9ba2e6b86ddb66d8b56d3b46ceb2ac8b1ec2af2b8ad6b5abaadaa6a6a92a3a7696a468ea368aa2684a02789d26f9ba6c99e639865c96659962559524f93a4d936499063e8ea378d6318ba2c89e248821d8621283e0c82a0681a02805fe7e9f57cdef7b1eb7a9e5791e477ddb761d6745ce731ca715c1701be6edb86ddb56c9af6b5ad6a9a668da0681a0669976559263d8e62d8a625846057f5ed7a5e1775c96e5b56b599645855f56958559535494f5354a52546509404e9374d12d4ad294912147d1b46d174551343d0b41d04411003f4fb3e4f83d0f33c0ec3ace9390e1378dc364d7350d0338cd328c8320c8320c6314c5310c2300b92e0b62ccaf2b0a7294a12749a25c93240902308720c822007b1ec7a1dc761c86e1a46418c5e1685915c541484c12c491144410c410f83c0f0370d42f0b42a0a027090220841f0701a0601704c1103409024070180400400]
def a3ranks (i : Nat) : Nat := a3ranksb0[i % 16]?.getD 0
def a3tbitsb0 : Array Nat := #[0x1000000094300008340440040102100800000210000000000260922400000000042140000030100080000010200000010e100041a10060130880020040000810800000000510000004000000883200000140021cc10110202800810860800020000008000000028001004458100000c00408000044680000c008000000000008000000000102400080000000004105400000040000004000000000030040200010a009e02008010100204010220000880000200010320000000200300000240054001040800080800400a0401020002108c0020460001030081000100800a00044000000000421100000000641000000800000004020100080080410120202408000100010130000100101000000400000100008003040120000000000000002008050182800004200004018000010012000c08010050000040040000080100100a41000000443000020000100800000200208000800022080000000800400048000100010401000002800000000000011400000102140020208000500000020000000000000000000a82810004104000010040000840010000049020000000400800042000000000008000810004124004040000000003c00081001000000080040000000000805008000c080808020000000100001200220000940008004000010041402000000082a0040010004000002080200002020008000000090002000401001a000000000040000040402040009020002010000020334001002400000500202409000e000280000a00000000c808100012000240002000040040600000000001018800201000002000040004018004000840a040400240040002020000000000a0080200042080000020108008000000000002600000500002000002020020002420020000000401000080400112021000004408004002020800000000100341000000040000880010c08008000040000000080808020010008000000000000000000000000000008000100000200000000000000004000000900000400400ca08100200080000000880000000084100440280a00100000800004e8000000404c0004000158000000404010a004000c12000000d000000000000000800220424120001280200020000010000240000050090010000000000200000200080080010000000230020800011045030000400310180002000001a000011040c0400000020000010000240040002000420000a400508800000000040010000000e01000000010000010000002100400010041000020000000000c4000402010000202004201900020002002060000410000000000004000020c000000030010000000000480010000084000100802800000001000000140002108000200080010220008000c1000000000000440000000400001020000040401000000200,0x100002200000200408000082000002600002001000204040000000080800d002140002044000420000000000001000000000002002000000040000002000800000000000a24000000020002000000441000080000000000000800402080000000000200080010010040000804000000002020200400002108420440c0210211000000000004000000010000000000400a00000321000604200088000c000088c00200000000300008800002004048100000000400006400000000020850080020401000000400000000d04020021010000020040010000001400000104000008000000000000500050810100000000000000200001002000000040000904000000000a00020014020002040000040000100100000500048000001100000000002402030004000041080400000000000000000000020040000200010010000000208000a001200000c0400010000000000000238000200042000000008000110004100000004012000200a400200800000000040010900042802200400204c00008200000000001800002000c0000000448100a110000000000004000020092004800000200000000800810000050100880600040200120c000001000000200044080000040200000020000a0204008800100012000]
def a3tbits (i : Nat) : Nat := a3tbitsb0[i % 16]?.getD 0
def a3expanded (i : Nat) := packedAt a3tbits i 1==1
def a3rank (i : Nat) := packedAt a3ranks (i/32*10) 10 + pc2303 (packedAt a3tbits (i/32*32) (i % 32))
def a3gidb0 : Array Nat := #[0x7551dd2e0d382d66b6acc45ea89442650b533b466c1276a2089abcccb32bc2443f1568c56da0458b557d1395c22f80b2794b8259992e1e9ab5f0ded07ab56b2724884e755914d2ee5bb55f52bb4b3693129cbcc2b330a0b348ac70e4508bcb1af278f6570f8aa94aa568d661207f357bdb95a6999c11b4f4d398d074be23699308b4ae9d52491652af5e84c9e94589ce7f308d71301c4e47360047900a314705895070272eaa98624347aab42f5e8564852c3d6d5e736b7215c7b26db068d107b58b69c2d3a5e2b78d4558ba760db67124d9eb8667d7955d6330281c1391401460aaa793296ed1aa8be28466497969cfeb4112bd78b5f6ae12692a2a46a49aa681520208651a049cc9a59b4f6794a54e4d63902b523e58526470c92c6a525db5884935ab36c4d4d55197076e93d82f6824b2417b3a9727dc9506db14ede3c55b361035ca154142b5eb6694691db511bd92ec4ecb9a8e8045ea2dce3cd272a4c649a6404ccc59044a2db4c8432a94ca1a4a2c91e8f30d3ca11552f8a6ee236c12d269d6cbb04d49f4b6a661539e4e5b21ecdb06b102bb680d9ca07e4ac468f02cc4ae0cfa69b0a22fa04275a76109a3284092e84097a3ac92b5876f00dc956554b893928762a53ab6a1ebd6653a7854c4a7565ad9c94349dccf8d71b271056ac7b674c5240a9c312b5db85ace5244534e256a3667d46f5a6cd4cbdfa46cf50087306196ad1641e541a4d023403cc92f1b40266a9d70e9a398b912107a13da4cac5e4b32e1ed28a04cec65f0a0a7b86e93cb01a884835e2d08a71ec4953d9a31476a3579041b63b610940b0845032f842b8ac5ace272131c9cd178fb2ee5264919640815cacc58fae566aac4910b06bb7524d8d80214b0e36662b670d0cdcb302ad21d01726653d516aede75888d951e4ac1b1a1b4cd2f0b14c0fa81cd846664a2b665e49212c57b69ee0dbbb741e26a5609b366a5804647599f8a7aab26c862871b0a78960ada1e8955e57b2f91d9167842d2659e27a701f457d6db439288d591514cd0a8e662e8692d9464a212b811ea855f1529d5e16e1d4495eb05cae81f6e09ab4b242bba7298ba486d602640fee15b4a854062983af3ca22d2821299a9e5abba62e4bc4115d6db3f02b13866ec35193e8bca4dc423215e1b11eb4ac52701051b316e1784dadd5aed62a19e36a9240bd09daeb839f5a88c9f3f457b2b10589d8a2dada]
def a3gid (i : Nat) : Nat := a3gidb0[i % 16]?.getD 0
def a3pickb0 : Array Nat := #[0x4002009c4100a10000a300101d0098656982856d00600024421003d000347000208d0804cf0002010002f5000005004a2d00854b000001000005480dc50000050000054092180819cd000c0f004c2200633000010504401400137200082600000348482300000340178000010104338e00800c188481802089001839142e021148204168480000030000d8022004025613400071081191282409008201000090914820a12150e5018600035b12f8ec68100100800900001948988404000500006640028000212f0000132ab090505722008af08450d100000602048924804c8d200400061b0020010840020080d8008281000312a588c820012500102300000100504304202251024a0007cb01022001034200000300000504003942208a8648210d10c400a165230026010101038a0600634900c4011420910043a40000010005345124688213350204420000aa000a0b00000100008200065b20598c00105584009c00d8c3060580644a900005c7840505044e2000002120120490220510187441182400042800080500020b00000384042001000542231349007002e04223012384124102801c0001220082b300f40200014f0000060c09c8010288648022000003928051000052000002006b6a000003900440005e5948480900008f32401824c4a001110202411000410700044800020200080500816d00004819052d0091430009070014c300119ad4c82000000f84258400008608011584412200000602005d02080800000320022a0000250190690844780000a1001873000009000011480201000a120109620021c1040263812810088689000c1000854b00008108454900000300008d00001308210688084000000100000300000500a561000795088228cd9cb41000420005b5a2220a00a52500051b1024d052210800105d00080d0012e50000030000010006d0000ca34008089c2114022004000478004649610a1200003c00029a0001361001950080d80841c60039820000070202010061330000c1000028024cd1000135091b0008123900000500000300906703088b00804220804102810a00000110008674218100003100000301022048910162001c01041d00005300020d00110f010220281450000214005e410000130000050000051050140006538004010005855098d100320444000521002b00000530003c2042d7286206000b4b0000144006221200ca000260002003490466000005006e0300052500102102022400001100000500000a000013000013000003004101442020e00080200512000009002b220004024a91c4000181000001508a41004a9403801d0005b30080090890830000030042670602250108d9000005122254e0010d904040030041802a4408800180008d00006600c8b100000982701e000495004440,0xe0041000700000582018700001300000a0000051a010e00000394a08b0000030101cd0080c900000190038600051504614e08082604010122909109849100000100ba08000003208500000005004842242832000003120855b502240100cf20800108600800002a00400a21320400501202194500001100060e000101102e1000002100000a0b000800400108080d00050a0800220071810012ab000003048098002c220114500048424440a000048f2006519422142039111102606051210014c30680b0b8180000000c00891012100200079340020400020d448481000021009a830000640005b920402300003305014704101200000100000300008b800006000a8000116300002300000300002900000300065b00119e2026320001210223130000050050a2240109228a0bc8123400000e20010800415300c2d70904581800280101240001f9038a0622528248509e11a10b0c01b890502024500408447804410700000500000500000c000003880a400006530010040085470062841533de8001081001c60000580101400000430085261081490000051101a200205524058200000510241204104801000c006e030200d1010a4c04992520281906804297ba820001020058050080090000030000130061811410a2017106500047000003000902000005010611000003001480588400001801f26a5c0082d58205c200003108084c00001d000042000805011e8a20201410280022411824d5de81d11280244704417c6380a218a12a8108a4000003f932ad001002000975804820e0002e00000504400884224200000fffdf7d0c00010051120402020006c281140800001d0000589d08100000050000668003714002ab000c0f00001500000208010200000a0000094a000100004100000100000100000100000320212000080300000300061d02058b0044710010bb40201d0000050220860000120008012880c39722b00000130000030021461010801227012289a100001a2c00ac0029150a4105006281b4888800080200000300000140110400430d00029a00222914641880010600510200000a20200a20000c0040822080880000030000050000310000310000030000038520a0005945068070024810822d1000c2d78a8084000d0a0041880006c504848025800818002652200700000500d73408302100012800035b00000500b82a8208811013081898800141890205050c5113818a06000089000448ab91380000014200898c52122000c000114221020c546645000005400b0000000c00020b000005004f13a0484000391800000d000005000082609121008520004b1e801f0180815000000300001304404c03690400000a26040b41088000010c1020206d435900058100000100008d0018010000060030125200811194304858,0x50884c22008c402043600460500000300011422ebc200005849482000901000004a0020010001010004430058c42101422131320062ce0107850000540008f9000205012408000519186113011020008081040e5502108400004200065b0401a200001100000300000100002d01928500000500690926270c00104d000041d002880010810000091014020000030104822422c808010200000100009c00000300028600802112418e000500000e5900101d0010594a214a0002454000340a00ae206e0004804500002a82808000050b060225006909100558001962000103004b4b80902084488200000a5c410408240800001b20201d08524202a80800009c81000c1001020000230030020a000210414600000100211480889400013554c30003292800000300a01100101d00000600104d00a5950a6315008c59809101000003508201b5043182020b00408230298a0000090008040416450059f100410500031000021a00000544024800002102084c000061204a18d4020012104391200500003010001a02108408394a10020300000100000300000500000300400100001931004031220100000380584000002100038918840148252900001100044810122b00000500000d4110c080000c42428a40029c03104304492360e1300248131400a1000003083193000003001c510100719550840400141a50270000d8401095000e804842160000310521020000014024300000350015990893100118c5008a0c0032810000230491ef005805000158000013000003000a398940ba0000050014539b220020040600804700001b04001400200a0302100119050104cb00101100060b00000310010201902000429c00020680a401000c2f00061110001100065300440900000300008500002d4b4c18000003000009000081001813d28204000d99000003000005822824281401081802000c0b050e2d222001220040001a74000041010427008216c9610000912300000a12213c008031004480008512000089052c600100700005ad000054010c2300008502429000400a06cd5200000300000100000c000300004b720104cb402001040204001453040121088e200025144570f70000820000010001010003c50000030a910808004901022000be49000012400a94208c4d000042000051010201000001000e2322024400005200029a029808825c84000003001a1901042540108400000301780a0a20410042fc0006a38939de000003020ac40080c703010000006000050b00200c0021cb00000508]
def a3pick (i : Nat) : Nat := a3pickb0[i % 16]?.getD 0
def a3hints : Hints := fun i => let g := packedAt a3gid ((a3rank i)*7) 7; selectedRules 11 24 (a3book g) (packedAt a3pick ((a3rank i)*24) 24)
def a3codesb0 : Array Nat := #[0xebbeaae99e88e77e55e44e33e22e11dbadb4db3db2db1db0dabda9da3d9bd9ad95d94d93d92d8bd8ad89d87d85d84d83d82d81d7bd7ad79d75d73d72d6bd6ad65d64d63d5bd5ad53d52d51d4bd42d3bd3ad32d31d2bd1bd0bcbacb9cb5cabca9ca4c9bc9ac8bc7a9ba9b59b49b39b29b19b09ab9a79a59a49a39a299b99a99599499399299198b98998798598498398298197b97597497397297196b96a9659649639619549539529519439429329319218ba8ab8a58a38a289b89a89589388b87b87a85b85a83b83a82b5ba5b95b45b05ab5a95a75a55a45a35a25a159559359258b58a58958758558458358258157b57a57957557457357257155b55a55455355255154b54a54254153b53a53253152b52a51b50b4ba4b94b74b54b44b34b24b14b04ab4a94a54a34a249a4954932bb2aa2992552332221ba1b91b71b51b41b31b21b11b01ab1a71a51a41a31a219b19a19519419318b18a18918718518418318218117b17a17917517417317215b15a15415315214b14a14314213b13a13213112b12a12111b0ba0b90b50b30b20ab0a90a50a30a209b09a09509305b05a05305203b03a03202b]
def a3codes (i : Nat) : Nat := a3codesb0[i % 16]?.getD 0
def a3rowsb0 : Array Nat := #[0xc843e4b153c84104b151628c3a69714c88f02abfd1837b146540e5b3155c84b1dc2991b1650f1283518c64b000cdf848c8821025407ac209f15c82377162a0c5844825008459edb514615a91558913b9684302821d2f16fe83866019aab6c0b152171709116aa68237879a64f23831a8263577f1951022b80b1bab0d8c0844e5194e4845fe8453f18206b1627196c2b159d1a7f23448cb29d0449671a822c600a82aec83b05073f11551cde97aaf2c318b4c4f29516c04b04291819c3045081524af60caf77f030a02292eb1bba44ca0ba81f18548283d4cd3fb194de4d64a8477eb159c7378c45c35078660d655169a8833c2c57a032a60695c84ba9d186e8d9a1cb3145133731784633c5f055c84b144c63fa795b22a12ea4690b128118a951704c6f5a8af5e3159a02a0ecb106429afaaf3d07ecaa2f912336242ab4f189411859e8eb4c4dc5ed151b0aa542425ec6308c67be36baf191cd0383c0496f146951577233664b6158c44a71591e47b20c6c34b12dc23ae71937a3375083674bf0c082876b09a05b9a0326d4be5c84b86ca45c84b5c84bbbb1a876b26ef17b81156b6615847e20af0600d1a1e83c802c650314d07eb1512b6117655150d47610116ae5178f682158271582f5c84b87edec3a73684479a0c7524abcb71883c23c3ac65c84bbfac5c0aa95c84b91a33cc684823179e6320cb1517c730af18772311b68448c8309517070794522a08c823ee7a5c84b1102a178f1c5d1999ec6280db5744221e725c84b82c3260479b600ba3d015851a084c4502af5aeff70314c5633b5484c86a9b2f1a5c84b1901e520821581b937191e0c6c06ac8f7182060e5c84b5a6111d306a1caf35d1a5c84bae29243036903153eb175c84bac4d851028ae1191103d1a6812062a1d884703184f50699a34b711748d1881c82551175271837a246c5191771621e79c30238ea50c7f1522b1420aabc4c336547a9324d1e24c8c44d6822883873077140c318849173d24463317776b106082565164af1457a505c84b38d16b48616ceb17a7198931a0d5185c84b4debe1986f5c84b5946974d19c0718604330644cb8ab0670832a313682bdcd043aeca7b8ac5a17158871583eb114484c39163baf28904559b155c84b16313669197b8ac96e3ec064c5a6a4c304c5fed27803277e225e716588225c84b3e31761c8324605a0119158b35c84b57a114302828a82a6a335c84b464116544dcef17094b0529143891896e405c84b7b01f670c65d0af4c11608d18110740503308ec8964b1626c5839134d69b10515ac7055c8c6496a37db193a4321b515547056aa847731a4d660b5cc64d611c4e8177ec719c6f53d15190a7a39197342ac8eb69c679a3632ac6f01b8320ea43236832c2c517d16ab7138926813239a3492ccd17b1e2319516bce730bc734bf16,0x891a7389a120321e5c84ba61070bd1650c338d443416325c84b23c325c84b86245c3516c0f1962b0122a233e46b91b17090e8721151f916b04820aec646317032299cc2f6569f78082cd008c92329123169023c59162a6c63e265ba6c3036b67ccf057519bcd0787cd843b169df1720a1b887187224d5771593683bb31958c32a0b019dac64f91996b18480616987021e73b9490626836748e59ec6a5e4d7722982c843431a0a07b10ec6792b1bceb15b916041155de83849130bb15ace0700d1a6bb189ccb3a6e796ba50a7d075c84b5587b278f1754ee5c84bb5e32422296ab16a0c3399e7016917557051100e1b917bfa9f2ee9f1e0fb14305b94349a516cb46d04cb60731a59045c031a19d1261d12114cb2af16735150e0afcb8807c516092c6070822f2798be827f11699eb10a115ae2441741fbe11a0e6555b515afa304b6285c916af4990320ec54c3b722860d1174033bc8567b482b446019d17464503e3180d2b6b5682ce4997d2621f51509481121162464d39c62922f45c11533e7a4bd1a22a211cc849e5152e2a425cb051ae88e0cfb06309c48227b16106f2091175c84b144315c84babab15c84b8c42aafe4d4c4ed42c9fc12276ba495c84b4729da3f1582719964b021e7b80517232825c84b70c76bb0050fe329b9170a032b12c65c84bb6f18576b10a7135c84b5c84b0862a21e7a4be8262c32bc812010840e676b262497c92503173e4c6ab81223d159a0316c518a38df2ae2a126c3a944c50313698c66f4795c84bb511646c4d2a2c5a5212ca072126827791603713b18824ef17a24b6bf4822a118314823f8df97e799c7180e6830331502f06690b0b9860be01107c699bf197deaf6cc82a62804542b61c84311190e0ac9a1025c31a26a504702a9a07b10eb162517bb11596e3f7db175b484af2823768a422c6ab6de3fc79a3ac42aa295120bcecaf2f71739cb05628142a3678e199ab175502bbe515c9707aead0376115547a8ef0ba911319b159e4454c07941e7385c82ca0c26f47a2eec551a822ab160d25d5ee8402e7d3b71638716cef1319c68c471a6ce329a82c5061053cb1485180762786c92574bfc2edea503096a7987c84cf90c0f5192ed0d1e51948c7e04cc4b9439bc115038b0abcd1458f18769e50eba1cb1876f1a0324fb46cdb9a82594afc4717aa717190bb1e0c5710c4c3e7a0bc2a24a509db1353c7314c826ff169ecf0ce478522b081c114b672b8e72ab62402cd83f6506d4045f6d250624a20b1574460ac706f8841e21ba94302911596e4d286695747259622106821742962d185c84b2f3185c84b5c84b5c84b309175c84b43046cbc9a5c84b675197cd07576235688253d183451696684c904d4e4836f682ab7141a0826243275479bd2836d71720b13015195588215683ae41f0c85ace46118a3333,0xd7165ea792c6822d11a05c7242a4da361b33229b011371cf1776840ea29b5c798760d568c6760b1a5c82bb4af828820bc32b102a04479cba4d7af1617518b2f188e71900c32b07193b8a99e22f1901ba50270cd184331a7e43315f17ad6b129c82a367a4f242372842ce3063482c7f160a0234a2d1584f8701162c4bdcecb8a10b03e22a0ad190f51a114a10fe1b32ec393f137722f6471850b183ac29c57162ce4c72e282b67bbfa0bc468442209234af9da4c5ca3d258af3231339f1926a243c279c7717600d2bf4ee3cf1844516c36845902315ecf9e6801d6b0ab64dc7c302eed81cb075a83339083c2e79423137085a46e7e6f8821e8be31116ba67abf4769e716c8015828b04b44d59046ce47e7805126a48b1e70bb51aa56ee8f6a3077012dc300a07a702f65101b5b3131803255c6c9e44d22cb125d1712e324fac403d0359612b93134447b8eee8c7c2f674b1838be1fd1718a736ba1446b18992d896317b8a4c0ea0eb47194ec32b50b10c0346511a2a8638eb18afe130c91a594733a0f823706ae02911633b46123a1017df1346ed8ce5155a6126f91622a8476e59a946d934af4ed170320516b19c30bd0e71712316b2ec4b00284de0e8eac61842a5c84b5d082bd4f25c84bcee824327d97cb13e408a0c779b473966b124a1429ceb02e720e319780b6b1a9e0e2af5c84ba4f13ab622922c50182971473b8f1a48cf1b4eb0ce4598764ca0e73714825c84b9827a5771a2df180bc09312c611516a4c720b2c51a1139bb162ce7abfa2a9a0228f269b94b38eeed30ac6c7c84b4e8462f02b1e72760f8884de5c84b5bf15a1c335c84b1fc7a195154204da3860c9e362ae29c3f17bcf02511199091ab9a3353c4d52f165c84bb51054cf169a0c6328afaef1806adc5c84bb007a1102821e7cbb4b1654b197b17a0adb1107b4df194c2a3ce51a4a63223e84c9a2a3e4af9751a5c84bb9b175c84b5c84b5c84b05c6194a775011532a3615f130bc3182a4d5588459a2a22f15574795c8825c84b5c84b957069e080388c6220847a118aa08358480144075831733e83a10c5333199669f8e91a25ec5379187662c8bd180323f9bab152a33b266141515ad6c69e65208ead084b136e7b7a117ab71227c8322a328491a7667ac091a37d1a3e9145971aca0aeb93128867e88eb291e4c3d07010e4c822b1a41162bacf5c84b2484c9e44b159178a318506295570dc3114422237bf173c4fd6988243f17a6b166d2d914d176367346f077808330b1590d19b04845e61b8b27274716bb11624a791a0837191029117a1863c0630710b061c73bb02a294c6090820a64d60d1a694b1b511590c9f81d1764ac65c8c4c571725d1337a291cac692318a9c847a50662c2a0a632a0e820031a71484c80848d6b1710820502b91e42931150a66bca1163f0bece42,0x3d58f171840e4c31534316c3282216807f51923c2f2d028a49052a68242a7bc96ee68a73798b16ef1ac86af779135003251030ace00ce4c541d1705c23576c66d673b7250468b10709e3f11631282c7c283091a144c51dc28ae2112eec71b6ee4bc76648c6c111534919c351765ab245b15a94315d11a124122eeb03862aa48f0502c638a824a233268dbca0270284da47169640ec9a7310407037158762857d0b9a9169927b5bafe2a718c1a8205d1427d1890e0e9de845c84b3722a2aa255ee82574280ac724e6333ee8350ebe044928430a0847da37190321b5a8235761b0ee2315e694f648041160d4c6626841106d03632c0482772b0773175f2a358919432ebc502a4531a42203698a3178d868481b111558e829cc7c1dcbf7f02dca119cd516bb65ab8aaf62c79a10bcb8b144828f076ab912420d473983154e9162dcb1ada403f11a23c2325c6b3266369716ab63e3e44c5482359cc805c84a4d064e8c6bdc63918b19e909c0b1695ced65c780f829afe241e0d992e7bba632065169a6c61cd18248c412460c9a2db08af5df153d23332e1b0f82a5b31603c84218690423229d031631a10d175c04cab6044151a43114c0a222db17b9d162c47ab72461be3262c823a6c3209181224d7c8845ccc5776c6142f050e7ab3b16a389eb9432bfe9f992df3ed17c5a7fc2eb06ce33634c6174309ab156908495cc69a1164ec848ae651e0af168d12ca799cd165027f1b517110731e07b9644d5c84b772325b5075c84b2b633738235b4f04344f7e916c3882018b08c8a9bfab140c241102332f13ab31553e82167175102f67919a2d1a848af914af3f03d39d0717513044c6c22761c057a4cf1532b162af831eaf02d191f5162e68232e7b0ed02936c56be7d50c7f9a0230f481b1058a0e796d64d9407351eb114084521180011734284376409aaafbe07ec3ab11a90b3d7153623003684a76b15c87954ad86ec2f00a84bd469aff150eb132dd178e70c5d317926795c84b5160d574af376b06c4c697b15b50834f91a8391550b1a9db18036236b5170ae34c1316b5f1a89b16c65185c84b5c84b5c84b39082156c55c84b7111522083372337a4af50e285c84bb06245c84b5c84b036b15c84b7362826abd822c8876c70dc735c84bcd4d85f7175323093e84b2b149f3197204d232845c84b5c84b5311a5c84b93a8022c835911acb6c697cc69fee65b4b139ad699b189c3130a6055ff1a506b05c84b3b0c682c23171175c84b5c84b22a501b8845c84b425168d833a0d15892326c2c30eac43727f2baf25a716c0a32b3cf09e41b04c6805caf19d1682c733e717b724ac3917c0612bf6af33f159c079a284d9a11590d18ada7687d1aca07a714790970d862bfaa0afcac8292e7aad7180802857713a1cad91e1f03b188267aa52118ab185111596f159,0x41b16232b0a542a605155be309b50ab5e131144ba5682c55077aac6b94092a09f001198d4827aeb15e3195124fa64b1273163d9184ed155191960c7a92a822caa35063e91e13827175be51a351ab4c2a842afa7c84c06785d0b125c2a2ead103a6d58a9ab927c8aef20e0753f1199143d1fc821804dc5473b2e0da3893b4084c311899f19a46335e64cab83323c286ba90798733e44f061192cf1522a1e110240ea73aa6790323d7a23277e32a91155964c85319ce40ac0632be013035158487e3250c95d191df1654d1644c4d04d13892737b4eace43158a7d586772d11522c7f5027257712144af7610a9cc221549f6a6ecc30b1632d029a32bf4b121e8294efd2c2c4ca884666c520a27954c85c1192af14018c4ced195411521ef220633a7b1ac86c496f195a80304c300d4820f48472e4c2ab15ce4350ea500e2c4bfb176b63232e7a278af83c327f31657633335154471759cc361f0685118145183d9178c8715c0afaf08220a7942b167811a2b673844b65c8321dd136f9186d51a09c837f506b5cbe548050e883a3ac6a0b18bb1145a916545194c8fc1141269309115145888da4062ad672afb16302f142eb152a4d3471904661737190a4cd914b670cc642a328e084540afb0f1746e7bcb668021055744d85a921902a51b19c071a21f1aa362fa2c45c2f147b1142ead219c7a190dea502a65c7b820b1964483e232b921b02f185582dcf8dba991ac9b166d61f1551844d15730ff822b002e79951169cd15586c63268f650512b8a480433703158d2f0ca11809319960329a0791111ac32c690718afcdf5762f0ea400e314aecc3040840fe2f20a903a633b07146446025c321a2631a1179e082c38099187237c5c9d918c971a2a2af9c31581d183222475b18bf518a0ab76d6af11f199e3126cc2365d1a1e2b1b811a558631042214c800f4a3cf5185868283c4c58f0ca7cf2590acae3197891611e830ea26b9b1950f1632d0646f1a7f3171dc4665718145147ab1878e63546d905c5cb86d4c3c724f4d690cc4605167b883811169407f4411695d0a584835745090f193a10b28c8419024568b15282a914c78ea489e084c1d1853261cc5184ae98a648374b058c119258765bf1a59f1550e23158790e88297d130169f6ed155751520610b000184107a51165b5161141e7f4c71ca610eb19b922a53118884c52a516b5f151262383c2f018c60ea21ae31625518574c796b1a9ea836f9175b284c1223a7f065c03025c2d4da798d08f9643ebcc7b9a02f70c80198682dc8417f1a3271697e7a3f8de606f02f719a364b9e51381e793d4bf16e796588f05d154307d5871aaff1a1587ca1e6d04caf762328be84aed1a60680532334b62a95d1528283778c678c1f6d66951713af47820a4c28cc697e9f4ced1400b18e2c510916090c69a1140ea,0x4113b8af634b15151a1b482110bd8291915680679158621133e32806833d22db571866a7363b1a3a0f0a81166f07337a008c45889aa4328b170a84071036ab172c30691484c80831e22fbf5173088426482b4f073c43f6cf15506091e31750a4762eb1b046f0402a7f11535c361751697a6b38903658d082c83711138864d1591a3f71a6f7188b71937a076ccc5282280c9133027f3a0c62fc2977222b2f164224d46e615c71419d1367318a186d89043954b0bcb187071ab4ec6036300ac738b4825d51545716376ad4d0d8b471a036c470813ba6237ead9854333f1181704d2f3163fc9f07c7b376af808bca3aaf2a1145b4c6912b36044d18cc63ac071fd15bc028ca1110eabe78c4d6d62440ab1c10391a07932a824308365a82c351ac3a6d19c3371f15abed692ec4bceb60569f8e2c674915bb66106919b2492808723d211c56c6094b14b4330ea6d5e6284224f45228a56a7a0ab00351693b1a3d0325509f3c2b09ba8259623b227b2fc24b1b198e51898e82568c85328473318caab630a4d9aa8470681b004c4e0133f07835b1a524824d433154db2deb1be08259ea366715678fcaa0c442cadbb9161fcc75bc47bb6af655176ccaf37cc7ab64f809195e713ace1d185165de137be504969d54d152071477224b411a247150f824afb19c26b165af008f183a515a2b16c44df01515b96b05b2229eb1787b1604f1907b163b85a8e4d90e682157199e4245c08285c839a515457034c29f5bf14aa111714c4844c452481a1d148d31833e84c062f2a28242228cee235161b41ec6bfb18cb6c443e83c36828fe337990b4b117a511545c333a0d8c467aba8c7a4ea8a3623aef199e0f203a84a4082be07a5c0975a84d5171928ac6822adc36b1646b14dc82bfa07056731aa6d50d177911a206836ec30c5c03b001b3250b29a4d0d28399f183b8b18c879a7a5e7091679a73a70823a6274e447656795751314b16a50286671412630b5cb1880c60671a0ea236311593e4d678c62947a2e6af10c846d318a6482743092511891e602c28286cbf7c717580d296e4b4543373b193a0e877a795271a2c6af56c828211a820af174c4a1d1a34b1820ac623c3054c4d7c433c5484c8683a90b16fa73b1a2950c4d9f69f40d1ac36c626a112b2bd02c830a4bf6ff1a3d31462e824aef10e0b1aceb3019134128404318698afb104db06052a0c63eea3630be62d16b064c4e5146d4419d0321111510684cb6bc10e63c23160802a78d16cb4c64d5166ba3909279afa12c30b0c30af84884c66bc0bd152231587caf3f64d0dcbf808b19bb15289186cc4c890126c24c0642451aedc270252f154931a28d197091aae229105132271742240b4eaf7627b65a83a0eb19e1061144c50640a0d1a2f91992eaf8ea784848217482ca01702e70b94364e11642b1558c84,0x13fd186be823e40e8d03308d1750a43afa1f528015eac69cc2723cc42371a2751a953151263256d189228018a840feb665b065a832610c62c28446e844c87b866f97a113696098130388d19956b108cc422715607171ca9f8d879138ff843012bb177a918379167362cb21179aa4c5c116250de70b1a6367b23cafbca829926c6807bc2ea4428b1866be492db26a47521177b882232c5c9b133ee0093b18590281e0b078c42bba149e31566cafa18847bec88ea4581d1a104be142582e0621140c221195e282bc918226321628342a846f4729e51a55d19a1e84595133d2300802972113432831f5181743262c348271867515a4c795be7e8d11702eb17a0c66d4588fe000322413317a0e331c51a492761cc82430451aa8f8d918c4f1791e4879901845138325f4eb1a6d422788d16d424619184e515156c8bc6778dec6afa1b1dc4da251394a7b5871735a92bacfe57516997059a0b061c229feaf58f0111632b7eb18d11693e691462815e31502b14af13162b13e46f806822a51a59cc67344dc725ea5d159930600717891190dc6925f176eac610b18081165bec5728bdc1a62ceeb14871a9369e174075a917106b140c13684501a3174af19a251725884822af188bc9db1470cad422bd0a6309f4f1bfd1a57f161e3152a2c4c42c4aaacfbcb172fa5e432825341f20915c9f1ab2f1923f066241143030866282c6c68c5192fc28a0f1ab708259f187402a3b87d8d4c8464420e71a416b198229bf2afa209fa3e6cb7e82666b7b1a25b97186cc31cab12346230c42a467148d8b21a2829b50d8484259c698b51999cc664b16510836fa32b722aa531619c3223eb153423584b6bbe8422a2f3e2c580516a90af3911761115a3716114cdae11665e7f25516890111f4f219c84a9cd1776afa1c2d23c7bce8f15f29f146dfbfa347e6b1a8c78b3f18ca8b3c5719b0875b3e80b271aa3d0b709152da84b6082cdcd103ad5178b075ab21cadf54083018c86d4a7468771c316632845b230712e111058173174be9f524c444e11594c61ccf14687b0aaee0f8336270623c7a205185c62920a8383c1b5d0c4a34796fe80302af4e882b5e2a69883b943b89a13a9119b34336ce84974735902d5df178d3051fc982e1187851672ac591438af2b180918982246f51a5d4b18c8c49a917686d9014b14de3f26a4218cae5500b19e6958ac6576af2ec735b2a982d13955143e458beb18922f219c4c8264fc9b1a7a116bb71a5c81b992b12d02322a076511732084568c55bc48be115258c4c93141f4b35be31bfa0937628686c596118018285325ac9e82cb518591178cb10bbb147ed1927411666b0b8eb0cb4840dedc1f4848307b302e71a68203ab011f17c811ab1e22730bb84519040635bc4465d173331664b1a01917464456cd152cb1860c8410c8222f1711,0x249eafaf0312793d27bafa3328230588be71023afa3574a8459e79ace636c31a93c7b4302f97a825fec6a8d1ac227246b19cd045767196611ac80353c71660c3362cb1178c4772264567e4e90620edbb50c762705b1317a371501830c411641715c9a28450690ea093ee2a884af25c1e684b7cd114162afa1cb0070c7afe295ef17060af2f8995a83025c3376b193c06085a7983c28362325f8900dc8f83c8445e7921ad9cc0844a716294114c9199642442f148eef83724d03ed119e7b07119768e1bc2d674032777176c2c48811878d152ca9fa56c49502a0c0c60e117ae518c3c93294b19a030a48d928665a50232ef143e2735bf1724ab09f7176aa32027095b47c9e413954af60cb1c5b17bd4af0e7161b6b15df165b2b1aa113876c3454b10ecaf6c25ec2f1abd8d0092f1524846171940a82b14bb4451761c64555002b663a2b13500c6052791e2304aec66ea790bc4e2a2b0aec735744813f19c0d198ae80a18ed8551655b14568319a02446edf2aa2a96e1fa387a16f1760c799cd174f0be119182fc1fad68490f1500ac6b208334317822c5001135ff071101f088b1b991a62cc68e457920b0b4c0e55010b8e6c9db1714716622be60d19686b035c8205518459184305039d18416736a6835742c70e835d5149e428376bd57caf424333a518144c4528220f807b966d2dc4c9b2db158af0f5171104d6ba4ea1a32ba917adb15c103222c799a87a2db1844d165b2070867ba451896e0c65c7574c920107bab314372321fcc62c27238a84b5d1610e28abe75308c42e29dc2114636bb93282a76f21471500a7951b185de72af0e528681aecee2c8b20ea24bb6233f114cb7192a47910eaf344df992f118033528bb0d479430241990025f184c901accc87171ab5f160846811022cf4cf9ecb33df16b4edf15919b40832e107076580e1149c91562682b9228584b30eab039d1360caeaf103128f00e318b42ffb3f0520b1733e337483077a2b966315691667479648b1aab19678b15c822308124c88f4223dcec32b485c3a712159165b27b376c88eab1ab832ab63d22a73664bc8904082b1568224c61068ae849e4503ec820a0304ee842a6f14b4033fa7a66c847a23377e2f72b0700318ceec6a40f85745c45a4d8c316638fa1a1120e07876916147197c4841911525c26558167323391a8f8e8de9a22a40c841fc78c3a1f2c8c504470816c37c5177df15076289dd16788d2be47a91284b951a66518955130ff1724a4dc805d294821043f5071621e701e0bc6bf1828c830f91632a4d453165ab151271a92ef12a1156824d58d15064238784d984d2aa119b00278664c87cc459f19236c4c5e84b483356d060322353ced323198904681c79bfb14b100e0a084610329e26f3f0b12348496cf8308335064d967180e6280606fbcec62a6b22063,0x199d08180ed4c222a2201109684bb468097076d42185abf0cc79c303da16738631ac11180d82a1802a08e9f1ded463b1971cc679b0ba2118bb71551af27c22aada0e18d15cee793a084b56c722a293bd164b437b4ef250e0232f166fb171e27982c7b422af83c2a3f9184ed1a39c846244d18d12bff152ce1b1488242f159e4126ccc44b4230911574a820011682b168e318592b1a041f32a34c402a77f127a0331dc428e918a90c6138dbc7d1aa4e8bb63160344d524c5379191dc4c7be822a7158bd19c3284876305b2236cc24678be24623b627b87116a2aab7beb377e2a37715ba7175df1acba2acf482a3e686ba9205adf8e6d2cb71a35b18a5717c2f182e084574243e24da8cbb1c08bc9a332ce014a71736e733ee33cf2b665f15844af1b518cb9172648044b18848310df19ba3161d428258b1ae114cbc7b9c0af25c843c2d832a265b4c42c90655472a90826d40c1ccb138c40ad083820c39da24234816cf16332bcb1f124db18b72129fee80ea4d376b15a8b18ef0c4ce7a1c1199e448283133622f69917b9233a364c5feb10cc732f878a24b10ea223d8822c4df8eb1491a6d83d131c31ab261350ac68a6c61dc4861f1833f19a610a4711622c82992b03c2f10ec8273070360d857f15c387eadb194c2c674115a0ec64fab12e6c4c121266d179e4272a0b04327899ac602f1958d17174afa0e3092ef09df18bc4dcc96a737c790a6248ca841fd194c877a167b96e23bb6830ea6b5a4822fa834e424992c620716c3f1839c8217c2a1043dae248528055c7151ca8415e1f0bc7b6c2c2065130ea4f9645b5251a943162f24d69117a0f161cf1760cc26e9191ba80bf2f17af1518083912dc5fec46366b2c28360f181fcb0c76960324da05190e31340a8366abb63b1858ee84220bc7b18aa482149166b91710e84c5d172a6c70ea2da6eee5f8bc96429aecafb264d15ee8adef1bd8d4bba1008c3784716828b26c27abd31aa5906a5cb1a20c60c51660c832e91a6f4c61e1199ba843ee24a4e1b2331870f1612e15c0918b48118eabcb5e4dc82de6bec453d01cd0af0eebc8d063c107963f1a05e842dc325888fb8b13325184e718954c5181169ec8025c6d37ab08922358cc615d18512032b412a462ac08bd584848bcbeafa1e3427a8e6f8c76a3a56799b3190e638bfcbeab859217190debe77518a4c8302e841ca80b1e83a2d161c516590c3656dbb62b12cf133a41f091185c0b1bad006e918230df6342a1ca8268d1a3ee0708eaf1bd173f0c61b6c677a396ea2a5e7129648e5eb18a8c9a7088444e13ae2bd6eb16be423a56c88f69f9d042a3d0ac303fc2685af0af0a64c95cb12dcc32891a0e28f82082610c33a4248206650a4d5ca245586548cb17083220f174d6d719c23c1af2b5ca330d1656838c02932911660ca63763eaf0b15,0xa2f932eb1832920d517a46703620597cbc90e4dc54c650e22114bea06b01944d77a822588095c8f7c6b2bb47dbb6aca4f16a5033000af42ec67c5159f506ca0b1087158de8240c28af47a829067362426b1623c794304c63479b107aabec4506be8c9131b71850e798d28060d167a3162c4de57eb16eab12dc2f04d1759114b1e328ea99ae1158863222a332c27382284c2e9232e231b4c67b884b92042ab1977715965191323472023b801137d18056623f075604324221f1a1153a0b11b51690716114a0a567b158338f3163151759024828c41dc13156ad9a117a8cacbc892c3b18c930269717bdc0b3fe6d4aef098d0907716a65074a64d77a2ac065004d19a1f178c8af335161048f0ea1e52823c2715ba68307688a1c366d68404612b62823a601ca8c8b54826d44fbd4c4c391968319ae6d8697188f5175c82347c7a3a62329b16a4715c504dc8f1ac9a2f96e4f33314c26c476083bdcb37c69eb8ebc8a282b11173dcd20511770d1a8f7173a7169e718ada0913282b1033be5137307a85517ab63f2ae4d7e5160907958ac46ec4c5767917318bdc9f302b10a30187c75a0b19bc518c287f932b1778af70cc4cee1b6071873315954c423c4c3311752912388b17f0324e030a9f1403a4c4f86618cc332cb0c2682876330447a5742053223940b1684315f91a7369ea211549d176d428afa3265d16013178bac60ea101271777a3221b188b31a702c50e2e8b94b1718d17f046324ed5fb17828c742b1728a7951ad0a8f172f31596c7340c32b1eb45683399a32c9a21a24826b71704c325c8b175b1922a4d1ff1633cb12a317ab64b16633767154e02a45f164a317c54723f1130d915b507a0ed192ce4bb4eb35be24400af1489f0c805a1a33ad0826c71a52ab1c2f165d08444c24ca879996c42a6b1ca04b83318a6d172b2463fd17720af0e9183ad1771c840eb144e4428c873495198c91a820c461c1b4b42b7384c1e2e91a119050003c4588928408e612df1952a2a71b18a8c754969f2b6e6064122c4c7cf4d1be117b2a230707a1749f1c08f964506ced232e4c4a07d58ec650c2a18a325a8280bc4d421152ae248d8c79db15ccede83d12c72dd95d0c90c827990c6343257e824e71519e6d5b5136a70622c7b2a0836eeb3ace2670cc8b2e1f93e3025517afe2ac1af809482b72139568296492c803e590361aa73aec8448c768eac726a299e0830ba2ab9a32a0ac6422058af17c111791f1383c7b3621203ae8b1f1a6343318d18772079a83546d154d08060c7b10e3025eb00431657c8419d195c11a08e7e58679bf515c7c1b66cc624b1a88a8376e32a1a843e43f432af776b020629bb0249f6947a22ab4c4009d183e4b0ac2848e70e7a084912b1ab3169a033bb714589120ea76867138f5188c082a4a8465cc37c64e9f6a35891a173,0x884c8031926b18791551cdb4308432b1ac3e838969d626af66717bba2450a9057c698ecdc698729131545233cb483a90a31dc12ba633315185871696f168b481c84138931343113c2ad80f4835d4c5b4e805c09a996d9c5518845126c279076beb451a0641f6d44b602820871648c84c531836e69c0a2f39660bb4b055917a6b1aa46321ccb030a4e32e841fd14bfab002e8259030690c477ea729d061f47940c2923c6f91e23c2ebd9c8835fe6c094c6884b0325150c0391583005665b02614cad477eb27dc29294b3aca5810e6919e65822800e67b400b527a13c451664b17baf180e6c86251659cb16f518828ab2e8a489315afa111a0c321519a98c5376be6820e7b8c640c151a91748265c531a00a73258b3742db8eb13a64845f68410e7ba44f13ad183f02827116780c5600849a028554bc3d28488079b2b16964794de4062eb0b4718bbe824a07945083a44d8a409f88ed89e405cef1258cb1718825b4824c082c34c36c2171744d1ac59580d1af716bf4860d4b03a4840e115c3115b171ab1b1696633b2a05826838462a912ce2c51a0bcb09651ac511997f1505316c9a6d1904d506c6ae44c20ac32e8840d46d126c46d63076e33613151f228b94c8b15135b1190c04d524b21551696ef907629bf4d93f012c9a31c0713454340ad1a994825fe82a50225c91220632b686d2187348d065107aac4ef15e305451649f1848517bba412d118a1d168c2a4007153268495c0e1dc050bc0722d06105182ce2778e3692718caab87f080914344302d7463368a69915170bc3871d04c9a6b78c4880480964c5507158c917422be5ad1648cd80d2310d224871150e633522827811832cc50402b174b15b512a11156c319627185d4c6b5d1832e279c6db08e7b1151a65c82c46998924c84715b724565cac76284b00231e9198384c32432aa884b0f1a4c0b17d6c5762114327bb44de781156084c6ecb62808e094313fa72376c44c91559084ce44fa0282afa445b47416e69538b0a20b08c44025c21626d80eac6b96c497b186d411912762b116438afc3e8250f117f0368eac4190ff2d0afc32d882918c811792f19914b05ac1233224c9f17466da4e51a6911524ac660c2f4d082204829a11958e842c2c6a3713611179927d2822a59716a98c642f189fec51428cc67184246dc04c5682be1fcc5baa8448d1a59f144ae9e1a8ed53228494c60ea07828f05aebbbce690c4285267940c3383805aba822dc124d9195030422e8340c319cd19772060acc8accb1071060ee4da5429a3e72b724742c7b144c8ae433ca91a48cee0d3159605251b0b01b164f1197b8b1ada2aba71576b1670ca421e847364f0531a992c40c81f32b17208c645d16bfb164d9157c42a8a28019b169a0af4b4390945b862500a117456824aec70a7024c31850a4268cdf55a9d,0xccd2874a62a82c7766a77014830a0af6df15a7718720b172a8220a7a654834e68311513745152ea330d4c897f16c7cc37722a12e84b26df8e8c63ac32b2632455188de4da501bc3482c347b9b31a0e69f0bc396822a584f4378c611b15922d983c053fee84851627f097caff17405b9713813192d04c6ef187371604282a1c7e04cc22fd14a4d15c0628378b11bcb7bb518966c82c684709172367d8646d0509f9043299ab1b627994905a4c822c4780e07b0d48450118490815cb154220e3551833e7882884ae71a50aff934c4b1eaeb911a0c88452916bceaf1100532118beaf0541125120096e24ca89fcee7bb5e15724d68eaac4221028b18912436787b0ec8300292b1e304927b34ac610663baeb199707600334e444560835171253d174bf18156c4776c40aa836eec810458cf71872240b63179e3174a1189e31322b1a378a305ef28e6d0b86d2380820ea28168cf4e02806aaf8ea608aa822e3154801389050494b16422a5bc4d96e4c3dabccc0d4b265d772b15c8309208291e2442882950d84543985315ae2796331940af69a6b16fe7a8f8821e2825c0c862aed53e80b2d15434dcb511738084c35133f7142fa300c514a6b1530a0939cf2c9a76b411736313b9b16258820ed1825cb177f175bcbd3624d2da81a504b69d05b222ab948200084c31135d1175431593705c3c7a2a49289118b50b2c300d33b142b66599e721891521ec6964136d62618cba7c91ab5079798e8c8ce8506bd650c5840f221a82a1d174d653b271583716bb484cbb16ba61bca0be996b05a84c0bc24a90794c858a251511e826d43e8904f052bf88e80040c63768f036c62eef11eadf506b118ad1966c678024c02906e6b13c2b16ec68b5f1788e83cb4738971571cef2cf171ad175b277c3cd8b26847a4c4976af78d1418316503158f3178127950279914ac866234d11a089185281e95c4f25c7d3f0894ae8337ac6b924d8624a416235ccb0b4e82bba8d28224a10c68e08251af8076745c0020d47d7c71972e4d39c63c1b18104234307b9cd1abb01f1bc3074117966b3c9a24c591a9b50145432362af87c7f14b197f200ca05c5c716151190bf17b06320764cc96b36cf17c267d2fc231571a658d18be819e2729ed173e40940081a4063c8681632d15767358ed06cc4d21300acc790404d8ba825e7195c801b1e8446e821451587c8228683b491669b16a1b1ac96af7087a1ccf7798f84c1156671809282a2a0d0ba7a5e2c68483b887171e2af5bc13c7c4c52915a91161be82bb029234f6ca9160f84dc3e721f315b2d16ce1195129f73ad14aeb1c9a7bb8f19a76c64dc4d145172c4b072069ac4af9d0368b268040340c81257d10b7316a504d104c4104714e67a126c67d6b024913c08b1ab716b86d1b0e8409515be0338d5182d113ae4076551960f1556,0x2a1e94ced78d1a0a027032be912805d4b063073884ac91f15a0316ae2c7b2b1351e8246a577be3425c2861317ba91895c4d20ab1992847a0796ce4d0ab037dc2aab61f1a3071bb181a8e81c11a8791659713295187724dbad1acee2f91431549153e44d4f87419c72afa24216831491891a6925879b99163f6461fc83b2eafb5e613d31507c655740ac7cafa0513a567cb401275515a05144c91a886b114abec768241f1a96679bcd15671189aa24a24b80371a37a2a0dd166fc84947166344dc308f25d1a23c820a7171f480c7679c840e2a8e2bdc7b002bf02ec6afaab66cb14e07e224459a24d99706aa0c3382bf4771ac468339c6d95f17c926732d183d3165c0c4afa23c7a8f50e68c227a2a8695b2280411838c2aca8b15e3183f62abb4ac174c6548292823197a7db5683a391a5b2c3ae514b54696c3168289e7f48340cb0019145c9157dec68c8b1a8517a768350e1ba0f152e9174da920771577714b9232c3ad0167199303950eaecd30505a6100033322b67c2c6b4cfc6ff17b9a7e5c84b5c84b965163a6af0560701484492ff5c84b5631765b0506072a3a6890ca3524b0a7cf82809f772366170e7084d9e24c03313b0631b14ffa647f71cafc81152a716904834b4c4674c676e800ef146d631bcec4a97163e2b0122b1a1c50294806ab152820709424bccc65e2b896443695181ab195c84b5c84ba57037491720607936b25c84bce5199e446c3d1a22a7645b16887165c84b90717432759f4c45c84b34a8140082a5c84940825c84b780305c84b05c83b1e1a3a42308ec55c84b1040e0711854079a10929551a6f084ae67a9a915c34c822d1922a6b9d8b679a32b6d18430ac20517ae428648323f0402ce3370e0018845632cf51b0141ec588f06bba3fbdc62b607942e840aa8216918b6f150943228203a7c7c3b62aab9163d228772b25d4a3c9313a1c322e6b11c0c6a6eb18922883c4dcef1ac491743aff33f165a8b0154a3b96e81447b9048497e826f87fb224d4b4b1a7673963168ea5e9ff0a6780ea02b15eab1c04c67d2e816c1161c82400844c91825d14ce514bc1169e423b9b156c68338d159c917a507f6d7152ef1843c1122a31c3abdc2af130b18b551796e3da91176ec23c9a262831651627128d92f87a10e2359715960821aa4f45a05807186a6f1b1e828771423682b128187b152e0820451928d06af0f25c84bc3ec6a90d80e67e46e765c84baf06f1be11702c65c84b22cc63e279c1ae05c84b5feb0c06c3876c88c43f9611a48d03156846e4b160a7a1e24bb04c41e0bfca8af0a67d626b04fb0602ef1452845c1172b316a0515a4517142fda65064e436bc04d377145feaf61d13bb71705d1760a9e6c2273a5179aab17ccafa4a651104f03aaf767168761fa861173b0d82a2a86ebe88670892af2a7179a0c8cee4,0x328771310e73174b02d4f061c2fc28c6aa8615c827cd04cc769f2fa11ae243c96843a71558ac3c7d161a2626488229e335a80703227b006eb1f17422b12b22aae5158c0b16c31854316baf155e317456c64b4079d51776082b04c655b152d0b16ec8444e159cef2b92236170a7c279adcde992833d5190f9183a10c3e262a8684a98b00607a524c7646823f05861c322ce2f24b1804edb9fe82ca0280e26d0ff12690827948271614636dbc511671072433074704d83c3366cb68c43d2a4c60ac7b7722d4163687d067c2368b0835c913b7f031251a6e6844bc7b21ac640115045182c91830c0b5691a8a116c9205cee3303b174c50b626f12ae2886f1991246a1c29918af37d16bd5072faca9644fae0246fd1059d122d4f1c80b04e5174b517702b18aee8bce66be51679ae8ce4244ec4d4f8be6ba470bcc658ef24811a8eeff174233f6bd0a6679d11845670562b11fc99506079b47b50a0943033610b12a8732431767840caa4c7c6b762c4d37629ae6728fe03ab61b10f1863517b1b146ba4227d171807a6a718650595c0786d623502efb4d193d2adae3182beacacb17c927da4882cec23a04296823e6e7159a0b160d1273f1a9bb1a22a7b070d85008238d1953d0c8c4290c7199e2326c2016104dc51175825b76e826947932e3004d1573ad222a7d3d04d61232798ed79716ca880b98bc2c4b1755033e41fb211a59118accc69ccb1b81189c0b1c327928e65964421fd169891a1702aa05165d49f96e2a98e6f5b271ba622104a9bba4fbfa39265180a7150007bb8a31710b1706822ce23ca0c61d082454792c4c602c827f29f1dcbc3a61ba042311512c1c7902f1a3f8b19128363a998ea28b65194e11a6844a65f17a448233a3d7de724d6d850e6f751156b6309e429733161a3185be590a1161ad180bcc552505568b04fac50e08441f1842a653222371316c3a053ee31c19163b8847de68c9a840e51a14c87cad1840b199d0310ad02ace19550334f318384690322296cd05e64b745189122d0b318248af5504e91e4d735164c8b148692c9a506070575eaf1e28408483bcd1757d0c844b85e2b1638ffc9a4d5231863e4a42c7632a43c9317c04b13971a8286d7d71a29c78095183b82311e813a6289121062eafb96cf25c29b4cbea1c4460d18432b19929acb47d62ee48af18c0a710e09aa4f12bfcc628c72580d4a9072914c5738285b8849e07b25ec72fa28ab882ada4d2a6801e11a4e716050798b7181c917453177c6c7c8032acadcc2eb1b05190a718b4c3fcd47a3ac4d0b51a7c6b0290b110a82378be15874a5caf9ec8241eafcacb1bfa293f03e63515ba62859c82b271418a4dbc71910f15445159131605f0787d041dc50444b19ef0976d168229fb50f00ac839a832454c6912504224ca51129c0825751a106627ae798769aa,0x642a97d15326730a03358eeda9a82ab64c3e29f48cc649e8294a8287716cb6af406de08e7610715aecb6684464a082c9a7dc9a36a4d18a60f20c115bf4790bc298eab016e6504117ca8c6be51977519afa2c85232000706b715710819e268ce517aa8df3864d4524d6d6056b62867082313180ef1544d146c4bea6a132fca1b6b16292b704c727c7186e4c662ec50761e449162587bbe44d9ed053e43d760c60ea7b680730764b65b19430ce7404da2a299131983c4b7aa928291ac7c799e07e39d1493e4c3d116156dbbcaa370914bfeff132b1b0623254000e91608f1a0771abcf07551161100d0761b92282c3b143d2321104c58914c0717c3aafc1312b724da50326ccb0b67150c44db711860283be0836cc05040324c50a3271779b199ff0c82c286fa846f063ae2420423323c73191140da822f681cee304e919aa11832633ce43e464bfc1a658483660f17376b320914a3f143146058ac8ada4f1b4796ecc3ae0fb79b0c432848f117314815fa3337915ba6309ec52c843f90515abab6992ee22b16caac3c9d19c06b157443033167be4ec0a7376acdc34793d31a8e6d1508af144339324e25c508d51a32f177b4b01caaf3ef1596e290407b9e0b329cee9da32a1703444c64d659b011a383167ccea7442aa0d173b7157b4b19131a9f4d80cc7b80f16cd0464826961c303f61397c6050e4cb2eb1a8b14bc0295c033020f03c2c6c30c6983160ea41a4084292db97cc48660c3e2c6748596eb1551023328bc70e0350ec210440b067da691742d1aafd1abfa4e2d1169143529cdc226c6a40b957b16b2082850dba1d152a86d748242ba8464918cf2bbbbab1a50b17547e53515b2e287e6c67a2c6b12c52a6834b42a656a3a3a727551750e729f4b0a4e4b3a513a4f01b90920bc638ed15a991852827abeafc5b1841319602c64deb16f8b199a39c30084551599484b20322a4b118d11a5f15ca113ab91ace4325884c27c32610229ab1406718936c7ac2737dd163f8c6a9eb05e715a07097028304c846241396f12775167371590517506008488241eb082c33084c60f8320a073b722491e295ff0682a29ab24d0acafbfa24af0794b6235ccc447115056632ef1510f1778c2aa4ed99e3192a2b174809b98bfa551459eb0b9b1a59116c27138a31a6b9187c2b163e50c091605d134751acd0c4ce47a79aed27a1161e825241f3ac31666815451705c5a956af28717324f85c8af40a8118440294c8a5713965188d44e5d482bf470cec12a951385b1abbb196247b2b25091f1609cf229cc64d633c3f15c56b19dac429a33afb149e27a1a9185909a63e46c731a0dc653e27bc56c719d151844f190272eb17a5d13b1e173ad147727aa951824a245f31656cc6a1b179fe8472f1578c055a829964468e718c29186d714702db7f04444c295322fa52,0x84b0c11819c280e07d5c84bbcc7f583195c84b71b17cee32c97195c84b7b5059127bc061f4e8c78b082c4d1620f181ccc55c84b3a43060c325c84b28f1652b195c84bc571562eeec85195c84b2131aa3b1a75a7a93f171d052468336d42a16d1696ebdc3b155d115876823f0bd1891a5c67aaea84322837a8c64de4f8c42458a84b89177be4370c7b158280fe233d516166007c465cf8d1394b7830be7bf1ab351602718114225b51780082a906c040b123d16a411841713b391923cc6094842fd1563e459348220917c50dc77f1696c4096e280fe8450f134691a72e238051a232afa7b168231443d1a60d130bc84736298a2333acb11487959cc4a10c4248821aa651e9157f91604073b2f1500719c844f5b4af51d1ab9a3564717cd318ca0797b8c46026f9e44ca38bc886ee5ef057483102eb211116c7d12a4f1971ec6adb16662d172f149c518286849667b71660308306d64c731194c1175c84ba8482084af549141a8b19791602eee5c84bba713b48844d682594b114e8383c27cd092750323e2316d43c72e24a2c442149e922b05c84bb831645b136c21b1b6839822a8ea1252a0eca87b75b1a6d512992eca4483bfa32b21155ac5b6d4295c84b2ef052a2c6ab6275c84ba25180e11640c2a3ff0c19c1b97b130e2b05231462b0c0d5155c84b5c84b7c9175ad1a6ec6e45717157189a84f6bac665a8436223a0279772c370319b80c618117884c40ea3e127155c84b5cadbcab1352b16808c642484bc8905c84b2a3141ac32038c53f31866a7b99518cec30c15185c84ba9514ba1185c84b0b2b04d07b624337f0849f6825c84b10718bd116a56b3c547d4af0596b16996f20324ba7cb6cea82832121168460682b50f1a4a69184bfabd1637ab1821195d5162fa7a840ab51715cec83b60346571609460a4cb2c3abeb38720df16ba64bada8a1462902e7a0dd195e60c5ccf15bc116366d6d427c931532c82bb4c6c5a32b001295cbe20ab3bfa8296ab1451179cd1223c692b224535133e0b5c42b1b63158fb09c81144b4305411690a603a64cb331644a9219c8396cb16e6825f8bfab6290529291e4692b18b8ec523c1b32e280011a1c5151a0af3eb183ef16b00229e10796d184f482a90b2156b3b389d4f7165b50553c3285d176ec831f4c865af1574bccacc619116ab9184301f4011a5284d4e6809a7157aab1ce518c96c3b944e646c62251a4db1642469cd118996afb066bbb0237b868bd4d0502825063f992b2032016ec72507185bc245e1176c2ba686d6a5684776c5c967a3084c081153291828119018123030232f12b61183244da1a1584105964445111378c47c548318b167b4c4a6ec6a30f83e4bd61f17684326543358eb12ec8296e0eb10dc60c6fbe4294e4b741e827e41243a9f1102169a6570c7e0ab1840d14a4cc6574b1]
def a3rowsb16 : Array Nat := #[0xb1ccee43032b011269118258c65c84bc303e432c6636ff3e4bea06c51eb16569145c84b59d15569151b67e3f0b04e87a7df17432c837b164e1174b715aab1703b1320624b2034a1c8025caf8ae62036af763162b21320b123fd16525146e6c6a9b170acc6bc8790f9177748e574b040adb5c083714c64c31787cf15b31a26a1397d1aced15400c455916920b177f1502d185fb165eb154af1710b032d07970d077bd19b94c669a69b3cf182c4da18690e63199d06533161d11667316b11166c2bea2a9eafb176d66d0c0b193318c968390c8397b0265f18bd8d3b0290964156bb1a2b91670cb132a394d718bfa3887cac0e26959115cab198911a5ccaf72c8453e83866270867333e357df1825d18cb672afa2d80482c085d2fc4d5411960c820e0c482716a80a40c1173c2821884cced176451a3b1187f076ced1a281165b51a2dd1230a8297d16a1b165c84b22a2d47d160bc34029165c84bc13153f644886766081f5c80493706376589608032b1809d078483784838563155c84ba2a4c82b145c84b0e714bfa2bb609f156b010e33779175c84b8a232c8c69b0b1a7af185c84bc86c65c84b5c84b58a78b1f150651a5c84b30918b8d16a651912684c7cc496ebe74d1a98f06a4918ab62a4a0b1777130183308ab65c84bc7b196b65bb9a83b2e23636765e6011e08c46c2a596289ba80702a35c84b051168851a0dc6d1ccc6170329143e6ec3222d05690c510e324e45072030ce1165c84b3e5192951962ae812f1a996c56ecb10eb185c84b954c65c84b52913bb1135b22f5c82817116574475b4c839cc52c492a44b2ac506156815c84b2a884576823e9155c84ba610b5c84b74083a3683a44c7a3a825c84b46444a5cc45fe7d7111719c225c84b72b065c84b5c84b7c6823ac33c4e848ff18bbabe6a6825a83146e8020e81000234c0c6aaad1954829ed189d117b951793315129055011ab602bc06364590618d1311069a907a77e826307bbe42a5ff181b6f2bc4825ed161744c58c819623370c9f54483ae4055af193ef149a42a1dc244b5169cc79c271723d12c34af3fac68862a25c734171aa4e28b9a288926929b17b00be7d2655c21129b1aa363065cc47be0bb0064b2e08c391882f16919028d0733a315c4c326cd181909e3ef171e3126031872ab13f03c9aab07dd1550b150e8798d065b061f566df99a8296ade1742a5c84b70cafcecb14aeb25064f3e4245feac0ea585c84b5c84b740845c84b1ab1695484982d897ac45c84b450658d43484843c97039ba33609135c84bb04afca87e23719541135b9175eca4162c3bb04d29cd87028206a79207177b4d84dab132eafb8c33ceec42c26d0fe30930325c84b2fa6142319b8f186ba436d41e9323481707c1b17144b1126afafab00191abba8f14473309167ab1a4aec5099155c84b5c,0xdc1bcd28268436540c3c7d17840849e447c84b1a0c321f4d96d4443f04c55c9daf0ee19e733464c5742ab9b1824a42ca0a66a3173228471a332cf1240d1591e2ab7248682401dc477d273ab9171e0dc8d6335bd1a4e115a91140640550f186d4f99ff036507e7031704cb11a2695131685ade4c2827ccec0e906c288233b15a24c689b1aaa0aecbd1a1bd15c9a071aa40a5d172a706a7ef11ce801e27b69879111128311a08eb17a6d1c465a861182a2680ecc46fe8440ca44df18362330f800ba882c30c40324058ab10a66f5b24d58284b6f1617033ac26587c9a723198ea1f4127db064d6b68438f17533176f9153f01f9d046c1033380c44329a8091a12712c9a229a919c96f2a371211041104af8d9170bd1450c847f030ae2adb4d1548240aee7a57abf2ea8486d1a82d1a5c64d59b1678e65c9b14142d99127ea608471884684b18767d07c6325f193731603228018afc34c6a33194f243c851a9b5192c6c4840f083ec686d18400f64b515bf5169c4842bf1908c34a3cd126a4d1e516319168fb186d5194aadeb9714930349e0d97a0827f233400c6b1ec60a7146d3194223f2f684772507da835102751a830a6b0aa1121227943c48144b052b174d7178ee73848c440b031d11800916caa32af083140812cb166f87787c7d25c361dd16ae42a41eb116e9f3a10623e8328057c3ac497ab01e20132e220c8b10282a423160b717754c61907243119a7cab830f9c5b1522cb29aa1f964c62cf1951ec608916687078eaaf690c696aa4c551a20a309ecc8b570662b0b1e0ad2a3067f07b33f1743012ae2c61c07b0eaaf4c8be8ea924dc0ea0e2394d0ac842a0189a554d8c102acc9166db1a20a825a9181be80c3c91bcd187791599e82a1a614a28422e327727d35669afa2965ac7c77187f480c507a4b67a828af72c810802478c50011173e22429517b4f1a1cab30aa79c3ab03e4236431570824c50324fa82b0e1163040042802e6c672f16b2e1297b141568291f14c3a89cb8f06ba4d08eb0a406971c825be33c04b7c547950eb1ab60d5907b604b15ff1923f18922b3065155c84bcc51ace9061bd19afc7a40aeeb47162548229c83444797b91a8de32b7205b92c364715afa461102607f159dab170f190a91774517abac6c20ffa1c282aa4d8369f0461341f1728cd835640baebe9feb05c84b0cd193a0f123c834bf179bf153b8305c84b5c84bb04b14e8b1a467ea17165c84b018315c84b90c7a2947953ce823ec67b91933e2c104734571800115122c630306c9b1522b1345a1f70d14574068386983c220e11a4ee8333d15a527bbe514c0675000724ae8298ef19e23006a760771362515772795c83310f160a883b8a30a1c849051a1f91333d170c8af5c84b0ae325c84bb8b17c347db6e79093065ea8e5c84b72316162825c84b5c84,0x931eb1a5a517ba71971b16050032c4930a5199144c82883942d45c8c3c06af77b154c2b164b186b633808d8afab155862c96c40fd17490afab628699150b8af532af8e10d86cde1ded125c2fb2eb0133187a4d6a24832c27d4c4f82ce83167167f4f150f158ff16b5106964146991846917c8682166a3440a49ccc3bf306c5070a60af9e07a0320d1bf17a523391230ac233569186c312ced131e3137dc4d604823c51961c6e99c82b07156751665cc83d22941282afa1c3af176ec12254790c02a62f0668c61956c657622514df3e5130fe4c63e47ab22a6ecaf1db1abe02a57f17b731325c7b46f181a0c637b1522cc7ae2505284c906a3bb0289231a2549f0320cc8292ad68100d17b61168b6db587159504d48c829a01b6d47bb36d39d0243151a93118c9b19ae2c5086331a8846531abaec6468329ba79a711645a2a00ab16ee82955171e0a3cd28050e1a50ec67485145517268ff1aabf28aeec38834f87bcbc781a07220719a071812f1692eabca0239a113a10de20aaf5bc4ac9a326e6c5bce821731501b1a72b18a871785d183771a8b483b96af5bd156668468d16cf90a7548608eb321eb12ee8376f1890e4fb1e1b6783f9a3164827b785170c915a47175be155b3175b4ab9fe69510729831457476a0e4cbef1615e4c78c230551914e80bf47e0b4c6ae314ad106af06846adb7222a8cb185bc465b4f28b2bc77ed90fe83458d81b71a22a6d8087148c7b4ae7a8f26d6d0de2186d876af77ab118c1ab7caf28d185103251d18c5c834e011c0629be0761dc45ab61e1591330d181dc2324a0990b196911363a7a59d16b1ec3aa0c2c131a17c7b547183571631484bfa7991228820848eac552512bf4c603432afe600768f83c01360c6a9096b2ecdae49f2651729d18a5d18a2915bd4e88c516422c4c8440c89166d6b1635160928359c663a10504033226b1adad962484ae2461e223c26c68e0f22f22a96e3c4aed8a57124e89915f19c851859ebf2e0b11e11845f175be130bb16363170c84c5763004d1a009181a71854c2a3247379af8c96c83a6b148ad1559182ab141bc842e815092729feeea047aaff169fef1b46110bad8772540188251117830a7b1f134948eb3517877180d5142c87e723155bf162ee9ea909f8e6d30feb81747904c23054cf8661b41630804795d47940d16040793a64d6d515cec4cc08be2948359e9f776b65c624b7eee7a0af158c3c2907ae0bc1d079b50824c8c6524d80e0c5c9a833221fc071604cb859a4d5325e0e629c4f1825e725164c7bd16413187c23382633b2e4cc304f1b91a13232c069ac469ab2316a8a4d5107078c292831529cd95ab18c54b1772c50bd1742eb04aeafbc811775156d42d9643f0d84d64412be46cb12b153313b3e822822310f13ce429940f2bd513c721261e8316aa9828c52,0x45a244aea38e8c55d1135c84b0d46b61c27513188782a6042a94ab15d0305c84bce5165b273377194f7155c84b5744f1902325c233767b5be0982c3043c461e2837a11a5901225c4a2dcafb92055c84b5c84bbb631bccb197ea33acb03a5146e903a4b17a3f133ad1606413c301f43c507151a59d079c8d803a30b3d06926826568e45a28302c60a0b10d4af8fd1861d15b9227992acb922263a7870883302ef24713bc6b1af1073fc8204c4c577161a8f82ef068c07f4b4c643c44a0e32827150a02f09033a36280ee2442463c9ace9651420a2f17517798c6c92243e467bc0244b4050323c7988287cef1d2c5b7ec69e41f107072d2a4114ca5e6275c84b5c84b32f15b4ec539c692a67aa50c3ba9195c84b52a325e60d20a33cf484171185c84b82279060799a0a744f1674b17ca882c081151622110be5880d2ee826d44d362b1918836c2288e8b0a4e2a842e8cb4afa168219022b731a89044bd8cd9e21b20b1a4567974882afa4b4f244a502f32231b8116c13130e208b7315532c9495180c11641e8470c8453f1761d16a57075c84b88f195c84b4447f7b4c5258c85c84b5c84baecf25c84b163155c84b1c0d99dac596e055284b70cb320a28017168e118807175c84b71eb15c84b533196d513c067d5b47b232f31740358283b5e308b26c7a279aa917308b1bc9196b89f41f146ec22a24c41cac471269ae2b26542a4d51898b174be79baa8276e154d68364316aeb0737a31937181fcd88ef0a3fab1a5113cd01f8f71603204a531a0e8b14571593f150c91771f17574133c4be5b4c34351921aee00f1991e4560c959f7181a9150d2b02824c28b03caa3039cac710c6149172ecb15671abb67d174310a919006818671224ac5cd11306ac4132c66ce735907d2a5155de6150c32936f110717c2315538f177b1748d1932e2f45882b5465513193f64294ac6cd2f0c9e507dd14231157d3167c2269a11815e84a651838ac66102f548247a11530ab10867fc091919112cec5a23e725611725eb17f1140a1131942a835175fec5532120e63060b1aab71560c705281b20b15a282a0a0280d3171ccd844473ab852aecb8a6478a19179eb19bc91a19a821f5075df193e4c443075aba84453155a91460ad89c88277a003fe69ca11a51a847f0ce0ff13b21187391358261b4eadb22738482158a7b1a8736d4507f0ad5687bb2c4d832bf7dec4a0d16a35189824d07c6250719a4e22c34763622a07e11bbe81a8a2332ac62c2b05be4d7a0731e0b1c5083920c529c9990cafae4322e063c7e7a6851a780595327a546f0914379c48122c7a114c97068470e330191699b1545a233ff011101da1c461cb1ab9316956b08a7159a71797eb17bf188ff1762d154fab07b04cb744d8bcc6c1b07127134e4465b4795bc2992e845060e8d0695a82a867195f8,0x11617d1532f1a96c8a7c24d33e994521383e823e518208832fb15ae2b171cc40bcb11103e1442403b0c6751877ec35e084c266f30c003f056b1f191d718b971730d1762ec660c178901465030054d1992822571a21ab160abd61033a4e73070832f51621516a3b0612e12a2a1b18d1a8287a23d139b4d185317af49e1bf166c0f04d4007e484812b1c8030114289e118bb24fbac60b9a2cae43020715b51192ed030f3165c84bc3cbf3f09aafb1269114c8078b6cd98e2b1c80994e878104c6864698ea4cc924d32314828c8c3a3d02e7396059a1865096d11be796d6360321f52a8472084992c583d1590a125ccd85742972ab07f27958aacbff16a91063071abba50a5516a8cdb9e0c6603195849f41682606d942e81996f05484d32ab187c781d51624a43c52b186463739163ff0a006c6181153a7130ba761e2281844d156af42eb787675a25196c2aa32a32a38d81442a3727a57a455c84b1711522a363e314b0f163d119bc02a7f0423fb1abfd157b3165282453012115193429baf0c6a4f150bc9f5c84b8a3176d43dae2b0584c80d916bcc844f6442611762c3301918caa222c8806c2aeac27b4dd18a2cbf9a08348c80145166f8f2191132327d918c6ac4847371426f19c0b1a6068765e325c84b51b07903161f91560d15a7707c967950eafb3f1771a006269e08d139c0c66007aa2b141dc1f5c84b866229da821fca31e3167407a4e88358a821042aa9e845c84d5c0ac3ac2424b15492ad590784f2927f0119311728232c9a1e50c7b8c514412c45c84b9da311ac12cc117254030005c006824c27977318a571a016a3185195c84b42a7309c82ab1175269254913c07141051a664920003250ea557a4868a65bbf175c84ba0317c92233e2336ccc63d2ce021185768425c245c84b30a3976233966821111365c845c84b6c24b9ba7bbb46c433183fedbb1eb85c84b0f91529cb15c84bc0a339227ebff139511550e5b9c3163ad152587e5c84b1ea11232ac48c7a2c499936d8a7caf78c247aa79666b150d167a07b5c84bb12af42116c0a4d4130760117965152c31ab08c44051643116ab6051e2c310d1a5a89f532326a316a76827e6823d3175c84b9323949f1723c331a1168deb19a00790f1697a672dd1561c4b2a082a528405d193ef19941077407b4448452517bba3d8927a572b608caf405151ac809ba1190e2ac968243117b8716b924b412c8c2ec68383d4b44c1ac523baafc56795e2a314f1742a63a9f1a93b17a2a1f55118104772fb16ba88194ef0aa91a5c84b5c84b1ca7e5c84b5bb1965cb1010118a21587c833ab17b99158d82b41717c9e448eedb40d1783316b664d5682b96e1e85b160ace36c2af1b6b308aff65d0782905c30b677ac6adac63c440528297da800d51a9a718a341157409a6318670d9c86842eea34c4d0,0x391244954ac18c232244450cb1a90c441ec474d1856cb0c7cb142208b21192908221eb3ca0225b87b7c31a66affa2b1948116adabe91870bbb15c062473b0ac64c62464c0d47b9e2331ea613f08f34ab1324e8523173b91a3a622a1e6978cbc22682a1d18588bd9a3150342a5bd1621b0391a84736d8bd6c678e1d8d317842696831494f051728232b15892338bab110e82ce483b99140951a6027d69482b1eb11fd061e08f66b1acb4b10c5150bc0b2b7179cc823223250714822b3035173e3153089aafa270ea0b55821706606d46d8e2823e5158f2731cc830403956282376fdcee2806692b5d135331a9d03016f183ee4dc43068c4be2c8f1ac263cecb6be1180aeb10006100c610189f0c83004cc6828f1ae4315742504d180331453283772213a630236849a6821569f422b0679167a6d272073a2aff7b4af6beac876c42c51870d183a31682c71992750644da8cff59c841cac8897164309a50c73917182864f9cc3278e6996b151631723718773166102aafb186ed139ff069ed1a595155c1180d4c3cee732fc2a30517bea82bb4c55de7a82699993195951791224b72bf6cd14844b156cc5416c63425dcbcac0d513106736c315536db83717ce2b677eee1101bc06b0aead19ecb1772c620e830bb19469163b919808a918cbebb483cab15044b19e516b951568518b2ebe52513104103d231323159671616884cee8486eb19125803a1fa711763adebfd19886332ce7c9191926a469d11a2f2c6b8d177484d060c4912ad92f06c3e798c87b0a631b0a13caa836c4af840af91e121102916d1a3250104c835691734713b33152d0c652a7391882bcc799ed1589222324cf1e076c667999303b2ec659e94863168a6b19a44da1e73a16b1a5004930b18331ac4d17cf2ffcc479a1c24144799c0f1ae42314d05b92010725eb231572edf79116bacbc8f263172b164a113d242bba58430786991658ef8bb71960c1ac11160767b6e48233a24aa481c4c8068316275164ca848ea290c8317a475bcc82afb1a5be8299cf1a5cc6afab38407c03a314d0b358684848c5980db8ea4328cb16cc1f3591638ab1287198c0834a0b093232037189a01e1e227729140ac822cf166ea4d0431a0af190e2d024b1690d13a21171d882772c7c831a1cd067f0280bc82bae8f6788f98d18730720184c5ca3e302c4686c47eaee064605881f4651a8a7186824fc311937a8221e7ead1183a632c4d1a81f09b966920f19ab2243e282cc717c1034070b21141b8c40e783171b4b133b1922061b2ebd65c7d4dec607601c231996e220ba7290b1a42e828dd14862464644895d01381193487a006f6070ee7dc24afa9f72ac609032b8ec678cbf2fb1903b1410d180e7184ae9f6e6b0a4efc50ac0616d1846b1a1c315851808adb40ac66c311c12225482a7fc4d82a24c2,0x5e825c84b9e1198ea0d208b07f0337029f5271662d177b8af4e03269cf0c8318cd11a4f11522a220d31a4e03335d1777e79ce43324b14844c657a440a01b1467aaaa840ea3c5c84b2b314592f15be29538c5845156aa83a2a27a4718154799c70978f17916f0a0ec40b30997caf060b1bfb155c84b1c211a1cb10cb160364ca3516044bf2b7165c84b966c5b9682ab6013d02a30a32b3ef0a4cd8cb4b0a53178df17a851859c790bc33a5d070c8231261b3224cafa22c5d168041254082c946503906c967bc46d6716127a0289c918ceb179ab1303682a4676a70799e411c7319ba6724d0843d2363d224b96c5c844d099168928302e8322a26c967c1bf1a859165901fc547057628388ee038d8236af0e0c3518d864a7b05501588247951910ec4a111442ec5c803357ce8aba7d0eab19da301d68289230291189a0b31a8c670ea33a4b63c306302d8b0473967172d0c4038f191513b5e33575188d9191047b2ef177c6adc64b186f18a544db15153a10a0560b8ae82c500e303043767639118922af96d16bab057c2824220d64a82c0a2a5961b594847c6c50e6b02ad1786d1634283a0c845242f1ccafb36d13a4312af156328301432aecc6562841262f2c2af8d916be1163f0ac37b17c224d16e624c9166ced177a9f08d1a6df19b5e7e37c1178c464d0c8c3a4c25433006b126a2a6ecb83e316772c8a20c50e7194c8dc04cb478318206a31c0bf9e679346be5c11378117a4e0ca5073592c6cd0bcb62736cd17afa45cb4c477718afb1546ec6864842ac635c82aaeaf2c331a23e82c7716c93185d5180e24c22e8493a82a647a22a4220b16c4e829bab3520844ef19848b386ec6bfcb126b146d4260f718abaf47ae82accbe6fe6145230a56af280946ff1516e8227f1896cc6684b0a50ef3d07663c848f483bc4f082c2a6ccb13d64d4c88b1d706590420c0321c0b1533159f4af24a2a14430abb186d4bd7fd1624a461caf21f22acd2d948718ace2d1f51ac2f1594cd11567eb0115526bf4dd17280a3b5c9f25092abb1a8ef0165d1528ab107316591135867b4b4af308afafa363f624c7f19c547ab13151b67a0927ab9a7a8c0c63a64bb5caf69919a9719816c44e62cad682c0b1320ac8b13185027a848b0c647966d15c1a639dab09e3167607364917bdb17c42c51a07037c9260ca54011741f15890484c4e8c35156d44066cc47363e7631a5060b8eb19540b1373150d516c9a30c50ee2b244538c41d117a4d167443384483c50b18cad1ae916b8b18b724c4d71a208821851566c824e9158430b8210772117b604ebccf2600839d0500d91750ec40fe2296714b8ac41444d5be2a1171698ec6b0483c327d2ba827082a35673213185689ac0a779f7164de2aa0c7f62a73a90837147d5a71a2b229b1282934c61ce830c02b9d0471ad1a5028,0x4d40b18718d20e0c651210645161a8cf7a0305c84b37cb22fc054a633ceeaf83d1606116015175c84bb57178267f4222a88916af07a5c84bc3b199e2835c84b5c84b93e235a8249e404480154687fca011c9230610795589f7f0242fa325c84b1ca7b6f4b177319126b1391153627b748616030659ec5aa51791e50740b1a0abcbdc69584827f03159279390c616e8413e403a60543cbf12918bd9167a24d5c84b0642843adb50d15bbf18a8b15876125c84b2949f59029b19180ac69328607b4f06d7135c84b5c84b133153f309adaee57717795180ac845c84b5c84b66d1359f160550da3ab130828249183baf05c0285c84b58aaf5c84b0e30188b1816683caa1b5c84bcb4c53a0ed7af17456b1a9484afa4c7807e62f035587936e633624c1a901c4aaf8e107b931592ea9b13144a7186fd0b9e42acdeafa9cd570d16754705904ca4e7b1e26e1c1188664b90d1607f1ac08a2be03259482328c4b2a1f70cb011f18c66db6f117312b1363157f4b2388825cb142831941f130187b6251a2ee798c428ae403656966989f4a0c689317ce45192516c50582fa3371905c9a429aa3032517ca0705ff108d2824f31aa56c3a3e2308472990af114bda310616e7b82d162ce22474339e444a1c4a8c88410115497163f07b3127db487bc28f2ccb17afa837487e4fac680ed113ebe53cd51dd1a2eef062319bca9f29a2a6ed12afac352a7f232c482282a542850117ba6704c5017fd15b951882c2fb1e5c48cb370c824e71932e326c717b20b132a0927d1523c841101eb12c48e70d3c44f0e5169ea82cc65c433197c68406117574c43f7160e8722e0738d51765c9a1cd1969516c7c82bbd17c81192ef1993e73c3f166c4c4549165c84b25d151cab11042870718ae424bc30614cf04e43095c096b88278c4c79a4d7e46125d167f11a59d02801171fd186d410490f76b71a74cb123c68b2b150bc6256119bc50508ec44ced063119c7c27c5076178c561c7aaed033a0825251943c429a833aff14a511741684044bc430235c84b44482593065c84b5c84b3a44c920c6a044c5c84b2a2725c84b3b119aea8246ef21b3079aa3194d037ccf2c42afbd5176231637cbf4c4c626a4420ac41f4b13d3194dc3390d159e6828cacf6bef5c9a29458c73b91578433054d021ec350f1a0b71606514c102b9de81b1313820694ee810e2bd626c41ed0509710cb91876e5244a7993cff49e320bc794a9172c51942a2a5c84b70cd9c9eb35c84b1264c9ccc652a7b8bcb15c84b5c84b5c84b8d2874231459cafba7168041179483a6e823c51648c793b9139551577a3399e83654325c84b1c077adb184e431b92300e8c75c84b5c84bb11198f033bd8bf9e2285c84b55819a711892b1774318b36d2674575c84b649155243190e406e7171bb172bb07a98bdb5d15922842,0x7483229c7a3471619872208c58e2b0638db1fc9f96e275be32b1eaf697151e912605177085d2ee7ab62656027222a30538af54117a21142211abfa310ad07bb713a0e66ae51351ab1bfedbb922f7a282cbc75914306fd0c21eee6aa77a3627412b1a407b456763d2506f907b2039522c51044f1d2d82e1158227b8c5155c84b696827726b862125c84bc85160a6afc0a7bcb6b1af2c653718a9d0c2111867103018b1b271760c285fe83a4cb1cd0b05763216f1697f195c84b33a3e5c84b5c84b5b91a7fc2a7c4325c84b27a12b491a3d117502f17a2b134a845c84b7491a72e29aecc45c84b28cb2497155c84b5c84b23c6e0868484517497145c84b5c84b82083612845c84b25890b4eb15c84b744323622861c285c84b60d17588235903292e834f5083f0c45689f07f162866363d17a0f19ceb18afa1802e7e8c91571e826cc309143a8f4823b057aed0757627c871a616d270d17423159aa323871523e7e16e33711188464d38c3f236a9bd484cee22934b132a4e5ca3f71114b0e7b3a71797ac6c711722b17ab640660d879b1728314a16c683260018c560c2e92e770002fac3170bc2b0970ba20827444dbbac625eb74bade60c2391e28cb4822a26c77879b94263763dcd0c559d1357b1a95c734acdf922ad144284b428a56730e6c7b1e2e3ed16c404d000837b4c6acd1804c1a528045c07aa2a281dd150ab19111190ea8f46eb33b883666c687629876c53ac2a0b2795a805c63177c44daf072acd1952828c0646bd715a1717ab2284c50c9ec87b1032602b16b716699138eb1632e33094c5172c623d1718ab1114a2a36335b2323d03334715c9a235c84b6784f50316159126e8fb0af17c926f4542a93c7799cb1cd317a94cf6bf07a368437b186ce2ac64c55c84b588b55c84b7731543c4561c236987a5c84b7f318844c33342a9931a8287d5c84b56cb151460c067b5c84bb751568424bc7173211753514a5ca976f1628205c807a992af5c84bbfd16cf8ff96d196d4735c84b2ce285c84b4faaf22b15c327303319837185c84b7b918a4e8f5c84b2eec625c4d50f195c84ba1c7654682948f06e7185c84b0804daec7c7811473e114cad25c84b6511493eaf8f04d1b70755034b5e285c84b0c079a38bf5c84bb0b163feff5b1162cec32a3158eb1a95d1805c301e0b343d160e6995c84bbbabdbc114a9118c064a510849a0c4b73143789fa16791631297ab158b1a690af65caf06083b9913aaa836231578031c12282b247984d138879c96b11bf1815519a90f1b004b5229fb4ed912f1714f19a90c71900660e8241e6d179060ac79687060d232836826468479b014223eaf3022cb19b5cc4754b1b071396c7b4164d4f116b12b029d1903717745169c9164b49f51b0c04082a8a247827fc063314319bba3e956c572f13778b12511a098,0x820e6c46371a6784dafa2892f1ab1eb6aa71638c4d5c84b5c84b5c84b08e825c84b5c84b914085c84b6c105b1f18231165c84b5c84b5c84b7eb030567b0d4c4b72bc05c7d23d1a5c84b594c41103f7c4736590141f07c3b1391a6537283574c556829a76846cc325c84b17c4da6317100d89ec84822762dc223f64868f16c0631c0f160bd18bd6d896cd15c84b430425e6228927b1e2329d0b78921b2fb175c84b5c84b05f1810519ab63cac504a9d1719b17455168f0321b67624a4730b17a5c730e0b01f47ba0e28b6033a37175cb196ed1ab9a30b944237a9f29f1659c7418a2acd04264a79a941f0ea2a95ce82e316bb630be4df610826668261116c42c6aec904aeb0272dfb2f14c5115892b1ba67c5c84b486de6d41b1be333087b4220722a28c921f954b128cf15c84b95233964091e69d1451a530117a4b06190978c28190299a0c583482bff145badb754767eb188d084c5f0e11715be71711a4d93209c3cbcca11208316006831e31a116735bd149a0c3aa01a9141f0e62b64a338c91696d1587631c10c6808af18b15032bd90cb11880593eb15c84bb9a117ca735c84b5c84b1cc6cc54825c84b1f482c507eb5d19664603f0291a6845c84b322304bea3b9a61324842a0b10e915555190e11893916bbb18a56c693682cbb1508e80087172b6844c4beb67167cd055d0ac422245c84b6671a5c84b5c84bafa311f517afa508cb0c60116b628440c5da1e6346915cef16a4cc7503063e91a610d842a198ae633ee323ea830f83133e4f5b4b30e20d6d663144231044d5be28502c45104b714b1922834e4815e623114ccaeb17862482fd16175147f0505c84c0acb1657195583359c7b4b48208c30af2c45c84bc9e113a62f4d7163f611684305c84bac316823161f316c0a308c44f40112906820864d0e65b71a0337d19309159da8425c30a571638118670eece430143180f410574145c84b4dac6a1c306be8482d1508114077195c84b5c84bc37178b117812be25c7658a7512612bba43350123d24683e841b2af3ee29590319031a5c84b5c84b5c84b5c84b46412af2afbd716cf517c80280ccb13d0838ca8215d170005a3dadbb5918105164e061afb13b9118033123f91aa90c5bfa4dc121b0560044f1a9d1145551ab8a820a08356b1a4b4349640f15e6db4d16282295c84b57423c9b175c84b3e2b17be3b0a6b1c8061971176d43f5bf180b518926c6114235c84b5c9176ba09236b142a3348479aa0aa11114604c68e70f8ea465c84b341195c84b3e40dc1a8499e8493a830d4b1115151e27ac08cd1e9163e229698b17b5065c84b5c84bbd68225cc3761035e6be7a7017223f4d67a5903372032ab8804c4b15c84b876545c84bc3715c20db96447912af29515739154e7171091a2eeb1a3a831e0db6d91807e1391519524f029a84,0xbb944da1c7b6591977e4d11909a0f136e714a0ac5c5a833f71520e8262ef14506d538d8454820eabd1bc834b513a3a8459050292ffa3aa9ae315198ff376c6ab719c08b08922f0c429636ce3e829966b075482bfac695c3f9a880a90b0940c6aecdc0a51696cbe685159c87a8ed1693317cb481651183d27e7721eb6000a571501915992c7b2f132745c1a26d80432652606fcd11103caa0b6afa2f74918a767fb50c653d103fb18bdc73914c403a699a0ee60c30b1b151a0b11b6802fd13b0011b071705d1a12315ca8f2bce8404c82828c69cef0a94e8c7d13ace033e4051231893e0522a2444ea4456ee7731450e178af073ac00c7c7b710c56d40e39d17714afa56f24dd161f24d2dd13044725b2afadd1888f182ac84812c63631aa464d9a02990d178483020b053b91760ec6afd190ac66ace165928205082b066f0eb152c4d81e2336bb150d31461d178624460914a4e235d5170323e2fc4c24a9263adf0471a44c2a7c31789312ce4158eabfb72233d2802b31ac10b19ecc64dc2a6d5162a917923079daaf5cd0619119c2ec5c4716538797728222ac304cae1222a19a7997ac519028763170e21f432c3bcd16c3872c09152eeb23e5140a61f710af0d83245b146ecc68a717b48321a28400c12967154e9188231a1140dba7120e0c86823f04d118d7188071a86716468842a28361c7b0defdb5e829951742a2d19e637127383119865170aab122c84b1a2ac26af00a7b8227ebf5031843f8207ba8b139ab18401135c84b1ecf05831a57514b8eb1092b1b1f11a1c112f2b16f8c645063b068326d1682ca95c84b77a079e11a7491424ab1c8411a64995c84b5a615bbab70e6af2a719c08c6abb079927891518ada3fbc30742f1743029144322c6b170cf21b2c46eb1865d138762fa55153e48984914bd6b12e11724a4817515ad6830f91481d167de838d436aa117875179c8808851900a7faba73586b16d63224a290ef1acb51a8771778c134af1823cb1c34c4c0684286357291510af49122991317828b14e64fa50af89316c0b178c0814dd1558f077c315afa01c124ccab1712e3329433b6010bdc0301884412af5767b000c965e4dc9ce14af069cf07be4720e917483197d4df5867f4527b50ab15c84b62c2bba627a50a8a2abbc571870717459175c84b3d07a3f0af8df186851460c2245e8278d13000284cb17c06238c4bdb7083b9317556846782a33f1a25f1558e7365082a3622af51938083cec84b5edfb051823c225881bccf18a90ee1707f9a11aae44dab2292064d930c68eb15ca9178f233b10834aec44824f70d156bab1a9469428c61ac82596279d08428317c30241e222778825a913c0ac38df15ca8762eb16ca907823154202aa7115162c62bb181ca76372735546c3f62941516aa0825c84baa2dfa74827a0c48771a02,0x9f196c4b1ada588e4db0d833c84c682c22ae516b647a110407b4f14b43291f1ac802457ec699c797e45b5324c63e44c56820a0c3174c58ea4228c82a98b11d6c599b172ec8424a1332669a60e61584cadcc653f1a5c62a11401ca8c4174244b713a24af6ec1b820c83344d1f0de40c4d0761f3ea825eb1608ec661cc3090b11043c60c1b1aa6997f176e51870b17adb0389a154f869390b10a623076c15c84bbfa33400c34a0c50eb1691a634df1580118424650324c25c073289255082566bf7a3179e5121a07a5c84b5c84b0111a8c8c37a0b1b77166ba1384632af4df65918caa7c7c232ae4295d04cc926b539065c84b8c0f679acf4588318cb6c30be86eaf5c0c61a8820e8c6b4e61c08cb07e4d249178d4427f2827f11837a4d5eed110e798c8c697e830af15c0518884bcc4d184c316b686911a2abe4247f4829a1030e1131b6825c84b5c84b4544d5c84bb80795c84b0007a66aa96f87b174287b90761c33b1ea65b832a70b1b2ecac42825c84b5c84bbcc732dd1a61ef160b190611395cf881c33597128b1186831551240ace215582b5c84b02f03076f99cc3305b1a17281172835c84b380af61d1abc9160e6c5c7a8d084825c84b5c84b40c30a9f17b2c2a13f162c8ad85f1621e834af15c32b16d46a92e82852834e9172823352b156aa7b49f1582678ac469ca01b1cf19b8a1f78c12890158c877b7229aed1958f1519c2f25c220ba25162c48483483c302c2b12c8b06ff192824d99eafc104d4e04d64ab15c84b06068ab81584f160e0825c84b5c84b9662937718be04d5c84babc73936b7c802911717bc6835c84b9e51444abf52a83c42b009514bbab0b1283914825c84b826325b2337be42b4e7e8911680083828d81dd143a62a5631a96e045c84b2e0c637ac546d1657e7955c726beaf4f5184e08204ca5936b07c316248303e2848f1157f0299a11258d1a32c830e87a2931a7291aa1118740736d61da871abd67957492ca0c372e055281f0ae82a56b11d515517160311798eb142a267ad193f6473d2767f5189642a4a106bba478a68277682510336fa4d9e41e0b1167a3159a0820ef1395edf280bf816af30c826c684076bd43c12c804fb047225c31a0eaf2a318c4c821448218b175de84ae31a22cf085b185c8050ea3fc3473682297f22bbd4824b71697cbf7c7140eb1a4df16a10afbe07276084b2b19bb04cbb5060a11a6d407c0a2854400940845e11a4131a7a4c56c31395cd0061128851829f1779a83b06678f284a02c697f1804317c28849123686715c81169e22371d060181f8f116a9e5d07c9f45d171cc722b24d8262c95679942d26cd1337a321fcb1072617d71890ebfa20a317433404ff2ce32cf8cf7e6791b679a4d171142736e6551116ab623212924e63264b150c914042df7de823d115c9115178af96e1,0x73a8cfa702815069f7367a86ec4589152067a41ec861cb163116c34848bf1871cd8c7c33029152ac65077122b51ab924c68444a450696ac64a316702b005c6c4f71a778c448433046df0451a87c7b7e51718cb10c033ca1155b81181c3287719912323cb1662c398c43e2a11744b1ac266702d17c1f17c387a050346ec649e27cb2030847178e68cc4c79be31611edbb26b02dc8306afd2951a9c919c0715a0c7b63c122ef161dc2aa91033a60479a84aec8222a2ac60f1686af9069f0e6b34d5170e6370ba4da3601530791141f19ab115882452323e91626b1a6e87976f1729aa45481f7291661caf922b695507c3eb1432ac03433aecf8ca915aecb1ba62f22cf196e0d282a32a6799f4c55bc50aa08458c82a4c7aa29165107b329197e4327f1177a0231f4c6a03154b4794e6354311a39caf4508491514189136651a2c4c560e8442ca3c28b1c0a8432665c2115b1e2f755160ac7a0acc32fa845eb1974ad2830dc0a112748c56fe5e9a04d3727bada709da1fae25ebd7175062a576c3a30d937a7950e12caa2353116323174dd19c411542cdc29b15b1a4d46516c108259d17061152e314a2b125bb1a7deb1980ff3e43e77b16362846791883d17cc71ab007279910c091413e4f6848426b15b5f180cf18c064578e845902f79884a0e74ca01a42517bba46913142fb1a464463291ab2055a16844c518096f2acd1a961172b24836213836a38a316309130322a4af16502d80591aa10b1412c3a4e2782d177f07e363160fc8377ec6147146fb15a30d652081b011677a4d1987ab031a714c350a927c680ab60e3b0b19e401c7d150ba2c2231678e6d90e3fb2a4cce4825c012932c68391955003483163d2830d4c515f143c11aa64c6562c6320816c21a9e7172bad015e8300c846951746eb1236ac9d115060c675117500b19da239551851112416af000b15881ec3915956f1a6f034162618cb40b6334db1552a7a412839e0b1c1d1a2b2420ff157e51a80680011169aa23baad233c321a7172591aa66afbb68430882c8515bb4829308211b1681318106c62821fadf068484eb006891e058c882286739bb1708c4e927067481345a4c32e839645594c79bdc07ab60c30a34bfa101bd143511abb4c49931860cc6772422d0120d2841e913221174e432b721f5a81f0550a0863255a9c1d2b07ca7b9cc7393e325e2834dc32423186ed17a0f179eb188d8822ecc64c519c9516ac4f139cc41108f9144e53cf8516235e29fadab10982a140af07e2a22b18c0a2397a6f431158767ac923125f1416c1305e7f8e5199e2229644052518aa48485aa4c5033a4117a2c4870cc5ca0afce42c333155a518c924c89056678735c82f97c7959eb108e8443031abac8a8c7b044af2fca26d4232b315540c465cc6c86b150abe77a3463e121b67b0c4243fca34,0xabc7ba2b1596f1359075070f1b2a2929033bc67b14429458b2636fa8491861c70b662a5bc2a741160003096e0155b1379b158d43b7b113a11136d48f747173625ab2518a58f10ae393b64d822c4cef15b62c668517cee690ff192e70672e2aa4ebe72e1f8309091918574c6630d15484cb151611066880b16d51470f171b2f235c4505cb12f683c062db051a81c80823189e422af0c49a0d804c2eb491745a29482]
def a3rows (i : Nat) : Nat := (if i<16 then a3rowsb0 else a3rowsb16)[i % 16]?.getD 0
def a3layer : Layer := (11943,fun i => let v := packedAt a3rows (i*20) 20; let p := a2layer.2 (v/512); let v := packedAt a3codes (v % 512*12) 12; let op := v % 1024; let a := op % 16; let b := op/16 % 16; let mask := if v.testBit 10 then p.2 ^^^ (1 <<< a) else p.2; let mask := if v.testBit 11 && a != b then mask ^^^ (1 <<< b) else mask; (p.1+(op <<< 30),mask+(1 <<< 12)))
def a4shiftb0 : Array Nat := #[0x700010800030050f60f600100800002c01500200000100306000803801800001600101300000500601600600e12700f0680200020000d80160030d903000100b00702b00006e04d00901202200516300f16001f00102505808006000f00005003513a09e00400000000006800100500000623900419200000900001201200000100000d0030000070720db00501200c09900400c00113600001202f00601b01e01700600201100200d00006800100b00500000702000500300f0030000a200a00101300419500c03300600200700003b00305900105300009301400300c0050000000010131990b102c05a0000c800f13700922008600000600201a02b00600a00101700803b00500200505600000c02a00100500200500100000101c0000ea01600000000a0260000000ba00300001002804700700c00500004000000000d02f0080380070a000000400600b01700000105a00900100200000a01100b04c02700c02700401624b02600403805100300001b00000000100011600805f01d00101b00202b02300c04f00000700600d00300102400000000c02a00000100301e00000301500000800000300500000000301400400402500002101c02b0090000280040a000000a00600903e00901505701500501000200e02101405e00300100200c0100000000a804d1f702400200000200a00100001b00400000400f00000002c00100001301a00f00006300000e00f02a00002500003200000200800000500000802100000001000000301a01700008400600700604b00200100602b00601e00001700019200901600601f00b00f04300000000602900104b00502400d01500000000400900001600400801803d01f00000200006600801100800001700006200000000501300f00001103300201401210700300100400000500000800701500d00009d00e04b04300300100200000501d00e01900700100a0000050000000cc00600003702400100100002e00001202901d00c00500200000011a00100000400001f00900702700500c00f00204f00100600c00300401f00a00700103e02901403700400000200100000c01400c00a00003901400506906b00501d04900000000601600200101700005a00000801a02f00300200106901000400400409103800207207f01302500000f05604b00200900000900000200004a00500201f00203300a00000100f0010040fa00800000000104000c00c01800000000000701500000300904700700000500603900001200000901700000201b00801300600500100100103a0000a800a04300002200000000e00402600000102800500701100600000d00100002e00003b00900001f04800600300500000500003804601e00701400302905101a00000000000400000e00000600200401000008000001204400e,0x651700500104e1162a20c602406067601000b00101d0940ec19802817e01a02703100000079515802a00c00400156605e00b1c100304000900145a00800100c00000f3ba00000204c1490031cc0280000000000022ad4a735106300400108e00903e0c90ef18400100a04800d04000400702500c05019301953f46301e00204301400500902a0020386e01c607c00000048d0b002e01000808c0b107b00400901101202e0910200190090530202b803802200215200006200000801060200501406c09800109d14676400000000c47e0210020150010020d10810050580c202300002a20b0364d300c1cf03d0210850020021e026e14501736411514e0ec2db03700500000100200400600603600000701300007e08007c0260b000b05614301100e00000a00000107905613301209409500f0040000071ad0160e51f304e07a0680002da18a0240021490d800364600013500c09801401401910800b00003107901a1e001600000d00100000a00000202f33904402201d07b00401800300000201c00206a06401100928700003406300900b0040aa0c400210744600500005e0060e501d29100400100004400e00200e08200000200900702407a0350171c600a00703c0000040cf20c00800000302c00b0030c64d100100000b00402f23c01e00002502500502101600400207500500001400046505a0000020980460ba0e800000002401302b00600d06800000000500005200700700000000500004922d03b08b0500750270080940094820770120111211e000000f0e801208c00000200705202501700a0cb01100400403a00600036404c0740090023da00f00002500d0050190cf00101500100108300001700000e0090060220191d417208f1c600100725a00404400034603204000000006400100201704900003000400f02d00400600100700b00200d00200a00d04700600142b0500000040a004900100f00000300b0000540000420070041300010070ae03a04100600300200d02200602602100102200002403100402300200101800a00200a00600b00200902c00101d00501a07644b00001c0000000110020000000070012bd00534203800601100403e15f0000100010030b80e100500203700000900500b02602500009a04c00200c00b00217d0150000030080930023c801a06301e00208a0050030051e301a00e0780000f200639d01000a13b00801100c0120640150e207e00000200105f01000c31d14801e00409804600d02600006b00123c0070c301708e06f01406b08100000a00300b04a04700900200e01a01c00000500301800900d00b0230ba01400001616d0a900100104a03200000000000200100d02101a03202805706901500000200000000600501700123b00f00200001900000002c0060040010270ea0130010000,0xe3e0003e60d3037012001008007de71983e700a1a20340014220a202201166700f0010060010040070070a405800000100101166706801504000112d0000b203700303607a14339b00c46d04803e0004760130be09c00500070c0220061f40090025d809001903147a00005600201300105c00219701106001600400701f00701600a00010001d4990283ee00351904d0040280080110ac04505600306600003200446902318930116900205b00009200905900800100201906e7ce32f05e00301]
def a4shift (i : Nat) : Nat := a4shiftb0[i % 16]?.getD 0
def a4idx : Index := fun x => let v := x*(x+701)%618970019642690137449562111; let h := v ^^^ (v >>> 37); let j := (h/1494+packedAt a4shift ((h % 1494)*12) 12)%4580; some j
def a4book0 : Array Nat := #[0x1,0x107b068d8ff0307da3b01dd8707402fe1b06e3e000603efc6f3702d024c7803507804202e,0x11d684cb3726b02c8a101607806b06891b9411a1c0327831b81a11a405f37042824878478,0x1876341b37e1bd1b2780ef06883a13a42440122412417633982484227693902d478442878,0x102ee1b71b40117803b878]
def a4book (i : Nat) : Nat := a4book0[i % 8]?.getD 1
def a4ranksb0 : Array Nat := #[0xbefbeeb6cb2cae9a279e69a69a69a69a69249238e28a28a186186181f7df7df79e79e75d75c71c6db6db69a69a6586185d75d659659659655555551451245145145145041041041041041040f3cf38e38e34d34d34d34d30c30c2cb2cb2892492082071c71860c30c1040000]
def a4ranks (i : Nat) : Nat := a4ranksb0[i % 16]?.getD 0
def a4tbitsb0 : Array Nat := #[0x10000000000000000002000000000000180000000000000000000000000000020000008010000000200100000000000000000002000000000000000000000000000000000000000000000000000000000000000000040800000000000000000000000080000000000000000040000000000000000000000000000000800000000000000000000000000000000040000000000020000000000000000000000000000000000200000000000000000000000000000000000200000000000000000000001000000000000000000000100000000000000000000000000000000100000000000000000000000000000800000000000000100000000000000000040000000000000000000000000008000000000000000000000000000000000000000000000000001000000000000000000000000000000200000000000000000000000001400000000010000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000100000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000080000000000000000000000000000040000000000001000000000000000000200000000000000000000000040000000000000000000008000000000000009000004000000000000000000400400000000000000000040000000000000000]
def a4tbits (i : Nat) : Nat := a4tbitsb0[i % 16]?.getD 0
def a4expanded (i : Nat) := packedAt a4tbits i 1==1
def a4rank (i : Nat) := packedAt a4ranks (i/32*6) 6 + pc2303 (packedAt a4tbits (i/32*32) (i % 32))
def a4gidb0 : Array Nat := #[0x6cb68b4da49a4d16a365c28a6ca31b713491]
def a4gid (i : Nat) : Nat := a4gidb0[i % 16]?.getD 0
def a4pickb0 : Array Nat := #[0x200622000801009844080000001100000220030600000600042108012000100800000688801000100600012000000a4300080000060010068201ac0000c100000900000a808080000041142840004600000041000007000002000007000950000011010041405102000009088205000024000011000006100300000011304200000011042090000901000421000490]
def a4pick (i : Nat) : Nat := a4pickb0[i % 16]?.getD 0
def a4hints : Hints := fun i => let g := packedAt a4gid ((a4rank i)*3) 3; selectedRules 12 24 (a4book g) (packedAt a4pick ((a4rank i)*24) 24)
def a4codesb0 : Array Nat := #[0xeccebbeaae99e88e77e55e44e33e22dcbdcadc5dc4dc3dc2dc1dc0dbcdb9dacd9cd9bd9ad95d93d92d8cd8bd8ad89d85d84d83d82d81d7cd79d6cd6bd6ad65d64d63d5cd5bd53d52d4cd42d3cd2cd1cd0cccbccacc9cc5cbccbacb9cb4cb3cacca9ca4c9cc9bc9ac8cc8bc7bc7a9c59c39c29c19b59b19ac99c99b99599499399298c98798598498398296c96b96596496395c95495395294c93291c8cb8ca8bc8b98b38ac8a589c89b89a87c85c84c80c5ca5c95c15c05bc5b95a758c58b58a58958758558458358257c57b57a57957357255c55b54c53c52c51c50c4cb4ca4c94c54c34c14c04bc4b24ac4ab4a549b4952cc2bb2aa2992552332221c71c51c41c31c21c11c01b41ac1a71a51a41a31a219518c18918718518418318217b17517417317215c15415315214314213211c0ca0c50c30c20b30ab0a50a30a209509305b053052032]
def a4codes (i : Nat) : Nat := a4codesb0[i % 16]?.getD 0
def a4rowsb0 : Array Nat := #[0xbb9c81ee80168441b665d4d51af2665a511a4e820ec1d951d3510afd686df5ced0d33b92a6570b500f68dd91d5b7f5354d8d47ca355f4ec197cb666a0b56b8964a9fc270eb54292d62d56e90c4b547c93e98da37dde750add90b2ab446dd3b4352aa27d67d3e597d0d47299ceb11700641ed472d9025294d535a5ebad62e479196b55075a02d1888000958aea0594834b9ab4e1546691b6c174f81889b48183c565f1d27f8c516c34657da91ce23a229c97a676543a707e96cd636d4229e58d4ed55f605a32ca24a63508d984a16b517fb89b0bb50b47ba5446e4e762c9996960b3a472993073ad984df54d26d4a36e88a9fb1aaf3528f6d5aac178c8dd4579d3457ed4105b465a51053967e033d30c7f5125d5984c23ebd2d70ad30e0aad9980b48bd5d43bea8ee95c94eca68d3fa50fa6647429d0be354c73d43cb0e4675d45bcee986cae8928ad0e0d059f674a59a6108afa032a9b956f6e6a1f9695d6cc98f60817006a3bb782eee20bc40075075fd34355669e9d400b970984484c2eecb39b09d2f0580dd4000255d39d314134c8677b6442a63f67b5349ee39c4575a7268a9d45ebf3e948a1069f4da7f2f588b29802d807e242783790c7c7de35a339d3619a21b4e312292ace574716086d69a312466fc160c6a4b428748fb52d20a54355eea5cd3b2a6d48d975127b548acd4a7a74e20cd63b0f4648fd58e7350555d638fb5ce3ed3490125ce6c569fce1d80d497ca1ec13b17a8120f55591f5f51b8cd36008fe0a6d43045c40009556c7580c67143804e671899667509a9c553a351ace95847969d4cd511b61e80ed49bd28ce228f889b512849f1633504059651d1e42927b8ec1288c1597dc68d770d5b0ca06765a3869b4e154b06c1b2d972d90687067ced7aec926770b06b3d21c984d903f59b67a33b9761917d4b0a1d43e0d4a169e8bd238684a8c1d7a32e1d10b32a72c64cc000952307625015c2d6ec0000686b8f4cb46384f0356113ca81f756914c7627b50639d41af750f6cd55fa1642d2d577b6ec4438f137ed4ba2d3a50972746beac85646cdc143561cf8ba9813751ca603629dc6a2fc3b64536596a31bb5f5272d9a2a61e039c0438064f844d2a8cd1056ae57c754227810e0752e95c50abf2ee916f09a688be5d9505b56081bb7dc2882d4cb95b8ce374a00b77546bd4d49fb610418974e4d119bd475534eab06a8b92c22e9d356fa8c216ba954295ed0a26b7a896bd4d2c4d1849ed4466d29ae2576bcdc17506c8a8f569b6a2546ce2af4a6a973519721a7c8afa8524919cb4d9c3d252be1cea59161ef52dcb71601751fb9d56f671d3b1d463417c45bd328735285880035f52a54a66a81707c68b2cb1ed6e0d48fc6594c0d4743315fa5c45fa359946a08e8a6685bd4b61e789844a46cc7cf292b5079aa5bba3072f65284d4,0x17a32cecb482db0b24f52b32c1121ef806ad63882590f0d767625a20bd49f0b64b69d56bc7569abd5892b4c124d22c4d729aad4b38b60abad910b58926ad8a7674ec28177c19241ccbea6f2884749d23b646582d7605e8a75fd3abb0656d7d76881a8ef2343b0604b5bc10f8356189d206f3543626a5a807d441bd9fde0467fbb1b682d593d47ee5640d77033fe8dd8aa519016d63990374eb9aa4a9757b525a5d1358965d018e99a74c5d4d9a4e81685881a3007d0e5bb19227c0e8d41472380e85a3c29be599d183bf552a18100b9216aad944cb2a00d5383516454f8f969748962a936eaf82d2d4206f4cc8b4d5438318f6d3ab574d2757939db655ee342bb365041d93c1a510e6d320ff5249f590b94de7e5ae7d42dd324d58fbb5639c559e3ae85197951e72cf6b49889b4ce27ae32cb52061d3ba56a5e5ba37298a2cc7d79a074c7c6d3053255937d4568626613d475428d479b58d1750f489f2d0942c9ea3b5f328b63a38502e63fdd3b7f744e93d4a3006ad6fc49cee8cc51a315d1e8975be67e3527abd4466d34b2c5c8ba758e0e402acdf13e5cb889865d69ad7b45a9697c46e4b503ecc07f474e9c7d369a755679d3596356b92d4193344036d486a2c0ad8d34380495b11f8976a50e0d40012b9945808e870cec10576423a484b0558352134d3b17764ba2d599cb4e2bad72dfb520b9d75eb1c4ee51d5f1af4b90d44526586ddd53b5765181d70be34e8524d4bcd720a66f2b8351ca63c346b5ac28d18bfe045a6d6b2df4e4bca980bf5037fb6089f5c2e54d51d0fa5a5d05ebf2df257bba9204504d40d36c64f1a372168e9638e856db130d5c720f49bb9b96ac7645825979ab30d52943e934a13e7f5e06d4bd20c505971e775f5d035c17dd41102b68a7ae88476521646a1275d0e60d41cf2ab39d89e0ec0c8ba6002675353d41e32b5645c49679a23767b10206adc3d44c7b51fb8d4035f566021215d21d3fcb57fe3527e2d457f344b19d121491db0eb0a6668e1271f03f6bac2833290f56aec030f56a4362d55c8a8249fd6164e5550ad42a3b4c492d551e35464cd275ba54dcb5a4a634d160d62cee1ce3e80abb3625f6a37a7ef65822c2a8f4daf1d9868f51854941f2ea56d7d38fc6c27e4d33646059e2d47801242f87b069f50ec116237b4ce511f35be34b19d3727e38a177ba5e35c8f6d43b9540081d6425351d0f9f7edb50c75d5287365c9fd42f48c43ead54e335681793b21da9f94d120ff4dba09d0aa68942fd492a6ecbd2d147c94cee57d755206b3d9d1aee89622cf5a8355dd09041e6c202f483ca4e2ac1a5781f5ac9fbd51d0487c6232871c5b96a548f9ec4049d5d7f5cd53d9b5c7647b4d4584e1dfec9d7b475c560b0765d707859f16c34caa3d947ff4e6724a84d3529c6d473268e2ddd4389e58b26a781176643a,0x587b71849f655ee5aa06765416d499c9e6b11d43cb75e8a9d58b75c293ad7892b58b3b386b564c3e9bb362b54db9a2943a8ac7ed1b1fb52e02b24d2ae8b3b81200e1dca608288298d1c750bb354f2c408b91e85e5a05fef5417bd68b4351b66d52c1729d8dd97b4752681d93d334d3afd14380cd12b94688358f25a39e7f04eafd9543b65dd2ae7dbefec87d78ddb58e762d0d8b598266f02da54ee55901f2f430ad39cab26d91d3b7bb54505b560bd362cf949d863875fd44ca30555ea6821b52aec1551d139b4ad50b52d527ed450bf4e2b6d469c2a443dcc0d370ac28d36f3752dc6d46f9f45815c219d5c5851d8a50e1e130cf44e535e9fb9a8975656e0c23c751e42d6464dec036d3829b4d7bb92110f4eaecd31f5f41065ca133751f94d391a2ed212d6a23e92d01d588a6b679fb08871ed5795c4a7f541871f5af75d90bd4438ec0bcdd45419c22f2d42f074e11ed4601f14b1914110f55d37d473c65ccad5c781d426f8ae56c4d1d8dd5992de6d47a6534f02602d779aad5b10b08a0b3585ad5923deec3208593355ca6278898d29afd3635698dcbd58192748f68e715b64856d5ab3b32750b372984595a6aa300d05baa9529b500009832bb51bffd7232b15802d42d875c02ed544e7540f595a6e578c6cb036f74edc36f754f50d9dd31b474ec32d61aeeea55ad1ac8750a4f9a608356561be729b4086a8111b752b6c4a668b608d97b19335410dd3739f5d4d397000255ca618ab77596ea6fa6bdea3f6d5acce06e8dd3b23284a0cc584775400095a17e6d31d15ac8754f8bad0b3f5cf2c1f603b28d22b50643501295c1d02d50e0329d4288878b0ab5935a7f3b3b77500f0d84c752000095b5c47cdd8d582e60692c7e5d4169d1db15a22c1e075961c27cf8349b215c25d45b9809e95bd9f433756d017b03092a2d928a81758090a5437b4dcafd43838e9cb4d88fbb590d5d43d54e57405c3b4de6659d584f16dbd3d4a4ea1d98a91524eedf25d48adf5490c4b2d1b645dad35bfe5886071603b30233495d0654dcbd4966749f6fb05d4350408d41777650a1b263db5285bd38b4364e77d48c1a89820d48c4294afbcf974e50518d46bc5729e91f681b551ba9550eb6411f371175f6154d519c9713ffa93eae894647a9d2ecd4afd577ea38054d488a6a5d02bd59af4e21bb548bd3649fd57af16d635b196945d69fd4a50925d395a3471eda2059374a5c922a25fedf4459d9720f4e25e7e927da97a2bdae56362a29d8c82ed6c0c20b957d067d4575e80aa77b7892c1d5e81487352261ce37435006ad45c3752183c96e2ac96bdd30c05f4c6f5ca9ce48432c22f4808672d115574c2b4b26842b923f3d257f5495fd8555f52189d166d729f25d5aabe7d8204849d6feb197251e7282d2488ada89a7f0e0002561893375335248fd484ad718,0x245d72d5125ea4997d46f2b500b4b4a7b6eee39c4b83171386d56b8570a8ed4309365ae2d97647524f67b9043514741905d6b4ee51811f3527f9ca9ce2a5ca6152a7e55f4eb0546cec8c4d46b135045bd853d6c297920b636e457e6f54165cf0ad59ae970c21b55fed65cc5d7835358b3b0d9fa52526ad401d3050018d7eff4e7ced42b434eb237b5d4354b19107e2e8ca947d15d74411fd3a81752e22d251d2113705c969761f9ed32d0b597d84870eb525a5437a81f5fd6d58b6766dc35bab0752c93d77dbdea20b70b7f755287c351296551b2d3fa356a47b341e9e57f28f4105f57e8d522cd34fb4953e3b461c18172f67d2569348f87c242d4008929401d3b86a51e995c1f02f9d5ed7a30081bc97c7d975493ea73daaf8e7689980b450d679428274e51d99127296aa8a0faf54ed0344d9b645b1d436775222ad97f4744ebab00c29c1557d3672f4e445940fa8d0582403b6b55047d46b8b51449a31020d15f2991551bdf1ed599cb450e00843834e5b9a3b086a66cba399c7581257697bf55c9cd46e1b51cc38e9d2ae8ec1d73b074d948d54c75720f0b67c974e15b5a0be130ab37575a6a4c21cb577ae9049d5a4df52c4dd8b636f61891d93f68c462c14ea565d978e45834db8ab075027ee02c35bf74e68163a2e2d5b6634ba920031f501f3ed56aa3887debae0cd3714755119a00b97628007004cd3590bd384ad25c2f8e917e890e61f93853547433b0a3405e79a49d6a0f29d551d150fd9d6a80aa5d54d7236754e0e593025f9d8dd447daf4dbd5b28a63a5991269ff5e1b7d312b2beab2c7150aea7b24939d9f5451d37875e444ad56b5e5818722b78264226d7acce01a70b511f3597fbd98ff7565f8b02f48b811fd880f6fd14cd52caf2151bd42cc3241a7d76bcf50714a031b2c494fa25fa350ed34d74e7567abd38ff534dcbd22caea4a249696417e602d6b925342426a584f547d77e308728d1c84992ecdd5ed335025861571b1346610ed634d836ad648720d211a2d40f83622a36500d281987a524d2a4795c17876c1ec4b549dec189fa328cf54ed0d59a04e25905c5332ecd94b5428b51dbd94475f14e06d93fbe5147418534b510e63411b74a85ad282e74e0d1bba16349f1ad77ebb5151b2e44dec1d65d572a966e95b5a97171458d443806113949a80b1c2d25ca0675e7d5d4a2ead655ad8435615cc5d40fa87ce50a65a2355b8dc950d46831f7b3b4d725f3ae36f75595e343b945c0d7d3ab7476978d60852eccfda917f525e4ad499a750f2dd99e7eb1b4a5b1608e63f17a0002d6391bf10c965d084c82e7516aad539e204b39c110b70ab32d67667529bab29d7d68f7ed5047f515b1d389528caa3d1781f54c21c9089a422e896abb3524105c890e8e151a717e16a85a7c0dfb52226145f7ec05f8d4200e84c16b5a23ed,0x8134cd70d49a0436086d59c8225ca63639474d451d5b9ab54b3b0b869868aa3d59aeb660c5b09412d4e762f969448ec187a3d83213cd4694e8ac5d7151d3582cac55133523ac9d6d2b60443d9923d35d1dae57c3019ab48907f5019cd1237b52599d3af41726f5d50135245746aa1634c3c0487a968e691d3399351d9bd47bff5256ca32c675ca0fd44abf52dfd4a2d6b5464c5cb207656e8d46786eccdec056734d7e7a3756f55724b55a2362c4dd44379729b2be7b85642d4cc924eb602f5c8722d4fa06887075e6c0d357bb4d998d52cef58866717b3ededa9d93b4364f129d670dbc8d3d468274d2988ea26354849d44f3b59366d68723269957c38f8f62d5a5ba56b5c82d4a4eb4dc2f8fa5e750867b060df65851d4977b31055bb425355d48d48dc526830d9a01e55688d4951a8a9e9d5ab92958029f74076159c532afd8a937d3ad1b5081b7b72d354bba81a3d95d921d4753171af8d51fde8c898b35ba128183be6947522d9d6507b4a5d46f0db6ea2a3d9869b520a6d232cb592fed30b0f5166ad512d351a83d53e2ed4866d53b075aae76c7635c4388d32fc750d91ba7dff51d03a2152366491d634d9ed0e006047caa5cd49973288cd3d57c852601b90977ad6cd7ba6c86065f2d36a55254d27951d03107ebd2cef5ea276a3589ed5f0ae3daf52aceb5b13748e99799c57502dd596b8f5564ed46269c6618d35f75f45d0c5b5eab569fd3b30e81d5ed254be8db661f3b4f54574d291f56eae7d2293a529e92084d1c56aa5aa1fb51a7f2d1d751c2262805d6a4fc1a96ee2e8fd9d995bb658d0d84286c159c5c0437507dad5781da93af790be07e8b7d172ab562b7d18c1239451d46e6e522b7d9464f4d87b702b79ca154d48bf35ad6fb5800d35f35d4073b60ee5d160635446d7ba3728e4f0d7a91f10b6ebd2a9d88b7ed33926ee4879f4dc3565904d5d0b51d65d12e8b508aaca15d35a39f9ab5eb254350882ab50ee5d03a675506ba33e3b4c90cd565be885aad76e3344175b5226750ad87b6c4b54ebab204934d6e0d5b4892a309d495b8759481a1bb564c7fd408b75195ad6047f49091d44e3172855b08551f2ae4a79a04c075d49a16b4d2afd9600b4e49fd48fdb5215bd7aac362c7ed81c7b59ca6d8af274cc299f0d2750009d23b04a411f188ba606b9ea21bef4ca7bd7257f4e6725c69ff658f6d26031d90add60f81be4111f485a82261ca3e3b4a0d4d51bded6520d49f935a5a5d42cd251065cf257dbc588d41f1b65ec1d41db289b7ba0676e42c28127635411f29a2ef68a886ad2f4861b4ad411b5ea1a8c5a4dc69998d49f9348c755c3f675ee2271739d69079c1b0ca1c088ba18be390e0245f354cbd2d47242510af6aa03a40c65bb5aa88983bd4490350ebac1af7f4e830d6765f54432b165212066fb09d4739041d53b6,0x223674c852a923c75ca249456d32cb264978df552e7cc437ef4e0fbb1872fe2ffd4534eba9bdd40e235ea7ed40c7f5461cbf1872fe93a346b7b468c0d31872fc61cbf14674de774859e750cdeae349b4c562d495569a8c0d5a58d3461cbfb8b75461cbf1872fd1309cac475461cbf1872fe1b7d64bcf55474d860c6d430148a809ec61cbface56c6d1875d02697a4d54bcd245d0caa71f49bc395b287399404a3fbe55aa04db5eaa57f99d89c36018b9aaa9699fb671a163464111a15068c951a69608e1392d501bf5086bd965234e374a369474d8d4b0608124bcdd725223a858d47ccb50b191397ce7eea4d736f750434a59d872cb7dbb34074d7703486a2c4141ba08a68e21c5927bf66c26ad573358b2c5653ef56493c79b007d66bd5421a3e600d42a9f4d1b295148a5600d7195bb447c67b0056ec009d7147352af1d59bcad455587499e7e8a9597298d042db139d8e2e6381332f61d5fd765cf61004d1090b5d9a9871205283e0592e89e5e00d541cd713a9d59a3b28f43a3ad6e6a12759496e1c2b380b8cef204fd455834e39cd533b2985bac7061d718d54ab886a6602d942b4ee8cdd937e6fa24b49904482bc3d49a32a615469739f5045cb5756b567c27db68526d7ccb843b55c37b5609b522bad32365e6b2150657b56978d91a234ae8dd460374edbcbbb31f527ad49a655e86dad45faa951938721eae92e2d80732a624a304c77499a2d404f352755a2880b2e691d249a935a7f316d5ad4b21d4527a8ea09d4a5df4a85a7b6825458025bb1e6885fa8eb64752312d3ac4a8ec28108b675cdd3c28b07510497019334e1c8cc80cf5222a5c394ed50e01457a34e2c1d7ba45a8bd214158b4dad96a2b83656887b84774e2089699d356226d117535d0afd4ba474a8a9d36392752981a7aef4c388d27ef28a9d9d79f235c640598e2296db7d55673502b1d5b951352e7cb729840b6959270a524a1b852bd64d91805bcf515919a3cb359f88d85b5655004d2500761fb97b0093526727b0faf51b4bbd4ecf50731a53fc9c5ae2d644cad4ccb69160b50e1ad95dc34c7b21f66a686b32b0676f51e65a7634a94f51ada58f514afd6230754e0aa603ff648937197c988ee5204dc34e940bf321266acbd3342752addd94a60d0ec134118ac2d3c6aaa0e560e9d4a28758867592d7354c88b2224f50d68ba79ab2a93a7b6034d1d01d53aeb0d78ad3b5becd27ed3571750b2bad72a9bc11f19471f529afd58ced26714cb7c9eedf06a9849f5892ad969ee766c0d985534d1138e9b01565822e7801288d9d09753521f9d65446596fdd7a1fb4c6fbd52cc331ed06aab2f518fad4b1db5a0819923c759d34d4692250867873e2f24213c211b6048b34845336526a4a8b77566186f48f869660a27f4351e61b348fb4e11dd492234c50eb552bdee3fd48a,0xfd97ee74e4f6d4374f02e05ae00b929972d70f1aee033d53fa352483d57b415ee16c99926a6ea5bb27cf50fd93b735a8ec4d037e5351ae250969430cb259913126410536c86e5c5ad731be9a22fa2031f66649c95cb241f944c6df136e2d5ca656c031f20a301367766a5f56cd6d7819b03561891e1bb74c61cbfb86a591b35ca30b519d4be75a6d4898a98ba251e5cd46521714c0d30c7f58226d438152a1c0a96034816aad765930cee551803766b39d57aedee6ab7b3c6352411d96e3ed461cbf1872fc61cbf956b4cd62872e1f56ab5d41872fedfe811872fd0e0173b97665820c1872fc83dd51872fed7c9da4e8d861cbf1521f61c0be60375405fd31872fedd2ba01d2c0803bb442304d29d595bb5461cbf2bb1728c07b84fb64c3ed52e89ec61cbf1872fdb2fa51d76a53af851872fca7b878551e5393d411b601eca5c8e736645bbeb2fa8a9afd638c7129424d7bbb5a2d0d7374ec683dd4508f14928a21609c6bdfd483bdc2d7ccc1c3ec0b8fc410f726c2e6f7562fdb667b04ca515eed7153e385197b00275075cd618bf3461cbf1872fc61cbf2caed461cbf1872fdcb46f6f672aa02b55ec6ba9437b2f4864f369f07e352e0c4ab17751b82d40962564939d1872fd993b5452650e37bb1872fd4d24c273a9626fd6b5eaf9e5bd323e288c755348ff5ddb3d8a5e570d36d3a30b4d89ad471f68061cbf3b956895fd21872fe6028521834861cbf047da57b8c7a4e89e8a97b956b51807be206d7061cbf1872fe2261a84666461cbf716b513a9d9b0cb5d5d09db38b5e5a2d411031debbd417daeebbbae11b5a855559b38b59d87d44ebf556d7d11872fd9484d1872fc187481872fd6ea6a2b834c61cbf1872fc61cbf81f75a99d8f617a944344a1872fcf2d851e4b50074c23b97505f8d5b16f04688d8797366355d3b87e8e229b51872fc62f8f0be085e75d4b43752915bb861712e1bc5803572aec34657868d01d403268aa27d511675decf7e00b574a1779ac85ee3ee7c51d19c61cbf1872fcf77a31872fc495b53b9440959979d2f10856d3a4dd35ad96472612861cbf9ddb50b98d442870def17d145ac061cbf2f4b4a8a7c01872fd64eba56369a064c765035220cd402baec7f2a92a7f05fb8711872fc61cbf1a875224a0d2882a55d1b51872fd663d353a16461cbf72ab529790b889848a7bd30682957d85c1872fc948c75b5f51ebcd51872fe2ffd7b4f35861cbf06beb919359919d2861cbf1872fe855c148be0861cbf98af2461cbf5c56385f3a91872fc61cbf1872fc61cbf15d1eed879f530349086901872fc61cbf215971ce6a682be9446dd71872fcb3b2c649eb4081b01872fee22d36051ec2afcc26edb5e59503932d4891b564ddc48e1b220fd24856d93f4b393e5b5512942ae7d4a4c350b6cd49a47508016f348b1569bb,0xa7f0c11643031f5926113437ed10e23517b9bb15576602f4a70e9648ded50daf5d0f0711b36c02d1adb9a9eeca9a9752361d2b341f6b6507a7a102146776d6a8cb505626b88721dd2b1a44e57027db58185ee9e9840df2516c0b12f484888fd35ae27e06179764240860d3489e8da8e4d3abf5a3c7d4724752751cb5916ce189d599cb54e76d6752f00e515a00025444ad4a5e75582fd478dd71a7f0b908e54f2cd55f61368f6d9106f2644c5c0c8d802d1c5a2828d18bd33e3b65501d52a8d355cdd440def811f1b904135caad88e3ea656ed39d7f528a950939e9d6bd8f206d063c71a70e9aa21cd36ad694548833d334882cb9a5e74d04ea2490121d91702fd600ad0d48c4b58b697b3b6b50ee3c49c0352c93d3804350867c21872fde775c2cb2c274b591872fc852d41122ed2d6b9b38a3d6d7d2584d4047cd30a5750ee5845a834d375a9507b5049e203b43519e26f53ee26a7ed304eb566717b8fc5e658d94b1fb4a410d565207c4aab511c9721b39546f35c367c52d1b5a1b787682568795b0763564672d920075088fd975c9c53a4b51ed354b3bd380375064057b9a8d11ecbe5dc07d340d5a71f52a57b473f67eb37a303832de374a4c9f5169797437b503c4d46eca81d4bb2219ec62828e1872fc472d51872fc61cbfb0a3608d9b01b7316676b51872fe154d61d735c61cbf474d6461cbf6034691dfb593da060168143809dc56d42a8c7c61cbf1d77526c6bb82ab569e91c06f3503ecae8b3b502c36f169714d531d28ef55b1dd58bf35556dd43abf5647dd5b2ee7de5bd465067dfd0d81872fc141b02e8b448c1d61872fd13dd51872fd3e1b51872fc1905961ef6461cbf381524570d372d16e774d498923c61cbf1872feab0d675535061cbf53236461cbfb1fb4edfeb50d89662ee6f020706c28d71872fe3c7341872fc61cbf1872fcaecd58b64f2c32346eea8cb467d856f5404d4a22cf516aa2b979b126c01d061f541294aaa5274e991d110d5c582d93b975461cbf1872fdc76d46c1a406cdc2b4f35ead6d4882351557d55e16ec44320372f5dbaca31872fd7cd1a0898da039ae1872fc61cbf7466ccb13d9792764d62d303c350141c179d759ca6d19d42b94741d28329c7b2d3352d24542815d435d964b2a31f4c4814989fe58124d48625e88f1d31bed55b949984a6594e8508475eeb4fd44a2f526724d1ecb5857450013520c059013eb5505dd386824156d4d10f6d483fd54c9359eca7bb04f0817bd504cf1658ca39a3971a72baab8b51464b097c9ede6ac917520d435365bfee64847904a7554c8d7ba5605831be859f54b60b27b75b6cb7d488d1e5f4f947ed97041bcb42b75e7f8a67edb653a0d4855360a9478713f5db66d634d8c2c87d64d996506ed7a16b55e209268b750ccb37811566bc9d450b28cc245c206f653a,0x52649be6b875626fd58aeb514d25638c6cd99bd419f56ec81d4960b59474d153a355049d426fee922fc73af689a70ad2ba2eaaec1a52e65d8dcb92e1f5830ad451e7253c970223f56e95be2cc2d668134546c2caa7d94380687d7d38ba752db6d425db5131d4d2df674b42d5752f0ddd6d47965aa963d58551aa5f8ae31d7529e97b484965d391f804a50f551f2c6740c08a928a751d69be51828a41049860f2cf83d4739f55ede9d63867e501d465c82e942d5ac874ee63d401fee8ef2d36277558fa8e6a0ad6599330b775202aa741eac16c09530171c2ddd3223f591b3d38adc74e379926b654f55404e3135554be2ddb50504817b4674db3a2160b590c4c95fa1417df790fab4c90c5ca4523c0c2a579f3569637b568565241d43b406a6696f6f26c0d9dd25f635471f99381b6174d944ebd65ae2d51f18d5f941457df0ebcca923ff5a4e14972734e7e28f0daf52304d42f48ad464793a6744f4cd49b00d2618d5a6ea5a979d96a83556a03439475e762a041075a9af7b335f52963d32acded160d5538d2a113c7775935b927141f2d5160d42c6752a94bbb0a0f13e5c9ab05288c3d3ac4764959c12bef3659ca6975361f86a37d8350b2bc720c3540096a374d65fdbd350075121c7108968927e5b2acec268a9d765e3ce99d69861ec11f15ab3b29f6f7bb0c89c70f7908a2e8ec10830dee57705a13cb61eecd360347c249a30c7b55ca6132ce6ea2e97b8311e6411d5559f52a0b958e734d7f2ca51d354b427ba1635c548d78b650a54fa2a815664847a2da61d3afd6938750367492e72764117b7e375224b4a7987124f687682751a20d5439b556fdd46a57562d9d868275520abaa34afab62d46d29be312d51520b9fd1d43b06282f8232cedee4f6d350d750f789f656b5644c4a1b46046fda79f128c588d816c7659a97b645a94d62d5381522761c772835ccbbb546571d0e6d95b5e011dfa978f351edebb227ec0bbb948dc75141ed77c852ad01d3089f52e4fd56ea35a183b5200dec792d38ec172c5bb00a374ea02b06b7b481a4a3588a42234af437b56c85d40fa96e7c2d546ccd2d918f69434cf292237e6a4bd21a00567647dd816c350df9b56032ac5557b017f5eaf1d68873567e5c033b316c10a22caef9474d9ab5924e9fbe8c48d166a5caa2a75cc3d4729b488665c0b95227c8d81ecb550e0115507514352812b676d3cd43b95e48ded73b4f448c3d43fb67de4a8f0ea352e16b51081ed4747ab887261a69697e1eeb8eb5243122bda813cb16437ed50c5f1473ad5538e952bfa5629f508b35ca7a4d1ee1d69697648767c622a7a9c6d30b4935e77d55161c6e0cd5b98f5e1b18e65cb4e8b7d3257d6e824a06d6b0d4c83ba03a38c3781404354a8e709bd751e37491bef4888f1f989239127d99ddb5ec4d345059c56b59f120535,0x46c1a99d44dc1edb5ab22acde5033d4116f50162d4435755435d3237969a50d41bef65474209203508d9d42b2ae43e85c80bf54b986fa16b602bea2a462ed74ad459aa413926f713d28bf1d3401a8ed82b0203282c28d4579f16590d5ac7ed50e001b39126187a2ba35b5a584aac85a882c8117f5357d0d32f48cc5a5be09db240ffd403023e8c0d41bb61e914be3d5e96e49485f37515d9a20fa356c2ed758d709d5e800dfb4c41bb569434a189d607eef6b01c47dbde4d48a244cb24d53d7546f66d013446f12872ad48187541874a3b0d6d275af49f28df77bb3d33445d4899a04ad6137b12b6eea02ce8ba75d34ed697cb595ead6892986af11f2b2af925ea215d7490b182332c6cb27b543c676501d57bb3526c3d99d2ec2ca19042c7654a5979a568e18979043605e005ca34ae518bd4781f510de4d51d1f03c29050f75224a6001d2c473ad4b0c814ec3d3657b50dcbd305d7251c5d43212ee59918030352a25d3600b568b7d5a89d6626f59160b56493c5775a96addd53cb75a805cf8551e8c11d442c752293a359aded0473b4287061be811a3241ebacb3b060eaf17b3953668fad5ac45729dfab3cb15c295d8755134e3ed424f2e8c6cc266368eaddd1b6f67e1be80798ea69bac37d834e411d38dab52dfdd321aa02adabe36f548b69d6a5094c535d879d565d9f8fa55676ab57172c680806d4b05f5c672d5603b2c2a5a51b4766d915c8453586b1d565cb50db6b5237946d224965787d108b030f7547c68c6d0348cceba383b65bc95c715a0813cd35eb352dc3d84c747dd2bd46afa6ad71d549fb54ab3842b6354574d5493ab8e228eb70f56d01d6ba9352411d426e6965635929ef58f2d7986c548555d53091c15f1d632f68e6a9a59c5328ee51c48fb569c7d7505b4cec3d53b0b5d6135959c752e6a5c20fd71033d33e39e6aa54db62b555c6b390bad4b2c7c4ba2660aad37e5060ca3be8928e2714b53d31a9948d43b05ec6d17bb69eee10ed46ad52868cca97bf5065ca25b81c04baa23ebb550e65c7af3621b77b8dda1d0e0d251d072e9a7d237f5129fd92c4f545b1704380092e7c93472c131d34720d369b9d6913355480c17c8aa6624d450eeda1547b0be35881bd12a5362d76d55b7a8a213d78b40ec8c1d34ea55eb1171546cc5ae148b5be91a7f2e2871c1ce0954c774dc835c3b94ce9f6d7410564574d4a50b50860d45f3534b3bd98b074e74b87b435346724db9aab88d9d866335e8a2712566c1f6faa3b4d2abd2d83c2b52942d372986857459512b51132cca7a44cad0d2b0c9ece51d50a4966061d119cb49921d3346b5c64051892d3523e2081175a9f5d4729825a7fd45e8ed6c28194ec74cec17d49013449ed97aef56563d5464f58b4661b83134813a043912417d909a075d31dd5373e650add49fde0031f874dc3,0x57b87ddd4d566d5710d550af32f836bd9aaf361362926d3e8a93734729b5c4ac7996974d59cd5a50d66a5cd999c5650f5a7635304190d3b7f571e59d5ab053607dd45fcb396a0d6b4f360f8bbeb0a044443d4546f5c8d9d1534b54d3ed5559f617dd9f689eb8cb2d97ae310b3997146745aa048acd255a51d286a2b5472d3ab9dac59fd4507a04806715af605281d114135dae14d977b2969bc384f354f9ab557174d25d872f4835d1fd52f5638b191811226525bd74f398a830d742bf5de49d48b642dbb9812a8d710f5a50a8e8c7da209c81f5241714a52944a1d4110d728fad43d575626f6a496f52ca9ad8bff4dd58aeb04e5624ad99a4f52045d5af433e12bd5383b59d60598112ed945819b0f54e4cc993db5a467d4964752e16be548e94bcdd68adddac817132b754022a51ce3510e03675323c7e2d3923d706d1d623870c2afca2f563cec3d47fe129688d39212101c2ba88980a8f9d41bb7548de7b81967e18912756302a5c7051d348ed01f880a400006815d34cd36d983bb525a518243129ccba30c1ac2e494a34263958dc54a0749bd9be923f4e1c0b543801dca6d38bf1a964e3d7c6b66a5cd5b63659959d5116510f55d65aba7caa29eb21f519a9c611cb50d53d5b1374c06ad72d0b51ee1d534d8d29635c39332a12739a824d0c24d479d754bf5812d1b550e000b645ed7cd34b4047d1ffd49664518ce9f411f5d840a324b6651b3d5888f502f8d98bae8d2d6be50d4d0e76d704a52296cd4739db1a955c261751ed07d8ced294e4b040f5a12f34a5752c1bd4d450d75ea02be9f71308f17b60edc23fd5c3471e5eba8e9d7f5483f4d875b508c1d4372db20b3b517535907fba7af352355d488a6f927e7b1de7504927b4bf9ad472d45a5ecd158767b293624a34a0aed69cfb5980810459d472985d679d56df1ec959ba86c7511f26c6a5521d54288dc529435274b8b641a1b056c755193d50d274c2c0d59801c48d97c5bcf5c5fdd48ad65622633729898b69d31def55e756a63ae84e99d9477eb5eb5bb6c4306493b5b5eb1d480b0185750580ba4d9b552dbbe0c7f4caa7874b9ed62fc591f1b5941ed33ac9eed715c045eea0e8bb2746d4b42d37b41150e02844dde5284d374e75ccb2575f603e5d0d4234d36d91d533fb15770d734d98c64052a9d6d611c9571d9c2a27d4b38b2e613d753c68c6edd9b0465c548d67147665f87caaaeea9afd286df668c7d461235127e6f064142dc5d4400638a7bd4b134684728eb49a75ca624869b5df285c2c068aaf1d398081e7e29001ab65b66d3073a38d3638645f4e15bd4477ef9a4dd577d5759a2d3b0c8da8f9d338396d5eed5793e748524da817565e6b3847b55d13d5a8274ed3c6f574ee9161c2496dedd998e39e2e5fdbd47298514afd3b0cb4ed7cb5aeef007e2d479035441bca74,0x81112b4dd8049729894ccbd48fdee40fdc0435abeea4d2b205c27e4d5312eee8559767db50b190710234e076cb6f9f4861cbf99a748758a08aeae5ef1482a7ec19caa35963525a1d94642562d97c51d02ae57d4541b51d01588a5e89980a599c5f6805cd5af7511a2d91ec8d0afb8ea8246aaf1d94abc356f38190728cf55d9206f551fcc466e72e29dd49608bd0e026435745416d9243f54ec136960b669d9d4ade35cb21d9b88b513a4c94355e6e16a9084ec4bfca288ab54e3e8190d2e82d2d38898553a9d49c533125bd67986d4afbcb1f6b50bd215924f261c1d4354f469afd48ec354d36d6b6ce9c867c17f423a7319484ea3c10dd72f4b66cc5d5849f54190d532cb55047d9512b5613ed19809e40e090abb34acc9cd38fb4a2b75ca3e75de5959903d641779496875d7b17b2f9eed324d4a169a4b870c11b758712a37edb563121f534b4ce0ed54975ee411345f374c5482da4df49ff29a93db5e3fdd495b9717d849903f55d5b576bc47c981a28898602f8341dbb560aa5c124b4c8c9a374769e26c95438344ab37a895b5d5dea944432538d941197550e02578c2d6d86d51b71707c6d8758354d6fd4ac861dca619630350f29d9532351ca25748fe05d8d5748f8d12fed451d07a1c8ca43835dd1dc516ea753c9d5507a0096dd519336574ad3551e862c1819f9351ca6a1b98d3523fba1b6831a10c07ee758b21d31bb626ad5d46e82d525bd366adf595ed389135e6bad53b049e134d2796f462b7d3415b007c687282e8ac281815c352d82c10b9a989379448fdc5f51be0c271d80eb50e22742e3a3b98f4cdf9c9584f4db8cd43b4decf649d7a647e618d21751f45dad431fb0e85ab01bb5ec755d5534b4693a813d555dbd94d756f653704d3cb366d904a9541283cfd41d7352d7ab52de2407c66ea4eb5941cd4a00350000688ba61cc09b71b6b649c0c1b1345620cd5202ad48b3d572d351f81a2a7a469bfcbb3b4f4c0e8d71b36c62d9d4593b5cb30cb0c2729911ae683350d1c5c7c8752bdfd88b552a5dec9468f5d4d8d79c821e74b7bb37e7c388d1a32ec8ff2d440134ce760b9fe641831c59f0b5a16ebb617a9e00dd52e3ecdd5da06b9f55328b005ef51a70c954df665a5467953606adb255e5242afb50fadc0c24d544da8e2eed4466e963c7d3725ad527e52598f51cc5d80fab588acd5881650c304da0eaea6023384c32a1d67190434eae7d31792d4bac9a7222468a2d4593351dfbd580bd2e0f8d546cd36a1eb5449352154d254eaf410ea9696350cad8f1d7b556797b277ad983bd5974a8e45e8e3abd66154d18e7164bd23451334d5a17d6a674e1275713375debac78115556c2d49737515794a224690688d347c9dca36a02f48c2720d659f6ed3a4ca75974c9a9a9559e38bd22f06421d5d4c1672f52acad557c564c75d9,0x83a274a7b7b56c5ed4d2af3ca75a85ad674af4c05fd417bf5564cd647cb64b875951d1a4898c4555f6481b799341c134ed7752eb8009d3391688f8e7b03268d9d695839a8c2a1d42f4b4c6405a373eed511bd29ef640eabb48bf297b8a51a2350fd9d4572694fa4d19694cd3a7d52d0964f298a3ded245f8d7b7b2d595a5960c6b5e59d416095ce54d41f5f4564e81b0a3481cbd555e756493a9729b52631a3758750802d500025613ed3438054f2dd106734a3f6d343574e9f57148ff50801d5a89751c83d5528ac2e8dd1567364e7aa071db569b9d86eee5042d607a0765e47b978f755e99d50f835a2d98843c35182bc3b217540e8d586c7568f9d997c9810e0105a21f20c5c1a033617e86a44e521e62d5966760fb6b92aeb50306c14380d057486584f51fb987ba934d9fd961d71ed0f0]
def a4rows (i : Nat) : Nat := a4rowsb0[i % 16]?.getD 0
def a4layer : Layer := (4580,fun i => if i==116 then (169708707202400,15775) else if i==120 then (169723521486176,14775) else if i==170 then (169722462422368,14717) else if i==229 then (169708471272800,14751) else if i==322 then (169653742945632,14845) else if i==749 then (169929694594400,14845) else if i==892 then (169740716033376,14845) else if i==912 then (169708555158880,14751) else if i==923 then (169708707202400,14783) else if i==956 then (180692665650528,12783) else if i==1151 then (417998654966112,9087) else if i==2927 then (169708472321376,14751) else if i==3960 then (169708504827232,15775) else if i==4224 then (169708505875808,15775) else if i==4519 then (169708556207456,14751) else let v := packedAt a4rows (i*22) 22; let p := a3layer.2 (v/256); let v := packedAt a4codes (v % 256*12) 12; let op := v % 1024; let a := op % 16; let b := op/16 % 16; let mask := if v.testBit 10 then p.2 ^^^ (1 <<< a) else p.2; let mask := if v.testBit 11 && a != b then mask ^^^ (1 <<< b) else mask; (p.1+(op <<< 40),mask+(1 <<< 13)))
def a5shiftb0 : Array Nat := #[0x45801930b4e0013382f5d0411130507063b020305070424053b062d00000401111505020000020803190218111c00000c03041700090117021a02]
def a5shift (i : Nat) : Nat := a5shiftb0[i % 16]?.getD 0
def a5idx : Index := fun x => let v := x*(x+701)%618970019642690137449562111; let h := v ^^^ (v >>> 37); let j := (h/59+packedAt a5shift ((h % 59)*8) 8)%185; some j
def a5book0 : Array Nat := #[0x1,0x41de02d]
def a5book (i : Nat) : Nat := a5book0[i % 8]?.getD 1
def a5ranksb0 : Array Nat := #[0x3c]
def a5ranks (i : Nat) : Nat := a5ranksb0[i % 16]?.getD 0
def a5tbitsb0 : Array Nat := #[0x80000000000000]
def a5tbits (i : Nat) : Nat := a5tbitsb0[i % 16]?.getD 0
def a5expanded (i : Nat) := packedAt a5tbits i 1==1
def a5rank (i : Nat) := packedAt a5ranks (i/32*1) 1 + pc2303 (packedAt a5tbits (i/32*32) (i % 32))
def a5gidb0 : Array Nat := #[0x1]
def a5gid (i : Nat) : Nat := a5gidb0[i % 16]?.getD 0
def a5pickb0 : Array Nat := #[0x3]
def a5pick (i : Nat) : Nat := a5pickb0[i % 16]?.getD 0
def a5hints : Hints := fun i => let g := packedAt a5gid ((a5rank i)*1) 1; selectedRules 13 2 (a5book g) (packedAt a5pick ((a5rank i)*2) 2)
def a5codesb0 : Array Nat := #[0xeddebbeaae99e88e77e55e44e33dd5dd3d85d6cd65d63d4dd1dcdbcdacd5ccdcc9cb9c9bc8d9d59d299d96d89b55d2aa2551a70d30d2]
def a5codes (i : Nat) : Nat := a5codesb0[i % 16]?.getD 0
def a5rowsb0 : Array Nat := #[0x11ac0872bd0c008de8520f5e6a4babd07525284180d675ac19f462e273b2c78b1243835597b08e0196bc16f6839d26709d9e07fc28084612910399f8b1250e57614250170e36a3b09478d60687d614fb4261c3a054b0dd5e741425b76612832761a850c246430734707e137413cd7a84f50480cdc235c6eb6392c0535e9d01fa6e1931a921c285e5e80a08e78382612b968b12516249764c9e18b410b209a784ecea5c4f8f03acbd79170f3a9d08b1251624a3a06823a207fbc0fc6cf50f3b2e17f02c809781f8e3b757616c29c1788d60a944c07e3cd3f385def416118b1250e57218109a2cb13aa11624a2c491efce6bd3d16248c5262f41e8b1242408411c341c938afbc0336e2d289f49e0c93cbda4d8b470be938223c5c26066e5b4b4e07fc6ecb89c06f1f49d3b42cbc02d08273c3ce79b1715f84276ec781e3e69498a286eb111ae1872c2444381f8e89d9b8603cbd084798712b115401c8b0441f90b161843e1412530c1aa83c990fabc6d478334d4300404d3a3a5395e9111ade310262cc68972887d4a822bc13b78a96f1f49c1b228c794dd4253b2e30a69d01e58fa8f2bd1e36a3e54b84b6263b2e08afbaa2f4d7388bb2c8]
def a5rows (i : Nat) : Nat := a5rowsb0[i % 16]?.getD 0
def a5layer : Layer := (185,fun i => let v := packedAt a5rows (i*19) 19; let p := a4layer.2 (v/64); let v := packedAt a5codes (v % 64*12) 12; let op := v % 1024; let a := op % 16; let b := op/16 % 16; let mask := if v.testBit 10 then p.2 ^^^ (1 <<< a) else p.2; let mask := if v.testBit 11 && a != b then mask ^^^ (1 <<< b) else mask; (p.1+(op <<< 50),mask+(1 <<< 14)))
def symmetry2303 (i : Fin 12) := ((#[[],[48,129,82],[81,130,118],[48,33,133,118],[16,82,131,100],[128,49,100],[16,33,50,131,100,133,118],[128,81,130,83,100,118],[32,49,130,83,116,118],[80,81,82,83,116,133,118],[32,83,116],[80,129,50,116]] : Array (List Nat))[i.val]?.getD []).map swapRows
def a0alias (_ : Nat) := 0
def a1symb0 : Array Nat := #[0x6000000000000000000000000000000000000000000000000000000000000008]
def a1sym (i : Nat) : Nat := a1symb0[i % 16]?.getD 0
def a1alias (i : Nat) := packedAt a1sym (i*4) 4
def a2symb0 : Array Nat := #[0x300a0000000b000780000b0600000000090010000000000500002004000000000000000000000a067070000a0000000100000806000000003000b000000000080000170b000000000020000060000000a0000000000300000000000000a0008060005000500000000000000000000600001000a0000008100090b07000000000000050000001000000000000000000000000000000020000b0000003b200000b0086007000000700000000000000a0700000000000000000000000360a02000b00b200b0b0000002060060b10000300000900000000000080200000360000000000200000000206000700000000006000000000000000000000000000010000002000000000001006000010000000000060b000000000000030030b000058045000000000000000000004300000000000000b00000000000000000000000000000000804600000a00000000030080b000000700500006600b00100000000400005000100020000000003000000000000007000000000000000090000060b100600000000300090b000080000000020000000006000600000160900000000000020600072000000000000200000020000000000060010600008003000007000000000000000001040200000000060000b000600300b0000000000000902b0000000000000000a000000000000015000400a0010000900000b000000000000010000010000000000090004000000000080000000800800000000000000000000004b00040010000000001000000070000000003000000000000000000000000000010004010000000000000a03b000000a00007000000000000080000000008000010000000000000100020030a00800000010030000000000000001000200800001020000000060000600000000000b000000001000000000200603000000030000000000410030000000000000b0300070000000000b08000b23000300801000000020000b0000b0000b0000010003000004000005000040000002000000000000000000009801009000100000000000a00000600000030000b0000b0004000060100000010000400000b00a00300000030000010000060100000006000000000200000020000a00000000000000000000000b0000000ba0000b20060870]
def a2sym (i : Nat) : Nat := a2symb0[i % 16]?.getD 0
def a2alias (i : Nat) := packedAt a2sym (i*4) 4
def a3symb0 : Array Nat := #[0x10000000000720b060b000000000020000000000000000b0000800000000000040000000000001000100000010000000b00100000000008000000b011000000000010600600000000006081000000015000000003a00003b000b70b00000000000004000000000000100000601000b00b004000000000000000010000000600300000000700000000008000370000000a0400000500200030b0000000000000002000000000000000000000b00005b600000200300000000b0000000a000000b800000000000000000b000000040000b0000000000010a00000000000000307000a00000b400001000000000800a0000010308000000000a00008003000000000001008000a000000000000000010000a1b000000000000b000001800000b100000070000b0035000b20000040040009000010200003000008000410006000b0000100000301000b000a02008000600000001000000000000000000010000000000000000000009b0000600003500000000ab090000b0000000000000b70000b00660015000600a060010000100302008200000000000000200a001000020b070001007000b07000000000000000002b52000b0000000070000000000000000100000b0000008000760003b00001002000000000000b0b0000000b00000000000b01000a00a1000001060000000005000b00000000000b0000300000000010000000060000000000000b00a20000000000000a000010b000500000ba0000010300000000a0000500100000000b0220b001003000008000060000800000100000000b000000000000b007000710000000000600900b000b00bb0700000000070169000700300000000000000b00700000b0000100596b00000000000000008000000000b00000000b010100000020000000600000b000b00900000000000000000000010003000000000000030000000030000000000000000000000000000a00000030000905000003000b3600000000a00002004000000000000020001900030000000a60090100a0000027100000000000009006000000001000000004000000800540b0b000000b000b0000000093000001b10b60000000000600600000000000000000000000000000102000080a000000000000a000000000a0010020070004010000002000400050000b0000000b00000000006089140b00030000400000000000000000000009000020000008100000003000100600000200008800000000000000200801400a3400000000090000000820b0005000000000ba00000000020000707000000b00000000000100001080000000b000000000000a000300000000000000400000000000008050000000100000200000014000000000000700a0000000b000900b0000b00a00b600008400000200bb07000000b20000,0x30a04030000030060000000000000005000201000000000100000000000b0000000010600b0a100b000000000007000000000000010012000000200100030b100000b00100001000000000030600100700000000002308000000000300000000000000000000000108702000001000800000000000600a800000621b000000000000000000000b006000000001a0060000000000660000000000000080000000000000000300010b0070000202004400300000000002bb0000000060000b00a03020003003001b000080000000000400a000200000000000000000120003000000000a0140000000009000000000000000400100a0000000060060000000000105000010000000000000a000100000b0006000000b60206000000b006000000000010000000000000000b0002000000a7b06b000a0000000000090090000007001703000a00700000000a00100000000000220700000006000000000201a0705000000000000100052000000000b0b5000201a0b0000800000013bb050000005500000000000000a00060b00000010060009000000900000600b0100001b00100a00b90000000010000000000000020000000300063000000000000000b000b000400100600000000b102a700000900000000220b500000000005071090000003002000a000000007000000000000000050801000000b00b0070300000000200b00000000000000108000a00200000060300800000000800010000000b00b08100000000000000000bb00200000040810300400000a0000000000700110000a000000000020000000030011000000000000070000000201040b000003020502000000b00707000020040700011000400600000020000300000b000000000000000000b0000b204000000000000000001000000700300060000000000006000000080b00100b00300090b00007000035000500000000000001006000000000000a3003100003000070000000a0010000006000060000000ba28000104001000100000000000007000000000000000000000309000010000000021000000084001b0000000000000a0020000007000b0000a0b001800100050300000000000009b007000020000010000000007070000000b0065b00010b816a8100010040000000007100900000003a0b0000700600000b00600640000080000017700002003000600000000000000b0a00707000000030b000000610000700080000980b10052000000000700010000000000b0000a00b400a000000410020290000000000080000400000051000000060010000100a00010a00006002000000b200000080000008300700000000000000000001000005b81000b0000010b0000000000010000000000000008b00000000103000401200100000000000000,0xb1000030300000000000700001009010000000a00700023000000b00060000000000000000000000002000000000000400007107000000000004800280800303a00000100088000003100000000000000000000000010000000004b00300000000000b00000000005000000000000040020006000040a06490007000000000000007060070202000100700000b0000000500000000000a000600000000000080000000000a0100069001a030000b0000000001006b00700000000007000070030600b0a00006000000000b06000000000000800020a0005020060000006000000000b009000000000290000900000000000b00030000010000000300000010100600000000600000000500000000000b003000000010000000006000002a03000000200000040bb20000000b00b00000000000030a0000000010009000b7bb000a020b0030000000003107010009000000a05070010000a08000000a00000000b00000020000300000000780000000000900000030000b333b00002040310b0000033b20070100000000600a000001000070000007000000a000000a0000000000410000060000900a09000000000000000a000a00b00000020000000000020008000001b2840020300000300000000000000000000000002800200000000b0030011000005000b0709200000000501081bba02b0b006000206000010000003a0000007070010a00000020003000700000300000000300230050004b00000060000a00050000600600000b000000000008014000500000000000000b00602079400300000300b00b0000000b100000800001000a00a00010aa0000000000b0000000000000000000000000000b0b01000000000200000000000000000000030000700000b0000000000000000a0000b0000000000000020000b00a00010000000000000000300100000b00000000066001200b10000b400000107003b00000400800000005b90000000000020000510000000000006002300030020000b60300039000b0010100002000460000000000006b000003a000000300660704000002000400008000000a000820000270480b000000000320000000b0000000b00b00010000000a004000000000b01000030100000000000000a090000008000080000002000070000000070000000094b2000517000000004000000300000000000000b000000000000500b000003005a200000800000000000000000000018a000000000000008000b000060900000500020000001000100000000000000000000000007000000001608003000000000000000000b00008b000001000001600000000000000030000010000100010009b04000000000b30000310000000b0b00321020000500000a0a0000011b0a0000000001a030000b41000000a0000,0x600007000000000000000000000000000a000010a000000006003401000000000600000050000000600000000000000000000000000000000000000000000000000000100000000100000000a0000b0003000000002060000000b0b0000090b1702000002000a0020b0000000b00000b00a00b00120000001009000a0100001040010001000000006b000000000760b00003a3000000000000101000000b0411000100100000200b60000063480000000000800010b0000000000b00008800000000000b0000010000000000000b0000000000000000002000000000000000001000000000000030b00800000000000000070000000700000010000000000000003b00640000000000000006a00000000708110000007000000320a0b0080000000000000000a000000030100010b0a0000000420007390000020000a0010001000900020000803009b000040001071000040070b0401000000000008b00010a0060000000013001a000000000000000000020000020000000000010061206000000100030b0080007000000003000300500000900000000600000000000000000000006080000001b08000000110000000160202030071000000b0000010000000000b500000000006007007000000060006005800000000000000300005050000000000000b0000000080200080a000250000011b6000060000000300000a10000020000b0060195000b06a000b616000000076000b0000000000000a01000b00002004000b0b0a00000b000413000000000000301000000000000001020010000000000003a000b00000020300000b000000000002000000000000100000a0300050000200100900000000000000000004006000000000930020000000400020004b000100b0b600500b6000000000a000000b00040000008000000000a000000002003000000b0000000030000b0600000000000000b007000002000000000000000300000300400000000000b9000b000000000b000000000000800010000007007090000030800007800000000b000b2034000100008010004600000b00000000060000001ba00b00000b000000000000120000000000000000000000070b00000200b08070000000000000000000010000005b00000b300b000000000071000730b000000000000b0000030200000000000000000000a0030400200000000000802010000000000000207001050000000000000000020000100000100300a0000a0000000000002000b000000000000000000000b800a0001000000b0000b00000000000410000000b01026000008000020000000000000300b07003b00000b000690000000001000300000000010000100000000000000000000000000000017000400000020000000000a000000000000006080000000000000000b,0x1000300001010000070000b50a00000000016000306000000101700000000001b100000000000b0000000070002000000000000000b00000000000000206000000202000000038900700000920000000000000000000030039700000000630000410b00000000007000000000000403001000000000000000000003076000200400000000000000000001060a7b00100000000000000000b00000b3000000000010000800060000a0000500001000000900000100000050000b10037b0010000a000000090001000000000000100b0000000000000000000000000000000060000000007000030250000080000300000000000b00000100000000000b00000000090700011200000009000000000060000100a000000000000101000001000000000000a0000000800040002600100b00b00000500300000000000b200009001b0030100000060000000a0000000000000000000000b0a0ab100030020908040000000000a000007b0000008000b010b0200a8000000090800b00b2610000000000300000000000b07000a0600000000800060000009030050030003800000b0000000410200000000000600200b0000000000000000000b0900200aa000a00000083160032000406001000000000107a000000031000000600000000000006006b0000000000100000000300000900010a20016000100000010040800000006000820010400000100b00000300000b00000000000063701000100000322b0000000b00000000000000000081000000000000060390000000b00370990000000000000000000000000000100b080b000003000000000000000000000000000000000009000000a020011000026002000000000b00000000a00040010010040000b30000100762b00000000000000000000000000000000010000b000a20000000070000000020000600000000000000700000000a0a2003000600000000000704000b0810a720200000905000000060000000b00060000000000000001060000030100004000b0022000000000190b000000a070060b0000a00010700040000001000000700005030000000000000000011000000000000000020000000b0000101030000000100b0b80000030000020000a060a000000030b0000004801000010001000050001b7002900100b000100000000010800910b00000000000002005000000020000000b00003ba0400b00000030013000000000000b00000000000000b0000500000000080006090400000001000200000000000000000010000600000000000030000000000600000000000000000000008000000700200b000040000000000000000090000000000000060000010000000000a0000900000b0000000b000072100b00008b0000000b0400000010000000000b00000a000000900,0xa8600000000000000000000041000020a0000b0000b00b0a000b00000000000000a0000000100000bb00a0000000280bb0a000000b010003002000000100000100200100001020600100b00003a0000000000200203000b00b0000000000300000000a000000100000000000200110010700000000000000000000b00009000000000000b000000000b0000024000000000030b000000a1000000008b080b00b6b700300000a01010200a0b0020bb000000a00000000000000000000000000320000010b000000000021000b600b400000001000700003050009008000001b00000b00001a0a000000000100085700000060000070003b0700000bb00000000001000b000000021000000000000000000800000ba060000000070000020000b0000000000003000000000000070200760a00b600006060008000000010008300000000011406000000100a61000000000000002000010070b00040000010000060080000900000008000000b04002000000000003300000b000003000100003000000000000a0801b000000000010b000000000300110a0a0001500000007000000600000000000a00000b008000000200000000ab00010000400338000007530700700b000001000000000001009007000000000002005b0000000100000a5000b6000000001000009000000000000000000073000000000000000000000000180007b10010b00000a05403b0001000090020b00000000006b0000b0000a00b010000000000bb0b000b600070000b0000010020000300001000000400030b00201002600a900000000300b00000100000800000000006000200b000007000000000030058000030100021000000000ab0001000b06b0000000a00000062006000200000010000200000000000000001010a000000a00000500a04030000b00000000000000000047030070308000100000020000a04000000000000080000b3000000000000000000000000a0000a200000077000000060000000000800000b0000000000000000000000000000600010000050000003000800000a000008000000000000000000000000000110000b02000000b000000001000000000003b00100000000500000000000000000000000200000000b8020000080000b0000000000400000000b00000001000bb70000b0]
def a3sym (i : Nat) : Nat := a3symb0[i % 16]?.getD 0
def a3alias (i : Nat) := packedAt a3sym (i*4) 4
def a4symb0 : Array Nat := #[0xa001a000000000000b0000001000000000000000050000000000000000000a000000000b00b0000b0000001000000000000000060000000010000000000000010000000000000001000000510001000000000000a000000000000000000000000000001000001a000000000000400a0000000010b00100b0000b000000000000000000000000000b000000000000a000000a1001000000000000000a000002000000000000010100000000060000b0100100000000000000006000000000000b010000000000000000000a00000000000a00400000000000000b0010b000010000000b0b000100004000b00000000000a000001000000b0000a001000020000100000b01000000000000000000000000000000b000000b0000001000000400b0000080050000b000100000001100000000000001010000000000000b00000000000000000000000000000000000000b000000000000001000000004000000001000000000b000050000000000a00a010007000000000000000000b00000000001000000000000000000400000000000000000000001000000b000400000000300000000b0000001000000600050000000000000000000001b00a00000b004b00000000001000100001000000000b0000000000000b000000b000000000000000000000a00000000000000000000001000000b001a000002000500000010004000000003000b0bb000000000000001000000000a0000000000000a0a0000020bb00100000000000000000000000040000000000b0000000000000000400000001000010a01001000000000b00000001000000000100000000a00ab000b00000000001060a000000000000000000000b000000000040000000000010aa000000a00000000000001b00000100b000100000500000000000000010000000000000001000000000000a0a000000020000b0a0001000000000000000005ba40000050000010000000000040000000000000000010001000100b0000000000000000000000100a00000000000000000000400b000a0000b00a00000000000000a000000b000b0000000000900100000000b10000040051000000000000000000000000000000b00000000000000a00000000000000000000000000b0000000000401000000000000400000b0000b0000000000000000b00000000000000b0000000000b0000200000000000002000000000000000000000000000000001000000000000000000000b0000000400000000000000a000000000000100044000000000010b0b00000000000000000000a00000010000000000bb0000000000000000000000b0000a0000000000000000b000000000010b100000000000100000000000a0a0000b0000001000000000b000b0000000000a00000000000000,0xb000b0000000101002000000050000000001000000000000000000000000100050000000000000000b050000001000000000b0000000a00010000000000000b00000000000000000000000000010000000000100b000000000000000000000000000400000000b00005000000000001000000a010000000000000000000000000000000000000000b00000000000b000000000b00000000000001000000000000010000000000000000aa00000000001101450b540000001000b000000b000000b00b00000000000b000000b0000001000000000000b00500000000000001000000000000000000000007000000000000000000000000000b00001000b0000000000000000000b0b0001000000b04100000000000000000000400a00b00a0000000000b00001000000b0000000000010000a00000000000000000000000000000000000001000000b0b000000000000000000000000000000000000a0b00000000001000001000000000000000b0000000000000000000100000000000000000200000000004000000001b0000000000001000000000000000000010000000010000020000a0400000020000b00000010b00000000000000004000000000000010b000000000000200000000000000000100000040000000000100000040000000000000010000000010000000b000000000000b000000000010b00a00000000000000000005000000000000002050000000001a00000000000b000a0b00b000000000000a00000000000000000000000000000b00000000000010020000b0000002000100000000000000b20000000020100000000000400000000000100000100000000000001000000000a000000000000000000000000000000100000000a00000000000000000010000000100000000000000000000b00010000000110000000000000b0040000002000001000000b0000000000000000000000000b000000000000400510000040000000000000b0000000000000b000b00000000000000000000000100b00001000000a00004000020b0000020000000000000000000000000a000010000a000000000000000000000000001500b0b0000000000010050450000000b00000b000000000000000000000010000000000000b0000a000020a0000000a0000000000000a000000000001000a000000000000000a000001b00000000000a000000000000000000000000000000000000b000000b000000000000000020400000000000b000000000000a0000000000b0100020a0000000000000000500000000011000000a40000000000000000b000000000a00000100000000000000000400000004000000a00000000b00000000000000b000000000000000a0b01000000005000000000000000001000000000000000001050000000,0x500000500000000000000000000005000000a0000010000b00b000000100000a600000100000b00000000000a000000000005000000000b010b010000000010a00000b0000001b0a0000000000b0000000000000500100010b000a00500000000000b00000000b0000010000000b0000000000000a00000000b000000000000a000b0000000000000b000000002000000000b01000105000200001b001b000000000000000001000000b000000b000000000000000000000a0000011000000b000000a0000000001000b000000b000400050400000000000000000000b0000000000000000000101000a0000000000b010b]
def a4sym (i : Nat) : Nat := a4symb0[i % 16]?.getD 0
def a4alias (i : Nat) := packedAt a4sym (i*4) 4
def a5symb0 : Array Nat := #[0xb0010000000000000000000a000a0000000000000000000000000000b000010001000000000000000000000a0a00000a4b00b000000000a0000000000000000b000000000000000000000000000010000000]
def a5sym (i : Nat) : Nat := a5symb0[i % 16]?.getD 0
def a5alias (i : Nat) := packedAt a5sym (i*4) 4

abbrev Memo := Sig × Nat × Nat × List Sig × List Sig

def memo (ws : List Decor) (k : Nat) (p : BoundPool) : Memo :=
  let d := p.domain
  let av := p.wires.map (masked d)
  let clean := fun (w : Sig) => let y := masked d w
                                y==zero || y==d || av.contains y
  (d,k+p.paid,p.bound+ws.countP (fun w => isMaskedConstant d w.1),
    av,(ws.map Prod.fst).filter (fun w => !(clean w)))

def worth2303 (cap n : Nat) (cov : CovPair) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>cap then false else
  let d := len==cap
  (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) == BitVec.allOnes 768

abbrev Ax2303 := Decor × Decor

abbrev Four := Nat × Nat × Nat × Nat

def couples : List Decor → List Ax2303
  | [] => []
  | a::l => l.map (fun b => (a,b)) ++ couples l

def liftSig (w : Sig) : Bits := BitVec.ofNat 768 w.toNat

def laneEq (r full a b : Nat) := fullMarks r (full ^^^ (a ^^^ b))

def zeroFour (x : Four) := (x.1 ||| x.2.1 ||| x.2.2.1 ||| x.2.2.2)==0

def wideWorth (n cap op r full : Nat) (v : CovPair) (a b : PackedSig) (ka kb : Bool) :=
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>cap then 0 else
  let d := len==cap
  let c := getCov v d
  let cover : PackedCov := (r*c.1.toNat,r*c.2.1.toNat,r*c.2.2.toNat)
  fullMarks r (takePacked cover (packedColumn d a) (packedColumn d b) un ka kb |||
    packedColumn d (packedOp full op a b))

def include2303 (r full z : Nat) (wires : List Sig) (seen : Nat) :=
  wires.foldl (fun m w => m ||| laneEq r full z (r*w.toNat)) seen

def maskKeep (r full a b : Nat) (un ka kb : Bool) (miss : List Sig) :=
  miss.foldl (fun m w =>
    let target := r*w.toNat
    m &&& ((if ka then 0 else laneEq r full a target) |||
      (if un || kb then 0 else laneEq r full b target))) r

def shade2303 (r cost top cv free : Nat) (ready : Bool) (loss : Nat) :=
  if ready && cost+loss+1<top then r else
  if cost+loss<top then free else if cost+loss==top then cv else 0

def wideRule (r full a b z : Nat) (un : Bool) (ps : Memo) (todo : Four) : Four :=
  let (dom,cost,top,av,miss) := ps
  if cost>=top+1 || miss.length>(if un then 1 else 2) then todo else
  let d := r*dom.toNat
  let cm := fun m => laneEq r full m 0 ||| laneEq r full m d
  let zm := z &&& d
  let cz := cm zm
  let free := include2303 r full zm av cz
  let shade := shade2303 r cost top cz free miss.isEmpty
  let ca := cm (a &&& d)
  let cb := cm (b &&& d)
  let step := fun (t : Nat) (ka kb : Bool) =>
    if t==0 then 0 else
    let ca := if ka then 0 else ca
    let cb := if un || kb then 0 else cb
    let kill := (((r ^^^ (ca ||| cb)) &&& shade 0) |||
      ((ca ^^^ cb) &&& shade 1) ||| ((ca &&& cb) &&& shade 2)) &&&
      maskKeep r full a b un ka kb miss
    t ^^^ (t &&& kill)
  (step todo.1 false false,step todo.2.1 true false,step todo.2.2.1 false true,step todo.2.2.2 true true)

def wideRules (r full a b z : Nat) (un : Bool) (todo : Four) : List Memo → Four
  | [] => todo
  | p::ps => if zeroFour todo then todo else wideRules r full a b z un (wideRule r full a b z un p todo) ps

lemma keyFold (ws : List Sig) (c : Nat) :
    ws.foldl (fun v w => v+keyWord w) c=c+(ws.map keyWord).sum := by
  induction ws generalizing c with
  | nil => simp
  | cons w l ih => simp [ih,Nat.add_assoc]
lemma keySum (ws : List Sig) : keySet ws=(ws.map keyWord).sum := by
  simp [keySet,keyFold]
lemma keyPerm {ws vs : List Decor} (h : ws.Perm vs) :
    keySet (ws.map Prod.fst)=keySet (vs.map Prod.fst) := by
  rw [keySum,keySum]
  exact ((h.map Prod.fst).map keyWord).sum_eq
lemma keyCons (a : Sig) (ws : List Sig) : keySet (a::ws)=keyWord a+keySet ws := by
  simp [keySum]
def deltaKey (total : Nat) (a b z : Sig) (un ka kb : Bool) :=
  total+keyWord z-(if ka then 0 else keyWord a)-(if un || kb then 0 else keyWord b)
lemma deltaKey_ok {ws : List Decor} {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (un ka kb : Bool) (ne : un=false → a≠b) (z : Sig) :
    deltaKey (keySet (ws.map Prod.fst)) a.1 b.1 z un ka kb =
      keySet (z::(opKeep un ka kb a b ws).map Prod.fst) := by
  have first := keyPerm (delOne_perm a ha)
  have second := keyPerm (delOne_perm b hb)
  simp only [List.map_cons,keyCons] at first second
  cases un
  · have both := keyPerm (delTwo_perm a b ha hb (ne rfl))
    simp only [List.map_cons,keyCons] at both
    cases ka <;> cases kb <;>
      simp only [deltaKey,opKeep,delOne,delTwo,Bool.false_or,Bool.false_eq_true,
        ite_false,ite_true,keyCons] <;> omega
  · cases ka <;> cases kb <;>
      simp only [deltaKey,opKeep,delOne,Bool.true_or,Bool.false_eq_true,ite_false,
        ite_true,keyCons] <;> omega

def linked (ws : List Decor) (links : Nat → List (List Sig)) (a b : Decor) (w : Sig)
    (un ka kb : Bool) :=
  let other := (opKeep un ka kb a b ws).map Prod.fst
  let st := w::other
  let tag := if un || a.1!=b.1 then deltaKey (keySet (ws.map Prod.fst)) a.1 b.1 w un ka kb else keySet st
  (links tag).any (fun v => v==other++[w] || sameWords st v)

lemma linked_ok {ws links a b w un ka kb} (ha : a∈ws) (hb : b∈ws)
    (ok : linked ws links a b w un ka kb=true) :
    let st := w::(opKeep un ka kb a b ws).map Prod.fst
    (links (keySet st)).any (sameWords st)=true := by
  let rest := (opKeep un ka kb a b ws).map Prod.fst
  have key : (if un || a.1!=b.1 then deltaKey (keySet (ws.map Prod.fst)) a.1 b.1 w un ka kb
        else keySet (w::rest))=keySet (w::rest) := by
    split
    next h =>
      apply deltaKey_ok ha hb
      intro hu eq
      simp [hu,eq] at h
    next => rfl
  change (links _).any (fun v => v==rest++[w] || sameWords (w::rest) v)=true at ok
  rw [key] at ok
  obtain ⟨v,vm,hit⟩ := List.any_eq_true.mp ok
  refine List.any_eq_true.mpr ⟨v,vm,?_⟩
  simp only [Bool.or_eq_true] at hit
  rcases hit with eq | yes
  · rw [beq_iff_eq.mp eq]
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    exact ⟨fun _ e => e.symm,fun _ e => e.symm⟩
  · exact yes

def wideFamily (c : NodeContext) (ps : List Memo) (op : Nat) (ops : List Ax2303) :=
  let (cap,n,ws,cov,_,links) := c
  let r := units ops.length
  let full := r*(BitVec.allOnes 768).toNat
  let sa := packedSig (fun e : Ax2303 => e.1.2) ops
  let sb := packedSig (fun e : Ax2303 => e.2.2) ops
  let a := combineLanes (fun e : Ax2303 => liftSig e.1.1) ops
  let b := combineLanes (fun e : Ax2303 => liftSig e.2.1) ops
  let un := op==2
  let z := if un then (r*one.toNat) ^^^ a else if op==1 then a ||| b else a &&& b
  let worth := wideWorth n cap op r full cov sa sb
  let todo : Four := (worth false false,if un then 0 else worth true false,
                       if un then 0 else worth false true,worth true true)
  let left := wideRules r full a b z un todo ps
  let verify := fun (ka kb : Bool) (t : Nat) => if t==0 then true else
    onMarks (fun e : Ax2303 =>
      let w := (movedDecor op e.1 e.2).1
      if !properB w || ws.any (fun v => v.1==w) then true else
      linked ws links e.1 e.2 w un ka kb) t ops
  verify false false left.1 && verify true false left.2.1 &&
    verify false true left.2.2.1 && verify true true left.2.2.2

def wideNode (c : NodeContext) :=
  let ws := c.2.2.1
  let ss := c.2.2.2.2.1.map (memo ws (c.1-1))
  let bs := couples ws
  prelim graph c && wideFamily c ss 2 (ws.map fun a => (a,a)) &&
    wideFamily c ss 0 bs && wideFamily c ss 1 bs

lemma xorHit (a b : Bits) :
    (BitVec.allOnes 768 ^^^ (a ^^^ b) == BitVec.allOnes 768) = (a==b) := by
  by_cases eq : a=b
  · simp [eq]
  · rw [beq_eq_false_iff_ne.mpr eq]
    apply beq_eq_false_iff_ne.mpr
    intro h
    apply eq
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have v := congrArg (fun x : Bits => x.getLsbD j) h
    simp only [BitVec.getLsbD_xor,BitVec.getLsbD_allOnes,hj,decide_true] at v
    cases ha : a.getLsbD j <;> cases hb : b.getLsbD j <;> simp_all

lemma eqLanes {α} (a b : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (laneEq (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes a xs) (combineLanes b xs)).testBit (769*i) = (a xs[i] == b xs[i]) := by
  simp only [laneEq,broadcast,lanes_xor,mark_at _ _ _ hi,xorHit]

lemma liftEq (a b : Sig) : (liftSig a==liftSig b)=(a==b) := by
  by_cases e : a=b
  · simp [e]
  · have neq : liftSig a≠liftSig b := by
      intro h
      have H := congrArg BitVec.toNat h
      have la : a.toNat<2^768 := lt_trans a.isLt (by decide +kernel)
      have lb : b.toNat<2^768 := lt_trans b.isLt (by decide +kernel)
      apply e
      apply BitVec.eq_of_toNat_eq
      simpa [liftSig,Nat.mod_eq_of_lt la,Nat.mod_eq_of_lt lb] using H
    simp [neq,e]

lemma lift_toNat (a : Sig) : (liftSig a).toNat=a.toNat := by
  have lt : a.toNat<2^768 := lt_trans a.isLt (by decide +kernel)
  simp [liftSig,Nat.mod_eq_of_lt lt]

lemma bitEqConst {α} (a : α → Sig) (v : Sig) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (laneEq (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes (fun x => liftSig (a x)) xs) (units xs.length*v.toNat)).testBit (769*i) =
      (a xs[i]==v) := by
  rw [←lift_toNat v,broadcast (liftSig v) xs,eqLanes _ _ _ _ hi,liftEq]

lemma worthAt (n cap op : Nat) (v : CovPair) (xs : List Ax2303) (i : Nat) (hi : i<xs.length)
    (ka kb : Bool) :
    (wideWorth n cap op (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat) v
      (packedSig (fun e : Ax2303 => e.1.2) xs) (packedSig (fun e : Ax2303 => e.2.2) xs)
      ka kb).testBit (769*i) =
      worth2303 cap n v op xs[i].1 xs[i].2 (movedDecor op xs[i].1 xs[i].2) ka kb := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  by_cases big : len>cap
  · simp only [wideWorth,worth2303,show 1+(n-(if ka then 0 else 1)-
        (if (op==2) || kb then 0 else 1))>cap from big,ite_true,Nat.zero_testBit]
  · let d := len==cap
    simp only [wideWorth,worth2303,show ¬1+(n-(if ka then 0 else 1)-
        (if (op==2) || kb then 0 else 1))>cap from big,ite_false]
    have cp : (units xs.length*(getCov v d).1.toNat,units xs.length*(getCov v d).2.1.toNat,
        units xs.length*(getCov v d).2.2.toNat) =
        packedCov (fun _ : Ax2303 => getCov v d) xs := by simp only [packedCov,broadcast]
    rw [cp,packed_op (fun e : Ax2303 => e.1) (fun e : Ax2303 => e.2),packed_column,
        packed_column,packed_column,takePacked_ok,lanes_or,mark_at _ _ _ hi]

lemma includeBit {α} (f : α → Sig) (vs : List Sig) (xs : List α) (i) (hi : i<xs.length)
    (seen : Nat) :
    (include2303 (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes (fun x => liftSig (f x)) xs) vs seen).testBit (769*i) =
    (seen.testBit (769*i) || vs.any (fun w => f xs[i]==w)) := by
  induction vs generalizing seen with
  | nil => simp [include2303]
  | cons w l ih =>
    change (include2303 _ _ _ l _).testBit _ = _
    rw [ih,Nat.testBit_or,bitEqConst _ _ _ _ hi,List.any_cons,Bool.or_assoc]

lemma keepBit (xs : List Ax2303) (i) (hi : i<xs.length) (miss : List Sig) (un ka kb : Bool) :
    (maskKeep (units xs.length) (units xs.length*(BitVec.allOnes 768).toNat)
      (combineLanes (fun e : Ax2303 => liftSig e.1.1) xs)
      (combineLanes (fun e : Ax2303 => liftSig e.2.1) xs) un ka kb miss).testBit (769*i) =
      miss.all (fun w => (!ka && (xs[i].1.1==w)) || (!(un || kb) && (xs[i].2.1==w))) := by
  let r := units xs.length
  let full := r*(BitVec.allOnes 768).toNat
  let a := combineLanes (fun e : Ax2303 => liftSig e.1.1) xs
  let b := combineLanes (fun e : Ax2303 => liftSig e.2.1) xs
  let f := fun (w : Sig) => (if ka then 0 else laneEq r full a (r*w.toNat)) |||
       (if un || kb then 0 else laneEq r full b (r*w.toNat))
  have get (w) : (f w).testBit (769*i)=
      ((!ka && (xs[i].1.1==w)) || (!(un || kb) && (xs[i].2.1==w))) := by
    cases ka <;> cases un <;> cases kb <;>
      simp only [f,r,full,a,b,Nat.testBit_or,bitEqConst _ _ _ _ hi,
        Bool.false_eq_true,ite_false,ite_true,Bool.false_or,Bool.true_or,
        Nat.zero_testBit,Bool.not_true,Bool.not_false,Bool.false_and,Bool.true_and]
  have aux (l : List Sig) (m : Nat) : (l.foldl (fun q w => q &&& f w) m).testBit (769*i)=
      (m.testBit (769*i) && l.all fun w => (!ka && (xs[i].1.1==w)) || (!(un || kb) && (xs[i].2.1==w))) := by
    induction l generalizing m with
    | nil => simp
    | cons w l ih => rw [List.foldl_cons,ih,Nat.testBit_and,get,List.all_cons,Bool.and_assoc]
  exact (aux miss r).trans (by simp [r,unit_bit _ _ hi])

lemma liftedAnd (a b : Sig) : liftSig (a &&& b) = liftSig a &&& liftSig b := by
  apply BitVec.eq_of_toNat_eq
  simp only [lift_toNat,BitVec.toNat_and]

lemma liftedOr (a b : Sig) : liftSig (a ||| b) = liftSig a ||| liftSig b := by
  apply BitVec.eq_of_toNat_eq
  simp only [lift_toNat,BitVec.toNat_or]

lemma liftedNeg (a : Sig) : liftSig (neg a) = liftSig one ^^^ liftSig a := by
  have eq : neg a=one ^^^ a := BitVec.allOnes_xor.symm
  apply BitVec.eq_of_toNat_eq
  simp only [eq,lift_toNat,BitVec.toNat_xor]

lemma maskedLanes {α} (a : α → Sig) (xs : List α) (d : Sig) :
    combineLanes (fun x => liftSig (a x)) xs &&& (units xs.length*d.toNat) =
      combineLanes (fun x => liftSig (masked d (a x))) xs := by
  rw [←lift_toNat d,broadcast (liftSig d) xs,lanes_and]
  simp only [masked,liftedAnd,BitVec.and_comm]

lemma opLanes (xs : List Ax2303) (op : Nat) :
    let a := combineLanes (fun e : Ax2303 => liftSig e.1.1) xs
    let b := combineLanes (fun e : Ax2303 => liftSig e.2.1) xs
    (if op==2 then (units xs.length*one.toNat) ^^^ a else if op==1 then a ||| b else a &&& b) =
      combineLanes (fun e : Ax2303 => liftSig (movedDecor op e.1 e.2).1) xs := by
  by_cases un : op=2
  · simp only [un,beq_self_eq_true,ite_true,movedDecor,codeDecor,dneg,liftedNeg]
    rw [←lift_toNat one,broadcast (liftSig one) xs,lanes_xor]
  · have ne : (op==2)=false := beq_eq_false_iff_ne.mpr un
    cases b : op==1 <;>
      simp only [ne,Bool.false_eq_true,ite_false,b,ite_true,movedDecor,codeDecor,un,dbin,bin,
        liftedOr,liftedAnd,lanes_or,lanes_and]

def absent (p : BoundPool) (ws : List Decor) :=
  (ws.map Prod.fst).filter (fun w => !availableB p.domain p.wires w)

def payable (cost top : Nat) (zc free ready : Bool) (loss : Nat) :=
  if ready && cost+loss+1<top then true else
  if cost+loss<top then free else if cost+loss==top then zc else false

lemma scalar_fast {p : BoundPool} {ws : List Decor} {k op a b ka kb}
    (nd : (ws.map Prod.fst).Nodup) (ha : a∈ws) (hb : b∈ws)
    (keep : (absent p ws).all (fun w =>
      (!ka && (a.1==w)) || (!((op==2) || kb) && (b.1==w)))=true)
    (test : let const := fun w : Decor => isMaskedConstant p.domain w.1
      let z := choiceVal (movedChoice op a b)
      payable (k+p.paid) (p.bound+ws.countP const) (isMaskedConstant p.domain z)
        (availableB p.domain p.wires z) (absent p ws).isEmpty
        (constantLoss const a ka+constantLoss const b ((op==2)||kb))=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let rest := opKeep (op==2) ka kb a b ws
  let miss := absent p ws
  let loss := constantLoss const a ka+constantLoss const b ((op==2)||kb)
  have failed {v} (hm : v∈ws.map Prod.fst) (no : availableB p.domain p.wires v=false) : v∈miss := by
    simpa [miss,absent,List.mem_filter,hm,no]
  have known : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro v vm
    obtain ⟨member,ia,ib⟩ := (kept_value nd ha hb (op==2) ka kb v).mp vm
    cases ev : availableB p.domain p.wires v
    · have bad := List.all_eq_true.mp keep v (failed member ev)
      simp only [Bool.or_eq_true,Bool.and_eq_true] at bad
      rcases bad with ⟨no,eq⟩ | ⟨no,eq⟩
      ·
        have vv : v=a.1 := (beq_iff_eq.mp eq).symm
        exact False.elim (by rcases ia with noeq|on <;> simp_all)
      ·
        have vv : v=b.1 := (beq_iff_eq.mp eq).symm
        exact False.elim (by rcases ib with on|noeq|on <;> simp_all)
    · rfl
  have all_of_empty (empty : miss.isEmpty=true) (w) (hm : w∈ws) :
      availableB p.domain p.wires w.1=true := by
    cases ev : availableB p.domain p.wires w.1
    · have bad := failed (List.mem_map_of_mem (f:=Prod.fst) hm) ev
      have nil : miss=[] := List.isEmpty_iff.mp empty
      rw [nil] at bad
      contradiction
    · rfl
  have counts := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2)||kb)
        ≤ rest.countP const at counts
  have mass : ws.countP const ≤ rest.countP const+loss := by dsimp [loss]; omega
  change payable (k+p.paid) (p.bound+ws.countP const) (isMaskedConstant p.domain z)
    (availableB p.domain p.wires z) miss.isEmpty loss=true at test
  unfold payable at test
  have cheap : k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+rest.countP const+(isMaskedConstant p.domain z).toNat := by
    split at test
    next h =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h
      have le := h.2
      cases availableB p.domain p.wires z <;> cases isMaskedConstant p.domain z <;> simp <;> omega
    next =>
      split at test
      next le => simp [test]; omega
      next =>
        split at test
        next eq =>
          have e := beq_iff_eq.mp eq
          have av : availableB p.domain p.wires z=true :=
            by simp only [availableB,isMaskedConstant,Bool.or_eq_true] at test ⊢; tauto
          simp [av,test]; omega
        next => contradiction
  have buy : (!(!availableB p.domain p.wires z) || choiceOK p.domain p.wires (movedChoice op a b))=true := by
    cases az : availableB p.domain p.wires z
    · have zc : isMaskedConstant p.domain z=false := by
        have ac := az
        change (isMaskedConstant p.domain z || _) = false at ac
        simp only [Bool.or_eq_false_iff] at ac
        exact ac.1
      have empty : miss.isEmpty=true := by
        cases m : miss.isEmpty
        · simp [payable,az,zc,m] at test
        · rfl
      have all := all_of_empty empty
      simp [choiceOK,movedChoice,all _ ha,all _ hb]
    · simp
  simpa only [scalarPoolCut,z,rest,known,Bool.and_true,Bool.true_and,Bool.and_eq_true,
    decide_eq_true_eq,List.countP_cons,List.countP_map,Function.comp_def,
    show (if isMaskedConstant p.domain z then 1 else 0)=(isMaskedConstant p.domain z).toNat by cases isMaskedConstant p.domain z <;> rfl,
    Nat.add_assoc] using And.intro cheap buy

def partFour (x : Four) (ka kb : Bool) :=
  if ka then (if kb then x.2.2.2 else x.2.1) else (if kb then x.2.2.1 else x.1)

lemma shadeAt {r i cost top cz free ready loss} (unit : r.testBit i=true) :
    (shade2303 r cost top cz free ready loss).testBit i =
      payable cost top (cz.testBit i) (free.testBit i) ready loss := by
  simp only [shade2303,payable]
  repeat' split
  all_goals first | assumption | rfl | exact Nat.zero_testBit _

lemma chosenShade {r i a b s t u : Nat} (unit : r.testBit i=true) :
    ((((r ^^^ (a ||| b)) &&& s) ||| ((a ^^^ b) &&& t) ||| ((a &&& b) &&& u)).testBit i) =
    (if a.testBit i then (if b.testBit i then u.testBit i else t.testBit i)
     else if b.testBit i then t.testBit i else s.testBit i) := by
  simp only [Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,unit]
  cases a.testBit i <;> cases b.testBit i <;> simp

lemma killedBit {t k i : Nat} (start : t.testBit i=true)
    (finish : (t ^^^ (t &&& k)).testBit i=false) : k.testBit i=true := by
  simpa [Nat.testBit_xor,Nat.testBit_and,start] using finish

lemma dropLoss (const : Decor → Bool) (w : Decor) (keep : Bool) :
    constantLoss const w keep = (if keep then false else const w).toNat := by
  cases keep <;> rfl

abbrev lanes {α} (f : α → Sig) (xs : List α) := combineLanes (fun x => liftSig (f x)) xs

def constantMask (r full x d : Nat) := laneEq r full x 0 ||| laneEq r full x d

lemma wireEqSym (a b : Sig) : (a==b)=(b==a) := by
  by_cases h : a=b
  · simp [h]
  · simp [h,Ne.symm h]

lemma constantAt {α} (f : α → Sig) (xs : List α) (i : Nat) (hi : i<xs.length) (d : Sig) :
    let r := units xs.length
    (constantMask r (r*(BitVec.allOnes 768).toNat) (lanes f xs &&& (r*d.toNat))
        (r*d.toNat)).testBit (769*i) = isMaskedConstant d (f xs[i]) := by
  dsimp only
  have z : units xs.length*zero.toNat=0 := by simp [zero]
  simp only [constantMask,Nat.testBit_or,maskedLanes,←z,bitEqConst _ _ _ _ hi,isMaskedConstant]

lemma freeAt {α} (f : α → Sig) (xs : List α) (i : Nat) (hi : i<xs.length)
    (d : Sig) (vs : List Sig) :
    let r := units xs.length
    let full := r*(BitVec.allOnes 768).toNat
    let zm := lanes f xs &&& (r*d.toNat)
    (include2303 r full zm (vs.map (masked d)) (constantMask r full zm (r*d.toNat))).testBit (769*i) =
      availableB d vs (f xs[i]) := by
  dsimp only
  let r := units xs.length
  let full := r*(BitVec.allOnes 768).toNat
  let zm := lanes f xs &&& (r*d.toNat)
  have I := includeBit (fun x => masked d (f x)) (vs.map (masked d)) xs i hi
    (constantMask r full zm (r*d.toNat))
  rw [←maskedLanes] at I
  refine I.trans ?_
  rw [show (constantMask r full zm (r*d.toNat)).testBit (769*i)=isMaskedConstant d (f xs[i]) from constantAt f xs i hi d]
  simp only [isMaskedConstant,availableB,List.any_map,Function.comp_def]
  congr 1
  congr 1
  funext v
  exact wireEqSym _ _

lemma memoAbsent (ws : List Decor) (k : Nat) (p : BoundPool) :
    (memo ws k p).2.2.2.2=absent p ws := by
  simp only [memo,absent,availableB]
  congr 1
  funext w
  congr 1
  have same (l : List Sig) (w : Sig) : l.contains w=l.any (fun v => v==w) := by
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.contains_cons,List.any_cons,ih,wireEqSym w a]
  simp only [same]

lemma partStep (todo : Four) (step : Nat → Bool → Bool → Nat) (ka kb : Bool) :
    partFour (step todo.1 false false,step todo.2.1 true false,
      step todo.2.2.1 false true,step todo.2.2.2 true true) ka kb =
      step (partFour todo ka kb) ka kb := by cases ka <;> cases kb <;> rfl

lemma killedRule {p : BoundPool} {ws : List Decor} {k op : Nat} (xs : List Ax2303)
    (i : Nat) (hi : i<xs.length) (ka kb : Bool) (todo : Four)
    (nd : (ws.map Prod.fst).Nodup) (ha : xs[i].1∈ws) (hb : xs[i].2∈ws)
    (beginning : (partFour todo ka kb).testBit (769*i)=true) :
    let r := units xs.length
    let full := r*(BitVec.allOnes 768).toNat
    let a := lanes (fun e : Ax2303 => e.1.1) xs
    let b := lanes (fun e : Ax2303 => e.2.1) xs
    let z := lanes (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs
    let cut := wideRule r full a b z (op==2) (memo ws k p) todo
    (partFour cut ka kb).testBit (769*i)=false →
      scalarPoolCut p k ((opKeep (op==2) ka kb xs[i].1 xs[i].2 ws).map Prod.fst)
        (movedChoice op xs[i].1 xs[i].2)=true := by
  let r := units xs.length
  let full := r*(BitVec.allOnes 768).toNat
  let a := lanes (fun e : Ax2303 => e.1.1) xs
  let b := lanes (fun e : Ax2303 => e.2.1) xs
  let z := lanes (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs
  let const := fun v : Decor => isMaskedConstant p.domain v.1
  let dom := r*p.domain.toNat
  let am := constantMask r full (a &&& dom) dom
  let bm := constantMask r full (b &&& dom) dom
  let zm := constantMask r full (z &&& dom) dom
  let av := p.wires.map (masked p.domain)
  let fm := include2303 r full (z &&& dom) av zm
  let miss := absent p ws
  let sel := maskKeep r full a b (op==2) ka kb miss
  let sh := shade2303 r (k+p.paid) (p.bound+ws.countP const) zm fm miss.isEmpty
  let aa := if ka then 0 else am
  let bb := if (op==2)||kb then 0 else bm
  let kill := ((((r ^^^ (aa ||| bb)) &&& sh 0) ||| ((aa ^^^ bb) &&& sh 1) ||| ((aa &&& bb) &&& sh 2)) &&& sel)
  let step := fun (v : Nat) (x y : Bool) =>
    if v==0 then 0 else
      let ax := if x then 0 else am
      let bx := if (op==2)||y then 0 else bm
      let kx := ((((r ^^^ (ax ||| bx)) &&& sh 0) ||| ((ax ^^^ bx) &&& sh 1) ||| ((ax &&& bx) &&& sh 2)) &&&
        maskKeep r full a b (op==2) x y miss)
      v ^^^ (v &&& kx)
  let t := partFour todo ka kb
  have unit : r.testBit (769*i)=true := unit_bit xs.length i hi
  have ca : am.testBit (769*i)=const xs[i].1 := constantAt (fun e : Ax2303 => e.1.1) xs i hi _
  have cb : bm.testBit (769*i)=const xs[i].2 := constantAt (fun e : Ax2303 => e.2.1) xs i hi _
  have cz : zm.testBit (769*i)=isMaskedConstant p.domain (choiceVal (movedChoice op xs[i].1 xs[i].2)) :=
    (constantAt (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs i hi _).trans (by rw [moved_full])
  have free : fm.testBit (769*i)=availableB p.domain p.wires (choiceVal (movedChoice op xs[i].1 xs[i].2)) :=
    (freeAt (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs i hi _ _).trans (by rw [moved_full])
  have lose (n) : (sh n).testBit (769*i)=payable (k+p.paid) (p.bound+ws.countP const)
      (isMaskedConstant p.domain (choiceVal (movedChoice op xs[i].1 xs[i].2)))
      (availableB p.domain p.wires (choiceVal (movedChoice op xs[i].1 xs[i].2))) miss.isEmpty n := by
    rw [show (sh n).testBit (769*i)=_ from shadeAt unit,cz,free]
  have amount (w sw : Nat) (flag : Bool) (prop : Bool) (e : sw.testBit (769*i)=prop) :
      (if flag then 0 else sw).testBit (769*i)=(if flag then false else prop) := by
    cases flag <;> simp [e]
  have notzero : t≠0 := by intro h; have := beginning; change t.testBit _=true at this; simp [h] at this
  dsimp only
  have memoE : memo ws k p=(p.domain,k+p.paid,p.bound+ws.countP const,av,miss) :=
    congrArg (fun v => (p.domain,k+p.paid,p.bound+ws.countP const,av,v)) (memoAbsent ws k p)
  rw [memoE]
  dsimp only [wideRule]
  by_cases skip : (decide (k+p.paid≥p.bound+ws.countP const+1) || decide (miss.length>(if op==2 then 1 else 2)))=true
  · rw [if_pos skip]
    intro f; exact False.elim (Bool.noConfusion (beginning.symm.trans f))
  · rw [if_neg skip]
    change (partFour (step todo.1 false false,step todo.2.1 true false,
      step todo.2.2.1 false true,step todo.2.2.2 true true) ka kb).testBit (769*i)=false → _
    rw [partStep todo step ka kb]
    change (if t==0 then 0 else t ^^^ (t &&& kill)).testBit (769*i)=false → _
    simp only [beq_eq_false_iff_ne.mpr notzero,Bool.false_eq_true,ite_false]
    intro h
    have v := killedBit beginning h
    change ( _ &&& sel).testBit (769*i)=true at v
    simp only [Nat.testBit_and,Bool.and_eq_true] at v
    have yes : sel.testBit (769*i)=true := v.2
    rw [show sel.testBit (769*i)=_ from keepBit xs i hi miss (op==2) ka kb] at yes
    apply scalar_fast nd ha hb yes
    have pick := v.1
    rw [chosenShade unit,amount 0 am ka _ ca,amount 0 bm ((op==2)||kb) _ cb] at pick
    simp only [lose] at pick
    have clear (f : Nat → Bool) (u v : Bool)
        (eq : (if u then (if v then f 2 else f 1) else if v then f 1 else f 0)=true) :
        f (u.toNat+v.toNat)=true := by cases u <;> cases v <;> exact eq
    dsimp only
    simp only [dropLoss]
    exact clear _ (if ka then false else const xs[i].1) (if (op==2)||kb then false else const xs[i].2) pick

abbrev wideArgs (xs : List Ax2303) (op : Nat) :=
  (units xs.length,units xs.length*(BitVec.allOnes 768).toNat,
    lanes (fun e : Ax2303 => e.1.1) xs,lanes (fun e : Ax2303 => e.2.1) xs,
    lanes (fun e : Ax2303 => (movedDecor op e.1 e.2).1) xs)

def runRules (xs : List Ax2303) (op : Nat) (todo : Four) (ps : List Memo) :=
  let (r,full,a,b,z) := wideArgs xs op
  wideRules r full a b z (op==2) todo ps

def runRule (xs : List Ax2303) (op : Nat) (todo : Four) (p : Memo) :=
  let (r,full,a,b,z) := wideArgs xs op
  wideRule r full a b z (op==2) p todo

lemma finishedRule {ps : List BoundPool} {ws : List Decor} {k op : Nat}
    (xs : List Ax2303) (i : Nat) (hi : i<xs.length) (ka kb : Bool) (todo : Four)
    (nd : (ws.map Prod.fst).Nodup) (ha : xs[i].1∈ws) (hb : xs[i].2∈ws)
    (beginning : (partFour todo ka kb).testBit (769*i)=true)
    (done : (partFour (runRules xs op todo (ps.map (memo ws k))) ka kb).testBit (769*i)=false) :
    ∃ p∈ps, scalarPoolCut p k ((opKeep (op==2) ka kb xs[i].1 xs[i].2 ws).map Prod.fst)
      (movedChoice op xs[i].1 xs[i].2)=true := by
  induction ps generalizing todo with
  | nil => exact False.elim (Bool.noConfusion (beginning.symm.trans done))
  | cons p ps ih =>
    let next := runRule xs op todo (memo ws k p)
    change (partFour (if zeroFour todo then todo else runRules xs op next (ps.map (memo ws k))) ka kb).testBit (769*i)=false at done
    split at done
    next => exact False.elim (Bool.noConfusion (beginning.symm.trans done))
    next =>
      cases he : (partFour next ka kb).testBit (769*i)
      · exact ⟨p,by simp,killedRule xs i hi ka kb todo nd ha hb beginning he⟩
      · obtain ⟨v,vm,cut⟩ := ih next he done
        exact ⟨v,List.mem_cons_of_mem _ vm,cut⟩

def familyCheck (c : NodeContext) (op : Nat) (e : Ax2303) (ka kb : Bool) :=
  let w := (movedDecor op e.1 e.2).1
  if !properB w || c.2.2.1.any (fun v => v.1==w) then true else
  linked c.2.2.1 c.2.2.2.2.2 e.1 e.2 w (op==2) ka kb

def todo2303 (c : NodeContext) (op : Nat) (xs : List Ax2303) : Four :=
  let r := units xs.length
  let f := wideWorth c.2.1 c.1 op r (r*(BitVec.allOnes 768).toNat) c.2.2.2.1
    (packedSig (fun e : Ax2303 => e.1.2) xs) (packedSig (fun e : Ax2303 => e.2.2) xs)
  (f false false,if op==2 then 0 else f true false,if op==2 then 0 else f false true,f true true)

def testMarks (c : NodeContext) (op : Nat) (xs : List Ax2303) (ka kb : Bool) (m : Nat) :=
  if m==0 then true else onMarks (fun e => familyCheck c op e ka kb) m xs

lemma todoAt (c : NodeContext) {op} (xs : List Ax2303) (i : Nat) (hi : i<xs.length)
    (ka kb : Bool) (same : (op==2)=true → ka=kb) :
    (partFour (todo2303 c op xs) ka kb).testBit (769*i)=
      worth2303 c.1 c.2.1 c.2.2.2.1 op xs[i].1 xs[i].2 (movedDecor op xs[i].1 xs[i].2) ka kb := by
  cases ka <;> cases kb <;> cases un : op==2 <;>
    first | exact False.elim (Bool.noConfusion (same un)) |
      simpa only [todo2303,partFour,un,Bool.false_eq_true,ite_false,ite_true] using
        (worthAt c.2.1 c.1 op c.2.2.2.1 xs i hi _ _)

lemma familyBranch {c : NodeContext} {op} (xs : List Ax2303)
    (pass : wideFamily c (c.2.2.2.2.1.map (memo c.2.2.1 (c.1-1))) op xs=true)
    (ka kb : Bool) :
    let done := runRules xs op (todo2303 c op xs) (c.2.2.2.2.1.map (memo c.2.2.1 (c.1-1)))
    testMarks c op xs ka kb (partFour done ka kb)=true := by
  obtain ⟨cap,n,ws,cov,ps,links⟩ := c
  simp only [wideFamily] at pass
  rw [opLanes] at pass
  let c : NodeContext := (cap,n,ws,cov,ps,links)
  let done := runRules xs op (todo2303 c op xs) (ps.map (memo ws (cap-1)))
  change (testMarks c op xs false false done.1 && testMarks c op xs true false done.2.1 &&
    testMarks c op xs false true done.2.2.1 && testMarks c op xs true true done.2.2.2)=true at pass
  simp only [Bool.and_eq_true] at pass
  cases ka <;> cases kb
  · exact pass.1.1.1
  · exact pass.1.2
  · exact pass.1.1.2
  · exact pass.2

lemma evalDone (c : NodeContext) (op : Nat) (a b : Decor) (ka kb : Bool)
    (ha : a∈c.2.2.1) (hb : b∈c.2.2.1)
    (checked : worth2303 c.1 c.2.1 c.2.2.2.1 op a b (movedDecor op a b) ka kb=true →
      familyCheck c op (a,b) ka kb=true ∨ ∃ p∈c.2.2.2.2.1,
        scalarPoolCut p (c.1-1) ((opKeep (op==2) ka kb a b c.2.2.1).map Prod.fst)
          (movedChoice op a b)=true) :
    evalMove c op a b (movedDecor op a b) ka kb=true := by
  obtain ⟨cap,n,ws,cov,ps,links⟩ := c
  let z := movedDecor op a b
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2)||kb then 0 else 1))
  let d := len==cap
  let bits := restCov (getCov cov d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2
  let skip := !properB z.1 || ws.any (fun v => v.1==z.1)
  let st := (opKeep (op==2) ka kb a b ws).map Prod.fst
  change (if len>cap then true else if bits != BitVec.allOnes 768 then true else
    if skip then true else closeChild ps links (cap-1) st (movedChoice op a b))=true
  by_cases long : len>cap
  · rw [if_pos long]
  rw [if_neg long]
  by_cases notfull : (bits != BitVec.allOnes 768)=true
  · rw [if_pos notfull]
  rw [if_neg notfull]
  by_cases short : skip=true
  · rw [if_pos short]
  rw [if_neg short]
  have w : worth2303 cap n cov op a b z ka kb=true := by
    change (if len>cap then false else bits==BitVec.allOnes 768)=true
    rw [if_neg long,beq_iff_eq]
    exact Classical.byContradiction (fun e => notfull (bne_iff_ne.mpr e))
  rcases checked w with link | cut
  · change (if skip then true else linked ws links a b z.1 (op==2) ka kb)=true at link
    rw [if_neg short] at link
    have link := linked_ok ha hb link
    simp only [closeChild,Bool.or_eq_true]
    left
    simpa only [z,moved_full] using link
  · simp only [closeChild,Bool.or_eq_true,List.any_eq_true]
    exact Or.inr cut

lemma wideFamily_pass {c : NodeContext} {op : Nat} (xs : List Ax2303)
    (nd : (c.2.2.1.map Prod.fst).Nodup)
    (pass : wideFamily c (c.2.2.2.2.1.map (memo c.2.2.1 (c.1-1))) op xs=true)
    {e : Ax2303} (em : e∈xs) (ha : e.1∈c.2.2.1) (hb : e.2∈c.2.2.1)
    (ka kb : Bool) (same : (op==2)=true → ka=kb) :
    evalMove c op e.1 e.2 (movedDecor op e.1 e.2) ka kb=true := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp em
  subst e
  apply evalDone _ _ _ _ _ _ ha hb
  intro w
  let before := todo2303 c op xs
  let ps := c.2.2.2.2.1
  let done := runRules xs op before (ps.map (memo c.2.2.1 (c.1-1)))
  let last := partFour done ka kb
  have first : (partFour before ka kb).testBit (769*i)=true := (todoAt c xs i hi ka kb same).trans w
  cases h : last.testBit (769*i)
  · exact Or.inr (finishedRule xs i hi ka kb before nd ha hb first h)
  · left
    have run := familyBranch xs pass ka kb
    change testMarks c op xs ka kb last=true at run
    have nz : last≠0 := by intro e; simp [e] at h
    simp only [testMarks,beq_eq_false_iff_ne.mpr nz,Bool.false_eq_true,ite_false] at run
    exact marked_ok _ _ _ i hi h run

lemma wideNode_sound {c : NodeContext} (h : wideNode c=true) :
    (prelim graph c && testAll c c.2.2.1)=true := by
  simp only [wideNode,Bool.and_eq_true] at h
  have good := h.1.1.1
  simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at good
  let ws := c.2.2.1
  have unary {a : Decor} (am : a∈ws) (keep : Bool) : evalMove c 2 a a (movedDecor 2 a a) keep keep=true :=
    wideFamily_pass _ good.1 h.1.1.2 (e:=(a,a)) (List.mem_map_of_mem am) am am _ _ (fun _ => rfl)
  have binary {a b : Decor} (am : a∈ws) (bm : b∈ws) (inPairs : (a,b)∈couples ws) (d ka kb : Bool) :
      let op := if d then 1 else 0
      evalMove c op a b (movedDecor op a b) ka kb=true := by
    cases d
    · exact wideFamily_pass _ good.1 h.1.2 inPairs am bm ka kb (by simp)
    · exact wideFamily_pass _ good.1 h.2 inPairs am bm ka kb (by simp)
  have all (l : List Decor) (sub : ∀ w∈l, w∈ws) (prs : ∀ e∈couples l, e∈couples ws) : testAll c l=true := by
    induction l with
    | nil => rfl
    | cons a bs ih =>
      have am := sub a (by simp)
      have rest (b) (bm : b∈bs) := sub b (List.mem_cons_of_mem a bm)
      have subP (e) (em : e∈couples bs) := prs e (List.mem_append_right _ em)
      simp only [testAll,testRow,Bool.and_eq_true,List.all_eq_true]
      refine ⟨⟨⟨unary am false,unary am true⟩,?_⟩,ih rest subP⟩
      intro b bm
      have im : (a,b)∈couples ws := prs _ (List.mem_append_left _ (List.mem_map_of_mem bm))
      have p (d : Bool) : testPair c a b d=true := by
        simp only [testPair,Bool.and_eq_true]
        exact ⟨⟨⟨binary am (rest b bm) im d false false,binary am (rest b bm) im d true false⟩,
          binary am (rest b bm) im d false true⟩,binary am (rest b bm) im d true true⟩
      exact ⟨p false,p true⟩
  simp only [Bool.and_eq_true]
  exact ⟨h.1.1.1,all ws (fun _ => id) (fun _ => id)⟩

def triangle (f : Decor → Bits) : List Decor → Nat × Nat × Nat
  | [] => (0,0,0)
  | x::xs =>
    let (suffix,left,right) := triangle f xs
    let m := xs.length
    let v := (f x).toNat
    ((suffix <<< 769)+v,(left <<< (769*m))+units m*v,(right <<< (769*m))+suffix)

lemma lanesAppend {α} (f : α → Bits) (xs ys) :
    combineLanes f (xs++ys)=(combineLanes f ys <<< (769*xs.length))+combineLanes f xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons x l ih =>
    simp only [List.cons_append,List.length_cons,combineLanes,lanePlace,ih,Nat.shiftLeft_eq,
      Nat.mul_succ,Nat.pow_add]
    ring

lemma lanesMap {α β : Type} (f : β → Bits) (g : α → β) (xs) :
    combineLanes f (xs.map g)=combineLanes (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,combineLanes,ih]

lemma triangle_eq (f : Decor → Bits) (xs) :
    triangle f xs=(combineLanes f xs,combineLanes (fun e : Ax2303 => f e.1) (couples xs),
      combineLanes (fun e : Ax2303 => f e.2) (couples xs)) := by
  induction xs with
  | nil => rfl
  | cons a l ih =>
    simp only [triangle,ih,combineLanes,couples,lanesAppend,lanesMap,
      List.length_map,←broadcast,lanePlace,Nat.shiftLeft_eq,Nat.mul_comm]

def packedFamily (c : NodeContext) (ps : List Memo) (op : Nat) (ops : List Ax2303)
    (sa sb : PackedSig) (a b : Nat) :=
  let (cap,n,ws,cov,_,links) := c
  let r := units ops.length
  let full := r*(BitVec.allOnes 768).toNat
  let un := op==2
  let z := if un then (r*one.toNat) ^^^ a else if op==1 then a ||| b else a &&& b
  let worth := wideWorth n cap op r full cov sa sb
  let todo : Four := (worth false false,if un then 0 else worth true false,
                       if un then 0 else worth false true,worth true true)
  let left := wideRules r full a b z un todo ps
  let verify := fun (ka kb : Bool) (t : Nat) => if t==0 then true else
    onMarks (fun e : Ax2303 =>
      let w := (movedDecor op e.1 e.2).1
      if !properB w || ws.any (fun v => v.1==w) then true else
      linked ws links e.1 e.2 w un ka kb) t ops
  verify false false left.1 && verify true false left.2.1 &&
    verify false true left.2.2.1 && verify true true left.2.2.2

def triangleNode (c : NodeContext) :=
  let ws := c.2.2.1
  let ss := c.2.2.2.2.1.map (memo ws (c.1-1))
  let bs := couples ws
  let (_,pa,pb) := triangle (fun w => w.2.1) ws
  let (_,na,nb) := triangle (fun w => w.2.2) ws
  let (_,a,b) := triangle (fun w => liftSig w.1) ws
  let family := fun op => packedFamily c ss op bs (pa,na) (pb,nb) a b
  prelim graph c && wideFamily c ss 2 (ws.map fun v => (v,v)) && family 0 && family 1

theorem triangleNode_ok {c : NodeContext} (h : triangleNode c=true) :
    (prelim graph c && testAll c c.2.2.1)=true := by
  obtain ⟨cap,n,ws,cov,pools,links⟩ := c
  apply wideNode_sound
  simp only [triangleNode,triangle_eq] at h
  exact h

theorem symmetryOK : ∀ i : Fin 12, autoOK graph (symmetry2303 i)=true := by decide +kernel

lemma symmetryBack {xs ys : List Sig} {cap : Nat} (a : Fin 12)
    (matchSet : sameWords (xs.map (movedWord (symmetry2303 a))) ys=true)
    (lower : Impossible graph cap ys.toFinset) : Impossible graph cap xs.toFinset := by
  let p := symmetry2303 a
  have checked := symmetryOK a
  change autoOK graph p=true at checked
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at checked
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id checked.2 r⟩
  have eq : xs.toFinset.image (rename (movedRow p))=ys.toFinset := by
    rw [←sameWords_sound matchSet]
    ext w
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map,moved_eq_rename,p]
  intro k t hk run
  have mapped := live_rename run (movedRow p) onto
  have goal : rename (movedRow p) graph=graph := (moved_eq_rename p graph).symm.trans checked.1.1
  rw [eq,goal] at mapped
  exact lower k t hk mapped

def symmetryTest (l : Layer) (idx : Index) (aliases : Nat → Nat) (depth i tag : Nat) :=
  let p := symmetry2303 (Fin.ofNat 12 tag)
  let projected := (bank2303 depth (l.2 i)).map (movedWord p)
  match idx (keySet projected) with
  | none => false
  | some j => decide (j<l.1) && aliases j==0 && sameWords projected (bank2303 depth (l.2 j))

lemma symmetryTest_ok {l idx aliases depth i tag cap}
    (master : ∀ j, j<l.1 → aliases j=0 → Impossible graph cap (bank2303 depth (l.2 j)).toFinset)
    (h : symmetryTest l idx aliases depth i tag=true) :
    Impossible graph cap (bank2303 depth (l.2 i)).toFinset := by
  unfold symmetryTest at h
  dsimp only at h
  split at h
  next => contradiction
  next j _ =>
    simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
    exact symmetryBack _ h.2 (master j h.1.1 h.1.2)

def primaryCheck (l next : Layer) (hs : Hints) (idx : Index)
    (exp : Nat → Bool) (cap depth i : Nat) :=
  if exp i then triangleNode (ctx2303 l next hs idx cap depth i) else verifiedTerminal cap depth (l.2 i)
def completeCheck (l next : Layer) (hs : Hints) (idx : Index)
    (exp : Nat → Bool) (self : Index) (aliases : Nat → Nat) (cap depth i : Nat) :=
  if aliases i==0 then primaryCheck l next hs idx exp cap depth i else
    symmetryTest l self aliases depth i (aliases i)

lemma completeCheck_ok {l next hs idx exp self aliases cap depth}
    (prior : excluded (cap-1) (depth+1) next)
    (pass : ∀ i, i<l.1 → completeCheck l next hs idx exp self aliases cap depth i=true) :
    excluded cap depth l := by
  have master (j) (bound : j<l.1) (direct : aliases j=0) :
      Impossible graph cap (bank2303 depth (l.2 j)).toFinset := by
    have h := pass j bound
    simp only [completeCheck,direct,beq_self_eq_true,ite_true,primaryCheck] at h
    split at h
    · exact ctx2303_ok prior (triangleNode_ok h)
    · exact verifiedTerminal_ok h
  intro i hi
  by_cases isMaster : aliases i=0
  · exact master i hi isMaster
  · have h := pass i hi
    simp only [completeCheck,beq_eq_false_iff_ne.mpr isMaster,Bool.false_eq_true,ite_false] at h
    exact symmetryTest_ok master h

def treeCheck (p : Nat → Bool) (start len : Nat) : Nat → Prop
  | 0 => span p len start=true
  | h+1 => treeCheck p start (len/2) h ∧ treeCheck p (start+len/2) (len-len/2) h
lemma tree_at {p start len height} (h : treeCheck p start len height)
    (i : Nat) (lo : start ≤ i) (hi : i < start + len) : p i = true := by
  induction height generalizing start len with
  | zero => exact span2303_at h i lo hi
  | succ n ih =>
    change _ ∧ _ at h
    by_cases first : i<start+len/2
    · exact ih h.1 lo first
    · exact ih h.2 (by omega) (by omega)
def empty2303 : Layer := (0,fun _ => (0,0))
def noIdx : Index := fun _ => none
def test0 := completeCheck a0layer a1layer a0hints a1idx a0expanded a0idx a0alias 14 1
def test1 := completeCheck a1layer a2layer a1hints a2idx a1expanded a1idx a1alias 13 2
def test2 := completeCheck a2layer a3layer a2hints a3idx a2expanded a2idx a2alias 12 3
def test3 := completeCheck a3layer a4layer a3hints a4idx a3expanded a3idx a3alias 11 4
def test4 := completeCheck a4layer a5layer a4hints a5idx a4expanded a4idx a4alias 10 5
def test5 := completeCheck a5layer empty2303 a5hints noIdx a5expanded a5idx a5alias 9 6

theorem certify
    (h0 : ∀ i, i<a0layer.1 → test0 i=true)
    (h1 : ∀ i, i<a1layer.1 → test1 i=true)
    (h2 : ∀ i, i<a2layer.1 → test2 i=true)
    (h3 : ∀ i, i<a3layer.1 → test3 i=true)
    (h4 : ∀ i, i<a4layer.1 → test4 i=true)
    (h5 : ∀ i, i<a5layer.1 → test5 i=true) :
    Impossible graph 14 start2303.toFinset := by
  have e6 : excluded 8 7 empty2303 := by
    intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  have e5 : excluded 9 6 a5layer := completeCheck_ok e6 h5
  have e4 : excluded 10 5 a4layer := completeCheck_ok e5 h4
  have e3 : excluded 11 4 a3layer := completeCheck_ok e4 h3
  have e2 : excluded 12 3 a2layer := completeCheck_ok e3 h2
  have e1 : excluded 13 2 a1layer := completeCheck_ok e2 h1
  have e0 : excluded 14 1 a0layer := completeCheck_ok e1 h0
  have init : (bank2303 1 (a0layer.2 0)).toFinset=start2303.toFinset := by decide +kernel
  rw [←init]
  exact e0 0 (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b0_0 : treeCheck test0 0 1 0 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
theorem proofLevel0 : treeCheck test0 0 1 0 := b0_0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b1_0 : treeCheck test1 0 71 6 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
theorem proofLevel1 : treeCheck test1 0 71 6 := b1_0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b2_0 : treeCheck test2 0 830 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b2_1 : treeCheck test2 830 831 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
theorem proofLevel2 : treeCheck test2 0 1661 10 := ⟨b2_0,b2_1⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_0 : treeCheck test3 0 746 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_1 : treeCheck test3 746 746 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_2 : treeCheck test3 1492 746 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_3 : treeCheck test3 2238 747 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_4 : treeCheck test3 2985 746 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_5 : treeCheck test3 3731 747 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_6 : treeCheck test3 4478 746 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_7 : treeCheck test3 5224 747 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_8 : treeCheck test3 5971 746 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_9 : treeCheck test3 6717 747 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_10 : treeCheck test3 7464 746 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_11 : treeCheck test3 8210 747 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_12 : treeCheck test3 8957 746 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_13 : treeCheck test3 9703 747 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_14 : treeCheck test3 10450 746 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b3_15 : treeCheck test3 11196 747 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
theorem proofLevel3 : treeCheck test3 0 11943 13 := ⟨⟨⟨⟨b3_0,b3_1⟩,⟨b3_2,b3_3⟩⟩,⟨⟨b3_4,b3_5⟩,⟨b3_6,b3_7⟩⟩⟩,⟨⟨⟨b3_8,b3_9⟩,⟨b3_10,b3_11⟩⟩,⟨⟨b3_12,b3_13⟩,⟨b3_14,b3_15⟩⟩⟩⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b4_0 : treeCheck test4 0 572 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b4_1 : treeCheck test4 572 573 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b4_2 : treeCheck test4 1145 572 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b4_3 : treeCheck test4 1717 573 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b4_4 : treeCheck test4 2290 572 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b4_5 : treeCheck test4 2862 573 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b4_6 : treeCheck test4 3435 572 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b4_7 : treeCheck test4 4007 573 9 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
theorem proofLevel4 : treeCheck test4 0 4580 12 := ⟨⟨⟨b4_0,b4_1⟩,⟨b4_2,b4_3⟩⟩,⟨⟨b4_4,b4_5⟩,⟨b4_6,b4_7⟩⟩⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem b5_0 : treeCheck test5 0 185 7 := by
  simp only [treeCheck]
  repeat' apply And.intro
  all_goals decide +kernel
theorem proofLevel5 : treeCheck test5 0 185 7 := b5_0

theorem certified : Impossible graph 14 start2303.toFinset :=
  certify
    (fun i hi => tree_at proofLevel0 i (Nat.zero_le _) hi)
    (fun i hi => tree_at proofLevel1 i (Nat.zero_le _) hi)
    (fun i hi => tree_at proofLevel2 i (Nat.zero_le _) hi)
    (fun i hi => tree_at proofLevel3 i (Nat.zero_le _) hi)
    (fun i hi => tree_at proofLevel4 i (Nat.zero_le _) hi)
    (fun i hi => tree_at proofLevel5 i (Nat.zero_le _) hi)

end PEqualNP.Outside.L_meta_3614.Seed


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 3000 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_3614 :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Bool),   x3 ≠ (0 : Fin (9 : ℕ)) →     x3 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < (10 : ℕ) + x4.size →               (∀ x13 ∈ List.take (x5 + (1 : ℕ) - (10 : ℕ)) x4.gates, ↑x3 ∉ x13.inputs) →                 (∀ (x14 x15 : Fin (9 : ℕ) → Bool), (∀ (x16 : Fin (9 : ℕ)), x16 ≠ x3 → x14 x16 = x15 x16) → x1 x14 ≠ x1 x15 → (x4.wires (x2 x14)).getD x5 Bool.false = !x6) →                   ∃ (x15 : Fin (9 : ℕ) → Bool),                     have x16 : Bool := (x4.wires (x2 x15)).getD x5 Bool.false;                     x4.eval ((x2 x15).set (↑x3) (if x6 = Bool.true then x15 x3 || x16 else x15 x3 && x16)) ≠ x1 x15 := by
  classical
  let target (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))

  let row (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 6]

  let emit (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let maskBit (x h disj : Bool) := if disj then x || h else x && h

  let redirect (v k i : ℕ) : ℕ := if i = v then k else if i < k then i else i+1

  let rename (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

  have fold_size (gs : List Gate) (w : List Bool) : (gs.foldl emit w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [emit]; omega

  have fold_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl emit w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (emit w g) (by simp [emit]; omega)]
      exact List.getD_append _ _ _ _ hi

  have set_emit_avoid (g : Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : v ∉ g.inputs) :
      emit (w.set v val) g = (emit w g).set v val := by
    have reads : ∀ i ∈ g.inputs, (w.set v val).getD i false = w.getD i false := by
      intro i hi
      have ne : v ≠ i := by intro eq; apply avoid; exact eq ▸ hi
      by_cases valid : i < w.length
      · rw [List.getD_eq_getElem _ _ (by simpa using valid),List.getD_eq_getElem _ _ valid,
          List.getElem_set_ne ne]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt valid),
          List.getD_eq_default _ _ (Nat.le_of_not_gt valid)]
    unfold emit
    rw [List.map_congr_left reads,List.set_append_left v val hv]

  have fold_set_avoid (gs : List Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : ∀ g ∈ gs, v ∉ g.inputs) :
      gs.foldl emit (w.set v val) = (gs.foldl emit w).set v val := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [set_emit_avoid g w v val hv (avoid g (by simp))]
      exact ih (emit w g) (by simp [emit]; omega) (fun a ha => avoid a (by simp [ha]))

  have append_other (w : List Bool) (b : Bool) (i : ℕ) (ne : i ≠ w.length) :
      (w++[b]).getD i false = w.getD i false := by
    by_cases small : i < w.length
    · exact List.getD_append _ _ _ _ small
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

  have suffix_shift (gs : List Gate) (v k : ℕ) (w y : List Bool)
      (hv : v < k) (hk : k ≤ w.length) (len : y.length = w.length + 1)
      (rel : ∀ i, y.getD (redirect v k i) false = w.getD i false) :
      ∀ i, ((gs.map (rename (redirect v k))).foldl emit y).getD (redirect v k i) false =
        (gs.foldl emit w).getD i false := by
    induction gs generalizing w y with
    | nil => exact rel
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      let value := g.op.eval (g.inputs.map fun i => w.getD i false)
      have emitY : emit y (rename (redirect v k) g) = y ++ [value] := by
        change y ++ [g.op.eval ((g.inputs.map (redirect v k)).map fun i => y.getD i false)] = _
        simp only [List.map_map,Function.comp_def]
        rw [List.map_congr_left (fun i _ => rel i)]
      rw [emitY]
      apply ih (w++[value]) (y++[value])
      · simp; omega
      · simp [len]
      intro i
      have sameWire : redirect v k i = y.length ↔ i = w.length := by
        by_cases eq : i = v
        · simp only [redirect]
          rw [ite_eq_left eq]
          omega
        · simp only [redirect]
          rw [ite_eq_right eq]
          split <;> omega
      by_cases hi : i = w.length
      · rw [sameWire.mpr hi,hi]
        simp
      · rw [append_other _ _ _ (fun a => hi (sameWire.mp a)),append_other _ _ _ hi]
        exact rel i

  have append_with_mask (v : ℕ) (old : List Bool) (hv : v < old.length) (bit : Bool) :
      ∀ i, (old ++ [bit]).getD (redirect v old.length i) false = (old.set v bit).getD i false := by
    intro i
    by_cases piv : i = v
    · subst i
      simp only [redirect, ite_true]
      rw [List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self,List.getD_cons_zero,
        List.getD_eq_getElem _ _ (by simp; exact hv)]
      simp
    simp only [redirect]
    rw [ite_eq_right piv]
    by_cases valid : i < old.length
    · rw [ite_eq_left valid,List.getD_append _ _ _ _ valid,List.getD_eq_getElem _ _ valid,
        List.getD_eq_getElem _ _ (by simpa using valid),List.getElem_set_ne (Ne.symm piv)]
    · rw [ite_eq_right valid,List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

  have row_pivot (x : Fin 9 → Bool) (v : Fin 9) : (row x).getD v.val false = x v := by
    unfold row
    rw [List.getD_append _ _ _ _ (by simpa using v.isLt),
      List.getD_eq_getElem _ _ (by simpa using v.isLt),List.getElem_ofFn]

  have mask_value (x : Fin 9 → Bool) (v : Fin 9) (k : ℕ) (disj : Bool) (old : List Bool)
      (hv : v.val < old.length) (oldv : old.getD v.val false = x v) :
      emit old ⟨if disj then .or else .and,[v.val,k]⟩ =
        old ++ [maskBit (x v) (old.getD k false) disj] := by
    unfold emit maskBit
    cases disj
    · change old ++ [(old.getD v.val false && (old.getD k false && true))] =
        old ++ [x v && old.getD k false]
      rw [Bool.and_true,oldv]
    · change old ++ [(old.getD v.val false || (old.getD k false || false))] =
        old ++ [x v || old.getD k false]
      rw [Bool.or_false,oldv]

  have insertMasked (C : Circuit) (v : Fin 9) (k : ℕ) (disj : Bool)
      (fan : FanInTwo C) (lo : 10 ≤ k) (hi : k < 10+C.size)
      (avoid : ∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs) :
      ∃ Q : Circuit, FanInTwo Q ∧ Q.size = C.size+1 ∧
        ∀ x : Fin 9 → Bool, Q.eval (row x) = C.eval
          ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj)) := by
    let pre := C.gates.take (k+1-10)
    let suf := C.gates.drop (k+1-10)
    let mask : Gate := ⟨if disj then .or else .and,[v.val,k]⟩
    let shift := rename (redirect v.val (k+1))
    let D : Circuit := ⟨(pre ++ mask :: suf.map shift),redirect v.val (k+1) C.output⟩
    have split : pre ++ suf = C.gates := List.take_append_drop _ _
    have maskLegal : mask.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ mask.inputs.length ≤ 2 := by
      cases disj <;> simp [mask]
    have legal : FanInTwo D := by
      intro g hg
      change g ∈ (pre ++ mask :: suf.map shift) at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact fan g (by rw [← split]; exact List.mem_append_left _ hg)
      rcases List.mem_cons.mp hg with rfl | hg
      · exact maskLegal
      obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
      obtain ⟨op,arity⟩ := fan g' (by rw [← split]; exact List.mem_append_right _ hg')
      exact ⟨op,by simpa [shift,rename] using arity⟩
    have hsize : D.size = C.size+1 := by
      have len := congrArg List.length split
      change ((pre ++ mask :: suf.map shift)).length = C.gates.length+1
      simp only [List.length_cons,List.length_append,List.length_map] at len ⊢
      omega
    refine ⟨D,legal,hsize,?_⟩
    intro x
    let old := pre.foldl emit (row x)
    have kBound : k+1-10 ≤ C.gates.length := by change k < 10+C.gates.length at hi; omega
    have length : old.length = k+1 := by
      rw [show old = pre.foldl emit (row x) by rfl,fold_size]
      simp [pre,row,Nat.min_eq_left kBound]
      omega
    have vBound : v.val < old.length := by rw [length]; have := v.isLt; omega
    have saved : (C.wires (row x)).getD k false = old.getD k false := by
      change (C.gates.foldl emit (row x)).getD k false = _
      rw [← split,List.foldl_append]
      exact fold_preserves suf old k (by omega)
    have savedV : old.getD v.val false = x v := by
      rw [fold_preserves pre (row x) _ (by simp [row]; have := v.isLt; omega),row_pivot]
    let bit := maskBit (x v) (old.getD k false) disj
    have oldSet : pre.foldl emit ((row x).set v.val bit) = old.set v.val bit :=
      fold_set_avoid pre (row x) v.val bit (by simp [row]; have := v.isLt; omega) avoid
    have law (i : ℕ) : (old ++ [bit]).getD (redirect v.val (k+1) i) false =
        (old.set v.val bit).getD i false := by rw [← length]; exact append_with_mask v.val old vBound bit i
    have simulated := suffix_shift suf v.val (k+1) (old.set v.val bit) (old++[bit])
      (by have := v.isLt; omega) (by simp [length]) (by simp) law C.output
    change ((pre ++ mask :: suf.map shift).foldl emit (row x)).getD
        (redirect v.val (k+1) C.output) false =
      (C.gates.foldl emit ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj))).getD C.output false
    rw [List.foldl_append, List.foldl_cons,mask_value x v k disj old vBound savedV,
      saved,← split,List.foldl_append,oldSet]
    exact simulated

  change ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (b : Bool), v ≠ 0 → v ≠ 6 →
    FanInTwo C → C.size ≤ 13 → 10 ≤ k → k < 10+C.size →
    (∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs) →
    (∀ x y, (∀ u, u ≠ v → x u = y u) → target x ≠ target y →
      (C.wires (row x)).getD k false = !b) →
    ∃ x, C.eval ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) b)) ≠ target x
  intro v C k b v0 v6 fan size lo hi avoid sensitive
  change ∃ x, C.eval ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) b)) ≠ target x
  by_contra! correct
  obtain ⟨Q,hQ,hsize,simulation⟩ := insertMasked C v k b fan lo hi avoid
  apply PEqualNP.Outside.L_meta_3614.Seed.noSeeded PEqualNP.Outside.L_meta_3614.Seed.certified Q hQ (by omega)
  intro x
  have h := (simulation x).trans (correct x)
  change Q.eval (row x) = _
  rw [h]
  change ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) =
      PEqualNP.Outside.L_meta_3614.Seed.edge x
  have check : ∀ v : Fin 9 → Bool, ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => v (Fin.ofNat 9 (e / 10)) && v (Fin.ofNat 9 (e % 10))) =
      PEqualNP.Outside.L_meta_3614.Seed.edge v := by decide +kernel
  exact check x
