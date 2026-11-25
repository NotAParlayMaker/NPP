import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14598.Model
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

theorem bRead (i) (w : List Sig) (j : Nat) :
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
  simp only [bRead]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

theorem exeBits (gs : List Gate) (i) (w : List Sig)
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
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
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
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
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
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

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
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

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

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
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
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
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



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
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
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

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

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
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

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

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

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
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

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
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
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
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

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
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
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

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
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
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
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
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
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


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
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
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
  exact hi k hk run

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


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


end PEqualNP.Outside.L_meta_14598.Model

namespace PEqualNP.Outside.L_meta_14598
open PEqualNP.Outside.L_meta_14598.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SB : Nat := 4

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := []

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) mirrorSteps then ws.map (movedWord mirrorSteps.reverse) else ws

theorem variant_ok {g k ws} (h : Impossible true (target g) k (List.toFinset ws)) (code : Nat) :
    Impossible true (target g) k (variant g code ws).toFinset := by
  unfold variant
  split
  next e =>
    simp only [Bool.and_eq_true] at e
    exact rotate_excluded h _ e.2
  next => exact h

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let code := locate g k tag
  let row := code / 2
  if row < count g k then [variant g code (vals g k row)] else []

def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

theorem checked {g : Atlas} {r s} (ready : Ready g r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at h
    by_cases hn : tip g k i = 0
    · simp only [hn,bne_self_eq_false, Bool.false_eq_true,ite_false] at h
      by_cases hk : k=0
      · subst k
        intro n cap run
        have : n=0 := by omega
        subst n
        have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
        exact h.1.2 (List.mem_toFinset.mp hm)
      apply node_sound (raw:=roots g) ready.1 _ h.1.1 h.1.2 _ _ h.2
      · intro a ha
        exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
      · simp
      · intro tag xs hx
        simp only [links] at hx
        split at hx
        next le =>
          obtain rfl := List.mem_singleton.mp hx
          exact variant_ok (ih (k-1) (by omega) (fun l hl => good l (by omega)) _ le) _
        next => simp at hx
    · simp only [bne_iff_ne.mpr hn, ite_true] at h
      have test := h.2
      simp only [deadTest,Option.any_eq_true] at test
      obtain ⟨bank,he,hc⟩ := test
      exact poolCut_sound (ready.2.2 k i hi hn) _ he h.1.1 hc

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : test i=true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_14598

namespace PEqualNP.Outside.L_meta_14598
open PEqualNP.Outside.L_meta_14598.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffff03e0ffff83c1fffffffc1c07ffe1ff33f
  | 2 => 0x3f83ffc00fffffc01e1e1f03fe007fff924c3f
  | 3 => 0xc003fffff07c1fffe01fe003ffff8781e38fcc
  | 4 => 0x3ffffff801fffffe00003fffff801fc0ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x50011801108000c0222211940450894049315
  | 2 => 0x8a67220da63319c30d0d1a22b20a5569924c2a
  | 3 => 0x9329449483412a5520174848d493060ca3854c
  | 4 => 0x2c528929081a54aa57401093292c60315c0ab0
  | 5 => 0x30630e31cc639f3399999ce030304441fb6000
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xffccccccffc0c0c0ffccccccffc0c0c0ffccccccffc0c0c0ffccccccffc0c0c0ffccccccffc0c0c0ffccccccffc0c0c0ffccccccffc0c0c0ffccccccffc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14598
namespace PEqualNP.Outside.L_meta_14598
open PEqualNP.Outside.L_meta_14598.Model
def s1K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*4) 4
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (5+((h/1+packedAt s1K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff73ffc71fff0ff
  | 2 => 0xffffffffffffffffffffffeaf8333f81ce7c93
  | 3 => 0x73ffc3cffe0f8f1c
  | 4 => 0x7cfffc0ffff00fe0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010400010420025
  | 2 => 0x1526a64c8ca56c92
  | 3 => 0xc42281524092518
  | 4 => 0x38402aa49204ac0
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 29 s1Pos s1Neg, 0xffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0ffaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14598
namespace PEqualNP.Outside.L_meta_14598
open PEqualNP.Outside.L_meta_14598.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfe1fe3c7e3fffe1c71f8fc0c707fffe19c0ff
  | 1 => 0xf1fe3fff803c78fe07e3f1fff8070e1e667c93
  | 3 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 4 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4028004410502000420502480101429008c025
  | 1 => 0x24448c080c88910601209086c832244c221c92
  | 3 => 0xa88094912409402a8802a41252500944870518
  | 4 => 0x41529224820125515480024a4a4a009700ac0
  | 5 => 0xc919300371326499e693493800c0c191dde000
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88ffeeeeccffaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14598
namespace PEqualNP.Outside.L_meta_14598
open PEqualNP.Outside.L_meta_14598.Model
def s3K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf83f87c7fffe1fe1fc3f0fe0c3fff87f4dc3cf
  | 1 => 0xffc7fff83c3fe1fe1fc3f0fffc383f87b27d33
  | 2 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xa0008411010200048050124004a082404c045
  | 1 => 0x10810080804402020440104244109102101512
  | 2 => 0xa11255120aa9106ca222aa08aa812650c30a28
  | 4 => 0x85b56624aa0d54b736a88812f3258312f80f80
  | 5 => 0xc626443733319939db33cc9c22060464efe000
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xeeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14598
namespace PEqualNP.Outside.L_meta_14598
open PEqualNP.Outside.L_meta_14598.Model
def s4K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (6+((h/1+packedAt s4K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf83f87c7fffe1fe1fc3f0fe0c3fff87f4dc3cf
  | 1 => 0xffc7fff83c3fe1fe1fc3f0fffc383f87b27d33
  | 2 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 3 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa0008411010200048050124004a082404c045
  | 1 => 0x10810080804402020440104244109102101512
  | 2 => 0xa11255120aa9106ca222aa08aa812650c30a28
  | 3 => 0x85b56624aa0d54b736a88812f3258312f80f80
  | 5 => 0xc626443733319939db33cc9c22060464efe000
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xeeeceeeceae8eae8eeeceeeceae8eae8eeeceeeceae8eae8eeeceeeceae8eae8eeeceeeceae8eae8eeeceeeceae8eae8eeeceeeceae8eae8eeeceeeceae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14598
namespace PEqualNP.Outside.L_meta_14598
open PEqualNP.Outside.L_meta_14598.Model
def s5K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (6+((h/1+packedAt s5K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 1 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 2 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 3 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 1 => 0xc4148944492854085064292124849286314512
  | 2 => 0x1a912289244a801ac80524849212530c28a28
  | 3 => 0x488c032520240c92352918000e498192540f80
  | 4 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14598
namespace PEqualNP.Outside.L_meta_14598
open PEqualNP.Outside.L_meta_14598.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xa00168e00098f8187811e8016000b1b82090013980a9c99849e14000014809d04000e9a02801f1c03059f851a92800c1d8390000008122095971b200d188f150b861306908d9108800c871180179903011208102020048e1a1c30a00200061814180007fd5001fe54007f55001fc54007fd4c01fe53007f54c01fc53007fd0c01fe43007f50c01fc43007fd48017f52007f94801fd52005f54801fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc32007fd4401fe51005f94401fd51007f144017c51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd40017f50007f94001fd50005f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x224000bfd8d20005fcc690002fd63480017e31a4000dfd4920006faa490003ee4248001f6a124000fb8c920007da6490002ff61480017e30a4000df94520006f8a290003ef2148001f690a4000dfd4120006faa090003fb2048001f71024000bfd9420005fcca100037e65080013f3284000bf59420006faca100027d65080017e3284000bfd9020005fcc810003be64080015f3204000bf590200077ac810002bd64080017e3204000bfd8c20005fcc610003de63080016f3184000bf58c20007bac610002dd63080017e3184000bf98820006fea410003ee5208001bea904000fb54820006daa410002fe6108001fb3084000bd98420005fac210003f561080017ab084000df94420006f8a210003ee2108001f61084000bf98020006fea0100037d5008001f79004000fe88020007da4010003f920080017fb2e2001dfd9710004fecb88002fe65c40017eb2e2000bf1971000ef8cb880027c65c40017fb262000bf99310005fac988002fc64c40017fb1e2000bf98f10005fac788002fc63c40017fb162000bf98b10005fac588002fc62c4001bfa962000df54b1000efca3880077c51c4001fb20e2000fd50710007ec6388003f531c4001fb10e2000fd48710006fea1880037d50c40017fb2c2000bf99610006fccb080027e65840017eb2c2000df59610004facb08002fc65840017fb242000bf99210005fac908002fc64840017fb1c2000bf98e10005fac708002fc63840017fb142000bf98a10005fac508002fc6284001bfa942000df54a10005fac3080037e5184001be28c2000bf98210006fea108003fa5084001bea842000fe54210006f2a108003fa2084001fc9042000fdc4210007f62108002ff6544001bfb2a20009fd9510005fcca88002fd65440017e32a2000df19510004f8ca88002ff64440017f3222000bf59110005f8c888002ff63440017f31a2000bf58d10005f8c688002ff6244001f7b122000bbd8910005fcc488002fd62440017e3122000fb18910005d8c4880037f5244001bea922000df94510006f8a288003f64144001faa0a2000fd8c510007ea6288003f62144001fa90a2000dfd4110007f4a0880037d5044001fca822000de54110007f44088003f92044001fd8822000fd84110005feca08002fe6504001bf32820009f99410005faca080037d65040013eb282000bf19410005fec808002fe6404001df3202000af99010005fac808003bd64040015eb202000bf19010005fec608002fe6304001ef3182000b798c10005fac608003dd63040016eb182000bf18c10005fec408002fe6204001f73102000bb98810005fac408003ed620400176b102000bf18810006fea4080037d52040017f3082001df9441000ef8a208002fe6004001bfa802000df54010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x3ed621000176b108000dfd4840006faa420002fe6110001fb3088000bd98440005fac220003f561100017ab088000df94440006f8a220002fe6010001bfa808000df540400077e8020003fa4010001dea008000fe50040005fecb98002fe65cc0017eb2e6000bf19730005fec998002fe64cc0017eb266000bf19330007bc8798003dd43cc0017f3166000bf58b30006fea5980037d52cc001ef9966000f74cb30005fcc398002fd61cc001bf28e6000df14730007be6398003dd31cc001bfa866000df54330005fecb18002fe658c001bf32c60009f99630005facb180037d658c0013eb2c6000bf19630005fec918002fe648c0017eb246000bf19230005fac718003df438c001ee21c6000bf98a30005fac5180037f528c001bea946000bf98630005fac3180037e518c001be28c6000bf98230006fea1180037d508c001fd2046000fe50230007be6118003fb308c0017fb2a6000bf99530005faca98002fc654c0017fb226000efd91300057ec898002fe644c0017eb226000bf1913000778c898002bc644c001ef21a6000f750d30005fec498002fc624c001bfa926000df54930007be6498003dd324c0017fb0a6000bf18530006fca2980037c514c001ef98a6000f74c530006fea0980037d504c001fd2026000fe50130007f66098003de304c0017fb286000bf99430006fcca180027e650c0017eb286000df59430004faca18002fc650c0017fb206000bf990300077cc818002be640c0017eb206000ef590300057ac818002fc640c0017f3186000f7d0c30007b88618002fe620c001f73106000bb98830005fac418003ed620c00176b106000dfd4830006faa418002fe610c001fb3086000bd98430005fac218003f5610c0017ab086000df94430006f8a218002fe600c001bfa806000df54030007be6018003fa300c001ee9806000fe4c030005fecb90002fe65c8001bf32e40009f99720005facb900037d65c80013eb2e4000bf19720005fec990002fe64c80017eb264000bf19320005fec790002fe63c80017eb1e4000bf18f20006fea5900037d52c8001f72164000fb50b20007dc6590003ed32c80017f30e4000bf58720006fca3900037c51c8001f790e4000fb48720006fea1900037d50c80017fb2c4000bf99620006fccb100027e65880017eb2c4000df59620004facb10002fc65880017fb244000bf99220005fac910002fc64880017fb1c4000bf98e20005fac710002fc63880017eb144000dfd4a20007dca5100037d5288001f6a944000db54a20005fcc310002fd6188001bf28c4000df14620007dc4310003ec21880017f3044000dfd4220006faa110003ef2088001fd9044000bfd9520005fcca900037e65480013f32a4000bf59520006faca900027d65480017e32a4000bfd9120005fcc890002fd64480017e3
  | 2 => 0x50006f865a80037f61d4001bf30ea0009f98750006fac3a80037c61d4001bfa0ea000df90750006fa83a80037c41d4001bf98ea000df8c750006fa63a80037c31d4001bf90ea000df88750006fa43a80037c21d40017eb2ca0009f59650005fcc928002fd64940017f31ca000bf58e50005fcc528002fd6294001bfa94a000df54a50005fcc328002fd6194001bf28ca000df14650005fcc1280037f5094001fda84a000bfd9150005f8c8a80037f5454001bf2a2a000df55150006f8a8a8002ff63540017e31aa000dfd4d50006fca6a80037d5354001be29aa000bfd8950005f8c4a80037f5254001bf292a000df54950006f8a4a8002ff61540017e30aa000dfd4550006fca2a80037d5154001be28aa000fed4150006fca0a80037f6454001bf322a000df59150006f8c8a80037f6354001bf31aa000df58d50006f8c6a80037f4354001bf21aa000df50d50006f886a80037f62540013fb12a000df98950006fac4a80037c6254001bfa12a000df90950006fa84a80037c4254001bf992a000df8c950006fa64a80037c3254001bfb0aa000df98550006fac2a80037c61540013e30aa000dfd0550006fc82a80037d4154001be20aa000dfcc550006fc62a80037d3154001be18aa000dfc8550006fc42a80037d2154001be10aa000dfd8150006f6c0a8002fe65140013f328a000bf99050005fac828002fe63140017eb18a000bf98850005fac4280037f5214001bea90a000bf98450005fac2280037e5114001be288a000bf98050006fea028003fa5014001bea80a000fe54050005fecba0002fe65d00017eb2e8000bf19740005fcc7a0002fd63d0001dfa1e8000ef50f40005fcc5a0002fd62d0001bfa968000df54b400077e85a0003bd42d00017f30e8000bf58740006fca3a00037c51d0001dfa0e8000ef50740006fea1a00037d50d00017fb2c8000bf99640006fccb200027e65900017eb2c8000df59640004facb20002fc65900017eb248000bf98e40005fac720003be4390001de21c8000bf98a40005fac5200037f5290001bea948000bf98640005fac3200037e5190001be28c8000bf98240006fea1200037d5090001dfa048000fed0240005fecaa0002fe65500017eb2a8000bf19540005fec6a0003df63500016fb1a8000bf18d40007b8c6a0002dc6350001dfa1a8000ef50d40005fec4a0002fc6250001bfa928000df549400077e84a0003bd42500017fb0a8000bf18540006fca2a00037c5150001dfa0a8000ef50540006fea0a00037d5050001fda028000ef90140005feca20002fe6510001bf32880009f99440005faca200037d65100013eb288000bf19440005fcc820002fe6310001ef3188000b798c40005fac620003dd63100016eb188000ef90c40007788620002fe6210001f73108000bb98840005fac42000
  | 3 => 0xe3226200f794d31007baa698803df434c401ee21a6200bfd8931005f8c4988037f524c401bea926200f7cc931007ba64988037e514c401be28a6200fd90531007ea8298803f7314c401ef18a6200bfd8131005f8c098802ff650c4017f3286200bf59431005f8ca18802ff640c4017f3206200bf59031005f8c818802fe630c4017f3106200bf58831006fea4188037d520c4017f3086201df9443100ef8a218803df310c401fb1886200f74c431007ea6218802fe600c4017eb006200bfd9721005fccb908037e65c84013f32e4200bf59721006facb908027d65c84017e32e4200bfd9321005fcc990802fd64c84017e3264200bfd8f21005fcc790802fd63c84017e31e4200dfd4b21007dca5908037d52c8401f6a964200db54b21006fca3908037c51c84017f3064200bf58321005fecb108077f65884013fb2c4200bf99621005facb10802fc6588403be32c42009f19621005fec910802fe64884017eb244200bf19221005fec710802fe63884017eb1c4200bf18e21005fac5108037f5288401bea944200fb90a21007da8510803ee3288401f69944200bf9862100efca3108077c5188401f790c4200fdc8621005fcc110802fd60884017fb2a4200dfd9521004feca90802fe65484017eb2a4200bf19521006f8ca908027c65484017fb224200bf99121005fac890802fc64484017fb1a4200bf98d21005fac690802fc6348401bfa924200fb94921006faa490803ed5248401b6a924200df94521006f8a290803f72148401f710a4200bfd8121005f8c090802ff65084017f3284200df99421004fcca10802fd6508401beb2842009f59421005f8ca10802ff64084017f3204200ef990210057cc810802fd6408401deb204200af59021005f8c810802ff63084017f3184200f798c21005bcc610802fd6308401eeb184200b758c21005f8c610802fe6208401bfa904200df54821007dc8410803ed4208401f71904200fb4c821005fcc2108077e5108403be2884200fbc8421007ec4210803ed2108401fa9084200bf98021007f4c010802fa60084017eb004200fe58021005f2c010802fe64d40017eb26a000dfd5350006fca9a80037d54d4001be2a6a000bf98f50005fac7a80037f53d4001bf29ea000df54f50006f8a7a8002fe62d4001f7316a000bb98b50005fac5a8003ed62d400176b16a000dfd4b50006fca5a80037d52d4001be296a000bf98750005fac3a80037f51d4001bf28ea000df54750006f8a3a80037f64d4001bf326a000df59350006f8c9a80037f63d4001bf31ea000df58f50006f8c7a80037f43d4001bf21ea000df50f50006f887a80037f62d4001bf316a000db98b50006fac5a80027d62d4001b6b16a0009b58b50006f8c5a80037f42d4001bf216a000df50b50006f885a80037f32d4001bf196a000df4cb
  | 4 => 0x8037f5214401bf290a200df54851006f8a428802fe6114401bfa88a200fd94451006faa228803f551144017f300a200fe98051005f4c028802fd6014401fcb00a200be5805100efec8288037e64144019f320a200df590510067ac8288077c6414403bfb18a200df98c51006bcc6288037d6314401aeb18a201df18c51006fe86288037e4314401bea18a200df10c5100efec4288037e6214401b7310a200df58851004fac4288036d621440136b10a201df18851006fe84288037e4214401bea10a200df10851006fe64288037e3214401be990a200df0c85100efcc2288027e6114401bb308a201dfd8051006fcc0288037a6014401beb00a2009f58051006f2c028802796014403be300a200bfd9741005fccba08037e65d04013f32e8200bf59741006facba08027d65d04017e32e8200ef953410077aa9a0802fe63d04017eb1e8200ef90f410077887a0802fe62d0401f73168200bb98b41005fac5a0803ed62d040176b168200dfd4b41006faa5a0803bf42d0401dea168200df94741006f8a3a0802fe60d04017eb068200bfd9641005fccb20802fd65904017e32c8200bf59241005fcc720803de63904016f31c8200bf58e41007bac720802dd63904017f3148200bf58a41006fea5208037d52904017f30c8201df9464100ef8a320803bf4190401fba0c8200bf98241005fac120802ff6550401bfb2a82009fd9541005fccaa0802fd65504017e32a8200df19541004f8caa0803be5450401deaa28200bfd8d41005f8c6a0803be4350401de21a8200bfd8941005f8c4a08037f5250401bea928200efd09410077a84a08037e5150401be28a8200fdd05410077c82a0802ff60504017e3028200bfd9441005fcca20802fd65104017e3288200bf99041005fcc620802fd63104017f3108200bf58841006fea4208037d52104017f3088201df9444100ef8a220803bf4110401fb2088200ef50441007ea8220802fe60104017eb008200bfd9731005fccb988037e65cc4013f32e6200bf59731006facb988027d65cc4017e32e6200bfd9331005fcc998802fd64cc4017e3266200f794f31007baa798803df43cc401ee21e6200bf98b31007dcc598802ee62cc4017eb166200fb58b31005dac5988037f52cc401bea966200f7ccb31007ba65988037e51cc401be28e6200bf98331005fac198802ff658c4017f32c6200bf59631005f8cb18802ff648c4017f3246200ef992310057cc918802fd648c401deb246200af59231005f8c918802fd638c4017f3146200bf58a31006fea5188037d528c4017f30c6201df9463100ef8a318803f6418c401faa0c6200f7cc631007ee6318802fe608c4017eb046200bfd9531006feca988027f654c4017f32a6200bf59531005f8ca988037c654c4013e32a6200bfd9131005fcc898802fd644c4017
  | 5 => 0x8142005f8c0a1002ff65108017f3288400df99442004fcca21002fd6510801beb2884009f59442005f8ca21002fe64108017f3188400bf58c42005fcc4210037f5210801bea908400efd0842007dc8421003bd4210801f6a108400bf98442005fac221002fe60108017eb008400bfd9732005fccb99002fd65cc8017e32e6400bfd9332005fcc999002fd64cc8017e3266400f7d0f32007b887990037f52cc801bea966400bf98732005fac399002fe60cc8017eb066400bfd9632005fccb190037e658c8013f32c6400bf59632006facb190027d658c8017e32c6400bfd9232005fcc919003be648c8015f3246400bf592320077ac919002bd648c8017e3246400bf58e32005fcc5190037f528c801f72946400df54a32007daa5190036d528c801f72146400fb50a32007be6519003ef328c8017f30c6400bf58632005fcc119002fd608c8017fb2a6400bf99532005faca99002fc654c8017fb226400bf99132005fac899002fc644c801efa1a6400f710d32006fea499003ee524c801bea926400fb54932006daa499003ee424c801f6a126400fbcc932007bc6499002ff614c8017e30a6400bfd8132005f8c099002ff650c8017f3286400df99432004fcca19002fd650c801beb2864009f59432005f8ca19002ff640c8017f3206400bf59032005f8c819002fe630c8017f3106400dfd4832006faa419003df320c801f71906400f74c832007da6419002fe610c8017eb086400bf98032005fac019002fe64d44017eb26a200bf98f51005fac7a8802fe62d44017eb16a200dfd4b51006faa5a8802fe60d44017eb06a200bf59651005fcc928802fd6494401bfaa4a200df95251006faa9288037c54944017f31ca200bf58e51006fea7288037e5394401bea9ca200df14e51005fcc528802fd6294401bfa94a200df94a51006faa5288037c52944017f30ca200dfd4651007eea328802fe60944017eb04a201dfd9251006fcc9288037d6494403be324a201dfd8e51006fcc7288037d6394403be31ca200dfd0e51006fc87288037d4394401be21ca201dfd8a51006fcc5288037d62944013eb14a201df18a51006fe85288037e4294401bea14a200df10a51006fe65288037e3294401be994a200df0ca51004fcc3288077f6094401bf304a200df58251004fac1288077c60944017fb22a200bf19151005fec6a8802fc63544017fb12a200bf18951006fea4a88037d5254401fba8aa200df94551005fec0a8802fc60544017f328a200bf990510077cc828802be64144017eb20a200ef590510057ac8288037f5414401bf2a0a200df55051006f8a828802fe6314401ef318a200b798c51005fac628803dd63144016eb18a200dfd4c51006fca6288037d5314401be298a200bf98851007dcc428802ee62144017eb10a200fb58851005dac428
  | 6 => 0x17eb248600bf98e430077e8721803df4390c017f3148600bf58a43005fcc321802fd6190c017f3048600bf58243005fecaa1802fe6550c017eb2a8600bf19543007be86a1803be4350c017fb128600bf18943005fec2a1802fc6150c017fb028600bf18143005feca21802fe6510c01bf32886009f99443005faca218037d6510c013eb288600bf19443005fcc821802fe6310c01dfa188600f790c430077a8621803dd4310c01cea188600bf98843007dcc421802ee6210c017eb108600fb58843005dac421802fe6110c01fb3088600bd98443005fac221803f56110c017ab088600bf98043007f4c021802fa6010c017eb008600fe58043005f2c021802fe64d48017eb26a400dfd5352006fca9a90037d54d4801be2a6a400bf98f52005fac7a90037f53d4801bf29ea400df54f52006f8a7a9002fe61d48017eb0ea400bf98352005fac1a90037f64d4801bf326a400df59352006f8c9a90037f63d4801bf31ea400df58f52006f8c7a90037f43d4801bf21ea400df50f52006f887a90037f61d4801bf30ea4009f98752006fac3a90037c61d4801bfb06a400df98352006fac1a90027d60d4801be306a400bf59652004facb29002fe64948017eb24a400bf98e52005fac729002fe6294801bfa94a400fbd4a52005fcc329002fd61948017f304a400bf58252005fec8a9002fc6454801bfaa2a400df95152006faa8a90037c54548017fb1aa400bf18d52006fea6a90037e5354801bea9aa400df14d52007dea4a90037e52548017fb0aa400bf18552005fec0a9002fc6054801bfb22a400df99152006fac8a90037c6454801bfb1aa400df98d52006fac6a90037c6354801bfa1aa400df90d52006fa86a90037c4354801bfb12a400dbd8952006fec2a90037e6154801beb0aa400df18552004f8c2a90037f60548013fb02a400df98152006fac0a90037c60548017f328a4009f99452005fcc829002fd64148017f318a400bf58c52005fcc4290037f5214801f7290a400df54852007daa429002fe61148017eb08a400bf98052005fac029002ff65d08017f32e8400bf59742005f8cba1002fe63d08017eb1e8400ef90f420077887a10037f52d0801bea968400bf98742005fac3a1002fe60d08017eb068400bfd9642005fccb210037e65908013f32c8400bf59642006facb210027d65908017e32c8400bf59242005fcc721003de63908016f31c8400bf58e42007bac721002dd63908017f3148400dfd4a42007dca5210037d5290801f6a948400db54a420077e8521003ef42908017f30c8400bf58642005fcc121002fd60908017fb2a8400bf99542005facaa1002fc65508017fb1a8400bf18d420077c86a1003bc4350801bfa928400fb94942006faa4a1003ed5250801b6a928400fbd09420077c84a1002ff61508017e30a8400bfd
  | 7 => 0xd000050070010040040102c00e00c0e0000040000280b00000c0000a018020008000020040000100006c000170000081c8060a60000500902a000148000000080000e014000000000220300000e0020340083e00400024803000004028040020000280403a0182080200002c0380b0020300200601000c0080010a02000002014000028030040000180004c00802802002020008010080600082a00c070000000100000280c0300000280002c018008060020100080000a008020010020540000f00c0a4000020000840080c016004038010040040400303c0280a802000004018040000d40c80200c0000780900000c0000f00000401800006034000020100240b031008000068000160040000800000c0680500c054000050000101600000a0700280203e00c008000060880000301a0180000c0000240401b00a00c058070061000480000006c04000000078000010040a82001400c000058280760240000200601006000008000000020020000e8030120001a00303e0100480100802c120010020040001709801406800006050160010000180101000c000008030000000000a0020800903b0021080080e0020001000005c00000803006000088040340000d8040240980000b078018000050080580000b0120000000a05e014008070040000185a0440040901001a00bf98f54005fac7aa002fe62d50017eb16a800bf98754005fac3aa002fe60d50017eb06a800bf59654005fcc92a0037f5495001dfaa4a800cfd5254005fcc72a002fd63950017f314a800bf58a54005fcc32a002fd61950017f304a800bf582540077ea8aa0037e54550017fb1aa800bf18d54005fec4aa002fc62550017fb0aa800bf18554005fec0aa002fc60550017f328a800bf99054006fea82a003be5415001beaa0a800ef55054005fcc62a002fd63150017f310a800fb98854005dcc42a002fd6215001f6b10a800bb58854005fcc22a002fd61150017f300a800bf58054005fcc9a9802fd64d4c01bfaa6a600df55353005fcc5a9802fd62d4c017f30ea600bf58753005fcc1a9802fd60d4c017eb2ca600bf99253005fac929802fe6394c01bfa9ca600f7d4e53005fcc529802fd6294c017f30ca600bf58653005fcc129802fd6094c017fb22a600bf19153006fea8a98037d5454c01efa9aa600df94d53005fec4a9802fc6254c017fb0aa600bf18553005fec0a9802fc6054c017f328a600bf99053005fac829802fe6314c01bfa98a600f794c53006faa629803dd5314c017f310a600fb98853005dcc429802fd6214c01f6b10a600bb58853005fcc229802fd6114c017f300a600bf58053005fecba1802fe65d0c017eb2e8600bf19743005fcc5a1802fd62d0c017f30e8600bf58743005fcc1a1802fd60d0c017fb2c8600bf99643005facb21802fc6590c0
  | 8 => 0x83312cf1d99751ef224a5418511b80000022aa4b82d08f0002412028001b180023aa1e87f244af300009980012100000005532d84c13c2d88000001dc0003320f10000002fe0c900000011b04a1982548f807a1ac9902191f6aa59e70002f98b30a0b1121a8000cb8000000001de2c40000001f0912a48b3992e04280000000000000033a8000418000002b49453122240e42c4a2c8862ed03e1032178250000f38000130000a10002b280030093700000000022e00000000012019eb3380000033a20208a16280027c0002c88491bd02029b86c22d2dfa0b26e2f8a1d14a98193312f96ea93189178868097ae4a948a332b9ef8e931481f2258031300aa1ea11f20011781ab1c18d0b929ea6033881e1b5a28822a358b820f24c00004da4e9848ad08e07f9f1a78b3918c146aa0a3ba900000000f30001a183c2758001793380d31ae06fac02b70330b78001cb9a60af92c902000097321000176a032b82e9110174a2c315857800029045a5588c0c500004985b8521e28758000538e2a9a30680023f800313927801b1ea672658dcaa9a1627410b8f5b3e8d58ce964a20860a261a513897c9b7ac0b1183a32a0c38e79ac258a6d88500028080002f00000030e83b0002a200000021080031788084a800154aeb29e20600526c8361690b1316a1312d2f2b2e1010102e20fa8d491ca6615d1a913386b0d61b9a309e630f8003351552f8048277800170a2f80010f8bc3228a98008c825816d2a630a9529db9938de2d39b09be10096a96d90797b9028db1ff1092592a00000ac0000002da3242b994122397b2701d60000002430c180004004105080c08680000000007393f0000000c592b0000000f40000000000000c080014380009a8000149140df8000eda0080023400019d0002350000001249a21aa2ac0001ea93d80000023d286a8e2570c321da3e14e1da867a3884082eb2fa4d2f510b17a16700028b9ff9218001e8297a909798950a79ab87901c90a1fa8348fc01d8cc1820001a71a092e97e9e58000000000002b3abda9380a03f8b980101a0a2008010040040040901200004c0080c0040000300f00800c0080301c02404014004028028140060041481600800407809000020018460040700400100201c0380301006c000000000400101700a1c0098010160000001600401004007016000038010060040000100601002812000028020060020a8098000000100080b0080200001407001405803004014080010060000082e01e0080180a0000700000002a060008010000140000201a03006830032010048010200080400400002c0500601000c01809000030040000020640680100415c00805004000010020000640180107a0101500f0020300100102a00800817004004000000000100180400600c010020060480000700405c1f00
  | 9 => 0xad79d4b1d9743100108000bb98123f21880013580028f93b0f21af8151bb1cb0000000000002aa00010180033781800027a206af499a3272fa29b1d9081a6f2c60000000000ee98e8001e9a210390002b0274a1695410f000284a1f0eba50a5a2ca2a933633c80007000018628524e0002aa80c864ab78078478002d51e8b0f00010c1618062898c991c090a8f219b249ee33e062213980af619b163302b079ed97801433f8421378000b8a4518a0f18000110fdae833497d07c2dd96baa3a9a87880030b2140001f8aae0a21888d51e69f5a468ef0000a62bf09680007db0e3080001620000e5ae9aaf1e030383382895a2bfa3c0ab8a483015d80008b80025610a86bafd8001002861440878002331170000a6a01a490ca8612f381e8000002721c28d70011b39c38e69321532d932e90e9c30b61920000dc04e8f52820889720cf85926522b0e89288d9160ae38d82eb9e18f09cf9292c58cd800323ac79139209dca49884027b140002120000e49b4b2f0000001b80a5b201071a12f1800158af018ba360001e488eb26acfa69856846000188261000000116a970240c685e8000002eda5d91931f1b60772be1682729968638468a18b59fc0001970000831052632668eb17128100013a9fd14c99cb331b40ba9521c7ab10000ed0699aaaf92f69f91238000002db8000002a6a051ccafe9161fb0329bea43b1b80026a281add13d27d0d200019415183113180007218700008aa290070001d709e80026f9e0ac70a51cd270b40211a7a80d2409e798f1700c4330a26a7d83d8931b29960e000019c1fd8000bf00028d0002200c10629d58000cb2e100004413e8000bd298a9d2a523c8000000211d386d13c8f68d12d21a28fb995aee1ba80d9581122c68acae28c707121e00a86610cade24a8782ff9e5079a7b8e80350281c730432931884b24721a148868861a529fbae580225232d01a28ea072fc16e2ce2e7a328e39180be09e2102b22732c90920870aa843a182088f720fa6b059ae70e72879041640749aea0c2538d408809c04cabc9929a4322149a690119ab1d420790e05e2719df83caa30b0a5bae630a0dd15e8ca1dda7e87e9f3130a7f0a029f05f0d78c626a96504fa0ba3989817629694f9c9ae30b2a6d09b11d08cad48002cd00ea381912500003340382378fc88f8fe871acb8ada92b0cb3198d89dadaa2711a14b2368ea0cc80013a1729229c9058b1faa81a30c019a80800025f268a349af0002c10000b48002ff04b8571deb250de80015005100008d30620a9f20002510001cd96a2311069859d097586a2959258e601f92307d00024d9b88d890da3e99f0c221587a85011d8001430b3a4b211109830a12ad72bc2c1a8000011eac203b9c88630e30000003301ecb0c1bf96394e8221390000a3ab51e22678ba27b2e18bc85
  | 10 => 0x1b3f1590002d580002b86e095a8400927810809416ca9982b1d695130bae8aaca8a9352302bd07c8000001c012f0732761e42d6a552d60000001ce3261c682083193280680033d9a69fe1198000e20448ae0ab142b32a21969a15106000000098a8cabea5aa9fb0505fa4f94d0ee05402c9bbac2b368c7a2331b1478a2a7385d1668ef8b6aef023144ade80025995bb0491325fb3c02a186a4796607500032895580031e0471111f517c02e1bf2df00000b0769f82f4000000066a2514d856000084a481ee80022f07b00000019d9b227e14214800007400000006aa038001730f49ec0002c309030702998c8000001a9afb9bdad0182a33ab6048936a22ab408220e0001c800017e0199220f2b162838af1800001462639f9aba00012615f2c805a00014088b25e29cafa8e12751cc22d80002d8000000d180028d8a92eaa428001d8141ad133585580017a80021c94b80016880018e32c00f14580020c80000020a00000011592b8708f9a9186c8002b90db8d28cd0269e10b231310483d1fcaa4b2ca0d83724f1c60000fa1a8ae41bca9500880020431aa829ceab680030da5eb05a768b7156a772f10000910262e0903940283052ab32441fa0ecaabb278b502aace864173a7fa891a826ba4c9509a797d88d8658d38b182c05ab171b021b11e0ea96b015a5ca093022a88059d0320aa117732a88923196f0e98548191ca8949d780413400fa3704315e2940fb05d8002b0a2a00029daa4321b129c48321e315ab0d00015b31a0f93030ddafc860309aaea859539149ba3150bf9c1aa79ca0ff2d9b2b12c2ec325813a2809d26e910a982b59992e51d3085b1d2608160369381a3a3dad42afa0584f28a17780ba991f3b1906f0671f10760bea2e8da21b8258ec18313e1c22082f201231815c2ad1b32172f09a584519780992699e0ce1299841eb0001db000000156199a5d16586da221f2adb0df204a882c3a8720d0a8b08800194a418000129e929625c0342cc26423b17f80019b97f32987babbadc0bd8e50839ad077b0121c0d69df1492519bc29128b0002ca80032800020989c9a018b0388002cda14b1083ea42118aec9c10fd1471719a494a1f78c8b3d0168c28800b4035b3b8001952568000001f62ea1118d09988530b01c41d209b9240000001838000fe2278002cc8000000001c58000002390000aea4a11500000e00000023a0001c0acb00010d0378001908f6000000167aee85b16c0002d800005c9f431c9b50172011d880027ca710001fea2b9b72f700026212a93b9b92682402f78002fb00014f2921ed00016101b018b090000e0882aa18a41ad82fa299da0001273199d293100380019fad282380033b02480011aabb3001e39f015707e1088000000d99eb94c159889821ad184d092ae010586e8f8800000000000000091991
  | 11 => 0x2799f715787296015c9878c498a8ffa9c20e92a0bb257adc83a98fae6800262a3211f92daab2d08a82b189a000000017a8c0002baa5316f8519f489f89389f01d03f1c52fd0001d18000652d31280f00690cf0000000000e180000000000000033700025b2b8aef89913995f8812ad8000000000002460271b104e26181c0029348000001b6b2321f80012526c0000048000000000001898000398000000001930f79cf1d11360d00daaf5aa71d51dd2c52790a7288a6480005c2a281b93fac98960002458003
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x13154110007722154110007712154110005797588110006e86288110007695288110007e22188110004f87648110005797548110007e1214811000d7b75c4110007715084110004be74d9410004bd74d9410004de73d9410004dd73d9410004ee72d9410004ed72d94100047d76994100047d729941000c7e71994100047f725941000c7c71594100047f70594100047d70594100047e7519410004be7419410004bd7419410004de7319410004dd7319410004ee7219410004ed7219410004fa70194100047e75d90100047d75d9010004de73d9010004dd73d9010004ee72d9010004ed72d9010004bd76990100063e65990100063d659901000e3e519901000e3c51990100063e65590100063d655901000e3e515901000e3c51590100047e75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed7219010004f671190100047e75d8c100047d75d8c10004be74d8c10004bd74d8c10004ee72d8c10004ed72d8c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c1000e5e5198c1000e5c5198c100065e6558c100065d6558c100069e6458c100069d6458c1000e5e5158c1000e5c5158c100047e7518c100047d7518c10004be7418c10004bd7418c10004de7318c10004ee7218c10004ed7218c10004f67118c100047e75d88100047d75d8810004be74d8810004bd74d8810004de73d8810004dd73d88100047e75988100047d7598810004ed76988100066e65988100066d6598810006ae6498810006ad6498810006ce6398810006cd63988100066e75988100066d759881000e6e519881000e6c51988100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd63588100066e75588100066d755881000e6e515881000e6c51588100047e75188100047d7518810004be7418810004bd7418810004de7318810004dd7318810004ee7218810004f67118810004fa70188100047f76d48100047d76d48100063e64d48100063d64d48100065e63d48100065d63d48100066e62d48100066d62d48100047f76548100047d76548100063e64548100063d64548100065e63548100065d63548100066e62548100066d625481000d74715481000c7f759841000c7c75984100047e75980100047d75980100047d76d40100063e64d40100063d64d40100065e63d40100065d63d40100056d72d40100066e62d40100066d62d40100047f76540100063e64540100063d64540100065e63540100065d63540100066e62540100066d62540100067a6054010006b564c4010006d563c4010006e562c4010004f97684010006796584010006e96284010004f77644010006b56444010006d56344010006e56244010004fb7644010006796544010006e96244010
  | 1 => 0x4b10005d57390710005b5748c7100076552487100056d72d431000d7671d431000d747154310004ee7299610004ed72996100056d72996100066e72996100047d72996100066d72996100046d72996100067a70996100047f72596100047e75d92100047d75d9210004df7359210004dc73592100047e75192100047d7519210004de7319210004dd7319210004ee7219210004ed72192100047e75d8e100047d75d8e10004bf7458e10004bc7458e100047e7518e100047d7518e10004be7418e10004bd7418e10004ee7218e10004ed7218e100047e75d8a100047d75d8a100047e7598a100047d7598a100047e7518a100047d7518a10004be7418a10004bd7418a10004de7318a10004dd7318a100047f76d4a100047d76d4a100057970d4a100047f7654a100047d7654a100066f6254a100066c6254a10005747154a100056d72146100057970146100056d72d42100067a65542100057b76542100067b76542100057b725421000d78715421000579758821000769528821000579754821000d7b75c42100047d72d95100047e7599510004ee7299510004ed7299510004ef7259510004ec72595100047e76195100047d721951000c7e711951000c7c71195100067970195100047e75991100047d7599110004ee7299110004ed72991100047f75591100047c7559110004df7359110004dc7359110004ef7259110004ec72591100047e7598d100047d7598d10004ee7298d10004ed7298d100047f7558d100047c7558d10004bf7458d10004bc7458d10004ef7258d10004ec7258d100066f65d89100066c65d89100066f75d89100066c75d89100047e75989100047d7598910004ee72989100047f75589100047c75589100047e75189100047d7518910004be7418910004bd7418910004de7318910004dd7318910004ee76189100066f65189100066c65189100066e75189100066d7518910006ae7418910006ad7418910006ce7318910006cd7318910006e57118910006e970189100047e76d49100047c76d49100066f62d49100066c62d49100057970d49100047e76549100047c76549100066f62549100066c62549100047e76945100066f62945100066c62945100047e76145100056d72145100066f62145100066c6214510005d57390510004f47650510005b5748c510004f4764c510006e46288510004f476485100076552485100047e76d41100056d72d41100066f62d41100066c62d41100057671d41100057975941100067865941100047c76541100066f62541100066c6254110005747154110004f876541100067b76541100057876541100067876541100047876541100057b72541100076b625411000768625411000773715411000d7871541100077071541100077241541100077141541100077231541100077
  | 2 => 0x47e75988200047d75988200047d76d48200063e64d48200063d64d48200065e63d48200065d63d4820004ed76948200056d7594820006ad6494820006cd63948200047f76548200063e64548200063d64548200065e63548200065d63548200066e6554820006ad6454820006cd63548200056f76548200066f76548200066f64548200072e64548200066d64548200072d64548200062d64548200066f63548200074e63548200066d63548200074d63548200064d63548200056c71548200056f7054820006766598420006756598420006b66498420006b56498420006d66398420006d5639842000765529842000e77759842000e7475984200067752984200067552984200047f75584200047c75584200066d5258420006766558420006756558420006b66458420006b56458420006d66358420006d56358420007655258420006777558420006747558420006775258420006e65258420006755258420006e5525842000665525842000c7f76944200047d76944200063e64944200063d64944200065e63944200065d639442000e76619442000675619442000c7f76144200047d76144200063e64144200063d64144200065e63144200065d63144200056d721442000e766114420006756114420005797014420004ed76884200056f7588420006ad6488420006cd6388420006e561884200056d7508420006ad6408420006cd6308420006e56108420005e970084200047e75980200047d75980200066d52980200047d76d40200063e64d40200063d64d40200065e63d40200065d63d40200056d72d40200067661d40200067561d40200047f76540200063e64540200063d64540200065e63540200065d63540200067661540200067561540200056d75c8020006ad64c8020006cd63c8020006e561c8020007695288020006f16188020004ef76480200056d7548020006ad6448020006cd6348020006e56148020004fb7648020006f161480200047d72d971000e7671d971000e7970d9710004be7419710004bd7419710004de7319710004dd7319710004ee7219710004ed721971000e3e741971000e3d741971000e5e731971000e5d731971000e6e72197100047d721971000e6d72197100046d721971000e76711971000e797019710004de73d9310004dd73d93100047e75993100047d7599310004ee7299310004ed72993100047f75593100047c7559310004be74d8f10004bd74d8f100047e7598f100047d7598f10004ee7298f10004ed7298f100047f7558f100047c7558f100047e7598b100047d7598b100047f7558b100047c7558b100047e7518b100047d7518b10004be7418b10004bd7418b10004de7318b10004dd7318b1000c7e76d4b1000c7c76d4b1000c7e7654b1000c7c7654b100066e6254b100066d625
  | 3 => 0xf7359220004dc73592200047e75192200047d7519220004de7319220004dd7319220004f67119220004f571192200047e75d8e200047d75d8e20004bf7458e20004bc7458e200047e7518e200047d7518e20004be7418e20004bd7418e20004f67118e20004f57118e200057970d4a200066e6594a200057b7054a200066f7654a200066c7654a200066f6454a200066d6454a200066f6354a200066d6354a200056c7154a200056f7054a200076b7054a20007687054a200047f75586200047c75586200066d525862000c7f76946200047d769462000579709462000c7f76146200047d76146200056d72146200057970146200056f75886200056d7508620005e970086200056d72d42200056d75c8220004ed72995200047d72995200066d72995200046d729952000c7e71995200047d7099520006797099520004f77159520004f471595200057471595200047f72595200066f725952000677715952000c7c71595200067471595200047471595200047f70595200067b70595200047e75d91200047d75d9120004df7359120004dc73591200047e75191200047d75191200047e75d8d200047d75d8d20004bf7458d20004bc7458d200047e7518d200047d7518d200057970d49200057b70549200066d6590920005cd7390920004ec76509200066d65509200066d658c920005ad748c920004ec764c9200066d654c9200047e75d85200047d75d85200047e75185200047d7518520004be7418520004bd7418520004de7318520004dd73185200047d76945200056d72945200057970945200047d76145200056d721452000677611452000e746114520005797014520004ee76c85200066d65c85200066d65485200056d72d41200047f76541200047d76541200056f72541200066d6588120004be74d9420004bd74d9420004de73d9420004dd73d9420004f671d9420004f571d94200047d76994200066e729942000c7e71994200047f72594200047d725942000c7c71594200047e7519420004be7419420004bd7419420004de7319420004dd7319420004f67119420004f571194200047e75d90200047d75d9020004de73d9020004dd73d9020004f671d9020004f571d9020004bd76990200063e65990200063d65990200063e65590200063d65590200047e75190200047d7519020004be7419020004de7319020004dd7319020004ee7219020004f67119020004f571190200047e75d8c200047d75d8c20004be74d8c20004bd74d8c20004f671d8c20004f571d8c20004dd7698c200065e6598c200065d6598c200069e6498c200069d6498c200065e6558c200065d6558c200069e6458c200069d6458c200047e7518c200047d7518c20004be7418c20004bd7418c20004de7318c20004ee7218c20004f67118c20004f57118c20
  | 4 => 0x943000c7c71594300047e7519430004be7419430004bd7419430004ee7219430004ed7219430004f67119430004f571194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d9030004bd76990300063e65990300063d65990300063e65590300063d65590300069c73590300047e75190300047d7519030004be7419030004de7319030004ee7219030004ed7219030004f67119030004f57119030004fa7019030004dd76d0c300069d64d0c30004dd7610c300069d6410c30005d97010c300047e75988300047d75988300066e65988300066d6598830006ae6498830006ad64988300066e75988300066d75988300066e65588300066d6558830006ae6458830006ad64588300066e75588300066d7558830006cf4358830006cc43588300047f76d48300047d76d48300063e64d48300063d64d48300066e62d48300066d62d48300047f76548300047d76548300063e64548300063d64548300066e62548300066d6254830006766598430006756598430006b66498430006b56498430006e66298430006e5629843000e77759843000e7475984300067752984300067552984300047f75584300047c7558430006766558430006756558430006b66458430006b56458430006e66258430006e56258430006777558430006747558430006d74358430006d4435843000677525843000675525843000c7f76944300047d76944300063e64944300063d64944300066e62944300066d629443000e76619443000675619443000c7f76144300047d76144300063e64144300063d64144300056d72144300066e62144300066d621443000e7661144300067561144300057970144300047e75980300047d75980300047d76d40300063e64d40300063d64d40300056d72d40300066e62d40300066d62d40300067661d40300067561d40300047f76540300063e64540300063d64540300066e62540300066d62540300067661540300067561540300069d64cc030006cd62cc030006d561cc030006b9648c030004df764c0300059c744c0300069d644c030006cd624c030006d5614c030004fb764c030006b9644c03000c7e719972000c7c71597200047e75d93200047d75d9320004de73d9320004dd73d93200047e75193200047d75193200047e75d8f200047d75d8f20004be74d8f20004bd74d8f200047e7518f200047d7518f200066d6590b20005cd7390b200066d6550b200066d658cb20005ad748cb200066d654cb200047f75587200047c755872000c7f76947200047d76947200056d729472000c7f76147200047d76147200056d72147200057970147200066d65c87200066d65487200056d72d43200056f72543200066d729962000c7e719962000c7c71596200047e75d92200047d75d9220004d
  | 5 => 0xc7f76144400047d76144400065e63144400065d63144400056d72144400066e62144400066d621444000e7661144400067561144400057970144400047e75980400047d75980400047d76d40400065e63d40400065d63d40400056d72d40400066e62d40400066d62d40400067661d40400067561d40400047f76540400065e63540400065d63540400066e62540400066d62540400067661540400067561540400069d63d0040006ad62d0040006b561d0040006d96390040004bf76500400059c73500400069d6350040006ad6250040006b56150040004fb7650040006d96350040004ee7219730004ed72197300047e75193300047d7519330004ee7219330004ed7219330004f67119330004f571193300069c6450f300047e7598b300047d7598b30004be7498b30004bd7498b300066e6254b300066d6254b300074d524cb30004be7498730004bd74987300047f75587300047c75587300056d7214730005797014730005cd72cc7300056d72d4330004ee7299630004ed72996300056d72996300066e72996300047d72996300066d72996300046d729963000c7e71996300047f725963000c7c71596300047e75d92300047d75d92300047e75192300047d7519230004ee7219230004ed7219230004f67119230004f571192300069f6410e30005d97010e300047e7598a300047d7598a300047f76d4a300047d76d4a300047f7654a300047d7654a300047f75586300047c7558630004ef7258630004ec725863000c7f76946300047d769463000c7f76146300047d76146300056d72146300057970146300056d72d4230007984390230005d873502300079b4350230004be7499530004bd7499530004ee7299530004ed7299530004bf7459530004bc7459530004be7499130004df73591300047e75191300047d7519130004ee7219130004ed7219130004f67119130004f57119130004be76191300063e75191300063d75191300069d7319130006ae7219130006ad7219130006b67119130006b57119130006b97019130004de7690d300069c6490d30004dc7650d300069c6450d300047e75189300047d75189300063f64d49300063c64d49300063f64549300063c64549300066f62549300066c62549300069c64cc9300069c644c9300074d524c9300047e75d85300047d75d85300063f64945300063c64945300063f64145300063c64145300056d72145300057970145300069c64cc530005cd72cc5300069c644c5300063f64d41300063c64d41300056d72d41300063f64541300063c6454130006b864901300079a4390130004f876501300079943501300069c648c130004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d94300047d76994300047d729943000c7e71994300047f725
  | 6 => 0xf75587400047c75587400056d7214740005797014740005ad72d07400056d72d4340004ee7299640004ed72996400056d72996400066e72996400047d72996400066d72996400046d729964000c7e71996400047f725964000c7c7159640005b97010e400047e7598a400047d7598a400047f76d4a400047d76d4a400047f7654a400047d7654a400047f75586400047c7558640004ef7258640004ec725864000c7f76946400047d769464000c7f76146400047d76146400056d72146400057970146400056d72d42400073950d0240004de7399540004dd7399540004ee7299540004ed7299540004df7359540004dc73595400047e7518d400047d7518d40004ee7218d40004ed7218d40004f67118d40004f57118d400065e7518d400065d7518d40006ce7218d40006cd7218d40006d67118d40006d57118d40006d97018d40004be76d0d400069c63d0d400069c6350d400047e75189400047d75189400065f63d49400065c63d49400065f63549400065c63549400066f62549400066c62549400069c63d09400069c63509400072d52509400047e75d85400047d75d85400065f63945400065c63945400065f63145400065c63145400056d72145400057970145400069c63d0540005ad72d05400069c63505400065f63d41400065c63d41400056d72d41400065f63541400065c63541400069c6390140004de73d9440004dd73d9440004ee72d9440004ed72d9440004f671d9440004f571d94400047d76994400047d729944000c7e71994400047f725944000c7c71594400047e7519440004de7319440004dd7319440004ee7219440004ed7219440004f67119440004f571194400065e6598c400065d6598c400065e6558c400065d6558c40004bd7690c400069d6390c400069d6310c40005b97010c400047e75988400047d75988400066e65988400066d6598840006ce6398840006cd63988400066e75988400066d75988400066e65588400066d6558840006ce6358840006cd63588400066e75588400066d7558840006ae4358840006ac43588400047f76d48400047d76d48400065e63d48400065d63d48400066e62d48400066d62d48400047f76548400047d76548400065e63548400065d63548400066e62548400066d6254840006766598440006756598440006d66398440006d56398440006e66298440006e5629844000e77759844000e7475984400067752984400067552984400047f75584400047c7558440006766558440006756558440006d66358440006d56358440006e66258440006e56258440006777558440006747558440006b64358440006b4435844000677525844000675525844000c7f76944400047d76944400065e63944400065d63944400066e62944400066d629444000e766194440006756194440
  | 7 => 0x87500055e73087500055d73087500066d62087500057a70087500057970087500066d6254a5000e7661946500056d72146500057970146500056d72d4250004ee7219150004ed72191500063f64951500056e72151500056d7215150004ee7218d50004ed7218d500065f6394d500056e7214d500056d7214d500066f62549500066c62549500047e7614950004be7418550004bd7418550004de7318550004dd7318550004ee7218550004ed72185500047e76d455000e7461945500057a70945500053e74145500053d74145500055e73145500055d73145500056e72145500056d72145500057a70145500063f64991500057970991500055f73591500055c73591500057b70591500056e72191500056d72191500065f6398d50005797098d500053f7458d500053c7458d500057b7058d500056e7218d500056d7218d500047e7610d500047d7610d500071d4310d500056e7210d500056d7210d50005767110d50005757110d500057a7010d50005797010d5000c7e71d89500057970989500057771589500057471589500057b70589500066d62189500047e76909500047d76909500055e73909500055d73909500047e76109500047d76109500047e768c9500047d768c9500053e748c9500053d748c9500047e760c9500047d760c9500057970985500056f72585500056c72585500057b70585500053e74185500053d74185500055e73185500055d73185500056e72185500056d721855000e3e741855000e3d741855000e5e731855000e5d731855000e6e72185500047d721855000e6d72185500046d721855000e7970185500047e76d05500047d76d05500056e72d05500056d72d05500055e73905500055d73905500057a70905500057970905500047f76505500047c76505500057a70105500057970105500047e76cc5500047d76cc5500056e72cc5500056d72cc5500053e748c5500053d748c5500057a708c55000579708c5500047f764c5500047c764c5500057a700c55000579700c5500047e76c85500047d76c85500067461c855000c7c76885500066f62885500057a70885500057970885500047f76485500047c76485500047e76085500047d76085500053e74085500053d74085500055e73085500055d73085500066f620855000e7461085500057a70085500057970085500056e72d81500056d72d81500076a72d81500076972d81500057971d81500066e72994500066d72994500066d62d48500047f76548500047d76944500056d721445000e7661144500057970144500056d72d40500047f7654050004fb76540500067a6554050004ee7219740004ed72197400047e7598b400047d7598b40004de7398b40004dd7398b400066e6254b400066d6254b400072d5250b40004de7398740004dd73987400047
  | 8 => 0x6e9325802100e7a515802100e785158021006eb2158021006f22158021006e92158021006f121580210063e64d53500056e72153500056d72153500057a70153500065e63d4f500056e7214f500056d7214f500066e7558b500066f5458b500066e5458b500066d5458b500066c5458b500066f5358b500066e5358b500066d5358b500066c5358b500066d62d4b500066d6294b500066e6254b500066d6214b500066d62d47500066e62947500066d62947500066d62547500053e74147500053d74147500055e73147500055d73147500056e72147500056d72147500066e62147500066d621475000e7661147500055e73d93500055d73d93500056e72d93500056d72d93500057970d93500063f64993500056e72193500056d72193500057970193500053e74d8f500053d74d8f500056e72d8f500056d72d8f500057970d8f500065f6398f500056e7218f500056d7218f50005797018f500047e7610f500047d7610f500071d4310f500056e7210f500056d7210f50005767110f50005757110f500057a7010f50005797010f500057970d8b5000c7c7158b500066f7658b500066f6458b500066e6458b500066d6458b500066c6458b500066f6358b500066e6358b500066d6358b500066c6358b500066f7458b500066e7458b500066d7458b500066c7458b500066f7358b500066e7358b500066d7358b500066c7358b500066f4358b500066e4358b500066d4358b500066c4358b500066f7158b500066e7158b500066d7158b500066c7158b500066f7058b500066d7058b500066d6218b50005797018b500066d62d0b500047e7690b500047d7690b500055e7390b500055d7390b500066d6290b500066d6250b500047e7610b500047d7610b500066d6210b500066d62ccb500047e768cb500047d768cb500053e748cb500053d748cb500066d628cb500066d624cb500047e760cb500047d760cb500066d620cb500056e72d87500056d72d87500066d62d87500057970d87500066e62987500066d62987500047d72987500066d62587500053e74187500053d74187500055e73187500055d73187500056e72187500056d72187500066e62187500066d62187500057970187500047e76d07500047d76d07500056e72d07500056d72d07500066d62d07500055e73907500055d73907500066d62907500047f76507500047c76507500066d62507500066d62107500047e76cc7500047d76cc7500056e72cc7500056d72cc7500066d62cc7500053e748c7500053d748c7500066d628c7500047f764c7500047c764c7500066d624c7500066d620c7500047e76c87500047d76c87500066d62c875000c7f76887500066d62887500047f76487500047c76487500066d62487500047e76087500047d76087500053e74087500053d740
  | 9 => 0xe74d8d21004bd74d8d210047e7598d210047d7598d21004ed7298d210047f7558d210047c7558d210047e76d49210057671d49210056d75949210066c65949210047c7654921005747154921004ec7654921005e471549210066f76549210066c76549210046c76549210066f64549210066d64549210066f63549210066d635492100767715492100d6c71549210076471549210056471549210056f70549210047e76945210047e76145210056d72145210057970145210076552c852100d6f75885210047e75181210047d7518121004be7418121004bd7418121004de7318121004dd73181210066d5218121004be74d9421004bd74d9421004de73d9421004dd73d9421004fa70d9421004f970d94210047d769942100c7e71994210047d709942100c7c71594210047f70594210047e7519421004be7419421004bd7419421004de7319421004dd7319421004ee7219421004fa7019421004f970194210047e75d90210047d75d9021004de73d9021004dd73d9021004fa70d9021004f970d9021004bd76990210063e65990210063d6599021006ae729902100e3e519902100e3c51990210063e65590210063d655902100e3e515902100e3c51590210047e75190210047d7519021004be7419021004de7319021004dd7319021004fa7019021004f970190210047e75d8c210047d75d8c21004be74d8c21004bd74d8c21004fa70d8c21004f970d8c21004dd7698c210065e6598c210065d6598c210069e6498c210069d6498c21006ce7298c2100e5e5198c2100e5c5198c210065e6558c210065d6558c210069e6458c210069d6458c2100e5e5158c2100e5c5158c210047e7518c210047d7518c21004be7418c21004bd7418c21004de7318c21004fa7018c21004f97018c210047e75988210047d75988210047d76d48210063e64d48210063d64d48210065e63d48210065d63d48210047f76548210063e64548210063d64548210065e63548210065d63548210066e6254821004ed76908210066d6590821005cd7390821006cd63908210066d6550821006ae6450821006cd6350821004ed768c8210066d658c821005ad748c821006ad648c8210066d654c821006ad644c821006ce634c82100c7f759842100c7c75984210066d65c8421004ef76484210066d654842100f645148421004f776484210076752484210047e75980210047d75980210067a6598021006796598021006ba6498021006b96498021006da6398021006d963980210067a75980210067975980210067b529802100679529802100e7a519802100e7851980210067a6558021006796558021006ba6458021006b96458021006da6358021006d963580210067a75580210067975580210067b5258021006795258021006ea4258021006e94258021006ea3258021
  | 10 => 0x4a310063d6454a310066e6254a310066d6254a3100d747154a31006b664506310069e64cc63100f5651cc6310047e75982310047d75982310047d72d95310047d70d95310047e7599531004ee7219531004ed72195310047e76195310056d72195310065d73195310066e72195310047d72195310066d72195310046d72195310047d70195310047e75991310047d7599131004ee7299131004ed72991310047f75591310047c75591310065c6594d31004dc7654d31004de76d0d310055d7510d310069d6410d31005cd7210d31005d67110d31005d97010d310047e75189310047d75189310047e76d49310047c76d49310047e76549310047c76549310057471549310074d524c9310047e76945310047e76145310056d7214531005797014531005d67390531004f476505310079443505310059e748c5310047e75181310047d7518131004be7418131004bd7418131004ee7218131004ed7218131004be7419431004bd7419431004de7319431004ee7219431004ed7219431004fa7019431004f97019431004de73d90310047e75190310047d7519031004ee7219031004ed7219031004f67119031004fa7019031004f970190310047e7598c310047d7598c310047e75988310047d75988310066e62548310066d6254831004be7498431004bd7498431004df764c431004f7764c4310047e75980310047d75980310066e72997210047d70997210047f70597210047e75d93210047d75d9321004de73d9321004dd73d93210047e75193210047d75193210047e75d8f210047d75d8f21004be74d8f21004bd74d8f210047e7518f210047d7518f210066e6554b210056f7654b210066f7654b210066f6454b210066d6454b210066f6354b210066d6354b2100d6c7154b210056f7054b210056d72147210057970147210047e75983210047d75983210066d529832100e6d72d962100e7671d96210047d70d9621004be7419621004bd7419621004de7319621004dd7319621004fa7019621004f9701962100e3e741962100e3d741962100e5e731962100e5d731962100e6d721962100e76711962100e7a70196210047d701962100e797019621004797019621004de73d9221004dd73d92210047e75992210047d75992210047f75592210047c7559221004be74d8e21004bd74d8e210047e7598e210047d7598e210047f7558e210047c7558e2100d7671d4a2100d747154a210066f6590a21005cd7390a210066f6550a210066f658ca21005ad748ca210066f654ca2100e6f65c86210047e75982210047d75982210047f75582210047c75582210047d70d95210047e75995210047e76195210066d72195210047d7019521004de73d9121004dd73d91210047e75991210047d7599121004ed72991210047f75591210047c7559121004b
  | 11 => 0x4de7319641004dd7319641004ee7219641004ed7219641004fa7019641004f970196410047e7598e410047d7598e41004ee7298e41004ed7298e410065e7598e410065d7598e41006ce7298e41006cd7298e41006d67198e4100e5e5198e4100e5c5198e4100e5e5158e4100e5c5158e410047e7598a410047d7598a410065e63d4a410065d63d4a410065e6354a410065d6354a410066e6254a410066d6254a4100d747154a410069e63d064100f3651d06410047e75982410047d75982410047d72d95410047d70d95410047e7599541004ee7219541004ed72195410047e76195410056d72195410063d74195410066e72195410047d72195410066d72195410046d72195410047d70195410063c6595141004bc76551410053d7510d41005ad7210d41005b67110d41005b97010d410047e75189410047d75189410047e76d49410047c76d49410047e76549410047c76549410057471549410072d52509410047e76945410047e76145410056d72145410057970145410059e73905410047e75181410047d7518141004de7318141004dd7318141004ee7218141004ed7218141004be7419441004de7319441004dd7319441004ee7219441004ed7219441004fa7019441004f970194410047e75990410047d75990410047e75988410047d75988410066e62548410066d6254841004bf7650441004f776504410047e75980410047d7598041004ee72d9731004ed72d97310065e73997310047d72997310047d70997310047f72597310047f7059731004ee7219731004ed72197310047e75d93310047d75d9331004ee72d9331004ed72d93310047e75193310047d7519331004ee7219331004ed7219331004fa7019331004f970193310065e6554f310055d7510f310069d6410f31005cd7210f31005d97010f310047e7598b310047d7598b31004be7498b31004bd7498b310066e6598b310066d6598b310066e7598b310066d7598b31006ae7498b31006ad7498b310066e6558b310066d6558b310066e7558b310066d7558b31006cf4358b31006cc4358b310047f76d4b310047d76d4b310066e62d4b310066d62d4b310047f7654b310047d7654b310066e6254b310066d6254b31006ce624cb310074d524cb310066e62947310066d62947310056d72147310066e62147310066d62147310057970147310047e75983310047d7598331004be74d9631004bd74d9631004be7419631004bd7419631004ee7219631004ed7219631004fa7019631004f970196310047e75992310047d7599231004ee7299231004ed72992310063e75992310063d7599231006ae7299231006ad7299231006b6719923100e3e519923100e3c519923100e3e515923100e3c51592310047e7598a310047d7598a310063e64d4a310063d64d4a310063e645
  | 12 => 0xc31588510066f70588510066e70588510066d70588510066c705885100e6f105885100e6c10588510066d62d085100d7671d08510057571d085100c7e76908510047d76908510055e73908510055d73908510066d62908510066d625085100c7e76108510047d76108510066d62108510066d62cc85100d7671cc8510057571cc85100c7e768c8510047d768c8510053e748c8510053d748c8510066d628c8510066d624c85100c7e760c8510047d760c8510066d620c85100e76719845100f36649845100f35649845100f56639845100f55639845100f66629845100f6562984510066d629805100d79769805100f3a649805100f39649805100f5a639805100f59639805100e7b629805100f6a629805100679629805100f69629805100669629805100e7a619805100f7261980510063e64580510063d64580510065e63580510065d63580510066e62580510066d625805100e7860580510047f725805100e7b105805100e78105805100d7b76580510067b765805100e7b64580510067a645805100f3a64580510063a645805100679645805100f39645805100639645805100e78645805100e7b63580510067a635805100f5a63580510065a635805100679635805100f59635805100659635805100e78635805100e7b62580510067a625805100f6a62580510066a625805100679625805100f69625805100669625805100e78625805100e7a615805100f7261580510067b74580510067a74580510067974580510067874580510067b73580510067a73580510067973580510067873580510067b43580510067a43580510067943580510067843580510067b72580510067a72580510067972580510067872580510067b42580510067a42580510067942580510067842580510067b32580510067a325805100679325805100678325805100e7a715805100e7a415805100e78415805100e7a315805100e78315805100e7a215805100e782158051004ee72d9741004ed72d97410063e74997410047d72997410047d70997410047f72597410047f7059741004ee7219741004ed72197410063e65953410063e65553410053d7510f410069d6310f41005ad7210f41005b97010f410047e7598b410047d7598b41004de7398b41004dd7398b410066e6598b410066d6598b410066e7598b410066d7598b41006ce7398b41006cd7398b410066e6558b410066d6558b410066e7558b410066d7558b41006ae4358b41006ac4358b410047f76d4b410047d76d4b410066e62d4b410066d62d4b410047f7654b410047d7654b410066e6254b410066d6254b41006ae6250b410072d5250b410066e62947410066d62947410056d72147410066e62147410066d62147410057970147410047e75983410047d7598341004de73d9641004dd73d9641
  | 13 => 0x8c510069d6498c510069e6458c510069d6458c510065f5458c510065d5458c510063d64d4c510065e63d4c5100d7671d4c510065d6394c510063d6454c510065e6354c510056e7214c510056d7214c5100d767114c51006ae6498851006ad6498851006ce6398851006cd6398851006ae6458851006ad6458851006ce6358851006cd63588510066e75588510066f54588510066e54588510066d54588510066c54588510066f53588510066e53588510066d53588510066c53588510063e64d48510063d64d48510065e63d48510065d63d48510066d62d485100d7671d48510047d76948510066d62948510063e64548510063d64548510065e63548510065d63548510066e62548510066d621485100d7671148510066d62d44510047f76544510066d6254451004f77654451006ba6498051006b96498051006da6398051006d96398051006ea6298051006e962980510067b5298051006795298051006ba6458051006b96458051006da6358051006d96358051006ea6258051006e962580510067a75580510067b54580510067a54580510067954580510067854580510067b53580510067a53580510067953580510067853580510067b52580510067a52580510067952580510067852580510067b515805100679515805100e3f649905100d3d769905100e3f629905100e3e619905100e3f609905100d3f76590510063f765905100e3f635905100e3f625905100e3e615905100e3f605905100e5f6398c5100d5d7698c5100f1e6498c5100f1d6498c5100e5f6298c5100e5e6198c5100e5f6098c510063d6458c5100d5f7658c510065f7658c5100e5f6458c5100f1e6458c510065d6458c5100f1d6458c510061d6458c5100e5f6258c5100e5e6158c5100e5f6058c5100c7e7610c510047d7610c510071d4310c510056e7210c510056d7210c5100d767110c51005757110c510057a7010c51005797010c5100d6d769885100f2e649885100f2d649885100f4e639885100f4d639885100e6e619885100e6f60988510063e64588510063d64588510065e63588510065d635885100e6c625885100e6e215885100e6c21588510047f705885100d6f76588510066f765885100e6f64588510066e645885100f2e64588510062e64588510066d645885100f2d64588510062d645885100e6c645885100e6f63588510066e635885100f4e63588510064e63588510066d635885100f4d63588510064d635885100e6c635885100e6e615885100e6f605885100e6c60588510066f74588510066e74588510066d74588510066c74588510066f73588510066e73588510066d73588510066c73588510066f43588510066e43588510066d43588510066c435885100e6e715885100e6c715885100e6e415885100e6c415885100e6e315885100e6
  | 14 => 0x47e75192320047d75192320063e64d4a320063d64d4a32006ad6494a320063e6454a320063d6454a320066e6554a32006ad6454a320056f7654a320066f7654a320066f6454a320072e6454a320066d6454a320072d6454a320062d6454a320056c7154a320056f7054a320056d7590a320066d6590a320066d6550a32006ae6450a320069e64cca320074d52cca320047f75586320047c75586320066d52586320047e75982320047d75982320066d52982320047e75191320047d7519132004de76d0d320069d6410d32005ce7210d32005d57110d32005d97010d320056d7594932004ec76549320066f76549320066c76549320066f64549320066d64549320074f73549320074c73549320074f43549320074c43549320056c71549320056f70549320056d7590932005ce7390932004ec76509320078c43509320059e748c9320074d528c9320047e75d85320047d75d85320066d52d85320047e75181320047d7518132004be7418132004bd74181320066d5218132004f67118132004f571181320047d769943200c7e71994320047d709943200c7c71594320047f70594320047e7519432004ee72194320047e75d90320047d75d9032004de73d90320047e75190320047d7519032004ee7219032004f67119032004f57119032004fa7019032004f970190320047e75988320047d7598832004be7498832004bd74988320047d76d48320047f76548320066e62548320066d658c832004df764c8320074d524c832004ef764c8320066d654c8320047f75584320047c75584320047e75980320047d75980320066d62d4b51004ee7299251004ed72992510063d649525100d76719525100575719525100d7471552510056e72152510056d7215251004ee7298e51004ed7298e510065d6394e5100d767194e51005757194e5100d747154e510056e7214e510056d7214e5100d767194a510066e6254a510066d6254a5100d747154a51004ef7258251004ec72582510056e72992510056d729925100e3c64592510056e7298e510056d7298e5100e5c6358e5100c7e7610e510047d7610e510071d4310e510056e7210e510056d7210e5100d767110e51005757110e510057a7010e51005797010e5100e6f6298a5100e6e2158a5100e6c2158a510047f7058a5100c7e7690a510047d7690a510055e7390a510055d7390a5100c7e7610a510047d7610a5100c7e768ca510047d768ca510053e748ca510053d748ca5100c7e760ca510047d760ca5100e7b60982510056f72582510056c72582510047f72582510066f72582510046f72582510066c725825100e7b105825100e7810582510047e76d49510066f62549510063e64d505100d7671d50510063d64950510063e64550510056e72150510056d721505100d7671150510069e649
  | 15 => 0xd7298d52005767198d52005757198d520056f7258d520056e72d0d520056d72d0d520056e7290d520056d7290d520047e7610d520047d7610d520071d4310d520056e7210d520056d7210d52005767110d52005757110d520057a7010d52005797010d520056d74d89520056d73d89520056d71d89520056e70d89520053e74185520053d74185520055e73185520055d73185520057a701855200579701855200e3e741855200e3d741855200e5e731855200e5d731855200e7a70185520047d701855200e79701855200479701855200c7e71d81520057771581520057471581520047f7654852004ef76548520066e6554852004f671d9742004f571d97420069d6310f42005b57110f42005b97010f42004de7398742004dd73987420047f75587420047c75587420047e75983420047d7598342004de73d9642004dd73d96420066e729964200c7e71996420047d709964200c7c71596420047f7059642004de7319642004dd73196420065e6598e420065d6598e42006ce7298e420065e6558e420065d6558e420065e63d4a420065d63d4a42006cd6394a420065e6354a420065d6354a420066e6554a42006cd6354a420056f7654a420066f7654a420074e6354a420066d6354a420074d6354a420064d6354a420056c7154a420056f7054a420069e63d0a420072d52d0a420047f75586420047c75586420066d52586420047e75982420047d75982420066d52982420047e7518d420047d7518d42005ae7210d42005b57110d42005b97010d420056d7594942004ec76549420066f76549420066c76549420072f74549420072c74549420066f63549420072e43549420072c43549420056c71549420056f70549420059e73909420072d52909420047e75d85420047d75d85420066d52d85420047e75181420047d7518142004de7318142004dd73181420066d5218142004f67118142004f571181420047d769944200c7e71994420047d709944200c7c71594420047f70594420047e7519442004ee72194420047e75988420047d75988420047d76d48420047f76548420066e62548420066d6590842004bf76508420072d5250842004ef76508420066d65508420047f75584420047c75584420047e75980420047d7598042004f671d9732004f571d97320047e75193320047d7519332004f67119332004f57119332004fa7019332004f970193320069d6410f32005d57110f32005d97010f32004be7498732004bd74987320047f75587320047c75587320047e75983320047d7598332004be74d9632004bd74d96320066e729963200c7e71996320047d709963200c7c71596320047f7059632004be7419632004bd74196320047e75d92320047d75d92320063e65992320063d6599232006ae72992320063e65592320063d6559232
  | 16 => 0x50540047f7655054004bf76550540066e75588540066f54588540066d54588540063e64d5353004be7498653004bd7498653004ee7219153004ed72191530047f7654c53004df7654c530066e75588530066f53588530066d5358853004ee7219743004ed72197430047e7598b430047d7598b430047f75587430047c75587430047e75983430047d7598343004ee7219643004ed72196430047e7598a430047d7598a430047f75586430047c75586430047e75982430047d7598243004ee7219543004ed72195430047e75189430047d75189430047e75d85430047d75d8543004ee72d8543004ed72d85430047e75181430047d7518143004ee7218143004ed7218143004f67118143004f57118143004ee72d9443004ed72d9443004f671d9443004f571d9443004fa70d9443004f970d94430047d76994430047d729944300c7e71994430047d70994430047f725944300c7c71594430047f70594430047e7519443004ee7219443004ed7219443004f67119443004f57119443004fa7019443004f970194430059d7490c43004bf7650c43004df7650c430059f7650c430069f7650c430071e6550c430071d6550c430059f7250c430059f7150c430059c7050c430047e75988430047d75988430066e65988430066d65988430078d43988430066e75988430066d75988430066e65588430066d65588430078d43588430066e75588430066d7558843006766598443006756598443007954398443006e66298443006e5629844300e77759844300e7475984430047f75584430047c7558443006766558443006756558443007954358443006e66258443006e562584430067775584430067475584430047e75980430047d75980430067a6598043006796598043007994398043006ea6298043006e96298043006f26198043006f161980430067a75980430067975980430069d43580430067a6558043006796558043007994358043006ea6258043006e96258043006f26158043006f161580430067a7558043006797558043006bb4358043006da4358043006b94358043006d943580430069943580430063e64d53520056e72153520056e7214f520056d72d93520063f64993520056d72193520056d72d8f520056d7218f520047e7610f520047d7610f520071d4310f520056e7210f520056d7210f52005767110f52005757110f520057a7010f52005797010f520047d70987520053e74187520053d74187520055e73187520055d73187520057a701875200579701875200c7c71583520063f64951520056e72951520056e72151520056e7294d520056e7214d52004be7418552004bd7418552004de7318552004dd7318552004fa7018552004f970185520063f64991520056d72991520057671991520057571991520056f72591520056
  | 17 => 0x5800001600101400202700500300601300300200000000000000000100000000000000700600f00000100900000500300000400c00100000400800000001500e00000b00600700800a00200a00300700201300400000f00200500e00700701b00105002600000e00100c01100100100801202000301800000a00600500100402b00600b00f00400400300200500000101901d00800401600301400000102200000300900200400000002f00500000000700300600100001100200601000000000a01900100000900000000000d00a00300500606100000700f00100100700100c04d00000000002000600000300000100000d00500100700800700101403300001802001200200000000200202f00300200a00000000200200000100d00200900000500002400b00700100000800701700400a00205700a00700600400000200500000100200501700500100100800701304200000000200500000d00100700001b00001100000501900002b00c00000a00400000600600200300400000100000000400102a04f00100700100000003300200800201900400700000000600800300000a00401700000100d00501200e00000100600000000100200801000500900200401300000000000000d02501400003800002000500000e00001800000700100001b00100100003d00100e00200004900000601700700001700000400101600700104000500000000000403001800000104b00001201f03600b00004a00100c00a00100000009100b00400200000102000600600a01200c00800700000900000002800100200106502901100100200200700d00000402200800600600d00900800400200102500d00201200101600001100100800400a00002300000000500000000000200100000f00e00201301e00300700100101100000a00100601100800f00400500400300200000a00100004f00100100d00100200100b00100400000001c00000000900000200300100802000a00000000200400000b01600200004900001800602001402400100500c00000000500000000000300100100200200100d05900000a00100200300200a01003300a01f00500000101600200300000100100100c00000300000102101900200302000001400400700200000502400000000300200e00200500800000000000800100400000101a02b00000400000700c00100401600200100300700001401a00d00300200c00e01100b00000400d02000f00000201700001500103c00300500c00300200901500900200603e00200202004500703900300c00700200002400000c02800c00000300100101000200100900f0080000030060000010210060040290130080020120053d76d52540063d76d5254004de7398654004dd7398654004ee7218d54004ed7218d540063e659
  | 18 => 0xc47ea2033412380e40e9533a47cfea6ac32027484802134ca189559aa784c511fd1506ed42d1f5d5863b819ca4f910c532101930049eb355541ba435802f0b5147c60664b22d11d84024f91bc85d52ae0000002964fa60004f89e4c7d22af4810f056986213b390b448a00054e28a0e6a8164110000828a4a43f88b8fc64804f92b891a21b60002ca15fc40100028748ea0000002c7c0006c749103340487af01724193b006e1b888f522a1835061dac00065d000164c00000033b00016421581d2a49c00000040e0000eaa4df04426fc00000058e914cffe43b088847d1048562a30a6d20e36b3f5000068426355b100941266600000009ec0002660000000a7218c0000000a643ff000004e1cc54d28640009a700019913c857f115000102819821d08d066065520780007960003a32d0955a9911c7154d40c8353e716855f682500029d095e1713a627d8f5000002c255033c3250001ce41482b806399ad458aa25821db4f0e03448b2b68e9e2855a3800092279e0e02754b7600001b00004e00001ee0098a5aacf30488ac154b235581b0caf85e3099a22d5247070bd1afc0000a91778ea4f228f7245a9b82f62ee12b13380000de563a8acd287b40e0a5786f082f1c4a1643425fc0000000908045000000000000026b0e8cfd01130002a9083e00000000000d68fa1b802400000000fc80008d431400021d85a668d0000bc135074a223a0cc46a33c0000b00c202221e799b0ba66ef18415a950aaf63ef810cce0af12e111a055600301400300100300100000100100000000403a00200101900300501802102800000101b00000201100001102a00200200a00001f00100000000400000500e00402400500000300000000100000200900500600001f00700400100000102a00400600100400000700100500000000a00600000a00100100200000000300100101100000100000000500200100000100300600003300a00200001f00400100401500a00000400400000c00000800200200100000a00400200001700000000400e03201900002100700000a00e00100101500000b00d00400600602400200202107300000101900101101502200500200000101700100700200300002300201000002e00101100000400600c00500f00001701200200100100600701500000900000201200c01701200300000b00100000700200600005100100200b00200600300000200700100800201306700900b00202b02203403600200100100400000000000000800000100300400100300000101200400f02300300c00601e03c00000a01d01000200200500000600200000902200500400202500100e00300300000000000000000c00400001100004f00000e00000400600002500400100001600000000301600500500600000000500f03b00c00000000d
  | 19 => 0x2545949c3443de05004c5346a513eda04c0008bc000000109e8d630587f40008c72650aa00004c104600004a88681e9226c9b6a863a59fa4be2b181c826c8c5265f265aba42285d503206dc8b27dd5ab97e83ccb0732b0d24f88a272dc91907e03014ad0000d2a86e4ff01683b4905273a9011321aa1daa3fcc2a1380472530dec7bd00020ec904a942cf9b654d28e5000000057c6863b9842c6b48074c683805302a340496c4e8eb081b39ac800012937c00013da1ba2af0c8cef684836e8c3121e6392ce979c6260f9001a17c11492c221ab490a474321a822c03a15633ca3d157698c27a0c1c09e199040a0605181f557e04812641b942887106da7f800c11c8b7e84e3f39facbca5671050734a126fa2db8278f448c81e696109cc383193894468086d31f00ed1ce29121a08c026c2e628e0bf09c69fd5a3040ced40b236d01f54a05f34a018b05ae00000016641a276c2b8052cb682aa3c50ecd3842d1375904012a5bd00000015b6a1e24300014381372952d5800028f55a80014ac56e080acd00000000002ca4000000031806c09c3325399f251889354150000000398000197934c0da3ca8000de2a4532806ec5289513be1dfcf96039306105c01c20655c08a0a5c0003b29c3d1725374c90908462759000281416c00031a00001b28dc0001a1c6680621be0b4000087200d1fe82904e50000e841447bb225161873e00000025100000000100f1d254000000136000089c1ada80113035600004793f472d318ad5543000000000012b8426000000129a1081049e90d0a6d508a87402fa5734602cf10a04d416c28b93dc93a11d1a7881853c2dd01756607d836697f498479c072a734fa0696051ac3525e49f356991c0005113338000d7a00000020a400092d0c8aa38000b3719c0000fc800047e033010e00000f0f84f745cf269086800063b55b97b90e683045495155d6b194e190587948050fe28ecf4e0002a5a6b0000000000136949c55b3f0926c6f40005450ee92be0000001489196add37e800022092100000016800003a8238400065b2d2a21400000014e8000c5e5390001ba941648a3859fb95e0a013ec8760b8227f3a980000005252101a2d1480000000ec54364ee00003f910213b4ee800111e7780002d6929656336b261536619f5599c60f02a5727f9ff11e40bb1bf1e1426a37b2638ef8136a4d3288b152728b2278937810a5512c703b114214945b99d018c385055ad6c62a68c3cd14d4d381f61c01c710ae4952b31461672b591db887cfa422d4612658a426195080c255808240f9894c652a02562a6e55ee6cb0d19b6c0589e23bb8518cc27570829bdc5481412f316910700740a291dd35a3ce2fc9d38e124c43a4a66000035d1fe20e863c0000002b451d45e900011f809429c09080dd4964fc2e605841781df4b0a5a
  | 20 => 0xe910832231718085f672a2f0820c0202f5000097d4104e900015e83165171970bd92c87110911ea40000000ce1ae8fca2591208d303b6abe36114351ec72f0b11508d6aa6b45a84c005a5d7216035877a00027090fc27e9530e8942919a0b403da4f4e2600056c897554062b1341a855f497116f9da01c6b4931b19b8778782371066cd3490d00023bc000000204000028435f401831024a67e03d004c4e858c38c8a38f5640316588bcebe34839417908524a83f788595425231508a2883217c4a825ec0acaee22aa7b0da649642500009743c90001ccd2467170001860000aae4c98000f36a36449957c0000002ec1a3825400000006f055c0440090cac00037200026c55a8a21324a7f0b0aa5e3fc95840001d644fa850ede00000006240008941d7128069a21d51f27302f053f2efa02c04a41e4ac87ad29cb254c41ed419eb020b212704704ed3d72ab0e4a2f24de89ed0720c8052815ceea36041a19d44204ae2ffa1c400064f38a9e0c90268935403dd1c80864441728f8e8f14949cf4a361de0190f0077241a3762bfc97651301d00000e28641f19bec8de98421195c816687c3822b3022c56c073086c0002214141af952e83f1baa60036a43200000003c25520002714bf64b20b013d400027e00000003520e8119acecc1a8ab1c6a9c0256000408901960a119103a7d08160003b489713f20001c08000eb45810002d3500800008105654da4390b327700004d756b017800000000017dc000b41086a57472e000000259552200037a00f52c00000f280006d800014b0afc70497e03b0ad40001cb37c955432e74d2eea7a027815a00021949a0000251a2b00003c22000cd44ee6c435b0e1114a88d11f1640990a120002cbc7aaaed599276c6406d237809f013446d52aa6ed3ac5ae09f00000008be48c00009c06c900008c8c9417953d0a5c96c00030295382e6a3c23097d48a80002ec80002ba00034989795ae289109000123a9d75730000c4c7d61a99ce078c58700a1c58b588ae0e3800031886141704308ba5e03d90931352a3030320354ba0000f184e8a7078e0b789540ce62300020286a81550002998b8a00006da71ca926990000fb4000000000294c0009f743d801cb709ba2b7a6b95c681f49b800066e3680c11c6c000260000236800000001080000009d40d7a984b4672222b8c68348652020000000039e37400c400000041f1e2400084032193149ba99900010140005683a101dccfe3ee49a1448f541e41638000000000000247868a7f325e29f0d4a436188a1752209904de1ae4e06000000191546a272000216cc365a945d8e2860a0000000fcd0029e111b85d0d4096a5aa12a438a1123d8104c2fe1850b49c183280001021e1800022327d9d8052487d00026911a68f030900009567265110f806c43b247700012dca3
  | 21 => 0x1d355851c0000a70000b5800000053f29f483a09625f18d51bcb3827206100fc0000000000f868c539590f03a4669299800000001707d849c4a043e000110854a9254b1800145e2d9509800022e24b2c6a8cc0000004fc00000000002e59c00a161000000000de60004871fdc5902da000211d1ea3a6000a2404fa4312db1740e6e000202168954c7f125c1110bd85a84cda56000018f35b800006a8462daa8a83c400045f8c349d89ab324000126c0f0000134475a7944901980508316596002041839c0000bfcb863335790b19200000011a9ed260407416800151a8f93e600015203ec11b07fc61400032680000d400000013c16660f10a18e31124a4355d20c84f018718ba9051007b920c263c0000000002528d220000000000fb8a3f2ed9d0521699510b8bf8d5c6fc4c5a59c6545475071d48f9a073316993000072056f94c40001c830e225c16031f1c593345d644f57caa947ea4880df09c4c502263b81ca50d89835831ff4d468a72a50a6948e44e3660b2868e9da4b684a000000051c2cd803221105b891c7f0006258a5bc558508190a91145225a16d80013880001b780012261d908d22e01845f84890c0865e6d700000010d434156097707f200034c0e6d0fc1e83b2000038c0000000d8d2ea3f25340f584ec53e25e8210648a6008e909cfcc66525381444ce00029a1a4039e8fe1079d455f07305a40000f667c00382b18b3c1b40d28910000000484a78000000000000009246d11e60c648820f60348f984388a61c880003f05c6000000074e1d50001acc0000001b2800109a000239a51c70e2f829428e86863a828605d81ba58f13980010aa5da447211090aa2d238ac6c130b0946a1b204b60005a98000f1a4830dc00000d03693ef15741aeb4e2e21a3c24c1ec1f38000c0200000000005ee00a1ba1c681be00046725489124a24651df421e046259ac488fa6bb2a789346085c84c49c414ca7cf1712a1cf4c000057287c1c8a5b1c99084000b000000bb4000b580d81a6c69c71d0000be4000000000116c5a4a9d0d580011da2900000d70be44c900218210f04d31efa67c95a8b149c2a253d6b3136f0ba90b07210cd06982124c61e1a1c00d836e0ea0cd812672300020b0b9247c41b00000005593812bd08a02b30f397d039c61759eaa210846583f91cc48d28b035383b400012f42592dc0003772151c152b657621712641aa4094df00001a42b42d808ed37006000000000008e20002b244043ac295a77c0005710c71e2cd5e0ff00000006c296c037a728ef250358b0ae89b215c4c30924b14ae12b58000eb800041b80000f009d00000006c889d43785b400060a0002a052922e90000d2c0000ac4989bc85e28750002740000aea00029710a63d049e0b30cae0054700e508a41655591464a9026c00001fc00045c3971c
  | 22 => 0x680db814e1f2959093c67b3fdaa010045404e00d1034e2a646b8df5236279579a7185162ec053125d4840be29d94bcf3e02242f00004b01673ba218088c11b3c7a1a4fc47f645b17a813e22750b94f40008d00000000aac91a0711a0ca2cae72c013f401a9aa000278c0006464888d5456e2bc0000ff4b2430b00000003dc3d143d19dc0008b30000510e587c53b703503d404d2c48e1889a00027980000000005588b900222ad25529dd09800025c88554be0d84e8a6751229f01c79530f3020050b11ac000b22206a898cdea950059c50000969298181072a3d94081ee006003e32c852800031b47d989c000b141439f54f6cae056200e000000000011240009e72a211807d40001c904b8d140af0000d48ac467800001241e84741ff84109fcacb53f9efc5c61bf2ae25049ee9b40049f688363fb00000580aa26e2800e90314aab0d6a7643ba7be457ac688c413222b26795c8b2b4e70b94e3ea1146a9658a0e97d4998c484a411835105b058886202c9b9c8707760f498c11463060bb965d6060995852960ba8b0f59012fc21426144b1a000f25244972520150ab9464813085e6030bf20182d609c5881f50cb883c15807bc1a66110c6a88c81400c1100ac80009281bfa03054e6fe15b00000008d800015d0c3eaef0568a7c9207bc1d0231953681922c0f74d9452052d0cf8e025b3228a514000428000185032601c4b9243075e8793c02170cc40000000aec00000001e13e0a3c000000000000014d0259a911d2000000000077e000000000000009227d00006765411b30000dc87c217a0d7967ead50002af418a2993a02a60d6097f3039d6108a62056723742a4a6c18791c0d029a23c80234d544872ab9d88af24e83842000c70b43277877160200000024fd20215f00011980001233b19908d1000002a00003f45ce17400007a892b1988fd00000000ad800011e1b2000000038670d37a800104e2752d7aa4c00083d00003ccf325d1460a98c75418834912843503c819308a45c2478247908882a616283273d08622c09ca930da0b2659d171d186b51336ad3c65a7452582a3c12816e2d00ed9284000036a5cc4c473b1ce82e48f265a1f5a9c4ddc8155a22ad067e59a31d041812e2c33cba05c4f43ef0328f88b280002091090bdaaf500019a80005984072924c44195135a9492868a02e01f44f4a15346625a0000a9650503bc362b4b59218cc1a000056c24ec81c000574203c0ea00024991e8c541f102e187400019d26aa0ac00039a0001d787fc54d4042410e485fe06512611b6aca30d0000000050000000964e26933180001d694628a2150000b1c1678c3800098139b15f47a608256e25e400057b0600aa4afc2645128f5c35c1fe1801e3017e00039e000113400000000ac0000003f680010d61241378a04000aa94fda19cad23
  | 23 => 0x1951532a620000a081fa0003ab000087a6e02560b7540600014404700005eb21988e40000000001d980004370000b70000328362800000000000022b418613d446129801e8fd4bd03d40c28ec000075c8bc0004ce0000b4e0002d3000000000023d80001c22de54f0b506a2ade2948ed078824e00000013bc000000265c0008833ae9c2800064100016c8d9c48c32715681708b40fb889407e5bc00aa63800026500000000000004e413acf2c2fa0000d1800097005e8e640000001250ae43e097800029500000f8058a33c8dc61e12427a917a8a233e853d48c7a004014041f860f512184cf425e84aaa9d86e61405551cd0ea82463890f60b382cd2362c78a6ca344ff99e82587323d68bcca8658b3c927990e84ea3a228113de64448a1b049289244daa93c88015e41301091f09b00872a104d407c2eb1cf8a2a0293b8890cb2a5603709070dca97655388644303e4524253c12234f4189ac52e812d4741c791124b50e9933cdbe92653ca81c2a870e2e697bc6b26b405aabf4be0041215a3cc8ca2e058aa3aca0a7f00b1aa306742c116aa3650ee89e5970530fc003310700007f42c25378728a1ea154bb8cb07446d40239fb0c6e26651c90c0ec231c471944036615020895600008aa2c112953d28494d2800052a7f438614b0300ad0261860541e9c91eda9d43da99a0770000000aec00000004100001ed2d40000000000240d12a49d000000130469f000000000000000000004280c135314090420000001540aeaa370000000b2274806718f0a1cb2a000000136e7c60000fa019659b2df1af09b826d00025f05fa0f222f9c9cba4b2d572a74d5049f3000146950623c24d07ed4d4b5248c8fd8ee46840001a092cc00014987d11a439637f8a189e418617386f439217200000a13ca0000cb000162e81b00003e90824b40002b08b100003002abd6266325641df8eb688714687805066b83071eb0b06aa325200012140003731a5d0cc78402f807c00019015e839d30e000000268417400000015dc41a9080292c30bbc3b02240da8710000329ac44cf88ba2b2ac392c400018805c139605306e138800069d1670b24c7e0001e28324000000000000053c0000002afc000b3e51e84d04168e61f880010c63bb3548d5d11400000005a000091c410000000046700007c800082300026d80540000001edcd9e2573120eac5629560ab9b001420004090fdc0009f50000d6169419215015b53821512318000a7422446fa0680000002930224e7e34a3e0800153e9af40e8000aa82a214019c4ef400000000000000000002af0bc47885a29234d8c05b22297d800000007510954629170001ec5616350102800000000040f16b40cc7ca28e98f420ea0d2d52868a0844b2d59e8cce61a03719b6089833d0e11e746ec7c810f2b4caf00483392
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc65821c565480038e30038aca900021b60a75d912000436c14ebb1a4000a6481596424800189acab9c84900029920565509200053240acb1924000c2d655d232480014c902b2a6490003195cb611452000639b0ae028a400086f8759721480034c902b2e42900061b21d654852000d3240aca90a4000a6481596204800149b07b22a41000299607645482000516c34c8a904000c2f76591520800145b09b1aa41000299607635482000526c34c6a904000e0d6498d520800189eecb1aa41000383991635482000706b22c6a904000c2d641c5520800189ac638aa4100025a600715482000616b26e0a904000c4d63dc15208001c4ac8a94c2100039158d52984200053240aa4b084000a67865496108001c4cc8a92c2100038959152584200072331aa4b084000e456354961080014c90ea92c21000299e01525842000c36c12ec2884000c2e645c8510800185ac8b90a2100031398d721442000626b1ae42884001c66615c851080018cae4b08a2100030e99170144200061cb22e02884000c5a635c051080018b2c6b80a2100071c985701442000638b0ae0288400086d86dd6210800185eeab24421000313dd5638842000633baac31084000c2d75590210800189aeab184210003195d5610842000654b22e01084000cc9635c0210800185cc8b96a0100030b59172d40200062731ae5a804000c4d635cb50080018cae530ea010003195c961d402000616baac99004000c4d7558f20080018caeab0e401000398549618802000437c32ea9004000964815d5200800185aeab224010003135d5634802000632baac2900400086d821d564c40010db043aac7880061b21d6254b1000d32432a490e2000c69729c265840010db053aec9080021b60a75d8e1000516c20c4a942000a4d8318952840018cec438aa5080025c6007154a10004b4c16eca842000b608154a20840032e102baa41080029a60075d891000616baae83122000c4d755cc624400191ae8b98c488003195d5711891000654ba2e03122000cc9735c062440019c2e2b80c4880061e21970d491000516c20c4a922000a4d8318952440010df0fb10a2880021b61c621451000532432a490a2000c647654921440010d90cb96a0880021be1f62d411000436c38c5a822000965821c550440018c8c438aa0880061ea1f7654110006343b6c4a822000c687618950440016630838aa088002d460c7154110005b0c10e2a822000b518390550440016630918aa08800358dca215411000534432a51022001878865d52044001ac2ea90a40880021b60b705941000d3240aeab102001874815d95204003868e2b22a408007151c5635481000e3238ac4a90200086d829d6600400185cc8b96a0080030b59172d40100062731ae5a802000c4d635cb50040010db0f316a0080021b61d62d4010
  | 1 => 0x2c4b80c3a80021b60a76d075000436c34e5a0ea00086f8758b41d40010db0eb1683a8003139cd629075000626b9ac520ea00086d821d941d40010db053b663a80021b61a72cc75000437c3ac598ea00086d8758b31d400185ce8b1463a80030b5d1628c75000436c10ec98ea001a648158921d400185ce8b1043a80030b5d162087500062739ac410ea000c4d7358821d40018d2c538043a80031a58970087500068ca1ae021aa000a648158862540038ce20b90c2a80071a841721855000e34882e430aa00086d821d941540010db043b262a80029960861c855000635b12e010aa001c70615c021540038ccc2b90a2280029360e6254b4000436c10eab0e8001874815d952900010df04bb4a320003155d57118d4000662b92e231a8000cc9725c063500019a2e2b80c6a00038318d525094000436c14ebb0a800085d8718c515000189ec6b90a2a00031318d72145400062db1ae028a8000c58635c05150001918c6b9682a000313d8d72d41400062631ae5a828000aa98010d62100010db043aac22000299608755844000558c0086b08800086f865c8511000189cc6b90a2200031358d721444000e3330ae4288800086d8798851100010db0eb10a220003195c961144400062d31ae02888000c59635c051100018d4c4b80a2200031a589701444000e3930ae02888000c71615c0511000189cc6b96a0200031358d72d404000436c3cc5a80800086d8758b50100018cae530ea020003195c961d40400064639ac4a008000c9473585401000145b09312a5980021b608755873000436c14ebb246000c9b645c0438c0030e902bb2a5180021be097694630004cd43e86a046000c35755c4644c00194ae4b88c898003265cd701913000654b92e03226000cb1715c0644c001c18c8a9264980021b60a75d85300041ec38c828a6000c2f645c8514c001858c8b90a2980030ed9170145300061c322e028a6000c8c645cb314c00185ec8b96a0980030b19172d41300054d434872026000c987650d404c001932c8b808618002b2600435883000436c10eab086000a65821d5610c0015a30021ac2180021be19721443000617322e42886000c2d645c8510c0038ccc2b90a2180021b61e621443000436c3ac42886000c6572584510c001874c8b80a2180030e591701443000635312e02886000c69625c0510c0038e4c2b80a2180031c585701443000617322e5a806000c2d645cb500c0010db0f316a0180021b61d62d403000632b94c3a806000c6572587500c0011390eb226018003231d1624c0300064a3a2c29806000c4d655ce42c800185acaba4659000699205654872000527c1ac8a944000a2f8458d52880010db0c38aa5100025a6007154a2000633b90e2b2a4001c36841c5654800386b0838aca9000715a0c715952000e2ac18e2b2a4001
  | 2 => 0x4725805100d3940e84b00a200a7181d0960144014b507212c0288029660e425805100d3940e64b00a200a7181cc9601440147509192c0288028e612325805100436c16e0b2e8200c99635c043d040189aeab9cc5a0802aa6004358b4100526c1cc4a968200a2f8654942d04010db0f310a3a08031a989701474100634b12e028e820086d829d660d04038a8e2b1aa520807191c56254a4100436c14eb304820086f825c3655040185ae8b90caa08025c60071549410059240aa4a12820086d829da51504010db053acc0208021b60b70597310064cb22e021e6200c2d755d262cc4015930021ac5988028b6126254b3100527c32a4996620086d8798851cc4018d4c4b80a3988031a589701473100436c14eb3066201c3471591528c4038c8e2b12a5188021b60a759823100437c12e1b2a6200c4d735c8654c4010db043aac898803265917010d31004b8c00e2a926200b4481549324c4010db053b4a298802c56144350531005c2c1086a0a6200b918010d414c4010db053acc0188029360f6454b2100516c26c6a964200c4f655ce428840185ecaba465108025c6007154921004f0c00e2a924200a4d83d9152484010d90eb22a4908028b61363549210043643ac6a924200b61801c552484012cd0c38aa49080719a18715492100e93420e2a924201d25841c552484018cec838aa49080319590715492100ea3418e2a924201d45831c552484018cec638aa4908031958c715492100eb1400e2a924200965801c55248403ac30038aa49080258600715492100437436e0a924201d60215c0514840185ae8a90c090803135cd52181210053240aa43024200c4d655ce420840185acaba4641080699205654842100532c36a49084201a70815d5600840159307212c010802aa612325802100f3028a42b004200e635248560084010db0d390a9a80021b61a7214f5000436c34e428ea00086d8798851d400185ce8b10a3a80030b5d162147500062739ac428ea000c4d7358851d40010db053b087a80021b61a7210f500068ca1ae021ea000a4e83d9162d400149b07b22c5a80028ba136358b5000516c26c6b16a000a4e83dd162d400149b07ba2c5a800299a067458b5000532c0ce8b16a000a2e84dcd62d400145b09b9ac5a800299a067358b5000532c0ce6b16a00086e8710d62d40010db0e21ac5a80038350c4358b500053340886b16a000a658110d62d40014d50021ac5a80029a6004358b5000517420e2b16a000a2d841c562d400149d0638ac5a80029360c7158b5000632b88e2b16a000a69801c562d40014cf02b82c5a8002992057058b500062739ac5216a000c4d7358a42d400185ce8b1465a80030b5d1628cb5000436c3cc430ea000c2e7458861d400185ae8b10c3a8003139cd621875000626b9ac430ea000c6a625c061d40018d
  | 3 => 0x2a18860098d821c14310c0132b0238286218021b60875584430043cc00eab088600e156550d6110c01d0a86b12c22180299608755844300538c00eab08860086d829d66010c014d3053acc021802a620143580430070d32a86b008600e196550d6010c01d1287312c021803a250d625804300748a1cc2b008600e91435856010c014d3053aac021802a621d43580430070d3aa86b008600e197550d6010c0153704a1ac021802a6e0543580430068ca1ae021ea400d19435c043548018d704b80c2a90031a209701855200e3920ae030aa401c72315c061548038d642b80c2a90071c885701855200e3490ae030aa400c99635c043d080189ac638aa5210025a6007154a4200626b1ee0a948400a6481549619080125d0e21aa4a1002c9604435494200594c0086a928400969801c55250801a1ce6a9484a1003135cd521814200632a92e23028400c2f765494210801932c8b8087990030b5907154a32004b4c00e2a946400c2d64dc1528c8014c902a92c319003265917010d320052743686a92640094e8710d524c801c1ac821aa499002d16044354932005a4c0086a926400969801c5524c80170b0221a8499002e26004350932006873a2a51926400c2d74548604c8018caa4b88c0990028b612625483200627bb2a49906401c64715895294401a3286b8087288021b61a721505100f0b28ac8b18a20086d869c85314403c64a2b22c02880794945635805100f3128ac4b00a200a6a829d560144014d3053aac0288029aa08545805100534c10a8b00a201a728115160144014d50429ac0288029a608535805100d39408a6b00a201a7281149601440183aeca1886288021b61a7210c510043cc34e0218a200d19435c0431440149d07ba2c4288029360f745885100d3340ce8b10a200a2e84dcd621440145b09b9ac42880699a0673588510043743886b10a20086d8710d6214401c1a8621ac42880699a04435885100532c0886b10a200a6a8010d62144014d30021ac42880699205705885100517420e0b10a200a2d841c1621440149d06382c4288029360c705885100d33408e0b10a201c667158b42144018cac4b8e8428803139cd629085100626b9ac5210a201c667158b32144018cac4b8e64288030b9d1628c85100616ba2c5190a200a5b835d160144014b106ba2c02880296a0c74580510052cc18e8b00a200a6a821d160144014d3043a2c0288069ca0474580510051dc22e6b00a200a38845cd60144014750839ac0288028e610735805100535410e6b00a200a69821cd60144034e50239ac0288021ea1c43580510043cc3886b00a200e194310d60144014d50421ac0288029a608435805100d3940886b00a200a718110d60144034e102b92c0288028ea1072580510051cc20e4b00a200a5a831c960144014b306392c0288069ca0
  | 4 => 0xcf8191000000081ff0004700000005e1a8808582882b4000332e25946c9e4000000bb10f0c60001b00012858cde9192228482e07b03a714b597b3fc4981d8000c83bc9000016600067052000174dd045000118cd88a1d8760d894f39c000001e235a10c0018136c3e40013f000000001d600055c54071332230000190462dd0c80004e4dc440001486ac5902400014cc30ba412000002022c4568d39a245a000270000007040000000000000038000000ce82106e5440b8003844307188b0681f4669b2328024880002c25f4749820006cc0021400a045110003e2360ab000000000b61f91ae57c001243f8000000bf0000790f800360284129452ce17cfd80000000000173146378449e91c4500e1917156418fb0f702c1a0000000000004306b0000000000017c194000000361b4000000bc82c000df000070000000008a8a804742a13ce80a72440b90d9aa0006e40004835c8bd1194714404800000000000001ee2746007502c000000000000000000003f18e83c000000007a8001be000000dc0002946dc000852126545c8a00004e4c980440a0b4611bc0268b8c90000440000016e0ec310130003062a85aa240003581022b1e46bcb01000b27303c1e001e5c00004141a7bc001d33500ac038bd2f2274000001f8000051d400065cbe0eb1c8670890001044b4001f83c6414001a3380330f41640000000008e27c0000607a0003749b0ed176000e380007813040a081261f09a0a92e46981f17543c27c3796f0001a467800000000d2000000000e21d715e0a4f59983ee778371df06000000149016124000281fa71849000122324bb8000003940020a318000918c52820340023040c774000001e0000970ee39a000e48613b81507f1a524a8702a800000628000001380011096a000000300001687f4ae0000001fc8a9ec394804f99d1278264a412731073caa11d196768cb0a60000000017e000000a5a1113c000a100043484c00000094110650000004ad148f3000038399a91b81d0ac9181cc00000000000000000040006000000010040000400018060000102003008000400201c0100c0300002008000000300c020100000c01020030040a0040100c1e02c1401400004000040900005004030380d000050000207403004060140001001000000000a008020000200c02000020040e0000000000000010100100000000000040e0040200c01000000000300c0204404058010082600c0100800000020000000800004000000500001000040280301c0102400008040200001c020000200c030000002c0001803018000041c00402000180040001400020080040b004010000f0240402400008080000000407008010db043aac3a18021b60a759834300436c10eab0c860086d829d66090c010db05b82ca2180307dd96550c43004c6c16e
  | 5 => 0x898698003ce5a4561d5216240000ff36a0000002a3580000000123e4c8001bf000000fa8003e4000380d10fc0003306c0001e4390000002588a131406020280001800004d92f3080540003d000000000000000009811600072c188000003d800225000000000000000000000000c3e89c0002aa538000002fe000001bb0002600000030a4f40d1f4028668a98561620000012c44e5e84a857000838001ed250000c48f543a000000000000e8820000c40002d0da39030cf280000016c000974585783388031e7846095228c64090929316108e914d2660009a8d542c3ec4d1db064000cf000236638d08024503d00000040e0010ba101702b8000001f01dc8104b00000c9da043400008981f1a02d826974108880f319f31a800000d4000000478c62cc3a08396811a39cb690d23c36ca60181780e4ad903000349060750003210c0872100d4288e000000000000462764c39fa00000000000000000001431604382011a1c25e0528f10004a8000002146d0000002b0000ae80000020
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x4264b81182889c0048a003a000060080d801e200000000007442c0000000f2300012981208b103e3402600009830a5402434002001c0400400400400000000401289922014358043004a46448050d6010c012899221d4358043004a46448750d6010c01609929d54358043004a264b8150d6010c014299420970185520051264c825c06154801849636007154a4200498640815496190801829646007154a320049864081549618c801a096460043549320068250d8010d62144018198750c4358051004c864081549425040134190205524c9310051164f641c5524840142594d8c715492100618259801c5524840186364600715492100618591801c552484018636360071549210061858d801c55248401825742055218121006115cc815486048401a09436004358b50006185c5801c562d400144491595739092000509245655d232480018296460071548200061258d801c552080012619021d525842000509245755912008001444915d5634802000618d89801c5528400116197205528821000419660621c55044003460965d52148110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xa6000005043484b30038aa490802841a3259801c55248401420d1ec8c00e2a924200a08693636007154921
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 66
  | 6 => 1665
  | 5 => 2908
  | 4 => 562
  | 3 => 39
  | 2 => 4
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | 3 => packedAt gbK3 (i*70) 61
  | 2 => packedAt gbK2 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | 3 => gbHint (packedAt gbK3 (i*70+61) 9)
  | 2 => gbHint (packedAt gbK2 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (1870+((h/22+packedAt gbK7 (1716+(h % 22)*7) 7) % 80)*8) 8
  | 6 => packedAt gbK6 (67710+((h/555+packedAt gbK6 (61605+(h % 555)*11) 11) % 1999)*12) 12
  | 5 => packedAt gbK5 (151212+((h/969+packedAt gbK5 (139584+(h % 969)*12) 12) % 3490)*13) 13
  | 4 => packedAt gbK4 (35028+((h/187+packedAt gbK4 (33158+(h % 187)*10) 10) % 816)*11) 11
  | 3 => packedAt gbK3 (2808+((h/13+packedAt gbK3 (2730+(h % 13)*6) 6) % 61)*7) 7
  | 2 => packedAt gbK2 (327+((h/1+packedAt gbK2 (324+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc1fe00306380c3fff0fffe07fc134dc00f3cf
  | 1 => 0xfe0fffc07c00fc383f0e0ff83c2cb27334d33
  | 2 => 0xfff003ff8000ffc03ff00fffc330c38c38e3c
  | 3 => 0xf000003ffffff00003ffff00003c0fc0fc0fc0
  | 4 => 0x3ffffffffffc000000003ff000fff000
  | 5 => 0xffffffc00000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1401220000080004a00128202200104c001045
  | 1 => 0x2041940640a4410910424501804101314512
  | 2 => 0x8b5a042bc8014aa812aa049a58330c30c28a28
  | 3 => 0xa108088d5292600003cc960308940f80540f80
  | 4 => 0x2101132a5258f325800000c112be000abe000
  | 5 => 0xcf9c9e00c006022060881810623fbefe000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xffeeeeecffeaeae8ffeeeeecffeaeae8ffeeeeecffeaeae8ffeeeeecffeaeae8ffeeeeecffeaeae8ffeeeeecffeaeae8ffeeeeecffeaeae8ffeeeeecffeaeae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14598
namespace PEqualNP.Outside.L_meta_14598
open PEqualNP.Outside.L_meta_14598.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
theorem alls3 : ∀ k ≤ 3, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
theorem alls4 : ∀ k ≤ 3, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1 := bs5_3_0
theorem alls5 : ∀ k ≤ 3, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 4 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 39 := (concat bgb_3_0 bgb_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_128 : Interval gbAtlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_160 : Interval gbAtlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 562 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)) (concat (concat bgb_4_416 bgb_4_448) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_32 : Interval gbAtlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_64 : Interval gbAtlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_128 : Interval gbAtlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_160 : Interval gbAtlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_224 : Interval gbAtlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_256 : Interval gbAtlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_320 : Interval gbAtlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_352 : Interval gbAtlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_416 : Interval gbAtlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_448 : Interval gbAtlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_512 : Interval gbAtlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_544 : Interval gbAtlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_608 : Interval gbAtlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_640 : Interval gbAtlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_704 : Interval gbAtlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_736 : Interval gbAtlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_800 : Interval gbAtlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_832 : Interval gbAtlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_896 : Interval gbAtlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_928 : Interval gbAtlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_992 : Interval gbAtlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1024 : Interval gbAtlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1088 : Interval gbAtlas 5 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1120 : Interval gbAtlas 5 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1184 : Interval gbAtlas 5 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1216 : Interval gbAtlas 5 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1280 : Interval gbAtlas 5 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1312 : Interval gbAtlas 5 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1376 : Interval gbAtlas 5 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1408 : Interval gbAtlas 5 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1472 : Interval gbAtlas 5 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1504 : Interval gbAtlas 5 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1568 : Interval gbAtlas 5 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1600 : Interval gbAtlas 5 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1664 : Interval gbAtlas 5 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1696 : Interval gbAtlas 5 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1760 : Interval gbAtlas 5 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1792 : Interval gbAtlas 5 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1856 : Interval gbAtlas 5 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1888 : Interval gbAtlas 5 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1952 : Interval gbAtlas 5 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1984 : Interval gbAtlas 5 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2048 : Interval gbAtlas 5 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2080 : Interval gbAtlas 5 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2144 : Interval gbAtlas 5 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2176 : Interval gbAtlas 5 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2240 : Interval gbAtlas 5 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2272 : Interval gbAtlas 5 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2336 : Interval gbAtlas 5 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2368 : Interval gbAtlas 5 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2432 : Interval gbAtlas 5 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2464 : Interval gbAtlas 5 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2528 : Interval gbAtlas 5 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2560 : Interval gbAtlas 5 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2908 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 (concat bgb_5_448 bgb_5_480))) (concat (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)) (concat bgb_5_608 (concat bgb_5_640 bgb_5_672))))) (concat (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832))) (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))) (concat (concat (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)) (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216))) (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))))) (concat (concat (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568))) (concat (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664)) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)))) (concat (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952))) (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))))) (concat (concat (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))) (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496)))) (concat (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688))) (concat (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784)) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_32 : Interval gbAtlas 6 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_64 : Interval gbAtlas 6 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_128 : Interval gbAtlas 6 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_160 : Interval gbAtlas 6 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_224 : Interval gbAtlas 6 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_256 : Interval gbAtlas 6 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_320 : Interval gbAtlas 6 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_352 : Interval gbAtlas 6 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_416 : Interval gbAtlas 6 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_448 : Interval gbAtlas 6 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_512 : Interval gbAtlas 6 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_544 : Interval gbAtlas 6 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_608 : Interval gbAtlas 6 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_640 : Interval gbAtlas 6 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_704 : Interval gbAtlas 6 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_736 : Interval gbAtlas 6 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_800 : Interval gbAtlas 6 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_832 : Interval gbAtlas 6 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_896 : Interval gbAtlas 6 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_928 : Interval gbAtlas 6 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_992 : Interval gbAtlas 6 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1024 : Interval gbAtlas 6 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1088 : Interval gbAtlas 6 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1120 : Interval gbAtlas 6 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1184 : Interval gbAtlas 6 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1216 : Interval gbAtlas 6 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1280 : Interval gbAtlas 6 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1312 : Interval gbAtlas 6 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1376 : Interval gbAtlas 6 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1408 : Interval gbAtlas 6 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1472 : Interval gbAtlas 6 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1504 : Interval gbAtlas 6 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1568 : Interval gbAtlas 6 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1600 : Interval gbAtlas 6 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1664 : Interval gbAtlas 6 1664 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1665 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 66 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_2 i (by omega) hi
  · exact allgb_3 i (by omega) hi
  · exact allgb_4 i (by omega) hi
  · exact allgb_5 i (by omega) hi
  · exact allgb_6 i (by omega) hi
  · exact allgb_7 i (by omega) hi
  · exact allgb_8 i (by omega) hi
def Complete (g : Atlas) := ∀ k ≤ top g, ∀ i < count g k, checkRow g k i = true
theorem frozen {g : Atlas} {p n} (ready : Ready g p n) (complete : Complete g)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 4 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 6 zero,inputs.getD 4 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 7 zero,inputs.getD 3 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffeeffeeffeeffeeffeeeeeeffeaeaeaffeeffeeffeeffeeffeeeeecffeaeae8ffeeffeeffeeffeeffeeeeeeffeaeaeaffeeffeeffeeffeeffeeeeecffeaeae8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) SB :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) SB :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) SB :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) SB :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_14598.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.or,[8,5]⟩,⟨.or,[9,6]⟩,⟨.and,[10,7]⟩,⟨.or,[0,2]⟩,⟨.or,[12,3]⟩,⟨.and,[13,6]⟩,⟨.or,[0,1]⟩,⟨.or,[5,7]⟩,⟨.and,[15,16]⟩,⟨.or,[11,14]⟩,⟨.or,[18,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))),len⟩
  · push Not at clean
    obtain ⟨a,ha,hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot,hop] at e
    exact ⟨mono,19,monoShape,by change 12 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_14598

open PEqualNP.Outside.L_meta_14598 in
theorem PEqualNP.Outside.L_meta_14598 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
