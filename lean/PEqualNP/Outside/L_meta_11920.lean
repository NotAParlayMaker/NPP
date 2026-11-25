import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_11920.Model
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
  (n*(n+971)) % 2305843009213693951
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


end PEqualNP.Outside.L_meta_11920.Model

namespace PEqualNP.Outside.L_meta_11920
open PEqualNP.Outside.L_meta_11920.Model
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

def SB : Nat := 5

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

end PEqualNP.Outside.L_meta_11920

namespace PEqualNP.Outside.L_meta_11920
open PEqualNP.Outside.L_meta_11920.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xd531
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | 3 => packedAt s0K3 (i*16) 16
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s0K3 (17+((h/1+packedAt s0K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xc3e0e1e1ffffff8e1870e1c1c3ffffff1193ff
  | 2 => 0x3ff01ffe1f0fff01f80fe01ffc3c1ffa21e4f
  | 3 => 0x3fffe01fe00f0ffe000fffe03fc01e0c3e38c
  | 4 => 0xfc000001ffff00ffffff000003fffe00fc03f0
  | 5 => 0xfffffffe000000fffffffffffc000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x843202423120800a1018a06460446432119095
  | 2 => 0x294455904c4524b08a824a0899a2894ca2064a
  | 3 => 0xb18ad0d484e645d6a2046c9c0aea1586c2a38c
  | 4 => 0x210c9919088466e4cb26081013331908e40360
  | 5 => 0x2100000110888091448912120002010195800
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfffffff0ccccc0c0fffffff0ccccc0c0fffffff0ccccc0c0fffffff0ccccc0c0fffffff0ccccc0c0fffffff0ccccc0c0fffffff0ccccc0c0fffffff0ccccc0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_11920
namespace PEqualNP.Outside.L_meta_11920
open PEqualNP.Outside.L_meta_11920.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe521
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | 3 => packedAt s1K3 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s1K3 (17+((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xc3e1e1e1ffffff8e1c3830e1c3ffffff1893ff
  | 2 => 0x3fe01ffe1ff0ff01fc03f01ffc3fc1fa11e73
  | 3 => 0x3fffe01fe1ff0ffe0003ffe03fc3fe0c1e39c
  | 4 => 0xfc000001ffe000ffffffc00003ffc000fe03e0
  | 5 => 0xfffffffe000000fffffffffffc000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x43082823112000a140ca030608446941890a5
  | 2 => 0xa94455504c4454b0894115049962a84aa10652
  | 3 => 0x3189505484c845d4a102164c0a6a3142c12318
  | 4 => 0xa10d9999088e66e6cd93840813b3218cea03e0
  | 5 => 0x210000011108809122428912000021014d800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfffffff0aaa0aaa0fffffff0aaa0aaa0fffffff0aaa0aaa0fffffff0aaa0aaa0fffffff0aaa0aaa0fffffff0aaa0aaa0fffffff0aaa0aaa0fffffff0aaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_11920
namespace PEqualNP.Outside.L_meta_11920
open PEqualNP.Outside.L_meta_11920.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe3c7c7f1fe3ff8e38e0e383f1f83ffe61339f
  | 1 => 0xf03f807fe3ffe3f03f00fc03fe3ff83e863cf3
  | 3 => 0x3fff8ffc03fc7fc000fffc7fc03fc107cf1c
  | 4 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x404610c15105400a182a40a0a0490d18611185
  | 1 => 0x288849228a4204502110a449121490a4862432
  | 3 => 0xa511282408c880b4400429185482a285024e18
  | 4 => 0xc40132484080c9268a46001069230309280bc0
  | 5 => 0x8224000931312493498d26200040430d5b000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88ffffff88eeccaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_11920
namespace PEqualNP.Outside.L_meta_11920
open PEqualNP.Outside.L_meta_11920.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3c38f1e3f1f8f8fce38e0c70f8fc38ff31370f
  | 1 => 0x3fc0fe03fe7fff1f03f00f80ff1fff0f4239f3
  | 2 => 0xc000fffcff80ffe3fc000fff1fe03ff083ce3c
  | 4 => 0xffff0000ffff0003fffff0001fffc000fc0fc0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8681184615215100a182a414282488a6311305
  | 1 => 0x82221082840802202110888410a1408422052
  | 2 => 0x1144480401220054400412212412240804c28
  | 4 => 0x919004d28410324968a460021c918262940f80
  | 5 => 0x222089000964c49293498e4c8002048c6bb000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xfffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_11920
namespace PEqualNP.Outside.L_meta_11920
open PEqualNP.Outside.L_meta_11920.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3c78f0e3f3fff8fc638e0c70f8fff87f1133cf
  | 1 => 0x3f80ff03fc78ff1f83f00f80ff1c3f8f623d33
  | 2 => 0xc000fffcff80ffe3fc000fff1fe03ff083ce3c
  | 3 => 0xffff0000ffff0003fffff0001fffc000fc0fc0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x6011804122041004102841420260844111045
  | 1 => 0x8852228a29419022829128884908950a622512
  | 2 => 0x1244440401220052400412212412220804a28
  | 3 => 0x9130065281103249a8a460021c918322a40f80
  | 5 => 0x224088800a64c49253498e4c8002044c5bb000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xfff8fff8eae8eae8fff8fff8eae8eae8fff8fff8eae8eae8fff8fff8eae8eae8fff8fff8eae8eae8fff8fff8eae8eae8fff8fff8eae8eae8fff8fff8eae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_11920
namespace PEqualNP.Outside.L_meta_11920
open PEqualNP.Outside.L_meta_11920.Model
def s5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (6+((h/1+packedAt s5K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf83f87c7fffe1fe1fc3f0fe0c3fff87f4dc3cf
  | 1 => 0xffc7fff83c3fe1fe1fc3f0fffc383f87b27d33
  | 2 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 3 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 4 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa0008411010200048050124004a082404c045
  | 1 => 0x10810080804402020440104244109102101512
  | 2 => 0xa11255120aa9106ca222aa08aa812650c30a28
  | 3 => 0x85b56624aa0d54b736a88812f3258312f80f80
  | 4 => 0xc626443733319939db33cc9c22060464efe000
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xeeeceae8eeeceae8eeeceae8eeeceae8eeeceae8eeeceae8eeeceae8eeeceae8eeeceae8eeeceae8eeeceae8eeeceae8eeeceae8eeeceae8eeeceae8eeeceae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_11920
namespace PEqualNP.Outside.L_meta_11920
open PEqualNP.Outside.L_meta_11920.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1825c2144681be024cc284e6420048343bb0a38a800095e0010d50000c00b1f000002300019291600a003c2883938f568004d18005c3d6267ebdb8074acb9d6c00012546c000620199102002c5010210280000cd041600000040c200007fd5001fe54007f55001fc54007fd4c01fe53007f54c01fc53007fd0c01fe43007f50c01fc43007fd4801fe52007f54801fc52007fd0801bf42007f90801fd42006f50801fc42007fcc801df32007f8c801fd3200774c801fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x244002bfd8e20025fcc710002fd63880057e31c4000bf58a200077e8510003ee4288001dea144000fb50a200075a8510003df3288001ee9944001bf98620005fac31000afe6088005fd2844000fe54220017de411000ffb20880017fb2a4006bf99520005faca9001afc65480017fb224005bf99120005fac890016fc64480017fb1a4004bf98d20005fac690012fc6348001dfa124000ef50920007be6490003ee3248001ee9924000fb4c9200079a6490002ff61480037e30a4000fbc8520007da4290003fa5048001fca824003fec8120017dc409000aff650800d7f3284002df99420004fcca10002fd6508005beb2840009f59420015f8ca1000aff640800b7f3204002ef990200057cc810002fd6408005deb204000af59020015f8c81000aff63080097f3184002f798c20005bcc610002fd6308005eeb184000b758c20015f8c61000efe6208007dfa104003fb9082001f7a8410003ed4208001d6a104003f7cc82001fba6410006fe6108005fb3084000bd98420005fac21000bf561080017ab084002bf98020017de401000bfa2008005f69004003fe4802000dfecb8801afe65c40017eb2e2001bf1971000dfec988016fe64c40017eb262001bf1931000dfec788012fe63c40017eb1e2001bf18f1000dfec58800efe62c40017eb162001bf18b100077e8588003bd42c4001ef9962000f74cb1000fec6388003f531c4003fb10e2000fd48710007f4a188003f950c40057fb2c2006bf99610005facb0800afc65840057fb242005bf99210005fac90800afc64840057fb1c2004bf98e10005fac70800afc63840057fb142003bf98a10005fac50800afc6284001dfa142000ef50a10007be6508003dd32840017eb0c2000fd94610007eaa30800afe6084005fd2042000fe50210017f44108003f92084005fb8842001fec4210005feca8801afe65440017eb2a2006bf19510005fec888016fe64440017eb222005bf19110005fec688012fe63440017eb1a2004bf18d10005fec48800efe62440017eb122003bf189100077e8488003bd4244001ef9922000f74c910007ec6288003f53144001fb10a2000fd48510007f48088003f94044001fd1022000fe4811000ff6208800bf610440057fb282006bf99410016fcca080027e65040017eb282002df59410004faca0800afc65040057fb202005bf990100177cc808002be64040017eb202002ef590100057ac80800afc64040057fb182004bf98c10017bcc608002de63040017eb182002f758c10005bac60800afc63040057fb102003bf98810017dcc408002ee62040017eb102002fb58810005dac40800afc6204001dfa102000ef50810007be6408003dd32040037f3082001fd94410007eaa20800afe6004005fd2802000fe54010017ee200800bfa1004005fa8802001fe44010
  | 1 => 0x3bd42d0001ef9968000f74cb4000dfcc3a0002fd61d000bdfa0e8000ef50740015fecb2001afe6590005bf32c80009f99640005facb2000b7d65900013eb2c8002bf19640005fac920012fe63900017eb1c8003bf98a40005fac520003bf4290001dea148000f7cca40007ba6520006fe61900017eb0c8002bf98240017f4a120003f95090005dfa048005fed0240005fecaa001afe65500017eb2a8006bf195400077ea8a0003bc54500017fb1a8004bf18d400077e86a0003bd43500017fb128003bf189400077e84a0003bd4250001ef9928000f74c940005fec2a0006fc6150001dfa0a8000ef50540007f4a0a0003f9505000bfda028002ef90140015feca2001afe65100017eb288002bf1944002dfcc820012fe63100017eb188003bf98840005fac420017bf4210001dea108000f7cc840007ba6420006fe61100017eb088002bf980400177e802000bfa4010005dea008005fe50040025fecb9801afe65cc0017eb2e6004bf19730025fec998016fe64cc0017eb266004bf1933001dfcc598002fd62cc001dfa166000ef50b30027be6598003dd32cc0037f30e6000bf58730027be6398003dd31cc0057fb2c6006bf99630005facb1800afc658c0057fb246005bf99230005fac91800afc648c0017eb1c6000f7d4e30007b8a718003de438c001eea1c6003bf98a30005fac518003bf428c001dea146000f7cca30007ba6518006fe618c0017eb0c6002bf98230017f4a118003f9508c005ef9846004fecc230005feca9801afe654c0017eb2a6006bf19530005fec898016fe644c0017eb226005bf19130005fec49800efc624c001dfa126000ef50930007be6498003dd324c0017fb0a6001bf18530007be6298003dd314c001fd2826000fe54130027f6609800bde304c0057fb286006bf99430016fcca180027e650c0017eb286002df59430004faca1800afc650c0057fb206005bf990300177cc818002be640c0017eb206002ef590300057ac81800afc640c0097f3186000f7d4c30027b8a618013de430c001eea186003bf98830017dcc418002ee620c0017eb106002fb58830005dac418003bf420c001dea106004f7cc830007ba6418006fe610c005fb3086000bd98430005fac21800bf5610c0017ab086002bf98030017be601800bfa300c005ee9806004fe4c03001dfecb9001afe65c80017eb2e4003bf1972001dfec990016fe64c8007df3264000af99320005fac99000fbd64c80015eb264003bf1932001dfec790012fe63c8007ef31e4000b798f20005fac79000fdd63c80016eb1e4003bf18f2001f7e859000fbd42c8007ef9964003fb8cb2001fba6590003ed32c8001e69964001bf98720005fac39000fef21c8001f690e4002bfd9620035fccb10002fd65880057e32c4002bfd922002dfcc910002fd64880057e3
  | 2 => 0x2101dfec790812fe63c8407ef31e4200b798f21005fac79080fdd63c84016eb1e4203bf18f2101f7e859080fee42c8407dea164200fb50b210075a859080fdf32c8407ee9964202bf98321005fac190806ff658840d7f32c4200bf5962100df8cb10806ff648840b7f3244200bf5922100df8c910806ff63884097f31c4200bf58e2100df8c710802fd6288401dfa144200ef50a21007be6510803ee3288401ee9944200fb4ca210079a6510806fe6188403fb28c4200fd5462100fde431080ff721884057f3044200bf58221005feca9081afe65484017eb2a4206bf19521005fec890816fe64484017eb224205bf19121005fec690812fe63484017eb1a4204bf18d210077e8490803ee4248401dea124200fb509210075a8490803df3248401ee9924200fd94521007eaa29080ff72148403f710a4200bfd8121015f8c090806ff650840d7f3284201df99421004fcca10802fd6508403beb2842009f5942100df8ca10806ff640840b7f3204201ef990210057cc810802fd6408403deb204200af5902100df8c810806ff63084097f3184201f798c21005bcc610802fd6308403eeb184200b758c2100df8c61080efe6208407dfa104203ef5082101fbe641080fee3208407ee9904200fb4c8210079a6410806fe6108403f79084201fd8842100fda421080ff521084057f3004201fe98021005f4c010802fd6008403fcb004200be5802102dfcc9a8002fd64d4001bf2a6a006df15350025fcc7a8002fd63d400dbfa9ea000df54f5001dfcc5a8002fd62d400dbfa96a000df54b500077e85a8003bd42d4001ef996a000f74cb5000dfcc3a801bf661d40017b30ea000bf58750037eac3a8002f561d400dbfa8ea000df54750005facb28016fe6494005df324a000af99250005fac92800bbd64940015eb24a004bf98e50005fac72800efe62940017eb14a000efd0a500077a8528003df3294001ee994a001bf98650005fac32800afe6094005bfa84a006fed4250005fec8a8016fc6454001bf2a2a000df15150005fec6a8003df63540016fb1aa004bf18d50007b8c6a8002dc6354001bfa9aa000df54d50005fec4a800efc6254001bfa92a000df549500077e84a8003bd4254001ef992a000f74c950005fec2a8006fc6154001bfa8aa000df54550037f6a0a800b7e505400d7f328a005bf99050005fac828012fe63140017eb18a003bf98850005fac428003bf4214001dea10a000f7cc850007ba6428006fe61140017eb08a002bf98050016fea02800bfa5014005bea80a006fe5405002dfecba001afe65d00017eb2e8005bf197400077ea9a0017bc54d00097f31e8005f798f40005bcc7a0002fd63d000beeb1e8000b758f4002f7e87a0003bd43d00077f3168005fb98b40005dcc5a0002fd62d000bf6b168000bb58b4002f7e85a000
  | 3 => 0xeb18a203bf98851005fac428803bf4214401dea10a200f7cc851007ba6428806fe6114403bfa88a201fd9445100efaa22881bf551144057f300a200bf5805102dfecba081afe65d04017eb2e8205bf19741025fcc7a0802fd63d04077f3168200bf58b4102f7e85a0803bd42d0401ef9968200f74cb41015fcc1a0802fd60d04037fb2c8206bf99641005facb20806fc65904017eb248200efd524100778a920812fe63904017eb1c8200efd0e410077a872080efe62904017eb148200efd0a410077a8520803df3290401ee9948201bf9864100feca320803f55190403dfa0c8205fdd0641015fcc120802fd60904017fb2a8206bf99541005facaa081afc65504017fb1a8204bf18d41005fec4a080efc6250401dfa128200ef50941007be64a0803dd3250401fb28a8200fd5454102fee82a0807be41504017fb028202bf1814100dfeca2081afe6510403bf32882009f99441005faca208077d65104013eb288201bf1944102dfcc820803bf541040bde2a08204bf98c4100fbcc620802de63104017eb188201f758c41005bac620817bf4310401dea188203bf9884100fdcc420802ee62104017eb108201fb58841005dac420817bf4210401dea108200f7cc841007ba6420806fe6110403dfa088201fd9044100f7a8220817f541104057f3008201fe98041005f4c020802fd6010403fcb008200be58041025fecb9881afe65cc4017eb2e6204bf19731025fec998816fe64cc409df3266200af99331005fac998813bd64cc4015eb266204bf19331007bea798813dc53cc409ef21e6200f750f3101dfcc598813ee62cc401773166200bf58b31027dac598802ed62cc401dfa166200ef50b31027be6598803dd32cc4057f3066200bf5833100dfecb1881afe658c403bf32c62009f99631005facb188077d658c4013eb2c6201bf1963100dfec918816fe648c4017eb246201bf19231005fac71880efe628c4017eb146200efd0a310077a8518803df328c401ee9946201bf9863100feca318803f5518c403ef98c6204fdcc631015fcc118802fd608c4017fb2a6206bf99531005faca9881afc654c4017fb226205bf99131005fac898816fc644c401efa9a6200f714d31007bc8698803dd434c4017fb126203bf189310077e8498803bd424c401ef9926200f74c931007eca298803f5514c409fb98a6201f78c531005fec09880afc604c4037fb286206bf99431005faca18806fc650c4037fb206205bf99031005fac818806fc640c4097f3186203bf98831005fac418803bf420c401dea106204f7cc831007ba6418806fe610c403ef9886201fd8c43100fba6218813f5310c4057f3006200bf5803101dfecb9081afe65c84017eb2e4203bf1972101dfec990816fe64c8407df3264200af99321005fac99080fbd64c84015eb264203bf193
  | 4 => 0xafe60cc8017eb066404f7d9732007bccb99003dd65cc809ee32e6404f7d9332007bcc999003dd64cc809ee3266400f7d5332007bca999003dd54cc801ee2a66400f7d4b3201fbca599003dd52cc807ee2966400f7d0b320073e859900fde42cc801eea166400e750b3201fb88599013df61cc801ef30e6400f758732027b8c399013df60cc801ef3066400f758332027b8c19900eff658c80d7f32c6400bf5963201df8cb1900eff648c80b7f3246403ef992320057cc919002fd648c807deb246400af5923201df8c919002fd638c8016eb1c6403bf98a3201fdca519003ed528c807dfa146403fb90a3201f7a8519003ed428c801d6a146403f7cca32027de6519006fe618c8017eb0c6402bf98232005fac119002ff654c80d7f32a6400bf59532035f8ca99002ff644c80b7f3226400bf5913202df8c899003df534c801ef29a6400f754d32007b8a699003df434c801ef21a6400f750d32007b88699003ee524c801f6a926400efd0932007dc8499003bd424c801f6a126400eb50932027de649900fde324c8017fb0a6401bf18532005fec09900afc604c801efb2a6400f799532007baca99003dc654c801efb226400f799132007bac899003dc644c801efaa26400f795132007baa899003dc544c801efb126400f3d8932007bea49900fde524c801e72926400f7549320079aa49900fdc524c801efa126400e7d093201fbc8499003ce424c801eea126400e7509320079a84990038d424c807ee2126400f7d8532007bcc299003dd614c801ee30a6400f7d8132007bcc099003dd604c801ee3026403bfd9432035fcca19002fd650c8077e3286403bfd903202dfcc81900fbe640c8015f3206400bf5903201f7ac819002bd640c8077e3206404bf98c32005bcc61900efe620c807dfa106403ef5083201fbe641900fee320c807ee9906404fb4c83200dfcc219002fd610c8057f3006400bf5803202dfcc9a8802fd64d440dbfaa6a200df55351025fcc7a8802fd63d4401bf29ea206df14f5101dfcc5a8802fd62d440dbfa96a200df54b510077e85a8803bd42d4401ef996a200f74cb51015fcc1a881bfa60d44017d306a200bf58351037f2c1a8802f960d44017eb2ca205bf99251005fac928812fe6394403ef31ca200b798e51005fac728807dd63944016eb1ca203bf98a51005fac528803bf4294401dea14a200f7cca51007ba6528806fe6194403bfa8ca206fdd4651015fcc128802fd60944017fb22a200efd91510057ec8a8816fc6454401de322a200af19151006fea8a88037d54544017fb1aa204bf18d51006fca6a88037c53544017fb12a203bf18951006fea4a88037d5254401dfa12a200ef50951007be64a8803dd325440dfba8aa201df94551005fec0a880afc605440d7f328a205bf99051005fac828812fe63144017
  | 5 => 0x9352005fac9a9012fe63d48017eb1ea401bf98752005fac3a900afe60d48017eb06a400bf5965202dfcc92900fbe64948015f324a400bf5925201f7ac929002bd64948097f31ca403f798e52005bcc729002fd6394807eeb1ca400b758e5201dfcc52900f7f529480df7a94a401bf98652005fac32900afe60948017eb04a400bfd915202df8c8a9002ff63548097e31aa406fbd495201efca4a9002ff61548037e30aa400bfd8152015f8c0a901afe651480b7f320a403ef990520057cc829002fd6414807deb20a400af59052025fcc62900fde63148016f318a400bf58c5201fbac629002dd63148077f310a403dfd485201fdca42900f7d521480df6a90a401bf9845201fecc229002f661148017eb08a403fd58452005eac22900afe6014807fd300a400be98052005fac02900ff960148017cb00a405bfd9742035fccba1002fd65d080b7e32e8400efd534202f7ca9a1003bd54d080bde2a68404bf98f42005fac7a1017bf43d0801df21e8400ef50f4202f7887a1006fe61d08017eb0e8402bf98342005fac1a1017bf65d0801df32e8400ef5974202f78cba1017bf63d0801df31e8400ef58f4202f78c7a1003bf53d0801df29e8400ef54f4200778a7a1003bf52d0807df2968400ef54b4201f78a5a1017bf61d0801df30e8400ef5874202f78c3a1017bf60d0801df3068400ef5834202f78c1a100eff659080d7f32c8400bf5964201df8cb21002fd64908015eb248404bf98e4201fbcc721002de63908017eb1c8403f758e42005bac72100efe6290807f72948400fb54a4201f7e8521017ef42908037f30c8400bf58642015fcc121002fd60908017fb2a8406bf99542005facaa101afc6550801dfaa28400ef951420077aa8a1003bc54508017fb1a8404bf18d420077e86a1003be4350801dea1a8400ef10d42007dca4a1003ed525080bf7a128403ef90942005fec2a1006fc61508017fb028402bf181420077ecaa1003be6550801deb2a8400ef195420077ec6a1003be6350801deb1a8400ef18d420077ea6a1003be5350801dea9a8400ef14d420077ec4a1003af6250801dfa928403ef949420075ca4a1003bd5250801d6a928403ef149420077ec2a1003be6150801deb0a8400ef185420077ec0a1003be6050801deb028400ef1814201dfeca2101afe65108017eb288403bf1944202dfcc821002be64108097f3188403f798c42005bcc621002fd6310807eeb188400b758c4201dfcc42100fbf4210807f72108403ef5084202fda8421006fe61108017eb088402bf98042005fac021012ff65cc80d7f32e6400bf59732025f8cb99012ff64cc80b7f3266400bf59332025f8c999003df53cc809ef29e6400f754f32027b8a799003df43cc809ef21e6400f750f32027b88799003bf42cc801dea166401bf98732005fac399
  | 6 => 0x80040080060028000008000000000000000000100000000010000000002000000000000000000000000000020000000002003000001000200000180080020020008008004001000800c000000000800400000000000080000010018004000001003000800000000000000020000000004000000001000000000300080040040030000000000000000000400800000080000040000008004000002000000c0000050000004097f31ea800bf58f5401dfcc5aa002fd62d50037f30ea800bf58754015fcc1aa002fd60d50017eb2ca805bf9925402efea92a01bbf54950019faa4a804bf98e54005fac72a00efe62950017eb14a801bf98654005fac32a00afe60950017eb04a806efd515402efca8aa002ff63550097e31aa800bfd895401df8c4aa002ff61550037e30aa800bfd8154015f8c0aa01afe651500b7f320a805dfd505402f7ca82a0177d541500ddeaa0a804bf98c5402fbcc62a002de63150017eb18a805f758c54005bac62a00efe621500bf7310a800bb98854005fac42a017ed621500176b10a801bf9845402fecc22a002f661150017eb08a805fd58454005eac22a00afe601500bfd300a800be98054005fac02a017f960150017cb00a805bf99353005fac9a980efe62d4c017eb16a601bf98753005fac3a980afe60d4c017eb06a600bf5965302dfcc929802fd6494c097f31ca604dfd4e53037bea72980efe6294c017eb14a601bf98653005fac32980afe6094c017eb04a600bfd915302df8c8a981bdf5354c09bf29aa600bfd895301df8c4a9802ff6154c037e30aa600bfd8153015f8c0a981afe6514c0b7f320a604ef990530057cc829802fd6414c09deb20a600af59053025fcc6298137f5314c09ef298a604df54c53037baa62980efe6214c09f7310a600bb98853005fac429813ed6214c0176b10a601bf98453027ecc229802f66114c017eb08a604fd58453005eac22980afe6014c09fd300a600be98053005fac029813f96014c017cb00a605bfd9743035fccba1802fd65d0c0b7e32e8605ef953430077aa9a180efe62d0c017eb168601bf98743005fac3a180afe60d0c017eb068604bfd9643035fccb21802fd6590c097e32c8600bf59243025fcc721813de5390c01eea9c8604efd0e4302fbe872180efe6290c017eb148601bf98643005fac32180afe6090c017eb048600bfd9543035fccaa1802fd6550c0d7e32a8600ef951430077aa8a1803de5350c01eea9a8605f7d0d430277c86a1802ff6250c077e3128600bfd854300df8c2a1802ff6050c057e3028604bfd9443035fcca21802fd6510c097e3288605bf99043025fcc621813bf4310c09ef2188604ef50c4302fba862180efe6210c09f73108600bb98843005fac421813ed6210c0176b108601bf98443005fac22180afe6010c017eb008605bf9
  | 7 => 0x9c8a300024426287c00000010a8000000000001be00000000000000000000000000000000000000000009b0000000001b20f52230000f88001ca22100000012000000000006daf30000000000b50000000002a992e00000002e8000000000000000000002c98000000e69e1a6800000000005e80000000000019617f0000000000000001cd15012d91e1982ce80022b00020607624c00005c80004b80000000000013500015c0000000000000000000001bc1cb8450001d307e9f68000000000001e88620001ba0000000002ba00000000000000026c00025c0630000e480000000000011680024d8000c3a8e0000001bd8000ed0001da0000000000001b08001598000000000001e300000000000029702498600020a09d8eb84713e13a15d80000026b1f38000000000ee0000000002800000000000002288000da23100001200000000000000004d0001fa0a09950000000001450000000000000000000000000000000a19aa8000002db00000022d000200100080000000000000008000000000000000400100180000060000018004000000000000400000000080040000000000000004003000002000600000400100000010000000000002000800800000300000040060000008000002000000800400000000080080000010008014000000000000400400000000040000020000000008005000800000200000100000000040000000002000000000000400000100000000000000004000001000000000000000080000000010008014004002000000000000100080000020000000000000000001000c0000000000004000002000800400000000000000040000000000000003001800000600400000040000000000004000000000001000000400080000000000000000000000000000000200000180000000010000008004001000800000200000080000020000000000000002002000c000000000000000000000000000020000000004000000000800c00000300000000000050010000000000000800800000000000000000000018000000002000000000200000000000080000000000002000000800000000000000000000000000000000001000001000000000000080060000028000002000001000c00200000000040000020000004000000000000000c0000000004002000000000400200100000140020000000004004001000000000000000000000080010000004000000000800000000000100080020030000000002000000800000200100080000040000018000000000000800000200000000040000000000004002000000800400600100000000000030018000000000003000000000000000080000010000000000000000800400400600200000040000008000002001000000000000000000000000000000004000000
  | 8 => 0x1e79968b880000024f8000000000000000570000000000000e980000000000000024580000000000000023a8000000000000002439e68001a88d5a54a810340000000002bf0000001f091e8000000002378000000000718000000710000ec00000003783f0000000000000000000000000000000000000000000000000000001f00000000000000000000000000000000000002d90000000000000000000000000000000000000000000000000001eb000263aa10001dc26201d0000001d800029924006b00005b8fe8000000000000000000000000002d08000000000000000000000000000000001f61cd8c58002cd8be80015829d8000000510002988000000000000000402d5800000081901027aa81dd8002760002ac2da8000000d200007f0001878000001578000f30000500e112b00000000000000000000000000000000000000000000000000000000000007e16e0a90002b01140000000001a599700000aa500000000000f180000000000a00000006610ea1780016c8000001228000000000000000000000fa8000002eaac286e0000000000000000000002db80026a8000000000000000000000000000000000000000628000000002220000002b40000000000001bd00000000029c8000000480a80001ae80000000000000018a0000000000000000000000000000000000000000000000000000000002bf8002ec95f1110001e9148000000000247aa72948e700000000020a91b80000000000004b00000000000000000000000000000000000000000000000000000000000000011228f8000000001e800000000000000024980000000000000000014300000000021a8220000000000000000000000000000000001382300000000002b80002470002d02228000000002332e08000000000000000658000000360000000000000000a10000000000000000000000000000000002a186e80000000000000000000021000000000003a80000000000000000000015600000000004f0000000000000000000000000000890000000000000000001978e297d1748f08000a20000001a18441198000c90b90000000000708878000000000000000000002080ce00006f0000001ec0000000000000b200000000000000000005300000000005a80000000000000000025b8002568000001910e20060000000000000000000001368000000000000000000000000000000bf00000000000000011317c0d500000000000000000000000000012f80009f0000000000000000001cb00000000000000000000000000007b00027d80000000009e80012c8000000000000000002e880000000000026580000000002c0000000000358000000001a30000000000a500000000023f8000001780000000001f300000010e000000000000000000
  | 9 => 0x2280000000000000000017980014016501c0002cc00000000000000024e8000000000000000b580000000000000002e0000002b725600000000000000000b8001988000001a12c12580000000000001262450002408000000000fd9e980000000001e80000000000000000000000001f8000000000000001ef8949ca82f9540000000988000000000000000000000000001a600000000026f8000000002f0a940cb050a999139aa1248000000000001ef0000be0750000001a48001df16d2038000000000000000000000001c024100000000000010a0000002122bc00000000012380000000000000000000000024a80005900000011180011b00000003c26ea9580000015b80000000000002d2c918e8328000000000000001148000000000002130000000000000b78000000000e08260000000000000ab0000000738001c39ab80000000026900000000007300019a00000000000000000000000000000023a0000000002071548002c22648000000000e920980000000000000000000000000000000016f0002d2a510128000002b60908ff8350018000000000000000090000002480000000000001ecac50e1a6895b0d08000421acab500011d00000000000000008f95c8828000000000000000000000000002a00002f48002068000002c400000000000000000000000000000000000000000011700013f0188001490000f90000000920000000000268000002ce0000000000002d60320cc00009a8b98000000000000000000000002be8000b38000cf80000000000009100000000010f9d88002e48280001e70000000000000d00000000880000000001908000b28bf99e0458000002b300000000000000019423d0000000000000000000000000000000000000068000b100000008a0002be00000005596400000000000000000000000000000025e0000c30000050000d9a6c80000006fa2a26a213a9b0000001710001ad00000000000000000000000000000000000000000019180000021d24a0000000002920002600f200027680028309e1d000007812d0002360002f402c80000014886d0000db0000808088000002110000001631fea91000052978a822e78002a202b0048000002380000000000002208000002e9af2a7b80026680017700009294b0000000000000000001e1000000000000051ad780029392a8000002a78000f58000001f501080029609b9c800000000000000000028b0001610000000000001100ca8c98f4000093986a9280000d0000000c880000000000f8169b10001cf86c80000000000000017300000000000000000028c00002d8000000000000001db0000001bc80000000000000000000000022e00000000005d8002a50000000000000000000002090000001cc0000000b414193c2c48000000
  | 10 => 0x2829c080022b8000000000000000000000000001268000000000000000000000000000000d38000000839bf0000ee80000027980000000000000000000009a2d20000002eb06c0001030000001040000000001ce0000000000000000000000001b700029d10d1e40abad480000011080000000006a8000002c00000000000001288002ab1070000000baa48acb18300000000027d0001d080000000000000022780000000012415080027500000000000000000022f24b800106000057a708000000000000000000ff00000000000000000000013700000000000000000000000000000000000020480000000018e0000000002d38002088002e90000001701c6953ae28e02df1b8a1b80000000000000001180002f10280000000000000000000000022e80000000000000000000000000000000000000010b80012700001528e800000000000000000000000000000000000000000013ab90000000000ce8000df8000001d180000000000000028180019d07a8000ea01300000000000028b8000002650001758ba00007fa1600000000000000018f22680000016baad8000001308000000000000000000ed800000000000000000000000000000000000000000000000000000000037234aa38820438b18001818000000000000000000000000000000001f900000000000000000000000000000580000000009980000000023e0000000000002338000000000a99688000560000000000da8000000000000178000002850000000000000000000002372dd8000000000000001938670368000000000000000000609a40000000000000002418000001ee80023c25a0002950700000000000000000002b282b8c000000016ea0f800000000000084800000000000000139000000000120977ac099d8a88000000000002dc0002b68000000000000000000002e380000024900022180000000010380000016180005d0000001d40000000000002bb8e51438002290f4abb19c00005200023520d800160079a01a0c8000000000000000000000000000002f00000000e7a359c58000000a680000000000000000027800000000000000000029a0000000002ab8002b780000000000000000000000000000016913c8000000000000000192698c212a2b380780000000016c00000000000000004f80000000000000013a8001810000000002cc9ea0000000000000000000000002740000000000d420b1b984d8ae1470001b51f2856ae100000000000000027c18021e8001f88000001278001f480000000000000000000000000000000000000000017b8001f200000000000000000000000000000021e0000000000001721b480000000000b12c0000000000001c40002980000002e30000000002b581d9b30968000000c480027480000000000000000
  | 11 => 0x2ae8000000000000002878001840002ed00000000000000000000000028480016a1d4ad122c8001bb25e8ad8f60d11760ac00028801f1b900003da1713e82389d00000003b80000016700000029080028380000000000005f8af8000001b780004600000000000013006a00000000000000000009600000000000000001980000000013f80017f8000d6a6d8000bda9c03900015a8000000000000eb0000000698ae9e60000000000000000000d900000014f80000000000000017e8000000000000000410000000000000002180000000070651a38bb1e500000000014d0000000000ad0000618002a880000021c0000000002df80003127796780000000000000000022700000000000000000000000011a00000000006798d12f00000000000008f00015520d0001ad9d50000250002de1d70000cc8000c500000000000009780000000000000000000000016829b9c493618ca5c8000000001920002630e30a4aac8000000000000000418000000000002720000000000002c78000000000000c0a1180000000000000000000000000000009900011821d80000019f0000f72108c71da8000000f381e11894d80000000000000000000024e0000000000000000902e80000861ff0d48000000000fc80008c0000000000000001fb8000002f214c9531ab0000000000000000000000000000cd0000810001888000000000000fb19c80000000000000007a000000000142a7e0000000000218000000001c280016081600000000019b0000a700000000000009180000000000001483a2460002c30980000000000648270000000000000000000a58002898000000002dc80019f8001a700000020f0000000000000000000000000000000200000000000000000000000001ea8df00000000000000000011f2900a013b9c887222480000020e800000000000000192ab08000000000588000001a20000a42200000000001882508002aa9821340000000041c78002d31fd80000019ea240000000000000e40002f180000000000008000028f00004e072a1f80000000000000000000000000014c00280008e0000000000000000000000000000000000000000000000000000000000000000000000ef000202a8a1a68000e8000000218a258002b89990e380000002a0ca16a93100000000000000000001c8f292803e00000011513d0000000000000002341e00000000000000000000000000000b0000000000125000000000139800151000094095000077000028a9687ba7f00028d80000000000020b8c100000000000000004c0000000001beae18000001358000000000000000000000000000000d80002770000000000000000000aa80000026e00000017a80000000000000000000000000000000000000000020c0cf04a1a50b7000
  | 12 => 0x2b20000000000000000000fa0000001708540000002ed97a0000000000000000000001c70002c88231998000000ac8001870000000000000000000000000000000000000000000000000000000000e88000000000002531099c60000001d79890012cd2d9830aaf80027f80000000000000000000000000000015d0000000000000fd0000000000000001d60000000000000002eb80000000000016680007918d80014a80000003b1568000001fa80000013380000000000000000000000012198f80200003025a8000000000000000001b18000000c78000000000000002a480000000000003d0000002598000000cb80000000000000001b8f12329c31740c627a05f1d109700ea0e2791f1a5d1498000000000002c70000638000000000002e00000000000002d180000000000000000000980000023900000026f00000000021a0002260000000000000000000000000000002528002c81fe2cb8002de94200000000000000000013d80019b80013b267a868d780000000000029a80000018b8000002c380000028d00000000000017e0000000a60c1a05a4b00000e000000000053a7c80014a00026d0f68000000000000000000000000000000000000002a28000000000000000000000002cf9408002b48000000002ef8000000000000000000001c90000000000002700000000000000000001c223180000000000008b0001cea538002430000002ee8000000002b12ec00000020400000000000000000018280016200000000000000008eaa90000000000000000000000000000001e20000000000000000000000002ca0001eb8000000de82900000000000021480000000023c80000000000000000000010f0850000f988d0000fc0000000e6000000275800000239a010d8add27180000000000000000000025da588000000000000000000000002e72610000000000000000000000de2a40000001dd0000778000001de8000002a616280005c0030c800007d0db8000000000000000001fc00015e02587580024c8000001e59589ff80000000000f00000000000015f80000000000000000000000021680000027e8000680000000000000001080002b180000014684c80000000000d9a780000000001a29e10781001800017d800000251a158000000000000000000001158000000002618000000000000001dc8000001e48f0000000106a919bf85a2e69058001388000000b09bb8000000000000000000000b30001518000000000000000000000000000000fb90d80000000000010480006b8000000000000000000002540000000000001698000000bc8001b590c0000000002a30dd0689c9800000000000021000257a1b0000000001d92789f996629300000000000000000000000000000000000025f0000000000
  | 13 => 0x1558000000001ac17b00014f1258000000001a28fe2140001090000000000668000889b680000029e8000000640000000000000000000001fc8600000000000c694e19017900000000000000000000000000021f0330000000000000000000000000000000000001318000000000000000000000001db9b600000000000000000000000028580000029fa6bada0000000000002c68000001a000000000000000000000025200000000000000000000000000010b2c19c50000001a0aee1c100000012e9a980000003fac580000000001580000000000022d80000000000000000025904300001411f8000000000000000000000000000552a080000000024200000028700000016b00018c0598000000000000000000000000000000000000000000000000002840000000000001b38000002732a689c2661f12860789210002b98000000002af0000000002ea22980013327a80000000000000022c1f7a321f42e58000b48000000000000000000000001e280000000000000000000000004e8000000000002078002e215e8000000000000000000002641e080000020300003ea468448000002d505e0000000000000002ad0001728002020000002d69838869cc80000000000000022a8000000000000002bd00000000000000000000025500000000000000000000000017500000002080000018580000000025b28900024f0000000000000000000000000000000000000002ca8000000000000b68000000000000000768ec9b28008000000000b81949fb24280000000000000000000019a80c8c28002d415a000000000000000000105147800000000000000000000000000000129165800000238800000271000000000000225034800144800033a00ae400000016f97680000000000000022800000000020511d8000000000000000000170000a380013200000000017caaa00000023da000000000001ed80000000000000000015200000008a8000002609648080000000000001018000cda73ac60000000000000000d28bd0000000000000000002ef0002d81190000dd80000010ca2f8001f80000000691160000000bb8748e58000000000000001460000000000dc23b80000028a84080000000000000000000000000007d8002e500000000000012b8000000000001178000d71458000002a58001a900023b00000000000000028880000000000000000007c8000000000000000000000000000000000002128002448958000000001848000001298000318000000000001b8152a308858498000001af29f1a825700018a80000000000000000000018082a800000000039a4d23f0f80000000b600000000000000000c0468001ee0000000000000000000380a78002bd91c042abc80000009f8af0000000f780000
  | 14 => 0x110001348000002d700000000000000012300000000000008b884000000000000112a5f8000000000000581021850000000000000000000000000d30000000000001379d58001221d38000000001fd00000010080000000000000380000000000023ea238d19c19638aa0000000000000000000bc0001d21ed01b0000000000000000000000dc8ef8000000000000000930000000000000000000000000000000000000000001ba80016d800000000000000000000000000000000000173a8caf380000000000000000000000000000000000002980000000026721c8d60000000001e380000000000027b00001a90004a8001592cf1af80000000000018b0001f58000ea8000000000000000872f12e6000193000000047889a978001ae0000000000000001898000000001de0000001d980000019580000011c8000000000000002d89b400007403880000000000000000008d94b80000000014e80000000011a8000000000000000002ba8000000000000001328000000000000000000000000000000a28000000000000000000000000000000240000000000000000000000c4219108a7285480000000000000005b0000000000000490000000001cf0000000000000001b02198001f717180000000000008c8002368000000000000000000002808001411441d68611d28488000002ae00000015700000003c8000002150000000000001df800000000000255800083000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xd429942001e5f329942001e5d329942001e3f425942001e6e425942001e3d425942001e5f325942001e5d32594200167a205942001e79205942001eae729902001e9f329902001e9d329902001cbf725902001cbd725902001e9f325902001e9d325902001e9f4298c2001e9d4298c2001cdf7258c2001cdd7258c2001e9f4258c2001ece4258c2001e9d4258c20016cf2058c20016cd2058c200066d655082002eae6450820006cd635082001daf7650820006af765082001eaf655082001f2e6550820006ad655082001f2d65508200062d655082001eaf635082001f8e6350820006ad635082001f8d63508200068d635082001fa6615082001fa5615082003eae605082001faa605082001eb7429842001eb5429842001ed7329842001ed53298420006ad425842001eb7425842001ee6425842001eb54258420006e54258420006a5425842001ed7325842001ed53258420016e72058420016f22058420016e5205842001ef12058420004bf745971002cbc745971001eae6250b10006ad6250b10046cf624cb1001ecc624cb100078d424cb10047c6214cb10007a54248710034fb7654310004df7359610024dc735961003eaf6250a1001eac6250a1003faa2050a1001ece624ca10006cd624ca100078d424ca10034f77654610007c93248210004bf745951002cbc7459510004df7359510024dc7359510004ef725951001cec7259510006af625091001eac6250910006cf624c91001ecc624c9100078d424c910014f4764c510007c53288510014f47648510007a5424851000cf87650110007a9428811000cf87648110007c93248110007e1214811000e7671994100167a7099410004bd7299010004bf725901000eb65159010016ba5059010016ba105901000eb91059010004dd7298c10004df7258c1000ed65158c10016da5058c10016d71058c10016d51058c1001eae749881001ead749881001ece739881001ecd7398810006ae7458810006ad7458810006ce7358810006cd735881000ee65158810016ea5058810016e71058810016ea1058810016e5105881000ee9105881002cbf76d0810004bd76d08100063e65d08100063d65d08100069e63d08100069d63d081001eae62d0810006ad62d0810004bf7650810004bd76508100063e65508100063d65508100069e63508100069d635081001eae6250810006ad6250810024df76cc810004dd76cc8100065e65cc8100065d65cc8100069e64cc8100069d64cc81001ece62cc810006cd62cc810004df764c810004dd764c8100065e654c8100065d654c8100069e644c8100069d644c81001ece624c810006cd624c8100078d424c810036766554410006b56454410006d56354410006e562544100367a6554010006b96454010006d96354010006e96254010007715154010
  | 1 => 0x5140015ba70d51400059d7315140005ad7215140005b57115140015ba7015140014bc7650d40014bc7650940006af625094001eac62509400078d424c940014bc765054002dba749414002cf8765414000738545414002eaf425884001ece624c840006cd624c8400078d424c840026cf3258b3001eae6250b30006ad6250b300078d424cb300059d7414e30005cd7214e30005d97014e3002cdf7650e3001cdf764ca3001ece624ca30006cd624ca300078d424ca30025d873542300075b5354230004df7359530006af625093001eac6250930014dc764c930006cf624c9300078d424c930005cd72cc530014dc764c530024f876541300265f3299430024dc73594300265c73594300265e43594300265f32594300167a30594300267930594300269e7399030004bd72990300269f3299030004bf72590300269f32590300065d65d4c300065d6550c3002e9e6450c3001eae749883001ead7498830026cf3258830006ae7458830006ad7458830026ce7358830006cf5358830026cc5358830026ce4358830006cd4358830016cf3058830016cd305883002cbf76d0830004bd76d08300063e65d08300063d65d083001eae62d0830006ad62d0830004bf7650830004bd76508300063e65508300063d655083001eae6250830006ad62508300065e654c8300065d654c8300069e644c8300069d644c83001ece624c8300078d424c830006b74298430006b54298430026d73298430006d53298430006d75358430026d45358430026d64358430006d54358430006b74258430006b54258430026d73258430006d53258430016d73058430016d5305843001e9f329932001e9d329932001e9f325932001eae325932001e9d325932001eaf215932003eae205932001eac205932001ece7298f2001e9f4298f2001e9d4298f2001e9f4258f2001e9d4258f20006ad644cb20026ce634cb2001dcf764cb20006cf764cb2001ecf654cb20006cd654cb2001ecf644cb2001f8e644cb20006cd644cb2001f8d644cb200068d644cb20046ce614cb20006ad6448720004df7359620024dc735962002cef7650a20006af7650a2002eac7650a2003eaf6550a20006ad6550a2003eaf6350a20006ad6350a20007ab7050a2003fa87050a2001eae6050a2003faa5050a200078d42cca200078d424ca20006ad4258620007a9425422002cbe74d9520004bd74d9520004df7359520024dc7359520004f7715912000cf47159120005cd738c9200078f424c9200078d424c920014ec764c920026cf764c920006cc764c920006cf654c920006cd654c920006cf644c920006cd644c920046cc614c920007cb704c920007c8704c92001ecf604c92001fcb604c920005cd73c8520014ec7648520007c9329412001cf87654120007c9325412001e3f429942001e3
  | 2 => 0x1ecf644c82101f8e644c821006cd644c82101f8d644c8210068d644c821046ce614c82101fc6614c82101fca604c82101fc9604c82101ebb429802101eb9429802101edb329802101ed93298021006cd325802101ebb425802101eb9425802101edb325802101eea325802101ed93258021006e93258021006c9325802100eeb215802100ef2215802100ee9215802101ef121580210147c755935001eae6250b50006ad6250b500072d5250b5001ece624cb50006cd624cb500074d524cb500078d424cb5000ed6739875000ed57398750006b74298750006b54298750006d73298750006d53298750036f25098750036f15098750036775258750006755258750006b74258750006b54258750006d73258750006d532587500053c745475000e76615475002e9e739925002e9d739925002eae7299250004bd729925002ead7299250004ad7299250016ba70992500163f50992500163d5099250004bf725925002cbf76d0a50004bd76d0a50004bf7650a50004bd7650a500069e64cca500069d64cca500069e644ca500069d644ca5001ece624ca50006cd624ca500078d424ca50014f870586500147e76951500063f64951500157a70951500055d73151500056d72151500057571151500157a7015150004dd72d8d50005cd7218d500269e7418d500269d7418d50026ce7218d50004dd7218d50026cd7218d50004cd7218d50026d67118d50026d57118d50026d97018d500265c63d4d500147c7654d500147c76549500069f63d09500069c63d09500069f63509500069c6350950006af625095001eac62509500072d5250950004de76cc950024dc76cc950004de764c950004dc764c9500074d524c9500078d424c9500065c63d45500157a70d45500147c76545500053c74545500065c635455001578705455001eae6250850006ad625085001ece624c850006cd624c8500078d424c850014bc7459740004dd7298f4002e9f4298f40004df7258f4002e9f4258f400269e6350f4001ece7398b4001ecd7398b4002eaf4258b4002eae7458b40006af5458b4002eac5458b40006ce7358b40006cd7358b4002eaf4358b40006ad4358b4002eaf4158b4003eae4058b4002eac4058b400069e6350b400069d6350b4001eae6250b40024df76ccb40004dd76ccb4001ece62ccb40006cd62ccb40004df764cb40004dd764cb4001ece624cb40006cd624cb400078d424cb40006ad62507400367671996400367571996400167a70996400163f40996400163d40996400063e65d0a400063d65d0a4001cbf7650a400063e6550a400063d6550a40006ad6250a400065e65cca400065d65cca400065e654ca400065d654ca4001ece624ca40006cd624ca400078d424ca400367a6554240004df7359540024dc7359540014be76d51400063f65d
  | 3 => 0xb415804100eb9415804100cdc73597310269e7399331004bd72993310269f3299331004bf72593310269f325933102e9e6450f3101eae7498b3101ead7498b31026cf3258b31006ae7458b31006ad7458b31026ce7358b31006cf5358b31026cc5358b31026ce4358b31006cd4358b31046ce3158b31026cc3158b31026cf3058b3102cbf76d0b31004bd76d0b3101eae62d0b31006ad62d0b31004bf7650b31004bd7650b3101eae6250b31006ad6250b310069e644cb310069d644cb3101ece624cb310078d424cb3100e76719963100e5f319963100e5d31996310367a70996310367970996310063e65d0a310063d65d0a310063e6550a310063d6550a3101eae6250a31006ad6250a310065e65cca310065d65cca3101cdf764ca310065e654ca310065d654ca31006cd624ca310078d424ca31036766554631004bf745953102cbc745953100cde76d4d310059d7414d31005cd7214d3100dd67114d31005d97014d3100cdc7650d3100cdc764c931006cf624c93101ecc624c9310078d424c931025d67394531024f47654531007545354531026cf325883101eae6250831006ad62508310078d424c83101eae729932101e9f329932101e9d329932101e9f325932101e9d325932101e9f4298f2101e9d4298f2101e9f4258f2101ece4258f2101e9d4258f21046ce2158f2101ecc2158f2101ecf2058f2102eae6450b21006cd6350b2101daf7650b21006af7650b2101eaf6550b21006ad6550b2101eaf6350b2101f8e6350b21006ad6350b2101f8d6350b210068d6350b2103eae6050b21004bf745962102cbc74596210078f424ca210078d424ca21024ef764ca21006cf764ca21026cc764ca21046cf654ca21006cd654ca21046cf644ca21006cd644ca21007c7714ca21047c4714ca2101ece614ca21047c6514ca21007c53254621006cd3258221024de73d9521004dd73d9521004bf745952102cbc7459521004fb7058d21014f87058d21005ad749092100cec765092102eaf7650921006ac7650921006af6550921006ad6550921006af6350921006ad6350921007a77150921007a4715092101eaf615092101fa7615092103eac60509210078d42cc9210078d424c921007a5429452101cf47654521007a5425452101e3f429942101e3d429942101e5f329942101e5d329942101e3f425942101e3d425942101e5f325942101e6e325942101e5d325942100e76215942101e75215942101e9f329902101e9d329902101e9f325902101eae325902101e9d325902100eaf215902100ead215902101ece7298c2101e9f4298c2101e9d4298c2101e9f4258c2101e9d4258c210066d654c821006ad644c821026ce634c82101dcf764c821006cf764c82101ecf654c82101f4e654c821006cd654c82101f4d654c8210064d654c821
  | 4 => 0x8132005d5711813201e9f329903201e9d329903201e9f325903201eae325903201e9d3259032026ad3259032026cd7298c3201e9f4298c3201e9d4298c3200c7c7558f5101eae6250b51006ad6250b510072d5250b5101ece624cb51006cd624cb510074d524cb510078d424cb51016ba7498351016b97498351006bb4298351006b94298351006db3298351006d93298351036f25198351036f151983510367b5258351006795258351006bb4258351006b94258351006db3258351006d932583510269e7498e510269d7498e51026ce7298e51004dd7298e51026cd7298e51004cd7298e5100ed67198e5100e5f5198e5100e5d5198e51004df7258e510069e63d0a510069d63d0a510069e6350a510069d6350a5101eae6250a51006ad6250a51024df76cca51004dd76cca51004df764ca51004dd764ca510078d424ca5100cf47158251004bd72d9151005ad721915102e9e731915102e9d731915102eae7219151004bd721915102ead7219151004ad721915102eb5711915102eba701915102eb9701915102e3c64d515100c7c765515100c7e7694d510053d7414d510056d7214d5100d767114d51005797014d5100c7c7654951004be76d095102cbc76d0951004be7650951004bc76509510072d52509510069f64cc9510069c64cc9510069f644c9510069c644c951006cf624c95101ecc624c9510074d524c9510078d424c95101eae6250851006ad625085101ece624c851006cd624c8510078d424c85102eaf4258b4101ece624cb41006cd624cb410078d424cb410063d65d5241005b571d52410059d7315241005ad7215241005b57115241024bf7650e4101cbf7650a4101eae6250a41006ad6250a410078d424ca4102db47454641007375454641004bf745954100cbc7650941006af6250941006cf624c94101ecc624c9410078d424c94102cf4765454102e3f429944102cbc745944102e3c745944102e3f435944102e3f425944100e76415944102e7541594410063d65d5041004dd7298c4102e9f4298c41004df7258c4102e9f4258c410063d6550c410269e6350c4101ece739884101ecd739884102eaf425884102eae7458841006af545884102eac5458841006ce7358841006cd735884102eaf4358841006ad435884100eaf415884100ead41588410063e65508410063d65508410069e63508410069d635084101eae6250841024df76cc841004dd76cc8410065e65cc8410065d65cc84101ece62cc841006cd62cc841004df764c841004dd764c8410065e654c8410065d654c84101ece624c841006cd624c8410078d424c84102ebb4298041006b94298041006db3298041006d93298041006bb545804102eb8545804102ebb4358041006b9435804102ebb4258041006b94258041006db3258041006d9325804100eb
  | 5 => 0x347c755913201cde76d4d3201dce72d4d3201cdc7654d320059e7414d320059d7414d3201dce7214d32005d67114d32005d57114d32005da7014d32005d97014d3201cde76d0d3201dce72d0d3201cdc7650d3201dce7210d32005ad7494932025ce7394932024ec7654932005ad7490932025ce739093201f8c3250932024ec76509320078f43509320078e43509320078d43509320078c435093202eaf7650932006ac7650932006af6550932006ad65509320078f73509320078c735093201eaf635093201f8f63509320078f53509320078e53509320078d53509320078c535093203eac605093202cbe74d8532004bd74d8532006ad42d8532005cd7299532005cf72595320059e74195320059d7419532005d67119532005d57119532005da7019532005d97019532005cd7299132005da7099132005d970991320055f75591320055c7559132005cf725913201dce72d5132005cd72d51320071f549513201dce7295132005cd7295132004de7615132004dd761513201dce7215132005cd7215132005d67115132005d57115132005da7015132005d97015132005cd75d8932005cd74d8932045ce71d8932005cd70d893201f4e52d4932005ce769493201ece7694932005cd759493201f8e7494932005cd749493201f8d74949320058d7494932045ce7194932005cd7094932025ce7654932005cc765493201dcf755493201f4f75549320074f65549320074c6554932005cf7454932045cc7154932005cf705493201d9d72d09320078f62d093201f8e52d09320078d52d093201f8c21d093201f8f20d0932005ce769093201ece769093201dcf7590932005cd7590932005cd74909320058d7490932045ce7190932005cd709093201f8c425093201d9f72509320078f72509320078f62509320078f525093201f8e52509320078d525093201f8c525093201f8f215093201f8c215093201f8f205093201f8c2050932025ce7650932005cc7650932005cf7550932005cd755093201dcf745093201f8f74509320078f64509320078c64509320078f54509320078e54509320078d54509320078c5450932045cc7150932005cf70509320078f76509320078e76509320078d76509320078c76509320078f75509320078e75509320078d75509320078c75509320078f65509320078e65509320078d65509320078c65509320078f71509320078e71509320078d71509320078c71509320078f70509320078e70509320078d70509320078c70509320059e74d85320059d74d85320078d42d85320055e75985320055d75985320078d42985320078d4258532005db7058532005d870585320078d42185320078d42d81320078d42981320078d42581320055e75181320055d75181320059e74181320059d74181320078d4218132005d6711
  | 6 => 0xf4258c5201e9d4258c5201eb7429845201eb5429845201ed7329845201ed5329845201e77525845201e75525845201eb7425845201eb5425845201ed7325845201ed5325845201ebb429805201eb9429805201edb329805201ed9329805201e7b525805201e79525805201ebb425805201eb9425805201edb325805201ed9325805201cbc745974201cbc7458f4201cbc745874201cbc745834202e3f659974202cbe7614f42004bd7614f4201dae7214f42005ad7214f42005b67114f42005b57114f42005ba7014f42005b97014f420053e75983420053d759834201ece7298e4201e9f4298e4201e9d4298e4201ece5258e4201e9f4258e4201e9d4258e42006cd6354a4201cec725824201cbe76d51420063f65d514201dae72d514201cbc76551420059e73151420059d731514201dae7215142005b67115142005b57115142005ba7015142005b9701514201cbe7690d4201dae7290d4201cbc7650d4201dae7210d4202dae7494942005cd739494202cec7654942024de73d8142004dd73d81420063f6599542005ad7299542005af72595420059e73195420059d7319542005b67119542005b57119542005ba7019542005b97019542005ad7298d42005b67198d42005b57198d420053f7558d420053c7558d42005af7258d4201dae72d4d42005ad72d4d4201dae7294d42005ad7294d42004be7614d42004bd7614d4201dae7214d42005ad7214d42005b67114d42005b57114d42005ba7014d42005b97014d42005ad75d8942005ad73d8942005ad71d894203dae70d894201f2e52d4942005ae769494201eae7694942005ad759494201f8e7394942005ad739494201f8d73949420058d7394942005ad719494203dae709494201f2c525494202dae7654942005ac765494201daf755494201f2f75549420072f65549420072c6554942005af7354942005af715494203dac70549420053e75185420053d75185420059e73185420059d7318542005ba7018542005b970185420059e73d81420059d73d81420053e75981420053d7598142005b77158142005b4715814202ead729904201e9f4298c4201e9d4298c4201e9f4258c4201ece4258c4201e9d4258c4202ecd4258c4201cdc735973201cdc735933201cdc735873201cdc73583320071f5495332024de7615332004dd761533201dce7215332005cd7215332005d67115332005d57115332005da7015332005d970153320078f7250b3201f8e5250b320078d5250b3201f8f2150b3201f8c2050b320055e75987320055d759873201eae729923201e9f329923201e9d329923201eae525923201e9f325923201e9d3259232006ad6454a3202eae6450a3201daf7650a32006af7650a3201eaf6550a32006ad6550a3203eae6050a3201cec7258632006ad42586320047f7559132
  | 7 => 0x800000000000000200000000100401500000200000000100100200700100100500202200400200200700000200000500000500800200200500600001000b00000100700100300000500100201a00000200000b00000b00400100200200300000300600100101100000000500000400000700700200000200200500100700000000000800800200400000600200200200100900201000100000300300b00000000000000000300000000000800300200000000300000000500200000900000000200000300a00100100100100100000000000600100b00000000200000b02300000000b00100200500900000000600000000000300000000000b00000b00000000000000000000000000200600100400101000000000600600200000500700300000000300000200100000400000700500000100800000100600000900100000300000200300a00600000000100400b00100b00300000d00500400000200200700000100100200e00000a00300100700401c00000300100800a002004000000000000002004df7358354024dc735835402d3d76d52540363d76d525402eaf4258a54004dd7298c5402e9f4298c5402e9e5458c540369d5458c54004df7258c5402e9f4258c5402e9c4158c540365f5058c5402e9f4058c5401ece739885401ecd739885402eaf425885402eae745885402eae5458854036ad5458854006ce7358854006cd735885402eac41588540366f505885402eaf405885402eb7429845402eb4415845402e77545845402e75545845402eb7425845403677505845402eb7405845402ebb429805402ebb4258054004bf745875302cbc7458753026cf3258a53004bd72990530269f32990530269e53590530369d5359053004bf72590530269f32590530363f51590530269f31590530269c305905301eae749885301ead7498853026cf3258853006ae7458853006ad7458853026ce7358853026ce5358853036cd53588530366f5158853026cf3158853026cc3058853026d73298453026d73258453026db32980530267b5358053026795358053026db32580530367b5158053026db315805302eaf4258b43024bc7458743026cf3258a43024dc7358243024bc765514302cdc7654d4302eaf4258843026cf325884302eae7458843026ce7358843026af4358843026ce4358843026ad435884302ecd4358843004bf745875202cbc7458752004df7358352024dc735835201eae729925201e9f329925201e9d329925201e9f325925201eae325925201e9d325925201ece7298e5201e9f4298e5201e9d4298e5201e9f4258e5201ece4258e5201e9d4258e5201e9f329905201e9d329905201eae5259052036ad525905201e9f325905201e9d325905201e9f4298c5201e9d4298c5201ece5258c52036cd5258c5201e9
  | 8 => 0x53a86c8ac56a68a0000000001c261e2fc0004380009b21207e076e0e80005600067a02ae78c5802bc00056e00000000092e83000099400025e5d600057c3ac47099a77e0006b86f04f01b081434c0d88ce01a1a45f80000000003967049fe0000a000072266626c74041a9660004ae0000006bc00000000000003036a00034417c2924bc01e0003000f600029033400000058400000054c1747700008f25e89c200052a00063455a8ec000000000000a082d80000001460000000000000000006f80004f85e48cc5120005aa0009280004aa00039c2028b62ce00000062627a3944140000000000000002e06c20420002fa0000a60000000000002680002a40000000008327a86080003a675a00000000000052035a0006686705ac6d400000000000000000050c0000000002e20000001c8a0c0000000003dc91264204400098a3b299600000000047c0000001a000028a6c48b46941fe2140000004005f24029484a62f459618c35c1f64c00700000000000002100000007f00000009060004403e61265b00860001a66b600000000038800000000034a9500008521521122c47c07027567e65f68da00069e0009ea07200025a0000000000000006c07ac0001e02fe99243400067a37e7ee0003802b000099e9de0000000004745f07bc57400000000040a1824a4778a1200060435806000000049247648a00000000000027e0000000000000005a298c00075e80600063c00028000066000096400029451c0004b44584529e457011646c75294298e03c93a57e0ec9fc95a82c0008f44607a260000016400000000087687aa0a79a35e0000526500000f43247324c400000013615c1e23901380000008680000001cc00079400042e20c38e1664f22a097a1060000006de0000001b60004f60c62c80000003468fc10c00088a48c84a0001ea2ea56468e00003600000000000000000000000000000000000077a0a86a87963c000000000000066c0004064ca00000000000063600000000059400000000000015a00089e1680680002120245060002b80009b000000000000000000000400000600000200100300200900000e00100800401a00200001800300300200000100100500000200100d00000700700c00100100600601600000000500000000602100000200000100700100000000300600100000100500000000500200200600001500000800101000002000100000300200400400300000700000001200000200400500300100000000400200400700000600100400900b00100300000000300800000300100000100000000000000100400000200200000000700600000500000000000000f00000500100000800200a00100200100000400000100500000000100300900000300800100200600000100000a00000000000000000100100
  | 9 => 0x2c5d22f285c0000000000e60000000008080000000225b60000006a451600081271e6dc41800a0005ae77c9f65566be28281a3403e212e58871400063e17a8c40008742c20001900000002f805e4e06580000000004e20000000006b200012479000092400001288486a65c0000005a04205a647e11c8be0000009020a20260000002700003861f25c498028c7dc26a9560000006fa1ee3a20001e800000016e1148e00501c0000000000000a164680000000004d00006da2cc9aa06e90c0009bc37200000000000000015800000000066e62496c61a0000009d27be3504a07faa066e88820665546380009c00000008aa32a0000000340008a020887e00000016c0009e20e24ee88041e59c1da8b804e6204822dc3640c25b894638261246269a8920001320000ea00000021649c0000008607fc2ba00000043e00000000000000000004a00000095414e00000000000000094e0005da18485a85000083e3740000008620004d282600073e64880010800000070a22c00062246e6ac3d679c0003ee0000001f00000004d80000000007a66ec4ba69c00000071271c8f06d05148f64228480022780000005c600046a0004e62d400044c93e80c01c9364b04960002f600049e0e45480000009be06c0006980003b87987546ba0003de00027c8e60000004ec00000036600012c3ca7480000007d40000009e000000000000083c44a2001fc0001429166d61440000ac00000033e6640003ec000000000000000a100000000000000006880005b20007343929180168ee0000005828640005ea54400c3e400054a00032c7883426f21e600000009e6800000008220000b86300769140000007c40006e60400000002c00007ea9225bc9e66180000002ac3983d431636e08477200041c0000003d20008168369e87e23767f4360a026fc7440ce02a54e3780d24545020000008c000e6820002540009686fe38c0005a417200000000000048050e4be0b008225c7660005c802e89422a00096e08a22640c0002348e233020e0fa00059a2606849a417e8540006e06aa0004c80007b01480000000000000000000380000000003d072a2460c406229c50400078a2d22407620007d27842f02423c261471a00000074c0005420008728fa1184240da1880000008589f80006c600000065200051a9ec60c0aa3200000000000008a805641208800034e0003f010400000093400000045c00000074208c0000008d20000000c83b4000a1442c0d47c29982b47280000000000000000005cc15e7163da05a0005384c20001be0000007ca5620000006cc0007063b039e0041f80000004488b01bc00040e9b41b40002483e87fe8d62283543f25400000007823145527cc9c614064c31e4b200000000080e1567aa1865762ec6a240461c00000089a67c288000000518
  | 10 => 0x7a8384ce2620000000000001a80009760009880100000000003fca0e30a56c00052c00072e0ae3fe8b20000000006b037000090000000018e00065a00000059000017600000000000000038400000069000093066a0007b80320ee00000000000088673800000018aa1c6f68d00007b20001622c68ca4fa0009da85e7ec01442a0000000000000002220000004fc3fa0009ee00089080487ca1a8705d00005fc9a05ee0007920002aa0004440a400023c00000032851000024e90a00043a0000989f491c5d49a886655c84c0000004cc58600000055003e00009a94a1300009ac00000020a0000004320000007d84165ca9c85b40640000009d014a07482040895203a84038a1220000001d08dc5346b453e0009fa5300007300007ba0cc3f42b200071800000000078e3a84e800000000000063a0000007e42a80000284de0000000d663209c0000000003ba4b86761b200000075045a00000000029a7769600f27c61ca3089866780802302584e482a3c459e0004940084c60000d000000070e21c4103b613e69600070080a0009087640fc00057a5bea2470c99c59212a00030600097800025097c0003520000005e60000002e60000001dc0de1fa7809d60000000000002ca00073a00036258c3ea8a400000056800000010a0002a674e6d830c0000000005980005fa0008a60006441c40000005dc0005ba52811000000000092c8464fe53222ea2600000066218000000067e0009b88a200000000000045075c23a2860000002448bc58e2644f462a00060a7588e85244282240003ae4a27f600027600094493c00004c00095c0006541d65466d276c0f04726a607e23207c5260008280008882e87b409681c45e2067ce7248340000002d655800000000089613a82400087860e4dc19200096a6ca21811e0901941ce7ae21e9b60000000000000f87860007365780004907744ac4640ca0008ba89c48e0009900000001709044a83a00789d80464885008c67e89ae84e0007f231c2723a47085c00001ae00000000050a1ec0000000001ac6f40000009c49a201847a1986ae7de92000091064e000a040000000008ea0000003c63040dc16a3cc80295e0000009320e019e0005fe6c80007208d48180000008d874633898244e1f402025613c4ea64014c86e8e40c00004d60007c80006100000000000000000002e400000000031a55e0007d02522983bc9f226e00000019a3680003f81d82de1a20003f62be5de9f00003d800048483a0000006925660008101780000009580003100009ca0bc33c1020001540000920009723be0003480001b87f8a220be3ce8fe92a5d839a62c00000011a8424788ae49a43600052e29e00000072c24a2040000000000005ec30e00028400029642632274a0006064560000000009400009ba9386743aa2d00
  | 11 => 0x71000000061676800010e9629a60006ee23653c5c20008de6ea05c0005a824c00000000051e0004d400000043c97400000046621a6a02da5081009ce5e092690e68c65668688e5e219c1aa94c0483183261506287d66e27da64a62e09408e646266196a1e0b431236c91e0fe23844206a00033a2a279e88c23e1c67b689800043030244637a5f48568f837c1de1609703324da8c85221ba1d291a28e0000001d40000000003c8000000000000000000000000000a180000000000007a4a000b64860000002ee498a200001289cc0000000b235600000082e00000000000073c5366722200000000007266e40005720000000000002740002b69dc0000000000005ce6ce76a98458a0540009d40ba3368c200081e00032e0583e097e1340004b676065e1e460200084400000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa8e861d5424c80151b0c3aa8499002e1a047550932005c2c08eaa126400b8a801d5424c801713003aa849900263a1c6550932004c6c38caa126400b8681195424c80170b0232a8499002e2a006550932005c4c00caa126400a8e861c5424c80161d0a38a8499002c36147150932005c5400e2a126400b89801c5424c80151d0db828499002c3a16705093200586c2ce0a126400b87815c1424c80170902b82849900263e1d42d8532006873aa8530a6400d0d7550a614c801b1285b82c299003625087058532004c7c3a843026400d0e75508604c801a1aeaa10c0990036150a7118132006c2a12e23026400e89424ca60d4401c52a4a12c1a880392549325835100744a1264b06a200c8e845ca639440191b08b94c72882313d457298e5104626a8ae531ca200a8d8298f429440151b0531a85288123360b764ca5100647bb284994a200c8d76509329440191d06b90c8a88032360d721915100546c10c9992a200a8d8219132544074990ca9264a8802a3a19424c9510054643284992a203a8c86509325040151b0531a842080323dd9424c8410070732a849908200e0d655093210401d1284994c020803a2509325804100546c14c89966200a8f8650932cc40791eeca12651880383995424ca3100706b2a849946200b158414d514c40168b0429aa298802d4600535453100546c26ec9944200a8f84595328840151b063b28490802a360f655092102c5643acaa124207aa88058d424840164b0a38a8490802e86007150921004d243a84a8a4200e85424ca61d4001c4aa4a12c3a800391549325875000742a1264b0ea00092d821d151d400191d06b94c9280032360d729925003e17a82e5324a007c2d505ca649400b15b05bb28528002a360a64cca5000546c14c8994a000a8f86509329400151b0ca12652800323a117218d5000646c22e431aa000a8d8218f425400151b0431a84a800e8b2195250950006473b284992a000c8c76509325400149b0431ea2a80024b608745455000526c10c6a8aa000a8d8298d42d000191eeca1265a000ea3e19424ca400070732a849948000e0d655093290001633062a2a0a0002ca608545414000598c08a8a828003c8c76509324c00751b06b128418002a360a644c83000547c32849906000e0e65509320c001c1acaa126418003a1509329843000742a1264b086000a8d83dd9428800151f06b2a8510002a3610764c92000546c26ca99240048cc87595324801158902b226490002d2614704c920005e0c08e099240009c8874c95048007948eca12428800f321d9324811000646ba2e6b102000a8d8298d420400151b053226408002a3e19424c81000546c32849902000c8f76509320400191aeca12640800383995424c81000706b2a849902000e31645455004001ca2c6a8aa008003985895154010
  | 1 => 0x1d862701f28800454d80008780008cc6024c1051a000b801343751a450a0a04a3c302c2f1981c380089420611d04894400889d4c084a2402c4e5003c009923068540341270da552e2013a5a100cce80b140643c6b0000000001b000000042000000037018b600000d00005169091862000011c592b19000243a8ac0013001cc760000140aea510a21060c00290009718000001b001607a87068549e4c29a788e7c0007cbe0000174fc00248000072148b8a29343000866f1a9a914890e1e87e8b19000f69500110e2771301c006700000d22f0020400961e0e4a8000a248c000001203a004f9f400002692c006c00194007929284d0003f88800000e020602040a5604000002420404000a0224000e0c0204000412042e020404062c0e006c080002381802061a1a1422020012020c1607c2d625d660d080131b05398caa1002c9604655494200594c00caa928408c4d625d661cc80751d0da9a849900263a1c5350932005c3408a6a126400b858114d424c8017150029a8499002e26005350932004c6c14e832a6400b4581195524c8016930032aa49900e63a1f545093200687baea8a126400a8e86151424c80170d022a28499002e16045450932005c5400a8a126400b8980151424c80171501bb28499002e26037650932005c340ceca126400b85819d9424c80161f0abb28499002c3215765093200687baceaa126400
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x1
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0xd09
  | 8 => 0xcca
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 64
  | 6 => 1514
  | 5 => 1300
  | 4 => 167
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (1811+((h/21+packedAt gbK7 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 6 => packedAt gbK6 (62570+((h/504+packedAt gbK6 (56018+(h % 504)*13) 13) % 4703)*12) 12
  | 5 => packedAt gbK5 (67596+((h/433+packedAt gbK5 (62400+(h % 433)*12) 12) % 2076)*12) 12
  | 4 => packedAt gbK4 (10293+((h/55+packedAt gbK4 (9853+(h % 55)*8) 8) % 221)*9) 9
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x71c0c70787f0fc3f8187fff83ff0c1134dc3cf
  | 1 => 0x7e00f807f87f0fc3fff8703fc1f10623b27d33
  | 2 => 0x8000fff8ff800ffc01ff803ffe0a083cc38e3c
  | 3 => 0xffff0000fffff00001ffffc0000c0fc0fc0fc0
  | 4 => 0xfffffffffe000000000ff000fff000
  | 5 => 0xffffffff0000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x205041410120140488009a0828c0c11104c045
  | 1 => 0x52228882081100414488209481210622101512
  | 2 => 0x80041230b2888aa811550123140a0804c30a28
  | 3 => 0x148e0010dcdaa22025e64581842c0a40f80f80
  | 4 => 0x80020e76ccf3238440602184e5000efe000
  | 5 => 0x6930e4c400000000400008042181a5bb000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfffffff8eeeceae8fffffff8eeeceae8fffffff8eeeceae8fffffff8eeeceae8fffffff8eeeceae8fffffff8eeeceae8fffffff8eeeceae8fffffff8eeeceae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_11920
namespace PEqualNP.Outside.L_meta_11920
open PEqualNP.Outside.L_meta_11920.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1 := bs5_4_0
theorem alls5 : ∀ k ≤ 4, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
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
theorem bgb_4_160 : Interval gbAtlas 4 160 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 167 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160)))
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
theorem bgb_5_1280 : Interval gbAtlas 5 1280 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1300 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))))))
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
theorem bgb_6_1504 : Interval gbAtlas 6 1504 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1514 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 64 := (concat bgb_7_0 bgb_7_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 32, 40),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 6 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 0 zero,inputs.getD 5 zero,inputs.getD 1 zero]
def fullWord : Sig := 0xffffffffeeeeeeeefffffff8eeeceae8ffffffffeeeeeeeefffffff8eeeceae8ffffffffeeeeeeeefffffff8eeeceae8ffffffffeeeeeeeefffffff8eeeceae8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
  have lift := lift_ok (u:=true) (ms:=fixRows 64 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 7 → Bool) := decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 7) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 7 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_11920.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[7,3]⟩,⟨.or,[5,6]⟩,⟨.and,[8,9]⟩,⟨.or,[1,2]⟩,⟨.or,[4,5]⟩,⟨.and,[11,12]⟩,⟨.or,[0,6]⟩,⟨.and,[14,4]⟩,⟨.or,[10,13]⟩,⟨.or,[16,15]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
    exact ⟨mono,17,monoShape,by change 11 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_11920

open PEqualNP.Outside.L_meta_11920 in
theorem PEqualNP.Outside.L_meta_11920 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
