import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_11924.Model
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


end PEqualNP.Outside.L_meta_11924.Model

namespace PEqualNP.Outside.L_meta_11924
open PEqualNP.Outside.L_meta_11924.Model
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

end PEqualNP.Outside.L_meta_11924

namespace PEqualNP.Outside.L_meta_11924
open PEqualNP.Outside.L_meta_11924.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffc3fe1fffc3c38703fff87e0fffe19f39f
  | 2 => 0xf07ffc3fff87fc03f803c3ff8fff03f213cf3
  | 3 => 0xff87ffc01ff87ffc0003fc3ff00ffc1c1cf1c
  | 4 => 0xf0007ffffe0007ffffffc003ffff0001fe0fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x11220491025000141812884501241518185185
  | 2 => 0xa291490a5084c54224841628c852a0a5212432
  | 3 => 0xc4555228d5244eea440926a2d20aca85c18e18
  | 4 => 0x6220808031108c89218003248c03084a0bc0
  | 5 => 0x8884433319c66733364e3b3040108c31b5f000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_11924
namespace PEqualNP.Outside.L_meta_11924
open PEqualNP.Outside.L_meta_11924.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3c3fffc7fc3fffe1c30e0fffc3f0ffff09f27f
  | 2 => 0xc03c3ff87fc7c3fe03f00f0ffc7f1e0f913d93
  | 3 => 0x3fc7ff8007fc3ffc000ff0ff801ff0e1ce1c
  | 4 => 0xffc007fffff8003ffffff000ffffe000fe0fe0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x440042204100008102421100908284085025
  | 2 => 0x928a94914a0a262a2290858a642a142a912492
  | 3 => 0xab11b5251a94a277648129a8e9065962e18e18
  | 4 => 0x8010200100088844824200092444040220b40
  | 5 => 0x3222243663273339b3c9cecc2008918cddf000
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xffffaaa0fafaaaa0ffffaaa0fafaaaa0ffffaaa0fafaaaa0ffffaaa0fafaaaa0ffffaaa0fafaaaa0ffffaaa0fafaaaa0ffffaaa0fafaaaa0ffffaaa0fafaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_11924
namespace PEqualNP.Outside.L_meta_11924
open PEqualNP.Outside.L_meta_11924.Model
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
  | 0 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 1 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x40118004220208008204820901304088105045
  | 1 => 0x52228891414810a0521244248449414612512
  | 3 => 0xaa444512412900354802489092092941828a28
  | 4 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_11924
namespace PEqualNP.Outside.L_meta_11924
open PEqualNP.Outside.L_meta_11924.Model
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
  | 0 => 0xf1e3c7fc78ffe3f18e3838fe38ff87f10f1cf
  | 1 => 0xfe03f9ff80e3fc7e0fc03f1fc0e3f8f633933
  | 2 => 0xf0003fe3fff03ff8ff0003fe3ff03ff083ce3c
  | 4 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x41404600421408400840908240830824105045
  | 1 => 0xa20c89489128540860a42910a424930a612912
  | 2 => 0x9110112400a0019100422409402440828228
  | 4 => 0x2404010a010004922229080032288102240d80
  | 5 => 0xc8d82250364d3924dcd273c90041066cdbf000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8ffffe8e8fafae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_11924
namespace PEqualNP.Outside.L_meta_11924
open PEqualNP.Outside.L_meta_11924.Model
def s4K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2003000004105f32dc6574cb6994d32
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x2350e32
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*4) 4
  | 3 => packedAt s4K3 (i*15) 15
  | 2 => packedAt s4K2 (i*26) 26
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (5+((h/1+packedAt s4K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s4K3 (79+((h/1+packedAt s4K3 (75+(h % 1)*4) 4) % 11)*4) 4
  | 2 => packedAt s4K2 (27+((h/1+packedAt s4K2 (26+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfdcf3e3f3e74cf
  | 1 => 0xfffffffffffffffffffffffdfef3cfc7cf9b33
  | 2 => 0xebf03f3f80fec3c
  | 3 => 0xf3ffc03fff00fc0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404104009020045
  | 1 => 0x208041042040112
  | 2 => 0x150aa0690a94c28
  | 3 => 0xe082ab24a14e80
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 15 s4Pos s4Neg, 0xeee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_11924
namespace PEqualNP.Outside.L_meta_11924
open PEqualNP.Outside.L_meta_11924.Model
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
  | 0 => 0xf3cfe3c7fc7e3f1f8c63c70fe3f0fc78474cf
  | 1 => 0xf03f1fc063f9fc7e3f07c780e3c7f1f99a4b33
  | 2 => 0xffc01fff83fe007fc7f807ff03f801fe638c3c
  | 3 => 0xffffe00003ffff8007fff80003fffe007c0fc0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1040200804004020000081020090040001045
  | 1 => 0x10888411049080c042024484484240a10a4112
  | 2 => 0x22024888090049200948012202902514208c28
  | 3 => 0x441241aa5225402495d4900a1324ac14740e80
  | 4 => 0x88a091304035924926a7264c9800c8215f6000
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xfefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_11924
namespace PEqualNP.Outside.L_meta_11924
open PEqualNP.Outside.L_meta_11924.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x110b1006802100000019831580219a0a81801789821c1208038c9e8f9e1b91841688859716011d8f1500001a988514801f1c9b0b8c001087800918000d20072086048e8d940e190a12829f80938000131d008a00140150214802003010c04288040200280007fd5001fe54005f95001fd54007f150017c54007fd4c01fe53007f54c01fc53007fd0c01fe43007f50c01fc43007fd48017f52007f94801fd52005f54801fc52007fd0801fe42007f50801fc42007fcc801df32007f8c801fd3200774c801fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd40017f50007f94001fd50005f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x224000df95120006f8a890002ff63480097f31a4000bf58d20025f8c6900037f5248001bea924000fb90920007da8490003df3248001f71924000f74c920007da6490003cd32480017fb0a4001bf18520007de4290003ed2148001bfa824000df54120007f48090003f94048007fd9024002fb88120015feca1001afe6508005bf32840009f99420005faca1000b7d65080013eb284002bf19420015fec810016fe6408005df3204000af99020005fac81000bbd64080015eb204002bf19020006fca8100037c54080057fb184004bf98c20017bcc610002de63080017eb184002f758c20005bac61000afc63080077f3104003dfd482001efaa41000fdf3208007ee9904001bf98420017ecc210002f661080017eb084002fd58420005eac21000afe6008005bfa804002df54020017de401000bfa2008005f69004003fe4802000dfecb8801afe65c40017eb2e2001bf1971000dfec988016fe64c40017eb262001bf19310006fca9880037c54c40037fb1e2004bf98f10005fac788006fc63c40037fb162003bf98b10005fac588006fc62c4001bfa962000df54b10007be6588003dd32c4003fb20e2000fd5071000fec6388003f531c4003fb10e2000fd48710006fea1880037d50c40057fb2c2006bf99610016fccb080027e65840017eb2c2002df59610004facb0800afc65840057fb242005bf99210005fac90800afc6484001bf2a42000df15210015fec708012fe63840017eb1c2002bf18e10015fec50800efe62840017eb142002bf18a10006fea5080037d5284001ef9942000f74ca10005fac30800afe6084005bfa842002df54210017f46108003f93084005fd1042000fe48210017ee2108007fb10840017fb2a2006bf99510005faca8801afc65440017fb222005bf99110005fac888016fc6444001bf2a22000df15110005fec688003df63440016fb1a2004bf98d10005fac688012fc6344001ee31a2000b718d10005fec48800efe62440017eb122003bf18910006fea4880037d5244001ef9922000f74c910007ec8288003f54144001fb18a2000fd4c510007ec4288003f52144001bfa822000df54110007f46088003f93044001fd1022000fe4811000ff6208800bf610440057fb282006bf99410016fcca080027e65040017eb282002df59410004faca0800afc65040057fb202005bf990100177cc808002be64040017eb202002ef590100057ac80800afc6404001bf2a02000df15010015fec608012fe6304005ef3182000b798c10005fac60800bdd63040016eb182002bf18c10015fec40800efe6204005f73102000bb98810005fac40800bed620400176b102002bf18810006fea4080037d5204001ef9902000f74c81000dfcc20800afe6004005bfa802002df54010017ee200800bfa1004005fa8802001fe44010
  | 1 => 0x37f5210001bea908000f7cc840007ba6420006fe6110005fb3088000bd98440005fac22000bf561100017ab088002bf98040016fea02000b7d5010005dfa008002fe900400177a8020017f940100097fb2e6006bf99730005facb98012fc65cc0097fb266005bf99330005fac998012fc64cc001bf2a66000df15330027bc8798003dd43cc0077f3166000bf58b30006fea5980037d52cc009ef9966000f74cb3000dfcc398002fd61cc009ef98e6000f74c730006fea1980037d50cc0057fb2c6006bf99630016fccb180027e658c0017eb2c6002df59630004facb1800afc658c0057fb246005bf99230005fac91800afc648c001bf2a46000df15230005fac71800efe628c0017eb146000dfd4a30006faa518003df328c001ee9946001bf98630005fac318003de318c001ee18c6002bf98230016fea11800b7d508c005ef9846004fecc230005feca9801afe654c0017eb2a6006bf19530005fec898016fe644c0017eb226005bf19130006fca8980037c544c001ef21a6000f750d30005fec49800efc624c001bfa926000df54930007be6498003dd324c0017fb0a6001bf18530007be6298003dd314c001bfa826000df54130027f6609800bde304c0057fb286006bf99430016fcca180027e650c0017eb286002df59430004faca1800afc650c0057fb206005bf990300177cc818002be640c0017eb206002ef590300057ac81800afc640c001bf2a06000df15030025fcc61800efe620c005f73106000bb98830005fac41800bed620c00176b106000dfd4830006faa418013df320c001ee9906001bf98430017ecc218002f6610c0017eb086002fd58430005eac218003de310c009ee1886002bf98030016fea01800b7d500c005ef9806002fe8c030017ba6018013f9300c0077fb2e4006bf9972001efccb900027e65c80017eb2e4003df59720004facb9000efc65c80077fb264005bf99320005fac99000efc64c8001bf2a64000df1532001dfec790012fe63c8007ef31e4000b798f20005fac79000fdd63c80016eb1e4003bf18f2001efea59000f7d52c8007f72164000fb50b2001fbe659000fee32c8007ee9964000fb4cb200079a6590006fe61c80017eb0e4003fbc8720007da43900037f50c8001bea864002bfd9620035fccb1000b7e65880013f32c4000bf59620016facb100027d65880057e32c4002bfd922002dfcc910002fd64880057e3244000df95220006f8a91000aff63880097f31c4000bf58e20015f8c710002fd6288001bfa944000df54a20007be6510003dd32880037f30c4000bf58620015fcc11000b7f5088005bea844002fe90220007f2811000bef2088007fd9044000bfd9520035fcca900037e65480013f32a4000bf59520006faca900027d654800d7e32a4000bfd912002dfcc890002fd644800b7e3
  | 2 => 0x50025fcc728002fd63940077f314a000bf58a50006fea5280037d5294001ef994a000f74ca5000dfcc328002fd61940057f304a002dfd4250037f6a128002ff645400b7e322a000dfd5150006fca8a80037d5454001be2a2a000bfd8d50025f8c6a80037f5354001bf29aa000df54d50006f8a6a8002ff62540077e312a000dfd4950006fca4a80037d5254001be292a000f7cc950007ba64a8002ff61540037e30aa000dfd4550006fca2a80037d5154001be28aa006fed4150016fca0a80037f6454001bf322a000df59150006f8c8a80167c6454001bfb1aa000df98d50006fac6a80037c6354001bfa1aa000df90d50006fa86a80037c4354001bfb12a0009fd8950006fcc4a80037d6254001be312a000dfd0950006fc84a80037d4254001be212a000dfcc950006be64a80037e3254001be992a000d74c950006f864a80037f6154001bf30aa000df58550006f8c2a80037f4154001bf20aa000df50550006f882a80037f3154001bf18aa000df4c550006f862a80037f2154001bf10aa000df48550006f842a80037f6054001bdb02a006bf99450004fcca28016fe64140017eb20a000df95050036f8a828012fe63140017eb18a003bf98850005fac42801b7f5214001bea90a000f7cc850007ba6428006fe61140017eb08a002bf98050016fea02800bfa5014005bea80a006fe5405002dfecba00177f65d000b3fb2e8006bf99740005facba0016fc65d000bbe32e80059f1974002efca9a00177c54d00097f31e8000bf58f4002f7e87a0003bd43d00077f3168000bf58b40006fea5a00037d52d000bdfa168000ef50b40007be65a0003dd32d00037f30e8000bf5874002f7e83a0003bd41d0001bfa868000df54340015fecb2001afe6590005bf32c80009f99640005facb2000b7d65900013eb2c8002bf19640005fac9200177e549000bbe2a48004bf98e40005fac72000efe62900017eb148000dfd4a40006faa520003df3290001ee9948001bf98640005fac32000afe6090005bfa848002fe94240016faa120003f95090001bca848002efd024002ff68120002ff6550001bfb2a80009fd9540035fccaa0002fd655000d7e32a8000df19540004f8caa00177e545000bbe2a28000bfd8d40025f8c6a0003bf4350001dea1a8000bfd894001df8c4a00037f5250001bea928000efd09400077a84a0003df3250001ee9928000bfd854000df8c2a0003bf4150001dea0a8000dfd4140007f4a0a00037d5050001fca828000de5414002ff680a000bbe40500057fb288006bf99440016fcca200027e65100017eb288002df59440004faca2000afc651000b7f3208005df9504002ef8a820012fe6310005ef3188000b798c40005fac62000bdd63100016eb188003bf98840017dcc420002ee62100017eb108002fb58840005dac42000
  | 3 => 0xeb106201fb58831005dac4188037f520c401bea906204f7cc831007ba6418806fe610c403fb2086200fd5043100fbe6218807f6310c403ee9886204fd4c431015fcc018807fa600c4017d3006200bf5803100ff2c018802f9600c4077fb2e4206bf9972101efccb908027e65c84017eb2e4203df59721004facb9080efc65c84077fb264205bf99321005fac99080efc64c8401bf2a64200df1532101dfec790812fe63c8407ef31e4200b798f21005fac79080fdd63c84016eb1e4203bf18f2101efea59080f7d52c8407ef9964203fb8cb2101fba6590803ed32c8401e69964202bf98321005fac190806ff658840d7f32c4200bf5962100df8cb10806ff648840b7f3244200bf5922100df8c9108037e5488401be2a44201bfd8e21025fcc710802fd63884037e31c4200bf58a21006fea5108037d5288401ef9944200f74ca2100dfcc310807f64188401faa0c4201fbc862101fee431080afe60884017eb044200bfd9521035fcca90802fd654840d7e32a4200bfd912102dfcc890802fd644840b7e3224200df95121006f8a890802ff63484097f31a4200bf58d21025f8c6908037f5248401bea924200f7cc921007dc6490803dd3248401f69924200f34c921007ec8290803f54148407fb90a4201fb88521005fec09080afc60484037fb284206bf9942100efcca108027e65084017eb284201df59421004faca10806fc65084037fb204205bf9902100f7cc810802be64084017eb204201ef590210057ac810806fc6408401bf2a04200df1502100dfec610812fe6308403ef3184200b798c21005fac610807dd63084016eb184201bf18c2101dfcc41080f7f5208407bea904203f7cc82101fba6410806fe6108403f79084201fd8842100fda421080ff521084057f3004201fe98021005f4c010802fd6008403fcb004200be5802102dfcc9a8002fd64d400dbfaa6a000df95350006faa9a801b7c54d40097f31ea000bf58f50036fea7a80037e53d4001bea9ea006df14f5001dfcc5a8002fd62d400dbfa96a000df94b50006faa5a801b7c52d4001ef996a000f74cb5000dfcc3a8002fd61d400dbfa8ea000df94750006faa3a801b7c51d400dbfb26a000df9935002cfcc9a80037d64d400dbe326a006dfd8f50006fcc7a80037d63d400dbe31ea000dfd0f50006fc87a80037d43d4001be21ea006dfd8b50006fcc5a80037d62d40013eb16a006df18b50006fe85a80037e42d4001bea16a000df10b50006fe65a80035f32d4001bf196a000df4cb50006ba65a80037c32d400dbfb0ea000df98750006fac3a801b7c61d4001bfa0ea000df90750006fa83a80037c41d4001bf98ea000df8c750006fa63a80037c31d4001bf90ea000df88750006fa43a80037c21d40017eb2ca0009f5965002dfcc928002fd6494001bf2a4a000df152
  | 4 => 0x8037d5254401ef992a200f74c951037eea2a88077e51544017fb02a202bf18151035fcca28816fe64144017eb20a200df95051036f8a828812fe63144017eb18a203bf98851005fac42881b7f5214401bea90a200f7cc851007ba6428806fe6114403bfa88a201fd9445100efaa22881bf551144057f300a200bf5805102dfecba081afe65d04017eb2e8205bf197410077ea9a08177e54d040bbe2a68205ef1534102e78a9a0812fe63d040bef31e8200b798f41005fac7a0817dd63d04016eb1e8205efd0f410077a87a080efe62d04017eb168200dfd4b41006faa5a0817bf42d0401dea168200f7ccb41007ba65a080afe60d04017eb068201bfd9641035fccb208077e65904013f32c8200bf5964100efacb208027d65904037e32c8200bf5924102efca9208177c54904097f31c8200bf58e4101dfcc520802fd6290401bfa948200df54a41007be6520803dd32904037f30c8201fd94641007eaa320807bf419040bfba0c8202bf98241005fac120802ff6550401bfb2a82009fd9541035fccaa0802fd655040d7e32a8200df19541004f8caa0803bf545040bbf2a28205df1514100778a8a08033c54504017fb1a8204bf18d410077e86a0803bd43504017fb128203bf18941006fea4a08037d5250401dfa128200ef50941007be64a0803dd3250401fb28a8200fd5454102fee82a0807be41504017fb028202bf1814100dfeca2081afe65104017eb288201bf1944102dfcc8208177e541040bbe2a08204bf98c41005fac62080efe62104017eb108200dfd4841006faa420803df3210401ee9908201bf9844100f7e8220807f64110403dea088205fd50441015fcc020802fd60104097fb2e6206bf99731005facb98812fc65cc4097fb266205bf99331005fac998812fc64cc401bf2a66200df1533101dfcc598802fd62cc401bfa966200df54b31027be6598803dd32cc401fb20e6200fd50731015fcc198802fd60cc4037fb2c6206bf99631005facb18806fc658c4037fb246205bf99231005fac918806fc648c401bf2a46200df15231005fac718803de438c401eea1c6203bf98a31005fac5188037f528c401bea946200f7cca31007ba6518806fe618c403ef98c6204fdcc631015fcc118802fd608c4017fb2a6206bf99531005faca9881afc654c4017fb226205bf99131005fac898816fc644c401bf2a26200df15131005fec49880efc624c401bfa926200df54931007be6498803dd324c409fb98a6201f78c531005fec09880afc604c4037fb286206bf9943100efcca188027e650c4017eb286201df59431004faca18806fc650c4037fb206205bf9903100f7cc818802be640c4017eb206201ef590310057ac818806fc640c401bf2a06200df15031025fcc618813de430c401eea186203bf9883100fdcc418802ee620c4017
  | 5 => 0x4f32027bca799003dd53cc809ee29e6400f7d0f32027bc8799003dd43cc809ee21e6400dfd4b32006faa599006fe61cc8017eb0e6402bf98332005fac199013df65cc801ef32e6400f759732027b8cb99013df64cc801ef3266400f759332027b8c999003df54cc801ef2a66400d795332007baa999003dc54cc801ae2a66400f7d4b32006bea59900fde52cc801eea966400d754b3201fb8a599003df42cc807ef2166400f750b3201fb88599013df61cc801ef30e6400f758732027b8c399013df60cc801ef3066400f758332027b8c19900eff658c80d7f32c6403df99632004fccb19002fd658c807beb2c64009f5963201df8cb1900eff648c80b7f3246400bf5923201df8c9190037e548c801be2a46400bf58e32005bac71900efe628c807bfa946403fb94a3201efaa519003ed528c801b6a946400fbd0a3201fd8851900fdf328c809f79946401bf98632005fac31900afe608c8017eb046400bfd9532035fcca99002fd654c80d7e32a6400bfd913202dfcc899002fd644c80b7e3226400df95132006f8a899003df534c801ef29a6400f754d32007b8a699003df434c801ef21a6400f750d32007b886990037f524c801f72926400df54932007daa4990036d524c801f7a126400fb10932027de649900fde324c8017fb0a6401bf18532005fec09900afc604c801efb2a6400f799532007baca99003dc654c801efb226400f799132007bac899003dc644c801efaa26400f795132006bca899003dd544c801ee2a26400d715132007bec499003cf624c801efa926400d7d493201fbca499003ce524c801eea926400d7549320079aa4990034d524c807ee2926400f7d09320079e849900fde424c801eea126403f710932007988499003df614c801ef30a6400f758532007b8c299003df604c801ef3026400f758132007b8c09900eff650c80d7f3286403df99432004fcca19002fd650c807beb2864009f5943201df8ca1900eff640c80b7f3206400bf5903201df8c8190037e540c801be2a06404bf98c32005bcc61900efe620c807bfa906403df5483201fbe641900fee320c807ee9906404fb4c83200dfcc219002fd610c8057f3006400bf5803202dfcc9a8802fd64d4401bf2a6a206df15351025fcc7a8802fd63d440dbfa9ea200df54f5101dfcc5a8802fd62d440dbfa96a200df54b51007be65a8803dd32d44057f306a200bf58351005facb28816fe6494403df324a200af99251005fac928807bd64944015eb24a200df95251006f8a928812fe63944017eb1ca203bf98a51005fac5288037f5294401bea94a200f7cca51007ba6528806fe6194403bfa8ca206fdd4651015fcc128802fd60944017fb22a205bf19151006fca8a88037c54544017fb1aa204bf18d51006fea6a88037d53544017fb12a203bf18951006fea4a8
  | 6 => 0x17eb06a406dfd9352006fcc9a90167e64d4801beb26a406df19352036fec7a90037e63d4801beb1ea406df18f52006fe87a90037e43d4801bea1ea400df10f52036fec3a90037e61d4801beb0ea406df18752036fec1a90037e60d4801beb06a4009f58352036f8c1a9002fd65948013eb2ca405bf99252005fac9290037e5494801be2a4a404bf98e5201fbcc729002de63948017eb1ca403f758e52005bac72900efe6294807bfa94a406fbd4a5200dfcc329002fd61948057f304a400bf58252005fec8a9016fc6454801bfaa2a400df95152006faa8a90037c54548017fb1aa404bf18d52006fea6a90037e5354801bea9aa400df14d52037dea4a900f7e52548017fb0aa401bf18552005fec0a900afc6054801bfb22a400df99152006fac8a90037c645480b3e322a400dfd8d52006fcc6a90037d6354801be31aa400dfd0d52006fc86a90037d4354801be21aa400dfd8952006dec4a90037f6154801bf30aa400df58552006f8c2a90037f60548013fb02a400df98152006fac0a90037c605480d7f328a4009f9945202dfcc829002fd6414801bf2a0a406df15052025fcc62900fde63148016f318a400bf58c5201fbac629002dd63148077f310a403dfd485201fdca42900f7d521480df6a90a401bf98452005fac22900afe60148017eb00a405bfd974202efecba10167f65d080d7f32e8400bf5974202df8cba10177c65d080b3e32e8405df9534202ef8a9a1012fe63d08017eb1e8400dfd4b42006faa5a1006fe61d08017eb0e8402bf98342005fac1a100eff659080d7f32c8403df99642004fccb21002fd6590807beb2c84009f5964201df8cb21002fd649080bbf2a48405df15242025fcc72100fde63908016f31c8400bf58e4201fbac721002dd63908077f3148403dfd4a4201fdca52100f7d5290801f6a948400db54a4201f7e8521017ef42908037f30c8400bf58642015fcc121002fd60908017fb2a8400dfd9542004fecaa101afe65508017eb2a8406bf19542006f8caa10027c655080bbf2a28405df15142005fec6a1012fc6350801bfa928400fb94942006faa4a1003ed5250801b6a928405fbd094201f7c84a1002ff61508037e30a8400bfd8142015f8c0a100eff651080d7f3288403df99442004fcca21002fd6510807beb2884009f5944201df8ca21016fe641080bbf2a08405df15042025fcc62100fde63108016f3188400bf58c4201fbac621002dd63108077f3108403dfd484201efaa42100fbf4210807f72108403ef5084202fda8421006fe6110807fb3088400bd98442005fac22100ff561108017ab088402bf9804201ff4c021002fa60108017eb008403fe58042005f2c021012ff65cc80d7f32e6400bf59732025f8cb99012ff64cc80b7f3266400bf59332025f8c9990037e54cc801be2a66400f7d
  | 7 => 0xaa0177e54550017fb1aa804bf18d54005fec4aa00efc62550017fb0aa801bf18554005fec0aa00afc605500d7f328a805bf9905402efea82a017be541500bbeaa0a806ef55054025fcc62a017de63150016f318a800bf58c5402fbac62a002dd63150077f310a805fb98854005dcc42a002fd621500bf6b10a800bb5885400dfcc22a017f661150017b308a800bf5845402feac22a002f561150057f300a805fe98054005f4c02a002fd601500bfcb00a800be5805402efcc82a0167e641500b9f320a805dfd8c5402efcc62a0175e631500bbeb18a805d758c5402ef8c62a0177f621500bbf310a805db9885402efac42a0027d621500bb6b10a8009b5885402ef8c42a0177f611500bbf308a805dd9845402efac22a01775611500bbe308a805dfd805402efcc02a0177a601500bbeb00a8009f5805402ef2c02a00279601500bbe300a805bf99353005fac9a98037e54d4c0dbe2a6a603bf98b53005fac5a9806fe61d4c017eb0ea602bf98353005fac1a9802fd6594c0b7f324a600bf59253006fca9298037c5494c097f31ca604dfd4e53037bea72980efe6294c017eb14a601bf98653005fac32980afe6094c017eb04a600bfd915302df8c8a98037e5454c01be2a2a606f7d4d53026fca6a9802ff6254c077e312a600bfd855300df8c2a9802ff6054c057e302a606bf9945302dfcc829802fd6414c01bf2a0a606df15053025fcc6298137f5314c09ef298a604df54c53037baa62980efe6214c09f7310a600bb98853005fac429813ed6214c0176b10a601bf98453005fac22980afe6014c017eb00a605bfd9743035fccba1802fd65d0c0b7e32e8605df9534302ef8a9a180efe62d0c017eb168601bf9874302fecc3a1802f661d0c017eb0e8605fd58743005eac3a180afe60d0c017eb068604bfd9643035fccb218137e6590c013f32c8600bf59643026facb218027d6590c097e32c8600bf5924302efca9218177c5490c097f31c8604f794e43007baa721813bf4390c0befa1c8603bf98a43027dcc521802ee6290c017eb148604fb58a43005dac521806fe6190c017eb0c8602bf98243005fac121802ff6550c01bfb2a86009fd9543035fccaa1802fd6550c0d7e32a8600df19543004f8caa18177e5450c0bbe2a28600f794d43007baa6a1817df4350c09df21a8600bfd894301df8c4a1802ff6150c037e30a8600bfd8143015f8c0a1812ff6510c0d7f3288600bf59443025f8ca21816fe6410c0bbf2a08605df15043025fcc621813bf4310c09ef2188604ef50c4302fba862180efe6210c017eb108601bf98443005fac22180afe6010c017eb008605bf99352005fac9a901b7f54d4801bf2a6a400df55352036f8a9a9012fe63d48017eb1ea406dfd4f52006fca7a90037d53d480dbe29ea401bf98752005fac3a900afe60d480
  | 8 => 0x100200500100500700300100100700300000000000500200000100200100000100000100400000300000000000100400200500000b00000100000100000000500100200000000100500600100400400000200200100100000000300300101601100400200300000000000200900200300000200000400100000300100100000000000300000000200300300200300600000000000300600200000000000200100000000100200000000000b00000000300100400000000000000000000000100d00000200301200400200000000700000000200000000100300100200000100000600000600100100200200000900000500100300500300500000100100000900200300100000300000300500100200b00000300000000100700200000200000000500100000400100200100100000100300000200300200001300000300000000200000200200300300000000000000400c00000200200400100000000000000300100000100200001100100400000000000100600000100000200501500000100500000200000000000000100200100000100300000000200000100000000000000100400100500100000700000100500100000000100a00000100400a00200200000000701100000500000000b00000100000100200000200400000300600000000000700200100000200200000000200100400100000000000400000000400100000300100000200000300200000000100000500200000000000100500900000000300300000300700000000300000000000000100300000700400000000600900100000300000d00400000100100000300000000000100100000100500e00000200000600000100000100000100200300200700000000200400300900200100000000600100200600200400100100000300100400000000700200300000000200600100200400000000100000e00000200600100600b00000000000300000100700300000100400200000100300100c00100000000300000500000000000000800300000000100100000000300000000200200900000400200200000000100000000e005000004003002005000000002004005000002000003001009000003001001012000008000001002005000003000005008000006004003000001001000025fcc7aa002fd63d50077f316a800bf58b5400dfcc3aa002fd61d50057f306a800bf58354005facb2a016fe649500bbfaa4a806efd52540067ea92a012fe63950017eb1ca803bf98a54005fac52a006fe61950017eb0ca802bf98254005fac12a0167e649500bbfb1ca805df98e5402efac72a0177c639500bbfb14a805df98a5402efac52a0027d629500bbe314a805dfd865402efcc32a0177d619500bbe30ca805dfd825402efcc12a0177d60950013eb04a805df182540377ea8
  | 9 => 0x2de3166d4000aba0006e6000d123200000000000000000000009b650838e000a8c00056e00085011cd5c75200024e602000d64406016b840b88a8410000000000000000d0e0cc000000000000a1a0000008b226a0006500008a40000000186b2ac80004f00bc7a698ad22110094be41ba000000000000000000000bc000000000068a000b8cc68000000266d52000000552000b1807cc82b40000000006000000cf0000000dbc41a78ab4800000000000000000000000037e000cf200098c0000000009c21b8b10ab4778000b2468c000bcc5680008921d650a0000005c80000000c4584000000544000d6c2f25f2bd800000028600000000000087eb7200000016ca24e040006c87f243cbde000a225d6df85020007c8a8ed7c00059e7440000000002ee34a00000000000000000000000000000000042000077e000000000000000000000000000000000e26000aa20002ac7e0abc808000000000000000956000d7e0005ae0000000000001a4000844000000126062be2000000706ba48946ea4fea101bebbc9ac0002445e4000000000000a84000000aa60000000a27d6000ac2000ba200000000000099a00072c7885feb9cc08bb46bcb9665e88aa940000001d0ad47aa000cbc00084a0000b21860000000000000000004343f2000000a6e68e00023a1b6000000000c3e82a000c6000000000061a000830000cd40000000000000000000000000000000000005a40000007f000094e000c66028000000000000000724000000da6000bb044200045a00000000000000033c000000000000000000000000e0600000099000003a000c7a0003c4af400081a0000000000000009989a600000000044000000000000056a3ce80689e83200000021400000039c1c000000000040e00046e5cc7a8000000df275400019600000000000000000000000000000049e756156000228348000000a02c940000008de102000000dc84820000006dc000000000000958000000baaa4cd4c0000003b88a646a000c86000000c32a7e012000c02878de606477200000000013a9340000fe00015abc807e000000000000000000000a928e659a000dc0000000e1a000b1e358000000000ca80d000000000000000027a0001360be00083e0000000001ccb4e4380b4000258000000000000000dea1280000c6c0a0003ae4a0d9a82e3840000000380000009ce0000000000001bc8c200000071000055e1e0daa000904a2800c000c2a656d4095000000079a0006de4d00000000000001800000000000007ec00093a0000005faa700000000000008420000000000ae21e5b200700000200000100000000100000000100100200300700800300400000500000000100000300100000000100000000b00100200100500000200000500400000a001003004000
  | 10 => 0x20000008020005b60007ce08092aa1c7f84123f0000000000000000000c50000000000780000000150000000000000aaaa486280000000000006fa000198a7c330000982af0b220008f20000000000000009100000001de1aa000000000000bee6d8be81fa3e0a4200027c00000085a0000000e630a8968409f200071ea1462a0005620000007dc000b365a00000001241ee2020000000000000000000000000006600000000001fe184968d040007ee00000000000056451868600000022400070e000000000a160006e000000000000000093c0006a69e64d2000000290ac40001e4c240008c679c000862e24992000834d6e15e374b860009a40000000000000002fc56600000000042400053400010a000000000000000408d34000dce000ae00009ca00840c9e83f43446ca000000000d941162ce032aa82c03a60000000006706f800e000278000000dfa0000000000007145c2868000a8a000000000000b6a000000bce000000d2000030200000094891217000000029a03e8fe000000308a3a00075a7b200018800000000000000062c3a800025ad8c8b8798000000000000b0058c0002a6000000000000000dfe4f80004640000000000003fcada6ba8740001e2000000000000402242014000000a9a92c3765f632a000ba60006b000000053a000054000000a80000000000a1e000b3a08625609c0000000000000000000000000000007a4000000000804000ba0000c9e000d489aa7fa38a974000000db260a98e0002041442d840a000000da820600000013e96c0000000006a202a0001662cc0001940000002c400092e3501629c4bd2942000a18226000902000000b88000594000000000a0c01ab6885e486db6000000000450000b5a00012a000000996000000000c84b4c0007827eabecd1097e02e000000866618000000000bf21c4cc829e9b40e2000000000a0a000000000294000000000908026c1a6f672e1ac0005fc000976000000ad800003614cb040003380002400006ce000d4e000000580000084000b7404e2e41ec8ee7de0000000000008ac000000122000296d0a000d14000a4a67a070390a060000009b83ca000000994c70000b085e2000e0c54c8282e0368c3a2602da61611e000000000000000000b5c00000000000000017e3ac37a00004649a0005426d216400000004a10012c6c4c4c022520d9c5ac9e000000000000090073e0000909dc000000b3200080a000e22000000492546d68b60000282000000218000000000000000000ddc000d08a5c00000094000000000000000096e3700000005c60006460000001f0000c5e00010600057a0a8b1200000000008a0004e400070c1a20006da97050e000570000b6c0000004c601e0000002be000000000068cc23c200000000081800000097a9fc0000000000
  | 11 => 0x2d4052000a30c8c5323d60005d85ce0000000002dc000000000c060000000000007e80000000000000000000000000003224f20000000000000000000002e80000c0d9ec54000000000a6416ad0600000006029c0008f87b0000000000d420009d41b4000000d02000000000000c8e796592000caa00000000000000000000069600000000086c00081200044e000000da04b4000b4a5220a0d28212ce60003fe506e1234e0b0dcc380b2c5e60a475872a000652000314000cdc00000000000000000000000000000000000000000000000000000095c3a20009ea000b54b2000097265c00000000075e71a000000d56000000000000c000000000000000002624185365d4cf4764d3ebba3e828a356b46530a2a13831abf4b26ab80fc9b2ca274a99cd5a000b9ecae6a0810c64a34aec1544e8000000000000c5cd9624c42c22cace10ec1c252c9a000000000000a78d36000a0400070830ca627b4000000000b3042ab168e000000000031e00006e0000000d40006a40008e2000ceedd600000000000019a0000009aece0690000d38aac2384a84581d898000000061c3260002ea000000b1cdbe00025c876000000000000000890000c900003d02805d224814e430848608af80000009d07348f0000000500000382000de4c926264aa35ccc6000ab2000000000000a7200023c2f04d4000d740f458a7be76eda454063a0009880000000000000000002bc000000556000a9800079e0000000006e4004c18386000c4a000e0e2760000dcdb400047ecd074c4669601d21aed3c0000001dc4485b8b027c4b64ccc880000cb25988ce00086a4beae4000c143000000000000000000000000002b017c8bc9d80007bc0000000000000000000001d4000bb206c5ca0000002687403720006aa4b69a00005281f20000ce8547224527a00007860000000008d2000000108000000000000134000000000000000000dd80000002a288e582a580003666c033a23455c5867326420000000000000006ae70452c00000000000036400060e000a820000000000000000000000007c253e000272000000000000a6a35a7ac4005ea3b2514676c5225ecfe000c9c3960000007cc8729d60006ac000cc0df4000000000000000692000000afc0002163600000004f6cceb7c000d6200089ab584f40006f40000006040000000000005ee6000000009f0000000000726000b42cd80000000000000005be000000000bd4494000b387ba00057e0009bad6a0000000000000000000000000003a0000836cb4000000000000a5278c2ba7e4ad26a819010c2b40000004c022e00000000024aae2b94000000000ae60000000003c600000000000073c000000000000498bac29290ab1415273086481c4e0d88000b0c81e6481b200067c00017404200000000000000000046
  | 12 => 0x3e4ba91a00000000070a00000000080e000678000dac00000036c000bc200090e77634ca36b82a6839a8526386349e436a5ba0768aa15c0000b60007423cc00028c000000a7ad8e00000026c0000000000004bc000000000668000b92000000ba8000db06447d800082c072178000000000000000df00000000000000000000001604e22c2610856000b060003dc0000f8388000de8000da2000b280000000000005ec0823b09cc9fa000c04550c308f6000e00dec00000064c000000000000000000000000000c76a3c4fc000000000000000000000aea2ca00000038ce16548000000000000c4e2f40000003420000006060000000000000000000000000004ca0e4d4a3066f25e8698928914000000000000cec1f4ac0b762e60000009fe41600005cd5e01063cccad18596c8a8825c0cc466cc289f449662e7740003f857c0006b8000a0867400000000000006a7680009bc0000000000004cc00000048c00000000032e930554000d0000000000000065a1c63e40002f800000093e3c03320009840ead24d840000001f800000000089c00030e000de00000000ba8d800049008e000000654000000254000b90c489e200000000000000000096a0000000007d20f20000409f65a278ecba00071200032c0000000000000004c466e6627ae35491ca260000000003b452600080c000000d923e6d3a340bd0000932bfc794bae000000000cfcbd62d29367ca000c3c694cde000a9e88885846091e924bdc1e60000006d00000000000007c08c8c2005643ea50000e1c640000c5a5bc0000007280001203ea69c4b8000b1a000000000bdad5800000067200085ce200001b0168718d80920000000000000000624be05b40000003b6cbe0005deb9879000084eaee0ecb8a51ec340000002e2000770dfc7666fc42202c1f6000dde000938a3820adc23aaa8805e8d626449cd4620c44a91600000000076a2aa01c73816e000c7e684b9ad76000dd42a00000003e2000ca6c100000000000000000006300000008ea0000005b005a0000000000003c80acbb8158b2e2d60585c4454000dc64b2658b3e00004c48e8b0000946000d7800000000000073a0000000000000000000009220000000009c812e000000ce20008ba3a400083c9d237c0000502080d6d542ec0003ba4fa8140000008ae000d4488c00027e63e03cd7a000846a2e000000a56000000000000000000000a000000000000000000004327000000003466c268286082200000074e2c688400039e57800000045e0000008be0002b20008d000000000000000000047aa9647c18c0006e21c8000000000000000aca8c40004dc680c6ebe6d1aade3bedbac0c9ec2708a0978cac1826ee4260e87b8ca48e4af29a8cb8792d8a2fe000a601ca00051c078000e020000000001120003ee328c2c
  | 13 => 0xa000484d5000000000000000000066ad16c4448a6b6c22dda000000000398dae0000000000008fc00008822a0000005f876200000000095a000000000000000000000b7acd697cd2a71cdc4000000000d90cea5380009be0001da4da0004a47fec7c33418e0000300004e6000000000000000b560000000008b608c800000000b520000000007f63bc0aa816c0ec740002220000000000000005a895209ad706d67d0000aae000000bca5a6e1e034000d0c4707848fa0000009c6000000074664bf646c0007500006fe000000af6a12298c4083a7e6ad000054aca0000092000000acc5dabfa0004a60dacb0000000000000000bea04800051a0001ce0008243d21e818a84c8a25880006144881927a2c80e0ac1e000a328ca3da14a000a5400000000009652ebf86ec000bfec8807ac127608ecb7869abf000000000054e4d80000001a6000000000000000d2600000000000000036267e2841c264e0000000000000d2c42c36b2a636000c6a0000004ea0001760c20008b46c65740000001304c200026e69e000000000d86000000000de291850c000000abec720004c8a408d4a6600000009800017a94c0005d0000000000000b0a0ca172000000000632d2e2b8132000b7e59045c000572d600000000003de55a9649da9b00000ee0e000000095e7b636e0000004460000000000000d8000000000000000000c5852ab0e39400010494a000000000002d72000000000c62d9883841c7da58e0a6000000000a2c9a2504000000000000cfa736b8000099e000000000000000000000114000bbe6e8a6c19c0008e8000b8e6bedca318a440003520008f4a5e0000000007469f864a2c80000dedb8146b62dd2cda474b6e42e19eab63d8b5e3100444ac31c14089800a82061ee08232688a0e954312020d1e0006f0000000000000000000000000000000a764ee00000086edd0620000000000000b660002b6000ad62302a4000000000000a46a5a2364aebb6afe3365f0d2c2884de000000000afa0000000003789444780002466b411a0000000c89ee000000444000428000000512c6cb3428edf60009c0000000b5000000020000087a5aad82986b44ac68c05f41480004b00000000008702ae0000002f6666000558142000c161a8ab0e10cf80000000000004ce9667209de48096292600000000000000000000060c44c000cb65dc000d30000000000c38000000b70cd20005101ea59caa409e8cc46800077c1fc524a200000000000000000000003f60000000005760fa000000000d6690c00000000013c000ce80004ec7e20004560000000001a087c000000000000000000000000000000000000000000000a4ec56210000274000000ce400000053c7fcc460007d40004a2000e18000d1c1180000660004760000000000000006120242505163
  | 14 => 0x4142fa7f400000000021a35e75c5607024040000000000000000000000000000000006cc8863ec0f6000000000b3c000906000000000000000a9cc2e0000000002a800076cae821c000220716000c96000000000a90000adc0000000000000000f0d3241e000000000000000000e147c6c98c26000000000000000324dee5e0aa03044d6bc620e43a77a2d08da000000000000000000c78436000000bc48dca74000000000a3ecf6a8600000000023e0000000000003d456c0000000000004727480008266220003923f
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf7654a100047d7654a100065e65cca100065d65cca100065e654ca100065d654ca1001ece624ca10006cd624ca100074d524ca10007c93248210004df7359510024dc73595100347e75d91100047d75d91100047f75591100347c7559110004df7359110024dc7359110004ef725911001cec72591100056d7215110005797015110024de76d8d100065e54d8d100065c54d8d10004dd72d8d10004de7618d10005cd7218d100265e7518d100265d7518d100269e7418d100269d7418d100065e5418d100065c5418d10026ce7218d10004dd7218d10026cd7218d10004cd7218d10026d57118d10026d97018d10004df7358910024dc73589100065f63d49100065c63d49100065f63549100065c63549100066f625491001e6c6254910004de76cc910024dc76cc910004de764c910004dc764c91001ece624c910006cd624c9100074d524c910006d46390510014f47650510007345450510006d46350510015f07050510026d4638c510014f4764c510014f47648510007c532485100065f63d41100065c63d41100065f63541100065c6354110017701054110026d8638c110007d2318c11000cf8764c110007d1314c11000cf87648110007c93248110007e1214811002c7e74994100047d729941002c7c74594100047f72594100147f70594100147d705941002e3f759901002e3c75990100163f50990100163d50990100047f75590100347c75590100063f75590100063c75590100163f50590100163d5059010016b71059010016b5105901002c7f76950100047d769501002e3e64950100063d649501002c7f76150100047d761501002e3e64150100063d64150100056d72150100057970150100065e5498c100065c5498c10004dd7298c100165f5098c100165d5098c100065e5458c100065c5458c10004df7258c100165f5058c100165d5058c10016d71058c10016da1058c10016d51058c1000ed91058c1001e6e759881001e6d75988100066e54988100066c549881001ece739881001ecd73988100166f50988100166d50988100066e75588100066d75588100066e54588100066c5458810006ce7358810006cd73588100166f50588100166d5058810016e71058810016ea1058810016e5105881000ee910588100347f76d48100047d76d48100063e64d48100063d64d48100065e63d48100065d63d481001e6e62d48100066d62d48100047f76548100047d76548100063e64548100063d64548100065e63548100065d635481001e6e62548100066d6254810024df76cc810004dd76cc8100065e65cc8100065d65cc8100069e64cc8100069d64cc81001ece62cc810006cd62cc810004df764c810004dd764c8100065e654c8100065d654c8100069e644c8100069d644c81001ece624c810006cd624c8100074d524c810
  | 1 => 0x95200067b70595200347e75d91200047d75d91200047f75591200347c755912002c7f76951200047d76951200056d729512000579709512002c7f76151200047d76151200063f641512002e3c64151200056d72151200057970151200347e75d8d200047d75d8d20004f77158d2000cf47158d200057970d49200057b70549200066d6590920005cd7390920014ec76509200066d65509200065e65cc9200065d65cc92001fc820cc9200066d658c920005cd738c9200065e654c9200065d654c9200074f524c9200074d524c920014ec764c9200066d654c920015e8704c920026cf764c920006cc764c920006cf654c9200074e654c920006cd654c9200074d654c9200064d654c92003ece644c92003ecc644c9200074e544c9200074c544c920007cb704c920007c8704c92001ecf604c92001fcb604c9200347e75d85200047d75d8520006cd32d8520005cd73c8520014ec76485200056d72d41200074d32d41200347f76541200047d76541200056f72541200074d3254120006796590120007c9329012001cf87650120006796550120007a94250120007c9325012002c7e749942001e5f329942001e5d329942002c7c745942001c7f725942001c7d725942001e5f325942001e5d325942002e3f759902002e3c759902001e3f529902001e3d529902001e9f329902001e9d32990200163f50990200163d50990200047f75590200347c75590200063f75590200063c755902001e3f525902001e3d525902001e9f325902001e9d32590200163f50590200163d5059020016af2059020016ba2059020016ad205902001eb9205902002c7f76950200047d769502002e3e64950200063d649502002c7f76150200047d761502002e3e64150200063d64150200056d72150200057970150200065e5498c200065c5498c2001e5f5298c2001e5d5298c200165f5098c200165d5098c200065e5458c200065c5458c2001cdf7258c2001cdd7258c2001e5f5258c2001e5d5258c200165f5058c200165d5058c20016cf2058c20016cd2058c2000676549842000674549842001e77529842001e75529842001ed7329842001ed5329842001677509842001675509842000676545842000674545842001e77525842001e75525842001ed7325842001ed53258420016775058420016755058420016e72058420016f22058420016e5205842001ef120584200047f75593100347c755931002e3e64153100063d64153100056d721531000579701531001ece624cb10006cd624cb100074d524cb10007345450710007c5324871002c7e74996100047d729961002c7c74596100047f72596100047f75592100347c755921002c7f76952100047d769521002c7f76152100047d76152100056d72152100057970152100347f76d4a100047d76d4a100047
  | 2 => 0x269f32990300163f50990300163d50990300047f75590300347c75590300063f75590300063c75590300269f32590300269c31590300163f50590300163d50590300169f30590300169d305903002c7f76950300047d769503002e3e64950300063d649503002c7f76150300047d761503002e3e64150300063d64150300056d721503000579701503001e6e759883001e6d75988300066e54988300066c54988300166f50988300166d5098830026cf32588300066e75588300066d75588300066e54588300066c5458830026ce7358830026cc31588300166f50588300166d5058830016cf3058830016cd30588300347f76d48300047d76d48300063e64d48300063d64d483001e6e62d48300066d62d48300047f76548300047d76548300063e64548300063d645483001e6e62548300066d62548300065e654c8300065d654c8300069e644c8300069d644c83001ece624c8300074d524c830006765498430006745498430006775298430006755298430026d73298430006d53298430016775098430016755098430026d43158430006765458430006745458430006775258430006755258430026d73258430006d53258430016775058430016755058430016d73058430016f23058430016d53058430026f13058430004dd768c4300069d648c430006cd628c430006d5618c43002c7e749972001e5f329972001e5d329972002c7c745972001e6e425972001e5f325972001e6e325972001e5d32597200047f75593200347c755932002c7f76953200047d76953200056d729532002c7f76153200047d76153200056d72153200057970153200065e5498f200065c5498f2001ece7298f2001e5f5298f2001e5d5298f200065e5458f200065c5458f2001e5f5258f2001e5d5258f2001ecf2158f200066d6550b200066d654cb20026ce634cb2001dcf764cb20006cf764cb2001ecf654cb2001f4e654cb20006cd654cb2001f4d654cb200064d654cb2003ece644cb2001ecc644cb200074e544cb200074c544cb20006cd3258720006cd63487200065e63d43200065d63d43200056d72d43200074d32d43200065e63543200065d63543200056f72543200074d325432002c7e749962002c7c74596200167a40596200047f75592200347c755922002c7f76952200047d769522000579709522002c7f76152200047d76152200056d72152200057970152200057970d4a200057b7054a200065e65cca200065d65cca200065e654ca200065d654ca200074d524ca20004df7358620024dc735862000679655022002c7e74995200047d72995200366d72995200047d7099520036797099520004bf745952002cbc74595200053c74595200063f745952002c7c74595200063c745952002c3c74595200047f72595200066f72595200047f705
  | 3 => 0xf424c9400063c65d05400059d73d0540014bc76505400063c655054002c7e76d414002d3e74d414000579759414003678659414002c7c765414002d3c745414001738405414002cf876541400367b765414002d78765414000678765414002c7876541400073b745414002d7a745414002d7874541400073874541400167b64541400173b64541400073b43541400073943541400057b72541400073b42541400073942541400075b32541400075932541400073b415414000739415414002c7e749944002c7c74994400047d729944002c7e745944002c7c74594400047f72594400167a405944002e79405944002e5e5498c4002e5c5498c40004dd7298c400165f5098c400165d5098c4002e5e5458c4002e5c5458c40004df7258c400165f5058c400165d5058c400169f4058c400169d4058c4001e6e759884001e6d759884002e6e549884002e6c549884001ece739884001ecd73988400166f50988400166d50988400066e75588400066d755884002e6e545884002e6c5458840006ce7358840006cd73588400166f50588400166d5058840016af4058840016ea4058840016ad405884002ee940588400347f76d48400047d76d48400065e63d48400065d63d484001e6e62d48400066d62d48400047f76548400047d765484002d3c74548400065e63548400065d635484001e6e62548400066d6254840024df76cc840004dd76cc8400065e65cc8400065d65cc84001ece62cc840006cd62cc840004df764c840004dd764c8400065e654c8400065d654c84001ece624c840006cd624c8400074d524c84002e76549844002e745498440006775298440006755298440006d73298440006d5329844001677509844001675509844002e76545844002e745458440006775258440006755258440006d73258440006d53258440016775058440016755058440016b74058440016b540584400047f75593300347c75593300056d7215330005797015330026cf3258b3001e6e6254b300066d6254b300074d524cb3002c7e74996300047d729963002c7c74596300047f72596300047f75592300347c755923002c7f76952300047d769523002c7f76152300047d76152300056d72152300057970152300347f76d4a300047d76d4a300047f7654a300047d7654a300065e65cca300065d65cca3001cdf764ca300065e654ca300065d654ca3001ece624ca30006cd624ca300074d524ca30005cd720c630005d9700c6300347e75d91300047d75d91300047f75591300347c75591300056d7215130005797015130005cd7290d30014dc7650d30014dc764c930006cf624c9300074d524c930004de76cc530014dc764c53002c7e74994300047d72994300265f329943002c7c74594300047f72594300265f325943002e3f759903002e3c7599030
  | 4 => 0xd500056d7290d500047f7650d500047c7650d500157a7010d50005797010d5002c7e74d89500055e73989500055d73989500057970989500053f74589500053c74589500057b70589500055e73189500055d731895002c7c76d09500157a70d09500057970d09500047e76909500047d769095002e3c64909500055e73909500055d73909500047f76509500047c76509500047e76109500047d761095002e3c64109500055e73109500055d73109500057671109500057571109500157a70109500057970109500465c64cc9500065f62cc9500047e768c9500047d768c9500055d738c95003e5c644c9500074f724c9500065f624c9500074e624c9500074d624c9500074f424c9500074c424c9500047e760c9500047d760c9500055e730c9500053e74985500053d74985500057970985500055f73585500055c73585500057b705855002e3c64d05500055e73d05500055d73d05500157a70d05500057970d05500047e76905500047d76905500047f76505500047c765055002e3c64505500157a70105500057970105500047e760c5500047d760c5500053e740c5500053d740c5500056e720c5500056d720c5500157a700c55000579700c5500047e76c85500047d76c85500055e73c85500055d73c85500074d32c85500074d32485500047e76085500047d76085500053e74085500053d74085500055e73085500055d73085500157a70085500057970085500057974d81500075b32d81500075932d81500367970994500047d76950500366f52588500047f76548500065e65cc8500065e654c85001ece624c850006cd624c8500074d524c8500047f7558f400347c7558f400047f7558b400347c7558b4002c7e76d4b4002c7c7654b4001e6e6254b400066d6254b400072d5250b400465f65ccb400465c65ccb4003e5f654cb4003e5c654cb400074d524cb4003f8f424cb400047f75587400347c755874002e3c655074002d3e74d434002d3c74543400173a40543400047d72996400167a70996400047f72596400347f76d4a400047d76d4a400057970d4a400047f7654a400047d7654a4002d3c7454a400065e65cca400065d65cca400065e654ca400065d654ca4001ece624ca40006cd624ca400074d524ca40004df7358640024dc73586400367a65542400157b76542400067b765424002d7a745424002d7874542400057b72542400075b32542400075932542400347e76d95400047d72d95400047e761954002c7e741954002c7c74195400047d7219540036797019540005b571d0d40014bc7650d400047e76d49400347c76d49400057970d49400047e76549400047c7654940014bc76509400072d52509400065f65cc9400065c65cc9400065f654c9400065c654c940006cf624c94001ecc624c9400074d524c9400078
  | 5 => 0x678549802101e7b529802101e79529802101edb329802101ed932980210067a75580210067975580210067a545802100678545802101e7b525802101e79525802101edb325802101ed9325802100eeb215802100ef2215802100ee9215802101ef121580210147c75593500147c7558f500147c7558b500366f5258b500055e7394b500055d7394b5001ece624cb50006cd624cb500074e524cb500074d524cb500147c75587500053e74947500053d74947500363f649935002e3c64993500057671d0f500057571d0f500347e7690f500047d7690f500056e7290f500056d7290f500047f7650f500347c7650f500055e7398b500055d7398b5002c7c7458b5002c7f76d0b500347e7690b500047d7690b500055e7390b500055d7390b500066d6290b500047f7650b500347c7650b500066d6250b500347e7610b500047d7610b500055e7310b500055d7310b50005767110b50005757110b500157a7010b50005797010b500465e64ccb500065d62ccb500347e768cb500047d768cb500066d628cb500066d624cb5003e5e644cb500074f724cb500074e624cb500065d624cb500074d624cb500064d624cb500074f424cb500074c424cb500347e760cb500047d760cb500053e74987500053d749875002e3c64d07500055e73d07500055d73d07500347e76907500047d76907500047f76507500347c76507500347e760c7500047d760c7500053e740c7500053d740c7500056e720c7500056d720c7500157a700c75000579700c7500347e76c87500047d76c87500055e73c87500055d73c87500074d32c87500066d62887500074d32487500347e76087500047d76087500053e74087500053d74087500055e73087500055d73087500066d62087500157a700875000579700875002e3e64952500063d64952500057970952500056d721525000579701525001c7f7654a500066d6254a5001ece624ca50006cd624ca500074d524ca500047e76d51500147e76951500063f649515002e3c64951500157a70951500147c76551500055e73151500055d73151500056e72151500056d72151500057671151500057571151500157a70151500147e7694d500147c7654d500056e7214d500056d7214d500147e76949500055e73949500055d73949500147c76549500066f62549500047e76149500055e73149500055d73149500074e524c9500074d524c9500147e76945500053e74945500053d74945500147c76545500063f64991500057970991500057b705915002e3e64191500055e73191500055d73191500056e72191500056d7219150005767119150005757119150005797098d500057b7058d500056e7218d500056d7218d500057671d0d500057571d0d500157a70d0d500057970d0d500047e7690d500047d7690d500056e729
  | 6 => 0xe64d48310063d64d483101e6e62d48310066d62d48310047f76548310047d76548310063e64548310063d645483101e6e62548310066d62548310065e654c8310065d654c8310069e644c8310069d644c83101ece624c8310074d524c83100675655043102eb66450431007345450431007954350431006e562504310167a75980310167975980310067a54980310067854980310067b5298031006795298031026db3298031006d93298031026d830580310067a75580310067975580310067a5458031006785458031026da4358031006d943580310067b5258031006795258031026db3258031006d9325803100ef24158031006f1415803100edb315803100ef2315803100ed93158031026f1315803102c7e749972101e5f329972101e5d32997210047d709972102c7c745972101e5f325972101e6e325972101e5d32597210047f70597210047f75593210347c755932102c7f76953210047d769532102c7f76153210047d76153210056d72153210057970153210065e5498f210065c5498f2101ece7298f2101e5f5298f2101e5d5298f210065e5458f210065c5458f2101e5f5258f2101e5d5258f2101ecf2058f210066d654cb21026ce634cb2101dcf764cb21006cf764cb2101ecf654cb2101f4e654cb21006cd654cb2101f4d654cb210064d654cb2103ece644cb2101ecc644cb210074e544cb210074c544cb21006cd32583210047f75592210347c755922102e3e64152210063d64152210056d72152210057970152210074d524ca21007345450621004df7358221024dc73582210347e75d91210047d75d91210047f75591210347c75591210056d7215121005797015121005cd738c9210074f524c9210074d524c92100cec764c921026cf764c921006cc764c921006cf654c921006cd654c92103ece644c92103ecc644c9210074e544c9210074c544c921007c7714c921007c4714c92101ecf614c92101fc7614c921007c5329052101cf47650521007345450521007c53250521006cd32d812102c7e749942101e5f329942101e5d32994210047d709942102c7c745942101e5f325942101e5d32594210047f705942102e3f759902102e3c759902101e3f529902101e3d529902101e9f329902101e9d32990210047f75590210347c75590210063f75590210063c755902101e3f525902101e3d525902101e9f325902101e9d325902100eb6215902101eb5215902102c7f76950210047d769502102e3e64950210063d649502102c7f76150210047d761502102e3e64150210063d64150210056d72150210057970150210065e5498c210065c5498c2101e5f5298c2101e5d5298c210065e5458c210065c5458c2101e5f5258c2101e5d5258c2100ecf2158c2100ecd2158c210167a75980210167975980210067a5498021
  | 7 => 0xcb4103f8f424cb410047d729964100e76719964100e3f419964100e3d41996410047d70996410047f72596410047f705964100cf47158e410347f76d4a410047d76d4a410047f7654a410047d7654a410065e65cca410065d65cca410065e654ca410065d654ca4101ece624ca41006cd624ca410074d524ca410367665546410347e76d95410063d74d95410047d72d95410047d70d95410047e76195410047d72195410367571195410047d701954100cbe76d514102d3e75d51410063f65d514100db671d51410063f65151410059d7315141005ad721514100db67115141005b970151410053e761514102e3e761514102f1e731514102f1d731514102f2e72151410053d721514102f2d72151410052d721514102f36711514102f35711514102e3f611514102f37611514102f3a70151410053d701514102f39701514100539701514100db671d0d4100cbc7650d410053c7550d4100db47150d410047e76d49410347c76d49410047e76549410047c765494102d3c745494102d3c75d094100cbc76509410053c755094101eac62509410072d52509410065f65cc9410065c65cc9410071c54cc9410065f654c9410065c654c9410071c544c941006cf624c94101ecc624c9410074d524c9410078f424c94103674659454102db6749454100734549454102cf4765454100734545454101e6e62548410066d625484101ece624c841006cd624c8410074d524c8410047f75593310347c75593310056d7215331005797015331026cf3258b3101e6e6254b310066d6254b310074d524cb3102cf776507310073454507310047f75592310347c755923102e3e64152310063d64152310056d7215231005797015231005cd7290e3102cdf7650e3101cdf764ca3101ece624ca31006cd624ca310074d524ca310347e75d91310047d75d91310047f75591310347c75591310056d721513100579701513100cdc764c931006cf624c9310074d524c93100dd4714c93102c7e74994310047d72994310265f32994310047d709943102c7c74594310265e43594310047f72594310265f325943100e7641594310047f705943102e3f759903102e3c75990310269e73990310269f329903100eb671990310047f75590310347c75590310063f75590310063c75590310269f325903102c7f76950310047d769503102e3e64950310063d649503102c7f76150310047d761503102e3e64150310063d64150310056d72150310057970150310065d6550c3102e9e6450c3101e6e759883101e6d75988310066e54988310066c5498831026cf32588310066e75588310066d75588310066e54588310066c5458831026ce7358831026ce4358831006cd435883100ee6415883100ecf315883100ecd3158831026cc30588310347f76d48310047d76d48310063
  | 8 => 0x5ce76d0932025cc76d093203dcf75d093203f4f75d093203d4f75d0932005cd75d093203f4c75d093201dce74d09320078f64d093203f8c64d093203f4e54d093203f4c54d0932005cd71d0932005cd70d09320055f75509320055c75509320074d525093201f8c4250932005ce761093201ece761093201dcf751093201f4e7510932005cd751093201f4d75109320054d751093203dce741093201f8e741093203f4e541093203f4c541093201fc67110932005cd711093201fc57110932005c5711093201fca7010932005cd701093201fc97010932005c970109320074d52d85320074d52985320074d52585320055e75185320055d75185320059e74185320059d74185320074d5218532006d56118532005da7018532005d970185320074d52d81320055e75981320055d75981320074d52981320074d5258132005d77158132005d471581320055e75181320055d75181320059e74181320059d74181320074d5218132005d67118132005d5711813202c7e749943201e5f329943201e5d32994320047d709943202c7c745943201e5f325943201e6e325943201e5d32594320266d32594320047f70594320047f75590320347c755903202c7f76950320047d769503202c7f76150320047d76150320056d72150320057970150320465e5498c320465c5498c32026cd7298c3201e5f5298c3201e5d5298c3200c7c75593510366f5258b5101ece624cb51006cd624cb510074d524cb510367b505835102e3f759925102e9e739925102e9d739925100eb6719925100e3f519925100e3d519925102e3e64952510063d649525100575719525102e3e64152510063d64152510056d72152510057571152510057970152510063e64d4a510063d64d4a5101c7f7654a510063e6454a510063d6454a510066d6254a510069e64cca510069d64cca510069e644ca510069d644ca5101ece624ca51006cd624ca510074d524ca5100c7e76951510063f649515102e3c649515100d76719515102e3e64151510055d73151510056d721515100d76711515100579701515100c7c7654d5100c7c76549510066f62549510074d524c9510363c54590510366f525885101ece624c851006cd624c8510074d524c8510367b505805100cbc74597410265e7598f410265d7598f4102e5e5498f4102e5c5498f41026ce7298f41004dd7298f41026cd7298f41004cd7298f4102ed64198f4102ed54198f4102e5e5458f4102e5c5458f41004df7258f4102e9f4058f410053c7550f410269e6350f4102d3c74d4b410065e63d4b410065d63d4b4102d3c7454b410065e6354b410065d6354b4101e6e6254b410066d6254b410053c7550b410072d5250b41024df76ccb41004dd76ccb410471c54ccb41004df764cb41004dd764cb4103f1c544cb410074d524
  | 9 => 0xf7654a320066f7654a3204d6c7454a3201e6f6454a320066d6454a320056f7054a3204d6f75d0a320347e75d91320047d75d91320047f75591320347c75591320056d721513200579701513201cde76d4d3201dce72d4d3201cdc7654d3201dce7214d3201cde76d0d32005d671d0d32005d571d0d320055e7590d320055d7590d3201dce7290d3201cdc7650d320055f7550d320055c7550d3201dcc7250d320056d7594932025ce739493201f4c3254932024ec76549320074f53549320074e53549320074d53549320074c53549320366f76549320066c765493203d6c74549320066f64549320066d64549320074f73549320074c735493201e6f635493201f4f63549320074f43549320074e43549320074d43549320074c43549320056f7054932024ee76d093203d6f75d09320056d7510932025ce7310932005e57110932005e97010932005cd7299532005cf72595320055e75d91320055d75d9132005cd7299132005d67199132005d571991320055f75591320055c7559132005cf725913201dce72d5132005cd72d51320071f549513203d5e749513203f4f72951320055d729513203f4c72951320055d7095132005cf725513201dcc7255132004de7615132004dd761513201dce7215132005cd7215132005d67115132005d57115132005da7015132005d9701513203e5e761513203e5d761513203d5e741513203f1e741513203f4e72151320055d721513203f4d72151320054d721513203f56711513203f55711513203f5a70151320055d701513203f597015132005597015132005cd75d893203dce74d89320074e54d89320074c54d8932005cd71d8932005cd70d893201f4e52d493203d5e74d493201d5d72d49320074f62d493201f4c42d493201f4f21d49320055d70d493201f4f20d4932005ce769493201ece7694932005cd75949320054d759493203dce74949320074e54949320074c5494932005cd7194932005cd709493201f4c525493203d5c745493201d5f72549320074f72549320074f625493201f4e425493201f4c425493201f4f215493201f4c21549320055f705493201f4f205493201f4c2054932025ce7654932005cc765493201dcf755493201f4f75549320074f65549320074c655493203dcc74549320074f54549320074e54549320074d54549320074c5454932005cf7154932005cf70549320074f76549320074e76549320074d76549320074c76549320074f74549320074e74549320074d74549320074c745493203d4c74549320074f64549320074e64549320074d64549320074c64549320074f71549320074e71549320074d71549320074c71549320074f70549320054f70549320074e70549320074d70549320074c705493203d5f75d093203d5c75d09320074f52d09320074d52d0932
  | 10 => 0x4a4201f4e6354a420066d6354a4201f4d6354a420064d6354a420056f7054a420347e76d95420047d70d95420047e76195420365e73195420365d73195420366d72195420047d701954202c7e76d494202d3e74d49420056d75949420366c659494202c7c765494202d3c745494201f2c425494202cec76549420366f765494202d6c76549420066c765494202c6c76549420072f745494202d6e745494202d6c74549420072c745494201e6f645494201f2f64549420066f63549420056f7054942024de73d8542004dd73d854202c7e749944202c7c749944201e5f329944201e5d32994420047d709944202c7e745944202c7c745944201e6e425944202e6d425944201e5f325944201e6e325944201e5d32594420047f705944202e5e5498c4202e5c5498c4201ece7298c4201e5f5298c4201e5d5298c4202e5e5458c4202e5c5458c4201e5f5258c4201e5d5258c4202e76549844202e74549844201e77529844201e75529844201ed7329844201ed5329844202e76545844202e74545844201e77525844201e75525844201eb7425844201eb5425844201ed7325844201ee6325844201ed532584420167a759804201679759804202e7a549804202e78549804201e7b529804201e79529804201edb329804201ed932980420067a755804200679755804202e7a545804202e78545804201e7b525804201e79525804201ebb425804201eea425804201eb9425804202ee9425804201edb325804201eea325804201ed9325804201cdc73597320047f75593320347c755933201cdc735933202e3e64153320063d64153320056d7215332005797015332005d671d0f32005d571d0f320055f7550f320055c7550f3201cdc7358732026d4315873201cdc7358332005d67199332005d571993320055f75593320055c75593320071f54953320055d72953320055d7095332024de7615332004dd761533201dce7215332005cd7215332005d67115332005d57115332005da7015332005d970153320465e76153320465d76153320471e74153320471e64153320071d64153320474e72153320055d72153320474d72153320054d72153320475671153320475571153320475a70153320055d70153320475970153320055970153320455e74d4b320055d70d4b320455c7454b320074f7254b3201f4e4254b320055f7054b320455f75d0b320455c75d0b320055f7550b320055c7550b320074d5250b32026d461587320055e75983320055d759833202c7e749963201e6e729963201e5f329963201e5d32996320047d709963202c7c745963201e5f325963201e5d32596320047f70596320047f75592320347c755923201cec725923202c7f76952320047d769523202c7f76152320047d76152320056d72152320057970152320366e6554a3201d6
  | 11 => 0x47d72996430265f32996430047d70996430047f72596430265f32596430047f70596430365e6554e4301e6e7598a4301e6d7598a4304e6e5498a4304e6c5498a43026cf3258a430066e7558a430066d7558a4303e6e5458a4303e6c5458a43026ce7358a43026ce5358a43006cd5358a4303ecf4358a43026cc4358a43026cc3158a43026cf3058a43024dc73586430347e76d95430047d72d95430047d70d95430047e76195430056d72195430365d73195430366e72195430047d72195430366d72195430046d72195430047d70195430365c6594d4302cdc7654d43026cf325884301c7c755935201c7c7558f5201c7c755875201c7c75583520367b50583520363f649935202e3c64993520057671d0f520057571d0f520347e7690f520047d7690f5201d6e7290f520056d7290f520047f7650f520347c7650f520053e74987520053d749875202c7c745835202e3e64952520063d64952520056d72952520056d72152520057970152520065e5498e520065c5498e5201ece7298e5201e5f5298e5201e5d5298e520065e5458e520065c5458e5201e5f5258e5201e5d5258e520047e76d515201c7e76951520063f649515202e3c649515201d6e729515201c7c76551520055e73151520055d731515201d6e72151520057671151520057571151520057a701515200579701515201c7e7694d5201d6e7294d5201c7c7654d5201d6e7214d520063f64991520056d72991520056f725915202e3e64191520055e73191520055d73191520057671191520057571191520057a70191520057970191520053e7498d520053d7498d520056d7298d520056f7258d5202e3c64d0d5201d6e72d0d520056d72d0d520057671d0d520057571d0d520047e7690d520047d7690d5201d6e7290d520056d7290d520047f7650d520047c7650d5202e3c6450d5201d6e7210d520056d7210d520056d74d89520056d73d89520053e74985520053d749855202c7e74d81520053f74581520053c74581520366d72994520047d76950520065e5498c520365c5498c5201e5f5298c5201e5d5298c520365f5098c520065e5458c520365c5458c5201e5f5258c5201ece5258c5201e5d5258c52036cd5258c520365f5058c520367b50580520047f7558f420347c7558f4202d3e74d4b4202d3c7454b4201f2e4254b420047f75587420347c75587420047f75583420347c755834201e6e729964201e5f329964201e5d32996420047d709964201e5f325964201e5d32596420047f70596420465e5498e420465c5498e4201e5f5298e4201e5d5298e4203e5e5458e4203e5c5458e4201e5f5258e4201ece5258e4201e5d5258e4203ecf4258e4201ecc4258e4201ecf2058e420366e6554a42006cd6354a4201d6f7654a420066f7654a4202d6e7454a4202d6c745
  | 12 => 0xf5298c540365f5098c540365c5358c5402e5e5458c5402e5c5458c54004df7258c540365f5258c540365f5158c5402e9f4158c540365f5058c5402e6e549885402e6c549885401ece739885401ecd73988540366f50988540366f52588540366c52588540366e755885402e6f545885402e6e545885402e6d545885402e6c5458854006ce7358854006cd73588540366f53588540366c53588540366f51588540366c515885402eaf41588540366f50588540366c505885402e76549845402e74549845403677529845403677509845403674515845402e76545845402e74545845403677535845403677525845403677505845402e7a549805402e7854980540367b52980540367b50580540367850580540367a755805402e7b545805402e7a545805402e79545805402e7854580540367b53580540367853580540367b52580540367852580540367b515805403678515805402ebb41580540065e73588540065d735885402e6f725885402e6f425885402e6c425885402e3f41588540047f705885402e6f745885402e6e745885402e6c74588540066f73588540066e73588540064e73588540066d73588540064d73588540066c735885402e6f435885402e6e435885402e6d435885402e6c43588540066f71588540066e71588540066d71588540066c715885402e6f415885402e2f415885402e6e415885402e6d415885402e6c41588540066f70588540066e70588540066d70588540066c705885402e6f405885402e6e405885402e6d405885402e6c40588540047f725805402e3f415805402e7b705805402e7b405805402e78405805402e7b745805402e7a745805402e7874580540067b73580540067a735805400679735805400678735805402e7b435805402e7a435805402e79435805402e7843580540067b72580540067a725805400679725805400678725805402e7b425805402e7a425805402e79425805402e7842580540067b71580540067a715805400679715805400678715805402e7b415805402e3b415805402e7a415805402e79415805402e7841580540247c75593530366f5258b530367b505835302e3e64952530063d64952530055d73952530055d73152530056d7215253005797015253026cf3258a530247e76951530063f649515302e3c64951530255e73951530255e73151530056d72151530057571151530057970151530066e54988530366c54988530366f50988530366f5258853026cf32588530366e75588530066e54588530366c5458853026ce73588530266f5358853026ce53588530266d5358853036cd53588530366f50588530367b505805300e76759874300e75759874302e76549874302e74549874302ed6439874302ed5439874302e76545874302e74545874302eb740587430265e7399643
  | 13 => 0x102900300200200100400000601900a00100100900b00300900002400100000300400000000000100c00300900400300700900000600300200805000001501100201300000a00400800100100b00100000100201801100a00b01204000000000100e00700e00000300801b01600000f00001300000200700401001102600000300300100000b00401401000400200500100500e00000300700700300100100600501902d00500000000a00401201c00002300701000000100000400400d00001001200d00000000000400200101b00300600000701700000100000000201300100500500200b01805200000100a01800700100300801800006100300a00600300a00200b00300200100000400000000200502101300400100a00700900100700400000900201400501200000100101701600600101501100200003000c01300200400100200c00a00200000000300000002700e00900200000000d00000000e00e00001a00400005602000000000000402200e01b00101a01700000200000000300900100f00400601200200300000400000100400000c00000000100900700500200101a01000100600000900300000700202800100600b00600000501300200401400900300001100000000c00000200202100505100000000000e00000300100000002c00200000000000002d00000200601300000800b00300200900b00000000200a00100e00202600100100200b01602300401e01600100305c00e01600202200301300000000100c00100501f00200000600000000500401300600000700801600200100000102800000000702800d00200600300401000500300d00000000800400400700800f00701b00000100100501800300800000600700600000e01100000301100c00000600100004900001700300600101500700a00200100800100000800601600000d00200400001900001000301e00000500200100a00100200100100d00700700300201602300000801c00200000001000405703701d00000100b00000300200200004100d00301800100c00700000000e00700000900300400500000600300100f01100d00700700400005600100700400200200500003b00d01000d00100000500100002001800000800a00803500000e00300300300200000100301100c00000d00000000200100300000000100700000000800201300000200000800000101206c00000000001700c0040080010060060010070160030000050070240060040020040040030050030000060080280020120000366f5258b540367b505835402d3d76d52540363d76d525402e3c545865402e6f7258a5402e6f4258a5402e6c4258a540047f7058a540047f725825402e7b705825402e7b405825402e78405825402e5e5498c5402e5c5498c54004dd7298c540365
  | 14 => 0x5d92e88338bc6000030800000064d0d8835038466137a13004581ce394994ce4c1f301986a43e86a00000af4000815158800089e12e30716f845a170000217c9600001959f549264b7000228817058300022140007dc00019eca2a00035f0ce412c00a3c680001300412d60000ed46fc32b920896c0190071dd05d44a90f58c9842e35526c15288aa46e17003d0d660b53758be071452603c1a700000000001ae8b9a3b00001ae43885ba0000000c502d425900001ac5de0a820a8f724e328f800027c2ee3b30fb44ba81c000000013426300019bc0006252de03b4d9e5133e3054c00015b36a99880000000e89950bf848829a9e140005c905e970892000027b9624f0e6e134c8000f9838b0ac1ae03c42e814f9cb893a0000489770002000198057c8962c02ed1750e447c54580c7407031b1040000e8e070059208c2267ce1c480003087630000a50154000000000050c3a5000005c00086e0001020df429c43d145c1ce66a00004accdc70d44b058049422800015b800083a2c205380006bb3ab000000000020c0f5c000344249000000080116520500000003448000c720001e419e42ea3de0000e8c0006e31351b60bea3502e980006300001681508de60000000110c6e4131ab21ac38c70c2738f1867c54826495d80205c42ce1d2912611100483008de00037b1d083540003260000000694202a2cc0005521868000ac888b0001a480000b0000142c0c80c63b29728d560e40001fb04147ad000060800073619c0000d4e43418580004a000034887c445e48c403a090df0047093a11473a19b00009d8afe4b300008dcbe677034d80000007d716400000008281af87f800055719b00005a40001e387f00003131f60cf4fb25621ad13590840003f020b0000000268980c0ea145013a104c6651a000143800087820d9404c0089a42a101c72600000000003560e61a783d44441a422e1b380c056b0e580000000000181ec03f4684273000000015a41f8500ddc23100009b851a4a70190158000000070815cbde0000748000e3c7971bd0000dda7890fe9ac4d3e5a409f8cdc00000000000000004860001cc4be81740cb9cd4d167381100a90d0a83d3e88c490b21d74450e68d3a46b32899785b240f0609d2c5fa7140d0096c20e00027d184862c01200400301000103e00000b00e01300201b00001100200400000101000200500001500101a00b00700300800000100a01f00301401c01500200400a00000e00002900200300600100000d00401c00e00000200400300000001b00000300002800000000000100200403800700501000100000f01d00400f00000c00100500b00001d00101a00303002c01401200000600100000000b00000201001d00000900400101300200300600802300101007f00200200001100e00d00301a00203400
  | 15 => 0xd20c4aca78e2889340eee2923ec02b4c78340339976c0001c83aa9adceb8396000038d15668c2dd834821221a27d800101a4bc3a922749e42e24040a94196805347131c20c49721198889a600013a9ab000087b000053c00082e00000000000df01200009221e00001574a3a000000000028478c1e907982380a71488eb459268a2939948ab43b70f711505766dd02c20ec6ba29b17b1da073073c3d10c680000002c613841d886645b1edc0002ff0000388bd20000000000c3a3df00001349b80000001aa511013d371175c4e83310249d9052c00005f14ac00000000016608204780e093180000b300008740001f80698af04c48380001f8800000030b801cc1638424716740002400c600000001cd17690581dc07339d8fb8e668972f294603da5683189decfb484d1158f746023291960000c0c2e92ea9e4030223622302f000037e000214cba00000001ac80000ba29b1f5813a2a10001da4fc86d40a18a80b6e0760000e140000001eb0ebc83a4061b1943494875b2f583940a67e72ab0f3c05c2570ee000000035b22f21d4a4a72d000173c0000003cd805400087008608c0d2a80f06d8be8a7440d0000000000343000000050414823300000005923b685f48e248f20e079447a25421c84790144613ab95c44f06360000000c6433233498206100001d003e90ec73e1d61960bdc4fd000021c0d67e808d1fcc87a0000001b24c0231c30480000006a400003f4b8682f13980004d24f100006885462f41d5800005a66026122244f47950000114c4e000395836800031503491200008a744c94410aa7e50ed99e8e8a5873238d981021e72cd10b0fa485c11fa098eea82d12c81ecf0800035e862c2ac3b217d8dccab21962e7118c3300ea00000002d87fb44a86cc0004f53b884585c60002bc1e7c77479e0000ee4a464a01e004f000006a20c8000e4e2ae000157c000746000179019e4dd340958c9fe4e813c91f50c00000161054cb624d40596a88820003b9990865e4400ed019c00012c15f00010bc01a22ca1a8c461900000000ea62ac0131b6cf644651d89a601ba063349a1ccc5c2814430ed04323f917a97800843a7000153885a26640706c0d6835304b986cc0e5ea00001a032620b09b10c88ac88e27a13f843e2490e28b30b8e28022f90488703c22341cf45f80002cb98b09b470f2e911d02680cc20d035c2204db0bc92c456a2af3ae8de04a61181340f6c0001ef2b6984c5603cd31a80000000003658c9450807f12f9864b644870ee85dc2706de00000082148a60ac8804c8c6300e91788000000000059c61e025003000050e5043d21d0cd007860ca9ebc3d00ff0d7a0d8de00001e4800000000009d9a8c0281a32d285043100000000cf00005b000c099cc5628827797f469804b29006142a488c3a88cecb1658833680dc10
  | 16 => 0xe26d01b0c240005a736100000100000900488720000137800007a7030001dbc22e2da17902311302b83840fdd0127ff413866400004f16f0c4088e3420001d9c79c2d11cf8dac42824e000132d07881e322108400000002300002c806e11493389c423930f05781324f800003d84466163b91f8c55687c00280004fe57b0d282fcf6637f00000005de15739612946e42064420a0c3a67343af0670fe24ac000206044e0003631fb4a4400029502ace004a237a8e70b3c0003ef1424d5050f00012b800000016116887c021841822e8f063e60a214ec000000000004c05e2cb3d597ec0000001de09780004ec132000114263b24f94f11587cb2551490e1422a00e8be4a146051e610ac84427e1918c1c71c82004f11f80000b43e100011365953b08170af26d911f0000b0c24c0c003ec00000000019d4000704107071c1107e90068b60e6e49525c808034e3b615685a0fc27920001c08f528b80001df80003052249380b6a5930ae04543ee13101e10386de66806480000005740b88b0c53c000440a064f7c7802781144a1024b34793480cc05a45a9e44ce441e1c0861c65a61519211740062c624f046cd4c4a63a722440904ed4001634e5417c029028458231e13022089aa08230e21483d24572320944c747c81f780fc4762e43bd0ca10b039e213204c9347f0124058902e51432e03e10c634511991484a47bd2f313290960c82cd8efc85405b11095c01a278221d99f82d420f42b06fc7548a02f891c08a64422ef8c9c0de73233e016473635c0fb043c37879405b10088183171f088b8f4040032183bc4c27fa2a61f4c5cc34a2e58df4000837045907ccc848b16da290b1e7c101f0d1cb7e3d5005990099e1291ec97a0c686ea27e0ef446482526c9d242323cb05b8c18d8017e0ca06b4a4263824c8898c406df1f815350c223c053034048a0003339df437c0003da00011500001b383611204ab07c87d419a7ba31f947057e7284591eb84f64eb0a485300000002db1ec4d7e16100000003680000002010d0e2b24310e902f00a40dca2503f61040d9042c7fa35e43b9e70d86000106166440600000000000005fa138800081200019000000008a50969bb0a70883289000000079d3721898000023162867848e0002e00070f783dc31f1ad8cfa6e517899d02f43ff2dc13940803eb08415dc00049b226900506a3c309ba2000002d615d0da01500af1caa0a47a27580dd870c19428b27b000041a89f12d00003a800002883542cc86920a07e42da19f3418bcc1d630c099216c6960942be8378aa65b116981d099001f02a1160f5075f21e02940005281a09e9c0003041f9156c8164300001968edc00032b228c00056600011fc00086800009c828c8331a4000000034d12a9540f8e000000000084a1c03738f9cb3e87e3d50a4c1207c003
  | 17 => 0x7e0db0e30778392968c80601114a8b9cea85a825198846c44a8443a2d0a043713fe8000c5e00003882480007f600000000001ff0de9c04bb02242c1000000000000d80000008b700016d010a200147960033a6f914b800000081112b00008d200000020890806633890dd87e867715b1a5887e000087086c7527063e7863411c42e1211270da06af0000e0cb5c73910b063cdd25963f305290a07401ab83c00184cc0148ddd0f26b01b81304dae72100000001625443151f3414084300015f80003e93db0a640000001358b5c6a463d1670ee097c0003c99b6831212f0a895cc09c11f2f68fa113878109c8cb88b62151c786d82f60430001a2054e0002ba8e5000014b00018340000000798404000285217800000058e29b85d8f165552020f6000000023017e4fee52900009040000721449ba072e7fe3df80000002b328d9868e0e21e24a02b0e227411c3206c2283753921ad4000211000031068c5ff3641a6853a47c1be0000ef87df0b9950497a8af1c0000000014d3fa951800008f277158400074d20892eca800000f50000b0a2fe0daa0400c400008e9bec20000000000008745e725a80000003c10000000a0c00043a0bb00003333a403f80004ea0000c004b86bc1230a2805647a26a1f74a2c2a23650f5000082b108122800009c39008d000018a21400000000003dda2b85683600000f900000000001d640000000000c0cae40000001c582d25a60001774bd84ad05c9dac1d01d636b200cb722aa0c31fd059a50534f000091a443000026c7fc0004250e64c4887f2960da4b66590458935c2fe78a2d021b49f25330141b9903a03437f8414b1479a32596b4c2056734106e90e47db2508308ad23f116e1e3cade000191175818a1723b614b80006024490d44394848132939043840a42d1c70e3a21224290808947992220484a92165181090c0003ca0f81bdce264291ba1eb01e205e2bd11ecbf006518a14bccca2c70b59dd8d5c00f01d8ed4f8606c3169e58d1a3883a802105501f232c87847f052d0c713cc51800032e88110ce6aa3d18000de264f1c900007f653e30612d09868472818db436e3d300000002040000250bc103e73f28c80002ba81a3668000c94000244800086283933b1c7ca688461c880000003bb0f2141cef22022f80a9839e000000093c0001a821a88e0b9021338a96a4e326fd41a0ae4a6067000011e49d23642af023400065f3ad20081b224400011d459e7d400011c8fd62f700022b4d8861400000d46f627042b85b800014728f150c3a06c70280fd4aa255c36e06b08660001d409dcf427b82120684c08103370152c37070b34811dc2461e33688ff10923e239d2084ff201602f8b8464223a31482b8cd8473236027cd980003b10000d5a1541d999e0e8871b07b87b111a4ba28622e475c0000431d304
  | 18 => 0xd8a1262311f283243fa02a958111e2eb1888814fde84f06190dc88a7ea4030000f10361036877c00087113e99545883d016f951487c72303b8c7cab029a1e2822822489e18514c4ad812800022a40240dc1129d3c90607916e9f10bfc4cd0001400ff028e1a4800074c0832fb1c6833487d1a7060c3aa6f22e2808425409314c1ed40744af1d0953c6b26a20001c3835c6502be155106438725c119d0882a91e200010984362ca1a5cad46d339792009be85123b04cc2600e02c89ff07448120aa858cc306451fb1e9884e3190188cd509c1912de80783b01352e0a19470433f2f909610d80a21f2831c3b25cc40601f4fa020929f9b04c8254701107300006a138b96bc8b43582629f24c1483e18705bc09853917299fc05407c19d2058ce23da0e49138d4a49625f88d4bc233416a80e490846a30f94f49880001f1800000061114804940000001c611400005c63f71dfd0de53238812040fc730136028cc1e6ef2c080008da3f304a89f02482b708699246546d226f00006d40003330000f3008938299ac1524170791a18dfc05d3d28db83bc00038496840083ea000192071a13a0000de41764984550ef80003543270d9400044c4321fc8bee0003b00698b5685d0
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc2e645c8540c00185ac8b90a8180170e99170150300061cb22e02a0600086d87152620c0014d3002a4c4180021b61c545883000534c00a8b106003a4d83589520c00149b0532a641800293e19524c83000707322a49906000e0d64549320c0014cb042a4c2180029c600549843000722a92653086000a6582151610c0014e3002a2c21800391549325843002c3dc32e02a64000a4d8215263c80014b3002a4c790002936085458f200052cc00a8b1e4007a4c8459532c800f49f0d2a2659000293618544cb20005a4c00a89964000c4d635cb50c800b0df0cb90a9100030bd91721512002e16322e42a24000c3b645c0544800b870c8b80a8900168b211659092000626b2ae7212400586c87595424801143908b2e64900268b211658c92000526c14ca9924007a1c84595324800f45908b2a649000293614764c920005a4c04ca9924007a8c84595324800161908b2a6490002d2e01654c92000707c22ca9924007a4c845953248001c1908b2a649001e83211654c92000527c02ca9924000e4b80595324800f49f0d2a26490002d2602544c92000526c30a89924007e0c641513248001693002a26490002e2610704c920005e0c08e0992400583c845d7614800189aea996c2900160f211765412000626bb264a824005a38845964048001c92ca99480900161e21d655012000714b2a84a024003cc8764c94048001c92ca99280900161b609761502002e17322e42a04000c2d645c8540800b874c8b80a8100030e591701502000526c10a93184000a5980152630800149b042a2c610002966005458c2000532c10a93084000a718015261080014cb042a2c2100029c600545842002e17322e42a62000c2d645c854c400b874c8b80a9880030e591701531000592c10a8a0e2000b318015141c400b07908bb2a5080029360a654ca1000527c32a49942000a4d86549328400149b042a6c6880029660054d8d100042ec38a831a2000a4d8215063440014b3002a0c68800313a157218d1000626c2ae431a2000c4e545c86344001898a8b90c6880029360863d491000526c10c6a9220048cc87589324400189ceca926488003131d9524c91000562c10c720a2000b25821514144001663002a2828800385150635051000562c10c6a0a2000a4d8218f504400149b0431aa088002b2219324811000516c10eab202005879805d854040010df0cb90a8080170b991721501000616b22e42a02005c3a645c05404001872c8b80a808002936085498c100052cc00a93182000a4d8215163040014b3002a2c6080021b61c549881000534c00a9310200086d8715162040014d3002a2c408003135d5735881000526c14c6a902000a4d82995320400149f0ca92640800293619524c81000627bb2a49902000c4d765493204001c1cc8a92640800383591524c810
  | 1 => 0xb042a28398802cc600545073102e17322e42a46200c2d645c8548c40b874c8b80a9188030e591701523100516c10eab206200a39801d5640c4010df0cb90a8188170b991721503100616b22e42a0620087b865c0540c40b874c8b80a8188030e591701503100436c38a93106200a6980152620c4010db0e2a2c4188029a600545883100526c14ca9906200a4f86549320c401c1cc8a92641880383591524c8310051ac30a8a086200b2582151410c401663002a28218803855954350431007122a2c4a086200e8543589410c4010f30e2a4c0188029a608549803100724a9265300620087987151600c4014d3042a2c018803925493258031007182a282b006200e9143505600c40149b042a4c790802966005498f2100526c10a8b1e4200a598015163c840f49908b2a659080293e01654cb2103d27c34a89964200a4d8615132c8401693002a265908170b991721522100616b22e42a44205c3a645c05488401872c8b80a910802c9608545062100598c00a8a0c4200a4d851d93248401693002a26490802e1610714c921005e0c00e29924200b25821514148401663002a2829080f311d93250521007822a264a0a4200a39801d5640840b85cc8b90a8108030b59172150210043dc32e02a04205c3a645c05408401872c8b80a810802936085498c210052cc00a93184200a4d8215163084014b3002a2c6108021e61c549802100534c10a930042008798715160084014d3042a2c010803135cd6290b5003d26422c4996a007a4f86d0932d400149b0c21265a8002d1604424cb50005a4c0084996a00094d829cf41d400189aec99643a80030b5d1620875000626b9ac410ea000c69625c021d400749f0ca9265280021b6087650d5002e1a322e2212a005c38645c042540016930131264a8002c3211624c950005a5c02c4992a000b4980d09325400149b0c21264a801f83190424c950005a2c0884992a000b4980109325400129b0439ac2a80025360a73d055002c1e422ed90aa000c4d764cb215400149f0ca92642801e93219524cb4000526c14ca9948000a4f86549329000149b0ca92652001ec3211524ca4000526c10ca9928000a4e8654932500014990ca9264a0002c660c745414000594c10e8a828000b31811d1505000166303a1aa0a0023161db325414003e2c3b264a828000f0b424c9505000b870eda0aa0a0002c660f415414002e1c3b282a828005a2c845d5621000189aeab9ac4200029360a635484002e0e3a2c6a908005c2c74589521000149b0532a642000293e19524c84000526c32a49908000c4f76549321000189aeca92642001ec3211524c84000722a92653088005a34845496110001c8aa4992c2200160f2117654a3000526c14ca9946000a4f86549328c00149b0ca9265180028b608755903000437c32e42a06005
  | 2 => 0x5701533204c3643ac8a94640686c87591524c80749d0da1aa49901f431d34354932005a340e86a926400b4581d0d524c80129d0f21aa4990025321d435493203e863a286a92640094d829d7644c80129f04b84a89902313a19721513203e26c32e42a26407d0f415c8544c80129f00b90a89900352a097015132006a4c12e02a26407d4b425c0544c80fa9084b80a89901f46d05701513203e873a0a9b126400b4980153624c80fa1ce92a4a499002d26005494932004a743ea8a926407d0c74951524c8072990eaa2a49900293a185454932005a3408a8a926400b4581151524c801695002a2a499002d2600545493200587424eca926400b0d849d9524c80149d0c3a2a49900293618745493203e873a0e8a926400b46811d1524c80168b023a2a499002d2a007454932005a4c00e8a92640094e87d91524c80fa18e9322a499002d1a066454932005a2c0cc8a92640094f87591524c8012990eb22a49901f431d1645493200587424e2a926400b0d849c5524c80f29d09b82a499002c3e11705493200586422e0a926407b0e84d4b424c80f61908a9684990025361676d0932004a7c2ae3a12640094f855c3424c80f2990ea92849901ec3211525093203ca7422ea212640794c845d4424c80129f00ba8849901f51951711093203ea22a2e22126400d4a855c0424c801a930ab80849901f52951701093203ea42a2e0212640094f87548614c801a1ce8a90c299003435d1521853200722a92c230a6400d49529c0614c801a92a4b80c299003345857018532006a2a96e2b026400d45521c5604c80129f0ea90c099003439d1521813200686ba2a43026400d45529c4604c801a8aa4b88c0990231398d721503202e1b322e32a4a205c2e645c8549440185ac8b90a9288170d991711525102e1d322e02a4a200c39645c0549440749f0ca92652880383991524ca5100706b22a4994a200c4e855ca63d040189b0ab94c7a081f139517298f4103e262a2e531e8207cc6415ca63d040f98a82b94c7a08024b6087550f4100526c14c7a968200a4d8298d52d040b838e8b1aa5a08170b1d16254b410460e2a2ed99682048cd82dd932d040189eeca9265a0803135d9524cb4103d86422a49968200a4d82995329040149f0ca92652080293619524ca4102e1bb0cec2a28200d0e835c85450401a1b06b90a8a080349a05721514100692c0ae42a28205c2f615c8545040ba4ec2b90a8a08034ca05701514100698c0ae02a28205d33615c0545040125b043aa86a08164b21d525094100516432a4a128200b0d821533250401633002a664a080293608654c94100586c10a89928200b1980151325040149d0ca9264a080293219524c94103d86422a49928200b25821525150401663002a4a2a0802c560c545454100592c10a8a8a8200b3180151515040164
  | 3 => 0x352002ae002c4638005db5e4817edb80031aca00000001ae6728c0b3be1a000048cef23b2bfa9c2780021af062aa2cb3a05c000e6800b414e5d0fe83800e9218a213adf10e000f2003b45c9b2d0bbc21032002a07d8004002eda148181fac5026b780099000000001612a0ab16c280000320000b47c00066000003623e800dd27e5b0d0bb85e920eae222acab54eea1099a1c77bc60586e4580000000a58007c8069701e37abe76000c91426fa6cf09a6418aacc21e582c2b587e1e0a45ea8034a5665384d5a92f3000b7088000f449b440d83e91000dc2c01b1f8c49b8f4800002f2000020000059800ca22ca900070b38002acd001300c350081c0000107c0000405000060c80200004000000001302c0409c01030030340200c0406421004000040b01c0203417004000a4090000105c2a024090100a0000000000004090000000000000090100405c1a01c000900600002000020280c0000b01c0001c0f01401014000200100c0c038020001003000010130000200009014020101b0040403406004230100000c0102407004051a00303400064060140500008070040040e02004008050080300c03000010840100404004000200a040280100000800008000100f49b0539ac42a02293e09735885402d17424e6b10a808e0e849cd6215001c1b0939ac42a02383d06735885400627c3ae6b10a807c4e745cd621500f898e8b9ac42a01f83d0573588540052741ee2b10a800a4d83dc5621500189ae7b8ac42a0168ba12715885400626b9ae2b10a805a2e841c5621500149d0638ac42a0029360c715885400535400e2b10a800a69801c5621500149d07b82c42a0029360f705885400626b9ee0b10a805a2c845c1621500189ae6b82c42a0168ba10705885400527418e0b10a800a4d831c162150014cd02382c42a00299604705885402d1d420e6b00a800a6a821cd60150014d30439ac02a0029ca04735805400538c08e6b00a800a5a839c960150014b307392c02a0168e211725805402d1d420e4b00a800a5a831c960150014b306392c02a0029ca04725805400538c08e4b00a805a3a849c560150014b706b8ac02a0029620d715805402d1d420e2b00a800a5a831c560150014b30638ac02a0029aa08715805400534c10e2b00a800c4e835c86550c0189b06b90caa1802936085498e520052cc00a931ca400a4d8215163948014b3002a2c7290025360a731915202e1a322e3a1aa407c4e7458d529080f898e8b1aa5210031358f7054a4200592c08e8a928400b29801d1525080b47108baac0210170b991721533200616b22e42a66405c3a645c054cc801872c8b80a99902345151719933203e62b12e3326640094d821d564cc811a1cc8b90a99900343591721533204687a0ae42a66408d1a645c054cc801a32c8b80a99902346d0
  | 4 => 0x4495206afac6a20000000391000000a3ac6630b2aa990f3b4800378df9e86139c5685a002f4391c6b83da2832e002987f19e7108ec309466a5e90136a6800b6ba6c0050e78000009268b7a9c800dcb94858ec6d94c00000d60003980012000042cc4c03000000063506e9e43838295020b2222618c0728ae001a891b984d000f4052c087a2f8bce431e18b36012b278046c42d2e58c8ddb64b89a0409562b34a35bb8808009411e721545a3d6090a81d290501085422486a0ad1a2e3338e65a940e81c96360f511449386268c410a68c116e8115e3510a5f13c1c06422800d9a6a48bd8f02f8981cc031ee938388cbb0b3abc3d85c510e200000cd0006a9288f000daa706921437000748000000000000000e8928b0d69e2b524c0011c2e92e58b4eeb000a7aa8bd808563aa12a2681a7a6d27c0015c79800001ce152e452baee2b8c002fcbb1da831d6a1b0e60104029bcad25a518900004c11082e88008c000cf04000000052381d8286b3067d0fc98978b631c3c080002120f308ad9c000188f29828e964d328426066f1138b9b80298da4b09c7a96ad722828822db04e1c8342e33225a762323474318ae0d83e3a8a0a36c98c2c8800ce8007b13e8fa00ae800baa8a772081a9b02d800001fecf800ed8ee468caa9a5243000ac000ba0560007c4ca6e64b929d1d49e24246
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd9602884123e2478428001063a807002e00c8b0a34e003084a80267880c00680004800191148c3940400cc200247001440f40e94e1d735885403e03211735c162150012499220d715805403e411d181d0d524c80f50894609701513203e429d180153624c80f90474606645493203d42251855c0424c801c4152585701853203e032117654932d04019058360572151410054424d815c054504012259815162504310058864054589410c4014319715141580310058864854505600c40170190151325052103e8119181109325400fa0864600424c95003d03251764cb215400f40c945d5735884003e0321176549321000f60494549325844003c8325186549328c00f40c94595739092003e8219180151324800f40c945d532d852003d03251764c9504800f60894595329012003d1225d654c9404800f20c94619524ca1000413660545c86344001449901517218d10004856605418d4144001605921506350510005846405418d4144001a04546086350510
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x840002501a224d815c05450401102d48a8c10c6a0a2000a80680546086350510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x1
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0xccd
  | 8 => 0x170d
  | 9 => 0x15cd
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 68
  | 6 => 1812
  | 5 => 2235
  | 4 => 494
  | 3 => 37
  | 2 => 3
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
  | 7 => packedAt gbK7 (1922+((h/22+packedAt gbK7 (1768+(h % 22)*7) 7) % 82)*8) 8
  | 6 => packedAt gbK6 (74292+((h/604+packedAt gbK6 (67044+(h % 604)*12) 12) % 3501)*12) 12
  | 5 => packedAt gbK5 (116220+((h/745+packedAt gbK5 (107280+(h % 745)*12) 12) % 2683)*13) 13
  | 4 => packedAt gbK4 (30786+((h/164+packedAt gbK4 (29146+(h % 164)*10) 10) % 593)*10) 10
  | 3 => packedAt gbK3 (2662+((h/12+packedAt gbK3 (2590+(h % 12)*6) 6) % 45)*7) 7
  | 2 => packedAt gbK2 (245+((h/1+packedAt gbK2 (243+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe1fc3f8c31e383fc3f81fe0ff022678474cf
  | 1 => 0xf0fe1fc3f03e3c0387c3fe0ff0f0c5999a4b33
  | 2 => 0xff001ffc7fc03ffc07fc000fff09061e638c3c
  | 3 => 0xffffe0007fffc00007fffff0000e07e07c0fc0
  | 4 => 0x7ffffffff8000000000ff8007ff000
  | 5 => 0xffffffff8000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x220240480004080c004808204402022801045
  | 1 => 0x204208412012241110412804c0a0c0890a4112
  | 2 => 0x551112a81640094806a804292a090614208c28
  | 3 => 0x999542205ea4802827325560220e0740740e80
  | 4 => 0x6939323230001840402248005f6000
  | 5 => 0xeef99f3202000040422061818ccdb7ff800000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xffffeee8fefaeee8ffffeee8fefaeee8ffffeee8fefaeee8ffffeee8fefaeee8ffffeee8fefaeee8ffffeee8fefaeee8ffffeee8fefaeee8ffffeee8fefaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_11924
namespace PEqualNP.Outside.L_meta_11924
open PEqualNP.Outside.L_meta_11924.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
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
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 1 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 5 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
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
theorem bgb_2_0 : Interval gbAtlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 3 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 37 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_480 : Interval gbAtlas 4 480 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 494 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 bgb_4_480))))
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
theorem bgb_5_2208 : Interval gbAtlas 5 2208 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2235 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))))) (concat (concat (concat (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344))) (concat (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))))) (concat (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))))))
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
theorem bgb_6_1664 : Interval gbAtlas 6 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1696 : Interval gbAtlas 6 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1760 : Interval gbAtlas 6 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1792 : Interval gbAtlas 6 1792 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1812 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 68 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 6 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 4 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffeeeeffffeeeeffffeee8fefaeee8ffffeeeeffffeeeeffffeee8fefaeee8ffffeeeeffffeeeeffffeee8fefaeee8ffffeeeeffffeeeeffffeee8fefaeee8
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
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
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
def posted (x : Fin 7 → Bool) := decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_11924.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,3]⟩,⟨.and,[7,5]⟩,⟨.or,[0,1]⟩,⟨.or,[9,2]⟩,⟨.or,[4,6]⟩,⟨.and,[10,11]⟩,⟨.or,[0,6]⟩,⟨.or,[4,5]⟩,⟨.and,[13,14]⟩,⟨.or,[8,12]⟩,⟨.or,[16,15]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_11924

open PEqualNP.Outside.L_meta_11924 in
theorem PEqualNP.Outside.L_meta_11924 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
