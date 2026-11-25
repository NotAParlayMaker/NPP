import PEqualNP.Defs

-- The live-wire checker and smaller graph bounds are adapted from project proofs L_meta_1667
-- and L_meta_1677, distributed under Apache-2.0. At the root, restriction bounds, truth-table
-- comparisons and conflict cliques exclude successor circuits up to graph automorphism.
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_670.Projection
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
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

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

private lemma extract {u target} (gs : List Gate) (w : List Sig)
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

private lemma b_read (i) (w : List Sig) (j : Nat) :
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

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
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

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem raw_modes (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ u k S, k ≤ (if u then 14 else 15) ∧ Live u graph k S ∧ ∀ a ∈ S, a ∈ inputs := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply bit_ext
    intro r
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 15 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 14 else 15) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode
  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph=false := by decide +kernel
  rw [nrm_id pg] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k,S,hk,run,hs⟩ := extract C.gates inputs legal mono graph_proper targetIn
  have ns : inputs.all plainWord=true := by decide +kernel
  rw [nrm_map ns] at hs
  exact ⟨u,k,S,by omega,run,hs⟩
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
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
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

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let hi := ((mask/512-1) >>> (4*i)) &&& 15
    let r := if mask >= 512 then (if hi = 0 then 0 else 1 <<< (hi-1)) else if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
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

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


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


abbrev Bits := BitVec 127
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 127 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 127 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 127 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 127 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 127) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 127) (j : Fin 9) :
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
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 127) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 127) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 127 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 127) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 127 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 127) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 127) (hq : chartSamples m q = 0) :
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
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

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
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

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
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 127) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^128*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^128 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<128 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<128 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<128 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 127) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (128*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^128)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 128*(i+1)-128=128*i := by omega
      have ge : ¬128*(i+1)<128 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 127 = (a==BitVec.allOnes 127) := by
  by_cases h : a=BitVec.allOnes 127
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^127-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^127 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (128*i) =
      (f xs[i]==BitVec.allOnes 127) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^128*u+x+(2^128*v+1)=2^128*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^128 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬128*(i+1)+127<128 := by omega
      have di : 128*(i+1)+127-128=128*i+127 := by omega
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

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 128) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (128*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 128) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
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

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (packedAt data (i*(len+(selected g.mask).length+depth)) (len+(selected g.mask).length+depth)) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 127 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 127
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
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
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

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
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
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
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

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
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def witPairs (m : Nat) (rs : List Nat) : List (Sig × Row × Row) :=
  ((selected m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def fullOK (m : Nat) (rs : List Nat) : Bool :=
  let xs := witPairs m rs
  checkEssential (graphGoal m) (varsX m) xs && (xs.map Prod.fst == vars m) &&
    properB (graphGoal m) && decide (varsX m = vars m ++ [typeWord (m/512-1)])
theorem full_split {u} {m : Nat} {rs : List Nat} (ok : fullOK m rs = true) {k : Nat} {S : Finset Sig}
    (h : Live u (graphGoal m) k S) (sub : ∀ v ∈ S, v ∈ varsX m) :
    S=(vars m).toFinset ∨ S=(varsX m).toFinset := by
  simp only [fullOK,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (varsX m) v sub r s hd hi
  have mem : ∀ v, v ∈ varsX m ↔ v ∈ vars m ∨ v=typeWord (m/512-1) := by
    intro v; rw [hX]; simp
  by_cases hs : typeWord (m/512-1) ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases (mem v).mp hv with hv | rfl
    · exact rest v hv
    · exact hs
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases (mem v).mp (sub v hv) with hv | rfl
    · exact hv
    · exact absurd hv hs
theorem strong_full {u} {m q cap : Nat} {rs : List Nat} (ok : fullOK m rs = true)
    (e : graphGoal m = graphGoal q) (ev : vars m = vars q)
    (a : Impossible u (graphGoal q) cap (vars q).toFinset)
    (b : Impossible u (graphGoal q) cap (varsX m).toFinset) :
    Lower u (varsX m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [fullOK,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.1.2) (essential_plain ok'.1.1.1).1 (essential_plain ok'.1.1.1).2 hr ha
  by_contra! small
  rcases full_split ok run hs with h | h
  · rw [ev] at h; rw [e,h] at run; exact a k (by omega) run
  · rw [e,h] at run; exact b k (by omega) run
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,1,0,0,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[((-0x7),0x30),((-0x21),(-0x33)),(0x26,0x2),(0x38,0x38),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : List ColumnInfo := []
def g15autos : List (List Nat) := [[],[48,33]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
theorem graphPieces (g : Forest) (p : Nat → Nat) (c a : Nat)
    (samples : chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 127 := by decide +kernel)
    (zeros : chartSamples g.mask (fun j => (g.samples j).2) == 0 := by decide +kernel)
    (cols : listPieces (fun v => colCheck g.mask v p) g.cols c := by
      simp only [listPieces]
      repeat' apply And.intro
      all_goals decide +kernel)
    (autos : listPieces (fun x => autoOK (targetOf g) (x.map swapRows)) g.autos a := by
      simp only [listPieces]
      repeat' apply And.intro
      all_goals decide +kernel) : graphValid g p=true := by
  simp only [graphValid,Bool.and_eq_true]
  exact ⟨⟨⟨samples,zeros⟩,listPieces_all cols⟩,listPieces_all autos⟩

set_option maxHeartbeats 0 in
theorem geomg15 : graphValid g15 (boundsBefore []) = true := graphPieces g15 (boundsBefore []) 0 0
def spanChecks (g : Forest) (k : Nat) : Nat → List (Nat × Nat × Nat) → Prop
  | _, [] => True
  | i, (n,a,d)::xs => cells g k i n a 0 d ∧ spanChecks g k (i+n) xs

theorem spansBlock (g : Forest) (k i : Nat) (xs : List (Nat × Nat × Nat))
    (ok : spanChecks g k i xs := by
      simp only [spanChecks,cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals first | exact True.intro | decide +kernel) :
    block g k i (xs.map Prod.fst).sum = true := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨n,a,d⟩ := x
    exact block_merge (cellsBlock ok.1) (ih (i+n) ok.2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact spansBlock g15 3 0 [(1,4,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (vars 15) (graphGoal 15) 4 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g15) (i:=0) rfl rfl (before_sound [] baseKnown) geomg15 tablesg15 (by decide +kernel))
def known15 := extendKnown [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known true known15 := extendKnown_ok (m:=15) baseKnown low15 (by decide +kernel)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,0,0,0,0,g31d6)
def g31h6 (i : Nat) : Nat := 0x30be670208000065000016357504004755c084
def g31d5 (i : Nat) : Nat := 0x40828fd20fd10
def g31l5 : Packing := (2,1,3,0,0,3,0,g31d5)
def g31h5 (i : Nat) : Nat := 0x300
def g31d4 (i : Nat) : Nat := 0x5dd4520
def g31l4 : Packing := (1,2,3,0,0,0,0,g31d4)
def g31samples : Array (Bits × Bits) := #[(0x2e44,0x2c52),(0x5a8a,0x5208),((-0x4b09),(-0x5f39)),((-0x3087),0x4f30),(0x718c,0x108c),(0,0),(0,0),(0,0),(0,0)]
def g31columns : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def g31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def g31levels : Nat → Packing
  | 6 => g31l6
  | 5 => g31l5
  | 4 => g31l4
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 15 3 9 1 4 g31h6
  | 5 => lookupWord 1 3 1 9 1 4 g31h5
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
set_option maxHeartbeats 0 in
theorem geomg31 : graphValid g31 (boundsBefore known15) = true := graphPieces g31 (boundsBefore known15) 0 1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g31 4 0 [(1,5,0)]
  · exact spansBlock g31 5 0 [(2,6,0)]
  · exact spansBlock g31 6 0 [(1,5,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (vars 31) (graphGoal 31) 7 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g31) (i:=0) rfl rfl (before_sound known15 valid15) geomg31 tablesg31 (by decide +kernel))
def known31 := extendKnown known15 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known true known31 := extendKnown_ok (m:=31) valid15 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (vars 47) (graphGoal 47) 5 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known31) (before_sound known31 valid31) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known47 := extendKnown known31 5 [(61,[50,65]),(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known true known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (graphGoal 55) 5 := plain_low (hints:=257) (by decide +kernel) (cut_root (prior:=boundsBefore known47) (before_sound known47 valid47) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known55 := extendKnown known47 5 [(55,[]),(59,[50,65]),(103,[82,98,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known true known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (vars 63) (graphGoal 63) 8 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known55) (before_sound known55 valid55) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def known63 := extendKnown known55 8 [(63,[]),(95,[101,66,16]),(159,[117,101,67,32]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16]),(492,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known true known63 := extendKnown_ok (m:=63) valid55 low63 (by decide +kernel)
def g111d6 (i : Nat) : Nat := 0x7213f
def g111l6 : Packing := (1,0,2,0,0,0,0,g111d6)
def g111h6 (i : Nat) : Nat := 0x8000
def g111d5 (i : Nat) : Nat := 0x17e51
def g111l5 : Packing := (1,1,2,0,0,0,0,g111d5)
def g111samples : Array (Bits × Bits) := #[((-0x13b1),0xc46),((-0x2ccd),(-0x2def)),(0xc9e,0x88e),(0x34e4,0x3460),(0,0),(0x38f8,0x30b8),(0x3fa0,0x2da0),(0,0),(0,0)]
def g111columns : List ColumnInfo := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def g111autos : List (List Nat) := [[],[32,83]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | 5 => g111l5
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 g111h6
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
set_option maxHeartbeats 0 in
theorem geomg111 : graphValid g111 (boundsBefore known63) = true := graphPieces g111 (boundsBefore known63) 0 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g111 5 0 [(1,6,0)]
  · exact spansBlock g111 6 0 [(1,6,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (vars 111) (graphGoal 111) 7 := plain_low (hints:=16785665) (by decide +kernel) (index_root (g:=g111) (i:=0) rfl rfl (before_sound known63 valid63) geomg111 tablesg111 (by decide +kernel))
def known111 := extendKnown known63 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known true known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)
def g189d7 (i : Nat) : Nat := 0x163441bf
def g189l7 : Packing := (1,0,3,0,0,0,0,g189d7)
def g189h7 (i : Nat) : Nat := 0x42f9f28c08140000000020f801630c00d0
def g189d6 (i : Nat) : Nat := 0x420a3fa41fd10
def g189l6 : Packing := (2,1,3,0,0,3,0,g189d6)
def g189h6 (i : Nat) : Nat := 0x18000
def g189d5 (i : Nat) : Nat := 0xb7d8d20
def g189l5 : Packing := (1,2,3,0,0,0,0,g189d5)
def g189samples : Array (Bits × Bits) := #[((-0xaabe9),(-0xb9bad)),(0,0),((-0x39f09),0x44076),((-0xf4435),(-0xfc577)),(0xf8724,0xb8124),(0x21bb8,0x1ba0),(0,0),(0xbec28,0xba408),(0,0)]
def g189columns : List ColumnInfo := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def g189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def g189levels : Nat → Packing
  | 7 => g189l7
  | 6 => g189l6
  | 5 => g189l5
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 9 13 2 9 1 4 g189h7
  | 6 => lookupWord 1 3 1 9 1 4 g189h6
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
set_option maxHeartbeats 0 in
theorem geomg189 : graphValid g189 (boundsBefore known111) = true := graphPieces g189 (boundsBefore known111) 1 2
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g189 5 0 [(1,6,0)]
  · exact spansBlock g189 6 0 [(2,7,0)]
  · exact spansBlock g189 7 0 [(1,6,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (vars 189) (graphGoal 189) 8 := plain_low (hints:=536879876) (by decide +kernel) (index_root (g:=g189) (i:=0) rfl rfl (before_sound known111 valid111) geomg189 tablesg189 (by decide +kernel))
def known189 := extendKnown known111 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known true known189 := extendKnown_ok (m:=189) valid111 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (vars 127) (graphGoal 127) 9 := plain_low (hints:=16785665) (by decide +kernel) (cut_root (prior:=boundsBefore known189) (before_sound known189 valid189) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))
def known127 := extendKnown known189 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known true known127 := extendKnown_ok (m:=127) valid189 low127 (by decide +kernel)
def g191d10 (i : Nat) : Nat := 0x8201ff
def g191l10 : Packing := (1,0,5,0,0,0,0,g191d10)
def g191h10 (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def g191d9 (i : Nat) : Nat := 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def g191l9 : Packing := (12,1,5,0,0,10,0,g191d9)
def g191h9 (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def g191d8 (i : Nat) : Nat := (if i<1 then 0x50b30a062068860c1071620828188001141c88038918b140c61c40b1a0821c49040b10a18885a12900e2468610b144063043858908b143122d10c2a20e20596046182c82c608322160c8246088071094438590503146400c68a00c1a1022c6305831c01630640389281160c82460840710c140c6090090e404803892100e1864038618c162401c48c60b160180d111103182838b1239014302141c48b3a5181c5091708320507124c195160c316314389160c90448d187120c6110890e34514481802c80858c1c1041c48b281142c624708082122c8246892c61458c2b0610e2c48e44a0c1c5a2065c02c60d3011630900487244022858c10714310040020e2cc1c4884930e0c81c48b280ca8848b18a062002438c50b10c1620e2470c62616044871e70a1c08a2250e2c5421260c1d08b262102c626102022859800f12308301250228a0048b18c1621898487020210b4051306022161ce1858a1930e0c61c00d160ca0458a1c1121c1920890e0c8083a1122ca0500b0624a0a007244181c482424459c607122c82c087120cb00007164140c48060a1240e251001628c306c54c090413820f044901871630c3c38c2458d8309030a1a24597160142c9badb87b53b11aebaa9a75a41a0d9cb9a59559218df8b989385f82b7db79977373170b6e56a367d6496155e15ad5795535114eb4c549144f40d3d93a537f34b3252e32691fd1831330e30a106d02afdaf98f64f14ee0ebae78e52e2cd96d46d12cd0c8ec5ac26bc8ba2b60b10adcab6a82a5ca36a029969548f68b48808227e079075c7366bc65061c5e85985645224e04904403fe3923503002be2982561f818c14a1160d4092042001ff54930ffaa0a07fd71483feb1c21ff50120ffcc5207fd52503fe98221ff58e20ffac0987fd1058ffeb9a41ff58640ffa60907fd72443fe882a7ff50910ffee2907fd2058ffe98c41ff54131ffa20907fd21903feb1281ff48153ffa42a07fe72443fe90c41ffdcd20ffa65087fd32883feb0c61ff8ca10ffa43187fd2158ffeb9a21ff54931ffac098ffd62903feb1461ff58931ffac0a07fd204c7fa38a417f5c520bfae5107f920842ffb9281fddc520ff221105fd75902feb88417fdd110fba60b1fdd324c6feb94617f5ce10bfee0a9dfd7054efebac61fdc8610bfee2907f910482ffb9263fd48531bfee2b1fbf744c2ffbb2617f5c163bfaed185ff71502ffb92217f5c553bfae9105fd76902feb9c417f5cc20bfee2a9dff704c7dea14817f5ca10ff260905ff7258fee982637fdd531fea63087dd3054efeb92637f5c131bfae2b1dff724c2ffbb2817fdcd10ff261105fd718c2feb8c817fdcd20bfeeaa05ff7058efeb9a41fe48230bfae3107dd3258efeba4217fdd530bfee2987f5514c6feb94817f5c963bfeec98df771482eeb9c416fdd130 else 0x10410e24)
def g191l8 : Packing := (113,2,5,0,0,12,0,g191d8)
def g191h8 (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def g191d7 (i : Nat) : Nat := 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def g191l7 : Packing := (116,3,5,0,0,11,0,g191d7)
def g191h7 (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def g191d6 (i : Nat) : Nat := 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def g191l6 : Packing := (12,4,5,0,0,6,0,g191d6)
def g191samples : Array (Bits × Bits) := #[((-0x25717e20b9b65b515fc0cad),0x1a8209cc44085084a802052),((-0x1aaf9d8422ea7615c7e9ef1),(-0x1aaf3fdc477b7694ebeaef7)),(0xb876f0435535c500a8ea8c,0x2872300045166108a00a84),(0x2669d0fd182653b341a80c0,0x2428c0bdd82211a84129140),(0x1554172223bd2f53d4f48e0,0x15416022395ae5314d4aa0),(0x253ba08288d622045549630,0x2509e022805626105509220),(0,0),(0x38f01c59fba0814d3746c20,0x18701c597ba0892d2056500),(0,0)]
def g191columns : List ColumnInfo := [(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]
def g191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def g191levels : Nat → Packing
  | 10 => g191l10
  | 9 => g191l9
  | 8 => g191l8
  | 7 => g191l7
  | 6 => g191l6
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 16 41 5 10 4 2 g191h10
  | 9 => lookupWord 67 277 6 13 7 2 g191h9
  | 8 => lookupWord 100 251 6 13 7 2 g191h8
  | 7 => lookupWord 4 19 2 10 4 2 g191h7
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
set_option maxHeartbeats 0 in
theorem geomg191 : graphValid g191 (boundsBefore known127) = true := graphPieces g191 (boundsBefore known127) 3 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g191 6 0 [(12,7,0)]
  · exact spansBlock g191 7 0 [(13,7,0),(18,8,0),(18,8,0),(18,8,0),(18,8,0),(18,8,0),(13,8,0)]
  · exact spansBlock g191 8 0 [(3,7,0),(18,8,0),(18,8,0),(18,8,0),(13,8,0),(18,9,0),(18,9,0),(7,9,0)]
  · exact spansBlock g191 9 0 [(12,8,0)]
  · exact spansBlock g191 10 0 [(1,7,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (vars 191) (graphGoal 191) 11 := plain_low (hints:=536879361) (by decide +kernel) (index_root (g:=g191) (i:=0) rfl rfl (before_sound known127 valid127) geomg191 tablesg191 (by decide +kernel))
def known191 := extendKnown known127 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(431,[113,129,97,82,32,65,48]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known true known191 := extendKnown_ok (m:=191) valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (vars 251) (graphGoal 251) 8 := plain_low (hints:=1358970881) (by decide +kernel) (cut_root (prior:=boundsBefore known191) (before_sound known191 valid191) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def known251 := extendKnown known191 8 [(251,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known true known251 := extendKnown_ok (m:=251) valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (vars 255) (graphGoal 255) 12 := plain_low (hints:=553656577) (by decide +kernel) (cut_root (prior:=boundsBefore known251) (before_sound known251 valid251) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def known255 := extendKnown known251 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known true known255 := extendKnown_ok (m:=255) valid251 low255 (by decide +kernel)
def g383d12 (i : Nat) : Nat := 0x1840804ff
def g383l12 : Packing := (1,0,6,0,0,0,0,g383d12)
def g383h12 (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def g383d11 (i : Nat) : Nat := 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def g383l11 : Packing := (6,1,6,0,0,9,0,g383d11)
def g383h11 (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def g383d10 (i : Nat) : Nat := 0x2e1d818587821e221614a130f091146478584c0c3c2c10b0a7088561608c040207a04c442860211d1a16112300a10082e1c61311850b0a4746c2c1058458988a3028223838785a5041d141418442a102d2088a0a12225460ac2c10805040f40583c282820b0a1c4c45191c1c4824e230c8c09820a901e8c30705040d0e3618222878514342c181c14442810482548c140e0b08166420584040b0a30885c282a3030203e08a072c1610102428b860a11821e1464106058707110b382838984902d1c1d18284824e230c8c0e201c1670947074642040a0f0b4e183a3022286871d083210102c28c861e0f818409821c149061607c10ac2110440306e0e102e1e00585261c18170708242c1100c140a08406050d0ac1080438303848582821818242f042010c0f840a23821408711c2060407c3c0c10a0f503606183e08206e10587291c1814370b04281108e0d878209840b801412a07050418804020c561f04108080a20504121e003e160821ac3aa6695281e74a5d64a236e2ba1a60b1fbdea9dd5d21bcdaf9a258b17fd7296355a14ad3b92851910bcf88e74d40c2cb98aa49d08fc8086b456044c2f828421017c1280d4003ff5c530ffd73443ff5c130ffd73043ff1cc10ffd73843ffa0d10ffd718c3ff9c430ffd30443ff1ce10ffc83443ffcc110fff814c3ffa0530ffe718c3ff4c610ffd318c3ff9ce10ffe318c3ff60530ffd710c3ff1c430fff83443ffcc610ffd83443ff20530fff718c3efe1130ff9708c2ff60d10bfd818c2ff60c10bfd838c2ff60610bfd810c2ff61e30ff9704c2ffe0530bfd83842ffe0d10bde83042bf61830bed828c2fb60810bdd83042efe1130
def g383l10 : Packing := (47,2,6,0,0,12,0,g383d10)
def g383h10 (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def g383d9 (i : Nat) : Nat := (if i<1 then 0xb102c382e18141e0b0515081b05844813238441e0b28448e13e08641e68382b080b205c2c0a1814320a1f08220f1817080b05100a17058c081a0c8c160a1210200b0890220a14101e2a30128a0e230b820f0510240a048f81c10782c145e083b0a0a0214100fe082808592d490e4231f18e446c63231688a8c4ea2230fa871c33216b09e843c15606b0037f63ee9f46f8c7b63d0de34ef1768baa1d10e6871fb8a1c10ddf6dfb6a1afed5f6a4347d9fecd665b327d8fec6861fb0a1822bf15e8aee9710b685a8ac7d5fead655faa354c8a294fba75d35c98e4bba53926e920484a35d15c897437213905c7fc3ee1f14f1476139c1bd0da86b434a1964c846102f39740b4e5902b39540a6051927c934096049023390f883c3e31e60eb072a37e1af0d1c6602fe16a8a8c4d023f10f87fc3be1b60cb05d82be13608f84201be0b604b0190064000dfeb8b07186ff60573843f7f08b8a61bfc7360610bfecb902986ff606738437fb0fc1a21bff874c110bffcbb06885ffe5d304437fb0e98c217fd9720d10bffcba63085ff65f30442ffb2fc1a217fd97a0d10bfecbe63084ff66173443bf2e1b8c613fd981cc109fe4c2e6884ffe61730427fb30388613fc985c530ddfca307184ffe45878c27fb30b9821bed828c6309ffcbb06085fbe4983442efb2a40a61fd9315c130deec1a63085fe64073842dff2cb88613fd985c130dfb38b02187dee55708c27fb2fc0a61bf581e0530def41f06884ff66173842f7f28c0a61bf57160430bdeca502986f7e0f304427fb3039c21afd91618309fecc6e3185fee41318c27ff2ec1a21bee7360810ddfca307085fee41318437bb2ec18217df935c1309ffcbb07086ef247844c37bb07c1a2177d959c430bfcc8463186fb60a718c27fb3138c61bdd835cc10bfcc80e6084ffa61734427fd30b8a613ff9760630df6cbb05185bf65b318437dd22c1461fd8935c130df6c8b05186f725d830437dae6c10213ff985c630df6c10e6086fbdcd82042feb2398221bed825c630ddf48f08986efe47844c377f08c0a617f5911ce10fddc22e0986efe11704c35fb0cb8861bed9360a30bdeca0e2186efe11714c37f730b84616ff965c630df6c16e3186fda07814c35fb0d38861bdf9760c10bf7c9302986f760c834427fb3138861bf581205309fecc4e7084ff65d810c27ff30b9c217f990dc630dfcc1ae1186fd605318c27ff2ec08617bf944c110ddfc2702985fee41834427fb3198c21bdd83cc610ddfc2502985fe643318435fd22c3061bef9260d109fecc2e3185df65683442efb2b982217ef924c610def4bb06086fb609318c3fb662b82617ef924c6309ffcc2e2186fba5d828c3faa63c0a619fd875c6309fecbf06886f7e0d3044377f0840a61bbd91e11309fecc463184fbe498344277f28c1c213bf9460e30 else 0x730608110514260a15041e8407028a0f1182c7c30505c2240382841342a1060e054102240482c411050a0a840b04480b04881e0410241620582440905881e04103c0a0405828a0b05058605040102e0e284c12202828082509942609105c1c202038143058142c0a203c16110511080404828804050447470503c164e18381e3e083c14342010160a203c2c2c204416308810140f211412111844342e1090220f2010160a182416208810140f2010420a1c10081105900821050c160f101c1c0f182416202858160a202c142088284c6070646040703c60a058a0b040e0581450203c14305038407050118a0e2810160a19140a090890120a102c140411864a090882824442a10081c0b028c0a0c0202e0f28441409183c0a0b07101211090c141910470c0e0590162210441e20902c505020142c0a2c1042208290161c1014080e0b918e1a0b8c2304058e8219420281656283c1430785041fa17068a0f05188c060702c9c1038281e4e17040e0aa28101e70805c163040501430284c123e07081dc107828c13088a0c0508e101650ad60140b20281e202114121120281c2e1f041e0a211c162048442430503c404070287040d8441640f04c1e34202c143e081c140f2210080b05101211090f85c18e810140f303c282020641630785040f0a0a8a0f050c1e0)
def g383l9 : Packing := (136,3,6,0,0,13,0,g383d9)
def g383h9 (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def g383d8 (i : Nat) : Nat := 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def g383l8 : Packing := (53,4,6,0,0,9,0,g383d8)
def g383h8 (i : Nat) : Nat := 0x834601a000
def g383d7 (i : Nat) : Nat := 0xa295fdb2e3ca3070852bfb65c79460e30
def g383l7 : Packing := (2,5,6,0,0,3,0,g383d7)
def g383samples : Array (Bits × Bits) := #[((-0x27814e7911717559e36ffe97),(-0x2795ee7dfbd7fe5efd6ffeb7)),(0x27b16fe31adb2d3474067090,0x22906c1518960818c4045090),(0x3f608048c4681557416c081e,0x1d608040c429154701680804),(0xce772a993e34c9ba0a86de,0x7752a10062a80ba0284da),(0x3790ca05a4c0c06e80091ee0,0x27908a05a0c0c04e00091a20),(0x3874c794087160298718700,0x3854c784087160298418600),((-0x3698fad73ade8d59dc7c07ff),0x9670168c52132a62281a800),(0,0),((-0x3e7656eccaf9e74b80267ff),(-0xbe77d7eddaf3ea6fac3efff))]
def g383columns : List ColumnInfo := [(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]
def g383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def g383levels : Nat → Packing
  | 12 => g383l12
  | 11 => g383l11
  | 10 => g383l10
  | 9 => g383l9
  | 8 => g383l8
  | 7 => g383l7
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 8 37 4 10 3 3 g383h12
  | 11 => lookupWord 48 123 4 13 6 3 g383h11
  | 10 => lookupWord 79 299 8 15 8 3 g383h10
  | 9 => lookupWord 39 99 5 13 6 3 g383h9
  | 8 => lookupWord 1 5 1 8 1 3 g383h8
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxHeartbeats 0 in
theorem geomg383 : graphValid g383 (boundsBefore known255) = true := graphPieces g383 (boundsBefore known255) 3 1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesg383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock g383 7 0 [(2,8,0)]
  · exact spansBlock g383 8 0 [(18,8,0),(18,8,0),(8,8,0),(9,9,0)]
  · exact spansBlock g383 9 0 [(3,8,0),(18,9,0),(18,9,0),(18,9,0),(18,9,0),(18,9,0),(18,9,0),(8,9,0),(17,10,0)]
  · exact spansBlock g383 10 0 [(6,8,0),(13,9,0),(18,10,0),(10,10,0)]
  · exact spansBlock g383 11 0 [(6,9,0)]
  · exact spansBlock g383 12 0 [(1,8,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower true (vars 383) (graphGoal 383) 13 := plain_low (hints:=12901687553) (by decide +kernel) (index_root (g:=g383) (i:=0) rfl rfl (before_sound known255 valid255) geomg383 tablesg383 (by decide +kernel))
def known383 := extendKnown known255 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known true known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
theorem validF : Known false known383 := known_down valid383
def x31d6 (i : Nat) : Nat := 0x1a230180fd10fc20
def x31l6 : Packing := (2,1,2,0,0,4,0,x31d6)
def x31h6 (i : Nat) : Nat := 0x104451000a0200202082101c0c0071400
def x31d5 (i : Nat) : Nat := 0x613110000e3d4507e48110bea9a217d53082faa4885f54420
def x31l5 : Packing := (5,2,2,0,0,5,0,x31d5)
def x31samples : Array (Bits × Bits) := #[((-0x3dd),0xac2),((-0xf71),(-0xae7)),(0x2cc,0x8e4),((-0xcad),(-0xcfd)),(0xd3c,0x43c),(0,0),(0,0),(0,0),(0,0)]
def x31columns : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def x31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def x31levels : Nat → Packing
  | 6 => x31l6
  | 5 => x31l5
  | _ => emptyPacking
def x31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 8 11 1 11 3 4 x31h6
  | _ => fun _ => none
def x31 : Forest := ⟨1055,6,fun j => x31samples[j]?.getD (0,0),x31columns,x31autos,x31levels,x31index⟩
set_option maxHeartbeats 0 in
theorem geomx31 : graphValid x31 (boundsBefore known383) = true := graphPieces x31 (boundsBefore known383) 0 1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesx31 : checkedTables x31 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x31 5 0 [(5,6,0)]
  · exact spansBlock x31 6 0 [(2,6,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl31 : Impossible false (graphGoal 1055) 6 (vars 1055).toFinset := plainA (q:=31) (prior:=boundsBefore known383) (before_sound known383 validF) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1567 : Lower false (varsX 1567) (graphGoal 1567) 7 :=
  strong_full (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl31
    (index_root (g:=x31) (i:=0) rfl rfl (before_sound known383 validF) geomx31 tablesx31 (by decide +kernel))
def known1567 := extendKnown known383 7 [(1567,[]),(2079,[50,65]),(6687,[50,33,16,64]),(7199,[66,16]),(1703,[115,67,100,83]),(4263,[114,33,97,82,50,65]),(7847,[115,50,98,83,66,16]),(12455,[113,97,82,32,65,48]),(2361,[131,115,65,50,98,81]),(6990,[131,115,100,50,33,16,80]),(4963,[130,33,113,99,82,65]),(9571,[130,33,50,113,99,82,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1567 : Known false known1567 := extendKnown_ok (m:=1567) validF low1567 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42527 : Lower false (varsX 42527) (graphGoal 42527) 7 :=
  strong_full (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl31
    (index_root (g:=x31) (i:=1) rfl rfl (before_sound known383 validF) geomx31 tablesx31 (by decide +kernel))
def known42527 := extendKnown known1567 7 [(42527,[]),(44063,[50,65]),(47647,[50,33,16,64]),(52767,[33,32,65,48]),(57887,[16,64,49,32]),(42663,[115,67,100,83]),(44711,[114,33,97,82,50,65]),(47783,[114,98,83,33,16,64]),(54951,[113,97,82,32,65,48]),(68775,[113,16,96,81,49,64]),(44345,[131,115,65,50,98,81]),(60217,[129,113,33,98,81,48]),(53070,[130,114,99,49,32,65,80]),(60238,[129,113,98,16,66,49,80]),(42851,[131,50,66,116,99,82]),(44899,[130,33,113,99,82,65]),(50019,[130,33,50,113,99,82,16,64]),(53164,[130,50,116,49,32,97,80]),(60332,[129,50,114,48,66,97,80]),(69548,[129,116,50,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42527 : Known false known42527 := extendKnown_ok (m:=42527) valid1567 low42527 (by decide +kernel)
def x111d6 (i : Nat) : Nat := 0x1040a3fa21fd51
def x111l6 : Packing := (2,1,1,0,0,3,0,x111d6)
def x111h6 (i : Nat) : Nat := 0x40000
def x111d5 (i : Nat) : Nat := 0x102de54110
def x111l5 : Packing := (1,2,1,0,0,0,0,x111d5)
def x111samples : Array (Bits × Bits) := #[((-0x32d),0x742),((-0x791),(-0x773)),(0x304,0x140),(0x322,0x6a2),(0,0),(0x4b4,0xb4),(0x38,0x770),(0,0),(0,0)]
def x111columns : List ColumnInfo := [(96,0,15,0,4),(1,32,78,0,4)]
def x111autos : List (List Nat) := [[],[32,83]]
def x111levels : Nat → Packing
  | 6 => x111l6
  | 5 => x111l5
  | _ => emptyPacking
def x111index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 x111h6
  | _ => fun _ => none
def x111 : Forest := ⟨1135,6,fun j => x111samples[j]?.getD (0,0),x111columns,x111autos,x111levels,x111index⟩
set_option maxHeartbeats 0 in
theorem geomx111 : graphValid x111 (boundsBefore known42527) = true := graphPieces x111 (boundsBefore known42527) 0 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesx111 : checkedTables x111 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x111 5 0 [(1,6,0)]
  · exact spansBlock x111 6 0 [(2,7,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl111 : Impossible false (graphGoal 1135) 6 (vars 1135).toFinset := plainA (q:=111) (prior:=boundsBefore known42527) (before_sound known42527 valid42527) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low49775 : Lower false (varsX 49775) (graphGoal 49775) 7 :=
  strong_full (q:=1135) (rs:=[2, 64, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl111
    (index_root (g:=x111) (i:=0) rfl rfl (before_sound known42527 valid42527) geomx111 tablesx111 (by decide +kernel))
def known49775 := extendKnown known42527 7 [(42683,[117,80,66,96,16]),(47806,[114,83,48,33,97,64]),(69498,[129,33,97,81,16,114,49,64]),(69557,[134,81,114,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid49775 : Known false known49775 := extendKnown_ok (m:=49775) valid42527 low49775 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42607 : Lower false (varsX 42607) (graphGoal 42607) 7 :=
  strong_full (q:=1135) (rs:=[2, 1, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl111
    (index_root (g:=x111) (i:=1) rfl rfl (before_sound known42527 valid42527) geomx111 tablesx111 (by decide +kernel))
def known42607 := extendKnown known49775 7 [(44155,[99,83,64,32,16]),(44219,[115,50,32,83,66,96,16]),(44731,[117,80,66,96,16]),(52926,[114,83,48,33,97,64]),(54974,[112,48,50,33,97,64]),(42711,[115,83,67]),(47838,[101,117,50,33,16,64]),(52958,[99,115,83,48,33,64]),(42739,[82,98,115,66,16]),(44787,[83,80,96,115,64,32,16]),(53054,[130,114,98,49,32,81,64]),(60253,[128,80,117,32,16,98,65,48]),(60282,[129,33,97,81,16,114,49,64]),(44981,[134,81,114,50,65]),(48071,[83,133,115,67,32,96]),(53212,[82,50,133,98,49,32,113,64]),(60408,[49,50,83,48,130,113,64]),(69624,[81,80,48,50,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42607 : Known false known42607 := extendKnown_ok (m:=42607) valid49775 low42607 (by decide +kernel)
def x63d7 (i : Nat) : Nat := 0x344640ac3f865fc10
def x63l7 : Packing := (2,1,2,0,0,4,0,x63d7)
def x63h7 (i : Nat) : Nat := 0x1520079d85d46b7171000680020c0000f391436008009b010
def x63d6 (i : Nat) : Nat := 0x1108482000804c8462023211880840401f7cb4e4b74a0b44658480fb48032fd4c410bf58032bf58c10bf590109f59432be580329f59410bd58432bb58810af59010b758c10
def x63l6 : Packing := (12,2,2,0,0,7,0,x63d6)
def x63h6 (i : Nat) : Nat := 0x24f9400060ba8030352
def x63d5 (i : Nat) : Nat := 0x108421184210872a1e50a03e498240196e52058432cea62b2821b54c1610cb5a98ac8086e53158810
def x63l5 : Packing := (6,3,2,0,0,6,0,x63d5)
def x63h5 (i : Nat) : Nat := 0x20034000
def x63d4 (i : Nat) : Nat := 0x3b04813058432
def x63l4 : Packing := (1,4,2,0,0,0,0,x63d4)
def x63samples : Array (Bits × Bits) := #[((-0xdf61),0x58096),((-0x6639f),(-0x7c79f)),(0x97be,0x2c69c),((-0x7b4b9),(-0x2c6fd)),(0x4c78,0x24468),(0x62f80,0x27f00),(0,0),(0,0),(0,0)]
def x63columns : List ColumnInfo := [(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def x63autos : List (List Nat) := [[],[65,50]]
def x63levels : Nat → Packing
  | 7 => x63l7
  | 6 => x63l6
  | 5 => x63l5
  | 4 => x63l4
  | _ => emptyPacking
def x63index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 7 21 2 9 4 1 x63h7
  | 6 => lookupWord 2 9 1 8 3 1 x63h6
  | 5 => lookupWord 1 5 1 6 1 1 x63h5
  | _ => fun _ => none
def x63 : Forest := ⟨1087,7,fun j => x63samples[j]?.getD (0,0),x63columns,x63autos,x63levels,x63index⟩
set_option maxHeartbeats 0 in
theorem geomx63 : graphValid x63 (boundsBefore known42607) = true := graphPieces x63 (boundsBefore known42607) 0 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesx63 : checkedTables x63 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x63 4 0 [(1,5,0)]
  · exact spansBlock x63 5 0 [(6,6,0)]
  · exact spansBlock x63 6 0 [(7,6,0),(5,7,0)]
  · exact spansBlock x63 7 0 [(2,7,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl63 : Impossible false (graphGoal 1087) 7 (vars 1087).toFinset := plainA (q:=63) (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6719 : Lower false (varsX 6719) (graphGoal 6719) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (6688,0,6687,0,7) (by decide +kernel) (by decide +kernel))
def known6719 := extendKnown known42607 8 [(2143,[101,66,16]),(2425,[128,80,84,66,16,114,97,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6719 : Known false known6719 := extendKnown_ok (m:=6719) valid42607 low6719 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1087 : Lower false (varsX 1087) (graphGoal 1087) 8 :=
  strong_full (q:=1087) (rs:=[16, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (index_root (g:=x63) (i:=0) rfl rfl (before_sound known42607 valid42607) geomx63 tablesx63 (by decide +kernel))
def known1087 := extendKnown known6719 8 [(1087,[]),(2623,[50,65]),(1119,[101,66,16]),(6303,[117,101,67,32]),(11423,[117,101,33,32,65,48]),(6319,[116,100,83,32]),(13487,[113,97,82,32,65,48]),(1207,[115,84,99]),(3255,[114,81,98,50,65]),(1255,[83,82,114,99,66,16]),(18749,[129,113,82,97,48]),(11614,[132,116,84,48,33,96]),(18782,[129,33,114,82,16,66,49,96]),(18798,[128,64,116,49,96]),(1395,[131,84,115,98]),(18809,[128,80,84,66,16,114,97,48]),(11708,[132,67,84,48,33,113,96]),(3555,[83,80,132,115,96,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1087 : Known false known1087 := extendKnown_ok (m:=1087) valid6719 low1087 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low11327 : Lower false (varsX 11327) (graphGoal 11327) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 16, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (index_root (g:=x63) (i:=1) rfl rfl (before_sound known42607 valid42607) geomx63 tablesx63 (by decide +kernel))
def known11327 := extendKnown known1087 8 [(2719,[117,101,67,32]),(13495,[115,84,99]),(3389,[132,116,65,48,80,97,32]),(8542,[132,116,84,48,33,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid11327 : Known false known11327 := extendKnown_ok (m:=11327) valid1087 low11327 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1599 : Lower false (varsX 1599) (graphGoal 1599) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (1568,0,1567,0,7) (by decide +kernel) (by decide +kernel))
def known1599 := extendKnown known11327 8 [(1599,[]),(12463,[113,97,82,32,65,48]),(1719,[115,84,99]),(2365,[132,116,65,48,80,97,32]),(9582,[128,16,113,65,49,33,96]),(4979,[130,50,81,115,98,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1599 : Known false known1599 := extendKnown_ok (m:=1599) valid11327 low1599 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47679 : Lower false (varsX 47679) (graphGoal 47679) 8 :=
  strong_full (q:=1087) (rs:=[2, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (47648,0,47647,0,7) (by decide +kernel) (by decide +kernel))
def known47679 := extendKnown known1599 8 [(47679,[]),(44127,[101,66,16]),(52831,[101,50,33,16,64]),(42671,[116,100,83,32]),(68783,[113,97,82,32,65,48]),(47799,[115,84,99]),(68791,[114,81,98,50,65]),(44349,[132,116,65,48,80,97,32]),(60366,[82,50,133,115,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47679 : Known false known47679 := extendKnown_ok (m:=47679) valid1599 low47679 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42559 : Lower false (varsX 42559) (graphGoal 42559) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (42528,0,42527,0,7) (by decide +kernel) (by decide +kernel))
def known42559 := extendKnown known47679 8 [(42559,[]),(42591,[101,66,16]),(47791,[116,100,83,32]),(54959,[113,97,82,32,65,48]),(42679,[115,84,99]),(44727,[114,81,98,50,65]),(60270,[128,64,116,49,96]),(60281,[128,80,84,66,16,114,97,48]),(69497,[128,81,67,112,97,32]),(48078,[83,133,115,67,32,96]),(69603,[81,80,128,113,98,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42559 : Known false known42559 := extendKnown_ok (m:=42559) valid47679 low42559 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low52799 : Lower false (varsX 52799) (graphGoal 52799) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 8, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (52768,0,52767,0,7) (by decide +kernel) (by decide +kernel))
def known52799 := extendKnown known42559 8 [(44719,[116,100,83,32]),(54967,[115,84,99]),(60239,[131,115,100,50,33,16,80]),(50014,[132,116,84,48,33,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid52799 : Known false known52799 := extendKnown_ok (m:=52799) valid42559 low52799 (by decide +kernel)
def x189d7 (i : Nat) : Nat := 0x8151108090c808420380cd31101fd30fe887f0c3f821fc20
def x189l7 : Packing := (5,1,3,0,0,7,0,x189d7)
def x189h7 (i : Nat) : Nat := 0x74308515c76e77000000818435800000a71f02000000828c06fa8001025909670038579507803705e0482024814000001004000000
def x189d6 (i : Nat) : Nat := 0x10842000421000040820b764a0f19283c280fe48130bf58910bf58430fe54030fe48110bf58930bf594209f59420bb58830bd58430
def x189l6 : Packing := (10,2,3,0,0,7,0,x189d6)
def x189h6 (i : Nat) : Nat := 0x700009040000000000ddd0800002
def x189d5 (i : Nat) : Nat := 0x104208141ba541620c36698ac4186f15058430
def x189l5 : Packing := (3,3,3,0,0,5,0,x189d5)
def x189samples : Array (Bits × Bits) := #[((-0xe77f1),(-0x19ff3)),(0,0),((-0xd9e61),0x2a10e),((-0x9fd8f),(-0x3a7af)),(0x507e6,0x187a2),(0x89c78,0x9870),(0,0),(0x87780,0xd4680),(0,0)]
def x189columns : List ColumnInfo := [(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def x189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def x189levels : Nat → Packing
  | 7 => x189l7
  | 6 => x189l6
  | 5 => x189l5
  | _ => emptyPacking
def x189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 23 29 4 12 4 4 x189h7
  | 6 => lookupWord 2 11 1 10 2 4 x189h6
  | _ => fun _ => none
def x189 : Forest := ⟨1213,7,fun j => x189samples[j]?.getD (0,0),x189columns,x189autos,x189levels,x189index⟩
set_option maxHeartbeats 0 in
theorem geomx189 : graphValid x189 (boundsBefore known52799) = true := graphPieces x189 (boundsBefore known52799) 1 2
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesx189 : checkedTables x189 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x189 5 0 [(3,6,0)]
  · exact spansBlock x189 6 0 [(3,6,0),(7,7,0)]
  · exact spansBlock x189 7 0 [(5,7,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl189 : Impossible false (graphGoal 1213) 7 (vars 1213).toFinset := plainA (q:=189) (prior:=boundsBefore known52799) (before_sound known52799 valid52799) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2237 : Lower false (varsX 2237) (graphGoal 2237) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=0) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known2237 := extendKnown known52799 8 [(2237,[]),(18109,[82,48,66,112]),(2395,[130,114,98,33,81]),(12774,[66,114,50,132,99,32,80,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2237 : Known false known2237 := extendKnown_ok (m:=2237) valid52799 low2237 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1725 : Lower false (varsX 1725) (graphGoal 1725) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=1) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known1725 := extendKnown known2237 8 [(1725,[]),(17085,[82,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1725 : Known false known1725 := extendKnown_ok (m:=1725) valid2237 low1725 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2749 : Lower false (varsX 2749) (graphGoal 2749) 8 :=
  strong_full (q:=1213) (rs:=[32, 8, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=2) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known2749 := extendKnown known1725 8 [(2749,[]),(11453,[117,67,32]),(1371,[130,50,98,82,115,33,65]),(6630,[115,83,82,130,99,66,16]),(13798,[66,114,50,132,99,32,80,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2749 : Known false known2749 := extendKnown_ok (m:=2749) valid1725 low2749 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43197 : Lower false (varsX 43197) (graphGoal 43197) 8 :=
  strong_full (q:=1213) (rs:=[20, 9, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=3) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known43197 := extendKnown known2749 8 [(43197,[]),(58557,[82,48]),(64189,[83,114,64]),(43823,[135,50,65]),(46427,[130,50,98,82,115,33,65]),(48475,[135,101,50,33,16,64]),(49638,[115,83,82,130,99,66,16]),(55782,[117,130,99,32,64,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43197 : Known false known43197 := extendKnown_ok (m:=43197) valid2749 low43197 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44221 : Lower false (varsX 44221) (graphGoal 44221) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=4) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known44221 := extendKnown known43197 8 [(44221,[]),(44733,[84,115]),(52925,[117,67,32]),(54973,[116,83,32]),(58045,[82,48]),(60207,[132,65,48,80,113,32]),(42843,[130,50,98,82,115,33,65]),(44379,[130,114,98,33,81]),(58203,[133,117,101,33,48]),(48102,[115,83,82,130,99,66,16]),(55270,[66,114,50,132,99,32,80,16]),(69606,[80,132,99,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44221 : Known false known44221 := extendKnown_ok (m:=44221) valid43197 low44221 (by decide +kernel)
def x251d7 (i : Nat) : Nat := 0x60bfd31
def x251l7 : Packing := (1,1,1,0,0,0,0,x251d7)
def x251samples : Array (Bits × Bits) := #[(0x4a,0x2),((-0x1fb),(-0xb)),(0,0),(0x34,0xe4),((-0x1c7),(-0xe7)),(0x1c2,0xd0),((-0x1f1),0xa),(0x18c,0x12c),(0,0)]
def x251columns : List ColumnInfo := [(88,0,163,0,4),(8,0,243,0,7)]
def x251autos : List (List Nat) := [[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def x251levels : Nat → Packing
  | 7 => x251l7
  | _ => emptyPacking
def x251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x251 : Forest := ⟨1275,7,fun j => x251samples[j]?.getD (0,0),x251columns,x251autos,x251levels,x251index⟩
set_option maxHeartbeats 0 in
theorem geomx251 : graphValid x251 (boundsBefore known44221) = true := graphPieces x251 (boundsBefore known44221) 0 1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesx251 : checkedTables x251 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x251 7 0 [(1,8,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl251 : Impossible false (graphGoal 1275) 7 (vars 1275).toFinset := plainA (q:=251) (prior:=boundsBefore known44221) (before_sound known44221 valid44221) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low48891 : Lower false (varsX 48891) (graphGoal 48891) 8 :=
  strong_full (q:=1275) (rs:=[2, 80, 16, 10, 1, 2, 32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl251
    (index_root (g:=x251) (i:=0) rfl rfl (before_sound known44221 valid44221) geomx251 tablesx251 (by decide +kernel))
def known48891 := extendKnown known44221 8 [(59646,[116,100,49,81,32]),(43479,[115,83,133,99,50,66,16]),(55773,[99,132,84,48,33,112]),(46581,[67,80,100,131,112,32,16]),(58874,[84,100,49,128,113,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid48891 : Known false known48891 := extendKnown_ok (m:=48891) valid44221 low48891 (by decide +kernel)
def x127d8 (i : Nat) : Nat := 0x1948817fd30
def x127l8 : Packing := (1,1,3,0,0,0,0,x127d8)
def x127h8 (i : Nat) : Nat := 0x8e80
def x127d7 (i : Nat) : Nat := 0x24c269243a037eb0261df54530
def x127l7 : Packing := (2,2,3,0,0,5,0,x127d7)
def x127samples : Array (Bits × Bits) := #[((-0x19eb1),(-0xdfb3)),((-0x1794d),0xc0b2),(0x1145c,0x10448),(0x11ba6,0x7ba6),(0x838,0x8410),(0x6340,0xdf00),(0x8380,0x13f00),(0,0),(0,0)]
def x127columns : List ColumnInfo := [(20,8,99,0,4),(96,0,31,0,7),(16,0,111,0,7),(66,0,61,0,5),(34,64,29,0,4),(1056,0,1119,0,8),(49,0,78,0,4)]
def x127autos : List (List Nat) := [[],[16,66,101]]
def x127levels : Nat → Packing
  | 8 => x127l8
  | 7 => x127l7
  | _ => emptyPacking
def x127index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 1 6 1 1 x127h8
  | _ => fun _ => none
def x127 : Forest := ⟨1151,8,fun j => x127samples[j]?.getD (0,0),x127columns,x127autos,x127levels,x127index⟩
set_option maxHeartbeats 0 in
theorem geomx127 : graphValid x127 (boundsBefore known48891) = true := graphPieces x127 (boundsBefore known48891) 1 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesx127 : checkedTables x127 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x127 7 0 [(2,8,0)]
  · exact spansBlock x127 8 0 [(1,8,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl127 : Impossible false (graphGoal 1151) 8 (vars 1151).toFinset := plainA (q:=127) (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2175 : Lower false (varsX 2175) (graphGoal 2175) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (2080,0,2143,0,8) (by decide +kernel) (by decide +kernel))
def known2175 := extendKnown known48891 9 [(2429,[129,82,113,48]),(7038,[129,98,82,16,66,49,112]),(9598,[128,100,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2175 : Known false known2175 := extendKnown_ok (m:=2175) valid48891 low2175 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1151 : Lower false (varsX 1151) (graphGoal 1151) 9 :=
  strong_full (q:=1151) (rs:=[16, 4, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (1056,0,1119,0,8) (by decide +kernel) (by decide +kernel))
def known1151 := extendKnown known2175 9 [(18814,[129,98,82,16,66,49,112]),(11742,[82,133,99,49,32,65,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1151 : Known false known1151 := extendKnown_ok (m:=1151) valid2175 low1151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low52863 : Lower false (varsX 52863) (graphGoal 52863) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 8, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (52768,0,52831,0,8) (by decide +kernel) (by decide +kernel))
def known52863 := extendKnown known1151 9 [(44925,[129,82,113,48]),(50046,[129,98,82,16,66,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid52863 : Known false known52863 := extendKnown_ok (m:=52863) valid1151 low52863 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44159 : Lower false (varsX 44159) (graphGoal 44159) 9 :=
  strong_full (q:=1151) (rs:=[16, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (44064,0,44127,0,8) (by decide +kernel) (by decide +kernel))
def known44159 := extendKnown known52863 9 [(44159,[]),(47743,[101,66,16]),(69501,[128,84,66,16,98,113,48]),(74110,[128,100,49,112]),(48094,[82,133,99,49,32,65,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44159 : Known false known44159 := extendKnown_ok (m:=44159) valid52863 low44159 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43647 : Lower false (varsX 43647) (graphGoal 43647) 9 :=
  strong_full (q:=1151) (rs:=[10, 1, 2, 5, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (index_root (g:=x127) (i:=0) rfl rfl (before_sound known48891 valid48891) geomx127 tablesx127 (by decide +kernel))
def known43647 := extendKnown known44159 9 [(43647,[]),(46455,[131,84,115,98]),(51063,[131,100,115,82,16]),(43901,[129,82,113,48]),(46461,[128,84,66,16,98,113,48]),(48510,[129,98,82,16,66,49,112]),(51070,[128,100,49,112]),(43423,[134,117,33,32,65,48]),(58811,[84,133,80,66,114,96,16]),(59900,[82,48,66,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43647 : Known false known43647 := extendKnown_ok (m:=43647) valid44159 low43647 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42623 : Lower false (varsX 42623) (graphGoal 42623) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (42528,0,42591,0,8) (by decide +kernel) (by decide +kernel))
def known42623 := extendKnown known43647 9 [(42623,[]),(60285,[129,82,113,48]),(60286,[129,98,82,16,66,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42623 : Known false known42623 := extendKnown_ok (m:=42623) valid43647 low42623 (by decide +kernel)
namespace Clique

def monoBin (d : Bool) (a b : Sig) : Sig := bin (if d then 1 else 0) a b

def Split (p n : Row) (v : Sig) : Prop := bit p v = true ∧ bit n v = false

def Sole (T : Sig) (S : Finset Sig) (p n : Row) (a : Sig) : Prop :=
  Split p n T ∧ ∀ x ∈ S, Split p n x → x = a

def Conflict (T : Sig) (S : Finset Sig) (a b : Sig) : Prop :=
  ∃ p n, (∃ r, Sole T S p r a) ∧ (∃ r, Sole T S p r b) ∧
    (∃ r, Sole T S r n a) ∧ (∃ r, Sole T S r n b)

def Coloring (T : Sig) (S : Finset Sig) (m : Nat) (c : Sig → Nat) : Prop :=
  (∀ a ∈ S, c a < m) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Conflict T S a b → c a ≠ c b

theorem bit_combine (i d) (a b : Sig) : bit i (monoBin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by
  cases d <;> simp [bit,monoBin,bin]

theorem split_inputs {p n d a b} (h : Split p n (monoBin d a b)) : Split p n a ∨ Split p n b := by
  unfold Split at *
  simp only [bit_combine] at h
  cases d <;> cases hpa : bit p a <;> cases hpb : bit p b <;> cases hna : bit n a <;> cases hnb : bit n b <;> simp_all

variable {T : Sig} {U : Finset Sig} {a b : Sig} {d : Bool}
def renWire (a b new w : Sig) := if w = a ∨ w = b then new else w

theorem move_sole {w p n} (h : Sole T (insert a (insert b U)) p n w) (free : w ∈ U → w ≠ a ∧ w ≠ b) :
    Sole T (insert (monoBin d a b) U) p n ((renWire a b (monoBin d a b)) w) := by
  refine ⟨h.1,?_⟩
  intro y hy sy
  rcases Finset.mem_insert.mp hy with rfl | hu
  · rcases split_inputs sy with sa | sb
    · have e := h.2 _ (Finset.mem_insert_self _ _) sa
      simp [renWire,← e]
    · have e := h.2 _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) sb
      simp [renWire,← e]
  · have e := h.2 _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) sy
    subst y
    simp [renWire,(free hu).1,(free hu).2]

theorem move_conflict {v w} (h : Conflict T (insert a (insert b U)) v w)
    (hv : v ∈ U → v ≠ a ∧ v ≠ b) (hw : w ∈ U → w ≠ a ∧ w ≠ b) :
    Conflict T (insert (monoBin d a b) U) ((renWire a b (monoBin d a b)) v) ((renWire a b (monoBin d a b)) w) := by
  obtain ⟨p,n,⟨u,hu⟩,⟨r,hr⟩,⟨s,hs⟩,⟨t,ht⟩⟩ := h
  exact ⟨p,n,⟨u,move_sole hu hv⟩,⟨r,move_sole hr hw⟩,⟨s,move_sole hs hv⟩,⟨t,move_sole ht hw⟩⟩

theorem force_gate {p n w} {k : Nat} (h : Sole T (insert a (insert b U)) p n w) (dropped : w ∉ U)
    (run : Live false T k (insert (monoBin d a b) U)) : Split p n (monoBin d a b) := by
  obtain ⟨x,hx,px,nx⟩ := mono_row_difference run rfl h.1.1 h.1.2
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ⟨px,nx⟩
  · exact False.elim (dropped (h.2 _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)) ⟨px,nx⟩ ▸ hx))

theorem distinct_children {k : Nat} (ab : a ≠ b) (au : a ∉ U) (bu : b ∉ U)
    (run : Live false T k (insert (monoBin d a b) U)) : ¬Conflict T (insert a (insert b U)) a b := by
  rintro ⟨p,n,⟨q,pA⟩,⟨r,pB⟩,⟨s,nA⟩,⟨u,nB⟩⟩
  have am : a ∈ (insert a (insert b U)) := Finset.mem_insert_self _ _
  have bm : b ∈ (insert a (insert b U)) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  cases d with
  | false =>
    have left := force_gate nA au run
    have right := force_gate nB bu run
    have ns : ¬Split s n b := fun h => ab (nA.2 b bm h).symm
    have nu : ¬Split u n a := fun h => ab (nB.2 a am h)
    unfold Split at left right ns nu
    simp only [bit_combine,Bool.false_eq_true,if_false,Bool.and_eq_true] at left right
    cases ha : bit n a <;> cases hb : bit n b <;> simp_all
  | true =>
    have left := force_gate pA au run
    have right := force_gate pB bu run
    have nq : ¬Split p q b := fun h => ab (pA.2 b bm h).symm
    have nr : ¬Split p r a := fun h => ab (pB.2 a am h)
    unfold Split at left right nq nr
    simp only [bit_combine,if_true,Bool.or_eq_false_iff] at left right
    cases ha : bit p a <;> cases hb : bit p b <;> simp_all

theorem conflict_symm {S v w} (h : Conflict T S v w) : Conflict T S w v := by
  obtain ⟨p,n,pa,pb,na,nb⟩ := h
  exact ⟨p,n,pb,pa,nb,na⟩

theorem rename_mem {v} (hv : v ∈ (insert a (insert b U))) : (renWire a b (monoBin d a b)) v ∈ (insert (monoBin d a b) U) := by
  rcases Finset.mem_insert.mp hv with rfl | hv
  · simp [renWire]
  · rcases Finset.mem_insert.mp hv with rfl | hu
    · simp [renWire]
    · by_cases h : v = a ∨ v = b <;> simp [renWire,h,hu]

theorem rename_ne {v w k} (hv : v ∈ (insert a (insert b U))) (hw : w ∈ (insert a (insert b U))) (ne : v ≠ w)
    (fresh : (monoBin d a b) ∉ (insert a (insert b U))) (ab : a ≠ b) (fv : v ∈ U → v ≠ a ∧ v ≠ b)
    (fw : w ∈ U → w ≠ a ∧ w ≠ b) (run : Live false T k (insert (monoBin d a b) U))
    (h : Conflict T (insert a (insert b U)) v w) : (renWire a b (monoBin d a b)) v ≠ (renWire a b (monoBin d a b)) w := by
  have zv : (monoBin d a b) ≠ v := fun e => fresh (e ▸ hv)
  have zw : (monoBin d a b) ≠ w := fun e => fresh (e ▸ hw)
  have noab : ¬(v=a ∧ w=b) := by
    rintro ⟨rfl,rfl⟩
    exact distinct_children ab (fun hu => (fv hu).1 rfl) (fun hu => (fw hu).2 rfl) run h
  have noba : ¬(v=b ∧ w=a) := by
    rintro ⟨rfl,rfl⟩
    exact distinct_children ab (fun hu => (fw hu).1 rfl) (fun hu => (fv hu).2 rfl) run (conflict_symm h)
  by_cases va : v=a <;> by_cases vb : v=b <;> by_cases wa : w=a <;> by_cases wb : w=b <;>
    simp_all [renWire] <;> grind only

theorem feasibleStep {k : Nat} (ab : a ≠ b) (fresh : (monoBin d a b) ∉ (insert a (insert b U)))
    (tail : Live false T k (insert (monoBin d a b) U)) {m : Nat} {c : Sig → Nat}
    (cost : m+(insert (monoBin d a b) U).card ≤ k+2) (limited : ∀ v ∈ (insert (monoBin d a b) U), c v < m)
    (good : ∀ v ∈ (insert (monoBin d a b) U), ∀ w ∈ (insert (monoBin d a b) U), v ≠ w → Conflict T (insert (monoBin d a b) U) v w → c v ≠ c w) :
    ∃ m c, m+(insert a (insert b U)).card ≤ (k+1)+2 ∧ Coloring T (insert a (insert b U)) m c := by
    classical
    let keep : Finset Sig := ({a,b} : Finset Sig) ∩ U
    have inKeep {v : Sig} : v ∈ keep ↔ (v=a ∨ v=b) ∧ v∈U := by simp [keep]
    have free (v) (e : v ∉ keep) : v ∈ U → v ≠ a ∧ v ≠ b := by
      intro hu
      constructor <;> intro h <;> exact e (inKeep.mpr ⟨by simp [h],hu⟩)
    have fz : monoBin d a b ∉ U := fun h => fresh (by simp [h])
    have sizes := Finset.card_union_add_card_inter ({a,b} : Finset Sig) U
    have sz : ({a,b} : Finset Sig).card=2 := by simp [ab]
    have un : ({a,b} : Finset Sig) ∪ U = insert a (insert b U) := by ext w; simp [or_assoc]
    rw [un,sz] at sizes
    change (insert a (insert b U)).card + keep.card = 2 + U.card at sizes
    rw [Finset.card_insert_of_notMem fz] at cost
    let rename := renWire a b (monoBin d a b)
    let next := fun v => if v ∈ keep then m + keep.toList.idxOf v else c (rename v)
    refine ⟨m+keep.card,next,by omega,?_,?_⟩
    · intro v hv
      by_cases h : v∈keep
      · have le := List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr h)
        simpa [next,h] using le
      · have le := limited _ (rename_mem (d:=d) hv)
        simp only [next,rename,h,ite_false]
        omega
    · intro v hv w hw ne edge
      by_cases kv : v∈keep <;> by_cases kw : w∈keep
      · simp only [next,kv,kw,ite_true,ne_eq,Nat.add_left_cancel_iff]
        intro same
        have av : keep.toList[keep.toList.idxOf v]? = some v := List.getElem?_idxOf (Finset.mem_toList.mpr kv)
        have aw : keep.toList[keep.toList.idxOf w]? = some w := List.getElem?_idxOf (Finset.mem_toList.mpr kw)
        exact ne (Option.some.inj (av.symm.trans ((congrArg (fun i => keep.toList[i]?) same).trans aw)))
      · have low := limited _ (rename_mem (d:=d) hw)
        simp only [next,kv,kw,ite_true,ite_false]
        change m + _ ≠ c (renWire a b (monoBin d a b) w)
        omega
      · have low := limited _ (rename_mem (d:=d) hv)
        simp only [next,kv,kw,ite_true,ite_false]
        change c (renWire a b (monoBin d a b) v) ≠ m + _
        omega
      · have hg := good _ (rename_mem hv) _ (rename_mem hw)
          (rename_ne hv hw ne fresh ab (free _ kv) (free _ kw) tail edge)
          (move_conflict edge (free _ kv) (free _ kw))
        simpa [next,kw,kv,rename] using hg


theorem feasible {T k S} (run : Live false T k S) :
    ∃ m c, m+S.card ≤ k+2 ∧ Coloring T S m c := by
  induction run using Live.ind with
  | stop hp => exact ⟨1, fun _ => 0, by simp, by simp [Coloring]⟩
  | @binary k U a b d hd ha hb ne fresh tail ih =>
    obtain ⟨m,c,cost,limited,good⟩ := ih
    rcases allowed_four hd with rfl | rfl | ⟨e,_⟩ | ⟨e,_⟩
    · exact feasibleStep (d:=false) ne fresh tail cost limited good
    · exact feasibleStep (d:=true) ne fresh tail cost limited good
    · contradiction
    · contradiction

def posRows : List Row := [3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288]
def negRows : List Row := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]

def onlyWire (target : Sig) (ws : List Sig) (p n : Row) (v : Sig) :=
  bit p target && !bit n target &&
    ws.all fun x => x == v || !(bit p x && !bit n x)

theorem onlyWire_sound {target ws p n v} (h : onlyWire target ws p n v = true) :
    Sole target ws.toFinset p n v := by
  simp only [onlyWire,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1,?_⟩
  intro x hx sep
  simpa [sep.1,sep.2] using h.2 x (List.mem_toFinset.mp hx)

def digit (code shift : Nat) := (code >>> shift) &&& 15

def rowArg (rs : List Row) (v j : Nat) : Row := if v.testBit 54 then Fin.ofNat 512 (v >>> (9*j)) else rs.getD (digit v (4*j)) 0
def edgeOK (target : Sig) (ws : List Sig) (a b : Sig) (code : Nat) :=
  let p := rowArg posRows code 0
  let n := rowArg negRows code 1
  a != b && onlyWire target ws p (rowArg negRows code 2) a &&
    onlyWire target ws p (rowArg negRows code 3) b &&
    onlyWire target ws (rowArg posRows code 4) n a &&
    onlyWire target ws (rowArg posRows code 5) n b

theorem edgeOK_sound {target ws a b code} (h : edgeOK target ws a b code = true) :
    a ≠ b ∧ Conflict target ws.toFinset a b := by
  simp only [edgeOK, Bool.and_eq_true, bne_iff_ne] at h
  exact ⟨h.1.1.1.1,_,_,⟨_,onlyWire_sound h.1.1.1.2⟩,⟨_,onlyWire_sound h.1.1.2⟩,
    ⟨_,onlyWire_sound h.1.2⟩,⟨_,onlyWire_sound h.2⟩⟩

def oneRow (target : Sig) (ws : List Sig) (a : Sig) : List Sig → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | b :: bs, code :: codes => edgeOK target ws a b code && oneRow target ws a bs codes

def everyEdge (target : Sig) (ws : List Sig) : List Sig → List Nat → Bool
  | [], codes => codes.isEmpty
  | a :: bs, codes => oneRow target ws a bs codes && everyEdge target ws bs (codes.drop bs.length)

theorem oneRow_sound {target ws a bs codes} (h : oneRow target ws a bs codes = true) :
    ∀ b ∈ bs, a ≠ b ∧ Conflict target ws.toFinset a b := by
  induction bs generalizing codes with
  | nil => simp
  | cons b bs ih =>
    cases codes with
    | nil => simp [oneRow] at h
    | cons code codes =>
      simp only [oneRow, Bool.and_eq_true] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact edgeOK_sound h.1
      · exact ih h.2 x hx

theorem colorsDistinct {target ws vs codes m c}
    (col : Coloring target ws.toFinset m c) (inside : ∀ v ∈ vs, v ∈ ws)
    (h : everyEdge target ws vs codes = true) : (vs.map c).Nodup := by
  induction vs generalizing codes with
  | nil => simp
  | cons a vs ih =>
    simp only [everyEdge, Bool.and_eq_true] at h
    have memA := List.mem_toFinset.mpr (inside a (by simp))
    have sub := fun v hv => inside v (List.mem_cons_of_mem a hv)
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_,ih sub h.2⟩
    intro same
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp same
    obtain ⟨ne,edge⟩ := oneRow_sound h.1 b hb
    exact col.2 a memA b (List.mem_toFinset.mpr (sub b hb)) ne edge eq.symm

def check (target : Sig) (cap : Nat) (ws : List Sig) (ids codes : List Nat) :=
  decide ws.Nodup && decide (cap+2 < ids.length+ws.length) &&
    ids.all (fun j => decide (j<ws.length)) &&
    everyEdge target ws (ids.map fun j => ws.getD j zero) codes

theorem sound {target cap ws ids codes} (h : check target cap ws ids codes = true) :
    Impossible false target cap ws.toFinset := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  let vs := ids.map fun j => ws.getD j zero
  have inside : ∀ v ∈ vs, v ∈ ws := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
    have lt := h.1.2 j hj
    simp [List.getD_eq_getElem?_getD,lt]
  intro k le run
  obtain ⟨m,c,cost,col⟩ := feasible run
  have nd := colorsDistinct (vs:=vs) col inside h.2
  have sub : (vs.map c).toFinset ⊆ Finset.range m := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
    exact Finset.mem_range.mpr (col.1 v (List.mem_toFinset.mpr (inside _ hv)))
  have card := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup nd, List.length_map, Finset.card_range] at card
  rw [List.toFinset_card_of_nodup h.1.1.1] at cost
  have len : vs.length = ids.length := by simp [vs]
  have tooBig := h.1.1.2
  omega

end Clique
theorem cliqueForest {g : Forest} {top : Nat} {prior used : Nat → Nat}
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true)
    (rows : ∀ k ≤ top, block g k 0 (used k) = true)
    (leaves : ∀ k ≤ top, ∀ i, used k ≤ i → i < (g.levels k).1 →
      Impossible g.mode (targetOf g) k (stateSet g k i).toFinset) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    by_cases inside : i < used 0
    · apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
      exact block_at (rows 0 hk) i (by omega) (by omega)
    · exact leaves 0 hk i (by omega) hi
  | succ k ih =>
    intro hk i hi
    by_cases inside : i < used (k+1)
    · apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega))
      exact block_at (rows _ hk) i (by omega) (by omega)
    · exact leaves _ hk i (by omega) hi

theorem cliqueRoot {g : Forest} {top : Nat} {prior used : Nat → Nat} {i : Nat} {ws : List Sig}
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true)
    (rows : ∀ k ≤ top, block g k 0 (used k) = true)
    (leaves : ∀ k ≤ top, ∀ j, used k ≤ j → j < (g.levels k).1 →
      Impossible g.mode (targetOf g) k (stateSet g k j).toFinset)
    (idx : indexedRoot g top i ws = true) : Impossible g.mode (targetOf g) top ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact cliqueForest lower geometry rows leaves _ (Nat.le_refl _) i idx.1

def rootLookup (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 2 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none




-- Successive groups record a common live-wire count and the number of states in the group.

-- Successive groups record a common live-wire count and the number of states in the group.
def edgeWalk (edge : Sig → Sig → Nat → Bool) (first curr : Sig) : List Sig → List Nat → Bool
  | [], [code] => edge curr first code
  | b::bs, code::codes => edge curr b code && edgeWalk edge first b bs codes
  | _,_ => false

theorem edgeWalkParity {edge : Sig → Sig → Nat → Bool} {ws : List Sig} {first : Sig} (c : Sig → Nat)
    (bound : ∀ x ∈ ws, c x ≤ 1)
    (valid : ∀ x ∈ ws, ∀ y ∈ ws, ∀ t, edge x y t=true → c x ≠ c y) (hf : first ∈ ws)
    (curr : Sig) (hc : curr ∈ ws) (bs : List Sig) (part : ∀ x ∈ bs, x ∈ ws) (codes : List Nat)
    (ok : edgeWalk edge first curr bs codes=true) : (c curr+bs.length+1)%2=c first := by
  have bf := bound first hf
  induction bs generalizing curr codes with
  | nil =>
    cases codes with
    | nil => simp [edgeWalk] at ok
    | cons t ts =>
      cases ts with
      | nil =>
        have ne := valid curr hc first hf t ok
        have bc := bound curr hc
        simp only [List.length_nil, Nat.add_zero]
        omega
      | cons => simp [edgeWalk] at ok
  | cons b bs ih =>
    cases codes with
    | nil => simp [edgeWalk] at ok
    | cons t ts =>
      simp only [edgeWalk,Bool.and_eq_true] at ok
      have hb := part b (by simp)
      have sub : ∀ x ∈ bs, x ∈ ws := fun x hx => part x (List.mem_cons_of_mem b hx)
      have eq := ih b hb sub ts ok.2
      have ne := valid curr hc b hb t ok.1
      have bc := bound curr hc
      have bb := bound b hb
      simp only [List.length_cons]
      omega

def oddCertificate (edge : Sig → Sig → Nat → Bool) (cap : Nat) (ws : List Sig) (ids codes : List Nat) : Bool :=
  decide ws.Nodup && decide (cap ≤ ws.length) && decide (ids.length % 2=1) &&
    ids.all (fun j => decide (j<ws.length)) &&
    match ids.map (fun j => ws.getD j zero) with
    | [] => false
    | a::bs => edgeWalk edge a a bs codes

theorem oddCertificateSound {edge cap ws ids codes u target}
    (feas : ∀ k, Live u target k ws.toFinset →
       ∃ (m : Nat) (c : Sig → Nat), m+ws.toFinset.card ≤ k+2 ∧ (∀ v ∈ ws, c v < m) ∧
         ∀ x ∈ ws, ∀ y ∈ ws, ∀ t, edge x y t=true → c x ≠ c y)
    (h : oddCertificate edge cap ws ids codes=true) : Impossible u target cap ws.toFinset := by
  simp only [oddCertificate,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨⟨nd,small⟩,odd⟩,sub⟩,walk⟩ := h
  intro k le run
  obtain ⟨m,c,cost,range,valid⟩ := feas k run
  rw [List.toFinset_card_of_nodup nd] at cost
  have bound : ∀ v ∈ ws, c v ≤ 1 := by intro v hv; have := range v hv; omega
  have members : ∀ v ∈ ids.map (fun j => ws.getD j zero), v ∈ ws := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
    have lt := sub j hj
    simp [List.getD_eq_getElem?_getD,lt]
  generalize he : ids.map (fun j => ws.getD j zero) = vs at walk members
  cases vs with
  | nil => contradiction
  | cons a bs =>
    have hm := members a (by simp)
    have subb : ∀ x ∈ bs, x ∈ ws := fun x hx => members x (List.mem_cons_of_mem a hx)
    have parity := edgeWalkParity c bound valid hm a hm bs subb codes walk
    have len := congrArg List.length he
    simp only [List.length_map,List.length_cons] at len
    have lim := bound a hm
    omega

namespace Clique
def oddCheck (target : Sig) (cap : Nat) (ws : List Sig) (ids codes : List Nat) :=
  oddCertificate (edgeOK target ws) cap ws ids codes

theorem oddSound {target cap ws ids codes} (h : oddCheck target cap ws ids codes=true) :
    Impossible false target cap ws.toFinset := by
  apply oddCertificateSound (edge:=edgeOK target ws) _ h
  intro k run
  obtain ⟨m,c,cost,bound,valid⟩ := feasible run
  refine ⟨m,c,cost,fun v hv => bound v (List.mem_toFinset.mpr hv),?_⟩
  intro x hx y hy t ok
  obtain ⟨ne,conflict⟩ := edgeOK_sound ok
  exact valid x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy) ne conflict
end Clique
def hDict (i : Nat) : Nat := (if i<1 then 0x60a74880866915829d2280c265160a6822c201924891a049080b444d07488084984a8945090063098a24742401a0d443440a08422542a086805502480c3441049088541a086881030984a814109006984460a6488032650682922240c08818c84809031502c1a22850841d0ac0a92150451883490d012065924d1232490844c3144a4828030a8311290028616091448c920210d02d1232050446c35448c868030d00d129205044742b44a4854115520d022a4508474361a0a8640c4d20d029245044340b028d014111c0d8682a190302c15448c828034d00d1292450444c25448c848035522d1234450841a0b150d012065520d122a450846c3544a4868034d22d129245045448b448d114210682d240504819348344a4914115522d122a45085309402a29200c0186924890504474361a224640c45a692489450442a0d44a480a180d05868890903106a21a2250421540b068921421034061a228240c0602d243404818160d1a24812061b2c924341921030161a228240c12855248a028613091028d120210b035129202860340d02a4812060586868810504474361a228640c13095028a1200d22b01a225202112a15243402a8164361a2486484148e12489140442a0d452480a1842a0d2434408180c1544a482803058692489050440c0d44a480a184c250688a480302c2144a482803132c9242419210220d44a400a18088345492028602c3144a4828031b0e85434190316091448d1202112a15203402a804c3144a484803130940a9212045348b448d114111308512921200c2c1502a4828030a8351290028616083448c920211d058682a190310825192480aa00a8311492028614483448d104215120c0a3241044340b44a4814115820d1234480844285490c80aa0510986892112114483448c904210b04512920a00c2a0c442400a1848aa8548145084221a150d0240c0d058688a09030220d452480a1859098489219211402102a4840111c0a512341404530b01a22520211089924890a00c4c2544a48480342894649202a810a251a2400aa0198e854341903046a2490d0448441a8864894108452a8490d0508445aa85489450850a251a2480aa00a830543402860180b190d012060b05412320a00c161a1a02414110883454340286034161a0a8240c0682c6434048182c11048c828034586924894504544361a248640c0b05512920a00c26161a228240c0a85924890a00c1a0b490d012065826112344803130841a225200c1c2a1122414211169a49225148410a15203002a810a25182400aa042094609002a8122941a225200c4d22d129245211161a1a22514110a83514340286034361a228640c0682d1434048182c1544a282803058682809050442a0c050500a180d058280a09030180b0905012060b05412120a00d2891448d1200c else (if i<2 then 0x588086144a24c501540a0c0e24498090a643a24c48650830d06287420c8207413444a024214c22287404c828303891a2024214c26283204c82643a24c506508a2934d11422c222b3434416282114c26286804c82144a34450154081c88d1058108664723a450654003510e91282108e5328a1d065401d0da0a6819030d86a19414d0060acd0e9058a086643a344486508068562468028620722194160421349aa25053400cf069809d0d0118b4560a328a00c4c25828c84803361a8651434018f061829d0d011349a855013400e6915829d22821a0994e91422c822b168941628038b0560a2a8a00e2d1582c4a28030d02e0b1205046824d154148b08a2194e91422c828906151d2024236188651434018c461828a8d003068a4651404c828906891260242130960a2a1200cd26a15414d003351a4922a3400cd26a89450d006a2130550522c207029829d014113518493123400c986219450d006311a60a2a3400e90613a45013209140e0a74810868a4c344148b08351a60b123400e23303a416202132d16287422c828906891d2084208cc0e9058808498038945012060a834d112028603416829a0240c0682e2505048184c2582c4848031d0da2868190301a0b1945012060b0560a320a00c340b82c50141103510e90282108e5308a1d06540980e0931418420984a8145090060b034931202860300d82c4812060c05a0a6809030061a8a41414110a830d11402860984a89450120688cc0e90581086104a3a4501540a080e0474809082c1582c08280301c88d10181084c3408a1d0832091188e914115028906891a20242351a603123400cd469828a8d00330d16287422c82144a3a4501540a0c0c5474809082c15828a8280383510e91282108c5288a1d01540a2934d10522c224506829a2040c2618a2514240184309891d0132091428927481032480c344484908309aa24493400e23413444a02422542a28740550212293a4501320984460a74810842c15248a828032894a24452800c944c3a44812060b068d1140903018158a1a00a180d00e0b140504434168a1a0240c8541a2868810301a0b894501206291460b122800c161a8a41414110a834d1140286030168a1a0240c0b0560b120a00c4b24891a0490885488e8498108612213a44813208acd0e9058a086482c34450490806856286802860702982c5014110586a250505044261a34414240c0a830d1120286207223a416042114c26287404c8240623a4504540a201a2474821080c1524c482803a0c0e247480908c262891d0d0062610a251424018340b80c501411a2930910522c222d15341d22821351a4e91234018d26a891d0d0061d0d8e86819030d4693a0c8d006351320a2a3400e0d2234416040c91188e914055028906891d2024283488d105810842c11341d024219844 else 0xa2994e91422c826513828ca2421361aa24743401a8a4d24c148b0888c24d112808621506829a2040c88c24d11480862074124c4a02423148a287411502482c24c144908920b0931212422643a34450650888cc0650))
abbrev HSpec := List (Nat × Nat × Nat × Nat)
def hUsed (sp : HSpec) (k : Nat) := (sp.getD k (0,0,0,0)).1
def hIsOdd (sp : HSpec) (k i : Nat) :=
  let z := sp.getD k (0,0,0,0)
  decide (i≥z.1+z.2.1+z.2.2.1)
def hArgs (sp : HSpec) (data : Nat → Nat) (k i : Nat) :=
  let (n,t,u,off) := sp.getD k (0,0,0,0)
  let j := i-n
  let r := if j<t then 2 else if j<t+u then 3 else 5
  let pos := if j<t then off+17*j else if j<t+u then off+17*t+39*(j-t) else off+17*t+39*u+65*(j-t-u)
  let v := packedAt data pos (if r=2 then 17 else if r=3 then 39 else 65)
  let ids := (List.range r).map (fun d => (v >>> (4*d)) &&& 15)
  let codes := (List.range (if r=2 then 1 else r)).map (fun d =>
    (1 <<< 54) + packedAt hDict (54*((v >>> (4*r+9*d)) &&& 511)) 54)
  (ids,codes)
def hLeaf (g : Forest) (sp : HSpec) (data : Nat → Nat) (k i : Nat) :=
  let args := hArgs sp data k i
  if hIsOdd sp k i then Clique.oddCheck (targetOf g) k (stateSet g k i) args.1 args.2
  else Clique.check (targetOf g) k (stateSet g k i) args.1 args.2
def hChecked (g : Forest) (sp : HSpec) (tape : Nat → Nat) (k : Nat) :=
  (List.range ((g.levels k).1-hUsed sp k)).all (fun j=>hLeaf g sp tape k (hUsed sp k+j))
def HGood (g : Forest) (cap : Nat) :=
  ∃ sp tape, (∀ k≤cap, block g k 0 (hUsed sp k)=true) ∧ (∀ k≤cap, hChecked g sp tape k=true)
theorem hIndex {g : Forest} {m cap i} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=false) (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (ok : HGood g cap) (idx : indexedRoot g cap i ws=true) :
    Impossible false (graphGoal m) cap ws.toFinset := by
  obtain ⟨sp,tape,reg,le⟩ := ok
  have lf (k : Nat) (hk : k≤cap) (j : Nat) (lo : hUsed sp k≤j) (hi : j<(g.levels k).1) :
      Impossible g.mode (targetOf g) k (stateSet g k j).toFinset := by
    rw [hu]
    have one := List.all_eq_true.mp (le k hk) (j-hUsed sp k) (List.mem_range.mpr (by omega))
    have rr : hLeaf g sp tape k j = true := by simpa only [Nat.add_sub_of_le lo] using one
    unfold hLeaf at rr
    split at rr
    · exact Clique.oddSound rr
    · exact Clique.sound rr
  subst m
  rw [←hu]
  exact cliqueRoot lower geom reg lf idx
def x191d5 (i : Nat) : Nat := 0x1e50549302048748153
def x191l5 : Packing := (1,6,7,0,0,0,0,x191d5)
def x191d6 (i : Nat) : Nat := 0xb0729d645516354e07ca9549861c153f525493021d2054e3f0a94818155110f6848171509601039a92021d4255110f4a4814258175103d2542245205d440f6150891481731039a542261205c440f2950891481761039d1302048748153f625092058173103f40a1481524c153
def x191l6 : Packing := (14,5,7,0,0,0,0,x191d6)
def x191h6 (i : Nat) : Nat := 0
def x191d7 (i : Nat) : Nat := 0x89010560b4804431058b02d1c414002683058168c00b83904800aa0a00154162c0b460b816881721f0563052105a105e0b440001782b182f0a1f05629cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399cce673399ced74b7fb24fa7329873cd9ab2461f0d85100000561b0043f261525d83087e4c2a4bb0818dc8758d6454ff4240a1282887e2481424c143f8c982a8a02a71fd984817114ff6282c2240887e5505314c940f5ab0a82b12815f59155072443a7aa4b92a8a076b509205d4408fecc240b88c7fa92050960103be122902e031fad5056158140ef248b00b9081f9930551315033e930902e2206fa4818255110aeec8ac0b9881d9d4254573102afb22b02ea207e64c14050553cbea9308382a79f48121d2054ebeb30902e229ff2481524c143cfa48b04b80a757d9258575103f6282b0a60a0767509525cc40edaa130cb88819dc874c12054e3f930902e2a9f5d245205d440e9ea12a4ba88197d526047054f9eac0c32e22073d585605c440ed6a1240b88811fd9121d2054fb6a84b8aa22067d245805c863afacaae298841db54261571103f4a8440a402065f21d5250153e9ea1304ba881cf491481761023fb2443aa2a067d261205c4538fec910eaa221df0914817014fbaaa2b9a6210767509205cc40edaa0aeca022197c875495150397a84902ec2074f509815d440e3eb0ac0ba8819f57160961103be2a2b9a408874f5d54258440af6c8ac0b9081de92058172103aeaa2a92e68877a481525cd10afac930cb8881db5615c941503f6282a12408847f6488750153e9ea12a2ba8819f55160c7244337a84c0aea207675cd4258440fd490284aa2215f59158171102bbb24b0ae6206ed5058158d40eea48a40b9881d3d4248175103fa260a8a62a076d5c54258440af6cc2c2b9081cf491481760c3f3282b1a60a07f84815250510e6eb0ac0b9881ced61581721033790ea12a88872f509515d840cfa40b0e902a7dd93021d2054fe72a8a9260a076d509525c440edaa1240b88817f09850520443fa26040a40a1fda5492044153df890302aa2219f92021d54443af240b02ea2074f509605d440ef8b0240b8881fd1302052054fb5a40a12ec2076d5c54258040ecea12c0b9881dd92058173103c3ac8aa2c6a9f2b509205d8408fa4c240b88a787d526187054fe9240a9260a9f4b509205d440ec6a1240b9881f91414c5305033390e42260a9f69509205c440
def x191l7 : Packing := (121,4,7,0,0,9,0,x191d7)
def x191h7 (i : Nat) : Nat := 0x202b048a8793824602316c340000500600123a0
def x191d8 (i : Nat) : Nat := (if i<1 then 0xd845c910ff5514c540dfd541c910ff9524c140dfd205d110fbd4158140fbd4154140dfd205c063dfd724c540ff9205cd10dfd615c840dfd7254540dfd525c031fdd634c140ff48148040dfd205c463ff9604c140dfd605c143ff56150553fbd4258440fbd541c940bfd8054831dfd855c830fdd314c140dfd7254830dfd7650020bfd855d110f7d5250553ff9614c140fdd3050553dfd754c420dfd7348020dfd745c910dfd7550020dfd511c940dfd635c910bfd821c153dfd8748063ff5514c910ff98448110dfd735c910dfd205c453bfd855cd10bfd8258031efd6058430dfd7244153ff92058030dfd405c910dfd7254140ff48148143dfd7250553dfd825c053bfd864c140dfd515c143fdd304c510dfd7158940ff93048110dfd855c831dfd405c553ff9204c140fdd3044153dfd605d110bfd831c910ff48148140bfd865cd10fdd6350553dfd764c510bfd8348110dfd7248030dfd714c020fdd534c140fbd5450110dfd615c143bfd8550510dfd7258030fbd4050553ff98348110fdd3059153dfd855c840ff92055110fdd3048153fdd2058d53dfd205d840dfd205d543fbd4258040dfc8748153dfd205c553ff48148153dfd205d440ff920580409fd825c053d7d525d440f3d54541409fc87545409fd831c910ddd7358c20f5d524c153ded615c840ddd205cc40fb9544c1409fd8758d10f9c844c153cfd615d830ddd7354c20bdd8358153df5615c440dbd425d543fb541585409fd815d840df9205c063d7d525d543cfd815d830cfd615d840cfd605d831ddd305c543bf581551109fd805d831df5205c453ded805c8409fd825d440d7d825d440d7d525d430ded855c840cfd605d830ddd305c553ded605c8409fd815d440ddd515cc40ded7254840df97348110fb9414c140d7d615d440ddd525cc409fd821c153cfd525d840cfd605d8409fd811c940df5411c910f9d424c143d7d521c1539fc8748153dbd425d8409fd841c153afd861c153dbd425c440edd6358153f3d52551409fd805c863dbd425d440fd9634c140cfd515d840df5515cd10d7d205d440fd93048153df57154440ded7254830fb5414c5409fd855c543df5605c4409fd811c1539fd874c420f5d5458d53d7d515d430cfd205d830ddd615cc40dbd7255140ddd605cc40df5714c4209fc8750153df5205c440ddd305d5439fc874c910df5865c440df5525c440edd6359153fb54250510f3d5450153ff141481109fd815d830cfd815d8409fd825d431dbd7250540fad4248040df5855c4409fc8750910cfd515d830fd9204c143d7d515d440bbd81551409fc8755110cfd205d840cfd525d830fd9314c140df57154430d7d815d440ddd734c420d7d605d440ded515c840d7d525d431df9205c053d9d425cc40cbd425d8408fd861c153d3d425d440db5425c440 else (if i<2 then 0x537403aff97b65d23390aa0550bae5c5ada0ac85375938c95608ad755a2a1d4dca4150f28153d89b54c4259525c8f746508d514e85c421a08100e7d03d699c8f0076739d1c34d9856434f99c8c9e6362f59748b4a56429b94789f64e225a922091046521c107c5503fc11a8f6446a3ac1bf8cf864a30216a8aa050a25811a88483ca17c09383480d20009fc87589409fd8758c209fd87589409fd861c9409fc87549409fd825d4309fc87591539fd805c553ddc835c9409fd825d5439fd835c9109fd825d5409fd8754c209fd841c9109fd851c9409fc874c540df9724c1409fc87441539fd874c940df4815c9409fc8758d10ddd635c1539fd815d5409fd87509409fc87585409fd815d430fd9534c140fe94248110f5d5258d53fb54150110bfd8148143dfd7254940ff56150540fbd4254543dfd7158c20ff92058d10dfd8748053bfd8255110efd6058d40dfd8748153dfd7154c20dfd205d540dfd755d110dfd7159153dfd205c543fbd4250510dfd205d430dfd865c440fbd4254440ff92058153dfd825c063ff9205d110dfd205c053ff55150510bfd8058940dfc825d540bfd811c153bfd864c510fbd4248040dfd7254440bfd8258430dfd205c143fdd204c143ff48148063efd6158140ff92044153dfd215d540dfd764c420ff94248110ff48148053bfd835c910dfd7148020dfd835c910bfd8158040fbd5250540ff5514c553dfd764c910dfd7154830dfd7348110bfd8448110fbd4158940ff5514c110bfd8148063dfd615d440dfd305c910f7d5255140fdd3054543dfd7258140fbd4254840dfd605c840bfd8148053dfd605c031ff53148510fbd4255110ff48148030fbd4158d40dfd525c143dfd7248140dfd755cd10ff55250510fbd2050540fbd544c540dfd7650110bfd8058430ff92058143f7d5254543dfd754c020ff55150110ff92058140bfd8258440dfd7158030dfd205c153dfd7148030dfd7258d40dfd535c910f7d5244153ff5514c420ff5415c910fdd3258d10bfd804c940dfd865c031fdd314c940ff9514c140dfd7044153bfd8254543bfd8058d10ff9204c910dfd7650510dfd7258430dfd525c831efd6158040fdd604c143bfd8054543dfd7348510bfd854c940ff5515d110dfd7254840dfd865c430dfd205d830dfd605c543dfd764c020fbd2055140fed2054940bfd8158d40dfd525cd10ff48148020ff5515cd10dfd7154840dfd765cd10ff54148110dfd7154140bfd8258143ff94048110dfd805c863dfd7344020dfd605c440fbc8255140bfd8258153dfd525d110dfd7254430dfd205c840dfd605c831fbd4250553dfd105d540fed4248110fdd3058d10fdd634c940dfd8748143f7d5254540dfd205c863fdd524c143f7d5250153dfd7258540dfd205c440dfd764c110efd6058d53ff5514c510bf else 0x404310a0e168d2181c2d0b888b05a170d230e0110ac2f0b4d2085c800c210b42f180110a42d1c828b05c1790010b42e80088a859000001694110c84e180e1705e301c000bc2d24371285e14c0016980049c2b1854038001705e50bc20385e20a82f0ac71a0508000313962587d0881e00285e0005a38002d0002e20040005c30442b0b460387a170e250a61f81e002a2a1e85a30402d0b870a8580005a48102a0bc600250158c2e0c4290bc2b0b4ca085a170c2d0b82c0cc800858178c1d0ac000bc80385a20442a0b83820010a85c30b02b107016882e07c2500216280e8005a17120009c2d18030385216c0050902b07000904a15a4e0005e40ba1f48061fa2d0f8621485b001c2d0bc480052168c000b451a066008001594110b42f185e18c201610330bc4038001685e40a6000002d243e890621705b001a2701c000ac81fa830005a40ac2a0bc61608a20fc1687c310a42d800e0885e20b8330a42c24371285e1485b0019158003d0b481705e20bc1f0ac61585a20102b0051f205b000641710070f42d1c500080015911f0ac417052178e258002f1a500885a1590110b82c0e090f8628b05a1740060b82d12500005e30a5000002d2023000521690010ac2f187e20c001692000a42d18040005a38961f81e0020380de2c1204a0fe2a0005e15ab160902507c2f0002e0ad01882008c88160561705a80731506c240941fc58000bc2b56820e0361204a0fe2a0005e15a9f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e31f18f8c7c63e3211706881dc061faefb47c63e45f18f6979e3c3ddb04e275a9d9dd24e657122171c02dca6ddb305b44da22b235fda90488688b3b8910cc164f17498f6c58610a1708ca))
def x191l8 : Packing := (382,3,7,0,0,13,0,x191d8)
def x191h8 (i : Nat) : Nat := 0x4642103a164c63988703090004cd27452004e0c70683745f11c7f0c45d390e21b157058b834851090c05f839248730fce920c34168de0cc230bf293400100cbc100db2e82c1556a5744935ccb020c415c1310cef3a8441d41d1f011290a60a8141a8aa12ccf25018280af3c53a0040e1b8ed23cbe000612c04c18973320260dcb62a0071ecd526cc328c99230700003d06c89228d80040b2d066278b3cd08107cac0109613c78eb477e5c200085b620785000000b090824f12141512daa310c22a0224922501ae300065081e08000300040
def x191d9 (i : Nat) : Nat := (if i<1 then 0x48cc58a0049c502c15945407908bc5a2430505510038484a290020942e160a83a5184823e0420943e2a008505a2e0004122b900b03e40e010481f0bc5a2a1b128445e0060943e11008cc0e00380c6629008bc5c2c152210251511c3e2d038010111501e0000108b45e81511c4a1f1981c007008be3c330e94082a088045a2414800049020b8222a00850800001246229220ae0011081c4c25190ac5f27001c3625120a802070e0a4822d002c282408c080e040090000913094481f158be44004044540c0f894520700220e07908b45e5150a057201607cc2a808be401f28943e2a03804381b0a8b85a00587037150f8a80e250b0a400a128903e2a088e45e2b11240300004a24e2b303c3e2a008a40e003810481f088041e14880cc00a004a05627203c5a2a008a4001038aa502b13890a06028aa04070200452004934981d1287c0e00385c381b120943f168a84400a2407036251207e8315088014430e06c4a240fd062c110028381b0b894481f8b454220050d86a14078903e108904400aea3751ba8dd46ea3751ba8dd46ea374539b3cb0e31f10f823bcdda0ebaf561a87d2f688f3e3992cabe4971c38a6c31609effd7d5bc45ccae256bcb4e58f6c295d9ad8556aa3f4dba4bd1de8553e69c3cd566112bb944c9163f11d8816c6762590fa86d427e0ff044816bfedf80f8e7ae3ca9dbae90714376db64d5367a327987ebe05d72dcd64caf4565a9d54989db4cba5291fa8b043620e8fc878e3a51c18d3c6482fd96b8af8541287929c8903f21db8dcc6282eb15389d443e1db0be05f023a0be02f8003fe99281ff5c940ffaeca07fd73503febaa81ff1c940ffae2a07fd73083fea0041ff48143ffaa0a07fd71083fe90281ff54430ffa60a07fd52503feb22a7ff50153ffa60887fd600c3feb1841ff58d10ffa4031ffd21443feb9221ff48053ffa20a9ffd42443feaa281ff4c553ffa82a07fd53083feb0a81ff58153ffa62107fd20443feb1aa7ff58d40ffaa2207fd62503feb0081ff48153ffa84a07fd200c3fe99221ff5c553ffac2207fd20103fe98a21ff44020ffaa2a1ffd610c3feb0287ff54153ffa60a9ffd7454ffeba221ff55110ffa82a9ffd73443fe98041ff58031ff8e0a9ffc72443fea0221ff54830ffaa418ffd52103feb82a7ff50510ffaa2a07fd60503fe98a81ff48020bfae4885fd7150fdea1081f758d53bfae0a1dfd71083dea0a817f5c153bfae2185fc72503fc902217f5d830fea82885fd72102feb90c77f1c910bfae031dfd7154efeb88c77f5cc20bfaea18dfd760c6fe382a7fe4c140bfaea205fd720c7ee982877f5c453fba60a9dfd74442feb9a217f5d840bfae2205fd7550efeb92817f5c053bfae4187bd54502feba8617f5d540bfae018df57114ef6b90815f5d440beae2204fd76102eeb98813f5d830 else 0x24b1f1188a005250d0522c13890c40148cc584020aa002813c1c56004400522d18903e00190acb0116c005c2b1609ce421300842271212c702e158b45e2203801e341087c702f160904e0048c0402f14c1c3e61f842002d20a8582e17906045178b0401f34963e0883c00a061f0145049100943e0302286004900823e1f34963e0c83c00a30108e05e2c1007ce2015c1c5e290f983a34164040027159c8907168840e2f307c022c1590542c168bc834204005c2c140ac4e8080804e2e8081c5f0016a45433178c602a900823e1f83c00089039145e31a07c5901130ac5e4613801411800a45a4170ac802c1309cc3f20c005a4020445507800845a4517a459010e89e0e2b30fc251f188a45b00388066421f0bc521f38845a2f1c6c2d25178b8522d80207e168f8c4522d801c0a30100845e3e020a60e1f50b85e30148b0b248f8bc5a2b1188a008094524a33170b4210040f45c2f11400a3c108a45e24000b4e211241c5701038005e8178e05a3180e0562c1007cc3b1d0844a248387c5e2b168e400c180be40200f943a2b178e0833174040500301c702d18bc5c01180a45860f8b041016400002d2c10582d8080a0060a8b2000016964221000b45e51b814081f16146829800b458281589d034160b85701800004e81a09050011289e0e331907c00b188c0062f170b4561140c240048f904c241287c222a11c88562f5458381b120943f15178ac00a249084027168008a2f03a44c25190a802240fc88562f547a3a030081c00401)
def x191l9 : Packing := (122,2,7,0,0,13,0,x191d9)
def x191h9 (i : Nat) : Nat := (if i<1 then 0x9daac1f156878438c05dbb401e3fc464a78b6c2dc6706ac5704a06d01346b47300657fc93030037c28e79404c21f58a9889480029f99768e94716c820da964400ac2cd90c71fba14399e576b3d83b317c6fc1084d302ca04310be06ccb748989af2f07c4290b534d03c01902b840c61966961921d7c46f452022756d8902ac08669c1b486095475001011dbd8a1444490072c0718585d82c04ec98849445616465cb48adcb905643cc7e4008168980a974eaae74905062d034cb0c4b06e8a54050799400978b897f559d4a458d9481847bc6b9b1463112f4a87f04c9b87a645bc6787cc9748f8b445d43ac08c69841c35aadc8d79e0bc07741a59a81041c99d454b8540cd9783445fca8c5f04700e417458090cba04141e4320b1022a0f18d36dd2287a40a54f874c18916413c99cad46677c464449c5ed3756674fc54598c9237064d41c07dcaac57d71c51f32c8ba734600398bdd67b3130e789c0b69096f8264764380594684628840668259b443ec944a383e44c231433c0f68a390da5654836804442c0e864c03033525c1406887958d886d564bb8ac41fd8441b84a89d829c4e01d8534a4c8ac2100000048746a33fa090000b3016728043412847fb089b94ac284a741d68204fca4083c3a00789e49958745c76947409603f86943bc5b45cca2147819c93a12c23c5117405388582443d0ab87148c86c49fcaf552a43c2fc06c8a712c881647a486e73c942b43c808aa09f43737b811000487c75d7580000002f4b203f4b80804404a0839003c02848f5748d812045c32bb985515302b456d72cb2892ab988954e8004420000a84b01964afd510b1c9a173c2a081c8b4b602d09d644e53484cb599040daba42e87787d09681507b4ba85290dc3d831c62256c9c40d002063c7ecb3c2e144e2f68340c4094250a980029dd9c870f94d9be3c8650a588e815a17b5594e3bb29a936d3fb96888c43b9ac2757b4824230610914480bd46d870026c2794508358b978c608aec8571603564249c846d83c0980fc8e01485083400020200404300807c2600119d012060083812510405000020380008060c810028b0001422000008c001d05808060f0383000181200002000301c0c280501018e70001c0011038200c00098000006008000a00018141a2b051200c061400c020f04000001d0004404000a82c16000201400060084c1600000082e08018c80001000287a00058081e010002c0a0737ca80800058080aca0b0500014000080602008042809000540600490fc4c000000404040e83036000680c2803018180417558200008008080a00001724c0e000000200038040c1e0a88032060137400010381000160e004000000034c400010000009008004600000000e3e140705200109640a04020000205000101400000040600328c800028e8240003 else 0x4bb4bea94aa045a27c48132082485e44bc0b985417c7216c67f8b9c9b03648f05a89ea8389584da8acbcf199631524a6c91b3e082f870a601e88c41a87a8ab0acc30ca1a6b876820473878e8087fd1ad8104f044cb78a30a2fa38ae24edb)
def x191d10 (i : Nat) : Nat := 0x28270019312920f8e91910020841c00602403e3031e1d18e0d8d0c8c0b8b0a888028504c483c3844400101e1c1a180e0060b0a090807003030282018100801fbb98bdd7a82ec539c87a00ff503fd43ff54ffd10ff083fc40ff0c3fc53ff18ffc31
def x191l10 : Packing := (10,1,7,0,0,9,0,x191d10)
def x191h10 (i : Nat) : Nat := 0x3ae33c9b7901e1005bd422a334d0a6c18547e20bc84279248e0d91380f6d06d17cae09029518985a08a0587ea2fb166cdd6f8e42ce9010c025f4111873324c7ddfc330ec1b270a21bbab37c2a110e901e7a29f6a23cacabc0b388b41a4013113830f772a074225afce07914cef2f4081740d1c8eb014e11248d08593251e30d0f1048bf870d5c74765c8220fae435c5020091164c73cacb48c2c190cb95f8712c87054380743cc61831eb883b68e15001ef867d6082324a52c496004632e8260c57b11f7a2afb91c4e76272715ae2f40dbe11cf280c034fe5130b90ddbd2dc6a00aa21400080000440506002030008d9b0408f801248487360c02002000020c004990700000e800b800a301111c3848a000c500518c21300633730820297
def x191T (i : Nat) : Nat := (if i<1 then 0x8dcc617562102c15c6e140bab108198ae37318d558840b0571b98c6aac420512a190c6174321028950d8141aa19081a4a8310a05d0c840a2543218c2e86420512a190c6174321035950d41b0ba19081a4125a0a05d0c840a254188505486420582b9582817452102895062140ba1908144a8310a05d0c840aa68338502e8642051049682835432103315cca630bab108144a8643185d0c840b0571b850a4ac420172c15cac6364510288f4c0140ba1908144a8310a05d0c8402a623088890e2a80511e9802817432102d824b4142c9b908144a8310a05d0c840b0572b0502eac420552a0c4a65243210288f4621415219080582a146101309444c865f2f0e94c0ba5c18b9085c402e2048401d400e900a306544343a02188412863a4034219c840542022651b200f50c78a02f5234c181c84a8645443189085c402e203a401d200a550f48017102a21889508264313228c1908407480225420990e900a88617101b281f0c874603a401d201510d0aa048401ba885c4062646d5042080dd4828422a102a2185c4028423a3017a920cc89080171034218e900f84268731ba920940fe8069831d2018c846242683215081c50012863d430b8805c4074803a301b200e8c00e426d5024200dd45028042101d20024c86ca07f400b880c4c828422a101d2005c40746017101d200f50ce2806d5034399a0c890a03a4020990e8c0f8643a40112a200402e20683203080e900626417100b8805c40fe80544338a01d500fc8022543ea005c40a8863f322a219f1c82e20485011329b540f6803a301d200dd449e6415702a218c4c8626454432428150c8f48067323c990508450a854430a081c500ea8036400b881e0402e2037520b880d4407480758011b21b500748022650b880d440748017100b881510c746068321d201510c748017103ba00e9007a6417103b080a150eaa074210a108e900e6801710112a05c40e420225436a01c500748041321d201c10074806d502a219b54028426f211d200c4c8dc805a3204991b5002e201e10870401f432100f074381b0d2190806412180a05cd48404c251131089046226210b05428c20171028389208072604f212708135902e20107620908c48498423731142a12c846c802f421b300dcc4942048401d18125d45a602a1011a10a8406c601421242811d508c203a4018908c48452862a1022b0110c074602f41071905c40862028542108104c82e2041211d100a50c80603f321f2a0bd0862643c401e908edc06c8030211d180f48478803930111905c4076a03a3017a90d8c022c6364015080e4c0508638541b980d8c06a20343219a10c9c062a4303217a90b9405a602c7315a80a94052862243141909d8414090401c0c86420050200c04014321009b28484020c81143083283cc81c420e3206990318016ca0054 else 0xb0574401c2eac420582b9582817562102c15cac140bab108160ae370a05d58840b0571b8502eac420582b)
def x191Sp : HSpec := [(0,0,0,0),(0,0,0,0),(0,0,0,0),(0,0,0,0),(0,0,0,0),(0,1,0,0),(1,11,0,17),(20,95,3,334),(126,226,4,2261),(113,0,0,7949),(10,0,0,8534)]
def x191samples : Array (Bits × Bits) := #[(0x9017721c30,0x14b5bd0008),(0x500e080936,0x634240ff36),((-0xb357779eff),(-0x73f265ff37)),(0xdc001a04a,0x12b065ab12),((-0x7eaefe7bb1),(-0x16b5fdab1b)),(0x2200761284,0xca4842b0f4),(0,0),((-0xdddf7bbd79),0x31b2254f02),(0,0)]
def x191columns : List ColumnInfo := [(24,0,167,0,7),(2,0,189,0,8),(6816,0,6687,0,7),(1538,0,1725,0,8),(43010,0,43197,0,8),(44546,0,44733,0,8),(54786,0,54973,0,8),(160,0,31,0,7),(17922,0,18109,0,8),(1664,0,1599,0,8),(42624,0,42559,0,8),(47744,0,47679,0,8),(16898,0,17085,0,8),(1544,0,1719,0,8),(42504,0,42679,0,8),(47624,0,47799,0,8),(2208,0,2079,0,7),(1,0,190,0,7),(2050,0,2237,0,8),(44552,0,44727,0,8),(54792,0,54967,0,8),(2688,0,2623,0,8),(2562,0,2749,0,8),(12304,0,12463,0,8),(42512,0,42671,0,8),(44560,0,44719,0,8),(47632,0,47791,0,8),(54800,0,54959,0,8),(68624,0,68783,0,8),(1560,0,1703,0,7),(1696,0,1567,0,7),(42520,0,42663,0,7),(42656,0,42527,0,7),(58370,0,58557,0,8),(58016,0,57887,0,7),(57858,0,58045,0,8),(44568,0,44711,0,7),(47640,0,47783,0,7),(54808,0,54951,0,7),(44192,0,44063,0,7),(44034,0,44221,0,8),(35,0,156,0,4),(4,0,187,0,7),(9,16,166,0,4),(19,0,172,0,4),(129,32,30,0,4),(36,128,27,0,4),(20,8,163,0,4),(42500,0,42683,0,7),(47617,0,47806,0,7),(25,0,166,0,4),(14,0,177,0,4),(44036,0,44219,0,7),(13320,0,13495,0,8),(68616,0,68791,0,8),(64002,0,64189,0,8),(56,0,135,0,4),(7704,0,7847,0,7),(12312,0,12455,0,7),(68632,0,68775,0,7),(11296,0,11423,0,8),(26,0,165,0,4),(52738,0,52925,0,8),(54785,0,54974,0,7),(134,0,57,0,4),(2592,0,2719,0,8),(52896,0,52767,0,7),(13328,0,13487,0,8),(3080,0,3255,0,8),(168,0,23,0,4),(4120,0,4263,0,7),(1152,0,1087,0,8),(6160,0,6319,0,8),(47776,0,47647,0,7),(44548,0,44731,0,7),(152,0,39,0,4),(1032,0,1207,0,8),(6176,0,6303,0,8),(162,0,29,0,4),(164,0,27,0,4)]
def x191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x191levels : Nat → Packing
  | 5 => x191l5
  | 6 => x191l6
  | 7 => x191l7
  | 8 => x191l8
  | 9 => x191l9
  | 10 => x191l10
  | _ => emptyPacking
def x191index : Nat → Nat → Option (Nat × Nat)
  | 6 => rootLookup 2 2 0 1 0 0 x191h6
  | 7 => rootLookup 11 19 4 6 4 1 x191h7
  | 8 => rootLookup 61 137 5 10 7 2 x191h8
  | 9 => rootLookup 251 557 9 12 9 2 x191h9
  | 10 => rootLookup 71 179 7 10 7 2 x191h10
  | _ => fun _=>none
def x191 : Forest := ⟨1215,10,fun j => x191samples[j]?.getD (0,0),x191columns,x191autos,x191levels,x191index⟩
set_option maxHeartbeats 0 in
theorem geomx191 : graphValid x191 (boundsBefore known42623) = true := graphPieces x191 (boundsBefore known42623) 4 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesx191 : HGood x191 10 := by
  refine ⟨x191Sp,x191T,?_,?_⟩
  · intro k hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact spansBlock x191 6 0 [(1,7,0)]
    · exact spansBlock x191 7 0 [(10,7,0),(10,8,0)]
    · exact spansBlock x191 8 0 [(5,7,0),(18,8,0),(18,8,0),(18,8,0),(18,8,0),(18,8,0),(18,8,0),(2,8,0),(11,9,0)]
    · exact spansBlock x191 9 0 [(7,7,0),(18,8,0),(18,8,0),(5,8,0),(18,9,0),(18,9,0),(18,9,0),(11,9,0)]
    · exact spansBlock x191 10 0 [(10,8,0)]
  · intro k hk
    interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl191 : Impossible false (graphGoal 1215) 10 (vars 1215).toFinset := plainA (q:=191) (prior:=boundsBefore known42623) (before_sound known42623 valid42623) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6847 : Lower false (varsX 6847) (graphGoal 6847) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (hIndex (g:=x191) (i:=0) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known6847 := extendKnown known42623 11 [(6847,[]),(1887,[133,117,101,33,48]),(14175,[131,67,99,116,50,33,16,80]),(8059,[128,64,116,81,96,49,32]),(17275,[130,114,98,81]),(17390,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6847 : Known false known6847 := extendKnown_ok (m:=6847) valid42623 low6847 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low18111 : Lower false (varsX 18111) (graphGoal 18111) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (hIndex (g:=x191) (i:=1) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known18111 := extendKnown known6847 11 [(14143,[135,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid18111 : Known false known18111 := extendKnown_ok (m:=18111) valid6847 low18111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low17087 : Lower false (varsX 17087) (graphGoal 17087) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (hIndex (g:=x191) (i:=2) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known17087 := extendKnown known18111 11 [(17087,[]),(9535,[133,117,16,64,49,32]),(4959,[133,117,101,33,48]),(2415,[128,16,64,100,80,113,33,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid17087 : Known false known17087 := extendKnown_ok (m:=17087) valid18111 low17087 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2239 : Lower false (varsX 2239) (graphGoal 2239) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (hIndex (g:=x191) (i:=3) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known2239 := extendKnown known17087 11 [(2239,[]),(4927,[131,65,50,114,81]),(6975,[133,117,16,64,49,32]),(2399,[133,117,101,33,48]),(9567,[131,67,99,116,50,33,16,80]),(4975,[128,16,64,100,80,113,33,48]),(7023,[130,33,113,98,66,16,80]),(2427,[130,114,98,81]),(9595,[128,64,116,81,96,49,32]),(9703,[67,132,99,82,16]),(12782,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2239 : Known false known2239 := extendKnown_ok (m:=2239) valid17087 low2239 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2751 : Lower false (varsX 2751) (graphGoal 2751) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (hIndex (g:=x191) (i:=4) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known2751 := extendKnown known2239 11 [(2751,[]),(1343,[135,50,65]),(18751,[132,65,48,80,113,32]),(1375,[135,101,50,33,16,64]),(18783,[132,67,100,84,48,33,112]),(1391,[130,50,97,115,82,16,64]),(18799,[128,97,65,49,33,112]),(1403,[130,50,81,115,98,65]),(18811,[128,80,81,67,96,113,32]),(28135,[80,132,99,112,32,16]),(6638,[50,117,131,49,32,65,96]),(28142,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2751 : Known false known2751 := extendKnown_ok (m:=2751) valid2239 low2751 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1727 : Lower false (varsX 1727) (graphGoal 1727) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (hIndex (g:=x191) (i:=5) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known1727 := extendKnown known2751 11 [(1727,[]),(2367,[135,50,65]),(7007,[135,101,50,33,16,64]),(9583,[130,50,97,115,82,16,64]),(4987,[130,50,81,115,98,65]),(17341,[129,82,97,48]),(14318,[50,117,131,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1727 : Known false known1727 := extendKnown_ok (m:=1727) valid2751 low1727 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42687 : Lower false (varsX 42687) (graphGoal 42687) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (hIndex (g:=x191) (i:=6) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known42687 := extendKnown known1727 11 [(42687,[]),(44351,[135,50,65]),(47967,[135,101,50,33,16,64]),(53087,[133,117,101,33,48]),(44923,[130,50,81,115,98,65]),(69499,[128,64,116,81,96,49,32]),(60349,[129,82,97,48]),(69565,[129,80,48,50,114,97,64]),(42983,[115,83,82,130,99,66,16]),(45031,[84,117,80,132,96,48,32,16]),(53230,[50,117,131,49,32,65,96]),(60398,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42687 : Known false known42687 := extendKnown_ok (m:=42687) valid1727 low42687 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58559 : Lower false (varsX 58559) (graphGoal 58559) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 36, 1, 9, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (hIndex (g:=x191) (i:=7) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known58559 := extendKnown known42687 11 [(58559,[]),(64191,[117,67,32]),(51007,[133,117,16,64,49,32]),(54079,[135,50,65]),(46431,[133,117,101,33,48]),(43887,[128,16,64,100,80,113,33,48]),(54127,[128,97,65,49,33,112]),(48507,[128,64,116,81,96,49,32]),(43951,[113,129,97,82,32,65,48]),(43453,[129,82,97,48]),(64445,[129,80,48,50,114,97,64]),(49646,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58559 : Known false known58559 := extendKnown_ok (m:=58559) valid42687 low58559 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58047 : Lower false (varsX 58047) (graphGoal 58047) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 16, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (hIndex (g:=x191) (i:=8) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known58047 := extendKnown known58559 11 [(58047,[]),(47935,[133,117,16,64,49,32]),(69439,[132,65,48,80,113,32]),(44383,[133,117,101,33,48]),(74079,[132,67,100,84,48,33,112]),(50043,[128,64,116,81,96,49,32]),(58235,[130,114,98,81]),(69102,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58047 : Known false known58047 := extendKnown_ok (m:=58047) valid58559 low58047 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44223 : Lower false (varsX 44223) (graphGoal 44223) 11 :=
  strong_full (q:=1215) (rs:=[16, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (hIndex (g:=x191) (i:=9) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known44223 := extendKnown known58047 11 [(44223,[]),(44735,[84,115]),(52927,[117,67,32]),(54975,[116,83,32]),(42815,[135,50,65]),(44863,[131,65,50,114,81]),(53055,[133,117,16,64,49,32]),(60223,[132,65,48,80,113,32]),(42847,[135,101,50,33,16,64]),(50015,[131,67,99,116,50,33,16,80]),(58207,[133,117,101,33,48]),(60255,[132,67,100,84,48,33,112]),(42863,[130,50,97,115,82,16,64]),(47983,[130,33,113,98,66,16,80]),(60271,[128,97,65,49,33,112]),(69487,[128,16,64,100,80,113,33,48]),(42875,[130,50,81,115,98,65]),(44411,[130,114,98,81]),(60283,[128,80,81,67,96,113,32]),(74107,[128,64,116,81,96,49,32]),(44989,[129,80,48,50,114,97,64]),(69095,[84,117,80,132,96,48,32,16]),(69607,[80,132,99,112,32,16]),(48110,[50,117,131,49,32,65,96]),(55278,[66,114,132,49,32,81,96]),(69614,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44223 : Known false known44223 := extendKnown_ok (m:=44223) valid58047 low44223 (by decide +kernel)
def x255d11 (i : Nat) : Nat := 0x4c88f1a284060808057fc10
def x255l11 : Packing := (1,1,6,0,0,0,0,x255d11)
def x255h11 (i : Nat) : Nat := 0x83800e3000c4814a28004c8280a80000001288072170108490827828b80af
def x255d10 (i : Nat) : Nat := 0x45e30d8a0c818140206a241064060040e1d00022e2050212800011103640685c1c10c04820d80802c260c58342c08544800504d78c021e1c0400087480d0b4609048382010050c640685848241c10080283c30342c27180a0c10040161a18161413918d06080200bbeabda425b7f9a15910f2e85d003ff5cc10ffd30043ff55010ffd42042ff60810bfd83042ff61010afd86042fb60810bbd84042f760c10
def x255l10 : Packing := (11,2,6,0,0,10,0,x255d10)
def x255h10 (i : Nat) : Nat := 0x202000000380606397c47943e48901800297152608243b403c8700800082947f118001c3285b90ec41920000002c8c93c003182c4b157140c72130003050003410000003d1e537c6746e01704d44505c06907602c00110950282796c162857834001c1c40e912986200108200000514a043340004082000000144000
def x255d9 (i : Nat) : Nat := 0x200005068b4c0503680286a12040a400206080504120c88021b072002050c8041c30dc0041b80081c018005c205070060017081507000e8709188586c321207400e040807861f848043300071805000004420507006001708140019090788000c8483c4414002210207e12010cc001c607006001708143509020640300081d050008800205a342c36190903a007014002210206a12040c80600103f1a161b0c8481d00385a0011081202000c8043c50a0404838007438407400001708141d000b84081a84810320180040e8280044204cc38befa5ddb8d652ba55da8d452714b98eb1560d3e876ce35b233b600b39452584287acd3963274420788c812c1b414800bfec92e6086ff609730437fa60c1021bfd5260c10dfeb8306086ff60954043ff2e098021bfd9460810dfea1304086bf551860427fb2ac2021bdd5260c10df6b9b04086f74c18304377ae0c2021bbd4261010df6aa304086f765d830427fb2ec1821afd4261810deeb8306086ef655840435fa60c3021bed4260810d7eb9b0c086ef649840437da60c1021bbd73610109fec9308086f75cd830437ba84c1821bbd5261010ddeaa308086f75518304377a60c2021bed9460810
def x255l9 : Packing := (36,3,6,0,0,11,0,x255d9)
def x255h9 (i : Nat) : Nat := 0x4200118060050390014553e041769a0
def x255d8 (i : Nat) : Nat := 0x190040e18320081c3064010386000418002029b9673502d1e1900abf6897361810afb6a57360810ebe5c13061810efa5c13060810eee5c13061010cfb649825cc10aef68973610108f72a54260c10
def x255l8 : Packing := (8,4,6,0,0,8,0,x255d8)
def x255samples : Array (Bits × Bits) := #[((-0x573ede6f),0x7c002100),(0x100d1cac,0x38d1ca8),((-0x3beb9df1),(-0x13fffdf9)),(0x5308cf2,0x139088f0),((-0x5e9fa8b3),(-0x7f90a9f3)),(0xa82987e,0x390807e),(0x1008e070,0x7c72e050),(0x4202ff80,0x106f7d80),(0,0)]
def x255columns : List ColumnInfo := [(2,64,189,0,8),(33,0,222,0,7),(1048,0,1255,0,8),(1184,0,1119,0,8),(17,0,238,0,7),(52800,0,52927,0,11),(54848,0,54975,0,11),(58432,0,58559,0,11),(64064,0,64191,0,11),(43010,64,43197,0,8),(11266,64,11453,0,8),(52738,64,52925,0,8),(57858,64,58045,0,8),(58370,64,58557,0,8),(145,32,78,0,4),(64002,64,64189,0,8),(73,16,166,0,4),(162,64,29,0,4),(41,16,198,0,4),(1096,0,1207,0,8),(148,8,99,0,4),(160,0,95,0,8),(12,0,243,0,7),(177,0,78,0,4),(54786,64,54973,0,8),(59393,0,59646,0,8),(52801,0,52926,0,7),(78,0,177,0,4),(193,32,30,0,4),(90,0,165,0,4),(84,8,163,0,4),(54849,0,54974,0,7),(0,128,91,36,7)]
def x255autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x255levels : Nat → Packing
  | 11 => x255l11
  | 10 => x255l10
  | 9 => x255l9
  | 8 => x255l8
  | _ => emptyPacking
def x255index : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 5 23 3 10 4 2 x255h11
  | 10 => lookupWord 27 69 6 12 6 2 x255h10
  | 9 => lookupWord 2 13 4 9 3 2 x255h9
  | _ => fun _ => none
def x255 : Forest := ⟨1279,11,fun j => x255samples[j]?.getD (0,0),x255columns,x255autos,x255levels,x255index⟩
set_option maxHeartbeats 0 in
theorem geomx255 : graphValid x255 (boundsBefore known44223) = true := graphPieces x255 (boundsBefore known44223) 3 0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesx255 : checkedTables x255 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact spansBlock x255 8 0 [(1,8,0),(7,9,0)]
  · exact spansBlock x255 9 0 [(18,9,0),(9,9,0),(9,10,0)]
  · exact spansBlock x255 10 0 [(4,8,0),(3,9,0),(4,10,0)]
  · exact spansBlock x255 11 0 [(1,9,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl255 : Impossible false (graphGoal 1279) 11 (vars 1279).toFinset := plainA (q:=255) (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2303 : Lower false (varsX 2303) (graphGoal 2303) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (2112,0,2239,0,11) (by decide +kernel) (by decide +kernel))
def known2303 := extendKnown known44223 12 [(27127,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2303 : Known false known2303 := extendKnown_ok (m:=2303) valid44223 low2303 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low17151 : Lower false (varsX 17151) (graphGoal 17151) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (16960,0,17087,0,11) (by decide +kernel) (by decide +kernel))
def known17151 := extendKnown known2303 12 [(17151,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid17151 : Known false known17151 := extendKnown_ok (m:=17151) valid2303 low17151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2815 : Lower false (varsX 2815) (graphGoal 2815) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (2624,0,2751,0,11) (by decide +kernel) (by decide +kernel))
def known2815 := extendKnown known17151 12 [(18911,[99,132,84,48,33,112]),(28151,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2815 : Known false known2815 := extendKnown_ok (m:=2815) valid17151 low2815 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6911 : Lower false (varsX 6911) (graphGoal 6911) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (6720,0,6847,0,11) (by decide +kernel) (by decide +kernel))
def known6911 := extendKnown known2815 12 [(17403,[118,130,81])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6911 : Known false known6911 := extendKnown_ok (m:=6911) valid2815 low6911 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1791 : Lower false (varsX 1791) (graphGoal 1791) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (1600,0,1727,0,11) (by decide +kernel) (by decide +kernel))
def known1791 := extendKnown known6911 12 [(17405,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1791 : Known false known1791 := extendKnown_ok (m:=1791) valid6911 low1791 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1279 : Lower false (varsX 1279) (graphGoal 1279) 12 :=
  strong_full (q:=1279) (rs:=[16, 4, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (index_root (g:=x255) (i:=0) rfl rfl (before_sound known44223 valid44223) geomx255 tablesx255 (by decide +kernel))
def known1279 := extendKnown known1791 12 [(3579,[99,81,115,130,65]),(18941,[82,129,48]),(11774,[117,99,49,32,65,128]),(18942,[100,49,128])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1279 : Known false known1279 := extendKnown_ok (m:=1279) valid1791 low1279 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58623 : Lower false (varsX 58623) (graphGoal 58623) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 36, 1, 9, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (58432,0,58559,0,11) (by decide +kernel) (by decide +kernel))
def known58623 := extendKnown known1279 12 [(58623,[]),(46559,[118,133,33,48]),(43517,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58623 : Known false known58623 := extendKnown_ok (m:=58623) valid1279 low58623 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58111 : Lower false (varsX 58111) (graphGoal 58111) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 16, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (57920,0,58047,0,11) (by decide +kernel) (by decide +kernel))
def known58111 := extendKnown known58623 12 [(68863,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58111 : Known false known58111 := extendKnown_ok (m:=58111) valid58623 low58111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44287 : Lower false (varsX 44287) (graphGoal 44287) 12 :=
  strong_full (q:=1279) (rs:=[16, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (44096,0,44223,0,11) (by decide +kernel) (by decide +kernel))
def known44287 := extendKnown known58111 12 [(44799,[84,115]),(42975,[118,101,133,50,33,16,64]),(58335,[118,133,33,48]),(60383,[99,132,84,48,33,112]),(48119,[115,82,98,131,66,16]),(69623,[67,80,100,131,112,32,16]),(45053,[80,48,50,114,129,64]),(58365,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44287 : Known false known44287 := extendKnown_ok (m:=44287) valid58111 low44287 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42751 : Lower false (varsX 42751) (graphGoal 42751) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (42560,0,42687,0,11) (by decide +kernel) (by decide +kernel))
def known42751 := extendKnown known44287 12 [(42751,[]),(47871,[117,67,32]),(42999,[115,82,98,131,66,16]),(60413,[82,129,48]),(69629,[80,48,50,114,129,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42751 : Known false known42751 := extendKnown_ok (m:=42751) valid44287 low42751 (by decide +kernel)
def x383d7 (i : Nat) : Nat := 0x20ee321b42a55148130c719536d0a9545204c39785c8a95c551481309739c42e551595204c35d254cb94817254530
def x383l7 : Packing := (5,6,8,0,0,0,0,x383d7)
def x383d8 (i : Nat) : Nat := 0x3a83e2414675c480060171009a0060178fc4802e10005e02e14677c480060171161616161616161616161616163856162a1f17560e403da4a9a404c260a95769b22819520530de92a4d0aa690261fd24c0a954d2054bfa4a9a40b92a2985779b72819520530f3cae4b8b04a8a615de2e551595204c33f854ae2a8a40987de1515c57248130afd172902e4a8a61fd24c1535c52054bfb0b8a60a8a40a97dd1315c0985c530c75b48d1330398218db655a221c814c2b9cda140ca902985758b954553481308ef172d2902b82618db695a2660730423dcda152a8a40985579b72819520530
def x383l8 : Packing := (22,5,8,0,0,8,0,x383d8)
def x383h8 (i : Nat) : Nat := 0xc80010751a
def x383d9 (i : Nat) : Nat := (if i<1 then 0x5348130efa54981481309ff6a5714c152dfb5c9914c152efe6056548130ddf6999520530cff261935c540ddf69d9520530aff6988760530efb5c98258130cff5c5984c152cff261985c530efb5c98558930e7f5c0985c530f7d4c5715c140ff62a55348130aff69c8160930ffa481714c152bdf694914c152aff6988760930efb5c98748130ebf58d8558130bfb6888758930ff35c95348130aff6a0935c540efb6097254530ffa5c96548130aff69487609309ff2a5315c130efd5c58254530fdb54d7148152cff548985c530bef690935c540bef690974c540ffa4817254530bdf694935c540efb5c98158930aff6a0974c540fdb5495348130dfb5c99648130aff69d8558930ebf68d864c010aff69c984c540bfe680935c540fed4c5415c140f9f5456558930cff261905c5309ff69c9858930ddf6557220530aff68c985c5409ff2a5714c110bfe688815c130bfe698815c130bfe2a5215c130efb5c98548130bfb6857258930fed504974c540f7b5c97148130efb5c92061930bbf68d6558130ddf6899520530bfe69c8148130cff26172545309ff6a48758930aff6a0914c152cff4c0985cd10cff261914c152f7b5c57260930bfb688974c110aff684984c152cff65d8254530d7f65d7220530bfe2a1215c130ddf5949854530bfe6948748130ebf6056558930bfe69887481309ff6989854530eef61d7150540cff2618758930fdb2a55348152ffa5c96048130bfe6848748130bfb6888758130edf5458558930eef61d31505409ff69c9854530cff261974c540aff6848760930efb69d824c010fd754c914c152aff6948760530dfb6497220530bfe2a1625c1309ff6a57220530fbe5816348130efb5c98148130ef74c49361d40ffa5c97048130fde5456548130ff65c55348130ffc5c55148130f7d5c5315c130f7e5c0985c530eed4c58750540cdf68d9520530fda4c15148152bfc2859648130afd2859261930bf668c8148130cfb65d93608109fe2a55148130bfa6888748130cfb689981cc10abf2a5865c430dde2819520530bde6948148130cdf6555161930cdf6555320530afb6888720530af768c9161930dfa4c19748152cdf54c9854530afb6819760810ef54c49161930e7e5c1874c010f7c5c5315c130bde694815c130fd65455348130fd35495348130afe2a17061930adf6948161930dd768d9520530ef64c57061930ebe5c1864c010bfa6888148130b7e69c815c130cdf5949854530ede5c1854c010adf6949161930f7a5c57248130efa5c98148130cdb655821cc10f745c5315c1308bf2a5865c4308fb689981cc10caf619941c430cfa609901cc10fd25495348130af66809760c10a9f6949161830af36889760c10aaf6909161830ad76949760c10abb6889161830a3f69c9161830ceb651821cc10cee611901cc10 else 0x3958260170c0e80b85cb20742d41e2417108350006120179401c1a80b8600e09805c305d06a1026803017817114400001a813080bb0bc0fc307e03a10ce817f12003017141ab4400b8607c00e0f8300707c141a83f0178f8901300b8609805c251d04d00607e02f28030350170c0b8130409809a285de2402e1988e880170c0180b81f0784809805c3c2406c02e182180301703e135041300b860d405c202e0f1203f080d40180b87c480d805c3920e2406a180382603f8c134132c81d074738900e80b9009a0d407540c09e586786607e02f201782d83f823101f01fe25c0b88622a282180d4a2061ee1c0d205c904c07f29702e202783e0408e26e19c13060fc09a10a102402f07c86704c2700f0182e0268409619d1981f80bc912f0ba05c39039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039039038da8bd8a08838426736048196217f07d379e7697407236e26b969067364a6216045c359a57d3c156053750e4e54bc49345e4353c14184073ea3c139836f3460292e12a026b23620119015b1321090d409f05e05e0290008ff6a57060d108ff68898545308ff688985c5308ff2a19720d108ff6a48720530abf69c91618308ff6a551619308ff6a585589308ff68d9161d40cfd28592619308ff685984c152aef6909161d40abf69d9161830cef6a1941c430afb6888760530cdf545984c152efa480984c1528ff6a19648130dd754c9854530eed504984c5408ff6989854530ebd5c591618308ff6a581589308ff6a570619308ff69c9854530adf69481609308ff2a53161d40ded505904c540bdb68d5148152bf6685)
def x383l9 : Packing := (187,4,8,0,0,12,0,x383d9)
def x383h9 (i : Nat) : Nat := 0xa80227a782424510a83042186f8041c04018280d276c000499e14040381a0008f301600178000c000240000541
def x383d10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xea8ac4987ff65d514c3ffb3098a81ffd8158930ffe98b0ea07ff589704c3ffb30b1261ffd905c540ffecc260a97ff595824c3ffae041a21ffc8758130ffe43b06887ff26173443ff92e98a81ffd6348130ffe49ae2a07ff5c53054bffb30b8a61ffd315c140ffeb8a40987ff5c530443ff930b8a61ffd7254530ffe98ae0987ff5c5824c3ffb20b8a61efd6558930fde98a82a06ff60d300437fa62c3a81ff9625c130dfec3b02185ff65c814c3ff2e098221bfd5161930ffcb8260086ff605604c2ff930b1261ff96048130bfec9820887fe61d204c3fbaa6b0261fed3048152f7eb1ac0987f764d514c3ff130b8261fed9348152fdecba82a06ff605204c37f930b8a81fed7248130ffc9030c986ff649864c37fb0298061fdd5360930ffcc9ae0986ff609514c3ff102b8261bfd7060d10bfecbb04987fe605704c3ff2e4b82617fd970c110fdeb8a82a05ff659204c3ff2e0c3261bfd985c430ffc902e2985ff654814c3ff262b8261ff97060930dfec3aa2985ff261514c2ffb2e41a21bfc8161930ffcb8240985ff649864c3fba6298221dfd715c140dfe4c2e2987fb249814c2ffb2c40a61bfd8160930fdea0ae0a06ff615204c37faa640a61ff99748130bfec8b04986ff2613054b7fb22c3261bfd2061930dfecc260a96ff261315037fb0ab0261bfd3060d10ffc90ae0986ff5c5875037f90e40a61fdd5348130dfec0ae2186ff605700c37fae0c3261ff88748130dfec2b04987ef64d415037fb02c3261fed7148152ffccb240986ff61d300437fb04c3261fed7258930bfec8b0c985ff648814c3f7a82c3a81bfd8258130dfec2ac4986ff245864c37fb0e90261fed7260930ffc40a40987fb65d2054bff2a290261bfd985c530dfec3ae0186ff661514c3ff2ca90261efd6558130dfec3b06087fe605204c27fb2ec1a213fd981cc109fe4c2e68867f61d830427fb30388617dd9304110df6cbb04084ff261714c27fb3039a217ed97481529fecb902185df654814c3fb262b82613fd9720d109fecc260886bf619700c35fb02c3061fd953481309fec9902986bf619300c27fb26c3a816fd960c110dfcc0a40986fd605710c35fb22c3061bdd9060c10deecbb06084ff654814c2ff32039a21fe97248130bfcc80e6086ef61d415037f2e0c3261bed824c010dee4bb06085fb648734437db0439821bed8260c109fe4c2a2984ff640834437db26c1021afd865c430fb6a8a40a95ef650710c3f6a62a0a81b7d8560c109fecb902987fa4c12054b77b0898021f6d53481529fec930c984ff661710c35f922c3061bdd7060c10dbec2a60084ff645875027fb30982a5afd864c010bf6c90208847f65c810c36bb0ac1821bad8460810ceec3b06084df654814c26fb2a40861b6d85608109eec9902986bb6198204379b04c18213ed9220430 else 0x6881c03230585e0ce0bd33161a868076310c1783382f8cc5a3a01c3087e05e10cc2202506100e410e2180387a207e09180427e0406f80c1d04d4a1d0fe0e807e0d85a0b83e06a48470b611822921442a81388c0040684988590085074b0c80d8000628c3890268074430c3b8460a60d8400400040cc1ec903502e6a118288761686902003f0707c0d4a6400f83f007c481a80352b0980b9412223800c035041b83ec0980c1d04d5802c0613c41081283606b82c3160a80e018e0d81ae0ac160d1038063e22c420031183a07c0b81784d483ec1a01c170690dc60a28281b035c160d103806404706c0e01b83506816c1700700ca12418c320620c317421e2400e906c0d403806200000e0187993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d993664d96fe50592363e98d6e3258ab620985960c17e65f0b7afddad7215bf76cf5aaf67d5951630d8615f4d71959d5613566d4b5514d3c54d8d3014a25227434d071403cf3f3b1ce393654d1d31e4beb2d1cacf295c9b3238c8551f746e119fc60715e44bf111c3770c5425b073416b047c09100bbfa0fca3eb0f88bd94f41bc8ef003b88ebeba82e8db9bee4c3876dfa3770db33628d563488d0f33aecc83292c5530f2c08afaaba0ae0ab6a2d5cb392bd2adc2af8a9aaa1ea69a92ea22a83e9f726ca989804c96ba4f4919a36a013231e88e217e82614407fd00007ce9eac7719d2271a1bae6b21a5064a18845f817525a09620559951a52314404d692e247f112c41c8ffa3eb8f360130ea83918de43450c442f88ae60130a2c241047c207873818f05c4148047c0eb031e099017e000004c013004c02b8000013004c013004c0006ff61d814c37f90e41a21bfd7360d10dfecbb06086ff26173442ffb2039a217fd984c152bfecc0e6885ff65d83442ffb22b8281bfd8760d10dfe4bb06085ff641315037f92ec0861bfc9361d40dfe43b06886ff661624c2ffb2e98a81bfd9161d40dfecbb06886ff25d834437fb2ec0861bfd8758930dfe43b02986ff61d824c37fb02b1261bfc8160930dfec9b0ea05ff66131502ffb22c3a81bfc9161d40bfec8a60a96ff21d824c2ffb22982217fd910c110ffe982e6887ff5c570503ff92e98221ffc9760d10ffecc2e6887ff4c530443ffae4b0261ffd914c152ffecba62a07ff641624c3ffae440a61ffd8758930ffeb2a40987ff21d624c3ffb2098a81ffd935c540ffeb8b0ea07ff4c5604c3ffb30b8a81ffd5348130ffe48a60a97ff5c531503ffb26a8a61ffd7360d10ff) else (if i<3 then 0x4c0000b898911204c05c406a12b0103747c1743280000c927cc3c1700609852381251213e4000b8d5082184c00c0f98802e385d09b8902602e2a1b07601a0820707c0b8fcaf1210709801817182483b4484f98804c05c7094c400004c09a5a040e01b83b00c58068861200006e0181d1c1a6596568fa8804c00001c17271242427c1242602e354100e8010303a2b0b6401340303a05ec42a0e240981a961840303905c46214709f04a0985c490909f04c0000b8d50a888430981340380605c80698900302f05c506e16c45e2cc360e82682e07698481303602e265961f0008393ea2000017201a62420e0182602e304c00c0e81711a0c0605c30900dea0e240d81f8d8902610705c42561303f02ec4841cc0ec1700020e130a9641d00000c0b8b4400323e27c224171a3204d63a01a038393410098c3c0006a05c6c480182610705c5c398829260dc1e0bcd8911231005c130b0f90013e620000171a9206a0e61301716902060d43a560180386905c50760010300640e130c21190000680e0d8884d098844303d0000700c134c1741a8070fc0bcb4501cb0f27d4400302e383707c001030060fa0e8e0e30207bc041a42506a06e019213587a0080e0189f03e0980b934400004c1d2b20e1e80304c05c681288a120064ec0bcd09295b100e60b826192441485b02e1004d0018383a40f6820e83482e704c00e1a817102484dc1582c1a20706c0d40325880000e6130171499131a1b5049043400e4acb8e240d81342637121070000b826171200020e0bc81c00302f183ea560183782e2d31a66c701c83a61f5003606905c01c37303684c0d80b894400306b00e0b8a1261a624e1e1a826180386a05c347d83e030060d45684c442651005c5a820e907a5909801c269c0306909a300c01c170692342a66c469004d6b013017b0fa218901730ac24961e01c1f00605c720e0ec0004c05c5c3789426e2d00d8b02602e40670cc0f82f07e0ba6aaf4a81f00000e0184b532a3a2542dac2d84508c308e0e01b83606a0d02d82e00e019417605e0910f8203fc0600e8a838903603e0000e4038060fc0bd583b0780609a0b83e06a384307241c03834c480bc172395d1c6418902602e305d0940dc03806c378b04584d000a07586c1f04cc580b81d9c2820206e1281c60409a01901460104f06e0e01d00000c8a634cd88d14e56c3f125100980b940d81a84c00e018a1402885d0700dc1aa0205e1942504f000019a1371100705d8842608d385106e4081c03a00c0ecf4ce8a04c0740b81d9a23220c0350702037c061341d242307e12224080d81ae0ac160d20384c00c8098238468d8e83e0c81f803861302e0d00ec64c89813324045387971c4813035282f05d0cc0be33961542584800003e22c478841702f55410d81341f6246394ac2602e48354160db0502f0 else 0x40ec388371040c4186a8250587b10c488902602e42220f99660302e2834cb2cae8802f0740b8e8b21280700c0e8171aa0e241371a119642602e2e5962143c2500000c0b8e0d3124246561301782e3848a825072c83a61e134ed0a99b11639452900940980b98787ea21891a9680042400c1e01d180302f09830758900007cc4213711b2005e1303502e6340682c801f02e662cad88000a381371204c6e0209e0e01b80000c620e0d81a06c05e13417624404a0760d11f40005c66234342184c00e0183f02e460ac160d42684c00c0b8f4ac1f00600e0e8171b1203920e0bc8cae8804c00e00017181b84c06c0d42383400e0190c3e8862420e1300002e3b0f00c1a417120a23e1120181714ab92c4930d387f1000e4083f624550800c0b83e128e049c484f90002e323ec1e018351204a2100c0bc88fa880000740b8b504362060fc426445096920868233878062e244d1f02fc48130353d880))
def x383l10 : Packing := (259,3,8,0,0,14,0,x383d10)
def x383h10 (i : Nat) : Nat := 0x3b428f1202a03d92ac1b49b648e3380072d000000637858800034c2400199614781180a451a4f01f99982d00044e000656644412216a43839c0e82925404fe529a7831621fbe01cc345bfc1601ac3200c74283f45042da5a407c37023cae73940e0334ba64354084943580f7bc41d051116013c1882c5ae2900035d5a4100168093440cc36e466c862560834782e8459cf40543bc5c903452255800048c59808ddc41a621033c5733ec0dc8422fe3da29804938c1f28f80b447886016c32a55006c5b05900d44008bc898039c784f642010502017a3842321d63ce1ee4e92401bc18029a0e03504a026c3a44484442be2f213400900043038c2f91bb51c0748500000000059b057c4bc5a4c484d81e09dc174248a0412c0fc4cd2e415a1f33d64d005c4683fc1c32781d85adc000bd1a85081ec19332458030827849d9ce0ec1325854f802480026231014e1444b019e45186011235c221c634d4d9402827414404436455c41c4664853282ae1083c854837c2e19b8c085385c40644200980ae12e2dc30746090438231c962c4c4845bc4ec2b106031c8fc3ac2022a69dc155c9a0a04082090462c447454456c258d7c2822904c628e25809410c5308c24aa22c52e11c5d00860d85522c8000402a40407e2c38a0c0058f3a48428000010006050910c60080000000000bc000181038700080800004000120090500000801cbc00200a438a0008004040000200005050064f85261c8800cb401490004ba1404305229c6838200037361ca1802551053800033580000800040190a6c68b0249c110018080
def x383d11 (i : Nat) : Nat := 0x11c360d4380dc3416c2e01c0650900006e248698861ea0c48918c070f0364c92a55d1d0ed2310682509395e208e4481724351a03b18ce330bc2e90470d4370e02f1944a808000195128002fc48304451085e0324370e1020183b28c1128bf120bd2c85d11442032957559555613d501411250d0d03ec3c0001d2c01b10172244ac2ea8782480e030770da491645a172958500495050d0d102c430f000064ae241302e7c4f154060000e030b512c492cc4711283033a2c86c5b0ec824a66988688a24195a578780c262211205e173c5a89a2a8a00701a25002249662388520819c1b8941c4050209a031c49876180d22d0f80c01e1284613872148820c0020f4921083406a8921a61e03076886571205c2628460de0450603804480e90238702308a45111d4491c469180f8004211b10d424472bc400643e240ba6a0a809fa641a226982289687c0380c9ea6698a1a9000187a568844883dc3c8962d8b21b0ec3a0b901ce1e8380f120681785c80e03780800018a1b06a1a41505c0e031d334c93145007c3d30481134b50b0032b01a240bd100ba43287c1a45b12c590d8768190631885d8906101ce2e8401207d04c11054160380ca00007018713c5512800038b5124b311c451080cc5615755955551535493d501414b10a435020f807c430f4ae24a08e1005a1f00100c0701408032851140370e04f00006389c2409423c590d800752d334c93144d304510b4b520caf0f89110001e2509395e208e44860a82900c2809c09092230962288406606c1a80e03101f0c004876128721a862170800b844140b40c83a0f83406980501c020040803180b82a0982007018d04c11054160380c695dc9723fb19e8bdc53a1cb086827bf99e1eea6705b5e9a9a18665930857acaff54b29054289514332044f7878539d1a0430c62c2f095e0aaa4d82058e886ae30c13888c03661860618208082000ffc10443ff5c530ffd73443ff5c130ffc73443ff1cc10ffd300c3ff61d40ffc30443ff5c140ffd604c3ff4c110ffd864c3ff5c540ffc83443ff60c10ffd824c3ff4c540ffd700c3ff4c152ffd814c3ff5c430ffc710c3ff54530ffd624c3ff60d10ffc814c3ff60430ffd30043ff48130fdd83042ff60d10bfc814c2ff60c10bfc810c2ff61d40bfd864c2ff60430efd860c2ff20d10ff9204c3fe5c130fbd41503fb60810fed2054abf61830bed82042f760c10
def x383l11 : Packing := (48,2,8,0,0,13,0,x383d11)
def x383h11 (i : Nat) : Nat := 0x3dae48cc448192173837459534484405e00742ae01ae2c00081770e28798054b200fa41512102c002c0fa05ec3fc16fa8c91342d5102427746200c1110ced5a71e14cc0f3863c0430604e083543be1262a9957c3fa107657d40eaa6d81e2132621774f10e906c4125591003809005095309f06149ce191858c1458680f4859048e36584502e81a42e01cc4aa87a80db6000e787c52f6420007e0711bf1240de430a363d9c08483b1861170410b3bc3b11bb86c80d80560b20da15a005e186073c25c14f8b90ed409b19b96f621021e1f2418281064c3c21ae60e06f83851230f9c18a3ac10a86d058a24e0fc88386e81720390f7a00e323d030ac037c13c0d80bca6fe21412e035946c0e4148082525a33a1450aa07ea3880a489d03c421c8314fdc44406044340587440f81990a814642b41640c1838822590660f80d034412a0bf83ac1b61f60a0022ca012002bbc659827092860a4081c24a24cad30a0d6444056816c26ad078fa06ac1400c4239469038e0c226183482359a001380402a504e02b83282ea19e467944ca291390bb20f40fe0520ee82d9b281e303a04a440ac160a5824004408d08642400891c605400001a11fa0c045522b71d5eb4a5a4002cb8040025806699c00000e808007130094280031170638260af408f27b833d1a213a8a4010c24912105500f500013c074012c13a44aa2180fc96951362206301dd0d10a1c7f4342d5a2df81841e61ed005416c26704b8d4015499c16d033c5e029e1140af075618e1b2852428009e0508d5c32425a94582c006708713c05f851c03c1e4023447800307a09be5683f00160eb14fc35a11f4ab0728000cb5eb9408800220202c02544031280c4c5743d2dbf051a0480ee0c007c004c1c8084a25f54a15e16803c85350b20fe0e403720851674afa10433415c066026c22dd54031035a368001ade80340c80000d4046410487209c907309c17c02f0137378196080419c20705d03d2149ab81b787a04722f806e04482b831483209017982621b90b30125084d0f0e0c0b438906c0d273441620056b386989000000ca02d082e0f6cb3e5760a40088d32058080a0200018040d018000000050483e00048181a020f8400200018b00000008002404000ac000100000001e04018000201800125b0080000040903c00020d0042e1502814ec0a02014088b0002826490300820560003c02140881400080180010060a80400000181402090100402000201c2a0000030000604000021a0109c2007011141233008000005000680000238a408000c158000f0d0016e003184194011c8c804040c08814000000008000097c02000d800301502010000001804182a000042c0c2c800040001000000e0201c1e240602c7000310a40e05039e0002c0f81400158180000001687c0e02
def x383d12 (i : Nat) : Nat := 0x5a2c1286c92b8843c484150a450271300c12251208c44210334401f0f074381b0d06430170b05402080a04c24110803c1c0d065c160a048200e063014080301004006f6f1294761d803fe887fd30ffa81ff54bfe087fc30
def x383l12 : Packing := (6,1,8,0,0,9,0,x383d12)
def x383h12 (i : Nat) : Nat := 0x6ce21024e003de0020381e4ccac00c5467002c129c0e8b60208448975a2874e70712403409c6d4c8930db689300212d74848a00a112dccb10a2920bc51178502f840e403e27030009430684e1e8b84143e040031f0b312020814962b99222d9a9e34ec30182508c6044f8349e6140d108665194c1f19a01934c40a41a8822a85e150631d95907898050441646020001c48c704200518400b28494714f48144068815500000000c367540000100201281
def x383T (i : Nat) : Nat := 0xaf78cd9def7432105d38570bc5ba19082be6f3677bdd0c841ed23913d188aec20ba9aaf578b7432109a4ce64be77b3990ae972ed89bad0c84230ab98ac616ae6811891cc1630b5734097c9e5d2d862bb084624f2c8cc2d5cd01ed2b6cbd188aec212a63c69e0ef67321564a564c0752b9a02b1572053add5d8415ef1783bdee86420b355ac962ea573407b48e4528862bb082b1572053add5d8415ef1783bdee86420af78bc1def7432105649e4cc0752b9a0486472558ba95cd015ef1783bdee864212491c894ed65761090aae351985ab9a02cd56b258ba95cd0158ab9029d6eaec20f655b514eb7576107b2ada8a75babb0847e3ce75f2499cc855ef18ec71ee864211b6d3654ed2576108c2ae351985ab9a046156b26042d5cd01de430c107790c2d021680c6759dbab58412ea0cf737a30b58419ee6d6109d28430421820c675860829d860e4297509c90c2d019ee739214ba8358412ea138736b0843041ac20d6107790af08616810b404ba8319d61820ba5caf978f7432107b3d5a8f4692bb083cdb4d453b495d84174e15c2f16e86420ba5cae14ad243210713857cf25ba19082bde2f077bb90c84174b976bb1d686420ba5caf978b74321059aad64b175231182e972be5e2dd0c841d2e873af9ccac642e270af9c0bb432106faadbcdd6e2328836db4d96c35d1944166ab592c5610c680d64cb55a89a8354059aada8d3692bb08345a0cf673351608592c863b198b08a60ba5cae124c44321061b0982c05fc09182e972be5e2dd0c84174b95eaf17686420ba5cae14ab74321059aad64b158431a02b156aa54aa15d841cae471c10b3196ca6525b2d568ca6af572b5885ee20f7108bb829485ee20a5217b88458c22a20fb108a082e0ca1920a74069082cdce2642d2104d28c4901ac209a418608290c222e0d2105e10ba8c22120d210860825d0141210c107b883e5414e830f64770824885fa210e90644233d4e1a20d6107a28c30421680f45049082484134a30a624b984261210a2e0218390a9d41d480d6106b0841841ee2105848228b58420620fb107a28294854ea0f7108140404418a80f71053a0c01c1fec4bc917f2031501ac20fd1075203d145f842f7107d8824841f620fa546c28be5013480f8524ea712a9b4d3399026530977654b25528c86a7205338294414840a3525143285d541009f854f42a411e8e46a3114841168a44b20a4d9124209160
def x383Sp : HSpec := [(0,0,0,0),(0,0,0,0),(0,0,0,0),(0,0,0,0),(0,0,0,0),(0,0,0,0),(0,0,0,0),(0,3,1,0),(9,10,2,155),(58,98,4,468),(183,41,0,4045),(48,0,0,7017),(6,0,0,7017)]
def x383samples : Array (Bits × Bits) := #[(0x840a108bec0006,0xd3584ac0e0a004),((-0xdb9bfaaf3affd7),(-0xd37a4efde0e7df)),((-0x9edffeabff76a9),0x503a0ef580c546),(0x4301e824009e18,0x874541086a3a18),((-0xfff48fdedffa1f),(-0xd75d4bc8eaba1f)),((-0x777ffd75f5bd81),(-0xfb58dad1f5a5c5)),(0x105404001123be,0xd362442c60629e),(0,0),(0x1a908a001273c0,0x28189ad1958540)]
def x383columns : List ColumnInfo := [(28,0,355,0,7),(2080,0,2399,0,11),(2112,0,2367,0,11),(2064,0,2415,0,11),(2052,0,2427,0,11),(1,0,382,0,9),(49,0,334,0,7),(70,0,313,0,7),(1056,0,1375,0,11),(1040,0,1391,0,11),(1088,0,1343,0,11),(1028,0,1403,0,11),(36,0,347,0,8),(53824,0,54079,0,11),(53776,0,54127,0,11),(32,0,351,0,11),(4,0,379,0,11),(47648,0,47967,0,11),(52768,0,53087,0,11),(44548,0,44923,0,11),(69124,0,69499,0,11),(1568,0,1887,0,11),(4640,0,4959,0,11),(6688,0,7007,0,11),(9248,0,9567,0,11),(13856,0,14175,0,11),(18464,0,18783,0,11),(42528,0,42847,0,11),(46112,0,46431,0,11),(59936,0,60255,0,11),(7684,0,8059,0,11),(16900,0,17275,0,11),(48132,0,48507,0,11),(44096,0,44351,0,11),(44036,0,44411,0,11),(44064,0,44383,0,11),(43536,0,43887,0,11),(42512,0,42863,0,11),(4624,0,4975,0,11),(6672,0,7023,0,11),(9232,0,9583,0,11),(18448,0,18799,0,11),(59920,0,60271,0,11),(64,0,319,0,11),(42560,0,42815,0,11),(42500,0,42875,0,11),(50,1,332,0,4),(13,16,354,0,4),(4612,0,4987,0,11),(49668,0,50043,0,11),(59908,0,60283,0,11),(73732,0,74107,0,11),(43522,0,43901,0,9),(18433,0,18814,0,9),(59905,0,60286,0,9),(50689,0,51070,0,9),(9217,0,9598,0,9),(57,0,326,0,4),(69,2,312,0,4),(42524,0,42851,0,7),(42752,0,42623,0,9),(52800,0,53055,0,11),(352,0,31,0,7),(13888,0,14143,0,11),(47680,0,47935,0,11),(50752,0,51007,0,11),(49696,0,50015,0,11),(34,0,349,0,7),(73760,0,74079,0,11),(9244,0,9571,0,7),(2400,0,2079,0,7),(2050,0,2429,0,9),(50696,0,51063,0,9),(43776,0,43647,0,9),(46088,0,46455,0,9),(9220,0,9595,0,11),(276,8,99,0,4),(104,256,23,0,4),(6657,0,7038,0,9),(72,0,311,0,7),(49665,0,50046,0,9),(73729,0,74110,0,9),(4672,0,4927,0,11),(6720,0,6975,0,11),(9280,0,9535,0,11),(18496,0,18751,0,11),(44608,0,44863,0,11),(59968,0,60223,0,11),(69184,0,69439,0,11),(16,0,367,0,11),(44288,0,44159,0,9),(83,0,300,0,4),(65,0,318,0,7),(1036,0,1395,0,8),(18449,0,18798,0,8),(59921,0,60270,0,8),(9233,0,9582,0,8),(6705,0,6990,0,7),(46082,0,46461,0,9),(59906,0,60285,0,9),(69122,0,69501,0,9),(48129,0,48510,0,9),(1312,0,1119,0,8),(18498,0,18749,0,8),(42848,0,42527,0,7),(321,32,30,0,4),(74,4,305,0,4),(59909,0,60282,0,7),(262,64,57,0,4),(18,0,365,0,7),(44572,0,44899,0,7),(52801,0,53054,0,7),(44098,0,44349,0,8),(18436,0,18811,0,11),(71,0,312,0,4),(43600,0,43823,0,8),(53,0,330,0,4),(272,0,111,0,7),(44384,0,44063,0,7),(305,0,78,0,4),(44102,0,44345,0,7),(51,0,332,0,4),(52785,0,53070,0,7),(5,0,378,0,7),(273,32,78,0,4),(2114,0,2365,0,8),(290,64,29,0,4),(26,4,353,0,4),(80,0,303,0,8),(2118,0,2361,0,7),(8225,0,8542,0,8),(47632,0,47983,0,11),(47872,0,47743,0,9),(41,16,326,0,4),(18438,0,18809,0,8),(59910,0,60281,0,8),(4620,0,4979,0,8),(11297,0,11614,0,8),(4636,0,4963,0,7),(280,0,103,0,5),(260,0,123,0,7),(59953,0,60238,0,7),(59974,0,60217,0,7),(324,0,59,0,5),(49692,0,50019,0,7),(49697,0,50014,0,8),(44546,0,44925,0,9),(40,0,343,0,7),(102,0,281,0,4),(300,0,83,0,4),(344,0,39,0,4),(1344,0,1087,0,8),(78,0,305,0,4),(354,0,29,0,4),(92,0,291,0,4),(18465,0,18782,0,8),(284,0,99,0,4),(3138,0,3389,0,8),(326,0,57,0,4)]
def x383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def x383levels : Nat → Packing
  | 7 => x383l7
  | 8 => x383l8
  | 9 => x383l9
  | 10 => x383l10
  | 11 => x383l11
  | 12 => x383l12
  | _ => emptyPacking
def x383index : Nat → Nat → Option (Nat × Nat)
  | 8 => rootLookup 3 7 1 6 3 2 x383h8
  | 9 => rootLookup 17 31 5 9 5 3 x383h9
  | 10 => rootLookup 137 307 7 12 8 3 x383h10
  | 11 => rootLookup 211 479 9 13 9 3 x383h11
  | 12 => rootLookup 47 113 6 10 6 3 x383h12
  | _ => fun _=>none
def x383 : Forest := ⟨1407,12,fun j => x383samples[j]?.getD (0,0),x383columns,x383autos,x383levels,x383index⟩
set_option maxHeartbeats 0 in
theorem geomx383 : graphValid x383 (boundsBefore known42751) = true := graphPieces x383 (boundsBefore known42751) 4 1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tablesx383 : HGood x383 12 := by
  refine ⟨x383Sp,x383T,?_,?_⟩
  · intro k hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact spansBlock x383 8 0 [(8,8,0),(1,9,0)]
    · exact spansBlock x383 9 0 [(16,8,0),(18,9,0),(18,9,0),(2,9,0),(4,10,0)]
    · exact spansBlock x383 10 0 [(11,8,0),(18,9,0),(18,9,0),(18,9,0),(5,9,0),(18,10,0),(18,10,0),(18,10,0),(18,10,0),(18,10,0),(13,10,0),(10,11,0)]
    · exact spansBlock x383 11 0 [(3,8,0),(15,9,0),(18,10,0),(12,10,0)]
    · exact spansBlock x383 12 0 [(6,9,0)]
  · intro k hk
    interval_cases k <;> decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl383 : Impossible false (graphGoal 1407) 12 (vars 1407).toFinset := plainA (q:=383) (prior:=boundsBefore known42751) (before_sound known42751 valid42751) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2431 : Lower false (varsX 2431) (graphGoal 2431) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (hIndex (g:=x383) (i:=0) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known2431 := extendKnown known42751 13 [(9599,[100,131,82,16]),(17343,[114,67,84,48,33,97,128]),(9711,[100,131,116,50,33,16,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2431 : Known false known2431 := extendKnown_ok (m:=2431) valid42751 low2431 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1407 : Lower false (varsX 1407) (graphGoal 1407) 13 :=
  strong_full (q:=1407) (rs:=[16, 4, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (hIndex (g:=x383) (i:=1) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known1407 := extendKnown known2431 13 [(28143,[33,80,112,97,130,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1407 : Known false known1407 := extendKnown_ok (m:=1407) valid2431 low1407 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low54143 : Lower false (varsX 54143) (graphGoal 54143) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 34, 4, 1, 5, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (hIndex (g:=x383) (i:=2) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known54143 := extendKnown known1407 13 [(54143,[]),(64447,[117,80,66,130,96,16]),(44015,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid54143 : Known false known54143 := extendKnown_ok (m:=54143) valid1407 low54143 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44415 : Lower false (varsX 44415) (graphGoal 44415) 13 :=
  strong_full (q:=1407) (rs:=[16, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (hIndex (g:=x383) (i:=3) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known44415 := extendKnown known54143 13 [(44927,[84,131,98]),(47999,[101,66,16]),(53119,[98,82,16,66,49,128]),(58239,[82,129,48]),(69503,[84,66,16,98,129,48]),(58303,[118,133,33,48]),(60351,[114,67,84,48,33,97,128]),(69567,[117,80,66,130,96,16]),(42991,[83,114,99,33,16,64]),(60399,[80,81,114,66,50,129,96]),(69103,[116,50,129,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44415 : Known false known44415 := extendKnown_ok (m:=44415) valid54143 low44415 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43903 : Lower false (varsX 43903) (graphGoal 43903) 13 :=
  strong_full (q:=1407) (rs:=[10, 1, 2, 5, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (hIndex (g:=x383) (i:=4) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known43903 := extendKnown known44415 13 [(43903,[]),(46463,[84,131,98]),(48511,[101,66,16]),(51071,[100,131,82,16]),(43455,[98,118,81,130,50,65]),(43967,[118,130,81]),(54207,[116,100,49,32,81,128]),(58815,[114,67,84,48,33,97,128]),(49647,[83,114,99,33,16,64]),(51183,[100,131,116,50,33,16,80]),(54255,[116,83,32]),(55791,[83,133,115,67,32,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43903 : Known false known43903 := extendKnown_ok (m:=43903) valid44415 low43903 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42879 : Lower false (varsX 42879) (graphGoal 42879) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (hIndex (g:=x383) (i:=5) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known42879 := extendKnown known43903 13 [(42879,[]),(60287,[82,129,48]),(44991,[98,118,81,130,50,65]),(69615,[33,80,112,97,130,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42879 : Known false known42879 := extendKnown_ok (m:=42879) valid43903 low42879 (by decide +kernel)
def rootGroups (g : Forest) (k : Nat) : Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | first, (ar,n)::xs =>
    (header g k first n ar = true ∧ rowCut g k first n ar 0 ar = true) ∧
      rootGroups g k (first+n) xs

theorem rootGroupsBlock (g : Forest) (k first : Nat) (xs : List (Nat × Nat))
    (checked : rootGroups g k first xs) : block g k first (xs.map Prod.snd).sum = true := by
  induction xs generalizing first with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨ar,n⟩ := x
    obtain ⟨⟨hd,hr⟩,rest⟩ := checked
    exact block_merge (cutsBlock hd hr) (ih (first+n) rest)

theorem rootSpan (g : Forest) (k start : Nat) (groups : List (Nat × Nat))
    (h : rootGroups g k start groups := by
      simp only [rootGroups]
      repeat' apply And.intro
      all_goals first | exact True.intro | decide +kernel) :
    block g k start (groups.map Prod.snd).sum = true := rootGroupsBlock g k start groups h




namespace SignedClique
def Split (p n : Row) (v : Sig) : Prop := bit p v ≠ bit n v

def Sole (T : Sig) (S : Finset Sig) (p n : Row) (a : Sig) : Prop :=
  (bit p T = true ∧ bit n T = false) ∧ ∀ x ∈ S, Split p n x → x = a

def Conflict (T : Sig) (S : Finset Sig) (a b : Sig) : Prop :=
  ∃ p n, Split p n a ∧ Split p n b ∧ (∃ r, Sole T S p r a) ∧ (∃ r, Sole T S p r b) ∧
    (∃ r, Sole T S r n a) ∧ (∃ r, Sole T S r n b)

def Coloring (T : Sig) (S : Finset Sig) (m : Nat) (c : Sig → Nat) : Prop :=
  (∀ a ∈ S, c a < m) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Conflict T S a b → c a ≠ c b


theorem bit_combine (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
def flipL (d : Nat) (x : Bool) := if d<3 then x else !x
def flipR (d : Nat) (x : Bool) := if d=2 then !x else x
def neededL (d : Nat) := decide (d=0 ∨ d=2)
def neededR (d : Nat) := decide (d=0 ∨ 3≤d)
def upd (d : Nat) (a b w : Sig) (x : Bool) :=
  if w=a then flipL d x else if w=b then flipR d x else x
theorem upd_ne {x y : Bool} (h : x≠y) (d : Nat) (a b w : Sig) : upd d a b w x ≠ upd d a b w y := by
  unfold upd flipL flipR
  split_ifs <;> simp_all
theorem split_inputs {p n d a b} (h : Split p n (bin d a b)) : Split p n a ∨ Split p n b := by
  by_contra! bad
  simp only [Split,ne_eq,not_not] at bad h
  exact h (by rw [bit_combine,bit_combine,bad.1,bad.2])
variable {T : Sig} {U : Finset Sig} {a b : Sig} {d : Nat}
def renWire (a b new w : Sig) := if w = a ∨ w = b then new else w

theorem move_sole {w p n} (h : Sole T (insert a (insert b U)) p n w) (free : w ∈ U → w ≠ a ∧ w ≠ b) :
    Sole T (insert (bin d a b) U) p n ((renWire a b (bin d a b)) w) := by
  refine ⟨h.1,?_⟩
  intro y hy sy
  rcases Finset.mem_insert.mp hy with rfl | hu
  · rcases split_inputs sy with sa | sb
    · have e := h.2 _ (Finset.mem_insert_self _ _) sa
      simp [renWire,← e]
    · have e := h.2 _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) sb
      simp [renWire,← e]
  · have e := h.2 _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) sy
    subst y
    simp [renWire,(free hu).1,(free hu).2]

theorem force_gate {p n w} {k : Nat} (h : Sole T (insert a (insert b U)) p n w) (dropped : w ∉ U)
    (run : Live true T k (insert (bin d a b) U)) : Split p n (bin d a b) := by
  obtain ⟨x,hx,sep⟩ := live_row_difference run (show bit p T ≠ bit n T by simp [h.1.1,h.1.2])
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact sep
  · exact False.elim (dropped (h.2 _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)) sep ▸ hx))


theorem sensitiveRawL {p n d x y} (varies : Split p n (bin d x y)) (fixed : ¬Split p n y) :
    bit p y = neededR d ∧ bit n y = neededR d ∧
    bit p (bin d x y) = flipL d (bit p x) ∧ bit n (bin d x y) = flipL d (bit n x) := by
  unfold Split at *
  rw [bit_combine,bit_combine] at varies
  rw [bit_combine,bit_combine]
  rcases Nat.lt_or_ge d 3 with h|h
  · interval_cases d <;> cases hp : bit p x <;> cases hq : bit p y <;>
      cases hn : bit n x <;> cases hr : bit n y <;> simp_all [neededR,flipL]
  · have h0 : d≠0 := by omega
    have h1 : d≠1 := by omega
    have h2 : d≠2 := by omega
    cases hp : bit p x <;> cases hq : bit p y <;>
      cases hn : bit n x <;> cases hr : bit n y <;> simp_all [neededR,flipL,Nat.not_lt_of_ge]

theorem sensitiveRawR {p n d x y} (varies : Split p n (bin d x y)) (fixed : ¬Split p n x) :
    bit p x = neededL d ∧ bit n x = neededL d ∧
    bit p (bin d x y) = flipR d (bit p y) ∧ bit n (bin d x y) = flipR d (bit n y) := by
  unfold Split at *
  rw [bit_combine,bit_combine] at varies
  rw [bit_combine,bit_combine]
  rcases Nat.lt_or_ge d 3 with h|h
  · interval_cases d <;> cases hp : bit p x <;> cases hq : bit p y <;>
      cases hn : bit n x <;> cases hr : bit n y <;> simp_all [neededL,flipR]
  · have h0 : d≠0 := by omega
    have h1 : d≠1 := by omega
    have h2 : d≠2 := by omega
    cases hp : bit p x <;> cases hq : bit p y <;>
      cases hn : bit n x <;> cases hr : bit n y <;> simp_all [neededL,flipR,Nat.not_lt_of_ge]

theorem sensitive_left {p n} {k} (h : Sole T (insert a (insert b U)) p n a) (dropped : a ∉ U) (ab : a ≠ b)
    (run : Live true T k (insert (bin d a b) U)) :
    bit p b = neededR d ∧ bit n b = neededR d ∧ bit p (bin d a b) = flipL d (bit p a) ∧ bit n (bin d a b) = flipL d (bit n a) := by
  apply sensitiveRawL (force_gate h dropped run)
  exact fun v => ab (h.2 _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) v).symm
theorem sensitive_right {p n} {k} (h : Sole T (insert a (insert b U)) p n b) (dropped : b ∉ U) (ab : a ≠ b)
    (run : Live true T k (insert (bin d a b) U)) :
    bit p a = neededL d ∧ bit n a = neededL d ∧ bit p (bin d a b) = flipR d (bit p b) ∧ bit n (bin d a b) = flipR d (bit n b) := by
  apply sensitiveRawR (force_gate h dropped run)
  exact fun v => ab (h.2 _ (Finset.mem_insert_self _ _) v)
theorem preserve_bits {p n w} {k} (h : Sole T (insert a (insert b U)) p n w)  (free : w ∈ U → w ≠ a ∧ w ≠ b)
    (run : Live true T k (insert (bin d a b) U)) (ab : a ≠ b) : bit p ((renWire a b (bin d a b)) w) = upd d a b w (bit p w) ∧ bit n ((renWire a b (bin d a b)) w) = upd d a b w (bit n w) := by
  by_cases wa : w=a
  · subst w
    simpa [renWire,upd] using (sensitive_left h (fun hu => (free hu).1 rfl) ab run).2.2
  by_cases wb : w=b
  · subst w
    simpa [renWire,upd,Ne.symm ab] using (sensitive_right h (fun hu => (free hu).2 rfl) ab run).2.2
  simp [renWire,upd,wa,wb]

theorem move_conflict {v w k} (h : Conflict T (insert a (insert b U)) v w) (run : Live true T k (insert (bin d a b) U)) (ab : a ≠ b)
    (hv : v ∈ U → v ≠ a ∧ v ≠ b) (hw : w ∈ U → w ≠ a ∧ w ≠ b) :
    Conflict T (insert (bin d a b) U) ((renWire a b (bin d a b)) v) ((renWire a b (bin d a b)) w) := by
  obtain ⟨p,n,sv,sw,⟨u,hu⟩,⟨r,hr⟩,⟨s,hs⟩,⟨t,ht⟩⟩ := h
  refine ⟨p,n,?_,?_,⟨u,move_sole hu hv⟩,⟨r,move_sole hr hw⟩,⟨s,move_sole hs hv⟩,⟨t,move_sole ht hw⟩⟩
  · simpa [Split,(preserve_bits hu hv run ab).1,(preserve_bits hs hv run ab).2] using upd_ne sv d a b v
  · simpa [Split,(preserve_bits hr hw run ab).1,(preserve_bits ht hw run ab).2] using upd_ne sw d a b w

theorem distinct_children {k : Nat} (ab : a ≠ b) (au : a ∉ U) (bu : b ∉ U)
    (run : Live true T k (insert (bin d a b) U)) : ¬Conflict T (insert a (insert b U)) a b := by
  rintro ⟨p,n,pa,pb,⟨q,pA⟩,⟨r,pB⟩,⟨s,nA⟩,⟨u,nB⟩⟩
  exact pa ((sensitive_right pB bu ab run).1.trans (sensitive_right nB bu ab run).2.1.symm)

theorem conflict_symm {S v w} (h : Conflict T S v w) : Conflict T S w v := by
  obtain ⟨p,n,sv,sw,pa,pb,na,nb⟩ := h
  exact ⟨p,n,sw,sv,pb,pa,nb,na⟩

theorem rename_mem {v} (hv : v ∈ (insert a (insert b U))) : (renWire a b (bin d a b)) v ∈ (insert (bin d a b) U) := by
  rcases Finset.mem_insert.mp hv with rfl | hv
  · simp [renWire]
  · rcases Finset.mem_insert.mp hv with rfl | hu
    · simp [renWire]
    · by_cases h : v = a ∨ v = b <;> simp [renWire,h,hu]

theorem rename_ne {v w k} (hv : v ∈ (insert a (insert b U))) (hw : w ∈ (insert a (insert b U))) (ne : v ≠ w)
    (fresh : (bin d a b) ∉ (insert a (insert b U))) (ab : a ≠ b) (fv : v ∈ U → v ≠ a ∧ v ≠ b)
    (fw : w ∈ U → w ≠ a ∧ w ≠ b) (run : Live true T k (insert (bin d a b) U))
    (h : Conflict T (insert a (insert b U)) v w) : (renWire a b (bin d a b)) v ≠ (renWire a b (bin d a b)) w := by
  have zv : (bin d a b) ≠ v := fun e => fresh (e ▸ hv)
  have zw : (bin d a b) ≠ w := fun e => fresh (e ▸ hw)
  have noab : ¬(v=a ∧ w=b) := by
    rintro ⟨rfl,rfl⟩
    exact distinct_children ab (fun hu => (fv hu).1 rfl) (fun hu => (fw hu).2 rfl) run h
  have noba : ¬(v=b ∧ w=a) := by
    rintro ⟨rfl,rfl⟩
    exact distinct_children ab (fun hu => (fw hu).1 rfl) (fun hu => (fv hu).2 rfl) run (conflict_symm h)
  by_cases va : v=a <;> by_cases vb : v=b <;> by_cases wa : w=a <;> by_cases wb : w=b <;>
    simp_all [renWire] <;> grind only

theorem feasible {k S} (run : Live true T k S) :
    ∃ m c, m+S.card ≤ k+2 ∧ Coloring T S m c := by
  classical
  induction run using Live.ind with
  | stop hp =>
    refine ⟨1, fun _ => 0, by simp, by simp [Coloring]⟩
  | @binary k U a b d _ ha hb ab fresh tail ih =>
    obtain ⟨m,c,cost,limited,good⟩ := ih
    let keep : Finset Sig := ({a,b} : Finset Sig) ∩ U
    have inKeep {v : Sig} : v ∈ keep ↔ (v=a ∨ v=b) ∧ v∈U := by simp [keep]
    have free (v) (e : v ∉ keep) : v ∈ U → v ≠ a ∧ v ≠ b := by
      intro hu
      constructor <;> intro h <;> exact e (inKeep.mpr ⟨by simp [h],hu⟩)
    have fz : bin d a b ∉ U := fun h => fresh (by simp [h])
    have sizes := Finset.card_union_add_card_inter ({a,b} : Finset Sig) U
    have sz : ({a,b} : Finset Sig).card=2 := by simp [ab]
    have un : ({a,b} : Finset Sig) ∪ U = insert a (insert b U) := by ext w; simp [or_assoc]
    rw [un,sz] at sizes
    change (insert a (insert b U)).card + keep.card = 2 + U.card at sizes
    rw [Finset.card_insert_of_notMem fz] at cost
    let rename := renWire a b (bin d a b)
    let next := fun v => if v ∈ keep then m + keep.toList.idxOf v else c (rename v)
    refine ⟨m+keep.card,next,by omega,?_,?_⟩
    · intro v hv
      by_cases h : v∈keep
      · have le := List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr h)
        simpa [next,h] using le
      · have le := limited _ (rename_mem (d:=d) hv)
        simp only [next,rename,h,ite_false]
        omega
    · intro v hv w hw ne edge
      by_cases kv : v∈keep <;> by_cases kw : w∈keep
      · simp only [next,kv,kw,ite_true,ne_eq,Nat.add_left_cancel_iff]
        intro same
        have av : keep.toList[keep.toList.idxOf v]? = some v := List.getElem?_idxOf (Finset.mem_toList.mpr kv)
        have aw : keep.toList[keep.toList.idxOf w]? = some w := List.getElem?_idxOf (Finset.mem_toList.mpr kw)
        exact ne (Option.some.inj (av.symm.trans ((congrArg (fun i => keep.toList[i]?) same).trans aw)))
      · have low := limited _ (rename_mem (d:=d) hw)
        simp only [next,kv,kw,ite_true,ite_false]
        change m + _ ≠ c (renWire a b (bin d a b) w)
        omega
      · have low := limited _ (rename_mem (d:=d) hv)
        simp only [next,kv,kw,ite_true,ite_false]
        change c (renWire a b (bin d a b) v) ≠ m + _
        omega
      · have hg := good _ (rename_mem hv) _ (rename_mem hw)
          (rename_ne hv hw ne fresh ab (free _ kv) (free _ kw) tail edge)
          (move_conflict edge tail ab (free _ kv) (free _ kw))
        simpa [next,kw,kv,rename] using hg


def onlyWire (target : Sig) (ws : List Sig) (p n : Row) (v : Sig) :=
  bit p target && !bit n target &&
    ws.all fun x => x == v || bit p x == bit n x

theorem onlyWire_sound {target ws p n v} (h : onlyWire target ws p n v = true) :
    Sole target ws.toFinset p n v := by
  simp only [onlyWire,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1,?_⟩
  intro x hx sep
  change bit p x ≠ bit n x at sep
  have g := h.2 x (List.mem_toFinset.mp hx)
  simpa [sep] using g

def witnessRow (code shift : Nat) : Row := Fin.ofNat 512 (code >>> shift)

def edgeOK (target : Sig) (ws : List Sig) (a b : Sig) (code : Nat) :=
  let p := witnessRow code 0
  let n := witnessRow code 9
  a != b && (bit p a != bit n a && bit p b != bit n b) &&
    onlyWire target ws p (witnessRow code 18) a &&
    onlyWire target ws p (witnessRow code 27) b &&
    onlyWire target ws (witnessRow code 36) n a &&
    onlyWire target ws (witnessRow code 45) n b

theorem edgeOK_sound {target ws a b code} (h : edgeOK target ws a b code = true) :
    a ≠ b ∧ Conflict target ws.toFinset a b := by
  simp only [edgeOK, Bool.and_eq_true, bne_iff_ne] at h
  exact ⟨h.1.1.1.1.1,_,_,h.1.1.1.1.2.1,h.1.1.1.1.2.2,
    ⟨_,onlyWire_sound h.1.1.1.2⟩,⟨_,onlyWire_sound h.1.1.2⟩,
    ⟨_,onlyWire_sound h.1.2⟩,⟨_,onlyWire_sound h.2⟩⟩

def oneRow (target : Sig) (ws : List Sig) (a : Sig) : List Sig → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | b :: bs, code :: codes => edgeOK target ws a b code && oneRow target ws a bs codes

def everyEdge (target : Sig) (ws : List Sig) : List Sig → List Nat → Bool
  | [], codes => codes.isEmpty
  | a :: bs, codes => oneRow target ws a bs codes && everyEdge target ws bs (codes.drop bs.length)

theorem oneRow_sound {target ws a bs codes} (h : oneRow target ws a bs codes = true) :
    ∀ b ∈ bs, a ≠ b ∧ Conflict target ws.toFinset a b := by
  induction bs generalizing codes with
  | nil => simp
  | cons b bs ih =>
    cases codes with
    | nil => simp [oneRow] at h
    | cons code codes =>
      simp only [oneRow, Bool.and_eq_true] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact edgeOK_sound h.1
      · exact ih h.2 x hx

theorem colorsDistinct {target ws vs codes m c}
    (col : Coloring target ws.toFinset m c) (inside : ∀ v ∈ vs, v ∈ ws)
    (h : everyEdge target ws vs codes = true) : (vs.map c).Nodup := by
  induction vs generalizing codes with
  | nil => simp
  | cons a vs ih =>
    simp only [everyEdge, Bool.and_eq_true] at h
    have memA := List.mem_toFinset.mpr (inside a (by simp))
    have sub := fun v hv => inside v (List.mem_cons_of_mem a hv)
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_,ih sub h.2⟩
    intro same
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp same
    obtain ⟨ne,edge⟩ := oneRow_sound h.1 b hb
    exact col.2 a memA b (List.mem_toFinset.mpr (sub b hb)) ne edge eq.symm

def check (target : Sig) (cap : Nat) (ws : List Sig) (ids codes : List Nat) :=
  decide ws.Nodup && decide (cap+2 < ids.length+ws.length) &&
    ids.all (fun j => decide (j<ws.length)) &&
    everyEdge target ws (ids.map fun j => ws.getD j zero) codes

theorem sound {target cap ws ids codes} (h : check target cap ws ids codes = true) :
    Impossible true target cap ws.toFinset := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  let vs := ids.map fun j => ws.getD j zero
  have inside : ∀ v ∈ vs, v ∈ ws := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
    have lt := h.1.2 j hj
    simp [List.getD_eq_getElem?_getD,lt]
  intro k le run
  obtain ⟨m,c,cost,col⟩ := feasible run
  have nd := colorsDistinct (vs:=vs) col inside h.2
  have sub : (vs.map c).toFinset ⊆ Finset.range m := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
    exact Finset.mem_range.mpr (col.1 v (List.mem_toFinset.mpr (inside _ hv)))
  have card := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup nd, List.length_map, Finset.card_range] at card
  rw [List.toFinset_card_of_nodup h.1.1.1] at cost
  have len : vs.length = ids.length := by simp [vs]
  have tooBig := h.1.1.2
  omega

end SignedClique



namespace SignedClique
def oddCheck (target : Sig) (cap : Nat) (ws : List Sig) (ids codes : List Nat) :=
  oddCertificate (edgeOK target ws) cap ws ids codes

theorem oddSound {target cap ws ids codes} (h : oddCheck target cap ws ids codes=true) :
    Impossible true target cap ws.toFinset := by
  apply oddCertificateSound (edge:=edgeOK target ws) _ h
  intro k run
  obtain ⟨m,c,cost,bound,valid⟩ := feasible run
  refine ⟨m,c,cost,fun v hv => bound v (List.mem_toFinset.mpr hv),?_⟩
  intro x hx y hy t ok
  obtain ⟨ne,conflict⟩ := edgeOK_sound ok
  exact valid x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy) ne conflict
end SignedClique


def rootSSamples : Array (Bits × Bits) := #[((-0x362537fcf33efd3e18bf2a2),0x485ac80140c10240a14004e),((-0x7addeeb36361ef4dff048fd),0x52011449c0e10900099711),(0x20c661f1060474c6543a85,0x4663b000040446562880),(0x4308090e0879b8f999c3e6,0x2080800087938b8888346),(0x7c1071f03081c301e1fcf8,0x781071e03080c301617cb0),(0x80107e0030fe03fe01ff00,0x103800102403f401ff01),(0x7001f80003f0003fffe0000,0x5001c00003f0002fff60000),(0x7ffe000003ffffc00000000,0x7ffa000002fdbf800000000),(0x7ffffffffc0000000000000,0x2fde3c7fe80000000000020)]
set_option maxRecDepth 16384 in
def rootSCols : List ColumnInfo := [(0,1,332,412316861106,8),(0,4,305,77309412042,8),(0,16,486,521,10),(0,64,189,770,10),(0,256,23,412316861160,8),(1,0,494,134218256,12),(1,2,312,824633721540,7),(1,16,486,520,9),(2,0,445,77309411904,12),(2,64,189,768,9),(3,0,428,77443629648,9),(3,128,344,548,6),(4,0,379,824633721472,12),(4,128,347,544,9),(5,0,378,824633721472,8),(5,2,312,824633721536,6),(5,16,354,824633721480,6),(5,128,330,134218288,6),(6,0,313,901943132864,9),(7,0,504,0,7),(7,128,344,544,5),(8,0,487,33554960,12),(8,4,305,77309412034,7),(8,16,486,513,9),(8,256,23,412316861152,7),(9,0,486,0,8),(9,16,486,0,8),(10,0,437,77309411904,8),(10,4,305,77309412032,6),(10,64,165,33555216,6),(11,0,480,1049092,5),(11,16,480,1049092,5),(12,0,355,824667275920,9),(13,0,354,824633721472,5),(13,16,354,824633721472,5),(14,0,497,0,7),(15,0,480,0,4),(16,0,495,0,13),(16,32,78,897,7),(17,0,494,0,11),(18,1,332,412316861088,6),(19,0,428,77309411904,8),(20,0,355,824652595848,9),(20,2,424,577,6),(20,8,99,824633721728,6),(21,0,490,0,7),(21,2,424,576,5),(24,0,487,0,11),(25,0,486,0,8),(26,0,485,0,7),(26,4,353,640,5),(28,0,355,824633721472,8),(32,0,351,412316861056,12),(32,1,332,412316861074,7),(32,16,198,15393162789641,7),(32,256,23,412316861128,7),(33,0,334,412451078800,9),(34,0,349,412316861056,8),(34,1,332,412316861072,6),(35,0,476,0,7),(36,0,347,0,8),(36,128,347,0,8),(37,128,330,134218256,5),(39,0,344,0,4),(40,0,215,15393162789632,8),(40,256,23,412316861120,6),(41,16,198,15393162789632,5),(48,0,334,412316862081,9),(48,1,332,412316861058,6),(49,0,334,412316861056,8),(50,1,332,412316861056,5),(56,0,455,0,7),(56,256,135,576,5),(57,0,198,15393162789632,5),(64,0,447,0,13),(64,8,163,788,7),(64,256,23,412316861096,7),(65,0,428,134242834,9),(66,0,445,0,11),(66,1,396,560,6),(67,0,428,134218256,8),(69,2,312,824633721472,5),(72,0,167,13194173088528,9),(72,4,305,642,6),(74,0,437,0,7),(74,4,305,640,5),(80,0,431,0,11),(82,0,428,3585,8),(82,1,396,544,5),(83,0,428,0,7),(84,2,424,513,5),(84,8,163,768,5),(88,0,167,13194139534080,8),(96,1,396,530,6),(96,256,23,412316861064,6),(98,1,396,528,5),(104,256,23,412316861056,5),(112,1,396,514,5),(128,0,383,0,13),(128,1,332,562,7),(128,4,305,77309411914,7),(128,8,99,788,7),(128,32,30,17179870017,7),(129,32,30,17179870016,6),(130,1,332,560,6),(132,0,379,0,11),(132,8,99,784,6),(133,0,378,0,7),(133,2,312,576,5),(133,16,354,520,5),(134,0,313,77309411904,8),(135,0,312,77309411904,5),(136,0,355,33817108,9),(138,4,305,77309411904,5),(140,0,355,33554960,8),(144,0,367,0,11),(144,1,332,546,6),(144,32,78,769,6),(146,1,332,544,5),(146,4,353,520,5),(148,0,355,18874888,8),(152,4,353,514,5),(156,0,355,0,7),(160,0,351,0,11),(160,1,332,530,6),(161,0,334,134218256,8),(161,16,326,520,5),(162,1,332,528,5),(164,0,347,0,8),(168,0,343,0,7),(168,256,23,576,5),(169,0,326,0,4),(176,0,334,1537,8),(176,1,332,514,5),(177,0,334,0,7),(193,2,312,516,5),(193,32,30,768,5),(194,4,305,520,5),(196,2,312,513,5),(198,0,313,0,7),(200,4,305,514,5),(200,256,23,544,5),(208,0,303,0,8),(224,256,23,520,5),(256,0,191,17179869760,12),(256,8,99,824633721492,7),(256,32,30,17179869889,7),(256,64,189,514,9),(257,0,190,17179869760,8),(257,32,30,17179869888,6),(258,0,189,0,8),(258,64,189,0,8),(259,64,156,4294967840,5),(260,0,123,824633721472,8),(260,8,99,824633721488,6),(264,0,167,17213424208,9),(265,16,166,17179869760,5),(266,64,165,33554960,5),(268,0,243,0,7),(268,64,177,514,5),(272,0,167,17186161224,9),(272,32,78,641,6),(273,32,78,640,5),(276,8,99,824633721472,5),(280,0,167,17179869760,8),(288,0,31,429496730304,9),(288,16,198,521,6),(289,0,222,0,7),(292,128,27,17179869760,5),(296,0,215,0,7),(300,0,83,0,4),(320,0,191,0,11),(321,32,30,640,5),(322,0,189,0,8),(323,0,156,4294967840,5),(324,0,187,0,7),(324,8,163,528,5),(328,0,167,33554960,8),(336,0,167,6291976,8),(336,8,163,516,5),(344,0,167,0,7),(352,0,31,412316861056,8),(356,0,27,0,4),(385,32,30,17179869760,5),(388,0,123,0,7),(388,8,99,528,5),(416,0,31,17179869760,8),(416,64,29,514,5),(420,0,27,17179869760,5),(448,32,30,513,5),(480,0,31,0,7)]
def rootSAutos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def rootSD14 (i : Nat) : Nat := 0x1892896adecbda5389d3ff
def rootSH14 (i : Nat) : Nat := 0x2f0000014edb20106622b8c2510416615140348080
def rootSD13 (i : Nat) : Nat := 0x2ac6869276ae690c0d4202b62a509daab1a0549dab9a456114a3489d6ab1a054d3ab9a45619622709cb2cd97100ffd30ffd20ffd10
def rootSH13 (i : Nat) : Nat := 0x310815207a1a1856a8d3a40000372b480e2304301249142c9b9e8e8724b382c72589335c8f91509a2e05557399451794c982231d89f1adcc108500900e8182cfc5d029a6cccbb35d8b2e2b723c552840469a5a860000cd0048e03402020002888800380004010010c20407400825c0
def rootSD12 (i : Nat) : Nat := 0x23443097cd07dc31971b81a869ab857622d22753a1d5e181803e5208b13ec4052d3bd972a7034e24045cd315c20131e83a89e696ac3264690a8700d6698ab2e35a104b8b313cd2d585cf6ae4eeaca904f084d205d292f9a48660450288b9a610d5835d58e409e9497cd2233815eac056ae34cd0382b41c1ac2389d2f9a54e0ba0d588a8ae683775614e2b13a9d348c209b49b04f349ec7d66f0c8289e0292f93b626ae27787a1c03414e698a93c09c10b4b5713916d028a50801aeacadc553d0f5340ee275a64e219e1013c1e92e1c015d5e6811826b4c9d13a5e45bf0c6ac3b07c1a5a762eaf7b4546c1658d5a2b9a025d5e2a1dad2098b2a6ac38083ab0a734c546b89d4e04d61c357d5e683969534a5e09a4900e3340c3151ae276ac13484fa50199a7560d69d34a5e90280ceaf34c541204c275a64e5086386698a8af8435734c4e90941a283abcd080c320593b624bc5960240af579a62a5d0272744eb48b2b083abcd0bec33625381a4015d5e698a8fa0716934c4ea7281aeacbac543b5a459393702f579a08a45e9409cd297a897eac800ec13d8915165013ec5a5757bded3a70328cd04ec547d2d0139a6276ad3b16950ac0bd5ef7b4e9c0ca750f2cb0d6e6ac76a3279e5823160f9e8dc21a2d8896bd5413c52490a4f28d34b68a148707445a044c2f817c003ffb02987ff64530ffecc241ffd81483ffaa6907ff64d20ffe98a41ffd91483ffb06887ff60910ffea9221ffd32443ffb26887ff64910fff0ca41ffe39483ffd12907fe4c120ffc902217fd98482ffb26885ff64910bff0ca617fe19482ffc52885ff8e520bff1ca21fbe494c2ffd12905ef92530
def rootSH12 (i : Nat) : Nat := 0x5db7fd9f512a4ab02bd116e8a11900c00289ae0af60c39e023775c00082911a614702129e921c0a60c0037d9e00804d193009e2c5bb488524130066437a119a4621e4afa5a000215d48b20210148ae449033508b2f847d5d59202096aacd1baa9613f87800811336f50451cb82e97590c550f4921336975a35016a193a500b3416400107fd0c1d7e473a80aaa81b28e0a6994310d41997b2868106c50b0cf8622a928b4ba65bc40642f1014242eddc56b9955b31afc183034c3ad0196307bcca180c000099c8095c308ec93c2370a0e0c3a38944105802a0bf3a855dd0f5097a20ecf60da0b4a5b000008e27c95d82a163c0000658af000101f23602ae03b43e23403580f4a99a21d2c733b9625b4d9413602d392f008011e0393332e528100a794fd8fa01a022b10988014463ba16421c0d47903568adc106a09214d26c027463549e02400004422c043081228bbc2d84e18d042c851e9213047512fa2e08bb98583e1c3c90856083708234fe47382c123c0e20c896a015af104449476668ef608b83f003d66e0d902f42041790d2d84001c98e4bccd7aac8d2e4b7812432a02dad5386cb3b250b8002f819e05e05cd07422a9700d4842816d0ef00084401508c90911bc58ea8c5a5fd2dd0700c100b5b5d12c550472a4c16800012d85c92e5a112000835d9ba826a5a00c69ded87090dada0e2f1c01720552780cb48a22e42b28fcb03951167e0aba7adcbea22c4f026815465c4a7086820c0468e960d81b011816bb4f59153401af2b9828d87e88400095180020f070e20cc2aa09e000a4d49640002a086685e40007bdb696d6705a465abe42fa11cabd4cf08fe51343fb0751b65aa8bc0160d9a09b403827183ec960c221c8a900630821c5c34491902589ed0a8891641d5702120644b0054913614d94a26bd06940610d81d12fb579ab9b2925c34920a0d4721265282b380e1078543589201123906f18d20080041000132301a8044410300001840450605005419201105023a0401d029c000000428f0a189440844608404d1091c0000c1c0800e0200380087c00502a018008040821814002001421008000002a290031e0d28e305420d164420802a00800c00c03160819e1ce40210014c00025c003005009a0c00206000028000140820000b93000003300000011c30685062c01e160490c00b480000340010008482
def rootSD11 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x37fe2a64d10bff8a9914c37fda58e520dffaa5324437fda3a2520bff6a1914c37fd8364910dff65592442ffe8a64530dffaa5834437fda960520dff6a5524437fda864910dff661924437fda364910dffaa5524437fea960530dffaa581483ffd5364520fff54e19483ffda360910fff6a532443ffe3a60910fff69582443ffda960910fff60993443ffd5264d10fffa6982443ffe5a60910fff6a583443ffd8364910fff54d92443ffda354910fff6a552443ffd8564d10fff61592443ffd5366120fff6a553483ffca954d20fffaa553483ffd53a2520fff6a5814c3ffd9360520fff549914c3ffd5260530fff54d81483ffd5360910fff60d52443ffd854c910ffe68131483ff9a84c120ffe66130483ff9814c120ffe69530483ff9954c120ffe54530483ff9914c120ffe61520443ff98348110ffe6a120443ff99848110ffe54d20443ff9a548110ffe65520443ff9a348110ffe64d204437fda166120dff6a5824437fd9864d20dff655934837fd8564d10dff661914c37fd8264d10dff655914c37fd5264d10dff661314837fd9864520dff54d92443bfd9860520bff6a191482ffda886520bff6a239482ffda564d20bff69639482ffda364520bff68e19482ffda3a2520ffb60952443ffa0a66120dff86998482ffe1a66120bff869934837fd5286530ffe86530483ff58186520dff662194837fd5386520bff8a9934437fd858a510dff60e294437fd538a510bffa6981482ffe3a66120bff8e982442ffe3a60520bff8e9524437fd988e520dff8e5814837fda88e520dff616394437fd828e510dff54a394437fea94c520fef92993483fbe4960530bff96982442ffe5a64d20ffe965304837fe5964d20dff965314837fea954d20fbf9a981483dfe7a54910bffa29934837fe8a64d10bffa2993443ffa894c120dff54e894837fe8964d20dffa25314837fea960910ffc54520443fe9524c120dfe66130483fd9534c120ff64c5304837f99348110ffa549204427fda864d109ff6a1924427fda8865309ff6a2194827fda88a5109ff6a2394827fda88e5109ff696194c27fda58a5109ff696394827fda58e5109ff68d924427fda3865209ff68e294427fda3a2520bbf69a894827fca954d209ff2a5314827fda2865309ff68a394427fda18e5209ff68689482ffa0a66120dfe82993442ffa0a64530bfe829934427fe1a66120bfe86930483ff21a48110dfd606194837f61a64910bfd869924427fe9a609109ff8a9934427fe3a64910ff68e5304837fa39481109ff8ea19482fbe4a64d20def92993442fbe4a64d10fee929304837be4960530def925914c37bda1925309ff969934427fe5a8e520bbf9a981482dfe7a549109ffa29934427fe8a64910dfea25304836fda6a2520cffa25984827fe8a865209bf69a894827be4a64d10 else 0x85d6270af53b348b008ca0762500e080ad22e42c9c20b1505b89c5f02c0279a6d58225051213cd38a86b35789c09a00484d1521ac23813300901a2745383e1161ac2a031026af560e80980f17cda6a70890349a2a2e3b10230762e42c81347abe681f45a66969d4bc09a39a7150fa2d334e27b5604d01f02e81301a89c4484613c81720681180a0f82744503140b903a08c0d07c1600c4fd884e87c046164a07040e270af9a43fdab05c8f5604c1d66969c068deae13a4e0455a4308133908e69c54cb893c4f9a5d582e481249c04005011f561e4308134fab074088358592817c102e057884c4e21c2309e4f34a2a2d713878c9c2c1b481f4f3404f9385f32fad22cc09a05801103404c5c85f05a7ad2c57bd813172164c0e01f0b2a9ccbc358b3026881dd2b9a7080bfeaf348890349e69c33270a3053d8bd585f1140695d8bd5f7bed20682c98108b0cd217c0c96867348fbc32cb819c2b816d5f6243353996ae9a029ad3d8aa707f160065229019a7dec428c42b4e0328e180d68a82d1242fb13e4e6f607d54bc4b88e6f62cc099b1a615e69c568405112d64313996cd20b99296107abe2a0f29a50cc9d89c1fa85cd1501a0a713e4e17c28c4781f55697562c447886c4e23424013489a13c10409d2fcd2eac112025734e2a178d5e69c4e2342401350020226ac46848026675625c1c0520d75383002d4734e2b9a7138972f62f57defb4e4e0346d67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd67359cd673534d38b49bd1273ecce6b348cc07283c8c71d4c5df13bc37b06bc066fd2bdaaf0dbb72e7fb8b6df1b67ed42b3c2c67b082bb8adc6ae8a9d6a39a6c2969a45e8c5a1ce80b9f127679c826c39942614973657b94a64cc926e43e8fde3798cca2d5895e1ef86ce14083360707ff5fb67d0df127aa9e5877c1dca7665d1b72a1c617095bf46e5db506bf9aa168e59fd6681959639987e602d7e55dc96f45a5d62f574956a540948450193b44d313054a7525647e51a744d10e241bcffc3ea8f373b68e933880db8356ccfe3284c442f9cb952d64afc2ad4a6327ec993255c8ef221c82a1f607911cd06cc1964612175854d139448810543ce0d142d2097c1f706681270380083011c000ffe829914c37fd9864d10dff64d914837fd9364910bff6a193442ffda864910bff69592442ffda364910dff64e194837fda386520bffa6982442ffe9a54910dff96993442ffe5a64d10fef92993443ffa0a64d10bff969914c3ff9a14c120dff6a2194837fda864d10dff695934437fda264d10dff649914c) else (if i < 3 then 0x2031855026118e4804b063026140231a02a9781807028e4e076cbdbda54be080700f5bd85502611900e02803b05c452ecbf0401a0402240984643ab036068318130b2118e04da7000112120a24c58d900278143b86039aba5f8148ab9013c23023205099b034dec228530ec784a0ec1340ca5f0c00f82e17cdef13bab609a0520685207f0b660780a90287115e17db4e4e14690340a4318860be28cc0aa0d01355a1540f8a1c9c2002352f6d2c0738304d5151281502f8717560c942783185d0260c8a1001da978254332705d17a12009b7b65ec1218168401308c144c5584b60ca1004c460463899c0b4204a0550d6118e0e28ae050aa2bc16871380d00e100cb89ac0a5cc46046486bc0a0f41f02d0e2600e68092e0c04603c4604646050660681106b08c608227b029b50d76ac09822413d12e048546277561e453d7bc9ca01c8144c88c08c5008c203401306417cc26702b081280281d02e38206118140d00a01e1c4e270560800bf5380d369834800ad38358462734e2a048c8669c4eeac28a04b3ab0261c41685f304032f8144105516004c24b7ba9ccbd61440db6901407c1718098671535a62c8797560ed00298a8180c95a43513d1522b819459584113025440c591155a59783b4990a11814078462841c180e2c8315c0a0384f08c064a132c54b90410c22e6b4e4e02789d41f020b1505a25f13e6932e862a250030231221672703dc4e4f549144f053c180b438981f54e0461058a8960d80b809851509e01c24419128a8a70301505e37b1471641da41d89e8702e458013146707e08e8a8951002ce2cb7b0269026070288c1981a0880909cd38659744e067b1508106092d5a195899a185c82d0411739381db7bc4ea6698140d00e074088c0299a00e074088a1001682208c413429d9a0130621b297851401301f4550508814660c05383662712c658289fd5f152d22a81e64ec4e0fd1c201b81901e6f809e69756089224313b9013407ca2681b819ec46f809bab03e80820e835bab026088c03c54c0a6f61830281317d9a424284f23805b830da86b75604c11244b85047004c53b900d80c69785150130ee1807eaf8a835a1893b92813076dec2d2a138208340691e83df5617e97b7b064b84e2780ae69a5eeac46046472501c1002fb340342c3348464c2704604da701a1619a423201180c03426809e4e65f5a430a7d593d07a0ea13813c9cdec1924018027214545c83d11d93b138820b4b00610409e081035a42e6277561c430ac4e03ded222ea708f034708215334886a9c04f1388f064912e0ec39569104164d45416e6917ceac09e2711e0c934541e8721042e42c9b86094084dec45d4e17a06902538a8950e55a42c83b383d08bd29bd8be15804e97888064a12a2e809d15ec41641d9c01023026096b48bec4f9385c861500743403 else 0x32ed8a4ba3dc4a4f60d21aa9c962b816a704132f25c079d8ad0c07604c4d041319bac4a6e1e93d415028ecd0d2d0c54b0809020a81480154233481a0aa08c171c4f52f0d01e80d0b008c713245606390118118c08a0641a7562e40984613d9a697b4e584007013c1981a172118e66c8a838a2adec1e88c08c813408e8ac0c69c1cb34846400a0d0c20098462a9781909c28832077939bda20540c52f0143785f0475a72732f50998198))
def rootSH11 (i : Nat) : Nat := (if i < 1 then 0x8de12483e2927a49403c834e408834813842ea0bfa13a07901e0000836c06f90860e650cecbad2732ec0002f4a4a269540460146c10686b20be08f529223305566415194e7a20b604503fe03e81268640000157025208a00000a703a0874926e0960064eb2038009e845d29d10d6068c14c947a3a609100128cf017287fdc228c35add47931b601401c0e38a09e142227e60783ecf4c81f20d4304494510fd67ed84f488916950c28c8e8783f7058841122f053324b8062e89042d68a8307482b41cc298d5880a010612203cce05808652b84d2806a32d55484740a580c00ab01980be90f6cbec91124782708b9a0d0f2f84cc15294972b324a8121586914ba4e610e23290e4494a13e92a365881d410540fb400b872150253c06380ce108a9ed250813c0aed82161d83ca01704f6069a2e004aa1816b158d809305361518022881802686e04f00ea818284c43b40e280be137a38b50820b2120c902109816f54ad8d529614280e75a420d7810807383d60f6016448900bb40b2026caaa4120faa01412cd53221303000af5ad848aa49294b01768a7041c21d82920bcb393625838602300fc402835886fba86d3edb76886125c926009209f2096144a2160772052c5f3cc54fb051e4cb390cc333d4a0bb03336dcd37806b0d5e88821a404b824a8f5836005184ba114831c1363cca4c983c60bd01da0fe8264a650494802820a86801d01538368016a3acd06bcc00c54a960d9ca3a05683be0d584b64962290d49050614b01c4140932081019f9147843615602c120105145555a5008d203080d24a282e954c0c23a82119a2760a8bc32e26d16210023e0154590491601e9695815680f382e40d8378918043ee5d847006783d201bb35484d81320ad00ef27da17a8a3c33cea2ca1c0e355200840002409982048b840a43e3a3002b026ac08802807b823a11bc94c12884d60a984ac93a25474b70000000153013a020e0200150d4d18c16ec0aaa0812385692ba70879a1728ee21ca753826293bd21211f8404143a0c00579038831b14e0b1a33b6de581c0c6526c0ba01fb27604a80b9a08b68b23b49575600590c000d3f000129000a0c2205290400215f390109110000021a002a2b003c000304231e2f001506028f0743010f0001060306330c283909020303005b000100000100020204001a1dab00000041830006040021040500000400000f9c051f0003150005260a0f02050103007b0000020611100c0e24050005000317dc0a0501010800120027030503171447480400043b02002655110002000000100b02240001000001010603002b1c010100160000390000003b36190c00040000030020080003080c0304071000110111020d0d010001a80801006100010005460d000030030a172d003c00060007011000112101140c420132062b0704 else 0x329380b6c66837c0b65ac80a129d8080d06849c33b4c1452d200c01900f780e8c410298867807e0ac2103462822c8fc21dc06a83740dc001f4f0009e91fa53b04008524ca00f4123840d65392c52a6047810a925692243c10ce800f6edb9b28cd82d68d080d042f825c11184ff40d422004600e600d83940898122c8882aa91504561161106823d966a7383e601c83468f050c809084a611a4ac8e1203f2871c984000000127c216f02ea08000000548e3218f688ca2282a00b002800a602591e6148a3e4110831323e21ce01e0230113c02200e001768d399a0313a4c112a4a68c0c)
def rootSD10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x86920443ff8c1c3490221ffc54e1a48110bff476cc240884ffeab54d82443fb6a9b04a92213ff6e23a54910bff370a9a40884ffdb58e9824427fedad14c9a213ff6ce5a609109ffb6545326885ffa3b615204437f71d304a92217fe96d8348110fbdcf4c12a4886dfdb39e952442ffd45aa690221ffa549814c120ffb2a6c0a60906efd5369a894827fedab4744a413ff6d63a605209ffb6b45326906ff583869924437faa9c34c92213ff96da88e5209ffcb71d3309075fe7b54a194c2bff45aa50ca61bfe6160a64d10dfeb0b0d324887fba4a60530483f7d35b02982417fea2d9348110eff512a8a609077f98564d20443bfcc2c72902217fe6d6894c120bff4b6c0a60904ffe8b69593482ffd45b2a982413ffa2da364520eff512caa609067fda5a25934833ff2d51298a41ff62e5534c120dfeb02d1c329057fdb58e581482bfedad12c9a415ff6e2594c520affb6b44a629077bdb2925814c2bff2db3098a415ff96d988e520cffcb51cb02907ebe6a925814c2bff45aa70ca419ffa299564d20cffd152ca62907fea8954930483feca9d1298241dfd64d8186520efeb46c0c32907ff18154530483bf6c12a4c9a219ff6a15264d10cffaa4d44329867fd526a2394433fec1b4b14a219ff609a58e510cffb0ad1b248857fdb8549934433fec2b4714a215ff6e15364910cffb0ad14728857fdb1aa5534833fea9b4344a41ffc606194c120affc56c2b268877ee2a549934433fec2c54c9a215ff6e1538a510affc76c2c528867fd858e992443bf6c12a51ca215ff8ad858e510affcb6c1c528867fe5a60993443aff3daa4c9a215ffa2d5364910affd16a9c528857fe8b54993442bff45aa51ca219ff6468a64d20cffd14a93268867fd95a29934433fec9514c9a21ff660d5348110fef30aa9a408867fda5661314827fe5d2a6c1221dfa5499348110efb33098a609073f99860530482f7cdb512982415fe2e5514c120fed2a6a9240884ff9b0a69814827fadac34c92215f76ce594c520afbb6744a629066fd5369a894823feda95298a411ff6d63a86520adfb6d44b269067bda8686494c27fd05b4ac9a417fc86da348110dfd2a50d2609073f59860619482bf715b52c12217fa8ad984c120bfd456c9a40884fee2b68d91483bed1db30982417f68eda84c120efd2a51ca408847feab66131482fdd25b46902219ef9299864d20bf7496c9a408867be4a609934433df252a4c9a21fea929524c120ef7494cc260907f9a4a54d30483fcd25262982415bf9ada1661209dfcd6d4322905efa6b66120442f7d35b02982419bf9aa3960520dd7cd524b02985dfa7b69520443ef53daa49022157f9ed5264d10abfcf6a94329877ea8954930483beca9d12982419ef92a8964d208ffd1715326887f615254520443fa4a9aa4982419af9aa4960530 else 0x219ef68a4a64d10cf7b25253268867bda8925914c33dedd492c0a619efaea4960530cf7d3524b029867be8a929934433df45492c8a615efa2da192530bfe436cc240885ff1b586920442ff90db50902217fc86da548110e7eb50c0c329076f66b60619483ff0d92a290221ff854a1a48110afbb6754a629047fdb3869984823ff0db4b1ca419ef92da386520afbb6754aa69047fe5b68a194c32ff3db4b1ca419ef96a4a64d10cf7cb524b229867be4a96593482bdf2db4324a619fd605a386520afeb6354a629076f9b6a2530482efd3db2a982417f68ed984c120ef7496c9a40886fb9a192930483fcd25472982414ff6e2a9609108ffb71153268847fdb568a194c23ff0db511ca411ff8ada864d108ffc56d2c329857edb2aa5824423ff15b511ca218ffa299864d209ff371053229867bda2686494c2bef1db30c9a415f78ed9564d20a7fb711cb029047fdb868e294423fedc3451ca211ff6ea39605208ffb711d3248847fdb88ea194823fedac74c92211ff6ce8a865208ffb731d3029047fe2b6a2194c23ff1db50c92211ff8eda8865208ffd16d1c329047fe8b68e2944337ed1b4d44a419ef6964a64d10cf7b2b253268847fdb8696294423fedc34b1ca211ff6a6a9609108ffb712d3268847fdb896a394823fedab46c92211ff6a6a954d208ffb6ad1c329047fdb568e294423fedab4744a411ff6d5a28e5108ffb6b4d3048847fdb58a9934423fedad14c9a211ff6a6a94c5208ffb752ca629047fdbaa25314823fed9d14c92211ff6ca5a64d108ffb65453268847fdb98e9824423fedcc74a92211ff6e65a609108ffc36d1d129047fe3b6a2294423ff2db510ca611ff96da88a5108ffcb6d44729047fe5b6a2394423ff2db46c92211ff96da3865208ffcb6d1c528847fe5b68e894823ff2dc54c9a219bf9ada864910cdfb53353029066fdb99a98148337f5ccd4c0a419bf9ada88a510cbfb533d2a48865fdb99e9524432ff5ccf4a922197faa67a549108ffd16d2c329847fe8b696394831fecc514c9a211ffa2da286530cdfd53353029047fe8b96993442fecdac72982417f68ed954c120efb3311ca609077da894c530482ff515b50982417fa8ada54c120efd456c9a40887fd1814c530483fe51caa498241bfa8aa0a66120e7f51305330907f6e5b60952443bdf252a4c9a21b7f9e98354910ddfcd4a9b029077be49549814c36fed1cf4a9221bef6164a64d20df7b03253269077bd85929934437dec2c94c9a21bef60a4a64d10df7aa5253268877bd52925914c37f6a9454c9a21b7f64e7a54910ddfb27353029077f985829934437fcc2c14c8a61dfd60e1a64910efeaa70d3248877bda9925814c3bded1492c0a61def6ea4960530bff516d2a40885ffa8b68d20443bfaa9b030ca41ffa60d5248110ffe306a8a40887ff185) else (if i < 3 then 0x6b03e032281684f83584780981118c2011029028c160a00a0e208c303c046071184b00782a8c26024c1801c4803213808c3013046100280b0360c278268118612808c2013829071180e0170b0300e809060e80da0c2064480a03a0241815db481403f0581793829816807906ada4c0334d283208c48150a3046185c8230828c0e8090609810a0aa3e0c00f046182ec050170ec200630334bf9a706803cf62a0d809817605c5f62f34a27f69d08d90596a19470400683a01f900f00c80fc7055c4fc9c0160eb8340e216c8066d4e0710b6c1a2e02d348240c10428c406d0d7756048400108f01f1d2700981ef92ab481d85b82a817242880640381010680f4157c969a42c00c97ec5b21a11c2bc0bef7ed2b2d4329b8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb8cb6fb46b1dae8abfa96a6da38a039da9b199496b9368dd8c087f8327f17c86fb79f7767417186fb6d26a968c66364661d5e85bf57e5314fc4d34b648d46443b4123b93783132de2b525020f1e61c919416b0fa071000e7f512cc2609057f61b655914c2aff3daa51ca216fe82d9860520aff536a8a609057f61b661914c33df2532ac9a41dee82a4964530cfec36d43248857f61b661914833fb0db46c92219fe82da864d10cff416d43248867be4b6a1934433df25b46c92213fe6c60a661209ff416d4322905fea2b66120442ff515b50902219fb54a2a64d10cfdb25153268867be19929934833df15494c9a219ef8aa4964530af7c56d0c929877ba4a82993443bdd25512982419fd6461a64d20cfeb510d3248867f59886992442bfb4db030ca419ef6464a64d20cf7b0b253268867bda8929934433decc494c9a else 0x334c0c11c818ae060c07003c0e8600c13003e0b0403c071046180d84d0230c07013c1207cd20c0026044401801301a046201c6138388c04c1c40b8701408c205f0130a3183282580985191c541b01838179a4050120e07c144203d095))
def rootSH10 (i : Nat) : Nat := 0x149325819801751209ced4505c4728e3b803a88116d3b04682802a10a680a02002570751c1f58723008223a0f990b180014a21322c1882708488e46a4b7560e0003b70268500f83c73410cb3010013d33470000c03c6900049141
def rootSD9 (i : Nat) : Nat := 0x3800f01d0c03241905c811880000000000000000000000000000000000000000000000000000f80140fd627c5495148110f74953a25524c120f3d181661314c120c5fda89ed5264d10c5fda89ed5286530d5be4a9ed5264d10c5fe8a9ed5264d10c6fdb59aa3960520e6bd529aa4960530e6bd929aa4960530e6bdc99aa4960530e6bdcb9aa4960530c7bdb592a8964d20e7ad829295264d10c7bdb89295264d10dee9529ad814c120ded9539ad814c120deba4a9ad814c120e5be7b9295264d10c7be8b9295264d10f7c931a25524c120f7aa4aa25524c120e7ad5292a8964d20e6bdc29aa4960530ff498354d5248110ff61835495148110ff498154d524c120dee9526da894c120ded9536da894c120fdaa7b929524c120c6fda56da8964d20ff48c954d524c120ff4a1c54d524c120d7f1812e5514c12087fccb695984c520c6be4a6da8964d20ff0a4a54d524c120c5be7b9295264d10
def rootSH9 (i : Nat) : Nat := 0x19
def rootSD8 (i : Nat) : Nat := 0x7f429ee4a54d524c120
def rootSLevel : Nat → Packing
  | 14 => (1,0,8,0,0,0,0,rootSD14)
  | 13 => (3,1,8,0,0,8,0,rootSD13)
  | 12 => (30,2,8,0,0,12,0,rootSD12)
  | 11 => (218,3,8,0,0,14,0,rootSD11)
  | 10 => (344,4,8,0,0,12,0,rootSD10)
  | 9 => (38,5,8,0,0,6,0,rootSD9)
  | 8 => (1,6,8,0,0,0,0,rootSD8)
  | _ => emptyPacking
def rootSIndex : Nat → Nat → Option (Nat × Nat)
  | 14 => rootLookup 11 19 3 7 2 4 rootSH14
  | 13 => rootLookup 37 67 6 10 5 4 rootSH13
  | 12 => rootLookup 181 431 7 13 8 4 rootSH12
  | 11 => rootLookup 251 571 8 14 9 4 rootSH11
  | 10 => rootLookup 23 53 6 11 6 4 rootSH10
  | 9 => rootLookup 2 2 0 5 0 4 rootSH9
  | _ => fun _ => none
def rootS : Forest := ⟨511,14,fun j => rootSSamples[j]?.getD (0,0),rootSCols,rootSAutos,rootSLevel,rootSIndex⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb9_0 : block rootS 9 0 4 = true := rootSpan rootS 9 0 [(9,3),(10,1)]
lemma rootSlevel9 : block rootS 9 0 4=true := rootSb9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb10_0 : block rootS 10 0 57 = true := rootSpan rootS 10 0 [(9,3),(10,16),(10,16),(10,16),(10,2),(11,4)]
lemma rootSlevel10 : block rootS 10 0 57=true := rootSb10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb11_0 : block rootS 11 0 80 = true := rootSpan rootS 11 0 [(9,2),(10,16),(10,16),(10,16),(10,14),(11,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb11_80 : block rootS 11 80 71 = true := rootSpan rootS 11 80 [(11,16),(11,16),(11,16),(11,16),(11,2),(12,5)]
lemma rootSlevel11 : block rootS 11 0 151=true := (@block_merge rootS 11 0 80 71 rootSb11_0 rootSb11_80)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb12_0 : block rootS 12 0 30 = true := rootSpan rootS 12 0 [(9,1),(10,12),(11,16),(11,1)]
lemma rootSlevel12 : block rootS 12 0 30=true := rootSb12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb13_0 : block rootS 13 0 3 = true := rootSpan rootS 13 0 [(10,3)]
lemma rootSlevel13 : block rootS 13 0 3=true := rootSb13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSb14_0 : block rootS 14 0 1 = true := rootSpan rootS 14 0 [(9,1)]
lemma rootSlevel14 : block rootS 14 0 1=true := rootSb14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rootSGeom : graphValid rootS (boundsBefore known383)=true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

def rootMSamples : Array (Bits × Bits) := #[((-0x7ffffffffffc1fe01fff81),0x2a90e502a912440ab91238),((-0x7ffffffff803ffffff8001),0x4047109c048c227000c9c7),(0x7f80000001fff80,0x19b8404198515106753610),(0x1f80000001fe01f8000,0x20239a821a6a6a08a888d),(0x1fffe00000,0x556d025556491955446542),(0x7e07f80003e000000000,0x10e0878106da1e0468583),(0x7f80000007fc0000000000,0x7882b607b73cd81ef0608),(0x7fff8000000000000,0x6641b78667820e1988486c),(0x7ffff80000000000000000,0x7871c4078400101e107070)]
set_option maxRecDepth 16384 in
def rootMCols : List ColumnInfo := [(0,1,332,412316861106,8),(0,64,189,770,10),(43008,64,43197,770,10),(44544,64,44733,770,10),(0,128,347,548,10),(2048,128,2395,548,10),(48128,128,48475,548,10),(1,0,494,134218256,12),(16897,0,17390,134218256,12),(12289,0,12782,134218256,12),(6145,0,6638,134218256,12),(27649,0,28142,134218256,12),(13825,0,14318,134218256,12),(52737,0,53230,134218256,12),(59905,0,60398,134218256,12),(49153,0,49646,134218256,12),(68609,0,69102,134218256,12),(47617,0,48110,134218256,12),(54785,0,55278,134218256,12),(69121,0,69614,134218256,12),(11265,0,11774,0,12),(18433,0,18942,0,12),(1,2,312,824633721540,7),(1,16,486,520,9),(12289,16,12774,520,9),(6145,16,6630,520,9),(49153,16,49638,520,9),(55297,16,55782,520,9),(47617,16,48102,520,9),(54785,16,55270,520,9),(69121,16,69606,520,9),(1,32,30,17179870144,7),(1,64,156,4294968098,7),(1,128,330,134218292,7),(2,0,445,77309411904,12),(16898,0,17341,77309411904,12),(59906,0,60349,77309411904,12),(69122,0,69565,77309411904,12),(43010,0,43453,77309411904,12),(64002,0,64445,77309411904,12),(44546,0,44989,77309411904,12),(18434,0,18941,0,12),(2,1,332,412316861104,7),(2,4,305,77309412040,7),(2,64,189,768,9),(2050,64,2237,768,9),(17922,64,18109,768,9),(1538,64,1725,768,9),(16898,64,17085,768,9),(11266,64,11453,768,9),(43010,64,43197,768,9),(58370,64,58557,768,9),(64002,64,64189,768,9),(44034,64,44221,768,9),(44546,64,44733,768,9),(52738,64,52925,768,9),(54786,64,54973,768,9),(57858,64,58045,768,9),(3,0,428,77443629648,9),(52739,0,53164,77443629648,9),(59907,0,60332,77443629648,9),(69123,0,69548,77443629648,9),(11267,0,11708,77309411904,9),(4,0,379,824633721472,12),(16900,0,17275,824633721472,12),(2052,0,2427,824633721472,12),(9220,0,9595,824633721472,12),(1028,0,1403,824633721472,12),(18436,0,18811,824633721472,12),(4612,0,4987,824633721472,12),(44548,0,44923,824633721472,12),(69124,0,69499,824633721472,12),(48132,0,48507,824633721472,12),(49668,0,50043,824633721472,12),(42500,0,42875,824633721472,12),(44036,0,44411,824633721472,12),(59908,0,60283,824633721472,12),(3076,0,3579,0,12),(4,2,312,824633721537,7),(4,8,99,824633721744,7),(4,16,354,824633721481,7),(4,128,347,544,9),(2052,128,2395,544,9),(1028,128,1371,544,9),(46084,128,46427,544,9),(48132,128,48475,544,9),(42500,128,42843,544,9),(44036,128,44379,544,9),(57860,128,58203,544,9),(5,0,378,824633721472,8),(59909,0,60282,824633721472,8),(58373,0,58874,0,8),(5,2,312,824633721536,6),(5,16,354,824633721480,6),(5,128,330,134218288,6),(6,0,313,901943132864,9),(44038,0,44345,901943132864,9),(59910,0,60217,901943132864,9),(69126,0,69497,824633721472,9),(7,0,504,0,7),(59911,0,60408,0,7),(69127,0,69624,0,7),(7,16,480,520,5),(7,128,344,544,5),(8,0,487,33554960,12),(9224,0,9703,33554960,12),(27656,0,28135,33554960,12),(42504,0,42983,33554960,12),(44552,0,45031,33554960,12),(68616,0,69095,33554960,12),(69128,0,69607,33554960,12),(26632,0,27127,0,12),(47624,0,48119,0,12),(8,4,305,77309412034,7),(8,16,486,513,9),(8,256,23,412316861152,7),(47625,0,48102,0,8),(9,16,486,0,8),(12297,16,12774,0,8),(6153,16,6630,0,8),(13321,16,13798,0,8),(49161,16,49638,0,8),(55305,16,55782,0,8),(47625,16,48102,0,8),(54793,16,55270,0,8),(69129,16,69606,0,8),(10,0,437,77309411904,8),(69130,0,69557,77309411904,8),(44554,0,44981,77309411904,8),(46090,0,46581,0,8),(10,4,305,77309412032,6),(10,64,165,33555216,6),(11,16,480,1049092,5),(12,0,355,824667275920,9),(42508,0,42851,824667275920,9),(49676,0,50019,824667275920,9),(12,128,83,15393162789664,6),(13,16,354,824633721472,5),(14,0,497,0,7),(14,16,480,513,5),(14,64,177,768,5),(15,0,480,0,4),(16,0,495,0,13),(9232,0,9711,0,13),(43536,0,44015,0,13),(42512,0,42991,0,13),(59920,0,60399,0,13),(68624,0,69103,0,13),(49168,0,49647,0,13),(50704,0,51183,0,13),(53776,0,54255,0,13),(55312,0,55791,0,13),(69136,0,69615,0,13),(16,1,332,412316861090,7),(16,4,353,650,7),(17,0,494,0,11),(16913,0,17390,0,11),(12305,0,12782,0,11),(6161,0,6638,0,11),(27665,0,28142,0,11),(13841,0,14318,0,11),(52753,0,53230,0,11),(59921,0,60398,0,11),(49169,0,49646,0,11),(68625,0,69102,0,11),(47633,0,48110,0,11),(54801,0,55278,0,11),(69137,0,69614,0,11),(17,32,78,896,6),(18,0,428,77309414977,9),(52754,0,53164,77309414977,9),(18,4,353,648,6),(19,0,428,77309411904,8),(52755,0,53164,77309411904,8),(59923,0,60332,77309411904,8),(69139,0,69548,77309411904,8),(19,64,172,768,5),(20,0,355,824652595848,9),(3092,0,3555,18874888,9),(20,2,424,577,6),(21,0,490,0,7),(21,2,424,576,5),(21,128,330,544,5),(22,0,353,824652595848,6),(24,0,487,0,11),(9240,0,9703,0,11),(27672,0,28135,0,11),(42520,0,42983,0,11),(44568,0,45031,0,11),(68632,0,69095,0,11),(69144,0,69607,0,11),(24,256,135,608,6),(25,0,486,0,8),(12313,0,12774,0,8),(6169,0,6630,0,8),(49177,0,49638,0,8),(55321,0,55782,0,8),(69145,0,69606,0,8),(26,0,485,0,7),(26,4,353,640,5),(28,0,355,824633721472,8),(42524,0,42851,824633721472,8),(44572,0,44899,824633721472,8),(3100,0,3555,0,8),(29,0,354,824633721472,5),(32,0,351,412316861056,12),(1568,0,1887,412316861056,12),(2080,0,2399,412316861056,12),(9248,0,9567,412316861056,12),(1056,0,1375,412316861056,12),(47648,0,47967,412316861056,12),(52768,0,53087,412316861056,12),(46112,0,46431,412316861056,12),(44064,0,44383,412316861056,12),(73760,0,74079,412316861056,12),(42528,0,42847,412316861056,12),(49696,0,50015,412316861056,12),(57888,0,58207,412316861056,12),(59936,0,60255,412316861056,12),(32,1,332,412316861074,7),(32,128,347,516,9),(1056,128,1371,516,9),(33,0,334,412451078800,9),(47649,0,48078,134218256,9),(49697,0,50014,412316861056,9),(34,0,349,412316861056,8),(34,1,332,412316861072,6),(35,0,476,0,7),(52771,0,53212,0,7),(35,64,156,768,5),(35,128,344,516,5),(36,0,347,0,8),(46116,0,46427,0,8),(36,128,347,0,8),(2084,128,2395,0,8),(1060,128,1371,0,8),(46116,128,46427,0,8),(48164,128,48475,0,8),(42532,128,42843,0,8),(44068,128,44379,0,8),(57892,128,58203,0,8),(37,128,330,134218256,5),(38,128,281,77309411904,5),(40,0,215,15393162789632,8),(42536,0,42711,15393162789632,8),(43048,0,43479,0,8),(40,256,23,412316861120,6),(41,16,198,15393162789632,5),(44,128,83,15393162789632,5),(48,0,334,412316862081,9),(52784,0,53070,412316862081,9),(47664,0,48078,1537,9),(49,0,334,412316861056,8),(52785,0,53070,412316861056,8),(59953,0,60238,412316861056,8),(47665,0,48078,0,8),(50,1,332,412316861056,5),(51,0,332,412316861056,5),(56,0,455,0,7),(47672,0,48071,0,7),(56,256,135,576,5),(64,0,447,0,13),(16960,0,17343,0,13),(64064,0,64447,0,13),(57920,0,58303,0,13),(59968,0,60351,0,13),(69184,0,69567,0,13),(43072,0,43455,0,13),(43584,0,43967,0,13),(53824,0,54207,0,13),(58432,0,58815,0,13),(44608,0,44991,0,13),(64,1,396,562,7),(64,2,312,824633721477,7),(64,4,305,650,7),(65,0,428,134242834,9),(52801,0,53164,134242834,9),(59969,0,60332,134242834,9),(11329,0,11708,25090,9),(65,2,312,824633721476,6),(65,32,30,896,6),(66,0,445,0,11),(16962,0,17341,0,11),(59970,0,60349,0,11),(69186,0,69565,0,11),(43074,0,43453,0,11),(44610,0,44989,0,11),(66,1,396,560,6),(66,4,305,648,6),(67,0,428,134218256,8),(52803,0,53164,134218256,8),(59971,0,60332,134218256,8),(69187,0,69548,134218256,8),(11331,0,11708,0,8),(68,0,313,824633729666,9),(58436,0,58811,0,9),(68,2,312,824633721473,6),(69,2,312,824633721472,5),(70,0,313,824633721472,8),(2118,0,2361,824633721472,8),(44102,0,44345,824633721472,8),(72,0,167,13194173088528,9),(68680,0,68775,13194173088528,9),(72,4,305,642,6),(73,16,166,13194139534080,5),(74,0,437,0,7),(69194,0,69557,0,7),(74,4,305,640,5),(78,0,177,13194139534080,5),(80,0,431,0,11),(43600,0,43951,0,11),(81,0,428,25090,8),(81,2,424,516,5),(82,1,396,544,5),(83,0,428,0,7),(52819,0,53164,0,7),(59987,0,60332,0,7),(69203,0,69548,0,7),(84,2,424,513,5),(84,8,163,768,5),(88,0,167,13194139534080,8),(42584,0,42663,13194139534080,8),(88,256,135,544,5),(89,0,166,13194139534080,5),(96,0,31,9208409883520,9),(52832,0,52767,9208409883520,9),(43104,0,43423,0,9),(96,1,396,530,6),(97,0,30,9208409883520,6),(98,1,396,528,5),(104,256,23,412316861056,5),(112,1,396,514,5),(128,0,383,0,13),(9344,0,9599,0,13),(53888,0,54143,0,13),(44672,0,44927,0,13),(47744,0,47999,0,13),(52864,0,53119,0,13),(57984,0,58239,0,13),(69248,0,69503,0,13),(43648,0,43903,0,13),(46208,0,46463,0,13),(48256,0,48511,0,13),(50816,0,51071,0,13),(42624,0,42879,0,13),(60032,0,60287,0,13),(128,1,332,562,7),(128,4,305,77309411914,7),(129,0,334,4966056496,9),(73857,0,74110,0,9),(48257,0,48510,0,9),(50817,0,51070,0,9),(129,32,30,17179870016,6),(130,0,313,77309936196,9),(130,1,332,560,6),(130,4,305,77309411912,6),(131,0,300,77443629648,6),(132,0,379,0,11),(7812,0,8059,0,11),(17028,0,17275,0,11),(2180,0,2427,0,11),(9348,0,9595,0,11),(1156,0,1403,0,11),(18564,0,18811,0,11),(4740,0,4987,0,11),(44676,0,44923,0,11),(69252,0,69499,0,11),(48260,0,48507,0,11),(49796,0,50043,0,11),(57988,0,58235,0,11),(42628,0,42875,0,11),(44164,0,44411,0,11),(60036,0,60283,0,11),(73860,0,74107,0,11),(133,0,378,0,7),(69253,0,69498,0,7),(60037,0,60282,0,7),(133,2,312,576,5),(133,16,354,520,5),(134,0,313,77309411904,8),(2182,0,2361,77309411904,8),(60038,0,60217,77309411904,8),(18566,0,18809,0,8),(69254,0,69497,0,8),(134,64,57,768,5),(135,0,312,77309411904,5),(1160,0,1395,262660,9),(50824,0,51063,0,9),(136,4,305,77309411906,6),(136,256,23,608,6),(137,16,326,4831838752,5),(138,4,305,77309411904,5),(140,0,355,33554960,8),(4748,0,4963,33554960,8),(9356,0,9571,33554960,8),(42636,0,42851,33554960,8),(44684,0,44899,33554960,8),(49804,0,50019,33554960,8),(1164,0,1395,0,8),(144,0,367,0,11),(2192,0,2415,0,11),(4752,0,4975,0,11),(6800,0,7023,0,11),(1168,0,1391,0,11),(18576,0,18799,0,11),(9360,0,9583,0,11),(43664,0,43887,0,11),(53904,0,54127,0,11),(42640,0,42863,0,11),(47760,0,47983,0,11),(60048,0,60271,0,11),(69264,0,69487,0,11),(144,1,332,546,6),(60049,0,60238,4831838752,8),(145,32,78,768,5),(146,0,365,0,7),(146,1,332,544,5),(146,4,353,520,5),(148,0,355,18874888,8),(42644,0,42851,18874888,8),(148,8,99,768,5),(152,0,355,262660,8),(152,4,353,514,5),(156,0,355,0,7),(4764,0,4963,0,7),(9372,0,9571,0,7),(42652,0,42851,0,7),(44700,0,44899,0,7),(49820,0,50019,0,7),(160,0,351,0,11),(13984,0,14175,0,11),(2208,0,2399,0,11),(9376,0,9567,0,11),(1184,0,1375,0,11),(18592,0,18783,0,11),(6816,0,7007,0,11),(47776,0,47967,0,11),(52896,0,53087,0,11),(46240,0,46431,0,11),(44192,0,44383,0,11),(73888,0,74079,0,11),(42656,0,42847,0,11),(49824,0,50015,0,11),(58016,0,58207,0,11),(60064,0,60255,0,11),(161,0,334,134218256,8),(52897,0,53070,134218256,8),(60065,0,60238,134218256,8),(11425,0,11614,0,8),(18593,0,18782,0,8),(8353,0,8542,0,8),(49825,0,50014,0,8),(162,0,349,0,7),(162,1,332,528,5),(162,64,29,768,5),(164,0,347,0,8),(1188,0,1371,0,8),(46244,0,46427,0,8),(48292,0,48475,0,8),(42660,0,42843,0,8),(44196,0,44379,0,8),(165,0,330,134218256,5),(168,0,343,0,7),(168,256,23,576,5),(176,0,334,1537,8),(60080,0,60238,1537,8),(176,1,332,514,5),(177,0,334,0,7),(6833,0,6990,0,7),(52913,0,53070,0,7),(60081,0,60238,0,7),(184,0,323,262660,5),(192,0,319,0,11),(4800,0,4927,0,11),(6848,0,6975,0,11),(1216,0,1343,0,11),(18624,0,18751,0,11),(2240,0,2367,0,11),(44224,0,44351,0,11),(50880,0,51007,0,11),(53952,0,54079,0,11),(47808,0,47935,0,11),(42688,0,42815,0,11),(44736,0,44863,0,11),(52928,0,53055,0,11),(60096,0,60223,0,11),(192,4,305,522,6),(193,0,318,0,7),(52929,0,53054,0,7),(193,2,312,516,5),(193,32,30,768,5),(194,0,313,524804,8),(194,4,305,520,5),(195,0,300,134218256,5),(196,0,313,8706,8),(60100,0,60217,8706,8),(196,2,312,513,5),(198,0,313,0,7),(2246,0,2361,0,7),(44230,0,44345,0,7),(60102,0,60217,0,7),(200,4,305,514,5),(200,256,23,544,5),(208,0,303,0,8),(224,0,31,8796093022976,8),(58080,0,57887,8796093022976,8),(224,256,23,520,5),(225,0,30,8796093022976,5),(256,0,191,17179869760,12),(17152,0,17087,17179869760,12),(2304,0,2239,17179869760,12),(1792,0,1727,17179869760,12),(42752,0,42687,17179869760,12),(58624,0,58559,17179869760,12),(44800,0,44735,17179869760,12),(52992,0,52927,17179869760,12),(68864,0,68863,0,12),(47872,0,47871,0,12),(256,64,189,514,9),(2304,64,2237,514,9),(43264,64,43197,514,9),(58624,64,58557,514,9),(44800,64,44733,514,9),(52992,64,52925,514,9),(257,0,190,17179869760,8),(47873,0,47806,17179869760,8),(257,32,30,17179869888,6),(257,64,156,4294967842,6),(258,0,189,0,8),(43266,0,43197,0,8),(258,64,189,0,8),(2306,64,2237,0,8),(18178,64,18109,0,8),(1794,64,1725,0,8),(17154,64,17085,0,8),(2818,64,2749,0,8),(11522,64,11453,0,8),(43266,64,43197,0,8),(58626,64,58557,0,8),(64258,64,64189,0,8),(44290,64,44221,0,8),(44802,64,44733,0,8),(52994,64,52925,0,8),(55042,64,54973,0,8),(58114,64,58045,0,8),(259,64,156,4294967840,5),(260,0,123,824633721472,8),(42756,0,42683,17179869760,8),(44804,0,44731,17179869760,8),(260,8,99,824633721488,6),(262,64,57,824633721472,5),(264,0,167,17213424208,9),(12552,0,12455,17213424208,9),(42760,0,42663,17213424208,9),(264,16,166,17179869761,6),(266,64,165,33554960,5),(268,0,243,0,7),(42764,0,42739,0,7),(44812,0,44787,0,7),(268,64,177,514,5),(268,128,83,544,5),(272,0,167,17186161224,9),(273,0,238,0,7),(273,32,78,640,5),(276,8,99,824633721472,5),(280,0,167,17179869760,8),(12568,0,12455,17179869760,8),(42776,0,42663,17179869760,8),(288,0,31,429496730304,9),(1824,0,1567,429496730304,9),(42784,0,42527,429496730304,9),(289,0,222,0,7),(47905,0,47838,0,7),(53025,0,52958,0,7),(289,64,156,514,5),(290,64,29,412316861056,5),(292,128,27,17179869760,5),(296,0,215,0,7),(42792,0,42711,0,7),(296,16,198,513,5),(320,0,191,0,11),(17216,0,17087,0,11),(2368,0,2239,0,11),(2880,0,2751,0,11),(1856,0,1727,0,11),(42816,0,42687,0,11),(58688,0,58559,0,11),(64320,0,64191,0,11),(58176,0,58047,0,11),(44352,0,44223,0,11),(44864,0,44735,0,11),(53056,0,52927,0,11),(55104,0,54975,0,11),(321,0,190,0,7),(53057,0,52926,0,7),(321,16,166,520,5),(321,32,30,640,5),(322,0,189,0,8),(1858,0,1725,0,8),(43330,0,43197,0,8),(58690,0,58557,0,8),(64322,0,64189,0,8),(44354,0,44221,0,8),(58178,0,58045,0,8),(324,0,187,0,7),(42820,0,42683,0,7),(44868,0,44731,0,7),(324,8,163,528,5),(328,0,167,33554960,8),(12616,0,12455,33554960,8),(42824,0,42663,33554960,8),(47944,0,47783,33554960,8),(1352,0,1207,0,8),(336,0,167,6291976,8),(336,8,163,516,5),(344,0,167,0,7),(1880,0,1703,0,7),(12632,0,12455,0,7),(42840,0,42663,0,7),(44888,0,44711,0,7),(47960,0,47783,0,7),(68952,0,68775,0,7),(352,0,31,412316861056,8),(42848,0,42527,412316861056,8),(353,0,30,412316861056,5),(48000,0,47647,17716740704,9),(43904,0,43647,0,9),(384,8,99,532,6),(385,32,30,17179869760,5),(388,0,123,0,7),(44420,0,44155,0,7),(388,8,99,528,5),(388,64,57,514,5),(416,0,31,17179869760,8),(42912,0,42527,17179869760,8),(1440,0,1119,0,8),(448,0,31,536871456,8),(480,0,31,0,7),(2016,0,1567,0,7),(2528,0,2079,0,7),(42976,0,42527,0,7),(44512,0,44063,0,7),(48096,0,47647,0,7),(53216,0,52767,0,7)]
def rootMAutos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def rootMD15 (i : Nat) : Nat := 0x531052387ff
def rootMH15 (i : Nat) : Nat := 0x102900157db68d4297000014000d3d0400b121d016f07000032a275464aeb889ba016b643bec888b331a1d2d47420db71568b48f28610be04c067392476876c1ec003180064d02c00010213044005000d2004000002001
def rootMD14 (i : Nat) : Nat := 0x21c41c4b89612a2504910b122910c78b823226c9b3c6686807e4388690f218910ec11913642d83544b89612a2e0538a51462885089049a5cc4e39220cd07e088340072a84304825220cd0d0098b289b21671224644d9583729245d97240cf026045231680d2270e1242401301e03924169138802a04c069b12d446c4e1f40ade186c15e404af14800ffd64ffd60ffd40ffd30ffd20ffd10ffc30ffc20ffc10
def rootMH14 (i : Nat) : Nat := 0xb0e821c2754b84a12890f1353d223f52739524188c38ea1c13492385a92995db1e11f9109110a692f43e3a53bd83802aa2ed16510251840c248235ae33e8303aa24800283984fcbc5ac9ada1d422536306954b20a3b8aa3b205d88b12b8ad11eb269180443a3d22bcb5cf04bc20816b8640b3a4140933834860addba7028a4903d8a34c33453e183514b00b107d602398bda0a004a2881f5b5d48ba623a91605802f8d2b1ba08000b9b04ca31006535a424b3a3c0090d98b424a053c085c6000000000c4b8a5855031ba1a44898d94c535d5da5d9d010833b4d841000000bcd856324a9242380a1308c722109c3018578a4c97a13ac78865e121bd4a10b20545d8528c48261318d381e40f24b05f090100b4f051a46018448a3d05c3e001b5b7b4610401932755d80f9198e0b4213283f80c51f89bd5ed9f20c0cda0dbc201a80311a01c12e84db9015009233d103024396d4eb8124532a96058ca4000732c21984510211d44e82b829b5b45ab23561c9245084292ad378321098d1b0bab438ba22040000030000010001047a00016f0804382600000c36001c720002011a9602000312000500010002c31b080007222e0406000208171d0501000806000000030e020f00020a03050200000506000000025503002c050100180002230085011d07084706010001004a040000160004010c00001a090300070005000101101e03
def rootMD13 (i : Nat) : Nat := (if i < 1 then 0x803c0ac0706889d48d0b5451a955d5505d05cc5bc5b85ac5c85b05a323a42c3a64745b5e07e0d107e92104c971216a6caa8950e50d11e11a84a02c89111d1e224913a5c48d24c6bc5d8b908e9825c2582542942882869365cc1d428c4e9600e21a48821e21823219a21c216b5b136424c10e4974964910a60a50a30a207558f09c21213613a700388692208608c834087085ea625c44d909306b42e046591259626cc09001e01008402a0162dc14449090cd0b803f5565551e11d990e90a90c90b1dd21289b0e91db812203400a8070288ae0d888d0520b5283341a00fc08943a2584d829428c7781d49344e9a19a07ea1ca1aa1912205817117623c23a3c4492274e03f11950d01100f84124606f21209c1dd586683408ca8702400788981604e0b81242c1a242d25429c29428c28828427c4642824741d45cc275e19b4931af0944882cb00f2b1232176a04901501300f11907500ea4809c16f50098b7cd880a806cb508d84e209103341a292635e1ac5c8294475202a02802601c0180160120be2341422d4b1190d7013a4617200f9680691210a5502486b835809807004124d240908b7851ac05405004c0480340326c446c271202a02601b3632d423613870130118cf96806909c300a809809008006c68c2188d84e279f0e2cf7d6da075a4d40f3d2cab717cc48f0cac166f34b92ed86b306c08ae5eadea8c69cca59e8d29f767789b8e63695364648dbe2ce882612080ddfd27d55e84781ddae74c5cb4719dc026de5afc693d99663758245ecd72a5a855f4560d51251953e84d1d2be49951e8454d0fa42550183f5cf663b74e60369cd3632b4c602f5cb422a54a0026cc94221f48001d7c6b218a45a0139c46a0fb43880c5c28e0844188045c0be02f80710003ffae4b27ff5c164ffecc2c1ffd84583ffb02b07ff65d60ffeb9ac1ffd71583ffae0b07ff65160ffec8ac1ffc95583ffa84b07ff50560ffeb8a81ffd63503ffac4a07ff58540ffe992c1ffd814c3ffb22987ff24d60ffe90ac9ffd84483ffb30907ff60520ffec0241ffd74483ffae6907ff5c120ffea9a41ffd43483ffb28907ff50520ffec9a41ffd31483ffa60907ff14d20ffec8a41ffc98483ff926907ff24960ffe292c9ffd83443ffb04887ff60110ffeb2a21ffd63443ffac4887ff65910ffeb0221ffd52443ffaa0887ff4c910ffec9a21ffd30443ffb24887ff48110ffe40a61ffc914c3ffb04187ff5c430ffeb0861ffd81083ffac6107ff0c420ffec1021ffd73043ffaa4087fe5c120ffc98241ff960443ff240887ef50540f7eb2ac1efd64583dfac6b05ff66120bfecc0417fd97582ffb2e085ff65940bfecb2217fd960c2ffb2c105ff65120bfec9a217fd93082ffb26085ff64910bfec90217fd910c2ffb22105fb64810beec98217bd94042dfb2c1857f65c10 else (if i < 2 then 0x29829429028c28827563c8481d44ee632a325171122327144aaeaac36f1200ae3bc3a62e63e7147043f09b50e8961360bc8a58a350684b13a24d0bb21c1de8a2807e04d83aa87286c48c51c4e44801a89d0b99268f9c52bc26c77943a25a6de2407cc9344ed319b21d21b21f21921687f23210a9a606e1423c849e276f4cd1368cd83f5652126440c086880751995490c8907322266ab2a8c83acaa48605da001e43e43642c7751b49184ed026b21d2109a512f12c2383324d814a3e326cc58f4b80a60a40a35194974964950a70a109f09d0a20a582696507590b0a0a2112d6a5c3224134b2c4dc85a13351a23361a00fc01e59626c86555d254475801f35aa3202a02801c01a0260229a904caab216140e18f49649516f0a70a50a30a20a082616d0a60a164b1a709d90b16a5969aabaaaa5c0b90b70b58b3a8c8ba0b98b78b68b62aa413074c858d38b44d55d6b45bc05404c04403c0394640355555505b05a05b60986f642c5c829a948819a0d007e84400eb5a97104cc952cb137216d4964954900a70a30a209f0a10a009d0b882690b0a51714bb824b24aa4825c24885385185104fa8c85004e850c1305a03ac858528b9cd25d25523d2e029828c28827d6b52582b02802742842781d65944742966c88b5aa328d104d2cb21614286444cda448cd0680074b889b16f11d54b280a80980780580428c80a007006004808c1303aaaa485850c489d9140201a010209874e42d6d12ed4c8899a8d00c62e414a23a72382276056015fd91d0630a016c649523823723541311a80a031c858b425daa43e43a43092159c4ecc26b12a89013a4d29af26cad484da8d784a22957402400e9582490bb13c5a66a3441140385646bc35c488b9124aa35c05404c03403003802e1ac0465c80e955428c925c87ea1ca1aa190d623509405823a27449237312250023cf43f50e50d8d750c11a84a11e02c1212491e20bb11d26a7a66a34287286c6ba8608f43581609544892489d0b908ebd43943446a1284784747889244ed2a1ca1a01e010a1909423c23a3c4492276b6444688070ac86ba490d70ee50d8911725809808807807006805804804524c358dc84f0e988f3993e35d34e9241ac5c82846a84ed2c8899aacb1af0954932b017627498d701501400e00d008011a4997250c00f5541210bb7322266a34524c6bc3588e8528b909d2a92405003803002635c0361ac03c18c5c8474295a4700be9a08503f88842432a884c172c98b89000707a42695451c076386f01d003c679160624079230b445ca801d53414a04c5a06f555c69c7761a87ca28d83baa1a2330da48c31a27670de0758081650ac24896f8a34003c07a872830c401789d1244b7c512808a04e02c6204eca1bc00f1a30264aa1882d5143236921200755918e0530c016a91b1b11f18a1590903a else 0xb28f24870ccc4a2b783e0cb81c05312849b2b5344d555a43a4216b477864625e25a25642c29c29428c28828555553d5515941d44e829866074e4db499b21b21807207006e06c068066064062060b1e48c4913b113642728cd90e90f24d49749649590c4b890b9190a70a60a50a40a30a109d9652490a20a058f21209f13a075247e466c86c8612312410f10d10c08f08e88e08d88d124c4da4a8ef909ca4364304dc0e40dc0d80cc0c96b477626d59484da3c23bf21b214970aab21c3bcaa81d2424aacaa43ca3c921f2192163c5488b5aacb2331363bb90e91e41da1d990e90d90856511c11b8b85565551e11df5ad90c11e1e21f111d21213a1dbc41faab0efc87486ad6c8c80a8098088078070068ecaaa0eeaaac87c86485ab28de8908520f1652582740cc1d47788504ecf21a0660620603c442827670074d490c90b2121161155ae13b4c66c8724aa5c248c8c853852051851109487a4ba4b4860528d1522050ab2c8584e83a89d6243925d25925643124447847429c))
def rootMH13 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x1ce030042a60b8202da3f4062e0bf6c2ec4677240855c1cdd1e772100acd63d018265600e61d191301123608e5175112aa47e0001119a05804a56af6d4dd8da036c8c510b602d7b568eb7892c840e28810b1c96d2391685a20d81a8215d63d550910d0a12e8054e15022c923905d2121186401e945308664227045a519a055111b2195924e25bd86e9229a4fe0b36c4782ae436d07b8217bb9326652dce9cb80fdb5060d858768c7c56b28f010b1d0907070c4c9c75a26926ac0bc015382b7b80ac3e8a0ab39d54e686bed202ab207fc414817ccaa7881cc810060db99a54a06fdd8008cd950047d115b00a1a04946dc8590000762000000000341003867d4424da3d84feb208896807c054a889214841f408c568200d3c8cb0590418899c82c3b3301c00c000000402016090255440e080000002a000000106000017000e61b80600002000080180100000224000240002c0000000024000440901400270001540e000010143200c0b0041917801048000081603800648560002a124000300b00c0b00400034300000700402054030040d0100100c0000c0503801008001b800018090b80300400098040140601ccf0e80000c07000050100a0141e02012000003e4ad0180104405000030600101c6200400010210280304997054320340400021010010241e000000000005c170c0010040500801000b729c04014170000701c01000fe01000010010181a010050f41b0c4020013a00400004000040601c000190000400150009bc380000004c0000800010140610800c0c0140200008074050080003c020000102c0008407014610d002008090680613c640f0000180300c6609c00139122700200407400c5288900440201800024010c40e080032b41507c05000020040a0b80700d5d0000e2701302c18018260dc05008000001d004310002a004090080002038010060000b004667c00300c07008000000700416090040513c0127300004000580a40400d020006302803000d30000003c035054f0500c000008e00001c131880001400010000480005008004140280b02800174010000000401038050082304029000020000003c000041a07c0100c0a024000007605c040000207419024030200803cc0014010000300804008010040706c0b001210180003009024210040500000000030003f01000014110000e0040d00009000280040000c000180051830054020b0030001900407000030140504800001d80100d0000105000010010040e0100100803014020f014000000580400004014090002100c0c044041840137c010ec080040003c3a0100323c000300000808014001e80e180010000f0040000dea0182500803000370040500015001ad01cf40101200c0339c0016c00010e3010220100000005004000ac002943800000310000040b else 0x3452f219512a4d064a8dc401d836fa84e0cfe11881d10016c85891a52deb378063c8dbcc782592e1cc21ba017a23f2f641d5a3f797af4d9d16aa04421d34d4ec6f5043937602784f2885c0078e4a800758d142a22fb812381c002fef0d64c822220420029548d8a05037603ec0e39354018c6ccce02112e47ca4e5c03f23d329082c791f0593004bce4e1d278a9b42ed0658a3f8b1704b80f11de403ba1180c60650e810b240e2bc4474047f51e40b6818d2bce73b66af5cc802ec84ea520d1c7122b858a0dee423d30143acc578488125a2112a8fc18a911d1640465098c2a6c83fc83e51c11b20a0468cb507a841e13eb45ce87180b6600a0830995db0302742bf58b2037c474a4adc03d019870eca8dc1b5b37435f20ac1973c2af28f40bd00a783ac75e60ebd0c5ba0a4752a615062806608e9615804b02d234ce8be8114340f03be2c481d14a41461e2a091948855019c2a50473031114e08556c22387aa50e0ed41fb51a270f011310284b450362c9e4186a3b6b81283c1177422704242ac80615336174f0814141da81a7ee23128dcbb06115e8f1d146da3608ce8f40640932f61c88df0858890450c20ce99c5b3e1025f030015698c6a5156cd803820ba05de0728144806a7764056420a505944f402b400d09bd054725da88d806f41cac04c059a39b011eb17a8bd82f701084478100c020017c900406c023721ab413822e927d05949098820a05f97b9633084582d505c40491896047800000d38000d2880000018c0ca90df063c04200c312b5479e09519b73470724b08b80005299228248659c78a9d00335008000b34225400ad5a0a0192b23680a010c924e04a2112dcee841304122b8893d12d646ea108ad45dc3b009684d819b086907a601140eb046a4505257009550f29246a7b2c430285874c086dc5a1095213c86a29b203a8731ac43018e3935443d404513f83b7716e07ec23881100386037c461a4622662cae40cd02f3311c834000080602168090408bcad785108968125bc06083003d486cd26f072209acc580261280d6d3c11ab10e14a48e260f54bdb02824d30116819f9338109e4a8013846d52e481e8822268520b70a28930c02dd20a4101b2baa3124ac90c20166682008ac0b8030b60784d3dc12baa244b80c8c1a2ba9cb8ee0efd9d191bf73408c99857c46a6448ed56d8c1c2147a8098c049d40b46f300f49565b56052ce9e496f913408a68c0d8fdd8d821bacdb2d4b04457484e4f0039102c06e80d6ad2610a1047803c8a22523747d289959842145a637080c8862a8516a04abc11f21b304fe0aac16f107c970a093c833029d474642e8d25041a6056a1710ce10070234083c03231f115fc8fe8073b332a7cf478812b2313029a4d1c2340a4cb91048ec091a0c1674c05e408288cf55340641868046c46034a08) else (if i < 3 then 0x818982b8026965cc076b0e604ced158000223d47e20ef05420915147ab1e1d55926688480da420832c5a6608ddd1248c84005e0cf12341847541c0ca81388ad0418e8be04bf540707c60b461220417a41221e699a00a26428d1b00d4c29f4764085199c8048a4f4ce94611d30207956c8207681db71e6eb5d05e812170e004c91f19130032c0c38134035f01df679451bd8434730846ac46d08c071830c294b0b94545c4070163380001776cc9047818b62942d211b7b18f03568a3dd4f0148845407481e6535a68e609b61385135a8ca4b09ccb13cf70988495d0d010e09040002086217c9620ee580000388a8ecae9c214c367008e0ba81b10000361e01a00c0927604fb507ddeca16ba44e85f81fd2397b3d88884d3291c04708e1b40985b5b0138e398137a16036968f7814f840d080e8aa44ec11cb016a4aac0f0224226a0838804cca0f82ff71941490137747086d01d3a3b0214a047019800394354717e93411378412491088903d846f6aa080af90d60552c0091deb14d2158081007238bc146acbd8083000c607c28bc230832708aa49fea000404948441fc21021b9004caa194f28275917011ec01f141127e211f0843104b88de0c8416c9084180827d8029b9e235802ccdcf3a1830872035d879aa04649f4add1fc9b13a73207641d28087065ec3c0173104747b20c1d0bd519f84d06445d94133a57d6d0300ea80ff02d4e6dd07791e307904b05467416d96500fa815e02c507722b605581334680a07889071231068c0920086043c025226051b400e396fe03a50c8a1d501620d08132d01e45bb2f7a02c4339084a0f3c1430143a32903851ff903200da223d1e290e708744d28224d1ed025a0f0401a238063d22a201d0a38742f007b805439cd47fa45ba075a14641a906d811041ed015f70480b2832d63080bec1ac0089047409c8081811562520fc18fa8480010207241ae03d56456866a139a14903fa07f88188162a63e02080e28095424cc0d90b4b8758449613999080a70136c7b822f02c16091205001b02be7662e6545ac32c6854f6c6c09fb11997a284d088a41ae028e0f9805c822f711ae08083201cd4790c30a9b00aac086407d49940188029685d4199043e451471691765b1db0b20d2c18480e0668c8594181d35d225010a84f1a03a08dc462118230bf21248f345f5215a00eb01a5c6582432877416adb049cc06a828f98c120d2976629b41fe83c3024e8b5a86ddb6305776d1a13b839422236a649a1018455c0d16097091b1088e44251bf8100935e71d1c11047655496fb1838837704608a40221c235a26c0c12dc7206b001206719e500c447e40ec8194039756a0085c0e7441625f324e987758d2477c068013d8232720ee4de87421a4a501718d4ded9f5235807e1c37a22901b60b92cdc80f0333885b8122018c else 0x25a40004614214e0232ef400000000668ace80e2e88fd68aaafbc055423a00000f1c03cb39f67524af824380bdb83804f0000a0f607c82af4e305a460000089595e037092d08af222f217303e400001502310b4c407a84230b55059c2a1))
def rootMD12 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x3dfd875cd20f7f5d173483dfd735c120f7f5c570483bfd9860520bff6a174482ffda865120bff6a053482ffda864520bff68980482ffda824d20dff66120442ffda750520bff69d93482ffda564d20bff69493482ffda364520bff68c98482ffda914d20dff64d20442ffda114d20bff68498482ffda124d20bff2a5814837fc9864d20dff261914837fca954d20dff255934837fd9258430dff2a5314837fd9824d20dff24d914837fc9524d20dff6a1920437fd5364810dff69592043efca258d60fbf59492583efd6324960fef504525937fd9114964dff249914c3fed8254910ffb54920443fdd314c910ff754d30443fdd314c110fbf59562443efd6358910fbf59560443efd6358110bff6a193442ffda864910bff6a120442ffda64c910bff69993442ffda54c110bff69592442ffda548110bff68d92442ffda14c910dff2a582442ffda020530dff61d910c37fd8264430dff6a1910c37fda764430dff5c5910c37fd6564430dff589910c37fda864420dff605910837fd6364420dff648814c37fc3166020dff65431083efd6258430f7f61d710c3bfd8160830bff695610c2ffda258430bff68d81082ffda158c20ffb60952043dfd875cc10bff68d82042ffda354810ffc54560443ff15148110ffa50970483fe9524c120efe601815837f9984c120ff654d30483fd9314c120f7e5d570483df9745c120f7e5cd70483df9715c120dfe64d20442ff9a014d20ffa54920443ef96558110fbe58d60442ff9a020530fbd58581583f755159510dfb649820c37ed8764810dfb6a1920437ed8264810dfb5cd920437ed5364810dfb695920437ed5264810df761d930437dd8264c10df769d930437dd7364c10df7695930437dd5364c10df754993043ebd8459160def55194482fbda414964faf591415837bd9650540def651414837bd8765010def609940437bd7365010def54d940437bd5265010dbf659635036fd8265830dbf69d960c36fd7165830dbf689960c36fd6265830dbf685960c36fd6165830dbf58d960835fd975c560d7f609970435fda365c10d7f5cd970433fd9860560cff605980827fda8651209ff6a1934427fda8649109ff689804827fda9608309ff6a1920427fda8644209ff6a5725927fda95cd609ff69d930427fda7644309ff695965027fda9589409ff6a4525927fda9585409ff6a5325827fda664d109ff699930827fda664430d7f65d610c27fca9605609ff695920435fd5265c109ff2a5425827fca9505609ff68d924427fda914d209ff2a5325827fda920530bef690814c2dfda7205309ff2a5814c35fca365c10bbf69893482dfda724d209ff2a5814827fca954d209ff2a5314827fca960d109ff2a5824427fca9595109ff2a5634427fca9589109ff2a5524427fca94c9109ff6a4310836fca165830 else (if i < 2 then 0xffe64d70483ff9a04c520ffe6a130483ff9984c120ffe60930483ff9814c120ffe60130483ff9a54c120ffe65530483ff9514c120ffe68930483ff9a14c120ffe2a130483ff8a54c120ffe64530483ff8984c120ffe25530483ff8a94c120ffe4c960443ff99358110ffe60130443ff98548110ffe60d20443ff9a848110ffe66120443ff98048110ffe54d20443ff9a548110ffe65520443ff95048110ffe68d20443ff99348110ffe4c120443ff55160560ffd4c581583ff53148564ffd54563443ff55158910ffd54596443fed524c120ff74c563503fdd314c960fef50572593fbd4250560fef61d41503fbd7350540fef5c541503fbd6550540fef58d41503fbd6250540fbf59571583efd8759160fbf59173583efd645c560fbf58d71583efd635c160dff691984837fda166120dff6a5824437fda960830dff6a5820437fda960520dff6a5810837fda166020dff5d1984837fd985c540dff661705937fd985c160dff661704837fd955c964dff645725937fd915c164f7f5c572593dfd735c164f7f5c570592ffda848564f7f61d71583dfd715c160eff60981583bfd8060560bff6a095582ffda260560bff695715837fd9558940bff69532582ffda524d60bff68c95582ffda548564dff6a5524437fda954810bff69492582ffda225560dff655610c37fd9825560bff68d415837fd4366120dff655434837fd9865120dff649635037fd9258540dff54d94483efd6550960dff661425837fd9750960dff64542583efd6350560dff661414837fd9750560fbf58d62503efd6258540f7f61d71502ffda358940bff68d61502ffda258540bff68d21592ffda14c960dff661934837fd9764d20dff65593483efd654c960fbf58d32583efd614c960dff6a5325837fd3265910bff68c92582ffda224d60dff615934437fda864d10dff661914c37fd8264d10dff661934437fd9360110dff595934437fda664d10dff589934437fd9664d10dff64d604437fda564d10dff655914c37fd5264d10dff689934437fd9264530fef4c5415037fd984c520dff4c5965037fd944c520bff6a1914c37fd984c120dff66130442ffda824530bff694914c2ffda920530dff261914c37fc9564530dff605930837fd6564c20dff699930837fd6364c20dff695930837fd5364c20dff61d930437fd8264c10dff69d930437fd7364c10dff695930437fd5364c10dff549930437fca366120fbf594935837fc5366120dff60d924437fda864910dff661914837fd9864910dff54d924437fd9564910dff68d924437fd9364520dff64d924437fd9114d20fef61121593efd6348564dff661215937fd9548564dff6a5215937fd9248564bff688814c2ffda114964bff688914c3fdd534c120ff74c530483fbd8450d20fef55194483fbd8450520fef6514148 else 0xa20086c07bc06d80628054403f803140230014c0003ffd854c910fff295914c3ffd9854110fff61593443ffd9354110fff66130443ffda54c110fff61592443ffc8524530fff208914c3ffd7566160fff6a573583ffda55cd60fff69571583ffda14c960fff6a121593ffda548564fff68d21593ffd3248564fff48532583ffc5266160fff14981583ffc5264560fff14893583ffda64c910fff6a532443ffda14c910fff6a193443ffd9864d10fff69993443ffd6264d10fff69593443ffda264d10fff6a192443ffd9864910fff69592443ffd9564910fff68d92443ffd9364910fff68d52043ffca264530fff6a1914c3ffd9864530fff695914c3ffd9564530fff689914c3ffd9264530fff2a1914c3ffc5264530fff68d81083ffd845c560fff66170583ffd5465d60fff60895583ffd8750960fff66142583ffd9750960fff50971583ffd7350560fff69532583ffd514c960fff4c562503ffd314c960fff6a5814c3ffd5260530fff605914c3ffd5264530fff2a5814c3ffd8761120fff69198483ffd8466120fff68d98483ffda166120fff68d81483ffda960520fff66181483ffda060520fff68980483ffd8260120fff68580483ffd7466120fff61173483ffd7366120fff66170483ffd545cd20fff54d98483ffd5360520fff5d153483ffd535c120fff6a553483ffd4366120fff66194483ffd5365120fff61d41483ffd9850520fff5cd41483ffd5350520fff65541483ffd8764d20fff6a193483ffd9864d20fff64d81483ffd7564d20fff69d93483ffd7364d20fff65d93483ffda564d20fff54d93483ffd9564d20fff68593483ffca864d20fff29593483ffd984c520fff4c580483ffd544c520fff65531483ffd944c520fff6a531483ffda04c520fff66130483ffd824c120fff60530483ffda54c120fff54d30483ffd954c120fff54930483ffda14c120fff4c530483ffca366120fff14d98483ffc5360520fff6a191483ffd9864520fff54d91483ffda364520fff64d91483ffc5364520fff26193483ffc984c520fff2a553483ffc9564d20fff25531483ffca94c520fff66093483ffc9360520fff149814c3ffda960d10fff69582443ffda360910fff6a582443ffda160910fff68182443ffda260110fff54d82443ffd5360110fff60d52443ffd5260110fff68d52443ffda954910fff68152443ffd8254110fff60532443ffd654c910fff54532443ffd8264d10fff64d80443ffd6564d10fff54993443ffd3160110fff60930443ffd814c110fff54930443ffd8364910fff54d92443ffda848110fff66120443ffd5348110fff69520443ffd9348110fff2a582443ffd5224530fff685820c3ffda560810fff68d82043ffd5360810ffe61170483ff9985c120ffe55170483ff9535c120ffe54570483ff9415c12)) else (if i < 4 then 0xe4a3e253e0d3df1fddd3db4fd933d6e3d42bd2abceefce3fcbbbcad7c9f3c8a7c75bc573c3f3c30fbfefbe07bcbbb9cfb883b737b54fb2cbb047ad27aa3ba6e7a533a44fa0939c079abb9837951792c78ed78dbf8ca78a57883b86ef856f842382a37f1b7d9b7c4f7b377a1f78d375b3722b70df6f2b6d776b5b6a43678b646b62eb5f975daf59bf580b55875407532350d34fef4f3f4d234c0b4abf49db488f470f458f447742f741df40c73edf3bf33adb38f337db358b329f301b2f032cb329c72777245722a320531e371bb319ff18b31733151713cb11af0ef70c0b0a23076b044b02ff0116fffefee6fc96fb16f9caf8e6f6fef5b2f432f34ef0caeca6ea56e76ae44ae15edd3ad9e6d866d64ad392d0a6ce56cb36c91ac6cac4e2c2c6c0aabf2abd76bb5ab9a6b7beb53ab3eeb206afb6ae02ac82aa9aa8e6a696a516a32ea0de9ec29cda9abe9806954e92ca91b28f968d128b5e883e862284d683f281a27f1e7cce7b4e79ce784e76ce7416715e6d3a6aea66c6623a601e5e025b7e5a66587e56ca5516525e50764d224a36461243c242de41c63eda3cf23902357a33fa303e2cea29ca2746266223761eea1c6619ae17fa16e214c61312115e0faa0dc20c760b5e097606f204d6021e0001fe19fb61f6d5f215ef29ec71eabde8d5e685e56de421e26de155dfd5debddd3ddbbdd8d1d515d25dd111cf5dce11cc29cb11ca2dc8adc691c475c189bf39bce9ba31b745b4c1b1d5af85ad69ab4da895a645a429a13d9e519c699a4d972d94dd928d8f6d8d518b6989198765857d83c981457f5d7ddd7bc17a0d7755756d74217309718971896f396d516c056aed68d166b5646562155ff95d0d5b5958d55685556d53b9520550854fa14ebd4ebd4c6d4a85489d45b1436141793f293cd93a8937d1361d333130ad2ef92dad2ac1287126892439214d1e951d151a2917a514ed12d1104d0e650be109910811065d04dd035d024500c4ff10fdf8fbdcfa5cf944f82cf6e0f4c4f2dcf1f8f114f030ef4cee00ebe4ea30e814e660e3dce1f4e040de58dca4daf0d970d754d56cd420d26cd050ce68cbe4ca98c8b0c730c57cc32cc0dcbef4bd40bc28baa8b990b844b6c4b510b3c4b2e0b230b180b068aeb4ad9cacb8ab6caa88a93ca824a70ca5f4a40ca2c09f389d849b009980979896e8949892488fc48da88c5c8aa8895c8810865c84a88224803c7e547c6c7aec790476e8756873b471986fb05d5c6dfc6be059c069f857d868ac66c465446390624460c45f105d5c5b7459c057d856c0550c53f4520c50f44f744e904d444c2c4ae0499434404814455c437441583fa43dbc3d0c3af0393c378836d8358c344032c031dc30c42fac2e942c782a5c291027f826ac252c23442260217c1e5c1ca81a8c19dc17581674148c13dc132c11440ef40ca4 else (if i < 5 then 0xaa14e01ca7b09d26c52d50a488e2442485306025aa2369b10f8c28502120038639ab20c04b5446d3621f1850a80be007c21c0341802584d8c472144924b0927a980a410f81d8d90b24a827c13a01e00d64762e6076480fd12a01b49b16e03e2076392589220a400ef5300ec21409da0044d0dcdb887c0ec13b3027c13c01e4b9c4743e6076381d54f6d5909d26c52d50a488e201bd8d1809895418896a850c46d02124c7356418096a88da6c43e30a14817f08700d060096136311c85120425015475a10c18111b4d887c6146904de2583bc0761099445901306f099e01e2124b442ed0188835a5a03a62132b55c3101bd47504ea0dc2124b4428d203306f429034e21328379082033003c29034e2133c1b431a21409d9023250d836863442813b301a006709b8b3884cb90c0ed80e71362130759a0261f106203a614311b3084800f01509d44661440eb3808b21b90c01b80d806603201880c300f1dfa4a884db015809c03800f8ce10a89222df0a3483340d149500f0069c881ebc8ec5cc0ecac6be12826a1c7524c2ef2b013c404d41f38d7c3586944af172852c47521c9803c55460dec67a03c45818809d21ae48d16844e281bd013c6887c418916a850c46d024906f4020180a488b787c6146806e887c0ec38ed80e411d89b10983acc21280a84ea2330a2075993bad57803889e17613a0759c2f69b703b084c80220d6c5cc0ec213284a88861d310f81d8b8968ef01d842813b283e40451e4c8680ceb6a18fab2c284426a04703a5a1a036019601c3459b985d884d5043019837a1481a710999a1b06d0c688502765028d4350db2460c684ecd90d10d09902331df10a04ece2120b6c0560860c088da6c43e30a34c0562330a20759214f09f0d504ec805108c801f21d497a4b429e14d0a4851427442419f03a84ede08ed24e35e23a27945dc5c8276806f508e01104012ad41834f64525d96c5524f0c704ec60e905dd108850426aa688d43e35b02ffc2e4a34caa69940a380762534085144207489c824242685c9935395410f81d870150fa0750647023791b828101403188662d04bb491c08dc06311ae09a028168074e42c2ec4bb5808807e00710f0874434216a4ad55c168213581a042403f067801c38013a120e42c1d4076031b04240fc08c85a81680778b7c475195811404ec60e390045c8276401f0a002763a86e5604c213b2008aa1c0e392487d02766c3580f01d613b2038c07a18e09d9102680b0c704ec802c80814152f803a1341bfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabfaabf6eff5d7f4bff3a7ee4bec97eaafe75b else 0x3c13d200ceace21e09e100594d103b07cc802c06f09a52380180d6181ce868a8c81f445b90c04201e42521aa517f304580707761af122a498dca099ba4980703bb0d60e2031a6e623b0a350391050825806817011456f09da099a0bbc2540380eb01181d543349309e4dc852d8826809c03eaa808480887142f213b4933712250cc5dc1282749b910ca08d18d709080d81cb17245d86a84329286046602900f806a6e443213d4143406d009807a1ac3c421909e201c41cbcac29260d617909e1ca6b8d7852874c282016c5da9262e414b5635f0441d385184e80f4a498b9052d20360dec1ae2e421909d99a1a05c01b072e0d69e210c84ed021280885eea1984a09d69261769b909ca8b1f04ad2489ab0d711d852a6e427c9011403e01da49c3589a8ada06388ec279372139669244f486b07145c82766414209601a21e00b03920d656f09da5044807c48897b2b093a1169e0d202a213205047795430104ed0d574b4069c0c60568088a0135ea4685f019d60de86b81e84581f205641a52d10a3523031d603d808403c1c61884ff41c02f213c4b55c2c8016113c1ad35e96809da1aaf06b4d782b83e4508cc03c1150704d7884c27a7807c1c042613b0f91609100f01e838c2fc13c3109601104880788542fc13c3b43823251a807862042b16f09e203155fc2b488f44ee13b308b201617f134102480e30d58c42618d09d8ca9b868109e2881d4521f88b301e2460a545a02538bb402170d01c310984f4a12b090884c358406f492319c22505707d0c51a0908854358410903ac10589b8d8e46cc075c0ae4671440eb2887805623d03d07d0a255107410f2361d52d4370d611dc2500b312213a4dcc9253a49c35a35c23a0a38b9182da0a164c325992ac9464955582e416c0d382972160e903ae474b2d100380fd99b468c13642da9d4904643443c21d10d086443021588e335292b1df109b00d0e44c1fd242aa990b03d1c00e068666e0fdc9590ba486476aa89a4825bd23a32ab85d00ac05502a3810b6990b649e4741d4b050b2542e805602a815304ce4b68396481d4b2ab85d02d805702b01540a8168c85869f23a0ea605d02d816b0b501600ae054e4724741d4ad24e35c07f11d45dc5c8c06826a5916a0d040a8d12ecb68807769270d789188ea6e4c037c2504771229b910998a1a12101b00cb0941e245d884d00682145536b6156921342e4c988486882c41290f486242d89380766c52543be2156543424211d01661af0941b9451c9252203c67a04501e22c40485a248c8bb4a37601aa7b06035643e29b1852447120de809e6c41881f1850c46ce0de003c04f1a212a06205aa14311b488491ba982809356418111b4d887c6142a02fc0341802584d8c4721447109405601a0c088da6c43e30a3408480eb01580683ac13711b4d887c6146a03))) else (if i < 9 then (if i < 7 then 0x903b51d701580683003e311a85126c418eb081015030f826cb2e42c39e13303d24230037046077443413d3446410464507601e8acda50021ac3a2064133a46d144574535281ff8d7c3580583550a5063a9262e414b503fe99b46821106a84af172852c47430e14b5d3341dc43f114e1ac35511d852a9262e414b5a35d0d6241031837dc95172852c474354a72208ea8d008621fe1ac275172031838e23a8a34dc84f9d8d772236b749311d45dc5c82968b2203f44324226d6a2840c613b03dc4762e414b653344520ee21fb9134921aa88ea2ee2e414b588f01be91d0a486a8b90da6929262331e18f880704d88a69625917602c8cc86000f626c4534b12c02c8cc860003826c385ecb6821f03d901be21203d87cc80de21408e29a00c02ff87c617256928e88d17908c4ac9a402e44884e935f26c1f34981712007621295ab2a857b28e81e924cd725403a01b00c80506f602607502de42eaa8149852b8845015809c04601900902e03892de91d850ac92c01a11a92ec03191d8b899300f6924b125403c01b00c828013b90b8b985240f6b247829003d9ad24b086413c01b0bd44740f6b24b027c13c01e00d828003097388e87b00f6b2ab85d02d816b02a955304c16802a069f2160b60773592a8a02cc819c0f590b07586a905572aa01540ad015807403201a05403385a32170a5075b8aa901580a403a01816a80681500c691d85283ad842210cd55e92a1000c382d623a802b09640c664b07581ecc4cd234642e92d49500f00642921f18b9c275c881ec03db844e47002c91ae08191d0e988b0c8a4b92db2ca6a0fc0d3c5c84af0a588e861c2969325403e01a219808872418909d4b6992418eb120889c8e046a235e09834e64611640532160638b412f9c0e9c35c03e01b00906440502caa4985044762e414b68164c890a000dc4741d607b39238432d574ba0153136082c1304e92d990b03e04e41dce028838a14205bc13163c4ae1870eae42c3561396089c8e046bc1340504ae1020b6818e2d190b25f03c5a64407e0170a6b1720d5447614a1870a5a8482605300609837a0a1130018e14116c32502258470a11c0204af506b2292ecb720c74a913493014804851a01816545dc4762e4149852b042d00832201641140820e9a4742525b425dacc94645008c5b21402190321c8e046a00881962d091d25d81910422044816c2ec0b410c8190e27d031889447a96c850b924ee014b62281c8a0642a0fd00e1c0c8583a82062423b36901351911ee42d09a1490eaa2a1a0029230490358501108ac10208041fe26e2de077099022940f30f9642c0c614a8b401e8e22d420c4740ca1aa2e42c1d40761210190a0de11301881890a10fa1a0260f302f83004b09b1045446e14316a508481e206280703011a208285087c938076b680c84d44019d59c4 else (if i < 8 then 0x2aa84a14b0a285082c53bb07585004e81e0e058e43b2101f148f24740e549684e89a94929e209db692d49185200e2b1e07610a04f100a9a4b07402001c912b868623a07a4b5583e21d3852c28c0720334eea3a442813b581c9179173c4e0870a50ec4e62404381f309d98aac195c48d46712021cc5103bd01bd45e45cc43813b2e258a351de45e06b043813b3d43b12021cc4e07cca0fc09c022c0f656f10f04ece0de238045c11856f10f04ece644ac7b08838a1d5076061c4aee4425c642e1421f50803ac894226abb5392e896f4b725b52e4d194b60208bb01d5850e42d2d010093912c884cd0713466a32468041642c3ab0a14b684e5a8cd04616d61421d510f180d090da6991aeaa25888508879090e48cd34cae021e09d981f4822027c79131f5b50c3c28443c9435b34d2e421e09d9721c21e2b384ec91ddc8686f48da58810f04ecf03f50001f588e9b913ea29d238a8085da999ac8ec6be128355958524c2ec38a13e533341fc42285d8389acb565322655321813c45109dc296e66680e845b8d70e3a9240f426a4b942ec468b666d3348d01796b2d5944d4a4985d871427cbc25405602300f805c0304881c992484eaaaa8bb0a5b587f03fc25247923a00168684843f026a4dcc2ed23814b7333591d8d7c25343523a0c94f105e6176a490e93199a0e9c6bb435238001090a0b03dc26a48ea5ca17613e76561a1a12548f41ad23a2800e285e549213b5d43623c12588e89f41c486b924c788276a64730fc44b84a13500ab4930bb4dc84f94237a1fa2f04d79542d686a8a3390c13bc2ec38a13f6a35f00e26e114e9241581c747734352e50bb5b33446ec8ec6b805b49213b85da5c8296a11bd9101fa42207136b5142565caa643027627785d852dd09684a81ec0f4060214909484709f212022daac07909db81d807e4d683104ae07a88ec5bc18e901162580f607601980c1aac07710a04ed407e07e12e592b11d450227d13a07d03c820816b16f0f981ede0fc1148388a6a565caa04f32190bb13b852d7013808c03a01a1d348cc2832175540a481e960fcc25404601f00d11d01a2028188aaa04e838b0bb524852de43f00762400ec4260de984b2a851c03d2844f89003d01d8b620e2caa14740fa907e02ee9a14420d3d5348450b90d21930200b43455940f6242caa01e44ee26a403880f48080fc01ec48590c6d703092a15807874c4aa08a52442722de8687403c28b04810923382421a752445ba14408c60379a1c130045412105e07952406b12087417b43a09100f0c709a0f04903ec0384d104804523384be0790d5aa09046a03c82280fad0e80706ad0a7b13940392d501500335641801f113ba6c614311a6837844a082809c0344aa96a88d81e9222512aa5a936311b03e19ab29b188d86380f8503b403444a2584d8c46c0fa71 else 0x1a90eaaab25926c1dd64881f40f607a03c81e2aac4bd0e9a2844245a72cd28480f9464b074d14a03301755951475560e3087c276baa8553ab5a90c0eed59407203801b80d8068033019555aab01c60c004e83b6214a0772a9c90fad6a466027011807c03521d556485c038425555aaa5562acb1bd0eea84a1496611325992a8a36d6b4d72ca1fa0f601e940ec6c781eb2ca1d2c4d841123a1870a5a919a935c35e2444ae1a706384122e589b924869992468b407b114622d2e34501a9ad03d03da2d489d48d831d311dc03a6b5171495aab84104ae8466a1a249080f07b25bd13825641924477015805c12202700f0c4492214413a8b48411a1a564a8681b27119613992c1d807a486200a2232c4821d636e25a03ad55914417b0e9c5ce332a4d0e2c02ed896c85c29003801a0ae556003aa4909d478c4fa0787555a3bf90ec8689f7216a49aac0486029012808c036aa82510d3c290200a4e0aed2aa91758b7863e14413a12bd55c0f41390762c2f65b110f81f081bd8cb807443e1ac2801e32389648ec29003c01d00dd556b5b54f0bc81e0276ec87625b1299362b7869e14c21f0f9a4aac555c8716b712a8bd45e642f2330a103e81f00f607a03c861b26c4e903c4caac555c8716b712e56548f247614f0a5851c2880a2a1283a93a42771c4b04e043f0a514108544d872ab15543c25adc860774aca22010f086a23d11d13e87c623989b27488524556c8716b4acb015809c04601f00e2aae43123c1ed48e93a42770c66e43048c21a88f446e23590d124087a92a226c4dc77c432fc86e43043511e40aa03d01a1298ef871443213d6135043028309e1321b90c10d086425511e089887a3bf4950948a084d82157000438990d2dd96d8b6a5b48ef64323ba5b988e814422607513e87c438a1d388d96c02536a8ca29442481703a84a83a68a34dbc9351791f36021721990bc8c80b024e28309d40dcb6b0a192787a9b1ddc8687c423046d0fd886827a808b04504345b209e1721189700b84e24d826788dc294b69936555394888b8c4888cea1a0c70e5a1488868aa703c41049194510721190ec86093b21e118924159c27a8226935321921208ae42c22c5ae09da400750d92321ac38613d300cc4a403113f04f0a43fa4b429003a1bd0f488800ec13b4c088208c9664ab2411461f90638310c9897103d300e564ca4ac2884b64d9063d4221461ab503f292d0a784f42772174950f999102931730f601e9b50e44e81e6a0d03513025ce49a1f303b2aa1d890450898002e875926a2743e6907981a01584baa4ac2884b024303c8731a1d17303eb41d214400ba91297090ba48a46614490ea4bd25aacb0a7852c28c42413a83a874d4250a1b01cb21d907527094692aa4909d429a1490a385083a692d0a5016068aacaa4f133a84a13a253ba76692f4b8)) else (if i < 11 then (if i < 10 then 0x8b508680f4c02896581420a064b325014b16f0e9b26192b1720f8b24b04d0e98b6e42cb2817aa31a18451748b8b910b1f90b0c3d55c2720ec5b26192cc9564a02962e916b07803b42f4100c8583bc3aaeaab96ceaa00ef07703b22dc0f0c1303b5c945bc0d3b4381d4faab96c0b671748b583b81da5b40bcb2522da10048e83adc59664b3255928c8f0d3c5d22e716f8b745b62d8051052874c0ea09e48ec5a02014722555e2e91728b745b62d782668cc5be2d85ad050e42e2d01008017107e4bb88e897e2de0c73b3360d0d1903aa597217554051097c200a611020b04cdad81f92e2920e44c85d5500f41f50803599a84d424211407ed1903d213108f90b64ba5ac4be0c7733340eb03f83402168d183f50cb55d92a91d5827c014015cd68051a320a70510284022d55050642c0ea1007b9120d155468ca5972161c525e09dc272a72202088d103f68ce42e92010006525b4272b72260fe07e96564a55500f291d08025c88ccd238211da3390b12f92ed2de1005391199b06841fd55031627748e92ec296a23401e704c089aaa39280f67234022413807ac858525b5c07b4391199a46881f82940c607b48ea5c8296a113b81444a063a4802252d8e4a4336b04d03f426e42c13a149044b6d1246c03d2135090847c13211497790b0a4a5b40f6c435c4659a621e4b904ecd50d092c4745011e2435c92438a13b48056aa98d7050828c0221c5cb9292617614b5a35e04ca49c48819597c56e48e2204ccda524819117657448d9d99a82206386a80c6a4988ec5c829690770324acb8bb81329262e414b402881420a000ab6da04c063051a9262e414b5818e094e4a45da6e435511d3e924432cb848c831c0c711d4dc84e52e4404310ff0d60e34dc818c14691e8b9052d60a305100280c6e4e04e247888c9b909cab4922196d6a4640c711d45dc5c82969077635dc88565d24818e23a8bb8b9052d4014c6b8288138219d24828c3e206307145ca23a8bb6c92443c21ac8689ba48d24811f89502531df4518875b8cdc86e43c45724810f64304cf1dfa4a84a4434c09c022cade07b13616a1b84aab284741c680f4dcc9261760e5501e42540e3a86839423b17209d228e4929b909f32a1a122071847409d2494dc84f500e9a114056029013807c03601800780741d6a195540a4c271e0bcc4b02ec27051ac5284b23bc21c09da825291904615bc43c13b3478043e07c0f99321a49188f447414809f00f006c3e207609dadaaf09003ab55936e85705641d549a973540c28d8d576ab06400f41944ef215e1429b70f981f17090214b55daac9b705707ccf09028d42842589b710e04f4ed0d28d42903e607610e04f0ed0e848428e0ea21c09d87cce8cdaab16d2aca03901b80b89d21db0e296e43a621f684de92f49689b086a14259a10fb5943a659b852085 else 0x334b6831cc8a1648061c9760b403d82d42668722333591d04881305e42660b5403b507e0e28242045c88179450c47416aa0b14285c8807a08015090847808c03a01900a4234274104149c85a5c80f4d02e403e01d009804057d43265580a01d4201554031a476142f72240342c411f8500304200723506200f407980511b08d607d808c03823e277aaa642e142076839108d101580a25b423f0a00c604012e44424211d09501580a403e01d00c805402602211f099e42c38e0c04b6c2866e4403dc0342c491d8500308200806f11a40f407980640248d807785125bd23a07b603d4c4e0f62ff04cc0f4187399140f41f5080100ea05c404060c42c1cd082031db6d11d65dada0a187031852c81f50318400764407ab9281be18b0a5818e23b0a58b929c88c8e0ad018c296510ca28604c1ec0318400c22d04307d4200405a016d2d8e490320224c0f1702818c44a17910c82d4e0f602e642c1d407607a816ce8070a38754112100288ed9a4807031c4741da0b53908907e17909982d4a0f582084cc168187282fc43284107ab1ac0c617988e82d5313602f817044a0760de852444cccd066073f21889d6b7b8484d65cac09882785c35890127422dc48819418f2494dca41ed8918b9492445a568283db0d6dad06d817045b89149d45ca492b666e35f0d680700b247923618b11362442088ac8b92475c222411203901adad07101e81ec9218b9228e492c48c81ea492972080141ec22549088b44850ac031a6e62e48bb924ac1c6063808c032014274106036d0d624209d16da145249743a40c80ee45da924b7813c121246d1451725e1a01d020e03a818e02b00e07708ec1b697209d428e4925b67b9101f117212a54352428bb0e5a1c88c6810745c810493a02e036f12350d0e5adc88c68107036d2431b9099d4351461cb5403a01a22311200001891b9524838e14656d88f3123c91c071c0360d717210f04ed10bb48e8218b6a21e09d9843c825806c1ae2e40e409d9f1ae03a06d8a0045a08405aa5c94930bb54924c88d650c584f0296601629253c412548f3439a1a28009e852d4229d24a3b807426f02e235c1081cb68684021769726c925051011805a1adaca03b8098228477555807a098278ec6688941b70a301d42ed2e4a4903d254930bb057c28613821003187140eb554851a098278d114a3a40c7015807691024300f042212839750c08026e6176f06fa2ed49257409e0190d0a57250909372147031c475177172481e83e30260318400a1210c5c0980c614b2b92b49300e0a389091769b9031c4762e50a55b1a043300f4f140980c61003b9102c5011056818c2966032c5c845a93b262420f500704119540ead4ea8ec1e5283a041098c4581a60a5191a2073c4d87c72328fc0c39c47a21e03d061c80f711303d844b80e10702081d69b1) else (if i < 12 then 0x6a4b429614827d0d101444240170e987c54922672b742853b3a041894433802c84e84e906e2534020c3ce8390e9969c42459750d84ed355763415c6aaa93664bb2591468a088f0144ade89d00b84ec3e70c8716690a2d550e981e223d11d109356027407c89db410a04f81bc48843c0f80c384ee14324f2daaf21a1170719214b6a13b10f1d1f98a545e62411761f310e04ed190e48c95bc43c13b0461999a9366b2817044a0e207b1955181954c8662419136909171d38e6558602303218d4ec482a99a425112d5940b9954309071418051d85daec88ccd11290fd87e084a8c971c0ead0d080353a176dc8662410f4658caa230cc3274b6b55e14b0a1a4b524e9201d32cd165292a97210c8528b3664c4b6428248a00fa840060fc453325992a1cf10ca294b1e1c5324a2800f4c64759103ea1002086523a1f50801199a51b0bc82d44ae129333358d111d0bc895c16a688eb6b59700f601580aa92b55710ca599ac6888e85e51422570949c0f49683230400896e4b6193cc00605423404e01d00d0e4895c1889723244281ec6880ac050c0083f806056923a1004869db3164403d03b03406aab166992c1abaaa01e80eed190e981f22e590b03d86a1c1884b4069ac880ec0c3980f405408fc5a82ec100301ec0f5172c85a2783a61a807701f120f507b508b04c0590e4831030e10007601e8c94c0c1857c1ea21910d016c2080b5a4ad55cc9511d635391441a825d32400f607a03c81dc27407dc8583b80ec1ab783b41dc1c1809c032014149aaa03b20225bcc8583a83aae074b531c88075647592b04c0f500fb46410405b07108972161d5803f113ac90062199c34c07a063a29220b40fa8400951905a428897549003d01e69220f5a4b428213c07bc8592f83d917303b4a92a96d6acb559a9c85102f25ce9210a3850d24434e1396a981d43a709e2cac4752d90a5b02b213c1a012b81e820066acb538356d5403d25b03a64b984f44740f81aa603d49744b985142800f5491a4b01f418e13a0e9c27a23a076781d692a219056428213d0a508025b418e139599e4b1e0896aba1452e896f4b6a5a92d00e94b725c84af90b099875614296c9b23a142e440fa8400ae4485099103ea1002b3358d00e20bcc864112257aab831d14311d583a5a9c96e4b699f72161be4b612f438aa722323a14296c0fa8400d00d23686f83ea9740d4061cf644850b56026617608019a98e44647428444a1f50801ec880e9266e0988e046d23511ac1ea082a8c889411390b0df052497d172259108d10a14b687d42007722323a1422250fa8400c468850b815c92089291a028e1d50448400accd10c80a830e133063980b3011807402e012179040c04e01a20c099840123a96f8503d92cc9545012e897207a03c92ec34e89d099874c0ee8a1076c4740f7110c83b40541 else 0xaab50feaaa0fc2ca2295140c9764a088042813d88ca27c43e59510d84f2482c128d5603ce1002c8480581e70f50400a21a0a1c4f043c27e291460e4d5741615c0168a4e526444cb3513))))
def rootMH12 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x81000e010074048020a80038f80502201c090030020d00412808e0009084900e02400803010284078070f80181f8010001f80b00c15c00c000000060200004083e25c068000140000281b006004018240083600080403a1b40000002a004010081600040002b0080216b805000380080010d406c44805006001aa00400007c0180e3ba01c0b80002288c4980100c010a30150520180703a00603a150015ce0840f00a046000088020000000003c010000a000006e00d16d4f0d20100001000200c0700806c0080000d01400c010002b40000012a0046a4030002280014d0004dc00c0a0290260000200f0cc0581895c01e00817015000090068300600041100000001402002016000078030002900619a010010088180320ac3e009ec4040018010000140300f016008230270ce160fe80000602400813002148001a30002b432800004008000be0260000101401e000008000020200092a00e06c02088012028010f001800c040040060000c00701a0180a8060000100445b5660040701101013c1f0040027d4000000100700180d08801c17816184154068000001048ea6704e04803058016034100040160040a80117400002801010040150040060000c95600e7d81000000013804b6c09e1b47d80008a069028d80083500281a00a068000000ce000008000140040900503e0540a808194064020160280381e8000040000000100c018e203f00a22c010290020e0028aa002008000f20d000c160000080000000a0000f4018008b00000000101600c45024002000000120020111d000008038140442420000501532c08c2c0000161300080904c0b00680004000c0100104e0240000901a000000000a80f85a0f20400940600a0b40000809d0020080400000000801028000000390023180b00c00204402c0000400a00004a5b00005c0980500e010028051860140100100600c09804002004028650000240e80500c7e4090500060880480a0000310601c2e0000008000260ec130062d20801303503a00006018002030008050c82880001b0161e00006d00e0080000001205c000040822c02c8330cc00c000000d60c0000010400082e00c35c0100d80003e82c0cb4300000c0b0000ea04000802004008008000880101e857720008060030100b40080003b198000000160040000e0040040088200202c01011006014079a40000640000005a010018030ee004170520ea0000100c014078028090000000180b0000fc0700d00402ad88010540100018200c5480802b0140300080004200c000ad018098108000ea49825802000034e480601c000208360067000000100003c180180c6024430e10040080980e03a00803800028000010000000100000b0000044600900008c0880b00c0380580400600100a420040019c80001602000840 else (if i < 2 then 0xc14c41e40222296001700204823290bac91f11dd0016514782085ce799abc191490f6de40005e097a58be4f650179186ec558074995f09d800c76d392473c20ed84fc0d3c002006e40de11a5c94309ca650941ae023d40df003b021d41c40858c4c110f28630050e1c5750531d0dc989691f104c81c2821fa94bc1f50c4141f0a46a406b41ba010200c101fa019d010cc1b581fa8dbfed470134e166c10e15308111a62f50d6edfa561b4157817cc192c0fd9190515ba0bb01bd81f421b0d1c5c913500c4010423ac0cf01f5d0cb29aac8971c5cddf400f1c20b98b18d8080ce41f741dd618e882fd9d26cfcc855822ac10a10680013d16cccc9c08581a80220801801c20a3780a8c9386898ecec81aadd7890cd422c0d2f1222607f287d4217ae02506d286e420250f5412bd15e413ec1bf9c758c05802e40c6411cc0bd4168507ead61a9a3814159fa412958f490085917821c823480db4a0285309230844c1ce6c905c4e4893b814e00c78d9da1f681a2889fdcd2585c640a020c042ddc49c0964230404c5c84444e00354a2b500cc2234123a1d22810ccb6a4bac1474cb7101602280190c172814a082b88aa812b420542400060d18b19a04a31195f9df3420380ab41c650b011759cf1241ec08529e9c077c63401378228c17d01f3c9d268185a23c1af9cca81af521400b5a0a081d4401b95e994181e3cc5f3d46380ae995941fcc98de89ec8f9c48b445409d4094d40a600b4810b11a5114d80e02113684f892380d280cc8dd60a2d01ff819bc19e4239e4fb1446c14ac08c005fa4e7c12ad641c061419b1dfc860e81c18a0958e9659300d6807c409b69336e0c818b408d898d511b510f80d4ca3e10ffc934003000504173c12fdce7246dc9de0006c48f823ea11082368e34a9e580da822b81f980c6802b258d423601c344c32a0d91bbc02f508b591d91b54d4bc854807540fc8a198e2c40b290f00153911c422f29e914bc80e7515dc112549ed912c11389e3c0454154010ec479458041a401576848116951e294eb90cfc17c00d8add8816510049a3a689119bf0806483dcdd88134008e08fc84ea822ec8c92d16c4a6551d5050edd2a91de1df5d74d1ecacf40009697bc132c02981419922c1714620186bd150c1f15c2c4617a23154e0e95f8041ad2e119a014b6d4d03a030050260410120040580103601c260091be0080000b008a840088c0500540705802201403000004008028041d004414801002028450330200200100d5285bc8a80000000c060700000440080000001c010240000100980d02a000000002160140101000c00c248000120c409013000018018030000000c0261c217c040160100bc098930000000180000002800800000274c800201205c020bd0020955e8010020380181301209c318010380e003800024004000 else 0x8074083bc1d748a14040c0824051c0cfc15d1ce8c0d14126ac778118017511b5ca0c9a3924f4918e4a3041c8416a2dd225df41de6d1f89060003ec5b811d0210c85b822b58a6421ec1ccc1ef000b8148e48a10cc0055d1ce9d444da2587a19a4ec4ec9c06d3711d6a58a8059088580f5808e84638068d97808dcec6b84e1422681f05d15403180e6403f51e100869163151165b2509341b8a828d15c915c4215c070a598849590cf49ee05e9ca374012c23c98608185c0e59e2758245996c81a09642cf4e517c9ab02381220c07dc1da1c9802290186c8c191952d3185a14054810401b2082f41ee81a015df910281a1c0f32594c02b99d040d0c0b901388e2f0188816d418d893e0886c12f40bbc09a8194ca38492548f728149162810f4021adc781320184ce228112c21a01d080a081cc1e2c1c98821f5cc0c01f4a0708a22875406a804380130240e8f810ed41111d69008b081200e8a58cc52e5199c201ea292e36c10c1076a53b8948291f817e0843c2009c5b51b851a30491c51ec9300044c93d40f141c9403e00e2ed2d2cfc013f21090a2701fd8a0e81d6c15829376568586aa84f090980dec146810dd853c1f18207dd6bdd70586050e151922e2f40c41df25db24a40198f805341276d7f9dc90036414240cb00b541339a3448fd199e80ca015ac964c2376c41014c814641552e03018e905d40d24227019882188189519709935cf5922e9065c87840668196485210f1c836c0bdc97a48a8c23200c2290250ccc0b980d7893fe55c411355854058585f80659a06916e00b84081016f084751945daac0db807f813dc20298f201e010064033187de9bcc16bc456821001c8906bc215287b296f498a02308081816744a5d46f50c6416d91b6404a9a072d2f69b1806f29610a0899114572d1ab40cec21e04ecac90083041e251e3ecedc0710099d06b44d7c183d228e96fc1e7823f41e86cea81e5c840c5bfc046c03582254171d1515d10cdd94224811700a191f540cd0033c0d30a1b0201608701a6093310455e1409a29d8800bed22f65bb2979a89311f81cceca33c45491b48d31a15f40eb40af021dd0f4c03d809be9655045811b801c102101cd9066407cc9d9e82b8091904b114f51c5296b421948289a1225638145411681520207021410ef907a8a3f0124016e814081e1496dd03f68f480f29237ad968996c11dc930c160d9a090c5915d494e12334231489b11548121a95f1a304032c20a00a3412ecca090c3c85cc20d4213422e2d10edd3244a1499e510d075a57a25968c97408a017260bd5596d0e88163d9f7912a6899c09fc1530196e45cc0b78038803429409189a046ca1581a3da3d44ed651600d8514001f9423fe4569104eda78063187340bc14da90d425941176e402c2411864a88f590e014909d96df5a8e1c0e081c6)) else (if i < 4 then 0x9140d58f41699cb0e93ad818d9c781fb00428a0b005d4152ed384ce580ee656ead8c1d2b00dd480099a144c9445b2d9a9d8c2d7b4071a22fac56800164fec1564027044ed0ca499e89aa185110d19087091618bb591429b048a9d45440a5da110129c0b3c0234a2bdce55061ed7309aac14280b65113441ed00b40679e211c7a51e66c8c821800b31d63cdf8044fa59e884a40f9c95f5d6f0180907465c50050851400be005b011880e3199d0932683fad95c5f8e4b2086ac85508bf005790fc9e2d522e40d741834189c1d9dda400ad813d5566810050771d8cd92d01ed1dd959cd1d3dde2465c3d1bb109268d6449dc626416e008059ac01dadd3aa9032a0d402cc092c895596440bb0e0c022c80cd822980e69922420581db498808f881cf44d40193083a910711b180254199811c09f681c98220198e447d4138421a915a4994d0905d3ce83e99ca5d6ec158ed7a9d354078e56cc17800a11d5f846ac034e1674e2ec4de51a9c5eca116592841f7915eda1190df41758c89c0e1c1854188489e8cfbe9e480cc5d1e48a0814b8019c097808cd0e9850d51fad57f590d41978064ade98084120010e300c525338163413fc0a96d27401581ef817f80aca94481592420ac550096ce0bde300177c212e59e4d0d4206187f085e1d87416f8022c1b9809ec211c02ae97ea1a5c1fc417a4c4a91d51456800d2219e5ba80ae009740e499eb50ec2598411ec125415580cbe018c0ac0181019a0dd2599fc16940194094609d5067918d8001c92a957ec0ea9cfb9c15e59a40c2e08641d20084c5c29d8a9dbe085d1027ddf941ee41cee59380781e26c96ba19d51d8c0eecc4c00ed012141ca1808c4d9017ac0a6c10ac1ce1015403e918ea8bf416c4a3884ea21e380fa419cc4778213dd5911b9018c695ea569018a11c6883d184880309d1ccd140a41415021ca463e90cec15b41d90145a0bc4174106965bc10cbc016a487186c0095e8c9088a40d9888ac069012cac04822a0206a9bc0225845001a49a138e3441d8896f01f4c4a0405a28771e01046f4a184149a9968011687a1d3e5d33ee0781a7911e4125c23900528222c4d54d0f1ce85822d06e9447508629a2c63749a6c1dc40dfc09de07a6816c15ba5b2c21bc15ec13e4a365dfd008f41708594c0f890b1d92ce4bf944e910f5626c01204fbc1e9d103c022012c41178a0da8dfc12d991864e865a40cfc88e60209e4b09c16801d80abd1dd800e81350093c0588168c165820dc960915600d4106de40980831949d8ae809510fb2c20c0e5245d00e401f6617f000d8849c0a241c7c595c1c1652a18a5c4c1c8c40216816cdddec12021608156c1396571c9a889d8c1318819101e18dd41278041214e457f2895d495404dc0dc4025d48b40484c1e81c740600100c11e0585544f000700bce101c47b else (if i < 5 then 0x500adc730ce62c9200238008c13a1d09c01ac9a7258b40b4023a462d08b7c98580000de882042c212532652bc07308b600fd504a5824c1ac489bad7c8535d1d24235ce07883381818934c043044d0a1d554d0195881ac05ed91ced0d00b6addcc0a2e40cd196d19e086f0182e97f91ea81d3c4ebe99ec20c90d38063ac5e000f4a34d177800021d2c09e5d8bd0ef00000dd5000051b4000041c0800069d840ea00004a3a9e0e893120bde9e7403b85d9623d609e018b9181c17648faacb40c8a114f81a0dc5c5051c19700004a034024c1e34191c1eac4d2801180004881000011b3c19f507fd1050cb5a5a5018e4080d1915e42083099ad911b8241800001f2d1c8c9b9814844dd8496e04888a011e800a385e345d629e0089f1deb0039c9338000002a00ff00004cd74a2e8000109e0221c03fc94b84245d3d4a2f9ddfcdd30a2c449a51e000d904ededdc6d6768ea494d90f7c054448bc93590704164c1e3808b8139ee342d0fd23200f90020413b0000000000000000000001e501b4d068c49548b74d29d216406fc2211e1bc840687f5de729e40000000051f12a1bd18a45968835a405695d48a19c185d7581a1059cd0170000413b80001119ed3b105d8a03cd12d131519ea0801e1740c00000023d89b769a48000096881bf500950fec57ac122c9d3e21559a182330000018f11e2506218f404eb44bcd8c84907a11cc4afc15d8520809c819da89190bc194801d32d9b6e03d080d1e501ad816a8820190fc9838167d59ec04cd1a959c9001a020fa09741f20d6649ce00bf40b71d96806648f7d82cd9e08104817b80e100a008560d324190219cadf354c965b301db92388109d05f01c009471588d0255a188a08405ae59551ec1c0e502601e90047ec874088c0e9c1cbc107ee29108941aea0be6961800021cf816600000123000051088000006c9cd1519fe9d2c23b00001d8e4d9781148000000019470000405cdd9e699641eb00c1a144c23c48e28d96e9f7c235419a8a280000698811c981b750de9910e987ae0c1188809a404901406a4091c84627a93899acc0144079d1b78062c0b02cf381a6c0d511866506d0f14119822dd0b110650834493ddd6cd1986d23a5794082892fa1a0c20e5051518409a7e94e804990f0dc1e81824853418d013c65894a2a408fe461d95880f700afc1a3409c400300599c37c04bc03688f818f0d81ded27ed25dd75409491c4c10d157351d788528913dc6e008a809d020a9227810bc07208b811f940f781508582c21b11090d0e220840dcee0d418cadf6020f119968a5c05c4219a05449cac56d4d83edbc0542018601ff2cebc86e418f80650135c0370a105d9e9d936e2804c4013694d58927d56a1942c1a2093c80728032682810fe096aa88c95715ddf014d0492d1cb005111ef104da063c14f8161 else 0x6916d1f88929d1f724dae55a00244044414e98638037c102c1d501d4c0d19212d11aec911c1480aa802fad7c04414935404241d1d1c70242059ed0919e15403c89a20428a5f9405dc1d784c4e167818010295d5f599cc02ed9d1010181e19160c214d9f310ba00c3d8276939492900ec2de59c7f09a61ccd5108401d00279dc09449199f0a1d9d8d0a2ad0f429111151d8452e0941e880fe01f800268a29c04b4499506c51e09cc9421211414e29c076403101b124e20cf349d18c736de48223de2341a740da123840a78c6ac09880ef19cc5c3f24860126411054eec1b1811451e1c1d81e0ac17b24ca99f548b681668d9e808d0062021c414dc04a093c5a0384ee81fe4a0e0128801558e4250a9498897a99a66910e575849fc0a841eb817f08b56cf08075804f81a8a43f419c007901caca1c594a10f38a0b80dd842840b1e053820040520227c119007b8406907504e34932ddf5e0f481df885c010502346a1d00a4d194c20301770a2288b101b6c0b8d0e6a51e697c015f4154848f581b921981cd18e3c83141794089d9f4822d0199545481ad41a5ca1b92286c9184d081e6906999ad40674122296481bd460e063380c488f90572489e2196d1eb9a0c4040207e2d188174a21391ba0130ad9e98d8c1a980f3da0b6c564dd5c6246d8e523fc2241c00012d2228d04a80c8c0a541be91c7c5d0d49a0038593c42171077c4d5801f80d5e8fc01bbc85181dc8053c17dcdde49dd8048e237040fdd0ad0d4c1e2d0f6149481a9401cc00440b10a3405f5c0286c8810b9c028c9360047412491820c582c5d81374231c9f3c176ad478046405741be4841edd4c96c597f619e90c8d9cf8d11c11a294cc10640c5c887d0eb41ea4dd4c921416b063b25b1094ec23be5cf860c00e3e20b448240a761a4889ac02d418701fe81b3c584d89dd60e5232c1fb95f385faa5cd0e19cceba8796d1459832d4c9cc7003c293068fc8115c1ec003a08378cf2d2085090c19ec147d04b80c908478c44c226182150f310ff2cf2002d8083c179820880d001284521007e40f25479507380c990b901f8c16210f69d60406461ded1b15067007d41ed80c82d99ed24c01b481fc233a8bd018466421415a80e49fe01ece890003d4a3c45c7d159c15108fa1d948162813c98021962045809d52d242227814380a440a981014c8aa9e3c017405f010305732d66c11fc03ae909c23e50f5d198919d98800007c03901d5994691d769b0e02120bced36660e40aa018781164144c5438178c1ab5ce5c0ad1106c96eaceb0a1755ea2d2601aa)))
def rootMD11 (i : Nat) : Nat := (if i < 7 then (if i < 3 then (if i < 1 then 0x66130482fecd992a982413fe2e9545c120bf73684aa60905ef9b625530482bfc5caa298241fda54d5248110cff32ad01029867f992680814c3fca98ac6a0a81ebd6096160560f5eac2c0302b073f598545815839facc262c0ac19fd2a53160560cfeb42c88a6907ed5634c521593f3ab2aa2b12219fd2a55158910e7eb02c13221877cd8254993043bd6c12a4ca0219fb6a1a564810cfdb4ac13240876ed52609960c3af6c12a4cb8219fb6a15264810cfdb24d1102987f4d53549304839f6c0b24c1061ddb54da564810eedaa6a93240875ed875cd920439f6c3b50c90215fb6dda864810afdb70a9b240857edb869592042bf6dc2a4c90215fb6cda864810afdb66c13240857edba5cd92042bf6d9b4ac90215fb6cd52648109fbb66d292298775da554993043baea9aa4c9821d7761da764c10ebbb0eb9b260857ddb869d93042beedc34ac98215f76e15364c10afbb70a93260857ddba60993042beed9b04c98215f76e95264c10afbb66a93260867bca950941583b9ea9aa4ca021d6f61d7365010af7b70a9b280857bdb854994042bded9b04ca0215ef6cd5265010adfb6c51b309066fd9869893483a7eb132eb0861d3f61d7165830e5fb02c132c1856fdb7285960c32fecc34e49a4157f6cd8265c10abfb7051b2e0853fdb814d984831fed4304c88618ff605a960830a7fb66c0b301053fdb80c5980823fedc152a12c11ff6e853661208ffb66d43240847fdb36a1910823fedd062cc04197f69597584308ffb6a54b02b047fdb32a5815832fed132eb08611ff6c8a9605608ffb6a54a84b047fdb568d924423fed9b2ac9a411ff6cda564810abfb66a932e0847fdb52a5325823fed8b4a982215bf6d8a954d208ffb6a54a629047fdb52a5824423feda952b1a211ff6d4a9589108ffb6a54a648856fdb5285960c23fed9952a0ac11ff6c8a9505608ff974a9b289066fca958d415823fed8b24c8a611ff6e5a2205308ffb74c88a69057bdb4255934833dec934840a615bf6d89564d20cbfb24d39029847fdb32a5814823fed9152c0a611ff6cca9609108ff974c13268847fdb32a5654423fed9952b12211ff6cca954910adfb6c54a629055fdb72a5314823fe5d33098a411ff2e9944c520afb966d23309056fdb624d91482afedb926c8a411ff6c8a960d108ffb6454aca8847fdb22a5634423fed8952a9a411ff2e95364910adfb6450b2c1847fcb96a1744823fe5cb4ea0a419bf6d8a954d208ff972d29269066fc956989348337edb15298a411ff2e5a114d20cdfaca54ac48866fd632a562443d78b0b00c0ac1fd85495148110fce2caa8ac0887f495354930483ed4ba284b82415bb6c8a165830ad7b6850b2c18567db5285960c237edb152a9a411bf6d8a94c520a9fb6e50b2c1852fdb8285960c22fe5d2a4cb8211ef2e5a420530 else (if i < 2 then 0x21dbf595985c160edfb30b1ae0b07cfd655c570583e7ec3ac8b9ac1f3f5cd635c160f9fac6b8ae0b06efda558d71583b7edab04cb061dbf6c58265830ebfae6cc2e0b075fd985c570593afecc2e2b82c1d7f6d58265c10ebfb66c132e0873fd9861d844839fec0b52c10619ff69da466120cffb52c3b089067fdba66131482bfedd0a6cc2419ff6c5a060910cffb42d4b041867fd986a0934833fedab50c90219ff695a960810cffb66d43240867fda36a5820433fedd304c9a219ff6e98264c10cffb74c13221857fdb168980442efedaae2b82c9b7f61da55c560bbfb6ab8ae0b067fda56619348377ed2ac6992c19ff695984c520ebfaa6c132e0867fd536a1924433fea9b50c90219ff6e95364910cffb74a9b240867fd98694934833fed434ac90217bf6d4a258d60ddfacad2924b06efd6369492582bfeda952c1221dbf5899558430cff974cc2829067fca95cd415833fed1b30c8a415ff6c99360110e7fb30c9b029057fdb9149814c2bfedc8a6cc241dbf5956264d10edfacac9ac08867fda864d20442bfedc15298a415ff6d4a94c520affb6251b309067fcba66131482bfed88a6cc2417ef6d05260530defaa4d29229873fd9860530483afec3b4ec9821d7f61d7364c10cffb4e51b309073fd9814d81482bfed8952a9a419ff661a124d20df7b08d08a4b26efd6368452592feed993098a417f76cc954c520febaa6a9260905fddb54c530482f7edb146cc241bbf661a624d20bbfb6e51b30906dfd9869c93482efedb926c0a416ff6e05366120b7fb7049b029057fdb5661204427fedd0a6cc2415ff6e193481109ffb7429b02904ffdb1689804827fedd126c0a413ff6d5a3645209ffb74a9260906dfcb769593482bfedab26902217bf6d8a954d209ff974a9b30904ffdba261314827fedd12a98a413ff6e85364520bf7b684ab26905efdb6255934827fe5d30ec9a413ff6cca960520bf7b684aa62905efdb625531482f7edb15298a413ff2e9984c5209ff97498b00904ffcba65531482fee59b48cc241df72e5534c120aff972a9b309077dcb94c530482bfe5ca62c02419ff694a94c520cffb6a54a629073fd9824d81483bbea9b4ac9021fdb54d8254910dfdb50a9240887f6d5354920443faea9aa4982217f76d5314c1109ff974a9b04884ffcba54d804427fe5d304c9a215ff2e5a560910efd972c12a48867fca9681824433fea9952c1221dfb5498264430ebfb0ed3b221875fd875c5910c3df6a9302c1061fdb54d8254810dfdb46c12a4084ffcba54d82043df8a8b00c0ac1efc4c58060560ffa30298a60907fe1b254520443f78db2a2b0221fbc58d5158110ff5284a0ae0907de97350970483bf4a9326902217fa6c8a54c120efb33098a609073f99860530482bfcd9300982419fe2e9984c120aff36029b309077d8b3 else 0x72a9a60907fd9b054d30483feca9b2a98241ff66cd514c120ffb2a6a8a60907fd95368530483fec98b0098241ff6695314c120ffb14a98a60907fb98455170483fdcc2282b8241fde551535c120fbf308b9ae0907df9845c570482ffcdc2a2b82417fe6d1985c120bff370c9ae0905ff9b166170482ffcdab26b82417fe6c1535c120eff330a8240885ff9b350570483efcb9a82b82417fe6c5935c120fbf2eac9ae0907df97364d70483bfcc2b2690221dfe6a19348110dff342c12609077f993601204437fcd2b4098a41dfe6959348110eff326a8240887f799554530483dfccc30298241efe609814c120f7f302c0260905ff9b829530482ffcdc322982417fe6c9804c120bff3704aa60905ff9b82a530483bfccc260902217fe6d4a84c120bff36a4c260905ff9b12a130482ffcd894a98241bfe2e9984c120dff174caa60905ff9b014d98482ffcd80a6c0a41bfe295a14c120ffb166cc260907fd95364530482ffcd80a6c8a417fe6c4984c120bff3624aa60905ff8b960530483fec5caa698241dfe2e5514c120bff172a8a60905ff9b0149814c3bfccc12a98241ff6255314c120dff3424aa60907fd9532a5304837fcd415298241ffa6a15248110ffd346a9240887fe9524c120443feca9b0098221ff64c5804c110dff350d2a40886ff9a8541204437fcd434690221fbe5959358110f7f302c0260886ff9a84c120443fecc1aa690221ff654d3048110fef30aa9a40887bf58254581583bfa5caa2c0ac1fed4c56550540ff6a62b1282a07bf5824c581583dfa98b00c0ac1bfd6893160560efe97298b02b07fd5814c530482ffad88a6c0a417fd6c45364520bfeb624c262905ff5b125531482ffad8926c0a41ff5605314c910ffaaa298a64887f75b354565443fbad92a2b2a21fbd6d95158910fdeac6a8ac4886ff5ba54563443bfad8b04c8861dfb6e58254910efdb72c12a4086fed8268895583bf6c12a4c9821ff354d524c120ff9aa498a609077ed5266120443fb6a9aa4982417fb6c5524c120efdb4ac93041877eda1649820c3bf6dab24c1061dfb6dda864810efdb0ed43240877edb56a192043bf6d9b50c9021dfb6d58264810efdb66c13240877ed736a192043bf6dc2a6c9021dfb54da864810efdaa6c13240877edba54d92043bf6d92a6c9021dfb6a1a564810efdb4ac13240877eda854992043bf65d2a6c9021fe75513158d40efbb3098a609077ddb560993043beedd304c9821df76cd8264c10efbb70d2b260877dda560993043beed934ac9821df76e15364c10efbaa6c13260877ddb254d93043bdeaa322a12c1def6617150540ef7b24b2a82a07ebd6550941583bdecc284a0ac1def65d4250560fb7b0eb9a82a07dbd875c541503bdedab04ca021def6cd8265010ef7b70a9b280877bd5360994043bded92a6ca0)) else (if i < 5 then (if i < 4 then 0x4437fea9b50c9221bff6e95364910dffb74a9a40886ffd83695924437fed1b52a9221bff6a1a054910dffb46d02a4886ffda1681524437fedd2a4c0221bff6a15264d10dffb74a9326886ffdba54930442ffeda952c12217ff6cd8254110dffb0ad1b24885ffdba60532442ffedd2a299221fbf5896564d10bffb70a9326885ffdb854d92443bfea8952c1221dff54d8164420ffeb64a8ac6887ff58154532443ffad0aa299221ff7695314c960ffdb64a9b04887fedb360952443ff6dcb04a9221ffb6c58254910ffdb46c12a4887fed826a552443ff6c1340a9221ffb4c9a160910ffdb04a8a64887fed8254993443feed426299221ff7695314c910ffd972c12a4887ff9b054d80443ffcd8304a8221ffe6d53258110fff360c12608877fd836a552443bfedcb04a8221dff6e55365120effae6cc284b077fd9850971582ffedaa62b1281dff6a59360520effaa6cbb269077fd9564d81483bfea9b2ac9a41dff2a19764d20eff950cab269077fdb54c9964437fe9934a90ac9dff6a5814c910effb52b2a648877fdba61593443bfedab04c9a21dff6e15264d10effb50a93268877fd98549914c3bfedd2a4c9a21dff6e55264530effb72a93268877fdb154993443bfed82a4c9a21dff615a264d10effb2aaa2629077fd31661425837fed42a4c8a61bff549a824530dffb74a93229877fdb9549304437fedd2a448a61dff655314c120eff930a93229877fcb9549914c3bfedab02c9841dff6e98164c20effb66c0b261077fda560593083bfea9b02c9841dff6e98364910effb72c1b248877fdb854d92443bfea9b50c9221dff54d9864520effaa6cc3248877fdba54d92443bfedcaa6c8a41dff6e55364910effb06cab248877fd8568d92443bfea9b26c8a41dff2e19364520eff974a9b24887fbda561121593f7ed2ac690ac9dff6959848564dffb6ad1102986ffdb5688914c37fea934448a61bff215a224530eff930cab269077fc9865531483bfe5caa6c8a41dff2559360520ffd944a93229877fcb954d92443ffcc12a298241dff2d5984c520bffb6a98b00907bfd5366181483ff8c0aa298241ffc6cd5158110ffe364a8ac0887ff13254560443ff8c9aa2b0221ffc60d5148110ffe350a8a40887ff19354520443ff4cc284b8241ffa54d425c120ffd350a9260907fe99854930483ff4a930298241ffa6e9524c120ffd366a9260907fe9b054930483ff4d92a298241ffa4c9824c120ffd2a4d0a60907fe8a854930483ff45d2a498241ffa549914c120ffd130a9260907fe8a954930483dfcd9b00c0ac1dfe661935c120eff366cc2609077f9b166130483bfcd830498241dfe661954c120eff330a8a609077f8b566130483bfccc34498241dfe661a14c120eff330c8a60907fd99368131483feca9b3098241ff654d814c120ffb3 else 0xe261514c120fff12ac0a60907ff8a960530483fdeaa32ea12c1f7f5cd985c160effb60c13268877fd5264d80443bfecc30298241bff6c9a524530dffaa4d2922986ffc82694914c37fed2b40c1221bff68da060910dffb42d0304885ffdb3549804437fea9b50902217ff6e1524c110eff972d0304885ffdb8548914c3ffcc22a6b8241ffe2d5a04c520fff170caa60907ff8a865530483ffc4c32a98241ffe611985c120fff372a9ae0907ff9b054d70483ffca9a82b8241ffe54d935c120fff170c9ae0907ff98260130483ffcd82a4c0221ffe549804c110fff366c2a40887ff9ba61520443ffcdcb0a90221ffe6d58348110fff374c1a40887ff9b960d20443ffcdc2a690221ffe54da848110fff2a6cc240887ff95360120443ffcdd2a690221ffe6e55348110fff360a9a40887ff98369520443ffcc1b2a90221ffe615a348110fff30ac9a40887ff8ba54d20443ffc5caa690221bff695845c560fdfacaa12e2b07efd6350971583efec3a84b8ac1bff695425c560fdf974b2a84b077fd8766141483bfecc2e6a0ac1f7f61d7350560effb72a9a829077fd8766193483bfecc326c0a41dff6498164530effb72c1260886ffda8605914c3bfedcb02982417ff6c8a960530bffb7229302985ffdb1149814c3efec3b08b9a41eff61d8466120dffb4ec2330906ffda861d934837fedcb5029a41bff6c5a814d20dffb42c2330906ffdb16a093482ffedc126c0a417ff6d59360520dff970d2b26906ffda361d41483efec3ae6a0a41bff6858764d20dff970d1b22907dfd875cd93482ffedc14ac9a417ff6e09564d20bffb6e54326905ffdb52a193482ffeda930c9a417ff6c4a864d20dffb62d1930906ffca869d934837fe5434ac9a41bff2a1a164d20bffb7229b02905ffdb825531482ffeda93098a417ff6cc984c520bffb664aa62905ffdb814d91483dfec1302982217ff6c9814c110bffb62a9260887fbd8750941583dfedab04c0ac1bff6e98225560dffb04d2ae2b06ffdb8688955837fec13444aac1bff685a54c960bffb74a8a64b07efda558d32583f7ed2ac2992c17ff6d5314c960bffb64a8a64b077fd9854532443bfed4aa299221bff6d5a324960dffb6ad1126b077fdb960993443bfed8b04c9a21dff6618164530effb2ac0b229877fd52661934437fed2a62992c1dff2558164530effb0ac9b24886ffd2169532583fdec3b08a0a41fef6119550520effb70a9b240877fd536a192043bfedd2a6c9021ff76e1534c110ffbaa6c1260887fddb254d30443feed8aa698221ff7609314c110fefaa6d02a4886ffda568d824437fedd306c9221bff695a960910dffb46d4b04886ffda5685824437fed1b42c12217ff6e95360910dffb74c1326886ffdba60930442ffed8b40c1221bff6a1a354910dffb4ac1260886ffdba54d8) else (if i < 6 then 0xb248867fda8689934433fed4346c92219ff68d9864910cffb42cbb269067fda2595934433fed3344c9a219ff6d5a364910cffb4ad13268867fda568d924433fed1b2ac92219ff661a14c910affb70cbb269067fda8649914c33fed4326c8a415ff6e09564d20affb66cab269067fda564d91482bfeda930c9a419ff6e99220530cffb70d48a69057fdb914d814833fed8b5229a415ff6e1a564d10affb70a93268857fdb868993442bfedc12ac8a615ff6d9a564d10affb6cd13268857fdb568993442bfeda930c8a619ff6959364910cffb4ac9a408857fdb5249914c2bfe5d30ac9a219ff6c9a920530aff974b2b268857fcba549934433fe54b52c0a615ff2e55260530cff966d43221067fda914d81482bfedc2a6c92215ff6e1a364910affb70c9b248867fda864453482bfedc126c8a415ff6d5a364910affb6ac9b229057fdb564d92442bfeda926c8a419ff6e99114d20affb664c3229057fdb914d91482bfed8930c9a419ff6949864d20cffb464c3229057fcb954d814833fe54b52a9a415ff2e55364d20cffb504ab269073fc52661815833fed48a4c0a615ff2e58354910cffb4a54b048867fca96a5824433fe54b42c12215ff2e5a354910ffb33098a60907fd9954c530483fecdca6298241ff6261314c120ffb17298a60907fe9b854920443ff4c1aa490221ffa5499848110ffd2a4c0240887fe9b354920443ff4dcaa490221ffa5499348110f7db04c0a64887f755159532443fbaa8acac9a21ff7549314c110fff364c0a60905ffdb12a553483bfecc34098a41ff76c5534c120f7fb04c0a609077fd98255314837fed1262c0221ffe6cd514c120fff36098b00907ff93160130483ffac0a6298241ff72e1314c120dffb4acc262905ffdb52a531483ff6a930298241ff754d814c120fff364a8a609077fdb94c580483fdeaa262b12817ff6d49360520dffb62d2926907fed8254930443ff6d8304a9221ffb6e1524c120ffdb66a9260907fedb154930483ff65c2a498241dff6e55366120effb2aa9a829077fd5366193483bfea933098221bff6a1544c520dffb4ac1260906ffd536a191483bfea9b3090221bff6e95364520dffb4aa9b269077fdb954d20442ffeda946cc2417ff2e95366120dffb30d2926907dfd875d5934837fed0b0498241bff685524c120dff950d0262905ffdb560530482ffed9302982417ff6cd524c120bffb62a9300885ffdb854d20443feedc2a698241ff754d824c120ffbb64a9a60907fdd5354930483fde5a352a9a41ffb6e15248110ffdb66a9240887f7d5354980443ffcdab0298241ffe6e9814c120fff366c0a60907ff9a860530483ffcdcb0298241ffe661814c120fff360c0a60907ff98160130483ffcd2b0298241ffe655814c120fff370a8a60907ff9a260530483ffc52b0298241ff else 0x3fed434ec88615ff6c5985c540cffb50b8b22184ffdb8695715827fedc3444aac19ff2e5a260560cffb4ab13268867fd98688955827fe5d2a2992c19ff6a19364910affb644ab229857fdb1261914c2bfe5d2c4c9a219ff6e5a114d20cff966d2b240867fd95688814c33fedcb4440a619ff661a114964affb62493229857fcb968d814833fe54b26c0a419ff6959258430cffb5054a629067fca96a5314833fe54b4098a415ff6e15364810affb66d2b240867fc522a5815827fedc34a982213ff6e1a5481109ffb70d1b24884ffdb36a1204427fedab46c92213ff6cda5481109ffb62d2a60884ffcba4c5804433fe5cb4a982215ff6e1a764430affb64d4322184ffdb868d5204377ed2ac8b8ac1dbf6556258540edfaa450b2c1877dd984c532443beed4a6299221dfb6e1a564810efdb66d2b240877edb854992043bf6d9aa4c9021dfb2cda564810ff9b0498a648877ed826a552443bf6c1352a9021dfb6095264d10dfdb24d11029857fdb2261914c2bfe5d304c9a21d7f5cd9764d20eff172d42609077f8b969530483bbed2aa4c9821ddf54d5264c10efb970d3b26086dfdb969c814c36fec934e40a61df76e15264c10efbb74a93260877ddb3549930433fed2342cc2419ff6a5a54c960cffb4cd2b261067fda558d930833fed0a86cc2415ff6c59550d20cffb50ca2629057fdb1661944833fed2b24b0a819ff68d9258540affb66cc284b057fdb325593482bfedc124c8a619ff649a920530affb6acc2608857fdb954d304827fedab4448a613ff6e5a2205309ff974a93229857fdb560593082bfedd302c98415ff6cd8164c20affb6cd2b261057fdb159593082bfedc34ec98215ff6e15264c10affb74a93260857fdb3549930433fe51b42cc2419ff6a09364520cffb4a49b229067fda8249914c377eb1b4a90ac9dbf6616550960edfac6cc284b06fbd8469521593bdec232aa1a41cff6cd8166020cffb72d1b040867fdb26a1934433fedcb46c08419ff6e5a814d20cffb4ad4b048867fdb36a1924433fed1b42cc2419ff68da960910cffb46d4b029067fdb16a5820c33fed9b50c88419ff68da960420cffb74c0b261057fdb3685980833fed0ae8cc2419ff6a19764d20affb66cc2e0b04ffdb8695215927fedc342292c95ff6d59258540cffb2ad12c2a067fda565d934833fedcb4a992c15ff6d53265910cffb72d1aa40867fcb9695325833fed434ac9a219ff699a564d10cffb4acb3268867fdb1695304433fed1b52a92219ff661a548564cffb72d2a42b267fda56a5215933fed2b2490ac99ff6959848110cffb74caa869067fdb168152442bfedab24b08619ff6cda564810cffb46d4aa40876fd52685960c33fed42a4c9a219ff6e95264d10cffb74a93260857fdb50c5980833fed132ab08619ff6a1950c420cffb0ad1))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x9a9e209d6e9cf49c5e9b209aa69a10995e9804978a96a09626959094de93f49326927491fa90f4900a8f908f328eb88e228da88cf68c288bae8b188a6689b488768818879e872486c6864c857e8520846e83f48396831c824e81f08106808c80127f7c7f027e347cda7c0c7b3e7ae07a827a24797278dc780e7778771a7630757e74e8748a73bc73267290718a70d870426fac6f4e6e806db26ce46bfa6b9c6ab269e4696a68d46822678c6712669865e6656c650e64b0643663a062b661b060e25ff85f2a5e785daa5cdc5bd65b245a56596c5946585c57e257305662555c548e53a452d65224518e42f650c04f9e4e604d764c384b4e4ab84a22497048da47f0473e473e468c45be44b8443e438c42f6420c4122401c3f323e803dea3d543cbe35f835f82d942d943c60263826383be63b183b183a823a823a2439aa39aa35f82d942d9426ce26ce38dc380e377836c635f82d942638356234cc346e3410337a331c326a2d94320c319230c42fda2f7c2f1e2ea42e0e2d942d1a2cbc2c262b202a5229bc28d22874278a274826ce263825da259824e623fc236622ec225621f8217e20781f021e6c1dba1d781cc61c141b2a1a78198e18c017d617400f90168e1630156214cc13fe134c127e11cc10c610680fee0f900f320ed40dea0d540cda0c600be60b6c0ad60ad60a08097208f8087e0740068e05a4050e044000bc03c6034c027e01cc015200bc005e00017fe6e15348110bff370d2a40885ff9b865520442ffcdc346902217fe6e19348110bff36ad1a40885ff9b564d20442ffcdaa6090221dfe6619548110eff370c9a40886ff9a8681314837fcd434298241dfe6619348110eff36ac9a40886ff9a568530483bfccab2690221bfe295a04c520dff3424c260906ff8a968131483ff8dd2a290221ffc68d5148110ffe174a8a408877dd984c530442ffcdaa64b02217fe6d593581109ffb6ad1924b04ffdb568893582bfedab26b02215ff6e55350520affb624ab229857fdb125593482bfe5cb0298241f7e64d715c120ddfb4ab0a64b077bd5464961503bdecab28a0a41bef551a358540fd7aa8b12c2a06fedba54930483bf6dcaa490221dfb5499348110efd970d2b240877dd53661304437eed9b4a48a61df76e5534c110efb972a9a60886ff551699324437faa8b4cc9a21bfd545a14c910dfeb74a8ac48857fdb366170482bfed8b30b82415ff6dd9850520affb64cc2608867fd95680814c36fed834e40a61bef551a358940eff172d0a60906ff995680814c37fcc934040a61bfe6a1a54c120dff150d0262905ff9b868530482ffcdab42982417fe6d5914c120bff3664c260905ff9b22a130482ffcd992a982417fe6c8a54c120dff150d0a609077bdb854994043bded9aa4ca021cff609a864430e7fb02c13221873fdb9605820c3 else 0x492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234922b3221d216b20d51fcf1f711ef71e451d931cc51c4b1b991b1f1a19194b187d175b16c5162f1599150314a513d71341127311dd116310cd106f0ff50f970f1c59470e6b0d9d0d070c8d0c130b7d0b030a51091308b5083b07c1077f0721066f05a1050b047503fb0311029701e500fb0048ffceff54fedafe7cfe7cfe02fd34fc9efc40fbc6fb14fa62f9e8f98af8d8f85ef7e4f76af6f0f622f570f4a2f3f0f376f2fcf1daf128f092efe0eef6ee44ed92ed18ecbaec40eb56eaa48396ea2ae9cce936e8a0e80ae720e6a6e5f4e4b6e420e3a6e2f4e296e21ce186e0d4dfcedf54dedade02de60de02dd6cdd0edc78dbe2db30dab6da58d9ded910d87ad81cd786d728d6aed650d5bad55cd4c6d44cd39ad33cd2fad280d196d11cd086cff0cfaecf34cebace40cdaacd30cc7ecbb0ca8eca14c97ec920c8a6c848c7ceaa78bb0ec754bb0ec686c628b9e2b9e2b984b9849f8ec55ac4a8c412c3b4c31ebb88c2a4c22ac1ccc0d8a0f2c16ec0d8c07abf90bf16be9cbe22bd8cbd12bc98bc02bb88bb0ebaccb9e2b984b926b83cb78ab6bcb546b440b356b2dcb27eb0ecafe6af34aed6ae94adfeadbcad5eacacac4eac0cabcaab50aaf2aa78a9fea8c8a9a0a926a8c8a84ea80ca792a718a6baa640a58ea434a34aa298a1e6a16ca0f2a0409f8e9ef89e) else (if i < 10 then 0x623a03283544e56022d04ec601f015a13f0c06309a41f2180cc076848203c80cec8e820403223958c4770a509080642805980384d60f9100eb992c06506a08076623a03c82ee405d80b40908064200580bb00ec12100c85c1200f1c09813105dc0c60190f28d005803b81d6032140e308581f404f48019842c0f88278408282090820207643420b7126d55b6db495086160777493c35c23b051a2e4600dc03300cb84ae1ad1e2828c21543c95c85f23b6a769205325459201e9e4b741c0ee01dcf80812f801d04d4404b897c098413b2006e01b006605a40ed07504267e26c03600ce077c5bc2133005847504c209d9002cc04097c00e826a2e02a0fa03a83d53423604ec723492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923492349234923 else 0x486692a117f1366b80432a6434209643d90ca05680db555d70071421904f1601c006e019f21a094839f451843a8008b90d00dc03604a790cd2571df04e008c0869601163bfc86822e10b5ade13202768005891d08f014906a8a09c011603dcade136140e304a00e5c5ca8a30864c0116492071a3de09e94a4608b300fa5a30bc084c13302d5010911d784de2374d8818e60838ccdc26f11ba6c40c7301bc107040d84de236cd8818e7a7fb00f081b06b04ce212c2899af031d2055a0f588d81d8408380ecc26f11ba6c40c730057212838a13b82765e42d075016c254b53814907ab0a242427407845892342d145e0252063a005f020807508389b1022b0a6c46c19e480b7811087e90d42d585103d4063a0075c05417bc46f0a103acd806c0f4cd8e1380fa1701503008ddc2701f4280b200f98dc10d03ac505f81f407547213484a12f83ac401d48eb083b09ba5ab11b0678e03ae04584d84cc4759701507d01d6180b202784340eb11004829001e48481a101d813b380e4475841d84dd2d588d833c701cb015c4670a223aca02cf08600f98dc10d03ac6044c082030311b095309c05fce0e701040e7843203d141ce03db168086407a2d00e0d624263c26c21723a8607b601f4b4617810c941c209b41f2180e6e8cf21609981d803d18c6807c41d6180e609981d803d10061c03ca46c1b113aa5a01043d0d610c845892351478b40252082200f6c2701f41e0160bf84d0309441a30490268202320154c8a07600f4500ac23d01e81f4201bc07b02fa09e100e305fc2681aa3489582760e1a4265045811405d821a05231df085827404f53c8682ed8ef843410b04ee09d9e0e040b681009b01f22f21a10d037a094e3be0c3843009da025106a813d1846200fe14b88e83ee08062e4133230078118412a844b88d83aa4048423d020b11b0754a128831c09e8f00781b05c4d80b707540ec01984846005e07709601abc5bc233c4740f1400798b901c8120027a5038d9b9098413d2024e10701c60fa027a5038c18e04f4600f8384130827a40144220031c0aac29007d031827704f1206e721da4be92c0cfe14f8526144128839c05b830e09db4079e42f17302d02422e1488cf818e03b042809e18016803440b0cc012b4847a13b8276604b54d1946823c05241aa36a3203d847bc8580c603d02920eaa007a01e156908f427704ecc88e99b54268424031829250c83aa8037016198004e908f427704ece042844010e81680eaeaae04484348e550078058c21f01d8a03af123cac04bc042045a600f80ad09fc612e007a09381c611283e809d9c20c00f022503ac13b2f13601b00678b7c0ee10b81147e26c081c47607703b408a300a310c8101c03818d8b782647b25689f01e716f02d0132301e764b592b451f2cbc8e83f40f600f49018c21906a86077)) else (if i < 13 then (if i < 12 then 0x4a3b061a309b208907a0524803ac18a13b8c182c01e0c509dc8079c0f400282940639403007140c70528848c80b6c8e839c0818484603cc187018c21901cc1f2031ce00ba0ec14000cc4912012a80681aa0898a4069c0a02782f210c816a62034db4013f11d03b40b5300b800fd08e0416023807009fc85d2e585080b6b01e40e202d4607a81ec333830e403d413302d0187201d8333830e303b013302d0187200e603181ea63582f388e816a703b06600400603984320bc98d788e816a602141ee019410020c4e0fa82003056813c0190100200b207acc8a63583dc6dc816a7095c1f504006039e23a03181ea63584ae0bc816a818c458f04a41002045c08803560801067c06ad96c07d4100284440d10252080100f6017190b83aa076016c0f53f04c02f00b800b83af03d043204141d806dcc9407ab00de00ec063013c17908640b53841801d80c60278252076816a708b41f50400685081120800c1d5022410018ce202e52e40c48d000449800d016c17608640892847603d00c788e80f6076816a736d006308640ed02d4b8b782520638c0510866219016402ac4740c7061d0028d23a11d8410119030e6c4740e901dc0f1061cb45002960c38c05c60fc05b070390b09040f7384320bb02940318208560fc081d55012502d4a039e016109841c0bb00a809280ee032a5e44007d1f103b403302d4d813609005a026407894219206e968018c14a2e01c02d830e3e5600f6089418462eea4903b8e074614690c810426682960e29c0eec03823361af11d26e709e3815047480b885dea1812fe1454b9200e2038c0b51800010900ea00b62e5c4881e812ea005608340f408482320704221380eb4b904ba0421022508e406424ec2402b044c03f12212e04581201825c040427508b893a284ee12f81c611a10213a91b0a3061c8071e0d6073348d85180ce60398213c28c067271460e782663e46c233061c611ef232119830e4084b16a01d422603dcbc86843c094b92812a63be08004348086b90d08af4950528129c77c1420879223414afc85e9214b7825211a1d007e2440e208cf8bb8474db402d50a86806fc48f1774dc916610e9d50d047784aa6e58bb0874c64980fa0bb22d8080523a03c1ec9502db82601eb90b03ac1aa3f492877209401f81c545de23acdc818e9335807a022413336b807b36920041044a03d523b4b782007e0ff490073d07a031e91d07d810046120103cf82601cc0820973554052407a400e608f80f4076101f5e0fc1cf061c14901e8da48723a02c80ec6da04be0801e0a505e716b03c390b03b791d05e01d5480f402cf21742682926da00ee7336b03fa137490286408936d0100472cb05180ea475d23a0448200703bba4962ef11d85c80c73041d2116ad20e284d65b434117e6dc07975bc21c04ecf4868416104d21f else 0x8641d304a4a116030e2c6e409a09b81872042412a21f80c3921230a0121884ec8109041c099e1440c397007037801f04009211319a02e038b8080200601c54cda9240e9c03c1490748e00fa8d883d28d6041601dc85e1436a72186a495c1c503fc1002500ecee845847e030e508f026c061c60c404c0065830e407991bd031c7062614253d83e84044817f43f0187202fd80691bacd883e803d030e7016c21a0678606f00c5803813411d83e20c39c0dea34409a08ec1f1061cc019a0c403aa3e807b9407b887013b182c403d026380882005094823d08d01872047a12f80f40c39007f09d013f184340df827e301eb00e66c421a08d0a895037c11a0ea49814691ea47509d014013a41d514b9a0f610e038a4427907588701492492303aa43609d9007204ea07540dc2532845409d11dd03a90072c26e07523bc86ab612184d84384779417f04810fc061c8129047a03d030e4090c19e1601c11301ee13a0104cd8843403d201d544a8274184e813f02003291b01200b0803d5530a44574a194601e2dc94242770384080180f781f607a287a07809a8a1a383b9a66f045807601b48618d8635d21caab2aab48580f0dd336c3f955b011c03d90c2478a1904f134342b69486822680bab73109038c866bc12f43f0187204c611302943095390e70ff012a925557555b90ce42c1a7a93b0a103c815d7587e80ea03841b04fa50c830209d20f299558832022255004e81c5302fe120030e308c0187110a883d03ef2cb0294508b014a11b2c0e90266341a1022b55107209d814a32a6a0fa8200307e80c71013384b8815b098c8ac052888f90c4e0820c17f04490fc061c808902fe47e030e4058c07a0528613ba26a11a0294401681a10528612b82b685602944056b155172100e989d209c102801159212095080de82520800d58f08641f504009034041f850ab6a058443c681c80e1083101709d01310528176c5bf11d04002346044c07be01c041041c075043403d200f3c47701107e31720410c079c2b980762d410d02086038918f07a82342037c072027e13a100f3052808247c80ec0410c06f00c404d04760f8830e600b0c4d359826b8868a66b8b9612a0c20f959c13a4868811c901fc4884bc11704806000c0e506b023e2034009c820003d018e50614187b5569e501f027007a805101e01e803196a470c880fa82004056807b47c42650400b45082c4a11043206382926c4d80a909ce89d073f90c04f8212312014b0224db66042203d03ea08010ccd635c126039e97209e30bb2865081604f009e8292408891eb03121ee0400a01e010203f818d8b78456608400f1257001f03b40c604c808a401e661100e60c380f4c8e818e7015007300a818704cc0c730263322830e0801005cd4140f6171ccd4e43007535bc8794f12103d010403a803eea7) else (if i < 14 then 0x1880610100229700fb02003647546807d8100228d14b6c8d072203ea08019068089408203d81c5a474100381e603d02944760200508941f50310100202c406204be0801146891a0e4407d41002a84541f810411a100f504100710714e4a0400c07a80ea803a0d002deaa80711c9413bd92b48ead596097c1001a14acb284be08010468097e96d040080a4816a236d291d04006666a00f4b289760a4846868280081804418765bc25f0400e6110978cb2829211a1405ca47407b23b4100280380e9c1d203c10c930278595c5b4c9605ea82601e1003d83ac07480f04746407b03c41a983a40783030f0b5214a0a4b924033d23b07822c9405fc8c834720e905e4daa803100fa82004d54058f07d410026aa02ec03ea08010a5706ac1001c13b00781d20801017606aec96b24c67d05e40783848148ec13c87680f0519f41aa0400633e83aa8298200403c916a43ac1f506a01873407e0328054c8e2adc65f1a03f05881330400806484680c38c20840fd8bb047c18b0400d41f844a0f8016a403a5257062c100201d312b831608010c22c0fc16204008611607e0b1504c50c82660801c83fc1a291d031d848061cc03a94240b1414b00a323a0801f4903464832018cdb401e8d81f9a6a0c402004381407a07d41002704c66900e7c8584820a5e92003180f46de2a4bba10c965097c0780400d00a414ad2483100801407bd550063061ce4a01e4c113811270280c74b669200d59c9480218e4ad550079286407b3010da4800ee6dd00f60801862751c01f5040080e581e20800c62701e81f5040080154c8a434039a06399706da4a348427008276d291d0308100301ea12fd2e408010660062c1001d2d8112e92072500c65013c0636474db40400a02d98440bb1432044940f601700e2d55390b03d7490016d04e2523a03c820040224c22a47407705d81003626c07b10d013b913a02e72180a5811266a1adeb51a08ec01e814a0400a84ebb680a4816a452ee09d05e591d018c1003097c02d82003047c0c405e01002604c666b2320c38200533350a14865919061c100301ddd2221d3051c4320a4838b45d820090413965a924100254010088158080128d7828c0e304008c1104320800c226b59550e04f414b2e0d6090820034088162097c07a0400ad24e095c48e23a6de14ccd03d425f829f1720400cd24b2398b9197c4e43421e04a460f4d14610d02524257b0a1c241072022c21c04f4e096612083904380949790d04a421e1f21e0f4f21810e02525444c129086060f4827010d02524a5bc12902d4610ccc8a6dc99700949407b04a4100180c60bc844a10c816a536d012903b40b5200e603182f2635a23a05a9821e02b41291815a0948803304e827404a4843cb00e107501fa85833c14002528038e80f0864129200f2072e2e54518432509ea80f else 0xc22044a81f81c40411421901e80f602080e22841942400b210700b80711a422020b02601700e22844a07b1bf9aaa01c402e60d1c85e9209074821a04a47051a4d46da02524d434111038cdb504ec21e3317708e84de09d03a40949804e01928d77424100828d5743e0948c5828e08010a3a62ee0a303b81d204a4c00d834e0fa820047438cbab24807901d813932f807803c12474999a0278292851038a0801e00780fcccd51a1e4407140c7391d303a81ec803a07e07169216ab818f48ea9e44565953607140c72a00ef221b6a063830e579100e937801c5031ca803c01f48e838a0801422503241871dc88474907f48ec9760e282007801c082b539e4a430cb6a77217a48010483d21864e51cccd91a2e4407140c7280b285012d8f251084d52ec96a41d41002a3e209e029439530))))
def rootMH11 (i : Nat) : Nat := (if i < 1 then 0x2b2076001012e806e894b8f48a005464b9252411fa2ce024013c0a82363237829008800004ed84e9515a01723f3020ea5c9ee1258548139c4572bf438e91304a640d82d4082018565e00d930ed3b43378296026c1142a5829c0b700ae84b942805903780fd0074944020c0aa036e41502ce46f835e84a4a09240933a13d5b8211da10207ea17205c048c08b034012d8994049a52c01784ec0ba04d61559354148c3a44ec02040ad8390ee1037ccae81d0110038e02f830089d8917239ac1008d81200750492a3201380ecb006e83815232023d0069145a00382be052815a06e3be20c9aba607c81e686c234483613f44ef199803cb3e20f6b47810b00020930298a6593c00f044a6119d3ea83981ea91904328bda33e0cdc8a846b054089e832c066902a0984b524eb839489b03480c4d3cc908cd3806c022490948f401233de019943e62e818aaf3b819413835453480240c300020b812dc000016924c851e027dc2a070839a01f03f24dc88ad50700000008ba404404fe05803640bc48c2825998945f519a06dcd146ba110a14600701262534443d0300008bec132189209c81ac09b94cc321301210282ff11e84860be224a13020c602800b60bb1b0400d012a12a80c806a821214f38ec013d18c095924041284d0000d3440974c4aed4b2b40cca08052cc9ea4d383dc0cf00f622d03580960308023cad688e0146ac502c50462ad20ca20f2855826a05381fe092818286d81f687a189b54898f054e82ae0fb8b6848a81910cc021a0f488ce8bf84ae13e2cdcc8723221533acc8d43bcae8183a20638c916a4409ea33001c037840ced684208ec8424cfe226829181be6293ae60a1d45201882a486a0196e1583808bc81cc4a30530015582d0ae200210093d041e2010068a0f627901ee4dd84ce0c124440ff3362154005008a1a4d25d23084160058080c9f60fed9740f300b24ee222c01a886a84c823c0b9d0d0022c36145e93e223280d60089ae02b403ea8d08b8e11a00a54c5bc78e6402320d1827f0f800844db01408351cc200e50c882fc068ccc14956e185340c653380d82c7c0d4a11ee301a0b131201050100081a01230100004b070007160335040502000000450b2c00100001001e150a0100090c000401050003030a30060900022c001d0a070f070d0a0d5a0d172101000009030000050d0d8209000a08009f040707211b00031d12032e27090e000002000200051d3018400000350600010700000008002b2100140200000f020a0002480c0901000000020201061f020006003618020600040106261a030708210300061d12001d0303012e3c0002000201020b0425211b4808002440010205010b000c1f0001021202000904080e080005040c02002502010004061b1d2403080247024a3d040e1400080f1b1c010301867808003b else 0x778ae550d841a078c8fa4114a9403b103f2e15b0e20500c606700140d3024527f301a08522f8071bc560ef130c0a201560a384d82cc01ca0b60000c9800780f500008a1dc54cb9a37e12803e48a648ea0b2a0ec1200250141853a4e2a8680b004e00b4b8dc02500000000041063a21364105280e700000451d28105129000082ba518049f04282f431f445211c80b80dad13411b89bb2b3803e83783e0143c8e0945508814b048809984be13128d052203a40dddc5c0cec41150413c68d913a805b83c64839040142031e6fe253241843d693c000a899815cc460888b15a3b814002788a704062f3c8ed3138)
def rootMD10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xff69c854d5248110ff699854d5248110ff698054d5248110ff69c954d5248110ff69c054d5248110ff68ca54d5248110ff595254d804c110ff68c954d5248110faf5c56096160560d7f5936c4954c520cff5512e98264d10f5ed875cda864810b7edc82e95364810d7ecca6e15364810d7edb82e95364810cfed522e98264d10f76d512e58254910dff1816c4a54c120dff1516c4984c120dff1816c4954c120f7f0b9605514c120b7f9c82e5514c120ffc582545314c910d7dd956cc984c520b7ddc52e5314c120ddbd846d5715c164f4fd655cd985c160dcfd636d5715c164e5fd716a58761120d5fd986d5715c164d5fdb35cd985c160c7fda56e0a94c520a7fdc52e9984c520a7fdca2d5984c520a7fccb695984c520d5fd956dc9360520d3fd956e09360520c7fd956e89360520c7fda86d4a94c520c7fda16d4a960910a7fdc52a5a060910c7fd956e8984c520c7fd986e8954c520c7fd956cca960520c7fd526cca960520c7fda06e0a94c520c7fda06d4a94c520c7fd952e98264d10d6fcba5956264d10d6fd936d8954c520c7fcb52e9984c520d6fd916d8a954d20c7fd912e95366120c7fda06c4a954d20c7fc952e9984c520d7edb02e582549109bfccb54d9860520ffc152605314c120fbd1814c5804c120cff1a16c4954c120d7f0b9605514c120fbd1814c5804c110f3e998549814c120ff4953661524c120ff4953549814c120ff49c954d524c120ff49536c1524c120dfc9b36c9514c120ff4953549a14c120ff48ba54d524c120ff4953549914c120ff48c954d524c120ff49532a5524c120b6f9c62d5984c120d6f9986d8954c120d3f9b2605804c12097f8cb661514c120e3f8ca661814c120d3f9986c05360520bed9c62e5534c1209fd8cb54d984c1209fd9c32e5514c1209fd9c36c4a54c120bf99c4255314c120cfb8ba611545c120af78ca551535c1208ff9c12e9545c120cfb9b4684954c12097f8cb6a193481109ef9c62e5514c120d7d9b32e5514c120d7d9532e5514c120ff49535493048110f3d598605314c120a7f5c22a53160560d3f5986c45360520e6f5632a55158910f72d536095265010d7adb36095265010e76d536a1a564810c7edb36a1a564810f2ed526058265830d76db854da564810d76db854d526481097eccb54da86481097eccb54d8264810cf5db3549a524530b5ddc72e5314c12097dccb661314c120a7bdc52a54250560e6bd652a54250560d73db854d526501097bccb54d8265010d1fd986dc936052087fdc86c8a95056087fdc52e9984c52087fccb695984c52087fdc92e95360810c6fdb66d4a94c520c5fdb76d4a94c520a6fdc22a5635056097bcc96d05260530c7dda72cda4661209de8cb5cd425c1208fb8ca6d0954c120e675652a55158910c4fdb76d8a94c52083fdc82e5a114d20 else 0xbfd1c1255314c120df4db5549314c120fbc582605314c910d7d5936c4954c520b7d9c12cd984c120d7d8cb661314c120bed9c6255314c120dfd1b5605314c120bfc9c2295314c120afe9c2295a14c120fbd198605314c120dfe1b36c95148110f3d8c3661814c120ff498354d5248110ff615264d5148110ff61a85495148110ff61a35495148110ff61a56c95148110ff61835495148110ff61c35495148110ff61c95495148110ff60ba5495148110e3ed526a18264430b3f5c82e55160560fe716564d5158110d7d5936c4984c520b3f5c82e53160560d3f5986c49360520f3e5526058264430e76d536958264810d7d9b5661314c120b7d9c32d5984c120d7d9986cc954c120f74da56095264c10f74d536095264c10f56d536095265c10e76d536a15264810faf1b35858060560f7ccb9549314c120ffc552605314c120dfe9816c8a54c120bfd9c12e5534c120ffe1836c95148110ff4d8154d524c120ffe1b2605514c120fef1636c95158110b7f5c12d5984c520d7f8b9609514c120d7f5986c4954c520fbf182605514c1208ffdc52e9984c520fbf131605804c120dff1316c4954c120b7ddc82e5314c120bfe9c12a1524c120bfe9c1261524c120dfd9816cc954c120bfd9c8255314c120f7d598605314c120cfecca6c5524c120ef6d536a15248110d7f9b32e5514c120d7f9532e5514c120d7f9b22e5514c120f76d535499848110dfb9816d0954c120df79516d4984c120dbf9816e0954c120d7f9b82e5514c120d7f9c82e5514c120dcfdb15cd635c160dcfdb558d715c160a7fdc52a57350560af7dc8549a524530df5db854d524c110ffd1814c5804c120def9106d8a954d20d7f5956c4984c520d7f5956c49360520ffd198605314c120ffd195605314c120ffd0b5605314c120ffd0a5605314c120aff9c8295a14c120cff9a16d4a84c120cff9a16d4984c120b7f8cb61593481109ff9c86c4a54c1209ff9c56c4984c1209ff9c52e5814c120f75d9854d524c110ff4d8254d524c110f75cc954d524c110dfe9b86c9514c120dfe9b36c9514c120bfe9c82e9524c120bfe9c52a1524c120bfe9c3261524c120bfe9c12e9524c120efe8a8549a14c120dfe9b12a1524c120efe8ca549a14c120efe9a1261524c120bfd9c8295314c120dfd9316d4984c120def9316d8954c120cff9b8684954c1209ff9c86c4954c1209ff9c82e5514c120cff9102e95366120cff9202e95360110e5fd872a573505608ffdc82e9954c520dfe8b9549814c120cff5812e9984c520cff5812e9954c520d7dd986cc954c520e7bd872a54250560e77d98549a524530cefdb358da524960c7fdb86d4a94c520d3fd816d4a960910c7fd512e98264d10b7ddc12e5534c120cfdd302e95360910cf7d522e953601108ffdc22e953601108ffdc52e98264d10) else (if i < 3 then 0xec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4e83e15de3dcfdacd89d57d07c6cc2bbeabb8b59aebaaaa1e9dd9ba99798394291f5c38b187f85c8398077d57a376273f46070d6db69a63b6185d75c359156e54b56e54b5194f64f62762764c448346041f3fc3d92763b63843522c62762442442031c21901220c3082032000f1ed875cda864810dee5216d8a94c520cef9b6684954c120cef9a06d8a94c520cfd9b3684954c120b6ddc62e5314c120d79d936d0954c5208ff9c02e95360910d7d9c32e5514c120b6ddc62e5534c120d6f9c62e5514c120d7b9c42e5514c120c3fdba660536052087fccb6a1934811097bdc86cd5265010d6bd526d0a165830c7f5a96c45360520c7f5816c4a954d20d2fd526e0a165830c5fda86dca94c520c6fda96d8a94c520c6fda06d8a94c520c5fda06dca94c520d6dd936d8954c520d6dd936d8a94c52097f4c96c4536052097edc86cda56481097edc86cd5264810d6edc56c8a165830d6ed526c8a165830e3ed52605a960830d7cdba6095264c10d7cdb36095264c10a7edc36958264810d5edb36095265c10c7edb36a15264810c7ed522e98264d1097f9c82e5514c120fe71656c95158110c7dd536cca960910c5fda86dc936452095fccb54d8265c1097ddc86e95264c1097ddc86cd5264c1097f8cb661a14c12087fdc82e9944c520c77d536d4a96091097dccb6958264c1097dccb54d8264c10c7dda12cda466120d75db86955264c10d75db854d5264c10c7f9b069ca366120c7f8ba6c5984c120c7f9a96c05260530c7bda96d05260530d67dc26d4a165830d67d526d4a165830c6fda76d8a366120c6fda56d8a366120c6fda86d89564d2095fdc86cd5265c1087fdc86d5a36491087fdc86cda56481087fdcb6a1934811087fdca6e4526053087fdc96e8536052087fdc86c4a954d2087fdc82e5a114d2087fdc56c8a96056087fdc56c8a950560c6fda96d8a954d2087fdc56c8a96053087fdc56cca96091087fdc52e98264d1087fdc92e95360910c6fda06d8a954d20c6fda56d8936452087fdc56c8a960d1087fdc56c8a958d1096fdc56c8a165830f3d198605314c120cfd9302e9984c520ded9306d8a94c5209fd9cb255314c120dfd1316c4984c120 else 0x410020b81300e22020e01ede42dea7008200b9d240f612005a8100181000c91dc1462015804a44061c0a500c7180f5020809dc0a480c7280f511d281d402dae4aba9dd2400e28233d23aa041cd6580f500c72020e1b6807a8080128038149016a311d320fc11a24bb02960690db53bc85f490602802084e490c3380f5044a05240d31007b005c01ea03880416d4ef217d24002da4a5dc96a00b60400803cc08009a3401001709008075010403d80801348e814a160e901ec016c07af49000b901d8e01c407a8100182250200299a408d0401ec02e01001a0e909f601e0603a403d919d18176025013ec05a90059010010a1900c604006238403c80b5180f600b601d40801007a90e9044b826f88e81d2300e2025220252049410f01332014a09126815808747c09013a0810901871700f039e04cc601d413a0b213016004683f21623b404080b52008a0200200bc0684057c0792121b80f2200e409d04018c0a5080ae01210208302c004d01198c0108020002e03d8107008202f2052411a24010821200ea089807b9402e813201e2380f100c88570133275058bdc041005a900798147018e3016a01dfc1300b4f21603ac0d51c05a80740169e42c04681d530033042c47bc09e900bb00f1016804c8032140a165bb00c83ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4ec4))
def rootMH10 (i : Nat) : Nat := 0x4591e9045001c13216da006dc0110b0400e2665b6780008c1e8752092a56a748d036957380800ddb57019090016880010ec0248c011000019001
def rootMD9 (i : Nat) : Nat := 0x7b002e76a77a48122c58b162c58b162c58b162c58b162c501c56d526ddb52a53148389eb02dbb6c54a62904fd237153661524c1208ef4e8996b9a84b8241f3c198549814c5304830fb26065b4acc2629074fc608b9605514c120bfa4e8992a9aa49824197d58132d984c530483aeb30aa9972a8a609053ee744ba611545c120df6490b8c5caa698241d7d1d32e58154530482fe93a25d2a6a92609071bd605b66d4a94c520e2fac0b6eda95298a41d7b1d42e581545304832fb390d9972a8a60905f92758c954d524c120
def rootMLevel : Nat → Packing
  | 15 => (1,0,10,0,0,0,0,rootMD15)
  | 14 => (9,1,10,0,0,10,0,rootMD14)
  | 13 => (98,2,10,0,0,14,0,rootMD13)
  | 12 => (581,3,10,0,0,16,0,rootMD12)
  | 11 => (1157,4,10,0,0,16,0,rootMD11)
  | 10 => (342,5,10,0,0,12,0,rootMD10)
  | 9 => (19,6,10,0,0,7,0,rootMD9)
  | _ => emptyPacking
def rootMIndex : Nat → Nat → Option (Nat × Nat)
  | 15 => rootLookup 29 61 6 9 4 4 rootMH15
  | 14 => rootLookup 127 257 8 12 7 4 rootMH14
  | 13 => rootLookup 587 1297 10 15 10 4 rootMH13
  | 12 => rootLookup 877 2423 11 16 11 4 rootMH12
  | 11 => rootLookup 251 577 8 14 9 4 rootMH11
  | 10 => rootLookup 19 37 5 10 5 4 rootMH10
  | _ => fun _ => none
def rootM : Forest := ⟨1535,15,fun j => rootMSamples[j]?.getD (0,0),rootMCols,rootMAutos,rootMLevel,rootMIndex⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb9_0 : block rootM 9 0 1 = true := rootSpan rootM 9 0 [(9,1)]
lemma rootMlevel9 : block rootM 9 0 1=true := rootMb9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb10_0 : block rootM 10 0 71 = true := rootSpan rootM 10 0 [(9,5),(10,16),(10,16),(10,16),(10,16),(10,2)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb10_71 : block rootM 10 71 1 = true := rootSpan rootM 10 71 [(11,1)]
lemma rootMlevel10 : block rootM 10 0 72=true := (@block_merge rootM 10 0 71 1 rootMb10_0 rootMb10_71)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_0 : block rootM 11 0 94 = true := rootSpan rootM 11 0 [(9,14),(10,16),(10,16),(10,16),(10,16),(10,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_94 : block rootM 11 94 92 = true := rootSpan rootM 11 94 [(10,16),(10,16),(10,16),(10,16),(10,12),(11,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_186 : block rootM 11 186 96 = true := rootSpan rootM 11 186 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_282 : block rootM 11 282 96 = true := rootSpan rootM 11 282 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_378 : block rootM 11 378 96 = true := rootSpan rootM 11 378 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb11_474 : block rootM 11 474 32 = true := rootSpan rootM 11 474 [(11,16),(11,12),(12,4)]
lemma rootMlevel11 : block rootM 11 0 506=true := (@block_merge rootM 11 0 282 224 (@block_merge rootM 11 0 94 188 rootMb11_0 (@block_merge rootM 11 94 92 96 rootMb11_94 rootMb11_186)) (@block_merge rootM 11 282 96 128 rootMb11_282 (@block_merge rootM 11 378 96 32 rootMb11_378 rootMb11_474)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_0 : block rootM 12 0 96 = true := rootSpan rootM 12 0 [(10,16),(10,16),(10,16),(10,16),(10,16),(10,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_96 : block rootM 12 96 92 = true := rootSpan rootM 12 96 [(10,12),(11,16),(11,16),(11,16),(11,16),(11,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_188 : block rootM 12 188 96 = true := rootSpan rootM 12 188 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_284 : block rootM 12 284 96 = true := rootSpan rootM 12 284 [(11,16),(11,16),(11,16),(11,16),(11,16),(11,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_380 : block rootM 12 380 96 = true := rootSpan rootM 12 380 [(11,16),(12,16),(12,16),(12,16),(12,16),(12,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb12_476 : block rootM 12 476 55 = true := rootSpan rootM 12 476 [(12,16),(12,16),(12,16),(12,7)]
lemma rootMlevel12 : block rootM 12 0 531=true := (@block_merge rootM 12 0 284 247 (@block_merge rootM 12 0 96 188 rootMb12_0 (@block_merge rootM 12 96 92 96 rootMb12_96 rootMb12_188)) (@block_merge rootM 12 284 96 151 rootMb12_284 (@block_merge rootM 12 380 96 55 rootMb12_380 rootMb12_476)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb13_0 : block rootM 13 0 77 = true := rootSpan rootM 13 0 [(9,5),(10,16),(10,8),(11,16),(11,16),(11,16)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb13_77 : block rootM 13 77 21 = true := rootSpan rootM 13 77 [(11,16),(11,5)]
lemma rootMlevel13 : block rootM 13 0 98=true := (@block_merge rootM 13 0 77 21 rootMb13_0 rootMb13_77)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb14_0 : block rootM 14 0 9 = true := rootSpan rootM 14 0 [(10,9)]
lemma rootMlevel14 : block rootM 14 0 9=true := rootMb14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMb15_0 : block rootM 15 0 1 = true := rootSpan rootM 15 0 [(9,1)]
lemma rootMlevel15 : block rootM 15 0 1=true := rootMb15_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rootMGeom : graphValid rootM (boundsBefore known42879)=true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

def rootMActive : Nat → Nat
  | 15 => 1
  | 14 => 9
  | 13 => 98
  | 12 => 531
  | 11 => 506
  | 10 => 72
  | 9 => 1
  | _ => 0
def rootMEdgeData (i : Nat) : Nat := 0x8986a2b38492936472929b044143953140125ab329964b0a69a937a7b6a629b9371a3b866bb30a30a9047a4b894b4ab5539804034a04893a5565ab48b864b2476ba3a8b486b864b534831254b62326143026b934b66b0aa61961a33b48a24b3135a540a93b6ba56b308746b2624b31314312959b07a94b6b96b86156b4316565402416233b96189081553bb6185a842bb3681819b91719a9172979371a65861a7b961a7586629b31629531a53a2ba53b2b906355a23b2849487535a404356734939b1774b6a357b329928b07575429929507b7b389319012486ba3534a0453b834761961148b907009a1531a0476096165a0407059a18793a28795a2b96907978561a36b48929737a1b28646ba7056b630908055a339489ab46b4746720936558726a2378672374672a26a2014ab98b35b10abb686a4b496b4a490b4849556b6404746b256ba407464b5879ba1a5492b90a1552aa628939a0429690768b75a6b970a90835535ab34090a5549467557742953b63442642353b804261431039a5426093153ba34a54a2b8493b2358312978b61a1b79694647565a14014a09065603064ab4068b70a26583130ab044a4b967546297b4b999ab47b754a2998b35b24462309385548698332ab04891b5b7647297868a28746a2658b4014a5906bb40aa36b7884b6a393a475a56b4056583056563029a90735a9044b3ab576b461094655039a0403ba04a56b48359312894b5ba1b486560a30906455b464954b1ab5b7b489765861356b345ab32b57a42996b96126b43057642914a19065813076b971929607b33b1837967231951203ba5476596190a055656b3065a0306561305ab12bb3691826b43165a130929a075aa42b31831226183164ab706585306bb60a36a93456ba30b36a18919b17314612656b400948557b4b8994a475906055658b3098b15ba2692829b90770b8a1a26b28b67b0a919b07b35b18486b8365a54084b6834b4a95754b2998b45b70b9a1565a3035a104539a0490a3551a7b8676b8614b48955a942b249623656530a54b2b3193121a6b8614ab90a1b786261931494a75318612a26a282659316bb70a35a7348796a2091a55426923929b0726b831094a55093a5565a53057b42976b961b4a495a1b68665ab408786a226b9315ab42b31961224b62365ab30b36b1853ba04426b2335ab04
def rootMColorD12 (i : Nat) : Nat := 0xce662d994407c5f89000ae42d0680200c0681212683211011c060613b4190880f85a0d89da0c8440180186c4ed0642202386812276832110060340913b4190880f85a0309da0c84508f0d02410d0642280c0681208683210e2f86e050bac1a00700e7b3d05d60d00382e3d9e82eb06801c1700c0a17583400e01c74240bac1a00440e340299160d00800701814c8b0680110380c0a64583400881c7424322c1a00700e3a1205d60d0038071b8142eb06801c1d8d00a17583400e01c06050bac1a00700e030285d60d002a071d09000b068015038e84800583400a81c7424002c1a0054c6030280160d002a510181400b0680150380c0a00583400a81c0605002c1a00540e030280160d002a070181400b0680150380c0a00583400a9440605002c1a00540e030280160d002a070181400b0680150380c0a00583400a81c0605002c1a00984a501200160d0020071b02c1eb0c20100704c240f5721008038261207ab9080401c130903d5c8402062098481eae420100704c240f57210080389a8e07ab9080401c130903d5c840200e098481eae42002198185a1f43210
def rootMColorD11 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xf43210010040c2d0fa19080080206068290c840043303034148642002008181a0a43210010040c0d0fa19080080206068290c840043303034148642002008181a0a43210150500c561921908008021b138290c840043321034148642002008181a0a43210012102c0d05219080a802166632d0c84054140b328fa864202a0a018320f43210010040c0802219081bc66421687d0c840e08421158648642070421fcac3243210378042c08052190826802061687d0c840040103020088642002008843a044321001005921202219080080216138290c8400401640e014864200200884949043210111b818c7099018318e044030631c088060c6381100c18c7001001b486066004c10c004006d21800a0c4243014001b486002003690c004009721863a085f4c8812db1968502134b2d080de45290368617ba8d9d45eea3f7517ba9b1d05ec82f6417b20bd918b0603834059026c834e4137262311fcc8fe6438a11c48876043b021d810ec0879852ac21e6105b082d843cc20b6105b082d843cc20b610f30879843cc21e6105b082d8416c26b6135b08798586c20b610f28879443ca21e510f2882d4416a20b51049082484124209210490824841242092104908248412420921049082484124209212e108208470424a211690864843a4208211c1089c847042652113908e08470420821614030600d5006a803540079403ca01e504aa8079403ca01e5005a802d4016a00b5005a802d4016a00b5005a802d4016a00b5005a802d4016a00b5005a802d4016a00b5005a80f94128a03e501f280f94128a00c501f280f940d2a00c5006280a540aaa029502aa80a54052a0295006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c5006280314018a00c50062803140d0a00c502aa81554180a03e400ba005d002e8017400ba005d002e8017400ba005d002e800040002005d002e800040002000100568000400ba000100008017400620031000080004000200f5007a803d401ea015500568000400020001000080004000200010000800040002000100568000400020001005680004000200ad0056802b4000200010000802b4000200ad00008000400020001000080004000200010000600030001805cc0006000300018000c0006000301598000c0006000300018000c0006027101c081944070200410498824c400820491020881f4406420921029880c840a62004101e0807c400820041002080104008200410020803c4008203c10270801040a4205410078803c401e200f10240824440082004100f8807c403e201f100f88028403e200a100508028403e200a1019080284014200a1019080c84014207e103f081f8401e204810240812040a620521005081f4401e209010 else 0x8ce0840600e2183414ae420402f96c320f572102017c2608022b908100be13040115c840220e0983414ae420110704c1004572100e038860d0fab9080c01c43068295c841440e219c882ae4201c0710ce4415721008838865c022b9081c4cc4d0c83d5c840200e1a89c08ae4201007134320f5721008038260807ab908040c44d0c83d5c8410ad76b06490ae420100704c100f5721042838264a07ab908044cc13040115c840220e0982008ae420110704c100457210202842608022b9081c41c13279515c84022d50982046ae420300704c1023572102017cb61911ab908100be5b0c88d5c840220e1a83414ae42011070d41a0a57210088386a0d022b9080401c35068115c840800e0982078ac420a25090cb804562100e038865c022b1081001c13040f1188406062268749c8c42002198185a1f43210010042c0802219080080206040110c8400433030200886420020085810044321001005a82d05219080080206068290c84004010b034148642002008581a0a43210010cc0c0d0fa19080080216068290c8400401030b43e8642002198185a1f43210010040c2d0fa19080080206040110c840aed303034148642057008581a0a432102b804b20824a19082800258040110c8414001030b4148642002008189e5443210010040c081e2190827028162b0c90c8405414030641e86420020a0191c0443210010500c1924219081bc28060c8110c84004010d8480886420020086c24044321001004361202219083493e1b0903d0c84004140306408864209a00960103c432104f004b0081e219082780258040f10c841a2011082078864202a00819a05e43210150040c1d27219080a802060e9390c840040103274a886420020a0843a5d4321001050421d2ea190800802214e9510c840040110874088642002008843a044321001050421d24219080080206040110c84004010302078864200200818100443210010040c0802219080080206040110c840040103034148642002008181a1f432102b8042c0d05219080080206040110c84004010d8480886420020081810044321001004361202219080080206040110c840040103048088642002008181acf432104e0502c5619219080a828160c83d0c84054140b1586486420700a058323243210150502c1907a19080a828160c83d0c84054140b0641e864202a0a058320f43210150042c9b29a19080a80216672490c84054010b26ca686420020086c2404432100100496120221908008021b090110c84004010d8480886420020086c2404432100100436120221908008021b090110c84004010d8480886420020086c24044321066804364a2721908008024b090110c84004010d848088642002008241004432100100436120221908008024b250110c8400401030201e86420020092c5a1) else (if i < 3 then 0x472380801c0605002391c1cc0e03188011c8e11818018148c8c24e8c0c06848464612746060060523230938e45e510d02591e49deac7700828e9264ed112ac0401749321ca2dd8eb0dbac192a1162501819d60c8722f0380c36eb06475441308806758321c8fc5c030dbac191d47e2e0d059d60c8722f0386812eb064aa110315214648325422c4a500332b993a914890181991cc9d2882600c0cc8e6439452240642647327422912032caa3190a03044108755ca044018018843aae502200c00c964a572811423c6e210eab9408808e1a048355e88450180d02410af442200c068121257921140603409042bc90995cea61d16695c844e200c00c374ae4227100600606a5721138803003034ab908a08e370b021a0c844047018181ad0642e6538dcb25c683211011c340906b41908a030440d821a0c8450180d02410ce642e5530e8b21957321100604429162ba503907288148b059241c675178a4582c9202823b88522c5748010060442922aba400808ee1148b15d2004018110a458ae900200c088522c57480140604429162ba400a03022148b15d20050183638058ae900280c0894a2c5748010060442922aba400984a5a028011ce004c2528090008e700111d80c0a005a340088ec6805002c9a004476340280160d00223b0181400b0680110380c0a0058340088ec0605002c1a00705c030285d60d0038076f8142eb06801c038d00a00583400881c0605002c1a03780e3702a9160d003807018142eb0680150380c0a00583404281c0605002c1a00400e340280160d0020070181400b0680110380c0a0058340130940631002c1a004498444337560d0022071b81400b0680110380c0aa4583400801c0605002c1a007076341880160d0060070d090e8b0680710380c0a00583400e21c0631002c1a00c00e031880160d00e607018c400b0680301700c62005834013094a024002c1a00705c030280160d002a070181400b0680670380c0a00583400a81c0605002c1a028c0e370280160d002a070181400b06801526110482b583400a81c0605002c1a019c0e030280160d002a4c2221856b0680111d80c0a00583400881c0605002c1a00c00e030280160d00382e01815b8ae6801c0380c0a0057340130940605002b9a0054a23a120011e4c022071d090008f26026129680a004723013094a02400239180984a5a028011c8c04c2528090008e460261280c6200472300a839b6da001ac1000802210e810ca840040110874ba65420020092c940432a10080389a1907a34880400e36058116184020071b02c08b0c2011038d83c3257610078401c3506d230803c20621a836918404c251b078474ea2026128d83c23a75100881c6c1e11a3a88041b2d80403d64840200e268641eb242002008843a233821001050421d119c10800828210e8 else 0x151700c6200472393381c0605002391c8540e03028011c8e546071b814008e472153180c0a00472390a930882415a391c8540e03028011c8e42a4c22218568e472152880c0a00472380818c0605002391c0410e03188011c8e020631b814008e470152880c0a00472380801c0605002391c0409844780ad1c8e0200701814008e470100380c0a))
def rootMColorD10 (i : Nat) : Nat := (if i < 1 then 0x31002b9a00c00e03028015cd00e6070181400ae680100380c6200573403881c342487233980c00e1a121d119cc0383b1a014008e460300380c0a00472301801c060500239180984a0302801188c04c2501814008c46002008585a1f32910010500c191193c0800828060c88c9e0400414030649065020020a018320432810010500c190219408008024b25010ca040141c3304c1108c2039868b8065839410010041212021c9080441c350682960840220e1a83408b04200200818102338210010040c08119c1080a0301a0489d5c840380e2183408ae4210c0704c240496210088386a0d11a31080441c350688d18840220e1a834148c420300704c10238521018038260811c2908028ae015d0364c84014020086c1b2642004010040c0883210010040c08024190800802210e8110c84004011087408864205700ae41a0a4321001004840802219081bc0216040110c84004010302008864200200818100443210010040c0802219080080206040110c84004010302008864200200818100443210010cc0c0d05219080080259040110c8400401108749c864210b008843a5d4321038050841907a190800802580c83d0c84004010d8480886420020092c24044321001004362705219084293e420403d0c84004012102008864200200818100443210010040c19022190800802210e8110c840ed09112d8f00c87251100cf2c7222018314e4d8033431c06806b75970d00e10b0e6c01c1d61e0c141c0b38d83505647111b8f2c6e22371e58dc44033429ba0869045271100d64a4e010040c85d706e5bc3b0008c60176082d8f306d024c00205802004b8832d568b32755aad1664ea2b234045940046300b28008c6016500118c02ca8323400595fefe05ba8bf5f8067214084d2c6e0143a3ec9c1f4f91f3a0088f00c740561e1650606157176041f0b1393882c15e0d710582bc1ae20613488dc40c26911b88184d20471030ab808e20377b85984006ce3457529b8f4dcc0ecf6767aa313c19e8e83f641fb220a8c07062f531fa9826490122809104c8826455b02088179c084d8426c2136105a082484124209210490824849e424f210410820847b40099005c814a40bd20098004c0026001300458022c0116008b002c8016401aa007b003d801ec01ddc1e4e02c7016380b1c0eee045703bb8115c08ae076703b381d9c016a06b500f2802d4016a03e5006280790018800c4034200f9000080174000200010000803d402aa0235011a800040059802cc016600b30059802cc016600b300b981d0c0006000300018000c00060003000180244012200910048813c4000205210488812440922049102488124409220541020881044082205e102f0817840a4200a1005081384082205310078801040a4200410020808c4082200a1005083c44082200a10 else 0x1c8ac514e7b3d001255c8c2262f038da2486b12bc0380c0a8d462373981c0605002311baf05c0302800da49e222f0386976a8d04751f8b834165367255265560200ba4990e47e2e0d0254da4450180d2ec112d042391f8b83409546211c8fc5c1a04a9b10c421e340b0b5a0c84501801ae84ed0642300380c0a004738013094060500231c0008020606828c86000433210b43e64300261280c0a005834008a1c06)
def rootMColorD9 (i : Nat) : Nat := 0x4c25018c400ca4601c1d8d06200452308dc6a330eca98c20dc9970780fb2a2e562728108bb4459955b02bd610b109ae017ac077500018000c012204f10
def rootMCliqueBits (k i : Nat) : Nat × Nat :=
  match k with
  | 12 => if i < 580 then (5,packedAt rootMColorD12 (0+(i-531)*65) 65) else (9,packedAt rootMColorD12 (3185+(i-580)*117) 117)
  | 11 => if i < 845 then (2,packedAt rootMColorD11 (0+(i-506)*17) 17) else if i < 860 then (3,packedAt rootMColorD11 (5763+(i-845)*39) 39) else (5,packedAt rootMColorD11 (6348+(i-860)*65) 65)
  | 10 => if i < 218 then (2,packedAt rootMColorD10 (0+(i-72)*17) 17) else if i < 260 then (3,packedAt rootMColorD10 (2482+(i-218)*39) 39) else if i < 261 then (4,packedAt rootMColorD10 (4120+(i-260)*70) 70) else if i < 341 then (5,packedAt rootMColorD10 (4190+(i-261)*65) 65) else (7,packedAt rootMColorD10 (9390+(i-341)*91) 91)
  | 9 => if i < 13 then (2,packedAt rootMColorD9 (0+(i-1)*17) 17) else if i < 17 then (3,packedAt rootMColorD9 (204+(i-13)*39) 39) else (5,packedAt rootMColorD9 (360+(i-17)*65) 65)
  | _ => (0,0)
def rootMCliqueCheck (k i : Nat) : Bool :=
  let (r,bits) := rootMCliqueBits k i
  let ids := (List.range r).map (fun j => getFieldV bits (j*4) 4)
  let e := if r ≥ 5 then r else r*(r-1)/2
  let codes := (List.range e).map fun j =>
    packedAt rootMEdgeData (24*(getFieldV bits (r*4+j*9) 9)) 24
  if r ≥ 5 then Clique.oddCheck (targetOf rootM) k (stateSet rootM k i) ids codes
  else Clique.check (targetOf rootM) k (stateSet rootM k i) ids codes

theorem rootMCliqueSound {k i} (h : rootMCliqueCheck k i = true) :
    Impossible rootM.mode (targetOf rootM) k (stateSet rootM k i).toFinset := by
  cases e : rootMCliqueBits k i with
  | mk r bits =>
    simp only [rootMCliqueCheck,e] at h
    by_cases large : r ≥ 5
    · simp only [large,ite_true] at h
      exact Clique.oddSound h
    · simp only [large,ite_false] at h
      exact Clique.sound h

def leafSpan (k i n : Nat) : Bool :=
  (List.range n).all (fun j => rootMCliqueCheck k (i+j))

theorem leafSpanAt {k i n} (h : leafSpan k i n = true) {j : Nat} (lo : i ≤ j) (hi : j < i+n) :
    rootMCliqueCheck k j = true := by
  have a := List.all_eq_true.mp h (j-i) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using a

theorem leafSpanMerge {k i a b} (h : leafSpan k i a = true) (t : leafSpan k (i+a) b = true) :
    leafSpan k i (a+b) = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have lt := List.mem_range.mp hj
  by_cases first : j<a
  · exact leafSpanAt h (by omega) (by omega)
  · exact leafSpanAt t (by omega) (by omega)

def leafSpanPieces (k start n : Nat) : Nat → Prop
  | 0 => leafSpan k start n=true
  | d+1 => leafSpanPieces k start (n/2) d ∧ leafSpanPieces k (start+n/2) (n-n/2) d

theorem leafSpanPiecesChecked (k start n depth : Nat)
    (h : leafSpanPieces k start n depth := by
      simp only [leafSpanPieces]
      repeat' apply And.intro
      all_goals decide +kernel) : leafSpan k start n=true := by
  induction depth generalizing start n with
  | zero => exact h
  | succ depth ih =>
    have v := leafSpanMerge (ih start (n/2) h.1) (ih (start+n/2) (n-n/2) h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMCliqueL12 : leafSpan 12 531 50=true := leafSpanPiecesChecked 12 531 50 2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMCliqueL11 : leafSpan 11 506 651=true := leafSpanPiecesChecked 11 506 651 6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMCliqueL10 : leafSpan 10 72 270=true := leafSpanPiecesChecked 10 72 270 5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootMCliqueL9 : leafSpan 9 1 18=true := leafSpanPiecesChecked 9 1 18 1
theorem rootMBranchTables : ∀ k ≤ 15, block rootM k 0 (rootMActive k)=true := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact rootMlevel9
  · exact rootMlevel10
  · exact rootMlevel11
  · exact rootMlevel12
  · exact rootMlevel13
  · exact rootMlevel14
  · exact rootMlevel15
theorem rootMLeafTables : ∀ k ≤ 15, leafSpan k (rootMActive k) ((rootM.levels k).1-rootMActive k)=true := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact rootMCliqueL9
  · exact rootMCliqueL10
  · exact rootMCliqueL11
  · exact rootMCliqueL12
  · rfl
  · rfl
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rootMImpossible : Impossible false graph 15 inputs.toFinset := by
  have leaves (k : Nat) (hk : k ≤ 15) (i : Nat) (lo : rootMActive k ≤ i) (hi : i < (rootM.levels k).1) :
      Impossible rootM.mode (targetOf rootM) k (stateSet rootM k i).toFinset := by
    apply rootMCliqueSound
    exact leafSpanAt (rootMLeafTables k hk) lo (by omega)
  have result := cliqueRoot (g:=rootM) (top:=15) (prior:=boundsBefore known42879) (used:=rootMActive)
    (i:=0) (ws:=inputs) (before_sound known42879 valid42879) rootMGeom rootMBranchTables leaves (by decide +kernel)
  exact (show targetOf rootM = graph by decide +kernel) ▸ result

def rootSActive : Nat → Nat
  | 14 => 1
  | 13 => 3
  | 12 => 30
  | 11 => 151
  | 10 => 57
  | 9 => 4
  | _ => 0
def rootSEdgeData (i : Nat) : Nat := (if i < 1 then 0x805012040e8a65124108b2012a15102802aa0f06a02850d0151b0e8502419031442682600458488c341010808628906413020842c4e148a49c083261110289220255522c9268450a4d46940a08d003a2934130122c26122910400132030d06082420c9151888008111200586a290505454d46d04828d00b361a84424340187436120a0640c369a914893402c52380a014501505836090204c1b07858240b03060682c64340489a07416020a02426562b00c0055016493048a104298acd040018a08522b01000520218b45603028a00d06a2100050421540b008801421144260a24044841b0d402021200c4c2504828480b1309603021240f12a8104011120502101228400a5649a028912425920941100124226915028922821854180808810330b8904817020ca241804408210a8303111820262582441228400a6643a044006508172a902051521709241020208a0132892014112110a25182400aa08512883010550607221201604251c4c20209104242c150080808030682e251404c5b138502023020c920b1118012420950a80904154130d06042220c8a144a28440154045aa84805450950a8301011020642a0c442400898d86a01010d0068ac5a05018a40e2309140c20238707020020604822d150080a28030682c24140485a603804c0441095120c1228410a41a0b190d0123688c241412808689a4b8141013062b15603020a40d169a0a01414154c2504828080b02c1540a0828030d0588a49090350a25112080aa2349a814093402e2b341201628250b05603020a40c4a85410880aa281d04a0128090a230904042021805868a84505054aa4d241400a18848a4490404c902a0d442400a18349a804013400f138502827020c14c26203004c83138502827020d2542a004005501548b048a11429058340802048181a0b8945013060a8345030028e053098209013240b068120509034950a881401540848a4611004c80b04a0285090151c0a40a1414056643a04c04650945aa85009450a544260220044840d0580a090103607412000a02420586820010504506a2140250429361a844243409b0b838141303068b45603028a40c2a16010042803920b01100124204c250080848031d0d80808190304ca24081444859a4540a248a0941a15090280a1a81d04900a809282c1504828280b0d0580808090304ca240010448414c26002004c82830305122024a851288100055001a0b8141013061d0d84828190b05309810881322920b0130112425442602a0444850682c4424048981a15080200a180d02c0a14050544a85400800aa00586a2101054450a25102000aa0351a4120a3402d06a2120150425351a402023400c1a0b010101206a0c0c0440809082a0d040400a180a834141202868341602824240d058682805050542c15008082803 else 0x22b3412016280645e26082404c913493120a0242c0a85a05010a40e8a4d04c048a039209413021200d169a482041411351b4120a3400cd46c1a0c8d03605868a0410504679150289228213c1a48a5434057158502827020c54626002044482164a20400154026d16020922c2184c402009800654622082404491458300881042185868200105044753281028650a14c2604220448a122911408132249ac85009410a42c1a04010240c0d02c021005044702900840501111a89000411210341302020240c13a89000411210341702020240c1b0e85024190b0d46c12088d0265924c0a244109479348082449091d4ca0209114255189880c1112085928a1100550283030914202420d02e0b14054562b16010062803058340800048182c1804814200d0c02c0a14040542a160000428038b45402028200c52380800450114c2500a09400362b542000a28422c12a0b14244545709820901324613804805600942c1a24914240d26954a04802860340b2295014158ad50c0228a1883417120a0242c361a84424340862b3412016282132d16082422c93118402023000c0d0584828090b06cb2408144485a21301301224260d442000a084246a2c442404898743602824440d2542e00400550245032299204252a95a05010a40f10a81241011245522c1228050a4d26a45224d08b990e815021942a131108022021891188830111506446220400454048ac05009400a5502c02a045085c2e0e0504c081988c201011800681c88c84581094cac5400800aa0741b08ac134215309402021200c0a834905002861b0d422121200c2b15402020a00d3496120a0242ca09a4490420c92482d044004908920941300124216098028912025990e815021940d0a25142200aa8540a40880142114423022004484c52a845024548a643a054086508a2994490422c90300d0284010150c0540a08080360642204040541a090)
def rootSColorD11 (i : Nat) : Nat := 0x2b171516094750a180a122c0275832670a171138758321e0a172c0275832180a126802758321e0a121102758321e46122102758321e0a17111975832670a171138758321e0a171138758321e0a121102758321e46122102758321866532c02758321866531102758326564392c0264732180a172c02647211b378b380f683211b378a3645574800832110e0d583402612631607586102612151607586102617151607586102b17151609586102617151607586102b1715160958610448915051a586100817151600586106288150543586102b0c2a140957210080c100600572100842100f20572102b0c2a140957210260c2a1407572100104022423432100104132500432100104020600432108704021452432100103020600432100104132500432100b0302242343210010402242343210158615860a750a750a750443044303430343044304432a721072107213321332023202320561056105610561056136501d500910
def rootSColorD10 (i : Nat) : Nat := (if i < 1 then 0x758321e465b21c175832c06439115e647322837bf5e0f57821be37111f25683217e7d5d13bd673211b3050024e573211b3050297f57321413050bc4e573211b3050297f57321080c10242346180080c1058004618028bb72bab9964707e7db8b7b656470285c3d3645463701b302f4f3b463701b302f7c454637041302f36453526008122c0e0d583400812681c0d583407b32111c0d58340085bb5b40d583400812211c0d583407b32111c0d58340010402060032810085bb31600586106253b2054358610237a0c2a1484610b1395a160947510593263051a47510593215051a47510590cb0af7957210080c77140057210080c10580057210080c10580057210080c10060057210080c10140957210784210060057210080c10140957210080c10060057210080c2aae4357210080c10060057210080c10140957210080c10140957210080c77140057210adacab4c4b562102642764e75462102642764e754621001041f2500432100b401f0f20432100104020600432100b03020f20432100140130f1a4321001031906004321001331f0f1a4321001331f0f7443210014d130f004321001331f0f1a432100104135600432102704020f20432100103132500432100b03020f20432100103190600432100103190600432100103190600432100103190600432100103190600432100103190600432100104020600432100104020600432100104020600432100103192423432100104aa1400432100b030256734321001041f2500432100140130f1a432100b401f0f204321001031906004321001331f0f7443210014d130f004321001331f0f1a4321001031325004321001a9020600432103f3e474c4b432103f3e474c4b432103f3e474c4b432103f3ea824a7432104a3ca65748432104a3c495748432104a3c495748432104a3c492548432100b03025673432100140130f1a432100b030214524321001036d2443432103f3e472423432100b03020f2043210a5a41d6383d6f1d6383da3a263772a1706370a2a71537a09f365370a9e715379d9c705279b6f6e527049a99217989705750966a1c3a182a281a270a95590e390e391c390e390e390e391c3913291829281907090909220922090b0927090b091d481d4855086e3794272e272e272e270a643343939292725432133202326d3219320432913254323c32133254326ca13aa10591056116610561106110610561056190616b61022102213a218f2138213a213b803b8005506a501d5005501d5005501d508e5005401d400d402d402d402d4069402d402d400d408d400d402d402d40054005400d300d303a1007100710231007100010201000100710001000100010001000103a1007100710001000100010001007100710001020108c1000100010071007101a10071007105210 else 0x3df1f005816cef48501291b6bee18464f3b58164090aed5d49185732944eceb04ea473292be9156a09475091b5ce84f3b5740904613d1d8237409e7395a16093640935310e0d221230935310e0d221230935e61c0d22123090b0302140732109010402060032109030214070b321090319060001321097812110ee5472387a12110ee447238e30a1211e253618e10a3211e053618df1c0d22de23018311c0d22352301804612fdd013740803dc2f4f013740803db2f7c013740803612f69013740826395a1607364082bdad9d8093640835311c0d221230835310e0d221230881310ed7d612308d5d40ed3d2123080429511a013210804025160273210803025f070b3210804025fd10b32108030251600132108040251600132108032934090b321084d2934090b3210804293409d03210804cf3409273210803025f070b32108032934090b321084d2934090b32108ce5c2c0ecd4612744cc210e2e36127cb12110e2e361274412210e2e3612780310e0d551230780cac9c85512307c73721c6c535076c4c3210e2e250161e0a17115e647821e0a1221c2)
def rootSColorD9 (i : Nat) : Nat := 0xfefd5dfc8563054fb8486507faf97986518281828652818282818411841181b181b18820827082708280828084108f8082708f7088608f617f507f48585658465058005808350f34005200520f210
def rootSColorD8 (i : Nat) : Nat := 0x8330
def rootSCliqueBits (k i : Nat) : Nat × Nat :=
  match k with
  | 11 => if i < 177 then (2,packedAt rootSColorD11 (0+(i-151)*16) 16) else (5,packedAt rootSColorD11 (416+(i-177)*60) 60)
  | 10 => if i < 183 then (2,packedAt rootSColorD10 (0+(i-57)*16) 16) else if i < 194 then (3,packedAt rootSColorD10 (2016+(i-183)*36) 36) else if i < 342 then (5,packedAt rootSColorD10 (2412+(i-194)*60) 60) else (7,packedAt rootSColorD10 (11292+(i-342)*84) 84)
  | 9 => if i < 35 then (2,packedAt rootSColorD9 (0+(i-4)*16) 16) else if i < 37 then (3,packedAt rootSColorD9 (496+(i-35)*36) 36) else (5,packedAt rootSColorD9 (568+(i-37)*60) 60)
  | 8 => (2,packedAt rootSColorD8 (0+(i-0)*16) 16)
  | _ => (0,0)
def rootSCliqueCheck (k i : Nat) : Bool :=
  let (r,bits) := rootSCliqueBits k i
  let ids := (List.range r).map (fun j => getFieldV bits (j*4) 4)
  let e := if r ≥ 5 then r else r*(r-1)/2
  let codes := (List.range e).map fun j =>
    packedAt rootSEdgeData (54*(getFieldV bits (r*4+j*8) 8)) 54
  if r ≥ 5 then SignedClique.oddCheck (targetOf rootS) k (stateSet rootS k i) ids codes
  else SignedClique.check (targetOf rootS) k (stateSet rootS k i) ids codes

theorem rootSCliqueSound {k i} (h : rootSCliqueCheck k i = true) :
    Impossible rootS.mode (targetOf rootS) k (stateSet rootS k i).toFinset := by
  cases e : rootSCliqueBits k i with
  | mk r bits =>
    simp only [rootSCliqueCheck,e] at h
    by_cases large : r ≥ 5
    · simp only [large,ite_true] at h
      exact SignedClique.oddSound h
    · simp only [large,ite_false] at h
      exact SignedClique.sound h

def signedLeafSpan (k i n : Nat) : Bool :=
  (List.range n).all (fun j => rootSCliqueCheck k (i+j))

theorem signedLeafSpanAt {k i n} (h : signedLeafSpan k i n = true) {j : Nat} (lo : i ≤ j) (hi : j < i+n) :
    rootSCliqueCheck k j = true := by
  have a := List.all_eq_true.mp h (j-i) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using a

theorem signedLeafSpanMerge {k i a b} (h : signedLeafSpan k i a = true) (t : signedLeafSpan k (i+a) b = true) :
    signedLeafSpan k i (a+b) = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have lt := List.mem_range.mp hj
  by_cases first : j<a
  · exact signedLeafSpanAt h (by omega) (by omega)
  · exact signedLeafSpanAt t (by omega) (by omega)

def signedLeafSpanPieces (k start n : Nat) : Nat → Prop
  | 0 => signedLeafSpan k start n=true
  | d+1 => signedLeafSpanPieces k start (n/2) d ∧ signedLeafSpanPieces k (start+n/2) (n-n/2) d

theorem signedLeafSpanPiecesChecked (k start n depth : Nat)
    (h : signedLeafSpanPieces k start n depth := by
      simp only [signedLeafSpanPieces]
      repeat' apply And.intro
      all_goals decide +kernel) : signedLeafSpan k start n=true := by
  induction depth generalizing start n with
  | zero => exact h
  | succ depth ih =>
    have v := signedLeafSpanMerge (ih start (n/2) h.1) (ih (start+n/2) (n-n/2) h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSCliqueL11 : signedLeafSpan 11 151 67=true := signedLeafSpanPiecesChecked 11 151 67 3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSCliqueL10 : signedLeafSpan 10 57 287=true := signedLeafSpanPiecesChecked 10 57 287 5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSCliqueL9 : signedLeafSpan 9 4 34=true := signedLeafSpanPiecesChecked 9 4 34 2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rootSCliqueL8 : signedLeafSpan 8 0 1=true := signedLeafSpanPiecesChecked 8 0 1 0
theorem rootSBranchTables : ∀ k ≤ 14, block rootS k 0 (rootSActive k)=true := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact rootSlevel9
  · exact rootSlevel10
  · exact rootSlevel11
  · exact rootSlevel12
  · exact rootSlevel13
  · exact rootSlevel14
theorem rootSLeafTables : ∀ k ≤ 14, signedLeafSpan k (rootSActive k) ((rootS.levels k).1-rootSActive k)=true := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact rootSCliqueL8
  · exact rootSCliqueL9
  · exact rootSCliqueL10
  · exact rootSCliqueL11
  · rfl
  · rfl
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rootSImpossible : Impossible true graph 14 inputs.toFinset := by
  have leaves (k : Nat) (hk : k ≤ 14) (i : Nat) (lo : rootSActive k ≤ i) (hi : i < (rootS.levels k).1) :
      Impossible rootS.mode (targetOf rootS) k (stateSet rootS k i).toFinset := by
    apply rootSCliqueSound
    exact signedLeafSpanAt (rootSLeafTables k hk) lo (by omega)
  have result := cliqueRoot (g:=rootS) (top:=14) (prior:=boundsBefore known383) (used:=rootSActive)
    (i:=0) (ws:=inputs) (before_sound known383 valid383) rootSGeom rootSBranchTables leaves (by decide +kernel)
  exact (show targetOf rootS = graph by decide +kernel) ▸ result

def orbitWire (i : Fin 9) : Sig := inputs.getD i.val zero

theorem orbitWireMem (a : Sig) : a ∈ inputs ↔ ∃ i : Fin 9, orbitWire i = a := by
  rw [← input_list, List.mem_ofFn]
  rfl

def orbitEssentialRows (i : Fin 9) : Row × Row :=
  ([(3,2),(3,1),(6,2),(12,4),(24,8),(33,1),(66,2),(132,4),(264,8)] :
    List (Row × Row)).getD i.val (0,0)

theorem orbitEssentialChecked : ∀ i : Fin 9,
    witnessB graph inputs (orbitWire i) (orbitEssentialRows i) = true := by decide +kernel

theorem orbitAllInputs {u k s} (run : Live u graph k s) (raw : ∀ a ∈ s, a ∈ inputs) :
    s = inputs.toFinset := by
  ext a
  constructor
  · exact fun ha => List.mem_toFinset.mpr (raw a ha)
  · intro ha
    obtain ⟨i,rfl⟩ := (orbitWireMem a).mp (List.mem_toFinset.mp ha)
    obtain ⟨p,n,diff,isolated⟩ := witnessB_sound (orbitEssentialChecked i)
    exact raw_required run inputs (orbitWire i) raw p n diff isolated

theorem parentFromModes (exM : Impossible false graph 15 inputs.toFinset)
    (exS : Impossible true graph 14 inputs.toFinset)
    (h : ∃ u k S, k ≤ (if u then 14 else 15) ∧ Live u graph k S ∧ ∀ a ∈ S, a ∈ inputs) : False := by
  obtain ⟨u,k,S,hk,hr,sub⟩ := h
  rw [orbitAllInputs hr sub] at hr
  cases u
  · exact exM k hk hr
  · exact exS k hk hr
end PEqualNP.Outside.L_meta_670.Projection

open PEqualNP.Outside.L_meta_670.Projection

theorem PEqualNP.Outside.L_meta_670 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  rintro ⟨C,legal,small,correct⟩
  exact parentFromModes rootMImpossible rootSImpossible (raw_modes C legal (funext correct) small)

