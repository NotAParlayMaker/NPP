import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13441
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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

abbrev Row := Fin 128
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

def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (o : Nat) : ∃ e, e < 4 ∧ ∀ a b, bin o a b = bin e a b := by
  by_cases h : o < 4
  · exact ⟨o,h,fun _ _ => rfl⟩
  · refine ⟨3,by omega,fun a b => ?_⟩
    have h0 : o ≠ 0 := by omega
    have h1 : o ≠ 1 := by omega
    have h2 : o ≠ 2 := by omega
    simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (R : List Nat) (T L : Nat) : Prop := Lower true (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice true (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

structure BaseP (T : Nat) (R : List Nat) : Prop where
  lt : T < 2^128
  plain : plainWord (W T) = true
  nodup : (rootsW R).Nodup
  plainR : (rootsW R).all plainWord = true
  ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a
  prop : proper (W T)

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {T R E K} (hB : baseOK T R E = true) (h : Impossible true (W T) K (rootsW R).toFinset) :
    LowN R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def av (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || Nat.beq x (Nat.xor d m))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available true bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS f bank P)
    (h : av d P v = true) : Available true bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | h⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv rfl e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {f : Row → Row} {roots bank p P} (o a b : Nat) (hr : Reach true roots p bank) (hP : PS f bank P)
    (ha : Available true bank (RF f a)) (hb : Available true bank (RF f b)) :
    ∃ next, Reach true roots (p+1) next ∧ PS f next P ∧ Available true next (RF f (nb o a b)) ∧
      ∀ v, Available true bank v → Available true next v := by
  obtain ⟨e,he,heq⟩ := bin_four o
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) (Or.inr ⟨rfl,he⟩) ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {f : Row → Row} {bank P} (hP : PS f bank P) (i : Nat) : Available true bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach true roots p bank)
    (hP : PS f bank P) : ∃ next, Reach true roots (p+cs.length) next ∧ PS f next (mkPool P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
    have : PS f next (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h2 v hv
      · rw [List.mem_singleton.mp hv]
        exact h3
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av c.1 c.2.2.2) && keepB c.1 c.2.2.2 ka a && keepB c.1 c.2.2.2 kb b &&
  (bif av c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av c.1 c.2.2.2 a && av c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def sepEval (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  let e := fun v => (Nat.testBit v p.1 == Nat.testBit v p.2)
  e z && (!ka || e a) && (!kb || e b) && rest.all e
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && (T.testBit p.1 != T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach true (roots.map observe) c.2.2.1 bank ∧ PS f bank c.2.2.2 ∧
    ∀ p bank, Reach true (roots.map observe) p bank → Available true bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {R T c k rest a b o ka kb} (hc : CutP R T c)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb c = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach true (roots.map observe) q bank' ∧ PS f bank' c.2.2.2 ∧ Available true bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply true bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available true bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem sep_sound {T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval rest a b (nb o a b) ka kb p = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,bne_iff_ne] at hT
  obtain ⟨⟨p1,p2⟩,hd⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  intro k' _ run
  obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W]; exact hd)
  apply hne
  rw [List.mem_toFinset] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [bit_W,bit_W]; exact h1
  rcases mem_kept hv with rfl | hv'
  · cases ka
    · cases kb
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx
      · rcases List.mem_cons.mp hv with e | hv
        · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
        · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
          rw [←e,bit_W,bit_W]; exact h4 x hx
    · rw [bit_W,bit_W]; exact h2.resolve_left (by simp)
  · cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv'
      rw [←e,bit_W,bit_W]; exact h4 x hx
    · rcases List.mem_cons.mp hv' with e | hv
      · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx

abbrev StD := List Nat × List Nat × List Nat × List (List Nat)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool (initPool s.1 s.2.2) c.2)
def hintOK (k : Nat) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 100 then (match cuts[i]? with
    | some c => cutEval k rest a b z ka kb c
    | none => false)
  else (match seps[i-100]? with
    | some q => sepEval rest a b z ka kb q
    | none => false)
def kidOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK k cuts seps rest a b z kk.1 kk.2) ||
  next.any (beqL (kidN rest a b z kk.1 kk.2))
def pairOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  [0,1,2,3].all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK k next cuts seps p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK k next (st.2.1.filterMap fun i => K[i]?) (st.2.2.1.filterMap fun i => P[i]?) st.1) (pairs st.1) st.2.2.2
def levelOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK T K P k next)
def LevelN (R : List Nat) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible true (W T) k (st.1.map W).toFinset
theorem cutsGood {R T} {Z : List SliceD} {C : List (Nat × List (Nat × Nat × Nat))} (hZ : ∀ s ∈ Z, SliceN R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut Z), CutP R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=true) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

theorem stStep {R T E K P k next st} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hn : ∀ s ∈ next, Impossible true (W T) k (s.map W).toFinset)
    (h : stOK T K P k next st = true) : Impossible true (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  have good : ∀ c ∈ st.2.1.filterMap (fun i => K[i]?), CutP R T c := by
    intro c hc
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hc
    exact hK c (List.mem_of_getElem? hi)
  have hs : ∀ q ∈ st.2.2.1.filterMap (fun i => P[i]?), sepOK T q = true := by
    intro q hq
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hq
    exact List.all_eq_true.mp hP q (List.mem_of_getElem? hi)
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have hd4 : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp

  have core : ∀ (o : Nat) (ja jb : Bool), o < 4 → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (by
      have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      simpa using this)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with (hk | hk) | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      cases hb : Nat.blt i 100
      · rw [hb,cond_false] at hi
        cases hg : (st.2.2.1.filterMap (fun i => P[i]?))[i-100]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact sep_sound (hs q (List.mem_of_getElem? hg)) hi
      · rw [hb,cond_true] at hi
        cases hg : (st.2.1.filterMap (fun i => K[i]?))[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (good q (List.mem_of_getElem? hg)) nk hi
    · obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hk
      rw [←kid_fin]
      rw [beqL_ok e]
      exact hn s hs'
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd4 (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have f4 : flipOp d < 4 := by
      rcases hfl.1 with h | ⟨_,h⟩ <;> omega
    have r := core (flipOp d) kb ka f4 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {R T E K P k D' D} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hI : LevelN R T k D') (h : levelOK T K P k (D'.map Prod.fst) D = true) : LevelN R T (k+1) D := by
  intro st hst
  refine stStep hB hK hP ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {T : Nat} {K : List CutV} {P : List (Nat × Nat)} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK T K P k next ((D.drop (i*c)).take c) = true) : levelOK T K P k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {R T E K D} (hB : baseOK T R E = true) (hI : LevelN R T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this

def target (x : Fin 6 → Bool) : Bool := Nat.testBit (3941132800 * 2 ^ 32 + 3939019264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[
    ⟨.and, [2, 5]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [4, 7]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [3, 5]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.and, [2, 12]⟩,
    ⟨.and, [1, 13]⟩,
    ⟨.or, [10, 14]⟩], 15⟩
theorem witnessMonotone : PEqualNP.MetaComplexity.Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.size = 10 := rfl

def v0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def v1 : Nat := 0xcccccccccccccccccccccccccccccccc
def v2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def v3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def v4 : Nat := 0xf0f0f0f000000000f0f0f0f0
def v5 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def v6 : Nat := 0xfcfc0000fcfc0000fcfc0000fcfc0000
def v7 : Nat := 0xfafa0000fafa0000fafa0000fafa
def v8 : Nat := 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8
def v9 : Nat := 0xf0f0f0f000000000f0f0f0f000000000
def v10 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa
def v11 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def v12 : Nat := 0xfafa0000fafa0000fafa0000fafa0000
def v13 : Nat := 0xa0a0a0afafafafa0a0a0a0afafafafa
def v14 : Nat := 0x32323232323232323232323232323232
def v15 : Nat := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0
def v16 : Nat := 0xffffffff00000000ffffffff00000000
def v17 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
def v18 : Nat := 0xffccff00ffccff00ffccff00ffccff00
def v19 : Nat := 0xfcfc0000cccc0000fcfc0000cccc0000
def v20 : Nat := 0xf0fcf0fc00cc00ccf0fcf0fc00cc00cc
def v21 : Nat := 0xf8f8f8f888888888f8f8f8f888888888
def v22 : Nat := 0xfcfcf0f0cccc0000fcfcf0f0cccc0000
def v23 : Nat := 0xfcfcfcfc0c0c0c0cfcfcfcfc0c0c0c0c
def v24 : Nat := 0xc0c8c0c8c0c8c0c8c0c8c0c8c0c8c0c8
def v25 : Nat := 0xc8c8c0c0c8c8c0c0c8c8c0c0c8c8c0c0
def v26 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa00
def v27 : Nat := 0xf0f0ffff00000000f0f0ffff00000000
def v28 : Nat := 0xf5f5f5f500000000f5f5f5f500000000
def v29 : Nat := 0xf8f80000f8f80000f8f80000f8f80000
def v30 : Nat := 0xf8f8f8f800000000f8f8f8f800000000
def v31 : Nat := 0xfcfcfcfc00000000fcfcfcfc00000000
def v32 : Nat := 0xfff0fff000000000fff0fff000000000
def v33 : Nat := 0xc8c8ccccc8c8ccccc8c8ccccc8c8cccc
def v34 : Nat := 0xeaea0000eaea0000eaea0000eaea0000
def v35 : Nat := 0xf0fa0000f0fa0000f0fa0000f0fa0000
def v36 : Nat := 0xfbfb0000fbfb0000fbfb0000fbfb0000
def v37 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0
def v38 : Nat := 0xeaeaaaaaeaeaaaaaeaeaaaaaeaeaaaaa
def v39 : Nat := 0x707070700000000070707070
def v40 : Nat := 0x70707070707070707070707070707070
def v41 : Nat := 0xe0e0e0e000000000e0e0e0e0
def v42 : Nat := 0xeeeeeeee00000000eeeeeeee
def v43 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def v44 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
def v45 : Nat := 0xeeee0000eeee0000eeee0000eeee0000
def v46 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def v47 : Nat := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
def v48 : Nat := 0xf8f8f8f800000000f8f8f8f8
def v49 : Nat := 0xfafafafa00000000fafafafa
def v50 : Nat := 0xfcfcfcfc00000000fcfcfcfc
def v51 : Nat := 0xeeee0000eeee0000eeee0000eeee
def v52 : Nat := 0xeeeeeeee00000000eeeeeeee00000000
def v53 : Nat := 0xf8f80000f8f80000f8f80000f8f8
def v54 : Nat := 0xfafafafafafafafafafafafafafafafa
def v55 : Nat := 0xfafafafa00000000fafafafa00000000
def v56 : Nat := 0xfcfc0000fcfc0000fcfc0000fcfc
def v57 : Nat := 0x500050f0f0f0f000500050f0f0f0f0
def v58 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
def v59 : Nat := 0xff33ff3300000000ff33ff3300000000
def v60 : Nat := 0xffaaffaa00000000ffaaffaa00000000
def v61 : Nat := 0xc000c0f0f0f0f000c000c0f0f0f0f0
def v62 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc
def v63 : Nat := 0xea00ea00ea00ea00ea00ea00ea00ea
def v64 : Nat := 0xee00ee00aa00aa00ee00ee00aa00aa
def v65 : Nat := 0xf000f000f000f000f000f000f000f0
def v66 : Nat := 0xfa00fa00aa00aa00fa00fa00aa00aa
def v67 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe
def v68 : Nat := 0x4040404040404040404040404040404
def v69 : Nat := 0x5050000050500000505000005050000
def v70 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def v71 : Nat := 0xa0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa
def v72 : Nat := 0x50505050505050505050505050505050
def v73 : Nat := 0xc0c00000c0c00000c0c00000c0c0000
def v74 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def v75 : Nat := 0xc0c0c0ccccccccc0c0c0c0ccccccccc
def v76 : Nat := 0xc0c0c0cfcfcfcfc0c0c0c0cfcfcfcfc
def v77 : Nat := 0xc0ccccc0c0ccccc0c0ccccc0c0ccccc
def v78 : Nat := 0xc0e0c0e0c0e0c0e0c0e0c0e0c0e0c0e
def v79 : Nat := 0xe0e0c0c0e0e0c0c0e0e0c0c0e0e0c0c
def v80 : Nat := 0xe0e0e0e0c0c0c0c0e0e0e0e0c0c0c0c
def v81 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00
def v82 : Nat := 0xf1f1f1f100000000f1f1f1f100000000
def v83 : Nat := 0xffffffff0e0e0e0effffffff0e0e0e0e
def v84 : Nat := 0xe0e0e0eeeeeeeee0e0e0e0eeeeeeeee
def v85 : Nat := 0xf0a0f0affaaffaa0f0a0f0affaaffaa
def v86 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
def v87 : Nat := 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e
def v88 : Nat := 0xf0f00000f0f00000f0f00000f0f0000
def v89 : Nat := 0xf3f3f3f300000000f3f3f3f300000000
def v90 : Nat := 0xf0f0000ffff00000f0f0000ffff0000
def v91 : Nat := 0xf0f0f0f000000000f0f0f0f00000000
def v92 : Nat := 0x10101010f0f0f0f010101010f0f0f0f0
def v93 : Nat := 0x22222222222222222222222222222222
def v94 : Nat := 0x2222ffff000000002222ffff00000000
def v95 : Nat := 0x2a2a2a2aaaaaaaaa2a2a2a2aaaaaaaaa
def v96 : Nat := 0x2a2aaaaa2a2aaaaa2a2aaaaa2a2aaaaa
def v97 : Nat := 0x30303030303030303030303030303030
def v98 : Nat := 0x30303030f0f0f0f030303030f0f0f0f0
def v99 : Nat := 0x3030f0f0000000003030f0f000000000
def v100 : Nat := 0x3030ffff000000003030ffff00000000
def v101 : Nat := 0x30323032303230323032303230323032
def v102 : Nat := 0x32323030323230303232303032323030
def v103 : Nat := 0x33323332333233323332333233323332
def v104 : Nat := 0x33330000333300003333000033330000
def v105 : Nat := 0x3333ffff000000003333ffff00000000
def v106 : Nat := 0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c
def v107 : Nat := 0x3f3f00003f3f00003f3f00003f3f0000
def v108 : Nat := 0x3f3fffff000000003f3fffff00000000
def v109 : Nat := 0x40404040404040404040404040404040
def v110 : Nat := 0x44444444444444444444444444444444
def v111 : Nat := 0x4c4c4c4ccccccccc4c4c4c4ccccccccc
def v112 : Nat := 0x50500000505000005050000050500000
def v113 : Nat := 0x50500000f0f0f0f050500000f0f0f0f0
def v114 : Nat := 0xfafafafaaaaaaaaafafafafaaaaaaaaa
def v115 : Nat := 0x50505050f0f0f0f050505050f0f0f0f0
def v116 : Nat := 0x5050f0f05050f0f05050f0f05050f0f0
def v117 : Nat := 0x50705070507050705070507050705070
def v118 : Nat := 0x55545554555455545554555455545554
def v119 : Nat := 0x55775577000000005577557700000000
def v120 : Nat := 0x55f555f50000000055f555f500000000
def v121 : Nat := 0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a
def v122 : Nat := 0x66666666666666666666666666666666
def v123 : Nat := 0x70705050707050507070505070705050
def v124 : Nat := 0x70707070000000007070707000000000
def v125 : Nat := 0x70707070505050507070707050505050
def v126 : Nat := 0x77777777000000007777777700000000
def v127 : Nat := 0xffffffff88888888ffffffff88888888
def v128 : Nat := 0x70707070f0f0f0f070707070f0f0f0f0
def v129 : Nat := 0x7070f0f07070f0f07070f0f07070f0f0
def v130 : Nat := 0x73737373000000007373737300000000
def v131 : Nat := 0x75757575000000007575757500000000
def v132 : Nat := 0x77775555000000007777555500000000
def v133 : Nat := 0x7777ffff000000007777ffff00000000
def v134 : Nat := 0x7f7f7f7f000000007f7f7f7f00000000
def v135 : Nat := 0x80808080f0f0f0f080808080f0f0f0f0
def v136 : Nat := 0x88888888888888888888888888888888
def v137 : Nat := 0x88888888f8f8f8f888888888f8f8f8f8
def v138 : Nat := 0x8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c
def v139 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def v140 : Nat := 0xa0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0
def v141 : Nat := 0xa0a0f0f000000000a0a0f0f000000000
def v142 : Nat := 0xa0a0ffff00000000a0a0ffff00000000
def v143 : Nat := 0xaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa2a
def v144 : Nat := 0xaaa8aaa8aaa8aaa8aaa8aaa8aaa8aaa8
def v145 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000
def v146 : Nat := 0xaaaaffff00000000aaaaffff00000000
def v147 : Nat := 0xff55ff00ff55ff00ff55ff00ff55ff00
def v148 : Nat := 0xacacacacacacacacacacacacacacacac
def v149 : Nat := 0xaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeae
def v150 : Nat := 0xafaf0000afaf0000afaf0000afaf0000
def v151 : Nat := 0xafafaaaaafafaaaaafafaaaaafafaaaa
def v152 : Nat := 0xafafffff00000000afafffff00000000
def v153 : Nat := 0xbbbbffff00000000bbbbffff00000000
def v154 : Nat := 0xc0c00000c0c00000c0c00000c0c00000
def v155 : Nat := 0xc0c00000f0f0f0f0c0c00000f0f0f0f0
def v156 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
def v157 : Nat := 0xfcfcfcfcccccccccfcfcfcfccccccccc
def v158 : Nat := 0xffccffccffccffccffccffccffccffcc
def v159 : Nat := 0xc0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0
def v160 : Nat := 0xc0c0ccccc0c0ccccc0c0ccccc0c0cccc
def v161 : Nat := 0xc0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0
def v162 : Nat := 0xc0e0c0e0c0e0c0e0c0e0c0e0c0e0c0e0
def v163 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def v164 : Nat := 0xc8c8c8c8ccccccccc8c8c8c8cccccccc
def v165 : Nat := 0xcacacacacacacacacacacacacacacaca
def v166 : Nat := 0xccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8
def v167 : Nat := 0xccee0000ccee0000ccee0000ccee0000
def v168 : Nat := 0xcceeccee00000000cceeccee00000000
def v169 : Nat := 0xccfc0000ccfc0000ccfc0000ccfc0000
def v170 : Nat := 0xccfcccfc00000000ccfcccfc00000000
def v171 : Nat := 0xd0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0
def v172 : Nat := 0xe0e0c0c0e0e0c0c0e0e0c0c0e0e0c0c0
def v173 : Nat := 0xe0e0e0e000000000e0e0e0e000000000
def v174 : Nat := 0xe0e0e0e0c0c0c0c0e0e0e0e0c0c0c0c0
def v175 : Nat := 0xe0e0e0e0f0f0f0f0e0e0e0e0f0f0f0f0
def v176 : Nat := 0xe0e0f0f0e0e0f0f0e0e0f0f0e0e0f0f0
def v177 : Nat := 0xeaeaeaea00000000eaeaeaea00000000
def v178 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def v179 : Nat := 0xecec0000ecec0000ecec0000ecec0000
def v180 : Nat := 0xecececec00000000ecececec00000000
def v181 : Nat := 0xeeee0000cccc0000eeee0000cccc0000
def v182 : Nat := 0xeeee0000ffff0000eeee0000ffff0000
def v183 : Nat := 0xeeeecccc00000000eeeecccc00000000
def v184 : Nat := 0xeeeeeeee0e0e0e0eeeeeeeee0e0e0e0e
def v185 : Nat := 0xeeeeffff00000000eeeeffff00000000
def v186 : Nat := 0xefef0000efef0000efef0000efef0000
def v187 : Nat := 0xefefefef00000000efefefef00000000
def v188 : Nat := 0xf030f03000000000f030f03000000000
def v189 : Nat := 0xf050f050f050f050f050f050f050f050
def v190 : Nat := 0xf070f070f070f070f070f070f070f070
def v191 : Nat := 0xf0a0f0a000000000f0a0f0a000000000
def v192 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0
def v193 : Nat := 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0
def v194 : Nat := 0xfff0ff00ff00ff00fff0ff00ff00ff00
def v195 : Nat := 0xf0faf0faf0faf0faf0faf0faf0faf0fa
def v196 : Nat := 0xf2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2
def v197 : Nat := 0xf3f30000f3f30000f3f30000f3f30000
def v198 : Nat := 0xf3f3f0f0f3f3f0f0f3f3f0f0f3f3f0f0
def v199 : Nat := 0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0
def v200 : Nat := 0xfafaaaaafafaaaaafafaaaaafafaaaaa
def v201 : Nat := 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0
def v202 : Nat := 0xfafafafaf0f0f0f0fafafafaf0f0f0f0
def v203 : Nat := 0xf0f3f0f300000000f0f3f0f300000000
def v204 : Nat := 0xf0f5f0f500000000f0f5f0f500000000
def v205 : Nat := 0xf0faf0fa00000000f0faf0fa00000000
def v206 : Nat := 0xf0fc0000f0fc0000f0fc0000f0fc0000
def v207 : Nat := 0xf0fcf0fc00000000f0fcf0fc00000000
def v208 : Nat := 0xf2f2f2f200000000f2f2f2f200000000
def v209 : Nat := 0xf3f3f0f000000000f3f3f0f000000000
def v210 : Nat := 0xf3f3ffff00000000f3f3ffff00000000
def v211 : Nat := 0xf4f4f4f400000000f4f4f4f400000000
def v212 : Nat := 0xf5f5555500000000f5f5555500000000
def v213 : Nat := 0xf5f5f0f000000000f5f5f0f000000000
def v214 : Nat := 0xf5f5f0f055550000f5f5f0f055550000
def v215 : Nat := 0xf5f5ffff00000000f5f5ffff00000000
def v216 : Nat := 0xf7f7f7f700000000f7f7f7f700000000
def v217 : Nat := 0xfafa0000ffff0000fafa0000ffff0000
def v218 : Nat := 0xfafaf0f000000000fafaf0f000000000
def v219 : Nat := 0xfafafafa0a0a0a0afafafafa0a0a0a0a
def v220 : Nat := 0xfafaffff00000000fafaffff00000000
def v221 : Nat := 0xfbfbfbfb00000000fbfbfbfb00000000
def v222 : Nat := 0xfcfc0000ffff0000fcfc0000ffff0000
def v223 : Nat := 0xfcfccccc00000000fcfccccc00000000
def v224 : Nat := 0xfcfcf0f000000000fcfcf0f000000000
def v225 : Nat := 0xfcfcffff00000000fcfcffff00000000
def v226 : Nat := 0xfdfd0000fdfd0000fdfd0000fdfd0000
def v227 : Nat := 0xfdfdfdfd00000000fdfdfdfd00000000
def v228 : Nat := 0xfefe0000fefe0000fefe0000fefe0000
def v229 : Nat := 0xfefefefe00000000fefefefe00000000
def v230 : Nat := 0xff22ff2200000000ff22ff2200000000
def v231 : Nat := 0xff30ff3000000000ff30ff3000000000
def v232 : Nat := 0xff3fff3f00000000ff3fff3f00000000
def v233 : Nat := 0xff77ff7700000000ff77ff7700000000
def v234 : Nat := 0xffa0ffa000000000ffa0ffa000000000
def v235 : Nat := 0xffafffaf00000000ffafffaf00000000
def v236 : Nat := 0xffbbffbb00000000ffbbffbb00000000
def v237 : Nat := 0xffee0000ffee0000ffee0000ffee0000
def v238 : Nat := 0xffeeffee00000000ffeeffee00000000
def v239 : Nat := 0xfff3fff300000000fff3fff300000000
def v240 : Nat := 0xfff5fff500000000fff5fff500000000
def v241 : Nat := 0xfffa0000fffa0000fffa0000fffa0000
def v242 : Nat := 0xfffafffa00000000fffafffa00000000
def v243 : Nat := 0xfffc0000fffc0000fffc0000fffc0000
def v244 : Nat := 0xfffcfffc00000000fffcfffc00000000
def v245 : Nat := 0xff04ff04ff04ff04ff04ff04ff04ff04
def v246 : Nat := 0xff05ff00ff05ff00ff05ff00ff05ff00
def v247 : Nat := 0xff05ff05ff00ff00ff05ff05ff00ff00
def v248 : Nat := 0xff0cff00ff0cff00ff0cff00ff0cff00
def v249 : Nat := 0xff10ff10ff10ff10ff10ff10ff10ff10
def v250 : Nat := 0xff11ff00ff11ff00ff11ff00ff11ff00
def v251 : Nat := 0xff11ff11ff00ff00ff11ff11ff00ff00
def v252 : Nat := 0xff44ff00ff44ff00ff44ff00ff44ff00
def v253 : Nat := 0xff50ff00ff50ff00ff50ff00ff50ff00
def v254 : Nat := 0xff88ff00ff88ff00ff88ff00ff88ff00
def v255 : Nat := 0xffc0ff00ffc0ff00ffc0ff00ffc0ff00
def v256 : Nat := 0xffddff00ffddff00ffddff00ffddff00
def v257 : Nat := 0xf0f8f0f8f0f8f0f8f0f8f0f8f0f8f0f8
def v258 : Nat := 0xf1f1f0f0f1f1f0f0f1f1f0f0f1f1f0f0
def v259 : Nat := 0xf1f1f1f1f0f0f0f0f1f1f1f1f0f0f0f0
def v260 : Nat := 0xf8f8f0f0f8f8f0f0f8f8f0f0f8f8f0f0
def v261 : Nat := 0xf8f8f8f8f0f0f0f0f8f8f8f8f0f0f0f0
def v262 : Nat := 0xf8f8f8f8fafafafaf8f8f8f8fafafafa
def v263 : Nat := 0xf8f8fafaf8f8fafaf8f8fafaf8f8fafa
def v264 : Nat := 0xfaf8faf8faf8faf8faf8faf8faf8faf8
def v265 : Nat := 0xcdcdcccccdcdcccccdcdcccccdcdcccc
def v266 : Nat := 0xcdcdcdcdcccccccccdcdcdcdcccccccc
def v267 : Nat := 0xececececccccccccececececcccccccc
def v268 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def v269 : Nat := 0xaaeaaaeaaaeaaaeaaaeaaaeaaaeaaaea
def v270 : Nat := 0xeaeaeaeaaaaaaaaaeaeaeaeaaaaaaaaa
def v271 : Nat := 0xa000a000a000a000a000a000a000a
def v272 : Nat := 0xc000c000c000c000c000c000c000c
def v273 : Nat := 0x220022002200220022002200220022
def v274 : Nat := 0x300030003000300030003000300030
def v275 : Nat := 0x440044004400440044004400440044
def v276 : Nat := 0x500050005000500050005000500050
def v277 : Nat := 0x880088008800880088008800880088
def v278 : Nat := 0xa000a000a000a000a000a000a000a0
def v279 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def v280 : Nat := 0xc000c000c000c000c000c000c000c0
def v281 : Nat := 0xf000f00000000000f000f000000000
def v282 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc
def v283 : Nat := 0x2020202020202020202020202020202
def v284 : Nat := 0x3030000030300000303000003030000
def v285 : Nat := 0x3030303000000000303030300000000
def v286 : Nat := 0x5050505000000000505050500000000
def v287 : Nat := 0x8080808080808080808080808080808
def v288 : Nat := 0xa0a00000a0a00000a0a00000a0a0000
def v289 : Nat := 0xa0a0a0a000000000a0a0a0a00000000
def v290 : Nat := 0xffffffff0a0a0a0affffffff0a0a0a0a
def v291 : Nat := 0xa0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa
def v292 : Nat := 0xc0c0c0c000000000c0c0c0c00000000
def v293 : Nat := 0xffffffff0c0c0c0cffffffff0c0c0c0c
def v294 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
def v295 : Nat := 0x10101010101010101010101010101010
def v296 : Nat := 0x11110000111100001111000011110000
def v297 : Nat := 0x11111111000000001111111100000000
def v298 : Nat := 0x20202020202020202020202020202020
def v299 : Nat := 0x22220000222200002222000022220000
def v300 : Nat := 0x22222222000000002222222200000000
def v301 : Nat := 0x22222222aaaaaaaa22222222aaaaaaaa
def v302 : Nat := 0x2222aaaa2222aaaa2222aaaa2222aaaa
def v303 : Nat := 0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a
def v304 : Nat := 0x30300000303000003030000030300000
def v305 : Nat := 0x30303030000000003030303000000000
def v306 : Nat := 0x3030f0f03030f0f03030f0f03030f0f0
def v307 : Nat := 0x33223322332233223322332233223322
def v308 : Nat := 0x33303330333033303330333033303330
def v309 : Nat := 0x33333333000000003333333300000000
def v310 : Nat := 0x55555555000000005555555500000000
def v311 : Nat := 0xcccccccc00000000cccccccc00000000
def v312 : Nat := 0x3f3f3f3f000000003f3f3f3f00000000
def v313 : Nat := 0x44440000444400004444000044440000
def v314 : Nat := 0x44444444000000004444444400000000
def v315 : Nat := 0x44444444cccccccc44444444cccccccc
def v316 : Nat := 0x4444cccc4444cccc4444cccc4444cccc
def v317 : Nat := 0x4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c
def v318 : Nat := 0x50505050000000005050505000000000
def v319 : Nat := 0x54545454545454545454545454545454
def v320 : Nat := 0x55445544554455445544554455445544
def v321 : Nat := 0x55505550555055505550555055505550
def v322 : Nat := 0x55550000555500005555000055550000
def v323 : Nat := 0xaaaaaaaa00000000aaaaaaaa00000000
def v324 : Nat := 0x5f5f00005f5f00005f5f00005f5f0000
def v325 : Nat := 0x5f5f5f5f000000005f5f5f5f00000000
def v326 : Nat := 0x77770000777700007777000077770000
def v327 : Nat := 0x80808080808080808080808080808080
def v328 : Nat := 0x88880000888800008888000088880000
def v329 : Nat := 0x88888888000000008888888800000000
def v330 : Nat := 0x88888888aaaaaaaa88888888aaaaaaaa
def v331 : Nat := 0x88888888cccccccc88888888cccccccc
def v332 : Nat := 0x8888aaaa8888aaaa8888aaaa8888aaaa
def v333 : Nat := 0x8888cccc8888cccc8888cccc8888cccc
def v334 : Nat := 0x8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a
def v335 : Nat := 0xa0a00000a0a00000a0a00000a0a00000
def v336 : Nat := 0xa0a0a0a000000000a0a0a0a000000000
def v337 : Nat := 0xa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaa
def v338 : Nat := 0xa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaa
def v339 : Nat := 0xa0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0
def v340 : Nat := 0xa2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2
def v341 : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def v342 : Nat := 0xaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0a
def v343 : Nat := 0xaa22aa22aa22aa22aa22aa22aa22aa22
def v344 : Nat := 0xaa88aa88aa88aa88aa88aa88aa88aa88
def v345 : Nat := 0xaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaee
def v346 : Nat := 0xaafaaafaaafaaafaaafaaafaaafaaafa
def v347 : Nat := 0xafafafaf00000000afafafaf00000000
def v348 : Nat := 0xafafafafaaaaaaaaafafafafaaaaaaaa
def v349 : Nat := 0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0
def v350 : Nat := 0xbabababababababababababababababa
def v351 : Nat := 0xbbbb0000bbbb0000bbbb0000bbbb0000
def v352 : Nat := 0xbbbbaaaabbbbaaaabbbbaaaabbbbaaaa
def v353 : Nat := 0xbbbbbbbb00000000bbbbbbbb00000000
def v354 : Nat := 0xbbbbbbbbaaaaaaaabbbbbbbbaaaaaaaa
def v355 : Nat := 0xc0c0c0c000000000c0c0c0c000000000
def v356 : Nat := 0xc0c0c0c0ccccccccc0c0c0c0cccccccc
def v357 : Nat := 0xc4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4
def v358 : Nat := 0xcc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0c
def v359 : Nat := 0xcc44cc44cc44cc44cc44cc44cc44cc44
def v360 : Nat := 0xcc88cc88cc88cc88cc88cc88cc88cc88
def v361 : Nat := 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0
def v362 : Nat := 0xcceecceecceecceecceecceecceeccee
def v363 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfc
def v364 : Nat := 0xcececececececececececececececece
def v365 : Nat := 0xcfcf0000cfcf0000cfcf0000cfcf0000
def v366 : Nat := 0xcfcfcccccfcfcccccfcfcccccfcfcccc
def v367 : Nat := 0xcfcfcfcf00000000cfcfcfcf00000000
def v368 : Nat := 0xcfcfcfcfcccccccccfcfcfcfcccccccc
def v369 : Nat := 0xdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdc
def v370 : Nat := 0xdddd0000dddd0000dddd0000dddd0000
def v371 : Nat := 0xddddccccddddccccddddccccddddcccc
def v372 : Nat := 0xdddddddd00000000dddddddd00000000
def v373 : Nat := 0xddddddddccccccccddddddddcccccccc
def v374 : Nat := 0xecececececececececececececececec
def v375 : Nat := 0xeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaa
def v376 : Nat := 0xeeeecccceeeecccceeeecccceeeecccc
def v377 : Nat := 0xeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaa
def v378 : Nat := 0xeeeeeeeecccccccceeeeeeeecccccccc
def v379 : Nat := 0xf030f030f030f030f030f030f030f030
def v380 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0
def v381 : Nat := 0xf0f0000000000000f0f0000000000000
def v382 : Nat := 0xfff0fff0ff00ff00fff0fff0ff00ff00
def v383 : Nat := 0xf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fc
def v384 : Nat := 0xf4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4
def v385 : Nat := 0xf5f50000f5f50000f5f50000f5f50000
def v386 : Nat := 0xf5f5f0f0f5f5f0f0f5f5f0f0f5f5f0f0
def v387 : Nat := 0xf5f5f5f5f0f0f0f0f5f5f5f5f0f0f0f0
def v388 : Nat := 0xfcfcccccfcfcccccfcfcccccfcfccccc
def v389 : Nat := 0xfcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0
def v390 : Nat := 0xfcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0
def v391 : Nat := 0xfefefefefefefefefefefefefefefefe
def v392 : Nat := 0xff0aff0aff0aff0aff0aff0aff0aff0a
def v393 : Nat := 0xff0cff0cff0cff0cff0cff0cff0cff0c
def v394 : Nat := 0xff22ff22ff22ff22ff22ff22ff22ff22
def v395 : Nat := 0xff30ff30ff30ff30ff30ff30ff30ff30
def v396 : Nat := 0xff44ff44ff44ff44ff44ff44ff44ff44
def v397 : Nat := 0xff50ff50ff50ff50ff50ff50ff50ff50
def v398 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88
def v399 : Nat := 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0
def v400 : Nat := 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0
def v401 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffee
def v402 : Nat := 0xfffafffafffafffafffafffafffafffa
def v403 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffc

def u0_T : Nat := 0x88888888888888888888888888888888
def u0_R : List Nat := [0, 1]
def u0_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem u0_B : baseOK u0_T u0_R u0_E = true := by decide +kernel
theorem u0_L : LowN u0_R u0_T 1 := lowCount u0_B (by decide +kernel)

def u1_T : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def u1_R : List Nat := [0, 1]
def u1_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem u1_B : baseOK u1_T u1_R u1_E = true := by decide +kernel
theorem u1_L : LowN u1_R u1_T 1 := lowCount u1_B (by decide +kernel)

def u2_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def u2_R : List Nat := [0, 1, 2]
def u2_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem u2_B : baseOK u2_T u2_R u2_E = true := by decide +kernel
theorem u2_S0 : SliceN u2_R u2_T (0x33333333333333333333333333333333,1,[0, 2]) := mkSlice (w:=0) u2_B u0_B u0_L (by decide +kernel)
theorem u2_S1 : SliceN u2_R u2_T (0x55555555555555555555555555555555,1,[1, 2]) := mkSlice (w:=0) u2_B u0_B u0_L (by decide +kernel)
theorem u2_S2 : SliceN u2_R u2_T (0xcccccccccccccccccccccccccccccccc,1,[0, 2]) := mkSlice (w:=2) u2_B u1_B u1_L (by decide +kernel)
theorem u2_S3 : SliceN u2_R u2_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]) := mkSlice (w:=1) u2_B u1_B u1_L (by decide +kernel)
theorem u2_S4 : SliceN u2_R u2_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]) := mkSlice (w:=0) u2_B u0_B u0_L (by decide +kernel)
theorem u2_S5 : SliceN u2_R u2_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1]) := mkSlice (w:=4) u2_B u1_B u1_L (by decide +kernel)
def u2_Z : List SliceD := [(0x33333333333333333333333333333333,1,[0, 2]),(0x55555555555555555555555555555555,1,[1, 2]),(0xcccccccccccccccccccccccccccccccc,1,[0, 2]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1])]
theorem u2_Y : ∀ s ∈ u2_Z, SliceN u2_R u2_T s := by
  unfold u2_Z
  simp only [List.forall_mem_cons]
  exact ⟨u2_S0,u2_S1,u2_S2,u2_S3,u2_S4,u2_S5,by simp⟩
def u2_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def u2_P : List (Nat × Nat) := [(4,5),(1,3),(0,3),(2,3),(2,6),(1,5)]
def u2_K : List CutV := u2_C.map (mkCut u2_Z)
theorem u2_W : ∀ c ∈ u2_K, CutP u2_R u2_T c := cutsGood u2_Y (by decide +kernel)
theorem u2_Q : u2_P.all (sepOK u2_T) = true := by decide +kernel
noncomputable def u2_D3 : List StD := [
([v0,v1,v2],[0,1,2,3,4,5],[0,1,2,3,4,5],[[0,1,100,2,3,101,102],[4,1,103,5,3,100],[4,0,101,5,2,104,105]])]
def u2_D2 : List StD := []
theorem u2_I2 : LevelN u2_R u2_T 2 u2_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u2_C3x0 : levelOK u2_T u2_K u2_P 2 (u2_D2.map Prod.fst) ((u2_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem u2_I3 : LevelN u2_R u2_T 3 u2_D3 := levelStep u2_B u2_W u2_Q u2_I2 (chunks 16 u2_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u2_C3x0
  ))
theorem u2_L : LowN u2_R u2_T 4 := lowSearch u2_B u2_I3 (by decide +kernel)

def u3_T : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
def u3_R : List Nat := [0, 1, 2, 3]
def u3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14)]
theorem u3_B : baseOK u3_T u3_R u3_E = true := by decide +kernel
theorem u3_S0 : SliceN u3_R u3_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) u3_B u2_B u2_L (by decide +kernel)
def u3_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2])]
theorem u3_Y : ∀ s ∈ u3_Z, SliceN u3_R u3_T s := by
  unfold u3_Z
  simp only [List.forall_mem_cons]
  exact ⟨u3_S0,by simp⟩
def u3_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def u3_P : List (Nat × Nat) := []
def u3_K : List CutV := u3_C.map (mkCut u3_Z)
theorem u3_W : ∀ c ∈ u3_K, CutP u3_R u3_T c := cutsGood u3_Y (by decide +kernel)
theorem u3_Q : u3_P.all (sepOK u3_T) = true := by decide +kernel
noncomputable def u3_D4 : List StD := [
([v0,v1,v2,v3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def u3_D3 : List StD := []
theorem u3_I3 : LevelN u3_R u3_T 3 u3_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u3_C4x0 : levelOK u3_T u3_K u3_P 3 (u3_D3.map Prod.fst) ((u3_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem u3_I4 : LevelN u3_R u3_T 4 u3_D4 := levelStep u3_B u3_W u3_Q u3_I3 (chunks 16 u3_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u3_C4x0
  ))
theorem u3_L : LowN u3_R u3_T 5 := lowSearch u3_B u3_I4 (by decide +kernel)

def u4_T : Nat := 0xa880a880a880a880a880a880a880a880
def u4_R : List Nat := [0, 1, 2, 3]
def u4_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem u4_B : baseOK u4_T u4_R u4_E = true := by decide +kernel
theorem u4_S0 : SliceN u4_R u4_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3]) := mkSlice (w:=1) u4_B u2_B u2_L (by decide +kernel)
def u4_Z : List SliceD := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3])]
theorem u4_Y : ∀ s ∈ u4_Z, SliceN u4_R u4_T s := by
  unfold u4_Z
  simp only [List.forall_mem_cons]
  exact ⟨u4_S0,by simp⟩
def u4_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def u4_P : List (Nat × Nat) := []
def u4_K : List CutV := u4_C.map (mkCut u4_Z)
theorem u4_W : ∀ c ∈ u4_K, CutP u4_R u4_T c := cutsGood u4_Y (by decide +kernel)
theorem u4_Q : u4_P.all (sepOK u4_T) = true := by decide +kernel
noncomputable def u4_D4 : List StD := [
([v0,v1,v2,v3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def u4_D3 : List StD := []
theorem u4_I3 : LevelN u4_R u4_T 3 u4_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u4_C4x0 : levelOK u4_T u4_K u4_P 3 (u4_D3.map Prod.fst) ((u4_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem u4_I4 : LevelN u4_R u4_T 4 u4_D4 := levelStep u4_B u4_W u4_Q u4_I3 (chunks 16 u4_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u4_C4x0
  ))
theorem u4_L : LowN u4_R u4_T 5 := lowSearch u4_B u4_I4 (by decide +kernel)

def u5_T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8
def u5_R : List Nat := [0, 1, 2, 3]
def u5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem u5_B : baseOK u5_T u5_R u5_E = true := by decide +kernel
theorem u5_S0 : SliceN u5_R u5_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) u5_B u2_B u2_L (by decide +kernel)
def u5_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2])]
theorem u5_Y : ∀ s ∈ u5_Z, SliceN u5_R u5_T s := by
  unfold u5_Z
  simp only [List.forall_mem_cons]
  exact ⟨u5_S0,by simp⟩
def u5_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def u5_P : List (Nat × Nat) := []
def u5_K : List CutV := u5_C.map (mkCut u5_Z)
theorem u5_W : ∀ c ∈ u5_K, CutP u5_R u5_T c := cutsGood u5_Y (by decide +kernel)
theorem u5_Q : u5_P.all (sepOK u5_T) = true := by decide +kernel
noncomputable def u5_D4 : List StD := [
([v0,v1,v2,v3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def u5_D3 : List StD := []
theorem u5_I3 : LevelN u5_R u5_T 3 u5_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem u5_C4x0 : levelOK u5_T u5_K u5_P 3 (u5_D3.map Prod.fst) ((u5_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem u5_I4 : LevelN u5_R u5_T 4 u5_D4 := levelStep u5_B u5_W u5_Q u5_I3 (chunks 16 u5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact u5_C4x0
  ))
theorem u5_L : LowN u5_R u5_T 5 := lowSearch u5_B u5_I4 (by decide +kernel)

def ptopT : Nat := 0xeae8ea00eac8aa00eae8ea00eac8aa00
def ptopR : List Nat := [0,1,2,3,4,5]
def ptopE : List (Nat × Nat × Nat) := [(0,8,9),(1,17,19),(2,18,22),(3,1,9),(4,3,19),(5,14,46)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
theorem ptopS0 : SliceN ptopR ptopT (0xff000000ff000000ff000000ff0000,5,[1,2,0,5]) := mkSlice (w:=16) ptopB u3_B u3_L (by decide +kernel)
theorem ptopS1 : SliceN ptopR ptopT (0xff00ff0000000000ff00ff00000000,5,[4,2,1,0]) := mkSlice (w:=32) ptopB u4_B u4_L (by decide +kernel)
theorem ptopS2 : SliceN ptopR ptopT (0xffff000000000000ffff000000000000,5,[0,2,1,3]) := mkSlice (w:=48) ptopB u5_B u5_L (by decide +kernel)
def ptopZ : List SliceD := [(0xff000000ff000000ff000000ff0000,5,[1,2,0,5]),(0xff00ff0000000000ff00ff00000000,5,[4,2,1,0]),(0xffff000000000000ffff000000000000,5,[0,2,1,3])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopY : ∀ s ∈ ptopZ, SliceN ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨ptopS0,ptopS1,ptopS2,by simp⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def ptopC : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(0,[(0,1,3)]),(0,[(0,2,3)]),(0,[(1,0,3)]),(0,[(2,1,3)]),(0,[(2,2,3)]),(0,[(3,0,3)]),(1,[]),(2,[]),(2,[(1,2,3)]),(2,[(2,0,3)])]
def ptopP : List (Nat × Nat) := [(9,0),(9,1),(9,2),(9,3),(9,4),(9,5),(9,7),(9,8),(9,10),(9,12),(9,14),(9,16),(9,17),(9,18),(9,21),(9,24),(9,26),(9,28),(9,32),(9,33),(9,35),(9,36),(9,37),(9,39),(9,40),(9,42),(9,44),(11,0),(11,1),(11,2),(11,3),(11,5),(11,6),(11,7),(11,8),(11,10),(11,12),(11,14),(11,16),(11,24),(11,26),(11,32),(11,35),(11,37),(11,39),(11,40),(11,42),(11,44),(13,0),(13,1),(13,3),(13,4),(13,5),(13,7),(13,8),(13,10),(13,12),(13,14),(13,17),(13,21),(13,24),(13,28),(13,36),(13,37),(13,40),(13,44),(15,1),(15,3),(15,5),(15,6),(15,7),(15,8),(15,10),(15,12),(15,14),(15,37),(15,39),(15,44),(19,0),(19,1),(19,2),(19,3),(19,5),(19,6),(19,7),(19,8),(19,10),(19,16),(19,17),(19,18),(19,20),(19,21),(19,24),(19,26),(19,33),(19,34),(19,35),(19,36),(19,37),(19,38),(19,39),(19,48),(19,49),(19,50),(19,52),(22,0),(22,2),(22,3),(22,4),(22,6),(22,8),(22,10),(22,12),(22,14),(22,16),(22,17),(22,18),(22,20),(22,21),(22,24),(22,26),(22,28),(22,32),(22,34),(22,36),(22,38),(22,48),(22,50),(22,52),(22,58),(22,60),(23,3),(23,5),(23,7),(23,17),(23,18),(23,21),(23,38),(23,39),(25,0),(25,1),(25,8),(25,16),(25,17),(25,20),(25,21),(25,24),(25,28),(25,49),(25,56),(25,60),(27,18),(29,1),(29,5),(29,8),(29,12),(29,17),(29,20),(29,21),(29,24),(29,28),(29,60),(30,2),(30,4),(30,6),(30,10),(30,12),(30,14),(30,16),(30,18),(30,20),(30,24),(30,26),(30,28),(30,34),(30,48),(30,50),(30,52),(30,58),(30,60),(41,0),(41,1),(41,3),(41,5),(41,8),(41,10),(41,12),(41,32),(41,33),(41,37),(41,40),(41,44),(43,0),(43,3),(43,8),(43,10),(43,14),(43,34),(43,35),(43,40),(43,42),(45,0),(45,1),(45,3),(45,4),(45,5),(45,7),(45,8),(45,10),(45,12),(45,14),(45,33),(45,36),(45,37),(45,40),(45,44),(46,0),(46,2),(46,3),(46,4),(46,6),(46,7),(46,8),(46,10),(46,12),(46,14),(46,26),(46,28),(46,32),(46,34),(46,35),(46,36),(46,38),(46,40),(46,42),(46,44),(46,58),(46,60),(51,3),(51,17),(51,21),(51,33),(51,35),(51,39),(51,49),(53,1),(53,5),(53,17),(53,20),(53,21),(53,33),(53,35),(53,37),(53,39),(53,48),(53,49),(53,52),(54,2),(54,18),(54,38),(54,52)]
def ptopK : List CutV := ptopC.map (mkCut ptopZ)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopW : ∀ c ∈ ptopK, CutP ptopR ptopT c := cutsGood ptopY (by decide +kernel)
theorem ptopQ : ptopP.all (sepOK ptopT) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD3 : List StD := []
theorem ptopI3 : LevelN ptopR ptopT 3 ptopD3 := by intro s h; cases h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD4 : List StD := [
([v4,v0,v5,v6,v3],[],[0,1,5,7,9,16,23,49,54,57,59,68,73,78,79,82,89,91,100,108,109,116,117],[[103,104,108],[117,121,122],[114,115,120],[101,102,107],[103,109,112],[103,105,113],[100,101,116],[114,118,119],[101,106,111],[101,110,114]]),
([v7,v0,v8,v9,v3],[],[1,3,4,7,9,10,12,22,26,28,36,79,81,83,88,100,128,202,209,224,225,232,235],[[103,104,113],[111,112,122],[112,115,120],[100,106,112],[104,105,110],[104,108,118],[100,102,121],[114,116,119],[100,101,109],[100,107,117]]),
([v10,v0,v8,v9,v11],[],[0,1,3,10,11,12,22,26,27,28,79,81,83,88,100,128,201,202,216,225,232,235],[[100,101,120],[101,102,109],[101,106,117],[101,105,111],[100,103,108],[100,107,116],[100,104,112],[113,115,118],[110,111,121],[111,114,119]]),
([v10,v0,v1,v9,v12],[],[0,1,2,3,12,17,22,26,27,28,79,81,83,88,100,128,201,202,216,217,232,235],[[100,101,120],[101,103,109],[101,106,117],[101,104,111],[100,102,108],[100,107,116],[100,105,112],[113,115,118],[110,111,121],[111,114,119]]),
([v13,v0,v8,v3,v11],[],[1,3,4,7,9,10,12,17,22,28,36,79,81,83,88,100,114,202,207,222,225,232],[[103,104,118],[114,116,119],[100,108,117],[112,115,120],[104,105,110],[100,102,121],[104,107,113],[100,101,109],[111,112,119],[100,106,112]]),
([v14,v0,v9,v12,v3],[],[1,3,4,7,9,12,17,22,26,28,34,78,79,81,88,100,128,202,209,222,224,232,235],[[103,104,110],[114,116,120],[112,113,122],[100,101,109],[104,108,118],[104,106,111],[100,102,121],[113,115,119],[100,107,117],[100,105,113]]),
([v15,v8,v3,v11,v16],[],[0,5,6,7,10,14,15,22,24,31,34,78,81,87,96,101,183,184,222,225,230,233],[[103,104,110],[100,101,120],[103,106,112],[103,108,117],[101,102,109],[111,112,121],[113,115,118],[101,105,112],[101,107,116],[112,114,119]]),
([v0,v5,v17,v18,v16],[],[0,1,6,7,10,14,17,19,24,66,71,109,110,113,121,130,181,184,222,225,232,233,249],[[103,104,110],[103,106,113],[100,101,120],[103,108,117],[112,113,121],[101,102,109],[114,115,118],[101,105,111],[113,119,122],[101,107,116]]),
([v0,v5,v9,v19,v3],[],[0,1,6,7,10,16,22,26,66,71,78,79,84,89,98,105,113,116,128,202,207,222,225],[[103,104,109],[103,107,120],[103,105,110],[100,101,113],[117,118,121],[111,112,115],[101,102,108],[111,114,122],[101,106,119],[101,111,116]]),
([v0,v5,v9,v18,v11],[],[0,1,6,7,10,12,13,22,26,66,71,79,85,110,113,116,130,202,207,222,225,232,235,247],[[103,104,110],[103,108,118],[100,101,121],[103,106,112],[115,116,119],[101,102,109],[113,114,122],[101,107,117],[114,120,123],[101,105,111]]),
([v0,v5,v20,v3,v11],[],[0,1,3,7,10,12,15,26,66,71,79,80,81,84,87,88,89,106,114,116,130,167],[[103,104,109],[103,107,114],[100,101,116],[103,106,111],[115,118,119],[101,108,120],[112,113,117],[101,102,115],[110,112,121],[101,105,112]]),
([v0,v5,v21,v3,v11],[],[0,1,3,7,10,12,15,26,28,33,34,67,77,79,81,84,88,97,104,105,109,114,128],[[103,104,112],[103,107,110],[100,101,118],[103,106,117],[116,121,122],[101,109,111],[114,115,119],[101,102,108],[113,114,120],[101,105,114]]),
([v0,v5,v19,v3,v16],[],[0,1,6,7,10,16,19,24,66,71,78,79,84,89,94,105,113,116,127,181,184,222,225],[[103,104,109],[103,105,110],[100,101,113],[103,107,120],[111,112,115],[101,102,108],[117,118,121],[101,111,116],[111,114,122],[101,106,119]]),
([v0,v5,v22,v3,v11],[],[0,1,6,7,10,12,15,22,26,66,71,79,87,88,89,98,100,114,116,124,225],[[103,104,110],[103,108,112],[100,101,114],[103,106,114],[113,117,118],[101,102,109],[115,116,119],[101,107,113],[111,113,120],[101,105,115]]),
([v0,v5,v23,v3,v11],[],[0,1,3,6,7,8,10,12,15,28,34,66,71,79,80,81,88,89,100,105,109,114,116],[[104,106,112],[104,105,110],[100,101,117],[104,108,114],[116,121,122],[101,103,111],[115,118,119],[101,102,109],[113,115,120],[101,107,115]]),
([v0,v24,v9,v3,v11],[],[0,1,3,7,10,12,15,22,26,66,71,79,81,83,88,100,128,202,207,222,225,232,235],[[103,104,110],[103,108,118],[100,101,121],[103,106,113],[114,116,119],[101,102,109],[111,112,122],[101,107,117],[112,115,120],[101,105,112]]),
([v0,v25,v9,v3,v11],[],[0,1,6,7,10,12,15,22,26,66,71,79,83,84,88,100,128,202,207,222,225,232,235],[[103,104,110],[103,108,118],[100,101,121],[103,106,112],[114,116,119],[101,102,109],[111,113,122],[101,107,117],[113,115,120],[101,105,113]]),
([v0,v8,v9,v26,v11],[],[0,1,3,9,10,12,17,22,26,28,36,79,81,83,88,100,128,202,209,224,225,232,235],[[103,104,110],[103,108,118],[100,101,121],[103,106,113],[114,116,119],[101,102,109],[111,112,122],[101,107,117],[112,115,120],[101,105,112]]),
([v0,v8,v9,v12,v3],[],[0,1,3,7,10,12,17,22,26,28,34,79,81,83,88,100,128,202,207,222,225,232,235],[[103,104,110],[103,108,118],[103,106,113],[100,101,121],[114,116,119],[111,112,122],[101,102,109],[112,115,120],[101,107,117],[101,105,112]]),
([v0,v8,v9,v3,v11],[],[0,1,3,7,10,12,15,22,26,28,34,79,81,83,88,100,128,202,207,222,225,232,235],[[103,104,110],[103,108,118],[100,101,121],[103,106,113],[114,116,119],[101,102,109],[111,112,122],[101,107,117],[112,115,120],[101,105,112]]),
([v0,v8,v27,v3,v11],[],[0,1,3,7,10,12,15,19,24,28,34,79,81,83,88,96,128,181,184,222,225,230,233],[[103,104,110],[103,108,118],[100,101,121],[103,106,113],[114,116,119],[101,102,109],[111,112,122],[101,107,117],[112,115,120],[101,105,112]]),
([v0,v8,v28,v3,v11],[],[0,1,3,7,10,12,15,22,24,28,34,79,81,83,88,100,126,202,207,222,225,232,233],[[103,104,110],[103,108,118],[100,101,121],[103,106,113],[114,116,119],[101,102,109],[111,112,122],[101,107,117],[112,115,120],[101,105,112]]),
([v0,v8,v29,v3,v16],[],[0,1,3,7,10,14,17,19,24,28,34,79,81,83,91,96,128,181,184,222,225,230,233],[[103,104,110],[103,106,113],[100,101,121],[103,108,118],[111,112,122],[101,102,109],[114,116,119],[101,105,112],[112,115,120],[101,107,117]]),
([v0,v8,v30,v3,v11],[],[0,1,3,7,10,12,15,22,26,28,34,79,81,83,88,96,128,193,196,222,225,230,235],[[103,104,110],[103,108,118],[100,101,121],[103,106,113],[114,116,119],[101,102,109],[111,112,122],[101,107,117],[112,115,120],[101,105,112]]),
([v0,v8,v6,v3,v16],[],[0,1,3,7,10,14,16,19,24,28,34,79,81,83,91,96,127,181,184,222,225,230,233],[[103,104,110],[103,106,113],[100,101,121],[103,108,118],[111,112,122],[101,102,109],[114,116,119],[101,105,112],[112,115,120],[101,107,117]]),
([v0,v8,v31,v3,v11],[],[0,1,3,7,10,12,15,22,25,28,34,79,81,83,88,96,127,193,196,222,225,230,234],[[103,104,110],[103,108,118],[100,101,121],[103,106,113],[114,116,119],[101,102,109],[111,112,122],[101,107,117],[112,115,120],[101,105,112]]),
([v0,v8,v3,v32,v11],[],[0,1,3,7,10,12,15,22,24,28,34,79,81,83,88,100,128,181,184,222,225,232,233],[[103,104,110],[100,101,121],[103,108,118],[103,106,113],[101,102,109],[114,116,119],[111,112,122],[101,107,117],[101,105,112],[112,115,120]]),
([v0,v33,v9,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,34,79,80,81,88,100,128,202,207,222,223,232,235],[[103,104,110],[103,108,118],[100,101,121],[103,106,112],[114,116,119],[101,102,109],[111,113,122],[101,107,117],[113,115,120],[101,105,113]]),
([v0,v1,v34,v9,v3],[],[0,1,3,7,8,12,22,26,28,34,79,80,81,88,100,202,207,222,223,232,235],[[103,104,109],[103,111,112],[103,107,116],[100,101,119],[110,112,120],[113,117,118],[101,102,108],[112,114,118],[101,105,112],[101,106,115]]),
([v0,v1,v17,v9,v18],[],[0,1,3,7,8,14,17,22,26,28,34,106,110,111,121,130,202,207,222,223,232,235,249],[[103,104,110],[103,106,113],[103,108,117],[100,101,120],[112,113,121],[114,115,118],[101,102,109],[113,119,122],[101,105,111],[101,107,116]]),
([v0,v1,v9,v35,v3],[],[0,1,3,7,8,12,17,22,26,28,34,79,80,81,88,100,128,202,207,222,223,232,235],[[103,104,110],[103,108,118],[103,106,112],[100,101,121],[114,116,119],[111,113,122],[101,102,109],[113,115,120],[101,107,117],[101,105,113]]),
([v0,v1,v9,v29,v3],[],[0,1,3,7,8,14,17,22,26,28,34,79,80,81,91,100,128,202,207,222,223,232,235],[[103,104,110],[103,108,118],[103,106,112],[100,101,121],[114,116,119],[111,113,122],[101,102,109],[113,115,120],[101,107,117],[101,105,113]]),
([v0,v1,v9,v26,v12],[],[0,1,3,9,10,12,17,22,26,28,36,79,80,81,88,100,128,202,209,224,225,232,235],[[103,104,110],[103,108,118],[100,101,121],[103,106,112],[114,116,119],[101,102,109],[111,113,122],[101,107,117],[113,115,120],[101,105,113]]),
([v0,v1,v9,v12,v3],[],[0,1,3,7,8,12,17,22,26,28,34,79,80,81,88,100,128,202,207,222,223,232,235],[[103,104,110],[103,108,118],[103,106,112],[100,101,121],[114,116,119],[111,113,122],[101,102,109],[113,115,120],[101,107,117],[101,105,113]]),
([v0,v1,v9,v36,v3],[],[0,1,3,7,8,12,15,22,26,28,34,79,80,81,88,100,128,202,207,222,223,232,235],[[103,104,110],[103,108,118],[103,106,112],[100,101,121],[114,116,119],[111,113,122],[101,102,109],[113,115,120],[101,107,117],[101,105,113]]),
([v0,v1,v29,v30,v3],[],[0,1,3,7,8,14,17,22,26,28,34,79,80,81,91,96,128,193,195,222,223,230,235],[[103,104,110],[103,106,112],[103,108,118],[100,101,121],[111,113,122],[114,116,119],[101,102,109],[113,115,120],[101,105,113],[101,107,117]]),
([v0,v37,v18,v11,v16],[],[0,1,5,7,10,12,13,19,24,49,54,79,85,110,113,116,118,127,181,184,222,225,233,249],[[103,104,110],[100,101,116],[103,106,112],[103,108,119],[101,102,109],[113,114,122],[115,117,120],[101,105,111],[101,107,118],[114,121,123]]),
([v1,v38,v9,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,34,79,80,81,88,89,100,202,207,222,223,235],[[103,104,110],[114,119,120],[101,102,109],[111,113,121],[103,108,118],[100,101,115],[103,106,112],[101,107,117],[113,116,120],[101,105,113]])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC4x0 : levelOK ptopT ptopK ptopP 3 (ptopD3.map Prod.fst) ((ptopD4.drop (0*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC4x1 : levelOK ptopT ptopK ptopP 3 (ptopD3.map Prod.fst) ((ptopD4.drop (1*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC4x2 : levelOK ptopT ptopK ptopP 3 (ptopD3.map Prod.fst) ((ptopD4.drop (2*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC4x3 : levelOK ptopT ptopK ptopP 3 (ptopD3.map Prod.fst) ((ptopD4.drop (3*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC4x4 : levelOK ptopT ptopK ptopP 3 (ptopD3.map Prod.fst) ((ptopD4.drop (4*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC4x5 : levelOK ptopT ptopK ptopP 3 (ptopD3.map Prod.fst) ((ptopD4.drop (5*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC4x6 : levelOK ptopT ptopK ptopP 3 (ptopD3.map Prod.fst) ((ptopD4.drop (6*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC4x7 : levelOK ptopT ptopK ptopP 3 (ptopD3.map Prod.fst) ((ptopD4.drop (7*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC4x8 : levelOK ptopT ptopK ptopP 3 (ptopD3.map Prod.fst) ((ptopD4.drop (8*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC4x9 : levelOK ptopT ptopK ptopP 3 (ptopD3.map Prod.fst) ((ptopD4.drop (9*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopI4 : LevelN ptopR ptopT 4 ptopD4 := levelStep ptopB ptopW ptopQ ptopI3 (chunks 4 ptopD4 10 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC4x0
  · exact ptopC4x1
  · exact ptopC4x2
  · exact ptopC4x3
  · exact ptopC4x4
  · exact ptopC4x5
  · exact ptopC4x6
  · exact ptopC4x7
  · exact ptopC4x8
  · exact ptopC4x9
  ))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD5 : List StD := [
([v39,v40,v0,v1,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,34,52,56,79,80,81,88,89,109,116,117,235],[[119],[103,112],[116,120],[101,111],[115,118],[103,108,112],[116,120],[101,107,111],[115,118],[103,104,110],[100,101,117],[103,106,114],[101,102,109],[113,115,121],[101,105,115]]),
([v41,v0,v1,v37,v3,v11],[],[0,1,3,7,8,12,15,22,28,34,52,74,79,80,81,88,89,100,109,116,136,252],[[103,111],[115,120],[119],[101,110],[114,118],[103,104,109],[103,111],[100,101,116],[103,106,113],[115,120],[101,102,108],[112,114,121],[101,107,110],[114,117,118],[101,105,114]]),
([v42,v43,v0,v1,v2,v11],[],[0,1,3,5,8,12,19,28,29,35,37,40,49,72,79,80,81,84,88,89,91,96,102,106,116,127,134,180,181,219,223,225],[[101,106,128],[100,109,127],[118,122,129],[124,125,130],[116,121,131],[101,108,119],[101,102,107],[101,103,112],[101,105,116],[104,109,118],[109,110,113],[109,111,115],[118,120,126],[114,116,129],[116,117,123]]),
([v42,v44,v0,v1,v3,v11],[],[1,3,5,8,12,19,28,29,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,116,127,134,181,195,222,223,225],[[124,125,130],[108,111,128],[118,122,129],[100,105,127],[116,121,131],[108,109,113],[118,120,126],[100,102,112],[116,117,123],[103,108,118],[100,107,119],[108,110,115],[100,101,106],[114,116,129],[100,104,116]]),
([v42,v0,v1,v37,v3,v11],[],[1,3,5,7,8,12,19,28,29,35,37,40,49,72,79,80,81,84,88,89,91,96,102,106,116,127,134,181,184,223,225,239,252],[[103,109,128],[118,122,131],[124,125,129],[100,106,127],[116,121,130],[104,109,118],[109,110,113],[100,108,119],[109,111,115],[118,120,126],[100,101,107],[114,116,132],[100,102,112],[116,117,123],[100,105,116]]),
([v42,v0,v1,v45,v2,v3],[],[1,3,5,7,8,12,19,28,29,35,37,40,49,72,79,80,81,84,88,89,91,96,102,106,116,127,134,181,184,223,224,225],[[103,109,128],[118,122,130],[116,121,131],[124,125,129],[100,106,127],[104,109,118],[109,111,115],[109,110,113],[100,108,119],[114,116,130],[118,120,126],[100,101,107],[116,117,123],[100,105,116],[100,102,112]]),
([v4,v43,v0,v1,v2,v11],[],[0,1,3,8,11,12,21,22,27,28,51,52,79,80,81,88,89,100,109,116,136,231],[[101,111],[100,110],[115,120],[119],[114,118],[100,101,116],[101,102,109],[101,107,111],[101,105,114],[100,103,108],[100,106,110],[100,104,113],[115,120],[112,114,121],[114,117,118]]),
([v4,v10,v0,v1,v2,v11],[],[0,1,2,3,11,12,22,26,27,28,52,56,79,81,88,89,100,109,117,169,235],[[101,110],[100,111],[114,118],[119],[113,117],[100,101,115],[101,103,109],[101,106,110],[101,105,113],[100,102,108],[100,107,111],[100,104,117],[114,118],[112,113,120],[113,116,117]]),
([v4,v44,v0,v1,v3,v11],[],[1,3,7,8,12,22,28,29,35,40,52,54,56,79,80,81,88,89,100,109,114,116,117,222],[[121],[108,111,112],[116,120,122],[100,110],[115,119],[102,108,112],[116,122],[100,105,110],[115,118,119],[103,108,112],[100,107,117],[108,109,114],[100,101,106],[113,115,123],[100,104,115]]),
([v4,v14,v0,v2,v3,v11],[],[1,3,7,12,22,26,27,28,34,39,52,56,78,79,81,87,88,100,109,114,117,235],[[116,120],[108,111],[119],[100,110],[114,118],[102,108,111],[116,120],[100,101,107],[113,114,121],[105,108,111],[100,106,115],[108,109,112],[100,104,110],[114,117,118],[100,103,114]]),
([v4,v40,v0,v1,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,33,34,52,56,79,80,81,84,88,89,109,116,117,223,225,235],[[121,123,124],[103,113],[118,122],[101,110,112],[116,117,120],[103,108,113],[118,122],[101,107,112],[116,120],[103,104,111],[100,101,119],[103,106,115],[101,102,109],[114,116,125],[101,105,116]]),
([v4,v0,v5,v46,v3,v11],[],[0,1,3,7,8,12,15,28,31,34,36,44,50,55,57,68,73,79,80,81,82,89,91,100,108,109,116,117,222],[[103,110,113],[122,126,127],[],[101,108,112],[119,120,125],[103,114,116],[103,104,109],[100,101,121],[103,106,118],[128],[101,111,115],[119,123,124],[101,102,107],[117,119],[101,105,119]]),
([v4,v0,v8,v2,v3,v11],[],[0,1,3,7,12,15,22,26,28,34,52,56,57,79,81,88,100,109,117,232,235],[[103,111],[115,118],[],[101,110],[114,117],[103,109,112],[103,107,111],[100,101,119],[103,105,117],[115,118],[101,102,108],[113,114,120],[101,106,110],[114,116,117],[101,104,114]]),
([v4,v0,v1,v37,v3,v11],[],[0,1,3,7,8,9,12,15,22,28,34,52,56,74,79,80,81,88,89,100,109,116,117,136,223,225,252],[[103,105,113],[117,123],[121,124,125],[101,111],[116,120],[103,104,110],[103,112,113],[100,101,118],[103,107,115],[117,122,123],[101,102,109],[114,116,126],[101,108,111],[116,119,120],[101,106,116]]),
([v4,v0,v1,v45,v2,v3],[],[0,1,3,7,8,12,22,26,28,34,40,52,56,79,80,81,88,89,100,109,116,136,235],[[103,112],[116,121],[115,119],[120],[101,111],[103,104,109],[103,110,114],[103,107,112],[100,101,117],[113,115,122],[116,121],[101,102,108],[115,118,119],[101,105,115],[101,106,111]]),
([v4,v0,v1,v2,v12,v3],[],[0,1,3,7,8,12,22,26,28,34,52,56,61,79,80,81,88,100,109,117,232,235],[[103,111],[116,119],[],[115,118],[101,110],[103,104,109],[103,107,111],[103,112,114],[100,101,120],[116,119],[113,115,121],[101,102,108],[115,117,118],[101,106,110],[101,105,115]]),
([v4,v0,v1,v2,v6,v3],[],[0,1,3,7,8,22,26,28,34,40,52,56,59,79,80,81,89,100,109,116,117,128,222,224,235],[[103,111],[120,121,123],[119],[115,118],[101,110],[103,104,108],[103,106,111],[103,109,114],[100,101,116],[120,122],[113,115,124],[101,102,107],[115,117,118],[101,105,110],[101,112,115]]),
([v4,v0,v1,v47,v3,v11],[],[0,1,7,8,12,15,22,26,30,33,35,37,47,52,56,81,84,88,91,98,99,109,116,117,128,218,223,235,245,247],[[102,111,114],[118,123,124],[122],[101,109,113],[115,116,121],[102,103,112],[102,107,110],[100,101,125],[102,105,120],[117,123,129],[101,108],[115,119,127],[101,106,108],[115,126,128],[101,104,115]]),
([v48,v0,v1,v47,v3,v11],[],[0,1,7,8,12,15,22,26,30,36,37,81,82,83,91,96,116,128,222,223,224,225,230,235,245,247],[[102,110],[114,117,120],[116],[101,108],[111,115,121],[102,103,109],[102,107,110],[100,101,122],[102,105,113],[114,118,125],[101,108],[111,112,123],[101,106,108],[111,119,124],[101,104,111]]),
([v49,v10,v0,v1,v2,v11],[],[0,1,3,5,9,12,19,28,49,51,56,57,61,73,79,81,84,88,91,96,102,109,117,169,180,181,217,224,225,232,235],[[101,106,125],[100,110,124],[117,120,127],[123,126,128],[115,119,128],[101,109,129],[101,102,107],[101,103,108],[101,105,115],[110,111,113],[104,110,124],[110,112,121],[117,118,122],[114,115,130],[115,116,121]]),
([v49,v14,v0,v2,v3,v11],[],[1,3,5,9,12,19,28,34,49,51,56,57,61,73,79,81,84,88,91,96,102,109,114,117,181,194,222,224,225,232,235],[[117,120,127],[107,110,125],[122,126,128],[100,105,124],[115,119,128],[110,111,113],[117,118,123],[100,101,106],[114,115,130],[103,110,125],[100,109,129],[110,112,121],[100,102,108],[115,116,121],[100,104,115]]),
([v49,v0,v8,v2,v3,v11],[],[1,3,5,7,9,12,19,28,49,51,56,57,61,73,79,81,84,88,91,96,102,109,117,181,184,224,225,232,235,247],[[103,110,124],[117,120,125],[126,129],[100,106,123],[115,119,126],[110,111,113],[104,110,124],[100,109,127],[110,112,121],[117,118,122],[100,101,107],[114,115,128],[100,102,108],[115,116,121],[100,105,115]]),
([v49,v0,v1,v2,v12,v3],[],[1,3,5,7,9,12,19,28,49,51,56,57,61,73,79,81,84,88,91,96,102,109,117,181,184,223,224,225,232,235],[[103,110,124],[117,120,126],[125,127],[115,119,127],[100,106,123],[110,111,113],[104,110,124],[110,112,121],[100,109,128],[117,118,122],[114,115,129],[100,101,107],[115,116,121],[100,102,108],[100,105,115]]),
([v50,v0,v1,v2,v6,v3],[],[0,1,7,20,22,25,26,30,35,40,52,56,59,80,81,84,89,91,96,106,108,116,117,127,128,223,224,225,235],[[102,108],[122,124,126],[121,123,125],[114,118,127],[101,107],[102,105,108],[102,106,111],[102,109,113],[100,101,116],[117,121,122],[114,120,128],[101,103,107],[114,115,119],[101,104,110],[101,112,114]]),
([v51,v43,v0,v1,v2,v16],[],[0,1,3,5,8,12,19,28,29,35,37,46,49,72,79,80,81,84,88,89,91,96,102,106,116,127,134,181,195,223,225,231,239],[[101,105,116],[100,109,115],[114,116,131],[116,117,123],[116,121,130],[101,108,119],[101,102,107],[101,103,112],[101,106,127],[104,109,118],[109,110,113],[109,111,128],[118,120,126],[118,122,132],[124,125,129]]),
([v51,v44,v0,v1,v3,v16],[],[1,3,5,8,12,19,28,29,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,105,106,116,127,181,195,223,225,233,239],[[116,117,124],[108,110,115],[114,116,131],[100,104,116],[116,121,130],[108,109,113],[118,120,123],[100,102,112],[125,126,129],[103,108,118],[100,107,119],[108,111,128],[100,101,106],[118,122,132],[100,105,127]]),
([v51,v0,v1,v37,v3,v16],[],[1,3,5,7,8,12,19,28,29,35,37,46,49,72,78,79,80,81,84,88,89,91,96,102,105,106,116,127,181,195,223,225,239,252],[[103,109,116],[115,117,133],[117,118,125],[100,105,117],[117,122,131],[104,109,114],[109,110,113],[100,108,120],[109,111,129],[119,121,124],[100,101,107],[119,123,132],[100,102,112],[126,127,130],[100,106,128]]),
([v51,v0,v1,v52,v2,v3],[],[1,3,5,7,8,12,19,28,29,35,37,46,49,72,78,79,80,81,84,88,89,91,96,102,105,106,116,127,181,195,223,225,239,252],[[103,109,116],[115,117,133],[117,122,131],[117,118,125],[100,105,117],[104,109,114],[109,111,129],[109,110,113],[100,108,120],[119,123,132],[119,121,124],[100,101,107],[126,127,130],[100,106,128],[100,102,112]]),
([v53,v0,v1,v47,v3,v16],[],[0,1,7,8,14,17,19,24,30,36,37,79,81,82,91,96,106,123,128,181,184,224,225,230,234,235,245,250],[[102,110],[112,113,125],[124],[101,108],[112,115,122],[102,103,109],[102,105,110],[100,101,123],[102,107,120],[111,114,127],[101,108],[114,118,121],[101,104,108],[116,117,126],[101,106,119]]),
([v7,v10,v0,v1,v2,v16],[],[0,1,3,5,9,12,19,28,49,51,56,57,65,73,79,80,81,84,88,91,96,102,109,117,139,162,174,181,209,224,225,235,247],[[101,105,116],[100,110,122],[114,116,131],[116,117,122],[116,120,130],[101,109,115],[101,102,107],[101,103,108],[101,106,127],[110,111,113],[104,110,124],[110,112,128],[118,119,123],[118,121,129],[125,126,132]]),
([v7,v14,v0,v2,v3,v16],[],[1,3,5,9,12,19,28,34,49,51,56,57,65,73,78,79,81,84,88,91,96,102,105,109,117,122,181,209,224,225,235,247],[[115,116,130],[107,110,114],[116,117,123],[100,104,116],[116,120,129],[110,111,113],[118,119,124],[100,101,106],[118,121,128],[103,110,114],[100,109,114],[110,112,127],[100,102,108],[122,125,131],[100,105,126]]),
([v7,v0,v8,v2,v3,v16],[],[1,3,5,7,9,12,19,28,49,51,56,57,65,73,79,81,84,88,91,96,102,105,109,141,181,209,224,225,232,235,247],[[103,110,122],[114,115,129],[115,116,122],[100,105,115],[115,119,127],[110,111,113],[104,110,123],[100,109,128],[110,112,125],[117,118,121],[100,101,107],[117,120,126],[100,102,108],[127,130],[100,106,124]]),
([v7,v0,v1,v9,v54,v3],[],[1,3,4,9,10,12,17,22,26,28,36,79,80,81,83,88,100,105,106,128,162,202,209,224,225,232,235,257],[[103,106,114],[111,113,126],[113,116,124],[],[100,105,113],[103,104,110],[103,108,122],[112],[100,102,125],[115,119,123],[115,117],[100,101,109],[127],[100,107,121],[100,118,120]]),
([v7,v0,v1,v2,v55,v3],[],[1,3,5,7,9,12,19,28,49,51,56,57,65,73,79,80,81,84,88,91,96,102,105,106,109,181,209,224,225,235,247],[[103,110,115],[114,116,129],[116,117,124],[116,120,128],[100,105,116],[110,111,113],[104,110,115],[110,112,126],[100,109,115],[118,119,122],[118,121,127],[100,101,107],[123,128,130],[100,102,108],[100,106,125]]),
([v56,v0,v1,v2,v31,v3],[],[0,1,7,14,16,17,30,35,42,46,52,56,79,81,84,89,91,96,105,106,116,127,128,193,195,223,224,225,235],[[102,107],[112,113,128],[113,114,119],[113,117,127],[101,106],[102,104,107],[102,105,111],[102,109,124],[100,101,115],[112,116,118],[112,122,126],[101,106],[120,121,125],[101,103,110],[101,108,123]]),
([v57,v0,v1,v2,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,34,52,56,79,80,81,88,89,100,109,116,117,235],[[103,112],[116,121],[120],[101,111],[115,119],[103,104,110],[103,108,112],[100,101,117],[103,106,114],[116,121],[101,102,109],[113,115,122],[101,107,111],[115,118,119],[101,105,115]]),
([v58,v0,v1,v2,v59,v11],[],[0,1,2,3,4,5,11,12,18,19,27,28,48,49,79,81,84,88,89,91,102,106,109,114,116,129,180,181,217,219,220,231,249],[[118],[101,103,111],[101,105,113],[101,109,127],[101,107,115],[100,102,110],[100,104,112],[100,108,126],[100,106,122],[117,119,123],[117,120,129],[114,115,131],[124,125,128],[115,116,121],[115,130,132]]),
([v58,v0,v1,v2,v60,v11],[],[0,1,2,3,4,5,11,12,19,24,27,28,48,49,79,81,84,88,89,91,96,102,106,109,114,116,129,180,181,217,219,220,235],[[118],[101,103,111],[101,105,113],[101,108,128],[101,107,115],[100,102,110],[100,104,112],[100,109,127],[100,106,123],[117,119,124],[117,121,130],[114,115,132],[125,126,129],[115,116,122],[115,120,131]]),
([v61,v0,v1,v2,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,34,52,56,79,80,81,88,89,109,116,117,235],[[103,112],[116,120],[119],[101,111],[115,118],[103,104,110],[103,108,112],[100,101,117],[103,106,114],[116,120],[101,102,109],[113,115,121],[101,107,111],[115,118],[101,105,115]]),
([v62,v0,v5,v9,v3,v11],[],[0,1,3,7,10,12,15,22,26,66,71,79,80,81,84,87,88,89,106,114,116,125,167,171,179,202,207,222,225],[[103,115,116],[116,119,120],[116,128],[102],[111,113,122],[103,104,110],[103,108,126],[100,101,117],[103,106,112],[120,124,127],[101,109,123],[113,114,118],[101,107,125],[113,121,128],[101,105,113]]),
([v62,v0,v37,v3,v11,v16],[],[0,1,3,5,7,10,12,15,19,24,49,54,79,80,81,84,87,88,89,91,96,102,106,114,116,127,167,181,184,222,225],[[104,116,117],[117,119,123],[102],[112,114,126],[117,121,130],[104,105,111],[100,101,118],[104,107,113],[104,109,128],[101,103,110],[114,115,122],[124,125,129],[101,106,114],[101,108,127],[114,120,130]]),
([v63,v0,v1,v2,v11,v16],[],[0,1,2,3,4,5,11,12,18,19,27,28,48,49,79,81,84,88,89,91,96,102,109,134,169,176,180,181,217,219,225,231],[[100,101,118],[101,103,111],[101,105,113],[101,107,115],[101,109,127],[100,102,110],[100,104,112],[100,106,122],[100,108,126],[117,119,123],[114,115,131],[117,121,129],[115,116,122],[124,125,128],[115,120,130]]),
([v64,v0,v1,v2,v11,v16],[],[0,1,2,3,4,5,11,12,18,19,27,28,48,49,79,81,84,88,89,91,96,102,106,109,114,116,129,180,181,217,219,220,231],[[100,101,118],[101,103,111],[101,105,113],[101,107,115],[101,109,128],[100,102,110],[100,104,112],[100,106,123],[100,108,127],[117,119,124],[114,115,132],[117,121,130],[115,116,122],[125,126,129],[115,120,131]]),
([v43,v44,v0,v1,v11,v16],[],[0,1,3,5,8,12,19,28,29,35,40,46,48,49,79,80,81,84,88,89,91,96,102,106,116,127,134,181,195,216,223,225,228],[[101,103,113],[101,108,119],[101,102,107],[101,105,116],[101,106,127],[100,109,112],[118,120,126],[116,117,123],[124,125,130],[104,109,112],[109,110,115],[109,111,128],[114,116,132],[118,122,129],[116,121,131]]),
([v43,v0,v1,v37,v11,v16],[],[0,1,3,5,8,11,12,18,19,27,28,37,48,49,79,80,81,84,88,89,91,96,102,106,116,127,134,180,181,223,225,239,252],[[100,101,119],[101,102,110],[101,103,113],[101,106,116],[101,108,128],[100,104,109],[100,111,112],[100,105,115],[100,107,127],[118,120,126],[114,116,132],[118,122,131],[116,117,123],[124,125,129],[116,121,130]]),
([v43,v0,v1,v45,v2,v16],[],[0,1,3,4,5,8,12,18,19,27,28,40,48,49,79,80,81,84,88,89,91,96,102,106,116,127,134,180,181,219,223,225,231],[[100,101,119],[101,102,110],[101,106,116],[101,104,113],[101,108,128],[100,105,109],[100,111,115],[100,103,112],[100,107,127],[114,116,132],[118,120,126],[118,122,129],[116,117,123],[116,121,131],[124,125,130]]),
([v43,v0,v1,v52,v2,v11],[],[0,1,3,4,5,8,11,12,19,27,28,46,48,49,79,80,81,84,88,89,91,96,102,106,116,127,134,180,181,219,223,225,252],[[100,101,119],[101,102,110],[101,108,128],[101,104,113],[101,107,116],[100,105,109],[100,111,127],[100,103,112],[100,106,115],[118,122,129],[118,120,126],[114,116,132],[124,125,130],[116,121,131],[116,117,123]]),
([v43,v0,v1,v9,v2,v11],[],[0,1,3,4,5,8,11,12,27,28,48,49,62,63,79,80,81,84,88,89,91,106,125,134,177,204,205,219,223,225,231],[[100,101,119],[101,102,109],[101,113,126],[101,104,111],[101,107,116],[100,105,108],[100,112,125],[100,103,110],[100,106,115],[118,124,127],[118,120,123],[114,116,130],[128],[116,122,129],[116,117,121]]),
([v43,v0,v1,v2,v11,v16],[],[0,1,3,4,5,8,11,12,18,19,27,28,48,49,79,80,81,84,88,89,91,96,102,106,116,127,134,180,181,219,223,225,231],[[100,101,119],[101,102,111],[101,104,113],[101,107,116],[101,109,128],[100,105,110],[100,103,112],[100,106,115],[100,108,127],[118,120,126],[114,116,132],[118,122,129],[116,117,123],[124,125,130],[116,121,131]]),
([v65,v0,v8,v3,v11,v16],[],[0,1,3,5,7,10,12,15,19,24,28,34,79,81,84,88,91,96,102,109,114,181,184,222,225,230,233,247,249,254,255],[[104,129,130],[115,116,120],[103],[113,114,119],[124,127,128],[104,105,111],[100,101,125],[104,107,119],[104,109,122],[101,102,110],[112,113,126],[115,118,123],[101,106,113],[101,108,121],[113,117,124]]),
([v66,v0,v1,v9,v2,v11],[],[0,1,2,3,4,5,11,12,27,28,48,49,63,65,79,81,84,88,89,91,106,109,114,130,138,204,205,217,219,220,235],[[100,101,118],[101,103,109],[101,112,126],[101,105,111],[101,107,115],[100,102,108],[100,113,125],[100,104,110],[100,106,121],[117,123,128],[117,119,122],[114,115,130],[127],[115,124,129],[115,116,120]]),
([v66,v0,v1,v2,v11,v16],[],[0,1,2,3,4,5,11,12,18,19,27,28,48,49,79,81,84,88,89,91,96,102,106,109,114,116,127,180,181,217,219,220,235],[[100,101,118],[101,103,111],[101,105,113],[101,107,115],[101,109,128],[100,102,110],[100,104,112],[100,106,123],[100,108,127],[117,119,124],[114,115,132],[117,121,130],[115,116,122],[125,126,129],[115,120,131]]),
([v10,v14,v0,v2,v11,v16],[],[0,1,3,5,9,12,19,27,28,38,41,49,56,79,81,84,87,88,91,96,102,109,117,168,175,181,192,216,224,225,235],[[101,102,108],[101,107,116],[101,103,111],[101,105,114],[101,106,125],[100,107,112],[117,118,122],[113,114,130],[117,120,128],[104,107,112],[107,109,121],[107,110,126],[114,115,121],[123,124,127],[114,119,129]]),
([v10,v0,v8,v2,v11,v16],[],[0,1,3,5,9,11,12,18,19,27,28,48,49,57,79,81,84,88,91,96,102,109,117,180,181,224,225,232,235,247],[[100,101,127],[101,102,110],[101,103,112],[101,106,115],[101,108,124],[100,109,113],[100,104,111],[100,105,121],[100,107,123],[117,118,122],[114,115,128],[117,120,125],[115,116,121],[126,129],[115,119,126]]),
([v10,v0,v1,v9,v2,v11],[],[0,1,2,3,5,9,11,12,27,28,48,49,63,65,79,81,84,88,89,91,109,117,125,128,205,209,217,224,225,235],[[100,101,118],[101,103,109],[101,112,124],[101,104,111],[101,107,115],[100,102,108],[100,113,125],[100,105,110],[100,106,120],[117,123,127],[117,119,121],[114,115,129],[126],[115,122,128],[115,116,120]]),
([v10,v0,v1,v9,v54,v11],[],[0,1,3,4,9,10,12,17,22,26,28,36,79,81,83,88,100,116,128,162,168,202,209,217,224,225,232,235],[[101,103,126],[101,102,110],[101,108,121],[117],[101,106,113],[104,105,111],[104,109,122],[100],[104,107,114],[115,118,124],[115,120],[112,113,127],[123],[113,116,125],[113,119]]),
([v10,v0,v1,v2,v12,v16],[],[0,1,2,3,5,9,12,18,19,27,28,48,49,61,79,81,84,88,91,96,102,109,117,180,181,217,224,225,232,235],[[100,101,128],[101,103,110],[101,104,112],[101,106,115],[101,108,124],[100,102,109],[100,105,111],[100,113,121],[100,107,123],[117,118,122],[114,115,129],[117,120,126],[115,116,121],[125,127],[115,119,127]]),
([v10,v0,v1,v2,v55,v11],[],[0,1,2,3,5,9,11,12,19,27,28,48,49,65,79,81,84,88,89,91,96,102,109,117,169,180,181,217,224,225,235],[[100,101,118],[101,103,110],[101,104,112],[101,108,126],[101,107,115],[100,102,109],[100,105,111],[100,113,125],[100,106,122],[117,119,123],[117,121,128],[114,115,130],[124,127,129],[115,116,122],[115,120,129]]),
([v10,v0,v1,v2,v11,v16],[],[0,1,2,3,5,9,11,12,18,19,27,28,48,49,79,81,84,88,89,91,96,102,109,117,169,176,180,181,217,224,225,235],[[100,101,118],[101,103,111],[101,104,113],[101,107,115],[101,109,127],[100,102,110],[100,105,112],[100,106,122],[100,108,126],[117,119,123],[114,115,131],[117,121,129],[115,116,122],[124,125,128],[115,120,130]]),
([v67,v0,v1,v2,v11,v16],[],[0,1,3,5,8,9,11,12,18,19,27,28,48,49,79,80,81,84,88,89,91,96,102,106,116,117,127,180,181,223,224,225,235],[[100,101,119],[101,102,111],[101,103,113],[101,107,116],[101,109,128],[100,104,110],[100,105,112],[100,106,115],[100,108,127],[118,120,125],[114,116,132],[118,122,130],[116,117,123],[124,126,129],[116,121,131]]),
([v68,v0,v1,v9,v3,v11],[],[0,1,3,7,10,12,15,22,26,28,34,35,79,81,83,88,100,106,116,128,169,202,207,222,223,225,232,235],[[111],[],[124],[101,118,120],[113,117],[103,104,110],[103,108,122],[100,101,126],[103,106,114],[115,119,123],[101,102,109],[112,113,127],[101,107,121],[113,116,125],[101,105,113]]),
([v69,v0,v1,v9,v3,v11],[],[0,1,3,7,8,12,17,22,26,28,34,79,80,81,88,89,100,114,116,128,169,202,207,222,223,232,235,258],[[115],[114,117],[127],[101,118,120],[],[103,104,110],[103,108,122],[100,101,125],[103,106,112],[114,119,123],[101,102,109],[111,113,126],[101,107,121],[113,116,124],[101,105,113]]),
([v70,v0,v8,v3,v11,v16],[],[1,3,5,7,12,19,28,48,49,54,57,60,64,71,79,81,84,88,91,96,102,109,114,181,207,222,225,232,233,247],[[103],[117,118,122],[100,102,108],[115,116,121],[126,129],[109,110,113],[100,107,127],[109,111,121],[109,112,124],[100,101,106],[114,115,128],[117,120,125],[100,104,115],[100,105,123],[115,119,126]]),
([v71,v72,v1,v9,v3,v11],[],[0,1,3,7,8,9,12,15,28,34,79,80,81,88,89,106,109,114,116,120,125,128,201,207,209,235,247],[[105],[103,104,109],[126],[100,101,114],[103,107,111],[113,117,118],[118,123,124],[101,118,119],[112,115,116],[113,121,123],[101,102,108],[110,112,125],[101,122,123],[112,120,123],[101,106,112]]),
([v13,v0,v1,v9,v3,v11],[],[1,3,4,7,9,10,12,17,28,36,79,81,83,88,106,114,116,169,207,213,215,222,223,225,226,232,235,252],[[103,104,116],[113,115,126],[123],[100,116,117],[111,114,127],[104,105,109],[104,118,120],[100,102,125],[104,107,112],[113,121,122],[100,101,108],[110,111,126],[100,119],[111,122,124],[100,106,111]]),
([v13,v0,v1,v2,v3,v11],[],[1,3,5,7,9,12,28,49,51,56,57,61,63,73,79,81,84,88,91,109,116,117,125,128,205,207,209,223,224,225,232,235],[[103,109,126],[117,123,128],[120,127,129],[100,112,124],[115,122,129],[109,110,113],[104,109,125],[100,108,130],[109,111,119],[117,118,121],[100,101,106],[114,115,131],[100,102,107],[115,116,119],[100,105,115]]),
([v13,v0,v1,v54,v3,v11],[],[1,3,4,9,10,12,17,22,26,28,36,79,81,83,88,100,116,128,202,207,209,217,222,223,224,225,232,235,257,258],[[103,108,120],[114,117,124],[116],[100,107,118],[112,115,125],[103,104,110],[119],[100,102,126],[103,106,113],[114,122],[100,101,109],[111,112,127],[100,121,129],[112,123,128],[100,105,112]]),
([v73,v0,v1,v9,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,34,81,88,89,105,106,114,116,125,128,169,202,207,222,223,235,258],[[103,113],[112],[126],[101,117,120],[111],[103,104,110],[103,108,122],[100,101,113],[103,106,113],[116,119,123],[101,102,109],[114,115,125],[101,107,121],[115,118,124],[101,105,115]]),
([v74,v0,v5,v9,v3,v11],[],[0,1,3,6,7,8,10,12,15,22,26,28,34,66,71,79,80,81,89,105,109,114,116,125,128,202,207,222,225],[[104,105,112],[122],[],[101,102,111],[115,117,120],[104,106,114],[104,110,126],[100,101,118],[104,108,116],[121,124,127],[101,103,113],[117,119,120],[101,109,125],[117,123,128],[101,107,117]]),
([v74,v0,v1,v9,v3,v11],[],[0,1,6,7,10,12,15,22,26,30,35,80,81,84,88,89,105,106,114,125,128,202,207,222,223,225,235],[[103,110],[114],[124],[101,109],[112,113,117],[103,104,110],[103,108,122],[100,101,115],[103,106,111],[118,120,123],[101,102,109],[112,116,126],[101,107,121],[112,119,125],[101,105,112]]),
([v74,v0,v1,v27,v3,v11],[],[0,1,6,7,10,12,15,19,24,30,35,80,81,84,88,89,96,105,106,114,116,128,181,184,222,223,225,233],[[103,110],[114],[120,125,126],[101,109],[112,113,118],[103,104,110],[103,108,123],[100,101,115],[103,106,111],[119,121,124],[101,102,109],[112,117,127],[101,107,122],[112,116,126],[101,105,112]]),
([v74,v0,v1,v28,v3,v11],[],[0,1,6,7,10,12,15,22,24,30,35,80,81,84,88,89,105,106,114,116,125,126,127,202,207,222,223,225,233],[[103,110],[114],[119,122,126],[101,109],[112,113,117],[103,104,110],[103,108,124],[100,101,115],[103,106,111],[118,121,125],[101,102,109],[112,116,128],[101,107,123],[112,120,127],[101,105,112]]),
([v74,v0,v1,v6,v3,v16],[],[0,1,6,7,10,14,17,19,24,30,35,80,81,84,89,91,96,105,106,116,117,127,128,181,184,222,223,225,233],[[103,110],[115],[112,113,118],[101,109],[119,121,126],[103,104,110],[103,106,111],[100,101,114],[103,108,124],[112,117,128],[101,102,109],[120,122,125],[101,105,112],[112,116,127],[101,107,123]]),
([v74,v0,v1,v31,v3,v11],[],[0,1,6,7,10,12,15,22,26,30,35,80,81,84,88,89,96,105,106,114,116,127,128,193,195,222,223,225,235],[[103,110],[114],[120,121,126],[101,109],[112,113,118],[103,104,110],[103,108,124],[100,101,115],[103,106,111],[119,122,125],[101,102,109],[112,117,128],[101,107,123],[112,116,127],[101,105,112]]),
([v74,v0,v1,v23,v3,v11],[],[0,1,6,7,10,12,15,22,26,30,35,80,81,89,100,105,109,114,116,128,222,235],[[103,110],[],[118],[101,109],[112,114,116],[103,104,110],[103,108,110],[100,101,113],[103,106,111],[117,119,120],[101,102,109],[112,115,121],[101,107,109],[112,116],[101,105,112]]),
([v74,v0,v1,v3,v32,v11],[],[0,1,6,7,10,12,15,22,24,30,35,80,81,84,88,89,105,106,114,116,125,128,178,181,184,222,223,225,233],[[103,110],[114],[101,109],[119,122,126],[112,113,117],[103,104,110],[100,101,115],[103,108,124],[103,106,111],[101,102,109],[118,121,125],[112,116,128],[101,107,123],[101,105,112],[112,120,127]]),
([v75,v0,v5,v9,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,33,34,37,67,72,79,80,81,84,88,89,106,114,116,202,207,222,225,235,245,247,252],[[103,104,111],[119,122,123],[127],[101,102,109],[115,117,131],[103,112,114],[103,108,125],[100,101,120],[103,106,116],[123,126,128],[101,110,113],[117,118,121],[101,107,124],[117,129,130],[101,105,117]]),
([v76,v0,v1,v2,v3,v11],[],[0,1,7,12,15,22,26,30,35,52,56,80,81,84,88,89,91,106,108,116,117,125,223,224,225,235],[[102,108],[114,120,123],[119,122,124],[101,107],[112,121,124],[102,108],[102,106,110],[100,101,115],[102,104,111],[116,119,120],[101,107],[112,118,125],[101,105,109],[112,113,117],[101,103,112]]),
([v77,v0,v1,v9,v3,v11],[],[0,1,7,12,15,22,26,30,35,80,81,88,89,100,105,106,114,116,128,202,207,223,247,252],[[102,108],[111],[117,121,122],[101,107],[110,115,117],[102,108],[102,106,120],[100,101,112],[102,104,109],[116,118,122],[101,107],[110,114,123],[101,105,119],[110,113,121],[101,103,110]]),
([v78,v0,v1,v3,v11,v16],[],[0,1,5,6,7,10,14,15,22,24,28,30,35,79,80,81,84,88,89,91,96,102,106,114,116,127,183,184,222,223,225,233],[[104,112],[117,119,123],[101,102,111],[115,116,122],[124,125,129],[104,105,112],[100,102,118],[104,107,114],[104,109,127],[102,103,110],[113,115,131],[117,121,128],[102,106,115],[102,108,126],[115,120,130]]),
([v79,v0,v1,v3,v11,v16],[],[0,1,6,7,10,14,15,19,24,30,35,80,81,84,88,89,91,96,102,106,114,116,127,181,184,222,223,225,233],[[103,110],[114,116,120],[101,109],[112,113,119],[121,122,126],[103,104,110],[100,101,115],[103,106,111],[103,108,124],[101,102,109],[112,114,128],[114,118,125],[101,105,112],[101,107,123],[112,117,127]]),
([v80,v0,v1,v3,v11,v16],[],[0,1,6,7,10,12,15,22,24,30,35,80,81,84,88,89,96,102,105,106,114,116,127,188,195,222,223,225,233],[[103,110],[114,120,121],[101,109],[112,113,119],[121,122,126],[103,104,110],[100,101,115],[103,106,111],[103,108,124],[101,102,109],[112,118,128],[117,120,125],[101,105,112],[101,107,123],[112,116,127]]),
([v44,v0,v1,v81,v11,v16],[],[1,3,5,8,12,19,28,29,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,114,116,127,181,195,223,225,239,252],[[108,109,113],[118,120,124],[100,102,112],[116,117,123],[125,126,129],[103,108,118],[100,107,119],[108,110,115],[108,111,128],[100,101,106],[114,116,132],[118,122,131],[100,104,116],[100,105,127],[116,121,130]]),
([v44,v0,v1,v45,v3,v16],[],[1,3,5,7,8,12,19,28,29,35,40,46,49,54,79,80,81,84,88,89,91,96,102,106,116,127,134,181,195,222,223,225,233],[[103,109,113],[118,120,126],[116,117,123],[100,102,112],[124,125,130],[104,109,113],[109,110,115],[100,108,119],[109,111,128],[114,116,132],[100,101,107],[118,122,129],[100,105,116],[116,121,131],[100,106,127]]),
([v44,v0,v1,v52,v3,v11],[],[1,3,5,7,8,12,19,28,29,35,40,46,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,195,222,223,225,252],[[103,109,113],[118,120,124],[125,126,130],[100,102,112],[116,117,123],[104,109,113],[109,111,128],[100,108,119],[109,110,115],[118,122,129],[100,101,107],[114,116,132],[100,106,127],[116,121,131],[100,105,116]]),
([v44,v0,v1,v9,v3,v11],[],[1,3,5,7,8,12,28,29,35,40,49,54,63,65,79,80,81,84,88,89,91,106,114,125,128,205,207,222,223,225,235],[[103,108,111],[118,120,122],[128],[100,102,110],[116,117,121],[104,108,111],[108,113,126],[100,107,119],[108,109,115],[118,124,127],[100,101,106],[114,116,130],[100,112,125],[116,123,129],[100,105,116]]),
([v44,v0,v1,v82,v3,v11],[],[1,3,5,7,8,12,28,29,35,40,49,54,63,64,79,80,81,84,88,89,91,106,114,125,126,205,207,222,223,225,233],[[103,108,111],[118,120,122],[128],[100,102,110],[116,117,121],[104,108,111],[108,113,126],[100,107,119],[108,109,115],[118,124,127],[100,101,106],[114,116,130],[100,112,125],[116,123,129],[100,105,116]]),
([v44,v0,v1,v3,v11,v16],[],[1,3,5,7,8,12,19,28,29,35,40,46,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,195,222,223,225,233],[[103,109,113],[118,120,124],[100,102,112],[116,117,123],[125,126,130],[104,109,113],[100,108,119],[109,110,115],[109,111,128],[100,101,107],[114,116,132],[118,122,129],[100,105,116],[100,106,127],[116,121,131]]),
([v44,v0,v1,v3,v11,v83],[],[1,3,8,12,22,24,28,29,35,40,52,54,79,80,81,88,89,100,109,114,116,233],[[105,108,111],[115,119],[100,104,110],[114,117,118],[120],[102,108,111],[100,107,116],[108,109,113],[108,111],[100,101,106],[112,114,121],[115,119],[100,103,114],[100,110],[114,118]]),
([v84,v0,v1,v2,v3,v11],[],[1,3,5,7,8,12,28,29,35,37,40,49,63,72,79,80,81,84,88,89,91,106,116,117,125,134,205,209,223,224,225],[[103,108,127],[118,123,129],[122,128,130],[100,112,126],[116,124,130],[104,108,118],[108,109,113],[100,107,119],[108,110,115],[118,120,125],[100,101,106],[114,116,129],[100,102,111],[116,117,121],[100,105,116]]),
([v85,v0,v1,v2,v3,v11],[],[1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,81,84,88,91,93,106,109,114,116,117,172,205,209,235],[[103,113,127],[117,124],[123,125],[100,112,126],[115,121],[103,104,109],[103,105,111],[100,103,119],[103,107,121],[117,118,122],[100,101,108],[114,115,128],[100,102,110],[115,116,120],[100,106,115]]),
([v86,v0,v1,v9,v3,v11],[],[1,3,7,8,9,15,29,30,34,49,54,58,63,65,80,81,84,88,89,105,106,114,116,125,128,202,209,223,224,225,235],[[102,104,110],[117,121,122],[127],[100,107,109],[115,116,120],[102,103,108],[102,113,126],[102,106,118],[102,105,114],[121,124,128],[101,107,109],[115,119,130],[107,112,125],[115,123,129],[107,111,115]]),
([v87,v0,v1,v3,v11,v16],[],[1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[103,105,113],[118,120,124],[100,102,112],[116,117,123],[125,126,129],[103,104,111],[100,103,119],[103,107,115],[103,109,128],[100,101,110],[114,116,132],[118,122,130],[100,106,116],[100,108,127],[116,121,131]]),
([v88,v0,v8,v3,v11,v16],[],[0,1,3,7,10,14,17,19,24,28,34,81,88,91,102,105,109,114,125,143,146,181,184,222,225,230,233,247],[[103,120],[112,113,117],[101,119],[111],[124,127],[103,104,110],[100,101,125],[103,106,116],[103,108,122],[101,102,109],[112,115,126],[112,114,123],[101,105,116],[101,107,121],[116,118,124]]),
([v88,v0,v1,v17,v9,v3],[],[0,1,3,7,8,12,14,15,17,22,26,28,34,79,80,81,88,89,100,105,106,116,117,125,128,202,207,222,223],[[103,107,114],[113,115,122],[121],[118],[101,105,115],[103,104,112],[103,108,120],[103,110,126],[100,101,117],[116,119,120],[116,124,127],[101,102,111],[120,123,128],[101,106,120],[101,109,125]]),
([v88,v0,v1,v89,v3,v11],[],[0,1,3,7,8,14,17,19,24,28,34,81,88,89,91,102,105,106,114,116,125,143,181,184,222,223,233,247],[[103,113],[112,114,118],[119,125,127],[101,119,121],[111],[103,104,110],[103,108,123],[100,101,113],[103,106,113],[112,115,124],[101,102,109],[112,116,126],[101,107,122],[117,120,125],[101,105,117]]),
([v88,v0,v1,v55,v3,v11],[],[0,1,3,7,8,14,17,19,26,28,34,81,88,89,91,102,105,106,114,116,125,143,181,184,222,223,235,247],[[103,113],[112,114,118],[119,125,127],[101,119,121],[111],[103,104,110],[103,108,123],[100,101,113],[103,106,113],[112,115,124],[101,102,109],[112,116,126],[101,107,122],[117,120,125],[101,105,117]]),
([v90,v0,v1,v17,v9,v3],[],[0,1,3,7,8,12,15,22,26,28,34,79,80,81,88,89,91,100,106,114,116,120,147,202,207,222,223,235,252],[[103,106,112],[111,113,127],[113,118,120],[117],[101,105,113],[103,104,110],[103,120,122],[103,108,124],[100,101,115],[114,116,119],[114,125,126],[101,102,109],[120,126,128],[101,120,121],[101,107,123]]),
([v91,v0,v8,v3,v11,v16],[],[0,1,3,7,10,12,15,22,26,28,34,79,81,83,88,100,128,188,190,222,225,232,233,235,242,244],[[103,118],[114,122,125],[101,117],[112,124],[],[103,104,110],[100,101,121],[103,106,113],[103,108,118],[101,102,109],[111,112,123],[114,116,119],[101,105,112],[101,107,117],[112,115,120]]),
([v91,v0,v1,v12,v3,v16],[],[0,1,3,7,8,12,17,22,26,28,34,79,80,81,88,100,128,188,190,222,223,232,233,234,235,242,244],[[103,118],[114,122,126],[113,123,125],[101,117],[],[103,104,110],[103,106,112],[100,101,121],[103,108,118],[111,113,124],[101,102,109],[114,116,119],[101,105,113],[113,115,120],[101,107,117]]),
([v92,v0,v1,v2,v3,v11],[],[0,1,3,7,8,12,15,22,28,34,52,56,79,80,81,88,89,100,109,116,117,252],[[103,111],[115,120],[119],[101,110],[114,118],[103,104,109],[103,111],[100,101,116],[103,106,113],[115,120],[101,102,108],[112,114,121],[101,107,110],[114,117,118],[101,105,114]]),
([v93,v0,v5,v9,v3,v11],[],[1,3,7,12,22,27,28,33,34,37,39,47,67,71,78,79,81,84,87,88,105,114,125,128,134,202,222,225,247,252],[[102],[124],[119,127,128],[100,101,106],[115,116,129],[108,109,113],[108,111,127],[100,105,118],[108,110,114],[121,123,126],[100,107,112],[116,117,120],[100,104,125],[116,122,127],[100,103,116]]),
([v93,v0,v37,v3,v11,v16],[],[1,3,5,7,12,19,27,28,34,37,39,45,49,71,78,79,81,84,87,88,91,96,102,105,114,126,134,181,194,222,225,239,252],[[103],[119,120,126],[100,101,107],[115,116,132],[119,122,131],[108,109,113],[100,106,118],[108,110,114],[108,111,128],[100,102,112],[116,117,123],[124,125,129],[100,104,116],[100,105,127],[116,121,130]]),
([v94,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,181,184,223,224,225,235],[[104,110,128],[119,123,130],[126,129,131],[101,109,127],[117,122,131],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,121,125],[101,102,111],[115,117,132],[101,103,113],[117,118,124],[101,107,117]]),
([v95,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,125,128,205,209,223,224,225,235],[[104,105,110],[104,114,127],[104,106,112],[100,101,120],[104,108,116],[119,125,129],[119,121,123],[101,102,109],[115,117,131],[128],[101,113,126],[117,124,130],[101,103,111],[117,118,122],[101,107,117]]),
([v95,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v96,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v97,v0,v8,v3,v11,v16],[],[0,1,3,5,7,9,10,12,15,19,24,28,34,49,54,79,81,83,88,91,96,102,181,184,222,225,230,233,247,249,250,252],[[104,105,114],[119],[101,103,113],[116,130,131],[125,128,129],[104,106,112],[100,101,126],[104,108,117],[104,110,123],[101,102,111],[115,116,127],[118,121,124],[101,107,116],[101,109,122],[116,120,125]]),
([v97,v0,v2,v6,v3,v16],[],[0,1,6,7,10,16,19,24,52,56,59,78,79,84,89,91,94,105,108,116,117,127,128,181,184,222,224,225,235],[[103,109],[115],[112,118,128],[101,108],[120,122,126],[103,104,109],[103,105,111],[100,101,114],[103,107,124],[112,113,117],[101,102,108],[119,121,125],[101,110,112],[112,116,127],[101,106,123]]),
([v97,v0,v2,v18,v11,v16],[],[0,1,6,7,10,12,13,19,24,52,56,79,85,110,112,113,116,121,127,130,181,184,222,224,225,232,233,235,249,255],[[103,110],[129],[101,109],[114,115,127],[117,119,123],[103,104,110],[100,101,125],[103,106,112],[103,108,121],[101,102,109],[113,115,126],[116,118,122],[101,105,111],[101,107,120],[115,124,128]]),
([v97,v0,v47,v3,v11,v16],[],[0,1,3,7,10,12,15,19,24,28,31,34,36,50,56,79,81,82,83,88,91,96,102,128,181,184,222,224,225,230,233,235,255],[[103,112,114],[132],[101,110,113],[116,117,131],[120,123,127],[103,104,111],[100,101,129],[103,106,118],[103,108,125],[101,102,109],[115,116,130],[119,122,126],[101,105,116],[101,107,124],[116,121,128]]),
([v98,v0,v1,v9,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,44,49,54,65,79,80,81,84,88,89,91,100,106,114,116,128,205,209,222,223,225,252],[[104,106,113],[119,121,124],[125,130,131],[101,103,112],[117,118,123],[104,105,110],[104,114,128],[100,101,120],[104,108,116],[119,126,129],[101,102,109],[115,117,132],[101,111,127],[117,122,130],[101,107,117]]),
([v99,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,125,128,205,209,223,224,225,235],[[104,114,127],[119,125,129],[128],[101,113,126],[117,124,130],[104,105,110],[104,106,112],[100,101,120],[104,108,116],[119,121,123],[101,102,109],[115,117,131],[101,103,111],[117,118,122],[101,107,117]]),
([v100,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,106,114,116,128,181,184,223,224,225,235],[[104,110,128],[119,126,130],[125,129,131],[101,109,127],[117,122,131],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,121,124],[101,102,111],[115,117,132],[101,103,113],[117,118,123],[101,107,117]]),
([v101,v0,v2,v3,v11,v16],[],[0,1,3,6,7,10,15,20,24,49,52,56,59,78,79,81,84,87,88,91,96,102,105,114,117,126,182,184,222,224,225,235],[[104,111],[118,119,124],[101,102,110],[114,115,131],[118,121,129],[104,105,111],[100,102,117],[104,106,113],[104,108,127],[102,103,109],[115,116,122],[123,125,128],[102,112,115],[102,107,126],[115,120,130]]),
([v102,v0,v2,v3,v11,v16],[],[0,1,6,7,10,15,19,24,52,56,59,78,79,84,87,88,91,94,102,105,114,117,126,181,184,222,224,225,235],[[103,109],[115,116,121],[101,108],[112,115,128],[115,118,126],[103,104,109],[100,101,114],[103,105,111],[103,107,124],[101,102,108],[112,113,119],[120,122,125],[101,110,112],[101,106,123],[112,117,127]]),
([v14,v0,v9,v2,v3,v11],[],[1,3,5,7,9,12,27,28,34,39,49,56,63,65,78,79,81,84,87,88,91,105,117,125,128,205,209,222,224,225,235],[[103,108,111],[119,124,128],[119,120,122],[100,101,107],[115,116,130],[108,113,126],[104,108,111],[100,106,118],[108,109,114],[127],[100,112,125],[116,123,129],[100,102,110],[116,117,121],[100,105,116]]),
([v14,v0,v9,v54,v3,v11],[],[1,3,4,9,10,12,17,22,26,28,34,36,79,81,83,88,100,105,114,128,168,202,209,222,224,225,232,235],[[103,104,111],[115,119,124],[],[100,101,109],[112,113,127],[103,108,122],[110],[100,102,126],[103,106,114],[123],[100,107,121],[113,116,125],[100,118,120],[113,117],[100,105,113]]),
([v14,v0,v2,v26,v11,v16],[],[1,3,5,9,12,19,27,28,49,56,57,61,65,73,78,79,81,84,87,88,91,96,102,105,114,117,126,181,209,224,225,235,247],[[109,110,113],[119,120,125],[100,101,107],[115,116,131],[119,122,129],[103,109,118],[100,106,118],[109,111,114],[109,112,128],[100,102,108],[116,117,123],[124,126,132],[100,104,116],[100,105,127],[116,121,130]]),
([v14,v0,v2,v12,v3,v16],[],[1,3,5,7,9,12,19,27,28,34,45,49,56,61,78,79,81,84,88,91,96,102,105,117,181,194,222,224,225,232,235],[[103,109,112],[118,119,123],[115,116,130],[100,101,108],[118,121,127],[104,109,112],[109,113,114],[100,107,129],[109,110,125],[116,117,122],[100,102,111],[126,128],[100,105,116],[116,120,128],[100,106,124]]),
([v14,v0,v2,v55,v3,v11],[],[1,3,5,7,9,12,19,27,28,34,39,49,56,65,78,79,81,84,87,88,91,96,102,105,114,117,181,194,222,224,225,235],[[103,109,112],[119,120,125],[119,122,129],[100,101,108],[115,116,131],[104,109,112],[109,113,127],[100,107,118],[109,110,114],[124,128,130],[100,102,111],[116,117,123],[100,106,126],[116,121,130],[100,105,116]]),
([v14,v0,v2,v3,v11,v16],[],[1,3,5,7,9,12,19,27,28,34,39,45,49,56,78,79,81,84,87,88,91,96,102,105,114,117,126,181,194,222,224,225,235],[[103,109,113],[119,120,125],[100,101,108],[115,116,132],[119,122,130],[104,109,113],[100,107,118],[109,110,114],[109,111,128],[100,102,112],[116,117,123],[124,126,129],[100,105,116],[100,106,127],[116,121,131]]),
([v103,v0,v2,v3,v11,v16],[],[1,3,5,7,8,9,12,15,19,24,28,34,49,54,78,79,81,84,87,88,91,96,102,105,114,117,126,181,184,223,224,225,235],[[103,104,111],[119,120,125],[100,101,110],[115,116,132],[119,122,130],[103,105,113],[100,103,118],[103,107,114],[103,109,128],[100,102,112],[116,117,123],[124,126,129],[100,106,116],[100,108,127],[116,121,131]]),
([v104,v0,v5,v9,v3,v11],[],[0,1,6,7,10,16,22,26,66,71,78,79,84,87,88,89,98,105,113,114,116,143,146,202,207,222,225,247,252],[[103,113,122],[119],[114,126,127],[101,114,121],[128],[103,104,109],[103,107,124],[100,101,115],[103,105,110],[120,125,126],[101,102,108],[111,112,117],[101,106,123],[111,116,126],[101,111,118]]),
([v104,v0,v37,v3,v11,v16],[],[0,1,5,7,10,16,19,24,49,54,78,79,82,87,88,89,91,94,102,105,113,114,116,118,127,143,181,184,222,225,239,252],[[103,113,123],[114,116,121],[101,114,125],[131],[114,118,130],[103,104,109],[100,101,115],[103,105,110],[103,107,127],[101,102,108],[111,112,119],[122,124,128],[101,111,120],[101,106,126],[111,117,129]]),
([v104,v0,v52,v2,v3,v11],[],[0,1,5,7,9,16,19,25,49,54,78,79,82,87,88,89,91,94,102,105,112,114,116,117,127,143,181,184,222,224,239,252],[[103,113,123],[114,118,130],[114,116,121],[101,114,125],[131],[103,107,127],[103,104,109],[100,101,115],[103,105,110],[122,124,128],[101,106,126],[111,117,129],[101,102,108],[111,112,119],[101,111,120]]),
([v105,v0,v1,v2,v18,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,81,86,111,112,113,116,119,121,130,181,184,223,224,225,232,234,235,249,255],[[104,110,125],[122,123,127],[120,126,128],[101,109,124],[119,128,132],[104,105,112],[104,106,114],[100,101,129],[104,108,116],[120,121,133],[101,102,111],[118,119,131],[101,103,113],[117,119,130],[101,107,115]]),
([v106,v0,v1,v3,v11,v16],[],[0,1,5,6,7,9,10,12,15,19,24,30,35,80,81,82,84,88,89,91,96,106,114,116,126,127,181,184,222,223,225,233],[[104,105,112],[117,119,122],[101,102,111],[114,116,121],[123,125,129],[104,106,112],[100,101,118],[104,108,113],[104,110,127],[101,103,111],[114,115,131],[119,124,128],[101,107,114],[101,109,126],[114,120,130]]),
([v106,v0,v2,v3,v11,v16],[],[0,1,3,6,7,8,10,12,15,19,24,28,34,50,55,79,80,81,82,88,89,91,96,102,105,108,114,126,128,181,184,222,225],[[104,105,112],[119,121,126],[101,102,111],[115,117,125],[119,123,128],[104,106,114],[100,101,120],[104,108,116],[104,110,130],[101,103,113],[117,118,124],[121,127,131],[101,107,117],[101,109,129],[117,122,132]]),
([v107,v0,v1,v9,v3,v11],[],[0,1,3,7,8,22,26,28,34,81,88,89,105,106,111,114,116,125,143,202,207,222,223,235,247],[[103,111],[110,115,116],[116,122,124],[101,116,118],[109],[103,104,108],[103,106,120],[100,101,111],[103,111],[110,121,122],[101,102,107],[110,112,123],[101,105,119],[113,117,122],[101,113,114]]),
([v108,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,110,129],[119,123,131],[126,127,130],[101,109,128],[117,122,132],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,121,125],[101,102,111],[115,117,133],[101,103,113],[117,118,124],[101,107,117]]),
([v109,v0,v1,v9,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,34,37,79,80,81,88,89,100,106,109,114,116,120,202,207,223,225,247,252],[[111],[120],[121,125,126],[101,121,122],[114,118,119],[103,104,110],[103,108,124],[100,101,116],[103,106,113],[115,126,127],[101,102,109],[112,114,128],[101,107,123],[114,117,126],[101,105,114]]),
([v110,v0,v2,v18,v11,v16],[],[0,1,5,7,8,9,12,15,19,24,49,54,79,85,111,112,113,116,117,119,121,127,130,181,184,223,224,225,232,234,235,249,255],[[104],[117,119,132],[101,118,120],[115,116,130],[120,122,126],[103,105,111],[100,101,128],[103,107,113],[103,109,124],[101,102,110],[114,116,129],[117,121,125],[101,106,112],[101,108,123],[116,127,131]]),
([v111,v0,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,125,128,205,209,223,224,225,235],[[104,105,110],[119,125,129],[119,121,123],[101,102,109],[115,117,131],[104,114,127],[104,106,112],[100,101,120],[104,108,116],[128],[101,113,126],[117,124,130],[101,103,111],[117,118,122],[101,107,117]]),
([v111,v0,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v112,v0,v1,v9,v3,v11],[7],[0,1,3,7,8,12,15,22,26,28,34,79,80,81,88,89,100,106,114,116,120,128,147,202,207,222,223,235],[[122],[114,118,119],[0,119,126],[101,119,120],[117],[103,104,110],[103,108,124],[100,101,115],[103,106,112],[114,121,125],[101,102,109],[111,113,127],[101,107,123],[113,116,126],[101,105,113]]),
([v113,v0,v1,v2,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,34,52,56,79,80,81,88,89,100,109,116,117,235],[[103,112],[116,121],[120],[101,111],[115,119],[103,104,110],[103,108,112],[100,101,117],[103,106,114],[116,121],[101,102,109],[113,115,122],[101,107,111],[115,118,119],[101,105,115]]),
([v72,v0,v1,v9,v3,v11],[],[0,1,3,7,8,9,12,15,22,28,34,79,80,81,88,89,100,106,109,114,116,120,128,202,207,223,224,225,235,247],[[105],[114,119,120],[120,125,127],[101,120,121],[113,117,118],[103,104,110],[103,124,129],[100,101,115],[103,107,112],[114,122,126],[101,102,109],[111,113,128],[101,108,123],[113,116,127],[101,106,113]]),
([v72,v0,v1,v27,v3,v11],[],[0,1,3,7,8,9,12,15,19,24,28,34,79,80,81,88,89,96,106,109,114,116,120,128,181,184,223,224,225,235],[[105],[115,120,121],[121,126,128],[101,121,122],[114,118,119],[103,104,111],[103,109,125],[100,101,116],[103,107,113],[115,123,127],[101,102,110],[112,114,129],[101,108,124],[114,117,128],[101,106,114]]),
([v72,v0,v1,v28,v3,v11],[],[0,1,3,7,8,9,12,15,22,24,28,34,79,80,81,88,89,100,106,109,114,116,120,127,128,202,207,223,224,225,235],[[105],[115,120,121],[121,123,127],[101,121,122],[114,118,119],[103,104,111],[103,109,126],[100,101,116],[103,107,113],[115,124,128],[101,102,110],[112,114,130],[101,108,125],[114,117,129],[101,106,114]]),
([v72,v0,v1,v6,v3,v16],[],[0,1,3,7,8,9,14,19,24,28,34,40,79,80,81,89,91,96,106,109,116,117,120,127,128,181,184,223,224,225,235],[[105],[116,120,121],[114,118,119],[101,120,122],[120,123,127],[103,104,110],[103,111,113],[100,101,115],[103,108,126],[112,114,130],[101,102,109],[116,124,128],[101,106,114],[114,117,129],[101,107,125]]),
([v72,v0,v1,v31,v3,v11],[],[0,1,3,7,8,9,12,15,22,28,34,46,79,80,81,88,89,96,106,109,114,116,120,127,128,193,195,223,224,225,235],[[105],[115,120,121],[121,123,127],[101,121,122],[114,118,119],[103,104,110],[103,111,126],[100,101,116],[103,107,113],[115,124,128],[101,102,109],[112,114,130],[101,108,125],[114,117,129],[101,106,114]]),
([v72,v0,v1,v3,v32,v11],[],[0,1,3,7,8,9,12,15,22,24,28,34,79,80,81,88,89,100,106,109,114,116,120,128,178,181,184,223,224,225,235],[[105],[115,120,121],[101,121,122],[121,124,127],[114,118,119],[103,104,111],[100,101,116],[103,109,126],[103,107,113],[101,102,110],[115,123,128],[112,114,130],[101,108,125],[101,106,114],[114,117,129]]),
([v72,v1,v9,v114,v3,v11],[],[0,1,3,7,8,9,12,15,22,26,28,34,79,80,81,88,89,100,106,109,114,116,120,202,207,215,235,245],[[115,120,121],[109,121,125],[103,105,121],[101,121,122],[114,118,119],[115,126],[103,104,111],[101,102,110],[112,114,126],[124],[101,108,123],[114,117,127],[100,101,116],[103,107,113],[101,106,114]]),
([v72,v1,v9,v54,v3,v11],[],[0,1,3,4,7,8,9,10,12,15,17,22,26,28,34,36,79,80,81,83,88,89,100,116,128,202,207,209,224,225,232,235],[[106,107,115],[106,112,127],[123],[101,103,130],[106,110,119],[120,124,128],[104,105,114],[101,102,113],[116,118,131],[126],[101,111,125],[118,122,129],[100,101,121],[104,109,117],[101,108,118]]),
([v115,v0,v1,v9,v3,v11],[],[0,1,3,5,7,8,9,12,15,22,28,34,49,54,65,79,80,81,84,88,89,91,100,106,114,116,128,202,207,223,224,225,235],[[104,106,113],[119,121,124],[125,129,131],[101,103,112],[117,118,123],[104,105,111],[104,114,128],[100,101,120],[104,108,116],[119,126,130],[101,102,110],[115,117,132],[101,109,127],[117,122,131],[101,107,117]]),
([v116,v0,v1,v9,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,106,114,116,125,128,205,209,223,224,225,235],[[104,106,112],[119,122,123],[123,128,130],[101,103,111],[117,118,121],[104,105,110],[104,114,127],[100,101,120],[104,108,116],[119,125,129],[101,102,109],[115,117,131],[101,113,126],[117,124,130],[101,107,117]]),
([v117,v0,v1,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,79,80,81,88,89,91,96,102,106,109,114,116,127,181,184,223,224,225,235],[[104,106,124],[116,118,123],[101,103,124],[115,121,122],[124,125,128],[104,105,112],[100,101,117],[104,108,114],[104,110,127],[101,102,111],[113,115,131],[116,120,129],[101,107,115],[101,109,126],[115,119,130]]),
([v118,v1,v2,v3,v11,v16],[],[0,3,5,7,8,9,11,15,18,24,27,34,48,54,78,80,81,84,87,89,91,96,101,106,116,117,127,180,184,223,224,225,235],[[103,104,111],[103,105,113],[100,103,119],[103,107,115],[103,109,128],[118,120,125],[100,101,110],[114,116,132],[118,122,130],[100,102,112],[116,117,123],[124,126,129],[100,106,116],[100,108,127],[116,121,131]]),
([v119,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,125,127,220,223,224,225,235],[[104,110,131],[119,122,130],[125,127,129],[101,109,128],[117,126,131],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,121,124],[101,102,111],[115,117,132],[101,103,113],[117,118,123],[101,107,117]]),
([v120,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,63,79,80,81,84,88,89,91,106,114,116,125,127,128,220,223,224,225,235],[[104,109,131],[119,127,130],[124,126,129],[101,114,128],[117,125,131],[104,105,111],[104,106,113],[100,101,120],[104,108,116],[119,121,123],[101,102,110],[115,117,132],[101,103,112],[117,118,122],[101,107,117]]),
([v121,v0,v1,v3,v11,v16],[],[1,3,4,5,7,9,10,12,17,19,26,28,36,49,54,79,81,83,84,88,91,96,102,116,127,131,134,135,181,186,223,224,225,235],[[104,105,114],[119,120,126],[100,103,113],[116,118,125],[123,124,130],[105,106,112],[100,102,127],[105,108,117],[105,110,129],[100,101,111],[115,116,133],[119,122,131],[100,107,116],[100,109,128],[116,121,132]]),
([v121,v1,v2,v3,v11,v16],[],[0,1,3,4,7,8,9,10,12,15,17,19,24,26,28,34,36,48,51,54,60,61,64,65,79,81,88,96,102,181,224,225,235],[[104,105,115],[104,106,119],[100,101,118],[104,109,121],[104,112,123],[106,107,116],[101,102,114],[124,125,132],[126,128,130],[101,103,117],[106,110,120],[106,113,122],[101,108,125],[101,111,129],[125,127,131]]),
([v122,v0,v2,v3,v11,v16],[],[1,2,3,5,7,8,10,12,16,19,25,28,34,49,55,78,79,81,84,87,88,91,96,102,106,108,116,127,128,181,185,223,225],[[104,105,112],[120,121,126],[100,102,111],[116,117,125],[120,123,128],[105,106,114],[100,101,119],[105,108,115],[105,110,130],[100,103,113],[117,118,124],[126,127,131],[100,107,117],[100,109,129],[117,122,132]]),
([v122,v1,v2,v3,v11,v16],[],[0,1,2,5,7,8,9,10,12,15,16,19,24,25,27,29,34,36,37,39,40,45,46,49,81,84,96,106,116,127,181,223,225],[[104,105,116],[104,106,118],[100,101,115],[104,109,120],[104,112,122],[105,107,117],[101,102,114],[105,110,119],[105,113,121],[101,103,123],[124,125,127],[128,129,131],[101,108,124],[101,111,130],[124,126,132]]),
([v123,v0,v1,v3,v11,v16],[],[0,1,3,7,8,9,12,15,19,24,28,34,79,80,81,88,89,91,96,102,106,109,114,116,120,127,181,184,223,224,225,235],[[103,105,123],[115,117,122],[101,123,124],[114,120,121],[123,125,128],[103,104,111],[100,101,116],[103,107,113],[103,109,127],[101,102,110],[112,114,131],[115,119,129],[101,106,114],[101,108,126],[114,118,130]]),
([v124,v40,v0,v1,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,88,89,91,106,109,114,125,128,205,209,223,224,225,235],[[128],[104,114,127],[118,125,129],[101,113,126],[117,124,130],[104,106,112],[118,120,123],[101,103,111],[117,121,122],[104,105,110],[100,101,119],[104,108,116],[101,102,109],[115,117,131],[101,107,117]]),
([v124,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,125,128,205,209,223,224,225,235],[[104,114,127],[119,125,129],[128],[101,113,126],[117,124,130],[104,105,110],[104,106,112],[100,101,120],[104,108,116],[119,121,123],[101,102,109],[115,117,131],[101,103,111],[117,118,122],[101,107,117]]),
([v125,v0,v1,v3,v11,v16],[],[0,1,3,7,8,9,12,15,19,24,28,34,79,80,81,88,89,96,102,106,109,114,116,120,127,181,184,223,224,225,235],[[103,105,122],[115,121,122],[101,122,123],[114,119,120],[122,124,127],[103,104,111],[100,101,116],[103,107,113],[103,109,126],[101,102,110],[112,114,130],[115,118,128],[101,106,114],[101,108,125],[114,117,129]]),
([v40,v126,v0,v1,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,88,89,91,102,106,109,114,116,125,127,181,184,223,224,225,235],[[125,127,130],[104,106,114],[118,120,124],[101,103,113],[117,122,123],[104,110,129],[118,121,131],[101,109,128],[117,126,132],[104,105,112],[100,101,119],[104,108,116],[101,102,111],[115,117,133],[101,107,117]]),
([v40,v0,v1,v9,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,44,49,54,65,79,80,81,88,89,91,100,106,109,114,116,128,205,209,223,224,225,235],[[104,106,113],[118,120,124],[125,129,131],[101,103,112],[117,122,123],[104,105,110],[104,114,128],[100,101,119],[104,108,116],[118,126,130],[101,102,109],[115,117,132],[101,111,127],[117,121,131],[101,107,117]]),
([v40,v0,v1,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,88,89,91,96,102,106,109,114,116,127,181,184,223,224,225,235],[[104,106,114],[118,120,125],[101,103,113],[117,123,124],[126,127,130],[104,105,112],[100,101,119],[104,108,116],[104,110,129],[101,102,111],[115,117,133],[118,122,131],[101,107,117],[101,109,128],[117,121,132]]),
([v40,v0,v1,v3,v11,v127],[],[0,1,5,7,8,9,12,15,19,24,30,35,45,49,54,81,88,94,95,102,103,106,109,114,116,117,127,223,235],[[103,105,114],[119,123,124],[101,102,113],[115,121,122],[124,126,127],[103,104,112],[100,101,120],[103,107,118],[103,109,111],[101,110],[115,117,128],[116,119,125],[101,106,115],[101,108,110],[115,122]]),
([v128,v0,v1,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,106,114],[119,121,125],[101,103,113],[117,118,124],[126,127,130],[104,105,112],[100,101,120],[104,108,116],[104,110,129],[101,102,111],[115,117,133],[119,123,131],[101,107,117],[101,109,128],[117,122,132]]),
([v129,v0,v1,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,106,114],[119,121,125],[101,103,113],[117,118,124],[126,127,130],[104,105,112],[100,101,120],[104,108,116],[104,110,129],[101,102,111],[115,117,133],[119,123,131],[101,107,117],[101,109,128],[117,122,132]]),
([v130,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,125,181,184,223,224,225,235],[[104,110,128],[119,122,130],[125,129,131],[101,109,127],[117,126,131],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,121,124],[101,102,111],[115,117,132],[101,103,113],[117,118,123],[101,107,117]]),
([v131,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,63,79,80,81,84,88,89,91,106,114,116,125,127,128,205,209,223,224,225,235],[[104,109,129],[119,127,131],[124,126,130],[101,114,128],[117,125,132],[104,105,111],[104,106,113],[100,101,120],[104,108,116],[119,121,123],[101,102,110],[115,117,133],[101,103,112],[117,118,122],[101,107,117]]),
([v132,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,125,127,148,220,223,224,225,235],[[104,109,131],[118,121,130],[124,126,129],[101,127,128],[116,125,131],[104,105,111],[104,106,113],[100,101,119],[104,108,115],[118,120,123],[101,102,110],[114,116,132],[101,103,112],[116,117,122],[101,107,116]]),
([v126,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,125,127,181,184,223,224,225,235],[[104,110,129],[119,122,131],[125,127,130],[101,109,128],[117,126,132],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,121,124],[101,102,111],[115,117,133],[101,103,113],[117,118,123],[101,107,117]]),
([v126,v0,v1,v47,v3,v11],[],[0,1,5,7,8,9,12,15,19,24,30,35,36,81,82,83,88,91,106,116,125,127,128,181,184,223,224,225,232,234,235,255],[[103,109,124],[117,122,126],[119,121,125],[101,108,123],[113,120,127],[103,104,112],[103,105,111],[100,101,128],[103,107,115],[116,117,131],[101,110],[113,114,130],[101,102,110],[113,118,129],[101,106,113]]),
([v133,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,110,129],[119,123,131],[126,127,130],[101,109,128],[117,122,132],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,121,125],[101,102,111],[115,117,133],[101,103,113],[117,118,124],[101,107,117]]),
([v134,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,110,129],[119,123,131],[126,127,130],[101,109,128],[117,122,132],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,121,125],[101,102,111],[115,117,133],[101,103,113],[117,118,124],[101,107,117]]),
([v135,v0,v1,v2,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,34,52,56,79,80,81,88,89,109,116,117,235],[[103,112],[116,120],[119],[101,111],[115,118],[103,104,110],[103,108,112],[100,101,117],[103,106,114],[116,120],[101,102,109],[113,115,121],[101,107,111],[115,118],[101,105,115]]),
([v136,v0,v5,v9,v3,v11],[],[0,1,3,7,10,12,15,22,26,28,33,34,67,79,81,84,88,105,109,114,125,128,202,207,222,225,232],[[111],[116,119],[116,125],[101,102,109],[113,114,118],[103,104,119],[103,108,123],[100,101,126],[103,106,118],[119,121,124],[101,110,112],[114,115,117],[101,107,122],[114,120,125],[101,105,114]]),
([v136,v0,v37,v3,v11,v16],[],[0,1,3,5,7,10,12,15,19,24,28,34,49,54,79,81,84,88,91,96,102,105,109,114,118,126,181,184,222,225],[[111],[117,118,123],[101,102,110],[114,115,122],[117,120,129],[104,105,113],[100,101,124],[104,107,122],[104,109,127],[101,103,112],[115,116,121],[123,125,128],[101,106,115],[101,108,126],[115,119,129]]),
([v137,v0,v1,v2,v3,v11],[],[0,1,7,8,12,15,22,26,30,35,52,56,73,81,84,88,91,108,109,116,117,125,222,223,224,225,232,235],[[102,109,111],[115,120,124],[119,123,125],[101,108],[113,121,125],[102,103,112],[102,107,111],[100,101,126],[102,105,118],[116,120,122],[101,108],[113,117,127],[101,106,110],[113,114,118],[101,104,113]]),
([v138,v0,v1,v9,v3,v11],[],[0,1,7,10,12,15,22,26,30,35,80,81,88,89,100,105,106,109,114,116,128,202,207,222,223,225,235],[[102,109],[112],[119,124,125],[101,108],[111,116,117],[102,103,109],[102,107,122],[100,101,113],[102,105,110],[118,120,123],[101,108],[111,115,126],[101,106,121],[111,114,125],[101,104,111]]),
([v139,v0,v8,v3,v11,v16],[],[0,1,3,5,7,10,12,15,19,24,28,34,49,54,79,81,83,84,88,91,96,102,131,134,181,184,222,225,230,233,247,249],[[113],[118,119,123],[101,103,112],[115,117,122],[127,130,131],[104,105,111],[100,101,128],[104,107,116],[104,109,125],[101,102,110],[114,115,129],[118,121,126],[101,106,115],[101,108,124],[115,120,127]]),
([v140,v0,v1,v9,v3,v11],[],[0,1,3,5,7,8,9,12,15,26,28,34,49,54,63,79,80,81,84,88,89,91,106,114,116,138,205,209,222,223,225,235],[[104,106,113],[119,121,123],[124,129,130],[101,103,112],[117,118,122],[104,105,111],[104,109,127],[100,101,120],[104,108,116],[119,128,129],[101,102,110],[115,117,131],[101,114,126],[117,125,129],[101,107,117]]),
([v141,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,125,205,209,223,224,225,235],[[104,114,126],[119,128,129],[127],[101,113,125],[117,124,129],[104,105,110],[104,106,112],[100,101,120],[104,108,116],[119,121,123],[101,102,109],[115,117,130],[101,103,111],[117,118,122],[101,107,117]]),
([v142,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,106,114,116,181,184,223,224,225,235],[[104,110,127],[119,129,130],[125,128,130],[101,109,126],[117,122,130],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,121,124],[101,102,111],[115,117,131],[101,103,113],[117,118,123],[101,107,117]]),
([v143,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,88,89,91,96,102,106,109,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,119],[104,108,116],[104,110,129],[118,120,125],[101,102,111],[115,117,133],[118,122,131],[101,103,113],[117,123,124],[126,127,130],[101,107,117],[101,109,128],[117,121,132]]),
([v15,v1,v54,v3,v11,v16],[],[1,5,6,7,9,10,14,17,22,26,31,36,79,80,81,87,88,89,96,102,103,169,183,186,223,224,225,230,234,235],[[104,105,111],[103],[100,101,127],[104,107,114],[104,109,123],[115,116],[101,102,110],[112,114,129],[116,119,125],[101,117,121],[113,114,128],[117,120,124],[101,106,114],[101,108,122],[114,118,126]]),
([v144,v1,v2,v3,v11,v16],[],[0,3,5,7,8,9,15,24,30,34,42,52,54,59,80,81,84,89,91,96,106,108,114,116,117,127,128,184,193,223,224,225,235],[[103,104,109],[103,105,112],[100,103,117],[103,106,114],[103,107,127],[118,122],[101,108,111],[115,121,132],[124,126,130],[102,108,111],[115,116,120],[123,125,129],[108,113,115],[108,110,128],[115,119,131]]),
([v145,v0,v1,v17,v9,v3],[],[0,1,3,7,8,12,17,22,26,28,34,79,80,81,88,91,100,105,106,111,117,125,128,202,207,222,223,232],[[112],[111,113,120],[113,118],[113,116,126],[101,105,113],[103,104,110],[103,106,118],[103,108,124],[100,101,127],[114,115,117],[114,122,125],[101,102,109],[118,121,126],[101,118,119],[101,107,123]]),
([v0,v146,v1,v2,v147,v11],[],[0,1,3,5,7,8,9,11,12,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,111,114,116,181,184,223,224,225,235],[[104,110,128],[104,105,112],[104,106,114],[100,101,120],[104,107,116],[119,123,130],[126,129,131],[101,109,127],[117,122,131],[119,121,125],[101,102,111],[115,117,132],[101,103,113],[117,118,124],[101,108,117]]),
([v0,v148,v1,v3,v11,v16],[],[0,1,5,7,10,12,15,19,24,30,35,80,81,82,88,89,91,96,106,109,114,116,126,127,181,184,222,223,225,233],[[103,110],[103,104,110],[100,101,115],[103,106,111],[103,108,125],[114,116,120],[101,102,109],[112,118,119],[121,123,127],[101,109],[112,113,129],[116,122,126],[101,105,112],[101,107,124],[112,117,128]]),
([v0,v149,v1,v9,v3,v11],[],[1,3,7,8,12,22,28,29,35,40,79,80,81,88,89,100,106,109,114,116,120,128,202,222,223,225,235,247],[[102],[103,108,113],[108,125,127],[100,107,114],[108,109,111],[113,118],[119,124,125],[100,119,120],[112,116,117],[113,121,123],[100,101,106],[110,112,126],[100,105,122],[112,115,125],[100,104,112]]),
([v0,v150,v1,v9,v3,v11],[],[0,1,3,7,8,17,22,26,28,34,81,88,89,105,106,111,114,116,125,128,143,202,207,222,223,235,247],[[103,112],[103,104,109],[103,107,122],[100,101,112],[103,105,112],[111,116,117],[117,124,126],[101,117,120],[110],[111,119,123],[101,102,108],[111,113,125],[101,106,121],[114,118,124],[101,114,115]]),
([v0,v151,v1,v9,v3,v11],[],[1,3,7,12,15,22,28,79,81,87,88,89,100,106,114,116,117,120,128,142,202,222,223,235,247],[[102],[109,110,116],[111,122,124],[100,111,119],[104,108,111],[110,114,115],[115,122,124],[100,115,117],[108,113],[110,118,121],[100,101,106],[107,108,123],[100,105,120],[108,112,122],[100,103,108]]),
([v0,v152,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,110,129],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,123,131],[126,127,130],[101,109,128],[117,122,132],[119,121,125],[101,102,111],[115,117,133],[101,103,113],[117,118,124],[101,107,117]]),
([v0,v153,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,181,184,223,224,225,235],[[104,110,128],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,123,130],[126,129,131],[101,109,127],[117,122,131],[119,121,125],[101,102,111],[115,117,132],[101,103,113],[117,118,124],[101,107,117]]),
([v0,v154,v1,v9,v3,v11],[7],[0,1,3,7,8,12,15,22,26,28,34,79,80,81,88,89,100,106,114,116,120,202,207,222,223,235],[[103,119],[103,104,110],[103,108,122],[100,101,115],[103,106,112],[118],[0,119,124],[101,119,120],[117],[114,123,124],[101,102,109],[111,113,125],[101,107,121],[113,116,124],[101,105,113]]),
([v0,v155,v1,v2,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,34,52,56,79,80,81,88,89,100,109,116,117,235],[[103,112],[103,104,110],[103,108,112],[100,101,117],[103,106,114],[116,121],[120],[101,111],[115,119],[116,121],[101,102,109],[113,115,122],[101,107,111],[115,118,119],[101,105,115]]),
([v0,v5,v156,v17,v3,v16],[],[0,1,6,7,10,14,16,17,19,24,66,71,78,79,84,89,91,94,109,116,117,152,154,181,184,222,225,233,237,245,249],[[103,104,111],[103,106,112],[103,107,122],[100,101,115],[103,109,124],[113,114,120],[119,127,128],[101,102,110],[125,126,130],[113,116,118],[101,113],[113,117,126],[101,105,121],[126,129,130],[101,108,123]]),
([v0,v5,v156,v9,v3,v11],[],[0,1,6,7,10,12,15,22,26,66,71,79,87,88,89,114,116,140,202,207,222,225,235,245,247],[[103,104,110],[103,112,113],[103,108,119],[100,101,114],[103,106,114],[113,115,116],[116,120,121],[101,102,109],[116,122],[113,121],[101,113],[111],[101,107,118],[121,123,124],[101,105,117]]),
([v0,v5,v1,v9,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,33,34,37,67,72,79,80,81,84,88,89,106,114,116,125,202,207,223,225,247,252],[[103,112,114],[103,104,111],[103,108,126],[100,101,120],[103,106,116],[122],[123,127,128],[101,110,113],[117,118,121],[119,128,129],[101,102,109],[115,117,130],[101,107,125],[117,124,128],[101,105,117]]),
([v0,v5,v1,v27,v3,v11],[],[0,1,3,7,8,12,15,19,24,28,33,34,37,67,72,79,80,81,84,88,89,96,106,114,116,181,184,223,225,247,250],[[103,112,114],[103,104,111],[103,108,126],[100,101,120],[103,106,116],[123],[124,127,128],[101,110,113],[117,118,122],[119,128,129],[101,102,109],[115,117,130],[101,107,125],[117,121,128],[101,105,117]]),
([v0,v5,v1,v28,v3,v11],[],[0,1,3,7,8,12,15,22,24,28,33,34,37,67,72,79,80,81,84,88,89,106,114,116,125,127,202,207,223,225,247,252],[[103,112,114],[103,104,111],[103,108,127],[100,101,120],[103,106,116],[122],[123,125,128],[101,110,113],[117,118,121],[119,129,130],[101,102,109],[115,117,131],[101,107,126],[117,124,129],[101,105,117]]),
([v0,v5,v1,v6,v3,v16],[],[0,1,3,7,8,14,17,19,24,28,33,34,37,67,72,79,80,81,84,89,91,96,106,116,117,127,181,184,223,225,240,250],[[103,112,114],[103,104,111],[103,106,116],[100,101,119],[103,108,127],[124],[117,118,122],[101,110,113],[123,125,128],[115,117,131],[101,102,109],[120,129,130],[101,105,117],[117,121,129],[101,107,126]]),
([v0,v5,v1,v31,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,33,34,37,67,72,79,80,81,84,88,89,96,106,114,116,127,193,195,223,225,239,251],[[103,112,114],[103,104,111],[103,108,127],[100,101,120],[103,106,116],[123],[124,125,128],[101,110,113],[117,118,122],[119,129,130],[101,102,109],[115,117,131],[101,107,126],[117,121,129],[101,105,117]]),
([v0,v5,v1,v3,v32,v11],[],[0,1,3,7,8,12,15,22,24,28,33,34,37,67,72,79,80,81,84,88,89,106,114,116,125,178,181,184,223,225,247,252],[[103,112,114],[103,104,111],[100,101,120],[103,108,127],[103,106,116],[122],[101,110,113],[123,125,128],[117,118,121],[101,102,109],[119,129,130],[115,117,131],[101,107,126],[101,105,117],[117,124,129]]),
([v0,v5,v9,v157,v3,v11],[],[0,1,3,7,8,12,15,28,33,34,37,43,47,67,72,79,80,81,84,89,98,106,114,116,128,203,208,223,225,247],[[103,110,114],[103,112,126],[103,104,109],[100,101,119],[103,106,116],[123,124,127],[122],[101,108,113],[117,118,121],[129],[101,111,125],[117,120,128],[101,102,107],[115,117],[101,105,117]]),
([v0,v5,v9,v3,v158,v11],[],[1,2,3,6,7,10,15,26,67,71,76,79,80,81,84,87,88,89,106,113,114,116,125,179,203,207,222,225,247,252,256],[[104,105,109],[104,107,125],[101,102,117],[104,115,130],[104,106,112],[121,123,126],[102,103,108],[120],[113,114,118],[102,110,124],[116,127,128],[113,122,127],[100],[102,113,119],[111,113,129]]),
([v0,v5,v2,v6,v3,v16],[],[0,1,5,7,9,16,19,24,49,53,54,57,59,68,73,78,79,82,89,91,94,108,109,116,117,128,181,184,224,225],[[103,111,114],[103,104,110],[103,105,115],[100,101,118],[103,107,127],[123],[116,121,122],[101,109,113],[124,125,128],[116,117,122],[101,102,108],[119,129],[101,112,116],[116,120,129],[101,106,126]]),
([v0,v5,v2,v18,v11,v16],[],[0,1,5,7,9,12,13,19,24,49,53,54,57,68,73,79,85,112,113,116,121,130,181,184,224,225,232,235,247,249,250],[[103,112,114],[103,104,111],[100,101,126],[103,106,116],[103,108,123],[119],[101,110,113],[117,118,127],[120,121,124],[101,102,109],[118,130],[125,128],[101,105,115],[101,107,122],[118,125,129]]),
([v0,v5,v157,v3,v11,v16],[],[0,1,3,7,8,12,15,19,24,28,33,34,37,67,72,79,80,81,84,88,89,96,102,106,114,116,127,181,184,223,225,239],[[103,112,114],[103,104,111],[100,101,120],[103,106,116],[103,108,128],[124],[101,110,113],[117,118,123],[125,126,129],[101,102,109],[115,117],[119,122,131],[101,105,117],[101,107,127],[117,121,130]]),
([v0,v159,v1,v9,v3,v11],[],[0,1,3,5,7,8,9,12,15,22,26,28,34,49,54,79,80,81,84,88,89,91,106,114,116,125,202,207,223,224,225,252],[[104,106,114],[104,105,112],[104,110,127],[100,101,120],[104,108,116],[119,121,123],[124,128,130],[101,103,113],[117,118,122],[119,129,130],[101,102,111],[115,117,131],[101,109,126],[117,125,130],[101,107,117]]),
([v0,v160,v1,v9,v3,v11],[],[0,1,7,12,15,22,26,30,35,79,81,88,89,106,114,116,125,202,207,223,247,252],[[102,108],[102,108],[102,106,118],[100,101,112],[102,104,112],[114],[115,119,120],[101,107],[110,113,115],[111,119,120],[101,107],[109,111,121],[101,105,117],[113,116,119],[101,103,113]]),
([v0,v161,v1,v9,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,106,114,116,125,205,209,223,224,225,235],[[104,106,112],[104,105,110],[104,114,126],[100,101,120],[104,108,116],[119,122,123],[123,127,129],[101,103,111],[117,118,121],[119,128,129],[101,102,109],[115,117,130],[101,113,125],[117,124,129],[101,107,117]]),
([v0,v24,v2,v3,v11,v16],[],[0,1,3,5,7,9,12,15,19,24,49,54,57,68,73,79,81,84,88,91,96,102,109,114,181,184,224,225,232,235,247],[[104,112,114],[104,105,111],[100,101,128],[104,107,122],[104,109,125],[118,119,123],[101,102,113],[115,116,129],[118,121,126],[101,103,110],[116,117,122],[127,130],[101,106,116],[101,108,124],[116,120,127]]),
([v0,v162,v1,v3,v11,v16],[],[0,1,3,5,7,8,12,15,19,24,28,34,37,67,72,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,225,239,252],[[104,112,114],[104,105,111],[100,101,120],[104,107,116],[104,109,129],[119,121,125],[101,103,113],[117,118,124],[126,127,130],[101,102,110],[115,117,133],[119,123,132],[101,106,117],[101,108,128],[117,122,131]]),
([v0,v25,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,49,53,54,57,68,73,79,84,88,91,102,109,114,125,181,184,224,225,232,235,247,250],[[103,112,114],[103,104,111],[100,101,127],[103,106,120],[103,108,124],[117,118,121],[101,110,113],[115,117,128],[117,119,125],[101,102,109],[116,120,130],[126,129],[101,105,120],[101,107,123],[120,122,126]]),
([v0,v8,v1,v9,v3,v11],[],[0,1,7,8,12,15,22,26,30,35,37,81,83,88,100,106,116,202,207,223,225,232,247,252],[[102,109,110],[102,103,110],[102,107,118],[100,101,121],[102,105,112],[113],[116,119,120],[101,108],[111,115,123],[120,122],[101,108],[111,123],[101,106,117],[111,114,120],[101,104,111]]),
([v0,v8,v17,v3,v11,v16],[],[0,1,3,7,10,12,15,19,24,28,34,79,81,83,88,91,96,102,109,114,145,147,156,159,181,184,222,225,230,233,247,249],[[103,104,110],[103,121,123],[100,101,128],[103,106,113],[103,108,125],[114,115,119],[101,102,109],[111,112,129],[114,117,126],[101,120,122],[118],[127,130,131],[101,105,112],[101,107,124],[112,116,127]]),
([v0,v8,v9,v2,v3,v11],[],[0,1,3,5,7,9,12,15,28,34,49,54,57,63,65,79,81,84,88,91,109,114,125,128,205,209,224,225,232,235,247],[[104,109,112],[104,114,125],[104,105,111],[100,101,128],[104,107,120],[118,123,126],[118,119,121],[101,102,108],[115,116,129],[130],[101,113,124],[116,122,127],[101,103,110],[116,117,120],[101,106,116]]),
([v0,v8,v9,v54,v3,v11],[],[1,3,4,7,9,10,12,17,22,26,28,36,79,81,83,88,100,114,128,202,209,224,225,232,235],[[104,105,111],[104,109,120],[103],[100,102,123],[104,107,114],[115,118,121],[117],[100,101,110],[112,113,124],[],[100,108,119],[113,116,122],[100],[113],[100,106,113]]),
([v0,v8,v9,v3,v11],[],[0,1,3,7,10,12,15,22,26,28,30,34,37,79,81,83,88,100,109,114,128,143,146,167,171,202,207,213,215,222,225,232,235,247,252,256],[[103,104,111,112,116,119],[103,108,126,128,130,133],[100,101,103,131,135],[103,106,114,115,118,122],[116,120,129,130,132,133],[101,102,109,110,116,124],[113,114,116,132,134],[101,107,125,127,130,133],[114,117,130,133,134],[101,105,114,121,123]]),
([v0,v8,v9,v3,v11,v16],[],[0,1,3,7,10,12,15,19,24,28,34,79,81,83,88,96,102,181,184,189,191,211,214,225,232,233,235,238,243,250],[[103,104,110],[103,120,122],[100,101,124],[103,106,113],[103,108,118],[114,125,126],[101,102,109],[111,112,126],[114,116,126],[101,119,121],[112,128,129],[123],[101,105,112],[101,107,117],[112,115,127]]),
([v0,v8,v2,v26,v11,v16],[],[0,1,3,5,9,12,19,28,49,56,57,61,65,73,79,81,84,88,91,96,102,109,114,181,209,224,225,232,235,247,254],[[109,110,113],[104,109,130],[100,101,127],[109,111,121],[109,112,124],[117,118,122],[101,102,107],[114,115,128],[117,120,125],[101,103,108],[115,116,121],[126,129],[101,105,115],[101,106,123],[115,119,126]]),
([v0,v8,v2,v12,v3,v16],[],[0,1,3,5,7,9,12,19,24,28,34,49,54,57,61,79,81,84,88,91,96,102,109,117,181,184,224,225,232,235,247],[[104,110,113],[104,105,112],[104,114,122],[100,101,128],[104,108,125],[118,119,123],[115,116,129],[101,102,109],[118,121,126],[116,117,122],[101,103,111],[127,130],[101,106,116],[116,120,127],[101,107,124]]),
([v0,v8,v2,v55,v3,v11],[],[0,1,3,5,7,9,12,15,19,28,34,49,54,57,65,79,81,84,88,91,96,102,109,114,181,184,224,225,232,235,247],[[104,110,113],[104,105,112],[104,114,125],[100,101,128],[104,107,122],[118,119,123],[118,121,126],[101,102,109],[115,116,129],[127,130],[101,103,111],[116,117,122],[101,108,124],[116,120,127],[101,106,116]]),
([v0,v8,v2,v3,v11,v16],[],[0,1,3,5,7,9,12,15,19,24,28,34,49,54,57,79,81,84,88,91,96,102,109,114,181,184,224,225,232,235,247],[[104,111,114],[104,105,113],[100,101,128],[104,107,122],[104,109,125],[118,119,123],[101,102,110],[115,116,129],[118,121,126],[101,103,112],[116,117,122],[127,130],[101,106,116],[101,108,124],[116,120,127]]),
([v0,v8,v47,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,36,37,81,82,83,88,91,96,128,181,184,224,225,230,235,247,250],[[103,110,111],[103,104,111],[100,101,123],[103,106,114],[103,108,120],[115],[101,109],[112,113,124],[116,118,121],[101,102,109],[112,126],[122,125],[101,105,112],[101,107,119],[112,117,122]]),
([v0,v8,v46,v3,v11,v16],[],[0,1,5,7,8,12,15,19,24,30,35,37,81,82,83,88,91,96,127,181,184,223,225,230,234,247,250],[[103,110,111],[103,104,111],[100,101,123],[103,106,114],[103,108,120],[115],[101,109],[112,113,124],[116,118,121],[101,102,109],[112,126],[122,125],[101,105,112],[101,107,119],[112,117,122]]),
([v0,v8,v3,v163,v11,v16],[],[1,4,5,6,7,10,14,15,22,24,31,34,79,81,84,88,91,96,102,109,114,183,184,222,225,232,233,247,254],[[104,105,111],[101,102,125],[104,128],[104,107,119],[104,109,122],[102,103,110],[115,116,120],[112,113,126],[115,118,123],[100],[102,106,113],[102,108,121],[113,114,119],[124,127],[113,117,124]]),
([v0,v164,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,128],[119,121,125],[101,102,111],[115,117,132],[119,123,130],[101,103,113],[117,118,124],[126,129,131],[101,107,117],[101,109,127],[117,122,131]]),
([v0,v33,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,91,96,102,106,114,181,184,223,224,225,232,235],[[104,105,112],[104,106,114],[100,101,130],[104,108,116],[104,110,126],[119,120,124],[101,102,111],[115,117,131],[119,122,128],[101,103,113],[117,118,123],[127,129],[101,107,117],[101,109,125],[117,121,129]]),
([v0,v165,v1,v3,v11,v16],[],[1,3,5,7,10,12,19,28,32,37,49,54,60,64,79,81,83,88,91,96,102,106,116,127,181,196,223,225,230,234,239,252,255],[[103,109,111],[104,109,111],[100,108,128],[109,112,116],[109,113,125],[117,118,132],[100,102,110],[115,121,129],[122,123,126],[100,101,107],[114,115,131],[117,120,130],[100,105,115],[100,106,124],[115,119,127]]),
([v0,v166,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,81,84,88,91,93,96,102,109,114,172,178,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,123],[104,110,128],[118,119,124],[101,102,111],[115,116,132],[118,122,130],[101,103,113],[116,117,123],[125,126,129],[101,107,116],[101,109,127],[116,121,131]]),
([v0,v156,v1,v17,v9,v3],[],[0,1,3,7,8,14,17,22,26,28,34,40,79,80,81,89,100,106,116,202,207,222,223,235,249,252],[[103,111,113],[103,104,110],[103,106,118],[103,108,120],[100,101,115],[112],[114,117,118],[114,116,122],[101,114],[118,123,125],[121,122,124],[101,102,109],[118,122,124],[101,105,118],[101,107,119]]),
([v0,v156,v37,v3,v11,v16],[],[0,1,5,7,10,12,15,19,24,49,54,79,87,88,89,91,102,114,116,127,140,181,184,222,225,233,246,249],[[103,112,113],[103,104,110],[100,101,114],[103,106,114],[103,108,122],[113,115,117],[101,113],[111],[113,116,124],[101,102,109],[118,125],[118,119,123],[101,105,120],[101,107,121],[124,126,127]]),
([v0,v156,v52,v2,v3,v11],[],[0,1,5,7,9,12,15,19,25,49,54,79,87,88,89,91,102,114,116,121,127,140,181,184,222,224,227,234,246],[[103,112,113],[103,108,123],[103,104,110],[100,101,114],[103,106,114],[113,116,125],[113,115,117],[101,113,119],[111],[118,120,124],[101,107,122],[125,126,128],[101,102,109],[118,127],[101,105,121]]),
([v0,v1,v167,v2,v3,v16],[],[0,1,3,5,7,8,9,12,19,24,28,34,40,49,54,79,80,81,84,88,89,91,96,102,106,116,127,134,181,184,223,224,225,235],[[104,105,111],[104,112,116],[104,106,114],[100,101,120],[104,109,129],[115,117,133],[119,121,127],[101,102,110],[119,123,131],[117,118,124],[101,107,117],[117,122,132],[101,103,113],[125,126,130],[101,108,128]]),
([v0,v1,v168,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,34,46,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,193,195,223,224,225,252],[[104,105,111],[104,112,129],[104,106,114],[100,101,120],[104,108,116],[119,123,131],[119,121,125],[101,102,110],[115,117,133],[126,127,130],[101,109,128],[117,122,132],[101,103,113],[117,118,124],[101,107,117]]),
([v0,v1,v169,v2,v3,v16],[],[0,1,3,5,7,8,9,19,24,28,34,40,49,54,59,79,80,81,84,89,91,96,106,116,117,127,128,181,184,223,224,225,235],[[104,105,110],[104,111,116],[104,106,113],[100,101,119],[104,108,128],[115,117,132],[120,123,124],[101,102,109],[124,126,130],[117,118,122],[101,114,117],[117,121,131],[101,103,112],[123,125,129],[101,107,127]]),
([v0,v1,v170,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,42,46,49,54,79,80,81,84,88,89,91,96,106,114,116,127,128,193,195,223,224,225,252],[[104,105,110],[104,112,129],[104,106,114],[100,101,120],[104,108,116],[119,127,131],[119,121,124],[101,102,109],[115,117,133],[125,126,130],[101,111,128],[117,122,132],[101,103,113],[117,118,123],[101,107,117]]),
([v0,v1,v171,v9,v3,v11],[],[0,1,3,7,8,9,12,15,22,28,33,34,67,72,79,80,81,84,88,89,106,114,116,125,128,202,207,223,224,225,235,247],[[103,104,111],[103,105,113],[103,126,131],[100,101,119],[103,107,115],[118,121,122],[118,124,128],[101,102,109],[114,116,130],[122,127,129],[101,110,112],[116,117,120],[101,108,125],[116,123,129],[101,106,116]]),
([v0,v1,v172,v3,v11,v16],[],[0,1,3,7,8,12,15,19,24,28,33,34,37,67,72,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,225,239,253],[[103,104,111],[103,112,114],[100,101,120],[103,106,116],[103,108,129],[119,121,125],[101,102,109],[115,117,133],[119,123,132],[101,110,113],[117,118,124],[126,127,130],[101,105,117],[101,107,128],[117,122,131]]),
([v0,v1,v173,v37,v3,v11],[],[0,1,3,5,7,8,12,15,28,34,37,49,54,63,79,80,81,84,88,89,91,106,114,125,205,223,225,249,252],[[104,105,109],[104,126,127],[104,110,112],[100,101,119],[104,107,115],[118,126,127],[118,120,122],[101,102,108],[114,116,128],[125],[101,113,124],[116,123,126],[101,103,111],[116,117,121],[101,106,116]]),
([v0,v1,v173,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,79,80,81,84,88,89,91,106,114,125,205,209,223,224,225,249,252],[[104,105,110],[104,125,129],[104,106,112],[100,101,119],[104,108,115],[118,127,128],[118,120,122],[101,102,109],[114,116,130],[126],[101,113,124],[116,123,128],[101,103,111],[116,117,121],[101,107,116]]),
([v0,v1,v174,v3,v11,v16],[],[0,1,3,7,8,12,15,19,24,28,33,34,37,67,72,79,80,81,84,88,89,96,102,106,114,116,127,181,184,223,225,239,252],[[103,104,111],[103,112,114],[100,101,120],[103,106,116],[103,108,128],[119,124,125],[101,102,109],[115,117,132],[119,122,131],[101,110,113],[117,118,123],[125,126,129],[101,105,117],[101,107,127],[117,121,130]]),
([v0,v1,v37,v81,v11,v16],[],[0,1,3,5,8,12,19,28,35,37,40,46,49,72,79,80,81,84,87,88,89,91,96,102,106,114,116,127,181,195,223,225,239,252],[[104,108,118],[108,109,113],[100,101,120],[108,110,115],[108,111,129],[119,121,125],[101,102,107],[114,116,133],[119,123,132],[101,103,112],[116,117,124],[126,127,130],[101,105,116],[101,106,128],[116,122,131]]),
([v0,v1,v37,v45,v3,v16],[],[0,1,3,5,7,8,12,19,24,28,34,37,40,49,54,79,80,81,84,88,89,91,96,102,106,116,127,134,181,184,223,225,239,252],[[104,105,110],[104,111,114],[104,112,116],[100,101,120],[104,108,129],[119,121,127],[115,117,133],[101,102,109],[119,123,132],[117,118,124],[101,103,113],[125,126,130],[101,106,117],[117,122,131],[101,107,128]]),
([v0,v1,v37,v52,v3,v11],[],[0,1,3,5,7,8,12,15,19,28,34,37,46,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,225,239,252],[[104,105,110],[104,111,114],[104,112,129],[100,101,120],[104,107,116],[119,121,125],[119,123,132],[101,102,109],[115,117,133],[126,127,130],[101,103,113],[117,118,124],[101,108,128],[117,122,131],[101,106,117]]),
([v0,v1,v37,v9,v3,v11],[],[0,1,3,5,7,8,12,15,26,28,34,37,49,54,63,79,80,81,84,88,89,91,106,114,116,125,205,223,225,249,252],[[104,105,110],[104,111,113],[104,108,128],[100,101,120],[104,107,116],[119,121,123],[119,128,129],[101,102,109],[115,117,130],[124,127,128],[101,103,112],[117,118,122],[101,114,126],[117,125,128],[101,106,117]]),
([v0,v1,v37,v3,v11,v16],[],[0,1,3,5,7,8,12,15,19,24,28,34,37,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,225,239,252],[[104,105,111],[104,112,114],[100,101,120],[104,107,116],[104,109,129],[119,121,125],[101,102,110],[115,117,133],[119,123,132],[101,103,113],[117,118,124],[126,127,130],[101,106,117],[101,108,128],[117,122,131]]),
([v0,v1,v175,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,252],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v1,v176,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v1,v34,v2,v3,v16],[],[0,1,3,5,7,8,9,12,19,24,28,34,49,54,79,80,81,84,88,91,96,102,106,134,181,184,223,224,225,232,235],[[104,105,111],[104,115,116],[104,106,113],[100,101,129],[104,109,125],[114,116,130],[118,119,123],[101,102,110],[118,121,127],[116,117,122],[101,107,116],[116,120,128],[101,103,112],[126,128],[101,108,124]]),
([v0,v1,v177,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,181,184,223,224,225,249,252],[[104,105,111],[104,127,131],[104,106,113],[100,101,119],[104,108,115],[118,122,129],[118,120,124],[101,102,110],[114,116,132],[125,128,130],[101,109,126],[116,121,130],[101,103,112],[116,117,123],[101,107,116]]),
([v0,v1,v178,v9,v3,v11],[],[1,3,7,10,12,22,28,32,37,79,81,83,88,100,106,114,116,169,202,223,225,232,247,252],[[103,108,112],[102],[108,120,122],[100,107,121],[108,110,111],[112,115],[112,120,122],[100,101,106],[109,110,123],[116,119,120],[100,116,117],[110,114],[100,105,118],[110,113,120],[100,104,110]]),
([v0,v1,v179,v2,v3,v16],[],[0,1,3,5,7,8,9,19,24,28,34,40,49,54,59,79,80,81,84,89,91,96,106,116,127,136,181,184,223,224,225,235],[[104,105,110],[104,111,116],[104,106,113],[100,101,119],[104,108,127],[115,117,131],[120,123,125],[101,102,109],[125,129,130],[117,118,122],[101,114,117],[117,121,130],[101,103,112],[123,124,128],[101,107,126]]),
([v0,v1,v180,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,42,46,49,54,79,80,81,84,88,89,91,96,106,114,116,127,193,195,223,224,225,252],[[104,105,110],[104,112,128],[104,106,114],[100,101,120],[104,108,116],[119,130,131],[119,121,124],[101,102,109],[115,117,132],[125,126,129],[101,111,127],[117,122,131],[101,103,113],[117,118,123],[101,107,117]]),
([v0,v1,v81,v45,v2,v16],[],[0,1,3,5,8,12,19,28,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,116,127,134,181,195,223,225,239,252],[[104,108,118],[100,101,119],[108,110,115],[108,109,113],[108,111,128],[101,102,107],[114,116,132],[118,120,126],[118,122,131],[101,105,116],[101,103,112],[101,106,127],[116,117,123],[116,121,130],[124,125,129]]),
([v0,v1,v81,v52,v2,v11],[],[0,1,3,5,8,12,19,28,35,37,40,46,49,72,79,80,81,84,87,88,89,91,96,102,106,114,116,127,181,195,223,225,239,252],[[104,108,118],[100,101,120],[108,111,129],[108,109,113],[108,110,115],[101,102,107],[119,123,132],[119,121,125],[114,116,133],[101,106,128],[101,103,112],[101,105,116],[126,127,130],[116,122,131],[116,117,124]]),
([v0,v1,v181,v2,v3,v16],[],[0,1,3,5,7,8,9,19,24,28,34,40,49,54,79,80,81,84,89,96,102,106,113,116,127,181,184,223,224,225,233,235,244],[[104,105,110],[104,111,115],[104,106,113],[100,101,118],[104,108,126],[114,116,131],[123,130,132],[101,102,109],[120,128],[116,117,121],[101,116,122],[116,119,129],[101,103,112],[123,124,127],[101,107,125]]),
([v0,v1,v45,v52,v2,v3],[],[0,1,3,5,7,8,9,12,19,28,34,40,46,49,54,79,80,81,84,88,89,91,96,102,106,116,127,134,181,184,223,224,225,252],[[104,105,110],[104,111,116],[104,112,129],[104,106,114],[100,101,120],[115,117,133],[119,123,131],[119,121,127],[101,102,109],[117,122,132],[117,118,124],[101,107,117],[125,126,130],[101,108,128],[101,103,113]]),
([v0,v1,v45,v9,v2,v3],[],[0,1,3,5,7,8,9,12,28,34,40,49,54,63,65,79,80,81,84,88,89,91,106,125,134,205,209,223,224,225,235],[[104,105,109],[104,110,116],[104,114,126],[104,106,112],[100,101,120],[115,117,130],[119,128,129],[119,121,124],[101,102,108],[117,123,129],[117,118,122],[101,107,117],[127],[101,113,125],[101,103,111]]),
([v0,v1,v45,v2,v3,v16],[],[0,1,3,5,7,8,9,12,19,24,28,34,40,49,54,79,80,81,84,88,89,91,96,102,106,116,127,134,181,184,223,224,225,235],[[104,105,111],[104,112,116],[104,106,114],[100,101,120],[104,109,129],[115,117,133],[119,121,127],[101,102,110],[119,123,131],[117,118,124],[101,107,117],[117,122,132],[101,103,113],[125,126,130],[101,108,128]]),
([v0,v1,v182,v2,v3,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,108,116],[104,106,114],[100,101,120],[104,110,129],[115,117,133],[119,121,125],[101,102,111],[119,123,131],[117,118,124],[101,107,117],[117,122,132],[101,103,113],[126,127,130],[101,109,128]]),
([v0,v1,v183,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,42,46,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,193,195,223,224,225,253],[[104,105,110],[104,112,129],[104,106,114],[100,101,120],[104,108,116],[119,123,131],[119,121,125],[101,102,109],[115,117,133],[126,127,130],[101,111,128],[117,122,132],[101,103,113],[117,118,124],[101,107,117]]),
([v0,v1,v52,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,34,46,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,252],[[104,105,111],[104,112,129],[104,106,114],[100,101,120],[104,108,116],[119,123,131],[119,121,125],[101,102,110],[115,117,133],[126,127,130],[101,109,128],[117,122,132],[101,103,113],[117,118,124],[101,107,117]]),
([v0,v1,v184,v2,v3,v11],[],[1,3,7,8,12,22,28,29,35,40,52,54,56,79,80,81,88,89,100,109,114,116,117,223,225,252],[[103,108,112],[102,108,112],[108,111,112],[100,107,117],[108,109,114],[116,122],[116,120,122],[100,101,106],[113,115,125],[121,123,124],[100,110],[115,119],[100,105,110],[115,118,119],[100,104,115]]),
([v0,v1,v185,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,110,129],[104,106,114],[100,101,120],[104,108,116],[119,123,131],[119,121,125],[101,102,111],[115,117,133],[126,127,130],[101,109,128],[117,122,132],[101,103,113],[117,118,124],[101,107,117]]),
([v0,v1,v186,v2,v3,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,108,116],[104,106,114],[100,101,120],[104,110,129],[115,117,133],[119,121,125],[101,102,111],[119,123,131],[117,118,124],[101,107,117],[117,122,132],[101,103,113],[126,127,130],[101,109,128]]),
([v0,v1,v187,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,252],[[104,105,112],[104,110,129],[104,106,114],[100,101,120],[104,108,116],[119,123,131],[119,121,125],[101,102,111],[115,117,133],[126,127,130],[101,109,128],[117,122,132],[101,103,113],[117,118,124],[101,107,117]]),
([v0,v1,v188,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,128,205,209,223,224,225,235,249],[[104,105,110],[104,114,126],[104,106,112],[100,101,120],[104,108,116],[119,124,128],[119,121,123],[101,102,109],[115,117,130],[127],[101,113,125],[117,129,131],[101,103,111],[117,118,122],[101,107,117]]),
([v0,v1,v189,v9,v3,v11],[],[0,1,3,7,8,9,12,15,22,28,34,49,54,65,79,80,81,88,89,100,106,109,114,116,120,128,209,220,223,224,225,235],[[103,104,110],[103,105,112],[103,113,126],[100,101,118],[103,107,115],[117,122,123],[117,125,129],[101,102,109],[114,116,131],[123,128,130],[101,111,124],[116,120,121],[101,108,127],[116,119,130],[101,106,116]]),
([v0,v1,v190,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,88,89,91,96,102,106,109,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,119],[104,108,116],[104,110,129],[118,120,125],[101,102,111],[115,117,133],[118,122,131],[101,103,113],[117,123,124],[126,127,130],[101,107,117],[101,109,128],[117,121,132]]),
([v0,v1,v191,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,138,179,205,209,223,224,225,235],[[104,105,110],[104,114,127],[104,106,112],[100,101,120],[104,108,116],[119,125,129],[119,121,123],[101,102,109],[115,117,131],[128],[101,113,126],[117,124,130],[101,103,111],[117,118,122],[101,107,117]]),
([v0,v1,v192,v9,v3,v11],[],[0,1,3,7,8,9,12,15,22,28,33,34,49,54,65,79,80,81,84,88,89,106,114,116,125,179,209,220,223,224,225,235],[[103,104,111],[103,105,113],[103,114,126],[100,101,120],[103,107,116],[119,122,123],[119,125,129],[101,102,109],[115,117,131],[123,128,130],[101,110,112],[117,118,121],[101,108,127],[117,124,130],[101,106,117]]),
([v0,v1,v193,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v1,v17,v2,v18,v16],[],[0,1,3,5,7,8,9,19,24,28,34,49,54,59,61,109,111,112,113,121,130,181,184,223,224,225,232,233,235,249],[[104,105,110],[104,114,118],[104,106,112],[100,101,126],[104,108,122],[117,118,128],[119,127],[101,102,109],[119,120,124],[116],[101,113,115],[118,125,129],[101,103,111],[123,125],[101,107,121]]),
([v0,v1,v17,v89,v3,v11],[],[0,1,3,7,8,12,15,19,24,28,34,79,80,81,88,89,91,100,102,106,114,116,120,147,181,184,222,223,233,249],[[103,104,110],[103,121,123],[103,108,125],[100,101,115],[103,106,112],[114,116,120],[114,118,126],[101,102,109],[111,113,128],[121,127,129],[101,121,122],[119],[101,107,124],[113,117,127],[101,105,113]]),
([v0,v1,v17,v55,v3,v11],[],[0,1,3,7,8,12,15,19,26,28,34,79,80,81,88,89,91,96,102,106,114,116,120,147,181,184,222,223,235,249],[[103,104,110],[103,121,123],[103,108,125],[100,101,115],[103,106,112],[114,116,120],[114,118,126],[101,102,109],[111,113,128],[121,127,129],[101,121,122],[119],[101,107,124],[113,117,127],[101,105,113]]),
([v0,v1,v9,v2,v12,v3],[],[0,1,3,5,7,8,9,12,28,34,49,54,61,63,65,79,80,81,84,88,91,106,117,125,128,205,209,223,224,225,232,235],[[104,105,109],[104,114,126],[104,106,111],[104,112,116],[100,101,130],[119,124,128],[119,120,122],[115,117,131],[101,102,108],[127],[117,123,129],[101,113,125],[117,118,121],[101,103,110],[101,107,117]]),
([v0,v1,v9,v2,v19,v3],[],[0,1,3,5,7,8,9,28,34,40,49,54,63,65,79,80,81,84,89,106,113,116,125,128,205,209,223,224,225,235],[[104,105,108],[104,113,125],[104,106,111],[104,109,115],[100,101,118],[123,127],[121,129],[114,116,129],[101,102,107],[126],[116,122,128],[101,112,124],[116,117,119],[101,103,110],[101,116,120]]),
([v0,v1,v9,v2,v6,v3],[],[0,1,3,5,7,8,9,28,34,40,49,54,59,63,65,79,80,81,84,89,91,106,116,117,125,128,205,209,223,224,225,235],[[104,105,108],[104,114,127],[104,106,111],[104,109,116],[100,101,119],[123,125,129],[120,122,123],[115,117,131],[101,102,107],[128],[117,124,130],[101,113,126],[117,118,121],[101,103,110],[101,112,117]]),
([v0,v1,v9,v2,v147,v11],[],[0,1,3,5,7,8,9,11,12,28,34,49,54,63,65,79,80,81,84,88,89,91,111,114,128,138,205,209,223,224,225,235],[[104,105,110],[104,114,127],[104,106,112],[100,101,120],[104,107,116],[119,124,129],[119,121,123],[101,102,109],[115,117,131],[128],[101,113,126],[117,125,130],[101,103,111],[117,118,122],[101,108,117]]),
([v0,v1,v9,v2,v18,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,81,86,111,112,113,116,119,121,130,205,209,223,224,225,232,235,249],[[104,105,110],[104,114,125],[104,106,112],[100,101,129],[104,108,116],[122,123,127],[120,121],[101,102,109],[118,119,130],[126],[101,113,124],[119,128,131],[101,103,111],[117,119],[101,107,115]]),
([v0,v1,v9,v2,v194,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,125,177,205,209,223,224,225,235],[[104,105,110],[104,114,127],[104,106,112],[100,101,120],[104,108,116],[119,125,129],[119,121,123],[101,102,109],[115,117,131],[128],[101,113,126],[117,124,130],[101,103,111],[117,118,122],[101,107,117]]),
([v0,v1,v9,v195,v3,v11],[],[0,1,7,8,9,15,34,49,50,54,58,63,65,66,79,81,83,88,100,106,114,128,169,202,209,223,224,225,232,235],[[102,103,106],[102,112,124],[102,104,109],[100,102,128],[102,105,116],[117,121,126],[117,120],[107,108,113],[114,115,129],[125],[107,111,123],[115,118,127],[101,107,122],[115,119],[107,110,115]]),
([v0,v1,v9,v196,v3,v11],[],[1,4,6,7,9,10,12,17,22,26,30,34,35,80,81,84,88,89,106,108,114,117,125,128,202,209,223,224,225,235],[[104,105,111],[104,109,125],[103,104,112],[100,101,117],[104,107,113],[121,123,127],[116,120],[100,102,110],[114,119,129],[126],[100,108,124],[114,122,128],[100,110],[114,115,118],[100,106,114]]),
([v0,v1,v9,v197,v3,v11],[],[0,1,3,7,8,22,26,28,34,40,79,80,81,88,89,100,106,114,116,120,128,143,146,202,207,222,223,235,247],[[103,104,108],[103,106,124],[103,118,122],[100,101,114],[103,109,111],[117,120,125],[113,117,118],[101,102,107],[110,112,127],[118,126,128],[101,105,123],[112,115,126],[101,118,119],[116],[101,112,121]]),
([v0,v1,v9,v198,v3,v11],[],[0,1,3,5,7,8,9,28,34,40,49,54,58,63,65,79,80,81,84,88,89,106,114,116,125,128,205,209,223,224,225,235],[[104,105,108],[104,114,127],[104,106,111],[100,101,120],[104,109,116],[122,125,129],[119,122,123],[101,102,107],[115,117,131],[128],[101,113,126],[117,124,130],[101,103,110],[117,118,121],[101,112,117]]),
([v0,v1,v9,v199,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,125,128,205,209,223,224,225,235],[[104,105,110],[104,114,127],[104,106,112],[100,101,120],[104,108,116],[119,125,129],[119,121,123],[101,102,109],[115,117,131],[128],[101,113,126],[117,124,130],[101,103,111],[117,118,122],[101,107,117]]),
([v0,v1,v9,v47,v3,v11],[],[0,1,5,7,8,9,12,15,30,35,36,44,65,81,82,83,88,91,100,106,128,205,209,223,224,225,232,235],[[103,104,110],[103,112,122],[103,105,109],[100,101,126],[103,107,115],[117,120,124],[116,117],[101,108],[113,114,127],[123],[101,111,121],[113,118,125],[101,102,108],[113,119],[101,106,113]]),
([v0,v1,v9,v26,v54,v11],[],[1,3,4,9,10,12,17,22,26,28,36,79,81,83,88,89,100,106,114,128,169,202,209,224,225,232,235,258],[[103,104,110],[103,108,122],[100,102,125],[115],[103,106,113],[114,119,123],[100,101,109],[114,118],[111,112,126],[100,107,121],[127],[112,116,124],[120],[100,105,112],[112,117]]),
([v0,v1,v9,v12,v54,v3],[],[1,3,4,7,9,10,12,17,22,26,28,36,79,81,83,88,100,106,128,202,209,223,224,225,232,235],[[104,105,111],[104,109,120],[104,107,114],[103],[100,102,124],[115,118,122],[112,113,125],[115],[100,101,110],[113,116,123],[121],[100,108,119],[117],[100,106,113],[100]]),
([v0,v1,v9,v12,v3],[],[0,1,3,7,8,12,17,22,26,28,30,34,35,79,80,81,88,100,106,117,128,143,147,165,173,202,207,213,215,222,223,232,235,247,252,256],[[103,104,111,112,116,119],[103,108,126,128,130,133],[103,106,114,115,118,122],[100,101,103,131,135],[116,120,129,130,132,133],[113,115,116,132,134],[101,102,109,110,116,124],[115,117,130,133,134],[101,107,125,127,130,133],[101,105,115,121,123]]),
([v0,v1,v9,v12,v3,v11],[],[0,1,3,7,8,15,22,26,28,34,81,88,89,114,116,120,128,143,147,202,207,222,223,226,232,235,247],[[103,104,109],[103,107,120],[103,112,118],[100,101,124],[103,105,118],[111,116,121],[111,113,125],[101,102,108],[111,125],[114,122,126],[101,106,119],[122,123,126],[101,114,115],[110],[101,117]]),
([v0,v1,v9,v12,v3,v16],[],[0,1,3,7,8,12,17,19,24,28,34,79,80,81,88,96,102,181,184,189,191,211,214,223,232,233,234,235,238,243],[[103,104,110],[103,120,122],[103,106,112],[100,101,124],[103,108,118],[114,125,126],[111,113,127],[101,102,109],[114,116,127],[113,126,129],[101,119,121],[123],[101,105,113],[113,115,128],[101,107,117]]),
([v0,v1,v9,v200,v3,v11],[],[1,3,7,12,17,22,28,79,81,88,90,100,106,114,115,116,128,144,147,150,169,202,222,223,232,235,247],[[109,110,114],[118,119,123],[102],[100,117,124],[104,108,118],[109,116,122],[109,113,125],[100,101,106],[107,108,125],[115,123,126],[100,105,121],[108,111,123],[100,115,120],[108,112],[100,103,108]]),
([v0,v1,v9,v201,v3,v11],[],[0,1,3,5,7,8,9,15,28,34,49,54,58,63,65,81,82,83,84,88,100,114,128,205,209,223,224,225,232,235],[[104,105,109],[104,114,124],[104,106,111],[100,101,128],[104,107,117],[119,122,126],[119,121],[101,102,108],[116,118,129],[125],[101,113,123],[118,120,127],[101,103,110],[115,118],[101,112,118]]),
([v0,v1,v9,v202,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,125,128,205,209,223,224,225,235],[[104,105,110],[104,114,127],[104,106,112],[100,101,120],[104,108,116],[119,125,129],[119,121,123],[101,102,109],[115,117,131],[128],[101,113,126],[117,124,130],[101,103,111],[117,118,122],[101,107,117]]),
([v0,v1,v9,v54,v3,v11],[],[1,3,4,7,9,10,12,17,22,26,28,36,79,81,83,88,100,106,114,116,128,169,202,209,223,224,225,232,235],[[104,105,111],[104,109,123],[103],[100,102,127],[104,107,114],[115,120,125],[115,118],[100,101,110],[112,113,128],[124],[100,108,122],[113,116,126],[100,119,121],[113,117],[100,106,113]]),
([v0,v1,v9,v23,v3,v11],[],[0,1,6,7,10,12,15,30,35,44,80,81,84,88,89,100,105,106,114,116,213,215,223,225,235],[[103,104,108],[103,121],[103,108],[100,101,114],[103,106,110],[118,122,124],[113,118,119],[101,102,107],[111,116,124],[123],[101,109,120],[111,115,122],[101,107],[111,112,117],[101,105,111]]),
([v0,v1,v2,v203,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,34,49,54,65,79,80,81,84,88,89,91,102,106,114,116,125,205,209,223,224,225,235],[[104,105,111],[104,106,113],[104,114,128],[100,101,120],[104,108,116],[119,121,124],[119,122,130],[101,102,110],[115,117,132],[125,129,131],[101,103,112],[117,118,123],[101,109,127],[117,126,131],[101,107,117]]),
([v0,v1,v2,v204,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,116,125,127,128,205,209,223,224,225,235],[[104,105,110],[104,106,112],[104,114,129],[100,101,120],[104,108,116],[119,121,123],[119,127,131],[101,102,109],[115,117,133],[124,126,130],[101,103,111],[117,118,122],[101,113,128],[117,125,132],[101,107,117]]),
([v0,v1,v2,v35,v3,v16],[],[0,1,3,5,7,8,9,12,19,24,28,34,49,54,61,79,80,81,84,88,91,96,102,106,117,181,184,223,224,225,232,235],[[104,105,111],[104,106,113],[104,114,116],[100,101,130],[104,109,126],[119,120,124],[115,117,131],[101,102,110],[119,122,128],[117,118,123],[101,103,112],[127,129],[101,107,117],[117,121,129],[101,108,125]]),
([v0,v1,v2,v205,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,34,49,54,65,79,80,81,84,88,89,91,96,102,106,114,116,205,209,223,224,225,235],[[104,105,111],[104,106,113],[104,114,128],[100,101,120],[104,108,116],[119,121,125],[119,123,130],[101,102,110],[115,117,132],[126,129,131],[101,103,112],[117,118,124],[101,109,127],[117,122,131],[101,107,117]]),
([v0,v1,v2,v206,v3,v16],[],[0,1,3,5,7,8,9,19,24,28,34,49,54,59,61,79,80,81,84,89,91,96,106,116,117,127,128,181,184,223,224,225,235],[[104,105,110],[104,106,112],[104,114,116],[100,101,119],[104,108,128],[120,123,124],[115,117,132],[101,102,109],[124,126,130],[117,118,122],[101,103,111],[123,125,129],[101,113,117],[117,121,131],[101,107,127]]),
([v0,v1,v2,v207,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,42,49,54,65,79,80,81,84,88,89,91,96,106,114,116,127,128,205,209,223,224,225,235],[[104,105,110],[104,106,113],[104,114,129],[100,101,120],[104,108,116],[119,121,124],[119,127,131],[101,102,109],[115,117,133],[125,126,130],[101,103,112],[117,118,123],[101,111,128],[117,122,132],[101,107,117]]),
([v0,v1,v2,v20,v3,v11],[],[0,1,5,7,8,9,12,15,28,30,34,49,54,65,80,81,84,88,89,106,116,124,128,130,167,172,173,205,235],[[103,104,110],[103,105,112],[103,113,118],[100,101,118],[103,107,114],[120,122],[117,122,126],[101,108,123],[115,121,128],[120,125],[101,102,111],[115,116,119],[101,109,127],[115,124],[101,106,115]]),
([v0,v1,v2,v82,v3,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,63,79,80,81,84,88,89,91,106,114,116,125,128,205,209,223,224,225,235],[[104,105,111],[104,106,113],[104,109,128],[100,101,120],[104,108,116],[119,121,123],[119,126,130],[101,102,110],[115,117,132],[124,129,131],[101,103,112],[117,118,122],[101,114,127],[117,125,131],[101,107,117]]),
([v0,v1,v2,v208,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,34,49,54,65,79,80,81,84,88,89,91,102,106,114,116,125,181,184,223,224,225,235],[[104,105,111],[104,106,113],[104,114,128],[100,101,120],[104,108,116],[119,121,124],[119,122,130],[101,102,110],[115,117,132],[125,129,131],[101,103,112],[117,118,123],[101,109,127],[117,126,131],[101,107,117]]),
([v0,v1,v2,v209,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,102,106,114,116,125,205,209,223,224,225,235],[[104,105,110],[104,106,112],[104,114,128],[100,101,120],[104,108,116],[119,121,124],[119,122,130],[101,102,109],[115,117,132],[125,129,131],[101,103,111],[117,118,123],[101,113,127],[117,126,131],[101,107,117]]),
([v0,v1,v2,v89,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,125,181,184,223,224,225,235],[[104,105,112],[104,106,114],[104,110,128],[100,101,120],[104,108,116],[119,121,124],[119,122,130],[101,102,111],[115,117,132],[125,129,131],[101,103,113],[117,118,123],[101,109,127],[117,126,131],[101,107,117]]),
([v0,v1,v2,v210,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,181,184,223,224,225,235],[[104,105,112],[104,106,114],[104,110,128],[100,101,120],[104,108,116],[119,121,125],[119,123,130],[101,102,111],[115,117,132],[126,129,131],[101,103,113],[117,118,124],[101,109,127],[117,122,131],[101,107,117]]),
([v0,v1,v2,v211,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,46,49,54,63,79,80,81,84,88,89,91,106,114,116,125,127,128,205,209,223,224,225,235],[[104,105,110],[104,106,113],[104,111,129],[100,101,120],[104,108,116],[119,121,123],[119,127,131],[101,102,109],[115,117,133],[124,126,130],[101,103,112],[117,118,122],[101,114,128],[117,125,132],[101,107,117]]),
([v0,v1,v2,v212,v3,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,79,80,81,84,88,89,91,106,114,116,125,127,128,220,223,224,225,235],[[104,105,111],[104,106,113],[104,109,130],[100,101,119],[104,108,115],[118,120,122],[118,126,129],[101,102,110],[114,116,131],[123,125,128],[101,103,112],[116,117,121],[101,127,130],[116,124,130],[101,107,116]]),
([v0,v1,v2,v213,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,116,125,127,128,205,209,223,224,225,235],[[104,105,110],[104,106,112],[104,114,129],[100,101,120],[104,108,116],[119,121,123],[119,127,131],[101,102,109],[115,117,133],[124,126,130],[101,103,111],[117,118,122],[101,113,128],[117,125,132],[101,107,117]]),
([v0,v1,v2,v214,v3,v11],[7],[0,1,3,5,7,8,9,12,28,34,49,54,63,65,79,80,81,84,88,91,109,114,116,117,125,205,209,223,227,232],[[104,105,109],[104,106,111],[104,113,126],[100,101,129],[104,115,116],[118,119,121],[118,123],[101,102,108],[114,116,128],[0,122,127],[101,103,110],[116,117,124],[101,112,125],[116,120,124],[101,107,116]]),
([v0,v1,v2,v28,v3,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,63,79,80,81,84,88,89,91,106,114,116,125,127,128,205,209,223,224,225,235],[[104,105,111],[104,106,113],[104,109,129],[100,101,120],[104,108,116],[119,121,123],[119,127,131],[101,102,110],[115,117,133],[124,126,130],[101,103,112],[117,118,122],[101,114,128],[117,125,132],[101,107,117]]),
([v0,v1,v2,v215,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,106,114,116,127,128,181,184,223,224,225,235],[[104,105,112],[104,106,114],[104,110,129],[100,101,120],[104,108,116],[119,121,124],[119,127,131],[101,102,111],[115,117,133],[125,126,130],[101,103,113],[117,118,123],[101,109,128],[117,122,132],[101,107,117]]),
([v0,v1,v2,v216,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,125,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[104,110,129],[100,101,120],[104,108,116],[119,121,124],[119,122,131],[101,102,111],[115,117,133],[125,127,130],[101,103,113],[117,118,123],[101,109,128],[117,126,132],[101,107,117]]),
([v0,v1,v2,v29,v3,v16],[],[0,1,3,5,7,8,9,19,24,28,34,49,54,59,61,79,80,81,84,91,96,106,117,128,181,184,223,224,225,232,233,235],[[104,105,110],[104,106,112],[104,114,116],[100,101,129],[104,108,125],[119,122,130],[115,117,131],[101,102,109],[122,123,127],[117,118,121],[101,103,111],[126,128],[101,113,117],[117,120,128],[101,107,124]]),
([v0,v1,v2,v30,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,42,49,54,65,79,80,81,84,88,89,91,96,106,114,116,128,193,195,223,224,225,235],[[104,105,110],[104,106,113],[104,114,128],[100,101,120],[104,108,116],[119,121,124],[119,126,130],[101,102,109],[115,117,132],[125,129,131],[101,103,112],[117,118,123],[101,111,127],[117,122,131],[101,107,117]]),
([v0,v1,v2,v21,v3,v11],[],[0,1,5,7,8,9,12,15,30,35,49,54,65,77,81,84,88,106,108,109,114,116,117,128,221,223,225,235],[[103,104,113],[103,105,111],[103,109,112],[100,101,124],[103,107,119],[120,121],[116,122,123],[101,108],[114,118,127],[121,125,126],[101,102,110],[114,115,117],[101,108],[114,119],[101,106,114]]),
([v0,v1,v2,v26,v12,v16],[],[0,1,3,5,9,12,19,28,49,56,57,61,65,73,79,80,81,84,88,91,96,102,106,117,181,209,224,225,232,235,247,255],[[109,110,113],[104,109,131],[100,101,128],[109,111,115],[109,112,125],[118,119,123],[101,102,107],[114,116,129],[118,121,126],[101,103,108],[116,117,122],[127,130],[101,105,116],[101,106,124],[116,120,127]]),
([v0,v1,v2,v26,v55,v11],[],[0,1,3,5,9,12,19,28,49,56,57,61,65,73,79,80,81,84,88,89,91,96,102,106,114,116,181,209,224,225,235,247],[[109,110,113],[104,109,119],[100,101,119],[109,112,127],[109,111,115],[118,120,124],[101,102,107],[118,122,128],[114,116,130],[101,103,108],[125,129,131],[116,117,123],[101,106,126],[101,105,116],[116,121,129]]),
([v0,v1,v2,v12,v55,v3],[],[0,1,3,5,7,8,9,12,19,28,34,49,54,61,65,79,80,81,84,88,91,96,102,106,117,181,184,223,224,225,232,235],[[104,105,110],[104,106,112],[104,113,116],[104,114,126],[100,101,130],[119,120,124],[115,117,131],[119,122,128],[101,102,109],[117,118,123],[127,129],[101,103,111],[117,121,129],[101,107,117],[101,108,125]]),
([v0,v1,v2,v12,v3,v16],[],[0,1,3,5,7,8,9,12,19,24,28,34,49,54,61,79,80,81,84,88,91,96,102,106,117,181,184,223,224,225,232,235],[[104,105,111],[104,106,113],[104,114,116],[100,101,130],[104,109,126],[119,120,124],[115,117,131],[101,102,110],[119,122,128],[117,118,123],[101,103,112],[127,129],[101,107,117],[117,121,129],[101,108,125]]),
([v0,v1,v2,v217,v3,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,181,184,223,224,225,235],[[104,105,112],[104,106,114],[104,108,116],[100,101,120],[104,110,128],[119,121,125],[115,117,132],[101,102,111],[119,123,130],[117,118,124],[101,103,113],[126,129,131],[101,107,117],[117,122,131],[101,109,127]]),
([v0,v1,v2,v218,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,102,106,114,116,125,205,209,223,224,225,235],[[104,105,110],[104,106,112],[104,114,128],[100,101,120],[104,108,116],[119,121,124],[119,122,130],[101,102,109],[115,117,132],[125,129,131],[101,103,111],[117,118,123],[101,113,127],[117,126,131],[101,107,117]]),
([v0,v1,v2,v55,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,34,49,54,65,79,80,81,84,88,89,91,96,102,106,114,116,181,184,223,224,225,235],[[104,105,111],[104,106,113],[104,114,128],[100,101,120],[104,108,116],[119,121,125],[119,123,130],[101,102,110],[115,117,132],[126,129,131],[101,103,112],[117,118,124],[101,109,127],[117,122,131],[101,107,117]]),
([v0,v1,v2,v219,v3,v11],[],[1,3,7,12,22,26,28,51,52,54,56,57,61,65,73,79,81,88,100,106,109,114,116,117,223,225,232,235],[[110,111,114],[105,109],[102,110,113],[100,107,126],[110,112,120],[117,121,122],[117,123],[100,101,106],[115,116,127],[122,124,125],[100,104,108],[116,118,119],[100,108],[116,120],[100,103,116]]),
([v0,v1,v2,v220,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,181,184,223,224,225,235],[[104,105,112],[104,106,114],[104,110,128],[100,101,120],[104,108,116],[119,121,125],[119,123,130],[101,102,111],[115,117,132],[126,129,131],[101,103,113],[117,118,124],[101,109,127],[117,122,131],[101,107,117]]),
([v0,v1,v2,v36,v3,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,91,96,102,106,114,181,184,223,224,225,232,235],[[104,105,112],[104,106,114],[104,108,116],[100,101,130],[104,110,126],[119,120,124],[115,117,131],[101,102,111],[119,122,128],[117,118,123],[101,103,113],[127,129],[101,107,117],[117,121,129],[101,109,125]]),
([v0,v1,v2,v221,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,181,184,223,224,225,235],[[104,105,112],[104,106,114],[104,110,128],[100,101,120],[104,108,116],[119,121,125],[119,123,130],[101,102,111],[115,117,132],[126,129,131],[101,103,113],[117,118,124],[101,109,127],[117,122,131],[101,107,117]]),
([v0,v1,v2,v19,v3,v16],[],[0,1,3,5,7,8,9,19,24,28,34,40,49,54,79,80,81,84,89,96,106,113,116,127,128,181,184,223,224,225,233,235],[[104,105,110],[104,106,113],[104,111,115],[100,101,118],[104,108,126],[122,130],[114,116,131],[101,102,109],[124,128],[116,117,120],[101,103,112],[122,123,127],[101,116,121],[116,119,129],[101,107,125]]),
([v0,v1,v2,v6,v31,v3],[],[0,1,3,5,7,8,9,28,34,40,42,46,49,54,59,79,80,81,84,89,91,96,106,116,117,127,128,193,195,223,224,225,235],[[104,105,108],[104,106,113],[104,109,116],[104,111,128],[100,101,119],[120,123,124],[115,117,132],[124,126,130],[101,102,107],[117,118,122],[123,125,129],[101,103,112],[117,121,131],[101,114,117],[101,110,127]]),
([v0,v1,v2,v6,v3,v16],[],[0,1,3,5,7,8,9,19,24,28,34,40,49,54,59,79,80,81,84,89,91,96,106,116,117,127,128,181,184,223,224,225,235],[[104,105,110],[104,106,113],[104,111,116],[100,101,119],[104,108,128],[120,123,124],[115,117,132],[101,102,109],[124,126,130],[117,118,122],[101,103,112],[123,125,129],[101,114,117],[117,121,131],[101,107,127]]),
([v0,v1,v2,v222,v3,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,106,114,116,127,128,181,184,223,224,225,235],[[104,105,112],[104,106,114],[104,108,116],[100,101,120],[104,110,129],[119,121,124],[115,117,133],[101,102,111],[119,127,131],[117,118,123],[101,103,113],[125,126,130],[101,107,117],[117,122,132],[101,109,128]]),
([v0,v1,v2,v223,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,42,46,49,54,79,80,81,84,88,89,91,96,106,114,116,127,128,193,195,223,224,225,237],[[104,105,110],[104,106,114],[104,112,129],[100,101,120],[104,108,116],[119,121,124],[119,127,131],[101,102,109],[115,117,133],[125,126,130],[101,103,113],[117,118,123],[101,111,128],[117,122,132],[101,107,117]]),
([v0,v1,v2,v224,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,116,125,127,128,205,209,223,224,225,235],[[104,105,110],[104,106,112],[104,114,129],[100,101,120],[104,108,116],[119,121,123],[119,127,131],[101,102,109],[115,117,133],[124,126,130],[101,103,111],[117,118,122],[101,113,128],[117,125,132],[101,107,117]]),
([v0,v1,v2,v22,v3,v11],[7],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,81,88,89,100,116,124,125,128,205,223,225,235,249],[[104,105,110],[104,106,112],[104,114,117],[100,101,117],[104,108,117],[119,122],[116,122,127],[101,102,109],[120,121,126],[0,119,124],[101,103,111],[118,119,121],[101,113,123],[115,121,125],[101,107,121]]),
([v0,v1,v2,v31,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,42,46,49,54,79,80,81,84,88,89,91,96,106,114,116,127,128,193,195,223,224,225,235],[[104,105,110],[104,106,114],[104,112,129],[100,101,120],[104,108,116],[119,121,124],[119,127,131],[101,102,109],[115,117,133],[125,126,130],[101,103,113],[117,118,123],[101,111,128],[117,122,132],[101,107,117]]),
([v0,v1,v2,v23,v3,v11],[],[0,1,5,7,9,12,15,30,35,49,54,80,81,88,89,100,108,109,114,116,117,128,223,225,235],[[103,108],[103,104,110],[103,108],[100,101,114],[103,106,111],[118,120],[113,120,121],[101,107],[112,116,124],[119,122,123],[101,102,109],[112,115,117],[101,107],[112,117],[101,105,112]]),
([v0,v1,v2,v225,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,106,114,116,127,128,181,184,223,224,225,235],[[104,105,112],[104,106,114],[104,110,129],[100,101,120],[104,108,116],[119,121,124],[119,127,131],[101,102,111],[115,117,133],[125,126,130],[101,103,113],[117,118,123],[101,109,128],[117,122,132],[101,107,117]]),
([v0,v1,v2,v226,v3,v16],[],[0,1,3,5,7,8,9,15,19,24,28,34,49,54,59,79,80,81,84,89,91,96,106,114,116,117,127,128,181,184,223,224,225,235],[[104,105,111],[104,106,113],[104,107,116],[100,101,119],[104,109,129],[120,123],[115,117,133],[101,102,110],[125,127,131],[117,118,122],[101,103,112],[124,126,130],[101,114,117],[117,121,132],[101,108,128]]),
([v0,v1,v2,v227,v3,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,42,49,54,79,80,81,84,88,89,91,96,106,114,116,127,128,193,195,223,224,225,235],[[104,105,111],[104,106,114],[104,109,129],[100,101,120],[104,108,116],[119,121,124],[119,127,131],[101,102,110],[115,117,133],[125,126,130],[101,103,113],[117,118,123],[101,112,128],[117,122,132],[101,107,117]]),
([v0,v1,v2,v228,v3,v16],[],[0,1,3,5,7,8,9,12,19,24,28,34,40,49,54,79,80,81,84,88,89,91,96,102,106,116,117,127,181,184,223,224,225,235],[[104,105,111],[104,106,114],[104,112,116],[100,101,120],[104,109,129],[119,121,126],[115,117,133],[101,102,110],[119,123,131],[117,118,124],[101,103,113],[125,127,130],[101,107,117],[117,122,132],[101,108,128]]),
([v0,v1,v2,v229,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,34,46,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,111],[104,106,114],[104,112,129],[100,101,120],[104,108,116],[119,121,125],[119,123,131],[101,102,110],[115,117,133],[126,127,130],[101,103,113],[117,118,124],[101,109,128],[117,122,132],[101,107,117]]),
([v0,v1,v2,v3,v230,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,178,181,184,223,224,225,235,249],[[104,105,112],[104,106,114],[100,101,120],[104,110,128],[104,108,116],[119,121,124],[101,102,111],[119,122,130],[115,117,132],[101,103,113],[125,126,129],[117,118,123],[101,109,127],[101,107,117],[117,131,133]]),
([v0,v1,v2,v3,v231,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,63,79,80,81,84,88,89,91,106,114,116,128,178,181,184,223,224,225,235,249],[[104,105,111],[104,106,113],[100,101,120],[104,109,128],[104,108,116],[119,121,123],[101,102,110],[119,125,130],[115,117,132],[101,103,112],[124,126,129],[117,118,122],[101,114,127],[101,107,117],[117,131,133]]),
([v0,v1,v2,v3,v232,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,110,129],[104,108,116],[119,121,125],[101,102,111],[119,123,131],[115,117,133],[101,103,113],[126,127,130],[117,118,124],[101,109,128],[101,107,117],[117,122,132]]),
([v0,v1,v2,v3,v233,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,125,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,110,129],[104,108,116],[119,121,124],[101,102,111],[119,122,131],[115,117,133],[101,103,113],[125,127,130],[117,118,123],[101,109,128],[101,107,117],[117,126,132]]),
([v0,v1,v2,v3,v234,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,63,79,80,81,84,88,89,91,106,114,116,138,178,179,181,184,223,224,225,235],[[104,105,111],[104,106,113],[100,101,120],[104,109,129],[104,108,116],[119,121,123],[101,102,110],[119,127,131],[115,117,133],[101,103,112],[124,126,130],[117,118,122],[101,114,128],[101,107,117],[117,125,132]]),
([v0,v1,v2,v3,v235,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,110,129],[104,108,116],[119,121,125],[101,102,111],[119,123,131],[115,117,133],[101,103,113],[126,127,130],[117,118,124],[101,109,128],[101,107,117],[117,122,132]]),
([v0,v1,v2,v3,v236,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,178,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,110,129],[104,108,116],[119,121,125],[101,102,111],[119,123,131],[115,117,133],[101,103,113],[126,127,130],[117,118,124],[101,109,128],[101,107,117],[117,122,132]]),
([v0,v1,v2,v3,v237,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,116,127,134,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,127],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[125,126,130],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v1,v2,v3,v238,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,110,129],[104,108,116],[119,121,125],[101,102,111],[119,123,131],[115,117,133],[101,103,113],[126,127,130],[117,118,124],[101,109,128],[101,107,117],[117,122,132]]),
([v0,v1,v2,v3,v239,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,125,178,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,110,129],[104,108,116],[119,121,124],[101,102,111],[119,122,131],[115,117,133],[101,103,113],[125,127,130],[117,118,123],[101,109,128],[101,107,117],[117,126,132]]),
([v0,v1,v2,v3,v240,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,63,79,80,81,84,88,89,91,106,114,116,125,127,128,181,184,223,224,225,235],[[104,105,111],[104,106,113],[100,101,120],[104,109,129],[104,108,116],[119,121,123],[101,102,110],[119,127,131],[115,117,133],[101,103,112],[124,126,130],[117,118,122],[101,114,128],[101,107,117],[117,125,132]]),
([v0,v1,v2,v3,v241,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,91,93,96,102,106,117,172,178,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,121],[104,108,116],[104,110,129],[119,120,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v1,v2,v3,v242,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,178,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,110,129],[104,108,116],[119,121,125],[101,102,111],[119,123,131],[115,117,133],[101,103,113],[126,127,130],[117,118,124],[101,109,128],[101,107,117],[117,122,132]]),
([v0,v1,v2,v3,v243,v16],[],[0,1,3,5,7,8,9,15,19,24,28,34,49,54,59,79,80,81,84,89,91,96,106,116,117,127,128,181,184,223,224,225,235],[[104,105,111],[104,106,113],[100,101,119],[104,107,116],[104,109,128],[120,123,124],[101,102,110],[115,117,132],[124,126,130],[101,103,112],[117,118,122],[123,125,129],[101,114,117],[101,108,127],[117,121,131]]),
([v0,v1,v2,v3,v244,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,42,49,54,79,80,81,84,88,89,91,96,106,114,116,127,128,181,184,223,224,225,235],[[104,105,111],[104,106,114],[100,101,120],[104,109,129],[104,108,116],[119,121,124],[101,102,110],[119,127,131],[115,117,133],[101,103,113],[125,126,130],[117,118,123],[101,112,128],[101,107,117],[117,122,132]]),
([v0,v1,v2,v245,v11,v16],[],[0,1,2,3,5,7,9,12,15,19,24,28,29,49,54,79,81,84,88,89,91,96,102,109,114,169,176,181,184,217,224,225,235],[[102,105,112],[105,106,114],[100,101,119],[105,108,123],[105,110,128],[118,120,124],[101,103,111],[115,116,132],[118,122,130],[101,104,113],[116,117,123],[125,126,129],[101,107,116],[101,109,127],[116,121,131]]),
([v0,v1,v2,v246,v11,v16],[],[0,1,3,5,7,8,9,11,12,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,117,169,176,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,107,116],[104,110,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,108,117],[101,109,128],[117,122,132]]),
([v0,v1,v2,v247,v11,v16],[],[0,1,3,5,7,8,9,12,15,18,19,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,176,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,109,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,110,128],[117,122,132]]),
([v0,v1,v2,v248,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,81,86,106,108,109,114,117,125,128,169,176,181,184,223,224,225,232,234,235,255],[[104,105,112],[104,106,114],[100,101,131],[104,108,116],[104,110,127],[120,121,134],[101,102,111],[118,119,133],[121,123,129],[101,103,113],[117,119,132],[124,125,128],[101,107,115],[101,109,126],[119,122,130]]),
([v0,v1,v2,v249,v11,v16],[],[0,1,3,4,5,7,8,12,15,19,24,28,34,49,51,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,219,223,225,231],[[105,106,112],[103,105,114],[100,101,120],[105,108,116],[105,110,129],[119,121,125],[101,102,111],[115,117,133],[119,123,130],[101,104,113],[117,118,124],[126,127,131],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v1,v2,v250,v11,v16],[],[0,1,3,5,7,8,9,11,12,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,116,127,134,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,107,116],[104,110,129],[119,121,127],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[125,126,130],[101,108,117],[101,109,128],[117,122,132]]),
([v0,v1,v2,v251,v11,v16],[],[0,1,3,5,7,8,9,12,15,18,19,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,231],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,109,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,110,128],[117,122,132]]),
([v0,v1,v2,v252,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,111,116,119,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,126],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[125,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v1,v2,v253,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,111,117,120,129,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v1,v2,v254,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,81,86,106,108,109,114,116,117,125,127,128,181,184,223,224,225,232,234,235,255],[[104,105,112],[104,106,114],[100,101,131],[104,108,116],[104,110,127],[120,121,134],[101,102,111],[118,119,133],[122,125,129],[101,103,113],[117,119,132],[121,124,128],[101,107,115],[101,109,126],[119,123,130]]),
([v0,v1,v2,v255,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,111,119,120,129,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v1,v2,v256,v11,v16],[],[0,1,3,5,7,8,9,11,12,19,24,28,34,49,54,81,86,111,112,113,114,116,117,127,128,181,184,223,224,225,232,234,235,249,255],[[104,105,112],[104,106,114],[100,101,130],[104,107,116],[104,110,126],[120,121,134],[101,102,111],[118,119,132],[122,124,128],[101,103,113],[117,119,131],[121,123,127],[101,108,115],[101,109,125],[119,129,133]]),
([v0,v1,v27,v54,v3,v11],[],[1,3,4,7,9,10,12,17,19,26,28,36,79,81,83,88,96,106,114,116,128,169,181,186,223,224,225,230,234,235],[[104,105,111],[104,109,123],[103],[100,102,127],[104,107,114],[115,120,125],[115,118],[100,101,110],[112,113,129],[119,124,126],[100,108,122],[113,116,126],[100,119,121],[113,117,128],[100,106,113]]),
([v0,v1,v257,v3,v11,v16],[],[0,1,5,7,8,9,12,15,19,24,28,34,49,50,54,81,82,83,88,91,96,106,116,127,128,181,184,223,224,225,230,234,235,255],[[103,104,111],[103,105,114],[100,101,130],[103,107,117],[103,109,126],[118,119,133],[101,110,113],[115,116,132],[119,124,128],[101,102,112],[115,121,131],[122,123,127],[101,106,115],[101,108,125],[115,120,129]]),
([v0,v1,v258,v3,v11,v16],[],[0,1,3,5,7,8,9,12,19,24,28,34,40,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,111],[104,106,114],[100,101,120],[104,112,116],[104,109,129],[119,121,125],[101,102,110],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,108,128],[117,122,132]]),
([v0,v1,v259,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,28,34,46,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,233],[[104,105,111],[104,106,114],[100,101,120],[104,108,116],[104,112,129],[119,121,125],[101,102,110],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v1,v28,v54,v3,v11],[],[1,3,4,7,9,10,12,17,22,26,28,36,79,81,83,88,100,106,114,116,127,128,169,202,209,223,224,225,232,234,235],[[104,105,111],[104,109,124],[103],[100,102,128],[104,107,114],[115,121,126],[115,118],[100,101,110],[112,113,130],[119,120,125],[100,108,123],[113,116,127],[100,119,122],[113,117,129],[100,106,113]]),
([v0,v1,v29,v47,v3,v16],[],[0,1,5,7,8,9,19,24,30,35,36,59,61,81,82,83,91,96,106,128,181,184,223,224,225,230,233,235],[[103,104,110],[103,112,115],[103,105,109],[100,101,125],[103,107,121],[113,114,127],[116,126],[101,108],[116,119,123],[118],[101,111,113],[113,117,124],[101,102,108],[122,124],[101,106,120]]),
([v0,v1,v260,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,81,82,83,84,88,91,100,116,127,128,181,184,223,224,225,232,234,235,255],[[104,105,112],[104,106,114],[100,101,130],[104,108,117],[104,110,126],[119,120,133],[101,102,111],[116,118,132],[120,124,128],[101,103,113],[115,118,131],[122,123,127],[101,107,118],[101,109,125],[118,121,129]]),
([v0,v1,v30,v47,v3,v11],[],[0,1,5,7,8,9,12,15,30,35,36,42,65,81,82,83,88,91,96,106,128,193,196,223,224,225,230,235],[[103,104,110],[103,112,122],[103,105,109],[100,101,126],[103,107,115],[117,120,124],[116,117],[101,108],[113,114,127],[123],[101,111,121],[113,118,125],[101,102,108],[113,119],[101,106,113]]),
([v0,v1,v261,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,125,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,124],[101,102,111],[115,117,133],[119,122,131],[101,103,113],[117,118,123],[125,127,130],[101,107,117],[101,109,128],[117,126,132]]),
([v0,v1,v47,v3,v11,v16],[],[0,1,5,7,8,9,12,15,19,24,30,35,36,81,82,83,88,91,96,106,116,127,128,181,184,223,224,225,230,234,235,255],[[103,104,112],[103,105,111],[100,101,128],[103,107,115],[103,109,124],[116,117,131],[101,110],[113,114,130],[117,122,126],[101,102,110],[113,119,129],[120,121,125],[101,106,113],[101,108,123],[113,118,127]]),
([v0,v1,v47,v3,v11,v127],[],[0,1,5,7,8,9,12,15,19,24,30,37,46,47,81,91,98,99,102,106,109,116,117,127,128,218,223,234,235,255],[[103,104,113],[103,105,112],[100,101,125],[103,107,117],[103,109,111],[118,121,129],[101,110],[114,116,128],[115,122,124],[101,102,110],[114,119,127],[121,123,126],[101,106,114],[101,108,110],[114,120]]),
([v0,v1,v262,v3,v11,v16],[],[1,3,4,7,9,10,12,17,22,26,28,36,79,81,83,88,96,106,114,116,127,128,169,184,188,223,224,225,230,234,235,255],[[104,105,111],[103,104,119],[100,102,128],[104,107,114],[104,109,123],[115,118,131],[100,101,110],[112,113,130],[115,121,126],[100,119,122],[113,117,129],[119,120,125],[100,106,113],[100,108,124],[113,116,127]]),
([v0,v1,v263,v3,v11,v16],[],[1,3,4,7,9,10,14,17,19,26,28,36,79,81,83,88,91,96,106,116,127,128,143,181,186,223,224,225,230,234,235,255],[[104,105,111],[103,104,119],[100,102,128],[104,107,114],[104,109,124],[115,116,131],[100,101,110],[112,113,130],[116,121,126],[100,119,122],[113,118,129],[119,120,125],[100,106,113],[100,108,123],[113,117,127]]),
([v0,v1,v264,v3,v11,v16],[],[1,3,4,5,7,9,10,14,17,22,26,30,36,81,82,83,88,91,96,106,116,127,128,183,186,223,224,225,230,234,235,255],[[105,106,112],[104,105,120],[102,103,128],[105,108,115],[105,110,124],[116,117,131],[101,103,111],[113,114,130],[117,122,126],[100,103,120],[113,119,129],[120,121,125],[103,107,113],[103,109,123],[113,118,127]]),
([v0,v1,v54,v6,v3,v16],[],[1,3,4,7,9,10,14,17,19,26,28,36,79,81,83,91,96,106,116,127,128,169,181,186,223,224,225,230,234,235],[[104,105,111],[103],[104,107,114],[100,102,127],[104,109,123],[115,118],[112,113,129],[100,101,110],[115,120,125],[113,117,128],[100,118,121],[118,119,124],[100,106,113],[113,116,126],[100,108,122]]),
([v0,v1,v54,v31,v3,v11],[],[1,3,4,7,9,10,12,17,22,26,28,36,79,81,83,88,96,106,114,116,127,128,169,193,196,223,224,225,230,234,235],[[104,105,111],[103],[104,109,124],[100,102,128],[104,107,114],[115,118],[115,121,126],[100,101,110],[112,113,130],[119,120,125],[100,119,122],[113,117,129],[100,108,123],[113,116,127],[100,106,113]]),
([v0,v1,v54,v3,v32,v11],[],[1,3,4,7,9,10,12,17,22,26,28,36,79,81,83,88,100,106,114,116,128,169,178,181,186,223,224,225,232,234,235],[[104,105,111],[103],[100,102,128],[104,109,124],[104,107,114],[115,118],[100,101,110],[115,120,126],[112,113,130],[100,119,121],[119,122,125],[113,117,129],[100,108,123],[100,106,113],[113,116,127]]),
([v0,v265,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,19,24,28,34,39,49,54,79,80,81,84,87,88,91,96,102,106,114,117,126,181,184,223,224,225,235],[[104,105,111],[104,106,114],[100,101,119],[104,112,116],[104,109,129],[120,121,126],[101,102,110],[115,117,133],[120,123,131],[101,103,113],[117,118,124],[125,127,130],[101,107,117],[101,108,128],[117,122,132]]),
([v0,v266,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,28,34,45,49,54,79,80,81,84,88,89,91,96,102,106,114,116,126,181,184,223,224,225,235],[[104,105,111],[104,106,114],[100,101,120],[104,108,116],[104,112,129],[119,121,125],[101,102,110],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v37,v3,v158,v11,v16],[],[1,2,3,6,7,10,15,20,24,50,54,79,80,81,84,87,88,89,91,96,102,106,113,114,116,118,127,182,184,222,225,239,252],[[104,105,110],[101,102,117],[104,115,125],[104,106,112],[104,108,128],[102,103,109],[116,118,123],[113,114,121],[124,126,129],[100],[102,113,122],[102,107,127],[111,113,132],[116,120,131],[113,119,130]]),
([v0,v267,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,65,75,79,80,81,84,88,89,91,106,114,125,128,206,210,223,224,225,235],[[104,105,110],[104,113,127],[104,106,112],[100,101,120],[104,108,116],[119,125,129],[119,121,123],[101,102,109],[115,117,131],[128],[101,114,126],[117,124,130],[101,103,111],[117,118,122],[101,107,117]]),
([v0,v267,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v0,v268,v2,v18,v11,v16],[0],[1,2,5,7,8,10,12,13,19,25,49,55,79,86,111,112,113,116,117,118,119,121,127,130,181,185,223,224,225,234,235,249],[[103],[104,105,111],[100,101,119],[104,107,113],[104,109,125],[117,120],[0,100,118],[115,116,130],[121,123,127],[100,102,110],[114,116,129],[117,122,126],[100,106,112],[100,108,124],[116,128,131]]),
([v269,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,83,88,89,91,96,102,107,115,172,178,181,184,223,224,225,235],[[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[101,103,113],[117,118,124],[126,127,130],[101,107,117],[101,109,128],[117,122,132]]),
([v1,v38,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,107,115,181,184,223,224,225,235],[[104,105,112],[119,121,125],[101,102,111],[115,117,131],[119,123,129],[104,106,114],[100,101,120],[104,108,116],[104,110,127],[101,103,113],[117,118,124],[128,130],[101,107,117],[101,109,126],[117,122,130]]),
([v1,v270,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,128,137,205,209,246,247,249,252],[[104,105,110],[119,124,130],[119,121,123],[101,102,109],[115,117,131],[104,114,127],[104,106,112],[100,101,120],[104,108,116],[129],[101,113,126],[117,125,128],[101,103,111],[117,118,122],[101,107,117]]),
([v1,v270,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,238,239,247,252],[[104,105,112],[119,121,125],[101,102,111],[115,117,133],[119,123,131],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[101,103,113],[117,118,124],[126,127,132],[101,107,117],[101,109,128],[117,122,130]])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x0 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (0*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x1 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (1*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x2 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (2*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x3 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (3*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x4 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (4*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x5 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (5*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x6 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (6*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x7 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (7*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x8 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (8*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x9 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (9*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x10 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (10*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x11 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (11*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x12 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (12*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x13 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (13*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x14 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (14*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x15 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (15*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x16 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (16*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x17 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (17*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x18 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (18*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x19 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (19*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x20 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (20*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x21 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (21*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x22 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (22*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x23 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (23*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x24 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (24*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x25 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (25*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x26 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (26*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x27 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (27*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x28 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (28*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x29 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (29*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x30 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (30*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x31 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (31*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x32 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (32*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x33 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (33*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x34 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (34*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x35 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (35*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x36 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (36*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x37 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (37*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x38 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (38*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x39 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (39*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x40 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (40*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x41 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (41*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x42 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (42*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x43 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (43*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x44 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (44*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x45 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (45*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x46 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (46*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x47 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (47*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x48 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (48*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x49 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (49*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x50 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (50*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x51 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (51*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x52 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (52*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x53 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (53*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x54 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (54*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x55 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (55*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x56 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (56*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x57 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (57*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x58 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (58*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x59 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (59*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x60 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (60*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x61 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (61*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x62 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (62*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x63 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (63*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x64 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (64*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x65 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (65*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x66 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (66*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x67 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (67*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x68 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (68*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x69 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (69*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x70 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (70*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x71 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (71*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x72 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (72*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x73 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (73*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x74 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (74*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x75 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (75*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x76 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (76*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x77 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (77*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x78 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (78*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x79 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (79*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x80 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (80*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x81 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (81*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x82 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (82*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x83 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (83*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x84 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (84*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x85 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (85*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x86 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (86*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x87 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (87*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x88 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (88*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x89 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (89*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x90 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (90*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x91 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (91*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x92 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (92*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x93 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (93*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x94 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (94*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x95 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (95*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x96 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (96*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x97 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (97*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x98 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (98*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC5x99 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (99*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopI5 : LevelN ptopR ptopT 5 ptopD5 := levelStep ptopB ptopW ptopQ ptopI4 (chunks 4 ptopD5 100 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC5x0
  · exact ptopC5x1
  · exact ptopC5x2
  · exact ptopC5x3
  · exact ptopC5x4
  · exact ptopC5x5
  · exact ptopC5x6
  · exact ptopC5x7
  · exact ptopC5x8
  · exact ptopC5x9
  · exact ptopC5x10
  · exact ptopC5x11
  · exact ptopC5x12
  · exact ptopC5x13
  · exact ptopC5x14
  · exact ptopC5x15
  · exact ptopC5x16
  · exact ptopC5x17
  · exact ptopC5x18
  · exact ptopC5x19
  · exact ptopC5x20
  · exact ptopC5x21
  · exact ptopC5x22
  · exact ptopC5x23
  · exact ptopC5x24
  · exact ptopC5x25
  · exact ptopC5x26
  · exact ptopC5x27
  · exact ptopC5x28
  · exact ptopC5x29
  · exact ptopC5x30
  · exact ptopC5x31
  · exact ptopC5x32
  · exact ptopC5x33
  · exact ptopC5x34
  · exact ptopC5x35
  · exact ptopC5x36
  · exact ptopC5x37
  · exact ptopC5x38
  · exact ptopC5x39
  · exact ptopC5x40
  · exact ptopC5x41
  · exact ptopC5x42
  · exact ptopC5x43
  · exact ptopC5x44
  · exact ptopC5x45
  · exact ptopC5x46
  · exact ptopC5x47
  · exact ptopC5x48
  · exact ptopC5x49
  · exact ptopC5x50
  · exact ptopC5x51
  · exact ptopC5x52
  · exact ptopC5x53
  · exact ptopC5x54
  · exact ptopC5x55
  · exact ptopC5x56
  · exact ptopC5x57
  · exact ptopC5x58
  · exact ptopC5x59
  · exact ptopC5x60
  · exact ptopC5x61
  · exact ptopC5x62
  · exact ptopC5x63
  · exact ptopC5x64
  · exact ptopC5x65
  · exact ptopC5x66
  · exact ptopC5x67
  · exact ptopC5x68
  · exact ptopC5x69
  · exact ptopC5x70
  · exact ptopC5x71
  · exact ptopC5x72
  · exact ptopC5x73
  · exact ptopC5x74
  · exact ptopC5x75
  · exact ptopC5x76
  · exact ptopC5x77
  · exact ptopC5x78
  · exact ptopC5x79
  · exact ptopC5x80
  · exact ptopC5x81
  · exact ptopC5x82
  · exact ptopC5x83
  · exact ptopC5x84
  · exact ptopC5x85
  · exact ptopC5x86
  · exact ptopC5x87
  · exact ptopC5x88
  · exact ptopC5x89
  · exact ptopC5x90
  · exact ptopC5x91
  · exact ptopC5x92
  · exact ptopC5x93
  · exact ptopC5x94
  · exact ptopC5x95
  · exact ptopC5x96
  · exact ptopC5x97
  · exact ptopC5x98
  · exact ptopC5x99
  ))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD6 : List StD := [
([v42,v0,v1,v268,v2,v3,v11],[7,8],[1,3,5,8,12,19,28,29,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,116,127,134,181,184,195,223,224,225,239,252],[[108,111,129],[118,122,133],[],[124,125,130],[100,105,127],[116,121,132],[103,108,118],[128],[108,109,113],[100,107,119],[108,110,115],[131],[118,120,126],[100,101,106],[114,116,134],[124],[0,100],[1,116],[100,102,112],[116,117,123],[100,104,116]]),
([v4,v70,v0,v1,v2,v3,v11],[],[1,3,7,12,28,51,52,56,57,61,65,73,79,81,88,109,116,117,207,209,223,232,235,247],[[],[107,110,119],[114,117],[116],[100,106],[113,115],[102],[114,117],[123],[100,106],[113,115],[107,108,111],[107,118,120],[100,105,121],[107,109,115],[114,117],[100,101,104],[112,113,122],[100,106],[113,115],[100,103,113]]),
([v4,v74,v0,v1,v2,v3,v11],[],[0,1,7,12,15,22,26,30,35,52,56,80,81,88,89,108,109,117,128,222,223,224,235,247],[[],[102,110],[117,118,121],[],[101,109],[112,116],[102,108],[113],[120],[101,107],[112,116],[102,108],[102,106,110],[100,101,114],[102,104,111],[117,119,123],[101,107],[112,115,122],[101,105,109],[112,116],[101,103,112]]),
([v4,v93,v0,v1,v2,v3,v11],[],[1,7,12,22,29,30,34,35,40,52,74,80,81,88,89,100,108,109,116,117,128,222,223,224,225,235,247,249,252],[[124,127],[107,110],[119,120,123],[118],[100,109],[112,117],[101],[113],[122,126],[100,105],[112,128],[106,107,119],[107,110],[100,104,114],[107,108,111],[119,121,126],[100,105],[112,116,125],[100,103,109],[112,115,117],[100,102,112]]),
([v4,v97,v0,v1,v2,v3,v11],[],[0,1,3,7,8,12,15,28,34,44,52,56,79,80,81,88,89,100,109,116,117,222,223,225,247,249,252],[[123,125],[103,111],[115,123,125],[119],[101,110],[114,118],[103,111],[120],[124],[101,110],[114,126],[103,104,108],[103,111],[100,101,116],[103,106,113],[115,121,122],[101,102,107],[112,114,126],[101,109,110],[114,117,118],[101,105,114]]),
([v4,v110,v0,v1,v2,v3,v11],[],[0,1,3,7,12,15,22,26,28,34,35,52,56,79,81,88,100,109,116,117,136,223,225,232,247,249,252],[[122,125],[103,112],[115,120],[118],[101,111],[114,117],[110],[119],[121,124],[101,123],[114,117],[103,109,115],[103,107,112],[100,101,123],[103,105,117],[115,120],[101,102,108],[113,114,126],[101,106,111],[114,116,117],[101,104,114]]),
([v4,v72,v0,v1,v2,v3,v11],[],[0,1,3,7,8,12,15,22,28,34,52,56,79,80,81,88,89,100,109,117,207,223,225,232,235,247,249],[[122,126],[103,122,126],[115,119],[],[101,110],[114,118],[111],[115,119],[121],[101,123],[114,118],[103,104,109],[103,120,125],[100,101,116],[103,106,113],[115,119],[101,102,108],[112,114,124],[101,107,110],[114,117,118],[101,105,114]]),
([v4,v136,v0,v1,v2,v3,v11],[7],[0,1,7,8,12,15,22,26,30,35,52,56,81,88,100,108,109,116,117,128,222,223,224,225,232,235,247],[[0,123],[102,111],[118,119,122],[117],[101,110],[112,116],[109],[113],[121],[101,108],[112,116],[102,103,118],[102,107,111],[100,101,124],[102,105,116],[118,120,126],[101,108],[112,115,125],[101,106,110],[112,114,116],[101,104,112]]),
([v4,v139,v0,v1,v2,v3,v11],[],[0,1,3,7,8,12,15,26,28,34,52,56,79,80,81,88,89,109,116,117,133,136,223,225,235,247,249],[[123,126],[103,123,126],[115,119],[118],[101,110],[114,117],[111],[115,121],[125],[101,110],[114,120],[103,104,109],[103,107,122],[100,101,116],[103,106,113],[115,119],[101,102,108],[112,114,124],[101,110],[114,117],[101,105,114]]),
([v4,v0,v5,v1,v2,v3,v11],[],[0,1,3,7,8,12,15,22,26,28,34,52,56,70,74,79,80,81,88,89,109,117,223,225,247,249,252],[[103,112],[123,125],[118,123,125],[],[101,111],[117,120],[103,114],[103,104,110],[103,108,112],[100,101,119],[103,106,116],[121],[122],[101,113],[117,120],[118,124],[101,102,109],[115,117,126],[101,107,111],[117,120],[101,105,117]]),
([v4,v0,v1,v268,v2,v3,v11],[4,7],[1,3,7,8,12,22,28,29,35,40,52,74,79,80,81,88,89,100,109,116,117,136,223,225,252],[[108,111],[115,121],[1,123],[119],[100,110],[114,118],[103,108,115],[102],[108,111],[100,107,116],[108,109,113],[120],[115,121],[100,101,106],[112,114,124],[122],[0,100],[0,114],[100,105,110],[114,117,118],[100,104,114]]),
([v4,v0,v1,v2,v54,v3,v11],[4],[1,3,7,12,22,26,28,51,52,56,57,61,65,73,79,81,88,100,109,117,209,223,232,235,247],[[109,112,120],[116,119],[],[],[100,108],[115,118],[109,110,113],[105,109,124],[102],[100,107,122],[109,111,118],[116,119],[116],[100,101,106],[114,115,123],[121],[100,104,108],[115,117,118],[0,100],[0,115],[100,103,115]]),
([v4,v0,v1,v2,v46,v3,v11],[4],[0,1,7,12,15,30,35,44,52,56,80,81,88,89,100,108,109,116,117,128,223,224,235,247],[[102,109],[118,119,121],[117],[],[101,108],[111,116],[102,106],[102,109],[102,106],[100,101,113],[102,104,110],[118,120],[112],[101,105],[111,115,122],[123],[101,107,108],[111,114,116],[101,105],[0,111],[101,103,111]]),
([v49,v0,v1,v2,v54,v3,v11],[7,8],[1,3,5,9,12,19,28,49,51,56,57,61,65,73,79,81,84,88,91,96,102,109,117,181,184,209,223,224,225,232,235,247,255],[[109,112,125],[117,120,127],[128,131],[],[100,105,123],[115,119,128],[109,110,113],[103,109,132],[124],[100,108,129],[109,111,121],[117,118,122],[117],[100,101,106],[114,115,130],[126],[100,102,107],[115,116,121],[0,100],[1,115],[100,104,115]]),
([v50,v0,v1,v2,v46,v3,v11],[8],[0,1,7,12,15,30,33,35,37,52,56,80,81,84,89,91,96,106,108,116,117,127,128,223,224,225,235,239,247],[[102,107],[120,122,124],[119,121,123],[],[101,105],[112,116,125],[102,107],[102,108,110],[102,107],[100,101,114],[102,104,111],[115,119,120],[127],[101,105],[112,118,126],[128],[101,106,109],[112,113,117],[101,105],[0,112],[101,103,112]]),
([v51,v0,v1,v268,v2,v3,v16],[0,8],[1,3,5,8,12,19,28,29,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,108,116,127,134,141,181,195,223,225,239,252],[[108,110,115],[114,116,134],[],[116,117,123],[100,104,116],[116,121,132],[103,108,118],[128],[108,109,113],[100,107,119],[108,111,130],[124],[118,120,127],[100,101,106],[118,122,133],[125],[0,100],[1,132],[100,102,112],[125,126,131],[100,105,129]]),
([v7,v0,v1,v2,v54,v3,v16],[0,8],[1,3,5,9,12,19,28,49,51,56,57,61,65,73,79,80,81,84,88,91,96,102,106,109,117,181,209,224,225,232,235,247,255],[[109,111,123],[114,116,130],[116,117,123],[],[100,104,116],[116,120,128],[109,110,113],[103,109,132],[115],[100,108,129],[109,112,126],[118,119,124],[118],[100,101,106],[118,121,127],[122],[100,102,107],[128,131],[0,100],[1,128],[100,105,125]]),
([v56,v0,v1,v2,v46,v3,v16],[8],[0,1,7,19,24,30,33,35,37,52,56,79,81,84,89,91,96,106,108,116,117,127,128,181,184,223,224,225,235,250],[[102,107],[112,118,128],[112,113,117],[],[101,105],[112,116,127],[102,107],[102,108,110],[102,107],[100,101,114],[102,104,124],[115,119,120],[111],[101,105],[120,122,126],[129],[101,106,109],[119,121,125],[101,105],[0,127],[101,103,123]]),
([v271,v0,v1,v2,v3,v11,v16],[7],[0,1,5,7,8,9,15,24,34,52,53,54,59,63,68,79,81,88,89,96,102,106,109,114,116,117,127,169,184,205,223,224,225,232,235,255],[[118],[117,125],[135],[101],[116,122],[0,132],[103,104,108],[103,105,111],[100,103,133],[103,106,122],[103,107,128],[117,123,124],[109,110,114],[115,116,134],[117,120,131],[102,109,127],[116,121,122],[124,126,130],[109,112,116],[109,113,129],[116,119,132]]),
([v272,v0,v1,v2,v3,v11,v16],[7],[0,1,5,7,8,9,12,15,19,24,28,30,34,49,53,54,80,81,88,89,96,108,109,114,116,117,128,172,178,181,184,223,224,225,235,255],[[103,119],[118],[124],[111],[117,122],[0,133],[103,104,112],[103,105,115],[100,101,119],[103,107,116],[103,109,130],[123,125,135],[101,110,114],[117,121,134],[125,126,132],[101,102,113],[117,122],[127,128,131],[101,106,117],[101,108,129],[117,120,133]]),
([v273,v0,v1,v2,v3,v11,v16],[],[0,1,3,7,8,9,15,24,30,33,34,42,54,67,80,81,84,88,89,96,106,108,113,114,116,117,127,128,170,184,193,223,224,225,235,249,252,255,256],[[138],[117],[124,137],[101],[115,136],[133,135],[103,104,110],[103,105,112],[100,103,118],[103,106,114],[103,107,129],[123,124,137],[102,108,128],[115,121,134],[125,127,132],[108,109,113],[115,116,120],[124,126,131],[108,115,122],[108,111,130],[115,119,133]]),
([v274,v0,v1,v2,v3,v11,v16],[],[0,1,3,7,8,9,12,15,19,24,28,33,34,49,52,54,79,80,81,84,88,89,96,102,106,114,116,117,127,181,184,223,224,225,235,249,252,255,256],[[103,138],[127],[137],[114],[118,136],[133,135],[103,104,112],[103,105,115],[100,101,121],[103,107,117],[103,109,130],[120,125,126],[101,102,110],[116,118,134],[120,123,132],[101,111,113],[118,119,124],[126,128,131],[101,106,118],[101,108,129],[118,122,133]]),
([v275,v0,v1,v2,v3,v11,v16],[7],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,81,84,88,89,91,93,96,102,106,109,116,117,127,134,172,181,184,223,224,225,232,235],[[119],[127],[126,130],[136],[116,125],[0,135],[104,105,112],[104,106,114],[100,101,121],[104,108,125],[104,110,132],[118,120,129],[101,102,111],[115,116,137],[118,123,134],[101,103,113],[116,117,124],[126,128,133],[101,107,116],[101,109,131],[116,122,135]]),
([v276,v0,v1,v2,v3,v11,v16],[7],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,109,116,117,172,178,181,184,223,224,225,232,235,256],[[136],[119,126],[125],[134],[117,124],[0,133],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,130],[119,121,126],[101,102,111],[115,117,135],[119,123,132],[101,103,113],[117,118,124],[127,128,131],[101,107,117],[101,109,129],[117,122,133]]),
([v277,v0,v1,v2,v3,v11,v16],[7],[0,1,5,7,8,9,12,15,19,24,28,30,34,49,54,81,84,88,89,96,106,108,109,114,116,117,121,127,128,181,184,223,224,225,232,235,255],[[118],[117],[124],[111],[115,122],[0,133],[103,104,112],[103,105,114],[100,101,134],[103,107,122],[103,109,130],[123,124,136],[101,110,126],[115,121,135],[125,128,132],[101,102,113],[115,116,120],[124,127,131],[101,106,115],[101,108,129],[115,119,133]]),
([v278,v0,v1,v2,v3,v11,v16],[],[0,1,3,7,8,9,12,15,19,24,28,34,49,52,54,79,80,81,88,89,96,102,106,109,114,116,120,127,133,136,181,184,223,224,225,235,249,255,256],[[138],[118,129],[137],[113],[117,128],[134,136],[103,104,111],[103,105,114],[100,101,119],[103,107,116],[103,109,131],[118,124,125],[101,102,110],[115,117,135],[118,121,133],[101,112,126],[117,122,123],[125,127,132],[101,106,117],[101,108,130],[117,120,134]]),
([v58,v62,v0,v1,v2,v11,v16],[],[0,1,4,5,8,11,12,18,19,27,28,29,30,48,49,81,84,88,89,96,106,109,113,116,120,127,163,164,168,169,170,177,180,181,219,220,223,225,231,232,255],[[101,112],[118],[101,110,130],[101,103,114],[101,106,115],[101,108,133],[100,111,139],[117],[123,124,129],[115,122,127],[135,137],[100,104,109],[100,102,113],[100,105,121],[100,107,132],[123,128,140],[115,126,138],[130,131,134],[115,116,120],[123,125,136],[115,119,137]]),
([v58,v65,v0,v1,v2,v11,v16],[],[0,1,2,3,9,11,12,18,19,27,28,48,49,51,52,79,81,88,89,96,102,109,116,117,169,176,180,181,217,220,224,225,232,235,249],[[101,114],[118],[101,103,110],[101,112,124],[101,106,116],[101,108,127],[100,113,132],[117,123],[122],[116,121],[129,131,134],[100,102,109],[100,104,111],[100,105,121],[100,107,126],[117,123],[115,116,133],[117,120,130],[116,121],[124,125,128],[116,119,131]]),
([v58,v0,v1,v9,v2,v3,v11],[],[0,1,7,8,9,15,34,54,65,79,81,84,88,89,91,106,109,113,114,116,117,120,121,125,128,164,169,170,209,220,223,224,225,232,235,249],[[113],[112,120],[132,135],[119],[101],[110,116],[102,103,106],[102,108,128],[102,104,107],[100,102,133],[102,105,116],[112,124,131],[112,114,118],[112,122,127],[109,110,134],[130],[129,132,135],[110,123,132],[119,121,126],[110,111,115],[110,117,125]]),
([v58,v0,v1,v2,v279,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,81,84,88,91,93,96,102,106,109,114,116,117,120,127,169,181,184,220,223,224,225,235],[[120],[101,102,111],[101,103,113],[0],[101,107,116],[101,109,131],[104,105,112],[104,106,114],[100],[104,108,124],[104,110,132],[118,119,125],[118,127],[115,116,137],[118,122,135],[126,128,130],[116,117,123],[126,129,134],[116,124],[133,136],[116,121,136]]),
([v280,v0,v1,v2,v3,v11,v16],[7],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,70,79,80,81,88,89,91,96,102,109,116,117,171,172,178,181,184,223,224,225,235],[[104],[126],[125],[115],[118,124],[0,134],[104,105,112],[104,106,114],[100,101,120],[104,108,117],[104,110,131],[119,121,127],[101,102,111],[116,118,135],[119,123,133],[101,103,113],[118,124],[128,129,132],[101,107,118],[101,109,130],[118,122,134]]),
([v62,v97,v0,v2,v3,v11,v16],[],[0,1,3,7,10,12,15,19,24,52,56,79,80,81,84,87,88,89,96,102,106,114,116,117,127,166,167,173,179,181,184,222,224,225,235,255],[[123],[103,115,116],[116,121,122],[102],[111,113,126],[116,119,133],[103,110],[135],[101,109],[113,125,134],[127,128,132],[103,104,110],[100,101,117],[103,106,112],[103,108,130],[101,109],[113,114,120],[122,124,131],[101,105,113],[101,107,129],[113,118,133]]),
([v62,v110,v0,v2,v3,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,49,54,79,81,84,87,88,91,96,102,106,109,116,117,127,134,167,170,171,173,179,181,184,223,224,225,255,256],[[0,117,124],[104,116,117],[117,118,126],[102],[113,114,127],[117,120,136],[105],[123,129,137],[101,128,130],[114,122],[130,131,135],[104,106,112],[100,101,138],[104,108,122],[104,110,133],[101,103,111],[114,115,121],[123,125,134],[101,107,114],[101,109,132],[114,119,136]]),
([v62,v0,v5,v2,v3,v11,v16],[0],[0,1,3,5,7,9,12,15,19,24,49,54,57,68,73,79,80,81,87,88,89,91,96,102,109,116,117,167,173,179,181,184,224,225,247,255],[[104,118,119],[0,119,126],[119,121,135],[102],[115,117,127],[119,123,133],[104,112,114],[104,105,111],[100,101,120],[104,107,116],[104,109,131],[125],[101,113,128],[117,124],[128,129,132],[101,103,110],[117,124],[133,134],[101,106,117],[101,108,130],[117,122,133]]),
([v62,v0,v1,v9,v2,v3,v11],[],[0,1,5,7,8,9,12,15,28,30,34,49,54,63,65,80,81,84,88,89,106,116,125,166,167,171,172,173,179,205,209,223,224,225,235],[[103,119],[118],[133],[121,126],[109],[116,124],[103,104,110],[103,114,130],[103,105,112],[100,101,119],[103,107,115],[127,128,132],[121,125],[101,108,127],[116,123,134],[131],[101,113,129],[116,122,133],[101,102,111],[116,117,120],[101,106,116]]),
([v62,v0,v1,v2,v3,v59,v11],[3],[0,1,5,7,8,9,12,15,19,24,28,30,34,49,54,80,81,84,88,89,106,116,166,167,171,172,173,178,179,181,184,223,224,225,235,249,255],[[103,119],[118],[121,125],[111],[0],[116,123],[103,104,112],[103,105,114],[100,101,119],[103,109,130],[103,107,115],[121,124,136],[101,110,126],[126,128,132],[116,122,134],[101,102,113],[121,127,131],[116,117,120],[101,108,129],[101,106,116],[116,133,135]]),
([v62,v0,v1,v2,v158,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,29,30,33,34,42,49,54,67,80,81,84,89,96,106,113,116,127,140,166,171,173,179,181,184,193,223,224,225,235,255,256],[[104,112,123],[102],[113,114,119],[0],[113,121,126],[113,116,136],[104,105,115],[104,106,118],[100,101,142],[104,108,120],[104,110,135],[127,131,141],[111],[121,130,140],[132,133,138],[101,103,117],[121,122,125],[127,128,137],[101,107,129],[101,109,134],[121,124,139]]),
([v62,v0,v268,v2,v3,v11,v16],[0],[1,3,5,7,8,10,12,16,19,25,49,55,79,80,81,84,88,89,91,96,102,106,116,117,127,134,166,167,170,171,173,179,181,185,223,224,225,235],[[104,116,117],[123],[116,118,125],[101],[112,114,127],[116,120,136],[103],[104,105,111],[100,104,117],[104,107,113],[104,109,133],[122,129],[0,100,128],[114,126,137],[130,131,135],[100,102,110],[114,115,121],[122,124,134],[100,106,114],[100,108,132],[114,119,136]]),
([v43,v0,v1,v268,v2,v11,v16],[0],[0,1,3,5,8,12,19,28,29,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,116,127,134,170,181,195,223,225,239,252],[[101,108,120],[101,102,107],[0],[101,103,113],[101,105,117],[101,106,129],[104,109,119],[100],[109,110,114],[109,111,116],[109,112,130],[128],[119,121,127],[115,117,134],[119,123,133],[125],[117],[132],[117,118,124],[125,126,131],[117,122,132]]),
([v43,v0,v1,v2,v3,v11,v16],[],[0,1,7,8,9,15,24,34,54,79,80,81,84,88,89,91,96,102,106,116,117,127,134,167,170,172,173,184,223,224,225,235,249],[[102,114],[113,120,126],[119,125],[101],[111,123],[130,132],[102,103,107],[102,104,108],[100,102,114],[102,105,110],[102,106,127],[113,115,122],[113,124,126],[109,111,131],[113,117,129],[119,125],[111,112,118],[119,121,128],[111,123],[130,132],[111,116,130]]),
([v43,v0,v1,v2,v11,v16],[],[0,1,3,4,5,8,11,12,18,19,27,28,30,35,48,49,51,52,79,80,81,84,88,89,91,96,102,106,109,116,127,134,136,143,167,170,172,180,181,187,188,219,223,225,231,232,234,242,249,252,255],[[100,101,123,145],[101,102,111,112,122,135],[101,104,115,117,129,136],[101,107,120,133,134],[101,109,138,140,143,148],[100,105,110,113,122,135],[100,103,114,116,129,150],[100,106,119,120,123,128],[100,108,137,139,143,148],[122,124,129,131,132,150],[118,120,122,144,149],[122,126,141,143,144,148],[120,121,127,128,129,146],[129,130,142,143,146],[120,125,143,147,148]]),
([v281,v0,v1,v9,v2,v3,v11],[7],[0,1,3,5,7,8,9,12,15,28,34,49,54,65,79,80,81,84,88,89,91,106,114,179,205,209,213,223,224,225,235,249,252,256,260],[[104,133],[118,134],[131],[0],[126],[116,132],[104,105,110],[104,113,125],[104,106,112],[100,101,119],[104,108,115],[118,123,128],[118,120,122],[101,102,109],[114,116,130],[127],[101,124,129],[116,129,132],[101,103,111],[116,117,121],[101,107,116]]),
([v65,v74,v0,v1,v3,v11,v16],[],[0,1,5,7,10,12,15,19,24,30,35,80,81,88,89,96,108,109,114,116,117,128,171,172,178,181,184,222,223,225,233,247,249,254,255],[[119],[103,133,134],[118,120,122],[102],[112,117],[129,131,132],[103,110],[113],[101,109],[112,117],[123,124,128],[103,104,110],[100,101,114],[103,106,111],[103,108,126],[101,109],[112,116,130],[120,121,127],[101,105,112],[101,107,125],[112,115,129]]),
([v65,v72,v0,v1,v3,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,79,80,81,84,88,89,91,96,102,109,116,117,135,169,172,178,181,184,223,224,225,235,247,249,255],[[0,123,127],[104,125,137],[117,119,124],[103],[115,116,122],[133,135,136],[106],[117,124],[101,126,127],[115,122],[127,128,131],[104,105,112],[100,101,118],[104,108,114],[104,110,130],[101,102,111],[113,115,134],[117,121,132],[101,107,115],[101,109,129],[115,120,133]]),
([v65,v0,v5,v1,v3,v11,v16],[0],[0,1,3,5,7,8,12,15,19,24,28,34,37,67,72,79,80,81,88,89,91,96,102,109,116,117,172,178,181,184,223,225,239,247,249,252,254,255],[[104,136,137],[0,124,126],[118,120,137],[103],[117,123],[131,133,134],[104,112,114],[104,105,111],[100,101,119],[104,107,116],[104,109,129],[125],[101,113,126],[117,123],[126,127,130],[101,102,110],[115,117,135],[118,122,132],[101,106,117],[101,108,128],[117,121,131]]),
([v65,v0,v1,v9,v2,v3,v11],[],[0,1,3,7,8,9,12,15,28,34,49,52,54,65,79,80,81,88,89,109,116,117,125,128,172,209,223,224,225,235,249,256],[[103,131],[117,121],[128,130],[120],[111],[116,119],[103,104,109],[103,113,125],[103,105,112],[100,101,118],[103,107,115],[117,123,127],[117,121],[101,102,108],[114,116,129],[126],[101,128,130],[116,122,128],[101,110,124],[116,119],[101,106,116]]),
([v65,v0,v1,v2,v163,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,51,52,53,54,59,63,68,79,80,81,88,89,96,102,109,117,172,178,181,184,205,223,224,225,232,235],[[104,114,138],[115,116,120],[103],[0],[115,118,128],[115,119,134],[104,105,112],[104,106,117],[100,101,125],[104,108,122],[104,110,133],[124,129],[101,102,111],[121,123,139],[124,127,136],[113],[123,128],[130,131,135],[101,107,123],[101,109,132],[123,126,137]]),
([v65,v0,v1,v54,v3,v11,v16],[0],[1,3,5,7,9,10,12,17,19,26,28,36,79,81,84,88,91,96,102,109,116,117,165,169,171,172,178,181,186,223,224,225,230,234,235,247,249,255,256],[[104,137,138],[115,116,121],[120],[102],[113,114,119],[131,135,136],[104,105,111],[103],[100,104,132],[104,107,119],[104,109,128],[115,124],[100,101,110],[112,113,134],[115,118,130],[0,100,123],[113,122,133],[125,126,129],[100,106,113],[100,108,127],[113,117,131]]),
([v10,v0,v1,v2,v54,v11,v16],[0],[0,1,3,5,9,12,19,28,49,51,56,57,61,65,73,79,81,84,88,91,96,102,109,117,169,181,209,224,225,232,235,247,255],[[101,109,129],[101,102,107],[101,103,108],[0],[101,105,116],[101,106,125],[110,111,114],[104,110,132],[100],[110,112,122],[110,113,126],[118,119,123],[118],[115,116,130],[118,121,127],[124],[116,117,122],[128,131],[116],[128],[116,120,128]]),
([v10,v0,v1,v2,v3,v11,v16],[],[0,1,7,8,9,15,24,34,54,79,81,84,88,89,91,96,102,109,116,117,167,169,172,173,178,184,223,224,225,235,249,255,256],[[102,113,132],[112,123],[118,122,131],[101],[110,120],[128,130],[102,103,107],[102,104,108],[100,102,132],[102,105,117],[102,106,125],[112,114,119],[112,123],[109,110,129],[112,116,127],[121,122,131],[110,111,117],[122,124,126],[110,120],[128,130],[110,115,128]]),
([v10,v0,v1,v2,v11,v16],[],[0,1,2,3,5,9,11,12,18,19,27,28,29,30,48,49,52,56,79,81,84,88,89,91,96,102,109,117,142,143,167,169,173,176,180,181,187,188,217,224,225,229,232,235,242,249,252,255,256],[[100,101,122,142,148],[101,103,111,113,121,132],[101,104,115,116,131,147],[101,107,119,129,130],[101,109,135,137,140,145],[100,102,110,112,121,127],[100,105,114,117,131,147],[100,106,119,126,128],[100,108,134,136,140,145],[121,123,127,131,147],[118,119,121,143,146],[121,125,139,140,143,145],[119,120,126,131,141],[131,133,138,140,141],[119,124,140,144,145]]),
([v282,v0,v1,v2,v3,v11,v16],[],[0,1,7,8,9,12,15,19,24,28,30,34,49,54,80,81,84,88,89,91,96,106,108,116,117,127,128,167,172,173,181,184,223,224,225,235,249],[[102,118],[117,124,129],[123,128],[110],[115,127],[134,136],[102,103,111],[102,104,113],[100,101,118],[102,106,114],[102,108,131],[119,123,124],[101,109,129],[115,122,135],[124,126,133],[101,112,128],[115,116,121],[123,125,132],[101,105,115],[101,107,130],[115,120,134]]),
([v283,v0,v1,v2,v3,v11,v16],[0,7],[1,7,12,19,29,30,33,34,35,37,40,46,52,54,56,80,81,84,88,89,91,96,106,108,114,116,117,127,128,181,195,223,224,225,235,255],[[101],[118],[135],[100,105],[0,116],[1,133],[107,108,114],[108,109,113],[100,104,119],[108,110,115],[108,111,130],[120,124],[100,105],[116,123,134],[126,128,132],[100,106,112],[116,117,122],[125,127,131],[100,102,116],[100,103,129],[116,121,133]]),
([v284,v0,v1,v2,v3,v11,v16],[7],[0,1,3,5,7,8,9,19,24,28,34,40,49,54,59,79,80,81,84,88,89,91,96,106,116,117,127,128,143,146,181,184,223,224,225,235,255],[[104,129],[119],[136],[101,128],[],[0,134],[104,105,110],[104,106,113],[100,101,120],[104,111,116],[104,108,131],[121,124,125],[101,102,109],[115,117,135],[125,127,133],[101,103,112],[117,118,123],[124,126,132],[101,114,117],[101,107,130],[117,122,134]]),
([v285,v0,v1,v2,v3,v11,v16],[0],[0,1,3,5,7,8,9,12,15,28,34,42,46,49,54,79,80,81,84,88,89,91,96,106,114,116,127,128,188,190,223,224,225,235,244,255],[[104,129],[134],[135],[101,128],[0,117],[],[104,105,110],[104,106,114],[100,101,120],[104,108,116],[104,112,129],[119,121,124],[101,102,109],[115,117,133],[119,127,131],[101,103,113],[117,118,123],[125,126,130],[101,107,117],[101,111,128],[117,122,132]]),
([v68,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,9,12,15,19,24,28,34,35,49,54,57,79,81,84,88,91,96,102,109,114,116,181,184,224,225,232,235,247],[[112],[],[125],[0,101],[0,117],[1,129],[104,111,115],[104,105,114],[100,101,130],[104,107,123],[104,109,127],[119,120,124],[101,102,110],[116,117,131],[119,122,128],[101,103,113],[117,118,123],[129,132],[101,106,117],[101,108,126],[117,121,129]]),
([v69,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,8,9,12,19,24,28,34,49,54,61,79,80,81,84,88,89,91,96,102,106,116,117,181,184,223,224,225,232,235],[[120],[119],[125],[0,101],[],[1,131],[104,105,111],[104,106,113],[100,101,132],[104,114,116],[104,109,128],[119,121,126],[101,102,110],[115,117,133],[119,123,130],[101,103,112],[117,118,124],[129,131],[101,107,117],[101,108,127],[117,122,131]]),
([v286,v0,v1,v2,v3,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,28,34,49,54,65,79,80,81,84,88,89,91,96,102,106,114,116,181,184,190,223,224,225,234,235],[[129],[119],[133],[0,101],[0,117],[],[104,105,111],[104,106,113],[100,101,120],[104,108,116],[104,114,128],[119,121,125],[101,102,110],[115,117,134],[119,123,131],[101,103,112],[117,118,124],[126,130,132],[101,107,117],[101,109,127],[117,122,132]]),
([v287,v0,v1,v2,v3,v11,v16],[7],[0,1,5,7,8,9,12,15,19,24,30,35,49,54,73,81,88,96,106,108,109,114,116,117,127,128,181,184,223,224,225,232,235,255],[[111],[116],[],[101,110],[115,120],[0,130],[103,104,114],[103,105,113],[100,101,131],[103,107,120],[103,109,127],[121,122,133],[101,110],[115,119,132],[123,125,129],[101,102,112],[115,118,120],[122,124,128],[101,106,115],[101,108,126],[115,117,130]]),
([v288,v0,v1,v2,v3,v11,v16],[7],[0,1,3,5,7,8,9,15,19,24,28,34,49,54,59,81,88,89,102,106,108,109,114,116,117,125,127,143,181,184,223,224,225,232,234,235,255],[[117],[116,124],[136],[101,127],[115],[0,132],[104,105,111],[104,106,113],[100,101,133],[104,107,121],[104,109,129],[116,122,123],[101,102,110],[116,120,135],[116,118,131],[101,103,112],[119,121,134],[123,126,130],[101,114,121],[101,108,128],[121,125,132]]),
([v289,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,63,79,80,81,84,88,89,91,106,114,116,125,127,128,188,190,209,223,224,225,235,242,244,255],[[129],[119,136],[137],[101,128],[117,135],[],[104,105,111],[104,106,113],[100,101,120],[104,108,116],[104,109,130],[119,121,123],[101,102,110],[115,117,134],[119,127,132],[101,103,112],[117,118,122],[124,126,131],[101,107,117],[101,114,128],[117,125,133]]),
([v70,v74,v0,v1,v3,v11,v16],[],[1,5,7,12,19,30,48,49,54,57,60,64,71,72,81,88,96,105,106,109,114,116,126,127,134,181,207,222,223,225,232,233,247,255],[[121,133],[102],[120,124,133],[100,101,107],[114,119],[129,132],[108,113,121],[115],[100,105],[114,118,119],[121,123,128],[108,109,112],[100,106,130],[108,110,119],[108,111,126],[100,105],[114,117,131],[120,122,127],[100,103,114],[100,104,125],[114,116,129]]),
([v70,v72,v0,v1,v3,v11,v16],[],[1,3,5,7,12,19,28,48,49,54,55,56,60,64,71,79,81,84,88,91,96,102,106,109,114,116,117,120,127,135,181,207,223,224,225,235,247],[[],[103],[118,119,126],[100,102,108],[116,117,123],[134,136],[111],[118,124,125],[100,125,127],[116,122,123],[125,128,132],[109,110,114],[100,107,129],[109,112,123],[109,113,131],[100,101,106],[115,116,135],[118,121,133],[100,104,116],[100,105,130],[116,120,134]]),
([v70,v72,v1,v2,v3,v11,v16],[],[0,1,3,7,8,12,15,19,24,28,34,48,51,52,54,55,56,57,60,61,64,65,71,73,79,80,81,88,96,102,109,116,181,184,207,209,224,225,232,235,255],[[],[103,104,110],[140],[100,101,113],[103,106,125],[103,108,133],[116,117,123],[131],[101,112,138],[116,119,130],[116,121,135],[114,115,122],[101,102,109],[124,126,139],[127,129,136],[101,111,113],[114,118,126],[114,120,134],[101,105,126],[101,107,132],[126,128,137]]),
([v70,v139,v1,v2,v3,v11,v16],[0],[0,1,3,7,8,9,12,15,19,24,28,34,51,52,54,56,57,61,65,73,79,80,81,88,96,102,106,109,114,116,127,181,184,209,223,224,225,235],[[0],[103,104,111],[105],[100,101,113],[103,107,121],[103,109,132],[115,116,119],[114],[101,112,113],[115,117,122],[115,118,133],[123,128,129],[101,102,110],[120,122,137],[123,125,135],[101,113],[122,126,127],[129,130,134],[101,106,122],[101,108,131],[122,124,136]]),
([v70,v0,v5,v1,v3,v11,v16],[],[1,3,5,7,12,19,28,48,49,54,55,60,64,70,72,74,79,81,88,91,96,102,106,109,114,116,127,181,207,223,225,232,239,247,252,255],[[103],[],[118,119,135],[100,102,108],[117,123],[130,133],[109,114,115],[109,110,115],[100,107,131],[109,111,123],[109,112,128],[124],[100,113],[117,122,123],[125,126,129],[100,101,106],[116,117,134],[118,121,132],[100,104,117],[100,105,127],[117,120,130]]),
([v70,v0,v1,v9,v2,v3,v11],[],[1,3,7,12,28,51,52,54,56,57,61,63,65,73,79,81,88,106,109,114,116,117,125,128,205,209,223,224,225,232,235],[[102],[116,121],[],[],[100,106],[115,118],[108,109,113],[108,112,125],[107,108,120],[100,105,129],[108,110,118],[116,123,127],[116,119,120],[100,101,104],[114,115,130],[126],[100,111,124],[115,122,128],[100,106],[115,117,118],[100,103,115]]),
([v70,v0,v1,v2,v28,v3,v11],[7],[1,3,7,12,28,51,52,54,56,57,61,63,65,73,79,81,88,106,109,114,116,117,125,127,128,205,209,223,224,225,232,235],[[102],[116,121],[],[0],[100,106],[115,118],[108,109,113],[107,108,120],[108,112,126],[100,105,130],[108,110,118],[116,119,120],[116,124,128],[100,101,104],[114,115,131],[120,123,127],[100,106],[115,117,118],[100,111,125],[115,122,129],[100,103,115]]),
([v70,v0,v1,v2,v3,v11,v16],[7],[1,3,7,12,19,28,51,52,54,56,57,61,65,73,79,81,88,96,102,106,109,114,116,117,127,181,209,223,224,225,232,235,255],[[102],[116,123],[132],[100,107],[115,120],[0,129],[109,110,113],[108,109,122],[100,106,130],[109,111,120],[109,112,126],[116,121,122],[100,101,105],[114,115,131],[116,118,128],[100,107],[115,119,120],[122,124,127],[100,103,115],[100,104,125],[115,117,129]]),
([v70,v0,v1,v2,v3,v11,v290],[],[1,3,12,24,28,51,52,54,56,57,61,65,73,79,81,88,106,109,114,116,117,127,209,223,232,235,247],[[103],[115,120],[126],[100,106],[114,117],[],[108,109,112],[107,108,119],[100,105,124],[108,110,117],[108,111,122],[115,118,119],[100,101,104],[113,114,125],[115,120],[100,106],[114,116,117],[119,121,123],[100,102,114],[100,106],[114,117]]),
([v70,v0,v1,v54,v3,v11,v16],[0],[1,3,5,9,12,19,28,49,51,54,56,57,61,65,73,79,81,84,88,91,96,102,106,109,114,116,117,127,169,181,209,223,224,225,232,234,235,247],[[103],[118,119,126],[0],[100,102,107],[116,117,123],[133,137],[110,111,114],[109],[100,108,134],[110,112,123],[110,113,130],[118,124],[100,101,106],[115,116,136],[118,121,132],[100,125,128],[116,122,135],[125,127,131],[100,104,116],[100,105,129],[116,120,133]]),
([v71,v0,v1,v9,v2,v3,v11],[7],[1,3,5,7,12,28,49,79,81,84,88,91,106,109,114,116,117,125,128,209,212,213,215,223,224,225,232,235,249],[[103],[110,116],[128],[0,115],[100,121],[108,113],[110,116],[119,122,125],[115,122],[100,120,126],[108,113],[110,118,124],[110,111,114],[100,101,105],[107,108,127],[123],[100,121],[108,117,125],[100,102,106],[108,109,112],[100,104,108]]),
([v71,v0,v1,v2,v3,v11,v16],[7],[1,3,5,7,12,19,28,49,79,81,84,88,91,96,102,106,109,114,116,117,127,181,209,212,213,214,215,223,224,225,232,235,249,255],[[103],[111,119],[0,118,133],[100,124],[109,116],[129,132],[111,119],[118,125,126],[100,123,130],[109,116],[122,126,129],[111,112,117],[100,101,106],[108,109,131],[111,114,128],[100,102,107],[109,110,115],[118,120,127],[100,104,109],[100,105,121],[109,113,129]]),
([v291,v0,v1,v2,v3,v11,v16],[0,7],[1,3,5,7,12,19,28,49,79,81,84,88,96,102,106,109,114,116,117,127,135,157,158,160,161,181,223,224,225,232,235,255],[[103],[111,118],[0,117,131],[100,122],[109,115],[1,128],[111,118],[117,120,123],[100,121,129],[109,115],[123,124,128],[111,116,117],[100,101,106],[108,109,130],[111,113,127],[100,102,107],[109,110,114],[117,119,126],[100,104,109],[100,105,125],[109,112,128]]),
([v73,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,81,88,89,106,108,109,114,116,117,125,128,181,184,223,224,225,234,235,255],[[104,117],[116],[122],[0,101],[115],[1,130],[104,105,112],[104,106,114],[100,101,117],[104,108,117],[104,110,127],[121,123,133],[101,102,111],[119,120,132],[123,125,129],[101,103,113],[118,120,131],[128,130],[101,107,120],[101,109,126],[120,124,130]]),
([v292,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,125,181,184,198,200,223,224,225,234,235,242,244],[[104,130],[137],[134],[101,129],[117,136],[],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,128],[119,121,124],[101,102,111],[115,117,135],[119,122,132],[101,103,113],[117,118,123],[125,131,133],[101,107,117],[101,109,127],[117,126,133]]),
([v74,v88,v0,v1,v3,v11,v16],[0],[0,1,6,7,10,14,17,19,24,30,35,81,88,89,105,106,109,114,116,117,125,128,143,181,184,222,223,225,233,234,247,255],[[0,118,129],[103,110],[112],[101,109],[115,116,129],[126,127],[103,113],[117,119,131],[101,122],[111],[127,130],[103,104,110],[100,101,113],[103,106,113],[103,108,124],[101,102,109],[114,116,128],[119,121,125],[101,105,116],[101,107,123],[116,120,127]]),
([v74,v91,v0,v1,v3,v11,v16],[7],[0,1,6,7,10,12,15,22,26,30,35,80,81,84,88,89,105,106,114,116,125,128,188,190,222,223,225,233,234,235,242,255],[[0,119,128],[103,110],[114],[101,109],[112,113,117],[119,125,126],[103,123],[118,127,131],[101,122],[112,130],[],[103,104,110],[100,101,115],[103,106,111],[103,108,123],[101,102,109],[112,116,129],[118,121,124],[101,105,112],[101,107,122],[112,120,126]]),
([v74,v97,v0,v1,v3,v11,v16],[],[0,1,5,6,7,9,10,12,15,19,24,30,35,49,54,80,81,84,88,89,96,105,106,114,116,117,126,127,181,184,222,223,225,233,247,249,250,252],[[],[104,112],[118],[101,111],[116,117,122],[124,127,131],[104,105,114],[125],[101,102,113],[116,136,137],[132,134,135],[104,106,112],[100,101,119],[104,108,115],[104,110,129],[101,103,111],[116,121,133],[123,126,130],[101,107,116],[101,109,128],[116,120,132]]),
([v74,v97,v0,v2,v3,v11,v16],[],[0,1,3,6,7,8,10,12,15,19,24,28,34,52,56,79,80,81,88,89,96,102,105,108,109,114,116,117,126,128,181,184,222,224,225,235,255],[[],[104,105,112],[126],[101,102,111],[115,117,124],[118,121,134],[104,114],[136],[101,113],[117,123,135],[127,129,133],[104,106,114],[100,101,119],[104,108,116],[104,110,131],[101,103,113],[117,122,124],[125,128,132],[101,107,117],[101,109,130],[117,120,134]]),
([v74,v139,v0,v1,v3,v11,v16],[],[0,1,5,7,10,12,15,19,24,30,35,49,54,80,81,88,89,96,105,106,109,114,116,126,127,133,134,136,181,184,222,223,225,233,247,249],[[],[103,110],[115],[101,109],[114,119,120],[122,124,131],[112],[121,126,127],[101,102,111],[114,125],[132,134,135],[103,104,110],[100,101,116],[103,106,113],[103,108,129],[101,109],[114,118,133],[121,123,130],[101,105,114],[101,107,128],[114,117,132]]),
([v74,v0,v5,v2,v3,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,53,54,57,68,73,79,80,81,88,89,91,96,102,108,109,114,117,128,181,184,224,225,247],[[104,105,112],[0],[124],[101,102,111],[119,121,128],[122,126,135],[104,116,118],[104,106,115],[100,101,123],[104,108,120],[104,110,133],[129],[101,114,117],[121,127,128],[130,131,134],[101,103,113],[121,128],[135,136],[101,107,121],[101,109,132],[121,125,135]]),
([v74,v0,v1,v17,v3,v11,v16],[],[0,1,6,7,10,12,15,19,24,30,35,80,81,84,88,89,96,109,114,116,117,128,145,147,156,159,181,184,222,223,225,233,234,247,249],[[103,110],[114],[119],[101,109],[112,113,132],[129,130],[103,104,110],[103,123,125],[100,101,115],[103,106,111],[103,108,127],[118,120,131],[101,102,109],[112,120,131],[120,121,128],[101,122,124],[117],[130,133,134],[101,105,112],[101,107,126],[112,116,130]]),
([v74,v0,v1,v9,v2,v3,v11],[],[0,1,5,7,9,12,15,30,35,49,54,63,65,80,81,88,89,108,109,114,116,117,125,128,205,209,224,225,235,247],[[103,108],[115],[],[120],[101,107],[114,118],[103,108],[103,112,125],[103,104,110],[100,101,116],[103,106,113],[121,123,126],[119,121],[101,107],[114,117,128],[129],[101,111,124],[114,122,127],[101,102,109],[114,118],[101,105,114]]),
([v74,v0,v1,v9,v3,v11],[],[0,1,6,7,10,12,15,22,26,30,35,80,81,84,88,89,105,106,109,114,116,125,128,134,143,167,171,172,202,207,213,215,222,223,225,232,235,247,252],[[103,110,120],[114],[133],[101,109,120,127],[112,113,117,118,120],[103,104,110,119,123],[103,108,129,131,134,137],[100,101,103,115,135],[103,106,111,112,115,118],[119,122,132,134,136,137],[101,102,109,119,126],[112,116,119,136,138],[101,107,128,130,134,137],[112,121,134,137,138],[101,105,112,124,125]]),
([v74,v0,v1,v9,v3,v11,v16],[7],[0,1,6,7,10,12,15,19,24,30,35,80,81,84,88,89,96,105,106,114,116,126,127,181,184,189,191,211,214,225,233,234,235,238,250,252],[[103,110],[114],[131],[101,109],[112,113,118],[0,120,122],[103,104,110],[103,126,128],[100,101,115],[103,106,111],[103,108,124],[119,130,132],[101,102,109],[112,117,132],[119,121,132],[101,125,127],[112,134,135],[129],[101,105,112],[101,107,123],[112,116,133]]),
([v74,v0,v1,v2,v89,v3,v11],[7],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,88,89,108,109,114,116,117,125,128,181,184,224,225,235,247,255],[[103,110],[115],[120],[0],[101,109],[114,118],[103,110],[103,104,112],[103,108,125],[100,101,116],[103,106,113],[119,121,130],[121,123,126],[101,109],[114,117,128],[127,129],[101,102,111],[114,118],[101,107,124],[114,122,127],[101,105,114]]),
([v74,v0,v1,v2,v3,v11,v16],[7],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,88,89,96,108,109,114,116,117,128,181,184,224,225,235,247,255],[[103,110],[115],[121],[101,109],[114,119],[0,127],[103,110],[103,104,112],[100,101,116],[103,106,113],[103,108,125],[120,122,130],[101,109],[114,118,128],[122,123,126],[101,102,111],[114,119],[127,129],[101,105,114],[101,107,124],[114,117,127]]),
([v74,v0,v1,v2,v3,v11,v293],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,89,102,108,109,114,117,128,223,224,225,235,247,255],[[103,110],[116],[122],[101,109],[114,118],[],[103,110],[103,104,112],[100,101,115],[103,106,113],[103,108,110],[119,120,127],[101,109],[114,117,125],[120,121,123],[101,102,111],[114,118],[124,126],[101,105,114],[101,107,109],[114,118]]),
([v74,v0,v1,v46,v3,v11,v16],[0],[0,1,5,7,9,12,15,19,24,30,35,80,81,84,89,91,96,106,108,114,116,117,127,128,181,184,223,224,225,235,247,250],[[103,110],[115],[0],[101,109],[112,113,117],[120,122,126],[103,110],[103,104,110],[100,101,114],[103,106,111],[103,108,125],[119],[101,109],[112,118,129],[121,123,127],[101,102,109],[112,131],[128,130],[101,105,112],[101,107,124],[112,116,128]]),
([v74,v0,v1,v3,v163,v11,v16],[0],[1,4,5,6,7,10,14,15,22,24,33,35,68,80,81,88,89,96,108,109,114,116,117,128,172,178,183,184,222,223,225,233,247,255],[[104,111],[115],[102,110,124],[0,121,124],[114,119],[124,125,129],[104,105,111],[101,102,116],[104,116],[104,107,113],[104,109,127],[102,103,112],[120,122,133],[114,118,131],[122,123,128],[100],[102,106,114],[102,108,126],[114,119],[130,132],[114,117,130]]),
([v75,v0,v1,v9,v2,v3,v11],[7],[0,1,5,7,9,12,15,30,35,49,54,63,65,80,81,84,88,89,106,116,205,209,224,225,235,246,247,249,252],[[103,108],[116],[123],[0,119],[101,107],[114,128],[103,108],[103,112,121],[103,104,110],[100,101,117],[103,106,113],[122,124,127],[119,124],[101,107],[114,124,128],[126],[101,111,120],[114,125,127],[101,102,109],[114,115,118],[101,105,114]]),
([v75,v0,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,84,88,89,96,106,116,127,181,184,224,225,233,234,235,238,247,249,252,255],[[103,110],[116],[120,127,133],[101,109],[114,132],[125,131],[103,110],[103,104,112],[100,101,117],[103,106,113],[103,108,123],[120,126,133],[101,109],[114,128,132],[124,128,131],[101,102,111],[114,115,119],[120,121,130],[101,105,114],[101,107,122],[114,118,129]]),
([v77,v0,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,84,88,89,96,108,109,114,116,117,128,181,184,223,225,234,249,252,255],[[103,110],[116],[122,129,132],[101,109],[114,120,131],[128,130],[103,110],[103,104,112],[100,101,117],[103,106,113],[103,108,126],[121,123,132],[101,109],[114,119,131],[123,124,130],[101,102,111],[114,115,129],[127,128],[101,105,114],[101,107,125],[114,118,128]]),
([v44,v0,v1,v268,v3,v11,v16],[],[1,3,5,8,12,19,28,29,35,37,40,46,49,54,72,79,80,81,84,88,89,91,96,102,106,114,116,127,134,181,195,223,225,239,252],[[108,109,114],[119,121,128],[],[100,102,112],[117,118,124],[126,127,131],[103,108,119],[113],[100,107,120],[108,110,116],[108,111,130],[125],[100,101,106],[115,117,134],[119,123,133],[100],[117],[132],[100,104,117],[100,105,129],[117,122,132]]),
([v44,v0,v1,v2,v3,v11,v16],[7],[1,3,7,8,12,19,28,29,35,40,46,52,54,56,79,80,81,88,89,96,102,109,114,116,117,181,195,224,225,235],[[102,108,113],[117,124],[123],[100,111],[116,121],[0,128],[103,108,113],[108,112,113],[100,107,118],[108,109,115],[108,110,126],[117,122,124],[100,101,106],[114,116,129],[117,120,127],[100,111],[116,121],[128],[100,104,116],[100,105,125],[116,119,128]]),
([v44,v0,v1,v3,v11,v16],[],[1,3,5,7,8,12,19,28,29,30,35,40,46,49,52,54,79,80,81,84,88,89,91,96,102,106,109,114,116,127,143,167,171,172,181,188,195,200,222,223,225,232,233,234,242,249,252,255],[[103,110,115,128,147],[120,122,127,128,147],[100,102,113,114,128,133],[118,119,125,126,128,143],[128,129,139,140,143],[104,110,115,120,127],[100,108,110,121,141],[110,111,117,118,121,126],[110,112,136,137,140,145],[100,101,107,109,120,132],[116,118,120,142,146],[120,124,138,140,142,145],[100,105,118,130,131],[100,106,134,135,140,145],[118,123,140,144,145]]),
([v294,v0,v1,v2,v3,v11,v16],[7],[1,3,7,8,12,15,19,24,28,34,52,56,79,81,88,93,96,102,106,109,114,116,117,127,172,181,184,224,225,235,258],[[102,111],[114,122],[124],[100,110],[113,119],[0,128],[102,103,109],[102,111],[100,102,115],[102,105,119],[102,107,126],[114,120,121],[100,101,108],[112,113,129],[114,117,127],[100,110],[113,118,119],[121,123,130],[100,104,113],[100,106,125],[113,116,128]]),
([v86,v0,v1,v2,v3,v11,v16],[0,7],[1,3,7,8,15,24,29,30,34,42,49,52,56,59,80,81,88,89,96,108,109,114,116,117,128,184,193,224,225,235,247,255],[[102,112],[0,116,123],[122],[100,107,111],[115,120],[1,128],[102,103,108],[102,112],[102,106,117],[102,104,114],[102,105,125],[121,123,131],[101,107,111],[115,119,129],[123,124,127],[107,110,111],[115,120],[128,130],[107,113,115],[107,109,126],[115,118,128]]),
([v88,v72,v0,v1,v3,v11,v16],[],[0,1,3,7,8,9,14,19,24,28,34,81,88,89,91,102,106,108,109,116,117,125,131,143,181,184,223,224,225,229,232,235,247,249],[[119],[103,113],[112,114,120],[101,123],[111],[128,132],[105],[112,120],[101,129,130],[116,118,122],[126,128,133],[103,104,110],[100,101,113],[103,113],[103,108,125],[101,102,109],[112,117,131],[112,115,127],[101,106,118],[101,107,124],[118,121,128]]),
([v88,v0,v5,v1,v3,v11,v16],[],[0,1,3,7,8,14,17,19,24,28,33,34,37,67,72,81,88,89,91,102,106,109,116,117,125,143,181,184,223,225,234,239,247,249,250,255],[[103,117],[122],[116,118,135],[101,125],[115],[129,132],[103,112,114],[103,104,111],[100,101,117],[103,106,117],[103,108,127],[123],[101,110,113],[120,121,130],[128,129,133],[101,102,109],[116,121,134],[116,119,131],[101,105,121],[101,107,126],[121,124,129]]),
([v88,v0,v1,v17,v2,v3,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,59,61,79,80,81,84,88,89,96,102,106,108,109,117,125,181,184,223,224,225],[[104,108,118],[117,119,128],[0],[120],[101,107,119],[119,123,134],[104,105,112],[104,116,127],[104,106,114],[100,101,122],[104,110,131],[121,126,127],[121,128],[101,102,111],[121,124,133],[125],[101,115,127],[127,129,134],[101,103,113],[132,134],[101,109,130]]),
([v88,v0,v1,v9,v2,v3,v11],[4],[0,1,3,5,7,8,9,28,34,49,54,59,61,63,65,81,88,89,106,108,109,116,117,125,128,143,205,209,223,224,225,235],[[104,117],[116,122],[0],[121],[101,125],[115],[104,105,108],[104,114,127],[104,106,110],[100,101,117],[104,112,117],[116,124,129],[116,122],[101,102,107],[116,119,131],[128],[101,113,126],[120,123,130],[101,103,109],[118,120],[101,111,120]]),
([v88,v0,v1,v9,v3,v11],[1,4,8],[0,1,3,7,8,14,17,22,26,28,30,34,35,81,88,89,91,105,106,114,116,117,125,128,131,143,165,172,173,202,207,213,215,222,223,232,235,247,249,252],[[103,115,120],[114,116,119,120,121],[1,2,137],[101,120,125,127],[0,113],[103,104,111,112,114,121],[103,108,130,132,134,138],[100,101,103,115,135],[103,106,115,118,124],[114,123,133,134,136,138],[101,102,109,110,114,128],[114,117,118,136,139],[101,107,129,131,134,138],[118,122,134,138,139],[101,105,118,125,126]]),
([v88,v0,v1,v2,v27,v3,v11],[1,4],[0,1,3,5,7,8,9,19,24,28,34,49,54,59,61,81,88,89,106,108,109,116,117,125,128,143,181,184,223,224,225,234,235],[[104,117],[116,122],[121],[1],[101,125],[115],[104,105,110],[104,106,112],[104,108,127],[100,101,117],[104,114,117],[116,122],[116,124,129],[101,102,109],[116,119,132],[0,128,130],[101,103,111],[118,120,131],[101,107,126],[120,123,130],[101,113,120]]),
([v88,v0,v1,v54,v3,v11,v16],[0],[1,3,4,7,9,10,14,17,19,26,28,36,81,88,91,102,106,108,109,116,117,125,143,147,181,186,223,224,225,229,230,233,234,235,247,255],[[104,123,135],[113,114,120],[0,119,132],[100,122],[112],[128,134],[104,105,111],[103],[100,102,130],[104,107,118],[104,109,125],[113,131],[100,101,110],[113,117,133],[113,115,127],[0,100,129],[116,118,132],[126,128],[100,106,118],[100,108,124],[118,121,128]]),
([v90,v0,v1,v9,v2,v3,v11],[1,7],[0,1,3,5,7,8,9,28,34,49,54,63,65,81,88,89,91,114,116,143,205,209,223,224,225,235,246,249,252],[[104,115],[114,125],[127],[0,1,118],[101,119],[113],[104,105,108],[104,112,121],[104,106,110],[100,101,115],[104,115],[114,123,124],[114,116,117],[101,102,107],[114,125],[122],[101,111,120],[124,126,128],[101,103,109],[118,128],[101,119]]),
([v91,v72,v0,v1,v3,v11,v16],[],[0,1,3,7,8,9,12,15,22,28,34,79,80,81,88,89,100,106,109,114,116,120,128,188,190,223,224,225,234,235,242,244],[[128],[103,124],[114,131],[101,123],[113,130],[],[105],[114,119,120],[101,120,121],[113,117,118],[120,125,127],[103,104,110],[100,101,115],[103,107,112],[103,124],[101,102,109],[111,113,129],[114,122,126],[101,106,113],[101,108,123],[113,116,127]]),
([v91,v0,v5,v1,v3,v11,v16],[],[0,1,3,7,8,12,15,22,26,28,33,34,37,67,72,79,80,81,84,88,89,106,114,116,125,188,190,223,225,234,242,244,252],[[103,126],[129],[119,131],[101,125],[117,130],[],[103,112,114],[103,104,111],[100,101,120],[103,106,116],[103,108,126],[122],[101,110,113],[117,118,121],[123,127,128],[101,102,109],[115,117,132],[119,128,131],[101,105,117],[101,107,125],[117,124,128]]),
([v91,v0,v1,v9,v2,v3,v11],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,63,65,79,80,81,84,88,89,91,96,102,106,114,125,127,128,181,184,205,209,223,224,225,235,238,239],[[104,110,132],[121,125,140],[0],[129],[101,109,131],[119,124,139],[104,105,112],[104,116,134],[104,106,114],[100,101,122],[104,108,118],[121,130,136],[121,123,127],[101,102,111],[117,119,138],[135],[101,115,133],[119,128,137],[101,103,113],[119,120,126],[101,107,119]]),
([v91,v0,v1,v54,v3,v11,v16],[7],[1,3,4,7,9,10,12,17,22,26,28,36,79,81,83,88,100,106,114,116,128,169,188,191,209,223,224,225,232,234,235,242,244,255],[[104,123,133],[115,132],[0,119,129],[100,122],[113,131],[],[104,105,111],[103],[100,102,128],[104,107,114],[104,109,124],[115,118],[100,101,110],[112,113,130],[115,120,126],[100,119,121],[113,117],[119,125,127],[100,106,113],[100,108,122],[113,116,127]]),
([v295,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,8,12,15,19,24,28,34,37,49,54,56,79,80,81,84,88,89,91,96,102,106,114,116,117,127,181,184,223,225,239,252],[[115],[128],[],[0,101],[0,118],[1,133],[104,105,111],[104,112,114],[100,101,121],[104,107,117],[104,109,131],[120,122,126],[101,102,110],[116,118,135],[120,124,134],[101,103,113],[118,119,125],[127,129,132],[101,106,118],[101,108,130],[118,123,133]]),
([v296,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,8,9,12,19,24,28,34,40,49,54,79,80,81,84,88,89,91,96,102,106,116,117,127,134,146,181,184,223,224,225,235],[[129],[126],[125],[0,101],[],[1,134],[104,105,111],[104,106,114],[100,101,120],[104,112,116],[104,109,131],[119,121,128],[101,102,110],[115,117,135],[119,123,133],[101,103,113],[117,118,124],[125,127,132],[101,107,117],[101,108,130],[117,122,134]]),
([v297,v0,v1,v2,v3,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,28,34,46,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,190,223,224,225,235,252],[[130],[134],[126],[0,101],[0,117],[],[104,105,111],[104,106,114],[100,101,120],[104,108,116],[104,112,129],[119,121,125],[101,102,110],[115,117,135],[119,123,132],[101,103,113],[117,118,124],[126,127,131],[101,107,117],[101,109,128],[117,122,133]]),
([v298,v0,v1,v2,v3,v11,v16],[],[0,1,3,7,8,9,12,15,19,24,28,33,34,52,56,72,79,80,81,84,88,89,96,102,106,114,116,127,136,181,184,223,224,225,235,249,252,255],[[114],[128],[137],[101,113],[118,136],[133,135],[103,104,112],[103,105,115],[100,101,121],[103,107,117],[103,109,130],[120,125,126],[101,102,110],[116,118,134],[120,123,132],[101,111,113],[118,119,124],[126,127,131],[101,106,118],[101,108,129],[118,122,133]]),
([v299,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,15,19,24,28,34,49,54,79,80,81,84,88,89,96,106,113,114,116,117,127,128,143,146,181,184,223,224,225,235,249,252,255],[[129],[118],[124,138],[101,128],[137],[134,136],[104,105,111],[104,106,113],[100,101,119],[104,107,115],[104,109,131],[123,124,138],[101,102,110],[114,116,135],[125,127,133],[101,103,112],[116,117,121],[124,126,132],[101,116,122],[101,108,130],[116,120,134]]),
([v300,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,24,28,34,42,49,54,79,80,81,84,88,89,91,96,106,114,116,127,128,188,190,195,223,224,225,235,244,249,252,255],[[129],[135],[125,138],[101,128],[117,137],[136],[104,105,111],[104,106,114],[100,101,120],[104,108,116],[104,109,130],[119,121,124],[101,102,110],[115,117,134],[119,127,132],[101,103,113],[117,118,123],[125,126,131],[101,107,117],[101,112,128],[117,122,133]]),
([v93,v97,v0,v2,v3,v11,v16],[],[1,3,7,12,19,27,28,33,34,37,39,45,52,71,73,78,79,81,84,87,88,96,102,105,108,114,117,126,128,134,181,194,222,224,225,235,239,252,255],[[120,126],[102],[120,125,129],[100,101,106],[116,117,137],[120,122,136],[108,114,126],[138],[100,112],[117,124,135],[126,128,133],[108,109,113],[100,105,119],[108,110,115],[108,111,131],[100,107,112],[117,118,123],[125,127,132],[100,103,117],[100,104,130],[117,121,134]]),
([v93,v110,v0,v2,v3,v11,v16],[],[1,3,5,7,12,19,27,28,34,35,36,39,45,49,71,78,79,81,84,87,88,91,96,102,106,108,109,114,116,117,121,127,128,134,181,194,223,224,225,239,252,255],[[],[103],[120,121,133],[100,101,107],[116,117,140],[120,123,139],[109],[127,128,141],[100,129,130],[117,125,126],[129,132,137],[108,110,114],[100,106,119],[108,111,115],[108,112,135],[100,102,113],[117,118,124],[128,131,136],[100,104,117],[100,105,134],[117,122,138]]),
([v93,v110,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,27,29,30,34,35,36,37,39,40,45,46,49,54,71,72,78,80,81,84,88,89,96,106,116,117,127,181,184,194,195,223,225],[[],[128],[103,104,121],[100,101,111],[103,106,126],[103,108,136],[133],[113,115,123],[101,110,129],[113,117,125],[113,119,138],[112,114,122],[101,109,111],[112,116,124],[112,118,137],[101,102,120],[126,127,131],[132,134,139],[101,105,126],[101,107,135],[126,130,140]]),
([v93,v136,v1,v2,v3,v11,v16],[0],[0,1,5,7,8,9,12,15,19,24,29,30,34,35,37,40,46,49,54,72,80,81,84,96,106,108,114,116,117,127,128,181,184,195,223,224,225,235,255],[[0],[104],[103,105,118],[100,101,111],[103,107,121],[103,109,132],[112],[113,114,119],[101,110,111],[113,115,120],[113,116,133],[126,127,138],[101,111],[121,125,137],[128,130,135],[101,102,117],[121,122,124],[127,129,134],[101,106,121],[101,108,131],[121,123,136]]),
([v93,v0,v5,v2,v3,v11,v16],[],[1,3,5,7,12,19,27,28,34,36,39,45,49,70,73,74,78,79,81,87,88,91,96,102,108,109,114,117,128,136,181,194,224,225,239,247,252,255],[[103],[129],[120,121,137],[100,101,107],[117,118,136],[120,123,134],[108,114,115],[108,109,115],[100,106,119],[108,110,116],[108,111,131],[126],[100,113],[118,124,125],[127,128,132],[100,102,112],[118,125],[133,135],[100,104,118],[100,105,130],[118,122,133]]),
([v93,v0,v1,v9,v2,v3,v11],[],[1,5,7,12,29,30,34,35,37,40,49,63,72,80,81,84,88,89,106,108,114,116,117,125,128,205,223,224,225,235,249,252],[[102],[116],[128,130],[121],[100,105],[114,131],[106,107,122],[107,128,130],[107,108,112],[100,104,117],[107,109,113],[122,124,127],[120,121],[100,105],[114,119,129],[126],[100,111,125],[114,123,128],[100,101,110],[114,115,118],[100,103,114]]),
([v93,v0,v1,v2,v3,v11,v16],[],[1,5,7,12,19,29,30,34,35,37,40,46,49,72,80,81,84,88,89,96,106,108,114,116,117,127,128,181,195,223,224,225,235,249,252,255],[[102],[117],[123,135],[100,106],[115,134],[131,133],[107,108,124],[108,109,113],[100,105,118],[108,110,114],[108,111,128],[122,123,135],[100,106],[115,121,132],[124,126,130],[100,101,112],[115,116,120],[123,125,129],[100,103,115],[100,104,127],[115,119,131]]),
([v93,v0,v268,v2,v3,v11,v16],[0],[1,3,5,8,12,19,28,29,34,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,108,114,116,117,127,128,134,170,181,195,223,224,225,235,239,252],[[103],[0],[119,121,131],[100,101,106],[115,117,140],[119,123,139],[108],[109,110,114],[100,107,120],[109,111,116],[109,112,134],[126,127],[100,128,132],[117,125,138],[128,130,136],[100,102,113],[117,118,124],[127,129,135],[100,104,117],[100,105,133],[117,122,137]]),
([v301,v0,v1,v2,v3,v11,v16],[],[1,3,5,7,12,19,28,49,79,81,84,88,91,102,106,109,114,116,117,125,127,181,195,197,198,200,223,224,225,232,235,249,255],[[103],[111,118],[117,132],[100,124],[109,115],[128,131],[111,118],[117,125,132],[100,123,129],[109,115],[122,125,128],[111,112,116],[100,101,106],[108,109,130],[111,113,127],[100,102,107],[109,110,114],[117,120,126],[100,104,109],[100,105,121],[109,119,128]]),
([v302,v0,v1,v2,v3,v11,v16],[0],[1,3,5,7,12,19,28,49,80,81,87,88,89,103,106,108,109,114,116,117,125,127,128,151,181,223,224,225,232,234,235,249,252,255],[[103],[0,111,119],[118,133],[100,128],[109,116,132],[127,131],[110,112,119],[112,118,133],[100,112,123],[108,112,116],[112,113,127],[117,118,133],[100,101,106],[115,116,130],[119,122,126],[100,102,107],[114,116,129],[118,121,125],[100,104,116],[100,105,124],[116,120,127]]),
([v303,v0,v1,v2,v3,v11,v16],[],[1,3,5,7,12,19,28,49,69,70,72,73,74,79,81,88,91,96,102,106,109,114,116,117,127,181,223,224,225,232,235,249,255],[[103],[115,123],[122,132],[100,109],[114,120],[128,131],[111,112,123],[110,112,122],[100,108,129],[112,114,120],[112,128,131],[115,116,121],[100,101,106],[113,114,130],[115,118,127],[100,102,107],[114,119,120],[122,124,126],[100,104,114],[100,105,125],[114,117,128]]),
([v304,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,96,102,106,114,116,117,127,158,160,181,184,223,224,225,235,249,252,255],[[104,129],[126],[138],[101,128],[137],[134,136],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,131],[119,124,125],[101,102,111],[115,117,135],[119,122,133],[101,103,113],[117,118,123],[125,127,132],[101,107,117],[101,109,130],[117,121,134]]),
([v305,v0,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,76,79,80,81,84,88,89,91,106,114,125,213,215,223,224,225,235,249,252],[[104,125],[129],[130],[],[101,124],[116,131],[104,105,110],[104,125],[104,106,112],[100,101,119],[104,108,115],[118,127,128],[118,120,122],[101,102,109],[114,116,131],[126],[101,113,124],[116,123,128],[101,103,111],[116,117,121],[101,107,116]]),
([v305,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,213,215,223,224,225,235,249,252,255],[[104,131],[135],[138],[101,130],[117,137],[136],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,137],[119,123,133],[101,103,113],[117,118,124],[126,127,132],[101,107,117],[101,109,128],[117,122,134]]),
([v97,v104,v0,v2,v3,v11,v16],[0],[0,1,6,7,10,16,19,24,52,56,78,79,84,87,88,89,94,102,105,108,113,114,116,117,127,143,146,181,184,222,224,225,235,239,249,252,255],[[0,114,123],[103,109],[136],[101,108],[111,119,132],[130,131,134],[103,113,126],[114,121,122],[101,114,125],[135],[114,117,133],[103,104,109],[100,101,115],[103,105,110],[103,107,128],[101,102,108],[111,112,118],[122,124,129],[101,111,120],[101,106,127],[111,116,131]]),
([v97,v72,v0,v1,v3,v11,v16],[],[0,1,3,5,7,8,12,15,19,24,28,34,37,49,54,79,80,81,88,89,91,96,102,106,109,114,116,120,127,181,184,223,225,239,247,249,250,252,255],[[126,138],[104,114,138],[120],[101,103,113],[117,136,137],[132,134,135],[112],[118,125,126],[101,126,127],[117,123,124],[126,128,131],[104,105,111],[100,101,119],[104,107,116],[104,109,130],[101,102,110],[115,117,137],[118,122,133],[101,106,117],[101,108,129],[117,121,132]]),
([v97,v136,v0,v2,v3,v11,v16],[],[0,1,3,7,10,12,15,19,24,28,33,34,52,56,79,81,84,88,96,102,105,108,109,114,117,126,128,136,181,184,222,224,225,232,235,255],[[127],[103,113],[135],[101,112],[115,121,134],[124,126,131],[111],[117,123],[101,102,109],[114,115,122],[117,119,132],[103,104,113],[100,101,133],[103,106,122],[103,108,129],[101,110,112],[115,116,120],[123,125,130],[101,105,115],[101,107,128],[115,118,132]]),
([v97,v0,v5,v1,v3,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,33,34,37,49,54,67,72,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,223,225,239,247,249,250,252],[[104,106,116],[0],[125],[101,103,115],[121,139,140],[135,137,138],[104,114,118],[104,105,113],[100,101,124],[104,108,120],[104,110,133],[129],[101,112,117],[121,122,128],[130,131,134],[101,102,111],[119,121,140],[123,127,136],[101,107,121],[101,109,132],[121,126,135]]),
([v97,v0,v156,v2,v3,v11,v16],[],[0,1,6,7,10,12,15,19,24,52,56,79,87,88,89,102,114,116,117,127,140,181,184,222,224,225,233,235,237,246,249,252,255],[[103,110],[118],[132],[101,109],[127,128,131],[124,125,130],[103,112,113],[103,104,110],[100,101,114],[103,106,114],[103,108,122],[113,116,117],[101,113],[111],[113,115,125],[101,102,109],[117,126],[117,119,123],[101,105,120],[101,107,121],[125,129,130]]),
([v97,v0,v1,v9,v2,v3,v11],[],[0,1,3,7,8,12,15,28,33,34,37,52,56,63,65,79,80,81,84,88,89,106,114,116,117,125,205,209,223,225,249,252],[[103,112],[124],[129,130],[],[101,111],[117,131],[103,104,109],[103,114,127],[103,110,112],[100,101,120],[103,106,116],[119,129,130],[119,122,123],[101,102,107],[115,117,131],[128],[101,113,126],[117,125,129],[101,108,111],[117,118,121],[101,105,117]]),
([v97,v0,v1,v2,v3,v11,v16],[],[0,1,3,7,8,12,15,19,24,28,33,34,37,52,56,79,80,81,84,88,89,96,102,106,114,116,117,127,181,184,223,225,239,249,252,255],[[103,114],[126],[135],[101,113],[117,134],[131,133],[103,104,111],[103,112,114],[100,101,120],[103,106,116],[103,108,129],[119,124,125],[101,102,109],[115,117,134],[119,122,132],[101,110,113],[117,118,123],[125,127,130],[101,105,117],[101,107,128],[117,121,131]]),
([v97,v0,v1,v54,v3,v11,v16],[],[1,3,5,7,9,10,12,19,28,32,37,49,56,61,65,79,81,83,88,91,96,102,106,114,116,127,169,181,196,223,225,230,234,239,247,249,250,252],[[104,110,112],[119],[],[100,102,111],[116,136,137],[130,134,135],[105,110,112],[103],[100,109,131],[110,113,117],[110,114,128],[118,123],[100,101,108],[115,116,137],[118,121,133],[100,124,126],[116,122,132],[124,125,129],[100,106,116],[100,107,127],[116,120,130]]),
([v97,v0,v2,v46,v3,v11,v16],[0],[0,1,3,7,8,12,15,19,24,28,33,34,37,52,56,79,80,81,84,88,89,91,96,102,106,108,114,116,117,127,128,181,184,223,224,225,235,239],[[103,114],[121],[0],[101,113],[117,125,136],[128,130,134],[103,112,114],[103,104,111],[100,101,120],[103,106,116],[103,108,132],[126],[101,110,113],[117,118,124],[127,129,133],[101,102,109],[115,117],[119,123,137],[101,105,117],[101,107,131],[117,122,135]]),
([v97,v0,v2,v3,v158,v11,v16],[0],[1,2,3,6,7,10,15,20,24,53,56,67,79,80,81,84,87,88,89,96,102,106,113,114,116,117,127,166,173,179,182,184,222,224,225,235,239,252,255,256],[[104,110],[138],[102,109,128],[0,117,125],[114,127,135],[128,129,133],[104,105,110],[101,102,118],[104,116,139],[104,106,113],[104,108,131],[102,103,111],[117,123,124],[114,115,121],[124,126,132],[100],[102,114,122],[102,107,130],[112,114,137],[117,120,136],[114,119,134]]),
([v98,v0,v1,v2,v3,v11,v16],[4],[0,1,3,7,8,12,15,19,24,28,34,52,56,79,80,81,88,89,96,102,109,116,117,181,184,223,225,234,238,239,249,252],[[103,112],[116,122],[121],[101,111],[115,120],[0,126,130],[103,104,110],[103,112],[100,101,117],[103,106,114],[103,108,124],[116,122],[101,102,109],[113,115,131],[116,119,129],[101,111],[115,120],[125,127],[101,105,115],[101,107,123],[115,118,128]]),
([v306,v0,v1,v2,v3,v11,v16],[7],[0,1,3,7,8,12,15,19,24,28,34,52,56,79,80,81,88,89,96,102,106,109,114,116,117,127,181,184,224,225,234,235,252,258],[[103,112],[116,124,131],[130],[101,111],[115,121,132],[0,129],[103,104,110],[103,112],[100,101,117],[103,106,114],[103,108,127],[116,122,123],[101,102,109],[113,115,131],[116,119,128],[101,111],[115,120,123],[123,125,133],[101,105,115],[101,107,126],[115,118,129]]),
([v14,v0,v1,v2,v3,v11,v16],[],[1,5,7,9,12,19,29,30,34,35,40,46,49,56,80,81,84,88,89,96,106,114,116,127,181,195,223,225,249,252,255],[[102,109,113],[117],[122,130],[100,107],[115,129],[127,128],[108,109,113],[103,109,113],[100,106,118],[109,110,114],[109,111,125],[121,122,130],[100,107],[115,129],[127,128],[100,101,112],[115,116,120],[122,123,126],[100,104,115],[100,105,124],[115,119,127]]),
([v14,v0,v2,v54,v3,v11,v16],[],[1,3,5,9,12,19,28,34,49,51,56,57,61,65,73,79,81,84,88,91,96,102,109,114,117,181,209,224,225,232,235,247,255],[[110,111,114],[118,119,124],[],[100,101,106],[115,116,130],[118,121,127],[103,110,132],[107],[100,109,129],[110,112,122],[110,113,126],[123],[100,102,108],[116,117,122],[128,131],[100],[116],[128],[100,104,116],[100,105,125],[116,120,128]]),
([v14,v0,v2,v3,v11,v16],[],[1,3,5,7,9,12,19,27,28,30,34,39,45,49,52,56,78,79,81,84,87,88,91,96,102,105,109,114,117,126,143,167,171,173,181,188,194,199,222,224,225,232,233,235,242,249,252,255],[[103,110,115,121,128],[121,122,127,128,147],[100,101,108,109,121,133],[117,118,121,143,146],[121,124,139,140,143,145],[104,110,115,127,147],[100,107,110,120,141],[110,111,116,118,120,126],[110,112,136,137,140,145],[100,102,113,114,127,132],[118,119,125,126,127,142],[127,129,138,140,142],[100,105,118,130,131],[100,106,134,135,140,145],[118,123,140,144,145]]),
([v307,v0,v1,v2,v3,v11,v16],[],[1,5,7,9,12,15,19,24,30,35,49,54,80,81,84,88,89,96,106,108,114,116,117,127,128,181,184,223,225,249,252,255],[[102,109],[115],[121,131],[100,108],[113,130],[128,129],[102,109],[102,103,111],[100,102,116],[102,105,112],[102,107,126],[120,121,131],[100,108],[113,119,130],[122,124,129],[100,101,110],[113,114,118],[121,123,127],[100,104,113],[100,106,125],[113,117,128]]),
([v308,v0,v1,v2,v3,v11,v16],[0],[1,5,7,9,15,24,28,29,30,35,42,52,54,59,79,80,81,84,88,89,96,102,106,114,116,117,127,184,193,223,225,239,249,252,255],[[102,109],[125],[0,124,134],[100,108,111],[116,133],[130,132],[102,109],[102,103,112],[102,107,119],[102,104,115],[102,105,127],[118,123,124],[106,108,111],[114,116,133],[118,121,131],[101,108,111],[116,117,122],[124,126,129],[108,113,116],[108,110,128],[116,120,130]]),
([v104,v110,v0,v2,v3,v11,v16],[],[0,1,5,7,8,9,19,24,49,54,78,79,82,87,88,91,94,102,106,108,109,113,116,117,127,134,143,146,181,184,223,224,225,231,232,233,239,249,252,255],[[123],[103,113,127],[114,115,125],[101,114,126],[138],[114,117,136],[104],[122,135,139],[101,133,134],[111,119,120],[131,132,137],[103,105,109],[100,101,134],[103,110,111],[103,107,129],[101,102,108],[111,112,118],[122,124,130],[101,111,121],[101,106,128],[111,116,132]]),
([v104,v0,v5,v2,v3,v11,v16],[],[0,1,5,7,9,16,19,24,49,53,54,57,68,73,78,79,82,87,88,89,91,94,102,108,109,113,116,117,143,146,181,184,224,225,239,247,249,252,255],[[103,117,129],[127],[118,120,138],[101,118,128],[137],[118,122,134],[103,111,113],[103,104,110],[100,101,119],[103,105,114],[103,107,131],[126],[101,109,112],[115,123,124],[132,133,136],[101,102,108],[115,116,124],[133,135],[101,115,125],[101,106,130],[115,121,133]]),
([v104,v0,v156,v1,v2,v3,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,40,49,54,79,80,81,84,89,96,106,113,116,127,140,141,181,184,223,224,225,233,237,246,249,250,252,255],[[104,108,127],[0],[134],[124,137,138],[101,107,126],[132,135,136],[104,113,117],[104,105,112],[104,106,115],[100,101,120],[104,110,129],[116],[118,119,122],[101,118,123],[118,121,132],[124,133,139],[101,102,111],[131,132,136],[101,103,114],[124,125,130],[101,109,128]]),
([v104,v0,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,28,34,40,49,54,63,65,79,80,81,84,88,89,106,113,116,125,143,146,205,209,223,224,225,235,249,252],[[104,125],[118],[130,132],[122],[101,124],[133],[104,105,108],[104,113,127],[104,106,111],[100,101,119],[104,109,115],[129,130,132],[122,131],[101,102,107],[114,116,131],[128],[101,112,126],[116,123,130],[101,103,110],[116,117,120],[101,116,121]]),
([v104,v0,v268,v2,v3,v11,v16],[0],[1,2,5,7,8,10,16,19,25,49,55,79,80,82,88,89,91,94,102,106,108,113,116,117,118,127,134,143,181,185,223,224,225,231,233,235,239,252],[[104,114,124],[0,114,123],[114,116,126],[100,114,127],[137],[114,118,136],[103],[104,105,110],[100,101,115],[104,106,112],[104,108,129],[122,134],[0,100,133],[111,120,135],[131,132],[100,102,109],[111,113,119],[122,125,130],[100,111,121],[100,107,128],[111,117,132]]),
([v309,v310,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,34,46,49,54,79,80,81,84,88,89,91,102,106,114,116,125,127,181,184,220,223,224,225,246,247,249,252],[[133,136],[104,129,136],[122],[125,135,136],[101,109,128],[117,134,136],[112],[119,132,133],[125,127,131],[101,130,133],[117,126,133],[104,105,111],[104,106,114],[100,101,120],[104,108,116],[119,121,124],[101,102,110],[115,117,137],[101,103,113],[117,118,123],[101,107,117]]),
([v309,v0,v311,v1,v2,v3,v11],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,42,46,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,193,195,223,224,225,246,247,249,252],[[104,110,131],[0],[125],[128,138,139],[101,109,130],[119,137,139],[104,114,133],[104,105,112],[104,106,116],[100,101,122],[104,108,118],[135],[128,129,134],[101,113,132],[119,124,136],[121,123,127],[101,102,111],[117,119,140],[101,103,115],[119,120,126],[101,107,119]]),
([v309,v0,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,76,79,80,81,84,88,89,91,102,106,114,116,125,181,184,213,215,223,224,225,249,252],[[104,110,129],[123],[134,135],[126],[101,109,128],[118,136],[104,105,112],[104,131],[104,106,114],[100,101,121],[104,108,117],[120,133,134],[120,122,125],[101,102,111],[116,118,136],[132],[101,115,130],[118,127,134],[101,103,113],[118,119,124],[101,107,118]]),
([v105,v0,v156,v1,v2,v3,v11],[3,6],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,81,88,89,116,140,181,184,223,224,225,233,234,235,237,246,249,252,255],[[104,110,121],[0],[123,124,130],[118,122,124],[101,109,120],[124,129,130],[104,117],[104,105,112],[104,106,114],[100,101,117],[104,108,117],[116],[118,126],[1,101],[115],[118,125,132],[101,102,111],[127,128,131],[101,103,113],[118,126],[101,107,119]]),
([v105,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,96,102,106,109,114,116,117,143,167,172,173,181,184,188,190,223,224,225,232,234,235,249,252,255],[[104,110,138,140,143,147],[123,127,142,143,146,147],[131,141,143,145],[101,109,137,139,143,147],[121,126,143,147,148],[104,105,113,114,123,132],[104,106,117,118,131,149],[100,101,104,124,144],[104,108,120,121,124,129],[123,125,130,131,132,149],[101,102,111,112,123,136],[119,121,123,146,148],[101,103,115,116,131,135],[121,122,128,129,131,145],[101,107,121,133,134]]),
([v107,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,19,24,28,34,49,54,81,88,89,91,102,106,108,109,113,116,117,125,143,181,184,223,224,225,233,234,235,249,255],[[104,115],[114,123,133],[122,132,135],[101,125],[113],[130,134],[104,105,110],[104,106,112],[100,101,115],[104,115],[104,108,127],[114,116,131],[101,102,109],[114,119,133],[114,117,129],[101,103,111],[118,120,132],[128,130],[101,120,121],[101,107,126],[120,124,130]]),
([v312,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,76,79,80,81,84,88,89,91,106,114,116,125,188,190,223,224,225,234,235,242,244,249,252,255],[[104,126],[118,131,133],[123,130,136],[101,125],[116,132],[134],[104,105,110],[104,106,112],[100,101,119],[104,108,115],[104,126],[118,120,122],[101,102,109],[114,116,135],[118,128,129],[101,103,111],[116,117,121],[123,127,129],[101,107,116],[101,113,125],[116,124,129]]),
([v109,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,74,79,80,81,84,88,89,91,96,102,109,116,117,134,181,184,225,232,239,247,249,252],[[115],[127],[126],[101,132],[118,125],[131,135],[104,105,112],[104,106,114],[100,101,121],[104,108,117],[104,110,130],[120,122,128],[101,102,111],[116,118,136],[120,124,133],[101,103,113],[118,119,125],[131,134],[101,107,118],[101,109,129],[118,123,131]]),
([v313,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,109,116,117,127,131,134,181,184,223,224,225,232,234,235],[[120],[126],[125,136],[0,101],[124],[1,134],[104,105,112],[104,106,114],[100,101,135],[104,108,116],[104,110,131],[119,121,129],[101,102,111],[115,117,137],[119,123,133],[101,103,113],[117,118,128],[125,127,132],[101,107,117],[101,109,130],[117,122,134]]),
([v314,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,181,184,200,225,232,234,235,238,239,252,259],[[129],[133],[126,132],[101,131],[117,137],[130],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,128],[119,121,125],[101,102,111],[115,117,136],[119,123,135],[101,103,113],[117,118,124],[126,132],[101,107,117],[101,109,127],[117,122,134]]),
([v110,v136,v0,v2,v3,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,81,84,88,91,96,102,106,108,109,114,116,117,121,127,128,181,184,223,224,225,232,255],[[0],[105],[125,126,137],[101,127,128],[116,123,124],[127,130,134],[112],[118,119,126],[101,102,111],[115,116,124],[118,121,135],[104,106,114],[100,101,136],[104,108,124],[104,110,132],[101,103,113],[116,117,122],[126,129,133],[101,107,116],[101,109,131],[116,120,135]]),
([v110,v0,v156,v2,v3,v11,v16],[0],[0,1,5,7,8,9,12,15,19,24,49,54,79,87,88,91,102,116,117,127,134,140,141,181,184,223,224,225,231,232,233,234,235,237,246,249,252,255],[[104],[0,114,118],[117,130,137],[101,128,129],[132,133,136],[126,127,135],[103,113,114],[103,105,111],[100,101,129],[103,107,122],[103,109,124],[114,115,120],[101,114],[112],[114,116,127],[101,102,110],[117,131],[117,119,125],[101,106,121],[101,108,123],[127,134,135]]),
([v110,v0,v1,v9,v2,v3,v11],[],[0,1,3,5,7,9,12,15,28,34,35,49,54,63,65,79,81,84,88,91,106,109,116,117,125,134,205,209,223,225,232,249,252],[[110],[123],[129,131],[122],[101,130],[116,121],[104,109,118],[104,114,127],[104,105,112],[100,101,130],[104,107,121],[118,129,131],[118,119,125],[101,102,108],[115,116,132],[128],[101,113,126],[116,124,129],[101,103,111],[116,117,120],[101,106,116]]),
([v110,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,9,12,15,19,24,28,34,35,49,54,79,81,84,88,91,96,102,106,109,116,117,127,134,181,184,223,225,232,239,249,252,255],[[112],[125],[124,136],[101,132],[116,123],[131,134],[104,111,118],[104,105,114],[100,101,132],[104,107,123],[104,109,129],[118,119,127],[101,102,110],[115,116,135],[118,121,133],[101,103,113],[116,117,122],[124,126,130],[101,106,116],[101,108,128],[116,120,131]]),
([v110,v0,v2,v3,v158,v11,v16],[],[1,3,6,7,8,9,15,20,24,50,54,79,81,84,87,88,91,92,96,102,106,109,113,116,117,121,127,134,171,173,179,182,184,223,224,225,232,239,252,255,256],[[104],[123,128,139],[101,125,136],[124],[112,121],[129,130,134],[103,105,110],[101,103,117],[103,114,140],[103,106,121],[103,108,132],[101,102,109],[115,116,127],[112,113,120],[123,126,133],[100],[101,112,122],[101,107,131],[111,112,138],[115,119,137],[112,118,135]]),
([v110,v1,v268,v2,v3,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,29,34,35,37,40,46,49,54,72,79,80,81,84,88,89,91,96,102,106,116,127,134,141,181,184,195,223,225,239,252,256],[[105],[0],[114,115,120],[101,112,126],[114,116,122],[114,117,137],[113],[125,127,133],[101,102,111],[121,123,141],[125,129,140],[104,106,119],[100,101,142],[104,108,134],[104,110,136],[101,103,118],[123,124,130],[131,132,138],[101,107,123],[101,109,135],[123,128,139]]),
([v315,v0,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,84,88,89,106,116,125,127,181,184,223,225,239,241,242,244,249,252,255],[[103,110],[116],[119,132],[101,109],[114,128],[125,130],[103,110],[103,104,112],[100,101,117],[103,106,113],[103,108,123],[119,129,132],[101,109],[114,127,131],[125,126,130],[101,102,111],[114,115,118],[119,121,124],[101,105,114],[101,107,122],[114,120,125]]),
([v316,v0,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,79,81,88,91,102,106,109,116,117,125,127,134,181,184,223,225,232,234,239,249,252,255],[[103,110],[121],[120,134],[101,109],[114,119,133],[128,132],[103,110],[103,104,112],[100,101,129],[103,106,119],[103,108,126],[115,116,124],[101,109],[113,115,133],[115,117,131],[101,102,111],[118,119,130],[120,123,127],[101,105,119],[101,107,125],[119,122,128]]),
([v317,v0,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,88,89,96,106,109,116,127,132,133,134,136,181,184,223,225,249,252,255],[[103,110],[115],[120,132],[101,109],[114,123],[129,130],[103,110],[103,104,112],[100,101,116],[103,106,113],[103,108,127],[120,124,132],[101,109],[114,122,131],[125,129,130],[101,102,111],[114,118,119],[120,121,128],[101,105,114],[101,107,126],[114,117,129]]),
([v112,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,109,116,117,131,160,181,184,223,224,225,235],[[128],[119,126],[125],[0,101],[124],[1,133],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,130],[119,121,126],[101,102,111],[115,117,134],[119,123,132],[101,103,113],[117,118,127],[131,133],[101,107,117],[101,109,129],[117,122,133]]),
([v318,v0,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,79,80,81,84,88,89,91,106,114,138,205,209,215,225,232,235,246,247,249,259],[[126],[118,129],[127],[],[101,128],[116,133],[104,105,110],[104,125,132],[104,106,112],[100,101,119],[104,108,115],[118,129],[118,120,122],[101,102,109],[114,116,129],[131],[101,113,124],[116,123,130],[101,103,111],[116,117,121],[101,107,116]]),
([v318,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,215,225,232,234,235,238,247,259],[[130],[119,134],[133],[101,132],[117,137],[131],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,134],[119,123,134],[101,103,113],[117,118,124],[126,127,136],[101,107,117],[101,109,128],[117,122,135]]),
([v72,v139,v0,v1,v3,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,109,114,116,120,127,131,134,181,184,223,224,225,235,247,249],[[0],[106],[119,126,127],[101,127,128],[117,124,125],[127,129,134],[114],[119,121,131],[101,103,113],[117,118,130],[136,138,139],[104,105,112],[100,101,120],[104,108,116],[104,110,133],[101,102,111],[115,117,137],[119,123,135],[101,107,117],[101,109,132],[117,122,136]]),
([v72,v0,v1,v17,v3,v11,v16],[0],[0,1,3,7,8,9,12,15,19,24,28,34,79,80,81,88,89,91,96,102,109,116,117,135,145,156,181,184,223,224,225,229,232,234,235,236,247,249,255],[[105],[115,122],[0,121,133],[101,131,132],[114,133,135],[128,130,137],[103,104,111],[103,123,138],[100,101,116],[103,107,113],[103,109,127],[115,117,122],[101,102,110],[112,114,134],[115,119,129],[101,124,125],[120],[130,136,137],[101,106,114],[101,108,126],[114,118,130]]),
([v72,v0,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,12,15,28,34,49,54,56,63,79,80,81,84,88,89,91,109,116,117,125,128,205,224,225,232,235,247,249],[[112],[118,123],[128,132],[122],[101,129],[116,121],[104,105,109],[104,128,132],[104,111],[100,101,119],[104,107,115],[118,125,127],[118,120,123],[101,102,108],[114,116,130],[131],[101,113,126],[116,124,128],[101,103,110],[116,117,121],[101,106,116]]),
([v72,v0,v1,v9,v3,v11],[7],[0,1,3,7,8,9,12,15,22,28,30,34,35,79,80,81,88,89,100,106,109,114,116,117,120,128,143,167,172,173,202,207,213,223,224,225,232,235,247,252],[[105],[116,121,122,123],[0,122,133,135,138],[101,122,124,128,136],[115,119,120,122],[103,104,111,112,116,123],[103,131,135,138],[100,101,103,117,136],[103,107,114,115,117,120],[116,125,134,135,137,138],[101,102,109,110,116,129],[113,115,116,137,139],[101,108,130,132,135,138],[115,118,135,138,139],[101,106,115,126,127]]),
([v72,v0,v1,v9,v3,v11,v16],[7],[0,1,3,7,8,9,12,15,19,24,28,34,79,80,81,88,89,96,102,106,109,114,116,120,127,181,184,189,211,214,225,234,235,238,243,250,255],[[105],[115,121,122],[0,122,131],[101,122,123],[114,119,120],[0,122,124],[103,104,111],[103,129,136],[100,101,116],[103,107,113],[103,109,126],[115,132],[101,102,110],[112,114,132],[115,118,132],[101,127,128],[114,134,135],[130],[101,106,114],[101,108,125],[114,117,133]]),
([v72,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,12,15,19,24,28,34,49,54,56,79,80,81,84,88,89,91,96,102,109,116,117,181,184,224,225,232,235,247,249,255],[[114],[119,126],[125],[101,131],[117,124],[130,134],[104,105,111],[104,113,135],[100,101,120],[104,107,116],[104,109,128],[119,121,126],[101,102,110],[115,117,132],[119,123,129],[101,103,112],[117,118,124],[130,133],[101,106,117],[101,108,127],[117,122,130]]),
([v72,v0,v1,v46,v3,v11,v16],[],[0,1,5,7,12,15,19,24,30,35,37,80,81,82,88,89,91,96,106,109,116,117,120,127,128,181,184,223,224,225,235,247,250],[[110],[116,120,121],[],[101,120,122],[112,118,119],[120,123,127],[103,109],[103,109],[100,101,115],[103,105,111],[103,107,126],[114],[101,108],[112,113,130],[116,124,128],[101,102,108],[112,132],[129,131],[101,104,112],[101,106,125],[112,117,129]]),
([v72,v0,v1,v3,v163,v11,v16],[],[1,5,6,7,8,9,14,15,22,24,31,34,79,80,81,84,88,89,91,96,102,109,116,117,120,172,178,183,184,223,224,225,232,235,247],[[105],[116,123],[101,124,132],[122],[114,121],[125,126,129],[103,104,111],[101,103,117],[103,117],[103,107,113],[103,109,128],[101,102,110],[116,118,123],[112,114,133],[116,120,130],[100],[101,106,114],[101,108,127],[114,115,121],[131,134],[114,119,131]]),
([v72,v1,v2,v54,v3,v11,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,51,54,56,57,61,65,73,79,80,81,84,88,89,91,96,102,109,117,181,184,209,224,225,232,235,247],[[116,117,120],[106],[0],[101,114,137],[116,118,130],[116,119,134],[125,127,131],[104,105,112],[101,102,111],[121,123,138],[125,129,135],[115],[101,103,113],[123,124,130],[136,139],[100,101,126],[104,108,122],[104,110,133],[101,107,123],[101,109,132],[123,128,136]]),
([v115,v0,v1,v2,v3,v11,v16],[4],[0,1,3,7,8,12,15,19,24,28,34,52,56,79,80,81,88,89,96,102,109,116,117,181,184,224,225,235,247,249],[[103,112],[116,122],[121],[101,111],[115,120],[0,126,129],[103,104,110],[103,112],[100,101,117],[103,106,114],[103,108,124],[116,122],[101,102,109],[113,115,127],[116,119,125],[101,111],[115,120],[126,128],[101,105,115],[101,107,123],[115,118,126]]),
([v116,v0,v1,v2,v3,v11,v16],[],[0,1,3,7,8,12,15,19,24,28,34,52,56,79,80,81,88,89,91,96,102,109,116,117,181,184,224,225,235,247,249],[[103,112],[116,123],[122],[101,111],[115,121],[127,130],[103,104,110],[103,112],[100,101,117],[103,106,114],[103,108,125],[116,118,123],[101,102,109],[113,115,128],[116,120,126],[101,111],[115,121],[127,129],[101,105,115],[101,107,124],[115,119,127]]),
([v319,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,12,15,19,24,28,34,35,49,54,79,81,84,88,91,96,102,106,109,116,117,127,181,184,223,224,225,232,235,249,255],[[111],[117,124],[123,134],[101,131],[115,122],[130,133],[104,110,117],[104,113,134],[100,101,131],[104,106,122],[104,108,127],[117,118,124],[101,102,109],[114,115,132],[117,120,129],[101,103,112],[115,116,121],[123,125,128],[101,105,115],[101,107,126],[115,119,130]]),
([v320,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,12,19,28,49,79,81,84,87,88,91,96,102,106,109,116,117,127,134,173,181,223,224,225,232,235,248,249,254,255],[[104],[113,120,123],[119,133],[101,128],[110,118],[127,131],[112,113,123],[119,132,133],[100,101,128],[110,118],[127,130,131],[113,114,122],[101,102,107],[109,110,129],[113,116,126],[101,103,108],[110,111,117],[119,121,125],[101,105,110],[101,106,124],[110,115,127]]),
([v321,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,12,19,28,49,79,80,81,84,87,88,89,91,96,102,103,109,116,117,135,172,178,181,223,224,225,232,235,249,255],[[104],[114,122],[121,124,133],[101,130],[111,120],[129,132],[113,114,122],[115,123,133],[100,101,115],[110,111,120],[115,119,129],[114,116,122],[101,102,107],[109,111,131],[114,118,128],[101,103,108],[111,112,120],[124,125,127],[101,105,111],[101,106,126],[111,117,129]]),
([v322,v145,v0,v1,v2,v3,v16],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,91,96,102,106,108,109,113,114,116,117,125,127,181,184,223,224,225,232,234],[[0],[108],[119,124,125],[123,125,138],[101,125,126],[125,130,136],[116],[115,117,129],[117,118,128],[101,107,117],[117,121,136],[104,105,112],[104,106,114],[100,101,137],[104,110,133],[119,120,127],[101,102,111],[119,122,135],[101,103,113],[128,131,134],[101,109,132]]),
([v322,v0,v146,v1,v2,v3,v11],[2,5],[0,1,3,5,7,8,9,12,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,109,114,116,117,131,181,184,223,224,225,232,234,235],[[119],[1],[118,126],[125,134],[0,101],[123],[104,109,129],[104,105,111],[104,106,113],[100,101,133],[104,115,116],[118,122,131],[125,130,132],[101,108,128],[116,121,132],[118,120,124],[101,102,110],[114,116,135],[101,103,112],[116,117,127],[101,107,116]]),
([v322,v0,v1,v9,v2,v3,v11],[1],[0,1,3,5,7,8,9,12,28,34,49,54,63,65,79,80,81,84,88,89,91,109,114,116,117,128,131,138,205,209,223,224,225,232,235],[[119],[118,124],[132],[123],[0,101],[121],[104,105,109],[104,113,129],[104,106,111],[100,101,133],[104,115,116],[118,125,131],[118,120,122],[101,102,108],[114,116,134],[130],[101,112,128],[116,127,132],[101,103,110],[116,117,126],[101,107,116]]),
([v322,v0,v1,v2,v147,v11,v16],[0,10],[0,1,3,5,7,8,9,12,19,24,28,34,49,54,79,80,81,84,88,91,96,102,113,114,116,117,127,131,142,181,184,223,224,225,232,234,235],[[128],[118,125],[124,135],[0],[122],[1,133],[104,105,111],[104,106,113],[100,101,134],[104,115,116],[104,109,130],[118,119,123],[101,102,110],[114,116,136],[118,121,132],[101,103,112],[116,117,127],[124,126,131],[101,107,116],[101,108,129],[116,120,133]]),
([v310,v323,v0,v1,v2,v3,v11],[0],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,125,127,128,181,184,220,223,224,225,235,238,239,247,249],[[0],[110],[119,129,134],[126,128,133],[101,132,135],[117,127,135],[131],[119,123,138],[126,139,140],[101,109,130],[117,122,137],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[119,121,125],[101,102,111],[115,117,136],[101,103,113],[117,118,124],[101,107,117]]),
([v310,v0,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,63,79,80,81,84,88,89,91,106,114,116,127,138,205,209,225,232,234,235,246,249,259],[[109],[119,132],[129,134],[124,125],[101,130],[117,135],[104,105,111],[104,128,134],[104,106,113],[100,101,120],[104,108,116],[119,132],[119,121,123],[101,102,110],[115,117,132],[131],[101,114,127],[117,126,133],[101,103,112],[117,118,122],[101,107,117]]),
([v324,v0,v1,v2,v3,v11,v16],[7],[0,1,3,5,7,8,9,19,24,28,34,49,54,59,81,88,89,102,114,116,127,131,132,133,136,138,143,181,184,223,224,225,234,235],[[104,116],[115,124],[119,132],[101,126],[114],[0,131],[104,105,110],[104,106,112],[100,101,116],[104,116],[104,108,128],[115,118,119],[101,102,109],[115,122,133],[115,117,130],[101,103,111],[119,121,132],[119,120,129],[101,113,123],[101,107,127],[123,125,131]]),
([v325,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,79,80,81,84,88,89,91,106,114,116,138,188,190,225,234,235,242],[[104,126],[118,129],[123,128],[101,125],[116,130],[127],[104,105,110],[104,106,112],[100,101,119],[104,108,115],[104,126],[118,120,122],[101,102,109],[114,116,129],[118,129],[101,103,111],[116,117,121],[123,128],[101,107,116],[101,113,125],[116,124,130]]),
([v40,v136,v0,v1,v3,v11,v16],[],[0,1,5,7,8,9,12,15,19,24,30,35,49,54,81,88,96,106,108,109,114,116,117,127,128,181,184,223,224,225,232,235,255],[[],[103,105,113],[120,121,132],[101,102,112],[114,117,119],[121,123,127],[111],[115],[101,110],[114,119],[129],[103,104,122],[100,101,130],[103,107,119],[103,109,126],[101,110],[114,118,131],[122,124,128],[101,106,114],[101,108,125],[114,116,129]]),
([v40,v0,v1,v2,v3,v11,v16],[7],[0,1,3,7,8,12,15,19,24,28,33,34,52,56,79,80,81,84,88,89,96,102,109,116,117,181,184,224,225,235],[[103,113],[118,124],[123],[101,112],[116,122],[0,128],[103,104,111],[103,113],[100,101,119],[103,106,115],[103,108,126],[118,124],[101,102,109],[114,116,129],[118,121,127],[101,110,112],[116,117,122],[128],[101,105,116],[101,107,125],[116,120,128]]),
([v40,v0,v1,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,88,89,91,96,102,106,109,114,116,117,127,143,167,172,173,181,184,188,190,223,224,225,232,234,235,242,249,252,255],[[104,106,117,118,130,150],[122,124,129,130,131,150],[101,103,115,116,130,135],[121,127,128,130,145],[130,132,141,143,145],[104,105,113,114,122,131],[100,101,104,123,144],[104,108,120,121,123,128],[104,110,138,140,143,148],[101,102,111,112,122,136],[119,121,122,146,149],[122,126,142,143,146,148],[101,107,121,133,134],[101,109,137,139,143,148],[121,125,143,147,148]]),
([v326,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,19,24,28,34,49,54,79,80,81,84,88,89,96,109,114,116,117,127,128,131,143,146,181,184,223,224,225,232,234,235,249,255],[[104,118,128],[117,123,136],[122,135],[101,127],[120],[133,137],[104,105,110],[104,106,112],[100,101,134],[104,114,115],[104,108,130],[121,122,138],[101,102,109],[113,115,136],[123,125,132],[101,103,111],[115,116,126],[122,124,131],[101,115,127],[101,107,129],[115,119,133]]),
([v126,v136,v0,v1,v2,v3,v11],[7],[0,1,5,7,8,9,12,15,19,24,30,35,49,54,81,84,88,106,108,109,114,116,117,125,127,128,181,184,223,224,225,232,235,255],[[0],[103,109,127],[122,125,129],[121,124,128],[101,108,126],[114,123,130],[111],[116],[121],[101,110],[114,119],[103,104,122],[103,105,113],[100,101,131],[103,107,119],[120,121,133],[101,110],[114,118,132],[101,102,112],[114,115,117],[101,106,114]]),
([v126,v0,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,102,106,109,114,116,117,125,127,143,167,172,173,181,184,188,190,223,224,225,232,234,235,249,252,255],[[104,110,139,141,144,148],[123,126,143,144,147,148],[130,133,142,144,146],[101,109,138,140,144,148],[121,132,144,148,149],[104,105,113,114,123,131],[104,106,117,118,130,150],[100,101,104,124,145],[104,108,120,121,124,128],[123,125,129,130,131,150],[101,102,111,112,123,137],[119,121,123,147,149],[101,103,115,116,130,136],[121,122,127,128,130,146],[101,107,121,134,135]]),
([v126,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,28,34,42,49,54,79,80,81,84,88,89,91,96,106,114,116,188,190,225,234,235,238,252],[[104,126],[118,129],[124,128],[101,125],[116,131],[127],[104,105,110],[104,106,113],[100,101,119],[104,108,115],[104,126],[118,120,123],[101,102,109],[114,116,129],[118,129],[101,103,112],[116,117,122],[124,128],[101,107,116],[101,111,125],[116,121,130]]),
([v327,v0,v1,v2,v3,v11,v16],[7],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,70,74,79,80,81,88,89,91,96,102,106,109,114,116,127,133,136,181,184,223,224,225,235],[[116],[131],[],[101,115],[119,130],[0,136],[104,105,112],[104,106,114],[100,101,121],[104,108,118],[104,110,133],[120,122,127],[101,102,111],[117,119,137],[120,124,135],[101,103,113],[119,125,126],[128,129,134],[101,107,119],[101,109,132],[119,123,136]]),
([v328,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,81,88,89,106,108,109,114,116,117,125,127,128,181,184,223,224,225,232,234,235,255],[[117],[116],[122],[0,101],[115],[1,131],[104,105,112],[104,106,114],[100,101,132],[104,108,120],[104,110,128],[121,122,135],[101,102,111],[119,120,134],[123,126,130],[101,103,113],[118,120,133],[122,125,129],[101,107,120],[101,109,127],[120,124,131]]),
([v329,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,125,127,181,184,198,200,223,224,225,235,242,244],[[131],[137],[125],[101,130],[117,136],[],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,124],[101,102,111],[115,117,135],[119,122,133],[101,103,113],[117,118,123],[125,127,132],[101,107,117],[101,109,128],[117,126,134]]),
([v136,v0,v5,v2,v3,v11,v16],[],[0,1,3,5,7,9,12,15,19,24,28,34,49,54,57,70,79,81,88,91,96,102,108,109,114,117,128,181,184,224,225,232,247,255],[[111],[118,125],[118,119,133],[101,102,110],[116,117,123],[118,121,130],[104,114,125],[104,105,113],[100,101,131],[104,107,123],[104,109,128],[124],[101,115],[117,122,123],[125,126,129],[101,103,112],[117,123],[130,132],[101,106,117],[101,108,127],[117,120,130]]),
([v136,v0,v1,v9,v2,v3,v11],[],[0,1,5,7,8,9,12,15,30,35,49,54,63,65,81,84,88,106,108,109,114,116,117,125,128,205,209,223,224,225,232,235],[[109],[116],[129],[121],[101,108],[114,119],[103,104,122],[103,113,126],[103,105,111],[100,101,130],[103,107,119],[122,124,128],[120,121],[101,108],[114,118,131],[127],[101,112,125],[114,123,129],[101,102,110],[114,115,117],[101,106,114]]),
([v136,v0,v1,v2,v3,v11,v16],[7],[0,1,5,7,8,9,12,15,19,24,30,35,49,54,81,84,88,96,106,108,109,114,116,117,127,128,181,184,223,224,225,232,235,255],[[111],[116],[122],[101,110],[114,120],[0,130],[103,104,123],[103,105,113],[100,101,131],[103,107,120],[103,109,127],[121,122,133],[101,110],[114,119,132],[123,125,129],[101,102,112],[114,115,118],[122,124,128],[101,106,114],[101,108,126],[114,117,130]]),
([v136,v0,v1,v2,v3,v11,v127],[],[0,1,5,7,8,9,12,15,19,24,30,46,49,54,81,84,102,106,108,109,114,116,117,127,128,184,223,224,232,235,255],[[111],[116],[121],[101,110],[114,119],[],[103,104,122],[103,105,113],[100,101,128],[103,107,119],[103,109,125],[120,121,130],[101,110],[114,118,129],[122,124,127],[101,102,112],[114,115,117],[121,123,126],[101,106,114],[101,108,110],[114,119]]),
([v136,v0,v1,v47,v3,v11,v16],[],[0,1,5,7,8,9,12,15,19,24,30,37,54,81,91,96,106,108,109,114,116,117,127,128,181,184,223,224,225,232,234,235,255],[[111],[114],[],[101,110],[113,118],[128],[103,104,121],[103,105,112],[100,101,129],[103,107,118],[103,109,125],[119,120,132],[101,110],[113,117,131],[121,123,127],[101,102,110],[113,116,130],[120,122,126],[101,106,113],[101,108,124],[113,115,128]]),
([v136,v0,v268,v2,v3,v11,v16],[],[1,2,3,5,7,8,10,12,16,19,25,28,35,49,55,79,81,84,88,91,96,102,106,108,109,114,116,117,118,127,128,170,181,185,223,224,225,235],[[112],[],[118,119,126],[100,102,111],[115,116,124],[118,121,136],[104],[105,106,114],[100,101,128],[105,108,124],[105,110,133],[125,126],[100,127,131],[116,123,137],[127,130,135],[100,103,113],[116,117,122],[126,129,134],[100,107,116],[100,109,132],[116,120,136]]),
([v136,v1,v268,v2,v3,v11,v16],[],[0,1,2,5,7,8,9,10,12,15,16,19,24,25,29,30,35,37,40,46,49,54,55,72,80,81,84,88,96,106,116,117,127,141,181,184,185,195,223,225,256],[[127],[],[116,117,123],[101,114,115],[116,118,124],[116,119,137],[131],[105,107,122],[101,102,115],[105,110,125],[105,113,136],[104,106,121],[100,101,140],[104,109,133],[104,112,135],[101,103,120],[125,126,129],[130,132,138],[101,108,125],[101,111,134],[125,128,139]]),
([v330,v0,v1,v2,v3,v11,v16],[],[1,3,5,7,12,28,42,49,79,81,84,88,91,96,106,109,114,116,117,127,128,184,187,188,190,191,223,224,225,232,235,249],[[103],[111,118],[117],[100,123],[109,115],[128,131],[111,118],[117,124,125],[100,122,129],[109,115],[121,124,128],[111,112,116],[100,101,105],[108,109,130],[111,120,127],[100,102,107],[109,110,114],[117,119,126],[100,104,109],[100,106,123],[109,113,128]]),
([v331,v0,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,84,88,89,96,106,116,181,184,224,225,233,234,235,238,249,252,255],[[103,110],[116],[120,126],[101,109],[114,130],[124,129],[103,110],[103,104,112],[100,101,117],[103,106,113],[103,108,122],[120,125,131],[101,109],[114,127,130],[123,127,129],[101,102,111],[114,115,119],[120,126],[101,105,114],[101,107,121],[114,118,128]]),
([v332,v0,v1,v2,v3,v11,v16],[0,7],[1,3,5,7,19,28,49,79,81,84,88,96,106,109,113,114,116,117,118,127,128,142,143,146,147,149,181,223,224,225,232,235,255],[[103],[0,110,117],[116],[100,122],[108,113],[1,129],[117,118,123],[116,123,124],[100,121,130],[108,113],[123,125,129],[115,116,132],[100,101,105],[107,108,131],[117,120,128],[100,102,106],[108,109,112],[116,119,127],[100,108,114],[100,104,126],[108,111,129]]),
([v333,v0,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,84,88,96,108,109,114,116,117,127,128,131,181,184,223,225,232,234,249,252,255],[[103,110],[116],[121,131],[101,109],[114,119,133],[129,132],[103,110],[103,104,112],[100,101,130],[103,106,113],[103,108,127],[120,121,134],[101,109],[114,118,133],[122,124,132],[101,102,111],[114,115,125],[121,123,128],[101,105,114],[101,107,126],[114,117,129]]),
([v334,v0,v1,v2,v3,v11,v16],[7],[1,3,7,12,19,28,33,51,52,54,56,57,61,65,79,81,84,88,96,102,106,109,114,116,117,127,181,209,223,224,225,232,235,255],[[102],[117,124],[123,133],[100,108],[115,121],[0,130],[110,111,124],[109,110,123],[100,107,131],[110,112,121],[110,113,127],[117,122,123],[100,101,105],[114,115,132],[117,119,129],[100,106,108],[115,116,120],[123,125,128],[100,103,115],[100,104,126],[115,118,130]]),
([v138,v0,v1,v2,v3,v11,v16],[7],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,84,88,89,96,108,109,114,116,117,128,181,184,224,225,235,247,255],[[103,110],[116],[122,131],[101,109],[114,120],[0,128],[103,110],[103,104,112],[100,101,117],[103,106,113],[103,108,126],[121,123,131],[101,109],[114,119,129],[123,124,127],[101,102,111],[114,115,120],[128,130],[101,105,114],[101,107,125],[114,118,128]]),
([v335,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,96,102,106,114,116,127,133,136,158,160,181,184,223,224,225,235,249,255],[[130],[119,128],[138],[101,129],[127],[135,137],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,132],[119,124,125],[101,102,111],[115,117,136],[119,122,134],[101,103,113],[117,118,123],[125,126,133],[101,107,117],[101,109,131],[117,121,135]]),
([v336,v0,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,65,79,80,81,84,88,89,91,106,114,125,128,213,215,223,224,225,235,249,252],[[126],[118],[131],[],[101,125],[116,132],[104,105,110],[104,113,129],[104,106,112],[100,101,119],[104,108,115],[118,124,128],[118,120,122],[101,102,109],[114,116,130],[127],[101,125],[116,123,129],[101,103,111],[116,117,121],[101,107,116]]),
([v336,v0,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,213,215,223,224,225,235,249,252,255],[[131],[119],[138],[101,130],[117,137],[136],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[119,121,125],[101,102,111],[115,117,135],[119,123,133],[101,103,113],[117,118,124],[126,127,132],[101,107,117],[101,109,128],[117,122,134]]),
([v139,v0,v5,v1,v3,v11,v16],[],[0,1,3,5,7,8,12,15,19,24,28,34,37,49,54,70,79,80,81,88,89,91,96,102,106,109,114,116,127,133,181,184,223,225,239,247,249,252,255],[[114],[127,138],[119,121,138],[101,103,113],[118,129],[133,135,136],[104,112,127],[104,105,111],[100,101,120],[104,107,117],[104,109,131],[126],[101,115],[118,124,125],[127,128,132],[101,102,110],[116,118,137],[119,123,134],[101,106,118],[101,108,130],[118,122,133]]),
([v139,v0,v1,v9,v2,v3,v11],[],[0,1,3,7,8,9,12,15,28,34,52,56,63,79,80,81,88,89,106,109,114,116,125,128,133,136,205,223,224,225,235,249],[[111],[116,125],[129,131],[],[101,110],[115,124],[103,104,109],[103,129,131],[103,105,121],[100,101,117],[103,107,114],[116,123,128],[116,120,121],[101,102,108],[113,115,130],[127],[101,112,126],[115,122,129],[101,110],[115,118,119],[101,106,115]]),
([v139,v0,v1,v2,v3,v11,v16],[],[0,1,3,7,8,9,12,15,19,24,28,34,52,56,79,80,81,88,89,96,102,106,109,114,116,127,133,136,181,184,223,224,225,235,249,255],[[113],[117,127],[135],[101,112],[116,126],[132,134],[103,104,111],[103,105,124],[100,101,118],[103,107,115],[103,109,129],[117,123,124],[101,102,110],[114,116,133],[117,120,131],[101,112],[116,121,122],[124,125,130],[101,106,116],[101,108,128],[116,119,132]]),
([v139,v0,v1,v54,v3,v11,v16],[],[1,3,4,5,7,9,10,12,17,19,26,28,36,49,56,79,81,83,84,88,91,96,102,106,114,116,127,131,134,169,181,186,223,224,225,230,234,235,247,249],[[114],[119,120,128],[],[100,103,113],[116,118,127],[134,138,139],[105,106,112],[104],[100,102,135],[105,108,117],[105,110,131],[119,124],[100,101,111],[115,116,137],[119,122,133],[100,125,129],[116,123,136],[125,126,132],[100,107,116],[100,109,130],[116,121,134]]),
([v139,v1,v2,v54,v3,v11,v16],[],[0,1,3,4,7,8,9,10,12,15,17,19,24,26,28,34,36,51,52,56,57,61,65,73,79,80,81,83,88,89,96,102,116,181,184,186,209,224,225,235,255],[[119,120,123],[140],[],[101,117,118],[119,121,126],[119,122,136],[106,107,116],[104,105,115],[101,102,114],[124,126,139],[128,131,137],[132],[101,103,118],[106,110,127],[106,113,135],[100,101,129],[104,109,125],[104,112,134],[101,108,126],[101,111,133],[126,130,138]]),
([v337,v0,v1,v2,v3,v11,v16],[7],[1,3,5,7,12,28,49,63,79,81,84,88,91,106,109,114,116,117,125,127,128,184,187,188,190,191,223,224,225,232,235,249,255],[[103],[111,117],[0,116,132],[100,123],[109,114],[128,131],[111,117],[116,124,125],[100,122,129],[109,114],[121,124,128],[111,112,115],[100,101,105],[108,109,130],[111,120,127],[100,102,106],[109,110,113],[116,119,126],[100,104,109],[100,107,123],[109,118,128]]),
([v140,v0,v1,v2,v3,v11,v16],[4],[0,1,3,7,8,12,15,19,24,28,34,52,56,79,80,81,88,89,96,102,109,116,117,181,184,223,225,234,235,238,249],[[103,112],[116,122],[121],[101,111],[115,120],[0,126,130],[103,104,110],[103,112],[100,101,117],[103,106,114],[103,108,124],[116,122],[101,102,109],[113,115,128],[116,119,128],[101,111],[115,120],[125,127],[101,105,115],[101,107,123],[115,118,129]]),
([v338,v0,v1,v2,v3,v11,v16],[0],[1,3,5,7,19,28,49,59,80,81,87,88,89,102,103,106,108,109,114,116,117,125,127,133,136,142,143,147,181,223,224,225,234,235,249,255],[[103],[111,124],[0,119,135],[100,126],[109,117,123],[131,134],[110,111,120],[112,119,127],[100,112,125],[108,112,117],[112,114,131],[111,118,119],[100,101,105],[111,116,133],[111,113,130],[100,102,106],[115,117,132],[119,122,129],[100,107,117],[100,104,128],[117,121,131]]),
([v339,v0,v1,v2,v3,v11,v16],[7],[0,1,3,7,8,12,15,19,24,28,34,52,56,79,80,81,88,89,96,102,106,109,114,116,127,133,136,181,184,224,225,234,235,258],[[103,112],[116,126],[131],[101,111],[115,121,125],[0,130],[103,104,110],[103,112],[100,101,117],[103,106,114],[103,108,128],[116,122,123],[101,102,109],[113,115,132],[116,119,129],[101,111],[115,120,123],[123,124,133],[101,105,115],[101,107,127],[115,118,130]]),
([v340,v0,v1,v2,v3,v11,v16],[],[1,5,7,12,19,29,30,34,35,37,40,46,49,80,81,88,89,96,106,108,109,114,116,117,127,128,133,136,181,195,223,224,225,235,249,255],[[102],[115,123,127],[122,135],[100,106],[114,126],[132,134],[107,108,123],[108,109,122],[100,105,116],[108,110,113],[108,111,129],[121,122,135],[100,106],[114,119,133],[123,125,131],[100,101,112],[114,118,120],[122,124,130],[100,103,114],[100,104,128],[114,117,132]]),
([v341,v0,v1,v2,v3,v11,v16],[],[0,1,7,8,9,12,15,19,24,30,33,35,52,81,84,88,91,96,106,108,109,114,116,117,127,128,136,181,184,223,224,225,232,235,249,255],[[111],[115,123,126],[122,135],[101,109],[113,120],[131,134],[102,103,123],[102,104,122],[100,101,132],[102,106,120],[102,108,128],[116,121],[101,109],[113,119,133],[123,125,130],[101,110,112],[113,114,118],[122,124,129],[101,105,113],[101,107,127],[113,117,131]]),
([v342,v0,v1,v2,v3,v11,v16],[0,7],[1,3,7,12,19,28,49,52,79,81,88,96,102,106,109,114,116,117,120,127,135,181,223,224,225,232,235,248,249,255,256],[[102],[110,117],[0,116,129],[100,107,125],[109,114],[1,124],[110,117],[116,120,130],[100,125],[109,114],[124,127,128],[110,115,116],[100,101,105],[108,109,126],[110,112,123],[100,106,118],[109,113,114],[116,119,122],[100,103,109],[100,104,121],[109,111,124]]),
([v343,v0,v1,v2,v3,v11,v16],[0],[1,5,7,12,19,28,30,49,80,81,84,87,88,89,96,103,106,108,109,114,116,117,121,127,128,181,223,224,225,232,235,249,252,255],[[102],[0,112,121],[120,133],[100,106,129],[109,132],[128,131],[111,113,121],[113,120,133],[100,113,129],[108,109,118],[113,115,128],[119,120,133],[100,105,122],[109,117,130],[121,124,127],[100,101,107],[109,110,116],[120,123,126],[100,103,109],[100,104,125],[109,114,128]]),
([v344,v0,v1,v2,v3,v11,v16],[0,7],[1,3,7,30,33,42,67,81,84,88,96,106,108,109,113,114,116,117,118,127,128,170,193,223,224,225,232,235,248,249,254,255,256],[[102],[0,109,117],[116],[100,103,126],[107,113],[1,125],[117,118,132],[116,130,131],[103,126],[107,113],[125,128,129],[115,116,131],[101,103,121],[107,112,127],[117,120,124],[103,104,106],[107,108,111],[116,119,123],[103,107,114],[103,105,122],[107,110,125]]),
([v15,v0,v1,v2,v3,v11,v16],[0],[1,5,7,52,53,59,63,68,79,80,81,87,88,89,96,102,103,106,109,114,116,117,127,133,136,169,205,223,224,225,232,235,249,255],[[102],[112,124],[0,120,133],[100,103,130],[110,123],[129,132],[111,112,121],[113,120],[103,113,130],[109,110,118],[113,116,129],[112,119,120],[103,104,107],[108,110,131],[112,115,128],[101,103,125],[110,117,118],[120,122,127],[103,105,110],[103,106,126],[110,114,129]]),
([v145,v0,v156,v1,v2,v3,v16],[],[0,1,3,5,7,8,9,12,19,24,28,34,40,49,54,81,88,89,106,109,113,116,125,127,140,181,184,223,224,225,232,233,234,235,246,249,250,252,253,255],[[117],[115,119],[133,137,138],[121,136,137],[101,107,124],[129,134,135],[104,112,119],[104,105,111],[104,106,114],[100,101,130],[104,109,126],[116],[118,119,132],[101,119,120],[119,122,129],[121,131,139],[101,102,110],[128,129,135],[101,103,113],[121,123,127],[101,108,125]]),
([v145,v0,v1,v17,v2,v3,v16],[],[0,1,3,5,7,8,9,12,19,24,28,34,49,54,61,79,80,81,84,88,96,102,106,108,109,113,117,125,181,184,223,224,225,232,234],[[116],[115,117,126],[117,124],[117,118,134],[101,107,117],[117,120,132],[104,105,111],[104,114,124],[104,106,113],[100,101,133],[104,109,129],[119,123,124],[119,126],[101,102,110],[119,121,131],[122],[101,124,125],[124,127,132],[101,103,112],[130,132],[101,108,128]]),
([v145,v0,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,15,28,34,49,54,63,65,81,88,89,91,106,108,109,113,114,116,117,125,128,143,205,209,223,224,225,232,235,249],[[116],[115,124],[132,135],[123],[101,127],[114],[104,105,109],[104,113,129],[104,106,111],[100,101,133],[104,107,120],[115,126,131],[115,117,122],[101,102,108],[115,119,134],[130],[101,112,128],[120,125,132],[101,103,110],[118,120],[101,120,121]]),
([v323,v0,v311,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,34,46,49,54,79,80,81,84,88,89,91,102,106,114,116,125,127,181,184,198,223,224,225,242,247,249,252],[[129],[133,136],[119,122,136],[125,135,136],[101,109,128],[117,134],[104,112,133],[104,105,111],[104,106,114],[100,101,120],[104,108,116],[132],[125,127,131],[101,130],[117,126,133],[119,121,124],[101,102,110],[115,117,137],[101,103,113],[117,118,123],[101,107,117]]),
([v323,v0,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,34,49,54,65,79,80,81,84,88,89,91,96,102,106,114,116,125,128,181,184,213,223,224,225,235,238,239,249],[[130],[119,123,137],[134,138],[126],[101,109,129],[117,122,136],[104,105,111],[104,114,134],[104,106,113],[100,101,120],[104,108,116],[119,128,133],[119,121,125],[101,102,110],[115,117,135],[132],[101,131],[117,127,134],[101,103,112],[117,118,124],[101,107,117]]),
([v0,v146,v1,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,96,102,106,109,114,116,117,143,167,172,173,181,184,188,190,223,224,225,232,234,235,242,249,252,255],[[104,110,138,140,143,148],[104,105,113,114,123,132],[104,106,117,118,131,150],[100,101,104,124,144],[104,108,120,121,124,129],[123,127,142,143,146,148],[131,141,143,145],[101,109,137,139,143,148],[121,126,143,147,148],[123,125,130,131,132,150],[101,102,111,112,123,136],[119,121,123,146,149],[101,103,115,116,131,135],[121,122,128,129,131,145],[101,107,121,133,134]]),
([v0,v345,v1,v2,v3,v11,v16],[],[1,3,5,7,12,19,28,29,49,79,80,81,84,88,89,91,96,102,103,106,109,116,117,118,127,134,167,172,173,181,223,224,225,232,235,249,255],[[103],[113,114,123],[114,121,136],[100,107,114],[110,111,120],[114,118,132],[113,122,128],[121,127],[100,133],[111,126],[132,135],[113,115,125],[100,101,106],[109,111,134],[113,117,131],[100,102,108],[111,112,119],[121,124,130],[100,104,111],[100,105,129],[111,116,132]]),
([v0,v346,v1,v2,v3,v11,v16],[],[1,3,5,7,12,19,28,49,51,79,81,84,88,91,96,102,109,116,117,167,172,173,178,181,223,224,225,232,235,248,249,255,256],[[103],[112,118],[120,131],[100,108,132],[110,116],[126,129,130],[112,121],[117,120,131],[100,127],[110,119],[126,130],[112,113,118],[100,101,106],[109,110,128],[112,115,125],[100,102,107],[110,111,116],[120,122,124],[100,104,110],[100,105,123],[110,114,126]]),
([v0,v149,v1,v2,v3,v11,v16],[],[1,3,5,7,8,12,19,28,29,35,40,46,49,72,79,80,81,84,88,89,91,96,102,109,114,116,117,181,195,224,225,232,235,247,249,255],[[103],[104,109,118],[109,113,135],[100,108,119],[109,110,115],[109,111,128],[118,126],[125,135],[100,131],[116,123],[130,134],[118,120,124],[100,101,107],[114,116,132],[118,122,129],[100,102,112],[116,117,123],[130,133],[100,105,116],[100,106,127],[116,121,130]]),
([v0,v150,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,19,24,28,34,49,54,61,81,88,89,91,102,106,108,109,113,116,117,125,143,181,184,223,224,225,234,235,249,255],[[104,116],[104,105,110],[104,106,112],[100,101,116],[104,113,116],[104,108,128],[115,124],[123,132,135],[101,126],[114],[131,134],[115,117,124],[101,102,109],[115,120,133],[115,118,130],[101,103,111],[119,121,132],[129,131],[101,121,122],[101,107,127],[121,125,131]]),
([v0,v151,v1,v2,v3,v11,v16],[],[1,3,5,7,12,15,19,28,49,79,81,84,87,88,89,91,96,102,103,106,109,116,117,135,142,181,223,224,225,232,234,235,249,255],[[103],[112,113,122],[114,123,133],[100,114,124],[105,110,114],[114,118,128],[113,122],[121,130,133],[100,129],[110,120],[128,132],[113,115,122],[100,101,107],[109,110,131],[113,117,127],[100,102,108],[110,111,119],[126,128],[100,104,110],[100,106,125],[110,116,128]]),
([v0,v347,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,65,79,80,81,84,88,89,91,106,114,116,125,128,188,190,223,224,225,234,235,242,244,249,255],[[104,127],[104,105,110],[104,106,112],[100,101,119],[104,108,115],[104,113,127],[118,134],[123,131,136],[101,126],[116,133],[135],[118,120,122],[101,102,109],[114,116,132],[118,125,129],[101,103,111],[116,117,121],[123,128,130],[101,107,116],[101,126],[116,124,130]]),
([v0,v348,v1,v2,v3,v11,v16],[],[1,3,5,7,12,19,24,28,49,79,81,84,88,91,96,102,106,109,114,116,117,181,187,190,223,224,225,232,234,235,249,255],[[103],[112,120],[119,123,131],[100,122,127],[110,117],[106,123,130],[112,120],[119,128,131],[100,127],[110,117],[126,130],[112,113,118],[100,101,107],[109,110,129],[112,115,125],[100,102,108],[110,111,116],[119,124,126],[100,104,110],[100,105,121],[110,114,126]]),
([v0,v349,v1,v2,v3,v11,v16],[],[0,1,3,7,8,12,15,19,24,28,34,37,52,56,79,80,81,88,89,96,102,106,109,114,116,117,127,133,136,181,184,223,225,239,249,252,255],[[103,113],[103,104,110],[103,111,113],[100,101,118],[103,106,115],[103,108,130],[117,125,128],[136],[101,112],[116,127],[132,134],[117,123,124],[101,102,109],[114,116,135],[117,120,133],[101,112],[116,121,122],[124,126,131],[101,105,116],[101,107,129],[116,119,132]]),
([v0,v350,v1,v2,v3,v11,v16],[],[1,3,5,7,9,12,19,28,49,51,56,61,65,73,79,81,84,88,91,96,102,106,109,114,116,117,127,181,209,223,225,232,239,249,252,255],[[103],[110,113,117],[104,110,135],[100,109,131],[110,111,122],[110,112,128],[117,125],[124,135],[100,131],[115,122],[130,133],[117,118,123],[100,101,107],[114,115,134],[117,120,132],[100,102,108],[115,116,121],[124,126,129],[100,105,115],[100,106,127],[115,119,130]]),
([v0,v351,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,19,24,28,34,40,49,54,81,88,89,91,102,106,108,109,113,116,117,125,127,134,143,146,181,184,223,224,225,232,234,235,249,255],[[104,116,129],[104,105,110],[104,106,113],[100,101,135],[104,111,121],[104,108,131],[115,124,137],[123,139],[101,128],[114],[134,138],[115,117,127],[101,102,109],[115,120,137],[115,118,133],[101,103,112],[119,121,136],[123,126,132],[101,121,122],[101,107,130],[121,125,134]]),
([v0,v352,v1,v2,v3,v11,v16],[],[1,3,5,7,12,15,19,28,49,79,81,84,87,88,91,96,102,106,109,116,117,127,134,142,146,147,149,181,223,224,225,232,235,249,255],[[103],[112,113,124],[119,124,125],[100,123,131],[105,110,118],[124,126,130],[113,120,132],[119,134],[100,131],[110,118],[130,133],[113,114,122],[100,101,107],[109,110,132],[113,116,129],[100,102,108],[110,111,117],[119,121,128],[100,104,110],[100,106,127],[110,115,130]]),
([v0,v353,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,28,34,46,49,54,79,80,81,84,88,89,91,106,114,116,125,127,188,190,223,224,225,235,242,244,249,252,255],[[104,127],[104,105,110],[104,106,113],[100,101,119],[104,108,115],[104,111,127],[118,131,133],[123,136],[101,126],[116,132],[134],[118,120,122],[101,102,109],[114,116,135],[118,129,130],[101,103,112],[116,117,121],[123,125,128],[101,107,116],[101,126],[116,124,130]]),
([v0,v354,v1,v2,v3,v11,v16],[],[1,3,5,7,12,19,24,28,49,79,81,84,88,91,96,102,106,109,114,116,117,127,181,187,190,191,223,224,225,232,249,252,255],[[103],[112,120],[119,124,125],[100,123,129],[110,117],[106,124,130],[112,120],[119,132],[100,129],[110,117],[128,130],[112,113,118],[100,101,107],[109,110,131],[112,115,127],[100,102,108],[110,111,116],[119,121,126],[100,104,110],[100,105,122],[110,114,128]]),
([v0,v154,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,109,116,117,181,184,223,224,225,233,234,235],[[104],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,128],[126],[125],[0,101],[124],[1,131],[119,121,132],[101,102,111],[115,117,134],[119,123,130],[101,103,113],[117,118,133],[129,131],[101,107,117],[101,109,127],[117,122,131]]),
([v0,v355,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,128,205,209,225,232,235,246,247,249,252,259],[[104],[104,105,110],[104,114,126],[104,106,112],[100,101,120],[104,108,116],[129],[127],[],[101,128],[117,134],[119,124,132],[119,121,123],[101,102,109],[115,117,133],[131],[101,113,125],[117,130,132],[101,103,111],[117,118,122],[101,107,117]]),
([v0,v355,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,127,181,184,225,232,234,235,238,239,247,252,259],[[104],[104,105,112],[104,106,114],[100,101,120],[104,108,116],[104,110,129],[133],[132],[101,131],[117,138],[130],[119,121,125],[101,102,111],[115,117,137],[119,123,135],[101,103,113],[117,118,124],[126,127,136],[101,107,117],[101,109,128],[117,122,134]]),
([v0,v5,v156,v2,v3,v11,v16],[0],[0,1,5,7,9,12,15,19,24,49,53,54,57,68,73,79,87,88,89,91,102,116,117,140,181,184,224,225,235,237,246,247,249,250,252,255],[[103,112,114],[103,116,117],[103,104,111],[100,101,118],[103,106,118],[103,108,125],[0,117,122],[121],[101,110,113],[128,129,134],[126,127,132],[117,119,135],[101,117],[115],[117,120,127],[101,102,109],[133,134],[127,131],[101,105,123],[101,107,124],[127,130,132]]),
([v0,v5,v1,v17,v3,v11,v16],[0],[0,1,3,7,8,12,15,19,24,28,33,34,37,67,72,79,80,81,84,88,89,91,96,102,109,116,117,145,147,156,159,181,184,223,225,234,239,247,249,255],[[103,112,114],[103,104,111],[103,128,130],[100,101,120],[103,106,116],[103,108,132],[126],[0,125,135],[101,110,113],[117,118,135],[133,134,138],[119,121,139],[101,102,109],[115,117],[119,123,136],[101,127,129],[124],[134,137,138],[101,105,117],[101,107,131],[117,122,134]]),
([v0,v5,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,70,74,79,80,81,88,89,91,109,116,117,125,205,209,225,247,249,252],[[104,116],[104,105,110],[104,114,128],[104,106,112],[100,101,121],[104,108,118],[125],[129,131],[124],[101,115],[119,123],[120,129,131],[120,122],[101,102,109],[117,119,132],[130],[101,113,127],[119,126,129],[101,103,111],[119,123],[101,107,119]]),
([v0,v5,v1,v9,v3,v11],[7],[0,1,3,7,8,12,15,22,26,28,30,33,34,35,37,67,70,72,74,79,80,81,84,88,89,106,109,114,116,125,143,167,172,202,207,213,215,223,225,232,247,252],[[103,114,117,118,128],[103,104,112,113,123],[103,108,134,136,138,140],[100,101,103,124,139],[103,106,120,121,124,126],[127],[0,128,137,138,140],[101,111,115,116,128,132],[121,122,125,126,128],[123,138,140],[101,102,109,110,123],[119,121,123,141],[101,107,133,135,138,140],[121,129,138,140,141],[101,105,121,130,131]]),
([v0,v5,v1,v9,v3,v11,v16],[7],[0,1,3,7,8,12,15,19,24,28,33,34,37,67,72,79,80,81,84,88,89,96,102,106,114,116,127,181,184,189,191,211,214,225,234,238,239,250,252,255],[[103,112,114],[103,104,111],[103,130,132],[100,101,120],[103,106,116],[103,108,128],[124],[0,125,134],[101,110,113],[117,118,123],[0,125,126],[119,139],[101,102,109],[115,117,138],[119,122,136],[101,129,131],[117,137,138],[133],[101,105,117],[101,107,127],[117,121,135]]),
([v0,v5,v1,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,70,74,79,80,81,88,89,91,96,102,109,116,117,181,184,225,239,247,249,252,255],[[104,116],[104,105,112],[104,106,114],[100,101,121],[104,108,118],[104,110,129],[127],[126],[101,115],[119,125],[130,133],[120,122,135],[101,102,111],[117,119,134],[120,124,131],[101,103,113],[119,125],[130,132],[101,107,119],[101,109,128],[119,123,130]]),
([v0,v5,v1,v46,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,33,35,37,67,72,80,81,82,84,88,89,91,96,106,116,117,127,181,184,223,225,240,247,250,251],[[103,112,114],[103,111],[103,104,111],[100,101,120],[103,106,115],[103,108,128],[125],[],[101,110,113],[116,118,123],[124,126,129],[119],[101,109],[116,117,134],[121,130,131],[101,102,109],[116,133],[130,132],[101,105,116],[101,107,127],[116,122,130]]),
([v0,v5,v1,v3,v163,v11,v16],[],[1,4,5,7,8,14,15,22,24,31,33,34,37,70,72,79,80,81,88,89,91,96,102,109,116,117,172,178,183,184,223,225,239,247,252,255],[[103,112,114],[103,104,111],[101,102,119],[103,119],[103,106,116],[103,108,129],[125],[102,110,113],[124],[117,123],[126,127,130],[102,109,113],[118,120,135],[115,117,134],[118,122,132],[100],[102,105,117],[102,107,128],[117,123],[131,133],[117,121,131]]),
([v0,v5,v2,v46,v3,v11,v16],[],[0,1,3,7,8,12,15,19,24,28,31,34,36,50,53,55,57,68,73,79,80,81,82,88,89,91,96,102,108,109,116,117,128,181,184,224,225,239,255],[[103,116,118],[103,112,115],[103,104,111],[100,101,124],[103,106,120],[103,108,134],[130],[],[101,114,117],[121,128,129],[131,132,135],[138],[101,110,113],[121,122,129],[125,136],[101,102,109],[119,121],[123,127,137],[101,105,121],[101,107,133],[121,126,136]]),
([v0,v5,v2,v3,v158,v11,v16],[],[1,2,3,7,9,15,20,24,50,53,54,57,70,73,79,80,81,87,88,89,91,96,102,109,113,116,117,173,179,182,184,224,225,239,247,252,255,256],[[103,111,113],[103,104,110],[101,102,119],[103,117,137],[103,105,115],[103,107,130],[125],[102,109,112],[126],[116,123],[127,128,131],[102,108,112],[118,120,136],[116,123],[132,134],[100],[102,116,124],[102,106,129],[114,116,135],[118,122,133],[116,121,132]]),
([v0,v356,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,84,88,89,106,116,125,181,184,223,225,234,239,241,242,244,249,252,255],[[103,110],[103,110],[103,104,112],[100,101,117],[103,106,113],[103,108,122],[116],[119,125,132],[101,109],[114,128],[124,130],[119,129,132],[101,109],[114,127,131],[124,126,130],[101,102,111],[114,115,118],[119,123,124],[101,105,114],[101,107,121],[114,120,124]]),
([v0,v159,v1,v2,v3,v11,v16],[4],[0,1,3,7,8,12,15,19,24,28,34,52,56,79,80,81,88,89,96,102,109,116,117,181,184,224,225,247,249,252],[[103,112],[103,104,110],[103,112],[100,101,117],[103,106,114],[103,108,124],[116,122],[121],[101,111],[115,120],[0,126,128],[116,122],[101,102,109],[113,115,129],[116,119,125],[101,111],[115,120],[126,127],[101,105,115],[101,107,123],[115,118,126]]),
([v0,v160,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,79,81,88,89,91,102,106,109,116,117,125,181,184,223,225,234,239,249,252,255],[[103,110],[103,110],[103,104,112],[100,101,116],[103,106,116],[103,108,125],[122],[121,128,132],[101,109],[114,120,131],[127,130],[115,117,132],[101,109],[113,115,131],[115,118,129],[101,102,111],[119,120,128],[126,127],[101,105,120],[101,107,124],[120,123,127]]),
([v0,v161,v1,v2,v3,v11,v16],[],[0,1,3,7,8,12,15,19,24,28,34,52,56,79,80,81,88,89,91,96,102,109,116,117,181,184,224,225,235,247,249],[[103,112],[103,104,110],[103,112],[100,101,117],[103,106,114],[103,108,125],[116,123,128],[122],[101,111],[115,121],[127,130],[116,118,128],[101,102,109],[113,115,128],[116,120,126],[101,111],[115,121],[127,129],[101,105,115],[101,107,124],[115,119,127]]),
([v0,v357,v1,v2,v3,v11,v16],[],[0,1,3,5,7,9,12,15,19,24,28,34,35,49,54,70,74,79,81,88,91,96,102,106,109,116,117,127,181,184,223,225,232,239,249,252,255],[[104,112,116],[104,111,116],[104,105,114],[100,101,132],[104,107,124],[104,109,129],[126],[125,136],[101,115],[118,124],[131,134],[119,120,136],[101,102,110],[117,118,135],[119,122,133],[101,103,113],[118,123,124],[125,127,130],[101,106,118],[101,108,128],[118,121,131]]),
([v0,v8,v1,v2,v3,v11,v16],[],[0,1,5,7,8,9,12,15,19,24,30,35,49,54,74,81,84,88,96,109,116,181,184,225,232,247,249,252,255],[[103,111,114],[103,104,114],[103,105,113],[100,101,124],[103,107,119],[103,109,122],[117],[120,128],[101,110],[115,127],[123,126],[128],[101,110],[115,127],[123,126],[101,102,112],[115,116,119],[123,125],[101,106,115],[101,108,121],[115,118,123]]),
([v0,v8,v2,v54,v3,v11,v16],[],[1,3,5,7,9,12,19,28,49,51,56,57,61,65,73,79,81,84,88,91,96,102,109,117,181,209,224,225,232,235,247,255],[[110,111,114],[104,110,131],[103],[100,109,128],[110,112,122],[110,113,125],[118,119,123],[],[100,101,107],[115,116,129],[118,121,126],[],[100,102,108],[116,117,122],[127,130],[100],[116],[127],[100,105,116],[100,106,124],[116,120,127]]),
([v0,v8,v2,v3,v11,v16],[],[0,1,3,5,7,9,12,15,19,24,28,30,34,49,52,54,56,57,74,79,81,84,88,91,96,102,109,114,117,143,146,167,173,181,184,188,190,224,225,232,235,242,247,249,252,255,256],[[104,112,117,118,122,128],[104,105,115,116,145],[100,101,104,139,146],[104,107,120,126,130],[104,109,134,136,138,143],[122,123,127,128,145],[101,102,110,111,122,132],[119,120,122,140,144],[122,125,137,138,140,143],[101,103,113,114,145],[120,121,126,145],[138,142,145],[101,106,120,129,131],[101,108,133,135,138,143],[120,124,138,141,143]]),
([v0,v358,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,88,89,96,108,109,114,116,117,128,172,178,181,184,223,225,249,252,255],[[103,110],[103,110],[103,104,112],[100,101,116],[103,106,113],[103,108,127],[115],[121,124,132],[101,109],[114,119],[129,130],[120,122,132],[101,109],[114,118,131],[122,123,130],[101,102,111],[114,119],[124,125,128],[101,105,114],[101,107,126],[114,117,129]]),
([v0,v359,v1,v2,v3,v11,v16],[],[0,1,3,5,7,9,12,15,19,24,30,35,49,54,79,81,84,88,91,96,102,106,109,116,117,127,134,181,184,223,225,232,239,249,252,255],[[104,111],[104,111],[104,105,113],[100,101,131],[104,107,122],[104,109,128],[124],[123,135],[101,110,131],[115,122],[130,133],[117,118,126],[101,102,117],[114,115,134],[117,120,132],[101,103,112],[115,116,121],[123,125,129],[101,106,115],[101,108,127],[115,119,130]]),
([v0,v360,v1,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,24,30,35,49,54,81,84,88,93,96,106,108,109,114,116,117,127,128,172,181,184,223,225,249,252,255],[[103,110],[103,110],[103,104,112],[100,101,116],[103,106,120],[103,108,128],[115],[122,126],[101,109],[113,120],[130,131],[121,122,133],[101,109],[113,119,132],[123,125,131],[101,102,111],[113,114,118],[122,124,129],[101,105,113],[101,107,127],[113,117,130]]),
([v0,v361,v1,v2,v3,v11,v16],[],[0,1,3,5,7,9,12,15,19,24,30,35,49,54,70,79,80,81,88,89,91,96,102,109,116,117,172,178,181,184,223,225,239,249,252,255],[[104,111],[104,111],[104,105,113],[100,101,119],[104,107,116],[104,109,129],[125],[124,126,135],[101,110,114],[117,123],[131,133],[118,120,135],[101,102,114],[115,117,134],[118,122,132],[101,103,112],[117,123],[126,127,130],[101,106,117],[101,108,128],[117,121,131]]),
([v0,v156,v1,v17,v2,v3,v16],[],[0,1,3,5,7,8,9,19,24,28,34,40,49,54,59,61,79,80,81,84,89,96,109,116,153,155,181,184,223,224,225,233,234,235,237,246,249,252],[[104,111,117],[104,105,110],[104,115,125],[104,106,113],[100,101,120],[104,108,127],[116],[118,122],[118,119,132],[101,118],[118,121,130],[133,134,137],[131,132],[101,102,109],[129,130,136],[123],[101,114,124],[130,135,136],[101,103,112],[128,130],[101,107,126]]),
([v0,v156,v1,v9,v2,v3,v11],[1],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,81,88,89,116,140,205,209,223,224,225,235,237,246,249,252],[[104,117],[104,105,110],[104,114,121],[104,106,112],[100,101,117],[104,108,117],[116],[124],[118],[0,101],[115],[123,124,128],[118,125],[101,102,109],[125,126,129],[122],[101,113,120],[124,127,128],[101,103,111],[118,129],[101,107,119]]),
([v0,v156,v1,v2,v18,v11,v16],[0,9],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,89,113,116,121,127,140,181,184,223,224,225,232,233,234,235,237,246,249,252,255],[[104,115],[104,105,112],[104,106,114],[100,101,126],[104,108,115],[104,110,122],[118],[117,128],[0],[116],[1,125],[117,127,134],[101,102,111],[129,130,133],[124,125,132],[101,103,113],[117,128],[117,119,123],[101,107,120],[101,109,121],[125,131,132]]),
([v0,v156,v268,v2,v3,v11,v16],[0],[1,2,5,7,8,10,12,19,25,49,55,79,88,89,91,102,116,117,127,134,140,181,185,223,224,225,231,233,234,235,237,246,249],[[104,112,113],[103],[104,105,110],[100,101,113],[104,113],[104,108,122],[117],[112,114,119],[100,112],[111],[112,115,125],[116,127],[0,100,126],[0,129,130],[124,125],[100,102,109],[116,128],[116,118,123],[100,106,120],[100,107,121],[125,131,132]]),
([v0,v311,v1,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,42,46,49,54,63,65,79,80,81,84,88,89,91,96,106,114,116,127,128,193,195,205,209,225,234,235,238,246,249,252],[[104,112,131],[104,105,110],[104,116,133],[104,106,114],[100,101,122],[104,108,118],[136],[134,139],[127,128],[101,111,130],[119,124,137],[121,129,139],[121,123,126],[101,102,109],[117,119,140],[135],[101,115,132],[119,138,139],[101,103,113],[119,120,125],[101,107,119]]),
([v0,v1,v362,v2,v3,v11,v16],[0,7],[0,1,7,9,15,24,28,30,33,35,42,54,67,79,80,81,84,88,89,91,96,102,106,113,116,117,127,134,184,193,223,225,239,252],[[102,109],[102,109],[102,103,111],[100,102,118],[102,104,114],[102,105,128],[125],[117,119,127],[106,107,117],[113,115,133],[117,121,132],[124],[101,107],[0,115],[1,131],[107,108,112],[115,116,122],[124,126,130],[107,115,123],[107,110,129],[115,120,131]]),
([v0,v1,v363,v2,v3,v11,v16],[0,7],[0,1,7,9,12,15,19,24,30,33,35,49,54,80,81,84,88,89,91,96,106,108,116,117,127,128,181,184,223,225,249,252,255],[[102,110],[102,110],[102,103,112],[100,101,117],[102,105,113],[102,107,127],[116],[118,122,123],[101,108],[114,121,131],[123,125,130],[0,122,132],[101,108],[0,114],[1,129],[101,109,111],[114,115,120],[122,124,128],[101,104,114],[101,106,126],[114,119,129]]),
([v0,v1,v364,v2,v3,v11,v16],[],[1,3,7,8,12,19,28,29,33,35,37,40,46,52,54,56,79,80,81,84,88,89,96,102,106,116,117,127,134,181,195,223,225,239,249,252,255],[[103,109,115],[102,109,115],[109,110,114],[100,107,121],[109,111,117],[109,112,130],[126],[120,125,128],[100,101,106],[116,118,135],[120,123,133],[125,136],[100,113],[118,135],[132,134],[100,108,113],[118,119,124],[125,127,131],[100,104,118],[100,105,129],[118,122,132]]),
([v0,v1,v365,v2,v3,v11,v16],[7],[0,1,3,5,7,8,9,19,24,28,34,49,54,59,61,81,88,89,102,114,116,117,127,143,181,184,223,224,225,234,235,246,249],[[104,105,110],[104,117],[104,106,112],[100,101,117],[104,114,117],[104,108,125],[116,121,130],[116,119,120],[101,102,109],[116,130],[116,118,127],[120,129],[101,123],[115],[0,128],[101,103,111],[120,129],[120,122,126],[101,113,123],[101,107,124],[128,131,132]]),
([v0,v1,v366,v2,v3,v11,v16],[0],[0,1,5,7,9,19,24,30,35,40,49,54,59,80,81,84,88,89,96,102,106,114,116,117,127,181,184,223,225,239,249,252,255],[[103,108],[103,108],[103,104,111],[100,101,117],[103,109,113],[103,106,126],[123],[116,121,122],[101,107],[114,116,131],[116,119,129],[0,122,132],[101,107],[114,131],[128,130],[101,102,110],[114,115,120],[122,124,127],[101,112,114],[101,105,125],[114,118,128]]),
([v0,v1,v367,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,116,128,188,190,225,234,235,242,244,252],[[104,105,110],[104,127],[104,106,112],[100,101,120],[104,108,116],[104,114,127],[119,130,132],[119,121,123],[101,102,109],[115,117,133],[119,125,132],[124,129],[101,126],[117,131],[128],[101,103,111],[117,118,122],[124,129],[101,107,117],[101,113,126],[117,131]]),
([v0,v1,v368,v2,v3,v11,v16],[7],[0,1,5,7,9,12,15,30,35,42,46,49,54,80,81,84,88,89,96,102,106,116,127,188,190,223,225,233,241,244,249,252,255],[[103,108],[103,108],[103,104,112],[100,101,117],[103,106,113],[103,110,124],[116],[121,127,129],[101,107],[114,128,131],[119,126,129],[0,121,132],[101,107],[114,131],[126,130],[101,102,111],[114,115,120],[121,122,125],[101,105,114],[101,109,123],[114,118,126]]),
([v0,v1,v171,v2,v3,v11,v16],[],[0,1,3,5,7,8,12,15,19,24,28,34,49,54,56,70,74,79,80,81,88,89,91,96,102,109,116,117,181,184,224,225,235,247,249],[[104,105,111],[104,114,116],[104,113,116],[100,101,121],[104,107,118],[104,109,129],[120,127],[120,122,127],[101,102,110],[117,119,132],[120,124,130],[126],[101,115],[119,125],[131,134],[101,103,112],[119,125],[131,133],[101,106,119],[101,108,128],[119,123,131]]),
([v0,v1,v369,v2,v3,v11,v16],[],[0,1,5,7,12,15,19,24,30,35,37,49,54,80,81,84,88,89,96,106,108,116,117,127,128,181,184,223,224,225,235,249,252,255],[[103,109],[103,109],[103,110,112],[100,101,117],[103,105,113],[103,107,126],[116],[121,122,133],[101,108],[114,120,130],[122,124,128],[121,133],[101,108],[114,132],[129,131],[101,102,111],[114,115,119],[121,123,127],[101,104,114],[101,106,125],[114,118,129]]),
([v0,v1,v370,v2,v3,v11,v16],[0,7],[0,1,3,5,7,8,9,12,19,24,28,34,49,54,81,88,89,114,116,117,127,128,140,181,184,223,224,225,234,235,246,249,255],[[104,105,111],[104,116],[104,106,113],[100,101,116],[104,116],[104,109,124],[115,119,129],[117,118,132],[101,102,110],[119,129],[119,121,126],[118,128],[0,101],[114],[1,127],[101,103,112],[118,128],[118,120,125],[101,107,122],[101,108,123],[127,130,131]]),
([v0,v1,v371,v2,v3,v11,v16],[],[0,1,5,7,9,12,19,24,30,35,40,49,54,80,81,84,88,89,96,106,114,116,117,127,128,181,184,223,225,237,249,252,255],[[103,109],[103,109],[103,104,112],[100,101,117],[103,110,113],[103,107,126],[116],[120,121,132],[101,108],[114,122,129],[122,124,130],[121,132],[101,108],[114,131],[128,130],[101,102,111],[114,115,119],[121,123,127],[101,105,114],[101,106,125],[114,118,128]]),
([v0,v1,v372,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,181,184,190,198,200,225,234,235,242],[[104,105,111],[104,127,129],[104,106,113],[100,101,119],[104,108,115],[104,126,129],[118,132],[118,120,123],[101,102,110],[114,116,132],[118,121,132],[124,131],[101,128],[116,133],[130],[101,103,112],[116,117,122],[124,131],[101,107,116],[101,109,125],[116,133]]),
([v0,v1,v373,v2,v3,v11,v16],[],[0,1,5,7,9,12,15,19,30,35,46,49,54,80,81,84,88,89,96,106,116,127,128,181,184,223,225,233,235,249,252,255],[[103,109],[103,109],[103,104,112],[100,101,117],[103,106,113],[103,110,124],[116],[120,127,131],[101,108],[114,128,130],[122,126,128],[120,131],[101,108],[114,130],[126,129],[101,102,111],[114,115,119],[120,121,125],[101,105,114],[101,107,123],[114,118,126]]),
([v0,v1,v37,v268,v3,v11,v16],[],[1,3,5,7,8,12,19,28,29,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,116,127,134,181,195,223,225,239,252],[[104,109,119],[109,110,114],[103],[100,108,120],[109,111,116],[109,112,129],[119,121,127],[],[100,101,107],[115,117,133],[119,123,132],[],[100,102,113],[117,118,124],[125,126,130],[100],[117],[131],[100,105,117],[100,106,128],[117,122,131]]),
([v0,v1,v37,v2,v3,v11,v16],[7],[0,1,3,7,8,9,12,15,19,24,28,34,52,56,74,79,80,81,88,89,96,102,109,116,117,136,181,184,225,239,252],[[103,104,111],[103,113,114],[103,105,114],[100,101,119],[103,107,116],[103,109,127],[118,124,125],[118,125],[101,102,110],[115,117,130],[118,121,129],[123],[101,112],[117,122],[0,128],[101,112],[117,122],[128],[101,106,117],[101,108,126],[117,120,128]]),
([v0,v1,v37,v3,v11,v16],[],[0,1,3,5,7,8,12,15,19,24,28,30,34,35,37,49,52,54,74,79,80,81,84,88,89,91,96,102,106,109,114,116,127,136,143,167,172,181,184,188,190,223,225,232,234,239,242,244,249,252,255],[[104,105,112,113,123],[104,114,117,118,131,150],[100,101,104,124,143],[104,107,120,121,124,129],[104,109,138,140,142,148],[123,125,130,131,133,150],[101,102,110,111,123],[119,121,123,149],[123,127,142,145,147,148],[101,103,115,116,131,136],[121,122,128,129,131,144],[131,132,141,142,144],[101,106,121,134,135],[101,108,137,139,142,148],[121,126,142,146,148]]),
([v0,v1,v178,v2,v3,v11,v16],[0,7],[1,3,5,7,12,19,28,37,49,57,69,74,79,81,84,88,91,96,102,109,116,117,134,181,225,232,239,247,249,252,255],[[109,111,115],[103],[107,111,130],[100,110,125],[111,113,119],[111,124,128],[115,121],[115,116,122],[100,101,106],[112,113,129],[115,118,126],[120,130],[0,100],[0,113],[1,124],[100,102,108],[113,114,119],[124,127],[100,104,113],[100,105,123],[113,117,124]]),
([v0,v1,v374,v2,v3,v11,v16],[0,7],[0,1,7,9,12,15,19,24,30,33,35,52,72,80,81,84,88,89,91,96,106,116,127,132,136,181,184,223,225,249,252,255],[[102,110],[102,110],[102,103,112],[100,101,117],[102,105,113],[102,107,126],[116],[118,121,124],[101,108],[114,123,130],[124,128,129],[121,131],[101,108],[0,114],[1,128],[101,109,111],[114,115,120],[121,122,127],[101,104,114],[101,106,125],[114,119,128]]),
([v0,v1,v81,v268,v2,v11,v16],[0,7],[1,3,5,8,12,19,28,29,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,116,117,127,134,181,195,223,225,239,252,256],[[103,108,118],[100,107,119],[134],[108,109,113],[108,110,115],[108,111,129],[100,101,106],[125],[118,120,127],[114,116,133],[118,122,132],[],[100,102,112],[100,104,116],[100,105,128],[124],[0,116],[1,131],[116,117,123],[124,126,130],[116,121,131]]),
([v0,v1,v45,v268,v2,v3,v16],[0],[1,3,5,7,8,12,19,28,29,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,116,127,134,181,195,223,225,235,239,252],[[104,109,119],[109,111,116],[103],[109,110,114],[100,108,120],[109,112,129],[115,117,134],[132],[119,121,127],[100,101,107],[119,123,133],[0],[117,118,124],[100,105,117],[117,122,131],[125],[100],[131],[100,102,113],[125,126,130],[100,106,128]]),
([v0,v1,v45,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,15,19,24,28,34,49,54,81,88,89,91,102,116,117,127,134,143,181,184,223,224,225,234,235,249],[[104,105,111],[104,116],[104,106,113],[100,101,116],[104,107,116],[104,109,125],[115,120,130],[115,117,122],[101,102,110],[115,130],[115,118,127],[119,129],[101,123],[114],[128,131],[101,103,112],[119,129],[119,121,126],[101,123],[101,108,124],[128,131]]),
([v0,v1,v45,v2,v3,v16],[],[0,1,3,5,7,8,9,12,19,24,28,30,34,35,40,49,52,54,56,79,80,81,84,88,89,91,96,102,106,109,116,127,134,136,143,167,172,181,184,188,190,223,224,225,232,234,235,242,249,252,255],[[104,105,112,113,123,146],[104,114,120,121,124,129],[104,106,117,118,130,150],[100,101,104,124,144],[104,109,138,140,143,148],[119,121,123,146,149],[123,125,130,132,133,150],[101,102,110,111,123,146],[123,127,142,143,146,148],[121,122,128,129,130,145],[101,107,121,134,135],[121,126,143,147,148],[101,103,115,116,130,136],[130,131,141,143,145],[101,108,137,139,143,148]]),
([v0,v1,v375,v2,v3,v11,v16],[],[1,3,5,7,12,19,28,40,49,79,81,84,88,89,91,96,102,103,109,116,117,118,127,131,134,151,181,223,224,225,232,234,235,249,255],[[112,113,121],[103],[113,119,134],[100,113,125],[107,110,113],[113,117,129],[112,120,132],[112,114,124],[100,101,106],[109,110,132],[112,116,128],[119,131],[100,130],[110,118],[129,133],[100,102,108],[110,111,123],[119,122,127],[100,104,110],[100,105,126],[110,115,129]]),
([v0,v1,v376,v2,v3,v11,v16],[7],[0,1,5,7,9,15,19,24,30,35,49,54,80,81,84,88,89,91,96,102,106,113,116,117,127,134,181,184,223,225,239,252,253],[[103,109],[103,109],[103,104,111],[100,101,116],[103,105,112],[103,107,127],[123],[115,117,125],[101,108],[113,115,132],[115,119,130],[122],[101,108],[113,131],[0,129],[101,102,110],[113,114,120],[122,124,128],[101,113,121],[101,106,126],[113,118,129]]),
([v0,v1,v52,v268,v2,v3,v11],[7],[1,3,5,7,8,12,19,28,29,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,116,117,127,134,181,195,223,225,239,252],[[104,109,119],[109,112,130],[103],[109,110,114],[100,108,120],[109,111,116],[119,123,133],[126],[119,121,128],[100,101,107],[115,117,134],[0],[125,127,131],[100,106,129],[117,122,132],[125],[100],[117],[100,102,113],[117,118,124],[100,105,117]]),
([v0,v1,v52,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,19,28,30,34,35,46,49,52,54,56,79,80,81,84,88,89,91,96,102,106,109,114,116,117,127,143,167,172,173,181,184,188,200,223,224,225,232,234,242,244,249,252,255],[[104,105,112,113,123,132],[104,114,139,141,144,149],[104,106,117,118,131,151],[100,101,104,124,145],[104,108,120,121,124,129],[123,127,143,144,148,149],[123,125,130,131,132,151],[101,102,110,111,123,137],[119,121,123,150],[131,133,142,144,146],[101,109,138,140,144,149],[121,126,144,147,149],[101,103,115,116,131,136],[121,122,128,129,131,146],[101,107,121,134,135]]),
([v0,v1,v52,v2,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,79,80,81,84,88,89,91,106,114,116,128,188,190,200,225,234,235,242,244,252],[[104,105,111],[104,126,127],[104,106,113],[100,101,119],[104,108,115],[104,109,127],[118,130,132],[118,120,122],[101,102,110],[114,116,133],[118,124,132],[123,129],[101,125],[116,131],[128],[101,103,112],[116,117,121],[123,129],[101,107,116],[101,125],[116,131]]),
([v0,v1,v377,v2,v3,v11,v16],[0],[1,3,5,7,12,19,28,46,49,79,81,84,88,91,96,102,106,109,114,116,117,181,197,200,225,232,234,238,239,249,252,255],[[112,120],[103],[119,123,131],[100,122,125],[110,117],[107,123,129],[112,120],[112,113,118],[100,101,106],[109,110,130],[112,115,128],[119,126],[0,100],[110,117],[124,129],[100,102,108],[110,111,116],[119,126],[100,104,110],[100,105,121],[110,114,127]]),
([v0,v1,v378,v2,v3,v11,v16],[0],[0,1,5,7,9,12,15,24,30,35,42,49,54,80,81,84,88,89,96,102,106,116,127,188,195,223,225,241,244,249,252,255],[[103,109],[103,109],[103,104,112],[100,101,117],[103,106,113],[103,107,124],[116],[121,128,131],[101,108],[114,127,130],[119,126,128],[121],[101,108],[0,114],[126,129],[101,102,111],[114,115,120],[121,122,125],[101,105,114],[101,110,123],[114,118,126]]),
([v0,v1,v268,v9,v2,v3,v11],[1],[1,3,5,7,8,12,28,29,35,37,40,49,63,72,79,80,81,84,88,89,91,106,116,117,125,134,205,223,225,249,252],[[104,108,118],[103],[108,128,129],[108,109,113],[100,107,119],[108,110,115],[123],[118,128,129],[118,120,125],[100,101,106],[114,116,130],[128],[122],[0,100],[0,116],[127],[100,112,126],[116,124,128],[100,102,111],[116,117,121],[100,105,116]]),
([v0,v1,v268,v2,v3,v11,v16],[0,7],[1,3,5,7,8,12,19,28,29,35,37,40,46,49,72,79,80,81,84,88,89,91,96,102,106,116,117,127,134,181,195,223,225,239,252],[[104,109,119],[103],[109,110,114],[100,108,120],[109,111,116],[109,112,130],[126],[119,121,128],[100,101,107],[115,117,134],[119,123,133],[125],[0,100],[0,117],[1,132],[100,102,113],[117,118,124],[125,127,131],[100,105,117],[100,106,129],[117,122,132]]),
([v0,v1,v379,v2,v3,v11,v16],[7],[0,1,3,7,8,12,15,19,24,28,33,34,52,56,79,80,81,84,88,89,96,102,106,114,116,117,127,167,172,173,181,184,224,225,235,258],[[103,104,111],[103,113],[103,113],[100,101,119],[103,106,115],[103,108,131],[118,125,129],[118,123,124],[101,102,109],[114,116,134],[118,121,132],[128],[101,112],[116,127],[0,133],[101,110,112],[116,117,122],[124,126,135],[101,105,116],[101,107,130],[116,120,133]]),
([v0,v1,v189,v2,v3,v11,v16],[],[0,1,3,5,7,8,12,15,19,24,28,34,52,56,79,80,81,84,88,89,91,96,102,109,116,117,181,184,224,225,232,235,247,249],[[104,105,111],[104,113],[104,113],[100,101,119],[104,107,115],[104,109,127],[118,125],[118,120,125],[101,102,110],[114,116,131],[118,122,128],[124],[101,112,130],[116,123],[129,133],[101,103,130],[116,117,123],[129,132],[101,106,116],[101,108,126],[116,121,129]]),
([v0,v1,v380,v2,v3,v11,v16],[7],[0,1,3,7,8,12,15,19,24,28,34,52,56,79,80,81,88,89,96,102,106,109,114,116,127,133,136,172,181,184,224,225,235,258],[[103,104,110],[103,112],[103,112],[100,101,117],[103,106,114],[103,108,129],[116,126],[116,122,123],[101,102,109],[113,115,132],[116,119,130],[127],[101,111],[115,125],[0,131],[101,111],[115,120,121],[123,124,133],[101,105,115],[101,107,128],[115,118,131]]),
([v0,v1,v192,v2,v3,v11,v16],[],[0,1,3,5,7,8,12,15,19,24,28,34,52,56,70,79,80,81,88,89,91,96,102,109,116,117,173,181,184,224,225,235,247,249],[[104,105,111],[104,113],[104,113],[100,101,119],[104,107,116],[104,109,128],[118,125,126],[118,120,126],[101,102,110],[115,117,131],[118,122,129],[124],[101,112,114],[117,123],[130,133],[101,103,114],[117,123],[130,132],[101,106,117],[101,108,127],[117,121,130]]),
([v0,v1,v381,v9,v2,v3,v11],[1,8],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,91,106,114,125,205,209,223,224,225,235,249,252,256,260],[[104,105,110],[104,133],[104,114,126],[104,106,112],[100,101,120],[104,108,116],[119,134],[119,128,129],[119,121,123],[101,102,109],[115,117,130],[131],[1],[0,101],[132],[127],[101,113,125],[117,124,129],[101,103,111],[117,118,122],[101,107,117]]),
([v0,v1,v17,v9,v2,v3,v11],[],[0,1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,80,81,84,88,89,109,116,117,128,158,160,205,209,223,224,225,235,249],[[104,105,110],[104,126],[104,114,128],[104,106,112],[100,101,120],[104,108,116],[119,123],[119,124,130],[119,123],[101,102,109],[115,117,132],[131,133],[122],[101,125],[121],[129],[101,113,127],[117,131,133],[101,103,111],[117,118],[101,107,117]]),
([v0,v1,v17,v9,v3,v11],[1,7],[0,1,3,7,8,12,15,22,26,28,30,34,35,79,80,81,88,89,91,100,106,114,116,117,120,128,143,147,158,160,172,173,202,207,213,215,222,223,232,235,249],[[103,104,111,112,116,123],[103,122,127,129],[103,108,133,135,137,140],[100,101,103,117,138],[0,103,106,114,115,117],[116,118,121,122,123],[116,125,136,137,139,140],[101,102,109,110,116,131],[0,113,115,116,139],[0,1,122,137,140],[101,122,124,128,130],[0,120],[101,107,132,134,137,140],[0,115,119,137,140],[0,101,105,115,126]]),
([v0,v1,v17,v54,v3,v11,v16],[0],[1,3,4,7,9,10,12,19,26,28,36,79,81,83,88,91,96,102,109,116,117,145,147,156,160,181,186,223,224,225,229,230,233,234,235,247,249],[[104,105,110],[104,122,124],[103],[100,102,131],[104,112,113],[104,108,126],[114,115,120],[114,132],[100,101,109],[111,112,134],[114,117,128],[119],[100,121,123],[118],[129,135,136],[0,100,130],[0,112,133],[127,129],[100,106,112],[100,107,125],[112,116,129]]),
([v0,v1,v9,v2,v114,v3,v11],[1,7],[1,3,5,7,12,28,49,63,65,79,81,84,88,91,106,109,114,116,117,138,205,212,215,225,232,235,246,247,249],[[112,118],[108,122,128],[117,122],[103],[100,121,124],[110,115],[112,125],[112,113,116],[112,118],[100,101,105],[109,110,125],[127],[123],[100,107,120],[110,119,126],[1,117],[100,102,106],[110,111,114],[0,100],[110,115],[100,104,110]]),
([v0,v1,v9,v2,v54,v3,v11],[1],[1,3,5,7,9,12,28,49,51,56,57,61,63,65,73,79,81,84,88,91,109,116,117,125,128,205,209,224,225,232,235,247],[[109,110,114],[109,113,126],[104,109],[103],[100,108,129],[109,111,120],[118,124,127],[118,119,122],[118],[100,101,106],[115,116,130],[131],[],[100,112,125],[116,123,128],[121],[100,102,107],[116,117,120],[0,100],[0,116],[100,105,116]]),
([v0,v1,v9,v2,v157,v3,v11],[1,7],[0,1,5,7,9,12,15,30,35,49,54,76,80,81,84,88,89,106,116,125,128,213,215,223,225,235,249,252],[[103,108],[103,122],[103,104,110],[103,108],[100,101,116],[103,106,112],[120,124,125],[118,125],[115],[101,107],[113,125,127],[123],[126],[101,111,121],[113,119,124],[1,118],[101,102,109],[113,114,117],[101,107],[0,113],[101,105,113]]),
([v0,v1,v9,v2,v46,v3,v11],[1],[0,1,7,12,15,30,33,35,37,52,56,63,65,80,81,84,88,89,91,106,108,116,117,125,128,205,209,223,224,225,235],[[102,107],[102,112,126],[102,108,110],[102,107],[100,101,117],[102,104,113],[122,124,128],[118,121,122],[116],[101,105],[114,120,130],[127],[],[101,111,125],[114,123,129],[],[101,106,109],[114,115,119],[101,105],[0,114],[101,103,114]]),
([v0,v1,v9,v2,v3,v279,v11],[],[1,3,5,7,8,9,12,15,28,34,49,54,63,65,79,81,84,88,89,91,93,106,109,114,116,117,125,128,172,205,209,223,224,225,232,235],[[103,104,109],[103,113,130],[103,105,111],[100,103,120],[118],[103,107,122],[117,127,132],[117,119,123],[100,101,108],[117,125],[114,115,135],[131],[100,112,129],[133],[115,126,133],[100,102,110],[124,128],[115,116,121],[134],[100,106,115],[115,122]]),
([v0,v1,v9,v2,v3,v158,v11],[],[1,3,7,8,9,15,29,30,33,34,54,65,67,76,80,81,84,88,89,106,113,116,125,166,171,173,179,209,220,223,224,225,235,249,252,256],[[102,103,109],[102,111,127],[102,104,110],[102,106,118],[102,135],[102,105,114],[125,126,130],[121,124],[101,107,125],[117],[115,123,132],[129],[107,113,128],[131,133],[115,122,131],[107,108,112],[121],[115,116,119],[100],[107,115,120],[115,134]]),
([v0,v1,v9,v2,v3,v382,v11],[],[1,7,8,9,15,34,54,63,65,79,80,81,84,88,89,91,106,114,116,167,172,173,179,209,213,223,224,225,235,249,252],[[101,102,105],[101,108,123],[101,103,106],[101,114],[101,114],[101,104,110],[113,122,126],[113,115,117],[113,121],[113,121],[109,111,128],[125],[107,124,127],[129],[111,127,130],[118,120],[118,120],[111,112,116],[100],[111,119],[111,119]]),
([v0,v1,v9,v2,v3,v163,v11],[4],[1,5,7,8,9,15,34,51,52,53,54,59,63,65,68,79,80,81,88,89,109,116,117,125,128,172,205,209,223,224,225,235],[[102,103,106],[102,113,127],[102,104,110],[102,107,119],[102,119],[102,105,116],[118,124,129],[118,122],[108,109,114],[118,122],[115,117,131],[128],[108,112,126],[0],[117,123,130],[101,108,125],[121],[117,120],[100],[108,111,117],[117,120]]),
([v0,v1,v9,v2,v3,v11],[1,4,7],[0,1,3,5,7,8,9,12,15,28,30,34,35,49,52,54,56,63,65,79,80,81,84,88,89,91,106,109,114,116,117,125,128,143,167,172,173,205,209,213,215,223,224,225,232,235,249,252],[[104,105,111,112,123,130],[104,118,138,140,143,146],[104,106,115,116,129],[100,101,104,124,144],[104,108,120,121,124,127],[123,132,142,143,145,146],[123,125,128,129,130],[101,102,109,110,123,136],[119,121,123,145,147],[1,2,141],[101,117,137,139,143,146],[121,131,143,146,147],[101,103,113,114,129,135],[0,121,122,126,127,129],[101,107,121,133,134]]),
([v0,v1,v9,v54,v3,v11],[],[1,3,4,7,9,10,12,17,22,26,28,30,36,37,79,81,83,88,100,106,109,114,116,117,128,143,147,167,169,172,173,202,209,213,215,223,224,225,232,235,247,252,256],[[104,105,112,113,117,123],[104,109,132,134,137,140],[103],[100,102,104,138,142],[104,107,115,116,120,126],[117,124,136,137,139,140],[117,121,122],[100,101,110,111,117,130],[114,115,117,139,141],[135],[100,108,131,133,137,140],[115,118,137,140,141],[100,122,128,129],[115,119,122],[100,106,115,125,127]]),
([v0,v1,v9,v54,v3,v11,v16],[7],[1,3,4,7,9,10,12,17,19,28,36,79,81,83,88,96,102,106,114,116,127,169,181,186,189,191,211,215,225,232,234,235,238,243,250],[[104,105,110],[104,125,127],[103],[100,102,129],[104,107,113],[104,123,127],[114,131],[114,118],[100,101,109],[111,112,131],[114,116,131],[130],[100,124,126],[112,133,134],[128],[100,119,121],[112,117],[0,119,120],[100,106,112],[100,108,122],[112,115,132]]),
([v0,v1,v2,v27,v3,v11],[1,4],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,96,106,109,114,116,117,128,143,167,172,173,181,184,188,190,223,224,225,232,234,235,249,252],[[104,105,113,114,123,131],[104,106,117,118,130],[104,110,138,140,143,147],[100,101,104,124,144],[104,108,120,121,124,128],[123,125,129,130,131],[123,132,142,143,146,147],[101,102,111,112,123,136],[119,121,123,146,148],[0,1,130,141,143,145],[101,103,115,116,130,135],[121,122,127,128,130,145],[101,109,137,139,143,147],[121,126,143,147,148],[101,107,121,133,134]]),
([v0,v1,v2,v195,v3,v11,v16],[0,7],[0,1,7,8,15,24,34,49,52,53,56,59,63,68,79,81,84,88,91,96,102,109,116,117,184,205,224,225,232,235,247,255],[[102,103,106],[102,110],[102,110],[100,102,128],[102,104,121],[102,105,124],[117,118,123],[117],[108,109,113],[114,115,129],[117,120,126],[122],[107,108,131],[115,116,121],[127,130],[101,108],[0,115],[1,127],[108,111,115],[108,112,125],[115,119,127]]),
([v0,v1,v2,v383,v3,v11,v16],[0,7],[0,1,7,8,12,15,19,24,28,30,34,52,53,56,80,81,84,88,89,91,96,106,108,116,117,127,128,172,181,184,224,225,235,258],[[102,103,110],[102,113],[102,113],[100,101,118],[102,105,114],[102,107,129],[119,123,124],[0,117,124],[101,108,112],[115,122,132],[124,126,130],[127],[101,111],[115,116,121],[123,125,133],[101,109,111],[0,115],[1,131],[101,104,115],[101,106,128],[115,120,131]]),
([v0,v1,v2,v196,v3,v11,v16],[7],[1,5,7,9,12,19,29,30,34,35,40,46,49,56,80,81,88,89,96,108,109,116,117,128,134,181,195,224,225,235,247,255],[[108,109,113],[103,109,113],[102,109,113],[100,106,117],[109,110,114],[109,111,126],[122,124,131],[116,122],[100,107],[115,119,129],[122,123,127],[121],[100,101,112],[115,120],[128,130],[100,107],[115,120],[0,128],[100,104,115],[100,105,125],[115,118,128]]),
([v0,v1,v2,v197,v3,v11,v16],[],[0,1,3,5,7,8,9,19,24,28,34,40,49,54,79,80,81,84,88,89,96,109,114,116,117,128,143,146,181,184,223,224,225,234,235,249,255],[[104,105,110],[104,106,113],[104,127],[100,101,119],[104,111,115],[104,108,129],[122,124,136],[118,124,134],[101,102,109],[114,116,134],[124,125,131],[123,133,136],[101,103,112],[116,117,133],[130,132],[101,126],[121],[132,135],[101,116,126],[101,107,128],[116,120,132]]),
([v0,v1,v2,v198,v3,v11,v16],[0,7],[0,1,3,7,8,19,24,28,34,40,52,56,59,79,80,81,88,89,96,109,114,116,117,128,181,184,224,225,235,247,255],[[103,104,108],[103,111],[103,111],[100,101,117],[103,109,114],[103,106,125],[120,122,130],[0,116,122],[101,102,107],[113,115,128],[122,123,126],[121],[101,110],[115,119],[127,129],[101,110],[115,119],[1,127],[101,112,115],[101,105,124],[115,118,127]]),
([v0,v1,v2,v89,v3,v11],[1,4],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,102,106,109,114,116,117,125,143,167,172,173,181,184,188,190,223,224,225,232,235,249,252,255],[[104,105,113,114,123,131],[104,106,117,118,130,148],[104,110,138,140,143,146],[100,101,104,124,144],[104,108,120,121,124,128],[123,125,129,130,131,148],[123,126,142,143,145,146],[101,102,111,112,123,136],[119,121,123,145,147],[0,1,130,141,143,148],[101,103,115,116,130,135],[121,122,127,128,130],[101,109,137,139,143,146],[121,132,143,146,147],[101,107,121,133,134]]),
([v0,v1,v2,v89,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,28,34,42,46,49,54,79,80,81,84,88,89,91,96,106,114,116,127,188,190,225,234,235,238,252,255],[[104,105,110],[104,106,114],[104,128],[100,101,120],[104,108,116],[104,112,128],[119,121,124],[119,131],[101,102,109],[115,117,131],[119,131],[125,130,134],[101,103,113],[117,118,123],[125,126,134],[101,127],[117,133],[129],[101,107,117],[101,111,127],[117,122,132]]),
([v0,v1,v2,v199,v3,v11,v16],[4],[0,1,3,7,8,12,15,28,34,42,46,52,56,79,80,81,88,89,96,109,116,117,128,188,190,224,225,235,255],[[103,104,108],[103,112],[103,112],[100,101,117],[103,106,114],[103,110,124],[116,121],[116,121],[101,102,107],[113,115,127],[116,122,125],[120],[101,111],[115,119],[126,128],[101,111],[115,119],[0,126],[101,105,115],[101,109,123],[115,118,126]]),
([v0,v1,v2,v384,v3,v11,v16],[7],[0,1,3,7,12,15,19,24,28,34,35,52,56,57,79,81,88,96,102,106,109,116,117,127,181,184,223,224,225,232,235,255],[[103,109,113],[103,112],[103,110,112],[100,101,129],[103,105,120],[103,107,125],[116,121,122],[116,122],[101,102,108],[114,115,130],[116,118,127],[131],[101,111],[115,119,120],[121,123,126],[101,111],[115,120],[0,128],[101,104,115],[101,106,124],[115,117,128]]),
([v0,v1,v2,v385,v3,v11,v16],[],[0,1,3,5,7,8,9,12,19,24,28,34,49,54,79,80,81,84,88,89,96,102,109,114,116,117,127,158,160,181,184,223,224,225,232,234,235,249],[[104,105,111],[104,106,113],[104,119,128],[100,101,134],[104,115,116],[104,109,130],[118,123,124],[118,125],[101,102,110],[114,116,136],[118,121,132],[124,135],[101,103,112],[116,117,135],[124,126,131],[101,127],[122],[133,137],[101,107,116],[101,108,129],[116,120,133]]),
([v0,v1,v2,v386,v3,v11,v16],[7],[0,1,3,7,8,12,19,24,28,34,52,56,61,79,80,81,88,96,102,109,114,116,117,127,181,184,224,225,232,234,235,258],[[103,104,109],[103,111],[103,111],[100,101,128],[103,112,114],[103,107,125],[116,120,121],[116,122],[101,102,108],[113,115,130],[116,118,126],[129],[101,110],[115,119],[121,123,131],[101,110],[115,119],[0,127],[101,105,115],[101,106,124],[115,117,127]]),
([v0,v1,v2,v28,v3,v11],[1,4],[0,1,3,5,7,8,9,12,15,24,28,30,34,35,49,52,54,56,63,79,80,81,84,88,89,91,106,109,114,116,117,125,127,128,143,167,172,173,205,209,213,215,223,224,225,232,234,235,249,252],[[104,105,112,113,123,130],[104,106,116,117,129],[104,109,139,141,144,148],[100,101,104,124,145],[104,108,120,121,124,127],[123,125,128,129,130],[123,133,143,144,147,148],[101,102,110,111,123,137],[119,121,123,147,149],[0,1,129,132,142,144,146],[101,103,114,115,129,136],[121,122,126,127,129,146],[101,118,138,140,144,148],[121,131,144,148,149],[101,107,121,134,135]]),
([v0,v1,v2,v28,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,28,34,49,54,79,80,81,84,88,89,91,96,102,106,114,116,181,184,190,213,215,225,234,235,238,252],[[104,105,111],[104,106,113],[104,128,130],[100,101,119],[104,108,115],[104,127,130],[118,120,124],[118,133],[101,102,110],[114,116,133],[118,122,133],[125,132],[101,103,112],[116,117,123],[125,132],[101,129],[116,135],[131],[101,107,116],[101,109,126],[116,121,134]]),
([v0,v1,v2,v387,v3,v11,v16],[4],[0,1,3,7,8,12,15,19,28,34,52,56,65,79,80,81,88,89,96,102,109,116,117,127,181,184,224,225,234,235],[[103,104,109],[103,111],[103,111],[100,101,117],[103,106,114],[103,112,125],[116,122],[116,122],[101,102,108],[113,115,129],[116,119,126],[121],[101,110],[115,120],[123,127,128],[101,110],[115,120],[0,127],[101,105,115],[101,107,124],[115,118,127]]),
([v0,v1,v2,v47,v3,v11,v16],[0,7],[0,1,7,8,12,15,19,24,30,33,35,37,52,56,73,81,84,88,91,96,108,109,116,117,128,181,184,224,225,232,235],[[102,103,114],[102,111,113],[102,110,113],[100,101,129],[102,105,121],[102,107,126],[118,123],[117,123],[101,108],[115,120,130],[123,124,127],[122],[101,109,112],[115,116,121],[128],[101,108],[0,115],[1,128],[101,104,115],[101,106,125],[115,119,128]]),
([v0,v1,v2,v26,v54,v11,v16],[0,7],[1,3,5,9,12,19,28,49,51,56,57,61,65,73,79,81,84,88,89,91,96,102,109,116,117,181,209,224,225,232,235,247,255],[[109,110,113],[103,109,132],[100,108,129],[118],[109,111,122],[109,112,126],[117,119,124],[100,101,106],[117],[114,115,130],[117,121,127],[100,102,107],[123],[115,116,122],[128,131],[],[100,104,115],[100,105,125],[0,115],[1,128],[115,120,128]]),
([v0,v1,v2,v12,v54,v3,v16],[0],[1,3,5,7,9,12,19,28,49,51,56,57,61,65,73,79,81,84,88,91,96,102,109,117,181,209,224,225,232,234,235,247,255],[[110,111,114],[104,110,132],[110,112,122],[103],[100,109,128],[110,113,125],[118,119,123],[115,116,130],[118],[100,101,107],[118,121,126],[116,117,122],[129],[100,102,108],[127,131],[0],[100,105,116],[116,120,127],[100],[127],[100,106,124]]),
([v0,v1,v2,v12,v3,v11,v16],[],[0,1,3,5,7,8,9,15,19,24,28,34,49,54,81,88,89,91,102,116,117,143,160,181,184,223,224,225,232,234,235,236,249,255],[[104,105,111],[104,106,113],[104,116,122],[100,101,128],[104,107,122],[104,109,124],[115,117,120],[115,130],[101,102,110],[115,130],[115,118,126],[119,129,133],[101,103,112],[129,131,133],[125,127],[101,121],[114],[127,132],[101,121],[101,108,123],[127,132]]),
([v0,v1,v2,v12,v3,v16],[],[0,1,3,5,7,8,9,12,19,24,28,30,34,35,49,52,54,56,61,79,80,81,84,88,91,96,102,106,109,117,143,160,167,173,181,184,188,190,223,224,225,232,234,235,242,249,252,255,256],[[104,105,112,113,123,129],[104,106,116,117,142,147],[104,118,120,121,128,131],[100,101,104,141,148],[104,109,135,137,140,145],[123,124,129,142,147],[119,121,123,143,146],[101,102,110,111,123,133],[123,126,139,140,143,145],[121,122,127,128,142,147],[101,103,114,115,142,147],[138,140,142],[101,107,121,130,132],[121,125,140,144,145],[101,108,134,136,140,145]]),
([v0,v1,v2,v200,v3,v11,v16],[],[1,3,5,7,12,19,28,49,61,79,81,84,88,91,96,102,109,116,117,131,147,157,160,161,181,223,224,225,232,234,235,249,255],[[112,118],[120,122,132],[103],[100,121,128],[108,110,122],[122,123,127],[112,113,118],[112,130],[100,101,106],[109,110,130],[112,115,126],[117,129,132],[100,102,107],[110,111,119],[125,127],[100,128],[110,116],[127,131],[100,104,110],[100,105,124],[110,114,127]]),
([v0,v1,v2,v201,v3,v11,v16],[7],[0,1,3,7,8,15,19,24,28,34,52,56,59,81,84,88,91,102,108,109,116,117,125,181,184,224,225,232,235,247,255],[[103,104,109],[103,111],[103,111],[100,101,127],[103,105,119],[103,107,124],[115,116,121],[115],[101,102,108],[115,118,128],[115,117,125],[120],[101,110],[114,119,130],[126,129],[101,110],[113,119],[0,126],[101,112,119],[101,106,123],[119,122,126]]),
([v0,v1,v2,v55,v54,v3,v11],[7],[1,3,5,7,9,12,19,28,49,51,56,57,61,65,73,79,81,84,88,91,96,102,109,116,117,181,209,224,225,232,235,247,255],[[110,111,114],[104,110,132],[110,113,126],[103],[100,109,129],[110,112,122],[118,119,124],[118,121,127],[118],[100,101,107],[115,116,130],[128,131],[123],[100,102,108],[116,117,122],[0],[100,106,125],[116,120,128],[100],[116],[100,105,116]]),
([v0,v1,v2,v55,v3,v11],[1,4],[0,1,3,5,7,8,9,12,15,19,28,30,34,35,49,52,54,56,65,79,80,81,84,88,89,91,96,102,106,109,114,116,117,143,167,172,173,181,184,188,215,223,224,225,232,235,242,249,252,255],[[104,105,112,113,123,132],[104,106,116,117,131,149],[104,118,138,140,143,147],[100,101,104,124,144],[104,108,120,121,124,129],[123,125,130,131,132,149],[123,127,142,143,145,147],[101,102,110,111,123,136],[119,121,123,145,148],[0,1,131,141,143,149],[101,103,114,115,131,135],[121,122,128,129,131],[101,109,137,139,143,147],[121,126,143,146,147],[101,107,121,133,134]]),
([v0,v1,v2,v55,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,24,28,34,49,54,79,80,81,84,88,89,91,106,114,116,127,188,190,215,225,234,235,242,255],[[104,105,111],[104,106,113],[104,126,127],[100,101,119],[104,108,115],[104,109,127],[118,120,122],[118,130],[101,102,110],[114,116,130],[118,130],[123,129,132],[101,103,112],[116,117,121],[123,124,132],[101,125],[116,131],[128],[101,107,116],[101,125],[116,131]]),
([v0,v1,v2,v114,v3,v11,v16],[0],[1,3,5,7,12,19,28,49,65,79,81,84,88,91,96,102,106,109,114,116,117,127,181,191,212,215,225,232,234,235,238,247,249,255],[[112,120],[119,123,133],[103],[100,124,127],[110,117],[108,125,132],[112,113,118],[112,120],[100,101,106],[109,110,129],[112,115,129],[119,128,133],[100,102,107],[110,111,116],[119,121,131],[0,100],[110,117],[126,132],[100,104,110],[100,105,122],[110,114,130]]),
([v0,v1,v2,v202,v3,v11,v16],[4],[0,1,3,7,8,12,15,24,28,34,52,56,63,79,80,81,88,89,109,116,117,125,128,188,209,224,225,235,255],[[103,104,109],[103,111],[103,111],[100,101,117],[103,106,114],[103,107,124],[116,120],[116,120],[101,102,108],[113,115,127],[116,122,125],[119],[101,110],[115,118],[126,128],[101,110],[115,118],[0,126],[101,105,115],[101,112,123],[115,121,126]]),
([v0,v1,v2,v54,v3,v11,v16],[0,7],[1,3,5,7,9,12,19,28,49,51,56,57,61,65,73,79,81,84,88,91,96,102,109,116,117,181,209,224,225,232,235,247,255],[[110,111,114],[104,110,132],[103],[100,109,129],[110,112,122],[110,113,126],[118,119,124],[118],[100,101,107],[115,116,130],[118,121,127],[123],[100,102,108],[116,117,122],[128,131],[0,100],[0,116],[1,128],[100,105,116],[100,106,125],[116,120,128]]),
([v0,v1,v2,v6,v46,v3,v16],[0],[0,1,7,19,24,30,33,35,37,40,52,56,59,80,81,84,89,91,96,106,108,116,117,127,128,181,184,223,224,225,235],[[102,107],[102,108,111],[102,109,113],[102,107],[100,101,116],[102,104,126],[117,121,122],[114,120,130],[],[101,105],[122,124,128],[114,115,119],[],[101,106,110],[121,123,127],[0],[101,112,114],[114,118,129],[101,105],[129],[101,103,125]]),
([v0,v1,v2,v6,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,81,88,89,91,116,117,127,128,140,158,181,184,223,224,225,234,235,249],[[104,105,112],[104,106,114],[104,117],[100,101,117],[104,108,117],[104,110,126],[118,119,120],[116,120,131],[101,102,111],[120,131],[120,122,128],[119,130],[101,103,113],[119,130],[119,121,127],[101,124],[115],[129,132],[101,107,123],[101,109,125],[129,132]]),
([v0,v1,v2,v6,v3,v16],[],[0,1,3,5,7,8,9,19,24,28,30,34,35,40,49,52,54,56,59,79,80,81,84,89,91,96,106,109,116,117,127,128,136,158,167,172,173,181,184,188,190,223,224,225,232,234,235,242,249,252],[[104,105,111,112,129,132],[104,106,116,117,128],[104,113,120,121,123,127],[100,101,104,123,144],[104,108,138,140,143,148],[124,128,129],[119,121,129,146,149],[101,102,109,110,129,136],[129,131,142,143,146,148],[121,122,126,127,128,145],[101,103,114,115,128,135],[128,130,141,143,145],[101,118,121,133,134],[121,125,143,147,148],[101,107,137,139,143,148]]),
([v0,v1,v2,v388,v3,v11,v16],[0,7],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,84,88,89,91,96,106,116,117,127,128,181,184,223,225,237,249,252,255],[[103,110],[103,104,112],[103,110],[100,101,117],[103,106,113],[103,108,126],[118,121,122],[116],[101,109],[114,122,129],[122,124,130],[0,121,132],[101,102,111],[114,115,120],[121,123,127],[101,109],[114,131],[1,128],[101,105,114],[101,107,125],[114,119,128]]),
([v0,v1,v2,v389,v3,v11,v16],[0,7],[0,1,3,7,8,12,15,19,24,28,34,52,56,81,84,88,89,91,108,109,116,117,125,127,128,181,184,224,225,234,235,258],[[103,104,110],[103,112],[103,112],[100,101,116],[103,106,116],[103,108,126],[117,120,121],[0,115,121],[101,102,109],[118,119,130],[121,124,127],[129],[101,111],[114,119,120],[120,123,131],[101,111],[113,119],[1,128],[101,105,119],[101,107,125],[119,122,128]]),
([v0,v1,v2,v31,v46,v3,v11],[7],[0,1,7,12,15,30,33,35,37,42,46,52,56,80,81,84,88,89,91,96,106,108,116,117,127,128,193,195,223,224,225,235],[[102,107],[102,108,112],[102,110,127],[102,107],[100,101,117],[102,104,113],[118,122,123],[123,125,129],[116],[101,105],[114,121,131],[122,124,128],[],[101,106,111],[114,115,120],[0],[101,109,126],[114,119,130],[101,105],[114],[101,103,114]]),
([v0,v1,v2,v31,v3,v11],[1,4],[0,1,3,5,7,8,9,12,15,28,30,34,35,42,46,49,52,54,56,79,80,81,84,88,89,91,96,106,109,114,116,117,127,128,143,167,172,173,193,195,198,200,223,224,225,232,234,235,242,249,252],[[104,105,111,112,123,131],[104,106,117,118,130],[104,114,139,141,144,149],[100,101,104,124,145],[104,108,120,121,124,128],[123,125,129,130,131],[123,133,143,144,147,149],[101,102,109,110,123,137],[119,121,123,147,150],[0,1,130,132,142,144,146],[101,103,115,116,130,136],[121,122,127,128,130,146],[101,113,138,140,144,149],[121,126,144,148,149],[101,107,121,134,135]]),
([v0,v1,v2,v31,v3,v11,v16],[],[0,1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,102,106,114,116,181,184,198,200,225,234,235,242],[[104,105,112],[104,106,114],[104,129],[100,101,120],[104,108,116],[104,110,127],[119,121,124],[119,132],[101,102,111],[115,117,132],[119,122,132],[125,131],[101,103,113],[117,118,123],[125,131],[101,128],[117,133],[130],[101,107,117],[101,109,126],[117,133]]),
([v0,v1,v2,v157,v3,v11,v16],[0,7],[0,1,5,7,9,12,15,19,24,30,35,49,54,80,81,84,88,89,96,106,116,127,128,181,184,223,225,235,249,252,255],[[103,110],[103,104,112],[103,110],[100,101,117],[103,106,113],[103,108,124],[120,127],[116],[101,109],[114,127,129],[122,126,127],[1,120,130],[101,102,111],[114,115,119],[120,121,125],[101,109],[0,114],[126,128],[101,105,114],[101,107,123],[114,118,126]]),
([v0,v1,v2,v390,v3,v11,v16],[4],[0,1,3,7,8,12,15,19,24,28,34,52,56,79,80,81,88,89,102,109,116,117,125,127,181,184,224,225,234,235],[[103,104,110],[103,112],[103,112],[100,101,117],[103,106,114],[103,108,125],[116,121],[116,121],[101,102,109],[113,115,129],[116,118,126],[120],[101,111],[115,119],[123,127,128],[101,111],[115,119],[0,127],[101,105,115],[101,107,124],[115,122,127]]),
([v0,v1,v2,v46,v3,v11,v16],[0,7],[0,1,7,12,15,19,24,30,33,35,37,52,56,80,81,84,88,89,91,96,106,108,116,117,127,128,181,184,223,224,225,235,255],[[102,109],[102,110,112],[102,109],[100,101,117],[102,104,113],[102,106,127],[118,122,123],[116],[101,107],[114,121,131],[123,125,129],[132],[101,108,111],[114,115,120],[122,124,128],[101,107],[0,114],[1,130],[101,103,114],[101,105,126],[114,119,130]]),
([v0,v1,v2,v391,v3,v11,v16],[0,7],[1,3,5,7,8,9,12,19,28,29,35,40,46,49,56,79,80,81,84,88,89,91,96,102,106,116,117,127,181,195,223,224,225,235],[[104,110,114],[105,110,114],[103],[100,109,120],[110,111,116],[110,112,129],[119,121,126],[],[100,101,108],[115,117,133],[119,123,131],[],[100,102,113],[117,118,124],[125,127,130],[0,100],[0,117],[1,132],[100,106,117],[100,107,128],[117,122,132]]),
([v0,v1,v2,v3,v392,v11,v16],[],[1,3,7,8,9,12,15,19,24,28,34,49,52,54,79,81,88,89,93,96,102,106,109,114,116,117,127,172,181,184,223,224,225,235,249,256],[[102,103,110],[102,104,113],[100,102,118],[102,117,135],[102,106,122],[102,108,129],[116,123,124],[100,101,109],[116,125],[114,115,133],[116,120,131],[100,111,127],[124,127],[115,121,122],[124,126,130],[112],[100,105,115],[100,107,128],[115,122],[132,134],[115,119,132]]),
([v0,v1,v2,v3,v393,v11,v16],[],[1,3,7,8,9,15,24,29,30,34,42,54,67,80,81,88,89,96,108,109,114,116,117,128,167,172,173,178,184,193,223,224,225,235,249,255,256],[[102,103,109],[102,104,111],[102,107,116],[102,136],[102,105,113],[102,106,128],[120,122,135],[101,108,126],[115,122,126],[114,118,133],[122,123,131],[108,112,125],[121,125,135],[114,119],[125,127,130],[100],[108,114,124],[108,110,129],[114,119],[132,134],[114,117,132]]),
([v0,v1,v2,v3,v394,v11,v16],[7],[1,5,7,8,9,12,15,19,24,28,30,34,49,54,80,81,84,88,89,96,106,108,114,116,117,127,128,167,172,173,181,184,223,224,225,235,255],[[102,103,111],[102,104,113],[100,102,118],[102,118],[102,106,114],[102,108,131],[122,123,136],[100,109,129],[117,124,129],[115,121,135],[124,126,133],[100,101,112],[123,128],[115,116,120],[123,125,132],[110],[100,105,115],[100,107,130],[115,127],[0,134],[115,119,134]]),
([v0,v1,v2,v3,v395,v11,v16],[7],[1,5,7,8,9,15,24,34,51,52,54,59,63,68,79,80,81,84,88,89,96,102,106,114,116,117,127,167,172,173,184,205,223,224,225,235],[[102,103,107],[102,104,110],[102,108,119],[102,119],[102,105,115],[102,106,130],[118,123,124],[109,113,129],[118,125,129],[114,116,135],[118,121,133],[101,109,128],[124,128],[116,117,122],[124,126,132],[100],[109,111,116],[109,112,131],[116,127],[0,134],[116,120,134]]),
([v0,v1,v2,v3,v59,v11],[6],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,102,106,109,114,116,117,143,167,172,173,178,181,184,188,190,223,224,225,234,235,249,252,255],[[104,105,113,114,123,131],[104,106,117,118,130,148],[0,100,101,104,124],[104,110,138,140,143,146],[104,108,120,121,124,128],[123,125,129,130,131,148],[101,102,111,112,123,135],[123,126,142,143,145,146],[119,121,123,145,147],[101,103,115,116,130,134],[130,136,141,143,144],[121,122,127,128,130,144],[101,109,137,139,143,146],[101,107,121,132,133],[121,143,146,147]]),
([v0,v1,v2,v3,v396,v11,v16],[],[1,7,8,9,15,24,29,34,54,79,81,84,88,89,91,96,102,106,109,113,116,117,120,121,127,134,164,169,173,184,220,223,224,225,232,235,249,255,256],[[101,102,107],[101,103,108],[101,106,134],[101,113,138],[101,104,118],[101,105,129],[112,114,125],[112,123,128],[112,121,128],[109,110,135],[112,116,132],[120,122,127],[120,137],[110,111,117],[120,124,131],[100],[110,119,126],[130,133,136],[110,118],[133,136],[110,115,133]]),
([v0,v1,v2,v3,v397,v11,v16],[],[1,7,8,9,15,24,34,51,54,79,80,81,84,88,89,91,96,102,109,113,116,117,120,121,164,170,172,178,184,220,223,224,225,232,235,249,255],[[101,102,106],[101,103,108],[101,107,114],[101,114],[101,104,110],[101,105,128],[113,115,121],[113,123,125],[113,121],[109,111,134],[113,117,131],[122,126,133],[120,126,136],[111,112,118],[126,127,130],[100],[111,119,124],[129,132,135],[111,118],[132,135],[111,116,132]]),
([v0,v1,v2,v3,v398,v11,v16],[],[1,3,7,8,9,15,24,30,33,34,42,54,67,81,84,88,89,93,96,106,108,109,114,116,117,127,128,167,172,173,184,193,223,224,225,235,249,255,256],[[102,103,109],[102,104,111],[102,107,117],[102,116,138],[102,105,121],[102,106,130],[122,123,137],[101,107,129],[115,124,129],[113,120,135],[124,126,133],[107,108,112],[123,128],[113,114,119],[123,125,132],[100],[107,113,127],[107,110,131],[113,121],[134,136],[113,118,134]]),
([v0,v1,v2,v3,v399,v11,v16],[7],[1,5,7,8,9,15,24,34,52,53,54,59,63,68,79,80,81,88,89,96,102,106,109,114,116,127,133,136,172,184,205,223,224,225,235],[[102,103,107],[102,104,110],[102,108,118],[102,118],[102,105,115],[102,106,129],[117,123,124],[108,109,113],[117,127],[114,116,134],[117,120,132],[101,108,128],[124,128],[116,121,122],[124,125,131],[100],[108,111,116],[108,112,130],[116,126],[0,133],[116,119,133]]),
([v0,v1,v2,v3,v60,v279,v11],[5],[1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,81,84,88,89,91,93,96,102,106,109,114,116,117,172,178,181,184,223,224,225,235],[[103,104,111],[103,105,113],[100,103,120],[103,109,131],[118],[103,107,124],[117,119,125],[100,101,110],[117,122,133],[117,127],[114,115,135],[100,102,112],[126,129,132],[126,128],[115,116,123],[100,108,130],[],[100,106,115],[0],[115,121,134],[115,124]]),
([v0,v1,v2,v3,v60,v11],[2],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,96,102,106,109,114,116,117,143,167,172,173,178,181,184,188,190,223,224,225,234,235,242,249,252,255],[[104,105,113,114,123,132],[104,106,117,118,131,150],[0,100,101,104,124],[104,110,139,141,144,148],[104,108,120,121,124,129],[123,125,130,131,132,150],[101,102,111,112,123,136],[123,127,143,144,146,148],[119,121,123,146,149],[101,103,115,116,131,135],[131,137,142,144,145],[121,122,128,129,131,145],[101,109,138,140,144,148],[101,107,121,133,134],[121,126,144,147,148]]),
([v0,v1,v2,v3,v400,v11,v16],[],[1,7,8,9,15,24,33,34,53,54,69,70,76,79,80,81,88,89,91,96,102,109,113,116,117,171,172,173,178,184,220,223,224,225,235,249,255],[[101,102,107],[101,103,109],[101,110,117],[101,117],[101,104,114],[101,105,129],[116,118,125],[108,111,127],[116,124,127],[113,115,134],[116,120,132],[106,111,126],[123,126,136],[115,121],[126,128,131],[100],[111,115,122],[111,112,130],[115,121],[133,135],[115,119,133]]),
([v0,v1,v2,v3,v401,v11,v16],[0,7],[1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,80,81,84,88,89,91,96,102,106,116,117,127,134,181,184,223,224,225,235,256],[[103,104,111],[103,105,113],[100,103,119],[134],[103,107,115],[103,109,129],[118,120,127],[100,101,110],[125],[114,116,133],[118,122,131],[100,102,112],[124],[116,117,123],[124,126,130],[],[100,106,116],[100,108,128],[0,116],[1,132],[116,121,132]]),
([v0,v1,v2,v3,v32,v163,v11],[4],[1,5,7,8,9,15,24,34,51,52,53,54,59,63,68,79,80,81,88,89,109,116,117,125,128,172,178,184,205,223,224,225,235],[[102,103,107],[102,104,111],[102,108,119],[102,106,127],[102,119],[102,105,116],[118,122],[109,110,114],[118,124,130],[118,122],[115,117,132],[101,109,125],[125,126,129],[121],[117,120],[109,113,128],[100],[109,112,117],[0],[117,123,131],[117,120]]),
([v0,v1,v2,v3,v32,v11],[1,4],[0,1,3,5,7,8,9,12,15,24,28,30,34,35,49,52,54,56,63,79,80,81,84,88,89,91,106,109,114,116,117,125,128,143,167,172,173,178,181,184,190,213,223,224,225,232,234,235,249,252],[[104,105,112,113,123,130],[104,106,116,117,129],[100,101,104,124,145],[104,109,139,140,144,148],[104,108,120,121,124,127],[123,125,128,129,130],[101,102,110,111,123,136],[123,132,143,144,147,148],[119,121,123,147,149],[101,103,114,115,129,135],[0,1,129,137,142,144,146],[121,122,126,127,129,146],[101,118,138,141,144,148],[101,107,121,133,134],[121,131,144,148,149]]),
([v0,v1,v2,v3,v402,v11,v16],[0,7],[1,3,5,7,8,9,12,15,19,24,28,34,49,54,79,81,84,88,89,91,93,96,102,109,116,117,172,178,181,184,223,224,225,235],[[103,104,111],[103,105,113],[100,103,120],[118],[103,107,123],[103,109,129],[117,119,125],[100,101,110],[117],[114,115,133],[117,122,131],[100,102,112],[124],[115,116,123],[126,127,130],[],[100,106,115],[100,108,128],[0,115],[1,132],[115,121,132]]),
([v0,v1,v2,v3,v403,v11,v16],[0,7],[1,3,5,7,8,9,15,24,29,30,34,42,52,54,59,80,81,84,88,89,91,96,106,108,116,117,127,128,184,193,223,224,225,235,255],[[103,104,110],[103,105,113],[103,108,119],[103],[103,106,115],[103,107,128],[120,124,125],[101,109,112],[118],[116,123,133],[125,127,131],[102,109,112],[134],[116,117,122],[124,126,130],[100],[109,114,116],[109,111,129],[0,116],[1,132],[116,121,132]]),
([v0,v1,v2,v147,v11,v16],[0,10],[0,1,3,5,7,8,9,11,12,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,96,102,111,113,114,116,117,127,142,143,181,184,188,190,223,224,225,232,234,235,242,249,252,255],[[104,105,113,114,123,132],[104,106,117,118,131,149],[0,100,101,104,124,143],[104,107,120,121,129,134],[104,110,137,139,142,147],[123,125,130,131,132,149],[101,102,111,112,123,132],[119,121,123,145,148],[123,127,141,142,145,147],[101,103,115,116,131,149],[121,122,128,129,131,144],[1,131,133,140,142,144],[101,108,121,129,135],[101,109,136,138,142,147],[121,126,142,146,147]]),
([v0,v1,v2,v18,v11,v16],[0,9],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,81,86,89,111,112,113,116,119,121,127,130,143,181,184,188,190,223,224,225,232,234,235,249,252,255,256],[[104,105,113,114,127],[104,106,117,118,125,143],[100,101,104,138,144],[104,108,120,121,124,142],[104,110,132,134,137,141],[125,126,127,143],[0,101,102,111,112,127],[123,124,127,140,142],[127,129,136,137,140,141],[101,103,115,116,125,143],[0,122,124,125,139],[1,125,128,135,137,139],[101,107,119,124,130,142],[101,109,131,133,137,141],[124,137,141,142]]),
([v0,v1,v47,v3,v11,v16],[],[0,1,5,7,8,9,12,15,19,24,30,35,36,37,81,82,83,88,91,96,106,109,116,117,127,128,143,146,167,172,173,181,184,188,190,223,224,225,230,232,234,235,242,249,252,255,256],[[103,104,112,113,118,123],[103,105,111,113,122,145],[100,101,103,138,139,146],[103,107,114,116,121,127],[103,109,132,134,137,143],[117,118,122,145],[101,110,118,130],[114,115,118,141,144],[118,125,136,137,141,143],[101,102,110,122,129],[114,120,122,140],[122,124,135,137,140],[101,106,114,126,128],[101,108,131,133,137,143],[114,119,137,142,143]]),
([v0,v1,v54,v46,v3,v11,v16],[],[1,5,7,9,12,19,30,32,36,37,56,61,65,81,82,83,88,91,96,106,116,127,128,169,181,196,223,224,225,230,234,235,247,250,255],[[108,109,110],[102],[103,109,134],[100,107,129],[109,111,115],[109,112,125],[117,120],[116],[100,106],[113,114,131],[117,122,127],[120,134],[100,120,123],[113,119,130],[120,121,126],[100,101,106],[113,133],[128,132],[100,104,113],[100,105,124],[113,118,128]]),
([v0,v1,v54,v3,v163,v11,v16],[0],[1,4,5,6,7,9,10,14,17,22,26,31,36,79,81,84,88,91,96,102,109,116,117,120,165,171,172,178,183,186,223,224,225,232,234,235,247,255],[[105,106,112],[104],[101,102,133],[105,137],[105,108,120],[105,110,129],[116,125],[102,103,111],[116,117,122],[113,114,135],[116,119,131],[102,123,126],[0,121,126],[114,124,134],[126,127,130],[100],[102,107,114],[102,109,128],[114,115,120],[132,136],[114,118,132]]),
([v0,v268,v2,v3,v158,v11,v16],[0],[1,2,3,6,7,8,10,16,20,25,50,55,79,80,81,84,88,89,91,96,102,106,113,116,117,118,121,127,134,166,171,173,179,182,185,223,224,225,235,239,252],[[104],[105,106,111],[101,102,117],[105,116,125],[105,107,113],[105,109,134],[123,130],[102,126,131],[0,116,124],[114,129,138],[131,132,136],[102,103,110],[116,118,128],[114,115,121],[123,127,135],[100],[102,114,122],[102,108,133],[112,114,140],[116,120,139],[114,119,137]])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x0 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (0*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x1 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (1*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x2 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (2*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x3 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (3*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x4 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (4*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x5 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (5*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x6 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (6*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x7 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (7*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x8 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (8*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x9 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (9*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x10 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (10*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x11 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (11*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x12 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (12*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x13 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (13*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x14 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (14*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x15 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (15*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x16 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (16*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x17 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (17*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x18 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (18*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x19 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (19*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x20 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (20*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x21 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (21*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x22 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (22*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x23 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (23*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x24 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (24*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x25 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (25*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x26 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (26*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x27 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (27*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x28 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (28*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x29 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (29*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x30 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (30*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x31 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (31*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x32 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (32*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x33 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (33*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x34 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (34*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x35 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (35*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x36 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (36*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x37 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (37*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x38 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (38*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x39 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (39*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x40 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (40*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x41 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (41*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x42 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (42*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x43 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (43*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x44 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (44*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x45 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (45*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x46 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (46*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x47 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (47*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x48 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (48*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x49 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (49*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x50 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (50*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x51 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (51*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x52 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (52*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x53 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (53*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x54 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (54*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x55 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (55*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x56 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (56*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x57 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (57*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x58 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (58*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x59 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (59*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x60 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (60*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x61 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (61*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x62 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (62*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x63 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (63*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x64 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (64*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x65 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (65*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x66 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (66*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x67 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (67*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x68 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (68*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x69 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (69*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x70 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (70*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x71 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (71*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x72 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (72*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x73 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (73*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x74 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (74*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x75 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (75*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x76 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (76*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x77 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (77*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x78 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (78*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x79 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (79*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x80 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (80*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x81 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (81*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x82 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (82*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x83 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (83*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x84 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (84*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x85 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (85*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x86 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (86*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x87 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (87*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x88 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (88*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x89 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (89*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x90 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (90*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x91 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (91*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x92 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (92*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x93 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (93*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x94 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (94*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x95 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (95*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x96 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (96*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x97 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (97*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x98 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (98*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC6x99 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (99*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopI6 : LevelN ptopR ptopT 6 ptopD6 := levelStep ptopB ptopW ptopQ ptopI5 (chunks 4 ptopD6 100 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC6x0
  · exact ptopC6x1
  · exact ptopC6x2
  · exact ptopC6x3
  · exact ptopC6x4
  · exact ptopC6x5
  · exact ptopC6x6
  · exact ptopC6x7
  · exact ptopC6x8
  · exact ptopC6x9
  · exact ptopC6x10
  · exact ptopC6x11
  · exact ptopC6x12
  · exact ptopC6x13
  · exact ptopC6x14
  · exact ptopC6x15
  · exact ptopC6x16
  · exact ptopC6x17
  · exact ptopC6x18
  · exact ptopC6x19
  · exact ptopC6x20
  · exact ptopC6x21
  · exact ptopC6x22
  · exact ptopC6x23
  · exact ptopC6x24
  · exact ptopC6x25
  · exact ptopC6x26
  · exact ptopC6x27
  · exact ptopC6x28
  · exact ptopC6x29
  · exact ptopC6x30
  · exact ptopC6x31
  · exact ptopC6x32
  · exact ptopC6x33
  · exact ptopC6x34
  · exact ptopC6x35
  · exact ptopC6x36
  · exact ptopC6x37
  · exact ptopC6x38
  · exact ptopC6x39
  · exact ptopC6x40
  · exact ptopC6x41
  · exact ptopC6x42
  · exact ptopC6x43
  · exact ptopC6x44
  · exact ptopC6x45
  · exact ptopC6x46
  · exact ptopC6x47
  · exact ptopC6x48
  · exact ptopC6x49
  · exact ptopC6x50
  · exact ptopC6x51
  · exact ptopC6x52
  · exact ptopC6x53
  · exact ptopC6x54
  · exact ptopC6x55
  · exact ptopC6x56
  · exact ptopC6x57
  · exact ptopC6x58
  · exact ptopC6x59
  · exact ptopC6x60
  · exact ptopC6x61
  · exact ptopC6x62
  · exact ptopC6x63
  · exact ptopC6x64
  · exact ptopC6x65
  · exact ptopC6x66
  · exact ptopC6x67
  · exact ptopC6x68
  · exact ptopC6x69
  · exact ptopC6x70
  · exact ptopC6x71
  · exact ptopC6x72
  · exact ptopC6x73
  · exact ptopC6x74
  · exact ptopC6x75
  · exact ptopC6x76
  · exact ptopC6x77
  · exact ptopC6x78
  · exact ptopC6x79
  · exact ptopC6x80
  · exact ptopC6x81
  · exact ptopC6x82
  · exact ptopC6x83
  · exact ptopC6x84
  · exact ptopC6x85
  · exact ptopC6x86
  · exact ptopC6x87
  · exact ptopC6x88
  · exact ptopC6x89
  · exact ptopC6x90
  · exact ptopC6x91
  · exact ptopC6x92
  · exact ptopC6x93
  · exact ptopC6x94
  · exact ptopC6x95
  · exact ptopC6x96
  · exact ptopC6x97
  · exact ptopC6x98
  · exact ptopC6x99
  ))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD7 : List StD := [
([v4,v0,v1,v2,v3,v11],[4,7,8],[0,1,3,7,8,12,15,22,26,28,30,34,35,52,56,79,80,81,88,89,100,109,116,117,143,167,173,223,225,232,235,247,249,252],[[1,103,114,128,132],[1,118,123,128,132],[1,122],[0,1,101,113,128,132],[0,1,117,121,128,132],[103,104,111,112,118,123],[103,108,114,127,131],[0,1,100,101,103,119,129],[0,2,103,106,116,117,119,121],[118,123,127,131],[0,1,101,102,109,110,118,126],[0,2,115,117,118,130,133],[0,1,101,107,113,127,131],[0,2,117,120,121,127,131],[0,101,105,117,124,125]]),
([v58,v0,v1,v2,v3,v11,v16],[0,7],[0,1,7,8,9,15,24,34,35,54,56,79,81,84,88,89,91,96,102,106,109,113,114,116,117,120,121,127,146,164,167,169,170,172,173,184,190,220,223,224,225,232,234,235,242,249,252,255],[[0,115],[114,124],[123,147],[0,101],[0,112,120],[1,140,145],[102,103,107,108,114,124],[102,104,109,110,123,147],[0,100,102,141],[102,105,112,120,128],[102,106,135,136,140,145],[114,116,122,123,124,147],[0,114,126,132,134,141],[111,112,114,143,146],[114,118,139,140,143,145],[0,123,125,131,133,141],[112,113,119,120,123,142],[1,123,127,138,140,142],[0,112,121,129,130,141],[0,1,137,140,141,145],[112,117,140,144,145]]),
([v62,v0,v1,v2,v3,v11,v16],[0,7],[0,1,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,80,81,84,88,89,96,106,109,116,127,143,166,167,171,172,173,179,181,184,188,190,223,224,225,234,235,242,249,252,255],[[103,122],[0,121],[126,132],[0,111],[0,119,130],[1,141],[103,104,112,113,133],[103,105,116,117,126,147],[0,100,101,103,122],[103,107,118,119,122,125],[103,109,136,138,141,145],[126,131,133,147],[0,101,110,133],[119,129,133,143,146],[133,134,140,141,143,145],[101,102,114,115,126,132],[119,120,124,125,126,142],[1,126,127,139,141,142],[101,106,119,128,130],[101,108,135,137,141,145],[119,123,141,144,145]]),
([v65,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,88,89,96,102,109,116,117,143,167,172,173,178,181,184,188,190,223,224,225,234,235,242,249,252,256],[[103,145],[121,127],[0,126],[0,115],[0,120,125],[1,139,143],[103,104,112,113,121,127],[103,105,116,117,130],[0,100,101,103,122],[103,107,119,120,122,125],[103,109,134,136,139,143],[121,127,130],[101,102,110,111,121,131],[118,120,121,141,144],[121,124,138,139,141,143],[0,101,114,130],[120,125,130,140],[1,130,132,137,139,140],[101,106,120,128,129],[101,108,133,135,139,143],[120,123,139,142,143]]),
([v70,v0,v1,v2,v3,v11,v16],[0,7],[1,3,7,12,19,28,30,51,52,54,56,57,61,65,73,74,79,81,88,96,102,106,109,114,116,117,127,143,160,167,172,173,181,188,209,215,223,224,225,232,234,235,242,249,252,255,256],[[102],[118,125],[145],[0,100,108],[0,117,122],[1,138],[110,111,114,115,118,125],[109,110,124],[100,107,110,139,146],[110,112,117,122,128],[110,113,134,135,138,143],[118,123,124,125],[100,101,105,106,118,131],[116,117,118,141,144],[118,120,137,138,141,143],[100,108,124,130],[117,121,122,124,140],[124,126,136,138,140],[100,103,117,127,129],[100,104,132,133,138,143],[117,119,138,142,143]]),
([v74,v0,v1,v2,v3,v11,v16],[0,7],[0,1,5,7,9,12,15,19,24,30,35,49,52,54,56,80,81,88,89,96,108,109,114,116,117,128,136,143,167,173,181,184,188,190,224,225,232,235,242,247,249,252,255],[[103,110],[117],[123],[0,101,109],[0,116,121],[1,135],[103,110,124,126],[103,104,113,114,142],[100,101,103,118,136],[103,106,115,116,118,121],[103,108,131,133,135,140],[122,124,142],[101,109,124,129],[116,120,124,137,141],[124,125,134,135,137,140],[101,102,111,112,142],[116,121,142],[135,139,142],[101,105,116,127,128],[101,107,130,132,135,140],[116,119,135,138,140]]),
([v88,v0,v1,v2,v3,v11,v16],[0,7,8],[0,1,3,5,7,8,9,19,24,28,30,34,35,49,52,54,56,59,61,81,88,89,102,106,108,109,116,117,125,133,143,167,173,181,184,188,190,223,224,225,232,234,235,249,252],[[104,121],[120,127],[0,126],[0,101,130],[0,119],[1,2,139],[104,105,111,112,120,127],[104,106,115,116,141],[100,101,104,121,140],[104,118,121,125,129],[104,108,134,136,139,143],[120,127,141],[101,102,109,110,120,132],[120,124,125,142,144],[120,122,138,139,142,143],[0,101,103,113,114,141],[0,123,125,141],[2,137,139,141],[101,117,125,130,131],[101,107,133,135,139,143],[125,128,139,143,144]]),
([v91,v0,v1,v2,v3,v11,v16],[0,7,8],[0,1,3,5,7,8,9,12,15,28,30,34,35,49,52,54,56,63,65,79,80,81,84,88,89,91,106,109,114,116,117,125,128,143,167,172,173,188,190,223,224,225,232,234,235,242,244,249,252],[[104,138],[123,146],[1,143],[0,1,101,137],[0,2,121,145],[1],[104,105,111,112,123,130],[104,106,115,116,129],[100,101,104,124,142],[104,108,120,121,124,127],[104,118,138,141,147],[123,125,128,129,130],[101,102,109,110,123,136],[119,121,123,144,148],[123,132,140,141,144,147],[101,103,113,114,129,135],[2,121,122,126,127,129],[1,129,139,141],[101,107,121,133,134],[101,117,137,141,147],[121,131,141,145,147]]),
([v93,v0,v1,v2,v3,v11,v16],[0,7],[1,5,7,12,19,29,30,34,35,37,40,46,49,52,72,74,80,81,84,88,89,96,106,108,109,114,116,117,127,128,143,167,172,173,181,188,195,200,223,224,225,232,234,235,242,249,252,255],[[102],[119],[126,147],[0,100,106],[0,117,146],[1,140,145],[107,108,127],[108,109,114,115,126,147],[100,105,108,120,141],[108,110,116,117,120,124],[108,111,136,137,140,145],[125,126,127,147],[100,106,127,133],[117,123,127,143,146],[127,129,139,140,143,145],[100,101,112,113,126,132],[117,118,122,124,126,142],[126,128,138,140,142],[100,103,117,130,131],[100,104,134,135,140,145],[117,121,140,144,145]]),
([v97,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,7,8,12,15,19,24,28,30,33,34,35,37,52,56,79,80,81,84,88,89,96,102,106,109,114,116,117,127,143,167,172,181,184,188,190,223,225,232,234,239,242,244,249,252,255],[[103,116],[129],[147],[0,101,115],[0,119,146],[1,139,145],[103,104,112,113,121],[103,114,116,128],[100,101,103,122,140],[103,106,118,119,122,126],[103,108,135,137,139,145],[121,127,128],[101,102,109,110,121],[117,119,121,146],[121,124,139,142,144,145],[101,111,115,128,133],[119,120,125,126,128,141],[128,130,138,139,141],[101,105,119,131,132],[101,107,134,136,139,145],[119,123,139,143,145]]),
([v104,v0,v1,v2,v3,v11,v16],[0,7,8],[0,1,3,5,7,8,9,19,24,28,30,34,35,40,49,52,54,56,79,80,81,84,88,89,96,106,109,113,116,127,143,146,167,172,181,184,188,190,223,224,225,232,233,234,235,242,249,252,255],[[104,131],[0,122],[128,148],[0,101,130],[0,147],[1,2,140,146],[104,105,111,112,144],[104,106,116,117,128,148],[100,101,104,123,141],[104,113,119,120,123,126],[104,108,135,137,140,146],[128,142,144,148],[0,101,102,109,110,144],[0,118,120,144],[2,139,140,144,146],[101,103,114,115,128,133],[120,121,125,126,128,143],[2,128,129,138,140,143],[101,120,127,130,132],[101,107,134,136,140,146],[120,124,140,145,146]]),
([v309,v0,v1,v2,v3,v11,v16],[0,6,7,8],[0,1,3,5,7,8,9,12,15,28,30,34,35,42,46,49,52,54,56,79,80,81,84,88,89,91,96,106,109,114,116,117,127,143,167,172,173,188,190,223,224,225,232,234,235,242,249,252,255],[[104,138],[2,144],[130,148],[0,2,101,137],[0,3,121,147],[2,146],[104,105,111,112,123,131],[104,106,117,118,130,148],[100,101,104,124,142],[104,108,120,121,124,128],[2,104,114,138,141],[123,125,129,130,131,148],[101,102,109,110,123,136],[3,119,121,123,147],[2,123,140,141],[101,103,115,116,130,135],[121,122,127,128,130,143],[2,130,132,139,141,143],[101,107,121,133,134],[1,101,113,137,141],[1,121,126,141,145]]),
([v110,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,9,12,15,19,24,28,30,34,35,49,52,54,56,79,81,84,88,91,96,102,106,109,116,117,127,134,136,143,146,167,172,181,184,188,190,223,225,232,234,239,242,244,249,252,255,256],[[113],[128],[127,149],[0,101,142],[0,119,126],[1,141,147],[104,112,121],[104,105,116,117,127,149],[100,101,104,142,150],[104,107,119,126,133],[104,109,137,139,141,147],[121,122,127,130,131,149],[101,102,110,111,121],[118,119,121,148],[121,124,141,144,146,147],[101,103,114,115,127,135],[119,120,125,126,127,143],[127,129,140,141,143],[101,106,119,132,134],[101,108,136,138,141,147],[119,123,141,145,147]]),
([v72,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,8,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,96,102,109,116,117,143,167,173,181,184,188,190,224,225,232,235,242,247,249,252,255],[[117],[122,129],[128],[0,101,139],[0,120,127],[1,138,143],[104,105,112,113,122,129],[104,116,145],[100,101,104,123,139],[104,107,119,120,123,127],[104,109,134,136,138,143],[122,124,129,145],[101,102,110,111,122,132],[118,120,122,140,144],[122,126,137,138,140,143],[101,103,114,115,145],[120,121,127,145],[138,142,145],[101,106,120,130,131],[101,108,133,135,138,143],[120,125,138,141,143]]),
([v322,v0,v1,v2,v3,v11,v16],[0,7,8],[0,1,3,5,7,8,9,12,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,96,102,109,114,116,117,127,131,133,143,172,173,181,184,188,190,223,224,225,232,234,235,242,249,252,255],[[0,123],[122,130],[129,145],[0,101],[0,127],[1,2,143],[104,105,112,113,122,130],[104,106,116,117,129,150],[0,100,101,104,144],[0,104,119,120],[104,109,138,140,143,148],[122,124,128,129,130,150],[101,102,110,111,122,136],[118,120,122,146,149],[122,126,142,143,146,148],[101,103,114,115,129,135],[120,121,129,132,133,145],[2,129,131,141,143,145],[0,101,107,120,134],[101,108,137,139,143,148],[120,125,143,147,148]]),
([v310,v0,v1,v2,v3,v11,v16],[0,7,8],[0,1,3,5,7,8,9,12,15,19,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,96,102,106,109,114,116,117,143,167,172,173,181,184,188,190,225,232,234,235,238,242,249,252,255,259],[[1,139],[122,143],[130,142],[0,1,101,141],[0,2,120,149],[1,140],[104,105,112,113,122,131],[104,106,116,117,130,148],[100,101,104,123,141],[104,108,119,120,123,128],[1,104,137,146],[122,124,129,130,131,148],[101,102,110,111,122,135],[118,120,122,143,147],[1,122,126,143,146],[101,103,114,115,130,134],[120,121,127,128,130,142],[1,130,142,146],[101,107,120,132,133],[1,101,109,136,138,146],[1,2,120,125,144,145,146]]),
([v136,v0,v1,v2,v3,v11,v16],[0,7],[0,1,5,7,8,9,12,15,19,24,30,35,49,52,54,56,81,84,88,96,106,108,109,114,116,117,127,128,143,146,167,172,173,181,184,188,190,223,224,225,232,234,235,242,249,252,255,256],[[111],[118],[124],[0,101,110],[0,116,122],[1,139],[103,104,125],[103,105,114,115,124,146],[100,101,103,140,147],[103,107,116,122,129],[103,109,134,136,139,144],[123,124,125,146],[101,110,125,132],[116,121,125,142,145],[125,127,138,139,142,144],[101,102,112,113,124,131],[116,117,120,122,124,141],[124,126,137,139,141],[101,106,116,128,130],[101,108,133,135,139,144],[116,119,139,143,144]]),
([v139,v0,v1,v2,v3,v11,v16],[0,7],[0,1,3,7,8,9,12,15,19,24,28,30,34,35,52,56,79,80,81,88,89,96,102,106,109,114,116,117,127,133,136,143,167,172,173,181,184,188,190,223,224,225,232,234,235,242,249,252,255],[[115],[119,130],[148],[0,101,114],[0,118,129],[1,141,146],[103,104,112,113,119,127],[103,105,126],[100,101,103,120,142],[103,107,117,118,120,124],[103,109,136,138,141,146],[119,125,126,127],[101,102,110,111,119,134],[116,118,119,144,147],[119,122,140,141,144,146],[101,114,126,133],[118,123,124,126,143],[126,128,139,141,143],[101,106,118,131,132],[101,108,135,137,141,146],[118,121,141,145,146]]),
([v145,v0,v1,v2,v3,v11,v16],[0,7,8],[0,1,3,5,7,8,9,15,19,24,28,30,34,35,49,52,54,56,81,88,89,91,102,106,108,109,113,114,116,117,125,127,143,167,172,173,181,184,188,190,223,224,225,232,234,235,249,255,259],[[0,120],[119,129],[128,147],[0,101,132],[0,118],[1,2,142,146],[104,105,112,113,119,129],[104,106,116,117,128,147],[0,100,101,104,143],[0,104,107,125],[104,109,137,139,142,146],[119,121,127,128,129,147],[101,102,110,111,119,135],[0,119,124,125,145],[119,122,141,142,145,146],[101,103,114,115,128,134],[0,123,125,128,144],[2,128,131,140,142,144],[101,125,126,132,133],[101,108,136,138,142,146],[125,130,142,146,148]]),
([v323,v0,v1,v2,v3,v11,v16],[0,2,7,8],[0,1,3,5,7,8,9,12,15,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,106,109,114,116,117,125,127,128,143,167,172,173,188,190,223,224,225,232,234,235,242,244,249,252,255],[[2,138],[122,146],[128,149],[0,2,101,137],[0,3,120,145],[2,147],[104,105,112,113,122,129],[104,106,116,117,128,149],[100,101,104,123,142],[104,108,119,120,123,126],[2,104,109,141],[122,124,127,128,129,149],[101,102,110,111,122,136],[118,120,122,144,148],[2,122,132,140,141,144],[101,103,114,115,128,135],[120,121,125,126,128,143],[2,128,131,139,141,143],[101,107,120,133,134],[1,101,137,141],[1,120,130,141,145]]),
([v0,v5,v1,v2,v3,v11,v16],[0,7],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,70,74,79,80,81,88,89,91,96,102,109,116,117,143,167,181,184,188,190,225,232,239,242,244,247,249,252,255],[[104,120],[104,105,113,114,124],[104,106,117,118,146],[100,101,104,125,139],[104,108,122,123,125,129],[104,110,135,137,138,144],[131],[130],[0,101,119],[0,123,129],[1,138,144],[124,126,146],[101,102,111,112,124],[121,123,124,145],[124,128,138,140,142,144],[101,103,115,116,146],[123,129,146],[138,143,146],[101,107,123,132,133],[101,109,134,136,138,144],[123,127,138,141,144]]),
([v0,v156,v1,v2,v3,v11,v16],[0,7,8],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,81,88,89,116,127,140,143,172,181,184,188,190,223,224,225,232,233,234,235,237,246,249,252,255],[[104,121],[104,105,113,114,137],[104,106,117,118,122,142],[100,101,104,121,134],[0,104,108,121,141],[104,110,128,130,133,140],[0,120],[122,136],[0,101],[0,119],[1,2,133],[122,135,137,142],[0,101,102,111,112,137],[0,137,138,141],[2,132,133,137,140],[101,103,115,116,122,126],[0,122,136,141],[2,122,123,131,133,136],[0,101,107,124,125,141],[101,109,127,129,133,140],[0,2,133,139,140,141]]),
([v0,v311,v1,v2,v3,v11,v16],[0,7,8],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,102,106,109,114,116,117,143,167,172,173,181,184,188,190,198,200,225,232,234,235,242,249,252,255],[[104,141],[104,105,113,114,123,131],[104,106,117,118,130,149],[100,101,104,124,143],[104,108,120,121,124,128],[1,104,110,137,139,147],[1,145],[130,144],[0,1,101,140],[0,2,121,146],[1,142],[123,125,129,130,131,149],[101,102,111,112,123,135],[2,119,121,123,148],[1,123,126,147],[101,103,115,116,130,134],[121,122,127,128,130,144],[1,130,144,147],[101,107,121,132,133],[1,101,109,136,138,147],[1,2,121,146,147]]),
([v0,v1,v268,v2,v3,v11,v16],[0,7],[1,3,5,7,8,12,19,28,29,30,35,37,40,46,49,52,72,74,79,80,81,84,88,89,91,96,102,106,109,116,117,127,134,136,143,167,172,181,188,195,200,223,225,232,234,239,242,244,249,252,255],[[104,110,122],[103],[110,111,116,117,129,150],[100,108,110,123,143],[110,112,119,120,123,128],[110,113,139,140,142,148],[130],[122,124,129,132,133,150],[100,101,107,109,122],[118,120,122,149],[122,126,142,145,147,148],[129],[0,100],[0,120],[1,142],[100,102,114,115,129,136],[120,121,127,128,129,144],[129,131,141,142,144],[100,105,120,134,135],[100,106,137,138,142,148],[120,125,142,146,148]]),
([v0,v1,v17,v2,v3,v11,v16],[0,7,8],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,96,102,109,116,117,143,158,160,173,181,184,188,190,223,224,225,232,234,235,242,249],[[104,105,113,114,123,129],[104,132],[104,106,117,118,142],[100,101,104,124,141],[0,104,108,120,121,124],[104,110,135,137,140,145],[123,129],[123,129,142],[101,102,111,112,123,133],[0,119,121,123,143],[123,126,139,140,143,145],[0,128],[0,101,131],[0,127],[1,2,140,145],[0,101,103,115,116,142],[0,121,122,142],[2,138,140,142],[0,101,107,121,130],[101,109,134,136,140,145],[121,125,140,144,145]]),
([v0,v1,v9,v2,v3,v11],[1,7],[0,1,3,5,7,8,9,12,15,28,30,34,35,49,52,54,56,63,65,79,80,81,84,88,89,91,106,109,114,116,117,125,128,143,167,172,173,205,209,213,215,223,224,225,232,235,249,252],[[104,105,111,112,123,130],[104,118,138,140,143,146],[104,106,115,116,129],[0,100,101,104,124,144],[0,104,108,120,121,124,127],[123,132,142,143,145,146],[123,125,128,129,130],[0,101,102,109,110,123,136],[0,119,121,123,145,147],[1,141],[0,101,117,137,139,143,146],[0,121,131,143,146,147],[0,101,103,113,114,129,135],[0,121,122,126,127,129],[0,101,107,121,133,134]]),
([v0,v1,v9,v2,v3,v11,v16],[0,1,7,8],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,96,102,106,109,114,116,117,127,143,167,172,173,181,184,188,190,213,215,225,232,234,235,238,242,252],[[104,105,113,114,123,132],[104,143],[104,106,117,118,131],[100,101,104,124,145],[104,108,120,121,124,129],[2,104,110,139,141],[123,147],[123,125,130,131,132],[101,102,111,112,123,137],[119,121,123,147,150],[2,123,127,147],[2,146],[0,2,101,142],[0,3,121,150],[2,144],[101,103,115,116,131,136],[3,121,122,128,129,131],[2,131,133],[101,107,121,134,135],[1,2,101,109,138,140],[1,2,3,121,126,148,149]]),
([v0,v1,v2,v54,v3,v11,v16],[0,7],[1,3,5,7,9,12,19,28,30,49,51,52,56,57,61,65,73,74,79,81,84,88,91,96,102,109,116,117,143,160,167,173,181,188,209,215,224,225,232,235,242,247,249,252,255,256],[[112,113,116,117,121,127],[104,112,144],[103],[100,110,112,138,145],[112,114,119,125,129],[112,115,134,135,137,142],[121,122,127,144],[121],[100,101,107,108,121,131],[118,119,121,139,143],[121,124,136,137,139,142],[126],[100,102,109,111,144],[119,120,125,144],[137,141,144],[0,100],[0,119],[1,137],[100,105,119,128,130],[100,106,132,133,137,142],[119,123,137,140,142]]),
([v0,v1,v2,v46,v3,v11,v16],[0,7],[0,1,7,12,15,19,24,30,33,35,37,52,56,80,81,84,88,89,91,96,106,108,109,116,117,127,128,136,143,167,172,173,181,184,188,190,223,224,225,232,234,235,242,249,252,255],[[102,109,124,127],[102,110,112,123],[102,109],[100,101,102,117,139],[102,104,113,114,117,122],[102,106,133,135,138,143],[118,123,124],[116],[101,107,124,131],[114,121,124,141,144],[124,126,137,138,141,143],[145],[101,108,111,123,130],[114,115,120,122,123,140],[123,125,136,138,140],[0,101,107],[0,114],[1,138],[101,103,114,128,129],[101,105,132,134,138,143],[114,119,138,142,143]]),
([v0,v1,v2,v3,v279,v11,v16],[0,7],[1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,81,84,88,89,91,93,96,102,106,109,114,116,117,127,143,146,167,172,173,181,184,188,190,223,224,225,232,234,235,242,249,252,255],[[103,104,112,113,121,131],[103,105,116,117,130,151],[0,100,103,124],[0,122],[103,107,119,128,134],[103,109,139,141,144,149],[121,123,129,130,131,151],[100,101,110,111,121,137],[121,131],[118,119,121,147,150],[121,126,143,144,147,149],[100,102,114,115,130,136],[130,136],[119,120,127,128,130,146],[1,130,132,142,144,146],[0,145],[100,106,119,133,135],[100,108,138,140,144,149],[0,119,128],[1,144],[119,125,144,148,149]]),
([v0,v1,v2,v3,v158,v11,v16],[0,7],[1,3,7,8,9,15,24,29,30,33,34,35,42,54,56,67,70,80,81,84,88,89,96,106,109,113,116,127,166,167,171,172,173,179,184,190,193,198,223,224,225,232,234,235,242,249,252,255,256],[[102,103,110,111,132],[102,104,113,114,126,147],[102,107,108,121,141],[102,148],[102,105,117,118,121,124],[102,106,134,135,140,145],[126,130,132,147],[0,101,108,132],[0,120],[118,128,132,143,146],[132,133,139,140,143,145],[108,109,115,116,126,131],[126,147],[118,119,123,124,126,142],[1,126,127,138,140,142],[0,100],[0,108,118,125,129],[108,112,136,137,140,145],[0,118,146],[1,140,145],[118,122,140,144,145]]),
([v0,v1,v2,v3,v163,v11,v16],[0,7],[1,5,7,8,9,15,24,34,35,51,52,53,54,56,59,63,68,70,79,80,81,88,89,96,102,109,116,117,158,167,172,173,178,184,190,205,213,223,224,225,232,234,235,242,249,252],[[102,103,107,108,121,127],[102,104,112,113,130],[102,109,110,122,140],[102,122],[102,105,119,120,122,125],[102,106,133,134,139,144],[121,127,130],[110,111,116,117,121,131],[121,127],[118,120,121,142,145],[121,124,138,139,142,144],[0,101,110,130],[0,126],[120,125,130,141],[1,130,132,137,139,141],[0,100],[110,114,120,128,129],[110,115,135,136,139,144],[0,120,125],[1,139],[120,123,139,143,144]])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC7x1 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (1*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC7x2 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (2*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC7x3 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (3*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC7x4 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (4*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC7x5 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (5*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC7x6 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (6*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC7x7 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (7*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopI7 : LevelN ptopR ptopT 7 ptopD7 := levelStep ptopB ptopW ptopQ ptopI6 (chunks 4 ptopD7 8 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  · exact ptopC7x1
  · exact ptopC7x2
  · exact ptopC7x3
  · exact ptopC7x4
  · exact ptopC7x5
  · exact ptopC7x6
  · exact ptopC7x7
  ))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD8 : List StD := [
([v0,v1,v2,v3,v11,v16],[0,7,8],[0,1,3,5,7,8,9,12,15,19,24,28,30,34,35,49,52,54,56,79,80,81,84,88,89,91,96,102,106,109,114,116,117,127,143,167,172,173,181,184,188,190,223,224,225,232,234,235,242,249,252,255],[[104,105,113,114,123,132],[104,106,117,118,131,151],[0,100,101,104,124,145],[0,104,108,120,121,124,129],[1,104,110,139,141,144,149],[123,125,130,131,132,151],[0,101,102,111,112,123,137],[0,119,121,123,147,150],[1,123,127,143,144,147,149],[0,101,103,115,116,131,136],[0,121,122,128,129,131,146],[1,131,133,142,144,146],[0,101,107,121,134,135],[0,1,101,109,138,140,144,149],[0,1,2,121,126,144,148,149]])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*4)).take 4) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ptopI8 : LevelN ptopR ptopT 8 ptopD8 := levelStep ptopB ptopW ptopQ ptopI7 (chunks 4 ptopD8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  ))
theorem ptopL : LowN ptopR ptopT 9 := lowSearch ptopB ptopI8 (by decide +kernel)

def sixInputs : List Sig := rootsW [0,1,2,3,4,5]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
def sample (r : Row) (i : Fin 6) : Bool := bit r (sixInputs.getD i.val zero)
theorem sixList : List.ofFn (fun i : Fin 6 => sixInputs.getD i.val zero) = sixInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = sixInputs.map (bit r) := by
  rw [←sixList,List.map_ofFn]
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sixTable : ∀ r : Row, bit r graph = target (sample r) := by decide +kernel
theorem sixEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sixInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sixInputs.toFinset := by
  have b := baseOK_ok ptopB
  have goalEq : (execute C.gates sixInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sixEval C legal C.output r).trans ((computes (sample r)).trans (sixTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sixInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W ptopT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sixInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sixInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = sixInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run sixInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes : Impossible true graph 8 sixInputs.toFinset := by
  intro k small run
  have steps := list_run run sixInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sixInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega
theorem replaceShort (s : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 target s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  classical
  by_cases big : 10 ≤ s
  · exact ⟨smallCircuit,witnessMonotone,(by rw [witnessSize]; exact big),witnessCorrect⟩
  obtain ⟨C,legal,hs,correct⟩ := h
  by_cases mono : ∀ g ∈ C.gates, g.op ≠ GateOp.not
  · refine ⟨C,?_,hs,correct⟩
    intro g hg
    obtain ⟨ho,hl⟩ := legal g hg
    refine ⟨?_,hl⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ho ⊢
    rcases ho with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact (mono g hg a).elim
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
    rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  obtain ⟨k,hk,run⟩ := physicalSigned C legal correct
  have hs' : C.gates.length ≤ s := hs
  exact (excludes k (by omega) run).elim

end PEqualNP.Outside.L_meta_13441

theorem PEqualNP.Outside.L_meta_13441 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132800 * 2 ^ 32 + 3939019264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132800 * 2 ^ 32 + 3939019264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_13441.replaceShort
