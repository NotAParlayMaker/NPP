import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3233
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

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
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

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
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

private lemma gate_rep (w : List Sig) (g : Gate)
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
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
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

private lemma extract (gs : List Gate) (w : List Sig)
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
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

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
def seed : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 2) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
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

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


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
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 2 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 2)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 2) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (2 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 2 zero).getLsbD (asRow v i).val = (v 2).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 2 zero := by decide +kernel
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
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
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
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
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
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
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
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
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
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
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
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
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
def mined8 (i : Nat) : Nat := 0x343d097a5b1e8b63d0805c18e98980ae2e79ecc6115260160592f839e72d5845498058164be8c784b561152601605927cb1e7b75525056044164
def minel8 : Packing := (4,7,7,0,0,7,0,mined8)
def mined9 (i : Nat) : Nat := (if i<1 then 0xc0b26eae611c32d58058164bd5ce916ac2300b02c97c78d56dd736016059375738ac2164c02c0b26eae611c32c980581649e7cebd98a9300b02c97c79d72d55260160592fcb3a65aaa4c02c0b25f9c744b55498058164dd5d66308a9300b02c9bab9c76115260160593f1718ec22a4c02c0b27e8e2d5845498058164fd1cbab08a9300b02c9faa9845c9526016059365f326e40a4c02c0b26eae611c3149805816483ff6e996cc34ea82c9f5717154570655505920ffdba65b4ec9aa0b261ef610cb69d935416483ff6e996d4324a82c907fcdb705a8649505920ffdba65b4ec92a0b241ff36dca61d9254164e9bcdbb2ac2b00a82c945fdd7aeda95493059299fbaf5db4ca9260b26ee6611c32d5804c164d5dcc239429300982c9bb998470c52601305930df972e316ad4240b241ff36dc8aa9974816483ff6e996d432e902c907fcdb705a865d205920ffdba65b30d2a40b2517f75ebb661a54816483fe6db915532a902c907fedd32da8655205920ff9b6e0b50caa40b241ff36dca61d954816483fe6e352dc2ea902c907fcdc6e9985d5205925b7baf6634ac2240b241ff36dc8aa9934816492feebd98d2b26902c907fedd32da564d205930f7b0865b4ac9a40b241ff36dca5d59348164967eebd98d2ac6902c925fdd7b31a5645205925b7baf6634aa0a40b27ab5605636a13148164fab4cc2eaa92e0902c9fd2975611525c120593ead2eac9aa4b8240b27f1a5d5635497048164fab4baaa4c8ae0902c9fd2975549415c120593ebc2e2caa42b8240b27d78661714857048164fed0c22e290ae0902c9f5e1935c5215c120593f9c2c6b8a42b8240b27fb058d314857048164fea463aa6a9260902c9bf49c5549314c120593d7a350c0a6298240b241ffb74cb69d9344164c3dec2196d3b26882c907fedd32da7649105930dfac665b4ec9220b277ac505606e1724416483fe6e374cc2e4882c907fcdc6e9955c9105920ff9b8dd326b9220b241ff371976e95244164a2feebd76d4aa4882c907fcdc6e993549105932f6a8265b3111220b24f3e75ecc5496044164df58a0b86292c0882c9beb18470452581105936de326e08a4b0220b25facb75525056044164bf58ebaa4a0ac0882c9fcb0d75494158110593fd42e4a9282b0220b249fe371a76552044164feb06baa4a8a40882c9f761935495148110593fcc2c6a92a290220b27f6835d525052044164ff90baaa4a0a40882c905fcdb71eaa6a5525920bfbb76635253aa4b25e8e355b76118058164ec5d5dceec2300b02c978b9d72d58460160592f553a45ab08c02c0b25eac744b56118058164ed1d5dcaac2300b02c9f83a779558460160593b55576c2444c02c0b27e2a9dd848898058164fd152ab0911300b02c97b31d12d58460150593f944ef11282b0220b27f88956225056044164 else 0x108000021840079081e42005c082031031880000000a1000002100284000018421000841a3d0e8003e000f00020f0c0730de1810717c302cc378584e3d91a31c47a3d0f8f70422b1e85c7a1e1e847a5e3d178f43e3d0d0f4343d0d0f4363dde10a87abc2130f678420ae8c5c4c3d91a0812a7080000008400453841a16080c020190801d50083aa010000101000042001080a020e9e84010100000e8f040026080173d082e3c1000c4204742d0a0b4182d3cf4505a08169e3c221086843f1617c583f1608000018f4200000a21000002e08c5c018269e8462e118b84f707a301f011058210170b07a7c217c5820ad0130a035f1614069e3c200580b85a3d0801a3d02c60840624068f40638211e8f40638211e8f70422060f420a1e8687a1060f4383d0c98495c9348a487c85482c79c7746e465462c60457447c45442c4043dc34c3242fc26c1dc1b418c16413c0ac01bff3f63ed3e43db3d8bcfbc03b0ba138b382372b69b60b57b4833f33632d32431b30bafc2ecadd2cdacb2c22bfabd2baab1aaf2acaa3aa129828f286283a81278275a6ca6a267a5ea5c25324a24123ea35a2ca2a227a25222a19a1720e20ba092001fd9f49f21e91d99d09c11b81a899f99018717e17b97917697416b16896616395a95815595314a13a9319289129030f38e40db0cb8bc0ac89d09409188f07287005a04403483202902681d814812009000437f36dc7aa9a05496486feee57653b40a92c925fdd7b31526a4525920ff9b6e0174cac44b2517f75ebbaa952641648afeeb9972ac44c82c945fdd7aeda9549805934afb52e394aa9300b269dd6a5c12955260164b6b6eb94ad12a4c02c96f65d1295a2549805920ff9b8cbb7429300b241ff371926e85260164c6dee3a825d444c02c9b39d8470ca5645805924bfbae65444c8b00b241ff371986ceaa5c16483fe6e32ad9d54b82c907fcdc649b3aa9705930bfb90b8974caae0b241ff36dc8aa9955c16483ff6e996d432ab82c907fcdb705a8655705930bf996b8b50caae0b241ff36dc8aa9935c16483fe6db9155324b82c9277dd5b31a8649705920ffdba65b50c92e0b261df32cc56a1925c16483fe6db82d4324b82c9277dd5b31a864570592b97baf5db08a92c0b2553f75ebb64d52581648e7eeb9972ac44b02c934fdd7b315264560592797baf662a4a0ac0b247bb74acc6dd3158164ac7eec0eadba62b02c95cedd21d5b74c560592b9f3a03ab6e98a)
def minel9 : Packing := (149,6,7,0,0,12,0,mined9)
def mined10 (i : Nat) : Nat := (if i<8 then (if i<4 then (if i<2 then (if i<1 then 0xc77cba9559348164a7ecca6555248164e76da995622481648dfdc72e93148164fec5634c52148164fd69755497048164fde1714857048164ff49535493048164ffc131485304816487fccb69d934416487fccb69d9244164e5eda99de2244164e76da99562244164fc7a779556044164bef1c11496044164fcea778896044164fe6a558896044164feb1725056044164feb1525056044164feb0525056044164feb2225056044164ff61525452044164dfb2bb5052044164fdb2775052044164ff32555052044164ffa1525052044164ffa222505204416497f8cb61d9580164f1fa889dd958016497f8cb6625580164f37a886565580164f57a776565580164b778cb6625580164f579989de5580164f97a889de5580164fd3a77955848016497f8cb61d938016497f8cb9559380164d778cb9559380164f57a779559380164dcfabb9dd6380164de7abb9556380164fc7a779556380164bedacc60d6380164fcda7760d6380164fe5a5560d638016497f8cb61d9280164f1fa889dd928016497f8cb9559280164d778cb9559280164f37a889559280164f57a77955928016497f8cb65d828016497f8cb655828016497f8cb64d8280164fad98358d82801649df9c7aed5280164d5f9b92dd52801649df8cb9dd5280164ded9b68cc528016497f8cb662228016497f8cb656228016497f8cb64e2280164f3ea8864a2280164f5ea7764a2280164f76a5564a2280164b7e8cb6622280164f3ea8865e2280164f5e9989de2280164f9ea889de2280164b7e8cb6562280164f3ea886562280164f5ea776562280164f769959562280164f769989562280164fb6a889562280164fd6a779562280164fdaa776122280164ff2a556122280164b7e8cb64e2280164f5ea7764e2280164f76a5564e2280164beeacc58e2280164fcea7758e2280164fe6a5558e2280164fec98358e2280164fdca778ce2280164ff4a558ce2280164f1fa889dd9180164f37a889559180164f57a779559180164f3ea888899180164f5ea778899180164f76a558899180164a7f8ca6e55180164f9ba889dd4180164fb3a889554180164fd3a779554180164fbaa888894180164fdaa778894180164ff2a558894180164dedabb58d3180164fcda7758d3180164fe5a5558d3180164fec9638893180164fed1634c52180164f5f27764e1180164fcf27758e1180164fbd2888ce1180164fdd2778ce1180164f5f27764a1180164f7e19288a1180164f7e19888a1180164fbe28888a1180164f7e19788a1180164fde27788a1180164f7e19588a1180164ff625588a1180164ffa18488a1180164f7e19388a1180164fee16388a1180164ffc23388a1180164dababb6118058164f8ba776118058164fa3a556118058164faa9848898058164fcb2775056044164fea2225056044164 else 0xadedc72ea2260164a7eccb6a62260164e5eda99de2260164a7ecca6562260164e76da995622601648dfdc72e931601648f7dc5aeda85c16487fdc52e9985c16487fdc12e9985c164c7f6112e9985c16487fdc82e9955c16487fdc12e9955c164c5fd712e9955c164c7f6112e9955c16487fccb6a1955c164c5fcba5d5955c164c77cba955955c1648f7ccb6a2555c164a77cca662555c16487fdc82e9935c164c3fe882e9935c16487fdc52e9935c16487fdc12e9935c164c7f6112e9935c164c77cba955935c16487fdc82e9925c16487fdc52e9925c16487fdc12e9925c164c7f6112e9925c16487fccb6a1925c164c77cba955925c164f47e776565558164ec7eaa9de5558164fc3e77955845816496fccb9559358164d67ccb9559358164f47e7795593581649cfdc7aed52581649cfccb9dd5258164eceeaa9de2258164f4ee776562258164f66d959562258164ee6eaa9562258164fc6e779562258164fcae776122258164fe2e556122258164f4ee7764e2258164f66e5564e2258164f47e779559158164f4ee778899158164f66e558899158164fcae778894158164fe2e558894158164be78c56dd8058164dcfabb9dd8058164bcf9c72d58058164bed9c32d58058164bee9c22d58058164bef1c12d58058164de7abb9558058164fc7a779558058164fababb6118058164fab9b76118058164fab9b56118058164fab8b56118058164fab9756118058164faba556118058164fab9846c98058164fab9842c98058164fab9845c98058164fab9845498058164baf9c81498058164fab9841498058164fab9848898058164deeabb8898058164fcea778898058164fe6a55889805816487fccb65eaa5416487fccbaa9985416487fccb661a75416497f8cb5c1955416487fccbaa9935416487fccb69d935416487fccbaa9925416487fccb6a1925416487fccb69d925416487fccb6a62254164a7eccb6a62254164e5eda99de2254164e76da99562254164bf71c12d5805416497f8cb6558054164f379956158054164dbbabb6118054164ebbaaa6118054164f9ba776118054164fb38b56118054164fb3a556118054164fba984889805416487fccb6a6224c164a7eccb6a6224c164e5eda99de224c164ecee7769a224c164e76da9956224c164ee6da6956224c164fbd1814c5804c16487fdc52e9984816487fccbaa9984816487fdc82e9974816487fccbaa9974816487fccb6a197481648dfdc7aeda54816487fccb661a548164c5fdb92dda5481648dfccb9dda54816487fdc82e9954816487fccbaa9954816487fccb6a1954816487fccb6a65548164a77cca6565548164a77ccb6a65548164a77cca6625548164e57da99de554816487fdc82e99348164c3fe882e9934816487fdc52e9934816487fccbaa9934816487fccb6959348164) else (if i<3 then 0xcff9a36c05244164d7f9936c05244164def9636c052441648ffecc6e93244164def9606e132441648ffdcb6a132441648ffdcb69532441648ffccb6a2224416497fccb66222441648ffccb696224416497fccb656224416497fccb64e2244164befacc5cd6044164befacc54d6044164bef9c754d6044164fed97354d6044164fcf9735c96044164befacc5496044164bef9c75496044164fcf8c75496044164fe79755496044164fe79535496044164fee9725496044164bef9c31496044164befacc4c96044164bef9c74c96044164bef9c54c96044164fed9734c96044164e7f99869d2044164bff1c12d52044164e7f9a76552044164efb9a76112044164e7f9a764d2044164eef9a758d2044164f7e9985492044164fde8c75492044164f7e9955492044164ff69755492044164ffa9845492044164efe9a35492044164f7e9935492044164fee9635492044164ff69535492044164f7f1935452044164fef1635452044164ffe1c25452044164f7f1925452044164ffe1525452044164ffb1b85052044164ffb1b75052044164ffb1875052044164ffb1b55052044164ffb1855052044164ffb1755052044164ffb2555052044164ffb1825052044164ffb1525052044164a5fdc5aaa776496487fdcbaa8526496487fccb696226496487fccb68e2264964a5fdc7aa9a954964a5fecc6a4a754964c5fdc92ea7754964c5fcba6a67754964977dc5aed9254964a5fdc7aa99254964a5fcca9dd9254964e76e55889a914964c5fe772e99588964c7edc22e9958896487fdc12e9958896487fdc02e995889648dfdc72ea5588964d5edb59dd9288964d5edb39dd9288964d5edb09dd928896497eccb9559288964a7ecca6555288964d76db99555288964d76e556e4a588964c7edba2e9958896497eecc2e99588964d5ee772e99588964c7eda52e9958896497edc12e9958896497edc02e99588964d5eebb9dd95889649dedc72ea5588964b76cca6565588964f56e776565588964bd6dc72ea5588964a77dc82ea5564164e57e772ea5564164a77dc32ea5564164a77dc22ea5564164e57eaa9de556416495fdc7aed5264164c5fdba2dd526416495fccb9dd5264164a7edc82ea2264164e5ee772ea2264164a7edc52ea2264164a7edc32ea2264164e5eeaa9de2264164e76cca9562264164e76cba9562264164e76eaa9562264164f56e779562264164cef9606c6aa60164c77da92d5a760164c5fda96dca560164c7eda96c8a560164c7f5a96c4a56016487fdc22e9956016487fccbaa99560164c5fcba9dd956016487fccb6a65560164a77cca6565560164a77ccb6a65560164e57da99de556016487fdc52e9926016487fccbaa99260164c5fcba9dd9260164c77cba95592601648dfdc72ea226016487fccb6a62260164a7ecca64a2260164 else 0xdf6db55493148164fecd635493148164cff4ba6053148164efd5a36053148164efd5a34c52148164fed5634c52148164ffc5324c52148164d7ed986d52148164ddecc76d52148164dfadb56112148164d7edb564d2148164deedb558d2148164f7e5985c52148164fde5a75c52148164fde5875c52148164f7e5955c52148164ffa5845c52148164f7e5935c52148164fee5635c52148164bfe5c74c52148164ffc5a34c52148164ffe1c04c52148164e7f9986957048164e7f9a56557048164f5f9756557048164f7e9526557048164f5f9716557048164f5f9985d57048164efb9a56117048164fdb9756117048164e7f9a564d7048164f5f97564d7048164eef9a558d7048164fcf97558d7048164f7e9985497048164ffa9845497048164f7e9935497048164fee9635497048164ff69535497048164e7f9a56457048164f5f9756457048164f7e9526457048164f5f9985c57048164fdb9845c57048164f5f9935c57048164fcf9635c57048164ef79a55457048164ff69525457048164efb9a55057048164fdb9755057048164ffa9525057048164fed9634c57048164f7e9984857048164bfe9c54857048164f7e9954857048164fde9754857048164ffa9844857048164f7e9934857048164fde9734857048164fee9634857048164ffe1314857048164bef9c62953048164bfd9c32953048164efe9a85493048164fde8c75493048164ff69755493048164ffc9535493048164ebf9a86053048164aff8ca5453048164ff69525453048164efd9a84c53048164bfd9c54c53048164ffc9524c53048164ffd1814c53048164ffd1314853048164dfe9b74853048164bfe9c54853048164ffc9534853048164ffe17148530481648ffdc3aeda744164afecc26dda344164a7fecc69d9344164c7fccb69d93441648ffecc6e98344164def9606e17344164aefecc69d63441648ffdc8aeda2441648ffdc5aeda2441648ffdc3aeda244164c7febb661a244164c7febb65da2441648ffccb61da244164cfbebb611a244164c7febb64da244164cefebb58da244164a7fecc69d9244164c7fccb69d9244164a7fecc69592441648ffecc6e98244164c7fda96e17244164def9606e17244164c7fdba6617244164c7fdba6557244164cfbdba6117244164c7fdba64d7244164cefdba58d72441649dfdc7aed52441648ffecc6e95244164cdfcc76e95244164c7fd976e95244164c7febb6a55244164c7fda96dd5244164cdfdba2dd5244164d5fdb92dd5244164e5fda92dd5244164c7fdba64d5244164cefdba58d5244164e7eda95c952441648ffecc6e85244164c7fda96cc5244164dfb5416cc52441648ffdcb68c5244164cfddb368c5244164c7fdba64c5244164cefdba58c5244164cff9a86c05244164d7f9986c05244164dfb9846c05244164)) else (if i<6 then (if i<5 then 0xafbecc69d8448164afbecc6958448164edbcc76958448164afbdca5d58448164afbcca9558448164aefdc6295a3481648ffdc8aeda3481648ffdc5aeda3481648ffdc1aeda3481648ffccb61da348164aefdc62d5a3481648ffccb955a348164a7fdc8aa99348164a7fdc7aa99348164a7fdc5aa99348164a7fdc1aa9934816497fccb6a19348164a7fecc69d934816497fccb61d934816497fccb6959348164a7fecc6959348164c7fccb6959348164e5fcc76959348164c7fcba6159348164a7fdca5d5934816497fccb9559348164a7fcca9559348164c7fcba95593481649fedc2aed73481648ffdc82e973481648ffdc52e973481648ffdc12e97348164cdfcba61d7348164aefdc82e96348164aefdc72e96348164aefdc52e96348164eedd832e96348164aefdc8aa96348164aefdc7aa96348164aefdc5aa96348164aefdc1aa96348164aefecc69d6348164aefcca61d6348164aefdca2d56348164beedc22d56348164aefecc6956348164ecfcc76956348164aefcca6156348164aefdca5d56348164aefcca95563481648ffecc6e95348164cdfcc76e953481648ffdc12e9534816497fccb61d924816497fccb9559248164f5f9755c192481649dfdc7aed52481648ffdcb6a15248164bdedc7aed5248164cfeccb6a15248164ef6cc56a15248164ddedb82dd5248164ededa82dd5248164f5ed982dd5248164e7ed9869d5248164e7eda76555248164ef6da85d55248164f76d985d55248164fd6d875d55248164fdacb76115248164efada76115248164ff2d756115248164f5ecb764d5248164e7eda764d5248164f76d7564d52481649feccb5cd5248164fcecb758d5248164eeeda758d5248164fe6d7558d5248164fd6cb754d5248164ef6da754d5248164ddecb76c55248164aefdc6295a148164a7fecc6a19148164a7fdca61d9148164a7fecc6959148164e5fcc76959148164a7fdca6159148164a7fdca5d59148164e7eda85499148164f5ecc75499148164e7eda75499148164f76d755499148164aff5c1aa98148164e5fd9869d7148164e5fda76557148164edbda76117148164e5fda764d7148164ecfda758d7148164c7fd952e951481648ffdc32e951481648ffccbaa951481648ffccb69d51481648ffccb68d5148164c7fcba64d5148164cefcba58d5148164fd6cc75495148164ef6da75495148164f76d935495148164fe6d635495148164afbecc6a14148164afbecc69d4148164afbdca61d4148164afbecc6954148164edbcc76954148164afbdca6154148164afbdca5d54148164efada85494148164fdacc75494148164efada75494148164ff2d7554941481648ffdc82e931481648ffdc52e93148164eedd636a13148164eedeaa58d3148164eedda758d3148164eedda558d3148164cfecba5493148164 else 0xf3f9856458054164fbb9845c58054164fbb9855058054164fbb9844858054164d7f9b864d7054164def9b858d7054164d7f9b86497054164f5f9716497054164d7f9b86457054164f5f9985c57054164fdb9845c57054164f5f9935c57054164fcf9635c57054164dfb9b85057054164fed9634c570541648ffdc1aeda74c1649dfdc7aed524c164c7febb6a5524c164c7fda96dd524c164cdfdba2dd524c164e5fda92dd524c164cefebb699524c164cefdb7699524c164ecfcb7699524c164e7eda95c9524c164eeeda65c9524c1648ffecc6e8524c164c7fd976e8524c164c7fd926e8524c164c7fd916e8524c164cfbd416e8524c164d7f9986c0524c164dfb9846c0524c164d7f9916c0524c164dfb9416c0524c164bf78c56dd804c164bdf9c72d5804c164bfd9c32d5804c164bfe9c22d5804c164bff1c12d5804c1649ff9cb149804c164aff9ca149804c164bbf9c8149804c164bfd9c3149804c1649ff8cb889804c164ffd131485804c164c7fd986ceaa48164c7fd976ceaa48164c7fd956ceaa48164cfbd846ceaa48164c7fdc9aeda8481648ffdc5aeda8481648ffdc1aeda848164af7cc56dda848164aefdc62d5a848164eedd6360da848164a7fdc7aa99848164a7fdc5aa99848164a7fdc1aa998481649fedc2aeda7481648ffdc8aeda7481648ffdc3aeda7481648ffdc1aeda748164c7febb661a748164a7fdc8aa99748164a7fdc1aa9974816497fccb6a19748164a7fecc6a19748164c7fccb6a19748164a7fdc16a19748164e3fd816a197481648ffdcaaed87481648ffdc52e987481648ffdc32e987481648ffdc12e987481648ffccbaa9874816497fccb6a587481649dfdc7aeda54816497fccb661a548164adfdc7aeda548164c7fdc9aeda5481648ffdc8aeda548164cdfdc7aeda5481648ffdc3aeda5481648ffdc1aeda548164a7fccb661a548164c7febb661a548164cdfcb76dda548164cdfebb2dda548164cdfdb82dda548164e5fd982dda5481648ffccb61da548164cdfcb76cda548164cdfcb76c5a5481648ffdca6e0a548164cefdb66a0a548164c7fda96cca548164a7fdc8aa99548164a7fdc7aa99548164a7fdc1aa9954816497fccb6a19548164a7fecc6a19548164c7fccb6a19548164a7fdc16a19548164e3fd816a19548164a7fecc69d954816497fccb61d9548164a7fdca61d9548164a7fcca61d95481648ffecc6e98548164cdfcc76e985481648ffdc32e985481648ffdc12e98548164a7fcca6e58548164a7fcca6558548164c7fda96e17548164c7fdba66175481648ffdc82ea55481648ffdc32ea55481648ffdc12ea55481648ffccbaaa55481648ffccb6a2554816497fccb6625548164a7fcca6625548164c7fcba6625548164afbdc7aa98448164afbdc5aa98448164afbdc1aa98448164) else (if i<7 then 0xfcbcb76115258164fe3d756115258164dcfcb76cd5258164d6febb64d5258164d6fdb764d5258164f4fcb764d5258164f67d7564d52581649efccb5cd5258164fead845c95258164f6ed935c95258164fced735c95258164dcfcb76c552581649efecc6e05258164debdc46e05258164debd846e05258164d6fd936e05258164d6fd916e05258164def9806e052581649efecc6cc5258164d6fdc96cc5258164d6fd936cc5258164d6fd916cc5258164debd416cc5258164debd846c45258164d6fd936c452581649efccb9562258164b6fecc5499158164b6fdc75499158164f4fcc75499158164f67d755499158164f6ed725499158164fced725497158164bebecc5494158164bebdc75494158164fcbcc75494158164fead725494158164beecc26dd31581649efecc6dd3158164dcfc756dd3158164deecc26dd3158164dcfdb75c931581649efdcb1493158164beddc31493158164bef5c11493158164bef9c32d58058164bef9c22d58058164befacc5cd8058164fcf9b75cd8058164bef9c52c98058164bef9c32c98058164fcf9735c98058164befacc5498058164bef9c75498058164fcf8c75498058164fe78b55498058164fe79755498058164fee9725498058164bef9c31498058164c7fdc9aeda8541648ffdc2aeda8541648ffdc1aeda854164eedd6360da854164c7fdb92c9a8541649f7dc5aeda75416497fccb661a7541648ffdc8aeda7541648ffdc3aeda7541648ffdc1aeda754164a7fccb661a754164c7febb661a7541648ffdcaaed87541648ffccbaa9875416497fccb6a5875416497fccb61d9554164f775515c59554164f5f9715c19554164f779515c19554164f779706558554164afbecc69d845416497fccb6a1935416497fccb69d9354164a7fecc69d9354164c7fccb69d935416497fccb61d9354164aefdc82e96354164aefdc72e96354164eedd832e96354164aefdc22e96354164aefecc69d6354164aefdca2c963541649dfdc7aeda2541648ffccb6a1a25416497fccb661a25416497fccb64da25416497fccb6a19254164a7fecc6a19254164c7fccb6a19254164a7fdc16a1925416497fccb69d9254164a7fecc69d9254164c7fccb69d925416497fccb61d9254164a7fdca61d92541649dfdc7aed525416497fccb6a622541648ffccb6a2225416497fccb662225416497fccb656225416497fccb64e22541649ff9c0aeda154164a7fecc6a19154164a7fecc69d9154164a7fdca61d9154164afbecc6a14154164afbecc69d4154164afbdca61d4154164eedd636a13154164eedeaa58d3154164eedda758d3154164d7f9b76558054164fbb9a76118054164fbb9842c98054164fbb9846898054164f3f9856498054164fbb9845c98054164fbb9845498054164fbb9848898054164fbb9846858054164 else 0x8ffdc52ea22601648ffdc12ea2260164cfbd412ea22601648ffccbaaa226016497fccb6a6226016497fccb6562260164a7fcca6562260164af7cc569da160164adfdc7295a160164afddc3295a160164afedc2295a160164aff5c1295a160164a7fdc7aa99160164a7fdc5aa99160164a7fdc2aa99160164b77cc569d9160164b5fdc72959160164b7ddc32959160164b7edc22959160164b7f5c12959160164a7fcca9559160164a7fcca5499160164a7fdca1499160164b3fdc81499160164b7f9c01499160164a7fcca88991601648ffdc22e931601648ffecc6e2aa5c164cfbd416e2aa5c164cfbd416d6aa5c1648ffdc86ceaa5c164c7fd986ceaa5c1648ffdc56ceaa5c164c7fd956ceaa5c164cfbd846ceaa5c164c7fd926ceaa5c164cfbd416ceaa5c1648ffdc36caaa5c164cfbd416caaa5c1648ffdc86c6aa5c1648ffdc26c6aa5c1648ffdcb546aa5c1648ffdc8aeda85c1648ffdc1aeda85c164e5fd71661a85c164edbd71611a85c164eedd6360da85c164a7fdc5aa9985c164a7fdc2aa9985c164a7fdc1aa9985c16497fccb661a55c164a7fdc8aa9955c164a7fdc2aa9955c164a7fdc1aa9955c16497fccb6a1955c164a7fecc6a1955c164c7fccb6a1955c164e77cc56a1955c164a7fdc16a1955c164e5fd716a1955c164a7fcca549955c16497fccb685955c164a7fcca545955c164e7f5a1545955c164f5f571545955c164c7fd852e9935c164a7fdc8aa9935c164a7fdc5aa9935c164a7fdc2aa9935c164a7fdc1aa9935c16497fccb6a1935c16497fccb695935c164a7fdc8aa9925c164a7fdc5aa9925c164a7fdc1aa9925c16497fccb6a1925c164a7fecc6a1925c164c7fccb6a1925c164e77cc56a1925c164a7fdc16a1925c164e5fd716a1925c16497fccb695925c164e5fda85d5925c164a7fcca549925c164f57d75549925c16497fccb685925c1648ffdc82e9525c1648ffdc32e9525c1648ffdc12e9525c164cfbd412e9525c164c7fcba661525c164f57d985d5525c164c7fcba64d525c164f57d7564d525c16497fccb661a15c16497fccb64da15c164a7fecc6a1915c164e77cc56a1915c164e5fda85d5915c164f57d75549915c1648ffccaaed315c1648ffdc82e9315c1648ffdc52e9315c1648ffdc22e9315c1648ffdcbaa9315c164eedd636a1315c164bdecc26dd315c1649efdc5aed87581649efdc3aed87581649efdc2aed87581649efdc8aed73581649efdc5aed73581649efdc2aed73581649efdc1aed7358164bcfdc7aed52581649efdc8aed52581649efdc7aed5258164dcfdc7aed52581649efdc3aed52581649efdc1aed52581649efecc6dd5258164dcfebb2dd5258164dcfdb82dd52581649efccb61d5258164f6ed726555258164fc7d875d55258164debebb6115258164debdb76115258164))) else (if i<12 then (if i<10 then (if i<9 then 0x3c303a60389036c0343032602fd02d4029f016e0145010400c3008200410000a7fdc5aa9726496497fecc6cc526496497fcca6cc5264964c7feaa6cc5264964d7dca36cc5264964c7fda06cc5264964d7dd306cc526496497fdcb60c5264964d3fdb860c5264964d7ddb360c5264964c7feaa6c05264964c7fda86c05264964c7fda36c05264964d6fd636c05264964d7f9306c05264964d7ed52aed955c964a7fcca5c1a954964a7fdc0aa99254964adfdc7aa9a054964cdfebb29da0549648ffdcb68da0549648ffdcb685a054964a7fecc549a914964c7febb2e99588964c7fdb72e99588964a7fdc12e99588964c7fdb12e99588964a7fdc02e99588964c7fdb02e99588964e6fd602e99588964c7fd752e99588964c7fdc02e99588964c7fd702e99588964c7fd302e99588964c7fcba9559588964b5fdc7aed526416497fdc8aed526416497fdc7aed5264164d5fdc7aed526416497fdc3aed526416497fdc1aed5264164c7febbaa9526416497fecc6dd5264164c7feaa6dd5264164d5febb2dd5264164e5feaa2dd5264164d5fdb82dd5264164e77eaa5d55264164d5fcb76cd5264164e7eeaa5c95264164d5fcb76c5526416497fecc6cc5264164c7feaa6cc5264164d6fdc66cc5264164d6fd636cc526416497fccb9562264164cfbd416deaa60164cfbd416d6aa60164cfbd416caaa60164af7dc52caaa60164c7fd936c6aa60164cefd636c6aa60164c7fd926c6aa601649f7dc5aeda7601649ff9c0aeda760164cf7eaa2d5a760164bd7dc51c9a760164bdf5c11c9a760164c7fda96c8a560164d7edc96c8a560164d7f5c96c4a560164dbf5c86c4a560164dfb5c46c4a560164ddbdb7504a560164df9db3504a560164dfadb2504a560164dfb5b1504a56016497fccb69d9560164c7fd972ea55601648ffdc22ea55601648ffdc12ea5560164cfbd412ea55601648ffccbaaa55601648ffccb69da260164af7cc569da260164adfdc7295a260164aff5c1295a26016497fccb655a260164c7fda96d4a260164c7fda96c4a260164def9606c4a260164a7fdc7aa99260164a7fdc5aa9926016497fccb69d9260164b77cc569d926016497fccb6959260164b5fdc72959260164b7edc22959260164b7f5c12959260164a7fcca9559260164c7fcba5c99260164c7fcba1499260164b7f9c01499260164c7fcba8899260164a7fcca65572601649dfdc7aed52601648ffdc12e95260164cfbd412e95260164af7dc5aa95260164c7febb6a55260164c7fda96dd5260164cdfdba2dd5260164e5fda92dd5260164e77da92955260164bd7dc72955260164bf75c12955260164e77da95d55260164ef6ca56895260164c7fcba6495260164e7eda95c952601648ffecc6e85260164c7fd976e85260164c7fd926e85260164c7fd972ea2260164 else 0x42a34292428142644247422a420d41f041df41c241a5417c415f412a40e940c040af40864069404c403b401e40013ff03fdf3fc23fb13f943f8f3f723f613f503f3f3f3a3f293f003ee33ec63eb53e8c3e633e463e293e243dfb3dde3dc13db03d873d5e3d593d3c3d2b3d0e3ce53cbc3c9f3c8e3c7d3c543c373c0e3be53bbc3b933b763b593b303b2b3b023ad93abc3a933a763a4d3a2439fb39ea39d939c839ab399a3971396039433932391538f838db38ca38ad38843867383e382d381037f337d637d137a8377f37563739371c36ff36e236c5369c367f3662364536283623360635e935cc35af359e358d35643553352a350d34e434c734aa348d3470345334363419340833df33ce33b13394335f33423325330832df32c232b13294327732663249322c320331e631bd31a0318331663149312c310f30e630c930a03077305a303d302030032fda2fbd2fa02f6b2f422f012ed82ec72eaa2e8d2e702e5f2e422e192dfc2dc72daa2d812d4c2d172ce22cad2c9c2c732c562c2d2c042bcf2b9a2b652b242aef2aae2a792a442a0329f229a52958293b291e28f528e428d328aa28812870286b285a2849282c280327da27c927c427b327a227912780277b277627652760274f273e2721271c270b2706270126fc26eb26e626c926b826b3268a2661265c263f263a262926182613260e2609260425ff25ee25c5259c2573254a2521250424db24be24952484247f24562421241023ff23ca2389237823672356235123282323230622c5229c22732262222d21f821cf21be214121242113210220f120c820b7208e205920482037200e1fe51fbc1fab1f3a1f291f181f071ef61ecd1ebc1eab1e8e1e7d1e6c1e5b1e4a1e391e281e171e061df51de41dd31dc21db11dac1da71d721d6d1d441d1b1cf21cc91cc41cb31c8a1c311be41b971b4a1afd1ab01a6f1a1619b11970192318be18b918a818971856181517a4179f175e16f916b8164715d6158915781573156e155d154c152f151e150d14fc14f714e614d514b814a714a21491148c147b142e140513d013a7137212f512c0125b1232121511ec11b7114611291118110710f610e510bc10ab107610410fdc0fcb0fc60fb50f800f4b0f0a0ed50e940e530dfa0dad0da80da30d920d5d0d4c0d3b0ce20c7d0c180bb30b4e0b250afc0ad30a860a5d0a400a2f0a1e0a0d09fc09eb09da09c909b8099b098a09790968094b092e091d090008e308c608a90898088708760865085408370826081507f807e707d607c507b407a3079207810770075f074e073d072c071b070a06f906e806d706c606b506a40693068206710660064f063e0621061005ff05e205d105c005af059e058d057c056b055a053d052c051b050a04f904e804d704ae049104740457043a04290418040703f603e503d4) else (if i<11 then 0x7b0b7aee7ad17ab47a977a7a7a5d7a4c7a2f7a1279f579d879bb79aa7999797c795f7942791978fc78df78b678817858782f780677dd77c077a3778677697740771776fa76d176a8768b766e76517628760b75ee75d175b47597758675697558753b752a7519750874eb74ce74b174947477745a743d7420740373da73b173947377735a733d732c730f72f272d572b872a7728a726d7250721b71fe71d571c471a7717e716d71507133711670f970dc70cb70ae7091707470577046703570186fef6fd26fb56f986f7b6f5e6f296f006ed76ea26e856e746e3f6e2e6e116df46dd76dba6d9d6d806d636d466d296d0c6cef6cba6c9d6c8c6c6f6c5e6c416c306c1f6c026be56bd46bc36bb26ba16b906b736b626b456b1c6aff6ae26ad16ac06aaf6a926a816a706a5f6a4e6a316a0869eb69ce69b169a06977694e692568fc68c7689e6881687068536836681967f067df67ce67bd67ac679b677e67616744673f672e6729671866fb66ea66c166b06693668266656648661f660e65e565bc65ab659a6571656065436532650964ec64cf64b264ad64906473645664456428640b63ee63d163b463af639263756358633b631e62f562d862af629e628162646247622a622561fc61df61ce61b161a0618f617e616161446127610a60ed60d060cb60ba609d6080607b605e604d603060135ff65fd95fc85fab5f825f655f485f2b5f1a5f095eec5ec35e9a5e715e545e375e265dfd5dec5ddb5dbe5dad5d9c5d735d625d455d285d0b5cee5cd15ca85c8b5c6e5c455c285bff5be25bb95b9c5b7f5b625b455b285b0b5afa5add5acc5abb5a9e5a815a585a3b5a1e59f559e459c759b65999597c595f59425925590858eb58ce58b158a0588f587258555838581b580a580557e857cb57ae579d5780576357465729570c56ef56d256b55698567b565256355618561355f655d955bc559355765559553c551f550254e554bc54ab548e5471545454375426540953ec53c353a65389536053435326530952ec52c352b252955278525b523e5239521c520b51ee51d151c051a3517a515d5140512350fa50d150b450a35086505d504050174ffa4fdd4fc04fa34f864f694f4c4f2f4f124f014ee44ec74e9e4e814e644e474e2a4e014de44dd34db64d994d7c4d5f4d424d254d084ceb4cda4cbd4c944c834c664c494c2c4c0f4bf24bc94ba04b834b5a4b314b084ad34aaa4a8d4a704a534a2a4a0149e449c749aa498d49704947492a490148d848bb489e488148644847481e480d47f047d347b6479947884777476647554750473f4722470546f446d746c646c1468c466f46524641462445fb45de45c145a44587456a454d45304513450244f144e044db44b244a14484446744564439441043f343d643ad43904367433e432d4310430b42fa42e942cc else 0x4210313031a1eb1e818811a38de2a10a0187a1c3d080980582183b0189404c02c10c1d80c4a02601600207c05401a03e08c0e69001f00582183b0189418002c0f80a80378601181cd00260160860ec062501300104402b02a01c04a03e01f483000980081f01500680f823039a41800041100bc0a8098c00e1003c582042102f06912400520029001024006200202604c200708285820616083191b10ff8b0b9f9e980401681b8607c08608004c400005a06f18300218200131004c18c0d00a80378601e40f807c161405c1adc31e7a401304403e00803ae1805107343810338278c31bc5840000b40de306004303c031200983182201781500683c80f818a40a00c459001f160e400580820000b40de36800812f0c02d0371018010c10009880c008807c0100740a20e7c308a8008180821ad87c038046402306522103e203b78b01606b79e940e035bcf416881ade2c043e7a842501cf16023f3d4212830005f0c01683481f41f1c18004c0a81a816a168c0061e84c5c16b4f40c4987a1c3d0c1e98fc39be141082d41f1e0f5f6c0f9f08c7e1ce0860f90ae30e60b401863f27b042074813d7db78e00c7d293d82103a400e06b0ab01d78b00d00ac1f20086084030690147b0423480a3d8211d1e81d011810c10c1f18c5e45c03060c7c302f160f0c07c583e2c1f160f8b07c583a7a1063e18170c07c583e2c1516d0e128b6870b478227b042293d821149ec10880038605e2c1e180f8b07c583e2c1146e18170c07860390c23e2e180f0c07c582a2c1e180f0c078603e2c1f160f8b07c583e2c1f160f8b07c583e2c1f160f8b07c583e2c1f160d9e86cf43e2c1f160f8b04c5ac38563c1b1e099e9108bc583e2c1f160f8b07c583e2c1f160f8b040774d45a6a1d350e9a874d43a6a1d35089ec10d8b0e0860f8504307c242143e108f81f0bc58363c1f160f8b07c583e2c1f160d8370c0811056842b5c30200cf1643e1c9b70c0a4d98610f86669e2cc423b0661f71e6212753b17d17e17b0f81349ceb83a85a86a871efb82b9cb9e39e9ee9ac2d18fde2a1f41f310e1f668f60861cc707a6a147b0430e6548083da3d8218732c4021eb1ea10a3994d420f61ce0860f8a90107b0e704307c5872f8712870186e486d386b68699867c865f8636861985fc85df85c285b18594856b854e8531851484eb84c284a58494848f847284618450844b843a841d840c83ef83d283b5838c836f83528335831882fb82de82c182a48287826a824d823c821f820e81f181d481b781a68189816c815b814a8121810480e780ca80ad80848067804a80157fe07fc37fa67f7d7f607f437f267f097eec7ecf7ea67e897e6c7e4f7e3e7e217df87dcf7db27d957d6c7d4f7d327d157cf87cdb7cbe7ca17c847c677c4a7c2d7c107bff7bd67bc57ba87b737b627b457b28)) else (if i<14 then (if i<13 then 0x8b07c5a0844039e2c2f16821101d040480744112843e2c3f160201010210f8b0fc58207a0ca2f3d03a100780088006802e032313d63d421190b81ee8f0c0f41bc40dc0602065024100600088030144402e019e2c340cb3d100600089030090400e00220003800880d0064400207c213d63d100084004202e07b67a3001081e8470120c0bbc58402e18c032302e01914610288800401c400207c202e01b13020150801c0b44098103d4c20241ce1040300644022068291100c93403a201e80c882100e84002018241740cb1e183980c8a208306ce7a208603a101b06209c78402e032213d63d421180c81e881400f4064603a0362001004100e80d88004010400204c2821044109ee1ec108e084110587a7a404234210443c5189ee1e8808c110586c05c2c3d3c2161ea1098f8f0f4f08462e018231113dc3d821241082201f0cc5c4f70f4f0a084b87a04278a385a081d00e08161168490d67a245a0a4358f0a06bc59084615be2c240481a42106e271ef8b080698f5cf46c7a8421aa04c440481af16421240d31ea10b8f1206b8f7c590849e2c131f51f71e1a4000e880700f8098603405e0dc333d00c03a00b219e80602d00590cf68f60849cc867a018f84074016533da3d821273218ba29d1ebe141094cf40ac0ea084867a0180164e6455583e00c00b05a2e8b0404c00411002c0741b4c0c000208805e05404c601302610348278b5641b813c609e1007080b8038348c1a40b813c600e103430401c2016074205c04d0311817056f9e8c118205020f0b0401c2a84100001c2000608018400401840f1608000f1608003c858400e100338278170d80819c13c60f16006103c58201e100000000d05d158841506e0cc420a830576210541b8303c0208c14c1d809860d20622a8042147118140188b2008849c47e2c1000802d0370c02c0e01e00c495001a80082206b031f9e900041100ab9c0098b9001f1608038419004424e23061f011881101e435b863cf4a0200b40dc301f05601d1b40041e40b40f81e090420d803e074443e82104a1b40074f404c02c0341e79641a40c407c119408e0ec2a8008630720020000b40de3680080802d0370e0841c41580748d001a80080401103c8c0401681b860ec0ae03a3680080980082381f01500681b02b00fa6a0034001e000e1e840f80341b87e2c1c00081571e8b8003c001a000b00078003c001a3d0d1e8680034001c000e000700020071e82c6398189000c78e60623063031c731831818e398c18f1c40c460c3d0c108318188e8f5e180f808c1620840c4f47a07c046f8b042062606363605831f821031341ebe143998fc1082c1a0f40f808df160840c4cc7a07c0460b08420626473bc5a364210632a1eb1e818811a10de2a399c18d0f6f081a416008d0851cd00f262fc7a0b0062543dbc5a3631f else 0x840c05842060208ef16103880c88c5c0c05e2c1f160a108328809404840100a2200801210328400dc060201d026179e80c880c0267a0f220080431004014880300144101e2c203d06f1012032880140e8402e0022233079178b0060028c004020402e0a2201198288bc58a08407a032203d0c206e18128328803007440320da2001008101700c88004020418405c032302e0837837080b806440ca048201d02610170405c004567a03220c66210191b9e80c880040b8402e07b6e03b3d019101700c880f4064567a0602702034025183b0411c10c401800a2063008100b8008800da07e2282080b800880041dc40da1008028100b86300c8fcf406440ca04a200c03a10140046b80c0220bc0a072660882001083703c880c0094070601803a20170c6019183701808004020404e0102017008110469e8836c1b84411a7a2017d3d100be9e8b4f4207ba7a207906e101869e80e0c1e4194406004a203a026100b812880c3c58094606004a20750804021880200a4401800a20010081007800880040204002010200f0011017040040b840116e0050300108008040803c020404e0102080f16101e83c880f43081b8601810c0743434f16101ee108378c07c91c0ec642e07ba3c353da1751e421201d81e8128c13c094407a04a220c026110b8328120c85c194094607a0482280024110b8120b4f4090442e04a203d08e024190b8128831805c0647e7a033e2c300c03a1004027880a40a842a409e202e01b101e86100c8f8603e7a0362621f16134078b0929fc585c3018a70a5387c5820f160d0c59e8929ecf4567a102de18125384144210de2c1ac4e18b1e1253d8f0ac78344363c20a7f160d61d4078b080300744006002203e06d1001800880040b8407c092200103e115387860254e1069e86deb80e208208e9042482b3d12410520ac78406c0180463025065100e80c8835805c0c4606804a2008036023181b0128118fc583e2c1ac2038f04098207404c22a7082026181304098258404c208202611538130b060098454e04c2d35081e83c880f41b8447a84202a301503a101191ec1080a900541680fa08408ca869e2c1ac3f160d4000aa108fc580d84104074241b081f110880e506c51001e180a4059e89200290163c2002d20d8bc58208e173d081c78203818c0b4301c41b12430328a308298408e450331704702a182381509168128404c2821b3d198bd9e8930a084462e18214c2b1e1a6918fd8f0c0842e7a24210a10b8f09087c58358607d042984383e00d14108616830b462ee7a300d85a102d18fb8f0f11bc58358688de2c1ac38214c2031181d0188a0840c4467b9840423042378b06b0c11e0e50846843e2c283942173d1c1ca10890843181686072842e3c30c6421f16180e040703e2c1c21f16178b040801b80bc7e2c1f1602117) else (if i<15 then 0x5c0e9c08602e002200100710038300008c01801c8849c480f3a7a0323079d3d030183ce9e8180c1e74f40c07a7a060200303e1001814880f812458430c60623c2106303118318188b08418c0c478420c606230030281036831880040f85800062042300807110018038801c050402e07a203d70210160403c0f4401e100f03d10078417c200e103d702100381e880f5c08400607a200303d10018188805c0f4400600a2482ca71241653d9e8ccf729c1e4602e0522007046100180288004084402e1007046103b0188808400440020502d3d0800e9e881b40fc450554e202d03402a2d22000810880ac0bc1b4654e104aaa710238300140c03c201e0522007046100283a880040844002042200708038148800c0144086042200700112108410c20da47e2448aa728218218108a148a9c408e09e238604f1021810880f7cf43481e4807a184068303d0c203a181d41a381469100b41e0530c102d0344d204c22c30400408440020422003001161f0220b000a9c58000942003034101e8118805c0f4400e028200303d150ba9ed53a109045308440541117e001700040f78005c001e00081bf000870b80040d21e000f00078003c001019e001700058f7800422fc000b035a7a0014c37000a8f4347a1a3d0ae151e8b80034001a000d000570a8004069c0038a39a763d14d3b000a69f8005c001117116e00183c8aef000c5741e58f462ba22ec00303e117031600231e8ae83c8c0fb8004c0019866001006b00080c40e8406222ec7a300d0f000700038001c0009e160008f0b00040b5c00200c10407841c3603a100e858d261b860603a1186e18100e840c40e840620742e3d234c711f1e848f70f60847c7b04271c3e3d0831870f5084e38787a11d5c3d161e878f6f09084787a7842c3d3c2161e91a08007a036201d031119e91089c382101e2c20010211037837080f4194403a0622000b800880f4064402e032202b0011015800889685210bc754e85022a74285021c9e8405f4f44002042200102110078008800560500023c21d1e168f054f50845a3c1d1e0e8f070bc064407a0322001021100081088004084400e0022001e04004084400e00220015800880f020dd85e2001007100b80d8800401c567a10010071040015f8b0c00c0044006002200103e1018840c42466062253d8824211c9eb17c108e4f520a084694f0ce233d02f158304cf40bef08694e133d099ede10ac183056102b8214a718b98529c0c4405e67a2b5b4a71253d8f0a50929c429009f94e382f4a7142d6538a16b29dcf470b594e205aca771e1a5381888cf408729c60740622e3de181000803880041544c7a036200702d150b0523a858542c19c20ce130b0805c064404b05e0b0302501b101f00e880e80f80c4710c107973d1443040c40e858420322c2103010318180b else 0x45007103281e08070200e01e2034081a00a08600094400e0c2206501210308340388c000004400204a20010081009307086182d4e00e294202a04f18008150801c0b84a2e00e200105003d180081e8610c05c01c400c1000180589c60205e1038c05b1413c4d0c1007044100d8078801801c438400e05a300103e1022027880b401c4002024200100b10168008800401c400e00226170071003b0b8801d8f8530c1007a3e14d38401c0b8407c070200f001100886618044400200e20540816043200f9c0870c60022003005101eb8f0800c0145e7a0f2032308007913108008870bcf41e41609e7a3840f20b0400702d10038318988418c0c46062c4226210311510818881e40c454420622a21031101083c8180c05c0a0400e07a200303d10160405c004407a0f20323d3ddc20791e9e83c8b4f41e440420f2060300102d100080488065cf4400e086200702910008108a18c10c40020422c2106310038318b08418c400e0502d3d08030388108ca18200200e2007045221271271e8400c0f440dae042086dc2100080388004154400ec7a200702d16e110b8874bcf45e7a1052986131083c880b401c534e84e2017001100084004200e088201703d100581d08))))
def minel10 : Packing := (1148,5,7,0,0,16,0,mined10)
def mined11 (i : Nat) : Nat := (if i<13 then (if i<6 then (if i<3 then (if i<1 then 0x48600593bfccc243002c9efea212180164bff36e90c00b277f99748600593efd3ba43002c97fe6d52180164eff32a90c00b27f7a5548600593fdcc2243002c97fe6cd2180164eff32690c00b27ef96348600593fed19a43002c9dfe6492180164ffd44490c00b27ff17148600593ff898a43002c9ffc60e1180164ffe2e708c00b27ff18284600593ff8b9423002c9ffc54a1180164ffe0a508c00b27ff13284600593ff911423002c91ff6d6aa64964cbfd553bb24b24dfdb7aa9525932fed494ea92c937f2ea7754964cbfb533baa4b265fe776a4525933f711352292c91ff2e99588964ebdceec9444b257edb954a22592bf6dc94b112c95fbaed9588964afd974cac44b275ee7765622593bb6cacab112c9f5b9de5588964cbfd553bb20b2677cba955905933bf554aac82c9d5f9de5564164cfd97511320b267eeaa88990593af73bc44c82c9ddb9562264164cbfb533bb00b247fcba655805933bed4caac02c91ff2e99260164cfdb5311300b247fcba661705923fe5d32ab82c91ff2e9935c1648ff974c92e0b26cfeaa9dd60593a7f3bb2ab02c9d9f6565558164dcfd552aac0b27c7e7795560593e5f3bb08b02c9f8f9558458164e9fceec9ac0b2767e5564d6059377755444b02c9f3b9de2258164eddb2b112c0b27e6e5588960593f56c2444b02c9dbb64e2258164e9fceec8ac0b2767e5564560593b7711322b02c9f2f9dd4158164fd5c44a0ac0b25efabb60160593e7d3bb00b02c9f9e9558058164fdd444c02c0b265fda99dd505933bed4caaa82c99fb6a62254164f77308c02a0b265fda99dd3059367f3bb4c982c99fb6a6224c164dddb4d11260b247fcba661205923fe5d32e902c997f6a677481648ff974caa40b2677da9955205923fe5d326902c99fb6a62248164cbfb533ba20b267eda988910593e7d3bac0882c9f9e9556044164fdd444b0220b27fb14148110593afccc4ef002c9e7ea227780164e7f510cac00b275fa7765600593bbccacab002c9dde6625580164f6f5112ac00b27d7a7795600593edd3bb09002c9fce9558480164ebf4eec9c00b2777a5564e00592f7d5dac7002c9f3e9dd6380164fcf4aab1c00b27ed98358e00593eed3bc67002c9cfea219280164ebf4eec9400b2777a5564a00592f7cdb0a5002c9dfa64a2280164efd33111400b27bea8888a00593bf4cbc45002c9f7a9de2280164efd32b11400b27f6a5588a00593fd4c2445002c9dfa64e2280164fdd2c711400b27fca3388a005939fd44323002c9d7e9dd9180164eef4aac8c00b277ea2264600593ddd44283002c9f6e9dd4180164fe74aaa0c00b27faa2250600593f6cb1a63002c9dfc65e1180164fbe4ef08c00b277f19384600593f78b1c23002c9ff48ce1180164efe32508c00b27fe22284600593d5cc2300b02c9fac5056044164 else (if i<2 then 0xc9fde9555380164ffb306a9c00b27fd97354e00593bfcc3b25002c9dfe6159280164eff2eac9400b277fa5564a00593bfcb9325002c9dfe1499280164eff444c9400b25ffabb60a00593bfcdcb05002c9dfe65d8280164f7f30ec1400b27dfa7760a00593bfccab05002c9fde9558280164eff326c1400b27bf98360a00593f7cb1b05002c9dfe6498280164bff370b9400b277f9985ca00593dfd442e5002c9dfe6557280164fef4aab9400b27fb9845ca00593bfcc9ae5002c9f7e5cd7280164fdf2c6b9400b27fda335ca00592ffd5daa5002c9dfe6e55280164bff370a9400b277f99854a00593dfd442a5002c97fe6dd5280164fbf16ea9400b27dfa7754a00593bfccaaa5002c9fde5d55280164fef4aaa9400b27fb98454a00593bfcc9aa5002c9fbe58d5280164fef2a6a9400b27fda3354a00593bfcc92a5002c9ffa6095280164ffd2e4a9400b25ff9b814a00593bfccc0a5002c9efea205280164ff730829400b25ff9b314a00593bfcc98a5002c9fbe58c5280164ffb46629400b25ff9b114a00592ffd5da65002c97fe6e13280164bff36e99400b27dfa774ca00592ffcdaa65002c9fde9553280164ffb2e699400b27fe9824ca00593bfccc445002c9efea222280164eff32b11400b27f7a5588a00593fdcc2445002c9dfe64e2280164fdf2c711400b27fda3388a00593ff4c1445002c9ffa54a2280164ffd26511400b27fe98788a00593ff45ac45002c9ffa6162280164ffd2eb11400b27fea5588a00593ff4c1c45002c9ffa5ce2280164ffd2a711400b277f98764600593bfcc2b23002c9dfe5d59180164eff4aac8c00b277f98264600593bfcb9323002c9dfe5499180164eff0a4c8c00b277fa2264600593efd3bb03002c9fde9558180164ffb466c0c00b27bf98260600593ff511303002c97feaed7180164bff370b8c00b277f9985c600593dfd442e3002c9f7e61d7180164eff32ab8c00b27f7a555c600593fdcc22e3002c9dfe64d7180164fdf2c6b8c00b27fda335c600593bfcc92e3002c9f7e5c97180164ffd444b8c00b25ffabb54600593bfcdcaa3002c97fe6e15180164eff330a8c00b27bfa8854600592ffcdbaa3002c9dfe65d5180164fbf4eea8c00b277f99554600593fbd2aaa3002c9fee6115180164eff326a8c00b27ef96354600593fed19aa3002c9dfe6495180164fef2a4a8c00b27fea2254600593ff8c0aa3002c9ffc5c55180164ff730ea0c00b27fb98550600593fdcbaa83002c9fee9554180164ff7304a0c00b27fb97250600593fdca9283002c9fee1494180164ff7444a0c00b25ffabb4c600592ffcdc263002c9efea213180164bff36e98c00b27dfa774c600592ffcdaa63002c9fde9553180164ffb26498c00b27fea224c600593ff8c0a63002c97feaed2180164eff37290c00b25ff9b8 else 0x4698a40b27edd634c520593bf6c9242902c97fbaed2148164dfdd5490a40b277edb948520593bf6d4a42902c9dfb6612148164fbdcee90a40b25fedb548520593bf6caa42902c9fdb9552148164ff5b0890a40b277ed9348520593f76b1a42902c9ff95c52148164ffca6290a40b25ffabb5c1205937fd552e0902c9dfe6a57048164eff330b8240b26ff9a55c120593bfccaae0902c9f7e5d57048164fef4aab8240b27fb9845c120593bfcc9ae0902c9f7e5cd7048164fdf2c6b8240b27fe9525c120593bfcc8ae0902c9f7e5c57048164ff7282b8240b27fe9215c1205937fd55260902c9bfe6a13048164bff36e98240b27dfa774c120593fbd2aa60902c9ff654d3048164ffd2a498240b27fea224c120593fec98a60902c9ffa48530481649ffd76d3a20b26dfe7769d105927ff5db46882c9b7f9dda344164cffb4ec9a20b275fe7764d105927fedd306882c93ff6e97344164ddfb4eb1a20b27cfe7758d105927ff5db44882c99ff6e5a244164cffb30d1220b267fd97689105936ff3bb44882c9bef611a244164cffb26d1220b26efd63689105933fed3b24882c9d7f9dd9244164cffb4ac9220b267fda2649105927fedd304882c93ff6e97244164cffb52b9220b24ffdba549105933fed4aa4882c93ff6e85244164cffb5229220b25ff9b0149105927fedd264882c99ff6a62244164dfdb4511220b277ed92889105937f6d4444882c9dfb6622244164dfdb4f11220b27dee77889105937f6d2c44882c9dfb6562244164fedcab11220b27fad84889105937f6d1c44882c9dfb64e2244164fddac711220b27ef97558110593f7d2aac0882c9fbe5cd6044164fdf2a6b0220b27ef97258110593f7ca92c0882c9fbe1496044164fdf264b0220b27efa2258110592ffd5da40882c9dfe6e52044164eff33090220b26ff9a748110593bfccba40882c9f7e9dd2044164eff32a90220b27f7a5548110593fdcc2240882c9bfe68d2044164eff32690220b27ef96348110593bfcc9240882c9ffa5492044164ffd44490220b27ff15148110592ffd5db0f002c9dfe61d9580164eff2eacac00b25ffabb61600593bfcdcb0b002c9efe61d8580164fbf4eec2c00b277f99561600592ffcdc2eb002c9dfe6617580164f7f510bac00b27df9875d600593bfccc4ab002c9efea225580164fef30b2ac00b27f798795600593fbc594ab002c9fee5d58480164ff74aac2400b277f98764e00593bfcc2b27002c9dfe5d59380164eff4aac9c00b25ffabb60e00593efd3bb07002c9fde9558380164bff576b9c00b25ff9b85ce00593efcc3ae7002c9fde9557380164fdf30eb1c00b27ef8b558e00593f7cc2ac7002c9fbe5d56380164fdf4aab1c00b27ef8b258e00592ffd5daa7002c97fe6e15380164bff36ea9c00b27dfa7754e00593fbcc2aa7002)) else (if i<4 then 0x592f7edb0a4982c9bbf698524c164bff36029260b267fda98893059377ed3444982c9bfb69e224c164fbdcef11260b27f6e5588930592ffd5db00982c9f7e9dd804c164f7f30ac0260b27f7a5560130593ff511300982c9efe605804c164ffb262c0260b24ffdb8aa9205927fedbd54902c93ff6d6aa481649ffb6755240b24ffdb1aa9205933ff55352902c99ff6a5a848164d7f950d4240b24ffebb6a1205933fedcb50902c99ff661a848164d7fd10d4240b26fbd846a1205933ff55330902c99ff6a5a7481649ffd76d3a40b267fd9869d205933ff5532e902c99ff6a197481649ffb74c3a40b24ffcba61d205936ff554ee902c9d7f6a67748164dbfb513ba40b275fd989dd205933fed4b4a902c93ffaeda548164cffb72d2a40b267fd98695205936fe5bb4a902c9b7f9dda548164cffb5252a40b25efdb6295205937bed294a902c99ffaa99548164cffb50caa40b267fda765520593aff3bb2a902c99ff69595481649ffb74c2a40b24ffcba615205927fedd2ea902c99ff6a575481649ff9752aa40b267fda9955205937bed2caa902c9ddf6565548164def9752aa40b26f7eaa95520593bbed4caa902c9bdf6a25548164eefb312aa40b26f7da795520593ebf3bcaa902c9fdb2ca5548164df7d54c2240b26fbda761120593edf3bb08902c9bef6958448164fe7caac2240b24ffebb68d205936ff3bb46902c9bdf955a348164cffd54c9a40b267fda764d20593aff3bb26902c99ff6959348164eefcaac9a40b24ffdba5cd205927fe5d2e6902c9b7f69d7348164bdfd76b1a40b26efcba58d2059377f552c6902c9bbf69d6348164f9fceeb1a40b26efda558d20593f3f2aac6902c93ff6e953481649ff974a9a40b267feaa649205933fed4324902c99ff69d9248164ebfceec9240b267fda564920593bbf2ab24902c9dfb8899248164eff2e0c9240b277ed92609205933fed4aa4902c9dfb6495248164bfdd76a9240b26feeaa54920593bf6dcaa4902c9dfb6a55248164dfdb50a9240b277ed9854920593ef65baa4902c9bfb69d5248164fbdceea9240b27f6ca554920593bf6caaa4902c9fdb5d55248164fedcaaa9240b27fad8454920593bf6c9aa4902c9fbb58d5248164fedaa6a9240b277eda9889205937f6d4444902c9dfb6622248164dfdb4b11240b277ed9588920593fb72ac44902c9feb6122248164dfdb4711240b277ed9388920593f76b1c44902c99ff6a5a148164cffd54c8a40b267fda8645205933fed3b22902c9d7f9dd9148164cffb4ac8a40b2777e5564520593bf6a9322902c9dfb8899148164dbfb4eb8a40b24ffcba54520593fb6a92a2902c9befaa94148164df7b50a0a40b26fbda750520593edf3ba82902c9bef6954148164fe7caaa0a40b27fad5250520593fd711282902c93ff2e93148164dfbb else (if i<5 then 0xf6c45258164ddfd55112c0b276fd9588960593f3f2ac44b02c9faf6122258164edfb27112c0b27eed5288960593f76c3c44b02c9fbb2d62258164fddaeb112c0b27eee5588960593f76b9c44b02c9dbf5d59158164edfcaac8ac0b276fd7264560593b7ea9322b02c9dbf1499158164edfc44c8ac0b25efebb5c560593f3f2aae2b02c9f3f5c97158164fddc44b8ac0b27ebd7250560593f5ea9282b02c9faf1494158164fd7c44a0ac0b25efebb4c560592f7edba62b02c9f3f9dd3158164fcfcaa98ac0b27eee224c560593f7d5db00b02c9fbe6dd8058164fdf36ac02c0b27ef8b560160593f7cbab00b02c9fbe9558058164fdf366c02c0b27ef97360160593f7cd9300b02c9fbe2c98058164fdf2e4c02c0b27ef95260160593f7c29300b02c9fbe8898058164cffb2f552a0b267fda96a1505927ff5db50a82c99ff6e5a854164cffb30d42a0b26bfe886a1505937dec2350a82c99ffaa99854164cffb52d3aa0b24ffebb69d505933fecc34ea82c93ff6e98754164dbfd553baa0b275fda99dd505936fed44eea82c9d7f6627754164cffb50caaa0b267fda765550593aff3bb2aa82c9dfe5c19554164eefb2ac2aa0b26f7da895550593bbecc4aaa82c9befaa98454164df7b4ec22a0b27dbe7761150593f9f2ab08a82c99ffaa99354164cffb4ec9aa0b275fe7764d50593bbf2ab26a82c97bfaed6354164ddf974b1aa0b26efeaa58d5059377ed3ac6a82c9f3f9dd6354164fcfcaab1aa0b267fda9689505933ff55324a82c99ff6a19254164cffb4ec92a0b275fe7764950593bbf2ab24a82c99ff6a57254164cffb52a92a0b267fda988950593bf6c9444a82c9bfb2ea2254164dfdd55112a0b277eda9889505937f6d4444a82c9dfb6622254164dfdb4f112a0b27dee7788950593bf6cac44a82c9fdb9562254164ff5b09112a0b277ed9388950593f76b1c44a82c99ff6a5a154164cffd54c8aa0b267fda8645505933fed3b22a82c9d7f9dd9154164eefcaac8aa0b277ee22645505937df55282a82c9bef6a14154164df7b4ea0aa0b27dbe7750550593f9f2aa82a82c9feb8894154164fdbac698aa0b25ffabb601505937fd55300a82c9dfe6e58054164eff352c02a0b27dfa7760150593fbc5ab00a82c9dfe6558054164f7f30ac02a0b27f7a5560150593bfcc9b00a82c9fbe58d8054164eff324c02a0b27fea2260150593bfcc8b00a82c9fee5058054164bff576b82a0b26ffaaa5c150593bfcd4ae0a82c97fe6e17054164eff330b82a0b27fb9845c150593bfcc9ae0a82c9f7e5cd7054164fdf2c6b82a0b277f9925c150593ff5112e0a82c9dfe6457054164fbf2e2b82a0b27fb9415c1505927ff5db4e982c9b7f9dda74c164cffb52b9260b26efda65c9305933fed4aa4982c9bbf699524c1649ffb7429260b267fda91493 else 0x320b2777d7554990593bbf2aaa4c82c9dfb5c95264164cffd5429320b257fdb814990592bfed98a4c82c95ff6c45264164cffd5511320b2777e5588990593bf6a9444c82c9dfb2d62264164efdaeb11320b277ee55889905927fedbd54c02c93ff6d6aa601649ffb6555300b24ffdb1aa9805933ff55352c02c99ff6a5a760164dbf94ed3b00b25f7cb569d805936ff554eec02c9d7f6a67760164cffb52d2b00b267fda929580592efedb94ac02c9bdf694a560164bfdb6452b00b25ff5b1295805933ff5532ac02c9d7f9dd9560164cffb52bab00b24ffcba955805933fed4caac02c9ddf6565560164def9752ab00b26f7eaa95580593bbed4caac02c9f5f9de5560164cffb52d1300b267fda9289805937f6d1144c02c99ffaa99260164ebfceec9300b2777e55649805933fed4ae4c02c93ff2e95260164cffb52a9300b24ffdba149805933fed48a4c02c97fe6c052601649ff97511300b267fda988980593bf6c9444c02c9bfb2ea2260164dfdd5511300b277eda988980593ef73bc44c02c9dfb6562260164fedcab11300b267feaa64580593aff3bb22c02c9ddf9559160164efdc44c8b00b24ffcba4c5805927fedc554b82c93ff6d6aa5c1649ffb67552e0b24ffdb2aa9705927fed8d54b82c9aff2a1a85c1649ffd76d42e0b267fd986a1705935ff44350b82c9bdf2d5a85c164df7b08d42e0b267feaa661705933ff5532ab82c99ff6a1955c164ebfaeacaae0b2777e55655705936ff552eab82c9b7f6a1755c164ebfb30baae0b26f7eaa955705937bed44aab82c9ddf662555c164cffd54c9ae0b275fd7564d70593bbf2ab26b82c9b7faa9735c164cffd54c92e0b267fda864970593afebab24b82c9ddf955925c164efdc44c92e0b24ffcba54970593ebebaaa4b82c9bfbaaa225c164dfdb51112e0b277ed9888970593bf6cac44b82c9f7b5d6225c164fedcab112e0b277ed9388970593ef6b9c44b82c99ffaa9915c164cffb50c8ae0b275fd7564570593bbf2ab22b82c9dfb889915c164dbfd54b8ae0b275fd935c570593afec92e2b82c9f7b889715c1649ff97498ae0b25dfdb74c570592f7f5db0eb02c9dbf5d59558164ddfd54baac0b27cfd875d56059377f554aab02c9f9f61e5558164fcf9652aac0b27ebd7561160593f5f2ab08b02c9dbf5d59358164edfcaac9ac0b25efebb5cd6059377f552e6b02c9f3f61d7358164fcfcaab9ac0b26efeaa5c960593b7ecaae4b02c9f9f9557258164fd7b08b92c0b276fd935c960593e7eb9ae4b02c97bfaed5258164ddfd54a92c0b25efdb754960593e7e5baa4b02c9f3f9dd5258164edfb2aa92c0b27e7d7554960593f3f2aaa4b02c9faf6115258164edfb26a92c0b27eed725496059377f550a4b02c97bf6e05258164fd7b08292c0b25efdb314960593b7ec98a4b02c97b))) else (if i<9 then (if i<7 then 0xffedc2e6882c9bff6a17344164fbfb0eb9a20b26ffebb689105937fedc344882c9bff6dda244164dffb0ed1220b26ffdb5689105937fe5ab44882c9bff6cda244164dffae6d1220b25ffebb609105937fedd304882c9bff69d8244164f7fb0ec1220b26ffda5609105937fed1b04882c9bff6898244164bffb70b9220b26ffda85c910593bfecc2e4882c9bff6957244164effb2ab9220b27fbd845c9105937fed1ae4882c9dff64d7244164fbfae6b9220b27efd635c910592fff5daa4882c9bff6e95244164effb72a9220b25ffdb754910593efe5baa4882c9bff68d5244164effb26a9220b27efd63549105937fed12a4882c9dff6495244164ffdb04a9220b27fed7254910592ffed98a4882c9bff68c5244164effb2629220b27efd6314910592fff5da64882c9bff6e93244164bffb7099220b26ffda84c910592ffedba64882c9bff69d3244164bffb6a99220b26ffda54c910593feeb9a64882c9bff6893244164ffdb0499220b26ffda888910593bfecc444882c9bff6962244164effb2b11220b27fbd84889105937fed1c44882c9dff64e2244164fdfac711220b27ffabb48110593ffcdc240882c9ffe6dd2044164fff30e90220b27ff9b548110593ffc5aa40882c9ffe6152044164fff2ea90220b27ffa5548110593ffcd9a40882c9ffe60d2044164fff2e690220b27ff95348110593ffcc1240882c9ffe5492044164fff26490220b267feaa5c9925933fed2ae4c92c99ff68d7264964cffb40b9324b267feaa14992592bfed98a4c92c99ff68c5264964edfac629324b277de3314992592bfed80a4c92c99ff6805264964cffb4b11324b267fda388992593b7eb1c44c92c9df78ce2264964efda6511324b267fda088992592bff5db2ab92c977f6deaa549649ffb6f552a4b26dfdb7aa9525927fed8554a92c95ffaeda954964cffd54d4aa4b275fcb76a5525933fed4b4ea92c93ffaeda754964dbfd5453aa4b275fda929d52592efe5d4eea92c9b7faaa7754964ebfb533baa4b257febb649525933ff55324a92c99ff69d9254964ebf94ec92a4b275fe7764952593bbe5ab24a92c9ddf5d59254964efdae4c92a4b277ee22649525937f7552e4a92c9dfb6a57254964cffb52d02a4b26dfca7681525937fc50340a92c99ff549a914964affd76cac44b267fcba656225927fe5d4ab112c9dfb2d59288964efd94ac9444b277ed7564a22593bf72ab25112c9dfb6e55288964efdb2aa9444b27f6e5554a22592ff6d894b112c97fb6c0a588964efd974cac44b277eca565622593bf6bab2b112c9dfb9559588964bfd9752ac44b27f6cba956225933ff552eac82c99ffaaa5564164eef9652ab20b267feaa5c990593bbf2aae4c82c95ffaed5264164cffb74a9320b267feaa54990592bfedbaa4c82c9d7f2dd5264164ebfceea9 else (if i<8 then 0x5248164ffdb6ea9240b27feda754920593ff6c3aa4902c9ffb6155248164ffdb66a9240b27feda354920593ff6b9aa4902c9ffb54d5248164ffdb62a9240b25ffebb4c9205937ff55264902c97ff6d53248164dffb4a99240b27fed524c920592fff5db42902c9bffaa9a148164dffb50d0a40b277fd98685205937fed3b42902c9dff65da148164dffb4ad0a40b26ffca568520593bfecab42902c9fef611a148164dffb46d0a40b277fd9368520593f7eb1b42902c9ffb549a148164effb50c8a40b277fd8764520593bfed2b22902c9dff6159148164effaeac8a40b277fe5564520593bfec1322902c9dff5499148164bffb74c0a40b26ffeaa60520593dfed4302902c9bff69d8148164dffb4ac0a40b26ffda360520593ff6a9302902c97ff6e97148164dffd54b8a40b25ffdb85c5205937fed42e2902c9dff6617148164fbfb4eb8a40b27dfd875c5205937fed2ae2902c9dff6557148164ff7b08b8a40b26ffda35c520593bfec9ae2902c9fbf58d7148164ffdaa4b8a40b26ffdba545205937fe5d2a2902c9bffaa95148164dffb4ea8a40b26ffda354520593bfec9aa2902c9fbf58d5148164ffdb64a8a40b277fd9254520593ff6a92a2902c9fef6a14148164ff7b4ea0a40b27fbd8750520593fded2a82902c9fef6154148164ff7aeaa0a40b27fbe5550520593fdec1282902c9fef5494148164bffd7698a40b25ffdba4c5205937fedd262902c9bffaa93148164dffb5098a40b25ffdb74c5205937fed3a62902c97ff6d53148164dffb4a98a40b27fdda34c520593ff6a9262902c9ff74c93148164ffeb0298a40b27ff9b04c5205937ff55242902c97ff6e12148164dffb5090a40b277fd9848520592ffedaa42902c9bff6952148164effb2a90a40b27fbd8448520592ffed9a42902c9bff68d2148164effb2690a40b27efd6348520593ff6c1242902c9ffb5492148164ffda6490a40b27ff53148520593ff755242902c9ffb6e12148164ffdb5090a40b27feda748520593ff6c3a42902c9ffb6d52148164ffdb4a90a40b27feca548520593ff6c2a42902c9ffb5d52148164ffdcaa90a40b27fedb348520593ff6d1a42902c9ffb5cd2148164ffdaa690a40b27ffaaa5c120593ffcd42e0902c9ffe6957048164fff30ab8240b27ff9a35c120593ffca9ae0902c9ffe6857048164fff302b8240b27ff9515c120593ffc98ae0902c9ffeaa93048164fff35098240b27ff9a74c120593ffcc3a60902c9ffe6953048164fff14a98240b27ff9854c120593ffcbaa60902c9ffe9553048164fff30498240b27ff9524c120593ffcd0a60902c9ffe6053048164fff2e298240b27ff9514c120593ffc90a60902c9bff6e1a344164dffb6ed1a20b26ffdb568d105937fed9346882c97ffaed8344164dffb74c1a20b25ffebb5cd10592 else 0x27ff9b760130593ffcdab00982c9ffe2d5804c164fff2eac0260b27ffa5560130593ffcd9300982c9ffe2c9804c164fff2e4c0260b27ff95260130593ffc29300982c9ffe889804c164fff362c0260b27ff97160130593ffc90b00982c9bff2d6aa48164bffd76d4240b26ffeaa6a120593bfecc350902c9fef611a848164dffd76d4240b26ffdb76a1205937fec3b50902c9bff6d5a848164dff96ad4240b26ffd856a1205937fec1b50902c9bff6c5a848164dffb02d4240b277feaa66120592fff5db4e902c9bffaa9a748164dffb50d3a40b277fd9869d20593bff5532e902c9dff6a19748164bffd76c3a40b25ffdba61d205937fe5d30e902c9bffaa98748164effb52c3a40b25ffebb695205937ff5534a902c9bff6a1a548164effb30d2a40b27dfcb7695205937fed3b4a902c9bffaeda548164dffb70d2a40b26ffdb7695205937fec3b4a902c9bff5d5a548164dffb66d2a40b26ffdb169520592ffedc14a902c9bff6a0a548164effb3052a40b25ffdb329520592ffed894a902c9dffaa99548164effb50caa40b277fda765520593bfec3b2a902c9dff6959548164effaeacaa40b25ffebb61520592ffedd30a902c9bff6e98548164dffd54c2a40b277fdb961520593bfed4b0a902c9bff69d8548164f7fb0ec2a40b26ffda561520593bfecab0a902c97ff6e97548164dffd54baa40b25ffdb85d5205937fed42ea902c9dff6617548164fbfb0ebaa40b26ffeaa955205937fed44aa902c9dff6625548164ff7d54c2240b27fbda761120593fded2b08902c9fef2958448164ff7aeac2240b27fbe5561120592fff5db46902c9bffaa9a348164dffb50d1a40b26ffda768d205937fed2b46902c9bff295a348164dffd76d1a40b26ffdb868d205937fedbb46902c9bff61da348164dffb6ad1a40b26ffcb568d205937fec2b46902c9bff5d5a348164dffcaad1a40b26ffdb168d20593bff55326902c9dff6a19348164effb4ec9a40b277fd8764d20593bfed2b26902c9dff2959348164effb0ac9a40b277fd7564d20593bff2ab26902c97ffaed7348164bffb74b9a40b26ffeaa5cd20593efed3ae6902c9f7f61d7348164dffb4ab9a40b27efcba58d20593f7f552c6902c9fbf6a16348164fdfb4eb1a40b27efd8758d20593f7e5aac6902c9fbf6956348164fdf94ab1a40b27efd8558d20593f7ebaac6902c9fbf9556348164dffb74a9a40b26ffeaa54d205937fed3aa6902c9dff61d9248164effb0ac9240b277fd7564920593bff2ab24902c9bffaa98248164effb2ac1240b25ffebb549205937ff552a4902c97ff6e15248164dffb50a9240b277fd9854920593bfecaaa4902c9fef6115248164dffb46a9240b277fd9354920593f7eb1aa4902c9ffb6095248164ffdd76a9240b27feeaa54920593ff6dc2a4902c9ffb6a1)) else (if i<11 then (if i<10 then 0x932aa82c9dff5c59554164bffd76c2aa0b27fbda761150592fff5db46a82c9bff6a1a354164dffb4ed1aa0b277fda864d50593bfed3b26a82c9dff61d9354164bffd76b9aa0b25ffdba5cd505937ff552e6a82c9f7f61d7354164fdfb50b1aa0b27efda758d50593f7ec3ac6a82c9fbf2c96354164bffd76d12a0b26ffda868950593bfecc344a82c9f7f2dda254164dffb4ed12a0b27fbd84689505937fed1b44a82c9dff64da254164fdfac6d12a0b277fda864950593bfed3b24a82c9dff61d9254164effb0ac92a0b277fda264950593bfeb9324a82c9dff8899254164bffb74b92a0b26ffeaa5c950593bfed4ae4a82c9bff6a17254164effb30b92a0b27fbd845c950593bfec9ae4a82c9f7f5cd7254164fdfac6b92a0b25ffebb549505937fed42a4a82c9dff6615254164ff7b08a92a0b277fd9354950593f7eb1aa4a82c9dff6495254164dffb74992a0b26ffeaa4c9505937fed3a64a82c9bffaaa2254164effb53112a0b26ffda888950593bfecc444a82c9dff6562254164ff7b09112a0b277fd9388950593f7eb1c44a82c97ffaeda154164dffb50d0aa0b277fd98685505937fed3b42a82c9dff65da154164ff7b08d0aa0b26ffda368550593bfec9b42a82c9fbf58da154164dffb44d0aa0b277fd9268550593bfed4322a82c9dff69d9154164effb0ec8aa0b277fd8564550593bfed1322a82c9dff5c99154164effaa4c8aa0b277fe2264550592fff5dae2a82c97ff6e97154164dffd54b8aa0b26ffda85c550593bfecc2e2a82c9f7f61d7154164ff7b08b8aa0b277fd935c550593f7eb1ae2a82c9dff6497154164fbfae4b8aa0b27fbda850550593fded3a82a82c9fef61d4154164ff7b0aa0aa0b27fbda250550593fdeb9282a82c9fef5494154164ff7c44a0aa0b25ffebb4c550592ffedd262a82c9bff6e93154164dffd5498aa0b26ffda84c550592ffedba62a82c9bff69d3154164dffb7490aa0b26ffeaa48550593bfed4a42a82c9bff69d2154164bffb6690aa0b277fd9348550593f7eb1a42a82c9dff6492154164fff576c02a0b27ff9b760150593ffcd3b00a82c9ffe6cd8054164fff346c02a0b27ff97360150593ffcd9300a82c9ffe2c98054164fff344c02a0b27ff97260150593ffca9300a82c9ffe4c98054164fff444c02a0b27ff9b160150593ffcd0b00a82c9ffe5c58054164fff262c02a0b27ff92160150593ffcd42e0a82c9ffe68d7054164fff344b82a0b27ff9325c150593ffcd0ae0a82c9ffe4c57054164fff242b82a0b25ffebb549305937fedd2a4982c97ff6dd524c164fbf96ea9260b27fed7254930592ffed88a4982c97ffaed714c164bffb70b8a60b27dfd875c530593efeb92e2982c97ffaed214c164dffb7490a60b25ffdb7485305937fed3a42982c9ffd5c5214c164fff576c0260b else 0x164effb4ac9300b277fca564980593bfebab24c02c9dff9559260164effb44c9300b277fca264980593bfeb9324c02c9dff1499260164effc44c9300b25ffdba5c9805937ff552e4c02c9dff6a57260164effb2ab9300b25ffebb54980592ffedd2a4c02c9bff6e95260164dffd54a9300b277fda954980592ffedbaa4c02c9f7f2dd5260164fef94aa9300b27f7d7554980593ff6d12a4c02c9dff6495260164ffdae4a9300b25ffdba149805937ff550a4c02c97ff6c45260164dffd5511300b277fda988980593bfecac44c02c97ffaeda160164dffd54d0b00b26ffda7685805937fed2b42c02c9bff295a160164dffb46d0b00b26ffda2685805937fe51342c02c9dffaa99160164effb4ec8b00b277fda564580593bfe52b22c02c9dff5d59160164effcaac8b00b277fda264580593bfe51322c02c9dff5c99160164effaa4c8b00b277fc5264580593bff11322c02c9bff6e93160164dffd5498b00b25ffdb8aa970592ffed9d54b82c97ff6c6aa5c164ff7a83552e0b26ffdb8aa9705937fed9d54b82c9bff6c6aa5c164dffaa3552e0b277fd986a170593fdec2350b82c9bff615a85c164dffb06d42e0b26ffd826a1705937fec0b50b82c9dffaa9985c164effb30d2ae0b27fbd4169570593bff5532ab82c9dff6a1955c164effb4acaae0b277fda265570593bfea932ab82c9dff685955c164effaa2caae0b277feaa64d70593bfed4326b82c9dff695935c164effb30d12e0b277fd9368970593bff55324b82c9dff6a1925c164effb4ac92e0b277fda264970593bfea9324b82c9dff685925c164effb30a92e0b277fd9354970593bfecc342b82c9dff64da15c164effb50c8ae0b277fda564570593bfea9322b82c97ffaed315c164dffb7498ae0b25ffcba4c5705937ff55262b82c9bff6a1315c164fbfb6e98ae0b27dfd754c570593f7f5db0eb02c9fbf6d58758164fdfb66c3ac0b27efdb261d60593f7f5dae6b02c9fbf6e17358164fdfb6ab9ac0b27efdb25cd60593f7ed8ae6b02c9fbfaed5258164fdfb70a92c0b27efdb754960593f7ec3aa4b02c9fbf6cd5258164fdfae6a92c0b27efdb154960593f7f2ac44b02c9fbf6d57158164fdfb66b8ac0b27efd525c560593f7edba62b02c9fbf6d53158164fdfaea98ac0b27efe554c560593f7ed9262b02c9fbf5c93158164fdfaa498ac0b27efc524c560593f7f11262b02c97ffaeda854164effb30d42a0b27fbd846a150593ffcc0350a82c9bffaeda854164dffb6ed42a0b26ffd876a1505937fec1b50a82c9bff6c9a854164dff964d42a0b26ffd826a1505937fed8b50a82c9bff605a854164bffd76d3aa0b26ffda869d50593bfecc34ea82c9fdf545a754164bffd76c3aa0b25ffdba61d505937fe5d30ea82c9bffaa98754164effb52c3aa0b277fd8765550593bfeb) else (if i<12 then 0x746039ff1cec8e6cc731a39721ca08e46c720038da1c5a0e20c70ba38371c088df806f7437941bb18dcf46e1836e61b550d9e46c90360c1af30d7006b4a35741aa18d44869d834d11a558d1e868be342e19f90cf04670a336a199c8cc2065da32d219560c9ec64aa322418ff0c7346322317618a80c47c61f230d318568c1f060ac302517ff8bf645f662f8d17b38bcd85e202edf17570b9f45c982e2617000b7685b682d8e16b98b5345a4e2d01166d8b2d459082c5316110afc4576a2b8415af0ace056242aec15688aaac54f42a5415118a7f453c429b114c58a5c0527e292414798a334514e288114280a0d4501e27de13dc09e484ed82746139589c144dd426b9134f099e04c8e261612f8097544b48257312a10941849aa24a41239890dc480c23e011d788df8469a2311117588ae845282263111e8883043b621c010cd085a44286211d107b88344412a2064101f0808c3ffa1fcc0fd307dd43e9e1f290f7c07b1c3d2c1e700f25078903be61dcd0ed3876303a481cdd0e4006fdc378c1b8a0da706c74353e1a4d0d0e067ac3348195d0c8b062e4311018570c18860002f7217930bb105c402d6616820b12857d02b4415710a9505360290c14340a0184f482758137b09aa84c9025e612c20948849802474120908e68467022d6113a087f043342138107608280407c1fdc0fbd07c603d6c1e540ee3075903a041ca00e1f06f1836701ac00d0306638320018880c1305f102ec417000b44057e82b0415200a5f05170279c1356096f049f0243411b808a0042c820a0100407dc03d581e140ea80718036881a800c9c061202eb016680ad2052d02788130008f20453021100fc40796039a01b480ce0060e02d60152809fc0470021d00f0806ec032a0164003c000f00001dff60d7264964effb0629324b277fca588992593bfec1c44c92c9dff54e2264964effae0d4aa4b25ffebb681525937ff55340a92c9bff6a1a054964fbf96ed02a4b26ffda768152593efe53b40a92c9fdf5d5a054964dffb46d02a4b27fed72681525937fed0b40a92c9dff641a054964fdfac0d02a4b27fed2068152593bff2ab2b112c9dffaed5264164effb70a9320b277fdb754990593bfed9aa4c82c9dff6c55264164effcab11320b27fbd41aa9805937fe5ad54c02c9bff2caaa60164bffd76d3b00b26ffeaa69d80593fbe5ab4ec02c9f7f1c9a760164bffd76d2b00b26ffeaa695805937fed3b4ac02c97ff6c8a560164bffb6252b00b27fbd4129580593bfed3b2ac02c97ff6e97560164dffd54bab00b27dfda75d5805937ff554aac02c97ffaeda260164dffd54d1300b26ffda7689805937fed2b44c02c9bff295a260164effb2ad1300b26ffca268980592ffeda944c02c9bff694a260164bffb6251300b27fbd4128980593bff55324c02c9dff69d9260 else 0x2242900547cca3aa51bca8d79462ea2d0514fa89b94438a1ca50c1a84c54200a0e55044281b540369fd44fdca7e4d3eda9f474f90a7bed3d529e574f0da77253aee9d304e6f272e1390e9c614e12a6fa537449b664d84a6b0935229a604d17a67f9335899654c8f26389312098544bfba5ec12efe97434b78a5aa92cb096064ada2550529f494a84a41250ed27e893ad49b8a4c7d259a92a7494ba49c5249691f948d3a46052274911448772432121189045480fa40111f648f60479d23c511df28ec84740a39411c6a8e1a46e9a36051a5e8cdd465ba3245187e8bf845d8a2e2d16ca8b3f4597a2bf915b08aa745462299914ac8a304505227bd133a894b4487a23211144887c442b220690fd287ad43c921ddd0eb887154382a1bd50d72867d43312191d0c1685da42e5215b50a6284df425ca122108ae8447421ba0fc10752836d419e20c01057282934120a086d03ea81a340bea04d9022080c94041200ecffd27f8c3fa81fbf8fd587e703f149f7b4fb787da13ec31f580fa747cfe3e669f270f8c07c243de91ee00f65c7adc3d4a9e938f40e79f73cc21e520f20278db3c4a1e134f02277ca3bbc1dc6ced7c76613b079d7a4eb9c75a83ac11d494e94e746b3a0c9cf1ce742734f39841cbb4e50a723338eb1c6c0e2bc70eb38579c1a0e0166fb937b91bd04de4c6f0037679bad0dd066e68371b9b870dc186dd036c49b58cda226ceb36471b1a0d86e6bda35be9ad5cd60a6aea35519a944d41469d934d41a558d1f268c834409a140cffc67b733b819ca4cdc466bc333a9993ccc6865ed32d89957cca46651332819931cc900642e31f398e80c6c86349319718bc8c58262b13140188b8c41061e230e398658c2e061343087183ccc19a609c303b18114c0125fac2fb297ca4be065ebc2f4b179c0bc945e192ee917658ba9e5d082e6b972f0b9005c5a2e1a17064b78e5b962da796c78b61c5afe2d6696a70b4d65a5b2d0a16734b34e598c2ca8164a8b20858c82c5696248b0ac581a2be995e30ae8a57142b7715a9cacc0562f2af995708ab0c556b2a9d1547ca9dc54b22a4b951c4a85453ee29e414e5ca6cc532a298214a9ca502523a290a14708a2e0513428819426ca0d4502327e893eac9ef44f1d277093a689ce84e1726e8135cc9a424ccf262e1302897704b66259512b34950c4a602517927f893b049b224cb925989254490f246f122b490e24840240211ec88e9446f823589197c8c1a45bb22af114e089f844c02242110f4884443e621da90e6886a6430c217310a7c849a422720df9063882e6414d208e103ac818a409f203c9014c80443ffc1feb0fec07f2a3f6f1fa48fc8c7dce3eb61f480f9a87c723e131ef68f71c7b423d701ea50f49079fc3ccd1e4e0f1ac785e3bfe1de68ee7076ec3b501d950ec1075bc3aad1d3e0e958)))) else (if i<20 then (if i<16 then (if i<14 then 0x1c108af8434420de100d07d583ccc1d1e0e0106cf833ec18ae0bdf05a882b64151a0a2b04d98254411b2086103f481dc40e1e06970304816440a06044901f380e6c064602ab01248074402de0123006080123fff9ffb0ff917fb03fcbdfdd0fea17f383f8fdfc1cfde87ee6bf671faecfd457e8fbf411f9e8fcc37e543f235f8cefc417e02bef51f746fb7d7da63ec6df5d4fac47d443e95df420f9c97cc6be571f26cf8fa7c5f3e1ddf08cf8207bf7bdea1eeeef7517b853db65ed50f6777b233d855ebb2f5b37ac13d571ea6cf5057a6a3d2b9e93cf4837a293d0dde822f3eb79e2bce7de6f2f34879913cbc5e580f28f792f3c889e3e2f1b578c7bc5a5e286f11d78763c2ede12af064781f3c035dfb8efb677d33bda9de88ef1e7781bbb1ddd16ee65771fbb865dbd0edc276ce3b5d9da8aed147671bb2c9d918ec5b761abb03dd7d2ebb875c93ad59d61eead375513a999d46aea0474e43a65dd2f8e94074823a34dd12ee87174203a03dcfa6e7a273b339cd5ce08e6d37351399c5cc80e60f72ef396b5cacce535727cb92f5c8d6e42471f438f09c722e34a718cb8bcdc59ae291712538865c38ee19670a7b844dc1aee0a6702a38061bfa2df956fa737c1dbd96dea56f2f37889bbe2ddb56ec237579ba18dcd06e44b7161b838dbeb6de2b6e51b6c6db326d75b6a91b4e6da376cf8366d1b2c4d91b6c6a362b9b0e4d82b6bf235ecdaf04d7466b7fb5b0dad0ed6406b0d35779ab70d5876aa03543da9bcd4b86a3e3512da81ed3de69d6b4e1da6c2d330696f34a89a4ccd22a68f734619a27ed0ed6863b422da088d01367f6b3ef19f42cf7b679fb3b899d62ce6a670c337459b2acd596699b3409998ccc746627330cd9804cbe765bfb2ce195e2ca9f6542329a5945ac9e664e0326c192e8c92d64683232d9108c82763eab1e398ee6c74d6393b1c318de2c6d6635db1a558cdec65f6327b18d18c32c5f362ec316458a7ec5196269312b1889ec41e61e630dbd860ec2e1614d309d18444c1c560b43045981b4c0936036b011d8042bffb5feaafe397e8ebef55f51af99d7c40be1b5ee4af68d7b26bd415e82af37d79b4bcb45e472f11d7842bbe55dd4aedb5768ebb215d7daebad75b6ba9f5d2c2e94d73ecb9db5ce02e5b97264b8eb5c4cae175702cb7cf5bbeadd896e78b7165b832dbd96da0b6c05b31ad89d6bd6b5af5ab42d4016972b4515a052ceb56750b3615987acb796518b23a58f42c6016230b0dc5860ac2c560d4b02357feabf5d5f78af5f578c2bbf55ddaae7a57092b7015b34ad7456912b3995980ac8f5634ab10d5850ac0d55f3aaf3156f4ab1d55762aaed552aaa855519aa78553a2a9a054b22a47551eea8dc5455aa21550bea84f540429ead4ec8a71d5365a9ac14ca6a638530ea972d4b60a5695291293c54954a4845 else (if i<15 then 0xb2594a2c9c364bbb23fd9192c85163e1b1d858dd2c69d6328b186d8b9ec56d6285b12fd88e6c41161d7b0d358602c29f6113b071582f2c1176044b009d7f32bf4d5f75afa257c4ebdc55eb1af405796abc275de2aecdd75aaba735d13ae71572c6b9175c65ae1a5700eb7d15bcdadce56ddab68b5b2aad87d6b7ab5715a92ad2b5683eb3d359b8acc3d652eb23558d3ac56d61f2b0ad5830abffd5f3aaf25576cab9dd5bfead9d5692ab3bd591aac1555d9aad45560aaa8d5515aa72552cea8ef5446aa0ad4f66a73b5356a992d4bd2a55b5266a90a54736a3395155a88cd4376a1595086a82ad40929ffd4fcda7ce53dda9e5f4ef3a750d39c29c7f4e24a70a5378e9b7b4d97a6be5352e9a614cffa6675327699054c67a6265306e97eb4bdaa5dfd2e3a96e74b42a588d2bda95b74aaaa53cd294e944549e6a4e05263e92914922a478d230291354874a427520768fef47dca3db51e428ed54744a394d1c0e8dd146cda35951a328ce3464ba312d17fe8bb3459da2b0d14ee8a1544c3a24951186884b43ffa1e750ea286c3433ba17fd0b0e85254261a1185082a83c941b3a0bbd0572826d40efa064d020a807740209ff7cfefa7f1b3f5c9fa0cfc427d933e8d9f394f95e7c4d3dd49ed74f59e7a2b3d059e7acf33e79533c6d9e1e4f05a77f73bbf9dccced4a76593b119d7b4eb6e753f3a6e9d244e83273b739b59cb74e52271ed38ba9c44ce162703937f69be2cde266e9b37119b6acda926ce736379af2cd64e6aaf353c9a7acd2e66911344c9a0dccfaa6789339e99c1ccd766685333299864cbc665c332b0994acc9be6493320d98e8cc68262df313e98814c2ee612b304e9803cbf5a5f1f2f69979c4bc765dd92eb097504ba425cd52e449714cb80e5ba52da196ad4b4d25a072cbc96404b06257a32ba095accacce55c32a9a952f4a90e542529ec94d84a5fe529d291d94764a2ee5141286f941f4a00a4f8d279593b7c9cfa4e1b26d1934ac99924c67260292ddc962a4a9d2512926b4929648d32438920948fb2474b235e9196c8bf2456b228f9129c880643a1219f90b7484f6420320d0904a48162404f1feb8fd247dce3e9b1f1c8f7047a923cfd1e428f08c77ae3b8b1d7e8eac4747239d71cc58e44c7136384f1c018de846eaa36f31b3d8d9146bc635971a848d29c688a33b719aa8cb7464ca31ed18d08c5ac61e6306518018bedc5e262e8517118b7045abe2d1316588b13c57da2b8b15aa8ac7c557a2a5b14fc8a5ac52122891140189e844e7e26b1131c896ac4a6624e7122c88f2c467a22c51126888044312213d1078882ec40de20230fd587ccc3da21e6f0efb875fc39e21c8f0e0b86f2c36fe1af10d47868b4336a19270c62861e4302e17e10bca85ccc2dce16850b1c857042aea14fd0a58850e427ae1333095d849bc241a1 else 0xe1f5352039a6a0f86226109391c2128d860e290c322163c47c8cf58f2212e6467a8858f0d9eb702e63442569a80d10b3d78586084d917a211b3d63c8846cf49c882303e08e1b71ef500541cc10a6a863d08e8f939a2130c505bdc38f735e302b79ea1adb0e604c0399cd2e2cdcd9083c98a1b982b4690c5e7a408d34a62a7344255a50be3885a842585f1c42d42120460c611f43021ee1c601f04fa7a09970f6add27a1d4029e85a384898a5cc9090244c52e6484985a9e93e08c5cc90982313d2e452c9f53d355ba1d40a9e84758a6c2cd6d2330e6004f52433d41d258a1579e92a82714428f8815b0c23e1d164e28851f131ea4d8cd861241d23046c308f8745938a2147c4cb789f1ee0ec30120e29cc3516cb78f707056c3112115402b273442408c0fba806985e0843986344804909cd10902303eea01a4108730c6790094939a2126d20950fab802108e607ddc02542fa7a084239fb86d20950fa9e82108e7ee1b482543ea7a084239e2ce184e68f88d42004218e644420bd398e406184e68f89860e963d195087b1ce10914043d8e70848d42004218e6450100210c732480c309cd1f130c1c5c7a390080110a73228090055b0c63d2c8047a9cd1092402004429cc8d42004218e645010fa004218e6550100210c7323c28e70861f11404738423831c5a398e1eb50c7b1cc82021ee3d8e641010f71ec7322099a48853991244d24429cc9200242214e640e20bf9ab3d0f2084d5402b2214e6482cd4210c7324804a48853992402164429cc811c1080cae0070bdc39980c0421580e1913a0298a88539941f77085fccc2380c0420711201242024429ccbdc3998470180840e191384898a8853996a827347c884920139a3e442487ad421f473208087b0fa39904043d0731ce1f151ef700757141083e33702aa522aca212b70aa18639e930c5452e7084956ca435984246b6cf58134505e884d201813456e0884b20217b70c31cf4a748aae18e7a4ae0d669ec212280ae14f61092ad955290d6610954055ba0551799c21313da7b084b991a853d84235014f6108c9ed3d0425cc8d439ec211e18aa45ce1092add27a04d6610954055ba8540b99c2131c529a0bcb9924035b64f8619e95a4427900c9ca43704425901515b8618e7a56b6c0b99956442538a5230c73d24806b652399a212a8090055b0c73d2c806e0cf510924035b64e52399a21348067a88472038b73d44248434d4b9c3e235987d0846a029ac3e84245014d61f4212173a6b0861f11acd358430f8845e9ac2187c426d4d610c3e20212e60f86c9d832216b25cc1f19acc3e132763cd14b983e2b1e2e60f87ccd10c3e1f166a45cd109353a2f85f8f78b5706a1541c3173cb34f70f473443087b871e07c56a1f541ea3df8408439941efc20e60841f16cd6d666fb324d9836cbb965abb2)) else (if i<18 then (if i<17 then 0x2167bc586cf4ab3501a2160c0bc70588b93d7854f4a4f61082fa7a42b7860b88cb3171c30322e549a8618242124f86064f4b24211d3da3d08474f68f421191728d47a10909e946c3032e38608f8e9ed1e842327b084b8d1e203ec304d28f124713d2e347892388f93d785478a4f610a2fa7a407d8609a51e211727b47a10908b93dc30322e4f70c0e9ed1e84233b78608f8e10d3d05e33b7c58d3821253de2c7481090a1171c3032cc5c70c0c8b9526a1860908493e181e182b4d4064d010e18193dc30222e4f70c570261861d5c07860a308a361838a38434f6b80cade182e35c090869ed701e182e35c0661b0c11f1c8627a5c58f130c15bae0322e4f70c0c8b945c3154090869ed50191728b862a81210d3daa0390c45c9edc267a522e5170c550261823ec78e2924314db8447d8f148fd3daa0322e4f70c0da1618111727a70b0c108b955b8586090869edc2e2c422e4f70c0c96e181421a7bc58645ee161820c438586050869edc2e2c490c45c9edc267a522e556e1618248623e4f6e131e2e1823e223f4f6e17162117b8449f0c10ede1811c2c30227a45f0c0c83134c3008485c617c21197105e0859e9088934c30320c4d30c021213485ec78109112c2f042227245f0c0c8893d843478845c9ee18191727b86074f610d1e191727a70b0c129ec21a3c3a7a0870c1c521dbc306387c59109061d3de2d4187c59109061d3de2d41864f68322167a4e2c884830c9eb3d44244494f78b221a0c4442cf483716222167af0b8b1110911e2c367a519a80d1098645e3442cf5b80d10b3d6a0367a8bc4cf58f221194d442c786cf58f221183ec305c460f8b8e18191707cd430c101f42124f86080f8b8c3e6e0422e56b0c3502117785c58aac3e293427386010901f421272387d0869a8e1f421a6a387c47e9a8f0c173143e8434d464f4ad43ea6a422e4f70c0ca403e26d4d485ce1f5351e182e6207c4d8a4535243e2ad4d465cc1f08a403e26d4d484d81f088fa2187d4d4856b0c13619c5c304d870f8a3535191727b0fa9a901f535111727b86060ac1f136a6a42e70fa9a8c8b93dc303057860ab0e10c3ea6a305e0f8508415f16197307c20560f89b535213607c223f0fa9a8c15936a6a0f88f08c361830448430fa9a8f0c17311566a1860e9109e973a6b08484f610973a6a422e4f5e1421a6a527b4d61082b213d8425ce9a92413c226c56892088b93d7854d4a0bc9b021272427b0849c8c8b93da3d0849c589e97384242e70fa8f421213d28dc58c34212c3ea3d084645c9ef16842487d47a108f8b18607c08490fa10d1e191fa3d084b9909e93987d4d480fa9a888b93dc3032120f89b535217387d4d4645cad618195ac3051870861f535191727a70a9ac3e290926d4d41f1210c3ea6a32e60f8445c9ee18190926d0e69a901c93607c387247 else 0xa40ee1f421303608f0fa1084a2a8082f0f860f8118730b50fa10994041787c30430861f0d40417010306235a1f05a20c68ac0841b43e03860ac0c69a82a87c507cb48325358420e8ca9c1b05a0474d610983681f0b5084905c2d083905a0474d6109540417a6a30434d6108e0b83910c610c0841b43e03808cf8601b02187c4047b48108652e60f8c0acb983e09e4e2c1e2c10565cc1f04f21730580f827902a00c07c8848168215818d350420aa1f18150472e60301f2213280901c5868841f08b98540180f91094b9a2107c30a80f82d0c0e02363c0f91094237161446e2c26b6122ac83109e567a0b0254c5042518511802d501adcf4cd6d9eb0208f3141098e97160581186b73d308090d11b8b1262b3d04236b6cf41604a98a084c0738b0c5e7a35810999a4c567a084815816550e7a358a1681f021094408c0141f0d60b4504216841580283e0b4490dc585c580ff3d8424e2c2186b73d04256a121842038b486181c06435b8b73d04261adc5810f3d842510021b8b0c0e33507c08494781083e842403f860230d687c582f0f5a80c1f421c301d0108d587c08d10f5a842118470641583103e8e665010121b0c0be1807a3582d73d842710d8603883de7a35a109c1901f0cb1cc1f154043d84347883586f00b1918601900c07d0f921b5398400a240e214c1f00c0f0884c1603680c4e607c2d2213c1787ad4063783ca2107c40641dc29a7303e0301f22144d203e1953983e282b0da07e1085a8e66501012108d4304a07d0843882b0a31cd00ac36c7309e0f813186b0cb03f8601e832e7b1cd01181e8640321686b73d3d594e60f810a2147c128e3186f00b0541400f83ac300f79eaa395504e60841f23e44270e80640f83ee7a0bc2d1c1b06d07c08510a3e09472680eb9e82f0b451ac05c286180da0f79ec21406d07c0851f221094642e0301c8d022210728d892038b23d4e64900811108d0ba3d0b43c7bc5852010ba3de2c49008138b22146c5c7bc5852011ea7367a4901c591ea212480409c5910a362c8047a8858f121eb5006d1cc2c14158230e61681f473062787a1c81c8846a14f418c73042987a1c84205a87d1cc109e1e8366a11ce1f05a343d046d403981a87d1cce0840605806d4f6398313c3d0e41601f4730430f8e1c8188230180f82d47387c801921b8b0d3984f0420f8189415e350940841f161b0311ac0f82d14062730b45581083e34360b424e78d42502107c51010db8b486202107c218d8d4118860420f8c0ad39e350940841f193982107c30560853984f07c0f0c358ab63de2c02c0d43e3c360180e460706b036042100ab00ae2c0f9245c9ed50c304c305c44d40a102f191727b5c30c11a157061d860855b0c1d21c21a7b5c075c0ad82f191727b860645ca9550c3048434f6a80cb8e183a4344249f0c0e9ec2f12) else (if i<19 then 0xa00482106c1942a171e84706c714b982fc42706c1942c2160429c4189c0e1c50cbcf4179416a2185e0241f07732160b1069398652c8042fc591e931ee18163dc3028e30878b0e38c216a030e3c5810f3d84251011c78b42120808e3c5a10911b61e0420fa109431a36ae00f810941787919a0e81f73d03870883781d03e1adcf40e1c3182a19a0e81f73d03871bc1946a83a07dcf40e1c368cd0740fb9e81c355b07d4081481c09e66040d9ad83e06013cdc5823580e0630163483c81fc300fb9ea9873020700c02797430364420301f078341787adc07a181f02367a8843c98040730f215010c21335b0e610024026284a08e11b0c0d6e7a686b8601606b08e1cd109ead85600a9caacc5604308500d831c0447f56411c56842805e08eb8046c300fb9e8d640770433141d570e7a070e85d1ed501c80604242e8f6a80e4021708e30cec9ea83020e60f81804f401c05f158058d605432c39e1807dcf56d09810380dc13cb860044590f015039a213f70e3dcd41561858bcf4f05e1eb501b0206c1b429a21042104e094298363a45cc0e1a10f16155b05e0a8398584b403010c2148635a40d83b448047084f56c3703107e08c23873842850105c238c17c214a007c1f4480ec718d1580582a03e1683ce1807dcf5431810f3d0381b4a3782361807c35b9e982920206c08510cc54e615101581083a1ac0bf9e81c3c208721b415a210a8642e8f56102f221705e242e8f78b0e4021747bc589201810a4021747bc5892010b8a4021747bc5898f78b0b8b04398230f34f610943903e0461e69ec21328087b4f469643903e0461e69ec213a8087b4f4635866e180da0841f73d842882f0f5a80d40417e2d0f4956d178080e69682a0218428ab7a191f82305811c39c21428082e11c61a4040234b215039c213a8082e2c301cc1f0d6e7b084c0d8434c5043cf61081c38c5c3007f9e8d6842631d07e1ed0e2020a7b0841d911783b07c33439d3d842706423b4303e0761ce9ec21428083f0f68f101f2500761ce9ec21328083f0f68f10636180e61681f73d842718c0d810f3d842070d56c1f42fc30070279917d3d0c70bc1f04f355b45e1593904704c658b0030c0c348730b40be1084f3280801860705c0e0aad82c0a211c2d04f30260e68001f04f2a020e69cc10cc50a4098e1a41303e05e13cbc583c582d09006180ec13ca59810b0224e0c0279853c561ac1a43ce18e7a705a021b80210a8884dc782c02ac31cf5a81853856c3035b9e96403501221e2c20b00311082f0ec509e74b0c73d202f0b70900cf5109016b3d0d2020108544427042cf5108d8f73d44236040f852010ba3de2c490085c040e4021747ab0b8b16402170103c7bc5852011eb3d1c8042fc591e9240217010390087d1eb1e235b0da0a41f04f2a2f07c08c3985a8430f80ea01f0365 else 0x884c36181a2138b80072011ee0019c5c008846d4010c218010f9e9473387207c880254008e60c4f0860043e8e6128a1c9a84000470861f473383684212a000218e60e8e1c9e92208011cc1d183183e05e0830c05a8e673a50db000e1f61838b1cc87161b600181a8e70fa1085a2bc20e608e39c2128368e616810c2106260e4081e947307450c60f80e4210b186239823418605e07038e188e665010da10e18228086d0870c1140436843860806a398630624c7ae39c303e0b11cc189f1eb8e07cf1639831306346c16010c73062687ad411b4730b0587ae381f3c50e71cc189f1ebc507c08418961ee3d784e18318310431cd18f5c703e0b11cc1899e2a368e618c90f418e3d78b1ccb0f431b502c98f418c733c3d0421611b473062687a18f1e964062f16399d2b0698c80ac2d42f44276b6c1ac306a03e0f82a1c3182f18c0d81507919b8601f73d530e605cd5a286f0a8660d0e41b2214080f83c1e0bc3d6e0307d0e411b3d4421e4c192a282b4b48be109ac322103e1d82a831303608d8606b73d286008f0e4118540e6884e08eb8046c300f86b73d3a3daa08bc7200285d1ed501c8042e8bc74181f42103e1512d06e383e0630840f8474721b8ea020bc001d5b08e0aca42d204262b60bc3b0d0ba3d05e390085c158c6f25aa7a0be1096b803e0e808e9ec21328087b4f460be9e8834864a8a0ad2d42145e70d211d1c8230a81ce109d4041785e350105c158cc750e102045f0841d903905a0774f610a2f30650774f610914051e1280a3c202b5400f8760aa0c4c10c34a6405616917c213e180c61681b054079084e0e70c0690e61501e4213a8082f0bc6a020b82b18369a48841084db8a9cce0b010a219a41203b1a1006d834136e2a73348042e8bc685d17f161c8047a8bc720032010ba3de2c490085d178e4021747bc5898f78b0a40217400345e19008f59e8e4021745e3900c78563ac322101819c1f054383e0461cc2d43e45f084e0f80f85a87d084a0f8118730730fa10994041785e350105c158d4041785e30c816a9a82f84250b408e9ac21207207208e9ac212a80a6a25014d44a029a882d0230421941f17337160f16087160c89c3c031282168a56c178312ca76a02043c5840bda28212e61b8a1ad6973d05e405e10d21983682b0e29541097344a70421c58f17328690da150158712e6084e20253f16187194e0841f1238ca766a0849c5820bc2d6c1c02128b348189802d5014e1e79e8d6306808e0ae69021287967b348109133047057348109417b1e1a5cf46b021333d9a4084611d3304f0a40ae690213880e2d29c60866903e194666a0bc028d207c358ecd669021183ec3005c6b73d842682f0f5a80c1b0010aa0851b077301942c08510dc54e66aa01cc2a8214429ccd54039a160b008d10a73382018c3203986507c0bf9e))) else (if i<23 then (if i<21 then 0x6ea00a86683ee7a18cc02c488691a40fb9e863382f0d20e86683ee7a18cf4181f4210c6150b6181b34507c1bc2a181c7b398d53a41e417f3d3c8042e8f472002c9d8358606c0f8378543b060e20843c04129d2e7a18c603a5cf4318ce9063e7a303f51610c734b41b8ca0210c7118550f20843c05428c60420bf9e8632d8646c0b4378542c804429c47c590ba3d1c8042e8f4720038f420d98303e0de150a887385c50ae18d3998002c3886d8e61682a021842850105c4a020b88168364e6084245c5442705e0846af3d0c65aa01cc108554e6884c3181b07919a0f817f3d38210120d83785429340381e4e2f3d05e61ac02c10869e7a18cc0b431840046122e2a213c8042e2e2c85d1e8e4021747a39001c7a1900885388f1e8436a648e21683183e87d0850a021f4218011c4aa021f4218011c4aa021f4218011c4a318388210c70f811982304a08e3583c8cdc300fb9ea4250470ad8639e8d630461bc1286b0650438601f73d484a08e11b0c73d1ac60c6110108d60758601f73d4001b07908d8639e8d634a78728842323e07c1e0ea020bc3d94e4e3dcd43c846033cf46b1e5383e87208d9ea210f2708c1cc3c25a0a8086109ead86e5a411839a5a0a808610a7612390c60bc1b07689008e10a418c2108eb483b154041712800cd214e1e41873d1ac60d0cf4238549a4884d2010ba3d1c8042e8f472010b8aadad208c1cd2d05404308501a69e8470a8b4a10994041710210d5b0acb48278470e61682a021842a8a40e431aa7ca00d82a03c84290a41a423d3d0a8b4a109d40417884382e168238c2505606c34b0c73d1ac718a11b0c73d1ac590085d1e8e4021747aa9c92010b8471c8042e11c7201538a2363d148042e11c72010f881f06d07611e1f4210947d840fa002a703e0e61f42144005a50fa10914041787d0008a020b8471a800ea7b0c8842a04707c5ccfa9c2383e0565cd1085a385a08470430f811901098687d0846b14178200381cf0c473302f0b01d86a03000b1ee183a49cc90f7002341a3d3a580060bc28d810c3d7a508639983183e78a08e3847305f08500d810c00842f4a399839bc504700239a2f306306e07018023c7b084f8028f09d3d868438f4c71dbc309cd074b000940600103005480010a21b8a9ccea03000a1b02147b71539a21303640008510dc54e668687171ea21201c0545902c03ec7a650170b000c151640320fb1e971f621c7b9cce96183280c00246d5401182f0ec5c7b8d0e2e1825c205e2b841cc11a3d4429ccd54039a0004688539981863d3a58608a001be0084240ca0841863d07c714179ee2c364e008510a7305e7c7a1941f1c50e60bcc886e28214000d939c2f38210b58f418914060012210d20be1020083571539a140600106305e08d39a3db8a884f0bcb22008357153998e2e00123d38b8006 else (if i<22 then 0x1747b7081f27367a618d16811a3daa0884c125025c20468d8a1111085a1a3d29b7091082363c61aa45f1ef1607c547bcf56101b2204046d081500b28c6e2c0f822131f71605c30434f6e171647a355109caaa04b8408d1b148fa3db840f910b1e305a47c0f80d902d22107c8f805971ef163b69cc98f46b05a180ce2c0f89a121b23d0460e884d00623604642690318f221046444c24488e3de2c0fa10980a51e47a06c845f1ef1607d084a2469ec2147b4793998637160890841f1448a1747b4f463421a3c722f8f4e171607d084c2450ba3da7b0868f1b1e8210b430180521081fa3c5c7a76f8b42131c9ccd4f6b823d4e60e40e990248644208c82191ed3d03a44088861ca3604658730301f27367a08cc8f41f01c0460e8a81110c3946c08ca0e60603e442c7811981d03e03830320fa1f236c6a507c0642d0d9ea7318c16880642d03e87c8db1a991b03a0420708cf539b7090c40421602d0f8b03e0732191b161f63507c0848cf58f27390c084acf4630210b4467ac7a43021203e4e60e460f80585a180c07c0841c92e12714420842b45a04c74e208423dc509e545f7082387709e54cd708245c509e506c08510c5a0da50d669c1b0210381943506d0b4906c8861c8210561dcc0dae28214420511b065398686905c64bc3503e0b4070a808108364421b42a1938847b0c13c88bc3104f183e0281941e10c343d118642e83868081f26603813ca1181b13e054084b9ec524281840b856f3d20de08c3181f73d1aa6ee1c7b9af1805a2b79e9c118730320fb9e8d5303d08c13c3b026283da841d83704f2bc20ec09860842403c0dc407c0846af3d1ac567adcd9082d67dcf4569c1e06e09e315a0b4430a4321747a408d21840f7280730544841097109e09920f80e53d0d20b42798348470e70bc1f0263427ae61a78c02ea7a13ceb4a13880381710510a41a42d04f2c660374002d05209e682eb16138c4305adb000915402795a1036ab20bc3704f353db1d5cc15058a7cb179ea001ce3882d04216a10989f42f0e6020b9821d8a4851dc3437184e408427ac5382d0c60841f73d1aa6c2c45c445c93a8619172a585878589389a14c5100698a205b708445c9e8391c8622e4bc7c582a18250962889ee16171622e4f460b59e881f0214429cd1f054306d4437141f02147c0c4e85d031a71a7307c086e2a2147c630d05e1f0c0e0672c98f42985609e0f900f02406e09e40e75413982107c8851f1e330013a41cc2a82109e0f900b710867c300573982ec7cd41261a0bc3e1e02e6619f0c05738a682e0b4e90e331d2c7a02f0c05738a706c88436dc507c0851f031463d0900f8e2e180e605036a03583e0ee050399c505e70ba0509c8210a850da086e283e4428f8c61a1f4061a1705a714685d139861d1642e8f874591f22718200880f86b73d0c6 else 0x251220840d900f82503607098f4e101b07d86010991ec1119b0840fd1e371687c08210904480c0320f880f806019038407d0f80c8c0080c104a0180642d112300c0a2367b0f82d019200c03a884600406081f061f33d032084800406081f024100c03406c60f804001183e82f0f96284a283e00202025101f43e0da5c490f82984a183e87c1b406901f43e84203480fa1f04a842403a4f40c8c0e23d0e50f81d141343e3054d483181f43e8421cc2d182d03e87d08439d35343e0421cc1f5352a8087d0869a909e81d032303813c6443e03a518c0721b13d03a51908f61084f18d4d4c0322d04f26c404c0742d0c63436c7a16888f61084f1914d46b1a2d03e09e1289168b983e18c619008427a3da6a601916827936205a09e4d81f1210c3ea6a35888f56143e03a406d0f80ea21201c14e0c61f01d284a06235860869a83107c40180b09b0d0f93607c35000761f535201c05602c1f103743e05e304c10b409840ea0b9730b447840984dc036d35183a0a816861b41d0311c180740986a021085a182304c0700e900e93d032304c1951e83a201c04c08c1d1011a3d842098813c0e01d18c40461286342104c50384f60f81d205a07c09a1082328210380e86a0013421183a038084707c1d17318260caa181d101f43e03607090f80d83e1c3e07c06e1c900602144230b40f80dc3e223d87c3200d900380c07c307c103a06c1f618042587c0f80d8c0602144230240f84b6c1f4214420e4a0fa1f421442168a0f81ca21183e4420e4606c4301c181b07c8841c929a83e036367a06c2d0d9e9730b430360f91085a233da6a1680d909b61844207092019e9736e04442cf42d0c1cc8067a8bc80fb0c2211d3507c88461451085a1c8067ac7910922303e038367b118e1550032567bcf6231c2aa0064d21810b3d88cdc0acf4a8550042467ac7a610d6042588c0f80c85a244607c0842d1010c4607c1686b159e8c60b408480f80e099ef3da3c47e10959eac5a3c47e10948fb3d6a12188cf5e171690c47cb0841081c191f67adc243108f8586a12188cf78b28623f218a195b80218424784354122558425a3c0f88fc21203e23f2199a908f83e66a318847c1f48666a41120921083e2023e7acf41d1011b3de7a0e8808d9ef3d0744046cf79e83a20dec7b0841f1648e66e7b1cd1e87920cbe2c08c2242128c6e2c0f82242128c61974f610a3da3c9ccf8f4edf1684263939984201c1120300c940633d032367a0302d01920c667b05e1ea730b4667a031e1019200c4420c060319e81918c61970f428a21287422f8f78b03e8e66e7b5c11e81b221747b4f43a4730b4318f8f4630730b440e885d1ed3d8e75c0c08d10a3d8e6194a0329ec730e35c0a31b8b03e088418d0842d45a47b541399c24a04b8408d1094630c547b08424d50304940970811a3629)) else (if i<25 then (if i<24 then 0xf8420c08cf6108651b3d842a380c911b17307d0859a959ea36e2c08610951081c032322fcf43187403251b74f40e019237000202064f5b833d1a21e7a07031874032667bcf40c8d9ec3d184d403c959ef3d7840649cf5108301b3d87adc05386f2b3d87ac780fa212f3d67a06460f91f079180850c0041090238c503231854f40e01924c518acf69e819280108e2010a0023051200888c14460708b93d8e38f78b189ef3d34e064885c23077ae0442e8f610d3d18d540c072e1048086422fcf4178d5032514f4f6e101c032567b4f6e102f0325011708008c1701912c567b4f4628192a21e7a070178d5032667bcf5e1019233de7a064631910b3d82f0f4613503c3d0b00bc610d60dc6e7ad419e819233de7af080c909e86d22e0708cf4184211a2126802010901082526807080c41d03e0384500a18008082001010200211c505cb8ac508e47840bc0080822d27840a823900e11727b8f78b06d313de7a7080c911ef3d5855c037140e23d8434f436d703028ae08003690b301c6040a488f610d3d1ac1b6b81838e3d585c58e9151ed3d58436eb806e306dae056c1782a293de7a0646070692178435402c186301c22f8f78b13d30c61a48f610d500b0622e14c23dc20f051a49c71ef163a45a7a1b4180c36a3da7b218181414c860d0350c0869e8d23d3d113d7854f465c410d3d1ad222f0f5e153d2aa727b0f54353d28251220641090108250320708cf610d3d032084acf610d3d032084acf610bc2a7a064109818025038084807048f3d032084acf79e8191b3de7a0646318108500ef0f5a819a833de7a06480841871604a4042cf436c3d6e0518c34810b5087a160ccf61e82f060467bcf40c8c04286002084802000896280108e308e56cb8877200878400470849a00804242cc1b4b88c8bad208ef08299436a8605231978f41f01c0a25e7a4f40c8c0e21719614610979e98e048070831a0fe3d3b7c5a4311f3a3d19635828c21291e079478609543021048427b4f4120d6298e48e09084f60fc3d2e2b168f1917c3d2680f084f5e153d048426908410825213d83f0f4b8d1e2ad223e4f60fc3d785478e4f60fc3d50c8be8f1b9ea5047a1b880701921747b4f78b4213a1747b4f78b032842358e0730c40009e168a59836b7080186003980e05380186027940e02b45e30e34f40d81c24db0ba02010a212e3d0423540d9053d3db8406c0e171e9c2c300f80d951edc214f1540d9416cc50100851096628070100bc88f662a1807ccf4b4f6e123d4420bc0d9816cc501008510951ec0698b8601f024363d5b770b0c23e90006c17a110886036354806c4301c1bc20368f910e182c8067bcf4d381b28c547c06c6a90d3c8018a11c0d9510b3d1acd408cf43702f1bc247d86110924033de2c0bd109428a211ac367a884178f9ebc20368f910e183 else 0x211707d0bc36909ed3d142f064064109010b3d8435c29e819302167b0869e819282b002205600450bcad8772e241960bc8b93d83f8f78b1f9e93d03231968f69e8c645f084c8be0fe3d3b7c586b11f3d1e0d1e0a2f2e34786a188f51e19170390bc6a8192b3da7b7080c9015dc2002305c06443199ed3d1a4064a4f6e133d1a210434f6e133d0326057708008ee131e102b002205600448be0bc2f2845c4a198159710da4784004158c8b93d45f0bc03949ea8685e01c84f79e819182f18a8f610d3d45e628a0bc008c630c542e8f610d3de2c722e5150ba2f85e505e4f51eb3d211728a8bc271217a1fc7bc588f961791f63c385e0846a86e208647b4f6e106e282d057709108212a1827b70817b3d282d057709108212e189017098f12400079a40ac9cf52851e47a06ca0bc48a3da7a8be10d1e389142e8f69e8c6843478e2191ed06a7a8bca0bc00884321747b41a9ef16310642e8be4342f2a174000bc14124302fa0c8f59e948322f85e04c921a1793d63c40562100c8c1f43e03230020ac40fa1f019182b0b0207c187c0f80c8c0082b103e0bc287c0641f100082b103e05600460f815801183e45f05e17971283e0560a117c21283e056f0800908b83e85e1248f081f02887c420c0f917c2f01451900bc9ec36c7a568c4f41581918c88421506343e45e618c8f6108541914d4c0ac2a45a26c445f0db1ef161ac5ccc5ce2d03e182b0a91689b102d03e10540564d8279117c36c7bc58c1141884188417973a6a38300be9a8de1031102f26d4d47061403c2a6a450c0bc9ed35202f22e4f71ef1604660564f40c8f9e86547a0e880bc11a3da7b085179a9ef1607d08411941791727b07f1eec2e2c6186b246353de2c0fa10823323d018b080d901788947b0869ea2f310905e004631844a1747b0869ef16382f22e4f61b63de2c622e4250b82b85e585e0f850bc1f00705641001e4318c6b33de7aa9c3c94b8b3d05e064936d9e82f0f2467a76c1082f233d63c358109153cdb67a1e4808431899ebc22e20bc929c10b3de2c467af086a86e05e594ecf4edb1e042594ec199ef16207267a1e465c41582f03242e60f86b33524a767bc58b9821282f94e0859ef162b3d38406417919e9500320bc8cf4e101905e467a358e282194ec78c0ace102f032467a35b8b4a704250427086b4a72b451aa4f71e821c305e7a9411e81b20c627b8f70c021292dc7b8870c131e9c2c303c7a084188c6413dc7a0861b61830c6c7a0849ec36c306c7b0db0c173263d86d860c1104493dc7a0861b618300c47a06c631a1b63d2b4084a31844a1783f4f78b23d3e3d3840db0c104042103218c8cf40ca1f842467b0840ca1f2171ae1084108302a1f6a10842c119e8648420c010959ef3d03287e10950fc210ca18c8cf638f1684287ca87d9ebc28e3c5a1098b8a1) else (if i<26 then 0xc3183122210431c418903182f8420c09cf43c93d032418c1a4298d2273d0f269c1810368290d2322fcf40e0790e8064c21a9e8010c6418ccf69edc20f2064c0bd9ed3d0024a7a8843ca7120634420c0688583421a7a405e4f434863233d8421a460843183e1917442c09399031a800021c4818c21880086914210c60843891690530d235b61b43482120010c628434f4445c9eac500e426845c368c9ea8600e327bcf4d3879032518c3150ba3d8434f4c516e280119454421a538906a86322e1a484f79e9c20f2064a8f79eac200e40c68f69edc20d2354c18caa85318c61aa4f434909686915a3e7b709108cc30d2c7a318869f9e879060424f70a5386900e534f8f46b0c9ef3d0f2064818e3886d053084a2271e917062410c85d1ed06a7a50c60045219108694e24e7a2103c8190e6507d4f431819207907d0f80c901f43e03230f34f510a7106054430f81f019207987c0f80c911080aa7b1cc8a0210adb0c60c4a0fa10863062407d08431831242104218c388312ad20a708638869286d5b708540069062607d0843183121178431c431908b84987d08423c71303e784a9e10c710d260150f89a42180045c189c1f00a87d08404471373d0ca8f41d1031a3da7b1cc11c2130db27a118630472846e7a0f8108c6283108e3181f12404c200a367bcf463047233de7a318239063047062309435816036200108edc0b811b817067a318ccf61ef3d14e1e4ccf61eca703e884a2199ec3de7b29d628793ca707c8f83c9023ac2002084811c0088028423ac2002084811c17801182f00211c60042389628475a40a8800425082502f0540f8811d61001042408f56d690012047002200211c40042389402c208e10c811d690431847086208e10c41496904709e408e10c445c23cc20ac422e11e610562001094200212840f969047088407c12823844205608e128645c610230944e7a1954323d074584211c108d1ed3d04708488f69eaa704631a109b9e823842318d4f553c2121c2b841c71e92e123ec7a347b70b1e8d1edc2c7a331c70a8f600223da3d800747b00098b51ec003a3c717000cc31a7c00347af0b000ce2e00123d38b8006f0b0008e2e0013c2c00230c8f7000ce900d11c586a034616a1b600182386c0e8608e1b03a1bc286c08e10e18282347a0c610e182c360460e8608e1b421c304046f0a1b186843860c8d018823074430d0d81183a21170c70bc7301928010570bc64f5b807967a4a7a0bc3c8d10f3d05e18c73019373d67a0646cf61e8c26a01e4acf61eb1e03e884acf79ebc20324442c1b9ef16233d87a21837939eb3d032307c1e51f0c8bc2f1a406483186933da7a064a0ac00881f13605e38e38f78b03e05e084dcf49e8191856e7b54153a3445e605e8f610d3daa08bcc0bc218817c1780019c80be0b82808e40505212d03e else 0x1c500e97a0bc3d4e260da9790fc3482e194c61a1e80719864bd0f432812298687a15c0911e102a08e13c845f9e8d603801c17984002da7a01c6a9417b3da7af0ae100733c200e0b86b159ed3d00e314a01c170943028a7a358e11417b3da7af0ae10073007a7a709e1119ed3d78401c2d141684323030b0461800d8c118113d0da0a06618d380705a447c0b5e100721c500e1546f08038571a3e05af0803911f02d87c0a48886404db06240d2004318d3880144218c83088bf3d0f2064a30a9e8010c640f3cf40c8f9e9c20f2160845f9e82f0f23980c9853d3d00218c83199ed3d0f20bc0c988b9550c6303445)))))
def minel11 : Packing := (1757,4,7,0,0,17,0,mined11)
def mined12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x3ffd8548164fff5d520593ffe5548164fff68d20593ffd7348164fff54d20593ffd8248164fff54920593ffd3248164fff68520593ffd8148164fff5c520593ffd5148164fff4c520593ffd2148164fff60d10593ffd7344164fff60910593ffd7244164fff54910593ffc5244164fff4c910593ffe2244164dff295925937fd7264964dff149925937fe2264964dff65572592ffeaa54964dff6a552592ffda754964f7f29d52593dfe7754964dff64952593fed7254964bff680525937fd9588964ffb54a22593feca588964ffb5d622593fee5588964dff5d5905937fe5564164dff5c9905937fd5264164dff149905937fe2264164bffaa9805937fda960164f7f9dd805937fd9560164fdf955805937fd9260164ffb889805937fd9160164bffaa970592ffda85c164dff661705937fd955c164f7f5d570593f7e555c164dff64d70593dfd735c164dff64970593fee225c164dff64570593dfd715c164fbf61d60593efd7558164fbf95560593efd7358164fbf5c960593efd5258164fbf14960593efe2258164fbf5c560593efd3158164bffaa9505937fda954164bff6a1505937fd9854164bff69d50593dfe7754164dff65550593f7e5554164fef611505937fd9354164fbf58d505937fd9254164ffb889505937fd9154164fef50550593ff98054164ffe5c150592ffda74c164f7f9dd30593fee224c164ffe60130592ffeaa48164dff6a520592ffda848164dff66120592ffda748164dff65d20593dfe7748164bff695205937fd9548164fdf95520593fbd8448164bff68d205937fd9348164fbf58d205937fd9248164ffb54920593fee2248164dff64520593fbd4148164ffb48520593ff97048164ffe4c120592ffda744164dff65d10593dfe7744164bff68d105937fd9344164fbf58d10592ffda244164dff64910593fee2244164ffe48110593ff98780164ffe61600593ff97580164ffe95600593ff98380164ffe5ce00593ff95380164ffe60a00593ff97280164ffe54a00593ff85280164ffe4ca00593ffa2280164ffe60600593ff97180164ffe54600593ff93180164ffe486005927feaa65d649ffaa9925935fe77649649ff6a5525927fda914964bef690525937ed9288964f7b9de225937ed9588964fdb956225927feaa64164d7f9dd9059377e5564164dfb889905927fda9601649ff6a570592efeaa58164f3f9dd605936fd9558164f9f95560593ebd8458164dbf64d60593eee2258164dbf64560593ebd4158164fbe601605927fda9541649ff6a530592efda64c1649ff6a5205927fda944164fbe581105937f99880164efea22005937f99780164f7e9de005937f99580164fde95600593fb98480164dfe64e00593ef96380164ff68ce005937f99280164ffa88a005937f99180164fee50600593ff21180164 else 0x910c4e6e2c431f2c55d407308482b0e6108e18d42211cc3e2ba4a84430c4e6e2c7b1f2000d402f0847329011f442e943139c7a7f083d1cc212001a8042399080886189cdc58f63e3801a80423987c5f08730843e207ba863d1e8e65122d20847320aba8042399016d40211cc8010a5628423997501cc210f881eea18f0e61f1527517500f970084da863d9aae10c67a656d274183e559735642146e0e963ce2e6aa84319ea15b0f945ccc2fd657308504005fb863d9aba50c67a84f759cd570084aada4e1f28b99eb2b98428d413d5cc21262db86a19ae7a10995b0f952ccf595cc213900a2ee18f66ae2c319ea135d41730843e2eb29aae61087c5a9c2f5423da1b165c1c59653d8787308770d431e0fa35b0ab40d5e6aa975402a41d406a79f4d4a960d262a457470a893d0bea06f3fb27c6cf249d7739226fecd809a2f3332636cc2c97af2d1a573caa6943f272a4b0c90c913320723edc7548deb1a32320c5e28b4314e227bc498889b0fe21c7c30884ef07c20dcc12881570069fddbf347d6ef8e9edebd4a79d6f281e2abbd876deec91d67ba70744ae7b9cc7b94e7206e2e1c40b8226f86dd41b73b6566b62d4d1a6fb49467f2ce919acb2e66536c991911b1c4628ec301821af9e5e6abab971dadf05b36b519673ac9c587aafc95b5aaee551ea8c14eda97c5226a321434a80a4f569d81380a6b64c9a97b92d1a52649b691c9209a3be46be8c29155a24c439e85c108da0f841328098fed9f683e267b20f399e283b927580e8f9cde393a70a8dd69b4e35f269f0d1399d232aa63b0c41982e2f9e5d98b8d96a82c9257a8ad495542a3a5320a43942827ba4ec09a8931025b24a109269216239645b089590ea213e41788098fd21f223d407788ec41d0638b87008db61aea34d06798cd0191e30985f28bae16c62c1055c8a5013ce26e849e88c0109a20803fe87c60ee21ce837786c20d2a192830985e60b5e16082aa852809e21310246844c08160ed81b0830c056e0a0011581fe037a05c808e80e6015e0003ffeaa54964fff69d52593ffda054964fff95622593ffeaa60164fff69d80593ffda560164fff29580593ffd7560164fff95580593ffda260164fff28980593ffd7260164fff54980593ffc5260164fff88980593ffda160164fff4c580593ffeaa5c164fff6a170593ffda55c164fff68d70593ffda25c164fff54970593ffda15c164fff4c570593ffda854164fff69d50593ffd8754164fff61550593ffda354164fff5cd50593ffda254164fff5c950593ffd5254164fff4c950593ffe2254164fff68550593ffd7154164fff4c550593ffd2154164fff5c930593ffd524c164fff14930593ffe224c164fff60530593ffd714c164fff48530593ffeaa48164fff6a120593ffda748164fff61d20593ffda548164fff2952059) else (if i<3 then 0x72c8b410a673886d215a3d16a183173d48e4002e62d5a5280941087c9348c511973884d60f8e1f47a10442e92a0e2c3039a436716218f673861d23b0c398411f47a1f442e94e617a8378f8738f5d2715509cc21486ce94430c4e71eb8a75402074a3e1cc3e8863d0bdc59ce1860431086d1ece6e285e71cc2f0823e8843e862738f5c55040e2c430c3a4a80b43987c90bdc5d421808c211cc3e40c82d6e1a807d1f4439e85e956c3e51733151730bc21403e2d6e11f07d10da50c67a9a18725162f0bc3eb497008524708c1c8e7b847d1087c694306b67ac8f673169508863e34a18cf52ad87ca2ea09eae617842834b3d0bc61ed0c3927a1787d692e010a466a18735153d8bc2f0fad25cc215d0c39c5e9eda4b98427198521cc394f62f0bc3eb49730856404e7108ad1e8b50c67a81c8395ce2fb48210f8e39072b9a6a17da41087c81c42fc7b35b4970cf4ea305f8b6e18f66a6b1a59ea42f1c839863700fa3ecf4d608551e8b4a84319ec4262023d0e618cf62130e39eea19aae010982034873dc23e8843e072c58633d5ab6816e1628a6a96661f2e62788210b0d207f708f83e886c58633d4d4e3905e2387d62ae010a02f238461cf700fa21168d6860c5cf58ad8e604666b98b42b0428a9e738863d168c58633d411c2b05e280e7b847c1f44362c319eb15b1cc004f4470bc3eb157308544047a2b4e710d8a17c7d0c67aa0f6a71c93d0fac55c02140e50c1a5b807d1f58b9e842956ea71cc2f4f4470fac55cc21554e1e8e762a7ab9842756ea71cc2f070004f57302c5a08562b05e406e11f442e94319ea6a7a3a738f4800e6183173d48e5692e6250421f1aa71c9734d43a168210f910c2e7108b41f171611b70c7b35358c5cf508f6e19ad8b9e84260bc5a8606411a73884d60f92158b4a80e6ab0421f1e3d169598f883205f0c18ba84e6118421f242b12350084730f8c1eea0108e61f142f1921807e738845a0f90158b4398421f14808f6180e63e2c7a1b46b39e3c2d07c70bd86518215c2180f950cf5210b8a1f430b867a6540210fa1874b3d331cc32e61f3a59e85e70bd707143ecf42133a4c32e61f2b39e8427479737143ecf42133a41087d0c2e19e98215643e861c5cf4ca82acc32e610ba41f4319ea4217173d0bc88f2e6e907d9e84260bd8e5cd060fa18cf5c5426a10ae61f11465cdd2714215403e3eb2b9a6a10b8a1f182f5cd35714210f8cb9a6a1cba41087c61587308462b07d1eea039842696e2783a00c59d29cd598845a562c215a5628e6109ad20bc5a1cc212e6613ee0431a42d042756d0e4003d159734f5211693b83a58f6302d18b9e9e1656c46439001213db157348544342c2b6e18f3a59ae3162e7aad40730843e24b62a89ae947ae289110c3139aa11f311696e0e15a028f4558627374a218f988b4b70747a2b else (if i<4 then 0x5ce730223d0842f8603e169c5cf58b803210b8a1787c6a39465cdc50bc5435a181cc21168d20f9ab984639c30e28b4178421f2550a38565ce181cc2f0845a0f951e87c10c319eb8b109e3d35973542180f821cf6214c7a10b8b9e85f109a3d5cc2f0e6180f821cf5c588550c06c10ae71087c6319737142f0d950086210f92b9c30e906c10c421f1c2f081733143a0fb3d0711b84439ad8ae904205c301f67aa0bf70885731285a35a18084190f8c5cf5b1e88d1085e0e0e6109acb847d0c07c62e7aedc05688573cd42fb15500840b0fa18cf5a1d042e967a0e163d15a2116873b14210706d8f83e5c218cf5d1ec433987c108b06947c62c30e967ac8f486885739cc200c2c50723e0f9d2cf42f76e0b9e6b62c30e907d9e84298f5739cc3e0bc1c336183585a3173d085b1eae73987c0e58b0c0651a8b59e842ca9c2f8840b0863d5c0730f8c58633d647ab9ce71094e058431f07d0c18b9eb2a78f5739cc2f0fa183173d168215ae017ee110c30108b40587c988535b48211cd730f8f108422a1ac3987c2d1c56885730702f034314d4730845a0f9953ae639046178389a8b41087caa9c0b086211cc5a0f8f1e85f0c0b41f0e610c7c88f4c61c85a0bd590f8218f931e84199ba41f0e71f1e3d085598f85a2c7a6b2ac39430a80421f47c90d80c0842f8f85a347a39666e907c10c7c71c82f0840c0f85a8f8e1eea0e90e610965b89e0e801d29cd508845a486c0a0420e47a3a34f108b4969e271cc140841c8f43e1d2211696ad822805a4108909eae690d8aa0bc6416b70a9e8615b1e35b35c603e3573d72b6232848720153ae6908903984362e2d998dc27c0461c821dc31e0fb183185a348c5cf5856ee18f66b8c1a462e7a89ce21154d28f8c5cf4e334a01ea1c39a0010c302b5a490ae62d27a27bf703171ec60d6168d2cf51b806d8f66b9e98a179c734002f084610f93d12173486c55ae69094e2aa7c62e7a73153d0e5d2cf4a2b18a9e8b4e967a685ac54f573484554fb3d74923309b0147ae2c421b0ab39c311f3a4c61873808208f46a9163e0fa2174a730bdb2d8aa08ba51ec421b09139c311f38ac1995011811808208f5d2154730f9c5862738863e80ba240431e8291086d39b8a17a8551cc2f0823d186181203e9ce218f9c5685e0f8b5a807d1f0c710ce10c67ab49f5018d4514c73084f53c431e8b4acce10c67a818d45b17500bc691cc2141011ec4362c7c17ce10c67a9a9c635485ad4073084e4028b53c431e8b5384319ea6a70005ad40730843e391c6918a23ee039c7d1087d614306b67ad23839dc0a711a3e8843e9421835b3d60e41788f694a01f58ab8042956c730f847b142f5ce590852236e11f442634306967a88f673886c515a3e860d2cf52ad8e61787c23da562ae72c842a348c5dc23ecf4d6084ead8e6238a5692e else 0x13d5cc390bd210b53ecf4d548aa2318a6b67a6a9b704f75063b1e15973cd40bc61503582a4fb3d7a7b1eae61cce6d3a4310d0c1785a9f47d9e9aaf0bc69714640fb3d18ce17ea18f30ca34e6109ad380321f67acd431e1a42f86273085c59c0190fb3d60e210ba59e8c6534a3da383e084588f8d58627074b3d647b4730c398421858b1f0c7383a41f67a17bb50c7a73748219c0190fb3d484234b8b9e8c65354cd0f8218f6708605a7173d514f1ed1c6b2aca847c31842349ab384301f67af244730c23d084c89c1c5cf42f51aa4885e0447a31843384301f0b4e2e7ad0bf5063b1e714730f8f538463185ee28b4398421f2770c7b353084a0861811b3d3595b81a4c763d9ac302307d9e9acadc18ec7973cd4d2860460fb3d3597b82e79a87d9e8426b1f7063b1e5cf35128c5860460fb3d35991ed1d3984262c7c2b4319e9aca5c37063b1e1183e358f53ae639047280b46b0421f2419085c50fb3d0bccc730cb99a42b07d9e85e88f68e619461cc2f0863e35a180f97034b3d730c398541087cb81a59e85e95cdc50fb3d0bc21347ac319ab9ce66b07c178b46967aac842d15973065500843ecf42f419b3987c10c7a694302d38b9ea9730a8218603e34b3d0bd11e922e2ae739c301f05e2d67a10ac91)))
def minel12 : Packing := (249,3,7,0,0,15,0,mined12)
def mined13 (i : Nat) : Nat := 0x8b706947a6b189eb150501e958e621b847a6a3e8c3498b3d681ae11e9ac614f3d62a14e3d031cc43708f4607c399eb158a71eb16a0210c1c07d3d48f48c73b83498a210c1407d3d58f50c73b80bc4218690fa7aa1e862e1501f4f4427538f4e770108f98a189ea47a18a81cc423e316c4e0e0300801162b1ccb2215dc1a51e62cd630509ea0b60e01000a5501e9cc4290b116e11e9ac618b3d416c4e0e010f48b500c1cc423e5d404218398f47c653940e01e628d47b70a847a6a189eb6cfd259b119e08ba9694c195827541a700b511d16a1e8007ff5c964ffea92c9ffc52593ffc44b27ff60164ffeb82c9ffd50593ffa60b27ff48164ffe882c97fd97593bfceeb25ff64964ff7112c97fd90593dfac0b27fe80164
def minel13 : Packing := (17,2,7,0,0,11,0,mined13)
def mined14 (i : Nat) : Nat := 0xb38280f1a8c1e9c0ffd64
def minel14 : Packing := (1,1,7,0,0,6,0,mined14)
def hashminel9 (i : Nat) : Nat := 0x90d0150b00002e9000000
def hashminel10 (i : Nat) : Nat := 0x1207c000080b634e600000001e0e8a03060d5842500fc15140000411200010032207800e400000001005500ddc45ea0620001810e00000001e0bfc126000000000000c0d260a7cf1e0001801b803e000000000001c070642160aa402fe51fd46cc06f20080000000000000000411600000000212020c200012ee60000000000000000e01c0000000000daa0a1c0fa00b3c0f7205114fa8439e028e0404058c0d1005f2091a04264598103004ec40320e68106000000000001410800012104e080a43b809ce01fe0d9e057750bb4cbc0652044c4222e54442854d1e0f3810a608de0d7003840ac0000402a0001e4320000e0b00000d50ec0bac124a05c000194bb202020fe2011c4e400000000000120002072000120f9a118a0dec0b86025c012006c0000005a000100940000000000000001442a604ac0880000e0c80001c03ba45ce129c0232053000e0000000000000000000160c6a0045410a0ee44e00000800260820001a06a0001d519a0a4a04c0001c067802c00a8009ba4640000c01880b414cc000000000001e086000100cb151f0069c0f00000011a000061006016000100c4a08fa0987404007e00000000801400000000000000002075e097e07b20ae20e3a12200a2210d0ee800000000000000f5607600000000000154cf40cc0001611040c00000000000000000000000000001800c34ece45a0000000004e72e68c00b411c40eca049403c0114445260ea404600000001441e2036243580358ee000000000646280ce0001c09220276ed500bc0000208ae11fe0606461e0840001c00620e0809e000000004030080400050080c000000804000000004040001008140000004020700008000e058082a0004000020000804060000004000200824000202020000400000000200000000700000020000008000101800000600004000500000000000800000001804000b000100202
def hashminel11 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x300700000000600300100000200e00000300001401800000001600100000001601100500d00700100000000000700100000000000800002200400000500100400100300900200000000d00100000700c00100000300000000800500000100400100200601d00000000200000800000000600e00c00802500500600001000200000100300000000300200000b00000000000200000000000000000900200d00100000300000300200200000300600100200000001500000400000200700000900000100401100000000202500001f00000000400700200f00000000000000200000000200100900000100500000000100000000201f00800c00100500900000d00400000000c00500100401400400000300b00a02a00000a00a00100100000200000400000100001200000800000400000b00000000100a00001200000200000300600000200000000000100000300400600300000000000000500000100200200000000901e00001700000200200000000b00300100100100100300500700000000100100100100200200101000002000000000000000000500300702200501500000500000100400900000300000d00200000900300800000200e00101b00900000400000c00000100000001f00800600400100200600a00300300000000000200100500500400200300000200000000000000000000400000300000000400100100401100000000100400901400100500000b00000000200101700000000002c00000900000700300c00000000000000300000200a00002301600000100c03d00b00100500000100100500500000300000200000300300300101400100200000100000000000100100000600800000000000000000b00201601300001d00300100800600f00100000600300000100200200300700000001b00200700000200102800600001300400e00000000100100000b00000300200000000400100400b00000302400100700100200300000c02e00c01300800100000200800000d00200100500600100000400800100600000000000401400500002600100000100000300100400000100600200100200000000100002100200000200600000e00200000303a00000000001000000000800000000003104301201000000302200602d00401600500000600100000001100000100000000600400000000101b00600000f00000100300000001900300000200f00103e00000000200200100000600100100a01b00000000200000200200000000000900400f00200300400300d00000000001700100000501b00000100100000400100000800100001c00000000000000b003003001000000003001000006001000000001000007004002001000000000000002000000000001010000000003000002000004002000000005007000000 else (if i<2 then 0x2c218300422041f60da06a1dd814af22d400000000010193e067b6090e40bd85332a0474e10a8ea2de80810000140163c17eb027d4036200002c06f883a6308860035000ad203d0600b600000000000000e231860e00003a291cd9080d64094c8f6fd20a00000000000000000c5904b0f4c200000282df871b80080081008011d00047400ae8060cbb55000000000141bcc11c740196e10c6c0c74384c2018014327c0b229225008f0c05a5803a90019026c5c11704028902907a6cc00003823d3026d0000080100000000000000000000000007b9950000000002014e000004059000000018280000901d000001802c8000000001004e400001b8d0e007400d6c01711d45f1049420fed9e2a80000e233175180483d8034df0334803ba41f9303ad00000e021ac14980000d0756e049440f0d83190000060ec7ddc76008aa051e00001018e00000000000000269d27805c2a26600000000000000a00765431fc1f9d82512003be08cf09c5b83ed426aef40ef405a03972b06300083881d0682ca70719e04d2009f5b9b8c0512c10e208f79030d728d3c0c595d6a701bb100ee4406d410d8116cc201f410778115e115d4077d20c319c2cd037e108a24004700b2893587a3008067ac9b02523be07f860fad4227203c5501d760bfe9d716d2dc60035841acc0c51828eb2824d5185c124000fbc06278ed9800000000000000000002a0800000000000000001021542b0000000003ea18800001737f009da0014182cbf08518419cc07e28479f050d4118681d478388ba714000000000000000000000d8209ade803d2a823f42d180f18844d307dcd45d489b228115f01c680cf2020b6813c602a800860ea2f751b90019aeeb49c0b10000ed05b7e057100cc9d0a2205af00a23c19560203400ab240f841a9281ce9084640e6e804d0b82e327cee028a8090853d4d06014049dc83361374f006f005b441efb046a5a485047e001b6302fb8a04dc01415e27f10cc1200e000030007b83a59730860de801a39045f01e00300100100001a00300700000000b00200400600100100100401900000900000700200c00000900000200000000000101700100500000000300000100200100000400200100100000100001600000000100000101800000201300100401b00000200000000000200000101e00100000000100001b00200000700000200d01000700500000000201100000400000200600100000000300001c00300200000000101000000000000101d00001500100000100500600000000300000e00700001100000000000900000000500800000700700000a00000000100800300500401400000000100200600000300600000000000400600000100000000500801000200200000000300000900401d01401a01500100f0040000000010000060000 else 0x302817eb049c4049080fdb01b47033aa0671416e78105103400027f423a901bc60641a1128802280000a230ec41180000490650000000427c2330000000000e08d3284fa821f000007515681a4f53878708ec09ce81982038fca18660321c0d9803bbe03d380a6d6853c11ce507f3c45240000582a8000000000348037012e002338e0c38087cb9be60128a119e1e2c00375623a00000000000000090389604738892bb89ad22916074981afd00b71a5a680c380000201000000000001811ab840b0067e2e74b00300ba45c0306e02b041c5383e1c0079c034c405f60312e040c007ae480439127007f1806ae0181fbb91c07fb0513e49175510e0076d40bde0178d384e904f32117801677832b3042c94c0e80a970141a0301a0bd2c0131d12a706c6aedf329a480345c06ecc01ee1c42e03ae976a2e0a6281cc6825ce22c6801a4a823610d40000000002dd23ab97e002e544000000000000b076060248000000000c25a400002806ed80bb000006ee1c00000d3f55a1914103e810ead392603a1800a800006108500001e01ae80e080000400426455301f8aba31f00944e1580000739da9024c802d7012eed38dea418000000000703e2f0572607a0c9042d0d7a087a20d5c80ac1008c071320000000007b84f706d2b51ab1cc3111b37736b608e3c8ead80308034ae052d4146b80e2523eb445b4aa191544fb0875606be289c3bb56106a194d4fc8e7ad2266088a0000000001040e00001c0e4d01ac452fbf04e3e114301577d3e8a08a8000b9801f880d56a0948029c817a8000000000a11cf880800000a2067e05f78970a8214106ef1412101b70000070371c472cc04f680c2127d000000018880000f008e00000000078449e2265ce7fc0000782990070d00c07e84f000004a81040d952980a83bde01ed40691a85ac0017a7720447c740dd1545c6056f00f9a1cd9501ac004b484669003fb02e37223a20f0649057010400083403cac088f8247a0665a051d00582001cf083fa433e88fe4006ac0857004789d24c01f22771ac0d9e0889882bc70435c482e08a8d01792054c0000180b78000000000000000000082694086a21095411b80231c017000000000000000e06760000381bde841a50062200e400000000040503e0ee4c03878291f015ea46bb4161711f3405c20000000001042c306d540186e93e382f3e0542d40cd9cb28d2d4f23d44063c011168442408d3c08c0c8e2739bd908314ebea41843044c3058a6059e0051b00563a48e000009e22083045a66d045818029f53f85084000000296c80000c70ae60eb1a9f500000b08ef00041421b402ec00000b4fbb80648b85500000000000000000000000000000a8898000000000404be48cb000006a0c8000000000000002001920f5c0000000007050f942e26a0cb0378b059a000)) else (if i<5 then (if i<4 then 0x98300000441c5c150382dd005ac00000c22b9811800001cedf51dbd88175e027724d981c8f639b990576c0a9d411ce8410200eca05ab5ce6182b330099c0a1780410511de134be0f44c1c6d02f60230cc0905c1a11500ef029260286c06bc0226e20456e0fb5c6ca03e8c085e548e742231d181e065ee0afb416798073207cf6eb5e402498022b03b40000000001837d104fe00003012f304003a188000014131b8277000000000001b830339170a6a006000002827267712000010209584530000000002014f45339a051800010000075020d04ce000026908d53fe106e784e70400f0b818fa253a48480000000000000040f2e1da87d03d676b400000401a00000c030da1188007080000f0150000004206800000000000000000003970a22a0000000000000000000000bf000005920fc26b800000000000000000000000040588000020324b48e0000000000570ee001cb0163510ced006b60e5a81191b9b700025e07b80000000008044a0057ea81a800b35a1b4808a7415580000b76ed606c800002022d907ace0d58c185f8334106c800002c8e3000000000000000c0e28b9def08f72e8dc0000192f2d27142099400002915b305bca402c0032a5137506e3e02cb81c1f382c604adee76401e02008900001e11c0ad685ba1d8039f40a09821e1027c805b2a0bbd297a89197f2019446c14a2221214f72e20000000005b845907d40000201f6012ddd036e0000000002831f00000000010054a13950000040848000070120504a10101d8099e01ccb23dc80b6ac1fd0826fc08de84bf008e8f81c620481605034170081d3c22abc0a9681a7950b3171c0210e74012cba67f73fca116e498641023c23f3e054480c2638126035bc0e3bc8c1100ad422fe807bf483a290721077e0000000002041c603fa0000141e930326307eba026000002816050774c0d0e9c6d50117f039000000000060456fa88881098801b2807c5082620136410bc3a32e2294c09ec00856032d00001c0b91c0995b9b6b02530066e80ffc0392701eb81122dc0c802f97157d00d88019ad8131a225a000034911800000000160175017f00000b0405a0120000000000007fee093e00d3f82596012200003889f0021e978a3610a400000000000000000000000000000039400000000068177ca69fe0fd800000000000001a4885291468366b06bac07500000201c700001e007dc02f00000c04c0000024a2ae138600000e0f328061a01d84a0bc00d4c00006045a72306948e8000000000e05e514fbc00000000000000000000000000001085a00000007880000da7d20000088b9703dd903da004de9dbd30097aa727401a1012de1144901a334b81821d8000da02bc00ccc00007121630173e01b9410cf0013804bf045acc0da80441c72c9a4570000008275ea5f274d0fdc else 0x18d6065ac106638330000160368c07c301f700001201b400006011b3036de039701623031b50720000005d1aa81d1775e08f15aa825b002c5238a60217c0233834af0865003dc80fe73ae6c730b205a109ab50474f244864dbf1cfdb396a8a14c0033180aa804654048ac0cd80201d50247a629611b300227538430013c0a88000000000106a200003c04800000804d60000300f99009500000000000000683d3605758109d40c8a3b95d02c7ee36e8063800000000080a8e28216826800001e03995cb3b811f000000000329cea0084fa884444f46987d12e2e017860e89c07570283101a4001b269cf7810e0a18d40cb8000000000e0107e03b400000000000000000000000383d9175ace00174052e044fb056a00000818100000202b2c0be000004d34a00000000000000452450a7e1b50c181f075302a0599e4e354191202ebb70fa80151820bb9161f20fb603bdc8373ba02e072ae0a7480a6a80bdf0681c023c697ec00154a41f85144297f681bdd040f8072dc16a301a2a244fc407b80eacd42a203fc407d4c0499813f60310b510e69c5b8372c011ca103081a6681e0c01fbe4610ddbc381a982413647b1c114402b88000f00ab3413f23c4bd0219a4036286b283aa601b654fd9e945991bb2079d003ce08f28830a4005260d720169201ecf066220b9440f8000002070800000000031217000006e472c1f7983d520788e08f401f4c5382476124ede480b0e8185522b4605c1c1ad4803eaa82b803380000101f900001445c58091800000000101055c053081db00000d514669c2854386057a210935c2c102af1a38140532c065682214070ee0559013c60382c78a8206254826180331023520522e96ab91c9c009f611764204250274a69960f63e91669014c022660d1a890f501954a03ba0ba3009a900dcba59794e7ea81930002703edee63a80ecd3ad5f05dd40c1ac0d1d80de770a5a46670105101e20086e5487c40818008b6a60d2e8bf9dc5f8399303ca20725c00db1354c0492c03fa8125d8174a04c540e9eca2c4880d60829c0edc8129482d31072f605e0000000000000000000000000000000001e1010011b400160000100b459dabb83ca000012088ec1ef00000000004e06a286cdd30c1021bb432880c08000050784a0930ddac6bb757052480c9d8037b01dc0219ae47c1890db0006b043880e1400000000000001007ea404000000908db42afe807380000c04dc340dcdcbcc822f1a71800002c0808000000001a0f3fc1b0800000000180f8c00002382b900a40000000003046420441ee0b60109e01f4a76b684c630104b8422f080a40051c1a72d45810189e0f6b820ce3b708041ac0d50000000000000000050a00a78000000001c018940052835e805d400000696d000000034200001c0ef111b63047800c5c000063) else (if i<6 then 0x604ac815b28270327d2a0274c1083833a2082380b42003f39449007480481fc1b6f03d44a7cc34277c1c5800009019f34d38000000000920258023781e3a02b0a00cc000000000000000000000000c0968000062238000011c8980000a705fc035a409e80000901e9c0ac4000000000f02a6002b8000000000f0742e0afe4205000007a0b800003096f282d510696c0c27c0ada01d690380a4055417339152ca5bf846a8007cd118147054a10bbc0fc7945330006247dbc1e48d01fe770c6026e80f21011000318c0ef0c0d3381227004e204a8811625045f06d6605380000502c1a22f3601e000000000000000000006a2680000600be00be841787839fb2315800e1c86d3000150289247fe005b75462a020c60e0640ca182aa00000a47228140454690000174d180000380fa4060e803c01cfe0511cf74c760f191d1b39369a00c9c02acc8073112850258551045c8ea029f802f500b240161d01c280508447eb4219a8440e03ba6089200168043fc25eda4926686a2020b3a6977516a00d84817fe0305209ea41d780000000013515d9db380000104e940a55007fc009c9037f00c74000000000f04a82065d809c2807100000000000000702ed5063cb4fdf88b800000e01b20000340b600000c06820000000006002f0000000003c14bc8444ba729a0360c05268176c0548a462e88088524080690a47dd29b439363b049a00001007258463f00f520857418ac807df0140a411d019f081aad0734000021c235013a00000d4c3a08cf0000050753e079c00003bc69f066f742800000791fba0373a08fe416c582ad045a000000000000000702e600001a8ea782573223d81027c12258112801c12040ac19290246ea7fbee01800004397d820de0000169f94826c00000a0ec800002b955e71a80000000005117a00000000000000482c0d047640f7000000000000001004a06852703b5ba84bf4ae3408a2028a22374409568194b0198aa756c0ed0c0f34503f801d96e92e4235b904eaa69014c6101fa239df82296200c9c174f3817e08dd0451d49099836f507c98021e40a2d114d2017e74fb7020f30063423018ebcc815a0829aaa45600f6f1dd17026a1a08fe070d5d7383b8f00000000000113d018b00001f4fac0000703c87a5ff4063740b8d0323000000000189105d3f3523940000000000000000001a0e2641d1e8455e001054789682f800000000000000000000000802dc44d94000000000d00b5b44785d7080000200ae00000000009016406ab203a58200839f900000000000000103742047d602219d8c0000050484e41e4420de104f00000000000000000000000000002821f13a34d00ce000000000600d06a3b800000e81c81387a02cda099b0055000000000060e500000183cd4a5b734b5c0000401082058fa055e8145f0296e else 0x10ebc400006d031f08b000c9180a318359f0261a045a003ca83b37040b445bba91fd10d9c71a2e515a40cf880430012cc1183401278459608e40000141c8800002035120ce181a24846800001e114a00e680000d769b80001c1fb88314b045514fc7821a193880000134c6b1d19a8264004a600000000000000000000000000005015df0897e0e77490658020902a1eee2a8190b02112a6a480c3e80ef80000c073d4454d80f8e831000000c0e73c1f28832cc08ed54144c9ad38421103d5406f80000701360000020ee2005d602940000000001281b752d61a68e0000040be00000c248a40264000000000000003515a9cb341045c749e60fc100c8611f4b203980c6ac0c3cd386f05642470e40838044757402a456500274037f1065060ff9c104602e752012c11c7c0a1802617035c608bb80b5a82a90000194c4609b08d23ce0804000018923a12efc0216a41a05c14b51e3b07860002c00001804b003afc0df0000000000f27ca)))
def hashminel12 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x8308b9e036b1efcd058a0000000002c076f91b027281ae45e5d945930440865c1a4f404c0000000000006ebab641813d273fb0ee9c6b634047870d69a11f45c8700000f28c22183800003539ca02a140d0c0000015a66276600003085d9919a00501500d06f00300c0000040390c80ad00300100602500000204600f01f02f0010010010020650150020010010020230000a80020b600102000301c0c203b03704300508701000a00003800300c0050400be00103f00000700f02d04002103100001700503701400700d01d02a01e01c00200400100405a00800100c00200f02702c02200300000800c00201500c01005306e05801a00400100200000800100105900000800b06b01600500a0d201004a00006a02700001400202605d00600a00200105e01404c01b02900002c00600108804f00b01001700001802e04700e00306602d00400f01201000100201900300f00400600302101f0010050a900300302c0c900407500b00300303103308b0170700050360000010020040180210000000020630310010000060000000080020020230a801802a03900000000000000003601203d02a04b01500b00c03900f00500500400e12d03401103e17a00700404504100301701b00800c00801600000c01402300c00104500308f00100506400d00001802a00a00205e00200701600101201400a00100200500100d00200501902a00800100004400701101a00501704800400002300201e0040350010080060000220270dd01804200000805c00d03f01408000000002200500c01b02700202600000001801205900702600702200605900002200f01b0100000000880050c80000120c400700300100d00b02101200400c01805000500105c00000300200008f00001400a00100003b00409500600001e0d600104100203903b0090d400400a00100400400205700900701012400904a0dc00e00500c03800004c00500200000204600000e02e00500700208100501800602a22c00700400202200100100205b00200500700101201402700e00000f0af00e01e02403b02700101d09e07005306800300000900002501400001800601d04a00a0ae01400407c06802f00800401900400b00500203301201b06709a00600901200b00800a00000000200305006d01b00000f01403600000001a00200500304109105100f00701f07e00000003c00402f07101c01301c00200001201e00604c00102b02f00b00700500200b02901006600000204612002c02900e00601205c08402300001700401900103101000300c0a507905c0190190020f800b00102803c00f00803100e15900804309600a00000d00000a00401802803100a07700400100206100002f01608100d00100b00501500002c0000020200020710100070031030000000210020000020ac018 else 0x97c041800005802ce0bb800000412a085c252530000000000703619244800001dcf36840a6abc6e0c221d31906dbc23d20000000000945ed0245a48b40000210d60011a000000015d83923a02a0566b017483868d03ae00000000049472d233d007cad04b3831840bcd84f04828a6149150b70000000000351d7cacfa00002800100000905300000282670000000001c09c5c218582f20000164250000000000f208d20ec00247fd67b2a28a407ac0000280258aa51c14ebc256614cbc08bb74efe4279e0168f2941ae37ec83ca14ac174eec46530b1525308e2c86610ba0284ed0a5b09f60053643569818160410355b1c2a6804990000044fca5c9e00000a0a7ccf76a9e243052060caec03e31c7e2be2f00001211440000081a27a063d5a9cdd07154d30a40814c640000306c427009414918271cd3da0000100e538b13586cca78220000243490125c20a54d508c00007149a00000000018179983339abb0000021cf8bbe26c072b056bd41b4194130000164e8702bc9549f000012033c82e68000000001f552f411b3d393d22d601ab0433300000000010f3e00000382d400001a47cd1e75800007a3d5e0d03c09b485a7702c9e175f9c0b292e66069c00003c0caa1485000000000000001842080085413f79d422016100001e5b26aab6d029b6081ea43624adb00000104c5aeb1442b8e50e3a0973206440189684a7000018f41c8281000000a9ae852cf4027682c310b7ac15040000206a100447ceb9bca08a053b0232200003cab9f8320005220000249d2480adb02cec1b27c1f59542de0797a4338c31b6036a507eb54e8e881a185e4c0c6e404f081453001d0000174384c032a0408ca4c7959e5aa174010410c0c80fd88524b818ed078e05148c04528246c00b3c06f2415980000d0d62a126faa09d01c30000000003c12b3835f507a0a0d2fc2ae054034066d012f942c60818b27335c4a5c085ef5688a035e0000388c7f82304030e6e79d816fb8174c238e606cec8e6900b83a77c4081cddcfd51524037000000820200000407352172e80bfb0180105d0c5667081730496d06fd20d60040cf031440a5c210aa411ab3cd90000121014e867d02834074be0b601e42902966076800003804b0000040bb76101e8b44603e3375702017902afa03975295460c789cd3dbb9600acee12fd810e08288729bb00ca582bab394830acbf4cdc0000316a122654601ddeacb8000020aa4803096b3d20051000012e3f40000195a000001a06ad82b4800000000000cdc00004bcc8a00e401316de06305fe9053504114000023b06000000e86000000852ce2b394163e02ce00602704f8a057e020d000401099ae060c280d9957880ca48471701d08000072af6152aec187452ddb06bc0133c806400000602a22421800001828d909f544582c036b004) else (if i<3 then 0x9e400000000000000a062b80432031502c5a000000ab8804b6e216db4e38e91040171b00012f8b741bcb814a221b600003c340a80b03033761414000000000e755ee091000000823110b2c00000dd32181d5e7c48000014b1200000faa3800002c22f58280a0b0e0000008ef1837ff054b8e697018ee82f840704000000000181a500001ced3940f410330379d8a03a70b1f800001273ee007e68c680000326f0206489da26d39a00179018d680304815aba4c364df02a6f0b99b3029cc1329484eb01bfaa2588416a81e000000a2340000000000084ffc0819cf154c33d5817bea8554e795e896a8276f028fa00d9c996e3918204178158c00007d4d0e22e7455fc0000404b2201eca55dadefe081fa2a20574f56832083c82b067a0000000000000000001ae16801ae0832c82524001a2a814e02c4b73e12146802c100000e0d96c0bf5023600000fa94b41386c10603ed140508c0938000000000a7d8deee795c63583c500000050e2c1cc4d5e2c0aab8f02f5ca2593bbe2387d4a835c756025db0753811e4812d28629e057661a739ce7c939687c7fc1704c252c83ed0000044dc84243594e500001251ba02aef16906232460f6142c1d947a5ac62000001e748000000a6aa1159c8538080810ab1c09f95c2e3536282b0ec4e9e42a50000042478c0f70c195880079059f418449c130000000001143cb6891d8316000004521f404d00000008f52430e2a5b0000000001604524b6223b1e207c8000018170a84ef82804000014187f84a260a11aeff6c343c824de05f460723082e000001744c813c02955385392ad07f4b7e1d88cbdd93073fe42280000505b242758cf38a42580000010806d4412411e1037a0000164bc949ffd82fcb280e000021f642bc70800318107c000038199ea25400003e823882066a9fe6561882e7c862ec08ea000030241f84950021201a76c9daf10b8f07d00000000000d5ecd73692000f0240638f7f07b3ae430810b3027580151412f0080180000500f8f481c291f7ba142011f019785f1b480d1e0858c10510041490c100039412ac5da36833500001210e62b050000040bf1e50cd405500000000001562f808be1234c0794c433301290844382152847dc80a6004d5c098e00002c27c5139d00000a0d355ee70000000000203f39e0c0000000000000004948bd28672917ae4ba011a6048770d2f20af400f72556e60d3e000000000580bf00001350af0085905abb0bd2e187401a8800007002e00000481add5abb01ce6043d1c5300000c03a20000140f28000000000000038182e0428e012400002c1f3a00f13036c000000000686abf042e015eb5e4e00000678e3a50508304f82fe000000000000001d33a00001e1b7381f0611f50017c0f3f6420c606cd0000061abb4155c80f000001e18e42a0525011c04 else (if i<4 then 0x386690000140169c165a843800791e0400818100000a726a411df80f600000e01b100710a97100000d033800000000040185108fe00889cb1465673104d70049e084ad16710072140aa90285195880013de4ff80000056d1727910e41cc1b2306b0000000000101b2e80ec000009489fc158a00b71014200000ded08044160798cf376c03a1d0e982ae8000000000385da60bd4e08ef1c12255090048f34c935e24f04462016a0050408fa585d15739d84cf7835515190475ff34a141c9cc838ef04a02029803694bc39b0c69b4d2d88eb0000020b0a40b5781e4e863800000a4cc882a7482f6705520000682eb73e4a32336000004b1380000b708b20171812098005020e9e0a88000023a2d72afdaf88b01b4d92f3c2529aea7400004d62d407e1444400000602f44004c2002880ea503df20d6620963c8c9f047c9a9588588b8325a024fa04480424e9f13c061cd03bca4f24005cd820eb06540105942eff1068274caaf5c580cf15516ba8052166a8009e86c540240a42b1c84600000aaceaa4fcc40ca480ee2214600001c02873cea30985c0a864341605a9a265e0f8a1001bd967397bbd6534c00007869000000056c9ea0590011323a74094fc1b8800000000081675c01c4833b57616e478000000d36c074f18049b833509076c0443410480000303fd101292f66f29f3b0481605920000000007bd08228deb53e1416cc007dfa7c125b540000503ffe0dab40e6c00000d4a2926812147a1d9ee385dc201421623c27f580ea206db00a3a484e150d200001a46059e0d80000c0570445f800005552700001609332829e12f50000141b19c1f7f839c2a54800000c13670391b77dda19eec2e223945576800000141bb80000da0a840b6dc036285c600000e1852e86ec900ed050ed57a00153c84d1e09c400002832ab5159272f2e05d41dd2d83d2300a4745fb815818289e2383044578182581541008b0424202a5b10a010a91d511089c05b9ff929af6119583405042f2112ca0b1dc0ac902c1d038000001411913812b024b445f000001826080d900054c4059c83a3703ad81ae0c22f80000309f8753700244812ef50a30000000000000007074c94ca701e200000f0756000026a448000010a84242495c118000057acd7460b00ddf83b10000000002c29b394659704f00bc2025030310c1a9a000038124f3c1900000f453ec1b5a0519d780c000000000306868a6220084202898000030db54f0eb801700000d0b24a10c782fb402dd0000064785aa703504900000641776ae842169000000000342a66062b00000545f0ca530066c1a24e0000000000000000001c0d1800004816c000000000300f20d63c001aa0f6c6c2468032de02c52ebe7c2b979311ea2394ea7b9c8df011a87b9bc55c3c0bc38239800c2eeb18407fe06d0c041f41 else 0x8670000002432ac15cabc0520352000034a3f8845260c584ec7c6a1600000373ee0000042bb8000000000000000000000000000040d2282ab8026500001c0ed4000000000d0a233452740ae800003022a000000000000000000000001a95fa81b500001c4e9400005501f925efa0fed435cd806300000a0eb0832d00000d0d8e00002c1db80000c2154809b402c345294e0243211ec000068662e0c984155308cf8000000000000000000156c300000000009e10b00c5209ade4d7e00a1c1474408d3c16354055f8294806180000380a3103ae827aa40f35e9f0982fbc2178000034a3ee11862245d01341c86073c1600a573449680cbe5122c0b200000143157389e422f5a032c68a1701e7ca57d411859e7680000d284c000000000391c210d134508ddc1fe84a8471fc0000040db800002722d7539cdc9928658b0938152a40000183d7507720000000007d0f827ad4000020a36000000209ae156608869056e90a9200002ea7230643e008f6e7d4c0354b8e750484950a6c0b5603322029e55494000008485509bbf42f908cb00000b0ae12e14343135159f67732000000099ad56f00001d44520877281fd408220000341898556aba5c6e11cedcf4a914de29cde0f08c8028000060bcf04ab400005512620ac0000018256b942f37b49817240000380a250bc4a037800000050b901114eff000007069900001400578300350690071ee4eb400007050e4aa5c00003c1abbd21fba031008f581d9853b10000160881c061d3de1324d274ab25cadc3a2450b0020433ea68c839932b58056e40193712eb10c5e809205e03f0537b799e4e11800002862592216a05bbc28edba3c2a2400000082896063d001c281abd824880000a7639c4ed980a4c056d5a5c8000020250804dfb799961503c25a4000c3a9c4818fd829f80000f04ee00000c09c0392fd06a460dcc000000000000016171c031800000e7045603e4000000000000006e99c000003dd7e2533a036c401218132000000181cc92dc860be0c46d509e80f8a844dc07c5c1263c2b67016580980c09c8c300e939e3746881aa681c01d58e5026f800d3007b9d2cdd0a8705b1a88ead8546007e234e800a0b702ae30b27c00f0e80e639f3921b38021c00005d67700001c015c6ab3601c2d214421410810dd50177023de1947014c8000000000159f302411861630518b4a7d4162cd5912a2bb255f000005065ff06a0000018296c019d60cbad443c0000000005a192000024128984bb409ee0000340fc91645a0203a18c80000301f3301c0c5b23811500000f281400e4c8185000000000100d09c85bf9444000016f05dc286800009a59000000c26469468c023a00000de7f18434f05db806f8433080000b2da480331080efd568406c5a1123205e2388d0282ad540a9dea8000030d9e000000))) else (if i<7 then (if i<6 then 0x401d1f40f1418c800009761a00002dc9f8000000000c50118a4b800005291c408140000485c80000140d9d8280ed1ac4713e24c48000053ba000001811c709311022f0000080375dd375006617903c00bdc010606bb0000061b528847104337aa2f618840000116701adafa02139e0efd044879ae00000c32a0000000000000000000490d52069400000000000000e08a02016e2a00a831b10b80000000083e50ab2078294330008cad4aa425d0641c5012d810bf80c1a00000e890b9226c21640e6a8a84c180fd803bbe168e435a8829f2a8f0c03cfeaca181e9e0b08d44289f690000030139219ddc23a6004fd75d17488b5cb9c95b5f07ccc022d5c16e03ead07fdc19f00b48d803bf096e0078f41f4fba17805694f01380da40642d086be0fdc82fee0176000010f6800000106a43704ac0f1bc9a0f829210146e0798812041168fa505a0db0a8a8893a3c0236811285e227556490d786006e0320000002743a4f75a08569bdd500cd7840195c9a590a800001a14191ca1f0619c0205003d58a0c1096997c7321a631c0f592abb7439748f000004390f004c741a6ac04de845a0000000000820e2567e8a3c4003429d890900400000000020168a059f4047dd509948ed80000904c2018cc0000383f2000004019e1d8a7011640d4e40b9c5e0873a31908432505d0a4023b4f3a40c0459c836be0169000000000142db4d113d0559a45c702080000007dab6127dc1c238620925d26115c9d74e02eb37955c178c0000080fbd202cb497800002067da28000000000001806e00001d447e033ac001a374cd40d52c281d81a150093c148e0a3b980790000164fd000004119700001419cfc0cb5857bd0847616d0421d9813912b77a10020230204f1b01adc5a59c2fe551fd320960000008659861870c95a520c00006918d306996ed06293d7d457f72f160719ca4b284e8d09ca6027fc3511829c6a67f41655410e8000062660e16a95cce5006f0052a00001011400000000008173902e50000000bde947ac000000000000000000142ddcd6717218a00002415b00000e04be356da02bed531cd039dc080bca2e6053182cee4158b699cb04aaf0ba6a0440000025520b28ec7444a82f8b833f000019412908c1e966f1235ce0c875eef8000030db04003f5d2f951f9e06f7001d4000070339f26294f39482cb984279735320ca000001149d40c210ea3d9d73cd5e9b03b2411099c50e92e7309c0a013400006bbfb00001351b7025d0929300000200a70183510910000100fb000000000090494e05ae02d3603250786e14d8008873d14e1790e00000886a7051070183619382b04813d900000c48c60351f827a7028b1492ae86f705a2e04d3a12cd00a413b368052000002086b80000000002459ac0190000080c8e00002c20a985ee521b820a76281c0 else 0x3546074359101821a5c16e3d40000505472ada40000041c6194b000d51a0311a88ac813e9741f6529288b2905a5502f305294020f2803e00000e16e400002159ba22f2a1916800900000a22ea0000240224034f20c4ec11a11e3f8000020bbaf4a8c000070497c036560dc0c22ce911b00000e524fe8721840e00b99404c6c8fcad56bc7bc1411c801d7800009ad6c00001420cebd82102b8e19c5ab25a84cce09154f63380794d2fe52460c16deea58e12f8e035d205f08004801894037a0000340ffabb2000d6def31fc1a27bd878760ac1004000000000000010526c000058039f09e44086982470000000000000024a5580000da54460e76891ac0644d28a600000028f83b1057ad6d4b9482dd7d3f000001817540000486310000080b910290a929622b3a8139cc137192eee28d7252a42b6ad8345b73564eae45d8d882d3e06c021a464052f0386ca54200001813443d65f0acc4037200899012eba4be00002408c590c400000547c8000069272002c76149501c508266e03b5755e80000000000acf1e4c0442b0f847e506cda15a10867f022600001b56f902524d14a20786000000000000005a552606c581692b9099052f6fb0c00002819fa2ae5605c02878883896a515258960251b8573c2646e0e9d80a178488000014185c4157b84ec00000601cc819c0393727c4a9583c881943b0f4210f00b1800007930f0000124f1000001397782943441c941ad80000a00f440ee102d73d5b31a6704e8340add384af971c18059bc02fc02be3032600000cad3b0285802e454b6800004040b9ac7bc0276c0876162ca79a6f40b048bf80000c0a7a2403c000000000f0d2d6039800000000057c6e00000000021398c726da17ee1d80e8095ba9d0aec8e41ba6868e0067c000008367696d050600003950307fd1f80000000003810c80000c705de45f4822480000a0252217cec0fa0038170c08451aac28a8bc5b00000a4fb80000482f1b0afe554c7088608008105c440d4e82ef7962e47b4d8420501b72d14b809b2e0e1ec2c5f3933372850f8c082ca000c73020b953b94046204f9c0cd1e04d0009559225078344124bc01855312fa3f46e8bbcb3a052dc90d7e64cbba941dd27cf73e90f8e3dc365d3fe5a918603884145d00310000140436000cc027b5a511a16c3c2ff8000080cc6c4a0386a600000000016425d9d0c8000092924c0d1de894c38408a62940894c916404d4903fc0000389da03914c01276472a8038915b417271844b9030421422000014119c08e445141a0826a0f3a416068233528bea4ff48143581cbd0be80000282370055e00be4856a301aee00580000140c0c8151b85000261a0000368ac50683a05c60000100c60000060b48c155a8902812f650c77601c35c157bc0db00c5208b25d8b0000020cce6429b02df901b0) else (if i<8 then 0x148149800000000120c7c0000004629087e209e6899bd046b9045c01324c23b582b5304bca0f775e04000004087a00001c1ad780bb000000000000002be348099601af80000286c00000144ba8000050464c03c06009c00006032e00001543340000000006026bee31c00000000000000800cc000000000f789be118d42a2a0281eab0e00000a8ffd80646039e00003c0ed80000970280000208eef018d40cb96149be96c382d7d06220000009f8582144089ee040cdd75390b3000f600002807273aabf00ff80fcc00003d0e8000004008800003d15400001e5090000000000d20d9c11500000380b452ac3809f7c861000001aacf640300095800006061a000000000501ef00000e02919d9b8000000000802a7c3462d596f00540000142cf0000000001e02380000700ba0000104cb383126810800844852880000385b1c09292f5eb01f2800003281d20aa1a82400000442502e68282ec08090d0398540752ab2b85e1771d6e03bfea53004556aa3e0000382b5100546291000000006a601a00000074e86c05e88021303a0000000000481901059140c2c0000000460000080cd00000000002043c0000081760bd0c7aad200002430d5d425a72820000302cc00000a0403c56861d37e869eb059ce08a400003801e1a5fa000004a0083c0a4096a00001a8ab993bff71e704e80833073c0fc064464d8c00000000002321e0bb8000019598e005bb56fc827313c1e000008ecd7c0fd800000a087455d443236861e0000014c408069ad5dcc0aec403d11c76403bf303a6000024342651ecb00952099f8309402b2209a464fdf0216800005ac7554d23010680424000000000069d2700d98255f144424a3a880538001a409c3420d880d7000004105f410c1567600000aeace0293a80061a01b8f1f68040e01287262000001023335522a0aa0612e20948586c397574c1ae8000058356ea260c265b41ba9409670a2c000024297e8650420a4000020059585be708b6014a32b3a5032300000812799e9780000face5405fb5c296001400000743b4000008327503b980e20000019629205a10e420c1db281ca323fbe461001aa800000000194aba81d6a15de7237e00003aa0a206bd8a5f540f55de637bc205a2ad217d4000005447f25e964ef8000000000b04c80000201fd4807600001a01ac48010000060935a5901c2fb80000804fec078841a080000000018f8a75e733869500001208b6026e703f40000000002000b0000032811158ef0060681a730008f456800002d2fcb07064179401d51840242016003260808684eaa0cff40e8202d0d159e000006423d4369d5028d09ec554b3c0d2003be3065f158ce815258173301f4c1488c2b780000b0989659e3df2199577000000000140d680000005bde01a5429a71672d0b8a000004a0300000825e else (if i<9 then 0xa4903bdb05d4a50af2aaa08023c743455745ca40800006097b4112f802b000002238000000aa6ae840d7025f7580348bb5804be06dfc102648c2905f000001813b61c7b5cdc800000c01071c09d038b303ece068c00007904fb0ae960af05e3e695a2723b800000c0c3581dfe2c56017504229e014bc281fc056deb1900000000014003968ae68672a0ce86122cc180a3d79c00874e8940000080fec06ed211324212b94278a15d60afc00004535f00000c5388dd5dc020300001015e21d3000000ca6140000102c880000a03510166e819d0000000ced40d6581ea00000879e561b65a910ab93bb0310e426d406915412fa27a000020ad4cb96f10c7de1854426df81b9408dbaec628272481f8404de00003084ca1318a72200000329812807eb23a82f027015b8000060744ef8d49c51882da00000642c56b1a190c810bd8000029da280000000001434542460054f00000611c01d0980000a04f04e8b2c0aacba05000008fb42022c5042bd213c0000080af3d6b700001b5a0000001829e000000000000003916ac04b9557f0a9ff8000002c88000038a4c6810a60101e0ff05e7e782dc3a23c2421400000051c00000d5a040000000006a202e0580000011579627574069800002036322160808fe69cff02a600001a0f3ec8e94b8f98211600002c01a8000000001e1a20000000000f054000002429e6021f2086fc0fe7c0b68012300613ef3dc000028385c292844bc241f0c00e30000100c5ea8a62b985fa1cc0000040ab83a16726c000003a887385b3b762ba15f24294993c0d0309e0245684d281f700000c51c64258b046a823be808480a5943915000002130f1f22000009026194a3b016600000aa535849cfc2e95d61567141c1a28c01ef058e505ad805dc00000000092c7c0000000003061f9051e00002c0d655128e238d602bc0000000000000160c1f83503826aa28420078400007065362301a1275009fe831a12074816bc0000704ee00001c11380000000001a724d44174122dd208a7b25e156c5c7a0944200000e071cca381d2428209cc0ee801cb33a3000001c05bc5e070000022d1d4095f009d800009066301829022000000ea728f4a245c2b7542260bda00559aada791af9019d013d70092085a040b12c0b08ca3d980ac0000125b0fe8f4304a96a1c421927c36b000008abb60000140a968200f007e000006b63d857ee095c6f200000015236321f464c380000605645a8c341a50830dc146090cde2e9788b502be3e9085200002831e000004206dc19e0e872f1632faa4ca56f00000186a5f039a6e5ed410500000109bc00003c897ed052403ea2188a0263700cd00000000039c5af062d8712100174a9ca800002728f8ec39df1948078000000000180e299082c7569614ce8306005e0d0649a1b2b011c0000000001e11 else 0x2c044cbade701be00001696cd3ec57701254b6c00006bb2a4059be44518058d517a0000000000c8449855ad0d6ea0f6f009d00000328c8818a280571822ba777f419220347c390daa206000011effd85f90000000000029800000c2398c193f9ccf0802800001419b601fc3d4b400000000031d56cd155a2169c032ae9d82526050908744ad08e200000c2055a196cc096b910fa09b4556340000385adc09a6c509681413814400000c04b00000190baf0331a1b4500e4805eb00000416b0000000000e088f811bfea9e8000000001647fd02a8901fc2707540471420ef85812aa54419921c7705382703e1543be0b688000000000150e180891004c000000000180ec00000a04ab4e7e40000584c1c0a2e00002ddceabc9e705efc07480000190d0a0408b573e40e080000105de81b0bcb109824300001e08450816c009900bf4ae537295ed014000000156412b6743e21103d4a12435cd9ed2fba0748000014a4ad51246215e0031b029c13cdadad848462c0000704f400b6a0047e8301d901ea087500bd4000019195aa3ef201559d5ad8111822d220040021e38665c047540cf181de684e9000000000000000000082b48a558800000000030d178124f417c800005086c8154c000000000f7421af1ae826bd83de0000101431c1d928227b04120000000007827400000000000000750da00000615afe9b0800009087c0f0e38156951b6d06faf4fb4000000000705ffa02140000000005059400001e86a80000b09d76151000418866ef042640e340000000002046e00000000000000277e0206a94172d818f9746a000000000285320000000001c287c02598abbc65049aa3bb511a97232e0280ca45000000000140aea01cf35068e28e7419365c8580000f2319748c71e231044400001343fc00001118ee789560eef89b0d865642172202d9a970f003aba64d359340000104d8000016475d820373cdbc03db60fbac1bc0865902c46e0f440000080a7c0d37805f40a164868d90d82000005e0f80000029040184e5f11d00eba7749819fb00bd7142a2a400150a2c2e1f06a632b60c109a1c2bf86059a58340b9800005037cda4ba61a140283800007042af4a30000000000b0b50a0ea1c2f43d1809282000b820005d83d6a063884fb3c31d283d34a667d44c6e80b000002777c817641e84a90a13094d447470b1a1919cc7742a16f35c512940bba402033002b4101170e26630146f82e83009700001aee8cc0cd68158306e4ef3378139b0599707b4f5a9801))))
def hashminel13 (i : Nat) : Nat := (if i<1 then 0x57aa0d413340174018c1d000000001882a2a5903a2a8764888cade00c0e902c361419dc32c40ce8214ca2148d983230156036f02ee0b49890c0000c044090948a4000282f00003252400035d8508c983cc00d30120003b81a81d440002885340580000000183308917dc50808800008a7c895c00035ee829b7826c0002807f808c5d6c0000000000000000a80c0002829e5c8aa90d0a6f0a1c0000000141e49dc3087d5d4dc9b86ba2ea08000000000000c28b00b5a9ef4a865eba9e15ca7400000000c82602c909d99de6c13602c1dc2a6845dc731db3423a1ec80a1b03aa82b641cfc198696b43ba69ea587c8a43a87c49f701f55ced9cd95d8940284ba8037fc026c1a6c3128b36c02eea7ec2bd2b531ed5413bd032825d5df00000000141a282a0000242c40000418f831e4b29e90840220308c063c04e5f028291c0566a57814b425bdf8400000002e97400034a83405c00000000000000005f5b42f4827049458938000202240003ca3cc3bdcd2481125fd8831941b2298a038fa8ff8ad11c251c6c896dc0eca8300081c372012b0bd8c3404382411da82081f82aee40d7828f406403d68235c0e3c19101c7421f43900003c8bc000000030874c8310230000248990303034ac99c298540b3433fc1ff8913e9c1e884000280dc00000001c805c090000200e44a6203b400000002c1400000000003380000000101de43c11d6b4223aae00002c525c219413c0003c2000001cab4000000034ad40003abd80002a9e7410d2a3000000001885e8b0269c8000269fc8b44deb5dd270ac40002883fc30f437aa8d302b9004388c000005e605e22830609fb007aeb5c1cd4ddbfa8e782db9d514152cb7edd1442a843db8256c8f58095c03c01aec9eb0099183002fcc2d000000001c315c17c00000003cd6ec347ab58c24c809d0b27c8c45f641f06856d028400021c18cab3dd67088e286081c8a948000302dc000080041900002000020040500c000380000000004000300501800000000980001400004020141e008000000206c000200c014020000c0140300005000000180000001008000040000004018010280501400000130300000000008000000d0341a0040d008030000000814018090000400000004190000205c0f00c000000100000000020040802800000000000000003000000101200001000060000200400004000040300004010060600000003000020180200000018030080000c000141d0080000400028000080b000040000000804020010040000c000000104c00000040000300000000000241800c00008000000e014000040900000000000040000000000000100001802020000000a0000103c000040301c0500002008010300b004070041e040040041a0280100002000000000000c0c02c090000100801018000240100000 else 0x9eee5e1c81d800008353c1d443840001c3c40296410be8559d5540fd026000000002c3c88182df2400000002c010000000000002816e81e00003eb179dd889640003aab0c22e80ea80dac0875e190969282c0335c3779cc2dc8c0003039800000000491c0000aac649c3ddbb81040002439d82ac00020ac2ddf4c228434fdd2c0002dcf5482c5e7c000328f00001ca6400018bbc0003eb300274c1192965c1bf039443a7dcebc14e82656033a943893c40f54aca8a5841bbc071df33a839014682d4d07de07cc2e08907818b41c1ea270873aa53c050c3e0c9a25d22406e000c82480000c1b40b07e9a8000028e39d1fc808800ac9e48175de6689dd40740001c16542e4818400030a04e8dccaee9e5a41240002c0691d60000048f8c27d02a400019c2f2b8700aa0b58e9736b72898c4a474a6a817a435c023d08dcc20e4365c0f800019c744b875f3c42cd8240c12ec036c0c54196c935c3889efac35441f0801fd525c0ac4ae3024400bf8173021068cc00030358dd18c2790102ca7b9cf283698326486f0000ddaf811400029f29c160415eab080002688c41ef29a488ce40c81c6480a3956d6ac000000003e9e0000341681c1c00000003c3280001299901eac0a61ebe00305d5eca30a958c15aca54000042b09df8491800021f7c000080b89cf91dc40000000000000209ab3dc280000143d29f47c9c40000c2534bc203b000015cde820400f000015de84a9c00000000000000000001496168116a5e829800480bae4b3a026a42fac3acc3dc0002294689bc00000000000388b00002089d28dac2eade)
def hashminel14 (i : Nat) : Nat := 0x180000000000000000b25800000000000000000000000000000001644508452c000248c0780000003400002b82414f480003800001c04da10014000000000381c0000000000000000000103000000000000033840000007758000001b4a0738000000000371000000160900000000016400000000000841000000000000052600011d4000000000000000000000000006490000001486000000000181a64a0000000000000a0400000000000000000001ee800000018a0000000102c000000000680800000000000000000000000000c84000000000089a0000006d06003e0e00000000000000000000000000000000000000000000000000000000000000000801800000000005010000010001010000
def minesamples : Array (Bits × Bits) := #[(0x2000a095db75066fcf3fafef0000080058008333022185c12,0x200020943ca706346f2447470000080040008222022085412),(0x185158a80150c0cb00d061090889afffe7e05873650101930,0x184100280150c04b10d020880089a7c783605851640100820),(0x6295228242106100f2a4e779bf8102806c7ffc8231018660,0xad200442138800f2a5e21994000280486a780031018240),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdba022422010c11570c0865024733207e06c0004000e7fc01,0x1ba021c22010c017a0c0805004313200e0400004000867c00),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec5f0003c300090014d300a0808ec1bb08bb5700c4fa02001,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc45f0001c3000900101300a0808ec1bb08bb5500c4d200001),(0xf6a51019ae7020808898084514a7c93116e0803f48ac00e,0xb2914083407100808888180490a1093116688025482800c),(0x13b02805e801cc80012f854018005010200c8600c4a8121c2,0x3b02803e8010480010b854018005010200c820000a8121c2),(0x3e8c00040c8b162d4a010006e221ead24319200f483220244,0x3e040c1d089a066d4001000662214ad24209000f482200000),(0x254205440024280c6d241024f74f4d24840204f490c440288,0x244d462410ac0a084c243024e34e0c2404000470900400200)]
def minecolumns : IndexTree ColumnInfo := (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12),(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12),(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7),(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12),(0,8,227,276,8),(9,0,486,0,8),(12,0,499,0,9),(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11),(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7),(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8),(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6),(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8),(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6),(36,0,347,0,8),(39,0,344,0,4),(49,0,462,0,8),(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13),(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8),(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7),(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7),(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13),(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9),(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5),(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6),(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11),(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8),(172,0,339,0,5),(176,1,332,2,5),(192,0,319,0,11),(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8),(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7),(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5),(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6),(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6),(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9),(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5),(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)])
def mineautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def minelevels : Nat → Packing
  | 8 => minel8
  | 9 => minel9
  | 10 => minel10
  | 11 => minel11
  | 12 => minel12
  | 13 => minel13
  | 14 => minel14
  | _ => emptyPacking
def mineindex : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 9 4 10 2 4 (hashminel9)
  | 10 => lookupWord 97 293 9 16 8 4 (hashminel10)
  | 11 => lookupWord 874 2187 12 19 11 4 (hashminel11)
  | 12 => lookupWord 619 3874 12 19 11 4 (hashminel12)
  | 13 => lookupWord 257 643 10 16 8 4 (hashminel13)
  | 14 => lookupWord 10 163 8 13 5 4 (hashminel14)
  | _ => fun _ => none
def mine : Forest := ⟨511,14,fun j => minesamples[j]?.getD (0,0),minecolumns,mineautos,minelevels,mineindex⟩
set_option maxHeartbeats 0 in
theorem geommine : graphValid mine (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine8_0 : block mine 8 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allmine8 : block mine 8 0 4=true := smine8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine9_0 : block mine 9 0 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine9_1 : block mine 9 15 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine9_1 : block mine 9 0 79=true := (@block_merge mine 9 0 15 64 smine9_0 smine9_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine9_2 : block mine 9 79 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine9_2 : block mine 9 0 143=true := (@block_merge mine 9 0 79 64 mmine9_1 smine9_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine9_3 : block mine 9 143 6=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine9_3 : block mine 9 0 149=true := (@block_merge mine 9 0 143 6 mmine9_2 smine9_3)
theorem allmine9 : block mine 9 0 149=true := mmine9_3
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_0 : block mine 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_1 : block mine 10 6 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_1 : block mine 10 0 70=true := (@block_merge mine 10 0 6 64 smine10_0 smine10_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_2 : block mine 10 70 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_2 : block mine 10 0 134=true := (@block_merge mine 10 0 70 64 mmine10_1 smine10_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_3 : block mine 10 134 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_3 : block mine 10 0 198=true := (@block_merge mine 10 0 134 64 mmine10_2 smine10_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_4 : block mine 10 198 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_4 : block mine 10 0 262=true := (@block_merge mine 10 0 198 64 mmine10_3 smine10_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_5 : block mine 10 262 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_5 : block mine 10 0 326=true := (@block_merge mine 10 0 262 64 mmine10_4 smine10_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_6 : block mine 10 326 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_6 : block mine 10 0 327=true := (@block_merge mine 10 0 326 1 mmine10_5 smine10_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_7 : block mine 10 327 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_7 : block mine 10 0 391=true := (@block_merge mine 10 0 327 64 mmine10_6 smine10_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_8 : block mine 10 391 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_8 : block mine 10 0 455=true := (@block_merge mine 10 0 391 64 mmine10_7 smine10_8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_9 : block mine 10 455 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_9 : block mine 10 0 519=true := (@block_merge mine 10 0 455 64 mmine10_8 smine10_9)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_10 : block mine 10 519 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_10 : block mine 10 0 583=true := (@block_merge mine 10 0 519 64 mmine10_9 smine10_10)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_11 : block mine 10 583 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_11 : block mine 10 0 647=true := (@block_merge mine 10 0 583 64 mmine10_10 smine10_11)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_12 : block mine 10 647 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_12 : block mine 10 0 711=true := (@block_merge mine 10 0 647 64 mmine10_11 smine10_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_13 : block mine 10 711 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_13 : block mine 10 0 775=true := (@block_merge mine 10 0 711 64 mmine10_12 smine10_13)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_14 : block mine 10 775 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_14 : block mine 10 0 839=true := (@block_merge mine 10 0 775 64 mmine10_13 smine10_14)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_15 : block mine 10 839 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_15 : block mine 10 0 903=true := (@block_merge mine 10 0 839 64 mmine10_14 smine10_15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_16 : block mine 10 903 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_16 : block mine 10 0 967=true := (@block_merge mine 10 0 903 64 mmine10_15 smine10_16)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_17 : block mine 10 967 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_17 : block mine 10 0 1031=true := (@block_merge mine 10 0 967 64 mmine10_16 smine10_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_18 : block mine 10 1031 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_18 : block mine 10 0 1095=true := (@block_merge mine 10 0 1031 64 mmine10_17 smine10_18)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine10_19 : block mine 10 1095 53=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine10_19 : block mine 10 0 1148=true := (@block_merge mine 10 0 1095 53 mmine10_18 smine10_19)
theorem allmine10 : block mine 10 0 1148=true := mmine10_19
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_0 : block mine 11 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_1 : block mine 11 2 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_1 : block mine 11 0 66=true := (@block_merge mine 11 0 2 64 smine11_0 smine11_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_2 : block mine 11 66 63=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_2 : block mine 11 0 129=true := (@block_merge mine 11 0 66 63 mmine11_1 smine11_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_3 : block mine 11 129 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_3 : block mine 11 0 193=true := (@block_merge mine 11 0 129 64 mmine11_2 smine11_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_4 : block mine 11 193 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_4 : block mine 11 0 257=true := (@block_merge mine 11 0 193 64 mmine11_3 smine11_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_5 : block mine 11 257 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_5 : block mine 11 0 321=true := (@block_merge mine 11 0 257 64 mmine11_4 smine11_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_6 : block mine 11 321 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_6 : block mine 11 0 385=true := (@block_merge mine 11 0 321 64 mmine11_5 smine11_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_7 : block mine 11 385 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_7 : block mine 11 0 449=true := (@block_merge mine 11 0 385 64 mmine11_6 smine11_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_8 : block mine 11 449 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_8 : block mine 11 0 513=true := (@block_merge mine 11 0 449 64 mmine11_7 smine11_8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_9 : block mine 11 513 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_9 : block mine 11 0 577=true := (@block_merge mine 11 0 513 64 mmine11_8 smine11_9)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_10 : block mine 11 577 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_10 : block mine 11 0 641=true := (@block_merge mine 11 0 577 64 mmine11_9 smine11_10)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_11 : block mine 11 641 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_11 : block mine 11 0 705=true := (@block_merge mine 11 0 641 64 mmine11_10 smine11_11)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_12 : block mine 11 705 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_12 : block mine 11 0 769=true := (@block_merge mine 11 0 705 64 mmine11_11 smine11_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_13 : block mine 11 769 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_13 : block mine 11 0 833=true := (@block_merge mine 11 0 769 64 mmine11_12 smine11_13)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_14 : block mine 11 833 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_14 : block mine 11 0 897=true := (@block_merge mine 11 0 833 64 mmine11_13 smine11_14)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_15 : block mine 11 897 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_15 : block mine 11 0 961=true := (@block_merge mine 11 0 897 64 mmine11_14 smine11_15)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_16 : block mine 11 961 42=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_16 : block mine 11 0 1003=true := (@block_merge mine 11 0 961 42 mmine11_15 smine11_16)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_17 : block mine 11 1003 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_17 : block mine 11 0 1067=true := (@block_merge mine 11 0 1003 64 mmine11_16 smine11_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_18 : block mine 11 1067 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_18 : block mine 11 0 1131=true := (@block_merge mine 11 0 1067 64 mmine11_17 smine11_18)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_19 : block mine 11 1131 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_19 : block mine 11 0 1195=true := (@block_merge mine 11 0 1131 64 mmine11_18 smine11_19)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_20 : block mine 11 1195 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_20 : block mine 11 0 1259=true := (@block_merge mine 11 0 1195 64 mmine11_19 smine11_20)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_21 : block mine 11 1259 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_21 : block mine 11 0 1323=true := (@block_merge mine 11 0 1259 64 mmine11_20 smine11_21)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_22 : block mine 11 1323 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_22 : block mine 11 0 1387=true := (@block_merge mine 11 0 1323 64 mmine11_21 smine11_22)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_23 : block mine 11 1387 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_23 : block mine 11 0 1451=true := (@block_merge mine 11 0 1387 64 mmine11_22 smine11_23)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_24 : block mine 11 1451 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_24 : block mine 11 0 1515=true := (@block_merge mine 11 0 1451 64 mmine11_23 smine11_24)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_25 : block mine 11 1515 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_25 : block mine 11 0 1579=true := (@block_merge mine 11 0 1515 64 mmine11_24 smine11_25)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_26 : block mine 11 1579 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_26 : block mine 11 0 1643=true := (@block_merge mine 11 0 1579 64 mmine11_25 smine11_26)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_27 : block mine 11 1643 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_27 : block mine 11 0 1707=true := (@block_merge mine 11 0 1643 64 mmine11_26 smine11_27)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine11_28 : block mine 11 1707 50=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine11_28 : block mine 11 0 1757=true := (@block_merge mine 11 0 1707 50 mmine11_27 smine11_28)
theorem allmine11 : block mine 11 0 1757=true := mmine11_28
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine12_0 : block mine 12 0 47=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine12_1 : block mine 12 47 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine12_1 : block mine 12 0 111=true := (@block_merge mine 12 0 47 64 smine12_0 smine12_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine12_2 : block mine 12 111 61=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine12_2 : block mine 12 0 172=true := (@block_merge mine 12 0 111 61 mmine12_1 smine12_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine12_3 : block mine 12 172 64=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine12_3 : block mine 12 0 236=true := (@block_merge mine 12 0 172 64 mmine12_2 smine12_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine12_4 : block mine 12 236 13=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine12_4 : block mine 12 0 249=true := (@block_merge mine 12 0 236 13 mmine12_3 smine12_4)
theorem allmine12 : block mine 12 0 249=true := mmine12_4
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine13_0 : block mine 13 0 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine13_1 : block mine 13 7 10=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mmine13_1 : block mine 13 0 17=true := (@block_merge mine 13 0 7 10 smine13_0 smine13_1)
theorem allmine13 : block mine 13 0 17=true := mmine13_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem smine14_0 : block mine 14 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allmine14 : block mine 14 0 1=true := smine14_0
theorem tablesmine : checkedTables mine 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mine 0 0 0 = true)
  · exact (rfl : block mine 1 0 0 = true)
  · exact (rfl : block mine 2 0 0 = true)
  · exact (rfl : block mine 3 0 0 = true)
  · exact (rfl : block mine 4 0 0 = true)
  · exact (rfl : block mine 5 0 0 = true)
  · exact (rfl : block mine 6 0 0 = true)
  · exact (rfl : block mine 7 0 0 = true)
  · exact allmine8
  · exact allmine9
  · exact allmine10
  · exact allmine11
  · exact allmine12
  · exact allmine13
  · exact allmine14

-- The step. The first gate is x4 OR x6. A backward derivation from the target
-- ends in the nine inputs, with or without that wire. Without it the merged
-- forest of the sibling step applies. With it the forest above applies.
theorem deadCase : Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

def seed2 : Sig := bin true (inputs.getD 4 zero) (inputs.getD 6 zero)
theorem seed2_table : ∀ r : Row, bit r seed2 = (sample r 4 || sample r 6) := by decide +kernel
theorem seed2_nonzero : seed2 ≠ zero := by decide +kernel

def lowRow (i : Fin 9) : Nat := [16,4,2,4,72,1,18,4,8].getD i.val 0
def absent2 (i : Fin 9) : Row := Fin.ofNat 512 (lowRow i)
def present2 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| lowRow i)

theorem seed2_witness : ∀ i : Fin 9,
    (bit (absent2 i) graph != bit (present2 i) graph) &&
    ((inputs++[seed2]).all fun w => w == inputs.getD i.val zero ||
      bit (absent2 i) w == bit (present2 i) w) = true := by decide +kernel

theorem all_roots2 {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed2]) :
    S=inputs.toFinset ∨ S=(inputs++[seed2]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed2_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absent2 i) (present2 i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed2 ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live2 (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed2]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed2 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed2_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed2_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed2 := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed2 at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots2 run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)

theorem tgtmine : targetOf mine = graph := by decide +kernel

theorem liveCase : Impossible graph 14 (inputs++[seed2]).toFinset := by
  have h := root_index (g:=mine) (before_sound known383 valid383) geommine tablesmine (k:=14) (by decide)
    (i:=0) (ws:=inputs++[seed2]) (by decide +kernel)
  rw [tgtmine] at h
  exact h

theorem sixteen (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) : 16 ≤ C.size := by
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_live2 C legal first computes (by omega)
  · exact deadCase k t hk hdead
  · exact liveCase k t hk hlive

end PEqualNP.Outside.L_meta_3233

theorem PEqualNP.Outside.L_meta_3233 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5.inputs ≤ List.map (fun (x8 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x8 x8) x5.inputs → (16 : ℕ) ≤ x1.size := by
  intro C legal first computes g _ _ _
  exact PEqualNP.Outside.L_meta_3233.sixteen C legal first computes
