import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_2778.Cert
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
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
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
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1))
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
def hashrestrictedl13 (i : Nat) : Nat := 0x3266d629c3000cc09800002c5a916a703a921aa561d5132e8d2800000381db0ef80ad078788712ce0036333c001b9c02082090848
def hashrestrictedl12 (i : Nat) : Nat := 0x62203295be14261132f30f3f1b40f70c8570ea66463a299d46c1ba2855693691546f740aeb454505f848713832723d0330abaef704500000000000000000002246c7f88ca8ddb1706419d9dfb457c0dd31f15082e0960004df3cf70400398003d17a2e309f11f451c7ee3c12b621bf3c50e3a1244b5ac092482789280c6564dc983c8302b1b20b118a5000015fc042239f2935ba13ff30f307a60f4e277ab838768f4897601ade5b3cc02721800000040b41f3cd8ce1d764963e1314d739b00162400126810b794f6be00053524d7cba0002ad8002c0325551ae8fc431233c90982be9e00000000034280009902110cb80007548254000000f1d800124d8a5e47463801066bfc798d0000b73042ca022e292214900000004943bd408c0000000005cc584c000c8b8002534e7c000622267486115380024940580007aa1947a4c4a8696fd33d25c0d7104063e0ecbc168c6eab8544eeabead2c83731524e6b306c0d0e1c4a7181079a312f870459c1949b742b43a40fe50dc8574d5a519b98ac54ed289cdc149c2f696baac46c504797113ed0d22df2d4cbc0010484160000231227702a9c9c08c67c09295f541c2a112421e513a8f00011e703768da14b1f5e046066c37470001c9cc81a1a4000000510127b5220000000000d36c76a3a000140e000bcd80000011496038b063a005800610001005489e36724000a60786185c2900f1439b5a08b00124c018022858000b4043180008626004825c0c3870a0401806148870c0c2800a1c3000204301042c184
def hashrestrictedl11 (i : Nat) : Nat := (if i<1 then 0xc1b5add011e81124450c3ea5c13b407274e85915c39d0c00d88150e791cb40c5ed0c9bc327aa27eaf919d389c944f96acc45d60131309832800061abc19ca1a4c1d63eea14d209bd4671f0d0b02441110c09b33efc4f51da0000b07025cc9514b49258c00031997106d7b9cd81924a9f310828f818760000e191c99000000000003c6748ccd83f61af88250ca20c7406f80b840f38420000000618f13b1c0566de0000e0c0f76ea068c9f000000000000000b08f84d10dfb9e83925f70bca615e2916002e24fa61bb0372c1d143f64027237829967ee939f3dee31c00000e3f34eb15d470c5b700000003c68d44dc92200014ab7042d2b40002c5ec1ff9a2ec6a9e74800083ceb3624fb000061a6c4ac00059eef16e8007671adcac30eb5bd44cb886a986177d43778cf48a98407230706a6381a2a4e0870d21b38c202425f0cdc306c2712be900000018364000007f2891b2c60fdf0b1a1cd902ce4381890000855c08ef965c0cc21740a2f4a348d6e07a85f392de2e6000149d2d3c000144d5e0630336149c066c3cd9e95ad1b67f882f84c000b65da09869a8f057d379cd3000000002510000140453188564caf59619bc2000369a8000c22253d988b398a005575548da85f7716bc3218e73813c182a76446dd8bf43ba17b6c90096b702db0228032040c0c46358cb8bc47313502614e601de5b0da634c5098b3d23e76a7ce32992c358a4312add05b207d43b38d0dd44437a8171cfed8fee80cc26d4ca95887173c2ca02fb9afe15dc41d44ec075e091c7240149046b82904568723010ba66a4ba894c0456ab1c6db691e07c012216d5cc7716e489624da25f10c3c24324eea150da582970791c75507ab0d0516b857f474403ec610805485443c005e6ceb945c12a7e10e8113db9f2db12a8ca42cb503e6e25842b8da6d070768b8c409b113c3201f6cec1500369116ee5dcc944a3b4074c6b8968081c2034cd1d146a225225e894190a10d356ae8cb006f71f900334282c7f239bf02a25269a27017a59c0128832000041c02040080e1472868001f0095000440200c2e060a23e1e005200c0c055409c08522004856221b00800010195c12050880408001100434080d8d800061a01000260d84c0003100100400038ac1c0a0a0000409080440a022e0282057090000001028000a080007824001401400103284c4e0e0a02c0605000241603010201c1e008006225018000a080180c060509814027800018060a2000002061e00c00010080000161e014000100008cc10010000a01030080002020381c160703000080300002b8040086e0400020041a038003e00000000a000100c001a039241a07000402a7604800063c080001c004301c040f000300200098100600010200a000081000010180c0412060cc0200018040e08050000001068180000 else 0x489ce72c899bc2511f5c1598b925a35b9ae653cb109e5f402873f05291c33b2dd1ba2b6d9035bb923a18bec0ad407ba22110058442b66676ea4108c651182690038402ca031f4d80b491c40a3727d44a979ad13a17254c75e93ff0e4e65eef998f768124661089d034b11a87c7828f51a321333cb64b81be00b2129ac5a0170712a40b400000000001a53445400000001b4502d89885f28e923caf479d40000d3110c58c620001f240000753db8dbc4946fdf181221bd1bf8babcafc094d39843624b4f1bd94788e50000301f27058ba44660001d1c00001cbad8d40001cb7c9a0000112c9496087342b1e5fc000692a7a4184bc0003cb6104800008ce8000836e72b000000004ba957fac930000000000032f1d0c5f23803d80003cc7f335832c00041eb71de067000079ea03d822d80006835233dc7b4000503a49700000c4954b3e03560ee879104993000000ca4c8413189253f4d991d6d9efc5524075090b051280a447e014c0b40002c53d17800000003087800049dcf396a1f60ddc21ce1e00000000c184d3a800010e900000002470685e000000000fce531d04d437148021dfa8eb66e0885a4dcc079f0884aed1f8a07f03f400048a0c17702b26451117000023d544a295bd262b1104c298208b0682f2a90bc6c892731940004027c8c7e48b20da14a721000022af8000a0aba186c8304f34bf3d2f1010999f71ddc1630d934f49b00a6426e20000ba30000346f80002008000286d7464e2870608cd2f4bd0000000000079ba000016f80000000c1b0927000058c90000621f8bdd037d1e733d6e3ba082eb7a822fc11b17a4025122e838d138d3a5455745d7d272283a5b30a161e2fbc083eee308503f1f327572e1d893ab8060bf20f01f2f24f1236696b1c5c011c48ce4cc036ec0165a90e8d530a234e13e83da05241e285f24e4111831e1b51523991c2f327f39d252c456c941f6502004db6000187980000000b0ee948800000005357678ca7800000000c6b8c1c882ea0386539ecf301100000001cc8f1fcd38e83fde75ecf1abe2f41a87118c0000190aeec2f1fa000000020518000e2c9022a2c680007281149409be19b209c000000000006885379cc5500000233e3d1c4249a92102f5834c300000144561000064237b7e00024b30000193794a64558000f061f2c306a10d07278000222619776930d7158ee717e0000000062f800081daa581caffc2419bb1128eda70027a4975bb8ff388e6b8f)
def hashrestrictedl10 (i : Nat) : Nat := 0x3152b8edb964ef3fc0c002b256fa5d1f878a5d56740ea51c00022340dc4b0003eac9d5d400034d790510dc3c33ad4d0068cfa54001d0b28349000000028fd024f40021a241478b668000000001477eb62bc002881a5da7ace99448e01871c5990982c65871cf9d2f86b194c5fc400c91340004a92c29a5821daad648c28861ca11953c15e698c6e253a761981b76a800224763097b968001588202eeaef5917ad12ca0445b0d624b699e17cca2e5869d4db060a6c71f89b576931cd3c481bc45192bcfecad02fcbbce7eb208fc78418c4ec10acc8584024ed827ad8c3689f94815a526513438b200000000034f2c1c91c00197045400023c0018bc002228c8ba964c4003c7f5ae16de0982a13b1cf40912358e097e240012c6831a900002189a4bd0790f1b806700364004104b99f041082101206060007acd0010810466420400010000c0002
def restrictedd9 (i : Nat) : Nat := (if i<1 then 0x1a30c230c230c020c23080128141000884160711871185118416842b0371056085608000a42010200000000000000000000000000000000000007800f800b8008000f001078008000078008000000000001e002000000000000000000388e0f7ede774dbf6ad9760d6f56d4741cf32cc7317c4b0dc2303bfaf9bd2efbaae5b56c5ad6a5a56909d6709825090230882107d5e5755d072dbb6ada66859c65d926358860d7e5e5745bd6a5956056d565454c51d424f5384cd2e4a52447d1a455053d4e5380db358c6304b12b0a72889d2348820c7e1e4741bc6a1946016c4b118410f0370c82d0a023078190500f028050029ff5da70cc04f4ffaed3a66027aefd769c32a13f57d784e19509e3ff5db50c984f5f7aed3864c27ebbaf09c32613d7debb6a19309faeebc350c984f5fdaed3846427ebeaf09c23213d7fabb4e10909f5ee9c35014a6b57faed3825d258ffb704d26e92e5fda825c394972febd2714ca4b1ffaeda864c25f3daf0942ae91fdcd784a13748fde69c2509aa474ffaed5866023a7fd76ad33011d5febb5619708ebfb5dab08c8475feaed58424238ffb7054a6b1155ecb7695290e2abf5daf0ca84f577aed7864c27cbbaf15532613d5f6bb5e11909e6f75da541c4ef1fe42c9a5e135b79a564c2709ac5fc9b69c384962fedd0704ba4b56f6d03825d25abda561c12e92d5f90b0e097497da69c2509aa4b5d726d374d525fa9a6e93a6a92f55c970e535496ee6db874942477f146c3a4a123f39af09426e91c5fcab9dd9548e2febdd54caa4747f6dc5a66023a5fb6c2d33011d3dd3b1699808e9fa8d8b4cc0474fe42c5a660238bfb742c32e11d5dd3b1619708eabedb8b0ca84755f6dca865423acfb6c5432a11d75d3b2a19508ebb695950ca8475dd46ca865423aef2165432a11d5bdb71619408eb5edb0b0ca0475e74ec5865023af5a562c32811d5f5b71611908eb7adb0b08c8475f54ec5846423afca562c23211d7f10b1611908eafcdb8b0848475be6d85842423afb2762c21211c7f9ab1610908ebf4958b0848475fc46c5842423b3bb702ba6f19ddcd2b15d378ceeec858ae9bc673f3aed2a1623397bd76d40af19cbdebb6a0278cf6aebc34a13c67ad7a21a509e33dbaaf08d04f19ebd688468278cf5ed4421413c67a77a20a7496339bb9573ba4b19cddd7baa9258ce2febd9532ac4537baeda7226229f9d769d0b1114deebb69c3888a7b75db4a1c44573b6d8389de22badb6a1c4ef115dadb40e27788aef28d8713bc4577a42c389de229bdaf654cab115d6d7b2a65588aeb6db8752ac457da6c03a95622badb6e1c4ab115f2db40e25588afb4858712ac457736dc898ce22bf8b6244c67115dcdb71623388af66db0b119c457f146c588ce22bf92162c4671179ce889de3388bda7444ab19c45f539de558ce22 else 0x490802b042484000000000)
def restrictedl9 : Packing := (118,4,7,0,1,10,0,restrictedd9)
def restrictedd10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xefdd2a16233bf72a5288cfbdc894a233ff30a5288cefdeaa4a233ef75e1288cefdda50a233bf72a6888cfbdd78a2233ef7562888cfbdd28a2233ef72a6888cfbdc7aa2233ef716a888cfbdc2aa2233bf76a1578cfddd7855e33bf76a0578cefdda849e33ef7a21278cfddd7809e33bf76a0278cfbde8809e33bf72a6778cfddd789de33ef7a22778cfddca99de33f77226778cfddc8a9de33f77562778cfddd289de33f77a22778cefdca949633fd7165258cefdda849633ff34a1258cfbde8849633bf769d258cfddca749633fd755d258cffcd2749633f779dd258cefdeaa49633bf76a0258cfbde8809633b7f69c5888aefda616222bef5285888afdd3a16222bfb4a85888aff51a16222bfe4285888a7fca94e222efb4e12888a7fca9a2222efb4a28888b3fca9a22229ff2a53588afeda849622efba212588bf6d35496229ff2a65588bf6d2595622bfb6a12388bbee8848e22bfb6952388bfcd288ce22ef7a223388bfcd258ce22bfb6948988afeda322622bfb6a05988afeda316622bfb6a03988afeda50e622bfbaa97888afeca956222bfbaa95888bbed7856222bfb4e85888afeca94e222efb2253888afeeaa4e222bfb69c3888afeda50e222bfb2a68888bbed78a2222efb5628888bbed38a2222efb2a68888bbec59a2222efb0e68888bbec5aa2222efb0ea8888afeda855e22f7b5e15788bbee8855e22bfb6a13788bded784de22efba213788afeeaa4de22f7b5627788bded389de22f7b0e27788bdee889de22bfb2a53588bf6c594d622bfb6a13588bf6d584d622ff34e13588bbee884d622bfb69d3588bfcd374d622f7b9dd3588afeeaa4d622bfb6a03588bbee880d622bfb2a65588bf6d5895622efba225588bf6d3595622fdb2a65588bf6c8a95622fdb0ea5588bf6d3895622fdb0e25588bf6d3795622ff34e23388bbee888ce22ff34de3388bdee778ce22ff34d63388bf6e558ce22ff32263388bfcc598ce22ff322a3388bfcc5a8ce22ff35e23388bfcd588ce22ff31623388bfce888ce22ff355e3388bfce558ce2297faa9970e27eeaa4a4388ffaa99809f57d7865427d775e19309e7deaa64c27d7d5e11909edbda40e277b7b4a8389dedf90a0e27797f26a774965fd7aa65258ffaa99808e77eaa65423bf5468788ceddda716233bb7698588cefcd2a16233bf5468588cefd90a16233af76a0578ceedda615e33bf34a8578cefd51a15e33bf6428578cebdda809e33bb7698278cef5da509e33bf5468278cefd90a09e33e77a22778ceddca749633bb7698258cededa722622bf96848988adeda716222bbb6985888afad4a16222bf34e85888afe51a16222bfa4285888adeda70e222bbb6983888af6da50e222beb6903888afe51a0e222bfa4283888b9ee889de22f5b9de5588bbce888ce22f739de3388bf4e558ce22 else 0x7b7f69c3849eefda60e127bdf6943849efbda40e127bfb4a83849eff51a0e127bfe4283849edfeaa4dd27b7faa97809e7feaa66027cff4e19809f3fd3a66027cffaa99809f77d3865427d7f5e19309e7fda864c27df74e19309f7dda864c27dfd4e11909f7f938424279ff2a5389dedfda70e277bef690389defed2a0e277bfe428389dedfda84de77b7f6a0399dedfca94e277b7faa9389dedfd2a0e2779ff269784d73fd9826135b7f69c984d6efda626135bfb4a8984d6ff51a26135bfe428984d7f5c5a4e135bf7aa9384d7bdc984e1359ff269284d7bdd384a135d7f5e1974d67feaa65d35bf76a1374d7ddd784dd35bf7aa9374d7ddd3749d35f774e2774d6efda60a535dfb4a4294d67fd8aa65359ff5ea994d67fd2aa6535df74e2994d77dd37a6535d7f9de994d73fd984a0359ff6a1290d77ed284a4359ff26938496dfda70e1259ff6a438496fbda40e125bfb4a838496ff90a0e1259ffaa9974975fd3825d25d7f0e0974967fc9a4dd25f7b4dd27496dfc9a9dd25d7f25d394975fc970e525df74e439496dfd7aa6525d7f25e994967fd7aa6525d7f5ea994967fd3aa6525dfb49e994975fe77a6525fd74e135497f6d284d525bdf69d35497d7c974d525fd74dd35497f6d274d525f5f9dd35497f6c2a4d525bdfaa935497f5c394d525ddfa65354967fda864c25df74e1930967feaa661239ff6692848ffcc3a4a123bfbaa92848fbed784a123efb4e12848e7fda865d239ffaa99748fddd784dd23ff34a13748efdeaa4dd23d7f6627748fded289dd239ff6a19548f7ed28655239ff69d9548f5fca765523df74dd9548f5fe77655239ffaa99548e7fd9a49523dfb4a29948f7dd37a6523d7f9de9948e7fd9a160239ffaa99808f3fd5866023cff1619808f3fd5a66023cff1699808f3feaa66023d7f5619708f5fc5865c239ff6a19508f77d5865423ddf1619508e7feaa65423ddf6a19508f77ca865423ddfaa99508f7bd5865023def1619408f7f55846423dfd1611908f7f95842423dfe1610908e7fca95e233bf74e8788ceff51a1e233b7f69c588ceefda616233bf74e8588cefed2a16233bfd468588ceff90a162339ff2a5288cfbdd384a2339ff2a6888cfbdd38a2233aff6a0578ceefda615e33bf74e8578cefed2a15e33bfd468578ceff90a15e33bf76a1378cfddd784de33f7715d378cfddd3749e339ff2a6778cfddd379de33d7f2a6778cfddd389de33bf76a1358cff5d584d633bf769d358cfdde774d6339ff2a5258cedfca749633fd74d5258cefdda848e33ff34a1238cefdda748e33f779dd238cefdda548e33bf769c898cefdda522633bf7688898cefdda81e633bf76a0598cefdda216633bf76a0298cefdda50a633bf72a5788cfddc795e233bf7aa9788cefdca956233fd7165588cefdeaa56233ef75e1588c) else (if i<3 then 0x30e3d38b8e1f3840e0137c8de33750dc536d8da73660d8935e8d613548d4334d0d253458cfd33b8cdf3368cd53340ccb3318cc132c8ca33228c7b31b0c673138c3f3098c173048c0d3020c032ff8bf92fd0bef2f80bd12ee0b9f2e68b8b2df0b632d28b452cd8b272c38aeb2b20aa52a08a692918a2327d89e727389c926e8997262097925a8951250893324b891f246891524188f723a08d923288bb22b089d223887f2198857212083920a881b20307fd1fe07f31fb87e91f907df1f687d51f187ad1ea07991e0077b1db07671d887531d3873f1cc07211c206ef1ba86db1b086bd1ab869f1a6868b1a1868119f067719c866d19a064f1928645190063b18d863118b0627188861d183860918105eb17985e117705c316a8591156852314284d312e84a11220465109040b0fc83cf0ed839d0e1036b0d483390c582fd0b902cb0ac828f09d825d091022b08481ef07581b30668181057814504b011303e80e103200af025807d019004b00c80190002ffeaa5e538bffaa9294e37fd794a538dff565294e37fd590a538bff694294e37fd79a6538dff4a6994e37fc7aa6538dff0aa994e2ffd5a26137bffaa9384df7fd984e137f7f5e1384df7fd38a6537dff6693849effeaa4e127bff6943849fdfd384dd27dff6693809effeaa4e027f7f5e13809f7fd3a66027dff4e19809effeaa4e277bff4a8984d6ffeaa4e135ff75e9384d7fdc9a4e135ff74a9384d7fdc2a4e135ff7aa9384d7fdd384a135dff4e1974d6ffda84dd35f7f5e1374d7fdd384dd35bffaa9374d7fdd284dd35bff6a1274d7fdd3849d35f7f4dd274d77fd980a535ff74e0294d6ffda80a535dff4e2994d77fd28a6535dff4de994d77fd27a6535dff66938496ffeaa4e125dff4e197497dfd3825d25ffb4e127496ffda80e525dff4e299497f7d384d525dff66938096ffeaa4e025bffaa97848f7fc5a66123dff5e19848effeaa4e123dff6613848ffec5a4a123ffb5e12848ffed384a123f7f5e15748f7fd9855d23ffb4a15748f7fd5865d23dff4e19748effda84dd23f7f5e13748ffdd384dd23ff75613748f7fd3865523bff6a13548ff7d584d523dff6613548ffdd384d523ffb4a13548effda74d523dff65d3548ffdd374d523bffaa93548f7fd78a6523dff5629948f7fd57a6523bffaa95808f7fd5a66023dff5619808effeaa5e233bffaa9588cfbfd7856233bff6a1578cfdfd7855e33bff6a0578ceffeaa56222bff4e85888affeaa4e222bff6a13588bf7d584d622ff74e13588affeaa4d622d7f5e4794e37ed290a5389ff5ea994e27fd2aa65389ffaa9970e35fd2a65c38d7faa9970e37eda74a438dfb695290e27feaa66137cff660984deff51a26137e7f261784de7fd9a4e1379ff62a994de7fd5aa65379ff4aa994df5fd78a65379ffaa9980de7fda90e12 else (if i<4 then 0x620b02410380083800c161e00200d80e144216098320e03170010183c0040544502e003c007800f001e003c0078009501e003c007800f001e003c0048f83c5c007800f001e003c0048380c5c00780080000000678780091f078b800f001019ea78b80099f060b80080000000007001e00254450223e0f103800f00120e03111f07881c00780099f0608c41041419880e1723334b403466267e0a0c360105918a00a0cc40533f1a7e1d88c07120308a007081c004160502d1c5018a0301843603849407800822808009407800f001e003c007800f001e003c00780091f078b800f001e003c007800f001e0020000000001c0048f83c40e00245c1620700100026083800f001e00245c16223e0f10380091f07881c0078008380080000000023d031000000000000046040040c8c1000093a0b149d058a188e4424c0d0c04e1c95ce81a1809c392c311c88ce81a1809c39299c4588ce22c44599c20443f0e46140ac16a51cbf1068fe0b147f0588ce2fcb9199c5c88ce2e44671722338b911726708bf24c467950498cbf24c45f926224cbf11305c88cf20cb919305c88982e445c9302e5f88117e5c88cf20cb9199dc4082833b88199c5c88ce2e445899c460cce2e446717222e4ce119c4588ce22c46711623388b119c45888b3385cbf102e5f88172fc40b97e205cbf102b01abedaf7abc5aedab9dae12b6bad72b4dacd2b1bac5ab07abbaae9ab42ab7aaa2aa3aa02a71a9b2a5da912a2ba84aa03a7d29dba6e299fa61a977a5a294fa502927a43a8eba34a8b9a282873a16a841a0a280f9fda7e79f3a7b59e4a7799d5a73d9c9271f9bf26e39b7a6cf9ada6b19a3a67f99c26619922639988261197e25df96f259995da55d953a535944a50393d24e5935a4bd929248b91ca44f912a43b908a4098fea3e18f4a3b98e823878dba3558d1a3238c2a3058c022dd8aea2a18a2226f895a23387f21f7872a1c5868a18985c2157852212584320f3836a0c182a208f81da05d813a0358049ff97f81fbd7e91f777d79f457cb1f137be9ed77af9e9b79e1e557919e3778a1e197829ddd7761dbf7671d797581d3d74e1d297469ccf7211c6b7121c257031bfd6f91bcb6ea1ba36dd9b5d6ce9b2b6c71b0d6bd1adb6ae1a9569c9a4f68d9a0967999cd66d1991659194b64f192364018fb63618bf629988d61d1865615983360698015f797c55eb17935de976b5d7174d5cd171b5b916cb5b196b75a7967b596163f587160357d15e557315b3566958155a154554d951353c14e153494c3528147d519144150a14054f893c94e9938d4d8133d4c9130b4ba12cf4ab128949c124d48d121147911d546c918f45b1149449910343810b3426907741c90454088fff3f70fb93e58f873de0f693d40f373cc8f233c78f0f3c00ef13bb0ed33ac0e973a20e7939a8e6539 else 0x582a8a06140454040420c50584361244d1848200804108c11482160642c8c24100050848160800204c2050071406100052788e333c2080c391848205007161e0809310a1e143e4e10162486c301446121e248a310c6210502414621c3c10106e1688140cc071a1e2b081401c467c18243ccf030492028248810050402092204014100808092308081b08040d840880e248e0f15841b00e248c3601050180e200052788e3010061012808040208067a19278e0b080a12c4202562242c20205828a020105a280c2d12070185a328e230dc622446038c04008402840403c447a07018c490a5012c4294040201040240c281804140c020a4f0404b18203080a1208050404588405154458870b1544010082c0c141004020802010403848f1220f18040208000600f118610846230c2c0ac41601c20b02b1058070a446742d18581e0aa0b0565019dc40ac161000482a1b8c220b0419858209c0e14161118188c461601c24a0351650070b2803859401c24a00e1250070b2803840304cf93c402028280e188e450c47220c05063c71cc30209f970e60624311c8a188e450c47228623914311c893ee203718581208c40683a18941662a34544a0b07c007800f001e003c00448010570508015814132e2b0283e045605062b0282e04141586002c2060424b3c0c13f0c1401438182786e67a1803892711037109820c62303c560dc62b06e202c254078243e0f119e540283004601029cb90320ac41189c0a0c0b08161e0020285a20882d100b0285a3147880d861be3a168c2e1241b18a6168845317150b486203e168c3603851fc7220401b0c071f8581bf1040c42d10081a7856127e08516302720d822304804105a12081103841b00e200c294040715b88180e2b0802158501c0c2b0c560dc4038ac240e0312062b080608ac140c31fc26284e3f10480e021c001c50802f10003085bcb880533c2d182bc406a30b00414061bf1030b788100c1e00285c1620b8191088168b971304210ac208c290dc7c004241301b18880c972300c3018780099e8606c31183186071fc162e5e0c0e071fc162e5e0c0e061c08cca8e3f82c5cbc181c0c1a0ec40340cca8764e5e0c0e060a02020683b172f0607030501010971fc163e5e0c0e071fc162a5e0c0e071fc162833970e07cba162a85a4e002250598a8cb1140141e462802833133f05066201c218f231401419880a67e308c480540e21070188180c4461803d128bd0b08251460e0c57c0c141e9c5881c315d030507a7172160f800c161830241c0)))
def restrictedl10 : Packing := (515,3,7,7,1,14,0,restrictedd10)
def restrictedd11 (i : Nat) : Nat := (if i<1 then 0x40b1f899d0bcbe2090b58aa32f882b3a5197c411623fc40d1f28cbe209280365f1048001fe07eb9f857d4df337be1ec6799de3e7879df57731dac75a1d4874a1cf67335c8970cdbf86f61b8b6d89b396c41ae76af9a716945a3168219df66d998d654990562bd86b61098195fe57d05ec17875d317115b7d6b65a5963758155c1561953053d54b15245456506d3d74e713734cbd2f44ac127548a11f646ed17744850cb428907940f90153fd4fcc3eb0f713d20f043b24ea039dce2137bcdc6362cd6234e4d1032e8c6d3110c092f38b9c2da8b412bf4acb2a88a79291ca15278c9b1264497a256893a248c8f1232089621b483b20487e01f007971ddc74e1c946f31b28698199863418505e217085ab165056b14e451013784b5120c46c110c4110fc43bf0e343640cec3120ba42c90aa42800980240088020007801c9068018905c815204ec12404340f6033409b01c805200a4000ffebca71ffc794e3ffa529c7ff0a538fff4ca71ffd984dfff9309bfff5e137ffe9c26fffd594dfffa529bfffa6537ffe9c24fffc3849fffa7013fff4e277ffe1c4efffd784d7ffb309afff26135ffe9c26bffd284d7ffb2e9afff4dd35ffe93a6bffd294d7ff8529afffa6535ffe9406bffd38497ff87092fff65d25ffe9ba4bffd39497ff87292fffa6525ffe9aa4bffd38097ffaf091fff56123ffecc247ffd3848fffa5091fff55d23ffecba47ffd3748fffb2a91fff4d523ffe92a47ffd5808fff8b011fff5e233ffe3c467ffd588cfff8b119fff4a233fff44467ffd578cfff8af19fff49e33fff3bc67ffd258cfffab1117ff16222ffe9c445ffe8888bffa6b117ff95622bff4ca717fd970e2ffa521c5ff66137efebc26f7fe994deffb301bf7f4dd27efebc04f7fd9809effb2613f7f4de77efe1ccefdfd389dfbf8713bff74e135bfecba6bfdd374d7bfcee9adffa6535bfecc06b7fd290d6ffb2e92f7f25d25ff693a4bdfe77496ffd3292fdf4d525bfec984b7fd9848ffda5091dff65d23fee9ba47dfe7748effb2a91dffa6523bfecc0477fd9508ffba7119ff74de33eff3bc67fdd358cffba4719ff722633fee3cc67fdc598cffb85319ff75e233fee3c467fdd588cffb8b119ff74a233fee14467fde888cffbaaf19ff715e33fee93c67fdc278cffbcef19ff749633fee12c67fed2888b7fd11117fb49622ff691c45fde3388bfd913117fb16622ff61cc45fed7888bfdab1117fb16222ff69c445fec3888bfdd11117fb55e22ff69bc45fed3588bfd86b117fb95622ff719c455fd970e2f7b281c5fb4a438bfc848717f9090de7fb3013dbf65827bbeca84f7bd9409efbb2613dfd46427bfc8484f5fc97496f7b2812cff66023afecb8476fd9608eefb2a11def65023bfa8c8477f90908f7bd1119f779de33df744445dee7788bedcab117f38ce22 else 0xb1546232e4232fd72347aa3102dcb941846862fc8b12201b10512b3b103718319d0cc0158586059399d0b1b94482847b389d0f940b711975338a83915107e33160c0b23198b088f87e227e49422c3634a93c188c0333e727234fe723670b272341c0f2e56c4150797248ec80c09c4f2f0c2b050e1018a0d9c4e98c0f2e0b4850a1971695b106541507236720e9d03188b72e0b40429cbf1c9072989c95880c862fc28402c3cac142123119716914637919180e56cbe210ce260b46391b06c623518dc5a41c952722d20fc6c1bc4100436878b481805926308b1c992a4827831180667ce500647810485687c1b103f481853060815711973a551e2f03116397c40188b920018604242e47e41f8b0083168ff1006233c7f3fc00bc0c667afa9e1003620cce1f8280d80293c213f85906ccf860c0c832a8c5630316c2e0d9750160ace162e4a2d543209128cbc2ce0741b39630386192605829399c0341c4c5a958a0d9d3181c2cc832465d7303858b4ec8862fc68fa72fe1f0b07199c83a72c6070b33380b05a704d262d392116c885e227e61b1463093223d9e4f87947113f3a3d16ce87c2e506675391e0f0a4ff1076722e9cb985c0cc0f1302e9c4685e5f108240dc0c4e059450a8271200d88303c04ce858df2f883938168f81b3a1637cbe2124805892622d85ca32f884918623f0590662c1fe2084f67c1a30271c98a0060c0e4997030e46ce028fc724188fd1634789916cecbe20d2311b391642703d9c5687e5f107221255197858e4c56cb8dc724a740f2e392110040b98958290bcbe212481881b2e0b29232e061c9088052481c7e3931240e3f1c90ac071f8e494e858fc724220140656988b60797c42416032b0b51703cbe21048cb81872407b385b28cbe20c4e670b40d97c4189033160ff105160dc523fc4169d0f1fe20844141585b28cbe20e489465c0d88283c8c3f059088491f82c8b1419132e0b2b3906b1cb82cb4e87aa32f0b2b39508fcb82cb97036206ce05880abf5c8d6397060d7e0b101962cecbe20a05672fd724032c59d97c414190c672e48b10333b2f8828159cbfc411628385b3b10502e5d723064317e9320157f88183218985c919d0b5fae48ce032c72f88283218985c911e44030ff1056743e173fc4159c8f030ff1051f81b103a743e7e06c4159c28c40c30b910fd162478187f88201962cecbe20a0381b39724588199d97c41407036722c8b10340d9d8828fd7226723c7f8823380cb1cbe20b97032e46ce0340f2eb92b39639703620a4803138164240189c0b21200c4e0590900b03138831058fc6060c0e464f0300c724030607231886018303060723030607231c8183031f8e4448078fc1841f82c43f05889e28058c7e0b10fc1621f82c)
def restrictedl11 : Packing := (176,2,7,10,1,14,0,restrictedd11)
def restrictedd12 (i : Nat) : Nat := 0x3ca1382e5e20c900c9c1644e310b2897883189f858cc4fe2060c307234e0b3f39227019885cbc41920c41a5c2ca9c1662512f10648061839227079405834bc41cfc2c49c1e500d2e1664e0f0b063f88318944bc4102e5e206512f103ab68894e36865fc75da25d54046cde3249417c3a07400ffd38ffc38ffd37ffc37ffd27ffc27ffe77ffd35ffc35ffd25ffc25ffd23ffc23ffe33ffe22dfe77fde33fee22
def restrictedl12 : Packing := (18,1,7,8,1,10,0,restrictedd12)
def restrictedd13 (i : Nat) : Nat := 0x2e205ff
def restrictedl13 : Packing := (1,0,7,5,1,0,0,restrictedd13)
def restrictedsamples : Array (Bits × Bits) := #[(0x2453cb22a70c5210332d0323c4f091816008074685802218b0a040a85951203063c7820104a00f4044043c0602103430189d328898110230252a1a6191091910c502400a210d1b4342404213601a4179a0a93080184c00604b808838014ab4c0,0x84128080840952001208020380d091886008062614812210808040a8305120204205020002a00e0040803c0202102130188110809050921021000841098909008000200a21081b40424040122002416980a910801848002049008038014aa440),(0x38010540050a06740823408020148308f61f898520749c00206114422a45c041810382a7111a00398010040dd85c2c526408c5726262906d880208a40048627203c90b40c6000b0851c396005a40e024054013342210f0090374147b0214101,0x30050440000a12440023000220000308e40a080424609800044204402245c041000b83040018013180000518c848205240004142600200dc88120840004002020388234086000b08010386001a40e00401001334021070010350107b0014100),(0xe954138d16845cf0809c381bcb25b8406312488e2a15e5a88e390bb438c73756cd651d5dc0be5191c164c22c934de58064809b70398e12c2329e6270c5f2098d1f128854d5145c554c44a51c436c70628da1b449233338c61c80c4c88a458e05,0x685c0791148440500214091b4121a8000112410c2401e4280a100198280223524524040d0028512003642020116110808082994001060400121e0250c48208041f020c00d5145c054404851c404840420da0b440221228c60c8044400a448401),(0x85270525d40a6c09749a92e59c0c63aee160045320f00a46ddbcfce3812b9150562263c4b6d09c8360d8c5103c0c0a29d54c43b6144438c50f1929d0223a671b289950b8a18b49403b7214a61aa1aa08288d4d244898f212615402abd8906134,0x942200200008240930889060188441a8606000410070024394a28c0481211020120000c094900e084498c0000c1420085164028714403841050120000018631b008840b0208b01401b4210820aa0a208200d412408085000215402abc0106014),(0x4c090356ee92181ea517e38363793336c7875b054734f3e4eac1054a481cc37929e0f5256c6cf777a0f78b7898c5d45cf1ca845c0c2146a180081eb7336124b42cf70846b4f88003a09f9be1701f594e14122e57a285a277bd1118002e3453e2,0x4009031663968806814725886229260681157908430691a42a4501430808431929e0dd24680ea173a06603781083d4c4a00a805849210480c04816b6b26204c42637004494708003a09d8b61501d180614122e53a285a257940118002e2413a2),(0x187a486011fd20dd6eb1403434a7465c1bdbe8c1e15c153e1f7b0250891a679bb3404362492885293643168343a2908288713cc6d324e527cd33850ecc862651d94acb814ce7e09f3811c812040006963f10ef91b8080d08a2d53f92cf46a009,0x12484020116400532c91c0101424463003d36801c0541028337a8a0001221492a1604542000081012663020000a090808070004400060d2704108008c406065518ea0a8004c5609f38118800040002122b00ef11a0000c00a2902f82ce040001),(0x286a13a9ae4e707b0fcc4b105629749446e552ed8261c4530b29b8ab601892e079c5586941d3c06dfd7afe064592064ab960b8d5ad43d7eb06406037d26fc6e832c2cc336416f65e18b01478e4b0251d16646623d428c03a5ea2aed23388496,0x4466211a82440403a8b5c4a114461dc86006450e9000047530b29e88b001a12a0114450014183c44c6dbe6086059205299040bc958c41d6204348243792a654c11020cc334016b45610b01078e4b0051916446003d028803a5c22ae803308096),(0xf03632c8e85288ac990e2cf6aa92c54cccc2b6869960911646040052c3d78aa7d8953090a90a619ab1729a3f6efea7031e08a01a4818e6586b656c194b4c11829401734d2a32116cc02b7a292ae210ad901fd10eada5d3a40466b111510c2a2a,0x80209040a81a888c900a0424a292014e5404948219a001964484004244d5c82508803090a102289ad810885f6a1e2d431708201aec09e25868612c811b09518a8000704d2a220160802a72212aa210ad901f000e0da5d3200066901111082a2a),(0x888ae064ca397c1d040714a93422195181dc4314c898f2b5955e28316254eca290edeec1384e8b4121a30e329930e2d0226759821f183d898c6b39524d95ae0a24cbd285320b78092a4a628f884c425472a02d844c3610d4029463236c9175a,0x8809e056c8191804042290ac1180005180800300e812900480520030644424108029a04030540b0100010e101020e2002032410213982889842019402c110208204b1084320940080a4262870044424440200c840c1210c4029401030c91748)]
def restrictedcolumns : IndexTree ColumnInfo := (.fork 44 (.fork 22 (.fork 11 (.fork 5 (.fork 2 (.leaf [(1,0,510,0,12),(2,0,509,0,12)]) (.leaf [(5,0,506,0,8),(6,0,505,0,9),(2,4,369,136,7)])) (.fork 3 (.leaf [(9,0,486,0,8),(14,0,497,0,7),(10,4,369,128,6)]) (.leaf [(17,0,494,0,11),(18,0,493,0,9),(18,4,353,136,6)]))) (.fork 5 (.fork 2 (.leaf [(25,0,486,0,8),(9,16,486,0,8)]) (.leaf [(13,16,482,0,5),(26,4,353,128,5),(33,0,478,0,9)])) (.fork 3 (.leaf [(1,32,94,384,7),(37,0,346,0,5),(39,0,344,0,4)]) (.leaf [(49,0,462,0,8),(57,0,454,0,5),(65,0,446,0,9)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(1,64,188,258,7),(66,0,445,0,11)]) (.leaf [(70,0,441,0,8),(66,4,305,136,6),(78,0,433,0,5)])) (.fork 3 (.leaf [(74,4,305,128,5),(14,64,177,256,5),(81,0,430,0,8)]) (.leaf [(82,0,429,0,8),(89,0,422,0,5),(97,0,414,0,6)]))) (.fork 5 (.fork 2 (.leaf [(98,0,413,0,7),(113,0,398,0,5)]) (.leaf [(129,0,382,0,9),(1,128,346,36,7),(130,1,332,48,6)])) (.fork 3 (.leaf [(133,0,378,0,7),(5,128,346,32,6),(134,0,377,0,8)]) (.leaf [(130,4,369,8,6),(6,128,345,32,6),(7,128,344,32,5)]))))) (.fork 22 (.fork 11 (.fork 5 (.fork 2 (.leaf [(142,0,369,0,5),(138,4,369,0,5)]) (.leaf [(145,0,366,0,8),(146,4,353,8,5),(153,0,358,0,5)])) (.fork 3 (.leaf [(161,0,350,0,8),(129,32,94,256,6),(33,128,346,4,6)]) (.leaf [(162,0,349,0,7),(35,128,344,4,5),(165,0,346,0,5)]))) (.fork 5 (.fork 2 (.leaf [(37,128,346,0,5),(166,0,345,0,5)]) (.leaf [(177,0,334,0,7),(161,16,326,8,5),(145,32,78,256,5)])) (.fork 3 (.leaf [(49,128,330,4,5),(193,0,318,0,7),(194,0,317,0,8)]) (.leaf [(198,0,313,0,7),(194,4,305,8,5),(70,128,281,32,5)])))) (.fork 11 (.fork 5 (.fork 2 (.leaf [(210,0,301,0,5),(225,0,286,0,5)]) (.leaf [(257,0,254,0,8),(273,0,238,0,7),(281,0,230,0,5)])) (.fork 3 (.leaf [(265,16,230,0,5),(289,0,222,0,7),(257,32,94,128,6)]) (.leaf [(305,0,206,0,5),(289,16,198,8,5),(273,32,78,128,5)]))) (.fork 5 (.fork 2 (.leaf [(321,0,190,0,7),(322,0,189,0,8)]) (.leaf [(258,64,189,0,8),(326,0,185,0,5),(330,0,181,0,5)])) (.fork 3 (.leaf [(266,64,181,0,5),(337,0,174,0,5),(321,32,30,128,5)]) (.leaf [(417,0,94,0,5),(385,32,94,0,5),(450,0,61,0,5)]))))))
def restrictedautos : Array (List Nat) := #[[],[100,131,82,16]]
def restrictedlevels : Nat → Packing
  | 9 => restrictedl9
  | 10 => restrictedl10
  | 11 => restrictedl11
  | 12 => restrictedl12
  | 13 => restrictedl13
  | _ => emptyPacking
def restrictedindex : Nat → Nat → Option (Nat × Nat)
  | 9 => fun _ => none
  | 10 => lookupWord 55 190 6 12 7 1 (hashrestrictedl10)
  | 11 => lookupWord 252 872 9 15 10 1 (hashrestrictedl11)
  | 12 => lookupWord 84 301 7 13 8 1 (hashrestrictedl12)
  | 13 => lookupWord 10 37 5 10 5 1 (hashrestrictedl13)
  | _ => fun _ => none
def restricted : Forest := ⟨1023,13,fun j => restrictedsamples[j]?.getD (0,0),restrictedcolumns,restrictedautos,restrictedlevels,restrictedindex⟩
set_option maxHeartbeats 0 in
theorem geomrestricted : graphValid restricted (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted9_0 : block restricted 9 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted9_36 : block restricted 9 36 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted9_72 : block restricted 9 72 19=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted9_91 : block restricted 9 91 27=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allrestricted9 : block restricted 9 0 118=true := (@block_merge restricted 9 0 91 27 (@block_merge restricted 9 0 72 19 (@block_merge restricted 9 0 36 36 srestricted9_0 srestricted9_36) srestricted9_72) srestricted9_91)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_0 : block restricted 10 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_36 : block restricted 10 36 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_52 : block restricted 10 52 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_88 : block restricted 10 88 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_124 : block restricted 10 124 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_160 : block restricted 10 160 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_196 : block restricted 10 196 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_232 : block restricted 10 232 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_268 : block restricted 10 268 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_304 : block restricted 10 304 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_340 : block restricted 10 340 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_376 : block restricted 10 376 34=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_410 : block restricted 10 410 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_446 : block restricted 10 446 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted10_482 : block restricted 10 482 33=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allrestricted10 : block restricted 10 0 515=true := (@block_merge restricted 10 0 482 33 (@block_merge restricted 10 0 446 36 (@block_merge restricted 10 0 410 36 (@block_merge restricted 10 0 376 34 (@block_merge restricted 10 0 340 36 (@block_merge restricted 10 0 304 36 (@block_merge restricted 10 0 268 36 (@block_merge restricted 10 0 232 36 (@block_merge restricted 10 0 196 36 (@block_merge restricted 10 0 160 36 (@block_merge restricted 10 0 124 36 (@block_merge restricted 10 0 88 36 (@block_merge restricted 10 0 52 36 (@block_merge restricted 10 0 36 16 srestricted10_0 srestricted10_36) srestricted10_52) srestricted10_88) srestricted10_124) srestricted10_160) srestricted10_196) srestricted10_232) srestricted10_268) srestricted10_304) srestricted10_340) srestricted10_376) srestricted10_410) srestricted10_446) srestricted10_482)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_0 : block restricted 11 0 27=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_27 : block restricted 11 27 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_63 : block restricted 11 63 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_99 : block restricted 11 99 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_108 : block restricted 11 108 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted11_144 : block restricted 11 144 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allrestricted11 : block restricted 11 0 176=true := (@block_merge restricted 11 0 144 32 (@block_merge restricted 11 0 108 36 (@block_merge restricted 11 0 99 9 (@block_merge restricted 11 0 63 36 (@block_merge restricted 11 0 27 36 srestricted11_0 srestricted11_27) srestricted11_63) srestricted11_99) srestricted11_108) srestricted11_144)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted12_0 : block restricted 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted12_3 : block restricted 12 3 15=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allrestricted12 : block restricted 12 0 18=true := (@block_merge restricted 12 0 3 15 srestricted12_0 srestricted12_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem srestricted13_0 : block restricted 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allrestricted13 : block restricted 13 0 1=true := srestricted13_0
theorem tablesrestricted : checkedTables restricted 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block restricted 0 0 0 = true)
  · exact (rfl : block restricted 1 0 0 = true)
  · exact (rfl : block restricted 2 0 0 = true)
  · exact (rfl : block restricted 3 0 0 = true)
  · exact (rfl : block restricted 4 0 0 = true)
  · exact (rfl : block restricted 5 0 0 = true)
  · exact (rfl : block restricted 6 0 0 = true)
  · exact (rfl : block restricted 7 0 0 = true)
  · exact (rfl : block restricted 8 0 0 = true)
  · exact allrestricted9
  · exact allrestricted10
  · exact allrestricted11
  · exact allrestricted12
  · exact allrestricted13
def clippedInputs := inputs.map (fun a => a &&& ~~~seed)
def clippedGraph := graph &&& ~~~seed
def clippedPairs : List (Sig × Row × Row) := List.ofFn (fun i : Fin 9 =>
  (clippedInputs.getD i.val zero, absentRow i, presentRow i))
theorem clippedLower (impossible : Impossible clippedGraph 13 clippedInputs.toFinset) :
    Lower clippedInputs clippedGraph 14 := by
  apply lower_impossible (by unfold proper; decide +kernel) _ impossible
  have es : checkEssential clippedGraph clippedInputs clippedPairs=true := by decide +kernel
  have all : clippedPairs.map Prod.fst = clippedInputs := by decide +kernel
  intro a ha
  apply essential_ok es a
  exact List.mem_toFinset.mpr (all.symm ▸ ha)

def clipBy (m : Sig) (r : Row) : Row := if bit r m then 0 else r
def clipRow := clipBy seed
theorem clip_general (a m : Sig) (origin : bit 0 a = false) :
    rename (clipBy m) a = a &&& ~~~m := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let r : Row := ⟨j,hj⟩
  change bit r (rename (clipBy m) a) = _
  rw [bit_rename]
  have e : (a &&& ~~~m).getLsbD j = (bit r a && !(bit r m)) := by
    simp only [bit,r,BitVec.getLsbD_and,BitVec.getLsbD_not,hj,decide_true,Bool.true_and]
  rw [e]
  by_cases h : bit r m=true
  · simp only [clipBy,h,ite_true,origin,Bool.not_true,Bool.and_false]
  · have v := Bool.eq_false_iff.mpr h
    simp only [clipBy,v,Bool.false_eq_true,ite_false,Bool.not_false,Bool.and_true]
theorem clip_word (a : Sig) (origin : bit 0 a = false) :
    rename clipRow a = a &&& ~~~seed := clip_general a seed origin
theorem seedSlice (lower : Lower clippedInputs clippedGraph 14) : Slice inputs graph (~~~seed) 14 := by
  have gg := clip_word graph (by decide +kernel)
  have go : restrictRows clipRow (observe graph)=observe clippedGraph :=
    (observe_rename _ _).symm.trans (congrArg observe gg)
  refine ⟨clipRow,clippedInputs,?_,?_,?_,?_⟩
  · intro r
    by_cases h : bit r seed=true
    · rw [clipRow,clipBy,if_pos h]
      decide +kernel
    · have e : bit r seed=false := Bool.eq_false_iff.mpr h
      rw [clipRow,clipBy,if_neg h]
      simpa only [bit,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and,Bool.not_false] using congrArg Bool.not e
  · intro a ha
    have orig : inputs.all (fun w => !(bit 0 w))=true := by decide +kernel
    have z : bit 0 a=false := by simpa using (List.all_eq_true.mp orig a ha)
    rw [←observe_rename,clip_word a z]
    exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem ha))
  · rw [go]
    exact observe_proper (by unfold proper; decide +kernel)
  · rw [go]
    exact lower

theorem completedRoots (deadCase : Impossible graph 14 inputs.toFinset)
    (clippedCase : Impossible clippedGraph 13 clippedInputs.toFinset) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_live C legal first h (by omega)
  · exact deadCase k t hk hdead
  · have noRun := poolCut_sound (seedSlice (clippedLower clippedCase)) [] (by rfl) (ws:=inputs++[seed])
      (by decide +kernel) (cap:=14) (by decide +kernel)
    exact noRun k t hk hlive
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

theorem restricted_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid restricted prior=true) (checks : checkedTables restricted 13) :
    Impossible clippedGraph 13 clippedInputs.toFinset := by
  have noRun := root_index (g:=restricted) low geometry checks (k:=13) (by decide)
    (i:=0) (ws:=clippedInputs) (by decide +kernel)
  have tgt : targetOf restricted=clippedGraph := by decide +kernel
  exact tgt ▸ noRun
end PEqualNP.Outside.L_meta_2778.Cert


namespace PEqualNP.Outside.L_meta_2778.Cert
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem unseeded : ¬HasCircuitSize 9 edge 14 := by
  rintro ⟨C,legal,size,computes⟩
  have goalEq : (execute C.gates inputs).getD C.output zero=graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates inputs legal graph_proper
    (out.resolve_right (fun hn => hn graph_proper))
  have roots := all_roots run (fun a ha => List.mem_append_left _ (sub a ha))
  have eq : S=inputs.toFinset := roots.resolve_right (by
    intro same
    have member : seed∈S := by rw [same]; simp
    exact (show seed∉inputs by decide +kernel) (sub _ member))
  have no := dead_start (before_sound known383 valid383) geomdead tablesdead
  exact no k t (hk.trans size) (eq ▸ run)
end PEqualNP.Outside.L_meta_2778.Cert
namespace PEqualNP.Outside.L_meta_2778.Cert

def vertexPair (a b : Nat) := inputs.getD a zero &&& inputs.getD b zero
def dSeed := vertexPair 0 4

set_option maxRecDepth 12000 in
theorem no_dead : Impossible graph 14 inputs.toFinset :=
  dead_start (before_sound known383 valid383) geomdead tablesdead

set_option maxRecDepth 12000 in
theorem low_from_roots {v : Sig} (all : ∀ k t S, Live graph k t S →
    (∀ a∈S,a∈inputs++[v]) → S=inputs.toFinset ∨ S=(inputs++[v]).toFinset)
    (whole : Impossible graph 14 (inputs++[v]).toFinset) : Lower (inputs++[v]) graph 15 := by
  intro p bank prog output
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live graph_proper prog output
  by_contra! small
  rcases all k t S run sub with rfl|rfl
  · exact no_dead k t (by omega) run
  · exact whole k t (by omega) run

set_option maxRecDepth 12000 in
theorem high_edge : Lower (inputs++[seed]) graph 15 :=
  low_from_roots (fun _ _ _ => all_roots)
    (poolCut_sound (seedSlice (clippedLower
      (restricted_start (before_sound known383 valid383) geomrestricted tablesrestricted))) [] rfl
      (by decide +kernel) (by decide +kernel))

def dNeighbor (i : Fin 9) : Nat := [1,2,1,2,3,0,1,2,3].getD i.val 0
def dAbsent (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< dNeighbor i)
def dPresent (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< dNeighbor i))
def dWitness := List.ofFn (fun i : Fin 9 => (inputs.getD i.val zero,dAbsent i,dPresent i))

set_option maxRecDepth 12000 in
theorem low_all {k t S} (run : Live graph k t S) (sub : ∀ a∈S, a∈inputs++[dSeed]) :
    S=inputs.toFinset ∨ S=(inputs++[dSeed]).toFinset := by
  have test : checkEssential graph (inputs++[dSeed]) dWitness=true := by decide +kernel
  have keys : dWitness.map Prod.fst=inputs := rfl
  have raw : inputs.toFinset⊆S := by
    intro a ha
    obtain ⟨r,s,diff,iso⟩ := essential_ok test a (keys ▸ List.mem_toFinset.mp ha)
    exact raw_required run _ _ sub r s diff iso
  by_cases h : dSeed∈S
  · exact Or.inr (Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
      (by intro a ha; rcases (show a=dSeed ∨ a∈inputs by simpa using ha) with rfl|hr
          · exact h
          · exact raw (List.mem_toFinset.mpr hr)))
  · apply Or.inl (Finset.Subset.antisymm _ raw)
    intro a ha
    rcases (show a∈inputs ∨ a=dSeed by simpa using sub a ha) with m|rfl
    · exact List.mem_toFinset.mpr m
    · exact False.elim (h ha)

set_option maxRecDepth 12000 in
theorem low_slice : Slice inputs graph (subcube 16 0) 13 := by
  have h := col_sound (m:=511) (16,0,495,0,13) _ (before_sound known383 valid383) (by decide +kernel)
  exact h

set_option maxRecDepth 12000 in
theorem low_edge : Lower (inputs++[dSeed]) graph 15 :=
  low_from_roots (fun _ _ _ => low_all)
    (poolCut_sound low_slice [] rfl (by decide +kernel) (by decide +kernel))

end PEqualNP.Outside.L_meta_2778.Cert
namespace PEqualNP.Outside.L_meta_2778.Cert
def edges2778 : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (5, 8)]
def pairAt (i : Fin 12) := edges2778.getD i.val (0,0)
def edgeWord (i : Fin 12) := vertexPair (pairAt i).1 (pairAt i).2
def maps2778 : List (List Nat) := [[], [116, 83, 32], [118, 133, 33, 48], [118, 133, 33, 48], [], [118, 130, 81], [100, 131, 82, 16], [116, 83, 32], [82, 129, 48], [116, 80, 100, 128, 48, 32, 16], [100, 116, 81, 128, 49, 32], [100, 116, 81, 128, 49, 32]]
def dClass (i : Fin 12) := ([false, false, false, true, true, false, true, true, false, true, true, false] : List Bool).getD i.val false
def sourceOf (i : Fin 12) := inputs++[edgeWord i]
def destOf (i : Fin 12) := inputs++[if dClass i then dSeed else seed]
set_option maxRecDepth 12000 in
theorem edge_maps : ∀ i,checkMap ((maps2778.getD i.val []).map swapRows) (sourceOf i) graph (destOf i) graph=true := by decide +kernel
theorem each_edge (i : Fin 12) : Lower (sourceOf i) graph 15 := by
  apply lower_map (edge_maps i) graph_proper graph_proper
  unfold destOf
  cases dClass i
  · exact high_edge
  · exact low_edge
end PEqualNP.Outside.L_meta_2778.Cert

namespace PEqualNP.Outside.L_meta_2778

namespace SLP2543
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev F (n : ℕ) := (Fin n → Bool) → Bool
def ff {n : ℕ} (b : Bool) : F n := fun _ => b
def vars (n : ℕ) : List (F n) := List.ofFn fun i x => x i
def pool {n} (seed xs : List (F n)) := ff false :: ff true :: (seed++xs)
def step {n} (s : List (F n)) (f : F n) :=
  ∃ a∈s,∃ b∈s, (f=fun x => a x && b x) ∨ (f=fun x => a x || b x)
def valid {n} (seed xs : List (F n)) :=
  ∀ i : Fin xs.length,step (pool seed (xs.take i.val)) (xs.get i)

theorem snoc_valid {n seed xs} {f : F n} (h : valid seed (xs++[f])) :
    valid seed xs ∧ step (pool seed xs) f := by
  constructor
  · intro i
    have k := h ⟨i.val,by simp⟩
    simpa only [List.get_eq_getElem,List.getElem_append_left i.isLt,List.take_append_of_le_length (Nat.le_of_lt i.isLt)] using k
  · have k := h ⟨xs.length,by simp⟩
    simpa only [List.get_eq_getElem,List.getElem_append_right (le_refl _),Nat.sub_self,List.getElem_cons_zero,List.take_left] using k

def raw {n : ℕ} (gs : List Gate) (i : ℕ) : F n := fun x => ((⟨gs,i⟩ : Circuit).eval (List.ofFn x))
def Bounded {n : ℕ} (gs : List Gate) (f : F n) :=
  ∃ i<n+gs.length, f=raw gs i
def Known {n : ℕ} (gs : List Gate) (f : F n) := f=ff false ∨ f=ff true ∨ Bounded gs f
def monoG (gs : List Gate) := ∀ g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2

lemma wires_len (gs : List Gate) (xs : List Bool) :
    ((⟨gs,0⟩ : Circuit).wires xs).length=xs.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp only [Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil,List.length_append,List.length_singleton] at *
    omega
lemma wires_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    (⟨gs++[g],0⟩ : Circuit).wires xs = (⟨gs,0⟩ : Circuit).wires xs ++
      [g.op.eval (g.inputs.map fun i => ((⟨gs,0⟩ : Circuit).wires xs).getD i false)] := by
  simp [Circuit.wires]

lemma persists {n gs} (g : Gate) (f : F n) (h : Known gs f) : Known (gs++[g]) f := by
  rcases h with h|h|⟨i,hi,rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  refine Or.inr (Or.inr ⟨i,by simp;omega,?_⟩)
  funext x
  change ((⟨gs,0⟩:Circuit).wires (List.ofFn x)).getD i false = ((⟨gs++[g],0⟩:Circuit).wires (List.ofFn x)).getD i false
  rw [wires_snoc,List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa [wires_len] using hi)]

lemma eval_new {n} (gs : List Gate) (g : Gate) (x : Fin n→Bool) :
    raw (gs++[g]) (n+gs.length) x = g.op.eval (g.inputs.map fun i => raw gs i x) := by
  change ((⟨gs++[g],0⟩:Circuit).wires (List.ofFn x)).getD (n+gs.length) false = _
  rw [wires_snoc,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp [wires_len])]
  rw [wires_len,List.length_ofFn,Nat.sub_self];rfl

def comb (conj : Bool) (u v : Bool) := if conj then u && v else u || v

lemma emit {n} (gs : List Gate) (hm : monoG gs) (a b : F n) (ha : Known gs a) (hb : Known gs b)
    (op : Bool) : ∃ ts : List Gate, monoG ts ∧ ts.length≤gs.length+1 ∧ (gs <+: ts) ∧
      (∀ g : F n,Known gs g → Known ts g) ∧ Known ts (fun x => comb op (a x) (b x)) := by
  let output := fun x => comb op (a x) (b x)
  have keep (h : Known gs output) : ∃ ts : List Gate, monoG ts ∧ ts.length≤gs.length+1 ∧ (gs <+: ts) ∧
      (∀ g : F n,Known gs g → Known ts g) ∧ Known ts output := ⟨gs,hm,by omega,List.prefix_refl _,fun _ z => z,h⟩
  have kf : Known gs (ff false : F n) := Or.inl rfl
  have kt : Known gs (ff true : F n) := Or.inr (Or.inl rfl)
  rcases ha with ea|ea|⟨i,hi,ai⟩
  · subst a;apply keep;cases op
    · simpa [output,comb,ff] using hb
    · exact kf
  · subst a;apply keep;cases op
    · exact kt
    · simpa [output,comb,ff] using hb
  have ka : Known gs a := Or.inr (Or.inr ⟨i,hi,ai⟩)
  rcases hb with eb|eb|⟨j,hj,bj⟩
  · subst b;apply keep;cases op
    · simpa [output,comb,ff] using ka
    · simp only [output,comb,ff,ite_true,Bool.and_false];exact Or.inl rfl
  · subst b;apply keep;cases op
    · simp only [output,comb,ff,Bool.false_eq_true,ite_false,Bool.or_true];exact Or.inr (Or.inl rfl)
    · simpa [output,comb,ff] using ka
  let g : Gate := ⟨if op then .and else .or,[i,j]⟩
  refine ⟨gs++[g],?_,by simp,List.prefix_append _ _,fun u hu => persists g u hu,Or.inr (Or.inr ⟨n+gs.length,by simp,?_⟩)⟩
  · intro v hv
    rcases List.mem_append.mp hv with old|last
    · exact hm _ old
    · obtain rfl := List.mem_singleton.mp last
      cases op <;> simp [g]
  · funext x
    rw [eval_new,ai,bj]
    cases op <;> simp [g,comb,GateOp.eval]

lemma vars_known {n} (f : F n) (h : f∈vars n) : Known [] f := by
  obtain ⟨i,_,rfl⟩ := List.mem_ofFn.mp h
  refine Or.inr (Or.inr ⟨i.val,by simpa using i.isLt,?_⟩)
  funext x
  change x i = (List.ofFn x).getD i.val false
  rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt];rfl


end SLP2543
namespace SLP2543
abbrev X := Fin 9 → Bool
def T (x : X) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
                    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
                    x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
namespace Certificate
theorem lower9 : ¬PEqualNP.MetaComplexity.HasCircuitSize 9 T 14 := PEqualNP.Outside.L_meta_2778.Cert.unseeded
end Certificate
end SLP2543
namespace Front2778

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k+1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

end Front2778

namespace Front2778
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}

theorem first_live {k : ℕ} {s : Finset α} (h : live ops goal (k+1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,Or.inl tail⟩
    · exact .inr step

end Front2778

namespace Front2778
abbrev W := BitVec 24
def raw : List W := [4358697,8397251,662022,304212,8980632,1068256,2199296,12709888,16646144]
def seed : W := 13339321
def inputs := raw++[seed]
def allBits : W := 16777215
def bases := 0 :: allBits :: inputs
def target : W := 3428671
def ops (a b : W) : Finset W := {a &&& b,a ||| b}

def valid (av xs : List W) : Prop := ∀ i (hi : i<xs.length),
  xs[i]∉av++xs.take i ∧ ∃ a∈av++xs.take i, ∃ b∈av++xs.take i, xs[i]=a&&&b ∨ xs[i]=a|||b

theorem unpack (av xs : List W) (h : valid (0::allBits::av) xs)
    (hit : target∈(0::allBits::av)++xs) : build ops target xs.length av.toFinset := by
  induction xs generalizing av with
  | nil =>
    simpa [target,allBits,build] using hit
  | cons v vs ih =>
    obtain ⟨fresh,a,ha,b,hb,how⟩ := h 0 (by simp)
    simp only [List.take_zero,List.append_nil,List.getElem_cons_zero] at fresh ha hb how
    have prune {w : W} (mem : w∈0::allBits::av) (h₀ : w≠0) (h₁ : w≠allBits) : w∈av := by
      simp only [List.mem_cons] at mem
      exact (mem.resolve_left h₀).resolve_left h₁
    have a₀ : a≠0 := by
      rintro rfl
      rcases how with rfl|rfl <;> simp_all [allBits]
    have a₁ : a≠allBits := by
      rintro rfl
      change v=BitVec.allOnes 24 &&& b ∨ v=BitVec.allOnes 24 ||| b at how
      rcases how with h|h
      · rw [BitVec.allOnes_and] at h
        exact fresh (h ▸ hb)
      · rw [BitVec.allOnes_or] at h
        exact fresh (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have b₀ : b≠0 := by
      rintro rfl
      rcases how with rfl|rfl <;> simp_all [allBits]
    have b₁ : b≠allBits := by
      rintro rfl
      change v=a &&& BitVec.allOnes 24 ∨ v=a ||| BitVec.allOnes 24 at how
      rcases how with h|h
      · rw [BitVec.and_allOnes] at h
        exact fresh (h ▸ ha)
      · rw [BitVec.or_allOnes] at h
        exact fresh (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have ab : a≠b := by
      rintro rfl
      rcases how with rfl|rfl <;> simp_all
    have vz : v∈ops a b := by simpa [ops] using how
    have tail : valid (0::allBits::(av++[v])) vs := by
      intro i hi
      have h' := h (i+1) (by simpa using hi)
      simpa [List.take_succ_cons,List.append_assoc] using h'
    have vt : target∈(0::allBits::(av++[v]))++vs := by simpa [List.append_assoc] using hit
    have next := ih (av++[v]) tail vt
    have form : (av++[v]).toFinset=insert v av.toFinset := by ext; simp [or_comm]
    rw [form] at next
    exact Or.inr ⟨a,List.mem_toFinset.mpr (prune ha a₀ a₁),b,List.mem_toFinset.mpr (prune hb b₀ b₁),ab,v,vz,next⟩

def separatesAt (p n : Nat) (x : W) : Prop := x.getLsbD p=true ∧ x.getLsbD n=false

theorem transfer (p n : Nat) (a b : W) (z : W) (hz : z∈ops a b) :
    separatesAt p n z → separatesAt p n a ∨ separatesAt p n b := by
  rcases (show z=a&&&b ∨ z=a|||b by simpa [ops] using hz) with rfl|rfl <;>
    simp only [separatesAt,BitVec.getLsbD_and,BitVec.getLsbD_or] <;>
    cases a.getLsbD p <;> cases a.getLsbD n <;> cases b.getLsbD p <;> cases b.getLsbD n <;> decide

instance (p n : Nat) (x : W) : Decidable (separatesAt p n x) := inferInstanceAs (Decidable (_ ∧ _))

def witnesses (i : Fin 9) := ([(0,7),(0,9),(1,6),(2,9),(3,9),(5,9),(8,6),(12,9),(18,6)] : List (Fin 24 × Fin 24)).getD i.val (0,0)
set_option maxRecDepth 8000 in
theorem check_witnesses : ∀ i : Fin 9, separatesAt (witnesses i).1 (witnesses i).2 target ∧
    ∀ j : Fin 10, separatesAt (witnesses i).1 (witnesses i).2 (inputs.getD j.val 0) → inputs.getD j.val 0=raw.getD i.val 0 := by decide +kernel

theorem uniquely_needed : ∀ w∈raw, ∃ p n : Fin 24, separatesAt p n target ∧
    ∀ u∈inputs, separatesAt p n u → u=w := by
  intro w hw
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hw
  let k : Fin 9 := ⟨i,hi⟩
  obtain ⟨sep,only⟩ := check_witnesses k
  refine ⟨_,_,sep,?_⟩
  intro u hu ds
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hu
  let t : Fin 10 := ⟨j,hj⟩
  have bj : inputs.getD t.val 0=inputs[j] := List.getD_eq_getElem _ _ hj
  have bi : raw.getD k.val 0=raw[i] := List.getD_eq_getElem _ _ hi
  exact bj.symm.trans ((only t (bj ▸ ds)).trans bi)

theorem root_cases {k : ℕ} {s : Finset W} (h : live ops target k s) (sub : s⊆inputs.toFinset) :
    s=raw.toFinset ∨ s=inputs.toFinset := by
  have must : raw.toFinset⊆s := by
    intro w hw
    obtain ⟨p,n,d,only⟩ := uniquely_needed w (List.mem_toFinset.mp hw)
    obtain ⟨x,hx,dx⟩ := live_separates (separatesAt p n) d (transfer p n) h
    rwa [←only x (List.mem_toFinset.mp (sub hx)) dx]
  by_cases marked : seed∈s
  · right
    apply Finset.Subset.antisymm sub
    intro w hw
    rcases (show w∈raw ∨ w=seed by simpa [inputs,or_comm] using hw) with hr|rfl
    · exact must (List.mem_toFinset.mpr hr)
    · exact marked
  · left
    apply Finset.Subset.antisymm _ must
    intro w hw
    have mem := sub hw
    rcases (show w∈raw ∨ w=seed by simpa [inputs,or_comm] using mem) with hr|rfl
    · exact List.mem_toFinset.mpr hr
    · exact (marked hw).elim

end Front2778
namespace Front2778
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev X := Fin 9 → Bool
def assignment (r : Fin 24) (i : Fin 9) := (raw.getD i.val 0).getLsbD r.val
def includes (x y : X) := ∀ i, x i=true → y i=true
def increasing (f : X → Bool) := ∀ x y, includes x y → f x = true → f y = true
def agrees (f : X → Bool) (w : W) := ∀ r : Fin 24, f (assignment r)=w.getLsbD r.val
instance (x y : X) : Decidable (includes x y) := inferInstanceAs (Decidable (∀ i, x i=true → y i=true))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem extremal_rows : ∀ x : X, ∃ r : Fin 24, target.getLsbD r.val=SLP2543.T x ∧
    (if SLP2543.T x then includes (assignment r) x else includes x (assignment r)) := by decide +kernel

theorem full_transfer {f : X → Bool} (inc : increasing f) (test : agrees f target) : f=SLP2543.T := by
  funext x
  obtain ⟨r,tag,order⟩ := extremal_rows x
  have hit := (test r).trans tag
  cases h : SLP2543.T x
  · rw [h] at order hit
    cases hf : f x
    · rfl
    · exact False.elim (Bool.noConfusion (hit.symm.trans (inc x (assignment r) order hf)))
  · rw [h] at order hit
    exact inc (assignment r) x order hit

def carries (gs : List Gate) (w : W) := ∃ f : X→Bool, SLP2543.Known gs f ∧ increasing f ∧ agrees f w

theorem raw_carried (w : W) (hw : w ∈ raw.toFinset) : carries [] w := by
  have form : List.ofFn (fun i : Fin 9 => raw.getD i.val 0)=raw := rfl
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp (form ▸ List.mem_toFinset.mp hw)
  subst w
  exact ⟨fun x => x i,SLP2543.vars_known _ (List.mem_ofFn.mpr ⟨i,rfl⟩),fun _ _ h => h i,fun _ => rfl⟩

theorem comb_inc (op : Bool) {f g : X→Bool} (hf : increasing f) (hg : increasing g) :
    increasing (fun x => SLP2543.comb op (f x) (g x)) := by
  intro x y h pos
  cases op
  · change f y || g y = true
    exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp pos).imp (hf x y h) (hg x y h))
  · change (f y && g y) = true
    exact Bool.and_eq_true_iff.mpr ⟨hf x y h (Bool.and_eq_true_iff.mp pos).1,hg x y h (Bool.and_eq_true_iff.mp pos).2⟩

theorem comb_agrees (op : Bool) {f g : X→Bool} {a b : W} (fa : agrees f a) (gb : agrees g b) :
    agrees (fun x => SLP2543.comb op (f x) (g x)) (if op then a&&&b else a|||b) := by
  intro r
  cases op <;> simp only [SLP2543.comb,fa r,gb r,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or]

theorem compile_build {k : ℕ} {s : Finset W} (prog : build ops target k s)
    (gs : List Gate) (mg : SLP2543.monoG gs) (pool : ∀ w∈s, carries gs w) :
    ∃ ts : List Gate, SLP2543.monoG ts ∧ gs <+: ts ∧ ts.length ≤ gs.length+k ∧ SLP2543.Known ts SLP2543.T := by
  induction k generalizing gs s with
  | zero =>
    obtain ⟨f,known,inc,rows⟩ := pool target prog
    exact ⟨gs,mg,List.prefix_refl _,by simp,full_transfer inc rows ▸ known⟩
  | succ k ih =>
    rcases prog with skipped|⟨a,ha,b,hb,_,z,hz,tail⟩
    · obtain ⟨ts,mt,pre,sz,known⟩ := ih skipped gs mg pool
      exact ⟨ts,mt,pre,by omega,known⟩
    obtain ⟨f,kf,inf,fa⟩ := pool a ha
    obtain ⟨g,kg,ing,gb⟩ := pool b hb
    obtain ⟨op,eq⟩ : ∃ op : Bool,z=(if op then a&&&b else a|||b) := by
      rcases (show z=a&&&b ∨ z=a|||b by simpa [ops] using hz) with h|h
      · exact ⟨true,h⟩
      · exact ⟨false,h⟩
    obtain ⟨ts,mt,bound,pre,inherit,out⟩ := SLP2543.emit gs mg f g kf kg op
    have extend : ∀ w∈insert z s,carries ts w := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|old
      · exact ⟨_,out,comb_inc op inf ing,eq ▸ comb_agrees op fa gb⟩
      · obtain ⟨t,kt,inc,agreement⟩ := pool w old
        exact ⟨t,inherit _ kt,inc,agreement⟩
    obtain ⟨last,ml,prel,cap,known⟩ := ih tail ts mt extend
    exact ⟨last,ml,pre.trans prel,by omega,known⟩

theorem build_subset {k : ℕ} {s t : Finset W} (run : build ops target k s) (sub : s ⊆ t) :
    build ops target k t := by
  induction k generalizing s t with
  | zero => exact sub run
  | succ k ih =>
    rcases run with skip|⟨a,ha,b,hb,ab,z,hz,tail⟩
    · exact Or.inl (ih skip sub)
    · exact Or.inr ⟨a,sub ha,b,sub hb,ab,z,hz,ih tail (Finset.insert_subset_insert _ sub)⟩

theorem live_build {k : ℕ} {s : Finset W} (run : live ops target k s) : build ops target k s := by
  induction k generalizing s with
  | zero => change s={target} at run; change target∈s; simp [run]
  | succ k ih =>
    rcases run with skip|⟨a,ha,b,hb,ab,z,hz,_,rest,eq,tail⟩
    · exact Or.inl (ih skip)
    · apply Or.inr
      refine ⟨a,ha,b,hb,ab,z,hz,build_subset (ih tail) ?_⟩
      apply Finset.insert_subset_insert
      rw [eq];exact Finset.Subset.trans (Finset.subset_insert _ _) (Finset.subset_insert _ _)

end Front2778
namespace Front2778
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem actual {gs : List Gate} (hm : SLP2543.monoG gs) (known : SLP2543.Known gs SLP2543.T) :
    ∃ C : Circuit, C.gates=gs ∧ Monotone2 C ∧ ∀ x : X,C.eval (List.ofFn x)=SLP2543.T x := by
  rcases known with h|h|⟨i,_,eq⟩
  · exact False.elim ((show SLP2543.T ≠ SLP2543.ff false by decide +kernel) h)
  · exact False.elim ((show SLP2543.T ≠ SLP2543.ff true by decide +kernel) h)
  exact ⟨⟨gs,i⟩,rfl,fun g hg => ⟨(hm g hg).1,(hm g hg).2⟩,fun x => congrFun eq.symm x⟩

theorem raw_excluded_with (ordinary : ¬HasCircuitSize 9 SLP2543.T 14)
    {k} (small : k≤14) : ¬ live ops target k raw.toFinset := by
  intro run
  obtain ⟨ts,hm,_,len,known⟩ := compile_build (live_build run) [] (by simp [SLP2543.monoG]) raw_carried
  obtain ⟨C,eq,mono,test⟩ := actual hm known
  apply ordinary
  exact ⟨C,fun g hg => ⟨(mono g hg).1.elim Or.inl (fun v => Or.inr (Or.inl v)),(mono g hg).2⟩,
    by change C.gates.length≤14;rw [eq];simp only [List.length_nil,Nat.zero_add] at len;omega,test⟩
theorem raw_excluded {k} (small : k≤14) : ¬ live ops target k raw.toFinset :=
  raw_excluded_with SLP2543.Certificate.lower9 small

theorem entire_root {k s} (fit : k≤14) (sub : s⊆inputs.toFinset) (run : live ops target k s) :
    s=inputs.toFinset := by
  rcases root_cases run sub with eq|eq
  · exact False.elim (raw_excluded fit (eq ▸ run))
  · exact eq

theorem mandatory {xs : List W} (fit : xs.length ≤ 14) (ok : valid bases xs) (hit : target ∈ bases++xs) :
    live ops target xs.length inputs.toFinset := by
  obtain ⟨s,sub,run⟩ := compress (unpack inputs xs ok hit)
  rwa [entire_root fit sub run] at run

def prepaid : Gate := ⟨.or,[0,4]⟩
theorem paid_mono : SLP2543.monoG [prepaid] := by
  intro g hg
  obtain rfl := List.mem_singleton.mp hg
  exact ⟨Or.inr rfl,by decide⟩

theorem seed_known : SLP2543.Known [prepaid] (fun x : X => x 0 || x 4) := by
  refine Or.inr (Or.inr ⟨9,by decide,?_⟩)
  decide +kernel

theorem paid_carried (w : W) (hw : w∈inputs.toFinset) : carries [prepaid] w := by
  rcases (show w=seed ∨ w∈raw by simpa [inputs] using hw) with rfl|hr
  · refine ⟨fun x : X => x 0 || x 4,seed_known,?_,?_⟩
    · intro x y h hit
      exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp hit).imp (h 0) (h 4))
    · unfold agrees
      decide +kernel
  · obtain ⟨f,known,inc,agree⟩ := raw_carried w (List.mem_toFinset.mpr hr)
    exact ⟨f,SLP2543.persists prepaid f known,inc,agree⟩

theorem paid_minimum {k} (run : live ops target k inputs.toFinset) : 14≤k := by
  obtain ⟨gs,hm,_,len,known⟩ := compile_build (live_build run) [prepaid] paid_mono paid_carried
  obtain ⟨C,eq,mono,test⟩ := actual hm known
  by_contra! small
  apply SLP2543.Certificate.lower9
  exact ⟨C,fun g hg => ⟨(mono g hg).1.elim Or.inl (fun v => Or.inr (Or.inl v)),(mono g hg).2⟩,
    by change C.gates.length≤14;rw [eq];simp only [List.length_singleton] at len;omega,test⟩

end Front2778
namespace Front2778

inductive accounted : ℕ → ℕ → Finset W → Prop where
  | done : accounted 0 0 {target}
  | gate {g e : ℕ} {a b z : W} {r : Finset W} (distinct : a≠b)
      (operation : z∈ops a b) (fresh : z∉insert a (insert b r))
      (next : accounted g e (insert z r)) :
      accounted (g+1) (e + (if a∈r then 1 else 0) + (if b∈r then 1 else 0)) (insert a (insert b r))

theorem accounted_live {g e s} (h : accounted g e s) : live ops target g s := by
  induction h with
  | done => rfl
  | gate ab hz fresh next ih =>
    exact Or.inr ⟨_,by simp,_,by simp,ab,_,hz,fresh,_,rfl,ih⟩

theorem live_accounted {k s} (h : live ops target k s) : ∃ g≤k,∃ e,accounted g e s := by
  induction k generalizing s with
  | zero => change s={target} at h;exact ⟨0,by omega,0,h ▸ accounted.done⟩
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,ab,z,hz,fresh,r,rfl,tail⟩
    · obtain ⟨g,le,e,proof⟩ := ih skip
      exact ⟨g,by omega,e,proof⟩
    · obtain ⟨g,le,e,proof⟩ := ih tail
      exact ⟨g+1,by omega,_,.gate ab hz fresh proof⟩

theorem exact_charges {g e s} (h : accounted g e s) : s.card+e=g+1 := by
  induction h with
  | done => simp
  | @gate g e a b z r ab hz fresh next ih =>
    have zr : z∉r := fun mem => fresh (by simp [mem])
    rw [Finset.card_insert_of_notMem zr] at ih
    rw [Finset.card_insert_eq_ite, Finset.card_insert_eq_ite]
    by_cases ha : a∈r <;> by_cases hb : b∈r <;> simp [ab,ha,hb] <;> omega

theorem exact_candidate {xs : List W} (fit : xs.length ≤ 14) (ok : valid bases xs)
    (hit : target ∈ bases++xs) : xs.length=14 ∧ accounted 14 5 inputs.toFinset := by
  obtain ⟨g,hg,e,trace⟩ := live_accounted (mandatory fit ok hit)
  have low := paid_minimum (accounted_live trace)
  have balance := exact_charges trace
  have size : inputs.toFinset.card=10 := by decide +kernel
  rw [size] at balance
  have gates : g=14 := by omega
  have charge : e=5 := by omega
  exact ⟨by omega,gates ▸ charge ▸ trace⟩

end Front2778
namespace Front2778

def better (u v : W) : Prop := ∀ r : Fin 24, if target.getLsbD r.val then
    v.getLsbD r.val=true → u.getLsbD r.val=true else u.getLsbD r.val=true → v.getLsbD r.val=true

theorem better_refl (a : W) : better a a := fun r => by split <;> exact id

theorem better_goal {a : W} (h : better a target) : a=target := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have good := h ⟨i,hi⟩
  change a.getLsbD i = target.getLsbD i
  cases ht : target.getLsbD i <;> cases ha : a.getLsbD i <;> simp_all

theorem better_op (op : Bool) {a b x y : W} (hx : better x a) (hy : better y b) :
    better (if op then x&&&y else x|||y) (if op then a&&&b else a|||b) := by
  intro r
  have u := hx r
  have v := hy r
  cases op <;> cases ht : target.getLsbD r.val <;>
    cases ha : a.getLsbD r.val <;> cases hb : b.getLsbD r.val <;>
    cases h₁ : x.getLsbD r.val <;> cases h₂ : y.getLsbD r.val <;>
    simp_all

def improvement (t s : Finset W) := ∀ a∈s,∃ x∈t,better x a

theorem improve_build {k : ℕ} {s t : Finset W} (run : build ops target k s) (sim : improvement t s) :
    build ops target k t := by
  induction k generalizing s t with
  | zero =>
    obtain ⟨x,mem,good⟩ := sim target run
    exact better_goal good ▸ mem
  | succ k ih =>
    rcases run with skip|⟨a,ha,b,hb,ab,z,hz,tail⟩
    · exact Or.inl (ih skip sim)
    obtain ⟨x,hx,goodx⟩ := sim a ha
    obtain ⟨y,hy,goody⟩ := sim b hb
    obtain ⟨op,rfl⟩ : ∃ op : Bool,z=(if op then a&&&b else a|||b) := by
      rcases (show z=a&&&b ∨ z=a|||b by simpa [ops] using hz) with h|h
      · exact ⟨true,h⟩
      · exact ⟨false,h⟩
    let v := if op then x&&&y else x|||y
    have more : improvement (insert v t) (insert (if op then a&&&b else a|||b) s) := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|mem
      · exact ⟨v,Finset.mem_insert_self ..,better_op op goodx goody⟩
      obtain ⟨u,hu,good⟩ := sim w mem
      exact ⟨u,Finset.mem_insert_of_mem hu,good⟩
    have suffix := ih tail more
    by_cases eq : x=y
    · subst y
      have vv : v=x := by cases op <;> simp [v]
      rw [vv,Finset.insert_eq_of_mem hx] at suffix
      exact Or.inl suffix
    · exact Or.inr ⟨x,hx,y,hy,eq,v,by cases op <;> simp [v,ops],suffix⟩

theorem dominated_skip {s : Finset W} {z u : W} {k : ℕ} (hu : u∈s) (dom : better u z)
    (continuation : build ops target k (insert z s)) : build ops target k s := by
  apply improve_build continuation
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl|mem
  · exact ⟨u,hu,dom⟩
  · exact ⟨w,mem,better_refl w⟩

end Front2778
namespace Front2778

theorem better_bits {a b : W} : better a b ↔ ((a^^^target)&&&(b^^^target))=(a^^^target) := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have atRow := h ⟨j,hj⟩
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_xor]
    cases ht : target.getLsbD j <;> cases ha : a.getLsbD j <;> cases hb : b.getLsbD j <;> simp_all
  · intro bits r
    have h := congrArg (fun w : W => w.getLsbD r.val) bits
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_xor] at h
    cases ht : target.getLsbD r.val <;> cases ha : a.getLsbD r.val <;> cases hb : b.getLsbD r.val <;> simp_all

def State := Nat × Nat × Finset W

def cutStep (p q : State) : Prop := ∃ a b z : W, ∃ r : Finset W,
    a≠b ∧ z∈ops a b ∧ p.2.2=insert a (insert b r) ∧ q.2.2=insert z r ∧
    p.1=q.1+1 ∧ p.2.1=q.2.1+(if a∈r then 1 else 0)+(if b∈r then 1 else 0) ∧
    ∀ w∈p.2.2, ((w^^^target)&&&(z^^^target))≠w^^^target

def optimal (g : Nat) (s : Finset W) := ∀ k<g,¬build ops target k s

theorem clean_trace {g e s} (trace : accounted g e s) (lowest : optimal g s) :
    Relation.ReflTransGen cutStep (g,e,s) (0,0,{target}) := by
  induction trace with
  | done => exact .refl
  | @gate g e a b z r distinct operation fresh next ih =>
    let start := insert a (insert b r)
    have sub : r⊆start := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have nextOptimal : optimal g (insert z r) := by
      intro k hk shorter
      apply lowest (k+1) (by omega)
      exact Or.inr ⟨a,by simp,b,by simp,distinct,z,operation,
        build_subset shorter (Finset.insert_subset_insert z sub)⟩
    have clean (w : W) (hw : w∈start) : ((w^^^target)&&&(z^^^target))≠w^^^target := by
      intro dom
      have rest := build_subset (live_build (accounted_live next)) (Finset.insert_subset_insert z sub)
      exact lowest g (by omega) (dominated_skip hw (better_bits.mpr dom) rest)
    exact Relation.ReflTransGen.head ⟨a,b,z,r,distinct,operation,rfl,rfl,rfl,rfl,clean⟩ (ih nextOptimal)

theorem root_optimal : optimal 14 inputs.toFinset := by
  intro k hk prog
  obtain ⟨s,sub,run⟩ := compress prog
  have eq := entire_root (by omega) sub run
  exact (Nat.not_le_of_lt hk) (paid_minimum (eq ▸ run))

theorem candidate_trace {xs : List W} (bound : xs.length≤14) (legal : valid bases xs)
    (hit : target∈bases++xs) :
    Relation.ReflTransGen cutStep (14,5,inputs.toFinset) (0,0,{target}) :=
  clean_trace (exact_candidate bound legal hit).2 root_optimal

end Front2778
namespace Front2778
namespace Re
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
abbrev certInputs := PEqualNP.Outside.L_meta_2778.Cert.inputs

def functionOn (f : X→Bool) := fun r : Row => f (sample r)
def carriesF (bank : List (Wire Row)) (w : W) :=
    ∃ f : X→Bool,Available bank (functionOn f) ∧ increasing f ∧ agrees f w

theorem runFull {k s} (prog : build ops target k s) {roots : List (Wire Row)} {p bank}
    (pr : Reach roots p bank) (supply : ∀ w∈s,carriesF bank w) :
    ∃ n≤p+k,∃ last,Reach roots n last ∧ Available last (observe graph) := by
  induction k generalizing s p bank with
  | zero =>
    obtain ⟨f,known,inc,test⟩ := supply target prog
    have fn := full_transfer inc test
    have eq : functionOn f=observe graph := by
      funext r
      exact (congrFun fn (sample r)).trans (edge_table r).symm
    exact ⟨p,by omega,bank,pr,eq ▸ known⟩
  | succ k ih =>
    rcases prog with skip | ⟨a,ha,b,hb,_,z,hz,tail⟩
    · obtain ⟨n,hn,ws,run,out⟩ := ih skip pr supply
      exact ⟨n,by omega,ws,run,out⟩
    obtain ⟨f,hf,fi,fa⟩ := supply a ha
    obtain ⟨g,hg,gi,gb⟩ := supply b hb
    obtain ⟨op,eq⟩ : ∃ op : Bool,z=(if op then a&&&b else a|||b) := by
      rcases (show z=a&&&b ∨ z=a|||b by simpa [ops] using hz) with h|h
      · exact ⟨true,h⟩
      · exact ⟨false,h⟩
    let v := combine (!op) (functionOn f) (functionOn g)
    have head : functionOn (fun x => SLP2543.comb op (f x) (g x)) = v := by cases op <;> rfl
    have supply' : ∀ w∈insert z s,carriesF (v::bank) w := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|h
      · exact ⟨_,head ▸ Or.inl (List.mem_cons_self ..),comb_inc op fi gi,eq ▸ comb_agrees op fa gb⟩
      obtain ⟨t,ht,ti,ta⟩ := supply w h
      exact ⟨t,available_cons _ ht,ti,ta⟩
    obtain ⟨n,hn,ws,run,out⟩ := ih tail (Reach.two (!op) pr hf hg) supply'
    exact ⟨n,by omega,ws,run,out⟩

def indicator (i : Fin 12) : W := raw.getD (pairAt i).1 0 &&& raw.getD (pairAt i).2 0
def coord (j : Fin 9) : X→Bool := fun x => x j

theorem roots_know (i : Fin 12) (j : Fin 9) : Available ((sourceOf i).map observe) (functionOn (coord j)) := by
  apply Or.inl
  apply List.mem_map.mpr
  refine ⟨certInputs.getD j.val zero,List.mem_append_left _ ?_,rfl⟩
  rw [← input_list,List.mem_ofFn]
  exact ⟨j,rfl⟩

def lhs (i : Fin 12) : Fin 9 := Fin.ofNat 9 (pairAt i).1
def rhs (i : Fin 12) : Fin 9 := Fin.ofNat 9 (pairAt i).2
def andFn (i : Fin 12) : X→Bool := fun x => x (lhs i) && x (rhs i)
theorem pair_in (i : Fin 12) : functionOn (andFn i) = observe (edgeWord i) := by
  funext r
  change (_ && _) = (vertexPair _ _).getLsbD r.val
  simp only [vertexPair,BitVec.getLsbD_and]
  have yes : ∀ i : Fin 12, (lhs i).val=(pairAt i).1 ∧ (rhs i).val=(pairAt i).2 := by decide +kernel
  simp only [sample,bit,(yes i).1,(yes i).2,certInputs]

def seedFn : X→Bool := fun x => x 0 || x 4

theorem edge_augmented (i : Fin 12) {k : ℕ} (run : build ops target k (insert (indicator i) inputs.toFinset)) : 14≤k := by
  let start := (sourceOf i).map observe
  let bank := functionOn seedFn :: start
  have beginAt : Reach start 1 bank := Reach.two true .start (roots_know i 0) (roots_know i 4)
  have supply (w : W) (mem : w∈insert (indicator i) inputs.toFinset) : carriesF bank w := by
    rcases Finset.mem_insert.mp mem with rfl|mem
    · refine ⟨andFn i,available_cons _ ?_,?_,?_⟩
      · rw [pair_in]
        apply Or.inl
        exact List.mem_map.mpr ⟨edgeWord i,by simp [sourceOf],rfl⟩
      · intro x y inc h
        exact Bool.and_eq_true_iff.mpr ⟨inc _ (Bool.and_eq_true_iff.mp h).1,inc _ (Bool.and_eq_true_iff.mp h).2⟩
      · exact (show ∀ j : Fin 12, agrees (andFn j) (indicator j) by unfold agrees; decide +kernel) i
    rcases (show w=seed ∨ w∈raw by simpa [inputs] using mem) with rfl|v
    · refine ⟨seedFn,Or.inl (List.mem_cons_self ..),?_,?_⟩
      · intro x y inc h
        exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp h).imp (inc 0) (inc 4))
      · unfold agrees
        decide +kernel
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem v
    let t : Fin 9 := ⟨j,hj⟩
    refine ⟨coord t,available_cons _ (roots_know i t),fun _ _ inc => inc t,?_⟩
    intro r
    change (raw.getD j 0).getLsbD r.val=(raw[j]).getLsbD r.val
    rw [List.getD_eq_getElem _ _ hj]
  obtain ⟨n,hn,ws,trace,out⟩ := runFull run beginAt supply
  have min := each_edge i n ws trace out
  omega

end Re
end Front2778
namespace Front2778

def positive (w : W) : Finset (Fin 24) := Finset.univ.filter (fun r : Fin 24 => (w&&&target).getLsbD r.val)

theorem indicators_sound : ∀ (i : Fin 12) (r : Fin 24),
    (Re.indicator i).getLsbD r.val=true → target.getLsbD r.val=true := by decide +kernel

theorem indicators_cover : ∀ r : Fin 24, target.getLsbD r.val=true →
    ∃ i : Fin 12,(Re.indicator i).getLsbD r.val=true := by decide +kernel

theorem two_positive (w : W) (all : ∀ i,¬better (Re.indicator i) w) : 2≤(positive w).card := by
  have miss (i : Fin 12) : ∃ r : Fin 24,r∈positive w ∧ (Re.indicator i).getLsbD r.val=false := by
    by_contra! bad
    apply all i
    intro r
    cases h : target.getLsbD r.val
    · exact fun hit => False.elim (Bool.noConfusion (h.symm.trans (indicators_sound i r hit)))
    · intro hr
      have mem : r∈positive w := by simp [positive,BitVec.getLsbD_and,h,hr]
      exact Bool.eq_true_of_not_eq_false (bad r mem)
  obtain ⟨r,hr,_⟩ := miss 0
  have both : w.getLsbD r.val=true ∧ target.getLsbD r.val=true := by simpa [positive,BitVec.getLsbD_and] using hr
  have tr := both.2
  obtain ⟨i,hi⟩ := indicators_cover r tr
  obtain ⟨s,hs,off⟩ := miss i
  apply Finset.one_lt_card.mpr
  exact ⟨r,hr,s,hs,fun eq => Bool.noConfusion (hi.symm.trans (eq ▸ off))⟩

def strongStep (p q : State) : Prop := ∃ a b z : W, ∃ r : Finset W,
    a≠b ∧ z∈ops a b ∧ p.2.2=insert a (insert b r) ∧ q.2.2=insert z r ∧
    p.1=q.1+1 ∧ p.2.1=q.2.1+(if a∈r then 1 else 0)+(if b∈r then 1 else 0) ∧
    (∀ w∈p.2.2, ((w^^^target)&&&(z^^^target))≠w^^^target) ∧ 2≤(positive z).card

theorem clean_count {g e s} (trace : accounted g e s) (lowest : optimal g s)
    (other : ∀ i,optimal g (insert (Re.indicator i) s)) :
    Relation.ReflTransGen strongStep (g,e,s) (0,0,{target}) := by
  induction trace with
  | done => exact .refl
  | @gate g e a b z r distinct operation fresh next ih =>
    let start := insert a (insert b r)
    have sub : r⊆start := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have transfer {u v : Finset W} (ha : a∈u) (hb : b∈u) (incl : v⊆u) (before : optimal (g+1) u) :
        optimal g (insert z v) := by
      intro k hk short
      apply before (k+1) (by omega)
      exact Or.inr ⟨a,ha,b,hb,distinct,z,operation,build_subset short (Finset.insert_subset_insert z incl)⟩
    have best : optimal g (insert z r) := transfer (by simp [start]) (by simp [start]) sub lowest
    have bestEdge (i) : optimal g (insert (Re.indicator i) (insert z r)) := by
      rw [Finset.insert_comm]
      exact transfer (by simp [start]) (by simp [start]) (Finset.insert_subset_insert _ sub) (other i)
    have rest := build_subset (live_build (accounted_live next)) (Finset.insert_subset_insert z sub)
    have clean (w : W) (hw : w∈start) : ((w^^^target)&&&(z^^^target))≠w^^^target :=
      fun dom => lowest g (by omega) (dominated_skip hw (better_bits.mpr dom) rest)
    have unique (i) : ¬ better (Re.indicator i) z := by
      intro dom
      have withSeed := build_subset rest (Finset.insert_subset_insert z (Finset.subset_insert (Re.indicator i) start))
      exact other i g (by omega) (dominated_skip (Finset.mem_insert_self ..) dom withSeed)
    exact Relation.ReflTransGen.head
      ⟨a,b,z,r,distinct,operation,rfl,rfl,rfl,rfl,clean,two_positive z unique⟩
      (ih best bestEdge)

theorem counted_candidate {xs : List W} (bound : xs.length≤14) (legal : valid bases xs)
    (hit : target∈bases++xs) :
    Relation.ReflTransGen strongStep (14,5,inputs.toFinset) (0,0,{target}) :=
  clean_count (exact_candidate bound legal hit).2 root_optimal (fun i k hk h => Nat.not_le_of_lt hk (Re.edge_augmented i h))

end Front2778

end PEqualNP.Outside.L_meta_2778

namespace PEqualNP.Outside.L_meta_2778

namespace Front2778
namespace Full
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed

def rowFrom (x : X) : Row := Fin.ofNat 512 ((List.ofFn (fun i : Fin 9 => if x i then 2^i.val else 0)).sum)
set_option maxRecDepth 12000 in
theorem sample_from : ∀ x : X, sample (rowFrom x)=x := by decide +kernel
set_option maxRecDepth 12000 in
theorem from_sample : ∀ r : Row,rowFrom (sample r)=r := by decide +kernel
def monotone (a : Sig) := increasing fun x => bit (rowFrom x) a
def project (a : Sig) : W := BitVec.ofBoolListLE (List.ofFn (fun r : Fin 24 => bit (rowFrom (assignment r)) a)) |>.cast (List.length_ofFn)
set_option maxRecDepth 12000 in
theorem project_bit (a : Sig) (r : Fin 24) : (project a).getLsbD r.val=bit (rowFrom (assignment r)) a := by
  simp only [project,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
set_option maxRecDepth 12000 in
theorem project_and (a b : Sig) : project (a&&&b)=project a &&& project b := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [BitVec.getLsbD_and,project_bit _ ⟨r,hr⟩,project_bit a ⟨r,hr⟩,project_bit b ⟨r,hr⟩]
  exact BitVec.getLsbD_and
set_option maxRecDepth 12000 in
theorem project_or (a b : Sig) : project (a|||b)=project a ||| project b := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  rw [BitVec.getLsbD_or,project_bit _ ⟨r,hr⟩,project_bit a ⟨r,hr⟩,project_bit b ⟨r,hr⟩]
  exact BitVec.getLsbD_or
set_option maxRecDepth 12000 in
theorem monotone_op (op : Bool) {a b : Sig} (ha : monotone a) (hb : monotone b) :
    monotone (if op then a&&&b else a|||b) := by
  intro x y le good
  have h := comb_inc op ha hb x y le
  cases op <;> simp only [SLP2543.comb,bit,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] at * <;> exact h good

set_option maxRecDepth 12000 in
theorem unique_target {w : Sig} (mono : monotone w) (eq : project w=target) : w=graph := by
  have agreesW : agrees (fun x => bit (rowFrom x) w) target :=
    fun r => (project_bit w r).symm.trans (congrArg (fun x : W => x.getLsbD r.val) eq)
  have full := full_transfer mono agreesW
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let r : Row := ⟨j,hj⟩
  have ev := congrFun full (sample r)
  rw [from_sample] at ev
  exact ev.trans (edge_table r).symm

def SOp (a b : Sig) : Finset Sig := {a&&&b,a|||b}

inductive Path : ℕ → Finset Sig → Prop where
  | endAt : Path 0 {graph}
  | step {k : ℕ} {a b z : Sig} {remainder : Finset Sig} (ab : a≠b)
      (hop : z∈SOp a b) (new : z∉insert a (insert b remainder))
      (clean : ∀ w∈insert a (insert b remainder),¬better (project w) (project z))
      (wide : 2≤(positive (project z)).card)
      (later : Path k (insert z remainder)) : Path (k+1) (insert a (insert b remainder))

set_option maxRecDepth 12000 in
theorem Path.live {k s} (p : Path k s) : Front2778.live SOp graph k s := by
  induction p with
  | endAt => rfl
  | step ab hop new clean wide later ih => exact Or.inr ⟨_,by simp,_,by simp,ab,_,hop,new,_,rfl,ih⟩

set_option maxRecDepth 12000 in
theorem lift_path {p : State} (h : Relation.ReflTransGen strongStep p (0,0,{target})) (s : Finset Sig)
    (matchSet : s.image project=p.2.2) (inject : Set.InjOn project s) (mono : ∀ w∈s,monotone w) : Path p.1 s := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing s with
  | refl =>
    have all {w} (hw : w∈s) : w=graph := by
      apply unique_target (mono _ hw)
      have mem := Finset.mem_image_of_mem project hw
      rw [matchSet] at mem
      exact Finset.mem_singleton.mp mem
    have targetMem : target∈s.image project := matchSet ▸ Finset.mem_singleton_self _
    obtain ⟨w,hw,_⟩ := Finset.mem_image.mp targetMem
    have key : s={graph} := Finset.Subset.antisymm (fun _ hm => Finset.mem_singleton.mpr (all hm))
      (Finset.singleton_subset_iff.mpr (all hw ▸ hw))
    exact key ▸ Path.endAt
  | @head p q step tail ih =>
    rcases step with ⟨a,b,z,r,ab,op,start,finish,time,_,clean,wide⟩
    have old : s.image project=insert a (insert b r) := matchSet.trans start
    obtain ⟨x,hx,px⟩ := Finset.mem_image.mp (show a∈s.image project by rw [old];simp)
    obtain ⟨y,hy,py⟩ := Finset.mem_image.mp (show b∈s.image project by rw [old];simp)
    have distinct : x≠y := fun eq => ab (px.symm.trans ((congrArg project eq).trans py))
    obtain ⟨which,eq⟩ : ∃ t : Bool,z=(if t then a&&&b else a|||b) := by
      rcases (show z=a&&&b ∨ z=a|||b by simpa [ops] using op) with hh|hh
      · exact ⟨true,hh⟩
      · exact ⟨false,hh⟩
    let v := if which then x&&&y else x|||y
    have pv : project v=z := by cases which <;> simp_all [v,project_and,project_or]
    let rest := s.filter fun w => project w∈r
    have incl : rest⊆s := Finset.filter_subset _ _
    have restImg : rest.image project=r := by
      ext w
      constructor
      · rintro hw
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hc).2
      · intro mem
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp (show w∈s.image project by rw [old];simp [mem])
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hc,mem⟩)
    have shape : s=insert x (insert y rest) := by
      apply Finset.Subset.antisymm _ (Finset.insert_subset hx (Finset.insert_subset hy incl))
      intro w hw
      have mem := Finset.mem_image_of_mem project hw
      rw [old] at mem
      rcases Finset.mem_insert.mp mem with ww|ww
      · exact Finset.mem_insert.mpr (Or.inl (inject hw hx (ww.trans px.symm)))
      rcases Finset.mem_insert.mp ww with ww|ww
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (inject hw hy (ww.trans py.symm)))))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hw,ww⟩))
    have newProj : z∉p.2.2 := fun mem => clean z mem BitVec.and_self
    have new : v∉s := fun mem => newProj (matchSet ▸ pv ▸ Finset.mem_image_of_mem project mem)
    have attach : (insert v rest).image project=q.2.2 := by rw [Finset.image_insert,pv,restImg,finish]
    have inject' : Set.InjOn project (insert v rest : Finset Sig) := by
      intro u hu w hw eq
      rcases Finset.mem_insert.mp hu with rfl|hu <;> rcases Finset.mem_insert.mp hw with rfl|hw
      · rfl
      · exact False.elim (newProj (matchSet ▸ pv ▸ eq.symm ▸ Finset.mem_image_of_mem project (incl hw)))
      · exact False.elim (newProj (matchSet ▸ pv ▸ eq ▸ Finset.mem_image_of_mem project (incl hu)))
      · exact inject (incl hu) (incl hw) eq
    have mono' : ∀ w∈insert v rest,monotone w := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|mem
      · exact monotone_op which (mono _ hx) (mono _ hy)
      · exact mono _ (incl mem)
    have tail' := ih _ attach inject' mono'
    rw [time,shape]
    refine Path.step distinct (by cases which <;> simp [v,SOp]) (shape ▸ new) ?_ (pv ▸ wide) tail'
    intro w hw
    exact (better_bits.not.mpr (clean _ (matchSet ▸ Finset.mem_image_of_mem _ (shape ▸ hw)))) ∘ (pv ▸ id)

end Full
end Front2778
namespace Front2778.Full
open PEqualNP.Outside.L_meta_2778.Cert hiding seed inputs
abbrev raws := PEqualNP.Outside.L_meta_2778.Cert.inputs
def paidWord := raws.getD 0 zero ||| raws.getD 4 zero
def starting := raws++[paidWord]

theorem raw_monotone (i : Fin 9) : monotone (raws.getD i.val zero) := by
  intro x y inc
  have px := congrFun (sample_from x) i
  have py := congrFun (sample_from y) i
  change sample (rowFrom x) i=true → sample (rowFrom y) i=true
  simpa only [px,py] using inc i

theorem start_mono : ∀ w∈starting.toFinset,monotone w := by
  intro w h
  rcases (show w∈raws ∨ w=paidWord by simpa [starting,or_comm] using h) with old|rfl
  · change w ∈ PEqualNP.Outside.L_meta_2778.Cert.inputs at old
    rw [←input_list] at old
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp old
    exact raw_monotone i
  · exact monotone_op false (raw_monotone 0) (raw_monotone 4)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem start_map : starting.map project=inputs := by decide +kernel

theorem start_img : starting.toFinset.image project=inputs.toFinset := by
  ext w
  simp only [Finset.mem_image,List.mem_toFinset]
  rw [←start_map,List.mem_map]

theorem start_inj : Set.InjOn project starting.toFinset := by
  have nd : (starting.map project).Nodup := start_map ▸ (show inputs.Nodup by decide +kernel)
  intro a ha b hb
  have inject := (List.nodup_map_iff_inj_on (l:=starting) (f:=project) (by decide +kernel)).mp nd
  exact inject _ (List.mem_toFinset.mp ha) _ (List.mem_toFinset.mp hb)

theorem beginning {xs : List W} (bound : xs.length≤14) (legal : valid bases xs) (hit : target∈bases++xs) :
    Path 14 starting.toFinset := lift_path (counted_candidate bound legal hit) starting.toFinset start_img start_inj start_mono
end Front2778.Full


namespace Front2778
namespace Price
open PEqualNP.Outside.L_meta_2778.Cert
variable {A R : Type} [DecidableEq A]

structure Model (A R : Type) where
  good : A → Wire R → Prop
  op : Bool → A → A → A
  combine_ok : ∀ b {x y f g},good x f → good y g → good (op b x y) (combine b f g)

def choices (M : Model A R) (a b : A) : Finset A := {M.op false a b,M.op true a b}

private theorem cost_ins (a : A) (s : Finset A) (v : A→Wire R) :
    ∑ w∈insert a s,cost (v w) ≤ cost (v a)+∑ w∈s,cost (v w) := by
  by_cases h : a∈s
  · simp [Finset.insert_eq_of_mem h]
  · simp [Finset.sum_insert h]

theorem finish (M : Model A R) (t : A) (T : Wire R) (terminal : ∀ f,M.good t f → f=T)
    (nc : ¬Constant T) {k s} (program : live (choices M) t k s)
    {roots : List (Wire R)} {p : ℕ} {bank : List (Wire R)} (history : Reach roots p bank)
    (v : A → Wire R) (hg : ∀ w∈s,M.good w (v w)) (ha : ∀ w∈s,Available bank (v w)) :
    ∃ q last,Reach roots q last ∧ Available last T ∧ q+(∑ w∈s,cost (v w))≤p+k := by
  classical
  induction k generalizing s p bank v with
  | zero =>
    change s={t} at program
    subst s
    have same := terminal _ (hg t (by simp))
    exact ⟨p,bank,history,same ▸ ha t (by simp),by simp [same,cost,nc]⟩
  | succ k ih =>
    rcases program with skip | ⟨a,am,b,bm,ab,z,how,fresh,r,rfl,tail⟩
    · obtain ⟨q,last,built,hit,num⟩ := ih skip history v hg ha
      exact ⟨q,last,built,hit,by omega⟩
    obtain ⟨op,eq⟩ : ∃ op,z=M.op op a b := by
      rcases (show z=M.op false a b ∨ z=M.op true a b by simpa [choices] using how) with h|h
      · exact ⟨false,h⟩
      · exact ⟨true,h⟩
    let out := combine op (v a) (v b)
    let v' := Function.update v z out
    have zr : z∉r := fun mem => fresh (by simp [mem])
    have sub : r⊆insert a (insert b r) := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have back {w} (mem : w∈r) : v' w=v w := Function.update_of_ne (show w≠z from fun eq => zr (eq ▸ mem)) ..
    have same : v' z=out := Function.update_self ..
    obtain ⟨p',bank',next,know,inherit,bill⟩ := extend_two roots op history (ha a am) (ha b bm)
    have good' : ∀ w∈insert z r,M.good w (v' w) := by
      intro w mem
      rcases Finset.mem_insert.mp mem with rfl|h
      · rw [same,eq]
        exact M.combine_ok op (hg a am) (hg b bm)
      · rw [back h];exact hg _ (sub h)
    have available' : ∀ w∈insert z r,Available bank' (v' w) := by
      intro w mem
      rcases Finset.mem_insert.mp mem with rfl|h
      · exact same ▸ know
      · rw [back h];exact inherit _ (ha _ (sub h))
    obtain ⟨q,last,built,hit,num⟩ := ih tail next v' good' available'
    rw [Finset.sum_insert zr,same] at num
    have old : (∑ w∈r,cost (v' w))=∑ w∈r,cost (v w) := Finset.sum_congr rfl (fun _ hw => congrArg cost (back hw))
    rw [old] at num
    have h₁ := cost_ins a (insert b r) v
    have h₂ := cost_ins b r v
    change p'+cost (v a)+cost (v b) ≤ p+1+cost out at bill
    exact ⟨q,last,built,hit,by omega⟩

theorem cut_bound (M : Model A R) (t : A) (T : Wire R) (terminal : ∀ f,M.good t f → f=T)
    (nc : ¬Constant T) {k s} (program : live (choices M) t k s) {roots : List (Wire R)}
    {p bank} (history : Reach roots p bank) {L : ℕ}
    (low : ∀ q last,Reach roots q last → Available last T → L≤q)
    (marked : Finset A) (sub : marked⊆s)
    (repr : ∀ w∈s,∃ f,M.good w f ∧ Available bank f ∧ (w∈marked → Constant f)) :
    L+marked.card≤p+k := by
  classical
  let v (w : A) : Wire R := if h : w∈s then (repr w h).choose else fun _ => false
  have rep {w} (hw : w∈s) : M.good w (v w) ∧ Available bank (v w) ∧ (w∈marked → Constant (v w)) := by
    simpa [v,hw] using (repr w hw).choose_spec
  obtain ⟨q,last,done,out,size⟩ := finish M t T terminal nc program history v
    (fun _ hw => (rep hw).1) (fun _ hw => (rep hw).2.1)
  have markedSum : (∑ w∈marked,cost (v w))=marked.card := by
    calc
      _ = ∑ _w∈marked,(1 : ℕ) := Finset.sum_congr rfl fun w hw => by simp [cost,(rep (sub hw)).2.2 hw]
      _ = _ := by simp
  have all := Finset.sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => Nat.zero_le (cost (v i)))
  have lower := low _ _ done out
  omega

end Price
end Front2778
namespace Front2778
namespace Face
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
abbrev rawFull := PEqualNP.Outside.L_meta_2778.Cert.inputs
abbrev S := Sig
structure Data where
  mask : ℕ
  lb : ℕ
  pos : S
  neg : S
  ps : List Row
  ns : List Row
def below (m : ℕ) (r t : Row) := (r.val &&& m &&& t.val)=(r.val&&&m)
instance (m r t) : Decidable (below m r t) := inferInstanceAs (Decidable (_=_))
def Up (m : ℕ) (f : Wire Row) := ∀ r t, below m r t → f r=true → f t=true
def compat (d : Data) (w : S) (f : Wire Row) :=
  Up d.mask f ∧ (∀ r,bit r d.pos=true → bit r w=true → f r=true) ∧
    ∀ r,bit r d.neg=true → f r=true → bit r w=true
def dataOp (isOr : Bool) (a b : S) := if isOr then a|||b else a&&&b
theorem op_compat (d : Data) (b : Bool) {a c : S} {f g : Wire Row} (ha : compat d a f) (hc : compat d c g) :
    compat d (dataOp b a c) (combine b f g) := by
  rcases ha with ⟨uf,pf,nf⟩
  rcases hc with ⟨ug,pg,ng⟩
  cases b
  · exact ⟨fun x y le h => Bool.and_eq_true_iff.mpr ⟨uf x y le (Bool.and_eq_true_iff.mp h).1,ug x y le (Bool.and_eq_true_iff.mp h).2⟩,
      fun r hp h => by
        have h0 : bit r a=true ∧ bit r c=true := by simpa [dataOp,bit] using h
        exact Bool.and_eq_true_iff.mpr ⟨pf r hp h0.1,pg r hp h0.2⟩,
      fun r hn h => by
        have v := Bool.and_eq_true_iff.mp h
        simpa only [dataOp,Bool.false_eq_true,ite_false,bit,BitVec.getLsbD_and] using Bool.and_eq_true_iff.mpr ⟨nf r hn v.1,ng r hn v.2⟩⟩
  · exact ⟨fun x y le h => Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp h).imp (uf x y le) (ug x y le)),
      fun r hp h => by
        have h0 : bit r a=true ∨ bit r c=true := by simpa [dataOp,bit] using h
        exact Bool.or_eq_true_iff.mpr (h0.imp (pf r hp) (pg r hp)),
      fun r hn h => by
        rcases (Bool.or_eq_true_iff.mp h) with v|v
        · simpa only [dataOp,ite_true,bit,BitVec.getLsbD_or] using Bool.or_eq_true_iff.mpr (Or.inl (nf r hn v) : bit r a=true ∨ bit r c=true)
        · simpa only [dataOp,ite_true,bit,BitVec.getLsbD_or] using Bool.or_eq_true_iff.mpr (Or.inr (ng r hn v) : bit r a=true ∨ bit r c=true)⟩
def model (d : Data) : Price.Model S Row := ⟨compat d,dataOp,op_compat d⟩

def checkEnds (d : Data) := (List.finRange 512).all fun u =>
  if bit u (graphGoal d.mask) then d.ps.any (fun r => bit r d.pos && bit r graph && decide (below d.mask r u))
  else d.ns.any (fun r => bit r d.neg && !bit r graph && decide (below d.mask u r))

theorem terminal {d : Data} (checked : checkEnds d=true) {f : Wire Row} (good : compat d graph f) :
    f=observe (graphGoal d.mask) := by
  rcases good with ⟨up,pos,neg⟩
  funext u
  have hh := List.all_eq_true.mp checked u (List.mem_finRange u)
  change f u=bit u (graphGoal d.mask)
  cases ht : bit u (graphGoal d.mask)
  · simp [ht] at hh
    obtain ⟨r,_,⟨rn,rg⟩,le⟩ := hh
    cases hu : f u
    · rfl
    · have impossible := neg r rn (up u r le hu)
      simp_all
  · simp [ht] at hh
    obtain ⟨r,_,⟨rp,rg⟩,le⟩ := hh
    exact up r u le (pos r rp rg)

def nonePositive (d : Data) (w : S) := (d.pos&&&w)==0
def allNegative (d : Data) (w : S) := (d.neg&&&w)==d.neg
def dead (d : Data) (w : S) := nonePositive d w || allNegative d w
def dominates (d : Data) (v w : S) := ((w&&&d.pos)&&&v)==(w&&&d.pos) && ((v&&&d.neg)&&&w)==(v&&&d.neg)

theorem left_const {d : Data} {w} (h : nonePositive d w=true) : compat d w (fun _=>false) := by
  have eq := beq_iff_eq.mp h
  refine ⟨fun _ _ _ => id,?_,fun _ _ h => Bool.noConfusion h⟩
  intro r p b
  have ee := congrArg (bit r) eq
  simp only [bit,BitVec.getLsbD_and,BitVec.getLsbD_zero,show d.pos.getLsbD r.val=true from p,show w.getLsbD r.val=true from b] at ee
  have hz : (0:S).getLsbD r.val=false := by simp
  exact Bool.noConfusion (ee.trans hz)

theorem right_const {d : Data} {w} (h : allNegative d w=true) : compat d w (fun _=>true) := by
  have eq := beq_iff_eq.mp h
  refine ⟨fun _ _ _ => id,fun _ _ _ => rfl,?_⟩
  intro r n _
  have ee := congrArg (bit r) eq
  simpa [bit,show d.neg.getLsbD r.val=true from n] using ee

theorem improve {d : Data} {v w : S} {f} (h : dominates d v w=true) (good : compat d v f) : compat d w f := by
  rcases (show (w&&&d.pos)&&&v=w&&&d.pos ∧ (v&&&d.neg)&&&w=v&&&d.neg by simpa [dominates] using h) with ⟨hp,hn⟩
  refine ⟨good.1,?_,?_⟩
  · intro r pr wr
    apply good.2.1 r pr
    have e := congrArg (bit r) hp
    simpa [bit,show d.pos.getLsbD r.val=true from pr,show w.getLsbD r.val=true from wr] using e
  · intro r nr fr
    have vr := good.2.2 r nr fr
    have e := congrArg (bit r) hn
    simpa [bit,show d.neg.getLsbD r.val=true from nr,show v.getLsbD r.val=true from vr] using e

def carries (d : Data) (bank : List (Wire Row)) (w : S) := ∃ f,
  compat d w f ∧ Available bank f ∧ (dead d w=true → Constant f)

theorem trivial {d : Data} {w bank} (h : dead d w=true) : carries d bank w := by
  rcases Bool.or_eq_true_iff.mp h with off|on
  · exact ⟨_,left_const off,Or.inr ⟨false,rfl⟩,fun _ => ⟨false,rfl⟩⟩
  · exact ⟨_,right_const on,Or.inr ⟨true,rfl⟩,fun _ => ⟨true,rfl⟩⟩

end Face
end Front2778
namespace Front2778.Face
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed

def rawAt (i : Fin 9) := rawFull.getD i.val zero
def seen (h : List S) := h++rawFull
def cheap (d : Data) (z : S) (past : List S) := dead d z || past.any (fun a => dominates d a z)
def price (d : Data) : List S → ℕ
  | [] => 0
  | z::h => price d h + (if cheap d z (seen h) then 0 else 1)

inductive History : List S → Prop where
  | empty : History []
  | gate {h : List S} (prior : History h) {a b : S} (oldA : a∈seen h) (oldB : b∈seen h) (op : Bool) :
      History (dataOp op a b::h)

def checkInputs (d : Data) := (List.finRange 9).all fun i =>
  dead d (rawAt i) || (d.mask.testBit i.val && (vars d.mask).contains (rawAt i))

theorem up_raw (m : ℕ) (i : Fin 9) (active : m.testBit i.val=true) : Up m (observe (rawAt i)) := by
  intro x y le hx
  have atI := congrArg (fun n : ℕ => n.testBit i.val) le
  have on : x.val.testBit i.val=true := (input_coords i x) ▸ hx
  change bit y (rawAt i)=true
  rw [show bit y (rawAt i)=y.val.testBit i.val from input_coords i y]
  simpa only [Nat.testBit_and,active,on,Bool.true_and,Bool.and_true] using atI

theorem present_raw (d : Data) (ok : checkInputs d=true) {w} (hw : w∈rawFull) :
    carries d ((vars d.mask).map observe) w := by
  change w∈PEqualNP.Outside.L_meta_2778.Cert.inputs at hw
  rw [←input_list] at hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  have supplied := List.all_eq_true.mp ok i (List.mem_finRange i)
  rcases Bool.or_eq_true_iff.mp supplied with free | h
  · exact trivial free
  by_cases e : dead d (rawAt i)=true
  · exact trivial e
  obtain ⟨active,bank⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨_,⟨up_raw _ _ active,fun _ _ => id,fun _ _ => id⟩,
    Or.inl (List.mem_map.mpr ⟨_,List.contains_iff_mem.mp bank,rfl⟩),fun v => False.elim (e v)⟩

theorem free_copy {d : Data} {bank : List (Wire Row)} {z : S} {past : List S}
    (yes : cheap d z past=true) (supply : ∀ u∈past,carries d bank u) : carries d bank z := by
  by_cases c : dead d z=true
  · exact trivial c
  have some := (Bool.or_eq_true_iff.mp yes).resolve_left c
  obtain ⟨u,hu,relation⟩ := List.any_eq_true.mp some
  obtain ⟨f,hf,av,_⟩ := supply _ hu
  exact ⟨f,improve relation hf,av,fun h => False.elim (c h)⟩

theorem history_model (d : Data) (ok : checkInputs d=true) {hist} (path : History hist) :
    ∃ p≤price d hist,∃ bank,Reach ((vars d.mask).map observe) p bank ∧ ∀ w∈seen hist,carries d bank w := by
  induction path with
  | empty =>
    exact ⟨0,by rfl,_,Reach.start,fun _ hw => present_raw d ok hw⟩
  | @gate h path a b ha hb op ih =>
    obtain ⟨p,count,bank,prev,old⟩ := ih
    let z := dataOp op a b
    change ∃ q≤price d (z::h),∃ next,Reach _ q next ∧ ∀ w∈seen (z::h),carries d next w
    by_cases yes : cheap d z (seen h)=true
    · refine ⟨p,by simpa [price,yes] using count,bank,prev,?_⟩
      intro w hw
      rcases List.mem_cons.mp (show w∈z::seen h from hw) with rfl|m
      · exact free_copy yes old
      · exact old _ m
    obtain ⟨f,gf,af,_⟩ := old a ha
    obtain ⟨g,gg,ag,_⟩ := old b hb
    have fresh := Reach.two op prev af ag
    refine ⟨p+1,by simp [price,yes];omega,_,fresh,?_⟩
    intro w hw
    rcases List.mem_cons.mp (show w∈z::seen h from hw) with rfl|m
    · exact ⟨_,op_compat d op gf gg,Or.inl (List.mem_cons_self ..),
        fun hh => False.elim (yes (Bool.or_eq_true_iff.mpr (Or.inl hh)))⟩
    obtain ⟨v,gv,av,dv⟩ := old _ m
    exact ⟨v,gv,available_cons _ av,dv⟩

end Front2778.Face
namespace Front2778.Face
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
def checked (d : Data) :=
  checkEnds d && checkInputs d && properB (graphGoal d.mask) && decide (d.lb≤boundsBefore known383 d.mask)
def rejects (d : Data) (k : ℕ) (ws hist : List S) :=
  decide (price d hist+k < d.lb+(ws.filter (dead d)).length)

theorem reject_sound {d : Data} (ok : checked d=true) {n ws hist}
    (past : History hist) (seenW : ∀w∈ws,w∈seen hist) (nd : ws.Nodup)
    (run : Full.Path n ws.toFinset) : rejects d n ws hist=false := by
  obtain ⟨⟨⟨ends,inputsOk⟩,proper⟩,lb⟩ :=
    (show ((checkEnds d=true ∧ checkInputs d=true) ∧ properB (graphGoal d.mask)=true) ∧ d.lb≤boundsBefore known383 d.mask
      by simpa [checked] using ok)
  obtain ⟨p,amount,bank,prog,supply⟩ := history_model d inputsOk past
  let marks := (ws.filter (dead d)).toFinset
  have sub : marks ⊆ ws.toFinset := fun w hw => List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp hw)).1
  have representation (w : S) (mem : w∈ws.toFinset) :
      ∃ f,(model d).good w f ∧ Available bank f ∧ (w∈marks → Constant f) := by
    obtain ⟨f,good,there,c⟩ := supply w (seenW w (List.mem_toFinset.mp mem))
    exact ⟨f,good,there,fun h => c (List.mem_filter.mp (List.mem_toFinset.mp h)).2⟩
  have low := before_sound known383 valid383 d.mask
  have priceOK := Price.cut_bound (model d) graph (observe (graphGoal d.mask))
    (fun _ hh => terminal ends hh) (observe_proper (proper_of _ proper)) run.live prog
    (fun q bs reach out => lb.trans (low q bs reach out)) marks sub representation
  have markLen : marks.card=(ws.filter (dead d)).length := List.toFinset_card_of_nodup (nd.filter _)
  rw [markLen] at priceOK
  simp only [rejects,decide_eq_false_iff_not,not_lt]
  omega

end Front2778.Face

namespace Front2778.Face
def face0 : Data := ⟨495,13,0x100000001000001000000000000000000000000010000001000000000000000040000000200001048,0x6000000000000000000000000000000200000000000000200000000000000040000000110000000200000040000000000,[3, 6, 12, 33, 66, 132, 264, 160, 320, 288],[42, 69, 100, 104, 138, 201, 261, 385, 386]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test0 : checked face0=true := by decide +kernel
def face1 : Data := ⟨503,12,0x100000001000000000000000000000000000000010000001000000000000000040000000200020048,0x40002000000000000000000000000001000200000000000010002000000000000000000100000000000200004000000000000,[3, 6, 17, 33, 66, 132, 160, 320, 288],[50, 69, 116, 193, 208, 261, 276, 385, 402]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test1 : checked face1=true := by decide +kernel
def face2 : Data := ⟨494,11,0x100000001000001000000000000000000000000010000001000000000000000040000000000001040,0x4000000000000000000000000000000100000000000000100000000000000040000000110000000000000040000000000,[6, 12, 66, 132, 264, 160, 320, 288],[42, 100, 104, 138, 200, 260, 386]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test2 : checked face2=true := by decide +kernel
def face3 : Data := ⟨447,13,0x1000001000000000000000000000000010000001000000000000000000000000201021048,0x40002000000000000000000000000001000200000000000000000000000000000060000000000000000000014040000000000,[3, 6, 12, 24, 17, 33, 132, 264, 160, 288],[42, 50, 52, 137, 138, 261, 276, 385, 402]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test3 : checked face3=true := by decide +kernel
def face4 : Data := ⟨383,13,0x100000001000001000000000000000000000000000000000000000000000000040000000201021048,0x1400200000000000000000000000000000000000100100000002200004040000000000,[3, 6, 12, 24, 17, 33, 66, 264, 320, 288],[42, 50, 69, 73, 104, 116, 261, 274, 276]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test4 : checked face4=true := by decide +kernel
def face5 : Data := ⟨510,12,0x100000001000001000000000000000000000000010000001000000000000000040000000001001040,0x40000000000000000000000000000001000000000000000010100000000000000040000100100000000000004040000000000,[6, 12, 24, 66, 132, 264, 160, 320, 288],[42, 50, 104, 116, 138, 200, 208, 276, 402]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test5 : checked face5=true := by decide +kernel
def face6 : Data := ⟨487,11,0x100000001000000000000000000000000000000010000001000000000000000040000000200000048,0x6000000000000000000000000000000200000000000000002000000000000000000000010000000200000000400000000,[3, 6, 33, 66, 132, 160, 320, 288],[34, 69, 100, 193, 261, 385, 386]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test6 : checked face6=true := by decide +kernel
def face7 : Data := ⟨431,11,0x1000001000000000000000000000000010000001000000000000000000000000200001048,0x6000000000000000000000000000000200000000000000000000000000000060000000000000000000000041000000000,[3, 6, 12, 33, 132, 264, 160, 288],[36, 42, 137, 138, 261, 385, 386]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test7 : checked face7=true := by decide +kernel
def face8 : Data := ⟨367,11,0x100000001000001000000000000000000000000000000000000000000000000040000000200001048,0x240000000000000000000000000000000000000110000002200000040000000000,[3, 6, 12, 33, 66, 264, 320, 288],[42, 69, 73, 100, 104, 258, 261]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test8 : checked face8=true := by decide +kernel
def face9 : Data := ⟨509,12,0x100000001000001000000000000000000000000010000001000000000000000000000000201021000,0x10002000000000000000000000000001000200000000000010200000000000000000000100100000000200000000000000000,[12, 24, 17, 33, 132, 264, 160, 320, 288],[69, 104, 116, 201, 208, 261, 276, 385, 400]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test9 : checked face9=true := by decide +kernel
def face10 : Data := ⟨507,12,0x100000001000001000000000000000000000000010000000000000000000000040000000201020008,0x40002000000000000000000000000000000000000000000010200000000000000040000010100000000000004040000000000,[3, 24, 17, 33, 66, 264, 160, 320, 288],[42, 50, 104, 112, 138, 201, 208, 385, 402]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test10 : checked face10=true := by decide +kernel
def face11 : Data := ⟨479,12,0x100000000000001000000000000000000000000000000001000000000000000040000000001021048,0x40002000000000000000000000000001000200000000000010200000000000000040000000000001000200000000000000000,[3, 6, 12, 24, 17, 66, 132, 264, 320],[69, 84, 138, 201, 208, 261, 276, 385, 402]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test11 : checked face11=true := by decide +kernel
def face12 : Data := ⟨255,12,0x10000001000000000000000040000000201021048,0x10200000000000004040000100100000000200004040000000000,[3, 6, 12, 24, 17, 33, 66, 132, 160],[42, 50, 69, 104, 116, 138, 146, 201, 208]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test12 : checked face12=true := by decide +kernel
def face13 : Data := ⟨445,11,0x1000001000000000000000000000000010000001000000000000000000000000201021000,0x10002000000000000000000000000001000200000000000000000000000000000020000000000000000000010010000000000,[12, 24, 17, 33, 132, 264, 160, 288],[40, 52, 137, 261, 276, 385, 400]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test13 : checked face13=true := by decide +kernel
def face14 : Data := ⟨379,11,0x100000001000001000000000000000000000000000000000000000000000000040000000201020008,0x400020000000000000000000000000000000000010100000002000004040000000000,[3, 24, 17, 33, 66, 264, 320, 288],[42, 50, 73, 104, 112, 257, 274]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test14 : checked face14=true := by decide +kernel
def face15 : Data := ⟨351,11,0x100000000000001000000000000000000000000000000000000000000000000040000000001021048,0x1400200000000000000000000000000000000000000000001002200000000000000400,[3, 6, 12, 24, 17, 66, 264, 320],[10, 69, 73, 84, 261, 274, 276]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test15 : checked face15=true := by decide +kernel
def face16 : Data := ⟨319,11,0x1000001000000000000000000000000000000000000000000000000000000000201021048,0x1400200000000000000000000000000000000000000000000000000014040000000200,[3, 6, 12, 24, 17, 33, 264, 288],[9, 42, 50, 52, 261, 274, 276]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test16 : checked face16=true := by decide +kernel
def face17 : Data := ⟨191,11,0x10000001000000000000000000000000201021048,0x4060000000000000000000014040000000020,[3, 6, 12, 24, 17, 33, 132, 160],[5, 42, 50, 52, 137, 138, 146]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test17 : checked face17=true := by decide +kernel
def face18 : Data := ⟨499,9,0x100000001000000000000000000000000000000010000000000000000000000040000000200020008,0x40002000000000000000000000000000000000000000000010002000000000000000000010000000000000004000000000000,[3, 17, 33, 66, 160, 320, 288],[50, 112, 193, 208, 385, 402]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test18 : checked face18=true := by decide +kernel
def face19 : Data := ⟨375,9,0x100000001000000000000000000000000000000000000000000000000000000040000000200020048,0x1400200000000000000000000000000000000000100000000000200004000000000000,[3, 6, 17, 33, 66, 320, 288],[50, 69, 116, 261, 274, 276]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test19 : checked face19=true := by decide +kernel
def face20 : Data := ⟨247,9,0x10000001000000000000000040000000200020048,0x10002000000000004000000100000000000200004000000000000,[3, 6, 17, 33, 66, 132, 160],[50, 69, 116, 146, 193, 208]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test20 : checked face20=true := by decide +kernel
def face21 : Data := ⟨486,8,0x100000001000000000000000000000000000000010000001000000000000000040000000000000040,0x4000000000000000000000000000000100000000000000001000000000000000000000010000000000000000400000000,[6, 66, 132, 160, 320, 288],[34, 100, 192, 260, 386]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test21 : checked face21=true := by decide +kernel
def face22 : Data := ⟨492,8,0x100000001000001000000000000000000000000010000001000000000000000000000000000001000,0x1000000000000000000000000000000100000000000000100000000000000000000000110000000000000000000000000,[12, 132, 264, 160, 320, 288],[100, 104, 200, 260, 384]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test22 : checked face22=true := by decide +kernel
def face23 : Data := ⟨462,8,0x100000000000001000000000000000000000000000000001000000000000000040000000000001040,0x4000000000000000000000000000000100000000000000100000000000000040000000000000000100000000000000000,[6, 12, 66, 132, 264, 320],[68, 138, 200, 260, 386]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test23 : checked face23=true := by decide +kernel
def face24 : Data := ⟨430,8,0x1000001000000000000000000000000010000001000000000000000000000000000001040,0x4000000000000000000000000000000100000000000000000000000000000040000000000000000000000041000000000,[6, 12, 132, 264, 160, 288],[36, 42, 138, 260, 386]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test24 : checked face24=true := by decide +kernel
def face25 : Data := ⟨371,8,0x100000001000000000000000000000000000000000000000000000000000000040000000200020008,0x400020000000000000000000000000000000000010000000000020004000000000000,[3, 17, 33, 66, 320, 288],[50, 65, 112, 257, 274]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test25 : checked face25=true := by decide +kernel
def face26 : Data := ⟨366,8,0x100000001000001000000000000000000000000000000000000000000000000040000000000001040,0x140000000000000000000000000000000000000110000000000000040000000000,[6, 12, 66, 264, 320, 288],[42, 100, 104, 258, 260]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test26 : checked face26=true := by decide +kernel
def face27 : Data := ⟨183,8,0x10000001000000000000000000000000200020048,0x4000200000000000000000014000000000020,[3, 6, 17, 33, 132, 160],[5, 50, 52, 129, 146]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test27 : checked face27=true := by decide +kernel
def face28 : Data := ⟨428,7,0x1000001000000000000000000000000010000001000000000000000000000000000001000,0x1000000000000000000000000000000100000000000000000000000000000010000000000000000000000011000000000,[12, 132, 264, 160, 288],[36, 40, 136, 260, 384]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test28 : checked face28=true := by decide +kernel
def face29 : Data := ⟨334,7,0x100000000000001000000000000000000000000000000000000000000000000040000000000001040,0x140000000000000000000000000000000000000000000001100000000000000400,[6, 12, 66, 264, 320],[10, 68, 72, 258, 260]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test29 : checked face29=true := by decide +kernel
def face30 : Data := ⟨508,9,0x100000001000001000000000000000000000000010000001000000000000000000000000001001000,0x10000000000000000000000000000001000000000000000010100000000000000000000100100000000000000000000000000,[12, 24, 132, 264, 160, 320, 288],[104, 116, 200, 208, 276, 400]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test30 : checked face30=true := by decide +kernel
def face31 : Data := ⟨493,9,0x100000001000001000000000000000000000000010000001000000000000000000000000200001000,0x2000000000000000000000000000000200000000000000200000000000000000000000110000000200000000000000000,[12, 33, 132, 264, 160, 320, 288],[69, 100, 104, 201, 261, 385]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test31 : checked face31=true := by decide +kernel
def face32 : Data := ⟨478,9,0x100000000000001000000000000000000000000000000001000000000000000040000000001001040,0x40000000000000000000000000000001000000000000000010100000000000000040000000000001000000000000000000000,[6, 12, 24, 66, 132, 264, 320],[84, 138, 200, 208, 276, 402]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test32 : checked face32=true := by decide +kernel
def face33 : Data := ⟨446,9,0x1000001000000000000000000000000010000001000000000000000000000000001001040,0x40000000000000000000000000000001000000000000000000000000000000000040000000000000000000014040000000000,[6, 12, 24, 132, 264, 160, 288],[42, 50, 52, 138, 276, 402]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test33 : checked face33=true := by decide +kernel
def face34 : Data := ⟨382,9,0x100000001000001000000000000000000000000000000000000000000000000040000000001001040,0x1400000000000000000000000000000000000000100100000000000004040000000000,[6, 12, 24, 66, 264, 320, 288],[42, 50, 104, 116, 274, 276]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test34 : checked face34=true := by decide +kernel
def face35 : Data := ⟨501,8,0x100000001000000000000000000000000000000010000001000000000000000000000000200020000,0x10002000000000000000000000000001000200000000000010002000000000000000000100000000000200000000000000000,[17, 33, 132, 160, 320, 288],[69, 116, 193, 208, 261, 276, 385, 400]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test35 : checked face35=true := by decide +kernel
def face36 : Data := ⟨471,8,0x100000000000000000000000000000000000000000000001000000000000000040000000000020048,0x40002000000000000000000000000001000200000000000010002000000000000000000000000001000200000000000000000,[3, 6, 17, 66, 132, 320],[69, 84, 193, 208, 261, 276, 385, 402]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test36 : checked face36=true := by decide +kernel
def face37 : Data := ⟨444,8,0x1000001000000000000000000000000010000001000000000000000000000000001001000,0x10000000000000000000000000000001000000000000000000000000000000000010000000000000000000010010000000000,[12, 24, 132, 264, 160, 288],[40, 52, 136, 276, 400]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test37 : checked face37=true := by decide +kernel
def face38 : Data := ⟨429,8,0x1000001000000000000000000000000010000001000000000000000000000000200001000,0x2000000000000000000000000000000200000000000000000000000000000020000000000000000000000011000000000,[12, 33, 132, 264, 160, 288],[36, 40, 137, 261, 385]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test38 : checked face38=true := by decide +kernel
def face39 : Data := ⟨359,8,0x100000001000000000000000000000000000000000000000000000000000000040000000200000048,0x240000000000000000000000000000000000000010000000200000000400000000,[3, 6, 33, 66, 320, 288],[34, 69, 100, 258, 261]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test39 : checked face39=true := by decide +kernel
def face40 : Data := ⟨350,8,0x100000000000001000000000000000000000000000000000000000000000000040000000001001040,0x1400000000000000000000000000000000000000000000001001000000000000000400,[6, 12, 24, 66, 264, 320],[10, 72, 84, 274, 276]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test40 : checked face40=true := by decide +kernel
def face41 : Data := ⟨231,8,0x10000001000000000000000040000000200000048,0x2000000000000000400000010000000200000000400000000,[3, 6, 33, 66, 132, 160],[34, 69, 100, 130, 193]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test41 : checked face41=true := by decide +kernel
def face42 : Data := ⟨175,8,0x10000001000000000000000000000000200001048,0x60000000000000000000000041000000020,[3, 6, 12, 33, 132, 160],[5, 36, 42, 137, 138]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test42 : checked face42=true := by decide +kernel
def face43 : Data := ⟨497,7,0x100000001000000000000000000000000000000010000000000000000000000000000000200020000,0x10002000000000000000000000000000000000000000000010002000000000000000000010000000000000000000000000000,[17, 33, 160, 320, 288],[112, 193, 208, 385, 400]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test43 : checked face43=true := by decide +kernel
def face44 : Data := ⟨490,7,0x100000001000001000000000000000000000000010000000000000000000000040000000000000000,0x4000000000000000000000000000000000000000000000100000000000000040000000100000000000000040000000000,[66, 264, 160, 320, 288],[42, 104, 138, 200, 386]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test44 : checked face44=true := by decide +kernel
def face45 : Data := ⟨437,7,0x1000000000000000000000000000000010000001000000000000000000000000200020000,0x10002000000000000000000000000001000200000000000000000000000000000000000000000000000000010000000000000,[17, 33, 132, 160, 288],[52, 261, 276, 385, 400]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test45 : checked face45=true := by decide +kernel
def face46 : Data := ⟨413,7,0x1000000000000000000000000000000001000000000000000000000000001021000,0x10002000000000000000000000000001000200000000000000000000000000000020000000000000000000000000000000000,[12, 24, 17, 132, 264],[137, 261, 276, 385, 400]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test46 : checked face46=true := by decide +kernel
def face47 : Data := ⟨355,7,0x100000001000000000000000000000000000000000000000000000000000000040000000200000008,0x60000000000000000000000000000000000000001000000020000000400000000,[3, 33, 66, 320, 288],[34, 65, 96, 257, 258]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test47 : checked face47=true := by decide +kernel
def face48 : Data := ⟨349,7,0x100000000000001000000000000000000000000000000000000000000000000000000000001021000,0x1000200000000000000000000000000000000000000000001002200000000000000000,[12, 24, 17, 264, 320],[69, 73, 84, 261, 276]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test48 : checked face48=true := by decide +kernel
def face49 : Data := ⟨243,7,0x10000000000000000000000040000000200020008,0x10002000000000004000000010000000000000004000000000000,[3, 17, 33, 66, 160],[50, 112, 146, 193, 208]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test49 : checked face49=true := by decide +kernel
def face50 : Data := ⟨238,7,0x10000001000000000000000040000000000001040,0x100000000000000040000000110000000000000040000000000,[6, 12, 66, 132, 160],[42, 100, 104, 138, 200]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test50 : checked face50=true := by decide +kernel
def face51 : Data := ⟨215,7,0x1000000000000000040000000000020048,0x10002000000000004000000000000001000200000000000000000,[3, 6, 17, 66, 132],[69, 84, 146, 193, 208]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test51 : checked face51=true := by decide +kernel
def face52 : Data := ⟨167,7,0x10000001000000000000000000000000200000048,0x600000000000000000000001400000020,[3, 6, 33, 132, 160],[5, 34, 36, 129, 130]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test52 : checked face52=true := by decide +kernel
def face53 : Data := ⟨505,9,0x100000001000001000000000000000000000000010000000000000000000000000000000201020000,0x10002000000000000000000000000000000000000000000010200000000000000000000010100000000000000000000000000,[24, 17, 33, 264, 160, 320, 288],[104, 112, 201, 208, 385, 400]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test53 : checked face53=true := by decide +kernel
def face54 : Data := ⟨415,9,0x1000000000000000000000000000000001000000000000000000000000001021048,0x40002000000000000000000000000001000200000000000000000000000000000060000000000000000000000000000000000,[3, 6, 12, 24, 17, 132, 264],[137, 138, 261, 276, 385, 402]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test54 : checked face54=true := by decide +kernel
def face55 : Data := ⟨381,9,0x100000001000001000000000000000000000000000000000000000000000000000000000201021000,0x1000200000000000000000000000000000000000100100000002200000000000000000,[12, 24, 17, 33, 264, 320, 288],[69, 73, 104, 116, 261, 276]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test55 : checked face55=true := by decide +kernel
def face56 : Data := ⟨223,9,0x1000000000000000040000000001021048,0x10200000000000004040000000000001000200000000000000000,[3, 6, 12, 24, 17, 66, 132],[69, 84, 138, 146, 201, 208]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test56 : checked face56=true := by decide +kernel
def face57 : Data := ⟨127,9,0x40000000201021048,0x100100000002200004040000000000,[3, 6, 12, 24, 17, 33, 66],[42, 50, 69, 73, 104, 116]⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem test57 : checked face57=true := by decide +kernel
def faces : List Data := [face0,face1,face2,face3,face4,face5,face6,face7,face8,face9,face10,face11,face12,face13,face14,face15,face16,face17,face18,face19,face20,face21,face22,face23,face24,face25,face26,face27,face28,face29,face30,face31,face32,face33,face34,face35,face36,face37,face38,face39,face40,face41,face42,face43,face44,face45,face46,face47,face48,face49,face50,face51,face52,face53,face54,face55,face56,face57]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem all_faces : ∀ d∈faces,checked d=true := by
  simp only [faces,List.forall_mem_cons,List.forall_mem_nil,true_and,and_true]
  exact ⟨test0,test1,test2,test3,test4,test5,test6,test7,test8,test9,test10,test11,test12,test13,test14,test15,test16,test17,test18,test19,test20,test21,test22,test23,test24,test25,test26,test27,test28,test29,test30,test31,test32,test33,test34,test35,test36,test37,test38,test39,test40,test41,test42,test43,test44,test45,test46,test47,test48,test49,test50,test51,test52,test53,test54,test55,test56,test57,by simp⟩
end Front2778.Face
namespace Front2778.Full
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
def posRows : List Row := [3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288]
def pMask : Sig := 0x100000001000001000000000000000000000000010000001000000000000000040000000201021048
def nMask : Sig := 0x40002000000000000000000000000001000200000000000010200000000000000040000100100000000200004040000000000
def global : Face.Data := ⟨511,0,pMask,nMask,posRows,[]⟩
def useful (ws : List Sig) (z : Sig) :=
    decide (2≤(posRows.filter fun r => bit r z).length) && !(ws.any (fun w => Face.dominates global w z))

def rowSmall (i : Fin 24) := rowFrom (assignment i)
theorem rows_ok : ∀ i : Fin 24,if target.getLsbD i.val then
    bit (rowSmall i) pMask=true ∧ rowSmall i∈posRows else bit (rowSmall i) nMask=true := by decide +kernel
theorem rows_inj : Function.Injective rowSmall := by decide +kernel
theorem global_pos : ∀ r∈posRows, bit r graph=true := by decide +kernel
theorem global_neg : ∀ r : Row, bit r nMask=true → bit r graph=false := by decide +kernel

theorem dominates_proj {a b : Sig} (rel : Face.dominates global a b=true) : better (project a) (project b) := by
  have E : (b&&&pMask)&&&a=b&&&pMask ∧ (a&&&nMask)&&&b=a&&&nMask := by simpa [Face.dominates,global] using rel
  intro i
  have label := rows_ok i
  cases hr : target.getLsbD i.val <;> rw [hr] at label
  · intro h
    have hit : bit (rowSmall i) a=true := (project_bit a i) ▸ h
    rw [project_bit b i]
    change bit (rowSmall i) b=true
    have eq := congrArg (bit (rowSmall i)) E.2
    simpa only [bit,BitVec.getLsbD_and,show nMask.getLsbD (rowSmall i).val=true from label,show a.getLsbD (rowSmall i).val=true from hit,Bool.true_and] using eq
  · intro h
    have hit : bit (rowSmall i) b=true := (project_bit b i) ▸ h
    rw [project_bit a i]
    change bit (rowSmall i) a=true
    have eq := congrArg (bit (rowSmall i)) E.1
    simpa only [bit,BitVec.getLsbD_and,show pMask.getLsbD (rowSmall i).val=true from label.1,show b.getLsbD (rowSmall i).val=true from hit,Bool.true_and] using eq

theorem wide_proj {z : Sig} (wide : 2≤(positive (project z)).card) :
    2≤(posRows.filter fun r => bit r z).length := by
  obtain ⟨u,hu,v,hv,diff⟩ := Finset.one_lt_card.mp wide
  have transfer (i : Fin 24) (hi : i∈positive (project z)) : rowSmall i∈posRows.filter (fun r => bit r z) := by
    have good : (project z).getLsbD i.val=true ∧ target.getLsbD i.val=true := by simpa [positive,BitVec.getLsbD_and] using hi
    have atI := rows_ok i
    rw [good.2] at atI
    exact List.mem_filter.mpr ⟨atI.2,(project_bit z i) ▸ good.1⟩
  apply Nat.le_trans _ (List.toFinset_card_le _)
  exact Finset.one_lt_card.mpr ⟨_,List.mem_toFinset.mpr (transfer u hu),_,List.mem_toFinset.mpr (transfer v hv),
    fun eq => diff (rows_inj eq)⟩

theorem useful_ok {ws : List Sig} {z : Sig} (clean : ∀w∈ws.toFinset,¬better (project w) (project z))
    (wide : 2≤(positive (project z)).card) : useful ws z=true := by
  have hh : ws.any (fun w => Face.dominates global w z)=false := List.any_eq_false.mpr (by
    intro w hw
    exact fun hit => clean _ (List.mem_toFinset.mpr hw) (dominates_proj hit))
  simp [useful,wide_proj wide,hh]

def remaining (p : Row) : List Sig → Sig
  | [] => nMask
  | w::ws => if bit p w then w&&&remaining p ws else remaining p ws
def separates (ws : List Sig) := posRows.all (fun p => remaining p ws==0)

theorem remaining_at (p n : Row) (ws : List Sig) : bit n (remaining p ws)=true →
    bit n nMask=true ∧ ∀ w∈ws,bit p w=true → bit n w=true := by
  induction ws with
  | nil => simp [remaining]
  | cons w ws ih =>
    cases h : bit p w
    · simp only [remaining,h,Bool.false_eq_true,ite_false]
      intro on
      obtain ⟨hm,all⟩ := ih on
      exact ⟨hm,by intro v hv hp;rcases List.mem_cons.mp hv with rfl|mem;exact False.elim (Bool.noConfusion (h.symm.trans hp));exact all _ mem hp⟩
    · simp only [remaining,h,ite_true]
      intro on
      have both : bit n w=true ∧ bit n (remaining p ws)=true := by simpa [bit] using on
      obtain ⟨hm,all⟩ := ih both.2
      exact ⟨hm,by intro v hv hp;rcases List.mem_cons.mp hv with rfl|mem;exact both.1;exact all _ mem hp⟩

theorem gate_sep (p n : Row) (a b z : Sig) (how : z∈SOp a b) :
    (bit p z=true ∧ bit n z=false) →
    (bit p a=true ∧ bit n a=false) ∨ (bit p b=true ∧ bit n b=false) := by
  rcases (show z=a&&&b ∨ z=a|||b by simpa [SOp] using how) with rfl|rfl <;>
    simp only [bit,BitVec.getLsbD_and,BitVec.getLsbD_or] <;>
    cases a.getLsbD p.val <;> cases a.getLsbD n.val <;> cases b.getLsbD p.val <;> cases b.getLsbD n.val <;> decide

theorem separates_ok {ws k} (run : Path k ws.toFinset) : separates ws=true := by
  apply List.all_eq_true.mpr
  intro p hp
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let n : Row := ⟨j,hj⟩
  change bit n (remaining p ws)=(0:Sig).getLsbD j
  have hz : (0:Sig).getLsbD j=false := by simp
  rw [hz]
  apply Bool.eq_false_iff.mpr
  intro bad
  obtain ⟨hn,miss⟩ := remaining_at p n ws bad
  obtain ⟨w,mem,hit,off⟩ := live_separates (fun w => bit p w=true ∧ bit n w=false)
    ⟨global_pos p hp,global_neg n hn⟩ (gate_sep p n) run.live
  exact Bool.noConfusion (off.symm.trans (miss w (List.mem_toFinset.mp mem) hit))

end Front2778.Full
namespace Front2778.Full
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
variable {α : Type}
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))

theorem pick_one {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a,rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,rest),hm,rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a,b,rest) ∈ pairs ws ∨ (b,a,rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hm,rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r,.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hm,rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),hm,rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),hm,rfl⟩))
def keepChoices (a b : Sig) (r : List Sig) := [r, a::r, b::r, a::b::r]

theorem recover_kept {ws r : List Sig} {a b : Sig} {needed : Finset Sig}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a::b::r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a::r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b::r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

def children (k : ℕ) (ws : List Sig) := (pairs ws).flatMap fun (a,b,r) =>
  [a&&&b,a|||b].flatMap fun z =>
    if useful ws z then (keepChoices a b r).filterMap fun retained =>
      let child := z::retained
      if child.length≤k+1 && separates child then some child else none
    else []

theorem Path.first {k s} (run : Path (k+1) s) :
    ∃ a b z,∃ r : Finset Sig, s=insert a (insert b r) ∧ a≠b ∧ z∈SOp a b ∧
      z∉s ∧ (∀ w∈s,¬better (project w) (project z)) ∧ 2≤(positive (project z)).card ∧ Path k (insert z r) := by
  cases run with
  | step ab hop new clean wide next => exact ⟨_,_,_,_,rfl,ab,hop,new,clean,wide,next⟩

theorem children_has {ws : List Sig} {k : ℕ} {hist : List Sig} (h : Path (k+1) ws.toFinset)
    (hn : ws.Nodup) (past : Face.History hist) (supply : ∀w∈ws,w∈Face.seen hist) :
    ∃ z rem, z::rem∈children k ws ∧ (z::rem).Nodup ∧ Path k (z::rem).toFinset ∧
      Face.History (z::hist) ∧ ∀w∈z::rem,w∈Face.seen (z::hist) := by
  obtain ⟨a,b,z,r,shape,ab,hop,new,clean,wide,tail⟩ := h.first
  have am : a∈ws := List.mem_toFinset.mp (shape ▸ (by simp))
  have bm : b∈ws := List.mem_toFinset.mp (shape ▸ (by simp))
  obtain ⟨rest,choice,order⟩ := pick_two am bm ab
  have credit := useful_ok clean wide
  have oldA := supply a am
  have oldB := supply b bm
  have hbuild : Face.History (z::hist) := by
    rcases (show z=a&&&b ∨ z=a|||b by simpa [SOp] using hop) with rfl|rfl
    · exact Face.History.gate past oldA oldB false
    · exact Face.History.gate past oldA oldB true
  have go {a b : Sig} (picked : (a,b,rest)∈pairs ws) (perm : ws.Perm (a::b::rest))
      (shape : ws.toFinset=insert a (insert b r)) (hop : z∈SOp a b) :
      ∃ rem,z::rem∈children k ws ∧ (z::rem).Nodup ∧ Path k (z::rem).toFinset ∧
        Face.History (z::hist) ∧ ∀w∈z::rem,w∈Face.seen (z::hist) := by
    obtain ⟨rem,hkept,nd,eq⟩ := recover_kept perm hn shape
    have old : rem.toFinset⊆ws.toFinset := by rw [eq,shape];exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have valid : (z::rem).Nodup := List.nodup_cons.mpr ⟨fun hm => new (old (List.mem_toFinset.mpr hm)),nd⟩
    have run : Path k (z::rem).toFinset := by simpa [eq] using tail
    have fits := live_card run.live
    rw [List.toFinset_card_of_nodup valid] at fits
    have sep := separates_ok run
    refine ⟨rem,?_,valid,run,hbuild,?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨_,picked,List.mem_flatMap.mpr ⟨z,?_,?_⟩⟩
      · simpa [SOp] using hop
      · simp only [credit,ite_true]
        exact List.mem_filterMap.mpr ⟨rem,hkept,by simp [sep]; simpa using fits⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl|given
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (supply _ (List.mem_toFinset.mp (old (List.mem_toFinset.mpr given))))
  refine ⟨z,?_⟩
  rcases choice with one|two
  · exact go one order shape hop
  · apply go two (order.trans (.swap _ _ _)) (shape.trans (Finset.insert_comm ..))
    rcases (show z=a&&&b ∨ z=a|||b by simpa [SOp] using hop) with rfl|rfl <;> simp [SOp,BitVec.and_comm,BitVec.or_comm]

end Front2778.Full
namespace Front2778.Full
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
abbrev Advice := ℕ→ℕ×ℕ

def scan (faces : List Face.Data) (k : ℕ) (hist : List Sig) (next : ℕ→List Sig→List Sig→Bool) :
    List (List Sig) → ℕ → ℕ → Bool
  | [], _, _ => true
  | [] :: _, _, _ => false
  | (z::r) :: more, child, packed =>
      let code := packed &&& 63
      let localCheck := if code=0 then next child (z::r) (z::hist)
        else (faces[code-1]?).any (fun f => Face.rejects f k (z::r) (z::hist))
      localCheck && scan faces k hist next more (child+(if code=0 then 1 else 0)) (packed >>> 6)

theorem scan_seen {fs k h next kids id packed z r}
    (ok : scan fs k h next kids id packed=true) (mem : z::r∈kids) :
    (∃ f∈fs,Face.rejects f k (z::r) (z::h)=true) ∨ ∃ i,next i (z::r) (z::h)=true := by
  induction kids generalizing id packed with
  | nil => simp at mem
  | cons child more ih =>
    cases child with
    | nil => simp [scan] at ok
    | cons v vs =>
      have both := Bool.and_eq_true_iff.mp ok
      rcases List.mem_cons.mp mem with eq|later
      · obtain rfl := List.cons.inj eq |>.1
        obtain rfl := List.cons.inj eq |>.2
        let code := packed&&&63
        by_cases zero : code=0
        · exact Or.inr ⟨_,by simpa [code,zero] using both.1⟩
        · have has : (fs[code-1]?).any (fun f => Face.rejects f k (z::r) (z::h)) = true := by
            simpa [show (packed&&&63)≠0 from zero] using both.1
          cases atIdx : fs[code-1]? with
          | none => simp [atIdx] at has
          | some f => exact Or.inl ⟨f,List.mem_of_getElem? atIdx,by simpa [atIdx] using has⟩
      · exact ih both.2 later

def verify (ad : Advice) (faces : List Face.Data) : ℕ→ℕ→ℕ→List Sig→List Sig→Bool
  | 0, _, _, _, _ => false
  | _+1, 0, _, _, _ => false
  | dep+1, k+1, id, ws, hist =>
    let cfg := ad id
    scan faces k hist (verify ad faces dep k) (children k ws) cfg.1 cfg.2

theorem verify_no {ad : Advice} {faces : List Face.Data} (valid : ∀f∈faces,Face.checked f=true)
    {depth k id ws hist} (pass : verify ad faces depth k id ws hist=true)
    (nd : ws.Nodup) (past : Face.History hist) (supply : ∀ w∈ws,w∈Face.seen hist) : ¬Path k ws.toFinset := by
  induction depth generalizing k id ws hist with
  | zero => simp [verify] at pass
  | succ depth ih =>
    cases k with
    | zero => simp [verify] at pass
    | succ k =>
      intro run
      obtain ⟨z,r,appearance,nd',child,past',sup'⟩ := children_has run nd past supply
      rcases scan_seen pass appearance with ⟨f,hf,yes⟩|⟨i,yes⟩
      · exact Bool.noConfusion (yes.symm.trans (Face.reject_sound (valid f hf) past' sup' nd' child))
      · exact ih yes nd' past' sup' child

end Front2778.Full

namespace Front2778.Full
def records0 : Array (ℕ × ℕ) := #[(1,0x820820020800020800000410410020820820810820000000420820000000400800c30c30820c3),(18,0x208209408229408200b6410410400820820820430c30c20820803d96400420c308201450e0018820830820825140820c35140410820c3),(24,0x208200208a0020000020820820820000000830c30c208308000e0020a20c30820830e28868800a2083),(37,0x20820af0822800410420820820420803310420c30c2083082010bc00400800030c208003100e0400800c30410410820c3000c40bc00410000820000410c3),(57,0x8208234208db4104100208208204208db800420c30c20830821041010840030c208d34e38138238304104104134d34d0410820c3041),(60,0x208208a0826c00410400820820810820310010830c30820c20850050050421400c308200ec40040094503082082000000c400410820823cf0c3),(75,0x20820800820000410400820820810820000010830c30820c208028a0010800030c208034d0000400820030820820001040000000410820000c3),(99,0x20820800820000410420820820420800000400830c30820c20802cb00100208000308200030c0010800c30820820001450000000410820000c3),(123,0x208208008200b041040082082081082031c410020c30c20830821040040010821000c208000f001099643082082c40c40c400410820c338e0c3),(137,0x8208290208c301041302082082042080b8c0400830c30820c20851450420850030823cf30c0423c308208230c30c0410410410820c3),(140,0x20820800822c004104008208208108200d0010020c30c20830820004ae0420800030823c0000001082003082082b80b80b80041041082b800c3),(159,0x20820800800020820820803000820000020030c30820c30a34000820000c30820830e31a30a38c0083),(172,0x20820af0410820820420803010820800010026430c20830c20840040010840040c308200040100202f003082082082492000041082000bc00c3),(189,0x82082b010420820810822cb04208202d04008b0c30820c30821401410851430c20904014022cb4030410410c32cb0410820412cb041),(192,0x208209b04108208204208c00108209b3410020030c20830c209b6d2042b800c30824000018c20800030820820c30820410826db6db0c3),(200,0x208209b0410020820810820000420820000400940c30820c30821401410851400c20841000421001030820824404400410824404400c3),(214,0x82082b010400820820420a400108208a2812822830c20830c209248109228a0c208410004208410308208228a08204104128a0410c3),(217,0x20820af04100208208108200004208236f0400940c30820c308249b6c10800000c2085005001082145003082082bc00c3410041082bc0bc00c3),(230,0x820820823830820940830420c23af0ec5020142820c10410830d92ce062882043514514),(231,0x8208008208e0c208208350108308a0ec50250d00a08208250438e641083514514),(233,0x820820823e20820825020c108308b002b140803190c20825053cf641083514514),(235,0x20820020823e208208208350108308f0ac50264008308208f294041083514514),(237,0x820825022940820820c30c20820803196420c30805143820830825140820c30820c30a32d90820c302f5140820830e31990820d48a2514),(240,0x20820826430948820820820c10830940d40998c25020820c20420d4654514),(240,0x2082bc22a208208208200c8820c30c2083080c4e0a20c30a34220800c30420830e21860a20c3),(243,0x2082bc208a3820820820ae30e0830c30820c20820c35d71825c20c2b9038e0af0030c10422802b128208a0c30410828a2b2c38e0828a20410c3041041),(245,0x208208a09b3820820820ae3b10830c30820c20820c35c65f1094083085bc53850859030c108a00a2b10822940c3082bef38eb2c0820823cf0c3041),(246,0x8208e0ac3820820820a43800830c30820c20820c35c65c0097083082bca2ae0aeb830c108a00a34a00208a0c3082bef10438e8a20828a20c3041),(250,0x820af0822ac0820820c30c20820313820830c20820c38931820830802cbbc2083bc088008200030cc420c38a2082000145000c710820c38a28a2),(260,0x820af0ae2c20820830c308208e38e0820c30820830dd4dd882083082104b04c4208310e1020aeb8fc420ce39908208228a28ac710820c30c328a38e0c328a),(260,0x208208a08c3020820830c30820a438c0820c30820830e218c3020830851450820c59050823cf30c0833cf08230c28a0410410c3082082),(260,0x820ac08bb820820830c30820ae36e0820c30820830d31a20020830820002ae0820eeba20823eeb800020838a2082082bae28abae0410820c38a28a2),(265,0x820af0820820ae3020c30820c238e0823830c20820c375d09908308210a100084c430c4102bae402bc338e762082082492bc0082bf10c338e186),(267,0x208208a08208208b2c20c30820c2b0e0822c30c20820c388608b083085bc50850c31450904022cb0d04100410c32cb0820410412cb186),(267,0x8209b08208208cb820c30820c26cd0828830c20820c36c60a20830826db282b830ee88242eb820800ee8a30820c30820826db0c36db6db),(268,0x8209b0820820acb020c30820c238e0823830c20820c375d8825020c216f14214314e142084100084b0310408228a46c08228a0c338e186),(269,0x820af0820820afbc20c30820c236f0825030c20820c31a2bc25020c208a6db080003be2085bc5bc20850c5bc508228a0c3410082bef0c3bef104),(271,0x8208250208a5010410820820810c30c208209b2d906308308201450e0620830420803190420c30020410410820c35141455000c30410820410c3),(275,0x20820820998c30805220c20c00410420c364b6418a20810c10410830d4154c43042043),(277,0x2082bc228008208208200cc420c30c20830a342f0800c3080c4e0a20c30420830e21860a20c3)]
def records1 : Array (ℕ × ℕ) := #[(281,0x820af08abc208208208032f0830c30820c28d0bef0af0030c2bc0bf13828830c20a28afc6fbc20a28810430c20830e21860a20c3),(284,0x8208234104208208108234c0420c30820c208d401bc2bc308234d381382383042084101084c430c40410410820c304134d34d0410820c30410c3),(284,0x820822810420820810822cb0420c30820c20904014022cb0c20ac381b022c3042085bc50421430c50410410820c30c32cb0410820412cb0410c3),(284,0x820826410420820810823190420c30820c20906590630800c209b34188264304209b2810ae0c30ae0410410820c30c31046400410826590410c3),(286,0x20820820998c00c26e20c20c00410420c36cd0628826410c10410830c3119bc1099043),(288,0x820820823af0c10410830d92ce06288204308e0ec5020142820c20825020c1083514514),(289,0x2082bc208a3820820820ae30e0830c30820c2b9038e0af0030c10420a28acb0e3820a28810430c22802b128208a0c30820830d75c6097083041041041),(291,0x208208a041082082042080c410830c20830824100014024000c30410836ef0710945010c2085bc50010853030c51420afbf104208f0c3145145145),(295,0x20820b404108208204208cc410830c208308242f0010020000c3041083c4d341002080043082bca2810800030f40020afbc40010800c3000bef000),(310,0x208208208ebc00c10410830ec341bc008004308ab83b82082c4d04a0020030820af10e3810ae0eebaebafbef),(315,0x20820af0822ac0410420820820430c3082082000c403810020c304108300b2ef04008204308200030cc410830ec002080140c710420c3000bef000),(330,0x208208208042f0c10410830c02ef06f00204308030300208200bbc130008308208015042f0420efbc002fbef),(340,0x208209008a40208208208032f0830c30820c2bc0410382bc30c10420a38d042fbc20a38c10430c230c32f0823000c30820830d8198098083041041041),(343,0x20820af0410820820420ae3010830c208308238038004e08e0c3041083659bc1bc26410c2084284001084c430c41020824af042bf10c3104104104),(346,0x8208208242e0c10410830d03418e309b0430900f46c2b8c0800c20820c20426c36db6db),(347,0x2082082b800c202e0c10410830cb3410000810c2bc2b8002e0ae08000000208230a041083baebaebafb80),(358,0x82082090b030b43830410420c3641bc00940430af3850050ac40400408208a04228340eb11b11451),(361,0x208208d08234b0410710820820810c30c208208d34e3813820c10412cb34d04208108234d3ed0420ce38308228ac410830c328334d38e),(361,0x8208208308d38104104b0420422ef08e34234c0ed0c20823450000420c43830c3),(363,0x208208d08208208d3020c30820c2104084c430c234d38238304104134d0820c304108d4020af0c310e34d0820830cd1828c20c438e186),(363,0x820822810420820810822cb0420c30820c2085bc50421430c20ac381b022c30420904014022cb0c50410410820c30c32cb0410820412cb0410c3),(363,0x8208234104008208204208b2c10830c208308214d1410850c208d3813822c30420841010842c31030410410412cb0410820412cb041),(364,0x20b108208234b0c2c4e2c22c408208d2c10822c30410412c10812c1),(364,0x20820af041bc2082081082bef0420c30820c2085bc504214308236fbc1bc250304208a6c1080003145082082104bc00c34100410820823cf0c3),(367,0x82bc20820afbc30afbd4080bc208236f04208f0c208212f0034010823c3),(369,0x208208a09b3820820820ae3b10830c30820c216f14e1421640c3082bef38eb2c0820823cf0c308a00a2b10822940c30820830d7197c425020c1041),(370,0x208208a041082082042080c410830c208308216f14004214c0c3082befc410823c30c20904000500900030c51410420dbbc1c42514043145145145),(374,0x20b10820823a40c208236c04208f0c22ae0ef14237104a00250208210e39b042503145145),(375,0x208208a08230c04104c0820820810c30c20820a438c3019020c20af2cb0420830823cf30c0420cf3c22c208c30a2810410c308230f30f),(375,0x820826c10400820820420acb010830c208308238e0013823940c20afbec04208f0c208410004212c0c410208a29104228a0c3104104104),(378,0x20820af041bc2082081082bef0420c30820c208dbef06f09450308234dbef0420823cf0c208a6db0420000efbc208a283410042bef0c3bef041041),(380,0x2082082bec0c2c42082bcb0420c24021714002cb2c200314c30f08b082094c4108314515451404104f3cf),(382,0x20800820ac0c202e08208b2c108308214002e000002b8008f3c23cb3c208229404108316eb9408208b2cb),(390,0x8208a082082080c420c30820c2085bc500214c0c30b13825140c20afbf100208208f3c30c24100824030c54104100820830db7825020c57a3186),(393,0x820820af30308e502082bc10823c308ac4314400409b40e400402082092042c4314ec6f011451),(396,0x8208250208b6410410020820820430c308208250ab8108308250db8188208304208f659001083b830820820821045005140410410820c3),(399,0x8208008208a0c2340882099b82082504659641083082082114014041083),(402,0x820826410420820810823190420c30820c209b2810ae0c30826cd0620990c10824196418c20030ae0410410820c30c31046400410826590410c3),(404,0x208208208ab8308d8820998c008209b1196410990c10410830c3119001099043),(406,0x820820010400820820420ae0010830c208308249204248308238e04e08e0c10821041040440841040c4104104)]
def records2 : Array (ℕ × ℕ) := #[(409,0x2082080041002082081082b800420c30820c2092481092b830c208e38004e082383082082bef6590410826590c30821041040440841040c4104104),(413,0x20820af041bc2082081082bef0420c30820c208a6c108000308236fbc1bc2503042085bc5042143145082082104bc00c34100410820823cf0c3),(416,0x20af0820822800c236fbc20af082084bef6c10940c208212f0034010823c3),(418,0x8208008208a0c208250438e64108308e0ec50250d00a082082083501083514514),(420,0x8208e0ac3820820820a43800830c30820c20af28ab82bae0c3082bef10438e8a20828a20c308a00a34a00208a0c30820830d71970025c20c1041),(424,0x20820b404108208204208cc410830c2083082bca2810800030c20afbc40010800c308242f0010020000c3d00041083c4d341002080043000bc0bc0),(439,0x208208208ab830820af10e3810ae0c23af003b82082c4d04a0020030410420c3b0d06f0020010eebaebafbef),(444,0x20b10820822ae0c208210e39b04250308e903bc508dc4128009408208db010823c3145145),(445,0x20820ac0822ee0410400820820810c30c20820ae34db8006e0820c2080004bae0420830823eeb800010820ecb820ae28ab810420c3baeb80b80),(453,0x2082002082340b820820801124ae0420c24800ae0820802ae0420c2082b8ab810420eebaebb2bb2),(458,0x8208208236e0820826c4492042b830928c2d1b09b2ae0c20820c20426c36db6db),(458,0x82bc208208dbef08208211249b042503092bc2bc508208a6c100308208a0d0042bc3145145),(459,0x8208208a0c2340082082bc40000420c22c0080000002303000000082085000c4108300000002fbef),(478,0x20b10820830b13820820af6410830acc4210d10d1041024aeb8e6596420822b10420ca28a0ca04104e38e),(478,0x8230208228308d32408208212eb8c0420c20a414230f3c20822810410cc082082),(478,0x820b408208208cc420c30820c20af28a0800030c2c4d3420800c20afbc41000020800030c242f0820030e3bc08e30820830c65428c20e38c08e3),(488,0x2082082b8308e082082bc10990c2d310ca10a1041040af48ebc06596420823410b10c234d34d041052492),(489,0x8208208a2c308db020820840000422c3083bc50902d04010412c10810432c30c3),(491,0xb4082082b030b43820820990425030923af16f0b4b0410410408208d04228328d041044104),(491,0x8208250208a5010410820820810c30c208209b2d906308308200c6410830c108201450e062083bc20410410820c35141455000c30410820410c3),(494,0x208208208b8c20803030948800820941545190420c10410830d4154003042043),(497,0x20820af0410820820420b1c41c420c30820c20b12c1c42bf10c208000c042643042084131042103104082082082492145c400410820c338e0c3),(500,0x20820b10822f10b10803030b1082080171c410990c2082092171001083383),(503,0x82082c410420820810820000400830c20830824100500900c208f3c108f0c10821451450450851450c5145145),(506,0x20820b10410820820420800010020c30820c20904014020900030823c03c108f0c3082082514c710410825140c30821451450450851450c5145145),(511,0x8208250104208208108250d0400830c20830822c00630820030823000425030420945120420030ee0820821455000820410410825140c3),(517,0x8208200208b8c2002303094b82082154500042503082085500081042503),(521,0x820820822c00820825053cf64108308f882b140803190c20825020c1083514514),(523,0x82082c4208bc42c420820053cf04264308f0adc440820803016430820ac301083383104104),(525,0x20820b40410820820420803410020c30820c208b2c00400820000c20850000010820030820004810820000eeb8208c32e0410ae0c3baec80c80),(541,0x20820800822c00800820853cf0010800c23c202e08208c0010800c208232c0410800c002e032cb2),(553,0x20820af0822ac0410420820820430c308208200030cc410830c2080140c710420c3082000c403810020c3b0004108300b2ef040082043000bc0bc0),(568,0x208208208030308208015042f0420c2010bc3bc208200bbc13000830410420c300bbc1bc00810c002f02fbef),(578,0x8208240295008208208042f0830c30820c208000c3310800c30828e3145410c710828e30c308c2cb3000823000c30820830d81980980020c1041),(585,0x20820af08200c0c20820054100426430a5403c440802c13000af08208248b042bc3104104),(589,0x8208200208c0c20821504310426c30900ee6c22c03020020820c20426c36db6db),(592,0x820af0822ac0820820c30c208200b2ef0820c208000c3310830c2080005140031c420830c20313820830ef0228a20820830e24c60820e20228a2),(602,0x8208208bbc208d30308208d140001083083b4408d38e38104104b04204d0c30c3),(604,0x20820824020800c20825310420c2bec0c53053051450b143100f514502082bcb0420cb2cb08b04104f3cf),(606,0x8208208b00208c0c20821400310420c228300000008d0020000000820af10000108300000002fbef)]
def records3 : Array (ℕ × ℕ) := #[(625,0x820ac082402b02d030820940425030afb051451450903f113108208c0422c32cc041045145),(625,0x8208a0822e508a08c0c2082171c4108a0c22924820a51020822810410c2282082),(625,0x2082bc20900af0830820af0425030903c00145140af0af2c52c51451420823010af0c330c30c041050410),(627,0x20820af0410820820420b1c41c420c30820c20841310421030820003010990c1082c4b0710afc43104082082082492145c400410820c338e0c3),(630,0x8208230104c08208204208a2812820c30820c208410c0421030823cc04228304208514108528310208208228a04104104104128a0c3),(630,0x820822c107108208204208a2812820c30820c20841310420840c208fb0108a0c108249204228a0c408208228a08204104108204128a0c3),(630,0x82082c4208f0ad0820ac30108338308bc42c7110208200c0590c20820053cf042643104104),(632,0x208208b041002082081082bae06e0830c2083082100100042084343082bb10010820ce0c2092012042092b83104082bae041099643104104104),(637,0x2080082b8208f0023420823c00420ce0c23c2b8408208f0010990c20823ee0410990c4104104104),(641,0x208208d08234b0410710820820810c30c208208d34fb4108308228ac410830c208d34e3813820ce3832810412cb34d0420810c334e34e),(641,0x20820af0410820820420b1c41c420c30820c208000c0426590c20b1c4c30108338e0c3082c402c1c42bf10f1c420824922cb0420afc43c71041041),(644,0x820826c10710820820420acb01b020c30820c208f00f0423d40c20acc710420ce0c208500504216c0c51420912cb04208b2c3145145145),(646,0x820af0ae2c20820830c3082082104b04c42083082bae3f108308208228a28ac710820c308e38e0820c310e38e0c328e28e0820830dd4dd8820831190c328a),(646,0x20b10820acc420820822b10420c20c4b92b8a28a0b138210d34e0ca0820af64108310411965904104e38e),(646,0x82082bc20820b1c420c30820c2104c42084c430820003026590c20b1c4c3020830ce3830c28cb082bc30c4c71c710820830e31828f1083123145),(648,0x2082b8209b08d09908208c0420ce0c26c34920a3084c40c420820c10990c26c2082),(649,0xaf082bc20af08d0940820af0420ce0c26cf4804822c2bc41401420820d0042bc310fbefbd1451),(651,0x208208a08230c04104c0820820810c30c208208f3cc30108308230c28a0410430c20a438c3019020cf3c2082bcb2c10820c22c230c3cf),(651,0x208208a08c3020820830c30820851450820c208f3cc3020c208c30a2810410430c290e3020830c590f0820820830e218c30208314f082),(651,0x823020820823020822810410c22833cc08d3240a408208212eb8c0420c53c2082),(651,0x8208250208b6410410020820820430c308208250ab810830823d96400420c108250db81882083b830820820821045005140410410820c3),(654,0x8208250104208208108250d06e0830c20830825144810ae0c208cb810940c10822ee063082b830c00820821455000820410410825140c3),(656,0x820822c104008208204208a2812820c30820c209248108a2830823ec0422830420841000420840c408208228a08204104108204128a0c3),(658,0x8208230104c08208204208d301b820c30820c20923010ae0c208f30c0423c304208514108216e0c508208230c04130c0410410820820c3),(658,0x20820020823c208208f29404108308f882b140990020c2082083501083514514),(660,0x20820b40410820820420803410020c30820c208001204208000308230cb81042b830c208b2c00400820000eeb82085000001082003baecb2000),(676,0x20820800823c200208232c0410800c22c00800020823000420030820853cf0010800eeb80032cb2),(688,0x208208b041002082081082bae06e0830c20830824804810824ae0c20aeb810426590c208400400108210d0c41020aec40042083383104104104),(693,0x2080082b8208f0ae08208fb8104264308f00234408208f0010990c20823c00420ce0c4104104104),(697,0x20820ac0822ee0410400820820810c30c208208fbae000042083082b8a2ae0410830c20ae34db8006e0820ecb82080004bae042083baebae000),(705,0x2082002082480082082b8ab810420c2340b82b8208200ab810830820801124ae0420eebaebaecb2),(710,0x20820af04100208208108236f0400830c20830823c03c004208f0c20ae5140410940c20850052c10821400c51420af0d00420af003145145145),(717,0x20800820020920020820925010425030922c20050820926c10800c20824834010800c5145145145),(723,0x820ac08bb820820830c30820820002ae0820c208fbae0000820c20820aeb8a2aeb810420830c2b8db820830eeba28a20820830d31a20020838a28a2),(728,0x2082082bc20ae08208230a0410830ae00300002e080b8302e02e0410420c32cd040002043b80baebaebc0),(739,0x20800820820ae00208208a5010420c2b0300500fb85b8202eb8f5020822cb0420c000008b3cf08208b2cb),(747,0x820b408208200d0830c20830820004820800030823000020800c208208c32e0010420ae0030c22c00820030e30008e30820830c65428c00838e38e3),(762,0x2082b820af0ae08208208c0410990c2d03480100b8400202e480b820822c108d0c2352480e8008208d34d),(769,0x2d020ac0820ac0b40820825010425030ac4850050b43c400408208b0422c348fb11b11451),(771,0x20828c22a308208208200cc420c30c20830a342f0800c30808ce0a20c30420830e21860a20c3)]
def records4 : Array (ℕ × ℕ) := #[(774,0x208209008a40208208208032f0830c30820c20820c36066026020c2bc0410382bc30c104230c32f0823000c30410828e3410bef0828e30410c3041041),(777,0x8208240295008208208042f0830c30820c20820c360660260008308200030cc420030c108c2cb3000823000c30828e3145410c710828e30c3041),(784,0x20820900820820803020af4026430c20830c20820c360609862f0830849444021311030c108c8cc08230032f0c3082082492410082bf1bef0c3041),(786,0x820825022940820820c30c20828cb6420830c20820c38c664208308200c6590830c050201450e0820ef8a20825140820c30820c3514514),(789,0x208208d08208208d3020c30820c2350082bc30c20820c33460a30830841021310c310408d34e08e0ce38e04104134d0820c304134d186),(789,0x8208a082082080c420c30820c24100824030c20820c36de09408308216f1400853030c5142c4e0945034107a3082befc400820823cf0c3410186),(792,0x820b408208208cc420c30820c242f0820030c20820c31950a3083082bca2820000c38e30b134d082003bc08c0082bef1040000820000c38e38e3),(802,0x82082bc20820b1c420c30820c28cb082bc30c20820c38c60a3c420c2104c42084c4313110208000c099643c63082c7130c0820c338e0c3c71145),(804,0x820b408208200d0830c208308b0020800c30820830c65428c00830820004820800038e30823000020800c002308208230cb80041082b800c38e38e3),(819,0x82082082d020b40940c20830c24020904030c20820c36c251e8c20c2085bc2145003145084084c440c440408230c08230c4740c3410186),(820,0x208208208c0822822830820c309008294a0c30820830c60a328a08308248248a2834920840821040c494408228a04128a0410c3082082),(820,0x820820af0823425030820c30900824100c30820830d50947a3083082482000bc34106c2085bc208516f0c540508208230c08230cbef0c30c330c4100c330c),(822,0x8208234104208208108234c0420c30820c2084101084c430c208d401bc2bc304208d34e04e08e0c40410410820c304134d34d0410820c30410c3),(822,0x20820af0410820820420b1c41c420c30820c2084131042103082c4b0710afc4304208000c042643104082082082492145c400410820c338e0c3),(825,0x82082bc20b1c430babef0bac420820922c10af0c2082092171001083383),(826,0x8204208204208b0420823410022c30820c30821010842c40c208d05008b4030420853410851431030410410412cd0410820412cb041),(827,0x20820af08234b0c2350bc234508208234108b3430410413410812c1),(827,0x20820af0410820820420ae3010830c208308210a1000421310c3082092bc10afc430c208e00e0013823830c41010420d966f06f099043104104104),(830,0x20820af0829500c20820922c10af0c200c0f110200b04c002bc2082005410042643104104),(834,0x20820900820820803020af4026430c20830c2125110084c440c3082082492410082bf1bef0c308c8cc08230032f0c30820830d8182618bc20c1041),(836,0x208108208108230108209b06e0990c20830c20846c10840040c3082341082e8d0c20926c10924830c44823420830426d9643082104104),(837,0x82082b82090c4308208d042c4d0c2403482342082401323080b830820830426d90c2082084104),(838,0x20820af0410820820420b1c41c420c30820c20b100b0710afc4308209248b2c1082bf10c208000c0426590f1c420b1c4c30108338e0c3c71041041),(841,0x820420820420b4042082d010025030820c308241b0500904000c20824810b1c6f0c2085bc10851400c514208c30108c3110c3145145145),(844,0x208108208108230108208a04a08a0c20830c20900650a528a0c208d0420b128308248109228a0d248234208a28104a2810c3082292292),(844,0x820af0820820ae3020c30820c20842840021310c30aeb900af0c20820924af0020afc430c238e0823830c438e38e0820830dd7426420c4762186),(846,0x8208208ac4309b402082092042c430af30310500508e510380382082bc10823c3110bf1011451),(849,0x2082082d310c2bc20823410b10c2b8310a29208d08e084bce00d34d0820af042643104119659041052492),(850,0x2082b820b40c202e08208b0423430af0ae492092352082100000e8000208230104264312e02e08208d34d),(857,0x20810820810822c108208d06f08b0c20830c209005008b2d00c104b2c108204b2c108248108b2ef0d040308230108bbc30c33032cb410),(857,0x208208a08208208b2c20c30820c216f1421430c241008b2c30410c32cb0820410410ac38208b0c31502cb0820830e21822c20c5410186),(857,0x820820830902c10412c108104228b0ef0c236c0902c208210000108b0c54030c3),(859,0x8208208240308208308109b0c242e0f46c2b8c0800c10410830d03418e309b0436db6db),(860,0x820820020900c20820c20426c308c0ee6c22c03020020821504310426c36db6db),(863,0x208108208108230108209b06e0990c20830c20926c10924830c20830426d964308211b0421001030c4482082341082e8d0c2342104104),(864,0x82082b820900c20820c109b643090c4348208209004c8c202e0c20823410b134308d082084104),(865,0x820820824a30820820c20426c308db82d1b09b2ae0c20826c4492042b836db6db),(865,0x20820825030998c20820830810830990d40948826420820830420d4514514),(865,0x8209b08208208cb820c30820c209b6ca0ae0c3090bae0820030820c30820826db0c309b3420a20c3bae6db0820830db1828820e28a36db),(866,0x2082b8209b0c28c208208304264309b08dc4400209949b08208c0420ce0d2c42082)]
def records5 : Array (ℕ × ℕ) := #[(867,0x8208234107408208204208b2c10830c208308214d1410850c20841010842c304208d3813822c31030410410412cb0410820412cb041),(867,0x8208230104c08208204208a2812820c30820c20851410852830821043010840c10823cc04228308408208228a04104104104128a0c3),(867,0x8204208204208b042082341b022c30820c308214d0421450c208404210b10304208d05008b4030c40410410412cd0410820412cb041),(867,0x8204c08208108230108208a04a08a0c20830c208504214528308210c0421040c108230109228310208208204128c04104128a0410c3),(867,0x820826c10710820820420acb01b020c30820c208500504216c0c20912cb04208b2c30823c03c108f503145082b31c41083383145145145),(869,0x820420820420b4042082d010025030820c308216f04214500308230c04230c4430c20906c1402410003145082092042c71bc3145145145),(872,0x820826c10400820820420acb010830c2083082104001084b0308228a44108a2830c208e38004e08e503104082befb010823c3104104104),(875,0x8206f082081082bc10820af06f0940c20830c2084bc10840040c208d34108244d34308249b0424804831040820d0042befbc3104104104),(877,0x8209b0820820acb020c30820c216f14214308210400212c0c208a291b0208a2830c238e0823830c538438e0820830dd762094083144186),(878,0x820820af0ac08208a042283090b031100100b438314e00e0410420c3641bc009404314446cb11451),(881,0xb40820820b4b0208234108a0c2b03484282d0e08e10d08209904250316fbc4104041044104),(881,0x820ac082bec08208230108b0c2402b0540b0b40c53cc082094042503145144c71041045145),(881,0x2d020ac082b02d020822c108b0c20ac1520120b40843c03c208250104250314446cb11451),(883,0x82082082d020b40940c20830c2085bc2145003084084c440c208c30208c311d030c24020904030c51104100820830db0947a3083144186),(884,0x208108208108230108208a04a08a0c20830c209204248a28308228a04128a0430c20900650a528a0d2482082341082c4a0c234228a492),(884,0x8208a0822820820822810410c22e508a94208c0d2282082171c4108a0d2102082),(884,0x208208208c0822822830820c308248248a2830840821040c208a28104a2810430c24020a52830d21250820820830c60a328a083484082),(884,0x20820af041bc2082081082bef0420c30820c208a6c108000308216f1410850c108236fbc1bc2503145082082104bc00c34100410820823cf0c3),(887,0x8208230104c08208204208d301bc20c30820c20923010af0c208514108216f0c10823cc30108f0c508208230c04130c0410410820820c3),(887,0x8204c08208108230108208a04a08a0c20830c208c04248a0c208504214528304208430108410308408208204128c04104128a0410c3),(887,0x20820af041bc2082081082bef0420c30820c208a6db0420000c208a283410042bef0c308236fbc1bc25140efbc208d36fbc108208f3c3bef041041),(889,0x20810820810822c108208d06f08b0c20830c20920422cbbc308230108bbc30c209005008b2d00d040330104b2c108204b2c10c32d02d0),(889,0x8206f082081082bc10820af06f0940c20830c20926c10920120c20834010afbef0c2084bc10840040c410208d34108244d343104104104),(891,0x82bc2082092bc208208a0d0042bc308dbef0af14208229b0400c208211249b042503145145),(892,0x20820af04100208208108236f0400830c208308214014b042085003082bc3401082bc00c208f00f0010823c3145082b94501042503145145145),(899,0x20800820020922c20020824834010800c24800850820926c10800c20824940410940c5145145145),(905,0x820af0820820afbc20c30820c208a6db080003085bc5bc20850c208a2830d04020afbc30c236f0825030ef16fbef0820830c68af094083885104),(907,0x2082bc2082bc2bc20823010af0c2402bd014b2c33020c03c014c30c0820af042503514505145041050410),(909,0xaf082bc209b08b0af0820834010af0c2bc23451001025123c03c2082bc1083383485befbd1451),(911,0x820820af0823425030820c3082482000bc308216f082145bc308208230c08230cbef0c30900824100c34101500c33103100820830d50947a30836c50c330c),(913,0x8106f),(913,0x8106f),(913,0xe503),(913,0x81072),(913,0xf303),(913,0x81072),(913,0x2503),(913,0x33cc),(913,0x3394),(913,0x3094)]
def records6 : Array (ℕ × ℕ) := #[(913,0x20830830c30803032e20830428c54108820e28a2),(914,0x20830830c308ab83c4d083042bc438e0a20e28a2),(914,0x20c30830c30af0ae0a208008208c2810838a38a2),(915,0x820820c33800c1b0d08104108ab83bce08306fbef),(916,0x20820830c0c420cb0810ae303c4e0ca28a),(917,0x820820c3c4e90336c08f0c108ab83bc438e6c2503041041),(917,0x820820c308ab83bce08304e00306c34204106fbef),(918,0x820820c3c422ae0c438e6c250304e903bcdb023c3041041),(918,0x20822ae0f13420c2bc438e0a20c30620830c38a2),(918,0x3380bb18af),(919,0x820822820820c30820b13820830c20820c38860820c241008341040208f3c20cf3c10821451450850c5145145145145),(919,0x820820c20c30b1402003094c420d4502145145145145),(920,0x820830830c28c2094085500081083514),(921,0x3500),(922,0x820830830cb0ae000b820af0ae08c0c0b80),(926,0xcf082bb2),(926,0x20830803030a315042208388b8820c10830c38a2),(927,0x20820830c2b8c0f13830310832c204a28a),(928,0x341b),(928,0x3c6e00e8af),(929,0x820830830c2bc2b823032c2b8002e0ae000),(933,0xc208fbb2),(933,0x20820c20c3bc2baf08252c2c2b82b85145),(933,0x3082145),(933,0x20c2bc2b8288208208c2810838830230830c38a2),(934,0x820820c20c308b40d0413420412c6),(934,0x820820c20c36ce42cbce28a0c5145),(934,0x341b),(934,0x820820c20c3bce28a0db390b05145),(934,0x20820c20c3bec2c2b82b82baf082505145),(934,0x3082145),(934,0x820822810420820810c3082082410050083082c4e06208304208f3c10833c2082145045083145145),(934,0x10cf08f),(934,0x433c2503),(934,0x10f108e503),(934,0x433ca),(934,0x10f1bc3),(934,0x20830830c308ab83c4d083042bc438e0a20e28af),(934,0x20830830c30803032ef0830428c5410bc20e28af),(935,0x20c30830c30af0ae0ae08008208c2810838e28af)]
def records7 : Array (ℕ × ℕ) := #[(936,0x820830c20c30ef3ac40228228340e191),(936,0x82bc00f13420420c30c22800efbc3befbef),(938,0x820310cbbc20420c30c200c0f1bc3befbef),(940,0xc00028af),(942,0x8204208204208c0420c20830824018c2bc308238138238304209204248308e082101102103104104),(942,0x10ef090643),(942,0x4348c),(942,0x10efb83),(942,0x81bc1),(942,0x8208e003b0d0810830c104108ab83bce083befbc1),(943,0x20822c20310830830c10ae303c4e0ca28a),(944,0x82082090b03043bd40af142b1010008a283444),(945,0x82082043c42bec0c2bc314200314c302c433c5),(946,0x82082043bc2bcc0c2bc31422b10c51000b10c4),(947,0x16fbc008c),(948,0x820824010420820810823120420c30820c208c30130230308234a042343302090341bc2bc3041),(948,0x820820823022800c208240449204200330236f081),(950,0x3010d2),(950,0x3010d2),(950,0x2002),(952,0x2082082bc00c10ef082b830af083492482104104104104),(953,0x3010d2),(953,0x2082082b800c10cd0020afb800ae08000008a0c0),(960,0x340082),(961,0x2f043c43),(961,0x82bc00c22800efbc3c4d081befbc20c30ef),(963,0x20820810c00822830af003bc23030000020310ef),(969,0x300080090),(971,0x208234208a00342f0cc30cbc20030830c1),(973,0x82082043bc2b830af0d20b4c432842840b10c4),(973,0xbc2041),(973,0x8208e003b0d08108ab83bce083befbc20c3041041),(974,0x23810f1503),(974,0x208308ab83c4d083042bc438e0a20e20830c38af),(974,0x8008eb8a),(975,0x820823c208a3810410820820810c30c208208a28a04a0830822cb2c10832820ae2ce06f083041),(975,0x82082082282b8c0c2082b853cf3810832822ef081),(975,0x2810cf),(975,0x2810cf),(975,0x20820820310c10f10820030b10833cf3c2145145145145)]
def records8 : Array (ℕ × ℕ) := #[(977,0xb82002),(978,0x2810cf),(978,0x208208202e0c10cb002080bae0af0ae00008c0c0),(984,0x2c0082),(985,0x820310c200c0f1bc32ef081befbc20c30ef),(987,0x2e043bc3),(987,0x20822c20ae303c4e0ca28a0310830830c1),(988,0x82082043c420030b10cf0afb033053050af0c5),(989,0x20820810c0082303080c43bc2283000002bc00ef),(995,0x2ae08008e),(996,0x208208208f2820c23010410830d414f3c3042043),(996,0x23c10cf),(996,0x10e3090502),(996,0x820804032ef08108030342f083befbc20c3041041),(998,0xb82041),(998,0x23c10cf),(998,0x10c008000c),(1001,0x20830803032ef0830428c5410bc20e20830c38af),(1002,0x24010ef643),(1002,0x8009000c),(1004,0x820804032ef0810830c104108030342f083befbc1),(1006,0x2082342bc20030830c108a00342f0cc30c),(1008,0x30400028ef),(1010,0x820820b438304366f0ac102bce14008a283445),(1011,0x82082043bc22b10c2c43102bcc0c41400af0c5),(1012,0x82082043bc2d310c2c43102b8310a282bc3484),(1012,0x81b81),(1012,0x820820af0ae0820820b1b81bc00830820c3),(1013,0x810cf503),(1013,0x208208202e0c10cb0020af0ae00008c0c202eb80),(1019,0x208b),(1020,0x10c000200c),(1023,0x2082082b800c10cd0020ae08000008a0c2bee000),(1030,0x208d),(1031,0x20c30af0ae0ae08008208c2810838e20830c38af),(1032,0xa2bc3),(1034,0x2bcc16f),(1035,0xa3bc00c1),(1037,0x820820b438304366f0af38500228a0d10ac105),(1038,0x82082090b03043bd40ac40400228a0d10af144)]
def records9 : Array (ℕ × ℕ) := #[(1039,0x820830ef3ac40228228340e0830c3191),(1039,0x208208308d3810410410810903423c3085145145145145),(1039,0x1083),(1039,0x8208234b0410812c10832c20c3386),(1039,0x2081bc20820420af0420c20830821410850c208e04e08e0c10824810920c5142084042103104104),(1039,0x82bc2082b02bee0ae082baf08f08f3cf),(1039,0x248f08208f),(1039,0x2bc20820ae0c2bce502382082bc10823c3042104),(1039,0x23cf),(1039,0x8208e90336c08f0c20c3c4108ab83bc438e6c2503041041),(1039,0x820820afb030af0c10f114200314c302c4314f),(1040,0x820820af3030af0c10ef1422b10c51000b10c4),(1041,0x820820af090b03043bd4142b1010008a283111),(1042,0x16fbc008c),(1043,0x8208e90336c08f0c22ae0ef10e39b0940c10410830f1041),(1043,0x20820823940af08a2831041026d0390002b05145),(1044,0x820820af0ac08a28310242c0c4400043bd4151),(1045,0x82094bec28a0c41040834100830ce),(1045,0x82bc2082bee08b2c20810aebc23cf2cf0942c5),(1045,0x4f0822c5),(1045,0x802cfbef310),(1046,0x820820afb030af0c200314c302c431410f114f),(1047,0xafbcc00b3d0),(1048,0x82bc2082b02bee0aebc2082b823cf3cf),(1048,0x208248f08f),(1048,0x23cf),(1048,0x82bc2082bee08b2c20aebc23cf2cf0942c2045),(1048,0x3c22c2045),(1048,0xbef08c005),(1049,0xbef3c23022c3),(1049,0x820823420c20c338b0410812c12c6),(1049,0x82094bc20d00830ceb1028a0c4104),(1049,0xefbcf08c08b),(1049,0x8208208d08e08b0900410420c304d04204b043),(1049,0x820820af3030af0c22b10c51000b10c10ef144),(1050,0x20820823940af09b40e4000ac08a283104105145),(1051,0x208208b0410020820810c30820824920420c208e3813820c10823c00420ce0c2084101083104104),(1053,0x8008f502),(1054,0x820820990821140010830835020c3894),(1055,0x208008208308038208e082094641083042104104104)]
def records10 : Array (ℕ × ℕ) := #[(1057,0x80002),(1059,0x19003),(1060,0x8204208204208c0420c20830824810920c208e04e08e0c10824018c2bc308e082101102103104104),(1060,0x10ef090643),(1060,0x820820ae0c23820a34820826c10990c1084104104104),(1060,0x4348c),(1060,0x8208208e0841041041022ef08e1023034840820850000420d2384),(1062,0x820820823020c208308248248308e08e0c10821040841040c4104104090082bc30d23841020820c31828c20d238e104),(1062,0x20820823821041041040834840902c40410410810432c4),(1062,0x2082082b830af083084104104102bc00c4043bc2492484),(1063,0x202e08066f),(1065,0x82082b83082bc26430841041041020ef6440830ce644),(1065,0x2043),(1065,0x2081bc20820420af0420c20830824810920c208e04e08e0c10821410850c5142084042103104104),(1065,0x82bc2082bee0ac0ae082baf08f08f3cf),(1065,0x248f08208f),(1065,0x2bc20820ae0c2bce082082099042503042104104104),(1065,0x2b82b8f3cf),(1065,0x81bc1),(1065,0xe503),(1065,0x20822ae0c2bc438e0a20f13420c38810830c38a2),(1065,0x820822ae0ef3820c20c304e00306c34206fbef041),(1066,0x820822ae0c438e6c25030830f104e903bcdb023c3041041),(1066,0xe0c0bb18af),(1067,0x820824010420820810823120420c30820c208d28108d0c208c301302303302090341bc2bc3041),(1067,0x820820822800c230208240449204200330236f081),(1069,0x3010d2),(1069,0x3010d2),(1069,0x2f043c43),(1069,0x8208a003bef0ef003c4d081befbc20c30ef),(1071,0x3010d2),(1071,0x20820822830af003043002bc23030000020310ef),(1077,0x300080090),(1079,0x208208a00342f0cd08c30cbc20030830c1),(1081,0x820820ae0c2bc3043bd20b4c432842840b10c4),(1081,0x2002),(1083,0x2082082b830af003043bc20af083492482104104104104),(1084,0x2082082bee0ae0030433400800ae08000008a0c0),(1091,0x340082),(1092,0x23810f1503)]
def records11 : Array (ℕ × ℕ) := #[(1092,0x20822ae0c2bc438e0a20c38b13420c10830c38af),(1092,0xbc2041),(1092,0x820822ae0ef3820ce003b0d081befbc20c3041041),(1093,0x8e080b8a),(1094,0x820822ae0c438e6c25033a40ef36c08f0c10410830f1041),(1094,0x8208238208b3810410020820820430c308208228a2812820c208b2cb0420ca0823cab81083041),(1095,0x8208008208d00a08208208f10e3ae0420ca08a0c1),(1097,0x208208236e082bee0820ee08b002b8000202e0ae),(1101,0xb00208f),(1102,0x82bc2082bee0aebc2082b02b823cf3cf),(1102,0x2b8f0ae3cf),(1102,0x2082082bee0ae082283002b800c0000043340080),(1109,0x82342bee082b8208a0c0b800830000830ee),(1113,0x9208f085045),(1113,0x248200d),(1114,0x208248f08f),(1114,0x8200d),(1115,0x4820aec83),(1115,0x920850423c5),(1115,0x20820820a20a30810410830c5500114001042043),(1117,0x94043000),(1119,0x99043000),(1121,0x23810f1503),(1121,0x92080502),(1122,0x8208228308dc420820840000420c24104023cf085145145145145),(1124,0x200000252f),(1127,0x8f080502),(1128,0x208208236e082bee0822c00ae000080b82083bae),(1132,0x8f08b),(1133,0x248008d),(1134,0x24010ef643),(1134,0x20820822830af00308c0c0000080c43043002bef),(1140,0x240200c),(1142,0x8eb8200a),(1143,0x2f0108ef003),(1145,0x8208208e08bbc238230348208214000108348e084104104104104),(1147,0xb8200266f),(1149,0xebb18af003),(1150,0x20822ae0c28c438e0a20c38a33420c10830c38a3),(1150,0x208208a00342f0c20c3bc200334230c301)]
def records12 : Array (ℕ × ℕ) := #[(1152,0x2f0c00108ef),(1154,0x820820830830e2099082114001083514),(1155,0x3640),(1156,0x820820823020c208308248248308e08e0c1090082bc30d23820820c31828c20d238e0821040841040c4104104104104),(1156,0x82082b830820ef0830ce0af0990d9642104104104104),(1156,0xe0d4),(1156,0x82342bee0820c00830ee0ae08008a0c0b80),(1160,0x483082bb2),(1160,0x820820ae0c2bc30b4c432842840b10c10ef484),(1160,0x20820823820d20902c10410420410cb084104104104104),(1160,0x1083),(1160,0x820822810420820810c30820824100500830823cf0420c1082c4e0620833c2082145045083145145),(1160,0x10f108e503),(1160,0x433c2503),(1160,0x820820900820030a23c20825190420c1085145145145),(1161,0x433ca),(1161,0x10c0003),(1163,0x2081082081082c41c420c20830824014024030823c108f0c10821010840c4102085042143145105),(1163,0x820ae082c6e0b10b1082bc2b92092492),(1163,0x23d2082092),(1163,0x2082c420900b10800c2082094042503042145144104),(1164,0x940b1084),(1164,0x2c42012492),(1165,0x820822820820c30820904020c208f3c20c10821451450850c51451450b13820830d03c51420820c38860820d040f145),(1165,0x20820900821451451450833c508d38504104104204d0c5),(1165,0x820824020851451451422833c508dc424050820840000420d03c5),(1167,0x82080082402002c420c2145145145082005083410405),(1170,0x20820820030b10830851451451420310c5043c423cf3c5),(1172,0x820820800c25310830851451451420f15050830d0505),(1173,0x2043),(1173,0x200008052f),(1176,0x20810820810823410020c20830824014024030823c108f0c10824810800c33c2085042143145145),(1178,0x80092502),(1179,0x8f082084),(1179,0x24010e3502),(1179,0x908c2084),(1179,0x820820940855000810830835020c38d4),(1180,0x20820020900800830900820b1042503042145145145),(1182,0xb1094084),(1182,0x80b82)]
def records13 : Array (ℕ × ℕ) := #[(1183,0x14003),(1184,0x81c81),(1184,0xf303),(1184,0x8f084042484),(1184,0x8208f084),(1184,0x8208240104208208108240d0400830c20830822cc04c08c0c208d34108d0cc082312042c83041),(1185,0x8208200208b3020020820854104810800cc08c0c1),(1188,0x20820822c008202e0820ee08db8202e002bee0ae),(1192,0xd002092),(1193,0x820af082402bc2bc20900af0af2c52c5082bc5),(1193,0xd2c2085),(1193,0x43003),(1195,0x820ae082c6e0af0ae082c42c42492492),(1195,0x2c52080492),(1196,0x820800824020020800830b1083410402145145145145),(1199,0x208208202e0af08230300202e0c0b800432c00ae),(1205,0xc0020010c0),(1208,0x8243108240200230330c30b0020030830c0),(1212,0xc002112),(1213,0x822c202e082bc208c0c0b80083bae0830c0),(1217,0x42f30008b3ef),(1218,0x82082b8208c0823c20820853cf081042503),(1218,0x8f08f),(1218,0x8f08f),(1218,0x8f080502),(1219,0xc82041),(1219,0x8f092084044),(1219,0x23c200b),(1220,0x810cf503),(1220,0x20823d2092),(1220,0x8200b),(1221,0x3c208c303),(1221,0x3c20aec83),(1221,0x820823c208a3810410820820810c30c208208b2cb0420c208a28a04a0832820ae2ce06f083041),(1221,0x82082082b8c0c2282082b853cf3810832822ef081),(1221,0x2810cf),(1221,0x2810cf),(1221,0x82080303c6f0c0c432ef081befbc20c30ef),(1223,0x2e043bc3),(1223,0x2810cf)]
def records14 : Array (ℕ × ℕ) := #[(1223,0x20820ae303c4e0cb08a28a0310830830c1),(1224,0x820820800c2c43043c4f0afb033053050af0c5),(1225,0x2082082303080c43043002bc2283000002bc00ef),(1231,0x2ae08008e),(1232,0x2082082003080c43043c420b10833cf3c2145145145145),(1234,0xb82002),(1235,0x208208202e080b830432c00ae0af0ae00008c0c0),(1241,0x2c0082),(1242,0x208208208308f2823010410830d414f3c3042043),(1242,0x23c10cf),(1242,0x23c10cf),(1242,0x208200c0c28c5410bc20c388bbc20c10830c38af),(1243,0x24010ef643),(1243,0x8208200c0d0bc20c04032ef081befbc20c3041041),(1245,0xb82041),(1245,0x9008000c),(1247,0x10e3090502),(1247,0x20010c000c),(1250,0x208200c0c28c5410bc20cbbc20c38810830c38a3),(1251,0x8208200c0d0bc20c20c304040304bbc206fbef041),(1253,0x8208200c0e31504026430830ef065403c522c2bc3041041),(1254,0xf0cc),(1254,0x8243108b0020030830c009008008c0cc30c),(1258,0x3c308230c),(1258,0x100c002f8ef),(1260,0x8208200c0e31504026439500f148b0af0c10410830ef041),(1261,0x2401044),(1261,0x8c2090084),(1261,0x8448c),(1262,0x81b81),(1262,0x2401044),(1262,0x106c3),(1262,0x208200c0c28c54108820c388b8820c10830c38a2),(1263,0x20820ae303c4e0c20c30310832c228a281),(1264,0x310ee00e8af),(1265,0x820822820820c30820904020c208f3c20c10b13820830d03c20820c38860820d040f0821451450850c5145145145145),(1265,0x820820800c20f10830d0094c420d4502145145145145),(1266,0x820820830830e3094085500081083514),(1267,0x3500),(1268,0x822c202e0820ee0830c00af0ae08c0c0b80)]
def records15 : Array (ℕ × ℕ) := #[(1272,0x3c3082bb2),(1272,0x100db),(1272,0x20820900820cf08d381041041081343085145145145145),(1272,0x1083),(1272,0x820820800c2c430afb033053050af0c10f13c5),(1273,0x22cfbef40c),(1274,0x20820828c20828810410830c5500114001042043),(1276,0x99043000),(1278,0x94043000),(1280,0x8f080502),(1281,0x24010ef643),(1281,0x820822ef0823030820850000420c249208e38e084104104104104),(1283,0x202e00266f),(1285,0x23810f1503),(1285,0x2082082303080c4308a0c00000af003043002bef),(1291,0xb8238200a),(1292,0x9000200c),(1294,0x31b8e8af003),(1295,0x92080502),(1296,0x20820822c008202e08236e080b800afb82083bae),(1300,0x9208d),(1301,0x23c008b),(1302,0x8208240208a0cf08dc4240208210000108340f085145145145145),(1304,0x200252f),(1307,0x1002f8ef003),(1309,0x820af082402bc2bc20af0af2c52c5082bc2405),(1309,0xb082345),(1309,0x2081082081082c41c420c20830821010840c208f0423c30420900500900c4102085042143105145),(1309,0x820ae082c42c6e0b1082bc2b92092492),(1309,0x23d2082092),(1309,0x8208f084),(1309,0x823c4042112),(1309,0xaf082b820af08d0af0821022c2b84140082b85),(1310,0x820ae082c42bc2b820b1b82c42492492),(1310,0x820ae0820af0ae099102c6e4822c234135248d),(1310,0x2c420ac082c420ac094102b1214008b08b151),(1311,0x20b108d082bc2b82644104083c710830ee),(1311,0x821023c4052),(1311,0x20823d2092),(1311,0x8210148d)]
def records16 : Array (ℕ × ℕ) := #[(1311,0x2084103),(1311,0x820ae08264230e0c208109b0d2482644104),(1311,0x820ae0820b1b822c23410af0ae49235209910d),(1311,0x5208210d),(1311,0x2bc20ac082502bc22c22c514509b3d2002b04104),(1312,0x2c420ac082c42b022c22c5082b05480094111),(1313,0x20b108d0820f1c420c3b82bc2b82644104),(1313,0x3082104),(1313,0x820ae08264230e0c26c3492099082044104),(1313,0x2bc20ac082502bc26cf4800ac08b08b145144104),(1314,0xaf082b820af08d0af0822c2b84140082b82105),(1315,0x208208b0410020820810c30820824920420c208f00108304208e3813820ce0c2084101083104104),(1317,0x8008f502),(1318,0x820826420821140010830835020c3894),(1319,0x2081082081082341b820c20830824810ae0c208f0423c30420900500900c33c2085042143145145),(1319,0x8f08f),(1319,0x208228208a08228a0c294a48208a492),(1319,0x8208a08208a04204a0c20e50820c3282),(1319,0x81c81),(1319,0x2503),(1319,0x8208240104208208108240d0400830c208308234d0423430822cc04c08c0cc082312042c83041),(1320,0x820820020822cc0800820854104810800cc08c0c1),(1323,0x43003),(1325,0x820ae082bc2b820b1b82c42c42492492),(1325,0x2c52080492),(1326,0x820800820800830900800b1083410402145145145145),(1329,0x2082082bc208c0c202e00202e0c0b800432c00ae),(1335,0xc0020010c0),(1338,0x8209008008c0d0c4230c30b0020030830c0),(1342,0xc002484),(1343,0x20820820c22c008202e0ae08db8202e002bee0ae),(1347,0xd002092),(1348,0x820af0820900af0af0900af0af2c52c5082bc5),(1348,0xd2c2085),(1348,0x820af0823032c202e0ae000083bae0830c0),(1352,0x42f3000af2cf),(1353,0x82082b8208f08c0820820853cf081042503),(1353,0x8f08f),(1353,0x810cf503),(1353,0x20823d2092)]
def records17 : Array (ℕ × ℕ) := #[(1353,0xc82041),(1353,0x823d2084101),(1353,0x8f08f),(1353,0x8200b),(1354,0x823cc303),(1354,0x8f080502),(1355,0x208f00b),(1356,0x823eec83),(1356,0x820ae082bc2b820b10b1b82c42492492),(1356,0x820ae082bc2b82642102c6e4822c234d492341),(1356,0x2c420ac0820ac0940b1102b1214008b08b445),(1357,0xaf082b82082bc2342bc21022c2b84140082b85),(1358,0x2082bc2b8267108d084104083c710830ee),(1358,0x20823d2092),(1358,0x821023d2101),(1358,0x82112341),(1358,0x2084103),(1358,0x8208238208b3810410020820820430c30820822cb2c108308228a2812820ca0823cab81083041),(1359,0x8208008208234028208208f10e3ae0420ca08a0c1),(1361,0x82bc2082baf0820afb82b02b823cf3cf),(1361,0x2b8f0ae3cf),(1361,0x2082082b8208a0c2bee002b800c0000043340080),(1368,0x20820820c236e082bee0ae08b002b8000202e0ae),(1372,0xb00208f),(1373,0x820ae082283342bee0ae0000830000830ee),(1377,0x208248f08f),(1377,0x8248f085141),(1377,0x8200d),(1378,0x209200d),(1379,0x824aec83),(1379,0x82bc2082baf0820ac0afb82b823cf3cf),(1379,0x82bc2082baf082502142bee3c22cb08b3cf2c1),(1379,0x2bc20ac082bc20940ac142bcf10008b08b444),(1380,0x820af0820af0af082bc50900af14b2c2bc2405),(1380,0xaf082b820822c2b820ae142bc23451000af084),(1381,0x2082baf08252c2c2085145083bae0830ef),(1381,0x20af0820af0af082bc51450834102d00830e3),(1381,0x208248f08f),(1381,0x8214248f141),(1381,0x8214f2c1)]
def records18 : Array (ℕ × ℕ) := #[(1381,0x20852cd),(1381,0x2085143),(1381,0x2082145403),(1381,0x20af08288208208c2810830ee8830230830c38a2),(1382,0x820af082303083b820c32c2b8002e0ae000),(1386,0x8308fbb2),(1386,0x2082baf0825020c20c3bec2c2b8214516e),(1386,0x20c2145),(1386,0x820820820af0ae0820b1b81bc00830c3082),(1387,0x810cf503),(1387,0x20af082b8208208c2810830c08c3ba20830c38af),(1388,0x80022bc3),(1390,0x2082082b8208a0c2b800c0000043340082bee000),(1397,0x8008d),(1398,0x80bccbc5),(1399,0x2082082bc208c0c202e0c0b800432c008202e02e),(1405,0x4300200c),(1408,0x8008b),(1409,0x2023bc00c1),(1411,0x82bc2082baf0820ac0afb82b823cf3cf),(1411,0x23cf),(1411,0x208248f08f),(1411,0xaf32f005),(1412,0x82bc2082baf082502bee3c22cb08b3cf2c2141),(1412,0x8f2c2141),(1412,0xbcc0af00b40f),(1413,0xaf32f3c22c3),(1413,0x20a3082b8208208c2810830c08c3ba20830c38a3),(1414,0x8209008008c0c20c300b00200343108c30c),(1418,0x8308f30c),(1418,0x20c0023bc1),(1420,0x83c650234b108d),(1421,0x820826420c20c30a2082114001083514),(1422,0x8208a0820c20c3282942281081283082),(1422,0x20d4),(1422,0x2082bc2b826420c20c3bb108dc42104131),(1422,0x20c2104),(1422,0x820ae0822830830020c334202ebee0ae000),(1426,0x83092bb2),(1426,0x20af0820834100830e30af0af2c20af145150)]
def records19 : Array (ℕ × ℕ) := #[(1426,0x20c2085150),(1426,0x83bccbcf08b),(1426,0x820ae082bc2b820b10b1b82c42492492),(1426,0x20823d2092),(1426,0x2480304),(1427,0xb1952c423408c3),(1428,0x208228208a08294a48208228a0d2292),(1428,0x820ae082bc2b82642c6e4822c234d492342101),(1428,0x92342101),(1428,0x2c420ac0820ac0940ac4850022c22d10b1105),(1429,0x2bc20ac082bc20940af3c40022c22d10ac144),(1430,0x20830830c308ab838cd0830428c438e0a20e28a3),(1430,0x20830830c30803032ef0830428c5410bc20e28a3),(1431,0x20c30830c30a30ae0ae08008208c2810838e28a3),(1432,0x820820c30100c12ef08104108030342f08306fbef),(1434,0x20820830ef0800cd08108a00342f0cc30c),(1436,0x30400028ef),(1438,0x820820c308030342f08304040304bbc204106fbef),(1440,0x820820c3bc200c0e3150402643065403c522c2bc3041041),(1441,0x33cc),(1441,0x820830c02c00800d0c4209008008c0cc30c),(1445,0xcf08230c),(1445,0x208200c0cbbc20c28c5410bc20c30620830c38a3),(1446,0x340002f8ef),(1448,0x820820c3be540348b0af0c1080303c63150402643041041),(1449,0xd2c40c4296308d),(1450,0x3394),(1450,0x33cc),(1450,0x3094),(1450,0x820820c20c308d38b0410812c12c6),(1450,0x820820c20c35103afb1028a0c4104),(1450,0xefbcf08c08b),(1450,0x820830830c20a2099082114001083514),(1451,0x3640),(1452,0x820820823020c2083090082bc30c20820c31828c20c20920920d248238238338e3810821040841040c4104104104104),(1452,0x820820c20c30ae0c2bce0af0990d9642104104104104),(1452,0x208308ab830a310e3828838a33420c10830c38a3),(1452,0x20820830c22800d0bc3bc200334204c30c),(1454,0x3394),(1454,0x820830830cd080bafb820ae08008a0c0b80)]
def records20 : Array (ℕ × ℕ) := #[(1458,0xd2082bb2),(1458,0x3bc00108ef),(1460,0x20820c20c3bb108dc42c42bc2b82644104),(1460,0x3082104),(1460,0x820830830c20990a2082114001083514),(1461,0x820830830ca08a082942281081283082),(1461,0x820830c009008008c0cb00200343108c30c),(1465,0xc208f30c),(1465,0x3094),(1465,0x20820c20c3b82bc2b8267108dc42c44104),(1465,0x3082104),(1465,0x820830830c2b8200228334202ebee0ae000),(1469,0xc2092bb2),(1469,0x20830830e30af0900900af0af2c20af405145),(1469,0x3082090145),(1469,0x20c28c20ae08008208c2810838c3ba20830c38a3),(1470,0x30800018ef),(1472,0xc2c650234b108d),(1473,0xc2bccbcf08b),(1473,0x820820c20c3b1028a0d440ebc4104),(1473,0x20830830e30af0af2c20af402bc2402405145),(1473,0x3090082145),(1473,0x2081082081082c41c420c20830821010840c20900500900c10823c108f0c4102085042143105145),(1473,0x820ae082c42c6e0b1082bc2b92092492),(1473,0x23d2082092),(1473,0x2082bc20b10c26d0bc23c2082092042bc3042145),(1473,0x820822cd0413420410832c20c3406),(1473,0x8208208ac430b10c10ef102bcc0c41400af0c5),(1474,0x820820b4c430b10c10ef102b8310a282bc3112),(1474,0x820820ac0b438304366f102bce14008a283151),(1475,0xa3090084),(1475,0x820a540348b0af0c200c0f18c54100990c10410830ef041),(1476,0x2401101),(1476,0x200448c),(1477,0x820a540348b0af0c20c3bc1080303c63150402643041041),(1478,0xd2c71002942363),(1479,0x820ae0820826c309910410265208c383052),(1479,0x4090041),(1479,0x820ae082c6e08b08d0810af0ae492352099344),(1479,0x52082344)]
def records21 : Array (ℕ × ℕ) := #[(1479,0x820ae08208264230e0c109b0d2482644104),(1479,0x20820826d00ac08a28314514239440e002bc4104),(1480,0x820820ac0af08a283142d0e0c538004366f111),(1481,0x8209bb2f28a0c514508338e0830d0),(1481,0x820822c20c20c340d0413420412c6),(1481,0x8209bb020ce0830d0bce28a0c5145),(1481,0x8208208b09008d08e0410420c304d04204b043),(1481,0x8208208ac430b10c2bcc0c41400af0c10ef105),(1482,0x20820826d00ac08e5103800af08a283145144104),(1483,0x820820b4c430b10c2b8310a282bc31010ef112),(1483,0x20822820a528208229208228a0d2292),(1483,0x820ae082c42c6e0af0ae082c42492492),(1483,0x20823d2092),(1483,0x248010c),(1484,0x820ae082c6e08b08d0af0ae492352099342044),(1484,0x482342044),(1484,0x4b1c429423408c3),(1485,0x20820830902c10410420410920c238b084104104104104),(1485,0x1083),(1485,0x8106e),(1485,0x8106e),(1485,0x2401101),(1485,0x106c3),(1485,0x820ae0826c309908210410265208c383481),(1485,0x4090041),(1485,0x341b),(1485,0x820ae0826c309909948230e0d2082104101),(1485,0x2c420ac082b022c22c2c45082b05480094444),(1486,0x2bc20ac0822c22c2502bc514509b3d2002b04104),(1487,0x820820af08a2830ac142d0e0c538004366f444),(1488,0x208208228a0c26d00ac14514239440e002bc4104),(1489,0x820af28a0dbb0514508338e0830d0),(1489,0x820820ac08a2830af10242c0c4400043bd4445),(1490,0x208208228a0c23940af1041026d0390002b05145),(1491,0x820ac28a0d4bc41040834100830ce),(1491,0x2bc20ac082bc22c22c2b040af0843c0094445),(1492,0x2bc20ac0822c22c26c2b0410409448f002bc5145),(1493,0x820af28a0c20ce0830db390b05145),(1493,0x820afb022822830d040338e0830c3191),(1493,0x820820ac08a283090b031100010ef5110af105)]
def records22 : Array (ℕ × ℕ) := #[(1494,0x820820af08a2830b438314e0010d9bd10ac144),(1495,0x2c420ac082b022c22c20ac1520025110b1144),(1496,0x2bc20ac082bc22c22c2bc210f0025110ac105),(1497,0x820ac28a0c20d00830d440ebc4104),(1497,0x2081bc20820420af0420c20830824810920c208504214304208e04e08e0c5142084042103104104),(1497,0x82bc2082b02bee0ae082baf08f08f3cf),(1497,0x248f08208f),(1497,0x82bc20820afb822cb0810aebc23cf2cf09414b),(1497,0x4f08214b),(1497,0x2bc20ac0826c2b022c22c410409448f002bc5145),(1498,0x2bc20ac082b02bc22c22c40af0843c0094151),(1499,0x8248504214f),(1499,0x820af082bc2bc20af0850900af14b2c2bc2150),(1499,0xaf082b8208b0ae082b82142bc23451000af084),(1500,0x82bc2082b02baf0820afb82b823cf3cf),(1500,0x82bc20820aebc2094142bee3c22cb0812cf3cb),(1500,0x2bc20ac082b02bc2094142bcf10008b08b111),(1501,0x20ac2c2082baf082505145083bae0830ef),(1501,0x20af0af082bc2bc20851450832d04100830e3),(1501,0x8214248504f),(1501,0x20852cd),(1501,0x208248f08f),(1501,0x821413cb),(1501,0x2085143),(1501,0x2082145403),(1501,0x20ac2c20820eeb820c3bc2baf082505145),(1501,0x3082145),(1501,0x820af082bc2bc20af0900af14b2c2bc2142150),(1501,0x22c214d),(1501,0xaf082b8208b0ae082b82bc23451000af082144),(1502,0x2bc20ac0826c2b025123c00af08b08b104105145),(1503,0x20af0af082bc20cb4020c38c2bc2402145150),(1503,0x2403082145),(1503,0xcc),(1503,0xcc),(1503,0x3b8a),(1503,0x32ae),(1503,0x3b8a),(1503,0x3b8a),(1503,0xd0)]
def records23 : Array (ℕ × ℕ) := #[(1503,0x20820c20c3402082145),(1503,0xc5),(1503,0x820830830cc082),(1503,0xd0),(1503,0xd0),(1503,0x303),(1503,0xcc),(1503,0x32ae),(1503,0x3b8a),(1503,0x820830830c2302),(1503,0xd0),(1503,0xd0),(1503,0x303),(1503,0xcc),(1503,0xcc),(1503,0xcc),(1503,0xc0),(1504,0xef02f),(1505,0xc0),(1506,0xef02f),(1507,0xc0),(1508,0xc0),(1509,0x3b8a),(1509,0x32ae),(1509,0x82082043bc2bc228a0d1102b05),(1509,0x2fbcc),(1509,0x82082043bc2bc2b0228a0d1105),(1509,0x2fbcc),(1509,0x92),(1509,0x4af),(1509,0x12),(1509,0x92),(1509,0x2e),(1509,0x3af),(1509,0x820820430020afb820c202e),(1511,0x2),(1511,0x80),(1512,0x4af),(1512,0x3),(1513,0x3)]
def records24 : Array (ℕ × ℕ) := #[(1514,0x2),(1514,0xc0),(1515,0xbc302f),(1516,0x0),(1517,0x820820430020afb8202e083),(1519,0x2),(1519,0x2),(1519,0x2e),(1519,0x2fbc3),(1520,0xc003),(1521,0x80),(1522,0xc0c0),(1523,0xc0),(1524,0x3b8a),(1524,0x2e283),(1524,0xf010),(1525,0x0),(1526,0xf),(1526,0x42e),(1526,0x82082043002080b820c2bee),(1528,0x2),(1528,0x3d0),(1529,0x3),(1530,0x2f32f),(1530,0x2),(1530,0xc0),(1531,0xbc302f),(1532,0xa0ee),(1532,0x2fbcc),(1532,0x2e),(1532,0x82082043002080b82bee083),(1534,0x2),(1534,0x2),(1534,0x0),(1535,0x2fbc3),(1536,0xab83),(1536,0xc0),(1537,0x300c),(1538,0x80),(1539,0x3)]
def records25 : Array (ℕ × ℕ) := #[(1540,0x303),(1540,0xcc),(1540,0x80),(1541,0x303),(1542,0xc0),(1543,0x300c),(1544,0xc0),(1545,0x3300),(1546,0xc0),(1547,0xc0),(1548,0x82082043bc2b0228a0d1142bc4),(1548,0x82082043bc2b02bc228a0d1144),(1548,0x2082082082082bee),(1548,0x42e),(1548,0x3d0),(1549,0x82082043002083080b82bee),(1551,0x2),(1551,0x3),(1552,0x2f32f),(1552,0x2),(1552,0x3),(1553,0x80),(1554,0x303),(1554,0x3af),(1554,0x4af),(1554,0x820820430020830afb8202e),(1556,0x2),(1556,0x80),(1557,0x3),(1558,0x3),(1559,0x2),(1559,0xcc),(1559,0x3),(1560,0x3),(1561,0x2f32f),(1561,0x3),(1562,0x3),(1563,0x82082043bc228a0d10ac142bc4),(1563,0x82082043bc228a0d10af102b05),(1563,0x2fbcc)]
def records26 : Array (ℕ × ℕ) := #[(1563,0x820820af043bc2b0228a0c4445),(1563,0x820820af043bc228a0c4442b05),(1563,0x2fbcc),(1563,0x820820af08a283102b05043bd1),(1563,0x820820af08a2831010ef442b05),(1563,0x2fbcc),(1563,0x2fbcc),(1563,0x2fbcc),(1563,0x2fbcc),(1563,0x820820af0ac043bc228a0c4151),(1563,0x820820af0ac08a283105043bd1),(1563,0x8f),(1563,0x20820821020c40830ce),(1563,0x8f),(1563,0x20820820c20c3382104),(1563,0x12),(1563,0x103),(1563,0x92),(1563,0x12),(1563,0xc4),(1563,0x208208e084104104090102102145145144140145),(1564,0x80),(1565,0x2e),(1565,0x80),(1566,0x2e),(1566,0x3b8a),(1566,0x3b8a),(1566,0x92),(1566,0x4af),(1566,0xbc302f),(1567,0xc0),(1568,0x0),(1569,0x820820afb810c008202e083),(1571,0x2),(1571,0x2),(1571,0x2fbc3),(1572,0x2e),(1572,0xc003),(1573,0x80),(1574,0xc0c0)]
def records27 : Array (ℕ × ℕ) := #[(1575,0xc0),(1576,0x12),(1576,0x92),(1576,0x2e),(1576,0x3af),(1576,0x820820afb810c00820c202e),(1578,0x2),(1578,0x80),(1579,0x4af),(1579,0x3),(1580,0x3),(1581,0x2),(1581,0x3b8a),(1581,0x2e283),(1581,0x820820830830ca),(1581,0x3af),(1581,0x383),(1581,0x0),(1582,0x820820afb820c202e043002),(1584,0x80),(1585,0x3),(1586,0x2),(1586,0x4af),(1586,0x3),(1587,0x820820afb820c10c008202e),(1589,0x80),(1590,0x2),(1590,0x3),(1591,0x3af),(1591,0xc0),(1592,0xc0),(1593,0x820820c20c3282),(1593,0xce),(1593,0x2),(1593,0x2),(1593,0x8208208e0a3082),(1593,0x820820a2090082),(1593,0x94),(1593,0x85),(1593,0x84)]
def records28 : Array (ℕ × ℕ) := #[(1593,0x99),(1593,0x92),(1593,0x208208e090082145145145142104104104105100),(1594,0x80),(1595,0x0),(1596,0x0),(1597,0x80),(1598,0x8f),(1598,0x0),(1599,0x820820afb8202e083043002),(1601,0x80),(1602,0x3),(1603,0x2),(1603,0x2),(1603,0x2fbc3),(1604,0x0),(1605,0x820820afb8202e043002083),(1607,0x2),(1607,0x2),(1607,0x2e),(1607,0x303),(1608,0x80),(1609,0x2e283),(1609,0xcc),(1610,0x3),(1611,0x208208e090082104104104102145145145144140),(1612,0x80),(1613,0x80),(1614,0x2e),(1614,0x2e0ca),(1614,0x3300),(1615,0xc0),(1616,0x300c),(1617,0xc0),(1618,0x20820830830ce082104),(1618,0xc4),(1618,0x820830830ca082),(1618,0xce),(1618,0xc0),(1619,0xc0)]
def records29 : Array (ℕ × ℕ) := #[(1620,0x10),(1620,0x10d0),(1620,0x10),(1620,0x10),(1620,0x10),(1620,0x208240208514514508508e142104104105100104),(1621,0x80),(1622,0x0),(1623,0x1000f),(1624,0x403),(1624,0x0),(1625,0xf010),(1626,0xd0),(1626,0x80),(1627,0x0),(1628,0x0),(1629,0x92),(1629,0x20820821420c50830d0),(1629,0x92),(1629,0x20820820c20c3402145),(1629,0xf),(1629,0x143),(1629,0xf),(1629,0xc5),(1629,0x820820830830cc),(1629,0x10d0),(1629,0x42e),(1629,0x403),(1629,0x82082080b820c2bee043002),(1631,0x80),(1632,0x0),(1633,0x3),(1634,0x2),(1634,0x10),(1634,0x10d0),(1634,0x10),(1634,0x0),(1635,0x1000f),(1636,0x403),(1636,0x3)]
def records30 : Array (ℕ × ℕ) := #[(1637,0x82082080b820c10c0082bee),(1639,0x2),(1639,0x2f32f),(1639,0x42e),(1639,0x40f),(1640,0x303),(1640,0x3),(1641,0x80),(1642,0x303),(1642,0xc0),(1643,0xd2),(1643,0xc0),(1644,0x483),(1644,0x303),(1644,0x820820c20c3302),(1644,0xd0),(1644,0xd0),(1644,0x2f32f),(1644,0x8f),(1644,0x2),(1644,0x2),(1644,0xbc302f),(1645,0xc0),(1646,0xa0ee),(1646,0x2fbcc),(1646,0x2e),(1646,0x82082080b810c0082bee083),(1648,0x2),(1648,0x2),(1648,0x2fbc3),(1649,0x0),(1650,0xab83),(1650,0x0),(1651,0xf010),(1652,0xf),(1652,0x42e),(1652,0x82082080b810c00820c2bee),(1654,0x2),(1654,0x3),(1655,0x2f32f)]
def records31 : Array (ℕ × ℕ) := #[(1655,0x3d0),(1656,0x2),(1656,0xcc),(1656,0x300c),(1657,0xc0),(1658,0x80),(1659,0x303),(1660,0x80),(1661,0x303),(1661,0x3),(1662,0xcc),(1662,0x300c),(1663,0xc0),(1664,0xd2),(1664,0xc0),(1665,0x303),(1665,0xc0),(1666,0xd2),(1666,0x300c),(1667,0xc0),(1668,0xd2),(1668,0x483),(1668,0xcc),(1668,0x32ae),(1668,0x3b8a),(1668,0xd0),(1668,0x20820830830d0082145),(1668,0xc5),(1668,0x820830830cc082),(1668,0xd0),(1668,0x303),(1668,0xd0),(1668,0x2fbcc),(1668,0x2fbcc),(1668,0x820828c2082382),(1668,0x82082402082882),(1668,0x84),(1668,0x99),(1668,0x94),(1668,0x85)]
def records32 : Array (ℕ × ℕ) := #[(1668,0x8f),(1668,0x2082402082382104104104102145145145144140),(1669,0x80),(1670,0x2e),(1670,0x80),(1671,0x2fbc3),(1672,0x2e),(1672,0x82082080b82bee043002083),(1674,0x2),(1674,0x2),(1674,0x0),(1675,0x2e283),(1675,0x303),(1676,0x80),(1677,0x2e0ca),(1677,0x92),(1677,0x82082080b82bee083043002),(1679,0x80),(1680,0x0),(1681,0x3),(1682,0x2),(1682,0x2),(1682,0x2082402082382145145145142104104104105100),(1683,0x80),(1684,0x80),(1685,0x0),(1686,0x0),(1687,0xcc),(1688,0x3),(1689,0xaf082b020af082b022c22c5444),(1689,0xaf082b020af0822c22c5442b04),(1689,0xaf082b020af08b08b142b04091),(1689,0xaf082b020af08b08b142442b04),(1689,0xaf082b020af0ac08b08b144091),(1689,0xaf082b020af0ac0822c22c5111),(1689,0x8f),(1689,0x20820821020c40830ce),(1689,0x8f),(1689,0x20820820c20c3382104),(1689,0x820820830830cc)]
def records33 : Array (ℕ × ℕ) := #[(1689,0x10d0),(1689,0x42e),(1689,0x403),(1689,0x10),(1689,0x10d0),(1689,0x10),(1689,0x1000f),(1690,0x0),(1691,0x403),(1691,0x3),(1692,0x82082083080b810c0082bee),(1694,0x2),(1694,0x2f32f),(1694,0x42e),(1694,0x40f),(1695,0x303),(1695,0x3),(1696,0x80),(1697,0x303),(1697,0xc0),(1698,0xd2),(1698,0xc0),(1699,0x483),(1699,0x82082083080b82bee043002),(1701,0x80),(1702,0x0),(1703,0x3),(1704,0x2),(1704,0x303),(1704,0x820820c20c3302),(1704,0xd0),(1704,0xd0),(1704,0x2f32f),(1704,0x2),(1704,0x8f),(1704,0x2),(1704,0xaf082b02082bc22c22d1142b04),(1704,0xaf082b02082bc2b022c22d1144),(1704,0x820820830830ca),(1704,0x3af)]
def records34 : Array (ℕ × ℕ) := #[(1704,0x383),(1704,0x4af),(1704,0x3),(1705,0x820820830afb810c008202e),(1707,0x80),(1708,0x2),(1708,0x3),(1709,0x3af),(1709,0x0),(1710,0x820820830afb8202e043002),(1712,0x80),(1713,0x3),(1714,0x2),(1714,0xc0),(1715,0xc0),(1716,0x820820c20c3282),(1716,0xce),(1716,0x2),(1716,0x2),(1716,0xaf082b02082b022c22d1102bc5),(1716,0xaf082b02082b02bc22c22d1105),(1716,0xcc),(1716,0x820820c20c3302),(1716,0xd0),(1716,0xd0),(1716,0x303),(1716,0x2082082082082bee),(1716,0xcc),(1716,0x3),(1717,0x3),(1718,0x4af),(1718,0x3af),(1718,0x3),(1719,0x820820830430020afb8202e),(1721,0x80),(1722,0x2),(1722,0x3),(1723,0x2),(1723,0x2f32f),(1723,0x42e)]
def records35 : Array (ℕ × ℕ) := #[(1723,0x40f),(1724,0x3),(1725,0x82082083043002080b82bee),(1727,0x2),(1727,0x2f32f),(1727,0x3),(1728,0x303),(1728,0x80),(1729,0x2),(1729,0x3),(1730,0x3),(1731,0x2f32f),(1731,0x2f32f),(1731,0xcc),(1731,0xc0),(1732,0xd2),(1732,0x303),(1732,0xc0),(1733,0xc0),(1734,0xc0),(1735,0xd2),(1735,0x20820820c20c3382104),(1735,0x820820c20c3282),(1735,0xce),(1735,0xc0),(1736,0xc0),(1737,0x483),(1737,0x483),(1737,0xaf082b020822c22d10af142b04),(1737,0xaf082b020822c22d10ac102bc5),(1737,0xcc),(1737,0xcc),(1737,0xc0),(1738,0x300c),(1739,0xc0),(1740,0x3300),(1741,0xc0),(1742,0xc0),(1743,0x300c),(1744,0xc0)]
def records36 : Array (ℕ × ℕ) := #[(1745,0xd2),(1745,0xc0),(1746,0xc0),(1747,0xd2),(1747,0x303),(1747,0xcc),(1747,0x300c),(1748,0xc0),(1749,0xd2),(1749,0xd2),(1749,0x20820c20c308e082104),(1749,0xc4),(1749,0x3300),(1750,0xc0),(1751,0x820830830ca082),(1751,0xce),(1751,0xc0),(1752,0xc0),(1753,0x300c),(1754,0xc0),(1755,0x20820c20c3082382104),(1755,0xc0),(1756,0xd2),(1756,0xc0),(1757,0x303),(1757,0x820830830c2282),(1757,0xce),(1757,0xc0),(1758,0xc0),(1759,0xcc),(1759,0xc0),(1760,0xc0),(1761,0xd2),(1761,0x820820ac043bc2bc228a0c5444),(1761,0x820820ac043bc228a0c5442bc4),(1761,0xd2),(1761,0x483),(1761,0xd2),(1761,0xd2),(1761,0x820820ac08a283142bc4043bd1)]
def records37 : Array (ℕ × ℕ) := #[(1761,0x820820ac08a2831410ef442bc4),(1761,0x820820ac0af043bc228a0c5111),(1761,0x820820ac0af08a283144043bd1),(1761,0x483),(1761,0x483),(1761,0xaf082b0208b08b0af142442b04),(1761,0xaf082b0208b08b0af142b04091),(1761,0x8208208a2830ac1410ef442bc4),(1761,0x8208208a2830ac142bc4043bd1),(1761,0x8208208a2830af1010ef442b05),(1761,0x8208208a2830af102b05043bd1),(1761,0xaf082b0208b08b0ac102442bc5),(1761,0xaf082b0208b08b0ac102bc5091),(1761,0x8208208a283043bd10af102b05),(1761,0x8208208a283043bd10ac142bc4),(1761,0xaf082b0208b08b0910af142b04),(1761,0xaf082b0208b08b0910ac102bc5),(1761,0xaf082b020ac08b08b102bc5091),(1761,0xaf082b020ac08b08b102442bc5),(1761,0xaf082b020ac082bc22c22c4445),(1761,0xaf082b020ac0822c22c4442bc5),(1761,0xaf082b020ac0af0822c22c4151),(1761,0xaf082b020ac0af08b08b105091),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x0),(1761,0x3),(1761,0x3)]
def records38 : Array (ℕ × ℕ) := #[(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x0),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3)]
def records39 : Array (ℕ × ℕ) := #[(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x82082382402091451451451),(1761,0x2),(1761,0x2),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x82082382402091451451451),(1761,0x2),(1761,0x0),(1761,0x0),(1761,0x2),(1761,0x0),(1761,0x3)]
def records40 : Array (ℕ × ℕ) := #[(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x82082382402091451451451),(1761,0x2),(1761,0x2),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x8209008208e091451451451),(1761,0x2),(1761,0x0),(1761,0x0),(1761,0x0),(1761,0x0),(1761,0x2),(1761,0x0),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x0)]
def records41 : Array (ℕ × ℕ) := #[(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x0),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x8209008208e091451451451),(1761,0x2),(1761,0x2),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3)]
def records42 : Array (ℕ × ℕ) := #[(1761,0x0),(1761,0x3),(1761,0x8209008208e091451451451),(1761,0x2),(1761,0x2),(1761,0x0),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0)]
def records43 : Array (ℕ × ℕ) := #[(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x0),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3),(1761,0x3)]
def records44 : Array (ℕ × ℕ) := #[(1761,0x3)]
def pages : Array (Array (ℕ × ℕ)) := #[records0,records1,records2,records3,records4,records5,records6,records7,records8,records9,records10,records11,records12,records13,records14,records15,records16,records17,records18,records19,records20,records21,records22,records23,records24,records25,records26,records27,records28,records29,records30,records31,records32,records33,records34,records35,records36,records37,records38,records39,records40,records41,records42,records43,records44]
def advice (i : ℕ) := ((pages[i/40]?).getD #[])[i % 40]?.getD (0,0)
end Front2778.Full
namespace Front2778.Full
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
def negRows : List Row := [42,50,69,104,116,138,201,208,261,276,385,402]
def misses (w : Sig) : List Row → Nat
  | [] => 0
  | n::ns => ((misses w ns) <<< 1) ||| (if bit n w then 0 else 1)
def encode (w : Sig) (block : Nat) : List Row → Nat
  | [] => 0
  | p::ps => ((encode w block ps) <<< 12) ||| (if bit p w then block else 0)
def coverage (w : Sig) := encode w (misses w negRows) posRows
def unionCover : List Sig → ℕ
  | [] => 0
  | w::ws => coverage w ||| unionCover ws
def pairMask : Nat := 2^144-1
def fastSep (ws : List Sig) := ((unionCover ws)&&&pairMask)==pairMask

theorem misses_lt (w : Sig) (ns : List Row) : misses w ns < 2^ns.length := by
  induction ns with
  | nil => simp [misses]
  | cons n ns ih =>
    unfold misses
    apply Nat.or_lt_two_pow
    · simp [Nat.shiftLeft_eq,Nat.pow_succ];omega
    · have pos := Nat.two_pow_pos ns.length
      cases h : bit n w <;> simp [Nat.pow_succ] <;> omega

theorem misses_at (w : Sig) (ns : List Row) (j : Fin ns.length) :
    (misses w ns).testBit j.val= !(bit ns[j] w) := by
  induction ns with
  | nil => exact Fin.elim0 j
  | cons n ns ih =>
    cases j using Fin.cases with
    | zero => cases h : bit n w <;> simp [misses,Nat.testBit_or,h]
    | succ j =>
      cases h : bit n w <;> simp [misses,Nat.testBit_or,Nat.testBit_shiftLeft,h,Nat.testBit_one_eq_true_iff_self_eq_zero,ih]

theorem encode_at (w : Sig) (ps : List Row) {block : Nat} (size : block<2^12)
    (i : Fin ps.length) (j : Fin 12) :
    (encode w block ps).testBit (i.val*12+j.val) = (bit ps[i] w && block.testBit j.val) := by
  induction ps with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
    cases i using Fin.cases with
    | zero =>
      have hj := j.isLt
      cases h : bit p w <;> simp [encode,Nat.testBit_or,Nat.testBit_shiftLeft,h,show ¬12≤j.val by omega]
    | succ i =>
      let t := (i.val+1)*12+j.val
      have large : 12≤t := by dsimp [t];omega
      have sub : t-12=i.val*12+j.val := by dsimp [t];omega
      have ht : block.testBit t=false := Nat.testBit_lt_two_pow (lt_of_lt_of_le size (Nat.pow_le_pow_right (by decide) large))
      have ht' : block.testBit ((i.val+1)*12+j.val)=false := ht
      cases h : bit p w <;> simp [encode,Nat.testBit_or,Nat.testBit_shiftLeft,h,show 12≤(i.val+1)*12+j.val from large,show (i.val+1)*12+j.val-12=i.val*12+j.val from sub,ht',ih]

theorem union_hit {w ws i} (mem : w∈ws) (hit : (coverage w).testBit i=true) : (unionCover ws).testBit i=true := by
  induction ws with
  | nil => simp at mem
  | cons a ws ih =>
    rw [unionCover,Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp mem with rfl|rest
    · exact Or.inl hit
    · exact Or.inr (ih rest)

theorem all_posrows : ∀ i : Fin 12, bit posRows[i] graph=true := by decide +kernel
theorem all_negrows : ∀ i : Fin 12, bit negRows[i] graph=false := by decide +kernel
theorem fastSep_ok {ws k} (run : Path k ws.toFinset) : fastSep ws=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and]
  cases ht : pairMask.testBit t with
  | false => simp
  | true =>
    have small : t<144 := by
      by_contra! bad
      have off : pairMask.testBit t=false := Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : pairMask<2^144) (Nat.pow_le_pow_right (by decide) bad))
      simp_all
    let i : Fin 12 := ⟨t/12,by omega⟩
    let j : Fin 12 := ⟨t % 12,by omega⟩
    obtain ⟨w,mem,on,off⟩ := live_separates (fun w => bit posRows[i] w=true ∧ bit negRows[j] w=false)
      ⟨all_posrows i,all_negrows j⟩ (gate_sep _ _) run.live
    have flag := encode_at w posRows (block:=misses w negRows) (misses_lt w negRows) i j
    have eq := misses_at w negRows j
    change (misses w negRows).testBit j.val= !(bit negRows[j] w) at eq
    change (coverage w).testBit (i.val*12+j.val)=(bit posRows[i] w && (misses w negRows).testBit j.val) at flag
    rw [eq,on,off] at flag
    have idx : i.val*12+j.val=t := by dsimp [i,j];omega
    rw [idx] at flag
    simpa using union_hit (List.mem_toFinset.mp mem) (by simpa [coverage] using flag)
end Front2778.Full
namespace Front2778.Full
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
def wideB (z : Sig) :=
  let n := (z&&&pMask).toNat
  (n&&&(n-1))!=0
theorem wideB_ok {z : Sig} (wide : 2≤(positive (project z)).card) : wideB z=true := by
  let n := (z&&&pMask).toNat
  obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp wide
  have trueAt (i : Fin 24) (hi : i∈positive (project z)) : n.testBit (rowSmall i).val=true := by
    have both : (project z).getLsbD i.val=true ∧ target.getLsbD i.val=true := by simpa [positive,BitVec.getLsbD_and] using hi
    have pos := rows_ok i
    rw [both.2] at pos
    have h := (project_bit z i) ▸ both.1
    change bit (rowSmall i) (z&&&pMask)=true
    simpa [bit,BitVec.getLsbD_and,show z.getLsbD (rowSmall i).val=true from h,show pMask.getLsbD (rowSmall i).val=true from pos.1]
  have vu := trueAt u hu
  have vv := trueAt v hv
  have nz : n≠0 := by intro hz;rw [hz] at vu;simp at vu
  change (n&&&(n-1)!=0)=true
  apply bne_iff_ne.mpr
  intro zero
  obtain ⟨m,hm⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo nz).mp zero
  rw [hm,Nat.testBit_two_pow] at vu vv
  exact uv (rows_inj (Fin.ext ((decide_eq_true_iff.mp vu).symm.trans (decide_eq_true_iff.mp vv))))
end Front2778.Full
namespace Front2778.Full
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
def quickUseful (ws : List Sig) (z : Sig) :=
  wideB z && !(ws.any (fun w => Face.dominates global w z))
theorem quickUseful_ok {ws : List Sig} {z : Sig} (clean : ∀w∈ws.toFinset,¬better (project w) (project z))
    (wide : 2≤(positive (project z)).card) : quickUseful ws z=true := by
  exact Bool.and_eq_true_iff.mpr ⟨wideB_ok wide,(Bool.and_eq_true_iff.mp (useful_ok clean wide)).2⟩
def wideChildren (k : ℕ) (ws : List Sig) := (pairs ws).flatMap fun (a,b,r) =>
  [a&&&b,a|||b].flatMap fun z =>
    if quickUseful ws z then (keepChoices a b r).filterMap fun retained =>
      let child := z::retained
      if child.length≤k+1 && fastSep child then some child else none
    else []

theorem wide_has {ws : List Sig} {k : ℕ} {hist : List Sig} (h : Path (k+1) ws.toFinset)
    (hn : ws.Nodup) (past : Face.History hist) (supply : ∀w∈ws,w∈Face.seen hist) :
    ∃ z rem, z::rem∈wideChildren k ws ∧ (z::rem).Nodup ∧ Path k (z::rem).toFinset ∧
      Face.History (z::hist) ∧ ∀w∈z::rem,w∈Face.seen (z::hist) := by
  obtain ⟨a,b,z,r,shape,ab,hop,new,clean,wide,tail⟩ := h.first
  have am : a∈ws := List.mem_toFinset.mp (shape ▸ (by simp))
  have bm : b∈ws := List.mem_toFinset.mp (shape ▸ (by simp))
  obtain ⟨rest,choice,order⟩ := pick_two am bm ab
  have credit := quickUseful_ok clean wide
  have oldA := supply a am
  have oldB := supply b bm
  have hbuild : Face.History (z::hist) := by
    rcases (show z=a&&&b ∨ z=a|||b by simpa [SOp] using hop) with rfl|rfl
    · exact Face.History.gate past oldA oldB false
    · exact Face.History.gate past oldA oldB true
  have go {a b : Sig} (picked : (a,b,rest)∈pairs ws) (perm : ws.Perm (a::b::rest))
      (shape : ws.toFinset=insert a (insert b r)) (hop : z∈SOp a b) :
      ∃ rem,z::rem∈wideChildren k ws ∧ (z::rem).Nodup ∧ Path k (z::rem).toFinset ∧
        Face.History (z::hist) ∧ ∀w∈z::rem,w∈Face.seen (z::hist) := by
    obtain ⟨rem,hkept,nd,eq⟩ := recover_kept perm hn shape
    have old : rem.toFinset⊆ws.toFinset := by rw [eq,shape];exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have valid : (z::rem).Nodup := List.nodup_cons.mpr ⟨fun hm => new (old (List.mem_toFinset.mpr hm)),nd⟩
    have run : Path k (z::rem).toFinset := by simpa [eq] using tail
    have fits := live_card run.live
    rw [List.toFinset_card_of_nodup valid] at fits
    have sep := fastSep_ok run
    refine ⟨rem,?_,valid,run,hbuild,?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨_,picked,List.mem_flatMap.mpr ⟨z,?_,?_⟩⟩
      · simpa [SOp] using hop
      · simp only [credit,ite_true]
        exact List.mem_filterMap.mpr ⟨rem,hkept,by simp [sep]; simpa using fits⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl|given
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (supply _ (List.mem_toFinset.mp (old (List.mem_toFinset.mpr given))))
  refine ⟨z,?_⟩
  rcases choice with one|two
  · exact go one order shape hop
  · apply go two (order.trans (.swap _ _ _)) (shape.trans (Finset.insert_comm ..))
    rcases (show z=a&&&b ∨ z=a|||b by simpa [SOp] using hop) with rfl|rfl <;> simp [SOp,BitVec.and_comm,BitVec.or_comm]

end Front2778.Full
namespace Front2778.Full
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
def tiles (v : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => ((tiles v k) <<< 12)|||v
structure Enc where
  val : Sig
  pos : Nat
  off : Nat
def enc (w : Sig) : Enc := ⟨w,encode w 4095 posRows,tiles (misses w negRows) 12⟩
def Enc.gate (d : Bool) (a b : Enc) : Enc :=
  if d then ⟨a.val|||b.val,a.pos|||b.pos,a.off&&&b.off⟩
  else ⟨a.val&&&b.val,a.pos&&&b.pos,a.off|||b.off⟩
def Enc.both (a : Enc) := a.pos&&&a.off
def Enc.Good (a : Enc) := ∀ i j : Fin 12,
  a.pos.testBit (i.val*12+j.val)=bit posRows[i] a.val ∧
  a.off.testBit (i.val*12+j.val)= !(bit negRows[j] a.val)
theorem tiles_bit (v k : Nat) (bound : v<2^12) (i : Fin k) (j : Fin 12) :
    (tiles v k).testBit (i.val*12+j.val)=v.testBit j.val := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    cases i using Fin.cases with
    | zero => have hj := j.isLt; simp [tiles,Nat.testBit_or,Nat.testBit_shiftLeft,show ¬12≤j.val by omega]
    | succ i =>
      have large : 12≤(i.val+1)*12+j.val := by omega
      have sub : (i.val+1)*12+j.val-12=i.val*12+j.val := by omega
      have hi := Nat.testBit_lt_two_pow (lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) large))
      simp [tiles,Nat.testBit_or,Nat.testBit_shiftLeft,large,sub,hi,ih]
theorem enc_good (w : Sig) : (enc w).Good := by
  intro i j
  constructor
  · have h := encode_at w posRows (block:=4095) (by decide) i j
    change (encode w 4095 posRows).testBit (i.val*12+j.val)=(bit posRows[i] w && (4095:Nat).testBit j.val) at h
    have yes : Nat.testBit 4095 j.val=true := by
      change Nat.testBit (2^12-1) j.val=true
      exact (Nat.testBit_two_pow_sub_one 12 j.val).trans (decide_eq_true j.isLt)
    simpa [enc,yes] using h
  · exact (tiles_bit _ 12 (misses_lt w negRows) i j).trans (misses_at w negRows j)
theorem Enc.good_gate {a b : Enc} (ha : a.Good) (hb : b.Good) (d : Bool) : (a.gate d b).Good := by
  intro i j
  obtain ⟨pa,na⟩ := ha i j
  obtain ⟨pb,nb⟩ := hb i j
  cases d <;> simp [Enc.gate,Nat.testBit_or,Nat.testBit_and,pa,pb,na,nb,bit]
theorem both_at {a : Enc} (h : a.Good) (i j : Fin 12) :
  a.both.testBit (i.val*12+j.val)=(coverage a.val).testBit (i.val*12+j.val) := by
  obtain ⟨yes,no⟩ := h i j
  have x := encode_at a.val posRows (block:=misses a.val negRows) (misses_lt _ _) i j
  change (coverage a.val).testBit (i.val*12+j.val) = (bit posRows[i] a.val && (misses a.val negRows).testBit j.val) at x
  rw [Enc.both,Nat.testBit_and,yes,no,x]
  exact congrArg (fun v => bit posRows[i] a.val && v) (misses_at a.val negRows j).symm
end Front2778.Full
namespace Front2778.Full
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
def unionEnc : List Enc → Nat
  | [] => 0
  | a::as => a.both ||| unionEnc as
def encKeep (k : Nat) (a b z : Enc) (r : List Enc) :=
  let rc := unionEnc r
  let ac := a.both ||| rc
  let bc := b.both ||| rc
  let abc := a.both ||| bc
  let zc := z.both
  let tagged := [(r,rc),(a::r,ac),(b::r,bc),(a::b::r,abc)]
  tagged.filterMap fun (keep,u) =>
    if keep.length≤k && (((zc|||u)&&&pairMask)==pairMask) then some (z.val::keep.map Enc.val) else none
def matrixWideChildren (k : Nat) (ws : List Sig) := (pairs (ws.map enc)).flatMap fun (a,b,r) =>
  [a.gate false b,a.gate true b].flatMap fun z =>
    if quickUseful ws z.val then encKeep k a b z r else []
theorem singles_map {A B} (f : A→B) (ws : List A) :
    singles (ws.map f) = (singles ws).map (fun (a,r) => (f a,r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a r ih => simp [singles,ih,List.map_map,Function.comp_def]
theorem pairs_map {A B} (f : A→B) (ws : List A) :
    pairs (ws.map f) = (pairs ws).map (fun (a,b,r) => (f a,f b,r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a r ih => simp [pairs,singles_map,ih,List.map_map,Function.comp_def]
theorem union_same {xs : List Enc} (good : ∀x∈xs,x.Good) (i j : Fin 12) :
    (unionEnc xs).testBit (i.val*12+j.val)=(unionCover (xs.map Enc.val)).testBit (i.val*12+j.val) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [unionEnc,unionCover,Nat.testBit_or,both_at (good a (by simp)) i j,ih (fun x hx=>good x (by simp [hx]))]
theorem masked_same {xs : List Enc} (good : ∀x∈xs,x.Good) :
    (unionEnc xs)&&&pairMask=(unionCover (xs.map Enc.val))&&&pairMask := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_and]
  cases ht : pairMask.testBit t with
  | false => simp
  | true =>
    have small : t<144 := decide_eq_true_iff.mp ((Nat.testBit_two_pow_sub_one 144 t).symm.trans ht)
    let i : Fin 12 := ⟨t/12,by omega⟩
    let j : Fin 12 := ⟨t % 12,by omega⟩
    have idx : i.val*12+j.val=t := by dsimp [i,j];omega
    simpa [idx] using union_same good i j
theorem sameKeep (k : Nat) {a b z : Enc} {r : List Enc} (ha : a.Good) (hb : b.Good)
    (hz : z.Good) (hr : ∀x∈r,x.Good) :
    encKeep k a b z r = (keepChoices a.val b.val (r.map Enc.val)).filterMap fun retained =>
      let child := z.val::retained
      if child.length≤k+1 && fastSep child then some child else none := by
  have consGood {c : Enc} {cs : List Enc} (hc : c.Good) (hs : ∀v∈cs,v.Good) : ∀v∈c::cs,v.Good := by
    intro v m;rcases List.mem_cons.mp m with rfl|m;exact hc;exact hs v m
  have m0 := masked_same (consGood hz hr)
  have m1 := masked_same (consGood hz (consGood ha hr))
  have m2 := masked_same (consGood hz (consGood hb hr))
  have m3 := masked_same (consGood hz (consGood ha (consGood hb hr)))
  simp only [unionEnc,List.map_cons] at m0 m1 m2 m3
  simp [encKeep,keepChoices,List.filterMap,fastSep,List.length_map,m0,m1,m2,m3]
theorem matrixWideEq (k ws) : matrixWideChildren k ws=wideChildren k ws := by
  simp only [matrixWideChildren,pairs_map,List.flatMap_map,Function.comp_def]
  unfold wideChildren
  apply List.flatMap_congr
  rintro ⟨a,b,r⟩ _
  change _ = (([a&&&b,a|||b] : List Sig).flatMap _)
  have hr : ∀x∈r.map enc,x.Good := by intro x hx;obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx;exact enc_good w
  have andKeep := sameKeep k (enc_good a) (enc_good b) (Enc.good_gate (enc_good a) (enc_good b) false) hr
  have orKeep := sameKeep k (enc_good a) (enc_good b) (Enc.good_gate (enc_good a) (enc_good b) true) hr
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [andKeep,orKeep]
  simp [Enc.gate,enc,List.map_map,Function.comp_def]
end Front2778.Full
namespace Front2778.Full.Flat
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
def d0 : Array ℕ := #[0,3737600,1705984,3835904,3868672,3901440,3934208,3837952,3870720,3903488,3936256,2793472,3876864,3909632,3942400,3911680,3944448,3946496,3868673,3966977,3870721,3969025,2828289,3977217,2785282,3835906,3901442,3934210,3840002,3872770,3905538,3938306,3876866,3909634,3942402,3911682,3946498,2752515,3801091,720899]
def d1 : Array ℕ := #[1769475,2850819,2883587,2916355,3964931,3803139,1771523,2885635,2918403,3966979,2756611,3805187,1773571,2854915,3969027,3973123,3946499,2756612,3907588,2863108,2850821,2883589,3932165,2916357,3964933,1771525,2852869,3966981,2756613,2887685,2920453,3907589,3973125,2863109,3946501,2752518,3801094,2850822,3899398,262150]
def d2 : Array ℕ := #[1310726,2916358,3964934,3803142,1771526,2852870,3901446,3966982,2756614,3805190,3903494,3969030,3907590,3940358,3973126,2863110,3946502,3979270,3981318,2752519,3801095,2850823,3899399,262151,1310727,2916359,3964935,3803143,3901447,2918407,3966983,2756615,3805191,1773575,3903495,3969031,1777671,3907591,3940359,3973127]
def d3 : Array ℕ := #[3946503,3979271,3981319,2850824,2883592,2916360,3901448,2918408,3966984,2756616,2854920,2887688,1777672,3973128,2863112,3979272,3981320,2756617,1777673,3973129,2752522,2850826,2883594,2916362,3803146,2852874,3901450,2885642,3934218,2756618,3805194,2920458,3969034,1777674,3907594,3973130,2863114,3946506,3981322,2719755]
def d4 : Array ℕ := #[3770379,3803147,3868683,3807243,3872779,3905547,3938315,3874827,3940363,3911691,3944459,3946507,2752524,2785292,3833868,2883596,3932172,2754572,3835916,1804300,2918412,3966988,2789388,2887692,2920460,1810444,3940364,3973132,3975180,2920461,1810445,3973133,3803150,3835918,2885646,3934222,3805198,3842062,1810446,3942414]
def d5 : Array ℕ := #[2752527,2785295,2883599,2916367,2787343,2885647,2756623,2920463,1810447,3940367,3973135,3942415,3975183,2897935,2885648,3942416,2897936,2752529,2785297,2916369,2754577,2885649,2918417,3805201,2789393,3837969,1810449,3942417,3975185,2897937,2951186,2885651,2897939,2951188,1806356,2885653,2897941,3803158,3971094,3973142]
def d6 : Array ℕ := #[3803160,3936280,3940376,2918425,2789401,2918426,2852891,2918427,2856987,3909659,262172,1310748,2916380,3964956,2918428,3967004,1675292,2756636,3969052,3973148,2852895,3901471,2920479,3969055,2856991,2883616,2887712,3868706,2885667,2822180,3870756,262181,3770405,3967013,3969061,1708070,2955302,3934247,3805223,3940391]
def d7 : Array ℕ := #[3911719,2920488,2791464,3975208,262187,3840043,1675308,2826284,2951213,2918446,2791470,2885679,2791471,2889775,3975215,65584,1114160,3735600,3768368,3833904,1310768,3737648,2787376,3835952,3838000,1806384,2791472,3840048,1808432,2889776,2820145,788529,2824241,792625,2826289,65586,1114162,3735602,3768370,1310770]
def d8 : Array ℕ := #[3964978,3737650,2918450,3967026,1773618,3969074,1775666,2889778,2922546,3971122,622643,1671219,2949171,755763,2951219,1675315,2953267,759859,2955315,2957363,2787380,2922548,3975220,2885685,2889781,2922549,2820150,98359,1673271,690231,1738807,2787383,659511,1708087,792631,1841207,2957367,1845303,690232,659512]
def d9 : Array ℕ := #[825400,294970,1343546,2897981,294975,2787391,3835967,327744,2822208,2918465,2787394,2885698,2889794,3975234,788547,2885701,2889797,2897989,2787398,3835974,2951239,659527,2918472,626760,1675336,2723912,692296,1740872,2924616,2932808,2887753,2891849,3977289,622666,657482,692298,262219,3901515,2863179,294988]
def d10 : Array ℕ := #[2889804,2897996,262221,3835981,294990,1675342,3907663,2863183,3946575,2887760,3942480,2898000,3981392,294993,2791505,3840081,327762,2826322,2885715,2898003,2850900,2852948,2918484,3909716,65621,2162773,3735637,3768405,3833941,1802325,3737685,2787413,3835989,1804373,2885717,3838037,1314901,2791509,3840085,2818134]
def d11 : Array ℕ := #[786518,2820182,788566,2822230,788567,65624,2162776,2852952,3901528,2920536,3969112,2857048,2863192,2951257,2887769,2955353,2891865,2898009,2820187,622684,1671260,2719836,2752604,2785372,327772,1376348,1673308,690268,1738844,2787420,1675356,659548,1708124,2756700,1839196,301148,1349724,1843292,2719839,1673311]
def d12 : Array ℕ := #[3868767,2822239,3870815,266335,1314911,3872863,2826335,3874911,657504,333921,1382497,262243,3967075,3969123,295012,1708132,2955364,262245,2920549,3969125,295014,2951270,2955366,1777767,3907687,3940455,2920552,2791528,1812584,3942504,3975272,295017,3836009,3936361,3840105,3938409,1812585,327786,2918506,2826346]
def d13 : Array ℕ := #[1847402,2951275,1810539,2951276,2955372,65645,2162797,2787437,3836013,2918509,3967085,3838061,2887789,3936365,1347693,2791533,3840109,1808493,3938413,1812589,3975277,622702,2719854,2752622,2818158,2820206,2918510,2822254,2824302,2922606,2826350,1843310,1847406,65647,2162799,3735663,3768431,1769583,3965039,3737711]
def d14 : Array ℕ := #[1771631,2885743,2918511,3967087,1314927,3969135,2922607,3971183,622704,2719856,2752624,753776,2949232,755824,2951280,2953328,2955376,2957424,2785393,2787441,2852977,3840113,2922609,3971185,3975281,788594,2951282,2955378,2957426,2820211,2918515,1847411,2752628,1706100,3967092,266356,1314932,2920564,3969140,2922612]
def d15 : Array ℕ := #[3971188,3973236,301173,1349749,690294,2957430,622711,1671287,2719863,2752631,2785399,295031,1343607,1673335,690295,1738871,2787447,1837175,1675383,659575,1708151,2756727,333943,1382519,1845367,659578,1708154,262267,2920571,3969147,2949246,2951294,2918527,2887807,2889855,2922623,2898047,2918528,2922624,2924672]
def d16 : Array ℕ := #[2932864,2918530,2922626,3971202,2918531,2922627,2922630,3971206,690311,690312,659592,262284,3903628,2863244,295053,3737741,2885774,2898062,2885776,2898064,65681,1114257,3834001,2883729,3932305,1343633,2787473,3836049,1804433,3934353,2791569,3840145,2922641,3971217,1812625,3975313,622738,1671314,2818194,2916498]
def d17 : Array ℕ := #[2820242,2918546,1675410,2822290,1839250,2824338,2826386,1847442,2883731,2885779,2918547,2922643,2898067,2916500,2918548,2920596,2932884,65685,1114261,2916501,3965077,2853013,2857109,3905685,2863253,2949270,2951318,2887830,2891926,2898070,2785431,2787479,2918551,2889879,2922647,1812631,2898071,2818200,2820248,2822296]
def d18 : Array ℕ := #[2924696,1847448,2932888,2850969,2857113,3905689,2924697,3973273,98458,2752666,786586,1835162,690330,2787482,2951322,659610,1708186,2756762,1839258,688283,1736859,2785435,2918555,692379,2789531,2924699,2932891,2818204,1673372,3770524,3868828,3934364,2822300,2887836,3872924,2889884,3938460,2826396,3874972,2924700]
def d19 : Array ℕ := #[3973276,3977372,655517,2752669,1706141,1869981,626845,659613,2756765,657566,692382,3934367,3805343,3940511,2787488,2920608,3975328,2787489,2853025,3838113,2920609,3969185,2791585,3975329,2820258,3977378,3967139,3805347,3969187,2883749,2887845,3977381,2818214,3866790,262310,1310886,1673382,2754726,3868838,2822310]
def d20 : Array ℕ := #[3870886,3874982,2918567,3967143,2818216,2883752,2754728,3803304,3868840,2885800,3934376,2822312,3870888,2920616,3969192,2824360,3874984,3940520,3977384,2822313,2855083,3903659,262317,2918573,3967149,295086,1845423,2885809,2918577,2889905,2949298,788658,2951346,2953394,2820275,3977395,2824372,2853045,2918582,3967158]
def d21 : Array ℕ := #[2922678,2787511,2791607,1845431,2887865,2891961,622778,657594,692410,657595,688316,624828,1673404,2754748,690364,1738940,1876156,327871,1376447,2820288,2820289,2918593,1847489,2820290,2853059,3872966,659655,2918604,2922700,2787533,2791629,1845453,2885838,2889934,2898126,2820303,2824399,2889936,819409,690385]
def d22 : Array ℕ := #[659665,657620,692436,2826453,295129,2791641,3840217,2791644,3840220,2820318,2824414,2820319,2885856,2918624,2789600,2791648,2922720,1812704,2898144,2820321,2920673,2824417,2826465,1847521,2932961,2826466,3875042,690403,2787555,690404,659684,2859237,3907813,2920688,2754802,2824435,2922740,2820342,659705,2920699]
def d23 : Array ℕ := #[295164,327933,65790,2162942,1347838,1710334,2922752,2918657,690435,65796,1114372,1343748,1706244,1673480,2920726,2787607,2820377,2826521,2918682,2924826,723227,692507,2826529,2922786,657699,2918692,624933,723238,2787624,2789672,295211,133419,2826540,2162990,657710,1706286,2754862,1151278,1808686,1810734]
def d24 : Array ℕ := #[692527,2824497,2826545,1343794,624946,1673522,2722098,1315122,1810738,788787,659763,2820404,2824500,2826551,792890,2920767,2924863,328000,2163010,657730,1706306,1347906,1808706,2924866,692547,2922820,2924868,2918726,2922823,1311048,624968,1673544,2722120,1347912,1810760,788809,2920781,2924877,690512,792912]
def d25 : Array ℕ := #[794960,2922833,657747,792915,2918740,2924884,2820437,2824533,657750,725334,657751,624984,754011,1081693,1343837,659805,1708381,1808733,2924893,694622,788831,694623,794975,1081696,1147232,659808,1708384,2756960,1808736,1810784,694625,2789730,727395,696675,727396,624997,729445,659814,659815,2918770]
def d26 : Array ℕ := #[657779,625012,657781,657783,625016,694652,2920829,690558,625028,659850,659851,3901836,2863500,301453,266638,2890127,2898319,98704,299408,299409,295318,1343894,2820505,328090,692634,2820517,659879,2787753,2791849,2822573,2826669,1343919,657839,1706415,2754991,1806767,1317295,788912,692656,2820529]
def d27 : Array ℕ := #[2826673,295347,100787,2824628,2228661,625077,1673653,2722229,2232757,1806773,1808821,659894,2822586,793019,2828733,2857406,2863550,1343935,657855,1706431,1804735,692672,2228675,1802691,625091,1673667,2722243,1804739,2232771,1673668,1739204,135620,2232772,690630,657864,262603,295371,295372,328140,295373]
def d28 : Array ℕ := #[328141,328143,301520,1350096,725457,694737,336337,295378,1346003,659923,1708499,1806803,694740,694741,1802711,1346007,659927,1708503,2757079,1317335,788952,694744,788953,690650,727514,297435,1346011,332252,696796,657885,2820575,2826719,690656,725472,262625,295394,131558,2228710,2722278,1743334]
def d29 : Array ℕ := #[2922990,98800,332272,2922996,332278,295417,1343993,2820602,2826746,1847802,2918907,2925051,2925052,328190,723454,692734,3836415,1812991,334336,299524,2826757,1847813,332295,332296,1778189,2787854,2791950,1813006,657935,2755087,1350159,1810959,692752,328211,100883,328213,2824726,2826774,1847830,1802775]
def d30 : Array ℕ := #[625175,2722327,2918935,2232855,1352215,786968,789016,659992,2818585,2820633,2886169,2824729,821786,2785819,135707,2232859,1352219,723484,295456,690723,657958,2921005,2925101,2918960,2925105,1311282,657970,1706546,2755122,1806898,1350194,789043,2923060,2925108,328245,2228790,625206,1673782,1806902,2923062]
def d31 : Array ℕ := #[1352246,660023,2925115,2921021,2925117,690751,793151,657985,791105,793153,2925122,2918979,2925123,2925124,2820678,2822726,2824774,2890310,657992,725576,2925129,825932,2925136,2918993,723538,2925140,295509,328278,131671,2228823,2789975,1352279,2925148,727645,262750,295518,295519,328287,295520,328288]
def d32 : Array ℕ := #[295521,301667,1350243,725604,336484,1802854,1313382,660070,1708646,2757222,1350246,789095,789096,694888,723561,328298,660075,2757227,1350251,1811051,694892,694893,297582,1346158,332399,727663,696943,625264,729712,658040,625275,658052,625285,660105,660106,3904139,2863755,301708,266893,1778324]
def d33 : Array ℕ := #[2787989,2790037,1813141,328342,133782,328344,2822809,2826905,1847961,1802906,658074,2755226,2919066,1151642,1348250,787099,789147,692891,2818716,2820764,2886300,2826908,821917,625310,2722462,1348254,1809054,660127,2720418,135842,1184418,1348258,658083,690859,295597,658094,658098,625331,2828985,2855610]
def d34 : Array ℕ := #[2863802,2163389,1802941,658109,1706685,2755261,1804989,1151677,1344190,625342,1673918,1804990,660159,1673920,1739456,135872,1184448,690883,658116,658120,625354,1706707,131796,1180372,1344212,1641172,754392,1708762,725723,695003,1082076,1147612,1805020,660188,1708764,2757340,1807068,695005,695006,1147615]
def d35 : Array ℕ := #[1344223,1805023,660191,2757343,2921183,789216,791264,695008,695009,690914,727778,690918,625385,1708779,2820844,2886380,2822892,2826988,690926,725742,690927,262896,131829,1180405,2722549,1743605,822012,690941,660225,660226,2921220,2788101,2919174,2923270,2820871,2824967,658184,693000,2919177,2923273]
def d36 : Array ℕ := #[2923274,2820876,2824972,2890508,2827020,2925326,658191,693007,2919184,658193,262936,295705,2820893,2824989,66335,2163487,2788127,2792223,658209,693025,262948,2820902,2886438,2824998,2827046,66347,1114923,2788139,2792235,2792239,658224,693040,658225,658235,625469,2921279,826177,2919234,658243,658249]
def d37 : Array ℕ := #[625482,660303,660304,822101,625496,658275,625508,658277,625510,658280,625513,658283,625516,660335,660336,660337,660338,658297,625530,658301,625536,660365,660366,691112,625577,691114,625579,693164,693165,1311674,1776570,756668,695230,625599,691137,691138,660419,1313732,1776580,695240]
def d38 : Array ℕ := #[660425,758730,658379,625612,691151,658384,1315795,1776595,695253,695254,691161,691162,1315806,1776606,662497,695266,691172,658405,760806,693223,760810,660459,691180,625645,658414,625647,693232,660465,695286,1313783,1776631,697337,695292,758781,1311745,1776641,756739,697348,658437,697352]
def d39 : Array ℕ := #[697353,695307,660492,623652,656421,623655,691245,658478,693295,1313840,1774640,695347,693301,758838,691255,625720,1311805,1774653,756799,662593,625730,693321,1770570,1313866,756811,691276,660559,1311824,1772624,756817,658515,691285,658518,558178,590947,695396,695397,558182,695400,1770601]
def d40 : Array ℕ := #[1315945,756842,691307,695406,695407,1772656,1315952,695412,758901,695415,693368,558201,590970,558203,691326,625791,693376,693377,691334,625799,623757,656526,691343,625808,691346,625811,623765,693398,693399,1770660,1318052,756901,695462,625831,691372,691373,660655,1772720,1318064,695476]
def d41 : Array ℕ := #[660662,758967,658617,625851,691397,658630,1774794,1318090,695501,695502,691408,691409,1774804,1318100,662742,695512,691419,658652,761053,693470,761055,660705,691427,625892,658662,625896,693482,660715,558337,591106,558340,695557,1772807,1318151,697610,695564,759053,1770768,1318160,757009]
def d42 : Array ℕ := #[697618,658707,558358,591127,558360,697625,697626,695579,660764,691502,658735,693553,1772850,1316146,695606,693560,759097,691515,625981,1770815,1316159,757056,662849,625986,693586,1312083,1772883,757076,691542,660824,1770841,1314137,757082,658779,691549,658782,695660,695661,695664,1312113]
def d43 : Array ℕ := #[1774961,757106,691572,695672,695673,1314170,1774970,695677,759167,695681,693634,691590,626057,693642,693643,691600,626065,658840,626073,658842,626075,660892,660893,658846,626079,658849,626082,660902,660903,658860,626093,658864,626097,660914,660915,658869,626103,658875,626108,660926]
def d44 : Array ℕ := #[660927]
def book : Array (Array ℕ) := #[d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15,d16,d17,d18,d19,d20,d21,d22,d23,d24,d25,d26,d27,d28,d29,d30,d31,d32,d33,d34,d35,d36,d37,d38,d39,d40,d41,d42,d43,d44]
def get (i : ℕ) := ((book[i/40]?).getD #[])[i % 40]?.getD 0
def remaining (i : Nat) := if i<1 then 14 else if i<18 then 13 else if i<230 then 12 else if i<913 then 11 else if i<1503 then 10 else 9
def recover : ℕ → ℕ → List Sig × List Sig
  | 0,_ => (starting,[paidWord])
  | _+1,0 => (starting,[paidWord])
  | d+1,id+1 =>
    let x := get (id+1)
    let (ws,h) := recover d (x&&&2047)
    let a := ws.getD ((x>>>11)&&&15) 0
    let b := ws.getD ((x>>>15)&&&15) 0
    let z := if x.testBit 19 then a|||b else a&&&b
    let r := (ws.erase a).erase b
    let withB := if x.testBit 21 then b::r else r
    let withA := if x.testBit 20 then a::withB else withB
    (z::withA,z::h)
def matchChild (k id : Nat) (ws hist : List Sig) :=
  decide (id<1761 ∧ remaining id=k) && (ws==(recover 5 id).1) && (hist==(recover 5 id).2)
def test (id : Nat) :=
  let (ws,h) := recover 5 id
  let k := remaining id-1
  scan Face.faces k h (matchChild k) (matrixWideChildren k ws) (advice id).1 (advice id).2
def chunk (b : Nat) := (List.range 8).all fun j => if b*8+j<1761 then test (b*8+j) else true

theorem nonzero (id : Nat) : remaining id≠0 := by simp only [remaining];split_ifs <;> decide
theorem exclude (all : ∀i<1761,test i=true) {k} : ∀ {id}, id<1761 → remaining id=k →
    let (ws,h) := recover 5 id
    ws.Nodup → Face.History h → (∀w∈ws,w∈Face.seen h) → ¬Path k ws.toFinset := by
  induction k with
  | zero => intro id _ v;exact False.elim (nonzero id v)
  | succ k ih =>
    intro id hi rem nd past supply run
    have ht := all id hi
    change scan Face.faces (remaining id-1) (recover 5 id).2 (matchChild (remaining id-1))
      (matrixWideChildren (remaining id-1) (recover 5 id).1) (advice id).1 (advice id).2=true at ht
    rw [rem,Nat.succ_sub_one] at ht
    obtain ⟨z,r,mem,nd',path',hist',supply'⟩ := wide_has run nd past supply
    rw [←matrixWideEq] at mem
    rcases scan_seen ht mem with ⟨f,hf,pr⟩|⟨j,valid⟩
    · exact Bool.noConfusion (pr.symm.trans (Face.reject_sound (Face.all_faces f hf) hist' supply' nd' path'))
    · obtain ⟨⟨⟨hj,rank⟩,hw⟩,hh⟩ := (show ((j<1761 ∧ remaining j=k) ∧ z::r=(recover 5 j).1) ∧ z::(recover 5 id).2=(recover 5 j).2 by simpa [matchChild] using valid)
      have next := ih hj rank
      change (recover 5 j).1.Nodup → Face.History (recover 5 j).2 → (∀w∈(recover 5 j).1,w∈Face.seen (recover 5 j).2) → ¬Path k (recover 5 j).1.toFinset at next
      rw [←hw,←hh] at next
      exact next nd' hist' supply' path'

theorem all_test (all : ∀ b : Fin 221,chunk b.val=true) (i : Nat) (hi : i<1761) : test i=true := by
  let b : Fin 221 := ⟨i/8,by omega⟩
  have hh := List.all_eq_true.mp (all b) (i % 8) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  have eq : b.val*8+i % 8=i := by dsimp [b];omega
  simpa only [eq,hi,ite_true] using hh
end Front2778.Full.Flat
namespace Front2778.Full.Flat
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass0 : chunk 0=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass1 : chunk 1=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass2 : chunk 2=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass3 : chunk 3=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass4 : chunk 4=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass5 : chunk 5=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass6 : chunk 6=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass7 : chunk 7=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass8 : chunk 8=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass9 : chunk 9=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass10 : chunk 10=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass11 : chunk 11=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass12 : chunk 12=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass13 : chunk 13=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass14 : chunk 14=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass15 : chunk 15=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass16 : chunk 16=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass17 : chunk 17=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass18 : chunk 18=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass19 : chunk 19=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass20 : chunk 20=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass21 : chunk 21=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass22 : chunk 22=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass23 : chunk 23=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass24 : chunk 24=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass25 : chunk 25=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass26 : chunk 26=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass27 : chunk 27=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass28 : chunk 28=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass29 : chunk 29=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass30 : chunk 30=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass31 : chunk 31=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass32 : chunk 32=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass33 : chunk 33=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass34 : chunk 34=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass35 : chunk 35=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass36 : chunk 36=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass37 : chunk 37=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass38 : chunk 38=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass39 : chunk 39=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass40 : chunk 40=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass41 : chunk 41=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass42 : chunk 42=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass43 : chunk 43=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass44 : chunk 44=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass45 : chunk 45=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass46 : chunk 46=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass47 : chunk 47=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass48 : chunk 48=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass49 : chunk 49=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass50 : chunk 50=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass51 : chunk 51=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass52 : chunk 52=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass53 : chunk 53=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass54 : chunk 54=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass55 : chunk 55=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass56 : chunk 56=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass57 : chunk 57=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass58 : chunk 58=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass59 : chunk 59=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass60 : chunk 60=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass61 : chunk 61=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass62 : chunk 62=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass63 : chunk 63=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass64 : chunk 64=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass65 : chunk 65=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass66 : chunk 66=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass67 : chunk 67=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass68 : chunk 68=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass69 : chunk 69=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass70 : chunk 70=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass71 : chunk 71=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass72 : chunk 72=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass73 : chunk 73=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass74 : chunk 74=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass75 : chunk 75=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass76 : chunk 76=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass77 : chunk 77=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass78 : chunk 78=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass79 : chunk 79=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass80 : chunk 80=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass81 : chunk 81=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass82 : chunk 82=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass83 : chunk 83=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass84 : chunk 84=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass85 : chunk 85=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass86 : chunk 86=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass87 : chunk 87=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass88 : chunk 88=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass89 : chunk 89=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass90 : chunk 90=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass91 : chunk 91=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass92 : chunk 92=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass93 : chunk 93=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass94 : chunk 94=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass95 : chunk 95=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass96 : chunk 96=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass97 : chunk 97=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass98 : chunk 98=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass99 : chunk 99=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass100 : chunk 100=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass101 : chunk 101=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass102 : chunk 102=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass103 : chunk 103=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass104 : chunk 104=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass105 : chunk 105=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass106 : chunk 106=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass107 : chunk 107=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass108 : chunk 108=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass109 : chunk 109=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass110 : chunk 110=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass111 : chunk 111=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass112 : chunk 112=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass113 : chunk 113=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass114 : chunk 114=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass115 : chunk 115=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass116 : chunk 116=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass117 : chunk 117=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass118 : chunk 118=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass119 : chunk 119=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass120 : chunk 120=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass121 : chunk 121=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass122 : chunk 122=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass123 : chunk 123=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass124 : chunk 124=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass125 : chunk 125=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass126 : chunk 126=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass127 : chunk 127=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass128 : chunk 128=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass129 : chunk 129=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass130 : chunk 130=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass131 : chunk 131=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass132 : chunk 132=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass133 : chunk 133=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass134 : chunk 134=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass135 : chunk 135=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass136 : chunk 136=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass137 : chunk 137=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass138 : chunk 138=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass139 : chunk 139=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass140 : chunk 140=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass141 : chunk 141=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass142 : chunk 142=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass143 : chunk 143=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass144 : chunk 144=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass145 : chunk 145=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass146 : chunk 146=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass147 : chunk 147=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass148 : chunk 148=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass149 : chunk 149=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass150 : chunk 150=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass151 : chunk 151=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass152 : chunk 152=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass153 : chunk 153=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass154 : chunk 154=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass155 : chunk 155=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass156 : chunk 156=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass157 : chunk 157=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass158 : chunk 158=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass159 : chunk 159=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass160 : chunk 160=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass161 : chunk 161=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass162 : chunk 162=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass163 : chunk 163=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass164 : chunk 164=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass165 : chunk 165=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass166 : chunk 166=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass167 : chunk 167=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass168 : chunk 168=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass169 : chunk 169=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass170 : chunk 170=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass171 : chunk 171=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass172 : chunk 172=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass173 : chunk 173=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass174 : chunk 174=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass175 : chunk 175=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass176 : chunk 176=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass177 : chunk 177=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass178 : chunk 178=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass179 : chunk 179=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass180 : chunk 180=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass181 : chunk 181=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass182 : chunk 182=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass183 : chunk 183=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass184 : chunk 184=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass185 : chunk 185=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass186 : chunk 186=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass187 : chunk 187=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass188 : chunk 188=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass189 : chunk 189=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass190 : chunk 190=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass191 : chunk 191=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass192 : chunk 192=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass193 : chunk 193=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass194 : chunk 194=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass195 : chunk 195=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass196 : chunk 196=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass197 : chunk 197=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass198 : chunk 198=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass199 : chunk 199=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass200 : chunk 200=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass201 : chunk 201=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass202 : chunk 202=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass203 : chunk 203=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass204 : chunk 204=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass205 : chunk 205=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass206 : chunk 206=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass207 : chunk 207=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass208 : chunk 208=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass209 : chunk 209=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass210 : chunk 210=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass211 : chunk 211=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass212 : chunk 212=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass213 : chunk 213=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass214 : chunk 214=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass215 : chunk 215=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass216 : chunk 216=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass217 : chunk 217=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass218 : chunk 218=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass219 : chunk 219=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem pass220 : chunk 220=true := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem checked (i : Fin 221) : chunk i.val=true := by
  fin_cases i
  · exact pass0
  · exact pass1
  · exact pass2
  · exact pass3
  · exact pass4
  · exact pass5
  · exact pass6
  · exact pass7
  · exact pass8
  · exact pass9
  · exact pass10
  · exact pass11
  · exact pass12
  · exact pass13
  · exact pass14
  · exact pass15
  · exact pass16
  · exact pass17
  · exact pass18
  · exact pass19
  · exact pass20
  · exact pass21
  · exact pass22
  · exact pass23
  · exact pass24
  · exact pass25
  · exact pass26
  · exact pass27
  · exact pass28
  · exact pass29
  · exact pass30
  · exact pass31
  · exact pass32
  · exact pass33
  · exact pass34
  · exact pass35
  · exact pass36
  · exact pass37
  · exact pass38
  · exact pass39
  · exact pass40
  · exact pass41
  · exact pass42
  · exact pass43
  · exact pass44
  · exact pass45
  · exact pass46
  · exact pass47
  · exact pass48
  · exact pass49
  · exact pass50
  · exact pass51
  · exact pass52
  · exact pass53
  · exact pass54
  · exact pass55
  · exact pass56
  · exact pass57
  · exact pass58
  · exact pass59
  · exact pass60
  · exact pass61
  · exact pass62
  · exact pass63
  · exact pass64
  · exact pass65
  · exact pass66
  · exact pass67
  · exact pass68
  · exact pass69
  · exact pass70
  · exact pass71
  · exact pass72
  · exact pass73
  · exact pass74
  · exact pass75
  · exact pass76
  · exact pass77
  · exact pass78
  · exact pass79
  · exact pass80
  · exact pass81
  · exact pass82
  · exact pass83
  · exact pass84
  · exact pass85
  · exact pass86
  · exact pass87
  · exact pass88
  · exact pass89
  · exact pass90
  · exact pass91
  · exact pass92
  · exact pass93
  · exact pass94
  · exact pass95
  · exact pass96
  · exact pass97
  · exact pass98
  · exact pass99
  · exact pass100
  · exact pass101
  · exact pass102
  · exact pass103
  · exact pass104
  · exact pass105
  · exact pass106
  · exact pass107
  · exact pass108
  · exact pass109
  · exact pass110
  · exact pass111
  · exact pass112
  · exact pass113
  · exact pass114
  · exact pass115
  · exact pass116
  · exact pass117
  · exact pass118
  · exact pass119
  · exact pass120
  · exact pass121
  · exact pass122
  · exact pass123
  · exact pass124
  · exact pass125
  · exact pass126
  · exact pass127
  · exact pass128
  · exact pass129
  · exact pass130
  · exact pass131
  · exact pass132
  · exact pass133
  · exact pass134
  · exact pass135
  · exact pass136
  · exact pass137
  · exact pass138
  · exact pass139
  · exact pass140
  · exact pass141
  · exact pass142
  · exact pass143
  · exact pass144
  · exact pass145
  · exact pass146
  · exact pass147
  · exact pass148
  · exact pass149
  · exact pass150
  · exact pass151
  · exact pass152
  · exact pass153
  · exact pass154
  · exact pass155
  · exact pass156
  · exact pass157
  · exact pass158
  · exact pass159
  · exact pass160
  · exact pass161
  · exact pass162
  · exact pass163
  · exact pass164
  · exact pass165
  · exact pass166
  · exact pass167
  · exact pass168
  · exact pass169
  · exact pass170
  · exact pass171
  · exact pass172
  · exact pass173
  · exact pass174
  · exact pass175
  · exact pass176
  · exact pass177
  · exact pass178
  · exact pass179
  · exact pass180
  · exact pass181
  · exact pass182
  · exact pass183
  · exact pass184
  · exact pass185
  · exact pass186
  · exact pass187
  · exact pass188
  · exact pass189
  · exact pass190
  · exact pass191
  · exact pass192
  · exact pass193
  · exact pass194
  · exact pass195
  · exact pass196
  · exact pass197
  · exact pass198
  · exact pass199
  · exact pass200
  · exact pass201
  · exact pass202
  · exact pass203
  · exact pass204
  · exact pass205
  · exact pass206
  · exact pass207
  · exact pass208
  · exact pass209
  · exact pass210
  · exact pass211
  · exact pass212
  · exact pass213
  · exact pass214
  · exact pass215
  · exact pass216
  · exact pass217
  · exact pass218
  · exact pass219
  · exact pass220
end Front2778.Full.Flat
namespace Front2778.Full.Flat
open PEqualNP.Outside.L_meta_2778.Cert hiding inputs seed
theorem no_target (xs : List W) (bound : xs.length≤14) (legal : valid bases xs) : target∉bases++xs := by
  intro hit
  have past : Face.History [paidWord] :=
    Face.History.gate Face.History.empty (a:=raws.getD 0 zero) (b:=raws.getD 4 zero)
      (by decide +kernel) (by decide +kernel) true
  have supply : ∀w∈starting,w∈Face.seen [paidWord] := by
    intro w hw
    simpa [starting,Face.seen,Face.rawFull,raws,or_comm] using hw
  exact exclude (all_test checked) (id:=0) (by decide) (show remaining 0=14 from rfl)
    (by decide +kernel) past supply (beginning bound legal hit)
end Front2778.Full.Flat
end PEqualNP.Outside.L_meta_2778

theorem PEqualNP.Outside.L_meta_2778 : have x1 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))]; ∀ (x2 : List (BitVec (24 : ℕ))), x2.length ≤ (14 : ℕ) → (∀ (x4 : ℕ) (x5 : x4 < x2.length), x2[x4] ∉ x1 ++ List.take x4 x2 ∧ ∃ x6 ∈ x1 ++ List.take x4 x2, ∃ x7 ∈ x1 ++ List.take x4 x2, x2[x4] = x6 &&& x7 ∨ x2[x4] = x6 ||| x7) → (3428671 : BitVec (24 : ℕ)) ∉ x1 ++ x2 := by
  intro a xs size legal
  exact PEqualNP.Outside.L_meta_2778.Front2778.Full.Flat.no_target xs size legal
