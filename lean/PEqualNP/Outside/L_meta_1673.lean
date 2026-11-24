import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1673
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
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

lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
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

lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
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
lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

lemma run_bit (i) (g : Gate) (w : List Sig)
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

theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
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
open PEqualNP.CircuitLowerBounds
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
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

open PEqualNP.CircuitLowerBounds
def orSeed : Sig := bin true (inputs.getD 0 zero) (inputs.getD 1 zero)
theorem orTable : ∀ r : Row, bit r orSeed = (sample r 0 || sample r 1) := by decide +kernel
theorem orNonzero : orSeed ≠ zero := by decide +kernel
def orNeighbor (i : Fin 9) : Nat := [1,0,1,2,3,0,1,2,3].getD i.val 0
def orAbsent (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< orNeighbor i)
def orPresent (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< orNeighbor i))

theorem orWitness : ∀ i : Fin 9,
    (bit (orAbsent i) graph != bit (orPresent i) graph) &&
    ((inputs++[orSeed]).all fun w => w == inputs.getD i.val zero ||
      bit (orAbsent i) w == bit (orPresent i) w) = true := by decide +kernel

theorem or_all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[orSeed]) :
    S=inputs.toFinset ∨ S=(inputs++[orSeed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := orWitness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (orAbsent i) (orPresent i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : orSeed ∈ S
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

theorem or_initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[orSeed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = orSeed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (orTable r).symm)
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
    exact False.elim (orNonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = orSeed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = orSeed at headEq
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
    rcases or_all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)

theorem after_or (unused : Impossible graph 14 inputs.toFinset)
    (used : Impossible graph 14 (inputs++[orSeed]).toFinset) :
    ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C fan first computes
  by_contra! small
  obtain ⟨k,t,cap,hn | hy⟩ := or_initial_live C fan first computes (by omega)
  · exact unused k t cap hn
  · exact used k t cap hy
end PEqualNP.Outside.L_meta_1673
namespace PEqualNP.Outside.L_meta_1673.Adjacent
def aug (m : Nat) := vars m ++ [orSeed]
theorem forbid {raw T L cap} (h : Lower raw T L) (hp : proper T) (nd : List.Nodup raw)
    (gap : cap < L) : Impossible T cap raw.toFinset := by
  intro k t hk live
  have sub : supply (raw.map observe) ((raw.map observe).map (restrictRows id)) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    exact Or.inl hv
  have est := projected_bound id (list_run live raw nd rfl) (observe_proper hp) Reach.start sub h
  omega
theorem aug_of {m L hints} (base : Lower (vars m) (graphGoal m) L)
    (pG : proper (graphGoal m)) (nd : (vars m).Nodup)
    (ess : checkEssential (graphGoal m) (aug m) (graphPairs m hints) = true)
    (xs : (graphPairs m hints).map Prod.fst = vars m)
    (unused : Impossible (graphGoal m) (L-1) (aug m).toFinset) :
    Lower (aug m) (graphGoal m) L := by
  intro p bank reachable out
  by_contra! small
  obtain ⟨k,t,U,le,live,sub⟩ := reach_live pG reachable out
  have needed : (vars m).toFinset ⊆ U := by
    intro a ha
    obtain ⟨r,s,ne,iso⟩ := essential_ok ess a (xs.symm ▸ ha)
    exact raw_required live _ _ sub r s ne iso
  by_cases hor : orSeed ∈ U
  · have eq : U = (aug m).toFinset := by
      apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
      intro a ha
      have hv := List.mem_toFinset.mp ha
      simp only [aug,List.mem_append,List.mem_singleton] at hv
      exact hv.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hor)
    exact unused k t (by omega) (eq ▸ live)
  · have eq : U = (vars m).toFinset := by
      apply Finset.Subset.antisymm _ needed
      intro a ha
      have hv := sub a ha
      simp only [aug,List.mem_append,List.mem_singleton] at hv
      rcases hv with hm | rfl
      · exact List.mem_toFinset.mpr hm
      · exact (hor ha).elim
    exact forbid base pG nd (cap:=k) (by omega) k t (by omega) (eq ▸ live)
theorem cheap {m L} (sz : L ≤ (aug m).toFinset.card-1) (pos : 0<L) :
    Impossible (graphGoal m) (L-1) (aug m).toFinset := by
  intro k t le h
  have b := (live_size h).2
  omega
def augMapTest (m q z : Nat) :=
  let ms := fixRows z 0
  checkMap ms (aug m) (graphGoal m) (aug q) (graphGoal q) &&
    (movedWord ms (subcube z 0)==one) && properB (graphGoal q)
theorem augSlice {m q z L} (check : augMapTest m q z = true)
    (lower : Lower (aug q) (graphGoal q) L) :
    Slice (aug m) (graphGoal m) (subcube z 0) L := by
  simp only [augMapTest,Bool.and_eq_true,beq_iff_eq] at check
  exact slice_correct check.1.1 check.1.2 (proper_of _ check.2) lower
def relTest (m q : Nat) (ps : List Nat) := properB (graphGoal m) && properB (graphGoal q) &&
  checkMap (ps.map swapRows) (aug m) (graphGoal m) (aug q) (graphGoal q)
theorem augRelabel {m q L ps} (ok : relTest m q ps = true) (h : Lower (aug q) (graphGoal q) L) :
    Lower (aug m) (graphGoal m) L := by
  simp only [relTest,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h
theorem fullOrdinary : Lower (vars 511) (graphGoal 511) 15 := by
  have eq : vars 511 = inputs := by decide +kernel
  have tgt : graphGoal 511 = graph := by decide +kernel
  have dead := dead_start (before_sound known383 valid383) geomdead tablesdead
  apply lower_impossible (by rw [tgt]; exact graph_proper) _
    (by simpa only [eq,tgt] using dead)
  have chk : checkEssential (graphGoal 511) (vars 511) (graphPairs 511 0x321032101) = true := by decide +kernel
  have xs : (graphPairs 511 0x321032101).map Prod.fst = vars 511 := by decide +kernel
  intro a ha
  exact essential_ok chk a (List.mem_toFinset.mpr (xs.symm ▸ ha))
structure Protocol (S : Finset Sig) (T : Sig) where
  pick : Row → Row → Sig
  mem : ∀ r s, pick r s ∈ S
  diff : ∀ r s, bit r T=true → bit s T=false → bit r (pick r s) ≠ bit s (pick r s)
  cross : ∀ r s u v, pick r v=pick u s → pick r s=pick r v
def chooseSide (d : Bool) (a : Sig) (r s : Row) := if d then bit r a else !(bit s a)
theorem side_left {r s a b d} (yes : bit r (bin d a b)=true) (no : bit s (bin d a b)=false)
    (side : chooseSide d a r s=true) : bit r a=true ∧ bit s a=false := by
  cases d <;> simp_all [bit_bin,chooseSide]
theorem side_right {r s a b d} (yes : bit r (bin d a b)=true) (no : bit s (bin d a b)=false)
    (side : chooseSide d a r s=false) : bit r b=true ∧ bit s b=false := by
  cases d <;> simp_all [bit_bin,chooseSide]
def Protocol.binary {A B a b} (f : Protocol A a) (g : Protocol B b) (d : Bool)
    (dis : Disjoint A B) : Protocol (A∪B) (bin d a b) where
  pick r s := if chooseSide d a r s then f.pick r s else g.pick r s
  mem r s := by split <;> simp [f.mem,g.mem]
  diff r s hy hn := by
    split
    next eq => exact f.diff r s (side_left hy hn eq).1 (side_left hy hn eq).2
    next eq =>
      have e := side_right hy hn (Bool.eq_false_iff.mpr eq)
      exact g.diff r s e.1 e.2
  cross r s u v eq := by
    have sep (j k l m : Row) : f.pick j k ≠ g.pick l m := by
      intro same
      exact Finset.disjoint_left.mp dis (f.mem j k) (same ▸ g.mem l m)
    cases d
    · by_cases hv : bit v a=true <;> by_cases hs : bit s a=true <;>
        simp [chooseSide,hv,hs] at eq ⊢ <;>
        first | exact f.cross _ _ _ _ eq | exact g.cross _ _ _ _ eq |
          exact False.elim (sep _ _ _ _ eq) | exact False.elim (sep _ _ _ _ eq.symm)
    · by_cases hr : bit r a=true <;> by_cases hu : bit u a=true <;>
        simp [chooseSide,hr,hu] at eq ⊢ <;>
        first | exact f.cross _ _ _ _ eq | exact g.cross _ _ _ _ eq |
          exact False.elim (sep _ _ _ _ eq) | exact False.elim (sep _ _ _ _ eq.symm)
def Protocol.invert {A a} (f : Protocol A a) : Protocol A (neg a) where
  pick r s := f.pick s r
  mem r s := f.mem s r
  diff r s h j := by
    simp only [bit_neg,Bool.not_eq_true',Bool.not_eq_false'] at h j
    exact (f.diff s r j h).symm
  cross r s u v h := (f.cross s r v u h.symm).trans h.symm
def Protocol.single (a : Sig) : Protocol {a} a where
  pick _ _ := a
  mem _ _ := Finset.mem_singleton_self _
  diff _ _ h j := by simp [h,j]
  cross _ _ _ _ _ := rfl
structure Network (R S : Finset Sig) where
  support : Sig → Finset Sig
  built : ∀ a ∈ S, Nonempty (Protocol (support a) a)
  inside : ∀ a ∈ S, support a ⊆ R
  apart : ∀ a ∈ S, ∀ b ∈ S, a≠b → Disjoint (support a) (support b)
theorem Network.extend {R S U z H} (net : Network R S) (sub : U ⊆ S) (ins : H ⊆ R)
    (new : Nonempty (Protocol H z)) (sep : ∀ a ∈ U, Disjoint H (net.support a)) :
    Nonempty (Network R (insert z U)) := by
  let supp := fun w => if w=z then H else net.support w
  refine ⟨⟨supp,?_,?_,?_⟩⟩
  · intro a ha
    by_cases eq : a=z
    · subst a; simpa only [supp,ite_true] using new
    · simpa only [supp,eq,ite_false] using net.built a (sub ((Finset.mem_insert.mp ha).resolve_left eq))
  · intro a ha
    by_cases eq : a=z
    · simpa only [supp,eq,ite_true] using ins
    · exact (show supp a=net.support a by simp [supp,eq]) ▸ net.inside a (sub ((Finset.mem_insert.mp ha).resolve_left eq))
  · intro a ha b hb ne
    by_cases ea : a=z
    · subst a
      have eb : b≠z := Ne.symm ne
      simpa only [supp,ite_true,eb,ite_false] using (sep b ((Finset.mem_insert.mp hb).resolve_left eb))
    · have aU := (Finset.mem_insert.mp ha).resolve_left ea
      by_cases eb : b=z
      · subst b
        simpa only [supp,ea,ite_false,ite_true] using (sep a aU).symm
      · simpa only [supp,ea,eb,ite_false] using net.apart a (sub aU) b (sub ((Finset.mem_insert.mp hb).resolve_left eb)) ne
theorem tree_net {T k t S} (run : Live T k t S) (tight : k+1 ≤ S.card+t)
    {R} (net : Network R S) : ∃ H ⊆ R, Nonempty (Protocol H T) := by
  induction run with
  | stop hp => exact ⟨_,net.inside _ (by simp),net.built _ (by simp)⟩
  | @unary k t U a ha hf tail ih =>
    have zu : neg a ∉ U := fun h => hf (Finset.mem_insert_of_mem h)
    have hc := (live_size tail).2
    rw [Finset.card_insert_of_notMem zu] at hc
    have au : a ∉ U := by
      intro h; rw [Finset.insert_eq_of_mem h] at tight; omega
    rw [Finset.card_insert_of_notMem au] at tight
    have mem : a ∈ insert a U := Finset.mem_insert_self _ _
    obtain ⟨f⟩ := net.built a mem
    obtain ⟨new⟩ := net.extend (U:=U) (z:=neg a) (Finset.subset_insert _ _) (net.inside a mem)
      ⟨f.invert⟩ (fun b hb => net.apart a mem b (Finset.mem_insert_of_mem hb) (fun eq => au (eq ▸ hb)))
    apply ih _ new
    rw [Finset.card_insert_of_notMem zu]; omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    have zu : bin d a b ∉ U := fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have hc := (live_size tail).2
    rw [Finset.card_insert_of_notMem zu] at hc
    have au : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      have bound := Finset.card_insert_le b U
      omega
    have bu : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have bound := Finset.card_insert_le a U
      omega
    have ab : a ∉ insert b U := fun hh => (Finset.mem_insert.mp hh).elim hab au
    rw [Finset.card_insert_of_notMem ab,Finset.card_insert_of_notMem bu] at tight
    have ma : a∈insert a (insert b U) := Finset.mem_insert_self _ _
    have mb : b∈insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have sub : U ⊆ insert a (insert b U) := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    obtain ⟨f⟩ := net.built a ma
    obtain ⟨g⟩ := net.built b mb
    obtain ⟨new⟩ := net.extend (U:=U) (z:=bin d a b) sub (Finset.union_subset (net.inside a ma) (net.inside b mb))
      ⟨f.binary g d (net.apart a ma b mb hab)⟩ (fun c h => Finset.disjoint_union_left.mpr
        ⟨net.apart a ma c (sub h) (fun eq => au (eq ▸ h)),net.apart b mb c (sub h) (fun eq => bu (eq ▸ h))⟩)
    apply ih _ new
    rw [Finset.card_insert_of_notMem zu]; omega
theorem tree_protocol {T k t S} (run : Live T k t S) (tight : k+1 ≤ S.card+t) :
    ∃ H ⊆ S, Nonempty (Protocol H T) := by
  apply tree_net run tight
  exact ⟨fun a => {a},fun a _ => ⟨Protocol.single a⟩,
    fun a ha => Finset.singleton_subset_iff.mpr ha,fun _ _ _ _ h => by simpa using h⟩
def uniqueTest (T : Sig) (ws : List Sig) (p n : Row) (w : Sig) :=
  bit p T && !(bit n T) && ws.all (fun a => a==w || bit p a==bit n a)
theorem forced_pick {T ws p n w H} (f : Protocol H T) (inc : H ⊆ ws.toFinset)
    (pass : uniqueTest T ws p n w=true) : f.pick p n=w := by
  simp only [uniqueTest,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at pass
  exact (pass.2 _ (List.mem_toFinset.mp (inc (f.mem p n)))).resolve_right (f.diff p n pass.1.1 pass.1.2)
def downTest (T : Sig) (ws : List Sig) (r s : Row) :=
  bit r T && !(bit s T) && ws.all (fun w => !(bit r w) || bit s w)
theorem needs_inv {T ws r s k t} (run : Live T k t ws.toFinset) (pass : downTest T ws r s=true) : 0<t := by
  by_contra! h
  have no : t=0 := by omega
  simp only [downTest,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,Bool.or_eq_true] at pass
  obtain ⟨w,hw,x,y⟩ := mono_row_difference run no pass.1.1 pass.1.2
  have z := pass.2 w (List.mem_toFinset.mp hw)
  simp [x,y] at z
def smallField (bits shift : Nat) : Row := Fin.ofNat 512 (bits >>> shift)
def rectTest (T : Sig) (ws : List Sig) (k b : Nat) :=
  let a := ws.getD (b &&& 15) zero
  let w := ws.getD ((b >>> 4) &&& 15) zero
  let r := smallField b
  let n := ws.toFinset.card
  (decide (k+1 ≤ n) || (decide (k ≤ n) && downTest T ws (r 62) (r 71))) &&
    (a != w) && uniqueTest T ws (r 8) (r 17) a && uniqueTest T ws (r 44) (r 35) a &&
    uniqueTest T ws (r 8) (r 26) w && uniqueTest T ws (r 53) (r 35) w
theorem rect_sound {T ws k b} (h : rectTest T ws k b=true) : Impossible T k ws.toFinset := by
  intro m t le run
  simp only [rectTest,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,bne_iff_ne] at h
  have tight : m+1 ≤ ws.toFinset.card+t := by
    rcases h.1.1.1.1.1 with loose | ⟨bound,down⟩
    · omega
    · have := needs_inv run down
      omega
  obtain ⟨H,inc,⟨f⟩⟩ := tree_protocol run tight
  have p₁ := forced_pick f inc h.1.1.1.2
  have p₂ := forced_pick f inc h.1.1.2
  have q₁ := forced_pick f inc h.1.2
  have q₂ := forced_pick f inc h.2
  have e := (f.cross _ _ _ _ (p₁.trans p₂.symm)).trans p₁
  have z := (f.cross _ _ _ _ (q₁.trans q₂.symm)).trans q₁
  exact h.1.1.1.1.2 (e.symm.trans z)
def Apart (X A B : Finset Sig) := ∀ w ∈ A, w ∈ B → w ∈ X
theorem Apart.flip {X A B} (h : Apart X A B) : Apart X B A := fun w hb ha => h w ha hb
theorem Apart.join {X A B C} (a : Apart X A C) (b : Apart X B C) : Apart X (A∪B) C := by
  intro w hw hc
  exact (Finset.mem_union.mp hw).elim (fun h => a w h hc) (fun h => b w h hc)
structure PProc (X S : Finset Sig) (T : Sig) where
  pick : Row → Row → Sig
  mem : ∀ r s, pick r s ∈ S
  signs : ∀ r s, bit r T=true → bit s T=false → bit r (pick r s)=true ∧ bit s (pick r s)=false
  cross : ∀ r s u v, pick r v∉X → pick r v=pick u s → pick r s=pick r v
def PProc.single (X : Finset Sig) (a : Sig) : PProc X {a} a where
  pick _ _ := a
  mem _ _ := Finset.mem_singleton_self _
  signs _ _ h j := ⟨h,j⟩
  cross _ _ _ _ _ _ := rfl
def PProc.relax {A w} (f : PProc ∅ A w) (X : Finset Sig) : PProc X A w where
  pick := f.pick
  mem := f.mem
  signs := f.signs
  cross r s u v _ eq := f.cross r s u v (by simp) eq
def PProc.binary {X A B a b} (f : PProc X A a) (g : PProc X B b) (d : Bool)
    (ov : Apart X A B) : PProc X (A∪B) (bin d a b) where
  pick r s := if chooseSide d a r s then f.pick r s else g.pick r s
  mem r s := by split <;> simp [f.mem,g.mem]
  signs r s hy hn := by
    split
    next eq => exact f.signs r s (side_left hy hn eq).1 (side_left hy hn eq).2
    next eq =>
      have e := side_right hy hn (Bool.eq_false_iff.mpr eq)
      exact g.signs r s e.1 e.2
  cross r s u v fresh eq := by
    have sep (j k l m : Row) (same : f.pick j k=g.pick l m) : f.pick j k∈X :=
      ov _ (f.mem j k) (same ▸ g.mem l m)
    have sep' (j k l m : Row) (same : g.pick j k=f.pick l m) : g.pick j k∈X :=
      ov _ (same ▸ f.mem l m) (g.mem j k)
    cases d
    · by_cases hv : bit v a=true <;> by_cases hs : bit s a=true <;>
        simp [chooseSide,hv,hs] at eq fresh ⊢ <;>
        first | exact f.cross _ _ _ _ fresh eq | exact g.cross _ _ _ _ fresh eq |
          exact False.elim (fresh (sep _ _ _ _ eq)) | exact False.elim (fresh (sep' _ _ _ _ eq))
    · by_cases hr : bit r a=true <;> by_cases hu : bit u a=true <;>
        simp [chooseSide,hr,hu] at eq fresh ⊢ <;>
        first | exact f.cross _ _ _ _ fresh eq | exact g.cross _ _ _ _ fresh eq |
          exact False.elim (fresh (sep _ _ _ _ eq)) | exact False.elim (fresh (sep' _ _ _ _ eq))
structure MNet (R X S : Finset Sig) where
  support : Sig → Finset Sig
  built : ∀ a ∈ S, Nonempty (PProc X (support a) a)
  inside : ∀ a ∈ S, support a ⊆ R
  apart : ∀ a ∈ S, ∀ b ∈ S, a≠b → Apart X (support a) (support b)
def MNet.relax {R S} (net : MNet R ∅ S) (X : Finset Sig) : MNet R X S where
  support := net.support
  built a ha := (net.built a ha).map (fun f => f.relax X)
  inside := net.inside
  apart a ha b hb ne w h t := False.elim (Finset.notMem_empty w (net.apart a ha b hb ne w h t))
theorem MNet.extend {R X S U z H} (net : MNet R X S) (sub : U ⊆ S) (ins : H ⊆ R)
    (new : Nonempty (PProc X H z)) (sep : ∀ a ∈ U, Apart X H (net.support a)) :
    Nonempty (MNet R X (insert z U)) := by
  let supp := fun w => if w=z then H else net.support w
  refine ⟨⟨supp,?_,?_,?_⟩⟩
  · intro a ha
    by_cases eq : a=z
    · subst a; simpa only [supp,ite_true] using new
    · simpa only [supp,eq,ite_false] using net.built a (sub ((Finset.mem_insert.mp ha).resolve_left eq))
  · intro a ha
    by_cases eq : a=z
    · simpa only [supp,eq,ite_true] using ins
    · simpa only [supp,eq,ite_false] using net.inside a (sub ((Finset.mem_insert.mp ha).resolve_left eq))
  · intro a ha b hb ne
    by_cases ea : a=z
    · subst a
      have eb : b≠z := Ne.symm ne
      simpa only [supp,ite_true,eb,ite_false] using sep b ((Finset.mem_insert.mp hb).resolve_left eb)
    · have au := (Finset.mem_insert.mp ha).resolve_left ea
      by_cases eb : b=z
      · subst b; simpa only [supp,ea,ite_false,ite_true] using (sep a au).flip
      · simpa only [supp,ea,eb,ite_false] using net.apart a (sub au) b (sub ((Finset.mem_insert.mp hb).resolve_left eb)) ne
theorem MNet.fuse {R X S U a b d} (net : MNet R X S) (sub : U ⊆ S) (ma : a∈S) (mb : b∈S) (ne : a≠b)
    (left : ∀ u ∈ U, Apart X (net.support a) (net.support u))
    (right : ∀ u ∈ U, Apart X (net.support b) (net.support u)) :
    Nonempty (MNet R X (insert (bin d a b) U)) := by
  obtain ⟨f⟩ := net.built a ma
  obtain ⟨g⟩ := net.built b mb
  exact net.extend sub (Finset.union_subset (net.inside a ma) (net.inside b mb))
    ⟨f.binary g d (net.apart a ma b mb ne)⟩ (fun u h => (left u h).join (right u h))
theorem mono_finish {T k t S} (h : Live T k t S) (no : t=0) (tight : k+1 ≤ S.card)
    {R X} (net : MNet R X S) : ∃ A ⊆ R, Nonempty (PProc X A T) := by
  induction h with
  | stop hp => exact ⟨_,net.inside _ (by simp),net.built _ (by simp)⟩
  | unary ha hf tail ih => omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    have zu : bin d a b ∉ U := fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have hcard := (live_size tail).2
    rw [Finset.card_insert_of_notMem zu] at hcard
    have au : a ∉ U := by
      intro h; rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      have := Finset.card_insert_le b U; omega
    have bu : b ∉ U := by
      intro h; rw [Finset.insert_eq_of_mem h] at tight
      have := Finset.card_insert_le a U; omega
    have ab : a ∉ insert b U := fun hh => (Finset.mem_insert.mp hh).elim hab au
    rw [Finset.card_insert_of_notMem ab,Finset.card_insert_of_notMem bu] at tight
    have ma : a∈insert a (insert b U) := Finset.mem_insert_self _ _
    have mb : b∈insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have sub : U ⊆ insert a (insert b U) := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    obtain ⟨new⟩ := net.fuse (d:=d) sub ma mb hab (fun u hu => net.apart a ma u (sub hu) (fun eq => au (eq ▸ hu)))
      (fun u hu => net.apart b mb u (sub hu) (fun eq => bu (eq ▸ hu)))
    apply ih no _ new
    rw [Finset.card_insert_of_notMem zu]; omega
def SingleOn (R : Finset Sig) (T w : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ a ∈ R, bit p a ≠ bit n a → a=w
def Coherent (R X : Finset Sig) (T : Sig) := ∃ f : Row → Row → Sig,
  (∀ w ∈ X, ∀ p n, SingleOn R T w p n → f p n=w) ∧
  ∀ r s u v, f r v∈X → f r v=f u s → f r s=f r v
def TwoParts (R : Finset Sig) (T : Sig) := ∃ X, Coherent R X T ∧ Coherent R (R\X) T
theorem outer_part {R X A T} (f : PProc X A T) (inc : A ⊆ R) : Coherent R (R\X) T := by
  refine ⟨f.pick,?_,?_⟩
  · intro w _ p n h
    obtain ⟨a,b⟩ := f.signs p n h.1 h.2.1
    exact h.2.2 _ (inc (f.mem p n)) (by rw [a,b]; decide)
  · intro r s u v hw eq; exact f.cross r s u v (Finset.mem_sdiff.mp hw).2 eq
theorem no_parts {R A T} (f : PProc ∅ A T) (inc : A ⊆ R) : TwoParts R T := by
  apply Exists.intro ∅
  exact ⟨⟨fun _ _ => zero,by simp,by simp⟩,outer_part f inc⟩
theorem shared_part {R X S T k t v} (run : Live T k t S) (no : t=0) (net : MNet R ∅ S)
    (hv : v∈S) (hX : X=net.support v) : Coherent R X T := by
  subst X
  obtain ⟨f⟩ := net.built v hv
  refine ⟨f.pick,?_,fun r s u v _ eq => f.cross r s u v (by simp) eq⟩
  intro a ha p n h
  obtain ⟨w,hw,x,y⟩ := mono_row_difference run no h.1 h.2.1
  by_cases eq : w=v
  · subst w
    obtain ⟨x',y'⟩ := f.signs p n x y
    exact h.2.2 _ (net.inside v hv (f.mem p n)) (by rw [x',y']; decide)
  · obtain ⟨g⟩ := net.built w hw
    obtain ⟨x',y'⟩ := g.signs p n x y
    have key := h.2.2 _ (net.inside w hw (g.mem p n)) (by rw [x',y']; decide)
    exact False.elim (Finset.notMem_empty _ (net.apart v hv w hw (Ne.symm eq) _ ha (key ▸ g.mem p n)))
theorem parts_mono {T k t S} (run : Live T k t S) (no : t=0) (cap : k ≤ S.card)
    {R} (net : MNet R ∅ S) : TwoParts R T := by
  induction run with
  | stop hp =>
    obtain ⟨g⟩ := net.built _ (Finset.mem_singleton_self _)
    exact no_parts g (net.inside _ (by simp))
  | unary ha hf tail ih => omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    have zu : bin d a b ∉ U := fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have hc := (live_size tail).2
    rw [Finset.card_insert_of_notMem zu] at hc
    have ma : a∈insert a (insert b U) := Finset.mem_insert_self _ _
    have mb : b∈insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have sub : U ⊆ insert a (insert b U) := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
    have whole : Live T (k+1) t (insert a (insert b U)) := Live.binary ha hb hab hf tail
    by_cases au : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem au)] at cap
      have bu : b∉U := by intro h; rw [Finset.insert_eq_of_mem h] at cap; omega
      rw [Finset.card_insert_of_notMem bu] at cap
      let v := net.relax (net.support a)
      obtain ⟨z⟩ := v.fuse (d:=d) sub ma mb hab (fun _ _ _ h _ => h)
        (fun w hw => v.apart b mb w (sub hw) (fun eq => bu (eq ▸ hw)))
      obtain ⟨H,hH,⟨g⟩⟩ := mono_finish tail no (by simpa only [Finset.card_insert_of_notMem zu] using cap) z
      exact ⟨net.support a,shared_part whole no net ma rfl,outer_part g hH⟩
    · have ab : a ∉ insert b U := fun h => (Finset.mem_insert.mp h).elim hab au
      rw [Finset.card_insert_of_notMem ab] at cap
      by_cases bu : b∈U
      · rw [Finset.insert_eq_of_mem bu] at cap
        let v := net.relax (net.support b)
        obtain ⟨z⟩ := v.fuse (d:=d) sub ma mb hab (fun w hw => v.apart a ma w (sub hw) (fun eq => au (eq ▸ hw)))
          (fun _ _ _ h _ => h)
        obtain ⟨H,hH,⟨g⟩⟩ := mono_finish tail no (by simpa only [Finset.card_insert_of_notMem zu] using cap) z
        exact ⟨net.support b,shared_part whole no net mb rfl,outer_part g hH⟩
      · rw [Finset.card_insert_of_notMem bu] at cap
        obtain ⟨z⟩ := net.fuse (d:=d) sub ma mb hab
          (fun w hw => net.apart a ma w (sub hw) (fun eq => au (eq ▸ hw)))
          (fun w hw => net.apart b mb w (sub hw) (fun eq => bu (eq ▸ hw)))
        apply ih no _ z
        rw [Finset.card_insert_of_notMem zu]; omega
theorem sparse_parts {T k t S} (run : Live T k t S) (cap : k ≤ S.card) : TwoParts S T := by
  by_cases no : t=0
  · apply parts_mono run no cap
    refine ⟨fun a => {a},fun a _ => ⟨PProc.single ∅ a⟩,fun a ha => Finset.singleton_subset_iff.mpr ha,?_⟩
    intro a _ b _ ne w h j
    simp only [Finset.mem_singleton] at h j
    exact False.elim (ne (h.symm.trans j))
  · obtain ⟨H,le,⟨g⟩⟩ := tree_protocol run (by omega)
    refine ⟨∅,⟨fun _ _ => zero,by simp,by simp⟩,g.pick,?_,?_⟩
    · intro w _ p n h
      exact h.2.2 _ (le (g.mem p n)) (g.diff p n h.1 h.2.1)
    · exact fun r s u v _ => g.cross r s u v
theorem observed {T ws p n w} (h : uniqueTest T ws p n w=true) :
    SingleOn ws.toFinset T w p n := by
  simp only [uniqueTest,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at h
  exact ⟨h.1.1,h.1.2,fun a ha ne => (h.2 a (List.mem_toFinset.mp ha)).resolve_right ne⟩
def edgeFirst (ws : List Sig) (b : Nat) := ws.getD (b &&& 15) zero
def edgeLast (ws : List Sig) (b : Nat) := ws.getD ((b >>> 4) &&& 15) zero
def edgeOK (T : Sig) (ws : List Sig) (b : Nat) :=
  let a := edgeFirst ws b
  let w := edgeLast ws b
  let r := smallField b
  ws.contains a && ws.contains w && (a != w) &&
    uniqueTest T ws (r 8) (r 17) a && uniqueTest T ws (r 44) (r 35) a &&
    uniqueTest T ws (r 8) (r 26) w && uniqueTest T ws (r 53) (r 35) w
theorem opposite {T ws X b} (C : Coherent ws.toFinset X T) (h : edgeOK T ws b=true)
    (ha : edgeFirst ws b∈X) (hb : edgeLast ws b∈X) : False := by
  obtain ⟨f,one,cross⟩ := C
  simp only [edgeOK,Bool.and_eq_true,bne_iff_ne] at h
  have p₁ := one _ ha _ _ (observed h.1.1.1.2)
  have p₂ := one _ ha _ _ (observed h.1.1.2)
  have q₁ := one _ hb _ _ (observed h.1.2)
  have q₂ := one _ hb _ _ (observed h.2)
  have e := (cross _ _ _ _ (p₁ ▸ ha) (p₁.trans p₂.symm)).trans p₁
  have z := (cross _ _ _ _ (q₁ ▸ hb) (q₁.trans q₂.symm)).trans q₁
  exact h.1.1.1.1.2 (e.symm.trans z)
theorem flips {T ws X b} (C : Coherent ws.toFinset X T) (D : Coherent ws.toFinset (ws.toFinset\X) T)
    (h : edgeOK T ws b=true) : decide (edgeFirst ws b∈X) = !decide (edgeLast ws b∈X) := by
  have z := h
  simp only [edgeOK,Bool.and_eq_true,List.contains_eq_mem,decide_eq_true_eq] at z
  by_cases a : edgeFirst ws b∈X <;> by_cases e : edgeLast ws b∈X
  · exact False.elim (opposite C h a e)
  · simp [a,e]
  · simp [a,e]
  · exact False.elim (opposite D h (Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr z.1.1.1.1.1.1,a⟩)
      (Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr z.1.1.1.1.1.2,e⟩))
def loopOK (T : Sig) (ws : List Sig) (start cur : Sig) (odd : Bool) : List Nat → Bool
  | [] => (cur==start) && odd
  | b::xs => (edgeFirst ws b==cur) && edgeOK T ws b &&
      loopOK T ws start (edgeLast ws b) (!odd) xs
theorem no_loop {T ws X start cur odd xs} (C : Coherent ws.toFinset X T)
    (D : Coherent ws.toFinset (ws.toFinset\X) T)
    (key : decide (cur∈X) = if odd then !decide (start∈X) else decide (start∈X))
    (ok : loopOK T ws start cur odd xs=true) : False := by
  induction xs generalizing cur odd with
  | nil =>
    simp only [loopOK,Bool.and_eq_true,beq_iff_eq] at ok
    rw [ok.1,ok.2] at key
    cases h : decide (start∈X) <;> simp [h] at key
  | cons b xs ih =>
    simp only [loopOK,Bool.and_eq_true,beq_iff_eq] at ok
    apply ih _ ok.2
    have z := flips C D ok.1.2
    rw [ok.1.1,key] at z
    cases odd <;> cases h : decide (start∈X) <;> cases j : decide (edgeLast ws b∈X) <;> simp_all
def oddTest (T : Sig) (ws : List Sig) (k : Nat) : List Nat → Bool
  | [] => false
  | b::xs => decide (k≤ws.toFinset.card) && loopOK T ws (edgeFirst ws b) (edgeFirst ws b) false (b::xs)
theorem odd_sound {T ws k es} (ok : oddTest T ws k es=true) : Impossible T k ws.toFinset := by
  intro m t le run
  cases es with
  | nil => contradiction
  | cons b xs =>
    simp only [oddTest,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨X,C,D⟩ := sparse_parts run (le.trans ok.1)
    exact no_loop C D (by rfl) ok.2
end PEqualNP.Outside.L_meta_1673.Adjacent
namespace PEqualNP.Outside.L_meta_1673.Adjacent.Packed
structure Level where
  count : Nat
  regular : Nat
  offsets : Nat
  rulesLen : Nat
  linksLen : Nat
  childBits : Nat
  progWidth : Nat
  opsMeta : List (Nat × Nat)
  opDict : Nat
  ruleBits : Nat
  ruleDict : Option Nat
  data : Nat → Nat
def emptyLevel : Level := ⟨0,0,0,0,0,0,0,[],0,0,none,fun _ => 0⟩
def padded (n v : Nat) : Bits := BitVec.ofNat 768
  (if v &&& 1 == 1 then v ||| ((1 <<< 768)-(1 <<< n)) else v)
def sampleColumns (n : Nat) (a : Array (Nat × Nat)) :=
  a.map fun (x,y) => (padded n x,padded n y)
def unpackCol (x : Nat) : Bool × ColumnInfo :=
  (x.testBit 40,x &&& 511,(x >>> 9) &&& 511,(x >>> 18) &&& 511,(x >>> 27) &&& 511,(x >>> 36) &&& 15)
def colTree (bits : Nat) (total start : Nat) : Nat → IndexTree (Bool × ColumnInfo)
  | 0 => .leaf ((List.range (min 4 (total-start))).map fun i => unpackCol (bits >>> (41*(start+i))))
  | d+1 => .fork (4 <<< d) (colTree bits total start d) (colTree bits total (start+(4 <<< d)) d)
def decodeOps (palette : Nat) (input : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (width,base)::xs =>
    let code := (palette >>> (10*(base+(input &&& ((1 <<< width)-1))))) &&& 1023
    code ||| ((decodeOps palette (input >>> width) xs) <<< 10)
structure Chart where
  mask : Nat
  bound : Nat
  arity : Nat
  colBits : Nat
  samples : Array (Bits × Bits)
  cols : IndexTree (Bool × ColumnInfo)
  perms : Array (List Nat)
  levels : Nat → Level
  leaf : Nat → Nat → Nat
  cycles : Nat → Nat → List Nat
def pos (g : Chart) (i : Nat) := ((g.samples[i]?).getD (0,0)).1
def negRows (g : Chart) (i : Nat) := ((g.samples[i]?).getD (0,0)).2
def rootD (g : Chart) := rawDecor g.mask (pos g) (negRows g)
def getFields (data : Nat → Nat) (width : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,offset => packedAt data offset width :: getFields data width n (offset+width)
def readState (g : Chart) (k i : Nat) : Nat × List Decor × List Decor × List Nat × List Nat :=
  let level := g.levels k
  let d := g.bound-k
  let fields := level.progWidth+g.arity+d
  let nodeWidth := fields+level.rulesLen+level.linksLen
  let rw := if i<level.regular then nodeWidth else fields
  let offset := if i<level.regular then nodeWidth*i else nodeWidth*level.regular+(i-level.regular)*fields
  let row := packedAt level.data offset rw
  let coded := row &&& ((1 <<< level.progWidth)-1)
  let ops := if level.opsMeta.isEmpty then coded else decodeOps level.opDict coded level.opsMeta
  let bits := (ops <<< 10) ||| 272
  let mask := (row >>> level.progWidth) &&& ((1 <<< (g.arity+d))-1)
  let bank := decodeBank d bits (rootD g)
  let dirs := level.regular*nodeWidth+(level.count-level.regular)*fields
  let base := dirs+level.regular*level.offsets + packedAt level.data (dirs+i*level.offsets) level.offsets
  let nr := (row >>> fields) &&& ((1 <<< level.rulesLen)-1)
  let nl := row >>> (fields+level.rulesLen)
  let refs := getFields level.data level.ruleBits nr base
  let width := g.colBits+d
  let rules := match level.ruleDict with
    | none => refs
    | some dict => refs.map fun x => (dict >>> (x*width)) &&& ((1 <<< width)-1)
  (bits,bank,selectLive mask bank,rules,
    getFields level.data (level.childBits+12) nl (base+nr*level.ruleBits))
def stateWords (g : Chart) (k i : Nat) := ((readState g k i).2.2.1).map Prod.fst
def columnRoots (g : Chart) (extra : Bool) := if extra then aug g.mask else vars g.mask
def poolsFor (g : Chart) (depth ops : Nat) (bank : List Decor) (codes : List Nat) :=
  codes.filterMap fun ref => (g.cols.read (ref &&& ((1 <<< g.colBits)-1))).bind fun (extra,c) =>
    materialize (columnRoots g extra) (chosenSteps bank ops (ref >>> g.colBits) depth)
      (subcube c.1 c.2.1) c.2.2.2.2
def linksFor (g : Chart) (k : Nat) (codes : List Nat) (tag : Nat) :=
  let w := (g.levels k).childBits
  codes.filterMap fun ref =>
    if ref >>> (w+4) == (tag % 65521) % 256 then
      let i := ref &&& ((1 <<< w)-1)
      if i < (g.levels (k-1)).count then
        (g.perms[(ref >>> w) &&& 15]?).map fun ps =>
          (stateWords g (k-1) i).map (movedWord (ps.map swapRows).reverse)
      else none
    else none
def context (g : Chart) (k i : Nat) : NodeContext :=
  let (ops,bank,ws,rs,ls) := readState g k i
  (k,ws.length,ws,preCov ws,poolsFor g (g.bound-k) ops bank rs, linksFor g k ls)
def nodePass (g : Chart) (k i : Nat) :=
  let c := context g k i
  prelim (graphGoal g.mask) c && testAll c c.2.2.1
def GoodSamples (g : Chart) :=
  properPairs (graphGoal g.mask) (asRow (pos g)) (asRow (negRows g))
def GoodColumns (g : Chart) := ∀ r ∈ g.cols.values,
  Slice (columnRoots g r.1) (graphGoal g.mask) (subcube r.2.1 r.2.2.1) r.2.2.2.2.2
def GoodNames (g : Chart) := ∀ ps ∈ g.perms.toList, autoOK (graphGoal g.mask) (ps.map swapRows)=true
def checkedNames (g : Chart) := g.perms.toList.all (fun p => autoOK (graphGoal g.mask) (p.map swapRows))
def checkedRows (g : Chart) :=
  (chartSamples g.mask (pos g)==BitVec.allOnes 768) && (chartSamples g.mask (negRows g)==0)
theorem rows_sound {g : Chart} (ne : g.mask ≠ 1023) (pass : checkedRows g=true) : GoodSamples g := by
  simp only [checkedRows,Bool.and_eq_true,beq_iff_eq] at pass
  simpa only [GoodSamples,chartGoal,ne,ite_false] using chart_pairs pass.1 pass.2
theorem names_sound {g : Chart} (h : checkedNames g=true) : GoodNames g := List.all_eq_true.mp h
theorem pools_sound (g : Chart) (good : GoodColumns g) (depth ops bank codes) :
    ∀ c ∈ poolsFor g depth ops bank codes, ValidPool (vars g.mask) (graphGoal g.mask) c := by
  intro c hc
  obtain ⟨ref,_,eq⟩ := List.mem_filterMap.mp hc
  obtain ⟨⟨b,ci⟩,found,done⟩ := Option.bind_eq_some_iff.mp eq
  exact materialize_sound (raw:=columnRoots g b) (good (b,ci) (g.cols.read_mem found)) done
def ValidLevel (g : Chart) (k : Nat) := ∀ i < (g.levels k).count,
  Impossible (graphGoal g.mask) k (stateWords g k i).toFinset
theorem links_sound {g : Chart} (names : GoodNames g) (k codes) (prec : ValidLevel g (k-1)) :
    ∀ tag xs, xs ∈ linksFor g k codes tag → Impossible (graphGoal g.mask) (k-1) xs.toFinset := by
  intro tag xs hx
  obtain ⟨ref,_,hh⟩ := List.mem_filterMap.mp hx
  split at hh
  · dsimp only at hh
    split at hh
    next h =>
      obtain ⟨ps,hp,rfl⟩ := Option.map_eq_some_iff.mp hh
      exact rotate_excluded (prec _ h) _ (names _ (by simpa using Array.mem_of_getElem? hp))
    · contradiction
  · contradiction
theorem node_sound' {g : Chart} (pairs : GoodSamples g) (co : GoodColumns g) (names : GoodNames g)
    (k i) (prec : ValidLevel g (k-1)) (pass : nodePass g k i=true) :
    Impossible (graphGoal g.mask) k (stateWords g k i).toFinset := by
  have fg : ∀ v ∈ (readState g k i).2.2.1, faithful (asRow (pos g)) (asRow (negRows g)) v := by
    intro v hv
    apply decode_faithful _ _ _ _ _ (raw_faithful g.mask (pos g) (negRows g)) v
    exact (selectLive_sub _ _).subset hv
  simp only [nodePass,prelim,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at pass
  apply node_sound (raw:=vars g.mask) pairs fg pass.1.1 _ _ _ pass.2
  · simpa [context] using pass.1.2
  · apply pools_sound _ co
  · apply links_sound names _ _ prec
def Range (g : Chart) (k start n : Nat) := ∀ i, start ≤ i → i < start+n → nodePass g k i=true ∨ Impossible (graphGoal g.mask) k (stateWords g k i).toFinset
theorem mergeRange {g k start a b} (l : Range g k start a) (r : Range g k (start+a) b) :
    Range g k start (a+b) := by
  intro i lo hi
  by_cases v : i<start+a
  · exact l i lo v
  · exact r i (by omega) (by omega)
def front (g : Chart) (k start n : Nat) := ((List.range n).map (start+·)).map (context g k)
def headCheck (g : Chart) (k start n ar : Nat) :=
  (front g k start n).all fun c => c.2.1==ar && prelim (graphGoal g.mask) c
def rowCheck (g : Chart) (k start n ar lo len : Nat) :=
  let xs := front g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem row_at {g k start n ar lo len} (h : rowCheck g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (front g k start n)) (front g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem row_join {g k start n ar lo a b}
    (h : rowCheck g k start n ar lo a=true) (t : rowCheck g k start n ar (lo+a) b=true) :
    rowCheck g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact row_at h (lo+j) (by omega) (by omega)
  · exact row_at t (lo+j) (by omega) (by omega)

theorem all_rows {g k start n ar} (h : rowCheck g k start n ar 0 ar=true) :
    runBatch k ar (front g k start n)=true := by
  let xs := front g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := row_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem range_ok {g k start n ar} (hh : headCheck g k start n ar=true)
    (h : rowCheck g k start n ar 0 ar=true) : Range g k start n := by
  intro i lo hi
  let xs:=front g k start n
  have hm : context g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,eq⟩ := List.getElem_of_mem hm
  have head := List.all_eq_true.mp hh _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at head
  have hk : xs[q].1=k := by rw [eq]; rfl
  have ha : xs[q].2.1=ar := eq ▸ head.1
  have hn : xs[q].2.2.1.length=ar := by rw [eq]; exact head.1
  exact Or.inl (Bool.and_eq_true_iff.mpr ⟨head.2,eq ▸ runBatch_at hq hk ha hn (all_rows h)⟩)
def rowParts (g : Chart) (k start n ar off num : Nat) : Nat → Prop
  | 0 => rowCheck g k start n ar off num=true
  | j+1 => rowParts g k start n ar off (num/2) j ∧ rowParts g k start n ar (off+num/2) (num-num/2) j
theorem rowParts_ok {g k start n ar off num depth} (h : rowParts g k start n ar off num depth) :
    rowCheck g k start n ar off num=true := by
  induction depth generalizing off num with
  | zero => exact h
  | succ d ih =>
    have v:=row_join (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
theorem done {g : Chart} (s : GoodSamples g) (c : GoodColumns g) (a : GoodNames g)
    (any : ∀ k, Range g k 0 (g.levels k).count) (zero : (g.levels 0).count=0) :
    ∀ k, ValidLevel g k := by
  intro k
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    rcases any (k+1) i (by omega) (by omega) with pass | closed
    · exact node_sound' s c a (k+1) i (by simpa using ih) pass
    · exact closed
def prior (q : Nat) := if q=511 then 15 else if q=111 then 7 else boundsBefore known383 q
theorem prior_ok (q : Nat) : Lower (vars q) (graphGoal q) (prior q) := by
  by_cases h : q=511
  · subst q
    exact fullOrdinary
  · by_cases s : q=111
    · subst q
      exact low111
    · simpa only [prior,h,s,ite_false] using before_sound known383 valid383 q
def checkColumns (g : Chart) := g.cols.values.all fun (b,z,o,q,s,L) =>
  if b then (o==0) && augMapTest g.mask q z
  else colCheck g.mask (z,o,q,s,L) prior
def needs (g : Chart) := g.cols.values.filterMap fun (b,z,o,q,s,L) =>
  if b then some (q,L) else none
def Permitted (ob : List (Nat × Nat)) := ∀ pair ∈ ob,
  Lower (aug pair.1) (graphGoal pair.1) pair.2
theorem columns_ok {g : Chart} {ob : List (Nat × Nat)} (ne : g.mask ≠ 1023)
    (pass : checkColumns g = true) (deps : Permitted ob)
    (inOb : (needs g).all ob.contains = true) : GoodColumns g := by
  rintro ⟨b,z,o,q,s,L⟩ row
  have valid := List.all_eq_true.mp pass _ row
  cases b
  · have v : colCheck g.mask (z,o,q,s,L) prior=true := valid
    simpa only [columnRoots,Bool.false_eq_true,ite_false,chartGoal,ne] using
      col_sound (m:=g.mask) (z,o,q,s,L) prior prior_ok v
  · have v : ((o==0) && augMapTest g.mask q z) = true := valid
    simp only [Bool.and_eq_true,beq_iff_eq] at v
    have pair : (q,L) ∈ needs g := List.mem_filterMap.mpr ⟨_,row,rfl⟩
    have known : (q,L) ∈ ob := by simpa using List.all_eq_true.mp inOb _ pair
    rw [v.1]
    exact augSlice v.2 (deps _ known)
def localLeaf (g : Chart) (k i : Nat) := match g.cycles k i with
  | [] => rectTest (graphGoal g.mask) (stateWords g k i) k (g.leaf k i)
  | b::xs => oddTest (graphGoal g.mask) (stateWords g k i) k (b::xs)
theorem localLeaf_ok {g k i} (h : localLeaf g k i=true) :
    Impossible (graphGoal g.mask) k (stateWords g k i).toFinset := by
  unfold localLeaf at h
  split at h
  · exact rect_sound h
  · exact odd_sound h
def endsAt (g : Chart) (k s n : Nat) := (List.range n).all fun x => localLeaf g k (s+x)
theorem ends_ok {g k s n} (passed : endsAt g k s n=true) : Range g k s n := by
  intro i lo hi
  have q := List.all_eq_true.mp passed (i-s) (List.mem_range.mpr (by omega))
  have e : s+(i-s)=i := by omega
  rw [e] at q
  exact Or.inr (localLeaf_ok q)
def pieces (g : Chart) (k start n ar rows : Nat) : Nat → Prop
  | 0 => match ar with
    | 0 => endsAt g k start n=true
    | a+1 => headCheck g k start n (a+1)=true ∧ rowParts g k start n (a+1) 0 (a+1) rows
  | d+1 => pieces g k start (n/2) ar rows d ∧ pieces g k (start+n/2) (n-n/2) ar rows d
theorem pieces_ok {g k start n ar rows depth} (h : pieces g k start n ar rows depth) :
    Range g k start n := by
  induction depth generalizing start n with
  | zero =>
    cases ar with
    | zero => exact ends_ok h
    | succ a => exact range_ok h.1 (rowParts_ok h.2)
  | succ d ih =>
    have q := mergeRange (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using q
theorem chartRoot {g : Chart} {ob : List (Nat × Nat)} {hints : Nat}
    (hz : g.mask ≠ 1023) (data : checkedRows g=true) (cols : checkColumns g=true)
    (deps : Permitted ob) (inOb : (needs g).all ob.contains=true)
    (ns : checkedNames g=true) (any : ∀ k, Range g k 0 (g.levels k).count)
    (zz : (g.levels 0).count=0) (ix : 0 < (g.levels (g.bound-1)).count)
    (roots : sameWords (stateWords g (g.bound-1) 0) (aug g.mask)=true)
    (e : prior g.mask = g.bound) (hp : properB (graphGoal g.mask)=true)
    (nd : (vars g.mask).Nodup)
    (es : checkEssential (graphGoal g.mask) (aug g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (aug g.mask) (graphGoal g.mask) g.bound := by
  have root := done (rows_sound hz data) (columns_ok hz cols deps inOb) (names_sound ns) any zz _ 0 ix
  apply aug_of (e ▸ prior_ok g.mask) (proper_of _ hp) nd es all
  rw [←sameWords_sound roots]
  exact root
abbrev Ticket := Nat × Nat × Nat × Nat × Nat × Nat
def reports (g : Chart) : List Ticket → Prop
  | [] => True
  | (k,off,num,ar,rows,d)::more => pieces g k off num ar rows d ∧ reports g more
theorem reports_join {g a b} (h : reports g a) (j : reports g b) : reports g (a++b) := by
  induction a with
  | nil => exact j
  | cons w xs ih =>
    obtain ⟨k,off,num,ar,rows,d⟩ := w
    exact ⟨h.1,ih h.2⟩
def sections (jobs : List Ticket) (k : Nat) := jobs.filterMap fun (n,s,l,_,_,_) =>
  if n=k then some (s,l) else none
theorem section_range {g xs k y} (checked : reports g xs) (hy : y ∈ sections xs k) :
    Range g k y.1 y.2 := by
  induction xs with
  | nil => simp [sections] at hy
  | cons a xs ih =>
    obtain ⟨n,s,l,ar,rows,d⟩ := a
    by_cases eq : n=k
    · subst n
      simp only [sections,List.filterMap_cons,ite_true,List.mem_cons] at hy
      rcases hy with rfl | ht
      · exact pieces_ok checked.1
      · exact ih checked.2 ht
    · simp only [sections,List.filterMap_cons,eq,ite_false] at hy
      exact ih checked.2 hy
def continuous (s : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (a,n)::rest => (a==s) && continuous (s+n) rest
def lengths (ls : List (Nat × Nat)) := (ls.map Prod.snd).sum
theorem sections_ok {g k s xs} (next : ∀ v ∈ xs, Range g k v.1 v.2)
    (ordered : continuous s xs=true) : Range g k s (lengths xs) := by
  induction xs generalizing s with
  | nil => intro i lo hi; simp [lengths] at hi; omega
  | cons v xs ih =>
    obtain ⟨a,n⟩ := v
    simp only [continuous,Bool.and_eq_true,beq_iff_eq] at ordered
    obtain ⟨ha,tail⟩ := ordered
    subst a
    apply mergeRange (next (s,n) (by simp))
    exact ih (fun v hv => next v (List.mem_cons_of_mem _ hv)) tail
def complete (g : Chart) (jobs : List Ticket) := (List.range g.bound).all fun k =>
  let xs := sections jobs k
  (lengths xs == (g.levels k).count) && continuous 0 xs
def cutoff (bound : Nat) (f : Nat → Level) (k : Nat) := if k<bound then f k else emptyLevel
theorem finished {g : Chart} {xs} (checked : reports g xs) (exhaust : complete g xs=true)
    (outside : ∀ k, g.bound ≤ k → (g.levels k).count=0) :
    ∀ k, Range g k 0 (g.levels k).count := by
  intro k
  by_cases h : k<g.bound
  · have ok := List.all_eq_true.mp exhaust k (List.mem_range.mpr h)
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    rw [←ok.1]
    exact sections_ok (fun v hv => section_range checked hv) ok.2
  · rw [outside k (by omega)]
    intro i _ hi
    omega
def w511k9 (i : Nat) : Nat := 0x28f7a3aa1617f7c542a2fead67537ad1e4ca8bfab8e4cddb19898afb421041f74822022bdd278145fd8890109b669f3b953ad1d312ae5a3a224d9e4f9e39b6c9f3b736e93e74f1ee4354065dc86280cdb90b501cb71d6a03a6e36d4057d88b280cfb106501cf61cca03aec3594076d863280cfb0665019bb2168039763ad0074ec6da00cf990a401cf31d4803ae63690076cc65200afa915701cf51cae03aea355c076d462b80efa075701cf91c8e03af2351c076e462380ef88b47015f622a0033ec4140073d872800ebb0d5001db618a002bf44500067e882000e7d0e4001d7a1a8003b743100077d02c800efc049001df2082002dda241c86bd886810e7b0fd0219f62000436ec4300879d876010dfa109021df41f2043de83a4087bd004810efa009021f741b2043f68324085dd80b810
def leaf511k9w (i : Nat) : Nat := 0x200023000460001000148000ae6005ca04b50167c826a43b80071000e20019a3333466668ccb0169602c2c058e5a3230122a6a44cd48f9aae5265ce6a29cd4833871633e30e1419c38b19f1870a10e142c058e5a363013a202744d44b19f5870ba0e1741c2e161714c2c3549d830af3615c680e29018590fac405e680ba185b420373306d0f261a6a70cd4eaa99e52639a6ad14d4419a88d355226aa454d5093291350c00b8
def leaf511k9 (i : Nat) : Nat :=
  let row := packedAt leaf511k9w ((i-0)*19) 19
  (((0x8786858481767572716560544310 >>> (8*((row) &&& 15))) &&& 255)) ||| (((0x2050483249149a28120b048281609044271200406221209c44051388802230900426051209c0a221380882430100406011108c0212098040403 >>> (27*((row >>> 4) &&& 31))) &&& 134217727) <<< 8) ||| (((0x185c4e0669158a45a2b14361a8d06a361a0d4693418c844129844245228940a2522810c84412118c8242219047436190e85a2a1d0a45438160a06c3a190b4742a148e854160a850261a090341609 >>> (27*((row >>> 9) &&& 31))) &&& 134217727) <<< 35) ||| (((0x2090848271208c48031109c44231100c28130904c120c0289c080c0101804030088c02210084c020c0080c0000 >>> (18*((row >>> 14) &&& 31))) &&& 262143) <<< 62)
def w511k10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x35fc7274031feb264034feb244038feae44035deb234039deae3403cdea634033fab26203bf87262035fab252039faae5202dfa7a52036fab24203afaae4203cfaaa4202dfa0de2037f2b22203bf2ae2203df2aa2203ef2a62202dfa0db202dfab502035fab102035fa1502039faad0203cfaa50202fdab4a2037dab0a203bdaaca203ddaa8a203edaa4a2027fc804683afcae46836fc0a4683cfcaa46827fc152683bdcae36837dc0a3683ddcaa3683edca63683bf4ae26837f40a2683df4aa2683ef4a62683fd4a22682dfcb506839fcad0683cfca50683ddca10682ff8b49683bf8ac96837f8089683df8a89683ef8a49683ff09c9683df8349683fd8249683afcae4003cfcaa4003bdcae3003ddcaa3003edca630027fcb5d0033fcadd0035fca9d0036fca5d0037f875d0037dcb5d0037dc8dd0037dc49d0037dc3dd0037dc79d0037dc5d10037dc5ce0037ec49c0037ec3dc0037ec45c0037ec39c0037ec31c003bf4ae2003df4aa2003ef4a62003fd4a220037f45e20037dc5d40037ec5940037dc5d00037ec5900037dc5cd0037ec58d0037dc5ca0037ec58a002ff8b49003bf8ac9003df8a89003ef8a49003ff09c9003fd82490032fe0a41c33f60a21c31fe0901c2fdab491c37dab091c3bdaac91c3ddaa891c3edaa491c3fd29c91c33fcb261c39fcae51c37f4b221c3bf4ae21c3bf40a21c37f40a21c3df4aa21c3ef4a621c2bfc11b1c27fc1541c2ff8b5a1c37f8b1a1c3bf8ada1c3bf811a1c37f809a1c3df8a9a1c3df80da1c3ef8a5a1c3ff09da1c32fe0a41033de0a31033fa089103afaae4083cfaaa40837f2b22083bf2ae2083df2aa2083ef2a62083fd2a22082dfab500835fab100839faad0083cfaa50083ddaa10082ff8b460837f8b06083bf8ac6083df8a86083ef8a46083fd8a0608019ff5c10960f1ff0a525829fdc528c1327fe14a28039ff85589007ff22ca0800ffe0c18200a5fb767658287fe59d06565ef7e7418287fc599060a3fe6c42582a7dde04967a5ef7e74115a5fe29904325fb150310387fc549720a4ff8e741438dfe210950fed630a2842fbd0a18a10a5bf867480297edd9d000a1ff1564002ff60714600a7ee7e70c0dff48924300bff01850c029efa19d200a77e8a75c029fb9f9d60067fc72758029fb9f9d00067fa767400297f8559000ffd22ca200a9efa19cb033fd87891c0fff60b24700b7da5c91002ff60820400f5fa5d00801bfe201820077f85c60802ffc101820728ef7e67a5b96ee19d2b6e5eb7e742db96fa19d2a927dcb5d0024cf72b74008f5dca9d002cdb7297400f37d875d001c9fb2d7000933ecadc0023d7b2a7000d36eca5c002cdf3287000af7d45e2002bdf9168800d37d85c9003cdfa162400367ec7c41c3cbf62d2470bfbd8ac91c1cdf6022470bbdd8a891c3dff4272470 else 0x8674aedbb8674aedf97274af4fb8e74af5bb8674ae5fb8274ae5fb7a74af5f97274ae5fb7274af5fa6e74aeddb7a576edf38e572edf382572fcf3aa472edf3b5272fdd3aa372fed3a6372e7eb7e742edeb7e742e5fb8e742e5fb82742f5eb7e742f5f37a742f5f972742f5fa6e742f4fbb2442f5dbb2342fcdba6342e5fbb5f36e5fb80336f5db66336f5db06336ecfd7267a28ff7a67a38fd7267a28ff7267a38fe6e67a2df57267229f78e67229f78267239f37667239f57267229f77267239f66e67238f7ae47239d7ae3723cd7a637228ff8c381a9fb74381b0ff8e765b1fd72765b1fe6e765a9df92675a9df12575a9df78175a9f7b5771a9f780171b9d74e371b9d702371b1df0a341ab778a67129f78c17138f70247131fd72764b1fe6e764a9dfb5774a9df8c174b8df4e474b8df02474b0ff6a444a7be8674aadbe8674ab5be8674aa5fe8274aa5fe7a74aa5fe7674ab5fc7274abcdeaa476addeb5276b1fe09b46bcf6aa472adf6b5272bdd6aa372bed6a6372bdd63e372adf6b5172b9f611172a5fe8e742a5fe82742b5ee7e742a5fe76742b1feb0442b4feb2442b8fe0a442b5deb2342b9de0a342bcdea6342a5feb5f36b1fe11f36b5de66336a5fe92726a5fe16526a5feb5f26b1fe11f26a5fe15226bcfaaa46eadfab526ebddaaa36ebedaa636ebdda3e36eadfab516eb9fa1116ebcfaa516ebdf2aa26ebef2a626ebdf23e26ebfd2a226ebdf23a26eadfab506ebcfaa506ebddaa106eadfa90d6eadfa90a6eb4feb243eb5deb233ebcdea633eb5f6b223ebcf6a623ebdd6a223ea5fe92732a5fe16532a5feb5f32b1fe11f32b5de66332b5f666232a5fe15032a77e8a722a5feb5f22b1fe11f22b4fe66422a5fe99222b5f666222a5feb5f16b4fe66416a5fe99216b5de66316a5fe99116bef4a626aadfcb506abcfca506aadfc90d6abef8a616abdf83e16abfd8a216abff09e16abdf83616abcfca4f6abddca0f6abdf49cf6aadfc90c6aadfc9096aadfc9076aa9fd7267d6bf5726716bf97266d73f50a26973f90a16977e95a10173ed593016aef7e6786bcf7e67465f7152246beb7e66c69fb9166c6bed7e66867f6146286afd726782bdd7267439dd1c35c2bf57267029f79167031df6635823fd8046832fd0a46831fd0926833dd0a36833f50a26827ddb5d0036dda5d0033dd49d0035dd3dd0037d975d0037dc6dd0033dd5d50036eda5c0033ed49c0037cda1c0033ed45c0037d55e20033dd5d40037e9589002fec7c2282fdc800282fec7c0282fec7c0182fdc8000c2efc726783afc7267838feae5782cfe7a5782fdc726743bdc7267439deae5742dde7a5743adeae4743cdeaa4742ff4726703bf47267039f6ae5703af6ae4703cf6aa4703bd6ae3703dd6aa3703ed6a637031fe9674035ee7e74035f67a74035fa76740) else (if i<3 then 0x8237f8a75c23fd7275c21ffb5f5821ff9202427fa7676027fc7276027fa7674827fc7274827fc7275c2dee7e7402ff8726203dda3491c3fd87091c3fd820b1c3fd845a1c37f855a1c3fd8ac91c3fd80891c3fd8a891c3fd89091c3fd85491c3fd84091c3fd83491c31ff3188271ffada7de5ff7a74a25ff8e74231ff05881a9ff8267da9ff7a67db1ffadd7db4ff2dd7da9ffb5705b1ff4dd05b1ff4db05a5ffb5d05a5ff71d05a5ff6dd05abdf8265db1ffac35db4ff2c35db1ffb015db1ff68145adfe6e745a5ff6e745b1ffb2645a9ff7a645a9ff0d559a7ef7e741a3ff80441b1ff09141a5ff82741a9ff80441a3ff9a625a5ff90425a7ef7c425a7fe6c425a9ff80151b1ffb014da9ff8014db1ffadb7d25ff8c35931ff0565927ef7e74127fb767412b7f8a6412def7e74125ff8e74135ef7e74135fb7674131ffb264129ff8c44131ff09e412b7f8a63525ffb5f3531ffadf3531ff11f3531ffac33531ffb01352dfb7a5312dfb0d43127fb150312dfbb503135fb150313ddba8a3135fb0583131ffade7cb1ffadd7cb1ff49d7ca77f8a75ca5ff8c35cb1ff4835cab7f8a75ca3ff8e75cb37f8a75cb1ffb255ca9ff8e55ca9ff8c35cb1ff05e5cb1ffb125cb1ff0595cb1ff0585cadfe6e744a5ff8e744a5ff6e744b1ffb1644a9ffb5738b1ffb1738b1ffb0138a5ff7674169ff7664163ff744257cdfa8e257ede3182569ff7a63d69ff10a3d7cdf30a3d677f8a7216bdf826216bdf10a216bfd7261571ff68330e3ff7676065ff7674863ff8e75c63ff7675c6bef7e6386df7743247dd7a8e247dd730a3c67f77a7306bef7e63063ff15530677f8a7206bef7e62069ff916207dd7a8a207dd70ca2077d760a207bd748a207dd73ca207fd324c206bef7e62c7fd6249287ff41852863ff7a76025ff7a74823ff8e75c23ff7a75c2bfd7263825ff8e7402bfd7263429ff915342bfd7262431ff6832425ff152243ddba8a203ddb0ca203bdb48a203ddb3ca203fd32ca203fda6ca2027fe7a7283ede30a283fda249283ff8185283ff8185183df60ca0c3fd630a0c27fe7a74827fe8e75c27fe7a7382ffc7263827fe8e75827fe14e5827fe8e74027fe14e402dfeb4e402dfe14e402ffc7263427fe8e7242ffc7262427feb5e2427fe152242ffab4d203fdab4a203fda10a203fdaa8a203fda90a203fda0ca203fda8ca203fda3ca203fda70a2037fab092c3dfa3492c3fda2492c3fda2c91c2ffcb4d1c3ff82da1c37fa609103ff820b102ffab4d0837fa5cd082ffab4a082ffa8ca083ff870a082cf77657b2aef7e67a71fead88279e759b8279f55598279ee5988279f65588279fc5188271fe518826cef7e67a6cfe6e67a68ff8267a78ef7e67a78f77a67a68ff7667a78fd7267a78fe6e67a68ff6e67a71fe6e765ecfb8257aecfb7a57ae7bb else 0xd18d13921c460fdd264851d243e2c02f669c8c2145dc11811c936e8d3835209a918427308b177069154295dcf600883210e90a7ae2675140345258f08d120058708a6726d69052794805e9d48953394ee03e7a885ab621d48652214ce52a6729520548b7f2f141e8650d40005b62cc13c1e0ba508c4664a00ae3ea84873c815075f760ebf49baa13ba74823eee0769a0da489cd19ef2ec1d199388a0734a7bb3306fae0e1341b53a0f0181aee023c00664c0d2387a33c181aac822f505c7a0ca3992e59a8108302d4e0624c0d27963b400b13818e00333d06426082387a33e80161682b0605af00bfd4173b030cb03f1e8c12dc60564813e902a9e38e97ed04c5a0a53409ac01e8e64b963e050bc049a40e868259e58e9f028f80225a0a40c0e53824d20551e1859fda09b0c0dd38249204e1a0963c30b3da810ee023590459607c4c1040933f0c0d8181c6903a4603d600f401d3d7c0be881a2e0329c0609008040168146416f8023c605578094d80e2d0289a04c8c07c00a5a56490da45874d2fea4315083ff90aba013520332c053f807a54438b9000a2a02dd0836d008a90194a8c5302cb46b20072c4132c05522e58c931088520574027680458002a544c16171a4002d9003eb00c94007d402580027f00f4a2c4851bafbaa7a6f9b395f94394390b8d37af77773f70757b45739b34730f2bb26722f1f71bf18714f11703f006fcef96f5ef42f0aeeeeb6e62dded22c12bdaba2b4eb32b16ade98a85271a5e24422a211df31cadb599b98355fd411241070e38bb4adc8586184c42a00031efa9c8269ef7e64a71efadc8271ef61c8271ef5dc8271ef59a8271ef5988265f77a76269ef7e66269ef7e65e69ef7e65669fe6e765f1ef7e765e1ff76765e1ff6e765e5bf8674a25ef7e74229fd7266225fb7675a24ff8c381a5fb74381a1ff9047da1ff8047da1ff7047da1ff6c47db1bf86765a1ff7a765a1ff72765a1ff6e765a1ff80441a1ff90425a1ff98125a9df80125a97f8a67d21ffb5b0521ff9674125fb7674121ff1664121ff9433521ff9813521ff82764b1ef7e764a1ff72764a1ff9275ca37f8a75ca1ff1655ca1ffb6044a1ff99738a1ff98138a37f8841169ef7e67c63fd7276061ffb5f6065bf8674865f77a74869ef7e64863fd7275c65fe6e74469ef7e64469ef7e63c63fd7276021ffb5f6025fb7674829fd7264))
def leaf511k10w (i : Nat) : Nat := (if i<1 then 0x8c801950b2826861193880193880003880000c800038801938b2953861193880003880003880006480002880005080008c80196861191d80001d80001d800038800038d0003880003980001d8000382a963980003980008c80196861191c80001d80001c80001d800050800024b94127010d27010d24c11325c11324611307201e24b20127010d24c11924b20e27010d24b20e24b20e27010924c10d24c11925c11324c11325c10d24611325c11325c10d25c11925c10d25c11925c10925c11325c11925c10d24611324611324c11324c1192461132493ce27010d2493ce2493ce27010924c10d24c11924c10924b21824b21827010924b21824c10925c10d25c10925c10925c10d24c10d24610d24610d24610924610d24610924610925711325711324611324611924610d24610d257113a05a0224611324611924610d24611324610d24611324610d24611324610d24611310b21305d01811d01211d0181093d31320121093d310b21f11d0121080121080121080121080181080181080183541d43941ce2961581141ce11615815615743328150b2821cb28248014170949529d00010b28148159950b2811cb28199e81438b2943880001c800010b28110b28113201910b28110b29423a28193a28193a28193a28192275293a28091e80e93a2819332811fa2819122813ba29492151993949443a28093a28093a28093a28092151e53a28027a28027a28179c10d1fa28027a28027a28179c10d27a2817ba2813ba29327a28d27a28e27a28e3ba28e27a28e3ba28e3ba28e69c11979c10d3dc10d79c10d31d01e25c11379c10d25c11979c10d25c1191dc10927949a27948d5f949a27948e7a310d5b949a27948e7b948e79710d1b949f27a2983ba2983ba29879710d7a310d5e310d9e310d2631195231094d088e61088e25089a79088a51088a13a28013a28013a28013a28013a28013a28013a28013a28013a28013a29313a29313a29313a29313a29311d01811c11e11d01211d01213949913949313949313949313949313a29f11f0121108896fa2807ba2806fa2807ba2801fa28013a2807fa28083a28093a28093949993a28093a28092b35791b0d892151891b0de93a2809192d79110989192d79110989110983ba2933ba2933ba2933ba2933ba29392b35d9192dd91b0de91109e91b0de91109e91351e91109e5b94998b94937b94939394933ba29f90e8896e52013a52146fa2815aa49a4ea49426a4947aa49452a4943a629f13a28027a28013a29327a2933a52133ba29383a2933ba2936c459f9134df5b94994794932f94936e068a94754d8794937834535394933ba29f6c45996c45996c45992f948e7b948e1b949f2fa2983ba2983ba2983ba2987b94945f949a2f948e53948e1f948e4717cb5717cb2f17cb7b17db5317c71f631c else 0xb28200800003200003200000540500540502471100d00000d00000540500d00002d28200d00000a04300540500540501800001800001800001a00000c12000540500d00000d00001800000542200540501a00000d00001d00001284200d00003b70c00540200a04300540500540501d0000180000180000054220055c2005a4501d00001d00001d00001d00001d00001d00001d00002726101d00001d00001d00000800001800001d00001800000540201d00001d00000f89500540203200000d00000d00002472301800001800001220201220201220201220203200001800001800003200001220201220200c12000d00003778a00d0000080000080000180000055c50055c5005405012842012841000141008000000141005a0501284201284202470c00540502724f02824f0122820058c500b28200074103429500014103a2a100542200540502726100542201d00001284f01284f01285501286101284f00f89e00b28201284e02470402938f03760a01228202738f00b28103a28202738a00800002738a0084c003718a00f88f00f88f00f8a100f88f01286401088e02470c0389e300f88e02470403564603718303c29a02470c03a28100540203a28003a28103a28103a28103a28101c11301c1130156cf02e8c20156cf02e8c202c9110317d001088e02c90801088e01088e01088e01088e01088e01088e03949a03949a01088e0363170206cf0206ca02e5c10317cb0317d00317d002c90c02f8c102c90838800050b28269c11375d00035d01369c11339c11305d01f68b28151d00051c11950d00051d00039d00050800035d01969c11950b28269c11928d00029d0002899952b20002b20192b20002b200028d00029d0000b20192961542b011929d0002b200028d00028b2122b200028b21228b21228949529d00029d00028d00029d00029d00009d01929c11929d00029d00029d00029d00028800029d0002880005080195080)
def leaf511k10 (i : Nat) : Nat :=
  let row := packedAt leaf511k10w ((i-69)*24) 24
  (((0xa7a5a3a2a09897969592919087868382818076757372717064626160535250434240322110 >>> (8*((row) &&& 63))) &&& 255)) ||| (((0x904426114924d2212098440a15048221308848261020140140c07028120b04828160904426120144a223018844241308100a00a0142a1000844150285028904a05048340a0482c140506824542b04828160902834120406020201804010180540a140a24138144825028502e0504834088042010100c020080c022010804040300802030088846010904c0210088040403 >>> (27*((row >>> 6) &&& 63))) &&& 134217727) <<< 8) ||| (((0x6a70b81ca4d22989c2e070b89c0d158a45a0c0e03348ac52643a1948a0d028d45a25168ac522b348a4562d148ac360b1184c06150681428940a7030980b24d249542e152a0582851098449a592493094482144a05369a8d06c351a0d64a249a8f068351b4d06a361a0d469341a4d46831908826230980b04a24148a25028948a04c25120945824128984821908823a1b0c87429150dc74321b0e864351d0c84c25120944c240d058241a058282c1a090582a140a86824150b0502a0d0284c221208870280d0a8141a0e028341609 >>> (27*((row >>> 12) &&& 63))) &&& 134217727) <<< 35) ||| (((0x1048340a10c04222908824220108500c1201c48031100c28110a030241609044201104c20122c04834120c0481c1108028940a0c0281c0a0602034080c0201808030101c04060100c022300884020c0081802030003000060000c0000 >>> (18*((row >>> 18) &&& 63))) &&& 262143) <<< 62)
def leaf511xk10w (i : Nat) : Nat := (if i<1 then 0x204311a3629b14e3d73e0c05eb451038a0659514fb43e0c0012042af1464c32764df00a441038a311a3629b14e3d70c0c05eb451cdcd4496a2115b72430161d030f63627b14e3d73e0c05eb451038a0659614fb83e0c0012041cdcd4476a4e3d7240c000a441038a06596142380c0c0006040658a14f963e0f8010c0103841038a0659614fb83e0c0010c430f6d627b74e25e0c0c05eb461038a2ce95627b71ad234a1af1038a06bd114b17360c0010c41038a06556142380c0c000604161c9041080e038025c10a310103b90658a1420f0c0c0001482cf15627b74e25e025c20a319103b60654a1420f0c0c0001471038a06551142170c0c0001441038a0655114057180c00080422f15627b74e09e025020a3191038a22f15627b71ad234a2af1038a06bd1142170c0c0001441cd4e446b24e25e0c0c00014422f15627b74e25e025c20a31922f15627b75409e1e5020a319268ca0655114057180c0408041ccce446b24e25e180c0008042638a0691114057180c0008043aee3787b36e274180c05ea857e8b21ad254a1b9468ca2325430eed626f7523de340c05ea86268ca06591142170c0c04080430ee3788b1742570c0c05eb45268ca06591142170c0c0408042638a06551140570c0c0008042638a069d114057340c0010c4102ca06591142170c0c000144102ca06596142380c0c00014422f15626f74e25e025c20a499627b71ada34a2af102ca22f15628b21ad254a1b9462ca23254627b71ada34a2af102ca22f15102ca06591142170c0c000144102ca06591142170c0c000144262ca0655114057180c000804806f21ad254a1b9102ca23254629b11ae1a566681038a2af14627b11ad1a4a1a7103842ce8e1038a0659114f973e0c0010c41ce4d44cab52b9e3e4402f0c41cccd446aa523d73e440010c41038a0655614fb86644001204627b11ad9a4a1a71038422f0e32f0e64af27671e008007c38428dcd44a2a583d72444000a441038a06556142380c44000604627b11ad1a4a2a71038422f0e1038a06551142170c0c000144462f622f0e627b11ad1a501ad161c9050486c038031c10a3107e8b21ad254a1b94638a23254627b11ad9a4a2a71038422e8e102ca06591142170c0c000144102ca06591142170c0c0001441ad124c1a4122f522f06628a95c7f02101370427065443820e1ad12481a4082f522f06627a96aab130f5a72427065443910e687f02101370367065443820e629a94e3d43e0ee5eb423119a687e83d08c7035e0654038206607a45a3b52cf056ac6030ecb7035706540422058279d5a3b82cfc26ac6030ecb7035706540422057a7134086c128ee22fc364ae16079c5a3b422e826079c5a3b422e826079c5a3b422e826079c5a3b422e827a70c40862088e622fc264ad86079c7c3b422f026079c5a3b42cf02 else 0x629b11ae1a4a6681038a2af141038a0655614fb8660c001)
def leaf511xk10 (i : Nat) : Nat :=
  let row := packedAt leaf511xk10w ((i-0)*20) 20
  (((0x92908582818078757473727068676564636261605958575653525150494847464342403938373635343230272625242321191816151205040301 >>> (8*((row) &&& 63))) &&& 255)) ||| (((0x30088c445225168a4162b102854220309841629158240a0d041249205048340845228102a1501884460241a0c0413098010281000442180446224060b048051288211289020542a0040a040011086060380c02231142215028120b049341a4900a25114a8552040280400110868321b0c924b2190a87430884c06090580c05038140905824824904822138904426120144a2281488448251088c0621040240204028028904a05024160a0142a120506820080c040021105120940a090681409058260309048a0520902834110084020201804010180540a140a24128142815028241a04402100802030080806010040601100840210088040403 >>> (27*((row >>> 6) &&& 127))) &&& 134217727) <<< 8) ||| (((0x314aa456255289c42a11185c4e06a9158a514ca45a0c0e03348ac52643a1949058249140e05168ac522b548a45669148ac5a290a2502a122904c241a0981d0602c270301649a492c92692590d864b048a41548b452a058285120d04a21388944261128846224a261208512814f06a341a8d868349a8d065a2914c5221116094482a958a851291409b452292a140a25130903a990c87130180d964321b0e864351b0d05924120a61209148e05026510884a85028944c240d058241a058282e1a0905834120b05428150b0502a0d0284c3412068540a0d05824161a0502c1a09 >>> (27*((row >>> 13) &&& 127))) &&& 134217727) <<< 35)
def cycle511k10w (i : Nat) : Nat := 0xd1e7b3394c7e2b0b80bdddae36cb3d8abb58a9d3a93449fcea6b3095c9a431c8bc4a1b0881bf9f2f477ba9cae06db59a2cc63b097ab859ab952a44fa692a9045a19027c3b9c8da6831978b254279288a401d8d8622c14890421c0b850220e058180600
def cycle511k10 (i : Nat) : List Nat :=
  if i < 648 then [] else
    let t := i-648
    let a := packedAt cycle511k10w (9*t) 9
    let z := packedAt cycle511k10w (9*(t+1)) 9
    (List.range (z-a)).map (fun u => leaf511xk10 (a+u))
def w511k11 (i : Nat) : Nat := (if i<6 then (if i<3 then (if i<1 then 0xfa3340097fe88d01cdffab2400b7fe8c90025ffa22404f7fe84900aff78f2404dff638901affeaa20049ffaa4800a7fea22004bffa84800affe982004bffa4c8012ffe9d2002dffa58800bffe91200d1ffa38800b7fe9b200477feacb0025ffa32c009efe60b00b77f912c0cfffa24b012dffab1c0097fe8c7003dffa11c029fde5c7021f7f911c007ffa70700bfff0c1c027ffca4701afff1d1c04dffc58700b7ff111c091ffc38700a5ffab100077fe8c400b5ffa11004d7fe7c400a7fd96100c9ffa24400a7ff0c1004bffc2040027fe980800bffa4c20017fe9d0802bffa582002ffe91080afffa3820347fe8a0806b5f785fc12d7ddf7f0495f771fc45f3de97b1af3ef7a095dd7bde8248f5fe6a096dc7fe1825771ff7e097667bde824e59f7760965c7fdc824c79fd6e0951e7f9a824711ff6a096be3fea7a5f71ffad971247fdc05c6b5fb85fb12d7edf7ec495fb75fb3df3ee97adb15fbad2b35f76e976cf5df3a5cb33fbce872ccfdf34dcb2bff4e772d6f5fbad0b2b73ee842cadddb9d0b2bd7ee236c475fb0cdb3c57f5b820531ff86081c47fdd820699fd6e083cc7fdb820679fe6a085463fea7a14d9f7a9c82b73de8720addd79dc81b47fe2818cd1ff11f66dc7feb6586b1ff7c161a47fdd0584b9df05d602c7fc4458ad9f765c611e7dc17192f1ff1106744dfe08106b1ff74141267dc1711b71ffad921247fdf048ad9df65d211e77c1748b31ff8d122373fa97a9715fead2a1af77a9768cfedea1da34f77937686d5fead1a2267f844688ddf6a5ca3cfbda8728f3df64dca33ff5a7728eddf649ca44d7fab428699fe110a3bf3fa8428eddde9d0a3bd7fa2368ef5fe889a22f7ea96e8efefaa1ba3c77e936e8cffda9dba3b77e926e8efff299ba33f7e916e86d5feacfa33f3fa83e8cfdde9cfa33f7da63e8ef5fe88ca3b57fa2228cf5fe885a31ffd266a8f1dfc45aa317fe256a8c7dfc41aa2c4ff5b814693fd11a51a5fb5e015d13ef7a0133c7fe2604f13fd6e002bc7fe2600cd1ff896029cff44681677dd7c003a5fb5e000ef7fc6e00226ff1b800ab9fea9f01a57f9d7c12fafea9e04c73fa9780efbdea9d03c777a9740ededea1d0436fdaa7010fdf6a5c042fbda8700cbfd69dc05b57fab400cf9fea90032f3fa8400abdde9d00525feab2016dbfaa8805bf7ea92016fefaa0804b7fca620133dfa448093ff68a200a9bfca9a02a5ff0468087dfca5a03b7bf28680cdfdc9da032ffd26680abdfc45a0437fe09680e9bfca80039f7f2900109efca0002a7f7270016b7fc7c0041ffd2600109ff824001b4ff841c193fda2470346ff2a1c08b7fc10703c77f291c129ff4987064ffe1c1c06d3fe10403a6feaa080c7dfaa4204afbea8080e9ff2982044f7e9108155ff8182053c7bde8260f7dc7c0083dfb1e002d1fd82470 else (if i<2 then 0x7ff18003ff89801ffc5c00ffe24007ff0f003ff8b001ffc4400ffe1c007ff0a0037fd5161dfea4b0fef4e587fda62c37fd50e1dfea470f7f50387fda61c37fd5081dfea440f7f50207f7a710027bffa896225ffc4258c5dffa4961a6ffea3506ddffa4d40af7fe938807eff3c55097fecd14c67ff728c10a6ffd824045fdf3c90097fdce24047ffb38801a7ff8a2802bffe386008fffa124027ffe60900a7ff8a2c067ffe38700a7ff8f100af3ff860919cffdc824295ff860909e7fe1824739ffa9f71bd7fdc7dc675ff0e0619e7fc38185b3ff7e062d4ffdd8180b3ff6e0602cffda818999ffa9f601d7fe37d8915ff7df61357fdd7d82d5ffad9602e7fea6588f9ff641633d7fdf0588f5ff0d760267fd95d86f9ff05762ed7feb458599ffa91602d7fe34588d3ff11062c57feb4182d9ffa9060257fe34184b9ff110634cffc42582f9ff64961ae7fc12584b9ff05462367fc14d8d39ffa9f423d7fdd7d0ab5ff0d645657feb410af9ffa9041a67fc4410975ff88d412d7fc33504d9ff04d43d77ee931009dfb88c41bf7ec3310b3dfb44c4347f6ca310719ffa9f213d7fe17c86f5ff7df21a57fc35c8d93ffad722e67fe95c8ad9ff0d722667fd35c8739ff61121367fc1388293ff7e0513cffdd8142b9ffa9f509f3fe93940b5ff896514d7feb4142f9ffa9050373fcf414ab3ff10952cfb7cf254095ff89550257feb3d42d9ffa8f50af3fcf3d40d5ff88551b4ffc41140b5ffacf302e7fea3cc4f3ffad8102e7fe96046f3ffad710367fe95c445df7a4911a77dc32442bbf760911377dd3244b1fd73c910ae7fd83c42ddf728f143ff5ca20447ff5182101f7fa92842defe3ca1127fd8a28409dfe40a10a7bf8c28467ff618a102d7fe26004f3ffad8002e7fe9600079ff89800267fc36006d5ffad200ae7fea480af3ffad700ae7fe95c0279ff0d7013e7fd35c0095ffad100367fea4402d9ff61100b4ffe33800b5ff88e00257fe25804d5ffad0002e7fea4004b9ff61000b67fd74000b5ff88d002d7fe224047dfba480136fed82004ddfb4c8003f7ed120111fdb28800affe9a20007aff60b002f7ed3080077fb7c2001f7ed20800bdfb44201affe46080697feaca00277f9228029efe3ca001eff962800ddfe44a012ffe8928009efe30a00affe85280277feac60025ffa118027bfe606009f7f9318009dfe44600a7f78818047ffa146009dffab0c007dfea430025ffa10c00dbfe603002f7f930c00b7fe7c301a7fd8a0c051ffa24300a7fd860c02dffa143012dffab60009dfe0d8022dffab4808b7fead7009f7f835c029bfe617001dffab44007dfe4d101cdffab380097fe8ce0025ffa23806b7fead6001f7f8358009bfe61601b5ffab40007dfea50002f7f9340007dfea9000a77f9840009dfe5d001bf7f8f400697feacd0025f else 0xd3a15dfe490aeff568577fa142bbfcfa15dfe3d0aeff38855ffab36bbfd49b5dfe88dabff446d7f7a736affd5935dfea49aeff444d5ffa226bbfc1935efea09abff424d77f9326bfbc7935ff6389affd26dd7fe926ebff47b75ffa45baffd1cdd7fe8a6ebdfd41f5dfe4cfafef4e7d77f923ebfed31f5dfe44faeff427d77f9f3ebbfc79f5dfe74faeff1c7d77f8a3eaffd5995dfea4caeff44655ffa232bbfc1995fde9ccaeff24657fda632bbfc8995efe38cabff564577fa922bbfd11157fe888af7f50455ffa122bbfc9915ff6988aeff22457f78a22bff469157feac5aeff522d77fa216affd10b5efea05abff422d77f9316bfbd38b57fe7c5aeff242d7fe8d16bff87355ffc35aaffe12d57ff076ab7bf53abddfa5d5b7fd672ebfea3977ef538bdf7a5c5febcee2fbdcf717bbf3a0bbfba9b5efdd2daff6e76d7df67b6bff399b5efda2daf77e73d7bef31ebbfda9a5feeced2f7f52697dfa7b4bff599a5efea2d2ffe65697bfa834bff59805dfeac02ffe650177faa80bdf7a5c3dfdd4d9f7ee96cfdf74367ff399b3e7fd079f7de63cfdfb4347bfd61a3efea6d1ffd6668fbfa8b47ff995a3efea0d1fff0b68f5ff53c3cffa5e1dfe84c0ef7ea747bbf4ba3edfa1d1defb0e8f77d37475ff42e3bfd0971bfbd648efdea247def4123bfba9b1efdd2d8fbee86c77f6c363dfb4db1fedced8efed76c7bf69363ff329b1e7fd078f77e73c77fb5343efda1a1dfeb0d0f7f53687fbb3b43bfd5da1efea4d0ffd4a687ff32b43dfd41a1bfbd620efdea107def4083fd79c41ff9ca20dffab2877fd5143fde9ca1ffd4a50fff24287ff81143affa9e0e7fd2f06ff426037bf53a1ddfa5d0f6fd0e86f7d8743bbe9ba1affa170dfe84b873fe84437ef5381df7a5c0f7bd0e06fdd8703bee9b81fd79dc0dfbaee077dd27035ff42c1bdf9d60dfe84b073fe8403bbf3a017fbac80dfdd4407bee8203fe73101efda1a0dfeb0d077f53683fbb3b41bfd5da0efea4d07fd666837fab341dfd45a0ffc92d07bf680037fac001dfd4c00feece005ff5f0037fab801ff59800dfeac007fe49003df74041fdb9c20ff9cc106ffaa283bfd4941fde9ca0ffb4c507ff24283ff81141ffc00a0dff543077fa9183dfd40c1ff69860ffe48307ff001837fd5061efea030fef4e187ff240c3ff80061efea9e0f7f52f06ffaa603bfd4b01ffc0980dff549077fa9483fbd53a1fdea5d0fef30e87f7937437fd52e1dfea570f7f50b87ff025c37fd5221dfea510f7f50886ffaa383bfd49c1ff6a9c0ffb52e07fd98703fec9b81ff65dc0ffb24e07fd8f7037fd52c1dfea560f7f50b07f7a7583ff812c1bfea900f7f50807f7a74037fd51a1dfea4d0fef4e686ffaa243bfd4921efea090ffe30d07ff13683ff8bb41ffc49a0ffe1ed07ff16683ff88b41ffc39a0ffe14d)) else (if i<4 then 0x2dffb4b95ffeb44b7ff52257ff8d12effd28977fd944bbfe9a25dffad12effc68977fe144bbfec225bff64e2effd2a16ffd850bbfe9a85bff5d42effa4a17fecd50afff5a65dffa532dffb09977fd34cb7feba65dff4932ffd9a996ffd44cbdfee9cbeff70e5f7fb672dffeb2577ff512bbff8c95effd24afff9a257bfe51eb7ffac85dffd442effe3217bff490bdff4485fef9442fff9a216fff58abbffa855dffc62af7fe9157bff10ab7ff7c55fff342aeffea117bfe808bff71c45bffd661f7fe930fbff1187dff0cc3fff3461dffeb14f7ff50a7bff8c53effd229f7fe214efff08a7bff6053bffd621effd810fbfe9887dff4043ffb8e21fff8b10effee847dff4423fff1611dffeb3877ff51c3bff8ce1effd270f7fe2387fef5923ff78491ffbb848ffddb247bfe79e37ffacc1dffd460effe33077fe2183dffa4c1effc460effd7307bfe9183ffe68c1bffd640effea2077ff1903dffa481effc440dffe12077fec103dff4c81ffd9a40effea2c7bfe8163eff34b1ffb9e20ffdcd107fee4883bffa821bffc210effd8087bfe9843bff5c21effa410ffdca087ffc4943ffe14a1bffd6706ffea3837ff19c1dffa4e0effc4707ff9a3837fe7ac1dff3d00bffd6686ffea3437ff19a1dffa4d0effc4686ffd7343bfe91a1ffe68d0bffd6486ffea2437ff1921dffa490effc44877fc3242fff0921dff4c90fff34487fee1203ff6e901ffb6c80dffae586ffd62c3ff64961bff6040dffae207fec9103ff67841ffb3820ffd94107ff86283ffc60c1ffe1860fff1e187ff8c0c3ffd59c1ffea8e0fff46707ff84383ffd49c1ffe88e0fff06707ff9d383ffcd9c1ffe3d60fff1e807ffaa343ffd19a1ffea4d0fff44687ff9f343ffcb9a1ffe48d0fff36687ffab243ffd5121ffe8c90fff08487ffa9243ffd1121ffe0c90fff26487ff9b243ffcb961ffe58b0f7bd2f66bfea7a79ff4bd3cffa9e9e7fd0bcf3fe8567df74bd77fbad2befdd295f7eeb4afbf6fa57dfb752bfedd2edffce972ffe69b977fbad0befdd285fbee842fbf69a17fdb9d0befdd685f7ee142fbf6fa17dfba4dbbfdc46dff6e736f5ff53d1cffa5e8defd4ec777e9763dbf43b1ddf4dd8dfbd4e477de9723def4391df74dc8febcee477dd27239ff4211ddf9d08e7fd4f477dea723beec391cffa168eefceb46f7ea75bbbf4badddf65d6defb2eb777c175b7ef538ddf7a5c6efbb2e36fdd971bfaf3b8ddf749c6eefce836fdea713bef4b89df765c4dfbb2e27bde87139ff42097fbacc4dfdd4627fce63137bf53a5ddfa5d2eefb2e96f7d974bdbf43a5affa172e7fd0895ffab4abbfd5a55dfe7d2aeff3a9577f9c4abfbc9bb5efea11aeff268d77f9d46bbfce2357feaceaeff527577fa23aaffd11d5ff64dcaffb24e57fd8f72affd5a15bfe110af7f508577f9342bfb else (if i<5 then 0x796045800013ff7e09df7bd04eff5b8277fcd4139ffa9f9cffd494d7fdf827bdef413df77609affb904f7f5b827bfcd4135ff6a09cffbf04e7fdc8273fedc139ff6a09affd6c4e7fea626bff5af39ffa979cffb0bcd7feb5673ff52b39ff6159cffaeacd7fe37df3fe23ef3ffad97cffd2cbe7feb65f3fee32f5ffad28cffd49467fea462bff5a119ffa908affc46c57feb6233ff53115ffad68cffd4b467fd85a33febad13ff8a069ff88fb67fc47da7ff5b2d9ffa596cffd6cb67fdd65b3feca2d9ff8d16cffb2b367fd941b3ff1a0d5ff8df4cff88fa57feb6527ff5b299ffa594cffb2b267fd94133ff1a095ff8d04efdb26257fe37cb3fe23e53ffad92cffd2c967feb64b3fefb259ff6572cffc4b94ffe344b3feca255ffad12cffd48967fe344abff1a259ff64e2cffb2a14ffdc8167fedc0b9ff60f3cffd4f8d7fe26073ff13039ff0d81affd690e7fea486bff12e39ff8971cff86b8d7feb4473ff52233ff8ce1efbc448d7feb3c73ff51e39ff5cf1affc460d7fe22067ff1963df74c41efba420f7dd01067ff5ac19ffa560cffc4b067fc35833fe9ac19ff49609ffc6684ffe3243bf711013ff8cb09ffc6387f6c91c27ff1881bf75840eff241877f92403bfd5a01dfe8500eff3e807ff2a1c3ff918e1ffc1070dffd4fbdffeb65fbff4b2f7ffad37effd29beffd74dffee526fbff5537effa09bfbfcd4df7fea26f7ffacd8dffd46c6ffe3363bff49b1dff88d8effa46c5ffe281affefc0d7ff7606bffb7035ffda81b7ff140dbff0e06dffbf036ffdd81b7fedc0dbff6a06dffd4fb5ffc47dbdfe73eddffa9f6eff88fb5ffeb65b7ff532ddffa596dffd40b77fd905affef82d7ff7416f7f9c0b5ffeb5db7ff52eddffa576eff86bb6ffd95db7fe0aed7ffad16dffd48b5ffe345affe222ddffa516effb28b77fc145bbff5a2ddffa916effc68b77fc445bbfeea2d7ffad66dffd4b377fe959b7fecacdbff0566dffaeb377fd259afff5a0dbffa906bffc6835ffc441bbff4a0ddff6506effa48377fd741afff192dbff6496ffdb84b5ffeb51b7ff528ddffa546dffaea377fd251b7feb28ddff4546f7f9ca37fec751afff5a6dbffa936effd29b77fc34db7feba6ddff4936dffac9b77fd14dbdfe726dffb1d36bffb69b6ffd44db7ff53e97ffad94effd2ca5ffeb593bff4ac9bff6564dffb0b25ffeb4137ff52097ff8d04effd28277fd9413bfe9a09dffad04effc68277fe1413bfec2097ff88d4effb26a6ffd9353ff75989ffba4c4ffdc4627fec3313ff6c989ffb74c4ffdac627fed1313ff6d989ffb68c4bffd69a77fe94d37fec269dff4d34dffac9a77fd14d3fbe5269ffb3534dffa89a6ffea7cb7fec3e5dff4df2bffd6c977fe964afff5ae5dffa572dffb2b96ffeb5cb7ff4ae5bff8972dff86b96ffe15cb7fe9ae5bff6d7 else 0xe005c14e9e5700df50015fe20bf4caa91620526b33994c25f2e198f80feb0008e500272c0484101227a047a380243a004f08129c0041dc801e8a049808021e00492d90be34040cce622c61cb4c72af1002f8008dd501f12c08b0a02037000e1e01f95c00c810230440063c02291800d1c002030089c0002b7c08299cc858c31998e54405470b8513b24019c10012214766803fc6401139514a214432803d3c000888516da00212903f905447215124c146468007ec146f785155e001318000146ccce6223974b585b817b71fb5f3b527b437b3b1b37bb32bb271b1fdb181b131b0a3afd7af51af13aeb1ae3dad83ad0fabb5aafbaa87aa25a8ffa7fda743a689a547a3b7a35da303a17ba145a0059f419ea99e4f9d219b9b9a6d9a259923975d962d95d394b7934b92b3926b91b9900f8f658e878dd58cb98b0f89e188ab861b84c183f5827f81cd81097f217ed97dd77c597ac179ad78d777d5770975297375722d70a56f7f6ebb6e476d716ceb6c896c2f6b356a8b6a1f68e9676b672366db664365bd65516461640763ad62d7627d617b610f60935fc75f415e7d5d115c8b5bf35a155987595158b9581957d1575d56a356495573551954e3549b53ab532551cb514550e3500d4fc54f594ec14e294dcf4d874cc34c694bb74b1f4ac54a6b49dd4919485547d745e74561452b44d1449b4465440b432d4261421941a5416f4103405140093f833f213ed93e773e153dcd3d593ccb3c693c333beb3b7f3b253acb39ff391738a3380b37593711360734fd349b342733f133bb3295324d3205312730f130a92fb92f832f292ef32e7f2e372d352c692c212bd92ab32a592a11293b28b527f12713267325ff254d24c72415236322cb222120891ff11f631f1b1ed31e3b1cb51c031bbb1b3d1ac919e319ad190318a117c316ff1667152714b3147d13e5132112ad115d10e910370fef0f950f710eeb0e910d370b9f0ac10a0f096f0749048f01e500b6fdb4fb0af7caf672f39cf25ef070ef5ceca2e948e8a8e7cae718e678e47ee1b2dfe4ddfcdc76daf0d996d734d5ecd4a4d34ad2bcd0f8cffeceeace1ecc48cb8ec946c722c5dac492c3a2c22ebf2cbe4ebd82bcd0bc76bb2ebaa0b896b59eb4c0b420b11eb07eaf36aea8ad2aac0ea99aa8bca736a58ca49ca3a4a288a0b29edc9d569bb699b498e89736959693e4923291288f768db28c2c8a8c88da8754866484de835881d280207e807cfa7bbc79f878cc778e76227556748a7192700c6e486cee6b7a6a68684e66d26520642862f26226601c5e005c4e5a8a58ea571e5540538652244fd44e4e4cec4bb649b64766450442a240aa3e7c3ae639c2389e37b8361834a43342320c30402ec42d5a2bb22a8e285026ba2512242221701fd81ece1d0a1b3618841794161814da12f411780f760d0a0ad4))) else (if i<9 then (if i<7 then 0x1a202025d5814f2e1088e3b2a3801ca440a66e0341100c728032ee40c16d00128807b8e033b2c0bc974b428239f03356504ddc02edb80d05801c2c40a550033d900c648032b640bf8d000e5c02884b4ab209f0335d40c559032678001d301e5e504efc02e8740cc8e0339e006fd1028e5d270c8525a239042017c704003680f0b206489a0992c05c94019624037358144900650f01892e88432060296c8224077750314bd04b44031cb806d870285900c61e03118c0009744219037d483dc0c00a030a100bea4006ee40c1b907728c293fc0283640bf8840e5c2399be93720468b83bffe04fba83c7b805d9f03bd4c0f2a683c4e600eed817b2c05cd003c9c00f07883c22003b7e0174a6010e58179960ed9544733973ea148db10296f00af6002ce800b73102a6432d951576c0a4e602ba280b2ca02d96c0b82d9558657cd02b5c40b1b102d7440a39518cabb805458816b9405b3581454005bbb01583405841c621496c8654e2058c50164c00599b01563405855814e580ccb5ed219566815bcc057438143780579b0156ec0560cc5cfa90ca9880aadc02a3f00a03102a6ac0a719c842cfa957f813f220536d814962052c38142d60517e0141a2051ba0321496c85f91004c5f01108e0093101394404f23001b8403d484b6552bac0022e604dd9813aae0066980f35004bef010f2a2a98fc400bb30275b4078a2027908096780218040101c0268292d95485cc09b620270e00851c026b0000a0a4b655218802617808412001cf408f0d023be809542025aa00971a02679407d5b217c58c396c8df91203bdf0110bc0420e801270042bc010c380046f010f2a7d4862407712001db407811001b4c0791001da8807bc201e8ab2d7e4865c0752801cf080749697026062d154e00725801c0b806d730077e02922b0072cc0711201ba8c2936d0a44fc1da7801bcb02399cb4aade90aa91a9e0365710d428035ea80c1b2034c68007271608cb12e96c8e41a043471000bf6033d780052e5f9564057d821779805d1401afa80669e0005bc86bce2198b05511c8e5d2d900509406a840194bc068ea019a7485bab016b64069fb019d8c0009748df52080016fb005f2c017198062ad07639805d990a4354060f7017aac05af00a3cc006198b70db2e2c4b56920467a80b06a02caa80af2a8e964aa132b2ca09a24029db20a61e0243e2091ec02b43809b2196c28aa4602963a0a840023c6a0920e02abca09d0a2a98c9d0463201301c05513413319055f6015b3005170414724046014b47d21851180a45e825f100a824029c600a0a4822e600a30890bea157080cdc009e64026520036ae02743809a9a8ea00809602999b64255853e94c8d20011cb0019df01268404a0f01235403e8901165c01ac90118e0018998ba64553530e14657d232aaeb21c00ed788169 else (if i<8 then 0x6cba2efc965e123cde0a36c0283140a6298297482980e029af697402591e6ab6028e64458560293680a437828c240a5120243339915a5cf58f4b228120e1050f60141a7051484144600508ad2e93c01951e7d0d827b7e09fff82812e9647878d62a9302799409f7c8259fe0a06202610408fc34bf2e7bcb23cd6ca04fae412abf04fd0811e9404dbd413b8bc365d13963f1b04c09e0d827bc00974f023be009afa82770e2b4ba4f1e7d359c01383d0472e012f7304afc01358b04de501368d0b4792e8f0e6585a08de00265c00975c025f94098fc8253880984665c1c9635a3cc408d5c8255f20965d825ae6095fc8253182b4b8c31e324b2b8924ee04a27811d240487d8926b1247e5ef58a45024126092b10234464918d1239d2093b1824cf5681605c2d97b3cc7f209245024002091de123c48090e40244fb8a3102345a08d9e82393c08ea1023d0408fbecc655970a5f28117fa046704226bf0460bd2f009e8beb0529878c116ca02d3f41159797c6e5ee403c85c11480044e5e333197c342207f086f04111872080041120400aec42a3ba0860dc10f090a9f102a4670ab0d8210790436653099a225d2f4d8b5e5d0ed91a6c09a9b72085fbc10e370aaa4ef99788cfa9e22850217dc10289053e6e1039a82104a104ec8215332b8025c8b2da74abfe150a3953604d4dbf820e46883c681645964a9fe93943819201068864192829c026a6e2029b9394c80ff4d91344104d9040d88105fc0406801022d98caab6078fb81fc6e07ab101f5a607e0d81fffa0771181fbe60806e81f7ec07a16c6e575a03c0ac0f3ab03bfd80f86103db680f71a03e4b6331b95c502941f038c3c1f2c303a40c0ede707a4c01eb999aa5c572da74aaa0067ad81c5fe0741f81d92e2d95cab3e066d501c29c0738a00d71c075cba541496956f40e6fd03a8740cc953d4c655e80396b886ab90352380ebf60159200caa002dcfc0ec5303825d275f1565a3e9559813bfa0750380aab2064d8816b1c075b201be100726710cd276e0525d2d95389b3d0072bc81a49c073db20a6c0059ff81d02606f4ba4e238ccb5c32a73026ef40e6c74151c40b14e039c900dd0803924f230ccba5a5811c83a00e5be0370cc0d11c0268200e4704144680b09708e32ec96caaa80e112014d900c6bc02bd6c0e213037b640695303825d2710b863b2a230149d40c5cd02b6a80e1240377a806664037f78087938ce5d2a710863b7c06e4200caf00433201bf980288f0188ec0562981c12e10bb23b2abe0370e0085240376300503602ac4c0de944b9ed1d950e01b170027850184c40551f81ad1206d8981b372069fc81aa3a06d5e01af2e1988654158ebc81a47e06b5c81a90e026ec817e62054cba4e2e108b2551d320132100bedc02a2e40d4330347e40d597086072a8ebc81a572069998 else 0x2d95caa4a0c864a326120cbcb5e255660669701984b465f8919a09065fb49668c06668018fff05011118f722fa5d2d8d1048b2a67064ff81942a065494190093536a01921b04f58018ea0063e1c1912b4b9db2a224749813c6b06368018f6585e08cd46304b9ef2a8e915ac18d60063b8c94b35060bd413b91cb8871d7e3ca2413ace061e1895796992546249177102c7950b20602c685255a5c139dc061a5a0e95189245d5f4b11542c4a70629d81895e25569d188ee0b0ec82c2110611c0138b54613e8188f40b165cd99306c1e2296a4a549c4640057c100c1c0057e5d934a8c658130616002bfc700e0b12a319744c185e406064c1411ca9e12d90188ba5811061378d415925dbc013535060a4cdf974a88b1d08060f9018195175e048501bf0c35fa160f2006a784a99312209c09a4983005a016cc8671d95189145dcb24cdf817fdd04cd8897ff300d9782195528a5ec25d6a20da3c255c80af72c229972867c8a5d9acd26731344ba5a23450add3897e1e0af1ea052988cc7ba0bea002fc1401ba1e1c015a98b2f55acbdd102f6c6cbe72056d526997605697e0be5d825a9811a0002f4e6d5b1581c44974a4cd2a5ca75568cf865e7b02ae2a0dcb044a734c2e412a3e05e00017ab835da472e204a4c9204705e72c17775961dcde0bb73925fec15821855ff209489a460d9702a528c902df7016b8005b9188adf6054a5ef463c69a8f04f05c30817254249c1c16a0705c6ac16d7d05bc5c1737122a8c0014210546350c97cb8bec931cb2701698005bad81507517d9520785582b79409f28029f000b74912428a0b44c660ec973de412c3e059fa8158ab05b56014e9a2482501367bbb1d4ca79cb8c92c900102cdcc2a68e029b2e96480c2d52c3802cbb20b62a0a99140a6380b85a2c4e02d2c445aee02d6240a54bdccc78c325e04c09e560292722a36e02d7dc0942282d0164564ca612e8c3ddd92f694b0f81670422a22852e0705aad0148f6249bc01357bbb1cd2f8c3ce5cd59636028e7c0b3ce02d35c4922282d1ea09dcce612897461f92c700594e45468a14b8081666f051b8012eb1247e5d27693f23ad53105776416371057e54162e705929c145e9049f3c161894325f2e9395c66d88efd82b9820b01d82bd2f2cb80ad560add10a82e20af908289f209631824c760af45e5f2e7bc9db11d310576ac15be1050fa8158b904a88c923fb0571952e93bf1b11d99056a4c125ea056128529c10565cc12b60050a351897cb9943996510a82d20aa6c0282942949502abf20948d12392e8c318b7201ccb04814ab60541f08b1f60549eeca64c79e1f2092560292a00a78b1156420a2298297ec0a94ca62ec973de3d2c01048ed0148580538788a7a414c180142210545eeec653ce5d1e6acb1b014750053f8414358053ad8150c8048a67318)) else (if i<11 then (if i<10 then 0x200fe5c01a68122105590a51f8fa0126f31c8ea7706c25ef792329afb64e808835e1f923f042d7bb26f7ec1d0923eda8d7ca25af6c9d0dc05afec1d02126bb9c8df64037e5c1ae75340bb359a4be34d4974a48b1e4ba995c8b481377313775841413039e520126b059dbe12fae03545c16ef4959f1816f4c25f33974d954335e26e9542d5240b72781c7a10a555c25cd406a7742d6ac0b5058974b9b90a67329809c112f19cb9709b5e7fccf1664dcbc839de60e34bc07292cae53a569306a2f4a0c17188546eb3d525c7cc033bf2aa39c1649c00f0b09b58908234ce0a25096dee2e16a04472f9711652ad45421446dc5506392e1903536c82c6a3759948577b8135af038b8a705ca034f305e9586b2e7e19937295da2a101cb8325cda42d9950588d01cd310b609ae40da26de082da1a0710740da900b6f4c25a50069a6732980cc4eea973756d2f4daf3409b810070c4c0d93407374c1cc460696241ca97bc146e410526d9141c2290aef2402e9c00f2b8231ff18884ce9d650aeaf4972cf0586642e16928812e949116cfb45700348460e4e98398f24d95c83837806bcbe5cea810722101cb230726581a389036f6096f890728bc9b4c10581bc1c097cba5232143e693661a0dfac40259333fa5e9d2b2f92d48a0e14f002ee20af8803861a0dfdb135abc0e2fc81aa340e25c8382580d1378380ea97cba34e822ca6c5dbe99056834ad12ea6fb79d9fd40b4b2cad2a80b47581bed709515019f8f2b41942d09625693c9be1303c1d262288e5d2997a71192e4cf590570587d9548ba44733b8360364d8bdc46219535c441aff506f5ec3210ca9afe00d8980378f595351afe446e980379c84b4fa837b2e0d77b02a4764d63e1a0c89acd2352e96b79ad2a572684a41b4c306dd981b21d234f700167906e0701b37d06d83c95dc206b7081b5210545a0be96c698b2e224abc01b1a425415c1acb60540ec9ac1b26c5cae49acd1a6ce974b64623900012dc220d7890294ae0d60e91c92e0d73b8360e86615a6b34694ba551d224d12d1580a4f883576e46e7a131b2e0d74d669327bcba551da2256ed0148f92682fc8d14525e3081ad7bba1e72e9547488d80a3f88357f24d02b8358d24a7cd669339748e3afc9306a3801a496068e5496dd400569c145460697b01a194069cb01a250069998569734c892a8e8792ce420a2330340ba4c116034432973ddb12a8ee7929dc20a1f60342cc0d052833a23973d9b12a8efb0aeca80cfa712b0c00a152833b1a118e25d2a224743819e4c067254556b671c70d6166e6032d7851c38232d600cdca14e7332b8025c8b2da74aa540cae7232b2d7b86e5d2a112b1265566066a04a373546526401973e8cd2a5b956a01924c464a3019996caa5c555c0662dcaa54029ca24e36870645dca362b464666047fa6c7e95 else 0x53a04d4d96805a378f840c492880a6ca83612040469791830d2654948c60444a24ae086f160808ce5551c604007a40ec40be4c0227546b4549dc03fef30bc1536235297c28fa4d88e4ea58c08020c201b807fdf41fd2200a8582026d07fbfc1fa3488e5c807aa56152c922a49f2f74e88d40692aa6c2e1423195246d2c23090584a340680949251180292307e5d01f87a9d8aa344a3f85352e14b9403f850034a924d95f08d24300fdc8cea23494687c926caf86e0c10a4a8481cff07ea34953e88d24691f0dd24460fc9dc421432a496a0472c065252310995257a40d464b092da80660623492d846214950005855348dd24e80fc500059202c2481002b918cd24551a24a460c32a4a301401aacba9285891e6214948d7c0c32a488802a2507dc741f65b08e5492342a448802a99c69d075119f63a924600a4d2142aa4918029681de303a31a49fc29a950a66463244a5524d92b195256e14c4b852e620140b83eb2318851549224009edc2964c07d2d0862118665495490e90b8234824974a8f8e3e446920c961250311a4be81f3ed4756fc1ed2508e5d2d10c653a889548c42654948c42654942004a500f8ea004c330bca92a9245911251c7c88525d00f79480486e011c8c662e0a2a924551a24a17037988524142aa485c022818dc42925b08c4292a207b1351d4bf07b6472e11bf12a8c8ec483b3a20ea9183cc199527dad230498d25230619525940e9ed817b960f54b89519681563a9b224aa46be0619525236591124080e96683d12e8c9ea3a72444a94103f7bcb8431d9521007ea6010bde5c238cb02542814a48851d8403d40c046f2aa81d41e3260a30327d2aa484428b7b8253aa03803209481f851ac46f0501395150311bfd409217077f20a8879885362352e6803e7c061bdcd623782805c2897bb8046ff502494428899c41eefa11a6d4b5e0ebb2803c460f32003a8a60109f83b50324cb8aa234dbea41f0149429b9013588d40120eedf00403168a32382132a4a38692aa4ae41dc8b138421655232bc1d7410758241ddb90771b4291cb076c9c559688d1afc90e4209566038c6404582524846cb10a4a326c2a8f86e444a2020311c34955257080c9400e74800dd18526164925232584a3685231973b0c0e6c11a509828c271a4c79c03278051fde1453dcd8473225070063170a25eee03a924ca92510a220ef7701bc46948907667c9d8ad07619401e118525d237d26d1920a101280c6a2b2319644495783ae6c2a8f86e644a39803b2e00d421ecbe2aaa9187000c470d255495783ae5800cb9803a820eb158038aa02bbd92b1d502083ac6c1081d285800c9580391a7b1b046948e280ca9211884123746159287000c34238a031a49a023048d128a881f0203a5a20eaa1007e800ea0f8ed0a4da2642fa5040ff281d3040749881d14) else (if i<12 then 0xc5380853134919d9015ec7019d2e96899d2b44698c46e8d9098bc4a3e98093c740cc103a5ae9911ca8ab721270c91907c0618a84c2421304a82e146ba14280c2d2096754258290aed5c037edb8ed942bad3096a5024c25096d985310cb92a4e8ea09308a11ca9882b9d50963cc0368e094ee40c19720c8b1d4708dd19812b6f84afee0604765ce8453104a5ae12a4704a686157c94482a971b9829b8ea30472a350946c82b81411656d62aa2856fe21280ac522331ba1e03245d64abdaee1254c049fe65011753cc6c50b4b4be4f274b8b06211a3657062210141a250afc84933a500be5f0209698a565de4092f900351e27fd84a129409309c2811cba0a3256cadf5181007714013a108bb8495f6e0f3994231a2ecb8466e41be9bf32123a50539fe12422d0ab2571c136447762047dfe12408d6b2a6ba4c8855c257ce642477909183e893ab5d74442aea84865aaf7448488230a35d0a9011dd3047e02159bd84808e159458482852189c420540cb8a27031ca640bf319d3047f8811f64abda66158cba044913ab90b2928ca9684431caabd9e211e9d04791a11d698473207cbe25d2942a404761ed1daa006886157bcc502608ca65ca4571cd2c859011b46a2c11aa1855e2b9714a53203f9c90c584808cbb02ae1b8add64477160502280a0c15c9d2807f35422c978a4285f119795df408cc31b61457249ec22e3a961244a161448a92f300ceb8231451445c2b0a0483caa495a846117170a428772f27594468eb68829d5d01042822b0c08bf48227a400c809201f10d5c300fde28455c4116c38062f61174c08e042f93a5cc24e474940d50a700aab2aa4b5422c268a0aa77182771422a2307c46414ec98a0111089525a4156829219de08600e5e592b17d1526021f0aa974885908584e9f04487a15587c0f24408ccee9d0f9e8c6e249108443b011145854c911784902583ba755c34179e8b097710878782162c24a2c21563087c941f70cc80c0f039084dee60022e13b22088600424f71785e0afd497b04297610eb8843d0e0188e83ec819749cc0c253bde1204d4d944681f1d276ec21d8b9545e236c24bd82148b08567421139084f002122200a87821607083d94699749d68dd8f23005256107058689482051250e018cc0ea5f922b1250e01883841f1a522d924210e0fd244c018490663749778218561071300611a0a249f2550d2ad253815146041b1a260c84e559527514323f15524ff5424c5c3d2aa4b0c02fa90831602a0940c428154a2484829f8b0c4f8554eddc09e7414f66853ac4105ad8414542609c460795277ba04e11c4604554b9982121d4825d1ca9b90206de624388dc222349008d25849468b04c2d941188e54d960865128175248e54dc40a8033e0753b230b9a4ca92180ed2892c900ba242081705024154a24a342e8f95 else 0x1ee134a04dc4301099878267d50110c8268370f864245f98cf425ed26010f255ed82a765dc24a409b8d42518e094e3c2557438848235f98ccba9e64f779a451074388ba555f98ce1e602e960aa581193b8603f19c97d82144c010a742112c08c9d18100160866e270c03f63a0fb08646da0ff48c9cfe4ed3683fc332a939740411807effc1fa91c68424eff80fa4719108644dc00f012c3804091be4d5960edc5a10d0252a207c800ea1f83b43e2c12b5403e8c1587c4ae807be54284a82a1468ad77a27d65e2b024b84a21451b8047c81667684bc564525326ad394815028a900b6dee534570150c001431b85552f58ac09e7b2c2788aef332918002867129fcb010449f0c0636bb68593741658705945551271c018b970a0cac18c7cab51bee134d8850526408c84e23084ba5ab44ea4cab2ad60a07dc2690527a82c21c4209c24c27971b89c621b911f52a9b090ba3c4c144205d1a27758281b80a03fc2a1b10a0a5a819746d145227ca9509d43154aaa24e5c050184af9cb84fef212322812893aae8bad72af8947d301278c840145c3356d7201eabc8c1e2aa893862130515093c609f5f827ec609d0f027c4096056879518daf981319f04cac413c8d84f76650ff704f52d1031144627e174742772757c3f0276de09bd14813188daf202a95640664d7e044be613a901408f97c4b4c46390174d29e81608d590271c409c9b95e892204be2896944472e3a260ba58903204e2841382045026974b5d223901d1305d2c1388c423c2683c26c8509b5b024de1279e4c1410cba548a1c00ef7026bedb8ee7003c940931985619099664a5c2d95403a8a8c8faad1bacc8c2551273f426ae4092e3ab85b229671a01ca600844c021b090737c16011108427098484c24934ba5443430abd382f13938cd2a49c0057d0015fe38070b60c2a4b0b33e099480a041bca99a5d57e604c7f2124fe044bce13238cf28f31975afb213127))))
def leaf511k11w (i : Nat) : Nat := (if i<1 then 0x30a000914000628000c32c3186586314000638e10d4000304a34609468c28001871d9304a346280006b80018251a304a34614000c38ec98251a4ae00100cb0ac196118251f1931b8326370628000c71421931b8938509250001071412440a04881409102812205020e28241c504838a09080502100a041c504838a090805020e28241c560838ac10715820e38241c704838e09071c120e3824581408b02811605022c0a04581408b02811918723230e458140838e091918521cd82439b04840281071c12080a0439b048736092205021cd82439b788314c10629820c530418d6085c4d90d75820e382488140838e090805020e3bc41c704820281040502080a04101408202810405020658440cb08820281071c12260a040cb088402810251f22c0a0461624819611032c22080a041c704819611032c22440a040947c8b02810e6c12065824616248c2c490405020e282461624900a09220502131c2438504840281185860b230810cb042196085858618e28431c509638a148714230e2b261c564c38ac98715918e384518a64a314c94629928c53251c58ca31ac8c108130210211c504238a084714108e28211c578238e084629e08023074042ce80888910a23c038261c564a314c94629928c53251c58d2084098108108e28211c504238a084715e08e382118a782008c0471404d83849b0708ee0888ec1c21d83843b0708700e10ec1c249c384770445160efc6c1d94d83b25acd64b59ac96b3592ba6b25acd64b59ac94d3592ae7005b078d208408c10810d83821b0704300e086c1c10d83821387042b9cb86c1de0d66bc100461160efb6c1d94d83b23b0764b59b1b2c1c1ad83823b0704b59af06c1c03a02149b0709360e15201c11d83843b0708760e10e01c21d838493870a870e0a6c1c23583b26b0764d60ec9a01d93583b26b0764c70ec9ac1d94d82843b050a960a0a6c1c21d8384aacd7e159aca6b3593583c61b0704300e086c1c10d8382138704360e086c1de0d82821b0704359af52c1c1a583834b0704760e0d2c1c1a583826b077a960a0d2b35e4d66b23acd64d60f1d6c1c1bd83823b0704d60ef06c1c03d83814b0701f60e0cec1c14d83826b0778360e052c1c06583829b0704760e086c1c0a583809b0705360e0d6c1c17583834b0700960e0dec1c11d83823b0704760e08ec1c17d8382eb0705360e0d2c1c02583833b0705360e092c1c17583826b0760d60ec1ac1d83583b06b0760d60ec1ac1d8658382eb0705360e08ec1c1a583804b0705360e08ec1c1246d28e8da807311111f80f73f01e97e084360e006c1c00d83801b0700360e006c1c00d838018da342fc04d2c1c0a583814b0702960e052c1c0a583814b0702862a950c552258382eb0704760e09ac1de258382eb0705360e09ac1de246d28e8da8131b470e6222 else (if i<2 then 0x8f00658600cb0c019618032c3030b1e00cb0c019618032c300658600cb0c019618032c300658606163c0c2c78032c300658600cb0c0a0000032c300658600cb0c019618032c300658600cb0c050000150000140000280000500000a00001400006163c0c2c781858f0403840805081036100a00000688600d10c01a218032c300688600d10c0b800017000006f0606493006bac8032c300658600cb0c019618032c3030b1e00d10c0c2c781858900658600cb0c019618032c300658600cb0c100e1003443030b1e061624019618032c300658600cb0c0196180e6c201cd840387080736100344300688600d10c01a2181700000688605c0000b80001700002e00000d10c0280001924c00658400cb08019610032c20065840a5c3806baf80344200658400cb08019618032c300658600cb0c070e100344301cd8400cb080196181858f04028406163c0c2c781858f030f9e061f3c070a100e14201c284038508070a100e14201c284038508070a101864f030c9e06193c0c32780a000030c9e0280000500000a00001400001c5080c2c7820142048700038508051c0018589030b1e06163c160a1024380030f9e028e000c2c481858f01cd8400cb0c038a100e6c201cd84039b080736100e6c100210200cb0c019618032c300658600d10c073610032c2030b1e06163c0c2c781858f04e90e0385080c2c481918c032498061624019618032c300658600cb0c0196101f81603f02c061f3c0fc0b0274870402840797540c8c601918c03231806493007cb281918700e28400d10c0196102c1c2058384038708160e101738001cdb2039b640736c80e6d900210206163c0c2c781858f00658606163c0c2c780378302e7000616241420982841301cd840a104c0b9c00295d50506260a104c14b8702c1c20583840a963c160ef81858902524406163c0c2c781858f030b1e00de0c0d9e2012925050818061624160e102c1c201c3840b0708160e102c1c10582840b07080c2c781858f03449806163c13a4381924c04ec0e0616240fc0b01f81601cd8407e05813a438270c7042f0607e1580fc078032c201aeb200cb08070e102c1420566c806163c0c9260254cc0566be0616240fc07818589058382095330160e082c1c10583820b0704160e082c1c10583820b0704160e08217820583820b0704160e0823694046d280616240c2c482a7c9046d2806192411b4a01f80f03f01e07e03c0fc0781f80f03f01e07e03c0fc2781f80f0583820b0704c38a92471c248e38495c0012b80025700028c524518a64a31491640002c8000590000a314914715d28e2ba518d64a31a914635228c6a4518d48ab8001570002ae00052e258a31ac94b89548e38491c708638e10c71c218e384390000c38ec9871d930e3b2690000c38ec98a00048e38431c7092280018500 else 0xc8c601918c0323180646300c8c601918c0323100807080084081858f0323180649300c92601924c032498090000050000032c300658606163c019618032c300658600cb0c019618185))
def leaf511k11 (i : Nat) : Nat :=
  let row := packedAt leaf511k11w ((i-415)*23) 23
  (((0xb7b2a9a7a5a4a2a1989695939291908685848382818075747372717064626153515043322110 >>> (8*((row) &&& 63))) &&& 255)) ||| (((0x2040a854041309400814080022108301a09020140142215028180e05024160920924120a0582402894448251088c0621040240204028024010884010180540a140a2412814120d0260309048a052090502c1205068220108040403008020300a81428144825028241a04402100808060100406011008402020180401018040403 >>> (27*((row >>> 6) &&& 63))) &&& 134217727) <<< 8) ||| (((0x6270b81c2e27038592c168a6522d149a45a0c0e03348ac52643a1945a2b148acd229158b452230980c2a0d02851281509148260d0a8130988c05522d14aa170a94426112144a05351a4d069351a0c46130148a25028948a04da2914984a2412898481d4c8643a1b0c86c3a190a4742a132884426128904a85028944c240d05824160d0482c150a0542c140a8340a0d0a8141a0b0482c1a09 >>> (27*((row >>> 12) &&& 63))) &&& 134217727) <<< 35) ||| (((0x8a04604068100c82421a04451081203044061100c281109060140304c20120c044200a0c02818080c0101804030088402060080c0000 >>> (18*((row >>> 18) &&& 31))) &&& 262143) <<< 62)
def leaf511xk11w (i : Nat) : Nat := (if i<1 then 0x650800360c33470523842110820001030cd1c148e1084420800040c33470533842110820001030cd1c14ce1084420800040c33470533842110820001030cd1c14ce1084420800040e36671e961a2a00cd1cbc508d99c7a5868a8033472f14236671e961a2a00cd1cbc508d99c7a5868a8033472f14236671e961a2a00cd1cbc500cd1c148e1084420800040c334705338421108200010322a2596226c958608001a0c8a8965889b0561820006833392595626c95820800360e36671e961a2a00cd1d0c504727a36676ce59308082514d7870523842110820156838d99c7ad868a8033472ee40d7870523842110820156838d99c7ad868a8033472ee4236671eb61a2a00cd1cbb9034d1c180e10844208001a0d1c1e8d99db3964c20209c54707a36676ce59308082514d78705338421108201568335ea4148710830208055a191c1e8d69db2560820209458d69c7a5868a8032c72f14235a71e961a2a00cb1cbc508d69c7a5868a8032c72f14032c70533842110820001030cb1c14ce1084420800040cd2c706238421108200068334b1c180e10844208001a0e36671eb61a2a00cb1cbc5022a2596226c958608001a0d1c1e8d99db0561820209854707a36676c1586080826148a8965889b0561820006834707a36676c15820808251432c70533842110820001030cb1c14ce1084424000040e37271e961a1a00cb1cbc508d99c7a586868032c743140334705238edd11b50001038d69c7a5868682d3474b1408a0965589d3964d0000d8322825956274e5934000360d2b90924a2a0db0040e13478d99c7a5868682d3474b14236671e961a1a0b4d1d2c5022825962274e59340001a0c8a0965f89d0561900006832f14248e8a836c010334d1c8a0965889d3964d000068322825962274e59340001a0e35a71ec61a1a034d1cbb904b1aa48e2a915c0683b4d2e35a71e961a2a0b4d1d2c508d69c7a5868a82d3474b1408a8965f89d2561900001038d99c7a5868a82d3474b1408a8965889d3964d00001038d99c7a5868680334742e409d13acf8ee1e922821955db4d2d2c6a8d9847ad2686709bd3acf8ee1e922a21955d8d69c7a5870a82d2c72f14235a71e961c2a0b4b1cbc504707a35a774958240082514aa89655889bd99cf9ae14d8d99c7a5870a82d2c74b1411c1e8d99dd2561900209858dc9c7a5870a8212c72ee4237271ec61a2a034b1cbc505979609844706273203db2a36671e961a2a00cd1cbc508d99c7ad868a8033472ee42265f78db0bb888d69c7a5868a8032c72f1409bd39cf8ee1692aa21955d8d985d3944d09209824706236616ce5130a4827091c188d685b3944c29209424706236616ce5130a4825091c988d985b3944c29209424706269a14704a731b0520d72099a6851c129cc6c14835c82669a14704a731b0520d7209 else 0x2f5a7a2961a1a00cd1cbc508e1847b526947033474313e35a11e949a19b0cd0d0c498d6847a526866c33434312635a71e961a1a00cd1d0c508d99c7a58686803347431408a09b1589fbd9a4f9851cd4786238616ce453080825111c188d685b3914c20209444707a35a76ce5930808251648e2a9169402b61d049bd38d685b3954c2ae0942470608a09655889bd9a4f9851cd22826c5627ef6693e6147351c1e8d69db3964c20209450cd1d0c508d69c7a58686808a09655889bd9a4f9851cd4727a36676ce593080825151c9e8d99db3964c20209454707a36676ce593080825151c1e8d99db3964c20209454727a36676ce593080825151c1e8d69db3964c20209454707a35a76ce593080825143347053384dd14c2000d8322a2596226c958608001a0c8a0965589b3964c2000d838d99c7a5868680334742e4236671e961a1a00cd1d0b908d99c7a5868680334742e403347053384cd14c2000d830cd1c14ce1334530800360c3347052384dd1942000d830cd1c148e1374650800360c8a8965889b2561820006838d69c7a5868a8033474314235a71e961a2a00cd1d0c500cd1c14ce1374)
def leaf511xk11 (i : Nat) : Nat :=
  let row := packedAt leaf511xk11w ((i-0)*18) 18
  (((0xa2a097928685838180797574726a686462615a585751504a484746403837343230292827262319161512050401 >>> (8*((row) &&& 63))) &&& 255)) ||| (((0x30104c2440a15082c522b048141a050181c08452280c42230120d06020984c0081408008241000442120305822050a841089448102a150020502000884340a8d46011188900a251060341204028032150e86110980c05038142215028120b05009148920924120a058241109845029108904a2110904c2080480408050051209409028341004060144825028120b04c061209140a4120506822010804010180540a140a24128142815028241a044021008080601004060110084020080c0220108040403 >>> (27*((row >>> 6) &&& 63))) &&& 134217727) <<< 8) ||| (((0xe03818189c2e070b89c0e124904a29348b4181c06643a194930904920b04915aa4522b168a428940a848a41309068260d0a8140e83017070180b24d249548b452a058285120d04a2130890a2502a0d44823c1a8d06c351a0d46c341a8d268349a8d04da2914950a050ea64321d0d8643a158a86c3a190b9542a16490482c540a0530904899442212a140a2513090341609068160a0b06824150b0501a150282c1a09 >>> (27*((row >>> 12) &&& 63))) &&& 134217727) <<< 35)
def cycle511k11w (i : Nat) : Nat := 0xa0e7e9e6749be6a9966096e569464c91e428f6388ce2e8a62487e1a8561082e06805fc7ddf27b5e878dde765d473dca715c06edb66c5ac69da26759864d8e625845fd7a5d5705ad665855c55d525354850d3e4e5344bd2a4952046d164450c41d023f4f83ccee3a4e437cda354d032cc6304bc2dcb22b4a828c9e2649423c8a214801ec761c46c19c621745814c4e124440fc3a0d4320b42808c1e0641403c0a01400
def cycle511k11 (i : Nat) : List Nat :=
  if i < 1153 then [] else
    let t := i-1153
    let a := packedAt cycle511k11w (10*t) 10
    let z := packedAt cycle511k11w (10*(t+1)) 10
    (List.range (z-a)).map (fun u => leaf511xk11 (a+u))
def w511k12 (i : Nat) : Nat := (if i<6 then (if i<3 then (if i<1 then 0x5278a298502626c6127008b0c41f81f060e9006c4c326a174e0aee04f5c23940fd50707030e015200809031d0119004740000fff827ffd89fff4a7ffd79fff567ffd88fff4a3ffd78fff463ffd68fff423ffd21fff447ffd51fff3c4b67ffbee623ffd97391ffe9b98cfff36147fffc0c6afffdf63d9ffecb187fff05965fffaec733ffd16495ffeb31ccfff419a5fff92c9b3ffd46597ffe9b16bfff7d0c57ffb289a3ffd6435bffe8230bfff351057ffa684afffdf2291ffec9207fff5c8b67ffa24a33ffce22cdffea11c8fff4c8037ffc0a09bffd7500dffe8a847fff594037ffa0a9c3ffc9508fffeaa805fff3d537fff90a933ffc55499ffe22826fff40c237ffaa6093ffcf3519ffe61a0cfff14ce3fff886597ffc2304fffec0828fff5c4f77ff9c29b7ffcc149bffe409ebfff2c4d47ff842117ffd8000bffe90066fff5c0027ffa20837ffce008dffeb0006fff40116fff9a09b7ffc90211ffe580c7fff1c0947ff880423fddfc5e17ff0498bdff7e4c677fbd26c37fd2955fbff0498bdff624b5effaf25af7fd596a5bfefb9acbff65c73ffdbf65affed2b2d3ff6859ebffb36cb5dffc105277fdf82d5dfef418fdff4a0a5fefbb05bf7fd182d3feee418fdff420a66ffc105b37fd882d3bfeb442dbff819e8effbec9b77fd9631b7fecb168dff05915fefbacd377fd16417feee32addff41964dffc08e4b7fdf4491bfeca16dbff651257fbb88cb37fd047d3ff662331dff7c8c65ffb247abf7dd26177feb92ccdff448b3fff25450fff91a397ffc751a6ffe429067ff1b48abff89a289ffc7d26affe32915fff11482fff85a61f7ff029ebdff7d4c57efbaa9abbfce53d5feee29eedff414f57fdb6a7b77fcf53cfffad28e4ffd014c4effbe66abfddc3317ff6d99cedff3ccb27feb469aaffe01397bfef89aceff785365ffb027bf7fd21315fbee8a6abff5c4f76ffa22babfdc91357ff6d89ccdff3c4d3ffeb4291bfdc414d9ffc509eabff800e4effbe07abbfde05597fec020fdff480d57efba0a2affd7035fbfe881e9ff7701365ffac07377fd00615ff6401c4ffd680e1ffe80079bfec20559ffc5024dffe18135fff06072fffa002d5ffcf828bffe600f67ff2409afff970359ffc8832bffe38135fff2c07afff9005d7ffc68349ffe24105fff160933ff8703d7ffc200e89ff5b463cffaba9bb7ddfc453deef63ac9ff82505e7fbd27ae7fd9714b3fe0ba4edfb7ed0477dbd682f7ed2b3d1fb6eda08ff372cf4efda16aae7fe083d59fef41eadf7720f5cffb2c2967fc161493fe0a1ea9ff648524ff8245ab7f9fa493dfcf526ddfe4a9147ef3b492f7f91a493fece526bdfe429247fd3748b37f8fa38dff8d526abfe80135eff3e09a3bf9e0451fbce8247ff670103eff200ca7fe880453ff8d0247ffc001637fe0e0b23fe820 else (if i<2 then 0x8870352e400972800f538036853c069d029c9b98978845722018fa00a5140f2e801bd4603b1be0680140e23300164c0348a400cee80038600243703a8c80077680f220803417005b7600c3680e414cfce4db6cc4bc44d81dc9f033f8a070c9800aec81c0120062f4801b840d41e01db240039340774040196b802c9a038f7600c1300140a01de869f9d9b6c989788820026d0068db80176b00063d034f300738a0011a981cc800037ec0741740179181cbd700593a00305c016b801d106039ee207361a7e767261c2200c015be8029d601b9781215b006deb80dadd0176960016c8060ce8022f50035a400aa6006ca184844c005024121a7c0a767261c220c80139900c0ea01991a0328700083a8019eb019ca40098a0011f580c80c00493a008994067d080c9fb0196a2000330062ff80ae25018f0c0048e40633900252c400b5e00879406687cfce814d8bcc4bb9f281bbd4003eea0066800dcd50020800036e006e09000e2181b764003bea00694c0de2401b4be0374fa06da440dae5001e9d07069c9b3c977688820026e406bc2c00113001545035ccc0059540d98500014a03578006c5fc0d6c981accc002fec06ca180095881b0bb0030b6005276726cf25e21d9c88066584831d201cc242de2c05acf80b4d8001b16402d2c2414c800b02216a3c42d98005c63800f3009025202dfa40074e800c510000d2520d8005b11100f9d9b98978173f64152000025dc054eb0006c6414cf4801b4c0024c80a840400974001d2c002d480ab7a414f3c0294510546980a7e7014c4000206d055162005df40109402aa76726c1cf25c29dae0596ed8b6ab5af8ad33d681bb3315945ac5896122af9a5764ab5c958cfab3ed54a2a78951cfa81e536f297f94ad5a4d7d201e8d55447ea1a8d073e833f4158a0945030a81253e5d9efbcf73e774539a49bd34dd7e6e0336ca9a4f4cb3a62a9302f97f04be265b812ba394cec9fb24d03262b9301c963a4add2396919c48c2242331efc8f024750a38671b3b8c5545cfa2b95141f88e2441621e070dae8564424f610c9070f82e541066058901968024bfaf5fafefc0a7d62be4e5efe6f6967aa8bc7c9dd70ec9b758fba789d006e54571beb84c9bde0dbdc6cff36265ad56d40c687db38d19980cb17644bb18f58a10c40a6138304557e8abd6e5e342e98d7108b6bc5a0e2c9ad620eaf0256acaae4153cea826534aa975148f0a2fd50c8a7f7d3d849cbd4d91a66612f0695b24a272492521008e1f464e22be9132e87c942da2102d050280d83f4a9f2b4f66479163bb99d748e77a721337cd9b8e4d9be6b56348999c34ca006366310c97fd4bc785c2f2d5216034ac00544f28f313d209b004b8224e8923c0905c4609221d104fc7eee3dc61e958ec7472da37a51b060d17065763080176b8b4b856fa2ae21 else 0x55007c09009d3452d53903e47007d7f010314127dd403fb9117381323cc881fbed040f7111ebb396bee050c9c04111007e48027d86528c4012742a726cc2625cf222541205383017d25eb18685e218355683048e00fbf2485d4c1303923015380d42241731003d91804d6840f73e2b3d386136db312f11920c0ea803e0a921f1e04e4de097e39180751a426f40d45a6146781813f80723f0097a04b921003d62007b9f839e2b9d9c8870982f3802d48e644ed088987091bff00ef9841591c8346784d00260d0fe01cb780250ba4cf2340e5a4133d7c24e4f81cf0584ce4dc24bcc44738169f600ec5c01c74803a360075403f8488455800ddf0057bd8036ed106d3d20dd3b362e8a06012250258a4006a3f0977eed2e9f425d44306a4a00d804c1a22003474111af10280843286f4e4d8018499f009e2c9d9c8887982f21029faa01a45583488806ba060d6807e4a5ea0407b28033c1829bae0582000157dc1637b8290f500c1ca0b615c152cc80659d6d6a219b283f3c99452710a388481f28033ce02b291051b5e0b7770823c7805f3300c9f2406c1002c91804dda24b6580a615c15ed480546624db180b4270a66e6a61b6662a55e04249a0057ef05c3560b834c92d7a806625052ca00aee88029af926c6c05c598481664145f21046de0094aa0b7e5c02f1d8063012034d4d252433851373530db33148ab248d9441455a02de9c208a9e0176c4150998064c400b1c601326892cb480522624d6980b38ec031b002c39900cad60ac2761a6e6a6229ce549c428bc0849aa15b51c4963c00312e80511a24d4a82a23380248002da5c246aa80a227c82229005cbb00acda0187b416dda02a09d6d6a219b9a3f988a73459b05a61a0a7d3c02e8a901d8f00be7e012fd892f240295c500a12e01794802e77920df500c18e0abb1091e8f82d5da05a80e011e761a726a621665c254d002baa920b0300905448edb402322805a100593760b2a0814f6200588a059976015a2802d820059430596d64970481645e82943a009edad53a513935310b324ae0fc0ace349385982b5a200a6ba0147e89056382b40000ab9e48e8a815c7282b712008b8a0142d415b3480522f2039520150e8027ce884e4dcc45394a9102a9f8054e0e49bc0c02404804e742410820aa3b4155a49238ce0093180113f41566f004a3f00965e0aab8c02611804d9d6d2112109c9b3c988a7245e82506b40a1670822ee10476d008d1801125414260128512008bc8411a7c8220482860905060e011e766cfcf2651400004b381aac203c0a40099f40eb55002049006eba00bd340e9808032c7001e8200d3480151281bf340344b40716840d33701c2a7006d0a053a0f3937312e7910dc00b9780e9090031310393b0003548019a081e236037d580765140d0e60017b2034afe07045801a9)) else (if i<4 then 0x36b6e02c41c19eb701c229259f179c3c6d98707e88e0066f0e0ccab40584d80d11501aba006f6f0069948336da066834063cac198df818e4a03569e0348d80df4680d09e014a0a0635bc19ab003304803697c0ccc940dfc3832faf00434803521a027cf275ce61c220c80603381aadf01867a069f840d41d00ad00065b4e02e4080625900c105031af60cba1c0d49e80c2b701636202f45e726cbca65cf1b5da216da00d18e0010ad0160ca02b3b405fa601a4dd01768080129c05cd800117903196406959405e3980bade017c588016840d35880bd9d6d9b4a2f3f973c8176735beb03173e067eb40583280acdf03409c02bf4c0021d00ad4503422602c9380057f80aec6016668068adc058ceb6ce0f0b9e3b44382fadde81653a01203e455e440bde990921321482c00d67414fcf05e65ad17a4851e6917c16030a280288108ab5c10919d039b3f2d7245f12066d60285b80172580a4d234c8480bca84046659228d404fa4a09968092af19067f40147ea01821ad750a00a2f805f274423e5c10eb6108a4fcf4ece3b4d17cc4cc3bfe4107b652438d60284f41855f8a61502614fa417fcc19647805fd42116620872688168b802dc400f6f6698734177a5008b9f9e9c9a6d988799306801380002540c015e584f3240136ce6489d804ee180989309e372058cd80443c8097602248d205279027a5d093a352950f0419a742797901875e01336e000e2802d94809a26012c376552340b7e7908e2c02313e42053c113a8f393533310e6241c80004abe8029e13431100c9ccc177580087da243510c1a8d0521f9105e0400b2800ca124845078329a604273f033c5b393530db32610e68015de5c429404e2d60229b221a174271901c8f0260d0e40583bc0428c911473191e6e0250c482b8714e29f9e09179c9a8498879930202109e2424c640aff080939601087e79321e60740242ac929771065ff01234202300002ac892e945011a1640c614047b28092810490d24bf9e0940f29225b2062bdc09e0fc131b7368bcfcf4ece3b4d97cc4bc43fef9089a5205960021c6c1238192f61224f8700c6f8883d3f921985011fb20989a89844b905d0d064c94022ea402a4fcf4e4db6cc4bc448105843011544014f9c8435690283320d5de02148c122d503226606436002382c97a0d127a2706470e484b84510cf8bcf34ce17cdb6cbcc446f908970010db609134893bfc0319e7210c180c4d14046a40277142488de4c655c8296683200a0112d2014a7e7a766e06625dcd0c0457f407b9b24494202329013afa82617024a3960c7a1898759906429063f8a014158973050089d0206094022e7e7a767221c260bef2d72b3831670010c6c0c619e0391b0088b0010fde0c5fbc0428812221904e8d4293b949279410633a009f3f3cee2f3b393110e1ee418a5804 else (if i<5 then 0xa6042706da253a30910a15308ae110ba0404450810713020fb7021f760d69ac8087303590801e0ee1238641a9970110a003f6cc04354c0c94601124602159204396c108ba81015b06ac260d6d14245cf02047b04213a05361e2f307914e6bab4083268103e282093e0414fc0837a801d8782056003cf0c082d041042c8206cd03e73c0810780f603441e22a00200800406c407989001cc402015b03f99e07c6800fd9001eb7503fed6080aac0feeb01fe340075104a7de007e3801a94a01f9ed020eb443e7500fd328108b601dd700d4370085cb81090106a28c04288c07fba00f89d9b3f0a3c45a80200e207d27047d8a81f58e020cd203d6d407eed90ac4a03e51c0413980811c819148069f9e07c460082dd81f63002064603fdd4080e681f3aa03ee942e2c0b361530188adb10bbd807c20807e6101ed1f01fd6a03f6980f71b80faeb8009d803ca641a6d700fb2003d7a60640300f7ba00f8db069d8a03e4780f64eb68b4d9281094c1e0640b9ad3710b9e803d3b403dda407af800f36203cd56122170078a700f66b01df6c03b8741a58400f06003cfd803c8f40f56980f40306996e07a271b45c84942a76617221c03401c6584834503cbac0370a419b39033f200394ca033cc00f1b801d19b03b4c00d26ec00c0a01de9d6d174925982f97885d3ceb019dec0743981a34d01dd600171b40791ac06f5f0333e203bf3a07541c19eceb68b834d8b1b441e22cd81dca401d9be030d8485bb600dbbf031d86035d540d9a081e2da01db6c0382a4055fd80cb53037860078cf40610301cffe01c86203a3040f0cfa50b97cbcc3b36ab442ec680cae50377840782600e71e01db02216b10038c3406ea200d60501d6c00cc3d80d91f80e6e203be9402a9a45c5a6d202a625d15b62175e40752301d8d701b446075e2c805f880e9c00362e60ceab00ec8a20a87b065cca02f2f80dd4d81dafe01c9bc02f8c40743881cda401a93eda5f3b312eecad02e6b5ec82a6800dcbe81d653039978034cdc0ea4400e3c8090e00039cfc0735881b06406733a0755b45a766d200a625dcd162177ac0c588834072035ebc074a6c068f88348c6414d480d09c00dc1c00e5e6068c9a074c8c0e5a780d28801c6740d2b981a0bf0344bf068f300365801a4a88343fe01c9140d16c405e949297cf9e4db6b9cc4bc46901c67701c48a06b9f00709881c94e015f3202a30c06b80032deb01908606dc800e55b00e0130165cc0d06680e3b000b6da03914803527db52a745dda60f1c22174441a06281c38b016b78034e2c06f8281c40d01bafe06b720243a200d66b01bda6029c94063be81b65a038b38da2e673a15304ae110bbb207035c19f4f80b4c301aee40cfd8c19dac033c4f01a4380361cc19d2200d69303591a0341e40c63f81c1cb0671ce0298e406332033991 else 0x8542cecd4c22c3b9ad13038ea81485f2326eac2444d04a20f06f0e2128ca4648ef0242a409229e126cac24c7b8c88dd27044008e21610504674945e6a6020fdcd721c041cbb4839ad7032c5804dcd88861201349e0498b2092970078a5824ba30733dc0e6024099600377da026d1e09058409adf8138d102635004b6389c0e88237970940421e073b35307f14e6bbb60912848d40d82470d04933809188c122ef02428f04830209227811835022c93046c3e090e76724a1a105e151a61ca1e841cb2a823f9504810e127858099c5049f09026430125f900966503824f09361a08d66424eaf849c841412859d17259808725c879d0456a408e47411d2e823d6003ce9e08f83411aef023c93046cb208199411d900238d1046e7e524e4333048bea04c1d01c073037f2804626c4433b88803402326b01deb408cf0c8958c04972106fd3c08c190244b804992b09316e04a93c11a01ceccb02f22ce822b2911f50e04afd0116b6822fba215a5208a9b409713022ee40259360dd7b41bb35022cd301e860040fdc64454012d9a025f6e04aa708416643c0d826285b61d77b00f83b821e6706e63608988c01f7090bf5b0453d8045cf40f51f83636302463c0476201b5d501f77b04213a0936545f311510ba79660485e01b8960225f2234ad808a13807b2803619906d28e1256ec0fb4601120c03deae049e5c10eceb6894d9b0b441e22f401e980040792087db0114708216d403f44c083df8106d301ee5b045262087170110ea82249b23474c084e726e1a0c60aa61b62a2008088ad020c8201f8880431b401e86821b05023790089ec4111dd0125f5091aee42c20808b6980f4d5032bb21243901aada011c57024ea4049bc00944e250185cda29e4c36c5442ee7022294217634046b5808a4b8124f001e7e40d7620100f48492dc02165c044218105d700fb6302467208699008fc341b48908cd8c24054c4536a2c42ee702224004005808968410aca01f91503ea7c08286c113588223f10433aa0891981095b81e89d9b8482048b986c8a887a06cf6604857601e4e08fb8206b0d8442b1410482811be50918f00862ac247c781225c0443da0454e411050c005ad49289e0d501c09032011f18019d9b45988a81735ac9043e34046a4808f558488f606cd4812465c0848c01054104103c0476d008e7a02175d02273b0904da23368a907e053114e710b5e007e1c40fa21020e9a040f8407b5dc10f06821b780431e20866dc8d218821c3904355607f7d010bcb821d9d9c838630986b8a881a0915da0dba8410ab390bd670929c2085aac247f40214e909251a125a90248c9049347092ac81224c0081ec84901606af4200f1641034e250285cec2a2cc1e38442eeb0114650211cc040adc0878782053701f5d8045e0808b768115b206dacc084974089960118))) else (if i<9 then (if i<7 then 0x785b089e8a960a08981280a81f5a304f58409cfd0116a40277b10446f00a06281383a12303d04f937350483162f30e715094e09ef1013fc358b28e020838051f541e71d8141352913e44e91b40976082767e276be2052cb80a2dc019878079a6e0f300c137658280059b0f9a41983f8a735df42340c609a69c13db881f41e04e54809d43410d988a17d404fbcc09b4384f6e812323d04f96c09fb7452fce4d41c5c2cc97cc38421b1499a304f43805210c64ecd09131c028ed20527980812513a69c07823209d20808b7881405b04d90623ca0daa14a09664be8436618211c177c41358c89eedb24634809d52013be082799c048dd02980388cfbe8267c104ec3209d1a8116258a1fee04f139370c2e2c8d30e515095a2469ac1354988fd5529303c09cb081399d8142160266c412b4ec0a0f2012ce6078dea0edbc40a07b81434a1714129b1605988a4584725d6b04d53a08afc4135ad020c7e04deb6095f98136c502700304e3bc08f0a812e81826ee000859a07cd6c136411f8f93ccc222b182695b04d09407c8a41153e8267e604cdf40105be651506cc090938bae4911fc4e0eb094132c383b318127a122990300f7a710084f02727e098e7484566cf05e24fd16fc530e101ed6f04be08401fd4130bc0218c714304a0994384f6ef11fa3704b68e29977452fcecd470b4342984c38448c89eee923f2840967d4130a90264e814c1b20989a85270f40061f0487c22884fc131cecdc743420b13354c4544c988fd7926f0c64426f012c07091b6f04bf9804f588256a9826099093a8c0e9508650a4013e80175308422c2b3a4b3679304914e512b57809614811ca10259c504122809716c12b9b825b2a04ba360978780f656025a12893f455d2189ae095b6807bc3849e3e06fb200e2c34124ef84a79a094496092cf42562d023326045c180e0d3c11f0d0040f2073cc80e5298129ce02824ecd4c234cae10ab839cc9072216094b448d4a582554e01ec7a12b33009d8203898104908e1256fc09c4d012f4f02730828253b1332782d049e8ad6469fa00f4eb825695048036091f8410b540a42590494960955a01192e823de9049d680946726a4a1a0e2214aa6661b61d2c24d1302508009523a12abb0858b480f51602679a0dec7c1c34e0246cb02785232476809b66013b450943c609537811e69003fd909213895350a2f31268adb330ebb5a093dcc860f800f3f91937be129d501bd3b04a8a6070a460917a4249308135700932ca08efc448aaf849c8381691285160e9a2508986d995c8755047e4c09436c122508215ad049e160948a0118fa022d1d0475680946dc0f45302539d9a92848b85179873872911f41e4df31c09d2902391f049a301296ac247b3838f4a207bc0129114250f4824eec01e5a452366424ea803791f0487e224553c09c82 else (if i<8 then 0x201be28d9ed02bbd01008a80acf4015c9702b6c0101af017653110eff2527c34319d4204b804081f080e0b3f3d362edb2f31139a4dc7581ddb284bef022965205609c1d651139ce525b12212fc94c9efb01563907b9ee0a42200cc9e02e947092a12d2d16c1ea8eb3e60223a4f8cba9700abfe81531107e2c2a39610fc845c527e7a749a723c9660be1e21fde496b45828e1c07bba00b9e588718832e8d2097b14d2c84025b8c34b9d3096cec12f27e7a70142c24c676621e2175441456a8069a1042ac6cb91200352e02e8d605cd76a72f40173ef32e53c05d2b249da481752712b68e34c13f3d3b1b2c7f3110e70f7a4e1c9c1f40c03ea00252eec0fb81025c094cb15902a8240a259488dd5848f8c07db1001a25c172e481527c51b22012dd441f64f81519d07d7fa054c001dcf203eff007d20a033f3c4b3b030f30e65f8a0f84cc5b3269141860969fe4e59089554114ad9607b0a80a22200344e04b2ba0967481245980a86703e0b807a2f40f7b641721514b15c07bf7ca34a8825acfcf4b15ce9f97c44c43b9ca5a02de7a236c000b5a14167de02c4a40562fa0b8ca815c5b82dc6605463e0b55b4f084a4a26516bc16e8002d640059abe0abf9415bdb82dc5605338640ef6816a2182bf73453f781093d04a0ec016ccd82d3c70578000b59e816b8802c96a052e5e0aa8a49035a82b6e505b0440aea6e6904f084a5b6611629ccb4156d982b585059e800b36f016245828ecd05a39a4109301670911bb43057e240b4a3016836b59e144ca28b91b53400ae780a74781462082a8c70579280b1f1c15a5e02c45415100a0ae7dc1630482862f2478c00b0d5c162ce4d3c9e149436cccc12c2b87c02a77e0566a00aef1c15e090289ae0583800a4c1415ce01285860581760158a815f1a120c220575380b095c15ea182bf9d9a6d3c869825857370222373380ac8b4156c5828ea40562be0abd5814cb302a3c7055cd60ac041c8f114081492d02853c053a3c0a311091bb602a60d053eec0a1ec4150bb91b4de2473bc012a0814f350297660547680a815c152a902a40105453936422420db308b14e4040a498880cb7029a25052c240a260c14d9e9209c005279c01254814e1e1204950508ac0a652014ab502972c05317a0a52766de9b4844261b11629c9441450f028c0300902e46e05c147c8828d120512ec0a1e2c1474c828b540511ee0a40509372682910905069249767671e1b44842621495c9c12c1415a814e78095c5c12bc44859e2027f8e020c380520ec0a17913a86d045e880f11bc1e56082797e076e9c2477c40a65c03bdad00860609c4ac4f8769234b604fc7c05367d28126d04966a60bca66612298d77581dda488fed404faf00a07c40a666013b18127a7c4687c40a5dd81f69a025ee20f0a701e477027857024f04d429371332 else 0x5f900234d583b42004030a9f9e9c459b849798886008c0dc110d4c8df5d1139c90723781185188a9de04282402fb620673009e41693612600f05c10c61c1d9c8817bfb09a7741157b40aea292c127a1b012d2d1580be1791385702fdf00be55c152ab81276151cb380bfa09b8fc827e79b270aa6cbd165e621221fd354724402fdb5294b880e41040ba941360820764e605eba00ae2012c022a1ae081332ec0b8bb016d2a2940a405e7cc17c2902a452024d3f3937082a1b2e5ead453110b2c4434db4265e004359f099c8413461c2692a12bfcf296f14d2c81c17bb302a3ab05f93f3d380616132e6341310910ba6e0bed900b4780174d726be620ec5a80bbcb815bef257db244dc041510081679c6f6e9744887f408805fa6e0bee7c959c0d1c06365c9124906c417fa902f6b1054362088eed4e59192432340e5a401d31c17a5582fc9c05fd3f3d370409092f2ad931119610fc5ca4e93038e190892321097cc0b98e93c625089536111d1c83445842f79099b444a9e128693301508c22656805c95417add8171b405417c45aad008e768448be51a5e0111810039c14fa2904f1f984dc2444bcc39d182ebfb257bca49283417d06829f0d0436a40bd8608debf924e7f00e45c01c42c9728382f75505ebf00be7cc17c4fcf4e41a001c24acc38446e816ce70847ba01c1609aeac842db2171e04132b9421b8c015a70257604c1a16889ac1016e82053d04045b1c17a5f116af4322b1a05bdd80b6c011519f83209e0f179c84309870886632004fea066cb80b31883c56b25d9fa4e3160a0b7392114025396c107bcc179a9029cd725e6d0058b4c1c65e02ec1c204eb60847289e2bd806ff0082dbe458a7c627a766d16625c5ecc090de81652e02cc5c4e2798a0d0c1112712537f013209017941829b4622a6104bcba08b28203899d0835da057534812e413ff8c0224c40fffec9e17e815372004a6a0669c41e1141121ab22ba341326120854467e7a7498926e41145e625e0e21ffbc2638782f16e05346253139ca609404c1f325e3de0e23602603b848ee809884010304e24a4b14c0ad4928504e2048a4735929a882f2c9765985617d42987f2102cc8262a21299d7098dee0bc15814ce794b710096fb64bc1b0261cfcf0d00cecd984c4bc0bfc4add182eb0320488408383c178e312ee280046480bcb78910b7a06a780431e60bcf749079b1298f600dbee0bc12014a8592e5cd05df3f3d3b203103312ae113721044a0208530161b902c6660bb8a0260c404c21802b4e4103fcc9fedb810f8d07f71001a1c80b04e80229c0782a6447fb408ab4016268270a40103948888559296bd05290045467e78b03e74c2405e0e61c223688988102eda305d6040a48080889404051802b5060e11d82050e04047608039840851c9fd6c04c0e107f2f44f0280)) else (if i<11 then (if i<10 then 0xc27de304ed0f065224121a767269b0614494588e6136661d516de4990ecdcb87009d87e13bef02428104ca72081fde0c5f1c2749b84f03125c0860b2e7269b059c66661b61d816d9c18b6cdcb87009d97213b8fc2744404c2a925bf760b2b18276a003284309093b342c10613064cf0ee6b7296fad209911f84e80e09d5100c9d282758104ca8809858e13a4009708902c89d9c6c083098523187725de171b19a4da49c5d70f947ce5258c1644efd88c2fb82c616030bc011f0f098ae6013b9906d23b51d4088e0c184e77f0383fc13989e86c04b4b4c678ebc66ebacae5a3f8186350335640c54fca484567e7a72205a6a4494c26212661dfec0272d512c4bc0588024c5186e596390d64401ade2137229a597d040d7706280853729c2724fcf4e4d0b84cccc4243b02d830324c1261e520c7f341904991dd0d064d3c0c71b9b45c405a21fd8c98283032418259d960c78a815c379319352387764b9d0018d3b831438064b3f3d39362ed2da5f2f3111424b7acc15afc0319be23b7de4bf2f818e9c031b400635f64c35dc18a4f031c9f9e9d9c8017988870b52587b649431c15a0603139c048d2c02100e98a6911c0ef010b056b913e98abb83140f15c980e702c818acfcf4e20130bb69e4c44381a04743206184600f8889f3eb03109c21ce2c0c4a9c26efd14511e09c1b2137e7440126c64be625e2174f2942391904c54209a3460c2e4c9f223830f0d23ab0e0c45aca26bb04bc9d6d179b3616883c453d0615380acb841875391ccb2060c20cba3909838b0312870623b64bc26496a4fcf4e4dc1b6984c4bc46a14c392259a8a0c2690158f4830daf290e6a52dbc426e5904e10d287030d2e47827041b48c0b8b0d82cdcb854c22b6c42ef0830e72060ba00b9fa4186eb031047061eb24adeac17e0603086b05613f3d3b37052c49312ed9100411c134957cf84ce00060ebe0abda4a6772130735296d5a537f4c25b6c84df84826d161a049d029b98978845735bc323a87a0c2914184800307320619460c2fdc1785a92dd0705ef8e0ab8301844fcf4ece41984c38443684cb2d055b7c4f89c81829c10e669299c70137ac81837884dca709bad8130ca896e4fcf41b68c0b8d81ce854c22b8442eb404dac9060774020ee49f0b6a303ad060922512a7026c6d1be16749b13ada2e206a4a5f312f10ba78c4135da026d0f04db2d49afd64b6d98a59909cb39e0605fa0ab1091813314469c9b1b17692f9798566d885d6209ae440aa6cc9efb38300a70602d2136484e59d394cd9c09b0c213587cd6d4e400bcecc18b8442e8102ed2d08a1401355689611e51c2d008c9120607f02335f84654424981a0be9b01531d04687653a7620bfddc86a930180e902ff0405bbb41cab20182b803070a11ab540cf7213cb0a087adc119ed00b91380795126c8ae0 else 0xd22f937b2327414a0e9de41d169148d99069be24dd5181d2ed90ff4f06a93c0e99046c5dae24fd15281d0071379e50918324e888c9d03c83a29b07429e43e1401bc8913a17401f10a7f12788b6a12ace61c599c948d60b4253140c438b339291ac6e0387a1072d364d5fb41b72b839c740701f2326c9009a18839f6d025c8a1287ec1cd81834cf2073c8e0e766a18583d04845db4da60fcc1ce1f701c3dc039238071a4c0e38f81c9eb8196c90723cc0dff101c841838467071f8a0e07b41cae980f4d90921f046357c1be2f849c640729390c801e2eda426d307860e50fb80e1d2c1c548038bab091f060e138c8600f8386ef07114c0e14200780203892106fd7c4d613c24de9838ced06eda204c6f49ab4ec23d0e8c45b51b4c0ba2b9c3a5849a9b26ae1e4df21c095d0134bc32257f64e0c741a5e283810c0707940e08581abee93828e2702be0df1bcfc74da6538a45a09b5146824569134ef502607c0df7341bdaa037a0f06f1800dded80775f13589b06eaa00de57c1be37948d0bc1391e22c001296b0404262d0278b1022c4a78bb4a42e9c108ceb01fe6d1674813c58813c3f5d7806e36a0653b41b77003521a0234a40dd2d407eb383730502371c0411a41af0e0370b706de0e0dcac81b681834c9b4818168b6d4c4198733c8a88a50232b607f1b4291604f161b42a0488f175e81b3f503687d06cb7246335808a3480f56906bc6c0db3d81b35381939906d2020d47b41b5298192d30321b21242201b5ce41a0432f36b5982ecc1e45445a81942f06c8ec0d8aac247f9035d6906bd6e0d7170078a80361a70327700d40e40c8f600f23f06c6500d83540cae4810e5d0227980d7e75b520622ce0ba61c1ccf22a22a0080410358440219ea1234741a58b03575b06adb60d39bca4584979b49555b088572848c5a21f28c042914245e280f9813c6f6c0f5c551a0915da041dac077a4034f1906a7320d3590244f203554f06a8da7824debcd64aab664c99e48f279832cf603a1460c2ca418ffd932ab62622ded84231322d04ff3e52ba52df903043e48264b0a410fc02808710eb88065716037eb02801c04defe03149613fd0420bdf031d9009f89653840427f7704fd0025c7cc0624fc0500902d29f9e9c9a8c540319179d23999860875b7427ebcc10e8a09927711df1f29a3dc13f5a01953580de2108293c0c729c2723b04bc846c189d88993f16824e45c2263d10473ae497bc4032b050389640c18e018de2930968065420cba1e896ac602d09f9e9c9a8381190e996d988773259eda132e14167e5131a9021bb82532e4027e0680dd16b9732653f30c20920031a1869733f3d06d8d20b102c07326130dac10eb64813e9d80c46184f7b908226c0c60fc277bc84f60e09d4f04b897827c5b809f8a05985213e49827a8ddbefcf2646180279d) else (if i<12 then 0x4c4f107f8ac4d6dc020ce0bc0c08083710daa676fb30e02ff24fa90420bd80415a0080600432830209e1841210096ff41034940639084146c0987e0105a76415200d8620cce61145dc221e81b3fa819bf3718dbe4649789c313540bf802bc2532c7e42058f83861902bf0d5035c80b00a10c6d2a334a60648802067d040d39018dc34318d40cd779367c178190112c6410231f5b45e0e60c1c222941e1a5838a3a07fc5e1002341fdf083f941218a080ff7c41fe33010d6207fe380fe27c1fd56a4944b077e364d6621b4ecd46859da61d45dec9a33d83f37607ddb4ad2bf41fadc03e4b107ef220fd9d825e4131908c0b882ec40b3f9e3d83f3b167c7544d16941f87303f49e67ca12ad14901f29633f0e707c73874342e6661305ea80f64995eeb683f27926e57e0eb5d81e91c33e21d09733812ca415a05283f02407cb66cfa8441f8b081552e279aa63074d8fb305f464f74dd5a18d83e75a07c5700f90381f30804b72407cbdccf7b4c25b7383e39d8f841a30812f98613f8773a327ba42053fb41b70edbdd9409622532c6a19ee932bdd1c07bb984db8525eec40199a523303c453f794ccef83a92a2962c52666e00cc6d13a9424140166d3f3c98883087739e079ec00f6d142582c936f5407b3700f5de49b96d83da9607b0764e74e41ee4e1d0dbb1e97cf03cf8207a8ce1251ec9a15f83ad7607a5b40f43f41e9d083d6b807a2b60f55e09e62203b8ed0779387434302eed305f080a1ec686b0cd64666a11b1890562083e105cfd756c13411014a6b728422a1305884721605225d2911f5124dfe684898803c96f0794e605184c9aabd83cbda026c72064514250f303c62e028baa06540c1e38003b9a8025b380f22b81e04d4328211e170f878b4c1f982e39b8425e8144e604cc3136704b08e4b01f082c78bb5a2468c41e28d9353a507860404467047daf137e050236880f107c1c34e03c150215dda0dd8001dcba81014b077ee20f08ac9aa5703c09b7a501f16188b366a9845178a84733316cdac0eefcc1da9603be101320504e9f489c05c03bddf0753e20500148c58283ba300207b21242e00cc2203b8ed0778000ee671005c3e2e618d70bdca11c12c24d0e93b7d60747e60ed65809fe913a37e076e504e9c4c9aad283a7cb269efc4ed5201a7fa83b6e406aa104edb348955b812a6f3f3c1e1b39994116846b4501215483062e447ebbfd12290a053c1a0909f942d1040a9833f3c5d9a17674c065e0807e0713790e1237642e3c1408db310a567071fec0ec21c1d9c103b2310762f22ec9009a83d89975d0755e62ec60c9bbd583b49b862118266d4c72983f8a89a6032e0d029b245b39383ac440748fa0ebeac247880990bf075bc04d49e41d12483aedf0752ba0ea908650ab03ab9d7841188b382f98723f7089d60746dc0ea1101 else 0x5284722b27edf01202e0a39349462bb08fd144cf69c27203833daf08c5220fda661209b0a4855d38586115fdd4a39ed933c580678014cf38aa388284718b78e33c11cc60a38e4bb3cbb08fda611fdb0dcd06c685a64c00099c0e84aa7d06ca4a11dc1c23c950478b008f7be11f4f45e8f7047ae008f8b22eac6023b76836a6c37341a6f1699300208e06811d2cdd9dd28472f908160a11c678239ea1339f109b914d2ca12def2884759c837b1b6d304d983c88702fcf08ad961179e822e0c8449bc08c28e0611d82050a046fb0a67f241113f4236dc139ae00853d4ad27ac99ba904325202f33411b174235ec046e9f9e9c9b845117057d372f97409888d008c826118f695a56d93334209a3cc10eb389f70c044dae09a96c1175d4204d784629107ed08dca82e2c201cbb10fe79374cf9f42211a044fef087996117b555a46b1332ec02f1c210e72422989844cb608bac0116fec22fb804089b8468173633164b977f98884a08b0581105e822e422b475908b30a4cc7b00bc3c0452c20896c0116fc822d0f840754513f8445887fa727319e1158d0227e78426d956831c4d8904218208175f002e9ca10df24229bc045286086d741155e45d97b9434bb02ed7605c63c22a57533a900880e0115e7e7a6c7058825dfd5a61ccb42281a044f37286a6ead0e7c2672184387b08a3e2113b3ca5b8c044d13089984112c3299df733de9b821a0284309788985b3f737d08845811072c21fb70443ef08787c0e4ca0202b513999208892410921821b4e918f04085d364f24102664804407602dbda11167e7a705df4dd026221c0189981b943506087cda132fbc21e7c93ea430870ca05c39821d708439a0080714d2c82821eec843b9c54518436170f984830887038271f204678e00b573816937286aa645a44a658eb8196c0086b072366c40ce33838f470869b205ae1821b3e28d935a169ee50d2b48cb6a819e2a02b3aa0656f88b51b91954d033bd850d8b9452e10fcf26220c1cdc134215f093c77208669c4d72d4a52b2016859085b1c4d890421845842f2e0863c28513a020111042c04085d364f25a421029043252083f3936362edc2cc92ef8b310edce108f3c2131c038d3e0726321096f02142a842a760803ec0ec2c0211490424b8272fc2851380214bc8bb2ea08425c109da421075932f52083ea40498040b3cd9e0b900b253b25cc443ac494147607ddd6033890a049904c5b6083d9c4fb88420a3a8409d5219dc21071b58d50584841145dfe24f03ca033b841db92832de5056c020a86041360080d8043360ca09b80419e5019bc2107220ecd600d8ccbe625c5dd420c0293c34b0714501304702023e10ccbb06b5601054fca075080c99d0835da05915c9ff74))))
def leaf511xk12w (i : Nat) : Nat := 0xe7055283020705d20aa506040e0ba4154a0c081c17482c941810382e705528b020705d20aa516040a0ba4154a2c081c17482c945810272e905928b0204e5ce0aa516040a0b9c154a2c081c17482a941c10482e9059283820905ce0aa61704120b9c154a2e08241
def leaf511xk12 (i : Nat) : Nat :=
  let row := packedAt leaf511xk12w ((i-0)*11) 11
  (((0x8572573823 >>> (8*((row) &&& 7))) &&& 255)) ||| (((0x40413098002210821128900205008a0522104024009028340a81428110084 >>> (27*((row >>> 3) &&& 15))) &&& 134217727) <<< 8) ||| (((0x6171381848a412a8160a14426111368a451d4c8642c920904a85028583412 >>> (27*((row >>> 7) &&& 15))) &&& 134217727) <<< 35)
def cycle511k12w (i : Nat) : Nat := 0x971a0bc6ec96a84678c941e28280
def cycle511k12 (i : Nat) : List Nat :=
  if i < 226 then [] else
    let t := i-226
    let a := packedAt cycle511k12w (7*t) 7
    let z := packedAt cycle511k12w (7*(t+1)) 7
    (List.range (z-a)).map (fun u => leaf511xk12 (a+u))
def w511k13 (i : Nat) : Nat := (if i<1 then 0x23d9669f81f8603d8a866d715eea067e193c5803992802740671083e1205e8c3de6e9968ad53da86502a990d03a9706594339f1839401544303b4485e519326e33b6d05b2a958d836535864cc137870666c1ad76063d50341700a9d8647783a7d020de3395080b0706368364dab3ada91917b3a580398c5de3f7ab1cd092061fb0474f0bb750c11f143bc2a1c2066940be890bca70c3d405ffc13abe24c87063f40c5cf0c21b0c42b065a40677f055cb15af122b6005ea40646e03bfc0625a0bf1b060d22b54d04b240bd4f0c028827d6716ba474140b4941baf3052e305b070b9a00b566044c60bab5144da1b61305de50b8fc13ae22adda0b63d1b9cc23c25059d805c3515d6c1b83a0b7cb15abc15bbf03a4d1526c05a0120028c20de70cb26887f0e53a0e46704df30520a0b1620b37c0b0be053dd0e38422dfe05601039f0058ae04e650ad7f055e50b2b70af3404ffa04106054c1051720505e2a3640578104c360e24d04b330ae28c5b3eb0e25aef37d8239d82133022158546f822ff053d29160f82458020070560081c818523c855090509c053138234c81ef1021bf85126052c2824fd020f681e3701daa051d78559f81fb5054cb81f5f81d3a02548a31077acd9e93c7811261335c924c304be10330982e8e8154712bc303b6890a71114c20147180a3a13b01014f30429411142824f7104b411435804a41153202be792e9083e261429062ef36a3e8d9c5ab7a1d821521040f013908036700d429adeb83caa00f13112f090dbf1244201443831ab045ec02e2992b5714eb4947cb10986050540079cdba5583ff6910f79bd62f637e109070074fdb9a504c8883f299100c84dd80202510c8c81349812cb002e904d7d1a25084c2603c6480ee9012799237e0315080b268a96412a745c59f7ac5ec68f02292061e305b5e253b90947428da1211170955401eb300d44274f801fbe20738021c901d3404f1c2812b2655109340020fb81a9824565092ef37acdaa77c487d82515d8161b2108c0886d019ce01a2d00cbe2727241ab201bae04ec008796280a5343a1016c6089a701c12243df3721b0606c05ae8b8b36f59b54e06406fa0261c01c5a019c84b26c0d2c20d96601ae04bf2c0dd0a02480021ba47d540dbc60296a0d76449b540d01a0e3900e1ea0175001f300de140d498023b2eb38b5d34e40374b00a2100611032c5007e40318b00105008960055e038f4036e902e5f034f802b1e0307f0026502c3202f6b009d30003a02d9503525004500337d0032f77acdaa7a67e6f7909e1a27a1db8f636161c4ec112b3a0cc2b288c82018b043d0870000419ffe997d9ffd93859ffd8375bffd92957ffd828d9ffd52817ffd32819ffd80719ffd5075bffd307d9ffd206a17fe99611fde335d77fd935d1fee225977fd92653ffa00651ff920 else 0x709507201bb904f488484d0696296e0b84af494f521480707087066060507e1663706e5814abb11beca4188393ce57a2584b36155b904f3a8608d03aa20736305d20972ce0772b97542138cb03713de569076cc86b6d94a508781c0535091ae9141d084f8d84e8f0182d077e5845411dc948766a067a88499184e6f147778311f7ac5ae6a2584b718b94a397c0152c304bac06f6d0db6916fb596f4c136df12a87070d5036c986ff7bc93f82aa6052bc811f354b6856f5a917e901219017ed517de3393cbef370706f9b94b1db32db91954bf4067328490ba7e3f581dae689c8738796c0f1618d03aa2073198477704610048c5954ac06f488484a05f7285c02074b01727283d5d8753b074519380a075fa841ab045da835a3164fd046e01199d047e58451b07177921883bd66d53d3ec11c154c9002048435c188b9b4949b406470060441f9f02c1bc377e49cdbc34d90355ccb03d420e643590c20380a93982178435384210e82de40209b4366801df2c363e09b36a8bef19c9b8371a436c6036b889402821aac1fc281a841ef29ac8eb63e61222793bc2868aec0b330227083ef0957cc9681e167e591f92134cd0697200bf283d6b83c9b034fc939dd93ca603c5b857a80685003b801)
def w511k14 (i : Nat) : Nat := 0x178027324e2833c09a8403ff251284050899e426c239c83dc80cea0a4407630250490720b9c282b93a1083f4113702cb0049c97320ddb219c01e848036451e00560105c10090401c0c050200c0401827ff
def levels511 : Nat → Level
  | 9 => ⟨70,0,0,0,0,0,20,[(3,0),(4,5),(4,18),(4,29),(5,45)],0x2ddb32bbaaa99a225575dd6751d270db56d0dc36cd92eaccaeeaaa66889563371dc3709b56d19860d532eaaaa22558cdb96d5b46619354d5295633889a564d8360981601525453028622801524c920,14,none,w511k9⟩
  | 10 => ⟨735,69,12,3,3,7,22,[(4,0),(6,13),(6,46),(6,86)],0xb32bbaaa99a22558cdcb729c9721c7719c5711c3709c1701ba6e5b86d5b46cdb16a5a8695a36619564d8560d8154d525453132cca324ba2e4a9aeeaaa668895633889ba6e5b86d5b46cdb26c5b06a5a8695a368998655936498560d8260553549514c931484ba2e4b12a4a1aaa99a22558ce22845a96a1a568da2685a06619564d9261583609816015354951541324c530484a92863388a0064d9260d8260152541324c120,7,(some 0xf01f80bc03c10e06701341da0ac06583ac1540c908c83a05501a80c3829818a1130510e885424611d08641de0ec07583a41d00e207083701b20d106783341960ca06483081800b905b02d41660ad053029412408e04182080f407703b01cc0e006d03601a80d005c029813c09803f01e80e806602d015007c03801b00d00640300130048018008000),w511k10⟩
  | 11 => ⟨1282,415,16,4,5,10,16,[(4,0),(6,13),(6,46)],0xaeeaaa66889563388a116e9b96e1b76d5b46cdb26c5b06a5a8695a3689a16619564d92615836098160153549514c931484ba2e4b12a4a1aaa99a22558ce22845a96a1a568da2685a06619564d9261583609816015354951541324c530484a92863388a0064d9260d8260152541324c120,9,(some 0xe0ee09e08e07e06e05e04e03e02e01c10c0ec0cc0ac09c08c07c06c05c04c03a11a0ea0da0ca0aa09a08a07a06a05a04a02a0187a83c83a82b82a82882081c81a81080c80a80980880780680580480371261261161060f60e60c60a60960860760660560460247d47c47a44e44d44944643f43a42b42a42842041d41c41b41a41941040e40c40a40840740640427d27a24e24d24a24924824724624223e23b23a22c22a22822722622522221821120e20b20a2092072060f40f30f10f00ef0ed0eb0ea0e90e80e60e50e40e30e20e10e00df0de0dd0dc0db0da0d90d80d50d30d20cf0ce0cd0cb0ca0c90c80c70c60c50c40c30c20c10c00bf0bd0bc0bb0ba0b90b70b60b50b40b20b00ad0ac0aa0a70a60a50a30a20a009e09d09c09b09a09909809709609509409309108d08c08b08808708308208107f07d07c07b07a07807707607507407307107006f06e06d06c06b06a06906806406305e05d05c05605505405305205105004f04e04d04c04b04a04904804604504404304204104003f03e03c03b03a03903803703603503403303203103002f02e02d02c02b02a02902802702602502402302202102001f01d01c01b01a01901801701601401301201000e00d00c00a009008007006005004001000),w511k11⟩
  | 12 => ⟨241,226,17,5,6,11,10,[(4,0),(6,14)],0x2aaa66889563388a116a5a8695a3689a168198655936498560d826058054d52545504c9314c1212a4a1a663388a0064d9260d8260152541324c120,8,(some 0x18430660ac1382303e06c0b81301e02c0344a3d44d87f0ea15c2a8510820ec1a8230420740c8150260440780d016023124f49391fa3b4568a91321d4248450820f41c83105a0a41282103a0640a811011121d63a0738e31c43806f0d519e334658c918c314608c01782e85c8b615a2a4530a51402704b89411822c418820fa1f03d0780ee1d83a8730da1b03586a0d21a03185e0ba1702a8540a61442784e09a1302504909011c230440841001f83e0780ec1d03906e0d41a03205c0b41602b0540a0138260420800e81c03405c0901001c0300580a0120200380600a01001801),w511k12⟩
  | 13 => ⟨18,18,14,5,6,8,10,[],0,5,(some 0x8260881e068160480e028047a1b46a1384d0fc3a0a820048110400e0300a0240801c0601404),w511k13⟩
  | 14 => ⟨1,1,0,4,6,5,0,[],0,9,none,w511k14⟩
  | _ => emptyLevel
def leaves511 : Nat → Nat → Nat
  | 9 => leaf511k9
  | 10 => leaf511k10
  | 11 => leaf511k11
  | _ => fun _ => 0
def cycles511 : Nat → Nat → List Nat
  | 10 => cycle511k10
  | 11 => cycle511k11
  | 12 => cycle511k12
  | _ => fun _ => []
def chart511 : Chart := ⟨511,15,9,8,sampleColumns 465 #[(0x30d8b531b15c7c0c000000000000000003ffc003ffc000003ffc4c10398cc00b1801080fc64c4481d3200821075b3090d9a33c9401c73e21f673,0xa230e5558e082415115115115115115115115115115115115104c10098c400b18010804c6444480d3200821014b100048a11c94000112209631),(0x22616d90392873c000000000000003ffc000000000003fffffe10a52610c040206430b2187c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x13550e1220318602a08e08e08e08e08e08e08e08e08e08e08e08e10a5261080402064309218180002040b30c6249420210200402162a448c24846),(0x1403fab42d8e00ff0000000000003ffc000000000003fffffc0000001c01f2583c181c13c6072081863c4010038e7c98c38470f188738f1078f9c,0x802d0a10e8800700c50c50c50c50c50c50c50c50c50c50c50c50000040052583c181c12c606208080144010008014984384705188508b1058298),(0x7d7849ce0c02d7c0000003ffc000000000003ffc003ffc000000600607e0080c000601c07f8070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x5492214f1202c0c81a41a41a41a41a41a41a41a41a41a41a41a4600002a0080c000600000a8070a07c003e0340f8020bc0280ae0283700680d60),(0x14090a0a41c1800000000000000000000003fffffc00000000380c7f80031f001f801ff800380ff8007c007ff000ff0007ff000ffc001fff000,0x14080a0a41c1802a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4b80c7f00031f001f801fb0003805f0007c004be000df00056e000d7c001976000),(0x8181210222016000003ffc003ffc000003ffc00000000000000000f800003e0001fffe000003ff000007fff800000fffff800000fffffe000000,0x194210aa10060a006c06c06c06c06c06c06c06c06c06c06c06c000000003e0000ae5200000299000005534800000fffb7000000fffeec000000),(0x200000840008003ffc000000000003ffc000000000000000003ff0000003ffffe0000000003fffffff8000000000fffffffffff000000000000,0x200000840008000370370370370370370370370370370370370e50000003e9d4a0000000003fffdfbf0000000000fdefdffbfde000000000000),(0x10000000012690000000000003fffffc000000000000000000003ffffffffc000000000000003fffffffffffffffff00000000000000000000000,0x10000000012690003383383383383383383383383383383383383ffffbffac00000000000000166f7febaacb7f7feb00000000000000000000000),(0x1fc01c204482e0003ffffffffc000000000000000000000000003fffffffffffffffffffffffc0000000000000000000000000000000000000000,0x1a841c6200c790203c03c03c03c03c03c03c03c03c03c03c03c031afffd5fc162b551adfff57c0000000000000000000000000000000000000000)],colTree 0x800ac0004e400780000f28043c20e014041d20680a01270832050218c11902840c608c214005e10604a0451822a051006d014428414608a21400bc0050ca800f0828250038c11142a009c20889404b120430a005a90214500398210928017240831400bc2040ca080bc01c051005e00c8280a62046414033801310a009e001865044c408c22c003c206094093801304a02a60056052005e00a828068c105414015c0028ca10a6005445005b000932822c2044914414c00a48b002708122500d88208c2802e204451401780021ca409c0090a50421e0070280b180138140097801a0a10c6004c451021e00582c0146082a1403a801150a20c6004a45026a004512a026204251401b801114a4043c0070500730023228038c101494015940098a00ad2004a50256100232803c8000d95016102068a40d40082a500f80200e2803c410069401e40802ca20ac2000e50478020072803c80005d4007300632a00598029950038c011ca8028e005c54014b002d2a00a98015860097841803050c608c019021e10500c145182280604b18212032049c20881820e304410c802f0820268087840c0302a620460180b3801300c480bc014060953002a031802f004418057102220d103182108620ce004843002f8004198117102208c30a6005046224e00481304b18013018508780140d0451820a06116300250320a6204241803b801110c889881084618630024236003c20209809b801104c02e60046062025e0028304398011119056102060d007182028620ea004143222c204091b004e10044c44d4008226812c4800c3202e204051881b801014c24ac200066802f080033023c81001d800cf004c0e000f803c07004e400c638029c00589c01ac0014ce0037803207002ec014438017c00a09c00d7004a0e006f002427003b801113801e600861c013e00304e00ae801447005e8008538033a00311c01b500128e00ee000467007a800153803e200071c01f80001ce812f0820070a38c110039a02f00401e286304200e0ab881100722ce0048038ca9801401f021e10100f1451820807454c4084038177002201c658c00900e484bc0040709730022039a10f00081f024e10040e8ab081020722ea00410388b9801081cc09780020e82b88101078838c100439077002021d117102008e30e6004047c017840013913700200dc00a700562e00b18013970071c003840007e00e020005f006810004f802c08002dc014840017a00a12000bd204090009e8018480057800a14002dc0048a0017900219000d7000a28006e400464003780021a001ce000c5000ada004880079800194003d80009a001e6080250007d802088002f401024001fc0080a001d7000a1000fa8001480079800094003f40002a0d097800011812f0800088a38c1000422ae20400208bb801001032e6004018002bc0150c001ce008c60015b00293000b3801318005cc008c4801be00902400f7004212025e902009005f400824802fc0040a4019f00181200df0008290077800214812b680102401ed00049200f9800189007e400064882b680022401fc0000d3005e900049047982001c800fe00c064017700221424ada0000a812f480005027cc10002c00bf00501600de80084b007b80011d8027e00606c015f00283600b780121b005ec0084d8035e00286c01e700061800fe80004c007f80001e001fe00807001df00083800fb80011c007ec0004e802fe00407401bf00103a00f780020f007fc0000 246 0 6,#[[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]],cutoff 15 levels511,leaves511,cycles511⟩
def jobs511_0 : List Ticket := [(9,0,70,0,0,0),(10,0,24,9,0,0),(10,24,38,10,0,0),(10,62,7,11,0,0),(10,69,96,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j511_0 : reports chart511 jobs511_0 := by
  simp only [jobs511_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs511_1 : List Ticket := [(10,165,96,0,0,0),(10,261,96,0,0,0),(10,357,96,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j511_1 : reports chart511 jobs511_1 := by
  simp only [jobs511_1,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs511_2 : List Ticket := [(10,453,96,0,0,0),(10,549,96,0,0,0),(10,645,90,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j511_2 : reports chart511 jobs511_2 := by
  simp only [jobs511_2,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs511_3 : List Ticket := [(11,0,4,9,0,0),(11,4,88,10,0,1),(11,92,73,10,0,1),(11,165,88,11,0,1)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j511_3 : reports chart511 jobs511_3 := by
  simp only [jobs511_3,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs511_4 : List Ticket := [(11,253,88,11,0,1),(11,341,54,11,0,0),(11,395,20,12,0,0),(11,415,96,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j511_4 : reports chart511 jobs511_4 := by
  simp only [jobs511_4,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs511_5 : List Ticket := [(11,511,96,0,0,0),(11,607,96,0,0,0),(11,703,96,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j511_5 : reports chart511 jobs511_5 := by
  simp only [jobs511_5,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs511_6 : List Ticket := [(11,799,96,0,0,0),(11,895,96,0,0,0),(11,991,96,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j511_6 : reports chart511 jobs511_6 := by
  simp only [jobs511_6,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs511_7 : List Ticket := [(11,1087,96,0,0,0),(11,1183,96,0,0,0),(11,1279,3,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j511_7 : reports chart511 jobs511_7 := by
  simp only [jobs511_7,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs511_8 : List Ticket := [(12,0,43,10,1,1),(12,43,88,11,1,2),(12,131,30,11,1,0),(12,161,65,12,1,2)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j511_8 : reports chart511 jobs511_8 := by
  simp only [jobs511_8,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs511_9 : List Ticket := [(12,226,15,0,0,0),(13,0,7,10,1,0),(13,7,11,11,1,1),(14,0,1,10,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j511_9 : reports chart511 jobs511_9 := by
  simp only [jobs511_9,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
theorem l115 : Lower (aug 115) (graphGoal 115) 5 := by
  apply aug_of (hints:=0x551004101)
  · exact prior_ok 115
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
def w375k8 (i : Nat) : Nat := 0x1ff
def levels375 : Nat → Level
  | 8 => ⟨1,1,0,1,0,0,0,[],0,1,none,w375k8⟩
  | _ => emptyLevel
def leaves375 : Nat → Nat → Nat
  | _ => fun _ => 0
def cycles375 : Nat → Nat → List Nat
  | _ => fun _ => []
def chart375 : Chart := ⟨375,9,7,0,sampleColumns 135 #[(0xfff03f006300843f34b367439f3f3,0x4a28a28a28a00630084131011234009131),(0x4003f000fff02040c18c9fb4c99fd64c9f,0x1145145145102040c18486104081524486),(0x40000000fc0ac7830e0f1cc70e18e78f1c,0x6ebaebaebaeac7830e0b18c70e18a58b18),(0,0),(0x3f000cf803f00fe0f80fe0f80fe0,0x35d75d75d75cf803f00ec0f80dc0f80ec0),(0xfc0fc0000f0003fff000fff000fff000,0x5145145145f0001529000fee000ff6000),(0x3f03f000000ffffc000000ffffff000000,0x6186186186f4a94000000efbf7e000000),(0,0),(0x3ffc0000000fffffffffff000000000000,0x38e38e38e380b56aad6fff000000000000)],colTree 0x18005cc0004 1 0 0,#[[],[16,66,101]],cutoff 9 levels375,leaves375,cycles375⟩
def jobs375_0 : List Ticket := [(8,0,1,8,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j375_0 : reports chart375 jobs375_0 := by
  simp only [jobs375_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def w371k7 (i : Nat) : Nat := 0xff
def levels371 : Nat → Level
  | 7 => ⟨1,1,0,1,0,0,0,[],0,1,none,w371k7⟩
  | _ => emptyLevel
def leaves371 : Nat → Nat → Nat
  | _ => fun _ => 0
def cycles371 : Nat → Nat → List Nat
  | _ => fun _ => []
def chart371 : Chart := ⟨371,8,6,0,sampleColumns 78 #[(0x7fff03009f2673ff,0x14a5294a030085023025),(0xf801f243313d99e93,0x2318c631243312488692),(0,0),(0,0),(0x3e0b83c1ce1e31c,0x2b5ad6b5b83c18e1c318),(0x1f07c00c03fe0fe03e0,0xa5294a5c01520fc03c0),(0x3e0f8000ffc000fffc00,0xc6318c6c94000b77800),(0,0),(0x3ff00000ffffff000000,0x318c631836aadf000000)],colTree 0x170058c0010 1 0 0,#[[],[81,134]],cutoff 8 levels371,leaves371,cycles371⟩
def jobs371_0 : List Ticket := [(7,0,1,7,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j371_0 : reports chart371 jobs371_0 := by
  simp only [jobs371_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def w355k5 (i : Nat) : Nat := 0x17e55beaa5f54af8a5f930
def leaf355k5w (i : Nat) : Nat := 0x2826120882012042a098482228148908c46130004040310a0c0e020220108c6826120882012031
def leaf355k5 (i : Nat) : Nat :=
  let row := packedAt leaf355k5w ((i-0)*62) 62
  (((row) &&& 255)) ||| (((row >>> 8) &&& 134217727) <<< 8) ||| (((row >>> 35) &&& 134217727) <<< 35)
def w355k6 (i : Nat) : Nat := 0x22c90903cd04e011d804f909b022c4447f
def levels355 : Nat → Level
  | 5 => ⟨5,0,0,0,0,0,10,[],0,4,none,w355k5⟩
  | 6 => ⟨1,1,0,1,4,3,0,[],0,3,none,w355k6⟩
  | _ => emptyLevel
def leaves355 : Nat → Nat → Nat
  | 5 => leaf355k5
  | _ => fun _ => 0
def cycles355 : Nat → Nat → List Nat
  | _ => fun _ => []
def chart355 : Chart := ⟨355,7,5,2,sampleColumns 50 #[(0x7fe61339f,0x14a5294611185),(0xf83e863cf3,0x2318c62862432),(0,0),(0,0),(0,0),(0x1f07c107cf1c,0xa5294b024e18),(0x3e0f801f80fe0,0xc6318d280bc0),(0,0),(0x3ff0001fff000,0x318c630d5b000)],colTree 0x10016100008800b10000340018c0100 3 0 0,#[[],[81,134],[16,101],[16,96,80,133],[80,16,129,97],[80,129],[96,133],[96,129,81,80],[128,81,97,16],[128,97]],cutoff 7 levels355,leaves355,cycles355⟩
def jobs355_0 : List Ticket := [(5,0,5,0,0,0),(6,0,1,6,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j355_0 : reports chart355 jobs355_0 := by
  simp only [jobs355_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
theorem l99 : Lower (aug 99) (graphGoal 99) 4 := by
  apply aug_of (hints:=0x551000101)
  · exact prior_ok 99
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l355 : Lower (aug 355) (graphGoal 355) 7 := by
  apply chartRoot (g:=chart355) (ob:=[(99,4)]) (hints:=0x551008101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    subst a
    exact l99
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=jobs355_0) j355_0 (by decide +kernel)
    intro k hk
    change 7 ≤ k at hk
    change (cutoff 7 levels355 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem l371 : Lower (aug 371) (graphGoal 371) 8 := by
  apply chartRoot (g:=chart371) (ob:=[(355,7)]) (hints:=0x551004101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    subst a
    exact l355
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=jobs371_0) j371_0 (by decide +kernel)
    intro k hk
    change 8 ≤ k at hk
    change (cutoff 8 levels371 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem l375 : Lower (aug 375) (graphGoal 375) 9 := by
  apply chartRoot (g:=chart375) (ob:=[(371,8)]) (hints:=0x521002101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    subst a
    exact l371
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=jobs375_0) j375_0 (by decide +kernel)
    intro k hk
    change 9 ≤ k at hk
    change (cutoff 9 levels375 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem l127 : Lower (aug 127) (graphGoal 127) 9 :=
  augRelabel (ps:=[115,84,131,98]) (by decide +kernel) l375
theorem l167 : Lower (aug 167) (graphGoal 167) 7 :=
  augRelabel (ps:=[135,67,50,98]) (by decide +kernel) l355
def w175k7 (i : Nat) : Nat := 0xff
def levels175 : Nat → Level
  | 7 => ⟨1,1,0,1,0,0,0,[],0,1,none,w175k7⟩
  | _ => emptyLevel
def leaves175 : Nat → Nat → Nat
  | _ => fun _ => 0
def cycles175 : Nat → Nat → List Nat
  | _ => fun _ => []
def chart175 : Chart := ⟨175,8,6,0,sampleColumns 78 #[(0xf801f208b6639f673,0x1294a529208962089631),(0x3ffc3138726487f,0x294a5294c31285224846),(0x1f07fe0041cf9c78f9c,0x6318c63040028458298),(0x7c00f81f01f80fe0,0x39ce739cf81f01b80d60),(0,0),(0x3e0f8000ffe001fff000,0xc6318c64d2001f76000),(0,0),(0x3ff00000fffffe000000,0x318c6318b2dfd6000000),(0,0)],colTree 0x170029c0008 1 0 0,#[[],[80,113]],cutoff 8 levels175,leaves175,cycles175⟩
def jobs175_0 : List Ticket := [(7,0,1,7,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j175_0 : reports chart175 jobs175_0 := by
  simp only [jobs175_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
theorem l175 : Lower (aug 175) (graphGoal 175) 8 := by
  apply chartRoot (g:=chart175) (ob:=[(167,7)]) (hints:=0x321002101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    subst a
    exact l167
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=jobs175_0) j175_0 (by decide +kernel)
    intro k hk
    change 8 ≤ k at hk
    change (cutoff 8 levels175 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem l179 : Lower (aug 179) (graphGoal 179) 5 := by
  apply aug_of (hints:=0x551004101)
  · exact prior_ok 179
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l207 : Lower (aug 207) (graphGoal 207) 6 := by
  apply aug_of (hints:=0x321002101)
  · exact prior_ok 207
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l227 : Lower (aug 227) (graphGoal 227) 5 := by
  apply aug_of (hints:=0x551000101)
  · exact prior_ok 227
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l231 : Lower (aug 231) (graphGoal 231) 8 :=
  augRelabel (ps:=[135,100,67,50,82,16]) (by decide +kernel) l371
def w503k11 (i : Nat) : Nat := 0x3ff
def levels503 : Nat → Level
  | 11 => ⟨1,1,0,1,0,0,0,[],0,1,none,w503k11⟩
  | _ => emptyLevel
def leaves503 : Nat → Nat → Nat
  | _ => fun _ => 0
def cycles503 : Nat → Nat → List Nat
  | _ => fun _ => []
def chart503 : Chart := ⟨503,12,8,0,sampleColumns 244 #[(0x3ffff007fc3043b3006300843f3081e40083b34b367439f3f3,0xaa954aa552a954aa552a83040b100630084131080e40080b1011234009131),(0x8000000007fc0000ffffe42924302040c18c9f00607631243b4c99fd64c9f,0x406030180c06030180c0642924202040c1848600201631242104081524486),(0x8000000ff8000000ff800001c7cac7830e0f1c91878841c7cc70e18e78f1c,0x998cc6633198cc6633198000414ac7830e0b1890828840414c70e18a58b18),(0,0),(0x1ff00003831f80cf803f00fe0e1f80f81f80f80fe0f80fe0,0x556ab55aad56ab55aad57831f00cf803f00ec0e1f00f81f00f80dc0f80ec0),(0x3ffff00003fe000000003e000f0003fff000fe000ffe000fff000fff000,0x140a05028140a0502814000000f0001529000b2000ad2000fee000ff6000),(0x7fc0000007fc000000003fc0000ffffc000000fffff000000ffffff000000,0x783c1e0f0783c1e0f078940000f4a94000000ffdfe000000efbf7e000000),(0x1ffff800000000003ffffff00000000000fffffffffff000000000000,0x6633198cc6633198cc663fffbeb000000000004d7d752dbeb000000000000),(0x7fffe0000000000000003fffffffffffffffff00000000000000000000000,0x783c1e0f0783c1e0f07836bffff0b56aad6fff00000000000000000000000)],colTree 0x1b0079c0010 1 0 0,#[[],[98,135],[81,114,134],[81,130,118]],cutoff 12 levels503,leaves503,cycles503⟩
def jobs503_0 : List Ticket := [(11,0,1,9,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j503_0 : reports chart503 jobs503_0 := by
  simp only [jobs503_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def w487k6 (i : Nat) : Nat := 0x1c0380680c840b7129d424c931d785d99220131d785d59220131de46513220131ef0261324c520f7025d324c520f705d9324c52063f0a961131483a7c29d844c520
def leaf487k6w (i : Nat) : Nat := 0x874120c1049244362b0982020281d518ac2608080a0754a2c9a0a022090d9241448210404424062f05830211489498bc160c08452252
def leaf487k6 (i : Nat) : Nat :=
  let row := packedAt leaf487k6w ((i-2)*62) 62
  (((row) &&& 255)) ||| (((row >>> 8) &&& 134217727) <<< 8) ||| (((row >>> 35) &&& 134217727) <<< 35)
def w487k7 (i : Nat) : Nat := 0x5230b010c000c802c0010101a06150aee03778390406004c0001003926073c09f60482039e96cd088011ee5198ff38ce7b94663fcc711fea3acfaa1547f8b872fbd239f8c368ff31bc7f98d73f18695ec4a4af62425fc840f3ef0675f6a33cfa171e7d1acf3e8587dd4273eeab39df5a1cff8a4e7fc4e73ef8a09dfc904ffa1427bd5a62fe25317f4214abf58059f9c02ef4b396fc198bbe08c5df1662fe88317f8918bfc14c5de9642ff04214faeb033d6d81aeb4c0cf4b606dacb033d2981bab0c0de576067a03037c31e195f4483bdf8e317df8904da3f09a5dfc0a62
def leaf487k7w (i : Nat) : Nat := 0x804009ee802010010080499045608216121080880080400402012441040080925482486012441139318321c424c821ae730f52107b10825a620b4530c9b1851540396c420b5109318864dcc3d46222330143a107b1083d4841ea420f6210045883d4621ea310739887a8c50c4c106250a31285189428c4a146250a31281189428c4a0c6265
def leaf487k7 (i : Nat) : Nat :=
  let row := packedAt leaf487k7w ((i-5)*21) 21
  (((row) &&& 255)) ||| (((0x41049248108a44c04130980607020980c2408150a601118888c062106034120808844080500490492090442610201400540a140a020301100840110084020281c0404030040403 >>> (27*((row >>> 8) &&& 31))) &&& 134217727) <<< 8) ||| (((0x38383c0e164905c1f07034532916830380c9a8b05911884507a2c160d448231782c162b0d82c262b054426112150681428940a8342a04cf4522988c264138844426510884c251201d0a05 >>> (27*((row >>> 13) &&& 31))) &&& 134217727) <<< 35) ||| (((0x1108440210281c0407008840000 >>> (18*((row >>> 18) &&& 7))) &&& 262143) <<< 62)
def leaf487xk7w (i : Nat) : Nat := 0xc52211410894435a0984822482491494483410144825201289848020080c060d448230104c213
def leaf487xk7 (i : Nat) : Nat :=
  let row := packedAt leaf487xk7w ((i-0)*62) 62
  (((row) &&& 255)) ||| (((row >>> 8) &&& 134217727) <<< 8) ||| (((row >>> 35) &&& 134217727) <<< 35)
def cycle487k7w (i : Nat) : Nat := 0x28
def cycle487k7 (i : Nat) : List Nat :=
  if i < 56 then [] else
    let t := i-56
    let a := packedAt cycle487k7w (3*t) 3
    let z := packedAt cycle487k7w (3*(t+1)) 3
    (List.range (z-a)).map (fun u => leaf487xk7 (a+u))
def w487k8 (i : Nat) : Nat := 0x49d27090236c3842db01824804df080e0223e00fcc38ff48d2741c2d9646d181c2206d221bb986059b0f9464aaf06a664aa03439874bb0cdab1d2f459740c6d03233798a5ba43039914b10bf782c9321c800f085d24027e8d65815fd90f20b7e73129261566c06358539a0a9085086129b0aa84127d84e38326c0caf15ebaa107e5c268b152609c7118da3e4d847fa007f8a69a0e21049be101c044480ec38424c0df36c5ea107e641eb417c901d000092042fe1745a6af144d07270dc0016b8cda98272645cd726a981a179b810c005cd414df49f2b06390013e00d99b3e832560c7f62a7e801800ba6823b259c013cd057f400d8058d4143e00d50124d04542fb7021f607d082b6b80cba05dd81b9a02d2815b4072c8124803b201996042a3c239a38635e3362da15e1220fa0d20aa06e01deb9e55dd1d39ca1b79b51ab99ed84979d705419274f90d28cd8a709488347546403c42e40027fa5f3fd2e9fe164ff0a27f84f3fc25dfd7b7fc4db7f0edbf956dfc9b5ff4c37fa21bfb30dfe986ff0437f7a1bfbb0dfc385ff0b77fa29bfb14bfe97eff43f7f61fbfd2fdfdc7dfef8b7f6057fbc2dfd717fc48b7f3c5bf942dfc915ff4af7fa17bfc2bbfe15dff02f7f657bfb2edfd776feb3b7f91dbfa6ebfe966ff432ff859bfaccbfe946ff422ff851bfac8dfc045ff49f7fa0f7fc27dfc43dff01f7f64f7fbc7dfd73ff691ffb2cfbfb12dfd695ff4ab7fa157fc0adfd956febabdf3d5bfacadfc055ff49b7fa0dbf886bfdf36fec1b7f58dbfaa6fdc837fb11bfd34dff026ff6937fb41bfd10dfebe6ff5837fa71bfd70dfeaa6ff4837fad1aff7c3bfb01bfde0dff0137f6497fbc4dfd725fee937f589fd964ff4725ff4a77fa13bfb29dfd74fbe727df353fe8e9dfe82efea96ff6cbfb8e5bfe01efec8eff787bfae3bfdd1efeb0ffb207fe8e3ff901ffc48ffe187ff323ff971ffd20ffe587ff183ff911ffc50ffe1c7bf356d7e8af3f3d73f9e1bbd14ddc4a7af35377629fa854ddd616bf30b7ba27ddcf3ded99fd72cff3927bdad3dec09e7f3bb6f95dbbc8edf6897bb34b7d625fac92bf5d96fab4b7d025fcc72df5597f8d4b7700d7ed26df6837bb31bf590dfa806fe6337ea3877ea23ef4d1df988fed2477e5a3bf011fea38efcac7fc8a37f051ff078dfa126fd08b7e843bfa91efd40fbe9c7f74a3fda41ff910ffc0877f043dfa807bd3037e601fb480df8007f5182fe701fe440057fd2d05bfd0d03efa8b05efa8a05fea8613fea4653fe966077fc0905ff263053fbf6053fbb6073fb96093fb563f3fd300b3fc2d173f88d193f894197e854393fbe2053fb82193f88b273f88c573f8881b3f887197f3529bbe88657beb06a3fa90685fe026093f88585fa8e539bf323377f3c329bf00337fd10387fe0e329fd0a3a37d380
def leaf487k8w (i : Nat) : Nat := 0x4d2904d2604d2904d2904d2904d6904d6904d6904d6904d6904d6904d6904d6904d6904d2904d6904d2904d2904d690180001800071af04d6904d29060e604d2603c8204d2903c8205a9005a900180004d6906d8a03f8204d69030000180001800018000398a0398a04d69018000398a0398a04d69018000698a0666f0666f04d69060e6065af05ad004ee902800066690666904d690502305daf05daf06e0a05e2f052a305714050230776604d2904d2904d290722f04d6904d2904d6902fb504d2605a8a04d2604d2604d2604d2605a8a04d6605a8a05a8a04d6605a8a04d2605daf04d6904d290398a0398a0398a052a303a0a050230398705a8a05daf05daf03f82060e605a8b071aa05a8a04d2903c8204d2904d270398a0398a0398a060e604d69061e60666905a8a039870398705a8a039870398705a8a03a0705707039870398705a8a4cd263cd2e3cd2e54d6914d271180014d3314d671cd247c4003bc8229f3029f3029f3029f2f29f2f298002bc8d5180031800118000cd260cd320cd660cd240cd260980c0b50d09f340980c0cd23840c20cd2664d263cd3284d2484a4829f3484a4824d2624d3224d6624d242086c23c8021f342086c0cd2324d2624d23410a0414a072441239876b987539873398510f540b984721cd5a441490a0590a0590a0110a0590a0290b15844140151
def leaf487k8 (i : Nat) : Nat :=
  let row := packedAt leaf487k8w ((i-38)*20) 20
  (((0x75737271706463626160545352514241323130212010 >>> (8*((row) &&& 31))) &&& 255)) ||| (((0x208249240a09064130184801028100044218180e022301884180d0482603090201401241248240101845029108904a211180c4220088441009008100a002a050a05010180880420100406011008402120180405030080806010040601110840220108040403 >>> (27*((row >>> 5) &&& 31))) &&& 134217727) <<< 8) ||| (((0x38383c0f05c2c1c2c960b84924128a6522d060701a09848322310898a6522a8906825109844a043209408341219408242a0d028512815068540998ca6432d148a6230980c24220908c241132884426128904c2311098422212a140a25130904a07028844c22 >>> (27*((row >>> 10) &&& 31))) &&& 134217727) <<< 35) ||| (((0x104a040a808242120844806110844120100840a060221004420101804030088c02210080c0000 >>> (18*((row >>> 15) &&& 31))) &&& 262143) <<< 62)
def leaf487xk8w (i : Nat) : Nat := 0xb92b55380600405309182568a70cc0080a212304ad14e198010144246095a29c33002028848c12b5538060040510917256aa700c0080a612
def leaf487xk8 (i : Nat) : Nat :=
  let row := packedAt leaf487xk8w ((i-0)*15) 15
  (((row) &&& 255)) ||| (((0x2040a854001108241109844825108100a0028904a04010180401018044021 >>> (27*((row >>> 8) &&& 15))) &&& 134217727) <<< 8) ||| (((0x2890682428940a8342a044ca2110944c24 >>> (27*((row >>> 12) &&& 7))) &&& 134217727) <<< 35)
def cycle487k8w (i : Nat) : Nat := 0x7b347a8a0
def cycle487k8 (i : Nat) : List Nat :=
  if i < 238 then [] else
    let t := i-238
    let a := packedAt cycle487k8w (5*t) 5
    let z := packedAt cycle487k8w (5*(t+1)) 5
    (List.range (z-a)).map (fun u => leaf487xk8 (a+u))
def w487k9 (i : Nat) : Nat := (if i<1 then 0x4fcd60e6301015a00e84010420f3d2300f2500e06f2564ff141dd9c103a82e75246f6e6e70e0fc4806e240ff3050917e983e4703c1b83a6e03d8d03af583bb5839db03e9083ca081b3003b2d83d0df24189a80ccd804934092c80d446234282d22e069e8238221d6f62bed419f9a176940bf341d27a1d4d405ae814e98388fa30f00268b615f9c103f21814e377e80389235f180aac80d2481bf3a0373c087700325e39ee210f7a03420c8839d1ef20857c0c908091fc0d0ca2bd000c0fe2b00c2cf824b4a8058c80d2d4266ec0a92a0d749e4d86df606b78c2486c14d78392cc379a4388b4106f438ef872dd0395c818fd42cbe805ce002ec819c645748c38414bbd647c440060e05f36c63c200ac482906c61878418449507a80cdb4263cc0a57c0c9f0080e40c6fa2c9000631c0cbc82b65a0ad0c0c5660b7fc2ad0a2c7a6055205262b40b18e0787135ac23efd815ac728bf43d9d808b3a0f3441ef2a2aaa705af71789a18b6c0da761d9d10a3a91c2da378180efb80aa2b27f560be043aa4a0d9a61aae9050052efc125a1207f372d9fb03f8c38bce278fe0c240250d82be91062a4cc0580cc0125c565d044998166d83456434a180a5a034e70411dc2a64c44c542f5080213c12ea013da804e00182a48dee80fb1004a618c1e26a045e405e4b05c6605965157ec05da705a3a0284a05f501325c04e6e03db305b9506bc0b18a0afc82f50e31aa61e57c1458e30a30101e236bf01e126358301dfac09adc18e501e3d0078f218c5a0ac22168f1d081d8d829f30293b026130aa14818468a76b026d4027ae027538a6970a9f48284602ac909836828bb02a4974987b4255a8116e85d8f042eb0269b0482681267460a80409b025ab002bb89f86407f1c654f465b1066780669fc2508827210123f411ab401e1842a2465f8c032f80e4e002d3c6624420b040800c11e6c084ac275801d9ac26f9012b140250c523002651800aa8516642600c25e41152742076f20845a083f0080fe0757c072702853e27bd00797407cdc07b7227880283f607f3c0874984cc013c80bb681b2e4018ac0bc441ac5c0d308015101bae81c5fc007981b5041cb4400ff01bca40c0180d7041c330076000c51800b000cc9c0c93478c104b1ac4a1b8002180a4e80a0304ada80b6e4401f0099500b16c49c200af4c0a85809d21b362be8aaca9c7a25a7e299d65cb92f635f86761077f59d97747dc486c3592360a553150791d541f0d7a2ee0aa5247c7b210f430204880001d7ff3b969ff5d4e6ffaca53ffe33397feb9909ff1cd15ffaa6417fd7231bfeb120dff50956ffa64337fe11397fea8b6fff4c454ff86251ffd2139ffea82edff4c0c2ffa41245fe7734fbf2ab8b7f5d505fbc672b5fd7355afe399a7fb88926bfae48aff611ad7fa989e7fe80174ff240717f810 else 0x1221ce2e01a441383a1db483cebe1b8101d820808fd21c3ad0d7890e8ac1ca330e6ee0db910e797172820e0c00998d0cd150836c024720ae3802268122470ccfa017ab01e9b0211b0164e12365025820e056023d82be4098b20ecc37b6005740053041c1b831c0c11cfc71c9037ca85c100941809b88f17706dbf84a250e6fe037d48646106ee60dd3d0e4008edaf86e5005d328b79d030c68668a9320eb435ff035bf4118e4354903506c760e8187c83618113d04342147183032f1ca2da833dc047508339306e1e4a00fc2951c3325804414bbe6426130212343355808e8622c6d812cce193dc19552190a42e30017f401756018637c90622605a470d5db062db03ee08101404814078eb8085a05c58061ff0611c4c5907b80f60a11c3203f8400a343142a17bf01e0ac17d08367f2181301830017ec2115661664a01e1816cd125641f684aa605a560057583bf405ab785b9515568801e685de98b71f85cc38460c0779083cce05e43050cf8075005d5a05c598598605b145422c7f2365681622e01bea164f804d0c1402081447f10c83d84f97041b90571c0112a8583b854bb0567e856dc0552d8579f852b08b68c0558a8408d74626bc2a240279ec27c441ada467ef828a3c68a1c230586934428ccc111d029de85ad3c12e18284fc296283ba182821c1f980685cc694481fef429870632a8224482924418a930f18492f8c9b2048998223a049b1427828474b0468e847ec045bf800c08b643846140483084555044846f9c2732e0837928091082ab01ea2038b4088c217d8c085130864c084ce27871087771758ac41a107c2502ba4f2ee700bc2f3384e7dc)
def w487k10 (i : Nat) : Nat := 0x5e02b4c722a0f450bc38247c3a1414e406a680f1c56881eca00970987432ee052e082481e002bfa064d16a4097c0619e2a8a040e8009c25fe372d06180bccc421c13ff0c6886a041d58165a1ae80e3f066ae3e07088906cfc096a1f1705eb871440408284bbff
def levels487 : Nat → Level
  | 6 => ⟨9,2,6,2,0,0,40,[],0,11,none,w487k6⟩
  | 7 => ⟨57,5,8,2,2,4,14,[(4,0),(5,11),(5,29)],0x299a227799a55912336599565193649916418561183609765d56250d42501324c49825c871ce889de11615846097558954509324c53048487204801ce335d56558953509324c5201cc10,10,none,w487k7⟩
  | 8 => ⟨244,38,12,3,4,6,11,[(5,0),(6,23)],0x2889de66956448ce2284587619856118360981601765d5745cd7259563589615815454d5150d42505404c9314c12121c83204801ce779563388a11801755cd725956254d51541424c9314c121480730c410,5,(some 0x824090a8441a08401f0e870361a0c8602e160a850200e0683016090401c0a04018080200),w487k8⟩
  | 9 => ⟨32,32,14,4,6,8,10,[],0,5,(some 0x8584821f1b1a1716100e0d0c0b0a09060504030200),w487k9⟩
  | 10 => ⟨1,1,0,2,6,5,0,[],0,7,none,w487k10⟩
  | _ => emptyLevel
def leaves487 : Nat → Nat → Nat
  | 6 => leaf487k6
  | 7 => leaf487k7
  | 8 => leaf487k8
  | _ => fun _ => 0
def cycles487 : Nat → Nat → List Nat
  | 7 => cycle487k7
  | 8 => cycle487k8
  | _ => fun _ => []
def chart487 : Chart := ⟨487,11,7,6,sampleColumns 159 #[(0x19a0800000000fe03fb1333190934c82336743f3,0x7095ba74e9d3a74e9d31313190914c8231234131),(0x67b380000007f01fffc24302031f00ec4399fc9f,0x7004183060c183060c242020306002c42081486),(0x664d000003f8001fc0007cbc1c1c8f107ce18f1c,0x6841962c58b162c58b0014bc1c18851014e18b18),(0,0),(0,0),(0x380000fffc000fe0000380c01fe0f01f80fe0fe0,0x802050a142850a1428000c00520901480dc0ec0),(0x127f000007f000007c00ffe000ffe000fff000,0x1a0e1c3870e1c3871400d4a000ffc000f7e000),(0x5c0001fff80000007fff000000ffffff000000,0x139c68d1a3468d1a347feb0000006aeb6b000000),(0x40007ffe00000000007fffffffff000000000000,0x444070e1c3870e1c386bff2b5adf000000000000)],colTree 0x400294810220028c005090016100218800b10010a400584088220010f00301001e00001e800138038140018c0184a0010e00b05000a300510a0073002025005980081280ac204401401a600104a00e30004252021e00202803c400029401e40000cb0052900045405840802a800ce00c05400e300412a00a38014063021e000034094a400019056102002e00538028170058c0084b8038e00102001e600007000738020180059c0080 33 0 4,#[[],[98,135],[81,114,134],[81,130,118]],cutoff 11 levels487,leaves487,cycles487⟩
def jobs487_0 : List Ticket := [(6,0,2,7,0,0),(6,2,7,0,0,0),(7,0,3,7,0,0),(7,3,2,8,0,0),(7,5,52,0,0,0),(8,0,1,7,1,0),(8,1,28,8,1,0),(8,29,9,9,1,0),(8,38,96,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j487_0 : reports chart487 jobs487_0 := by
  simp only [jobs487_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs487_1 : List Ticket := [(8,134,96,0,0,0),(8,230,14,0,0,0),(9,0,13,8,1,1),(9,13,19,9,1,1),(10,0,1,8,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j487_1 : reports chart487 jobs487_1 := by
  simp only [jobs487_1,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
theorem l39 : Lower (aug 39) (graphGoal 39) 4 := by
  apply aug_of (hints:=0x521002101)
  · exact prior_ok 39
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l103 : Lower (aug 103) (graphGoal 103) 5 := by
  apply aug_of (hints:=0x521002101)
  · exact prior_ok 103
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l135 : Lower (aug 135) (graphGoal 135) 4 := by
  apply aug_of (hints:=0x21002101)
  · exact prior_ok 135
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l163 : Lower (aug 163) (graphGoal 163) 4 := by
  apply aug_of (hints:=0x551000101)
  · exact prior_ok 163
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l327 : Lower (aug 327) (graphGoal 327) 5 := by
  apply aug_of (hints:=0x621002101)
  · exact prior_ok 327
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l359 : Lower (aug 359) (graphGoal 359) 8 :=
  augRelabel (ps:=[101,50,66,16]) (by decide +kernel) l371
def w455k6 (i : Nat) : Nat := 0x7f
def levels455 : Nat → Level
  | 6 => ⟨1,1,0,0,0,0,0,[],0,1,none,w455k6⟩
  | _ => emptyLevel
def leaves455 : Nat → Nat → Nat
  | _ => fun _ => 0
def cycles455 : Nat → Nat → List Nat
  | _ => fun _ => []
def chart455 : Chart := ⟨455,7,6,0,sampleColumns 75 #[(0x7d8cf193c8ce93,0x3def7bd8c7191c8c691),(0x1fffe10c21f0f0fff,0x4210842108206030826),(0x3e0f801f3c1cf1f31c,0x14a5294053c18505318),(0,0),(0,0),(0,0),(0x7c1f003e03fe0fe03e0,0xc6318ca014a0fc03c0),(0x3e0003ffc000fffc00,0x6b5ad6bfac000afac00),(0x7c00003ffffff000000,0x739ce735feb5f000000)],colTree 0 0 0 0,#[[],[98,135]],cutoff 7 levels455,leaves455,cycles455⟩
def jobs455_0 : List Ticket := [(6,0,1,7,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j455_0 : reports chart455 jobs455_0 := by
  simp only [jobs455_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
theorem l455 : Lower (aug 455) (graphGoal 455) 7 := by
  apply chartRoot (g:=chart455) (ob:=[]) (hints:=0x621002101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp at ha
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=jobs455_0) j455_0 (by decide +kernel)
    intro k hk
    change 7 ≤ k at hk
    change (cutoff 7 levels455 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem l487 : Lower (aug 487) (graphGoal 487) 11 := by
  apply chartRoot (g:=chart487) (ob:=[(39,4),(99,4),(103,5),(135,4),(163,4),(167,7),(227,5),(231,8),(327,5),(355,7),(359,8),(455,7)]) (hints:=0x521002101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact l39
    · exact l99
    · exact l103
    · exact l135
    · exact l163
    · exact l167
    · exact l227
    · exact l231
    · exact l327
    · exact l355
    · exact l359
    · exact l455
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=(jobs487_0++jobs487_1)) (reports_join j487_0 j487_1) (by decide +kernel)
    intro k hk
    change 11 ≤ k at hk
    change (cutoff 11 levels487 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem l503 : Lower (aug 503) (graphGoal 503) 12 := by
  apply chartRoot (g:=chart503) (ob:=[(487,11)]) (hints:=0x521002101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    subst a
    exact l487
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=jobs503_0) j503_0 (by decide +kernel)
    intro k hk
    change 12 ≤ k at hk
    change (cutoff 12 levels503 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem l255 : Lower (aug 255) (graphGoal 255) 12 :=
  augRelabel (ps:=[131,100,66,115,82,16]) (by decide +kernel) l503
def w379k6 (i : Nat) : Nat := 0x280f05e809ec68096509416735a5259425069ad2999550941
def leaf379k6w (i : Nat) : Nat := 0x0
def leaf379k6 (i : Nat) : Nat :=
  let row := packedAt leaf379k6w ((i-2)*0) 0
  (16) ||| (0x202018 <<< 8) ||| (0x4461301 <<< 35)
def w379k7 (i : Nat) : Nat := 0x782fb2082aec00785f641f8081401bb02028507c0403034280e0443098143c1bf1daba8c635136241b008bf3ae46f9573ea206f1fe55c8ff4adc7f956e3fd0539dc2998ff4136770a5a3fd0513de2189fd00c56f95163fd04b3de2159fd00ad6f1a96f688e9f35874edad2a57d1ccabe8d655f46728fe46d47f232be724cff71047fb8723fec311fee246ffb0a83ddaf20fe9310676e1e19b6ef0d5b67866d6bc372be413d70e0ceb7706b5b3833ab5c1b96ae0dd2f886f17440a77c830b37e615697e282d5ed1151ef6cca85fa54543eead4917f458dc72780187f31247
def leaf379k7w (i : Nat) : Nat := 0x40100301003010086320a330086320f5410013009c540862107010030100e9530862103010086210862102d200c7510a3300d75108632086321073106b4106b4106b411073008610088210ba3285460c5450e5450e54502546041260c1250e1250e125061250a5460a1260
def leaf379k7 (i : Nat) : Nat :=
  let row := packedAt leaf379k7w ((i-10)*20) 20
  (((row) &&& 255)) ||| (((0x2031088942215028104a240805006110980a8643a0440210080806004402100444230088042010904c0210088040403 >>> (27*((row >>> 8) &&& 15))) &&& 134217727) <<< 8) ||| (((0x5c0f070a0c0e034130906643a194c87030951a8552281c0a4462114461301391c4e06b3c1a0c64220988c26029144a03a158a8742915068160a >>> (27*((row >>> 12) &&& 31))) &&& 134217727) <<< 35) ||| (((0x209088042080600223008840213008440000 >>> (18*((row >>> 17) &&& 7))) &&& 262143) <<< 62)
def leaf379xk7w (i : Nat) : Nat := 0x950a05400814065848a412228148952450381104c0614028948a0020080c0607418090004421625428150120d05161229048820120569140e04011008580c2623000802030181d0602601118852141a05106034126a0c26020a0906980713018400110802
def leaf379xk7 (i : Nat) : Nat :=
  let row := packedAt leaf379xk7w ((i-0)*62) 62
  (((row) &&& 255)) ||| (((row >>> 8) &&& 134217727) <<< 8) ||| (((row >>> 35) &&& 134217727) <<< 35)
def cycle379k7w (i : Nat) : Nat := 0xd830
def cycle379k7 (i : Nat) : List Nat :=
  if i < 53 then [] else
    let t := i-53
    let a := packedAt cycle379k7w (4*t) 4
    let z := packedAt cycle379k7w (4*(t+1)) 4
    (List.range (z-a)).map (fun u => leaf379xk7 (a+u))
def w379k8 (i : Nat) : Nat := (if i<1 then 0x38d05424115802cf0134404a8814144dd02a040cc103b240da60409c0f1449c699c9909429308d089487c85e82880a7ec7e67ce7a479278075c74a71a6cc6a868a6786606546426306065dc5ac58857055e5284ec4c849e48646245642c3cc33c3122fa2c42a628e27c2342041da1801381020f00780009fc4867f7619fda867f7e09fdd0a7f6829fe7627f7d49fc5527f9d79fdf4e7f7ce9fdf367f7ca9fe7567f7d19fc5467f7cc9fdf277f9a0dfc582ff760bfdc82ff6e0bfd883bf9e0dfe5677f5c2bfdb0aff682dfe6537f957bfe74f7f993dfdf4f7f5d3dfd64eff9cedfe63aff78ebfc43b7f5cefbd13aff116dfc05b7f956dfc45b7f456dfcd5aff9d2dfe64b7f592dfd54aff9cddfe6377f14dbfc4377f5cddfd537f740dbfe72b7f98abfde2aff10adfd72b7f00abfdd2b7f58afbcd2bf740abfc4577f495dfd1577f355dfd646ff9ccdfe632ff78cdfd7337f54cbfe7277f989bfde277f5c9dfd627ef208ff6523fd488ff5023fd308bfc41b7f006fdd01bfd106ff401bfd346bfc412ff11abfe73f7f98fdfc53f7f5cfdfc03f7f58ffbc23f7f54fefd13f7f50fefd03f7f4cfff473eff6c1bfda06ff78bf7cd2fdf30bf7cb2ffe38bff912ffe24bff8f2ffe20bbfde1f7f5c7bfdd1f7f587dfd41fef247dfd31ffd187ff8e1ffe287dfe6177f5c5dfc016ff745dfd6177f545ff4717fe285bfe70f7f983bfde0eff103dfd70eff743dfd60eff703dfd50ffb2c3fec80ffd1c3ff8a0f7d661cfe6833f7e0cfc5833f959cfd70b3f942d7e67f9f95fd7d77f5f01fcfe5636f99eebe57b6f5dedbc07bcf91edbd67b3f957d7e45f7799dede577775ddddc077d791dddd677e78ddddd5773f956d7e45b6f8d6dee673bb95cded7737b01cf6e4737b59cfae3737b55ccfe5575f915dbe3577d99bef656f7d5dbdf406fed8dbdf556ff589bdf546ff985bdf536f3f010bf8142fe048bf67237d988ef6523dd908fd6223f9848ff0122fe046bf671b7d986ef651bdd906fb631bfc046bf81137e99aefa56b7e5dadf806bde91abf9d6b7e59afba36b7e55afda26b7e51afea16b7e4daff206bfc1daff066b3f00fbfa72f7e98befa52fee8cbfda22ffa84bdf6603bd940df5703ed8c0bf5c03f5880bf5b03f98400aff6a0337f5d20b7f99172ff10c0ffb3cc92ff10952ff74927ef4492bfd3c84ffd2c82bfd9462bfd48607fd44613fd18f33fe40b0ffe3830e7f7a12e7f7210e7f6e1367f160727f9d92f5f0d92b6f0990e7f9c2127f7020a7f6c20e7f1180e7f117327f153327f14e4a7f9d62e7f116127f7d20e7f1524e7f14d527f14a2e7f115327f14c137b4cc2e7f1490a7f150337d5c893ed348efed208337d5c612fd7064ff54062bf5306127f7cf0f7e5cb6fde34b4bde30b33de2cb8ffc1cb6ffc18b4fed1c70ff5185caed700caf56c0 else 0xd1bdc0375b8431c6c6027502b7b0b180123e260fbd09eb4087501ac4280402868001e2c057dd34cd7098012011f05901b8b015f5053508910d882184b85f1842d6c0281a6057900050d4be0a944570924cd422207197500837a30d188363481d6f600528cff600633c55112144124534915c9454d709881cd489c20207352260cf4c323d33807c649100504e254455c31000c03854c80bce42e1215d5730786491fb0b450215050d664602926150d5974237c5056ce00148248b017ec25485056e10597423c1069c417120122c057501a2701f700e114359b1135bdc035b00a20d38d0d4f4c50c13c5616ce002501d91065b158e007234352d86406cf70563801cc106b38006406c26d6910656c028d0d427167105de81850458459)
def leaf379k8w (i : Nat) : Nat := 0x51040510405104051040672f051040510405104051040612d0460e051040300005104051040300005104024000510405104051040510405104051040510402400024000240002400024000672f0672f02400030000612d0612d054650460e0616d030000672a0612d0612d0528404eaf0616d024000612d02400061280672a0510403c0003c0003c00024000460e0460e052e400b430300004eaf04eaf0528400b430240005aaa05102051020672a061270460e054650672a0460905d270612706a0e05104051040510405104051040510405104052840510405104051a406732051a4051020612d0460e051040510405d280720a05102051020612703b0d03b0d05104051040510405104051a406128051a40612705102051020612d0616d06ce7052e406ce706e4706127061270460e0460e04ecf051040466e052e403d400528403d400460904eaa04eaa04609651023510432400351043d1043c000324002d1042d1042d1042a400324001d1041d1041d1041a4001d1041a400330002b0001510d1510d1510d124001510d124001510d13000324002a4001a4004c9cd4c9cd4c9cd4a4004c9cd4a4004c9cd4b00033c002bc001bc000d1020d1020d1020a40b0d1020b00b0d1110a40b0c9d10bc0b4082350c4151c410d10285102351022d102151114c9d1515ec5a8830e1277e127361312e1261e12659a2d50190251022510225102220cb2510225102220cb2510222ccb25111220cb249d1234cb0d1002510026125384a32510275102351021d102151114c9d160c4168c4168c4118c416904110c506a88348c40
def leaf379k8 (i : Nat) : Nat :=
  let row := packedAt leaf379k8w ((i-59)*20) 20
  (((0x75717065646261605453525141403230212010 >>> (8*((row) &&& 31))) &&& 255)) ||| (((0x10188444a110a8140825124140b04180d048100a00a060381140a44223018844011088201200900422100406014120d028120b04c0612090502c11008402020180110084020080c0310088044421008804201090440210088040403 >>> (27*((row >>> 5) &&& 31))) &&& 134217727) <<< 8) ||| (((0x524d249a0c0e0341309066472194c87432980e0612a350aa450381446130185128150988c06122904c20160a351a4d0693c1a0d26a34188c26030988c06121104a45128144a450289088242309048451208e8562a1d0a4541a0582833080484c2212 >>> (27*((row >>> 10) &&& 31))) &&& 134217727) <<< 35) ||| (((0xc04228108a01120908804211084241108060150804c2011080110804030088402110080c0000 >>> (18*((row >>> 15) &&& 31))) &&& 262143) <<< 62)
def leaf379xk8w (i : Nat) : Nat := 0x5f9dbc85310ce875baf98a1660a17675f2754434a2fcede429886743ae97c85043050bb3af90a6219d17e75f314c433a2ecede629886743ae97c85043050bb3b790a821b117e75f215043622fcede429886745f9d7cc5310ce8bb3b790a621a917675f2754434a2fcede4ea886945d9d7c85310ce8bf3af93a6219d17676f2150434a
def leaf379xk8 (i : Nat) : Nat :=
  let row := packedAt leaf379xk8w ((i-0)*11) 11
  (((0x6456403226150301 >>> (8*((row) &&& 7))) &&& 255)) ||| (((0x80906830020502000884180446228104a25009148900a25104c061200088422814884100900400211048a05208080600401018044021 >>> (27*((row >>> 3) &&& 15))) &&& 134217727) <<< 8) ||| (((0x141309064503814461301848a41303a0c04d26a34184c46028948a04a8502871301802c340a >>> (27*((row >>> 7) &&& 15))) &&& 134217727) <<< 35)
def cycle379k8w (i : Nat) : Nat := 0xbf6aad0971a0bc6ec96a84678c941e28280
def cycle379k8 (i : Nat) : List Nat :=
  if i < 294 then [] else
    let t := i-294
    let a := packedAt cycle379k8w (7*t) 7
    let z := packedAt cycle379k8w (7*(t+1)) 7
    (List.range (z-a)).map (fun u => leaf379xk8 (a+u))
def w379k9 (i : Nat) : Nat := (if i<1 then 0x96422a4011ee30200682448804a4c0ead3008a6826d6425c4201a15094ee80e6d012c920a8d6013188396641f0f44aab6069dc8026880480e0bde0087d883fd5401c3e0b33d363e281cca4113761317803f6b815fa51879eb8581c8a4092de088f5035df01f4740ac20012620483a83768813212095d9010bf808fb81ee901330b0693b8089d4268e80b2206832eb75ac04b9e81ded012cde08c1204c71020ad00ba1209588043eb81f0d80aaf608f41032f3c58604763025140264ac105c20535503936c25a240f5e20107983b8bc1a3000bb1b09661849e6016144086bb098f881ed400a7c21140f0a3f5f50c08e0d048b5824dc408a760810d02e3e81c588121c20853003d47814aa807e28092a503b3d823ffe0ed8467841d21008d590974c0411bc118080a4d1097ed84b4d49cce20cf0400fb603fb6815ff071180038720212782566607992028ce0498a30fab78a037b78222700a16e03de1042d381908411510087a2043148227901090e08b8d02273e3f6027c38425382167608193085108069ec107c40821b096720334d41741c1089e095b59bafcc0dc8e01cfd00df4a1e5c7b206dbe03ef58138180766007af6031b801ff5c0f9e207b7803f1981e758101b8043e7c67e0143d03b8a84a4fc197200b869077e303c5380d98612760026a6805bc41e14a0769c0933584ab940f050f23718581ca280dfb206d380263e81c6f40e89c06cc5039c001c08c0ebe606ee7885d3008fc00c8c40ce680ca37002b7003cbc1bf3a0aebb070a2000c740214e064f6031aa812eb41c5660317b0342e018b680cdc800d6a070208197581425257c1bdb036f200959a00b2306d1d80096405c400300d02e26817ad00bab40605500759817c200196c02db90020382df801b27a02fe4006f1016ca4e5c7ec04fc80251c0130740ad38050eb0277d01523c0a4aa04bcf02c300134d80aaa0053d702bc90144d40b3cff882bd061740019c408a6e005b10232080b0a40912a0bffd060dc802688010e6007de0600b811ee40091a044dc021f2faf178c08082042b701e8300eebc0795403fea020cb00fb68000aa001293546cf4f38bcbfb2efc5f316dbf56e1eb782c58abaa962a4d27eb998e4f091e64408f4e3908d8a15c84a20327c49dce72159d261115814f292aa438cf993708ca22c7c9ff224479616543c309680dc000004ffcee83ffe6609bfebb0c7ff1d803ffaea83ffd6500ffeba24dff59138ffaa8127fd7345ffeb1a0dff54d17ffa860affd7239ffeb122fff54907ffa8423ffd6108ffea088bff4c425ffa420affe005dffeb0045ff180b3ffaa069ffd4039bfe981cfff481f8bfcee926fe6681efebb2717f1d8d3efcaaa3dfd753cfdf222ad7f5d0d3fbc668b5fd7334ff71120d7f5c8b4fec22bb7f541557fa98a0bfe80115ff2a0517f410 else 0x209f72008f2100eb6c232961237e092ac048acc26a9c10b4d04d9000c03c24854120a204cd6838a78242aa0278ea838566a009a3208ef0be18618211b510862802688c1b4c211c3208ec7152e20d862f730985d83868818f8c0f1660889e9b1fe0e224c6e19b08d5d84c5b0de31671a6b3759e80bd181d6937875a143582c8456dc22f7a0c24d00f7a00ce1c2121c0be590172c84ba44231ce0cea30873183eaa01cccc1115b08b7883c384229e78c37a600440e003bea0bca30876d84b5a41ded40f6e9089de031874020cc111a200470043cf82244c6e1e307a070423801b2be034a3fd268c25510863b0437811c34c1b8ac1052100d6e80e660208960196307d1d841904059be2b34c079b58331901fa1000c6c378b50383d020ffe2270a8d201639a00b2f06fb503da502071a0c57e08039801c6c259620ff6c07f078409901fad86f15e00c54840786954a39807cae83f1b455ec60fa1207ab503da641f1ee0fb4c079fe83065c02fdc0f70a05cf183d278257c800d8e1577d6f75c23d507972211c30815578128f80190a84a76c06d500e67521c7983b9e89546a4e6e62196c00e3781808c0ebff0ec8546f60a73f00a55028fa000c4c0eae1074c203b1b0c5fb6036a700acd03b4c006f86127b3018a303ad7c068220c4e6630a94674035f4019b703a0c4026dc00fb5051550390c41cb500e68f073ca82fd1414bcc43248071ce04997c069f545f708fd40d620012660051581ab9a287c3bf001a5201c61adf4c1b8ea0ddf3030eb037b8110ee8e0d82502d72211dec01ae220eb729024f3835b081541c0be34065738338fc197be2b3a2063e58342400565e0d19706a5b034dac198e20cf1406ab3002868187c80cdb6016a702d82c1a5fe7861697a01920c0c8addec14e900b1f505e5682828818f780c68d0628d030dac16b060ad1106260b76d1578702fbd4179200b844001a28296001760e0bd6b05a8502e4d41749c0b60705b8835ac15a2402c5b455e76002df159ce82ba601603e0b3da057be82d20c15b1e2b28e1573a02cbf6684a37b053e682a6a8146660acc205561029924150080a4b50515382aeb41412002b45052eb0287fc8b4251db845df824a820426b049ea04e2101d9ae02831033dd04deac13d1602a3b0830902629c1571e0e7f707dec00e0501aa2e0473e089078409bc26d6605f7d05a4d84688c0eb0e08b34014c0827f581006a059207a51faf5ac04b98847f181281008dab04f588119ec1069a05ebd03a1e027084114e007fcf02c548277a808228092da0337281e380ff)
def w379k10 (i : Nat) : Nat := 0x34247a01f6402340a9a826310b3d0001e02cc41a3707b90045e043bc06ee08f140d5a049081daa0879015510677c0c77081980f2102aac16be06e2c1fc40471c17ca0046014f10970822940219c299307198033004fb82b4e0a2a427d6016ec0e4c0b408183a0241143bbff
def levels379 : Nat → Level
  | 6 => ⟨3,2,5,2,0,0,40,[],0,10,none,w379k6⟩
  | 7 => ⟨56,10,8,2,2,2,14,[(4,0),(5,13),(5,35)],0xa667799a4465995651936418460d76595635895454d52509412609725887216889de668ce226158460d735c965591635815450d425053121c86211765cd6054d5254143509415013148010,9,none,w379k7⟩
  | 8 => ⟨313,59,12,3,3,6,12,[(6,0),(6,34)],0xa227799a559123388a1161d866158460d82605805d9755d1735c9655916358960551535495050d425053121c8621484200769de66956448ce22846005d9755d1735c96559163589615815454d525414350941501314c1214807618010,6,(some 0xc38583828180454341401f1e1c1b1a19181716141311100f0e0a09080706050403020100),w379k8⟩
  | 9 => ⟨46,46,14,4,6,9,10,[],0,5,(some 0x8b0e1413e78e9c3668c972c54a13203868c16284880e182840608080),w379k9⟩
  | 10 => ⟨1,1,0,2,6,6,0,[],0,6,none,w379k10⟩
  | _ => emptyLevel
def leaves379 : Nat → Nat → Nat
  | 6 => leaf379k6
  | 7 => leaf379k7
  | 8 => leaf379k8
  | _ => fun _ => 0
def cycles379 : Nat → Nat → List Nat
  | 7 => cycle379k7
  | 8 => cycle379k8
  | _ => fun _ => []
def chart379 : Chart := ⟨379,11,7,5,sampleColumns 165 #[(0x23faa80000007f01fff8130021ccc2670e40ff27f,0x219042448912244891201300204c4023064009215),(0x1c07a4800003f800003f88432c530cd9833fca4c4f,0x10063bc3870e1c3870e188432c5308488109ca4c4a),(0,0),(0x1c0450001fc000fe00021803063f31e1c38f38f8c,0x4b050d1a3468d1a346a1803001511e143853868c),(0x1f849000000000fffc04e03c07c03e01fc0fc0ff0,0x5a06852a54a952a54a94e03c07802e00b80ac0960),(0x2001200fe0007f000007003ff8003ffe000fff000,0x8c4021b366cd9b366cdf001748003fdc000ff6000),(0x1c00047f0003f80000007ffc000003ffffff000000,0xe30441c3870e1c3870e7394000003b77ef6000000),(0,0),(0x187ffffc000000007ffffffffc000000000000,0x110018e0c183060c18300c6a8b7eac000000000000)],colTree 0x2000c608881000392040880098800944004e00043200270022090014a000c4800ac000464005882009a0003600b050006300460a021c9020050818c1100280670022016006304040a01b1040105005e000032c0072400114116208004a409c008035001cc0108a802960018540153000a0d021c90000604d8820003440c6080018833801000e009c800847005e80001b802c6000c2001790000b000ad800418005cc0008 32 0 3,#[[],[65,99],[128,49,100],[128,97,67]],cutoff 11 levels379,leaves379,cycles379⟩
def jobs379_0 : List Ticket := [(6,0,2,7,0,0),(6,2,1,0,0,0),(7,0,2,7,0,0),(7,2,8,8,0,0),(7,10,46,0,0,0),(8,0,2,7,1,0),(8,2,41,8,1,1),(8,43,16,9,1,0),(8,59,96,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j379_0 : reports chart379 jobs379_0 := by
  simp only [jobs379_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs379_1 : List Ticket := [(8,155,96,0,0,0),(8,251,62,0,0,0),(9,0,18,8,1,1),(9,18,28,9,1,2)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j379_1 : reports chart379 jobs379_1 := by
  simp only [jobs379_1,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs379_2 : List Ticket := [(10,0,1,8,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j379_2 : reports chart379 jobs379_2 := by
  simp only [jobs379_2,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
theorem l27 : Lower (aug 27) (graphGoal 27) 4 := by
  apply aug_of (hints:=0x301004101)
  · exact prior_ok 27
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l331 : Lower (aug 331) (graphGoal 331) 5 := by
  apply aug_of (hints:=0x301008101)
  · exact prior_ok 331
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l339 : Lower (aug 339) (graphGoal 339) 5 := by
  apply aug_of (hints:=0x601004101)
  · exact prior_ok 339
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
def w347k6 (i : Nat) : Nat := 0x2fd63bf58bf940
def leaf347k6w (i : Nat) : Nat := 0xa4512800404031088c26020a09068ca230980820201821
def leaf347k6 (i : Nat) : Nat :=
  let row := packedAt leaf347k6w ((i-0)*62) 62
  (((row) &&& 255)) ||| (((row >>> 8) &&& 134217727) <<< 8) ||| (((row >>> 35) &&& 134217727) <<< 35)
def w347k7 (i : Nat) : Nat := 0x11021622b819e2894989016ff
def levels347 : Nat → Level
  | 6 => ⟨3,0,0,0,0,0,10,[],0,4,none,w347k6⟩
  | 7 => ⟨1,1,0,1,3,2,0,[],0,3,none,w347k7⟩
  | _ => emptyLevel
def leaves347 : Nat → Nat → Nat
  | 6 => leaf347k6
  | _ => fun _ => 0
def cycles347 : Nat → Nat → List Nat
  | _ => fun _ => []
def chart347 : Chart := ⟨347,8,6,2,sampleColumns 79 #[(0x400003ff130e670e427f,0x14a5294a130263064215),(0xf801f84298633fc4f,0x6318c631842984109c4a),(0,0),(0x1f07c001831f9c38f8c,0x6318c631800a943868c),(0x40007fe0e03e01fc0ff0,0x694a5294e03c00b80960),(0,0),(0x3e0f8000ffc001fff000,0xc6318c6394001ef6000),(0,0),(0x3ff00000fffffe000000,0x318c6318c6bf56000000)],colTree 0x1001580000ca00ac8000550052c0010 3 0 0,#[[],[65,99],[16,131,100],[16,96,67,48,131],[48,65,96,129],[48,129],[64,16,131,49,97],[64,49,134],[96,132],[96,129,48,65],[128,49,100],[128,97,67]],cutoff 8 levels347,leaves347,cycles347⟩
def jobs347_0 : List Ticket := [(6,0,3,0,0,0),(7,0,1,7,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j347_0 : reports chart347 jobs347_0 := by
  simp only [jobs347_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
theorem l347 : Lower (aug 347) (graphGoal 347) 8 := by
  apply chartRoot (g:=chart347) (ob:=[(331,5)]) (hints:=0x301004101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    subst a
    exact l331
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=jobs347_0) j347_0 (by decide +kernel)
    intro k hk
    change 8 ≤ k at hk
    change (cutoff 8 levels347 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem l379 : Lower (aug 379) (graphGoal 379) 11 := by
  apply chartRoot (g:=chart379) (ob:=[(27,4),(99,4),(115,5),(331,5),(339,5),(347,8),(355,7),(371,8)]) (hints:=0x351004101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact l27
    · exact l99
    · exact l115
    · exact l331
    · exact l339
    · exact l347
    · exact l355
    · exact l371
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=(jobs379_0++(jobs379_1++jobs379_2))) (reports_join j379_0 (reports_join j379_1 j379_2)) (by decide +kernel)
    intro k hk
    change 11 ≤ k at hk
    change (cutoff 11 levels379 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem l319 : Lower (aug 319) (graphGoal 319) 11 :=
  augRelabel (ps:=[84,131,98]) (by decide +kernel) l379
theorem l351 : Lower (aug 351) (graphGoal 351) 11 :=
  augRelabel (ps:=[100,131,82,16]) (by decide +kernel) l379
theorem l367 : Lower (aug 367) (graphGoal 367) 11 :=
  augRelabel (ps:=[101,66,16]) (by decide +kernel) l379
def w383k8 (i : Nat) : Nat := 0x53edb321d920429f6db906c902147b6ca999dd83a79b654cc66c1cbb9b4aa9838025f4d9554c1c011ddaeda524530c6ed10d292298657677694914c33aad2c6648a615dc6d49180130a7ab734446608735688656330439cb4432919821d659dd948cc10
def leaf383k8w (i : Nat) : Nat := 0x2d710000367204421110020311100100cc600100cc600088e3700201a3600281a3600281a3701508e376020180700201a36002019a6002819a60
def leaf383k8 (i : Nat) : Nat :=
  let row := packedAt leaf383k8w ((i-0)*32) 32
  (((row) &&& 255)) ||| (((0x80203004040300802030088846010904c0202018040003 >>> (27*((row >>> 8) &&& 7))) &&& 134217727) <<< 8) ||| (((0x10685408984a2409c0c050b8180a160a8502a160a01c0c05 >>> (27*((row >>> 11) &&& 7))) &&& 134217727) <<< 35) ||| (((row >>> 14) &&& 262143) <<< 62)
def w383k9 (i : Nat) : Nat := 0x2a048100120901141381504e0481382104e084139040520fc2602d0500fc1e01f0941182583f04e13014c110a61480882e05302026021095c0c168360780001f8000a204824804098084258170761141084b0360340884f04212c1084b03c074288210960a00681e099301c098110070961080601e0995a1a0981100700c12c00aacc2c48265c3009008e07c042270209c12bdc1bf421741c881604138082303d7627cc07c0f8000643b4e25a403c0f8040700d0779c41340b81f0000c875b003480781f0000c87716616c017aaea5beb51676b8d45a5f4667c4c192b1fe29c3d84f045fdbe5788eb9c136c6accd58faf356ea2d221ac2763bc4c04c0019ee71263fda3457baf968ff6b2d9f6b65a3fc8bb47fb9838ff70471ff0c8e3fdcc2c7f91858ff866b1ff09963fe19a47fb8c48ff704997e14473dc77863fa4b08ff70218fe90433dce0857fb4499ff68d13fed65abfdac357f8f769ff86479fefc8ebfc76ae7f88d5dfb7dc55fed05efbd803dfdac079ff6b295fed6127fc8ba57f8f74cff12e95fe3a927fc84a4ffc321cff7e43b7ef4476fda88cffc2f0cff7de1beeebc37de1786fbbcf0df719e19fe92c2bfda086fb9c00bfb5801bf6f3837edd706fd80e0afe5093df86366bddac477b2988af784d15eed1a2bdc7bc73bbf78e7712f19eebe5b3f94cb63fc176c7f22ed8fe915b3de0b357b9166e777acd5eeb88ebde159f3bbcb3c7f7a473fd0b4b7f056957f2f87afe5ccf5fc3d9fbd9fb3f7b0f67ef612cfeecf59ebfa15be7f10b7afe216fcfcf2dfbd9d5bf7b1417e7e782f5fcd05ebf9b53d7f0ea7afe6c0f7dcc01efe9603dfe2a07efc7eaffe8ed5fbf0aabf7e0357c7f4ee98fe25d2bdc7b267bc014e777829dea0d533f5f1a6bebc34df574699fa50d33f93a267f0944ef60689bf81d131fd210cdfc311d3f7a23b7a8d467de1786bbbcf0d7b79c1be6eb835f92386df2270dee3ce1bf469c33f5cc06f6bf00ddd42c1bda7d83bd5fb07babd60ddd4161bda7ac37750086f69e10ded3d415fad802fb58006f69e00bf958017f8a00014ff9178059ff0614167fa66505beed3c014ffb8a005bee728016fd92e003bf86364256fb249093f6b658147fa996051fee6081c7fc3320b9f6fb88267f3ed2051fe42dc24f7b194053faae50157baf84051ff0990167f0884051fee6041c7fb8210597efc44265f9711051fee600167bbef0079ee72c0167dbee0099f65b80a67d84e0099f65380ae7d82e0911f6b65a9ceeb234491fae6012e76bf0049baa858126f29f60
def leaf383k9w (i : Nat) : Nat := 0x3d2305ce303d2303d2303d2305ce305ce30148101481035510148103ce30355305d230162105d230162101481014810216503ce303ce303ce303ce305a0d05a0d05a0905a0903cf103cf103d2305ce303cf3035530355105a090355173d210bce03600033ce735000350003600033ce8350003500064c6f4d0004d0006b00035000450004500082c00300004000052c001bce139d0a1cc6a1cdca1cc6a1bceb1cc661bceb1bceb1cc6a1cc6f1bd211cc661cc66190661a4661a46a1cc6a1a46a1bce11bce11b5501bce00bce013cef1500e0ac0e4d00049481451803148141481104cb298a0398a0398a0398a01cc6a59480594805890a50c0023ce34bce313ce133cf14bcec4b54c33cf27e5a47d5ef7c9a27c1a22a8a03b82a3c44f3b82f2a8a03a8a03c44f3b82f3c44f3b82f3b82f3a8a03a8a03b82f3a8af39d0f
def leaf383k9 (i : Nat) : Nat :=
  let row := packedAt leaf383k9w ((i-39)*20) 20
  (((0x9287828180767572717064626160434032302110 >>> (8*((row) &&& 31))) &&& 255)) ||| (((0x2050483082012005124960a0482c122a14824140b040403008020300a090681404060202018040101804050300808060100406011108c0212098040403 >>> (27*((row >>> 5) &&& 31))) &&& 134217727) <<< 8) ||| (((0x2430380c5a2b148541a050914824d629151a8d268349a8d069251244e06028940e050d0582417030142c1a090582b140b0542816088482a160a0541a0508858240e058281a0b048300e0505c20120b07028160d0481c1805 >>> (27*((row >>> 10) &&& 31))) &&& 134217727) <<< 35) ||| (((0x20a0c1508450211148020110500c1308044200a0c02818080c0201804420100c02030000c0000 >>> (18*((row >>> 15) &&& 31))) &&& 262143) <<< 62)
def leaf383xk9w (i : Nat) : Nat := 0x9040641081a558298d1750803413c25eca8a1d42063c8a751ad8d1750803413ce5eda8a1d42063c8a751ad8d1750803413c2decd8a2142063cda558298c07208023169560a6301c82008c5a558298d17508034129d46b6301c82008c4a751ad8d17508034169560a6301c82008c4f0b7b3628850818f329d46b6345d4200d04f0b7b3628852418e329552a6581c82040c4f097b2a4172241ce23c31ece8a2152063ccf0b7b364182241ce33c31ece8860920638cf097b2a4172241ce2
def leaf383xk9 (i : Nat) : Nat :=
  let row := packedAt leaf383xk9w ((i-0)*14) 14
  (((0x857568676456504034232016151201 >>> (8*((row) &&& 15))) &&& 255)) ||| (((0x412050682112890280c0e031088c008140240289440011084904920820120090283410040601409058245029048141a0902034100406010140e020080c020080c0220108042011 >>> (27*((row >>> 4) &&& 31))) &&& 134217727) <<< 8) ||| (((0x13088c424503814262301848a41306a24120d0a8140e83013c1a4d069351a09a552292c9a4925428141a058282c1a090542c14068540a0d07010160d048180602 >>> (27*((row >>> 9) &&& 31))) &&& 134217727) <<< 35)
def cycle383k9w (i : Nat) : Nat := 0x1b34e4bf6aad0971a0bc6ec96a84678c941e28280
def cycle383k9 (i : Nat) : List Nat :=
  if i < 166 then [] else
    let t := i-166
    let a := packedAt cycle383k9w (7*t) 7
    let z := packedAt cycle383k9w (7*(t+1)) 7
    (List.range (z-a)).map (fun u => leaf383xk9 (a+u))
def w383k10 (i : Nat) : Nat := (if i<1 then 0xdb869186b13c0b16803572056f265666d5b06a87e802b758144c14d62842559155d80ce692ba184e7c84c83b76a00f580186a3558006b1d06a0b681db543ed459a545a5e41a4b41538019a9cea52a45bb566c17c40644e168a8164e80682f338c14f205731019194195e818e0857f8019a944080a9dbb566c0f82d2c029180308582f5d8303a8317782f82b76a5412f66c0e028b382dd982e1b12582b76824b1c051e3053c715358052cf1522d05424151a51c284b76acd8e7246f9046040ae7e050bd0ad2369199b6a8788809a380941022ed04a03827848d61e1b6908c1f6a0994e09a5a0967e0896c804b43c101218c10fa0125e411c400113812885ab26064103d81048403aac239fc03e440fdd82afec23cf435a2c7ff8d3fa81f5d044420448f8455881ea10058619d4b011dc8d49e8550b8060009d1e3660bf709cfe0041d041018036501dc084180840e391c5701e1f803c801bdb004ed8100a0051e3660bf601968099600016a0019d8815481b5bb14c256ec032950318500000001b7602565a1017302f8702cc0002ea13048035f5033850003f12e3c134bc0294602db760c17a8c2a1ba7fe9d6a70a985a5de95ba40e8eea3168879fb679b9dca73b9a9e68b985a5c5948e4ca91fa42c8f823958c1a2d58a1222c865616b848204e80e60027f99faf7d25f1a7a49e177809dcb7619d2d73d9cd372c1c6c706db936d71b0b6bd9a2d64b58775eb56b3598957051f53fd4ce51ce44c909e40e4f9e3ae4e0f3454c872ec0b362a30a2e258c89f20b07681b4c63116f852a119c347084c1780430000dffc6dff56fffb8fffa6ffe66ffee3fffb2fff97ffe07ffe64ffe94fffa1fff90ffe00fefb8fee78fefa8fee68fee38effa6fef96effa3feed3fef97ffdb7ffd97ffc57ffcd7ffc17ffc07ffd87ffc47effa4fef94fee14ffb84ffa44ffd74effa1ffb81fef90ffc80ffbb0ffb90ffad0ffa10ffac0ffa0014fffa803fffa304fffb513fff6510ffe7523ffef502ffe3504ffec734fffa403ffe2413ffec416ffeb472ffec026bff2913ffcf915dff2964dfe5904dfef92bdffb833bfe7866bffc627dffb618dfee626dffa618dfe6625dffb349bff5307dfee333dfe2334dffa33ddffb506bff6525bfe757adffb203bff6215bfef204dffb715dfed736dfe1721ffcc748bffc439dffb403dfe7415bff5417dfee427dfe2415dfed405bff0405fee9424ffca433dffb148bff5115dfee133dfe2103bff0193dffb0a8bff2076dfed086dfe109a9ff2933dfcf9a69fe7899defb854dee7878eefa8f99ffc658cffa664def9643deed365cffa3979ff535a9ff659a9fe75569ff6295bf71246bfcf25adfdb742dfc7779fed9778dfcd745dfc1778ff987579ff64669fe7445dee1464bfa4485b7f41d4bef20e4bf71065dfbb044feb90c4bdb30 else 0xe026467c11a340cf478c7884501243843e28092bc274d027a107246cd53a47881804b6884aed04a4f461082320a51c24c1900e781253e1850874d8b8906e01132090b09106f010ed8106e1901e3730172fe344481825ca5c0200fc13ce4e02ee2a35d25c4b90f541404880f1a0401c05db1052c43ebdcc78c6dc020570d03e5bb5453a63eb5b2a1f55646856c292041c5707703643b7402ab00dce042a5203bd21474119e04bdccc05c99851519f389025ee6f42b67ce87081af0cb291d68d82da7165aa8cbc39073b76ac162240cbccb09f080b55ca4135719613fde2df04140c81687819ab7696b1543e1c22242a8f766a0dfde2dec816809ab8de294da094ec06c040ddb45b025140b15a0b28f18902456ed59b0818b8688cfaf2e616322ceedb4e8304b94b8580180a01b342198c119063193b318bb019b768f9e2241f3d1f55f86592e04e1473f0ce63d220e12805d91414e9cc084dc10229f8222e3890207718c0b23e0b40a9c136e8056602601405ac260a1015b66e5ec0505825d3812add8a33c90504bdc874ce6f42b59b02e61cde856cf160e1af0ce6a4449fc2b0f16201269978f208e88aaa1ef1183443d6230a11d39a91124701204cd839210907f00fdd01152b5c108482282150848f9008033c689db5a2c790807542a5d2bb45042760abf201004d5c043ce9c06314042a744321c232688285c0305002ab803454c296a8707a1160c14db80440810b06150840165230f0e119bc042e811a6c1a63c091982f8a40e840167e00e806135410f14213ae152c890a12e9cc490303053018030218441854270844d853ae0431f0ab95846fde2fcf6028b032ee44284872ece4d2340f8f20d2b41641425ab0647d9b6f1c2883fd303ec50bedab3310499d4c19f4c2e8202d7605e990139046556c93a041c434e551da336d58fec032a607d560793607eac232ce2662c27de0066160729d1e35bb5666d81ea64caca0cbca0f6340f9d40f16ed4d1e8c662ac0f2d06c7ce2f0f40c72a063d40f142283056ed59b0040394200bd60ea184381e56ec21715c4ec1016ac80ec3a16ec64c42c0e54440aea0c4280ee6ed59323ec5b78e7ac1d4741d37497e401c3bc17c15bb53e719b3630116be49782c17a041c4581ca401c2ddaae3d601bb481b52897570176dda1f6a09958499424b81649f660b80e09e0c15bb5555496e0426d9c16cbca6fe82cf74eb3b01b170218246b060bb768d311e1a6b5808b43e0b548eb4441606c080b56c459b0edcb3a2ce302ca5baca38499b0579f149da0c9c01c9e192cd80a12d191f66)
def leaf383k10w (i : Nat) : Nat := 0x667501232012320677501132066750113207976066750113206675011323118232a86311823118231182612325129268393512823119221121266642956221221283622112121121211216959353b9652a8619562458757956261132111213119284440400104001040010400104001040010
def leaf383k10 (i : Nat) : Nat :=
  let row := packedAt leaf383k10w ((i-92)*20) 20
  (((row) &&& 255)) ||| (((0x808261300044208100a010004421140a4420804801301848245429044021005048340808060080a06 >>> (27*((row >>> 8) &&& 15))) &&& 134217727) <<< 8) ||| (((0x28a4d22c905824911884509148260d44821a4944926d148a2c920903416090582212 >>> (27*((row >>> 12) &&& 15))) &&& 134217727) <<< 35) ||| (((0x54210500c1108028300a060203004030080c0000 >>> (18*((row >>> 16) &&& 15))) &&& 262143) <<< 62)
def leaf383xk10w (i : Nat) : Nat := 0x254281500205019e1229048820120759140e0409140a540d26a3400802030181d0602480512858950a05404834167848a4122281489d6450381024502950349a8d0020080c06074180920144a16
def leaf383xk10 (i : Nat) : Nat :=
  let row := packedAt leaf383xk10w ((i-0)*62) 62
  (((row) &&& 255)) ||| (((row >>> 8) &&& 134217727) <<< 8) ||| (((row >>> 35) &&& 134217727) <<< 35)
def cycle383k10w (i : Nat) : Nat := 0xa50
def cycle383k10 (i : Nat) : List Nat :=
  if i < 138 then [] else
    let t := i-138
    let a := packedAt cycle383k10w (4*t) 4
    let z := packedAt cycle383k10w (4*(t+1)) 4
    (List.range (z-a)).map (fun u => leaf383xk10 (a+u))
def w383k11 (i : Nat) : Nat := 0x27c6247c2158818470137305f6b05397411b5051888d87e41664013910dcca45099c224c010a88937dc1f5581cca45b598bdb3392602d878305e142350243c8bdcd00c7483f82835691c0408a2630c0679306f824f10a9fe1351103b9b21a571a9848c4789396b09f338448e842018397880f2f0ad1528ce15fe08a6c0789a4be48aacba08cde4e0a8280dc10e440ef020e1d602fb830db2111380bee60eb1808e0c0f05188207df16caa6664de3007f3a04a8a0defc0833a0b4c00bd3244b940edd602eac0d3a4080404bc60084662a49a4d2e60ebfe6a4b410d8cc5538861e20ae0e0a2448b3ba076940b01c87af609e6c079fc4a248aac26e60c24bae207ae82a37a6ac806a336cad0646952461166abf20b35e0a86c8692a068fc0acf0877600bb8c0aaba6a8d4060c8027a28797a02834e689416f6ce145a0243e10baa1064a07172671760dc160216a073ac0b906507600fdce4227e223726232c4b9dc6214c074dc023704dc5ce2aa55184d50838217413036640668a136af054e8037d1166fa26ddf1351d084e6035ad0742920dcda8c3006207051400325d02b880092902a0f05011008520683702e1002c58082e40670506a6406699225ce007bf052bc05356069e906b7a02d01006db033030316a030dc081f102f28528b5f1954e74097500a330203e4194c80140409d7c0a5c41915809a0fca14600c572606ac244f609f68048462473a2c40620756242a0209d20ff64042f20c6602ff600fcec4c4ba2c674047dc0449a407706c5940098e00707b59ca49480065f2299680486e4653a6532225334604e207b5a265fa09610040f26657841fbe093d006fba0983443ede03b9c01e4c2934c075d2004be0537a0952c66e9a4534603ea623aa2296662407301cace2f68400ddf176dc07bc52799f001f401c4c2745907a0901b7c07c790636236511119561655f2016f01d7216bbe0793e36b991788120d66116f707dad07405ed9c2a710c3604be90cbf9c8339810c4c0da68063e4031441101022f048d810069f8065e80b6f422bb8089c48b75cc9f2c49ef40502075ed9c2bd8054540fa148d4440210805ac80873801e6cc9a3c49aac4bb1481ddccbae882f980d4908233002f3855d0b8c20069f0b79d8b95d8375900722837d5836b113234086fc8061d03654838ad934609b240838380864a81a67007ce9b47c0b87000562885ab039818396600580f8be6cc620610f0609f0015915e56160d605c6005e8310173000ee1009c05fb005de90021315fcd9acd81e376e9b5bd96cc512008da266aabd50b865e2530d5c2580004afffa21a6ffe33473ff60d34ffc838e3ff5cd35ffc733a3ff801caffd30257ff0c174ffc107e6ffa2186fde33522ff60d03bfc8369ffe800e4ff410
def w383k12 (i : Nat) : Nat := 0x1e24fee291007e610ce0dd450a06e201bfe26882e9a604816ba0ac03058710e3ade42a825ca1f241d3612b60444090203b839b23cb2153800240fc618927206040201f9ff
def levels383 : Nat → Level
  | 8 => ⟨15,0,0,0,0,0,40,[],0,12,none,w383k8⟩
  | 9 => ⟨188,39,11,4,3,4,15,[(4,0),(5,10),(6,36)],0xaaa99a22778cda96a1a7695a468da2685a06619765995651936499161d835cca92a0a7284982448720c73a66889de3384600661976599464d926418760d735c5704c09825c932448720c73a2233801835cd3020c730c010,11,none,w383k9⟩
  | 10 => ⟨140,92,14,4,4,8,9,[(4,0),(5,10)],0x299a22778ce118019865d9665193649916418760d735c5704c5302609724c912408720c73a2233801835cd3020c730c010,7,(some 0xc0f02c070087e1d8460981e06816048060047d1e445104250841d064150440d024009f240531485113c4e1304b124481184510c42104400fc3e0f43c0ec3a0e0370d4340c8300b42c0ac2a0a427090220842007c1e0741c06c190601504c120441003c0e0340c02c0a0240801c060140400c01),w383k10⟩
  | 11 => ⟨16,16,13,4,6,8,10,[],0,5,(some 0x2070280c013e4e2612c76271087c3c1d098441c0d038180a04018080200),w383k11⟩
  | 12 => ⟨1,1,0,3,5,4,0,[],0,8,none,w383k12⟩
  | _ => emptyLevel
def leaves383 : Nat → Nat → Nat
  | 8 => leaf383k8
  | 9 => leaf383k9
  | 10 => leaf383k10
  | _ => fun _ => 0
def cycles383 : Nat → Nat → List Nat
  | 9 => cycle383k9
  | 10 => cycle383k10
  | _ => fun _ => []
def chart383 : Chart := ⟨383,13,8,7,sampleColumns 262 #[(0x388ac000000003fe00ff80001ff002c6004203f193090d9a33c9401c73e21f673,0x57700984c26130984c26130984c002c6004201319100048a11c94000112209631),(0xbc50c0000007fc000000003ffff01008190c2c861f1632604c0ff66a4c8c6487f,0x1288c5068341a0d068341a0d068301008190c2486060210200402162a448c24846),(0xc11380000000000000007fffe00960f060704f181c98c38470f188738f1078f9c,0x8113ac964b2592c964b2592c964960f060704b1818984384705188508b1058298),(0x3cb6f00000ff80001ff007fc0000203000180701fe0e0fc0780fe0f83f01f80fe0,0x5248432190c86432190c86432192030001800002a020bc0280ae0283700680d60),(0x10084000000000001ffff8000000c7c007e007fe000ff0007ff000ffc001fff000,0x10084345a2d168b45a2d168b45a2c7c007e007ec000df00056e000d7c001976000),(0x10008001ff00003fe00000000000f80007fff800000fffff800000fffffe000000,0x1000806633198cc6633198cc6633f80002b94800000fffb7000000fffeec000000),(0x5403fe00007fc0000000000000fffff8000000000fffffffffff000000000000,0x5400783c1e0f0783c1e0f0783cfa7528000000000fdefdffbfde000000000000),(0,0),(0x202b03ffffff8000000000000000fffffffffffffff00000000000000000000000,0x20b1381c0e070381c0e070381c0058ad546b7ffd5f00000000000000000000000)],colTree 0x20003c20a090001d2048880031822284000e4810620002f003410013801114800a60006640053002322002b0001390016102068800b10401b40005c0168a0003600b250002700562800318023850218c11102840c6088214005e10404a080bc00c051005e0048280670022214013c0010ca049c0088250153002302802b8001194214c00888b0031820285005b00013288298010914036208030a00b88101450059820092802f0000394813801016a0017802a15000dc0148a800ce008c18043d20400c143182200602ce00440304a98011018454c00840c600bc00106015c408083002f800019a003d20008c08b88100461853002023400bc200098116608004c449c008036001dc010838003e00b01c013900118e00a7000627001bc011038027c00209c016d00048e00bd0000a73405e00003c087a40001e025e10000f1431820007055c4080039167002001c654c00802e00b1800388000fc01404000be009020013d00109000af000428005b800114002f2000360015b00093000b3800318005cc000c4802fa000124017e000072003f802019005dc0008d8027e00206c015f00083600b780021b005ec0004 84 0 5,#[[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]],cutoff 13 levels383,leaves383,cycles383⟩
def jobs383_0 : List Ticket := [(8,0,15,0,0,0),(9,0,6,8,0,0),(9,6,26,9,0,0),(9,32,7,10,0,0),(9,39,96,0,0,0),(9,135,53,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j383_0 : reports chart383 jobs383_0 := by
  simp only [jobs383_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs383_1 : List Ticket := [(10,0,1,8,1,0),(10,1,32,9,1,0),(10,33,46,10,1,1),(10,79,13,11,1,0),(10,92,48,0,0,0),(11,0,6,9,1,0),(11,6,10,10,1,0),(12,0,1,9,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j383_1 : reports chart383 jobs383_1 := by
  simp only [jobs383_1,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
theorem l23 : Lower (aug 23) (graphGoal 23) 4 := by
  apply aug_of (hints:=0x21002101)
  · exact prior_ok 23
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l47 : Lower (aug 47) (graphGoal 47) 5 := by
  apply aug_of (hints:=0x321002101)
  · exact low47
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l55 : Lower (aug 55) (graphGoal 55) 5 := by
  apply aug_of (hints:=0x521002101)
  · exact low55
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l119 : Lower (aug 119) (graphGoal 119) 6 := by
  apply aug_of (hints:=0x521002101)
  · exact low119
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l383 : Lower (aug 383) (graphGoal 383) 13 := by
  apply chartRoot (g:=chart383) (ob:=[(23,4),(27,4),(39,4),(47,5),(55,5),(99,4),(103,5),(119,6),(127,9),(319,11),(347,8),(351,11),(355,7),(359,8),(367,11),(371,8),(375,9),(379,11)]) (hints:=0x321002101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact l23
    · exact l27
    · exact l39
    · exact l47
    · exact l55
    · exact l99
    · exact l103
    · exact l119
    · exact l127
    · exact l319
    · exact l347
    · exact l351
    · exact l355
    · exact l359
    · exact l367
    · exact l371
    · exact l375
    · exact l379
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=(jobs383_0++jobs383_1)) (reports_join j383_0 j383_1) (by decide +kernel)
    intro k hk
    change 13 ≤ k at hk
    change (cutoff 13 levels383 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
def w431k6 (i : Nat) : Nat := 0xc5b214925cd42
def leaf431k6w (i : Nat) : Nat := 0x0
def leaf431k6 (i : Nat) : Nat :=
  let row := packedAt leaf431k6w ((i-0)*0) 0
  (82) ||| (0x2240a0d <<< 8) ||| (0x41b1582 <<< 35)
def w431k7 (i : Nat) : Nat := 0x3a0034180b0502c1a060503018040a487ed921b24021ff058fc8e7f42998ff8163feec8ff4523fd0c8ffa123fe04d9f1636bc50dae1436ec48dba1232ff92daf64b6dd12dbd24a3fa32cbe2cb2f8aabbc687ed1a1fd4e872bd9321fd4c8461ff0428f658c63f24118fc8c4a7e219
def leaf431k7w (i : Nat) : Nat := 0x104632001000102140001072327262756282218421743274723b727421135277320a105c4269519861
def leaf431k7 (i : Nat) : Nat :=
  let row := packedAt leaf431k7w ((i-7)*16) 16
  (((row) &&& 255)) ||| (((0x22301884401018814120c5024160240a0d02a241a0504834088846011100c022010804040300220108040403 >>> (27*((row >>> 8) &&& 15))) &&& 134217727) <<< 8) ||| (((0x34b89c0e2b0d82c541b0583c560a482c1242a0d028362b04a241a094426110984a24 >>> (27*((row >>> 12) &&& 15))) &&& 134217727) <<< 35)
def leaf431xk7w (i : Nat) : Nat := 0x20d0a81020080c2316490490004420da12290488201206492e160a801028115502c14413018452848a41220804814c4a8502a0040a034540b0500540a15070b89c0820080c121649049000442096120d0488a0522269142a04090283580592412400110802
def leaf431xk7 (i : Nat) : Nat :=
  let row := packedAt leaf431xk7w ((i-0)*62) 62
  (((row) &&& 255)) ||| (((row >>> 8) &&& 134217727) <<< 8) ||| (((row >>> 35) &&& 134217727) <<< 35)
def cycle431k7w (i : Nat) : Nat := 0xd830
def cycle431k7 (i : Nat) : List Nat :=
  if i < 28 then [] else
    let t := i-28
    let a := packedAt cycle431k7w (4*t) 4
    let z := packedAt cycle431k7w (4*(t+1)) 4
    (List.range (z-a)).map (fun u => leaf431xk7 (a+u))
def w431k8 (i : Nat) : Nat := 0x6145e0cd8033882c302c29544a1a00520540040b530ef3079dc360828205a1a0c0f14910c89c2097d062d04426082dcc17650b6a807600c9c041a1404018806098a8909888a85020c3c056285c2a289813fe0a0a8a360447824022a29062dd915ca0ab681f142e3008210399853c6097105a50364015b62fc4020c5b01050b298745b54022c5205da0e75022a80f082cbe00da0e06020a4ae8c710a0cbce74adf1a12dd578a9146274484840eb0f11c23005388e0740027f6b67f82a7f6ae7f8227f69e7f6967f686bf646fe4c67f6927f6827f68eff5b6ff5777f7ab7f7a77f0e6ff81b7f45aff0ef7f7a37f3637f262ff81eff0df7f45f7f41f7f39eff8177f696ff6577f4977f4577f4177f3d7df2577f396ff647df346ff5c7df006ff586ff8137f692ff613df0d2ff0d37f4537f393fb212ff602ff582ff80eff60eff0cf7f44eff5cf7f40ff724f7f38ffe78bfe34bfe30bfe28bfe24bfe2cbfe20bfe18bfe10b5f6b75f7abd77b3774735f7a77b6afbb7ef7b4afdb7af7b46feb76ff372f7b3ef3f7e35f7a36f763777237b6e2fe80bbe7cbde78bee74bf670bfa6c82efcd73f7f3d06fecb41ffe1c8f9fc1a1e7f82479fc392e7f0a569fc191a7f69839fc380e7f0a03cfd272aef5c4abdd612efd5075b7c340afe4c06df922177e4485df8f24bfa188bff052
def leaf431k8w (i : Nat) : Nat := 0xc1206090304818840c42055502aa818240000000000000052e0c12015b8000000000e690000053a815940e6900000120c154e0000060905848182416320555039a4000018d20783030481cd200000732830480c4a02970c0903048056e02f7000002a980000124109208490424820aa6014a039941cca029450003304918308c1856211a1e0d0b06858342c1a160d0b06c1c343c3800140002000400018000a482f24159208c9052497107b
def leaf431k8 (i : Nat) : Nat :=
  let row := packedAt leaf431k8w ((i-23)*17) 17
  (((0x76716463625453524340322110 >>> (8*((row) &&& 15))) &&& 255)) ||| (((0x22301881422150248249048281608a0522112094420804804080500245029048141a0880420100406014120d022201804402100808060040403 >>> (27*((row >>> 4) &&& 31))) &&& 134217727) <<< 8) ||| (((0x62b0d82c541b058a5522b1385c0e171381920b0490a8340a122904c1a1502550b854a241a090a25028984a24 >>> (27*((row >>> 9) &&& 15))) &&& 134217727) <<< 35) ||| (((0x120c044200a8402210080c010180403008840000 >>> (18*((row >>> 13) &&& 15))) &&& 262143) <<< 62)
def leaf431xk8w (i : Nat) : Nat := 0x3692aa551c080210101094a1909c8ac4528291a3cda0c468f3694321311588a46d2553aa38d00420202123692a9d51c680210101091ac9552a8e34010808084a50c84c4562294148d1e6d2874a622b414a0a468f379429930d18883051247929b49552a8e040108080848d64aa75471a00840414246d2553aa38d0042020212
def leaf431xk8 (i : Nat) : Nat :=
  let row := packedAt leaf431xk8w ((i-0)*17) 17
  (((row) &&& 255)) ||| (((0x413018480022108211289020542a0040a0400110824110984482510820120102014009028341004060150285028904a04010180401018044021 >>> (27*((row >>> 8) &&& 31))) &&& 134217727) <<< 8) ||| (((0x124c2412122904c1a15025120d04a2130890a25028b24824132884425428144a261202c1a09 >>> (27*((row >>> 13) &&& 15))) &&& 134217727) <<< 35)
def cycle431k8w (i : Nat) : Nat := 0x3cdf2b688de6543ca140
def cycle431k8 (i : Nat) : List Nat :=
  if i < 104 then [] else
    let t := i-104
    let a := packedAt cycle431k8w (6*t) 6
    let z := packedAt cycle431k8w (6*(t+1)) 6
    (List.range (z-a)).map (fun u => leaf431xk8 (a+u))
def w431k9 (i : Nat) : Nat := 0x3901bb9064910bfc019fa472520df5f0ccaa1cc1873f28653a1ccec2df4016bb28961f0d5281bdb2258881c9a850fd01bb21881466b4861fa16cb00f9dc199205d76321c350c05e1c7100bb881d721c8840b9fc1699c2ac7893f60de180ca380b410bbb90b0bc16f302c9f00a29028e8439ca11f9c5a32031050afe41444427b3855690a848148d4281a86e8108402159601f32853712c4b0d73013b9403c284dc50d91e13110256a0084e013381b7882594c43048e508f1411bfc229e8954a185f030ca81dcf801d8129cc1aba8033504982176721120421650b047061aa054a40a7a043891022594a1a5a86069840e610b42105e40294c178b5ac05e540ed641c7203d6c074440e5941fac03ead078541a1cc87230532909acc1599e06974153e0200204da82aa3c507b82c8c05c19380ae305e7f05a4014bb0387204683083801570600f4c776b0d3fd01a6a1b8e422320dade0e56c095a430e8812e50cb5a0f2344932853d005a2ed65380ad9c541689baa030ae07b7411b50a1f705839a203dc832790515d055b829f44076c063fd01b442134c77ec010a20223e009c86a6a8155204520228a8343940dd0277513e0409b7411a6029b604b020911c4ce08285204418421c2442fac838e60d42213df0105100bf60deae0791c5d1a86eb90b1f607e4c2f1d8216b0192234bd0218f8d97103a48174a834490dc572037ac05ec80c67c00ea01ccf035540620c01cd0350c0649c067981b0a0008e0363e00b901a23830720278805ddc19cb00487b2837bd81e00df56642fad47a9bf46d2004c4a58520f8d6433e0006effcaaddff54c97ff1136ffd627cffaa4b7ff14acffea119ffc425dffa64b5df95716febaa17de3394bfae6a5fb88adafeb9567f920
def w431k10 (i : Nat) : Nat := 0x4a8a4c001301f58da280a704bc8e65813f074e89ac08fd07e103bd058404250d72832d85528ee0024c82d80b910632097e0f398695080626eff
def levels431 : Nat → Level
  | 6 => ⟨1,0,0,0,0,0,40,[],0,10,none,w431k6⟩
  | 7 => ⟨31,7,7,3,1,0,11,[(3,0),(4,6),(4,20)],0x65d966559464d926416555143508982549221454a218761183605765d5735c94250485210825d57354d4248052,9,none,w431k7⟩
  | 8 => ⟨116,23,11,2,4,5,10,[(4,0),(6,14)],0x28899a559123388987619856118360981601765d5745cd72595645895454d5250d4250532214842085495633889755cd7258953549424c92014842,8,none,w431k8⟩
  | 9 => ⟨16,16,13,3,5,7,10,[],0,4,(some 0x448658a9418284870c10180),w431k9⟩
  | 10 => ⟨1,1,0,2,5,4,0,[],0,6,none,w431k10⟩
  | _ => emptyLevel
def leaves431 : Nat → Nat → Nat
  | 6 => leaf431k6
  | 7 => leaf431k7
  | 8 => leaf431k8
  | _ => fun _ => 0
def cycles431 : Nat → Nat → List Nat
  | 7 => cycle431k7
  | 8 => cycle431k8
  | _ => fun _ => []
def chart431 : Chart := ⟨431,11,7,5,sampleColumns 150 #[(0x800000007f0003fa319909193208b6639f673,0x10b468d1a3468d1a2318909191208962089631),(0x180000000001fffcc21c3061fc3138726487f,0x94a952a54a952a54c21430606c31285224846),(0x33800003f80fffc0003e1c181c041cf9c78f9c,0x2091224489122448800a1c1818040028458298),(0x3200fe00000fe0000fc0601fe0f81f01f80fe0,0x170e1c3870e1c38705406002a0f81f01b80d60),(0,0),(0xc7f01fc07f0000070007fe000ffe001fff000,0xe03060c183060c180006520004d2001f76000),(0,0),(0x40001fff80000007fff800000fffffe000000,0x6cd9b366cd9b367ff5800000b2dfd6000000),(0x7ffe00000000007fffffffff000000000000,0x2070e1c3870e1c387abf9add5f000000000000)],colTree 0x1000a304410800560020640021e0028200318001190018c00888800d40000e4006a00405a0001e00d050002700622800438025140028c010c281146088014012d00208a0843c004050163002202c014608021403a801012a00178030150023c012030a10f00001a08a304000c22c6004007006b00003b8014e00842001ad00009000d7000038002bc0100 27 0 3,#[[],[16,82,131],[48,129,82],[128,49]],cutoff 11 levels431,leaves431,cycles431⟩
def jobs431_0 : List Ticket := [(6,0,1,0,0,0),(7,0,5,7,0,0),(7,5,2,8,0,0),(7,7,24,0,0,0),(8,0,19,8,1,0),(8,19,4,9,1,0),(8,23,93,0,0,0),(9,0,7,8,1,0),(9,7,9,9,1,0),(10,0,1,8,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j431_0 : reports chart431 jobs431_0 := by
  simp only [jobs431_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
theorem l15 : Lower (aug 15) (graphGoal 15) 4 := by
  apply aug_of (hints:=0x321002101)
  · exact low15
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l143 : Lower (aug 143) (graphGoal 143) 5 := by
  apply aug_of (hints:=0x321002101)
  · exact prior_ok 143
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l431 : Lower (aug 431) (graphGoal 431) 11 := by
  apply chartRoot (g:=chart431) (ob:=[(15,4),(39,4),(47,5),(135,4),(143,5),(163,4),(167,7),(175,8)]) (hints:=0x321002101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact l15
    · exact l39
    · exact l47
    · exact l135
    · exact l143
    · exact l163
    · exact l167
    · exact l175
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=jobs431_0) j431_0 (by decide +kernel)
    intro k hk
    change 11 ≤ k at hk
    change (cutoff 11 levels431 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
def w495k8 (i : Nat) : Nat := 0x17057c6300a7d091218fa0280b1f8048147792632f740ce652fe2c1d65be98425b9d04849faa20a78fe78d8acfca0295be94542a2fa5fad2cf4c2270eef750cb6d308897d160f12f382c634e6c58c4b75308797e160ef7e82850f8dc07614bda0b12c7b39625a7662c4ade480595fa0c2429f641845b6c6308b3d846116bb06c22df41d8457e881ccb7d0f39977a1c732ef404e65ee869ccbdd023997da1873221fcb18118de03408c7b0160557712632
def leaf495k8w (i : Nat) : Nat := 0x1280080100ba850c481042700e3400f571e80102801068010560105127058010580101806011276c227524270772604727087250a7250fd07535176d5165d3676d5165da7549a7541a7544a774ca774b9974b08658a743
def leaf495k8 (i : Nat) : Nat :=
  let row := packedAt leaf495k8w ((i-4)*20) 20
  (((row) &&& 255)) ||| (((0x10104c244822138900203110904e220088c120406010100c0110084020080c0222118040403 >>> (27*((row >>> 8) &&& 15))) &&& 134217727) <<< 8) ||| (((0xc2e27034583c1649208242a0d0236d148a6c351a0d46c341a8d268349a8d06632990c64220984c4602118c822c060a04a26120301609 >>> (27*((row >>> 12) &&& 15))) &&& 134217727) <<< 35) ||| (((0x82480910820908500c1200c120d04830110802834080c0101804030088c02210080c0000 >>> (18*((row >>> 16) &&& 15))) &&& 262143) <<< 62)
def leaf495xk8w (i : Nat) : Nat := 0x10914825d49448341013984c46017081d06030064a8502acd6122904ba9289068202730988c02e103a0c0600c950a0559ac24520965212a140b248a8160a09030988c01809328844a15a098482aa665629164d1d06c34120e13118031236590c944b09068258da450a812301368a45c03
def leaf495xk8 (i : Nat) : Nat :=
  let row := packedAt leaf495xk8w ((i-0)*39) 39
  (((row) &&& 255)) ||| (((0x4041309801028100044210020501000442124124822814884100900240a0d040101804402100401018044021 >>> (27*((row >>> 8) &&& 15))) &&& 134217727) <<< 8) ||| (((row >>> 12) &&& 134217727) <<< 35)
def cycle495k8w (i : Nat) : Nat := 0x2f26a060
def cycle495k8 (i : Nat) : List Nat :=
  if i < 39 then [] else
    let t := i-39
    let a := packedAt cycle495k8w (5*t) 5
    let z := packedAt cycle495k8w (5*(t+1)) 5
    (List.range (z-a)).map (fun u => leaf495xk8 (a+u))
def w495k9 (i : Nat) : Nat := (if i<1 then 0x2aef95295779694b9be24a55dec092f6d8859776a22cb1fe26898ff12a49fb95514fecaa0abed81235f6c071afb7498d7db44c79ee37e3cf653f1e7b15f8d7dca946becb4a3cf71251afb6848f75c6f47baca7a3dd62bd1f6b89e8f75a2f47bac17a3fd233d1afb9518d7d968c79ee2463cf71071afb7438d7dbc146eedc0a37b6d851bf36428dfcae146fe960a39fabc2dcfe5a16e3fc8fb71fcb7db9df23cdcef2de6f37c4f373bd31db9f723ade7b89d6f75c2eb71fe2687cdf13c3cef51e1e3fc4b8f3be15c78feabebcef55e5e7daaeaf3bd57833fd2a61dee8530e3faafa73ed57538feabe09df95806afc4c027f655019fb1a80d7d894067f469835fa24c15fb2a50e7d89287b6c4f43bb517a15fb2a30e7d8918776c28c2bf5e3e15faf050bbd70285eeb6142fd590a17f2c050bfc58287bcc4ec3be51761fd30bb0ef941d857eca8439f62421ddb0a10ef9810857ebc742bf5e0617f8b030afd78c857ebc042f75b0217f8b010dfc5a1467ec90235f647d1cfb1be8e7d29f457eca9233f64491cfb1248eed21246f6c8f23bb63791edb13c8eed45e46fcc8ea3be63751ef313a8ef945d47f4c2ea3fa487517db2988ded90c4776c6623bb4a311edb1188fe980c47f4846233fa480dafd23e6e7e8df373f14f9b9f857cd5fd2a46cfe912373f4491bbe8748dbdd23c6eee8de37770af1bdba278dddc8bc6fea1de37f60cf1b3fa40cdcfd1066dfa91d377d46e9bdea274ddf48ba6fea85d377d00e9afea530dbf52186efa8cc37bd4461bfaa130dfd41986dfc91c37be44e1bbf1170dfd90b86ff881c37fc1ae1bdf2214dbf8a0a6efc44537f64229aff1a14dff068a69fe2cd35fe4a59b7f242cddf91966f7c88b37f64259bfe202cd7f52946dfa90a37bd4451bfaa128c057fab8eb11bfd94e401ffe1c5980a3fd885e275eec8ef028ff95528147fcad100a3fe55480597f1b2202cdf8d810167bc6b08477e96544059fd1a62028ff2d288163fa878c4e3fdf0862557ee04312adf6c218957bb210c4abf96086051fe5a2b12a7f743581d7bb21ac0abed80d6071fef861038ff2d248157db02240b1fd4480051fef88002cfd45400167f229800aff168500777ae10803cfd2d24015eeb63204aff16190055faf02801bed6814015fe2c0a04fbb5131007fd2718802afe74930167f0af980b3f8568c059fc2bc603cfe1573015ef363984aff171cc2b5fce86614cfe14f3014ff3e1180abf9e08cc59fc284611bbe702308def3611846fd9908c237f4c04611bfc5c231177d146180fbe8530c29df48986139fe2cb311efe165984fbf112cc05fd8996603ff860b301ffc1a5980bfb0d2cc09df4894603bfa68a3017fc185196237db85eaf1fcb42e338f7956219e3bc4b108ebcd90e2278fc2be613cee15e322d7b3219952fb1a14d15fd06966 else (if i<2 then 0x25a2b04c4293669429c0a4ddac46317412c7c5accd0585ac0ab160b58d613856cb20c06c1ce334a1d735565c39e16b9781016723821264858e1b68112254e9c81381ce0485228153cb84ae01c4802ea01324af2e11c75008e4480270502a3812149c3b01564200ac498b62d613c02a159548506422c250003807161163584e4c2ac0871f8458147b220b0e0708b0e00361164883da20fc504a0e0e248310c1c2230193052902dbf037800bea84c2e2b848504fc06ca3481dd5050201a7c19ee903b24096283211f3d0806b141908e1b9b82a05cba370540b975aa0a490259008f3826a89a41c34940cf503c200de402cb00e850068b8902aa408040258c040e01dac27c9018ec057ef0584810a0b662b2a2a9c697293a89e86682e7f67be78674e6ea6b267a6425a65264a64263a636e2ee29a26220e1ba18214a1120da0a206a015fc1f89f09ed1eb5e7dde1d8dd55d1dce5cadc59c21ba1acda159dd9a57bd7596f569162d5c95014ad3f53592751d91a114d0f90c1050ffcfc4d7cb50a248f88147786dc5303580023fcb8279bedc2f8ff6a17c7fcab963fcb8251fe5a528ff621767f2d0bb3de25899eeeac4cf7616247fbd0b23fcb8191ff2b62cfb8d5167dbca8b3eca5459fb1a828ff2e08d7bb21c63fdd85b1fed42d8ff2de6c7f967b63fdf09b57ee04dadf6c26d7bb2136bed809b5fab84dafe5826c7fcad0e3fe55c71fef9e3afb6021d7eae10e3fde8573eecc2b8ff2e05c7fcadae3fdf0d71ff2b618ff7d10d7bb21873fa34c39fc8261cfe0130c7fbd0a66fdc8531fe5c098ff95b4c7fbe9263fdf1131ff2b608ff7d2066fc6c0337de6019be5300cdf458066f82c0377966013bedc2a9fe5a154ff2d0a27f9684f1fefa478ff7d13e7f1691bfa8d2cd5fec0efaff6867d7fb024b3fe25493fec42ccff920657fb04b33fc55595fef0ccbfe58664ffcaa8b3fe3545bf72aa2dfb5d5157fb4246bfdd0e33fe59f1bbf7028defb6146fdd90a37f6c051bfe5828e7fc8fb6bfdd1db5ff29edcff90f6d7fca78e7fda857beecc2bcff9205d7fb44ae7fcb7979fe2aebaff7875defb63aeff961d75ff2a2bcff9115cffcab873fe35c33feec29dbf7214e7fc9026bfdd2533fe5be9cff15a4cffcad273fe36939fe5349aff9524e7fc8927bbc84933fef9c9efb8ce4f7d94727bec53939feabe09ff95a067fc6d037f62501bfd1260f7b38c57f59c622ff582117fae8c8fed38c45dfb811ef7db08f7eec847bfb6023dff2c11fbf857cd7fcd106bfe747377f4419affa53cddfc51e6efe14f377f2279bbf9138ddfc01c6efe44c37fd4461bfe8930dff42186ffa3cc37fd1a69bff222cdff87966ffc34b37fd4451bfe8f28d4fed133a7f6099e7eaf0bf3f9685f8ff23efcef4c77e7da433ebbda1255dee932aef6099737c6fcb9bca7e5cde2bf else 0x586b108ca39202c8b4720920b4422128a4c2151d5c6971d5cd2159c3ab842c08815c0304cd2bcb849d7ba8049d7c48029d7ab8069d7b34b1c1084601923004c44985a))
def leaf495k9w (i : Nat) : Nat := 0x18d600e328020000100002ee88122880200004a420080001a28406358031ac018d300c698020000546502ee880c6e40634e031a6018d300c6980200001000008000040000380004a420196300c6b00200004a4200e0000400007b4e031a60080000400007194038ca02521013bac09a6005465025210199080948404a42025210166400b3200598b025210179ac03800054640080001228809144048a1024508179c00462404d2a02450809c4806372031a7018d300c6980634c068e10347081a3840d1c2068e10347081a3840d1c2031a602a318166280c2e8042ae030ba0185d00c2f0068e0034700134940c2e806174348001a4000a291c8c8a13645142d000e0001190000880004400029144148a20880005228822000148a20880007228439142e0441348000d14541914321000488000c4000620003450a1a2850c400068a1e310001a2850c400068a1431000188000d142868a14310001a2848c40006200031000182248c113868a1e3450f1a2878d22dc68a1c3450e74809a230ccd200069000088000440002200109000188000c400062000f9c0008e00047000d2000590004080004400062000148a21745085a284d20003100034800132288d91440c8a15a4509b2285791426c8a106450832284191420c8a104806824020120100900d06450832284191420c8b40628a03228018a1c0c50e062870240201201a09008048040240201201a0c8a1074500240341201a0c8a106450032280191420c8a15a450b52285691420c8a142450c4683819142cc8a18a450c5228418a1c3450e1a2870d143868a1c4510e8951482a8a59546902a3435512a8b7d9b5bec2e8e117470afa384dd1c26e8e15f4708ba3850d1c27094e1747085a3842d1c2168e10b4708985d03d1c02e8e1374708b85b8fc2dc7616e3b0b71d85b8fc2dc76174170b73185b8dc2dc6616e9614483a3801d1c00e8e0074700385cc1c2e6f68e07b6703da3802d1c0f68e07b0b9a7a2841d1c02e8e0574701ba3822d1c0761733b0ba0f85b8dc2dc1616e
def leaf495k9 (i : Nat) : Nat :=
  let row := packedAt leaf495k9w ((i-81)*21) 21
  (((0x9491878582818075747372717064636261605453514140322110 >>> (8*((row) &&& 31))) &&& 255)) ||| (((0x4104924446031028442a05024160a0080c124124824140b04822130900406110904c20804804080500260309048141a0902030110084020080c028241a04402100808060100406011008402020180401018040403 >>> (27*((row >>> 5) &&& 31))) &&& 134217727) <<< 8) ||| (((0xc56170589c2e071184c06171381a29948b4526916830380c9a1502920b0490a8340a0d0a8140e1502629948aa2130894083412144a05361a8d06a361a0cf45229968a4531184c04a361a0944c240984a24128984821160901a0b04830160a >>> (27*((row >>> 10) &&& 31))) &&& 134217727) <<< 35) ||| (((0x8248204068088504a040a80c04222d0082422010855081403049061209848251208448061200c442611084440610084130804834120c044200a250288408060110804260101c04060100c02250088c02210080c0000 >>> (18*((row >>> 15) &&& 63))) &&& 262143) <<< 62)
def leaf495xk9w (i : Nat) : Nat := 0x215230e25581dd7cb1cda108547c395461d65f7c73683c8a1089c92949801609f2c72264246e4a446001427cb1c58495d37d9052082000582228422724a526005827cb1cb9dc8548d905208201e8042262626dfa524805807cb089848b1069b38b4c200014226122c41a6ce2d308000508b9d585179b38b4c201e683228422724a446001427cb1c8a1089c92911800509f2c78548c389560775f2c732640388e60771f2e12262615de16391741a6492c208000514b9d585779904b38201e68385478388e60761f2c23262458c95d07d92520820001422e756145e6ce2d308079a0c58c95d07d92520820001422264226e4a526001427cd1c899089b92949800509f3472264246e4a446001427cb1c58c95d07d92520820001421632974296494820800050858c85d06d925208200014216321741a6492c20800050858ea5d069924b08200014660a6010c61009965410e239741a6494420a60050058c41e125741f64148e0802ad08899089b9291182960ad2c742e72a46394948208079a10b9d585779904b38201e68389b7e91173c09963c11ab3cba5c8548d905238201e6841ac3e73208c6a07c085d968ba5c8548d905238201e68416325741f649482080005085c095d07e525208202b5828518c389560775f2c73664058495d37d905208200058226122c41a6ce2d30800050a145e0e23981d8b8b08d9893662626dfa52480580b8b08d98989b7e911200502e2c21632574df1ab5a73228c832f5df0e25d81e8b581c8bcf1632574df1ab5a73228c83058c95d37d90520820001421632574df6414820800050909dca948e525208201e68416125741f6494820800160858495d07d92520820005828517d289474765f2c75663cba658517d979244201e6857cb1d598f8517d289474766151f4a251d1d97cb1cda0f52121c41b6414910800050a145a4a235d1d37cb095988a147d295461d65f7c732a3e151e0e23981d87cb08da0985478390e60761f2c222626145e0e23982987cd08898916325741f6494820800050858c95d37d905208200014285478388e68762e2c236826051798d9c8983
def leaf495xk9 (i : Nat) : Nat :=
  let row := packedAt leaf495xk9w ((i-0)*18) 18
  (((0x85848281807675747372686463625754535251484746454140383736353432302826252318171514120301 >>> (8*((row) &&& 63))) &&& 255)) ||| (((0x6020984c0223110522d1609028341049248108a45020542a0241a0c0413098010281000442180607020844a2408150a801028100044218044622411098453219488c0621060341204028040011085088540a0482c1241248241109848051288a05221120944223018841009008100a0100044209140a4120506822010804010180540a140a2412814120d022010804040300802030088042010100c020080c0220108040403 >>> (27*((row >>> 6) &&& 63))) &&& 134217727) <<< 8) ||| (((0xc42a11185c4e070988c06124904c1e17034532916830380d04c241920b049228540a450381488c4228541a050a2502a122904c241a098342a0503a0c05d06c34314ca455522d14a8160a14483412884c22428940a8351208d964321b1d068349a8d06562914ca663218a442231184c061311809b4522932884425428144a261205caa150b24824162a05029848244ca2110984a2412a140a25130901a0b0482c1a09 >>> (27*((row >>> 12) &&& 63))) &&& 134217727) <<< 35)
def cycle495k9w (i : Nat) : Nat := 0x2af52a6d22873e9ccd25f2a92c82371688c320f027ebe1e6ee74b91beda6ab4196c660af16eb256aa1469e4ca511e8a42a00f676389b0ce622e960a64e249107e3a1a8c05626108702e12068200600
def cycle495k9 (i : Nat) : List Nat :=
  if i < 365 then [] else
    let t := i-365
    let a := packedAt cycle495k9w (9*t) 9
    let z := packedAt cycle495k9w (9*(t+1)) 9
    (List.range (z-a)).map (fun u => leaf495xk9 (a+u))
def w495k10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xf6d97fdb15ff505bfd18dff85bbfd26eff45bbfe16eff7dbbfda6eff21bbfd76eff09b7fdb5dff6c3bfd10dff6d37fdb05ff691ffdf97ff7ddffe167ff6d9ffd267ff459ffd567ff519ffdf8fff7a3ffc28fff7dbffcf6fff857ffdb5fff497ffd75fff457ffd05fff517ffde0fff853ffdb4fff693ffc84fff493ffd14fff413ffce4fff513ffdf07ff795ffcf57ff395ffdf47ff3d1ffcc47ff7cfffde3fff08fffce3fff30fdfc79f7f1a7dfdf7f7f7e5fbdf97ef225fbd297ef1a5dfdf77ef79ddfdf67ef799dfdf8fef7a3fedf8ffb223fed28ffb7a3fec78ffb463fecf8ffb0a3dfdf6fef79bfedd6f7f7d7fbde5ffb757fbde0f7f7d3fbde4ffb753dfdf07fd7e1ff5e87fd3e1ff4287fd761ff4e87fd061ff4c87fd021dfdf57ef795fedd577f7d1fbde47fb751dfdf3fef78ffedd388bff8cc0a7ff3e215ffef2c89ffc75857ff9eb12fff7d225ffe7a44bffcc5057ff9c80a7ff3ce17dff04ccbbfc779137f8cf13eff82437dfe9484bbfc491177fbe4355ff85837dff0300dbfdb60cf7f92c136ff49875dff009317fd5109f7fc111beff4a226dfe2448bbfc388977fbcd11eff1da4adfe7b44dbfdf189b7fbc3236ff3c683dfe10cf77fe159237fc0b02eff6d634dfe4ac4bbfd2592f7fa2b2beff0d616dfe82c4bbfe0091effae11a6ff0c204bfea05177fe149a37fc0902eff6d254dfe4a4977fda4a377fa4913eff11216dfe824d1fece49177fc0023dff68055dfe90047bfc4000effa80125ff85403dfe9282dbfd1505b7fa0a0a77f39414bff0a02bbfd2400f7fa280aeff41024fde6200bff4d4057fec2812ffd7d004ffad204bff484013fea4801ffd45015ffa7a049ff5d4053feaa8227fd19004ffa82095ff4e40d3fe82812ffd31024bff09c0d7fda389b7fa470adff5ce15dfe89c07bfd03853fe96701ffe84c76ffcf9847ff9a3097ff10601ffe48c35ffcf1849ff973117ff0e6027fe44c8affc79909ff8230d3ff1c61affe30c03ffca184bff8d310fff16602ffe28c56cff04cc79fc99b6e7fc2f4367f7de569feb94cd3fd5291b77c1221eef26498edefc911bbd290977789221fed1649c9ff0b88d9fdf21da7fb44334ff548549fed89096fd91212efb02425f758484bf6a88c77f541212ff26223efb82242df64c511dedf89e37da5112efb12288fd6f44cfbed188db7d871574ff85a67cfefb4cfbbde699b7dbad1a67f7c6549fed0c69bbde19127fae334cff6d6559fed84eb7f9309aa7fb692bcff6c094bbec00ad7f54015aff2602af7d7e076dfa940cbfb5e819b7ea3022ff976067dfa8410f7f6141937ec083c77d7d098dfa920c9fb5e41a3fcba8647ed310a6bfd098cbbfa032137f1266b77e7ccfadfc9198ffb9e31db7f06642ffa74d48ff4618c9ff1c31d3fe0a68d7fc2cc96ff4519473dd6218a7f126 else 0x182668413d6608bed04fe5d19f05fcc1b0012b4209e0004e018160d8122f008acf944165a04a1d8276740afa00900004e090222441379705f0d9f35bd18202f62049a18266881314a0112b04d6c023fdc12e34029cae4466d19e2c1fb04b2d0251740ad2008e62049e002572e60c5e4011ce2092d00486c023f6411a6c091cb82f86cf9ade8380464804aecc11624088150068d021bdc050900871a014be0001e0115d4089be1b368cf960cadf03ac981cd940ff860852b029be81b3540ce5807cf202cb602133e6cb7c9068e035e18214f40f6060587d041d981cb3e5102cb528055c004b00027db011d0047d9c24aa807a94040a124585eb81e6040093a0579903a2681c6440c2fa08394040f28148dc0d51e0666c04207020b081cf9b2dfde006180052200caca07f2b08f4e84777c0f14a011740b70f81faa0101b011b550383501f6640bf44406179f2accd8618601dd04007ae079e003b0681bf7c0f0a205e3d03daa01ea940a29e0642c03e6110073e6cb7f7c0ead81221708e4c81d33c0dd56002fc010210395f972d6c063930398681bf4c0aa9a071cf0372a81c2cc0e5709660c2cc00294405c8e035800059200174a015890342e81b57422c8e16da00313e81b130230861175d08c85046bdc0d37a00e370353e0000466be1b2e7871ad80c710065a00316a819d3c0c91e066259f296a202e3b8175b40c06c0015102f488186640bf9f29625521147008a8d8139740ac7c05a9d02ba4004958227a6055a50088181605401b6c010c4007de803bc80b2f8000b648401ce1b3658f07780189000bfb02a15814fc422370112a5028b5802b940a4ff3e58f18b6780155030de81a7650d475801dec3524c03a770cf54001aac00428b968d00faa00990400702004f300e488090b0bbcc978ceefddd8bbaa7741ae5cdc6cb869700eddedb1cb5596946cf0d994b23b6166bf4d7bfaed75c5eb30d56caa235286a26d3d6a7134d2a958525ca411462a866cfed9ec33cfa771ce969beb356e68e4ccf98952fbe5e9cade945128164c048df8fb91e063a1468c8c2b164228244c5896111aa22ac41687af0e9a1bac33d86510bc21554287849f080a0f3419982fb05a209840ea81730126016bf937e70fbadf52be7b7c4ef7bdedbbda27ae2f571e4fbc607826eff9dce3b5675beeb0dceab911716ce151c1fb7f26f12dd99b69b64069c4d0419beb2d564aec7b987cb0195f98bd8d7292dd45a2eb1bd5f52b2654c4a67946d28474f069bf934e25bc49e292911e22315455885e1064a01a3ee47c5cf491e373b8e7428e3f1bc8360869a8cc898fe30d65f7cb9116812bb25588a5993da268049d48c010e620603bf07000d5f19362d804ef88b20fea1ca82a704b4080a09680b9808c00017fe17eff85fbfd77eff55f7fe176ff49dbfe176ff55dbfc675f) else (if i<3 then 0x862903c3006d19f08cf708483057aa035cda0efd80be90179c34819400f98a01b7b812de82d5b017d39080292f9d28618741063d03db00ae1c01dd9f2d10d56bf2841120210360ed5b083e52f5f5c0f3ca1048406b6e83fc281d61a0d03a0832602eb2c20b44404d19f2e4cdb8101df03c32840f941fc240eaad0812a02e53819620268cf966d5cc721006707488099e8d7dd07ff001d84c1d1ca0feca5ebae8eac24170861aaa20d58f052180570c2008a0173eb039f00809a2fe72c2f36595046c1f932074cc07254001ad86099726320071820627202bbf20fdfc0105200edc4094605e5405cb0206246c1f800039f3024a883e3f42d2a02653e5cb3e838ab83337e0b4100d22c807459d2e31301c29e0407c0244702cfd02b65001bd50cc4604a972d2e33842b42a01ac20cbbc84a5201c09603f78023c502c90ab2e335832d1a1285c06faf80fa3008d3c0b1040ac9c006572d2e32ac08a2e1a3290580683ecbc2c1f815f6f0d09b868972d2e32a81f570017650ca75837bb831c361a03a5c60d855cc403df8193b30934103761407b64044c4057ae365c63803b8d8123600f5ef06a67cb52886175fbc1ed0a0ec7007be283cc5d7b30571903d0281d7a0090cc072068396c01eb8a0f3a22c267cb87466bb056a583c4481d5b008f520782f0b1b6c1e550267cb3740bccda0ef670748b099e8d70a0758d83b44c1d0240ea700774283b208158ce0e9a82c467cb8746676055e68adcf41cc1a0e55e1636b039f406cf9a965179e00520071e6039278b0d96c57170ce218674f81b6440aac106e62854e302acf20d8b906d778352f921c203681e145e6cb9e1bf1906cc2035be81a7720da7e0631e02a7406cf9b26519080d6d506bdd0349e41b1f80a84e065e80d9f317cb8a9418ac60a7b50655d034be81a7de0d4d180366bc2e040081a0d0c10670609871b7064b5419e801904e0210a83444222c2d040061a0d0d5067880d871c083350032168191c1067044e585bf8332d41945418af70533905f93819674be7ca333688d147414b28187740649d00b21c3102342d0a2e80307c2184840c2cb0293b418f6602abc0641204b428ba5062f3828de82fee417e3e15abf031b40e0b9f283cd2a1c69a0be170313cc2f74c0a21009a2e1c17308862f382f5c00a1c50bb1605e4d018696175770613985e1fc2ef2444316841316f05fcb0305dc067aa0c05c3b308862d6417cd60a0d50980102f428064b8ee6110c5d982b90016e980ba8f0331e02a6882cf971c282ee200cb220b50e05e5d82b7dc14ca80b9a8533e5aa5bec12c980ba4f0327e02a208158a80b9a80b3e5c6800b79105a8482e1d8157ce0a30f05b51119f2d52d660aebb056bb02ae0815954167cb8d8c14e440aae7051fb829bf0150780a9a944967cb40b7d8258ec13a7c05a710492 else (if i<4 then 0xbe7ea20f8cf0373b867b202ba630922f087c3367c2b5a2a858a876c155c306ab866ff142a61a19a720bf08055088e4b9f3654ccdfbc540130a83454270c11ec981066c880914a211845c48d00fa0064138085321522240b0bc38fa831e9e0405f01f7980738c0829603f8501ef7063823d89a0147430c6b9853c682a08818ca2027c78544704cf9516642d85bb2ce614f7109ea8862c6026e8b3d97195e96af94c8c6d16cc26c3614c950a7657b4ddce8476602e09060617174028e4003c1e0a43905f9711b29f3e64b1f2c176081891708e0000e4980754803b2e3c5589e1a2cc05c112116582c6840c2ec851708608c5fdc00ae5030fb2145cc0a30d3074d060a2e80306a81867401c3c24aa10402fe0a9850ce01192e181fb09d2e81b5642855e182610a2671c132b9439978b8c5a380d6b21424e0c03884f46026ef008acb76d51cea0b57ce2ebb98df21410000b7184fe2826bd4089cf96bc07109eb905f9182784e13ec238e0dcce7283cf14b1800506c273f613a2601bb905fb60236340295e09dda11364b9cac0fe68ea33c18a01b6c05f4a8f101ab0c951016fba2e916111acc26d8412e05097fb80a06026f14135422026672d33e55905f6705e964265aa0c070203317fe617b590991400d68426660886ccc440bf30bd9400d5dc066140327f0bbcd702d841c50bb0f80d023e7e21741060b9f805d2f949304b49826436f2e5898a0906602e084b58161208284bf286bf07a42e57c42e826436f14584478219741880b786a2223c1c20972385b7386bf0740a2e5a0ab00c4402d0b60b80456881314aa942d2b4502d05f0061d412da25044a8628b968219741a908a66aa20b4ad302aa4021c9512f071001fa289783d612c1a0430b00b4cc05c4aa86821a897823604e90095d1013fdc0508835b99a33e6cb2a1dc00ace80596602aa24a54156089de803b30a2c5e57d81532c2e37c93f83a0017be1e0ef0032602e151c16082e0a4002f404be260c405be8ba142e0867eddac0141ae97820494354013380455b0244ce125b80890f81f8282359e4862efeb368181c004a185c34c08c7f049339216fe08b2d0d740adee06991012510c205c3db011db0042886170e0024712068b9011538085f97241a1d10c2e1c6807ea42285611ea008ff884450c22ec6121210905f3a70317cf9b2a37e2a01a3100f5c005fcc039860182800d9c00656403b44e17863604e1708e4e84744161719582262a00dd808dd110585c67e2e1ae845bb00b76c40b2d05200168e16d6b0056d804d68682fce061704e820c0009c7d041d28432c01eb9f2d40d56b9903d1e4221961059104daa043c381059c25709026be06bc38178ca103370876886c1d021a5609aa5086540203a8012bc13bdb07914117f3652c2f4678b0614176fe0ccdc080d102607c0fc502c5a5 else 0x7b0b1b18590e98ac0ae617f7cec3053570ba68854a0525e4294a2050020a5a9141111204e2fd310108c48500282356a98b92e50c22e48138bf4cb8434ba11605097e89d8e49dc209768996d71df1088e810fc75786c69a942ab084938202f1b09cf105b04c099ee0977d085e670c24c3c20b5e50429d02dcd407dcd564c1aa0d6e002569c910fc34887ee1ac62049f40a8e68608a308a87ee1097a0b53c0821d446c0913d86a7e41fbfa1695418a30931e1a663090a705a0402a932152c60b391cf94ee608e1abc2cb41a57109ee3059f3e5ab85516af54e9b0ad590385988424012165a72de190dbcac23d542e12e1a28b868df00911804678023d90112fc2c2361a0ba18248874c162ea0c7d70664c403d1e158c300c5f8585c032a4e1275c394065a70b8cc30cfd981ca9c916e03317f6a0ca2e021aa81c26a80ce020b83400f9060af3b3c105)))
def leaf495k10w (i : Nat) : Nat := 0x60106010601060106010601069106010277074802770621062102770277027709a902870277027703150748074809a905ba08680748074809a907480601060106010277060106010748027707480277027707485601527766015601260126012601274656012601a601c601527720df343b31cc343b343b343b343b343b343b56212621345d927720dfd2742313574e47468745560116001600160016001274127413121745160076012601343d5601b601343d527720df3274
def leaf495k10 (i : Nat) : Nat :=
  let row := packedAt leaf495k10w ((i-185)*16) 16
  (((0x95939285827574736463625352513221 >>> (8*((row) &&& 15))) &&& 255)) ||| (((0x100205020008842040280248249048281608904a210201400980c24120506822010804010180504834088042010100c >>> (27*((row >>> 4) &&& 15))) &&& 134217727) <<< 8) ||| (((0x28a6522d149a45920b0490a8340a144a0541a1502510984485128144ca2110950a05 >>> (27*((row >>> 8) &&& 15))) &&& 134217727) <<< 35) ||| (((0x8101a0221412805108124804406054201308044200a210101802210080c0000 >>> (18*((row >>> 12) &&& 15))) &&& 262143) <<< 62)
def leaf495xk10w (i : Nat) : Nat := 0xd5d93de4738637a2eaec9ef239c31bd1757651791ce18de8babb27bc9670e6f45d5d945e473863492eaeca2f239c31bd14dc90aaa03084018270485550184200c159c6aee80c210b696a6ca2f239c31a5175764f791ce18da4babb27bc8e70c6d2559c6aee80c210b696a6c9ef259c39a4975764f792ce1cde8a70485551184200c1382422a88c2100109c121154461080084e0908aa230840042704845511842002138242aa88c2100109c1211544610800875764f792ce1cd28ba9b27bc8e70c6f2537242aa80c210060eaeca2f259c39a4975364f791ce18d24be9be8bc8e70c6955
def leaf495xk10 (i : Nat) : Nat :=
  let row := packedAt leaf495xk10w ((i-0)*13) 13
  (((0x746462574640372623151201 >>> (8*((row) &&& 15))) &&& 255)) ||| (((0x2040a854041309801028100044210422512040a8540081408002210c0223109044261140a44224128841009008100a0048141a08020300a81428144825022010804010180401018044021 >>> (27*((row >>> 4) &&& 31))) &&& 134217727) <<< 8) ||| (((0xc52a91524c2412122904c1a150281d0602a241a094426112144a0526d148a4ca2110950a050b24824132884425428144a261202c1a09 >>> (27*((row >>> 9) &&& 15))) &&& 134217727) <<< 35)
def cycle495k10w (i : Nat) : Nat := 0x8c87827d78736e69645f5a55504b46413c37322d28231e19140f0a0500
def cycle495k10 (i : Nat) : List Nat :=
  if i < 278 then [] else
    let t := i-278
    let a := packedAt cycle495k10w (8*t) 8
    let z := packedAt cycle495k10w (8*(t+1)) 8
    (List.range (z-a)).map (fun u => leaf495xk10 (a+u))
def w495k11 (i : Nat) : Nat := (if i<1 then 0x63e606774813c8259f37b63686407b8600720403ca607c91065cc81f91c03e1807ff704004830b3c22fdc07d8800ebdb73a3441e8260c0d90389a01ed4c182ac04dfe03b8181e030163120bf5b03d0b01e6600c3c61166307b3703d6a7ca08dc5963e0767e05f408133640e25c07337078da02f3dc0bf0c0754103a7b01cb8c22c3405c990793003cc2c1609a0bd2650dc5a8b3502e9f03b2ec1731a0604802f7b83bbbc005ee05faa0314a83be600c3400af670780903b5501743405c9405dcb812ce4cc558b2161401484025438034f411174033f60511f8237dc101280ab9f0533302b844128a6044620501c88c597c222d57013bf02fa10094ac0d569071cb006e441962a0492e0747f83abb4085f80df51075d9804cc0017ba02a9405dd780f79819cc6031066f6c2764c04729005190882a425f1a060af0245e02b77c108b8030260984301d56c0f53c01a9903f4c008c3c25c6c0aa41051d98247d40820809f190565d8048e141ad7ce12760404a04f418114d01076202f500237701f62c153822c4c180dc0e55600c9d8102ec1c9800e76b068dd039af01bdda042f0004ff010e74052a80baf601f9180bbd40824c0255302254033c941a80ce2f666d94253c222d32110320ca9200bd5403e9a13c8b80b770256820749c08cc40082e82542c0790f194ac8063f04bd863256e048580862fc24a826597c597ac02c5b045d900040c0786803b8205416823df813b5e03db20040ecc5cf036758058b803017016e3035ad0179740332f06e6780ca2417fc80db9f06c66005ec405ec80da6f06b9b03748c05dd2010630188337c591b3502ea8047a1c10408028e2090a004730c0565c073a708e8181e2200408c0166304ddb847f7813930023e904d5804816c11d3a029dd0151c99be2cb42b809f2c0483e026c904b33826268000e40973904c9300950ba20643483285018aac019650634b006e6400a8c0164f061e6005e78034b201808063a88310241854c0c9c596140145f0326e01987001e6806c500377781ad500cf2c06dbf0354301bcc40cae60119b0384101a55002b66013b6001b981a1b00c7d2010bb0090cf7cdb0b290056181526c00926051810264380356409d3c00cef0012b0136c40ae820066c029cc8015d801c8a0583102b1e01480c0b55c050f0004cd0002d80066000b8902d8f81665c09764008e9027b3001e280ab7c590bb71ec8eaab695f9a4a5048d361ff7c0ddee6b2199e608569453b53a94734fbd3c18d2a2d24a6322706bb17d04950a900005dfff9dcd8ffd87563ff910e8ffd84827ff5d124ffc744e3ff888e8ffd828abff5c8c5ffc7292bff508d5ffc42427ff5c518ffd414a7ff484e6bfe8855f7f9dd79bfd8720eff21d57fbe44562ff610a4bfc8451ffb88958bfd8224aff20903ff61159ffd505f5ff920 else 0x4c0473c08a348329901ee0211553060d703a7001cf9e10d860379c83840c0b5560d2b00903383c208151720b33606ee18c94e4132c00f3660571c0428e8366b84dd0444b020cdc0e5340365703a6c40af741285e0919b84c59c1f9c80db7109610046ced4131682ca41c402115ac05b7e8433e41c05c0e83102b6f0271cc0232a0ef6406d1b02a99c131280abe9080d303358c1ed602184d05ed303262c152879177b4d8ea1103c08a738410a41c5de06b69071dd04a1b00a632122320969103ee7c1b0e212c1008c3c8d462d058b843ee8223ac10e321103a844288190d40a7280525d04a2dc169f20e034052b6044c2016f7e06a390709e014af022448085e904d71845a8015fe40b26f06ba0828ff04bce4097990794f8299c42139c0b86e07aa0dace2d76264c0a28011cf70776500d8bc0738c0d6990931f80dd8007592096f605174049c2018e560386501a3902873806adc10b7b989040145d82e434198ca0c64a04f7e8432301a6100b7cf086de037a080d3f80dfe10683f02741013f7e1256e085b3001d8814072472bbc91b80665606aac81383c1f5180d35e0918c84892c248201182008db88424e0215c61032506a44e4c5a085e883d22420a58106bc040f384105018b0a107ac05b7f01dc9812b6e0b46b0688302d4c40cb30061ab0694c008eb80a13410824042ad8238481da5a08f6407cf0834080237660916e0480582c044129c61030c08106024eec1247018b9c5edb47402297c0c97c0225b0459b8086702328c11a3f046c6023144189d2101a8067c5b92a2f01030e0821c007cb83e0f81d8500870d0665604037c1093427937078a08018f41115e0860f07d7b817ec01ff100200c0448602c7101fcce0fc2207dfb01c93c186680831008c120217c8164180fdb9059b203e69819ad8)
def w495k12 (i : Nat) : Nat := 0xc15bd009b82ce801ce049e06dc81bc022da053f057d01dc007521697074e833c824de146c07e386a08315e029404d50411c32a417190de204c18100602040037cbff
def levels495 : Nat → Level
  | 8 => ⟨44,4,5,2,0,0,18,[(4,0),(4,10),(5,24),(5,41)],0xaeeaaa66889ddba6ddb56cdb26c5b065d872e0a9262aaa6677695a468da2685a0508a92a0a426094248849de448899364987611745c942504912107491222845875c9425052021074,12,none,w495k8⟩
  | 9 => ⟨434,81,12,4,4,6,17,[(5,0),(6,20),(6,54)],0xaaa99a2277912226a5a869da6695a468da2685a0661976519261d845d172509412a4a829ca4288a1260972509221c84a66889de4488a116619765995651936499164187611825d1725c54250521260972509224487210741c8429de4488a1161d84609745c971509414852021c84208741c842,7,(some 0xe07c0b80f00c070720dc0860686d0711c2361883085f0bc1742e05b0b41642c0570ac1542a0530a21402784b0921202084007c0f41d03906e0d81a8340640c4180290500901182103e0700d81902e0580981201c0340500800e01802003),w495k9⟩
  | 10 => ⟨306,185,15,4,5,9,11,[(5,0),(6,20)],0xa66889de4488a116619765995651936499164187611825d1725c54250521260972509224487210741c8429de4488a1161d84609745c971509414852021c84208741c842,7,(some 0x303c0b01c021c86e0f83a0a8220781a0480e028011c46d0f4390a421074190540d024050018c6217c5e1745c16c5a1645815c56154521445013c4e124471184410c42104400f83c0ec3a0e4370d8340c8300bc2e0b42c0a8290a0270982508c210801f0781d0701b068190601705814048110400f0380d0300a0240801c060140400c01),w495k10⟩
  | 11 => ⟨28,28,14,4,6,9,10,[],0,5,(some 0x8dc22070280c00be5d2c95caa471d0e4461c0d8441e0e050200e06018080200),w495k11⟩
  | 12 => ⟨1,1,0,3,5,5,0,[],0,8,none,w495k12⟩
  | _ => emptyLevel
def leaves495 : Nat → Nat → Nat
  | 8 => leaf495k8
  | 9 => leaf495k9
  | 10 => leaf495k10
  | _ => fun _ => 0
def cycles495 : Nat → Nat → List Nat
  | 8 => cycle495k8
  | 9 => cycle495k9
  | 10 => cycle495k10
  | _ => fun _ => []
def chart495 : Chart := ⟨495,13,8,7,sampleColumns 283 #[(0x14681013e7c0000000000000ff80001ff988c662c6109193894c84116cc36792839f673,0x648888972a9c4e271389c4e271389c4e2988c622c6109191894c84112c4123928089631),(0xe8f09ac07c00000000001ff00003ffff21308600843061f0070f86270cc981ff26487f,0x2064620452231188c46231188c46231121308400843060600103862508408043224846),(0x683fa5b2180000000003fe00007fffe000000f88f01c181c118f00839f30e1e31c78f9c,0x681011802088c46231188c46231188c460000288f01c1818100500800510e0a30458298),(0x10300c001800000ff8000000007fc0000c03f01300601fe0e1f01f03e03f01fc1f80fe0,0x10220c0018072391c8e472391c8e47239c015013006002a0e1f01f03e02f015c1b80d60),(0,0),(0x23c05643e0001ff007fc0000ff800000001c001c007fe000fe001ffc003ffe001fff000,0x45508d101a0d068341a0d068341a0d000001c00652000320009a4003edc001f76000),(0x4080080c003fe000000001ff000000000fe0001fff800000ffffe000003fffffe000000,0x4080080c8005c2e170b85c2e170b85c2eca0001f52800000ffefc000003bf7fbc000000),(0x300a8100000000007fffe00000000000fffffe000000000ffffffffffc000000000000,0x300a81000361b0d86c361b0d86c361b0ffffd6000000000cdfaf65bfac000000000000),(0x7c00c2e0003ffffff8000000000000000fffffffffffffff00000000000000000000000,0x2310a29106381c0e070381c0e070381c035eafe0ad1add5f00000000000000000000000)],colTree 0x20009c00d090004e10604800528029440028c1144200158408190014c0028c800a600544400584088a20010f003410018c0018c800c6004c44006a00047200350022290014a40094800f00001e4002b00103200318003150000f00782800318031940021c0168a0014600a614024e10600a00570028250033801212801c608821400ad20408a8027082025004b400c2280a98015014056102220a00b60010650458408822c009c204094108780180a02c6004c051021e00482c014608221403a801110a20c60048452021e002828029680121401cc0008ca00e600444500790000b29035002029600ac2000ca00e60004550013c01a0a800ce00c45400e300432a00a38015150052c00a432049c20801a024e10200c0ab0811006115300280301750022018458c00900c4843c0040601730022031810f000419056102020c20a5a000868038c100431075002021a00ad20008c88b081004610730020236009c20009889a801006c00678024070053800a138035800219c006f00600e0077002027005b400823803d400029cd08780000e24a5a00007c093840003c11c608001d156102000e45d4008007117300200b8014e00a45c016300232e00e3800508005b8008140035a00212001ce00085000f3000128007b00003c0015e00a06000e700423000b3801109007b400025803dc0000ec016f00203600d780081b0079c0008 100 0 5,#[[],[81,130,118],[48,33,133,118],[48,129,82],[96,115,133],[96,129,82,115,33,48],[112,33,99],[112,81,130,99,33,48]],cutoff 13 levels495,leaves495,cycles495⟩
def jobs495_0 : List Ticket := [(8,0,4,8,0,0),(8,4,40,0,0,0),(9,0,10,8,0,0),(9,10,68,9,0,1),(9,78,3,10,0,0),(9,81,96,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j495_0 : reports chart495 jobs495_0 := by
  simp only [jobs495_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs495_1 : List Ticket := [(9,177,96,0,0,0),(9,273,96,0,0,0),(9,369,65,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j495_1 : reports chart495 jobs495_1 := by
  simp only [jobs495_1,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs495_2 : List Ticket := [(10,0,2,8,1,0),(10,2,73,9,1,2),(10,75,88,10,1,2),(10,163,12,10,1,0),(10,175,10,11,1,0),(10,185,96,0,0,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j495_2 : reports chart495 jobs495_2 := by
  simp only [jobs495_2,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
def jobs495_3 : List Ticket := [(10,281,25,0,0,0),(11,0,13,9,1,1),(11,13,15,10,1,1),(12,0,1,9,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j495_3 : reports chart495 jobs495_3 := by
  simp only [jobs495_3,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
theorem l79 : Lower (aug 79) (graphGoal 79) 5 := by
  apply aug_of (hints:=0x321002101)
  · exact prior_ok 79
  · exact proper_of _ (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact cheap (by decide +kernel) (by decide +kernel)
theorem l495 : Lower (aug 495) (graphGoal 495) 13 := by
  apply chartRoot (g:=chart495) (ob:=[(15,4),(79,5),(99,4),(103,5),(135,4),(163,4),(167,7),(175,8),(207,6),(227,5),(231,8),(327,5),(331,5),(355,7),(359,8),(367,11),(431,11),(455,7),(487,11)]) (hints:=0x321002101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact l15
    · exact l79
    · exact l99
    · exact l103
    · exact l135
    · exact l163
    · exact l167
    · exact l175
    · exact l207
    · exact l227
    · exact l231
    · exact l327
    · exact l331
    · exact l355
    · exact l359
    · exact l367
    · exact l431
    · exact l455
    · exact l487
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=((jobs495_0++jobs495_1)++(jobs495_2++jobs495_3))) (reports_join (reports_join j495_0 j495_1) (reports_join j495_2 j495_3)) (by decide +kernel)
    intro k hk
    change 13 ≤ k at hk
    change (cutoff 13 levels495 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem l447 : Lower (aug 447) (graphGoal 447) 13 :=
  augRelabel (ps:=[100,131,82,16]) (by decide +kernel) l495
def w507k11 (i : Nat) : Nat := 0x3ff
def levels507 : Nat → Level
  | 11 => ⟨1,1,0,1,0,0,0,[],0,1,none,w507k11⟩
  | _ => emptyLevel
def leaves507 : Nat → Nat → Nat
  | _ => fun _ => 0
def cycles507 : Nat → Nat → List Nat
  | _ => fun _ => []
def chart507 : Chart := ⟨507,12,8,0,sampleColumns 244 #[(0x800000000003fe00ffffc4c11ccc098010e66490e402109fc2670e40ff27f,0x28140a05028140a0502804c104c4098010262490640210854023064009215),(0x7fc0000007fe10a530c4219629860033fcc6313cd9833fca4c4f,0xc4e271389c4e271389c4e10a530842196298400109cc63128488109ca4c4a),(0,0),(0x1ff0000001ff0000060063f10c01831f871c380f83e331e1c38f38f8c,0xd46a351a8d46a351a8d460001510c01800a8714380f81a311e143853868c),(0x80000000000001ffff80380c7c02701e03e0181fc0f003fc3e01fc0fc0ff0,0xd2a954aa552a954aa552b80c7802701e03c0180b80f002582e00b80ac0960),(0x3fe00ff803fe000000000f8003801ffc001fe000fffc003ffe000fff000,0x3c1e0f0783c1e0f0783c0000003800ba40009200054a4003fdc000ff6000),(0x7fc0000007fc000000003ff00003ffe000001fffff0000003ffffff000000,0x1b0d86c361b0d86c361b0e5000039ca000001ffef60000003b77ef6000000),(0xff800000000003ffffffc000000001fffffffffffc000000000000,0x7c3e1f0f87c3e1f0f87c3ffffffc0000000016dfffab5bffc000000000000),(0x7ffffff00000000000003fffffffffffffffe000000000000000000000000,0x6030180c06030180c06031affeac63545bf56000000000000000000000000)],colTree 0x1b005ec0080 1 0 0,#[[],[65,99],[128,49,100],[128,97,67]],cutoff 12 levels507,leaves507,cycles507⟩
def jobs507_0 : List Ticket := [(11,0,1,9,2,0)]
set_option maxRecDepth 28000 in
set_option maxHeartbeats 0 in
theorem j507_0 : reports chart507 jobs507_0 := by
  simp only [jobs507_0,reports,pieces,rowParts,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
theorem l507 : Lower (aug 507) (graphGoal 507) 12 := by
  apply chartRoot (g:=chart507) (ob:=[(379,11)]) (hints:=0x351004101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    subst a
    exact l379
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=jobs507_0) j507_0 (by decide +kernel)
    intro k hk
    change 12 ≤ k at hk
    change (cutoff 12 levels507 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem l479 : Lower (aug 479) (graphGoal 479) 12 :=
  augRelabel (ps:=[100,131,82,16]) (by decide +kernel) l507
theorem l511 : Lower (aug 511) (graphGoal 511) 15 := by
  apply chartRoot (g:=chart511) (ob:=[(115,5),(127,9),(167,7),(175,8),(179,5),(207,6),(227,5),(231,8),(255,12),(319,11),(327,5),(331,5),(339,5),(347,8),(351,11),(355,7),(359,8),(367,11),(371,8),(375,9),(379,11),(383,13),(431,11),(447,13),(455,7),(479,12),(487,11),(495,13),(503,12),(507,12)]) (hints:=0x321002101) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact l115
    · exact l127
    · exact l167
    · exact l175
    · exact l179
    · exact l207
    · exact l227
    · exact l231
    · exact l255
    · exact l319
    · exact l327
    · exact l331
    · exact l339
    · exact l347
    · exact l351
    · exact l355
    · exact l359
    · exact l367
    · exact l371
    · exact l375
    · exact l379
    · exact l383
    · exact l431
    · exact l447
    · exact l455
    · exact l479
    · exact l487
    · exact l495
    · exact l503
    · exact l507
  · decide +kernel
  · decide +kernel
  · apply finished (xs:=(((jobs511_0++jobs511_1)++(jobs511_2++(jobs511_3++jobs511_4)))++((jobs511_5++jobs511_6)++(jobs511_7++(jobs511_8++jobs511_9))))) (reports_join (reports_join (reports_join j511_0 j511_1) (reports_join j511_2 (reports_join j511_3 j511_4))) (reports_join (reports_join j511_5 j511_6) (reports_join j511_7 (reports_join j511_8 j511_9)))) (by decide +kernel)
    intro k hk
    change 15 ≤ k at hk
    change (cutoff 15 levels511 k).count=0
    simp only [cutoff,ite_false,if_neg (Nat.not_lt.mpr hk),emptyLevel]
  all_goals decide +kernel
theorem fullResult : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1)) →
    PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  apply after_or (dead_start (before_sound known383 valid383) geomdead tablesdead)
  have p : proper (graphGoal 511) := by unfold proper; decide +kernel
  have h := forbid l511 p (by decide +kernel) (cap:=14) (by decide)
  have eq : aug 511 = inputs++[orSeed] := by decide +kernel
  have tg : graphGoal 511 = graph := by decide +kernel
  rw [eq,tg] at h
  exact h
end PEqualNP.Outside.L_meta_1673.Adjacent.Packed
theorem PEqualNP.Outside.L_meta_1673 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size :=
  PEqualNP.Outside.L_meta_1673.Adjacent.Packed.fullResult
