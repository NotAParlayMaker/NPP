import PEqualNP.Defs

-- The live-wire verification framework and the subgraph bounds are adapted
-- from L-meta-1667 and L-meta-1920, merged in pull requests 4332 and 5546.
-- Those contributions are distributed under the Apache 2.0 license.
-- The proof of L-meta-1920 credits PressF10 for the framework.
namespace PEqualNP.Outside.L_meta_3122
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
def seed4 : Sig := neg (inputs.getD 4 zero)

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed4_table : ∀ r : Row, bit r seed4 = !(sample r 4) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed4_nonzero : seed4 ≠ zero := by decide +kernel
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
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 4 then neg (inputs.getD 4 zero) else inputs.getD j zero) else zero
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

def supportPairs (baseRow mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,Fin.ofNat 512 baseRow,Fin.ofNat 512 (baseRow ^^^ (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  let base := if m.testBit 9 && m.testBit 4 then 16 else 0
  (selected m).map fun (i,a) =>
    let r := base ^^^ (1 <<< ((hints >>> (4*i)) &&& 15))
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< i)))

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
def colFree (m z o : Nat) := (m &&& 511) ^^^ ((m &&& 511) &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz := if m.testBit 9 && drop.testBit 4 then drop &&& (511 ^^^ 16) else drop
  let lo := if m.testBit 9 && drop.testBit 4 then 16 else 0
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows lz lo) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) _ hh.1 p bank hr ha)
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
  let x := fun j => if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if m.testBit 9 && j.val == 4 then ~~~(v 4) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : (m.testBit 9 && j.val == 4) = true
    · have hj4 : j.val = 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hf; exact hf.2
      simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i ⟨4, by decide⟩)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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

abbrev ExtraCut := Nat → List Sig → Bool
abbrev ChildLinks := (Nat → List (List Sig)) × ExtraCut

def closeChild (pools : List BoundPool) (links : ChildLinks) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links.1 (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op) || links.2 k ws

theorem closeChild_sound {raw T pools} {links : ChildLinks} {k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links.1 tag → Impossible T k (List.toFinset xs))
    (cutValid : ∀ ws : List Sig, ws.Nodup → links.2 k ws = true → Impossible T k ws.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with (⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩) | cutProof
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · exact cutValid _ nd cutProof

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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × ChildLinks
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
theorem evalMove_sound {raw T r s ws pools} {links : ChildLinks} {cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 tag → Impossible T (cap-1) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
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
  exact closeChild_sound pv lv cv nd' test k t hk h


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

theorem node_sound {raw T r s ws pools} {links : ChildLinks} {cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 tag → Impossible T (cap-1) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
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
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv cv pro fresh (all_unary checks ha keep)
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
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv cv
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
  cut : ExtraCut := fun _ _ => false
  cut_sound : ∀ k (ws : List Sig), ws.Nodup → cut k ws = true → Impossible (chartGoal mask) k ws.toFinset := by
    intros
    contradiction

def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
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
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls,g.cut) ws)

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
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (g.cut_sound _) (by simpa only [h0,if_false] using checked.2)
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
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true,Bool.true_or]
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
  (k,ws.length,ws,preCov ws,rules,ls,g.cut)


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
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]

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
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index,fun _ _ => false, by simp⟩
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
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index,fun _ _ => false, by simp⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index,fun _ _ => false, by simp⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index,fun _ _ => false, by simp⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index,fun _ _ => false, by simp⟩
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
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index,fun _ _ => false, by simp⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index,fun _ _ => false, by simp⟩
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
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index,fun _ _ => false, by simp⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index,fun _ _ => false, by simp⟩
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
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index,fun _ _ => false, by simp⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index,fun _ _ => false, by simp⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index,fun _ _ => false, by simp⟩
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
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index,fun _ _ => false, by simp⟩
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
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex,fun _ _ => false, by simp⟩
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

theorem dead_start : Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun




theorem low511 : Lower (vars 511) (graphGoal 511) 15 :=
  lower_forest (g:=dead) (i:=0) (hints:=13438755073)
    (before_sound known383 valid383) geomdead tablesdead (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def bounds511 (q : Nat) := if q = 511 then 15 else boundsBefore known383 q
theorem bounds511_sound (q : Nat) : Lower (vars q) (graphGoal q) (bounds511 q) := by
  unfold bounds511
  split
  next h => exact h ▸ low511
  next => exact before_sound known383 valid383 q


private lemma cutLiveSize {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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

private lemma cutBitBin (i : Row) (d : Bool) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]
private lemma cutBitNeg (i : Row) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
theorem inverted_pair {T k t S} (l : Live T k t S) {p n : Row}
    (pp : bit p T = true) (nn : bit n T = false)
    (h : ∀ w∈S, bit p w=true → bit n w=true) : t ≠ 0 := by
  intro eq
  obtain ⟨w,hw,wp,wn⟩ := mono_row_difference l eq pp nn
  exact Bool.noConfusion ((h w hw wp).symm.trans wn)

def Sensitive (T : Sig) (S : Finset Sig) (r : Row) (v : Sig) : Prop :=
  ∃ s, bit r T ≠ bit s T ∧ ∀ u ∈ S, u ≠ v → bit r u = bit s u

def Pivot (T : Sig) (S : Finset Sig) (r s : Row) (v : Sig) : Prop :=
  Sensitive T S r v ∧ Sensitive T S s v

private theorem sensitive_mem (l : Live T k t S) (h : Sensitive T S r v) : v∈S := by
  rcases h with ⟨s,d,h⟩
  obtain ⟨u,hu,hd⟩ := live_row_difference l d
  by_contra z
  exact hd (h _ hu (fun e => z (e ▸ hu)))

private theorem sensitive_unary (az : a∉U) (h : Sensitive T (insert a U) r v) :
    Sensitive T (insert (neg a) U) r (if v=a then neg a else v) := by
  rcases h with ⟨s,hd,hn⟩
  refine ⟨s,hd,?_⟩
  intro u hu ne
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a
    · simp [eq] at ne
    · rw [cutBitNeg,cutBitNeg,hn _ (by simp) (Ne.symm eq)]
  · apply hn _ (Finset.mem_insert_of_mem hu)
    intro e
    subst u
    by_cases eq : v=a
    · exact az (eq ▸ hu)
    · simp [eq] at ne

private theorem sensitive_binary (az : a∉U) (bz : b∉U)
    (h : Sensitive T (insert a (insert b U)) r v) :
    Sensitive T (insert (bin d a b) U) r (if v=a ∨ v=b then bin d a b else v) := by
  rcases h with ⟨s,hd,hn⟩
  refine ⟨s,hd,?_⟩
  intro u hu ne
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a ∨ v=b
    · simp [eq] at ne
    · rw [cutBitBin,cutBitBin,hn a (by simp) (fun e => eq (.inl e.symm)),
        hn b (by simp) (fun e => eq (.inr e.symm))]
  · apply hn _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    intro e
    subst u
    by_cases eq : v=a ∨ v=b
    · rcases eq with e|e
      · exact az (e ▸ hu)
      · exact bz (e ▸ hu)
    · simp [eq] at ne

private theorem sensitive_pass {g a b : Sig} {d : Bool} (az : a∉U) (ab : a≠b)
    (law : ∀ r, bit r g = (if d then bit r a || bit r b else bit r a && bit r b))
    (l : Live T k t (insert g U)) (h : Sensitive T (insert a (insert b U)) r a) :
    bit r b = !d ∧ bit r g = bit r a := by
  rcases h with ⟨s,hd,hn⟩
  obtain ⟨u,hu,uh⟩ := live_row_difference l hd
  rcases Finset.mem_insert.mp hu with rfl | hu
  · have eq := hn b (by simp) ab.symm
    rw [law,law] at uh
    rw [law,←eq] at *
    all_goals cases d <;> cases a' : bit r a <;> cases b' : bit r b <;>
      cases c' : bit s a <;> simp_all
  · exact (uh (hn _ (by simp [hu]) (fun e => az (e ▸ hu)))).elim

private theorem two_split {U : Finset Sig} {i j a b : Sig} {d : Bool}
    (az : a∉U) (bz : b∉U) (ab : a≠b) (hf : bin d a b ∉ insert a (insert b U)) (l : Live T k t (insert (bin d a b) U))
    (p : Pivot T (insert a (insert b U)) r s i)
    (q : Pivot T (insert a (insert b U)) r s j)
    (hi : bit r i ≠ bit s i) (hj : bit r j ≠ bit s j) (ne : i≠j) :
    ∃ i' j', Pivot T (insert (bin d a b) U) r s i' ∧ Pivot T (insert (bin d a b) U) r s j' ∧
      bit r i' ≠ bit s i' ∧ bit r j' ≠ bit s j' ∧ i'≠j' := by
  let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
  have lift {v} (pv : Pivot T (insert a (insert b U)) r s v) :
       Pivot T (insert (bin d a b) U) r s (f v) :=
    ⟨sensitive_binary az bz pv.1,sensitive_binary az bz pv.2⟩
  have passA {row} (pv : Sensitive T (insert a (insert b U)) row a) :=
    sensitive_pass az ab (d:=d) (fun i => cutBitBin i d a b) l pv
  have passB {row} (pv : Sensitive T (insert a (insert b U)) row b) :
      bit row a = !d ∧ bit row (bin d a b) = bit row b := by
    apply sensitive_pass bz ab.symm (d:=d) (fun i => ?_) l
    · simpa [Finset.insert_comm] using pv
    · rw [cutBitBin]; cases d <;> simp [Bool.and_comm,Bool.or_comm]
  have val {v} (pv : Pivot T (insert a (insert b U)) r s v) :
      bit r (f v)=bit r v ∧ bit s (f v)=bit s v := by
    by_cases eq : v=a ∨ v=b
    · simp only [f,ite_eq_left eq]
      rcases eq with rfl|rfl
      · exact ⟨(passA pv.1).2,(passA pv.2).2⟩
      · exact ⟨(passB pv.1).2,(passB pv.2).2⟩
    · simp [f,eq]
  have fresh {v} (pv : Pivot T (insert a (insert b U)) r s v) (h : ¬(v=a ∨ v=b))
      (fv : v=bin d a b) (hf : bin d a b ∉ insert a (insert b U)) : False := by
    subst v
    obtain ⟨row,hd,ex⟩ := pv.1
    obtain ⟨u,hu,uh⟩ := live_row_difference l hd
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rw [cutBitBin,cutBitBin,ex a (by simp) (fun e => h (.inl e.symm)),
        ex b (by simp) (fun e => h (.inr e.symm))] at uh
      exact uh rfl
    · exact uh (ex _ (by simp [hu]) (fun e => hf (e ▸ (by simp [hu]))))
  refine ⟨f i,f j,lift p,lift q,by rwa [(val p).1,(val p).2],by rwa [(val q).1,(val q).2],?_⟩
  by_cases ei : i=a ∨ i=b <;> by_cases ej : j=a ∨ j=b
  · rcases ei with rfl|rfl <;> rcases ej with rfl|rfl
    · contradiction
    · exact (hj ((passA p.1).1.trans (passA p.2).1.symm)).elim
    · exact (hj ((passB p.1).1.trans (passB p.2).1.symm)).elim
    · contradiction
  · simp only [f,ite_eq_left ei,ite_eq_right ej]
    intro e
    exact fresh q ej e.symm hf
  · simp only [f,ite_eq_right ei,ite_eq_left ej]
    intro e
    exact fresh p ei e hf
  · simpa [f,ei,ej] using ne

theorem tight_no_conflict {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t)
    {r s i j} (p : Pivot T S r s i) (q : Pivot T S r s j)
    (hi : bit r i ≠ bit s i) (hj : bit r j ≠ bit s j) (ne : i≠j) : False := by
  induction l generalizing i j with
  | stop hp =>
    have mem := sensitive_mem (Live.stop hp) p.1
    have mem' := sensitive_mem (Live.stop hp) q.1
    simp only [Finset.mem_singleton] at mem mem'
    exact ne (mem.trans mem'.symm)
  | @unary k t U a ha hf tail ih =>
    have hfU : neg a ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have az : a ∉ U := by
      intro hal
      rw [Finset.insert_eq_of_mem hal] at tight
      omega
    rw [Finset.card_insert_of_notMem az] at tight
    have next : k+1 ≤ (insert (neg a) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a then neg a else v
    have lift {v} (pv : Pivot T (insert a U) r s v) :
        Pivot T (insert (neg a) U) r s (f v) := ⟨sensitive_unary az pv.1,sensitive_unary az pv.2⟩
    have dv {v} (dd : bit r v ≠ bit s v) : bit r (f v) ≠ bit s (f v) := by
      by_cases e : v=a
      · subst v; simpa [f,cutBitNeg] using dd
      · simpa [f,e] using dd
    apply ih next (lift p) (lift q) (dv hi) (dv hj)
    have mi := sensitive_mem (.unary ha hf tail) p.1
    have mj := sensitive_mem (.unary ha hf tail) q.1
    by_cases ei : i=a <;> by_cases ej : j=a
    · exact (ne (ei.trans ej.symm)).elim
    · simp only [f,ite_eq_left ei,ite_eq_right ej]
      exact fun e => hf (e ▸ mj)
    · simp only [f,ite_eq_right ei,ite_eq_left ej]
      exact fun e => hf (e ▸ mi)
    · simpa [f,ei,ej] using ne
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have az : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    rw [Finset.card_insert_of_notMem az,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    obtain ⟨i',j',pi,pj,ii,jj,z⟩ := two_split (fun hm => az (by simp [hm])) bz ab hf tail p q hi hj ne
    exact ih next pi pj ii jj z

theorem tight_no_binate {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t)
    {r s i} (p : Pivot T S r s i) (hi : bit r i = bit s i) (goal : bit r T ≠ bit s T) : False := by
  induction l generalizing i with
  | stop hp =>
    have mi := sensitive_mem (Live.stop hp) p.1
    simp only [Finset.mem_singleton] at mi
    exact goal (mi ▸ hi)
  | @unary k t U a ha hf tail ih =>
    have hfU : neg a ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have az : a ∉ U := by
      intro hal
      rw [Finset.insert_eq_of_mem hal] at tight
      omega
    rw [Finset.card_insert_of_notMem az] at tight
    have next : k+1 ≤ (insert (neg a) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a then neg a else v
    have lift {v} (pv : Pivot T (insert a U) r s v) :
        Pivot T (insert (neg a) U) r s (f v) := ⟨sensitive_unary az pv.1,sensitive_unary az pv.2⟩
    have dv {v} (dd : bit r v = bit s v) : bit r (f v) = bit s (f v) := by
      by_cases e : v=a
      · subst v; simpa [f,cutBitNeg] using dd
      · simpa [f,e] using dd
    exact ih next (lift p) (dv hi)
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have az : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    rw [Finset.card_insert_of_notMem az,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    have nz : a∉U := fun h => az (Finset.mem_insert_of_mem h)
    let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
    have lift : Pivot T (insert (bin d a b) U) r s (f i) :=
      ⟨sensitive_binary nz bz p.1,sensitive_binary nz bz p.2⟩
    apply ih next lift
    by_cases eq : i=a ∨ i=b
    · simp only [f,ite_eq_left eq]
      rcases eq with e|e
      · subst i
        have pick {row} (pv : Sensitive T (insert a (insert b U)) row a) :=
          (sensitive_pass nz ab (d:=d) (fun j => cutBitBin j d a b) tail pv).2
        exact (pick p.1).trans (hi.trans (pick p.2).symm)
      · subst i
        have law (row : Row) : bit row (bin d a b) =
            (if d then bit row b || bit row a else bit row b && bit row a) := by
          rw [cutBitBin]; cases d <;> simp [Bool.and_comm,Bool.or_comm]
        have pick {row} (pv : Sensitive T (insert a (insert b U)) row b) :=
          (sensitive_pass bz ab.symm law tail (by simpa [Finset.insert_comm] using pv)).2
        exact (pick p.1).trans (hi.trans (pick p.2).symm)
    · simpa [f,eq] using hi



def DOnly (T : Sig) (S : Finset Sig) (v : Sig) (p n : Row) : Prop :=
  bit p T = true ∧ bit n T = false ∧ ∀ u∈S, u ≠ v → bit p u = true → bit n u = true

def DPivot (T : Sig) (S : Finset Sig) (p n : Row) (v : Sig) : Prop :=
  (∃ s, DOnly T S v p s) ∧ (∃ r, DOnly T S v r n)

private theorem donly_vals (l : Live T k t S) (ht : t=0) (h : DOnly T S v p n) :
    v∈S ∧ bit p v = true ∧ bit n v = false := by
  obtain ⟨u,hu,pp,nn⟩ := mono_row_difference l ht h.1 h.2.1
  have eq : u=v := by
    by_contra ne
    have z := h.2.2 _ hu ne pp
    simp_all
  exact eq ▸ ⟨hu,pp,nn⟩

private theorem donly_binary (az : a∉U) (bz : b∉U)
    (h : DOnly T (insert a (insert b U)) v p n) :
    DOnly T (insert (bin d a b) U) (if v=a ∨ v=b then bin d a b else v) p n := by
  refine ⟨h.1,h.2.1,?_⟩
  intro u hu ne pp
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a ∨ v=b
    · simp [eq] at ne
    · have a' := h.2.2 a (by simp) (fun e => eq (.inl e.symm))
      have b' := h.2.2 b (by simp) (fun e => eq (.inr e.symm))
      rw [cutBitBin] at pp ⊢
      cases d <;> simp_all [Bool.and_eq_true,Bool.or_eq_true] <;> tauto
  · apply h.2.2 _ (by simp [hu]) _ pp
    intro e
    subst u
    by_cases eq : v=a ∨ v=b
    · rcases eq with e|e
      · exact az (e ▸ hu)
      · exact bz (e ▸ hu)
    · simp [eq] at ne

private theorem incompatible {T : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (az : a ∉ U) (bz : b ∉ U) (ab : a ≠ b)
    (l : Live T k t (insert (bin d a b) U)) (lt : Live T (k+1) t (insert a (insert b U)))
    (ht : t=0) (pa : DPivot T (insert a (insert b U)) r s a)
    (pb : DPivot T (insert a (insert b U)) r s b) : False := by
  cases d with
  | true =>
    obtain ⟨s',h⟩ := pa.1
    obtain ⟨s₁,h₁⟩ := pb.1
    have bb := (donly_vals lt ht h₁).2.1
    have bz' := h.2.2 b (by simp) ab.symm bb
    have h' := donly_binary (d:=true) az bz h
    simp only [true_or,ite_true] at h'
    have g0 := (donly_vals l ht h').2.2
    simp [cutBitBin,bz'] at g0
  | false =>
    obtain ⟨r',h⟩ := pa.2
    obtain ⟨r₁,h₁⟩ := pb.2
    have bb := (donly_vals lt ht h₁).2.2
    have hmb := h.2.2 b (by simp) ab.symm
    have bz' : bit r' b = false := by
      cases e : bit r' b
      · rfl
      · have h' := hmb e
        simp_all
    have h' := donly_binary (d:=false) az bz h
    simp only [true_or,ite_true] at h'
    have g1 := (donly_vals l ht h').2.1
    simp [cutBitBin,bz'] at g1

theorem mono_tight_no_conflict {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t) (ht : t=0)
    {r s i j} (p : DPivot T S r s i) (q : DPivot T S r s j) (ne : i≠j) : False := by
  induction l generalizing i j with
  | stop hp =>
    obtain ⟨_,dp⟩ := p.1
    obtain ⟨_,dq⟩ := q.1
    have mp := (donly_vals (Live.stop hp) rfl dp).1
    have mq := (donly_vals (Live.stop hp) rfl dq).1
    simp only [Finset.mem_singleton] at mp mq
    exact ne (mp.trans mq.symm)
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have ax : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    have az : a∉U := fun h => ax (Finset.mem_insert_of_mem h)
    rw [Finset.card_insert_of_notMem ax,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
    have lift {v} (pv : DPivot T (insert a (insert b U)) r s v) :
        DPivot T (insert (bin d a b) U) r s (f v) := by
      obtain ⟨⟨aa,haa⟩,⟨bb,hbb⟩⟩ := pv
      exact ⟨⟨aa,donly_binary az bz haa⟩,⟨bb,donly_binary az bz hbb⟩⟩
    have before := Live.binary ha hb ab hf tail
    apply ih next ht (lift p) (lift q)
    by_cases ei : i=a ∨ i=b <;> by_cases ej : j=a ∨ j=b
    · rcases ei with rfl|rfl <;> rcases ej with rfl|rfl
      · contradiction
      · exact (incompatible az bz ab tail before ht p q).elim
      · exact (incompatible az bz ab tail before ht q p).elim
      · contradiction
    · simp only [f,ite_eq_left ei,ite_eq_right ej]
      obtain ⟨n,hn⟩ := q.1
      exact fun e => hf (e ▸ (donly_vals before ht hn).1)
    · simp only [f,ite_eq_right ei,ite_eq_left ej]
      obtain ⟨n,hn⟩ := p.1
      exact fun e => hf (e ▸ (donly_vals before ht hn).1)
    · simpa [f,ei,ej] using ne



structure Six3640 where
  p : Row
  n : Row
  ni : Row
  pi : Row
  nj : Row
  pj : Row

def invRows3640 : List (Row × Row) :=
 [(139,138), (101,100), (401,400), (170,138), (154,146), (325,261), (6,10), (180,52), (298,42), (98,104), (7,261), (120,116), (404,402), (43,42), (403,402), (197,201), (277,276), (320,68), (131,385), (304,50), (13,5), (132,384), (152,146), (273,257), (81,80), (168,138), (160,136), (105,104), (152,400), (66,72), (288,40), (264,258)]

def sixRows3640 : List Six3640 :=
 [⟨160,69,128,101,32,197⟩, ⟨17,10,1,26,16,11⟩, ⟨320,50,256,114,64,306⟩, ⟨24,5,16,13,8,21⟩, ⟨33,272,32,273,1,304⟩, ⟨132,42,128,46,4,170⟩, ⟨66,385,64,387,2,449⟩, ⟨288,138,32,394,256,170⟩, ⟨17,104,1,120,16,105⟩, ⟨12,385,8,389,4,393⟩, ⟨264,50,256,58,8,306⟩, ⟨6,104,4,106,2,108⟩, ⟨12,208,8,212,4,216⟩, ⟨288,65,32,321,256,97⟩, ⟨33,208,32,209,1,240⟩, ⟨3,80,2,81,1,82⟩, ⟨6,385,4,387,2,389⟩, ⟨12,50,8,54,4,58⟩, ⟨24,257,16,265,8,273⟩, ⟨264,69,256,77,8,325⟩, ⟨320,138,256,202,64,394⟩, ⟨3,104,2,105,1,106⟩, ⟨17,138,1,154,16,139⟩, ⟨3,276,2,277,1,278⟩, ⟨6,208,4,210,2,212⟩, ⟨264,208,256,216,8,464⟩, ⟨160,260,128,292,32,388⟩]

def inversion3640 (ws : List Sig) (rn : Row × Row) : Bool :=
  ws.all fun w => !bit rn.1 w || bit rn.2 w

def deviates3640 (p n r s : Row) (w : Sig) : Bool :=
  (bit p w != bit r w) || (bit n w != bit s w)

def pick3640 (ws : List Sig) (p n r s : Row) : Option Sig :=
  match ws.filter (deviates3640 p n r s) with
  | [w] => if (bit p w != bit r w) && (bit n w != bit s w) then some w else none
  | _ => none

def pairCut3640 (p n : Row) (a b : Option Sig) : Bool :=
  match a,b with
  | some u,some v => (bit p u == bit n u) || (bit p v == bit n v) || (u != v)
  | some u,none => bit p u == bit n u
  | none,some v => bit p v == bit n v
  | none,none => false

def sixCut3640 (ws : List Sig) (s : Six3640) : Bool :=
  pairCut3640 s.p s.n (pick3640 ws s.p s.n s.ni s.pi) (pick3640 ws s.p s.n s.nj s.pj)

def shapeCut3640 (k : Nat) (ws : List Sig) : Bool :=
  (k+1 ≤ ws.length || (k == ws.length && invRows3640.any (inversion3640 ws))) &&
    sixRows3640.any (sixCut3640 ws)

def sixValid3640 (T : Sig) (s : Six3640) : Bool :=
  (bit s.p T != bit s.n T) && (bit s.p T != bit s.ni T) &&
  (bit s.n T != bit s.pi T) && (bit s.p T != bit s.nj T) && (bit s.n T != bit s.pj T)

theorem sixRows3640_valid :
    sixRows3640.all (sixValid3640 (chartGoal 511)) = true := by decide +kernel

theorem invRows3640_valid :
    invRows3640.all (fun rn => bit rn.1 (chartGoal 511) && !bit rn.2 (chartGoal 511)) = true := by
  decide +kernel


private theorem pick_single3640 {ws p n r s v}
    (h : pick3640 ws p n r s = some v) : ws.filter (deviates3640 p n r s) = [v] := by
  unfold pick3640 at h
  split at h
  next w eq =>
    split at h
    · cases h
      exact eq
    · contradiction
  next => contradiction

private theorem pick_pivot3640 {ws p n r s v T}
    (h : pick3640 ws p n r s = some v) (dr : bit p T ≠ bit r T) (ds : bit n T ≠ bit s T) :
    Pivot T ws.toFinset p n v := by
  have good := pick_single3640 h
  have agree (u : Sig) (hu : u ∈ ws.toFinset) (ne : u ≠ v) :
      bit p u = bit r u ∧ bit n u = bit s u := by
    have hd : deviates3640 p n r s u = false := by
      cases e : deviates3640 p n r s u with
      | false => rfl
      | true =>
        have a := List.mem_filter.mpr ⟨List.mem_toFinset.mp hu,e⟩
        rw [good] at a
        exact False.elim (ne (List.mem_singleton.mp a))
    simpa [deviates3640] using hd
  exact ⟨⟨r,dr,fun u hu ne => (agree u hu ne).1⟩,
    ⟨s,ds,fun u hu ne => (agree u hu ne).2⟩⟩

private theorem six_impossible3640 {ws k t T s} (run : Live T k t ws.toFinset)
    (tight : k+1 ≤ ws.toFinset.card+t) (valid : sixValid3640 T s = true)
    (cut : sixCut3640 ws s = true) : False := by
  simp [sixValid3640,and_assoc] at valid
  obtain ⟨diff,dr,ds,er,es⟩ := valid
  let pi := pick3640 ws s.p s.n s.ni s.pi
  let pj := pick3640 ws s.p s.n s.nj s.pj
  change pairCut3640 s.p s.n pi pj = true at cut
  cases hi : pi with
  | none =>
    cases hj : pj with
    | none => simp [pairCut3640,hi,hj] at cut
    | some v =>
      have pv := pick_pivot3640 (v:=v) (show pick3640 ws s.p s.n s.nj s.pj = some v from hj) er es
      exact tight_no_binate run tight pv (by simpa [pairCut3640,hi,hj] using cut) diff
  | some u =>
    have pu := pick_pivot3640 (v:=u) (show pick3640 ws s.p s.n s.ni s.pi = some u from hi) dr ds
    by_cases eu : bit s.p u = bit s.n u
    · exact tight_no_binate run tight pu eu diff
    cases hj : pj with
    | none => simp [pairCut3640,hi,hj,eu] at cut
    | some v =>
      have pv := pick_pivot3640 (v:=v) (show pick3640 ws s.p s.n s.nj s.pj = some v from hj) er es
      by_cases ev : bit s.p v = bit s.n v
      · exact tight_no_binate run tight pv ev diff
      exact tight_no_conflict run tight pu pv eu ev (by simpa [pairCut3640,hi,hj,eu,ev] using cut)

theorem shapeCut3640_sound (k : Nat) (ws : List Sig) (nd : ws.Nodup)
    (cut : shapeCut3640 k ws = true) : Impossible (chartGoal 511) k ws.toFinset := by
  intro j t budget run
  simp only [shapeCut3640, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.any_eq_true] at cut
  obtain ⟨room,s,hs,why⟩ := cut
  have tight : j+1 ≤ ws.toFinset.card+t := by
    rw [List.toFinset_card_of_nodup nd]
    rcases room with room|⟨eq,p,hp,inv⟩
    · omega
    · have test := List.all_eq_true.mp invRows3640_valid p hp
      have sign : bit p.1 (chartGoal 511) = true ∧ bit p.2 (chartGoal 511) = false := by simpa using test
      have need : t ≠ 0 := by
        intro zeroNot
        obtain ⟨w,hw,h1,h0⟩ := mono_row_difference run zeroNot sign.1 sign.2
        have wi := List.all_eq_true.mp inv w (List.mem_toFinset.mp hw)
        simp [h1,h0] at wi
      omega
  exact six_impossible3640 run tight (List.all_eq_true.mp sixRows3640_valid s hs) why


def nd9 (i : Nat) : Nat := 0xd0803901006840eb6081d6c10003420000002e026880000190c10000000005810000001d040093c8a20fe7cb9dc4d065ae568af552950c813e1dce4602d958a24c23908602b13084380a02803e6c872c12a4c0aa3007d1d0e5765957154600f4e6bd30ec126498c01f3c4396095260531803ed8872b2ac498a430061af2994c26e3360600837e6b3585cae6c0c0186f4a6470b95cd818020df9acd61729930300417f1f55c4aca960600837ede9395514cc0c0105fcad4b0b961d718020dfadb6631654ae300417f1f52c2e56a54600b9b26cb04a9302a8c0106fcd66312b2a5518020bf8fa9e25654aa30041ef534c94aeaa4c60083dea69395db1498c0185ecb2325875e9318020df9acc6172bd26300417f1f52c2e55a4c600837eb6d98c595298c0106fcd66312b2a5318020bf8faae25654a630041bf5b49caed8a48600837e6b3185cab490c0107bd4d272bb4e9218020df9acc61729d24300417f1f5ac2e5654860082fe3eb585caa690c01b6c4c958d624c5218020dfadb6631654a430041fe2b6cc2e5514c200
def nd10 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0xcfb0ba9118154600cfd0ba8cd8154600fb61825498154600fc71765957154600fd6172549715460085fc7c4aca9546008df87c4aca954600aee8c662a2250600afa8ca6122250600ccf8b69dd8a506008ef8bc9998a50600ce78b69558a50600c6fa662e55a50600cdb8ba9dd8450600cf38ba9558450600cbb8baa214250600cf38ba95542506008df87c56eaa4c60087bd4c26eaa4c6008df97c2ae554c600ad797c2ae554c6008fe8cb5ea224c6008ef96caed8a4c600ccf8b69dd8a4c6008ef8bc9998a4c600ceb8b69118a4c6008fe92caed7a4c600cbe8b2a217a4c600cee8b29997a4c600cf68b29557a4c600cfa8b29117a4c6008ef8c662d7a4c6008fe8c262d7a4c6008df8cb61d7a4c600cde8b261d7a4c6008fe8c25ed6a4c6008bf88c5ad5a4c6008bf8cb629824c6008df97c2e9824c6008fb94c2e9824c6008ef8cb5a9624c600ced8ba58d624c600cf58ba955324c600cf98ba911324c600bbc98c289324c600bf894c289324c600cdf0ba9dd814c600cf70ba955814c600cfe0ba889814c6008ff0bc569814c600fad18658d814c600fbc1824c9814c60086fcc662ca94c6008ef8c662ca94c6008ef96caed8a48600ccf8b69dd8a486008ef8bc9998a48600ce78b69558a48600ceb8b69118a486008ef8c662d7a486008df97caed5a48600c9f87ba215a486008df8bc9dd5a48600ccf87b9995a48600cdb87b9115a48600cdd87b8cd5a486008ef8c662d5a486008df87c5ad5a486008ef8c662d3a486008df87c56d3a48600fce1765897148600cbf0baa213148600cef0ba9993148600cf70ba95531486008ff0cb6293148600fec1635893148600bee16c2c931486008ef8c662ca9486009af88c5ad5358200ceba6652eaa4c200afa94caaa224c200afb14caaa114c2008fb94caed6a4c2008ef8c662eaa482008ef96c2ae8848200aaf96c2ae8848200afe0c15aa22482008ff0cb5aa11482008df8cb5cd7a482008ff11caed6a48200cbf0b1a216a48200cdf0b19dd6a48200cf70b19556a48200cfd0b18cd6a482008ff0c162d6a482008ff0c15ed6a482008ef8cb5956a48200cef0b15956a482008ef8cb58d6a48200ced8b358d6a48200cef0b158d6a482008fb94caed3a482008ff0c15ad3a482008ef96c2e953482008bf8cb62981482008df8cb5e971482008ef96c2e951482008fb94c2e951482008fd8cb4e931482008df97c2e931482008ef96c2e93148200afe0ca5c52148200bde17c2852148200bfc13c28521482008ef96caed8a44200ccf8b69dd8a442008ef8bc9998a44200ce78b69558a44200ced8b68cd8a44200cee8b68898a442008ef8c662d7a442008f78c562d7a442008fb94caed3a442008ef8c662d3a442008fe8c25ed3a442008ef8c662d2a442008df87c56d2a442008ff0cb6295144200 else (if i < 2 then 0xd6ecb95956248600d6ecb958d624860087fcc96e98148600b5f4c961d7148600fce576589714860087fcc96e9514860087fdac2e5514860087fcc96e931486008ff4cb6293148600e7d4396293148600b7d4c958d3148600f7c42958d3148600fec5635893148600b7e4c95893148600f7c4395893148600b7d4c94c9314860087fecc62ca94860087fcc562ca94860087fecc56ca94860087fd8c56ca94860087fc8c56ca94860087fd8c4eca94860087fd5c4eca948600a5fd7c214a948600a6fd6c214a94860087fdcb214a948600a7bdc4214a948600a7ddc3214a948600a7edc2214a948600a7f5c1214a948600a7f9c0214a948600d5ec295ec8548600d6ec295ac854860087fcc96e88548600c7ec296e88548600d7ac296d08548600d7cc296cc854860097ecc96c88548600d7e4296c48548600d7e8296c08548600c5fca95ec8348600d5ec295ec8348600c6fca95ac8348600d6ec295ac8348600c77ca956c8348600d76c2956c8348600c7bca952c8348600d7ac2952c834860087fcc96e88348600c7ec296e8834860097ecc96c88348600c7eca96c88348600c7f4a96c48348600d7e4296c48348600c7f8a96c08348600d7e8296c0834860087fcc96e85348600c7ec296e85348600c7f4a96c45348600d7e4296c4534860097facc2e5514c200aef96c54d6a482008bf88c6ac5958e00c6be6652ca960a00ceba6652ca960a00ced8a3aed6358a00ecd8a39dd6358a00ce78ba9556358a00ee58a39556358a008ef8cb6296358a00aed8c36296358a00f8e9875d98258a00ced8b39998a50a00cde8ba9dd824ca00f9c9875cd824ca00bdc97c2cd824ca00bfc1c12cd824ca008efacc5aeaa60600acf96caaa7760600ccfa772ae6660600ae796caaa5560600ae78ac99a5560600aeb96caaa4460600ecb8a69de4460600aeb8ac99a4460600ee38a69564460600aed96caaa3360600ecd8a69de3360600aed8ac99a3360600ee98a69123360600aee96caaa2260600aee8ac99a2260600eea8a69122260600eec8a68ce2260600cbb8ba91182606008ef8c66ac59606008ef8c66ac3960600cef0a646c39606008ef8c66ac2960600ceb8a652c29606008ef8c66ac5360600cef0a66c453606008ef8c66ac52606008ef8ac5ac5260600ceb8a652c52606008ef8c66ac3260600caf8a662c3260600ccf8a65ec32606008ef8ac5ac3260600ce78a656c3260600ceb8a652c3260600cef0a66c432606008ef8cb62a665c600aeb8c662a445c600adb8ca61e445c600aed8c662a335c600add8ca61e335c6008ef96caed8a5c6008df8ca62d725c6008ef8c662ca95c6008ef96caed8a58600fae18258981586008fb84c4eeaa546008fb94c2ae3354600af994c2ae33546008fb9c42e982546008ef8cb5a962546008fb9c42ad4254600 else 0xf3d4894c9814c600f6d4392d9814c60087fcc96e9514c600c5fca95ec8a4c600d5dc395ec8a4c60087fc8caeca94c60087fc5caeca94c60087fcbca20a94c60087fcbc954a94c60087fecc62ca94c60087fdc762ca94c60087fdc662ca94c600c3fd8262ca94c600c6fcc662ca94c60087fcc562ca94c60087fecc56ca94c60087fd7c56ca94c60087fd6c56ca94c600c77d5256ca94c60087fc8c56ca94c60087fd8c4aca94c60087fd7c4aca94c60087fd6c4aca94c60087fd5c4aca94c600c5fd7b61ca94c60087fccb61ca94c60087fdcb5d8a94c60087fdcb60ca94c60087fdcb5cca94c60087fdcb54ca94c600c5fd7b5c8a94c600c6fd6b588a94c600a5fc7c548a94c600c7ec2b548a94c60087fdcb604a94c60087fdcb5c4a94c60087fdcb544a94c600a5fd7c214a94c600a6fd6c214a94c60087fdcb214a94c600a7bdc4214a94c600a7ddc3214a94c600a7edc2214a94c600a7f5c1214a94c600a7f9c0214a94c600d5dc395ec854c600d6dc395ac854c60087fcc96e8854c600c7dc396e8854c60097dcc96cc854c600d7cc396c8854c600d7d4396c4854c600d7d8396c0854c600c3fca962ca24c600d3dc3962ca24c600c5fca95eca24c600d5dc395eca24c600c6fca95aca24c600d6dc395aca24c600c77ca956ca24c600d75c3956ca24c600c7f8a96c0a24c600d7d8396c0a24c60087fcc96ac824c60097dcc94ec824c600d7d4396c4824c60087fcc96ac524c600c7dc396ac524c600c6fca95ac524c600d6dc395ac524c60097dcc94ec524c600c7dca94ec524c600c7f4a96c4524c600d7d4396c4524c60087fc8c26eaa4860087fc3c26eaa4860087fdac26e884860087fcac26e884860087fcac26e554860097bd4c26e334860087fcac26e33486008efd6caed8a4860087fc9caed8a4860087fecc2e58a4860087fd7c2e58a4860087fd6c2e58a4860087fd5c2e58a4860087fd3c2e58a4860087fc5c2e58a4860087fc3c2e58a48600c6fcb62e58a4860087fcc962d7a486008efcc662d7a4860087fcc962d6a486008dfd7caed5a4860087fcc962d5a486008efcc662d5a4860087fcc95ed5a486008dfc7c5ad5a4860087fcc95ad5a4860087fecc2e55a4860087fd8c2e55a4860087fd7c2e55a4860087fd6c2e55a4860087fd3c2e55a4860087fc8c2e55a4860087fc3c2e55a48600c5fc7b2e55a4860087fc9caed3a4860087fcc962d3a486008efcc662d3a4860087fcc95ed3a4860087fcc95ad3a486008dfc7c56d3a4860087fcc956d3a4860087fd8c2e53a4860087fd7c2e53a4860087fd6c2e53a4860087fd5c2e53a4860087fdac2e5874860087fcac2e5874860087fdac2e5654860087fdac2e5834860087fdac2e5634860087fdac2e5534860087fcac2e5534860087fdac2e5824860097bd4c2e58248600)) else (if i < 4 then 0x87fc8c4aca95460095fc7c4aca954600c5fc7c4aca954600a5fc7c4aca95460087fc3c4aca95460087fdcb5d8a95460087fccb58ca954600a5fc7c688a95460087fccb608a954600c6fd6b588a95460087fccb588a95460087fccb4c8a95460087fdcb604a95460087fdcb208a954600a3fd8c0c8a954600a5fd7c0c8a954600a6fd6c0c8a954600a77d5c0c8a954600a7bd4c0c8a95460087fdcb0c8a954600a7f5c10c8a954600a7f9c00c8a95460087fcc96ac825460097f4c96c48254600d774596c4825460087fcc96ac3254600c77c596ac3254600c7f4196ac3254600d37c5962c3254600d3f41962c3254600d57c595ec3254600d5f4195ec3254600d67c595ac3254600d6f4195ac3254600977cc956c3254600d7741956c3254600d73c5952c3254600d7b41952c325460097f4c96c43254600d774596c43254600d778596c03254600d7f0196c0325460087fcc95eeaa4c60087fcc95aeaa4c6008dfc7c56eaa4c60087fcc956eaa4c60087fcc94aeaa4c60087fd8c26eaa4c60087fd7c26eaa4c60087fd6c26eaa4c60097bd4c26eaa4c600a7bd4c26eaa4c600c7bd4c26eaa4c60087fc8c26eaa4c60087fc5c26eaa4c60087fc2c26eaa4c60087fdac26e884c6008dfd7c2ae554c600c7dc392ae554c60087fcac26e224c60097dc3c26e224c6008efd6caed8a4c60087fc9caed8a4c60087fd7c2e58a4c60087fd6c2e58a4c60087fd5c2e58a4c60087fd2c2e58a4c60087fc5c2e58a4c60087fc2c2e58a4c600c6fcb62e58a4c6008fed2caed7a4c60087fcc962d7a4c6008efcc662d7a4c6008fecc262d7a4c6008dfccb61d7a4c600a5fcc961d7a4c600cdecb261d7a4c60087fecc2e57a4c60087fd8c2e57a4c60087fd6c2e57a4c60087fd5c2e57a4c60087fd2c2e57a4c60087fc8c2e57a4c600c7ecb22e57a4c600c7eca92c97a4c600d7cc392c97a4c60087fcc962d6a4c60087fcc95ed6a4c6008fecc25ed6a4c60087fd8c2e56a4c60087fd7c2e56a4c60087fd5c2e56a4c60087fd2c2e56a4c6008bfc8c5ad5a4c60087fcc95ad5a4c60087fecc2e55a4c60087fd6c2e55a4c60087fd2c2e55a4c60087fc2c2e55a4c60087fdac2e5874c60087fdac2e5654c60097dd2c2e5634c6008bfccb629824c6008dfd7c2e9824c6008fbd4c2e9824c60087fcc92e9824c600c7dc392e9824c60087fdac2e5824c60097bd4c2e5824c60097f51c2e5824c6008efccb5a9624c600c6fcb95a9624c600cedcba58d624c600d6dcb958d624c60087fdac2e5524c60097dcc95ad324c60097dd6c2e5324c60087fcc96e9814c6008ff4bc569814c600e3f489569814c600e7d439569814c600f3d439619814c600fad58658d814c600b7d4c958d814c600b3f4c9609814c600f3d439609814c600fbc5824c9814c600b7d4c94c9814c600 else (if i < 5 then 0x87fcc96ac3260600c3fc896ac32606008efcc66ac326060093fcc962c3260600cafca662c3260600d1fc895ec3260600ccfca65ec32606008efcac5ac3260600d37c8956c3260600ce7ca656c3260600d3bc8952c3260600cebca652c3260600d3f4896c43260600cef4a66c43260600d3f8896c03260600cef8a66c0326060087fcc962eaa5c60087fcc95aeaa5c60087fcc94eeaa5c60087fdac26e885c60087fcac26e885c60097bd4c26e335c60087fcac26e335c6008efd6caed8a5c60087fecc2e58a5c60087fd6c2e58a5c60087fd5c2e58a5c60087fd3c2e58a5c60087fd2c2e58a5c60087fc3c2e58a5c600c6fcb62e58a5c60095fecc2e5875c600c5feaa2e5875c600d1fe882e5875c60095fd6c2e5875c60095fd2c2e5875c60095fcac2e5875c600c5fcba2e5875c600d5f4b12e5875c60095fcc962d765c60087fdac2e5655c60087fdac2e5835c60087fdac2e5635c60087fdac2e5825c60095fd7c2e5825c60097bd4c2e5825c60097f51c2e5825c60087fcac2e5825c6008dfcca62d725c60095fcc962d725c6008ff9c02ad625c60087fecc62ca95c60087fcc362ca95c60087fecc56ca95c60087fc8c56ca95c60087fcc356ca95c60087fecc4eca95c60087fd8c4eca95c60087fc8c4eca95c600a5fd7c20ca95c600a6fd6c20ca95c600a77d5c20ca95c600a7bd4c20ca95c60087fdcb20ca95c600a7edc220ca95c600a7f5c120ca95c600a7f9c020ca95c60087fcc96ac835c60095fcc95ec835c60097bd4c26e33586008efd6caed8a5860087fcc962d7a5860087fdac2e5875860087fdac2e5835860087fdac2e5735860087fdac2e5825860097bd4c2e5825860087fdac2e5525860087fdac2e53258600b3f4c96098158600fae5825898158600b6f4c9589815860087fcc96ac5358600a77cc9596aa54600a77cc954aaa54600e76c2954aaa5460097bd4c26e335460087fcc95ed6a5460087fecc2e56a5460087fd8c2e56a5460087fd7c2e56a5460087fd3c2e56a5460087fd2c2e56a5460087fc3c2e56a5460087fc2c2e56a5460097facc2e5a45460087fdac2e5635460087fdac2e5825460097bd4c2e582546008efccb5a96254600c6fcb95a9625460087fdac2e53254600f374596198154600b3f4c96098154600f374596098154600fb65825498154600f76429549815460097f57c2e58154600d775522e58154600d6f4b92d98154600f674592d9815460097f4c962d7154600b5f4c961d7154600fc75765957154600b774c95957154600fd65725497154600d774b9549715460097f58c2e5715460087fc3caeca95460087fc2caeca95460087fcbc8cca95460087fecc4eca95460087fd6c4eca95460087fcc24eca95460087fd8c4aca95460087fd7c4aca95460087fd6c4aca95460087fd3c4aca954600 else 0x8efccb6296358a00a6fcc96296358a00aedcc36296358a00d6ecb92c96358a00f8ed875d98258a00e67d65954a958a00c6fd6362ca958a0087fecc56ca958a00c77e5556ca958a0087fcc356ca958a0087fc5c4eca958a00a6fd6c14ca958a0087fdcb14ca958a0087fcc96ac5358a0087fcc95eeaa4ca0087fcc95aeaa4ca0097bd4c26eaa4ca00a7bd4c26eaa4ca0097dd3c26eaa4ca0087fcac26e554ca0087fd6c2e58a4ca0087fd1c2e58a4ca0087fcc962d6a4ca0087fcc95ed6a4ca0087fecc2e56a4ca0087fd8c2e56a4ca0087fd7c2e56a4ca0087fd5c2e56a4ca0087fd1c2e56a4ca0087fc5c2e56a4ca0087fdac2e5874ca0087fcac2e5874ca00b5dcc961d734ca0087fcc96e9824ca00f9cd875cd824ca0087fdc662ca94ca0087fecc56ca94ca00c5fca95ec854ca00c6fca95ac854ca0087fcc96e8854ca00c7dca96cc854ca00c7eca96c8854ca00c7f4a96c4854ca00c7f8a96c0854ca0087fcc96ac814ca00c5fca95ec814ca00c7dca94ec814ca00c7eca94ac814ca0087fcc96ac514ca00c7dca94ec514ca0087fcc95eeaa60600c6fcc95aeaa6060087fcc95aeaa60600c6fc595aeaa60600c6fc395aeaa60600c6fc295aeaa6060097f51c26eaa60600c6fd6b26eaa6060087fcac26e5560600c6fca626e556060097bd4c26e336060087fcac26e3360600c6fca626e336060087fcac26e226060093fc8c26e2260600c6fca626e2260600c6fca62e5a560600c6fca62e5a36060087fdac2e5736060097f51c2e57360600c6fca62e5736060087fdac2e5636060097f51c2e56360600c6fca62e5a26060087fdac2e5826060093fd6c2e58260600b3bd4c2e5826060097bd4c2e58260600d3bd4c2e5826060093fcac2e58260600d2fca62e58260600e2fca9299826060093fcc962d6260600b3ecc9609526060087fdac2e53260600c6fca62e5326060087fecc56ca96060087fcc356ca96060087fcc256ca96060087fecc4eca96060087fd7c4eca96060087fc5c4eca96060087fcc24eca96060087fecc4aca96060087fd7c4aca96060087fd5c4aca96060087fd3c4aca96060087fc5c4aca96060087fc3c4aca960600a5fc7c548a96060087fdcb14ca960600a7f5c114ca960600a3fd8c148a960600a7bd4c148a96060087fdcb148a960600a7f5c1148a960600a3fd8c0c8a960600a5fd7c0c8a960600a77d5c0c8a960600a7bd4c0c8a96060087fdcb0c8a960600a7f5c10c8a960600a7f9c00c8a960600a6fc9caa8a660600a6fcc969ca66060087fcc96ac5360600c3fc896ac53606008efcc66ac5360600d3f4896c45360600cef4a66c4536060087fcc96ac5260600c3fc896ac52606008efcc66ac526060093fcc962c52606008efcac5ac5260600d3bc8952c5260600cebca652c5260600d3f4896c45260600))) else (if i < 9 then (if i < 7 then 0xc7fcb95e96354600e6fc395a96254600b7f4c95cd8154600f3f4396098154600f774395498154600fbe5824c98154600d7f43962d7154600f5f43961d7154600f5f4395d97154600f774395957154600b7f4c958d7154600a7fd7c58ca954600e6fd63588a954600e7ed824c8a954600a7fc9ca217a4c600c7fcb95957a4c600dded872c97a4c600e7dc3961d5a4c600e7dc395d95a4c600c7fd872e55a4c600c7fd762e55a4c60097fc9caed874c600f5dc3961d754c600f6dc395d9654c60097fcc962d734c600d7dcb95d5634c6008ffcbc569824c600a7fcc9569824c600e7dc39569824c600e9fd7a61d824c600f6dc39595624c600c7fca962d524c600d7dc3962d524c600c7fca95ad524c600d7dc395ad524c600b7dcc958d524c600ef6d5a609524c600afecca609524c600e7eca9609524c600f7cc39609524c600eddd7a61d324c600efcd7a609324c600fbcd87609324c600f7d4395d5814c600fbe582549814c600f7d439549814c600e5fd875d4a94c600e6fd76594a94c600e6fd65588a94c60097fcc95ad5348600f6ec395956248600beed6c54d6248600b7ecc954d6248600f7cc3954d6248600ddf57b61d3148600f7d4396153148600f7d4395953148600fee565589314860097bd4c26e335da0087fcc95eeaa58e0087fecc2e57a58e0087fd2c2e57a58e0087fd1c2e57a58e0087fc5caeca958e0087fc2caeca958e0087fecc62ca958e0087fdc762ca958e0087fcc562ca958e0087fcc262ca958e0087fd8c56ca958e00c77d8556ca958e0087fcc256ca958e0087fc5c4aca958e00a3fc8c694a958e00a6fd6c148a958e00a7bd4c148a958e0087fdcb148a958e0087fcc96ac5258e0096fcc95ac5258e0087fcc95aeaa60a00c7dc394eeaa60a0087fd6c26eaa60a0097ed2c26eaa60a0087fd2c26eaa60a00c7ed5226eaa60a0087fc1c26eaa60a0087fdac2e56360a0097ed2c2e56360a0087fcac2e56360a00c7ed52aeca960a0087fc1caeca960a00c7bd7b52ca960a00c7bda752ca960a00d3bd8752ca960a00c7bd8752ca960a00c7bd7652ca960a00c7bda152ca960a00c7bc5152ca960a0087fd6c4eca960a00c7f61146ca960a00c7bd4b46ca960a0087fc5c46ca960a0087fdcb5d8a960a00c6fd6b58ca960a00c7bd4b58ca960a00a7ed2c144a960a0087fdcb144a960a00c6fca95aca360a00c7bca952ca360a00c7f4a96c4a360a00c7f8a96c0a360a00c5fca95eca160a00c7bca952ca160a0087fcc96ac5160a0087fcc96ac3160a00c3fca962c3160a00c7eca94ac3160a0087fdac26e885ca0087fdac2e5635ca0087fcc95eeaa58a0087fcc956eaa58a00a77cc96965558a0087fcac26e5558a0087fd7c2e58a58a0087fd5c2e58a58a0087fd3c2e58a58a0087fd1c2e58a58a0087fcc962d7a58a00 else (if i < 8 then 0x6caac8556eaa99544aa6c54b6a8f9510aa0453e6a7894e8a9b4532ea6194baa96452a6a4a948ca90851eea30944ca88850eea169412a81450069f993d8a7944f069dc93b0a7444e669c8937ca6e84d969a89348a65c4c9698e930ea6004bde97192daa5984ac6954929aa5184a0e9379266a4a448f69179226a424482690091f8a3c8476e8e691c4a378469e8cf918aa30445e68b59162a2b445468a49128a234442e88190eea1c0435e86790c0a17042be853909ea12c423683c9070a0d0414e81f9036a050407e80b90029ff43f7e7eb8fce9f683eae7d18f9a9f243e267c08f789ee03d9e7af8f569e9c3d167958f109e043be676f8ec49d6c3a6e7498e8a9cf839ce7358e629cb439467248e409c7038be7138e1e9c2c38367028dfc9be837ae6f18dda9ba437266e08db89b60369e6cf8d969b1c36166be8d749ad8358e6a78d3a9a58348e68d8d0c99f033be6738cd8999433066598c9e9920321e63c8c7098c4314e61f8c36985c30666088c0897f42f965eb8bce97802ec65d48b9a970c2df65ba8b6696a42d2659a8b20960c2bc65748ae0958c2af655a8aa6952429de5348a6094b0293e5238a38946028565068a0493f8279e4ef89d0937826ce4cf898a92e0256e4a68932923c240e47a88e091b0233e46088b89160229e44f8896911c221643e887490d8218e42d88529094210641c88309050207e40b880e900c1ff63fa87ec8fc81f563e687c48f6c1e9e3cf87968f1c1e163be87748ec01d5e3a7873a8e4c1c5e38787068df01bbe37086d88da01b0635c86b08d501a6634886888cf419c633486608cb0193e323863e8c6c18b6312861c8c1017fe2fb85ee8bcc17462e485c08b7016a62d085988b20161e2bc85708ad0157e2a885488a8014de29785268a3c1456286850489e0138626c84d0899012fe25b84a889401246244848088f011be233845e88ac1136222843c886810ae211841a8824102620083f887e00f9e1ef83d6879c0f161de83b487580e8e1ca838c87080dd61b0835886a00d1e19f833086500c7e18b830e860c0bf617a82ec85c80b6e16982ca85840ae615882a885400a5e147827a84e409a61308258848808be113821e842c083610281fc83e8077e0e881c8837406c60d1819a832406260c0817882e0059e0af8156829c051609e81348240045e08780f481d8038e06780ba8158025e041807480d8017602a804c808800ee019802a8044006600880088000b6fc9c9556358a00beedc65cd8258a00faed8758d8258a00a7fcc95a95a4ca00f9ed875d9824ca0097fc9caed736060097fcc962d7360600f3ec396095260600fbcd736093260600c7fd8a26e335c600d5fd8726e335c600f4fc395d9655c600a7fc9caa9835c600a7fcc96e9835c600ebed8a609325c600f9ed87609325c60097fcc95ed6354600 else 0x42d821ee14b6087b852d8296c10b6086c8531421b214c50a6285314216c10c5085b0431421ee1b21bc34860a4305218211c10bc3b60f7185c8449640c2d823be1810090804840204610b6082500f07b8f8683dc45041e1a0f71047078683dc490414820a410520821041082085485208211c108e0a410408c2104104a01e0f7184104208209405a03c1ee4023084107868030364609403c1ee3e1a0de10250208060c1281040307c341ee24b60f0d07b892d8296c14b6085b042a4204610b60843042d8218a10a90d43ca857506aa04d404a7e74f5a9e2d3b4a72f4e1a9bad364a6a74d3a99ed32ca6374c2a97cd2e8a5af4b4a960d2b0a53f4a3a93ed26ca4b7495a91cd228a42f484a906d1f0a3a7470a8d8d1a0a30745fa8b0d150a27f44ba88ed10ca1f743aa86cd0c8a16f42ca850d090a0ff418a82ed058a08f40da80cd0089fd73f6a7e4cfb89f4f3e5a7c2cf809edf3daa7a6cf309e3f3baa766cebc9d573a6a744ce789ccf38ca704cdf89bcf375a6d0cd909acf34ca690ccf899cf335a662ccb49947324a634cc4c987730aa60ccbe497772e7a5bacb4c962f2b5a562cab494ff29ba52eca4c9477284a4f4c9d8938f26da4d2c9949307256a4a4c938924f245a482c8e8919722ea454c89890f7214a41ac818900f1f7a3e6c7c88f271e0a3acc73c8e571c6a384c6e08d871a3a338c6548c87189a30ac6048be7175a2d6c5908aff155a2a2c5288a1713ea262c4b488ff11ba216c41c87ff0fba1eec3cc87770eaa1ccc38886ef0d9a1aac34486670c8a182c2d085370a2a13cc26884af08ea114c21883df077a0e6c1bc8357066a0bec160826f046a084c0e08187029a04ac08480b700ca004bff87fb6ff29fd6bf907ecefd59f9cbf287e2efbb9f6ebecc7d76fa19f3abe407c2ef819efabde47b8ef6d9eccbd7c7abef539e98bd1479eef369e58bc9478eef139e18bc147806efc9df0bbd07766ee89dc8bb8076c6ed49da0bb307626ec09d78bae0759eeaf9d56ba8474e6e989d28ba40745ee879d06b9fc73a6e679cbab96472a6e4d9c92b8fc71d6e369c5eb89470bee139c18b820701edff9bf6b7d06f7edeb9bd4b78c6ef6dda9bacb7486e6edc39b78b6e06d9edac9b50b6786cced959b22b6346c2ed7b9aeeb5b46b16d589a9cb51c69e6d359a56b49068fed189a1cb41c6816cfe99f4b3d8675ece799c6b37066a6cd09998b320661ecbf996ab2b8654ec9f9936b2446436c8298fcb1dc637ec6898bcb16862aec4e9894b10c61f6c349860b0b06126c209838b060606ec0097f2afa45f26be097b8af605e9ebc69784aef85d9ebaf9756ae845ce6b989722ae345c46b849700adf05bbeb7396deadac5b36b5c96a4ad2059d6b2d9646ac58585eb0495faabe457a6aed95d2ab945706adc95b0ab50567eacb958eab0c55f6aba95)) else (if i < 10 then 0x8200203e200101f10430415ac0007c6092102b01f16fa02b58000f9037c200203e200d034101b87f140fc1c8600c1b0004401f1fe281e8390c0f40a0410c1df40d90241811840442c1c107b04401f1810841940f4410c103c0ee407b8120c0f03f8a07a0e4303d089b8400407c41be155f0b070583823e9f8bf3017207a571a03d103281e898383f8bf3007a371a03d12af85838200203e20110b070417c205210110808841340f41cc60921037080a80b0378f4001f407c6052102b01f1024840dc202a02c0da305f0fdb68003e00f90124206e106bfc583e01f202484044206e14020a01050082092103709e284018281c140e0a070411f400fd00d087aba007e8068402b01f101184f540b4fd00d087be0a4086050402b01f10232801fa01a118382c1c100101f1307041882c1c160e0b07040442c1c10110b07040442c1c10110b07040442c1c1015080905838202a100d080a858382024101508068583820be100e08338402420121017080487f143d407c60760f803e300d0341024840dc205607a207b04301f181484038207607a200101f105b0400407c5f6c0e4060300101f105b0400407c418a100101f100681a0bed81f007c609210370fe283d00f8c17c201c100d030102b03c80f8c00407c416c100101f100080f88314200203e2fb607c01f1824840dc205603e2044b00054180487f140fc1c860896000a83df402eb0005427e281f8390c02422be1cc807812180c201e040f0200203e27009c50d919fa7cc06c81e9000407c425210150847054382e3407a26060fe2fcc07b81e900f02a1c10120c1e03e00f8c0a4205603e285e07303d182f860f01f407c60c70bc03e33df047c3c03421fa62581a0c0ac07c47be2478bc06843dfc5e03419ef816a2f01a1102407c47bf8bc06836060b030400407c4c0c16060b03041602c0c1606080a85818202a1606080a85818202a1606080a8581820241015080a85818202a1606080a85818202a16060d0d01a082dc21be1078823137a41189238291c14860a4704238211c12dd0f70d91a470523821a078a1b230c90922a01849150086d83b8a18f48b817ff04bd0ae05b3016b6097a15c09ad83ffc16b6097a15c09ad83ffc12f42b8135b05ad8290410b6085b05ad8216c16b6085b05ad8216c10e09a90de1b5b042d82d6c16b608704d006f0dad82d6c16b60f6287b88ad8250412b60941043dc364410410b60a5c062e03dc4130102308118408c210c10860a54852a43ffc11dd0f70d918e406c88114218a12b60941052d821ee84624b60b5c41189208290414820a4104314203210d9086c8436421ee14b6087b852d821b214860a4305218290c10b608430437c290c1086086f8421821b210230843043dc3784904148208490e40872024808c691c148e0a470437c23e81ee2ffe081b0 else (if i < 11 then 0x1c05c40101012081b8401407c408ce000683047034101b8415ec001cc6092102a034100280f880a43f6dbab63408e4012086cce2b8d03d90194278bf6c1a01b3e345037081501a0819420ca106508328419420ca1065080a84054202a1015080a84054208e06820b771a07d03d202301e87a81a11ca42e1c17060833841f007c40c016b6082b83c8880c1802d6c1060082f85ad8207607a203b03d17db03e00f8c5380f44d6c1057b0001f181f01e880ec0f4420c11370d8003c0328c15c48c1e060ae0ca0883004082201e88180217207a205704417db03e00f8dad8201a068200e0803041340f41a4609210290803060301340fc07c80921d00fc503f01f27e2f7a00f8c0a4201c13c5081580f880f4201801a202b01f101580f8803428ec03e2c7601f163b00f8b1d807c5f8a8ec03e347601f100080f881301cc0f4607607a200101f132f842d82cbe16b6080080f8997c216c106a082181e8997c2d6c165f080080f8997c216c10620b5b0597c2d6c1fc58e803d1b2f85ad82cbe16b60b2f85ad82cbe16b60b8006f01a0dc683d432c1108e001bc068304908258444015c409610f5ed501f1824840dc205603e2b0004301f181581fd8000f90038207607a2b000d8006c00226e10d905210020537c207000d91024841242092104908248448732015c7d8a07a204b08410411c3645970103d07c01f18070416420be100e082900f8a1781f407c60be10d904705219fa68d0290cfd346814867e82440a4305201f11fa68d0290d12c07c47e80a4068300101f1027044401105f8a1c003e300101f101b840dc206e1037089083c0220c0dc206e104403d106f00f880f0207c17000b8005c0022200ae088300101f101b86c001f007c60921fc507a01f1fe281f8390c038200c102e03d101700f880b80f442420ae0883086081e040b807c4c52102e03d131487f141c80f4660c103d0836826880f42c52103d0b8006c8220c777e603dc0f4800a07a21c8fb6f980d904d2825840f4201c10060816841340b01e407c806e10060fdb03e00f8c124206e1fc5eb8072182f84514206003e23c50807040dc205a13c50816840dc205a10120a1487f141e807c65bc24403e32de12201f197b96f09100f93f14e381e807c85bc24403e3fc538e07a01f216f09100f8c00407c400203e20090b148400407c4c5216020b14858082c5216020b1485808207a16020b1485808201216290b148580820020482024044106284004090404806820630241024840dc20421003017100080b8817c205210060833841e83640906c1c1011080707f17a383d407c80760f803e3049081b840ac07c5f8a08760003e40290803040ec0f45f6dd1dbaa03e400101f105b0421821be17000d91243041243f6c0f803e3037081580f8810ec0007c60be1b000c905204d200a8583 else 0x7a843d4376c100a48411c0ec4e1c17c50c9102b8815c2e1c12490b80040192102e082b85c3820f8170e0b87040e1c170e0b8705c38205c12b9081e8400afb8a20430f80040004606d101e81d885242c1c160e08238028800da1ca200d0b07043242c1c10160b07040582c1c103f083684002c160e0864843247204000068583827aa08e2043095cc0a880142e1c10b90edb04c38219210287040221dba204707b101b87bd00aec000a0800a03e20290803041d420921029080307f174020f81c89f8ade80583006081484bd021ea26479006840230e801e401a0c3d5c027200d08078107d03f0341987040dc20ce10670d800400820f96000503cf4052101f074002004107891a065057203c48d03d8c1e01944de90460f638230787dd1fe2c8d03c032901c5f55ee1030094a06e1d00081da8d03282b900a4206e1037081087400f5411067aa274068306108308418420c210610830841184e80d060ca10650832841242092103d034101601a09c0020781049081501a0815a8e81a4600a03e2047034104707639c683dc611c1016e86cf8d07b9340020f01ee0de302a03416800403820521d1a0f545e1a2f01a083d41184880d0800204e2001027101084))))
def hx10 (i : Nat) : Nat := 0x603400000000005148000000340000000009080000705c000000141c7033016503cc018043812a07fc14900e811701c000006dc06607888f60640000000000004c00000000003038000706b418d0758098010000400800000000000000000c02c00a0087c086014415407f00002260
def nd11 (i : Nat) : Nat := (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then 0x845108027fd5db1488401afea218a44200dbf4eec5221006efa66629108037bd2ab1488401bf68cd8a44200dfd444c52210067f8b96291080377c5b314884013fe2d58a442009ff166c5221004ff8b2629108027fd5daf488401afea217a44200ddf4ccbd221006f7a555e9108037ed19af488401bfa8897a442009ff316bd221004ff88b5e9108033fc5caf4884013fe2cd7a44200d7f510b5221006dfa775a9108037bd2aad488401bf68cd6a44200dfd444b5221004ff98b5a9108027fcbdad4884013feaed5a44200ddf4ccad221006fda33569108037f5112b4884013fe5ad5a44200cff172ad221004ff8b3569108027fc592b4884013feaed3a44200d7f5109d221006dfa774e91080377d3327488401bde9553a44200dfb4669d221006fea224e9108027fcc5a74884013fe5ed3a442009ff2d69d221004ff95b4e9108027fc45a74884013fe16d3a44200cff1729d221004ff8b24e9108027fd5da5488401afea212a44200dbf4ee95221006efa664a9108037bd2aa5488401bf68cd2a44200dfd44495221004ff98b4a9108027fcbda54884013fe5ad2a442009ff2b695221004ff93b4a9108027fc45a54884013fe16d2a442009ff076952210067f8b94a9108027fc5d30e884013fe2e985442009ff174c1a21004ff8ba5cd108027fc5d2a6884013fe2e98244200bbf0f6a9221004ff8ba549108027fc5d264884015fe2e58144200aff172b8a21005ff2bb545108037f9552a288401efca215144200fbe4eea8a21007ef26654510803fb92aaa288401ff48cd5144200ffc444a8a21006ff18a545108037f8bd2a288401fdc5955144200fee2a4a8a210077f0b954510802bfc5caa2884015fe2e53144200aff17290a21005df97b21510802f7cb590a884013fe6e88544200bf736842a21005fd9b321510802ff4d910a884017fc6c48544200bbf2f641a21005ef96b20d10802fbcad906884017ee52c83442009ff37441a21005fe9b220d10802ff8d8906884013fe6e85344200bfe36229a21004ff9ba20910802f7cb58a4884017ee52c52442009ff37429221005ff1b114910802dfcc58648840177e5ec3244200bdf2d619221005f795b0c910802fdca5864884013fe6e83244200bfe362192210047bd4b2a5828027dca5952c14013be2e96358a00ddb146b1ac5004fd8b3629428027f45d304994013be5aeaa60600d9f14d3bb03004ef8ab9998180373c534aac0c01bae29a4460600ddb14d19b03006ee8a6889818025fc5d304c0c013be2d98a5c6009bf174c3ae3004ff0ba6055180277c5b314a0c011fe2e55a506009f7174c2283004fb8ba5094180277c5b31498c013fa2c97a4c6009fb17499263004ff0ba6053180277c5b31490c0137e1ed5a486009fe17498a43004fb94baa9308027f858ad4904013be2d98a44200 else 0x1bbe9993a48200def4aa9d241004ff98b4e9208027fcbda74904013fe5ad3a482009ff1169d241004ff85b4e9208033fc5ca74904013fe2c53a482009ff174c3a41004ff8ba615208027fc5d2ca904013fe2e983482009ff174b9a41004ff8ba58d208027fc5d2a690401afe2298248200aff172c12410057f8b958920802ff55daa490401bfaaa95248200f7d510a9241007dea7754920803f75332a490401fda9555248200ff9466a9241006fe97a54920803fb4baaa490401fda54d5248200fbd0f6a9241007f685a549208037bc2d2a490401dfa2e55248200aff172a9241006fd83a4c920802bfc5ca6490401afe62981482009ff174c0a41005ef8b6605208037f850b0290401b7e5e971482009ff174b8a41006ef96a58520803fb4a92a2904013fe2e95148200dfb27498a41004ff8ba4c520802ff55da4290401efaa212148200fbd4ee90a41007eea6648520803fb52aa4290401ff28cd2148200bfd2b690a41006fe96a48520803ff0b8a4290401ff84c52148200efd17290a410057f8b948520803ff050a4290401bfc2852148200d7f31445241005ef96b16920802fdca58b490401bde5685a48200bbf2f61d241005ef96b0e9208037ec9d0749040177e5ec8548200bdf2d642a41004ff9ba21520802fdcda10a904017f66cc8548200bfd36442a41005ff1b121520802efcbd906904017be5ac8348200bef2b641a41005fb94b20d208027fcdd106904017fa6c88348200bfe36241a41004ff9ba14d20802ff4d90a6904016fe62ca148200bbf2f650a41005ef96b28520802fbcad942904017ee52ca148200bfb27650a41006ff1a1285208027fcd59029040177e5ec8148200bf729640a41005fe92b205208027fcd58a2904017fa4ac51482009ff35618a41005fe92b0c5208035fd4455488401b7e9deaa44200def4ab55221006fda33aa9108037f511554884013fe22eaa442009ff0b755221004ff83baa9108027fc15d54884013fe2ae8844200d7f15744221006bf85aa21108035fc1d51088401afe0aa8844200f3f5113ba21006df88a9dd108036fc1d4ee88401ebea226644200f9f4ef33221007b7a8895510803ebd3bcaa88401f9e99a55442009ff1572aa21006f78ab95510802ff80dcaa88401fdc06e5544200def1152aa21006f783a955108037bc154aa88401ef6a223344200fbb4ef19a21007eda668cd10803fad2ac66884013fe2ae3344200dfb15719a21006fd88a8cd108037ec2d46688401bf60aa3344200f7d51111221007dea7788910803f753344488401fda9562244200ff946711221004ff8ab889108037f455c44884015fe26e2244200efd13711221006fe88a889108037f42d44488401bfa0ea2244200fbe4ef08a21007fd23384510803ff11142288401bfc5ea1144200dfe27508a21006ff12a) else (if i < 3 then 0x5708a61005fd83b84530803fe81dc2298401bfc22a114c200dfe0b508a61006ff0a2845308027fd5dad498401b7e9dd6a4c2009ff2f6b52610067f8b95a9308027fc5aad4984013fe2c96a4c200aff172b1a61004ff8ba60930802fec59b04984013fe2e9624c200aff17299261004ff8ba60530802f7c5b302984013fe2e9714c2009ff174a8a610057f8b954530802fed5da6298401ef6a21314c200fbb4ee98a61007eda664c530803fe511262984017f656d314c200dfb2d498a61007fd1814c530803bec5ca62984015fe2e5314c200ffa26290a61004ff8ab485308027fcd5904984013fe6ac814c200bbf2f640a61005fb94b20530802fec9d902984013fe6ac514c200bfb27628a61004ff9ab08530802dfcc58429840177e5ec214c200bdf2d610a61005f795b08530802fdca5842984017f64ec214c200d7f51155241006efa66aa9208037bd2ad5490401bf68ceaa482009ff31755241004ff96baa9208027fcadd54904013fe4eeaa482009ff23755241004ff88baa9208027fc2dd54904013fe0eeaa482009ff03755241004ff8aba21208035fc55d1090401afe16a8848200d7f07544241006bf8a1a2120803cfd444ee90401b7e22a7748200dbf0753ba41006df8a19dd20803d7d444cc90401f3e9de6648200ddf0b533241006ef83a99920803dbd444aa90401f5e9de5548200fcf4cd2aa41004ff8ab955208037bc55caa904017fa0ae5548200fed0572aa41006f788a955208037bc1d4aa90401bde2865548200f7b51119a41007dda778cd20803f6d3346690401fd695633482009ff15719a41006fd8ab8cd20802bfc4dc6690401df626e3348200dfb11519a41006fd85a8cd208037ec50c6690401efaa222248200fdd4cd11241007fca33889208037f4c544490401bfa5aa2248200dfd11511241006fe83a889208037f450c4490401bfcaaa1148200f7e51108a41007df27784520803f793342290401fdc9561148200ffa46708a41007fe222845208037f8c542290401bfc5ea1148200dfe2d508a41006ff13a84520803ff0a9422904013fe2ae1148200dfe15708a410057f89b84520802ff415c2290401ff80ae1148200dfe11508a41006ff05a845208037f81d422904013feaed8a48200ddf4ccc5241006fda33629208033fc5cb14904013fe2cd8a482009ff162c5241006bfa885e92080377d332f490401bde9557a48200dfb466bd241006df9735e9208027fc45af4904013fe2cd7a482009ff162bd241004ffabb5a9208035fd442d490401b7e9dd6a48200def4aab5241006fda335a9208027fcc5ad4904013fe5ed6a48200ddf2cab5241006ef9635a9208033fc5cad4904013fe2d56a482009ff166b5241006ff0b15a920802ff858ad49040177e1ed5a482009ff5769d241006bfa884e9208036fd3ba74904 else (if i < 4 then 0x18027fc2d95290c013fe0eca9486009ff35644a43005fb94b225218027fcd58b290c013fe6ac3948600bfe2361ca43007fd1310e5218037f55505290c01efaa202948600fdd4cc14a43007f6a550a521803fe51985290c017fa5ac2948600dfd2b414a43007fe1310a521802efcbd90a90c017be5ac85486009ff37442a430057f9b921521802fdcda10a90c017f66cc8548600bfd36442a43005ff1b121521802efcbd90690c017be5ac8348600bef2b641a43005fb94b20d218027fcdd10690c015fe6e48348600bfd36441a43005ff1b120d218027fcdd0a690c017fc6c45348600d7f14b442c1006bf8a3a21608035fc51510b0401e7ea227758200dbf1473bac1007b7a8895560803ebd3bcaab0401f9e59655582009ff1572aac1006f78ab955608037bc51caab0401bde28a5558200f7b51119ac1007dda778cd60803fad2ac66b0401bf65ea3358200fdb2cb19ac1007ed9638cd608027fc55c66b0401bf62ae3358200dfb14b19ac1006fd8a28cd60803df544444b0401f7a9de2258200fed4ab112c1007fca33889608037f4bd444b0401fba5962258200fdd2c7112c1004ff8ab889608037f455c44b0401bfa2962258200dfd147112c1007bf28884560803ef93bc22b0401fdc9561158200ffa46708ac1007fe222845608037f8bd422b0401fbc5961158200fde2c708ac1004ff8b35e9608027fc5d30eb04015fe2e5a5582009ff174c2ac1005efabb59560803d7d442cab0401f3e9dd6558200fcf30ab2ac10076f8b959560802bfc5cb46b04013fe2e983582009ff174b9ac1005efabb58d60803d7d442c6b0401f3e9dd6358200fcf4aab1ac1007ed98358d60803b7c5cac6b04017be5ad53582009ff156a9ac10057f8b9689608027fc5d304b04013fe2ad5258200bbf0f6a92c1004ff8ab4c9608036fcbd2e2b0401ebea216158200f9f4eeb0ac1007e7a5558560803f6d19ac2b0401fba8896158200fde302b0ac1005ef96b54560803f3cb2aa2b04017be5ad3158200fdb2c698ac1004ff9ab14d60802f7cb58a6b04013fe6ac5258200bdf2d6292c1005fb94b149608027fcd5864b04016fe62c3258200bbf2f6192c1005ef96b0c960802fbcad864b04017ee52c3258200bfe362192c1006efa66aa9308027fc15d54984013fe06eaa4c200f9f4ef33261006ef85a9993080377c514cc98401fb699a334c200dfb2d519a61006feaaa88930803df54444498401f7a9de224c200fdd4cd11261006fe97a889308037f4b5444984013fe2ae224c200dfd157112610057f89b889308037f44544498401bfa16a224c200dfd14311261006ff2aa84530803df94442298401f7c9de114c200fde4cd08a61007f725584530803fe919c2298401ff888a114c200dfe2f508a61006ff16a84530803fe8a9c22984013fe2ae114c200dfe1 else 0xe9997a48600def4aabd243006fba445e9218027fcc5af490c013fe6d17a486009ff116bd2430047fcb95e9218027fc5caf490c013fe2cd7a486009ff576b5243006bfa885a9218036fd3bad490c01bde9556a48600df7488b5243006fda335a9218027fcc5ad490c013fe5ed6a486009ff368b52430047fcb95a9218027fc5cad490c013fe2d56a486009ff166b5243004ffabb569218035fd442b490c01b7e9dd5a48600ddf4ccad243006fba44569218037ed19ab490c013fe62d5a486009ff2f6ad243004ff96b569218027fcda2b490c013fe22d5a48600dbf0f6ad243005df87b569218026fe3dab490c011ff2e55a486009ff172ad2430067ec29569218027fc59ab490c01afea214a48600dbf4eea5243006efa66529218037bd2aa9490c013fe22d4a486009ff0b6a5243004ffabb4e9218035fd4427490c01b7e9dd3a48600ddf4cc9d243006f7a554e9218037dd2227490c013fe62d3a486009ff2f69d243004ff96b4e9218027fcada7490c013fe52d3a486009ff1169d243004ff85b4e9218023fe5ca7490c013fe2e53a486009ff174c3a43004ff8ba615218027fc5d2ca90c013fe2e984486009ff174aa243004ff8ba60d218027fc5d2e690c013fe2e963486009ff174a9a43004ff8ba609218035fc4530490c017fc2c58248600bfd576b1243006feaaa58921803df5442c490c01f7a9dd6248600fed4aab1243007faa44589218037f4c52c490c01fba5d96248600fdd2cab1243007ee96358921802bf65cac490c017fa2e562486009ff174a9243006f785a54921802ff858aa490c017fc2c542486009ff17499243006fd83a4c921802ff858a6490c013fe6e981486009ff174c0a43006bf88a60521802ff45930290c017fcaed7148600dfe554b8a43007bf2885c521803f79332e290c01fdc9557148600ff6488b8a43007fd2335c5218037f8ad2e290c01f7c61d7148600fbe2ecb8a43007fe1625c5218027fcdd2a290c013fe2e95148600def0b4a8a43005fe8b254521802ff95da6290c01bfcaa93148600f7e51098a43007df2774c521803f793326290c01fdc9553148600ff648898a43005ff17b4c5218027fcdd26290c01bfc6293148600dfe29498a43007fd1634c521803ff0b126290c01ff44c93148600dfe17498a43005ff0ba4c5218027fc5d26290c013fd2e93148600ffa07498a43006fd83a4c521803bea1ca6290c01df90a53148600ffc16498a43005fe8b24c5218035fcc511490c01bde5685a48600dfb2741d2430063fe882a5218035fd4415290c01b7e9dca948600ddf4cc54a4300677e552a5218037bd2a95290c019f78cca948600dfb46654a430047fd8b2a5218027fcc595290c013fe5eca9486009ff2d654a430047fd5b2a5218027fcad95290c011ff4eca9486009ff27654a43004ff88b2a52))) else (if i < 7 then (if i < 6 then 0xa63005fd8b35c5318027fcdd2a298c013fe2e9514c600def0b4a8a63005fd8b3545318037f95528298c01efca21414c600fbe4eea0a63007ef26650531803fb92aa8298c01ff8889414c600ffa2c6a0a63007fd13250531802efcbd91498c017ee52c8a4c600d7f31445263006f795a169318023ff5d95298c018ffa20a94c600d7f51054a630065fe772a5318036fd3b95298c019bf998a94c600ddf4cc54a6300677e552a5318037bd2a95298c019fb888a94c600dfd44454a630047fd8b2a5318027fcc595298c011ff5eca94c6009ff2f654a630047fd6b2a5318027fcb595298c011ff56ca94c6009ff2b654a630047fd2b2a5318027fc9595298c011ff22ca94c6009ff11654a630047fc5b2a5318027fc2d95298c011ff0aca94c6009ff05654a63004ff9ab22531802fdca591298c017fc46c894c600f7e30244a63004ff9ab165318037ed5507298c01ef6a20394c600fbb4ee1ca63007eda660e531803fad2a87298c01ff2888394c600bfb2d61ca63005fd92b0e5318037ecad07298c01ff4604394c6009ff35614a63005fb94b0a531802fec9d85298c017fc46c294c600bbf2f642a63005ef96b215318027fcdd10a98c015fe6e4854c600bf736842a63005fd9b321531802ff4d910a98c017fc6c4854c600b7f31651263005df97b28931802f7cb594498c017de56ca24c600bf7296512630057f9b9289318037f4d114498c013fe6ac824c600bfb27641263005ff1b1209318027fcd58a498c017be5ac524c600bf729629263005fd93b14931802ff8d88a498c01afea22aa48600dbf4ef55243006efa66aa9218037bd2ad5490c01bee912aa48600dfb46755243004ff98baa9218027fcbdd5490c013fe5aeaa486009ff2b755243004ff94baa9218027fc9dd5490c013fe42eaa486008ff93755243004ff88baa9218027fc2dd5490c013fe0eeaa48600cfd85355243004ff8aba21218035fc55d1090c01afe16a8848600d7f075442430073ec29a2121803cfd444ee90c01b7e22a7748600dbf0753ba430065fca99dd21803d7d444cc90c01f3e9de6648600ddf0b533243006ef83a9992180337e54ccc90c01dbb0a66648600f6f5112aa43007d7a7795521803f3d334aa90c013fe2ae5548600def1572aa43006f788a955218037bc1d4aa90c01ddb0a65548600f7751122243007dba7791121803f5d3348890c01fce9564448600df711522243006fb85a91121803f6d3346690c01fd69563348600ff348919a43006fd94a8cd218037ec2d46690c01df30a633486009ff576c5243006dfa776292180377d3331490c01bde9558a48600df7488c5243004ff9b4629218023fe5cb1490c013fe2e58a48600ddf16cc5243005ef8b66292180277e5b31490c013fe2d58a486009ff166c5243004ffabb5e9218035fd442f490c01bb else 0xedd3bc8898c01fae99a444c600fe74ab22263006fb88a911318037dc2d48898c01bee28a444c600dfd55511263007bea8888931803ef53bc4498c01fba99a224c600fed4ab11263007faa44889318037f4bd44498c01bfa5aa224c600dfd2b511263006fe94a88931803fe4b1c4498c013fe2ae224c600dfd15711263005fd83b88931803fe41dc4498c017fc06e224c600ffc03711263006fe88a889318037f42d44498c01df30e6224c6009ff576c5263006dfa776293180377d3331498c01bee9118a4c6009ff368c52630047fcb9629318027fc5cb1498c01bbe2d98a4c600bdf16cc5263004efcb6629318027fc5ab1498c013fe2c98a4c6009ff576bd263006bfa885e93180377d332f498c01bde9557a4c600df7488bd263004ff98b5e9318036fcc3af498c013fe6d17a4c6009ff116bd2630047fcb95e9318027fc5caf498c01bfa2c97a4c600bfd164bd263004fecb25e9318027fd5dad498c01b7e9dd6a4c600def4aab5263006fba445a9318027fcc5ad498c013fe5ed6a4c6009ff368b52630047fcb95a9318027fc5cad498c013fe2d56a4c6009ff164b5263004ffabb5693180377d332b498c01bee9115a4c6009ff2d6ad263004ff9b4569318023fe5cab498c013fe2e55a4c600cfb872ad263004ff8b2569318035fd4429498c01b7e9dd4a4c600ddf4cca5263006f7a55529318027fc45a9498c013fe16d4a4c6009ff164a5263004ff8ba61d318027fc5d2ca98c013fe2e9844c6009ff174aa263004ff8ba60d318035fc4530698c017fc2c5834c600bfe162b9a63005fdabb58d318037ed552c698c01f769dd634c600feb4aab1a63007f9a4458d318037ecc52c698c01fb6619634c600fdb2c8b1a630057dcb958d31802fec5cac698c013fe2e9534c600bfe162a9a63006bf98a609318027fc5d30498c01b7e5e9724c600ddf2d4b1263007ed963589318027fc5d2c498c0177e1ed524c6009ff174a9263006fe8a2549318027fc5d28498c017f6aed324c600dfb55499263007dda774c931803f6d3326498c01fd6955324c600ff348899263005fd96b4c9318037ecbd26498c01ff2609324c600ff928499263006fd8ba4c931802fec5d26498c013fe2e9324c6009fb974992630057dcb94c931802fec5ca6498c01ff2289324c600dfd14499263007fd0b14c931802ff858a6498c017fcaed814c600dfe554c0a63007df27760531803f793330298c01fdc955814c600ff6488c0a63007fe222605318027fcdd30298c01bfc5a9814c600dfe2b4c0a63007bf18660531802ff8da30298c01ff458d814c600f7e304c0a63007fd132605318037f85d30298c017fc2e9814c6009ff174c0a63004ff4ba60531803df84530298c01afe229814c600e7e912c0a630077d43960531803f785b30298c01ff42cd814c600bfb166c0) else (if i < 8 then 0xa9546009ff07654aa30047fc2b2a5518027fc15952a8c013fe6ac39546009ff35614aa3005f795b0a551802fdca5852a8c01fda5482954600dfe5540caa3007df27706551803fe919832a8c017fc62c1954600bfe2f60caa3007f7152065518037ecd1946a8c017be5aca254600bf7296512a3006fe9a2289518027fcd5904a8c017fc6c482546009ff356192a3005bf98b0c951802efcbd864a8c017be5ac3254600bef2b6192a3005fb94b0c951802bfcdc864a8c017fc6c43254600d7f51155283006dfa77aa9418037bd2ad54a0c013fe2ae8850600d7f15744283006bf85aa21418035fc51510a0c01e7ea227750600dbf1153ba83007afa8899941803e7d3bccca0c01edea225550600faf4ef2aa83007e7a66955418027fc55caaa0c01bde2ae5550600def1152aa83006f78a295541803ded44466a0c01f769de3350600fdb4cd19a83007f5a558cd418037ec45466a0c01bf616a3350600dfb14519a83006feaaa88941803df544444a0c01f7a9de2250600fdd4cd11283007f6a5588941803fe519c44a0c01bfa62a2250600dfd2f511283006fe96a88941803fd4c2444a0c01fea59222506009ff15711283006fe8ab889418037f445444a0c01bfa16a2250600dbf4eec5283006efa66629418037bd2ab14a0c013fe2d58a506009ff164c5283006bfa885e94180377d332f4a0c01bde9557a506009ff116bd283006bfa885a9418036fd3bad4a0c01bde9556a50600ddf4ccad283004ff8b2569418027fcdd30ea0c013fe2e987506009ff374c3283005fb9b4619418027fcdd2eca0c013fe6e96550600fb74eec2283007eba6661141803f9d2ab08a0c01eeea216450600fb74eeb2283007f3a55591418027fc5d306a0c013fe2e97350600bf7368c1283004ff8ba60941802fdcda2c4a0c0177e1ed52506009ff174a9283007bba8850941803edd3ba84a0c01fae9994250600fe74aaa1283004ff8ab4c941802efcbd90aa0c017be5ac85506009ff37442a83005fb9b421541802fecd990aa0c017fa6c88550600bfe36242a83004ff9ab20941802fdca5904a0c013fe6ac5250600bdf2d629283005fb94b149418035fd4455498c01b7e9deaa4c600ddf4cd55263006f7a55aa9318037dd2255498c013fe62eaa4c6009ff2f755263004ff96baa9318027fcadd5498c013fe52eaa4c6009ff25755263004ff90baa9318023fe4dd5498c013fe22eaa4c6009ff0b755263004ff82baa9318033ee1cd5498c01afe16a884c600e7b87344263006bf8a2a2131803cfd444ee98c01b7e22a774c600ebb8733ba63007cfa779993180377c2d4cc98c01db70e6664c600ddf14533263007b7a8895531803ebd3bcaa98c01f9e99a554c6009ff1572aa63006f78ab955318037bc454aa98c01dd70e6554c600def1452aa63007bba8891131803 else (if i < 9 then 0x7f3a55911618037dcc5488b0c01bee5ea4458600f7b51119ac3007dda778cd61803fad2ac66b0c01fe69123358600dfb31519ac3006fd97a8cd618037ecd2466b0c01efaa222258600ff5489112c3007fca33889618037f4c5444b0c013feaed8a58600dbf4eec52c30047fcb9629618027fc5cb14b0c013fe2d58a586009ff166c52c3004ff8b2629618027fd5daf4b0c01afea217a586009ff316bd2c3006df9875e9618023fe5caf4b0c013fe2e57a586009ff166bd2c3006fb9a461161802f7d5dac4b0c01ebea216258600f9f4eeb12c3007e7a5558961803f5d222c4b0c01fb68cd6258600ddf2f4b12c3007ee98258961802b7e5cac4b0c017be2e56258600bbf0f6a92c3005ff2bb60561803ef93bb02b0c01fdc9558158600ff6488c0ac3007fd23360561803ff111302b0c01efc6098158600fde2c4c0ac3004ff9ab165618027fcd5872b0c013fe6ac2958600bdf2d614ac3005fb94b0a5618027fcd58a6b0c013fe6ac5258600bdf2d6292c3005fb94b149618027fcd5864b0c016fe62c3258600bbf2f6192c3005ef96b0c961802fbcad864b0c017ee52c3258600aff372192c3005ff1b10c96180377d33554a8c013fe5aeaa546009ff297552a3004ff93baa9518027fc95d54a8c013fe42eaa546009ff077552a3004ff82baa9518033fa0cd54a8c01f3e9de6654600ecf8b3332a3006ef8a39995180377c514cca8c01beeaaa4454600fd74cd222a3006fb96a911518037dc51488a8c01bf6aaa3354600fdb4cd19aa3007f9a448cd518037ecb5466a8c01bf669233546009ff15719aa3006fd8ab8cd51803bea0cc66a8c01bf628a33546009ff576b52a3006dfa775a9518027fcbdad4a8c011ff2e56a546009ff172b52a3004ff8b35a9518027fc592d4a8c015fe2e5a4546009ff174b1aa3005df87b689518027fc5d304a8c01bbe5a962546009ff174b12a3006fb9a4509518027fc55a84a8c013fe2ad3254600bfe576c0aa3006ff2aa60551803ef93bb02a8c01fbc9998154600ff6488c0aa3007fd233605518037f8b5302a8c01efc6198154600f7e304c0aa3007f7152605518037f85d302a8c017fc2e981546009ff174c0aa3004ff4ba60551803df845302a8c01afe2298154600afe972c0aa3005ff0b9605518039fa44b02a8c01ddd1658154600fde16cc0aa3007f70b560551802fbc5ab02a8c017fcaed7154600dfe554b8aa3007ef2665c551803fd9222e2a8c01ff48cd7154600bfe316b8aa3007df1875c551803ef8bb2e2a8c01fdc5957154600fbe2e4b8aa3007f71525c551802bfa5cae2a8c017fc2e571546008ffd7654aa30066fe662a55180377d33152a8c019f78cca954600dfb46654aa30047fd6b2a5518027fcb5952a8c011ff4eca9546009ff27654aa30047fd2b2a5518027fc95952a8c011ff0ec else 0x394cc0c019bf2a4a660600def34a52b03006ef8a6295818037ecd1946c0c01bbe298a3606009ff35629b03005ff1b114d8180377c530a6c0c01bfa688a260600ddf14c51303004ff9ab14981802dfcc58a4c0c017be5ac5260600bf729629303005ff1b11498180377c530a4c0c013fe6ac3260600b7f31619303005df97b0c981802f7cb5864c0c017de56c3260600bf7296193030057f9b90c981802ff8d8864c0c01bbe2983260600d7f511552e3004ff98baa9718027fcb5d54b8c013fe56eaa5c6009ff297552e3004ff93baa9718027fc95d54b8c013fe42eaa5c6008ff937552e3004ff88baa9718027fc1dd54b8c013fe2ae885c600d7f157442e3006bf8a3a217180377d554ccb8c01ebea22665c600ddf315332e3007cf9879997180337e54cccb8c01bbe28e665c600def5552aae3007b7a8895571803f3d334aab8c01f5e5da555c600def1152aae3006f78a3955718037dd55488b8c01eeea22445c600fd74cd222e3007f3a55911718037dcc5488b8c01f6e61e445c600fb72ed222e3006fb88a911718037ed55466b8c01ef6a22335c600fdb4cd19ae3007f5a558cd71803fcd22466b8c01bf662a335c600fbb30f19ae3007dd9768cd718037ecd2466b8c013fe2ae335c600dfb15719ae3006fd88a8cd718027fd5db14b8c011ff2e58a5c6009ff172c52e3006ef8b662971802f7c5b314b8c013bf2d98a5c6009ff166c52e3005dfabb61d718036fd5530eb8c01b7e2e9875c600bbf174c3ae3004dfcba61d71803cfc4530eb8c0157f2e5875c600bbf172c3ae3007df0b161d718036fd552ecb8c01e7ea21765c600bbf316bb2e3006df98a5d971803e7cbb2cab8c013fe2ad655c6009ff174c22e3005fe8b268d718027fc5d306b8c013fe2ad635c600d7f314c12e30079f987609718027fc5d304b8c01b7eaa9725c600f3f510b92e3007cfa665c971803ebd2aae4b8c01f6e911725c600bbf316b92e3005df97b58971803e7cbb2c4b8c013fe2ad625c600fbd2e4a92e3004ff8ab549718037dcd2284b8c013fe2ad425c6009ff156992e3006bf88a605718035fcc5114b8c018ffa20a95c600d7f51054ae3006efa662a5718033bf2a952b8c01bde954a95c600cfbc6654ae3006fda332a5718023fec5952b8c013fe62ca95c6009ff2d654ae30047fd5b2a5718027fcad952b8c011ff4eca95c6009ff27654ae3004ff92b2a5718027fc45952b8c013fe0eca95c6009ff35644ae3005df97b22571802fdca5912b8c017fc46c895c6009ff3561cae3006fd9a328d718027fcd5906b8c0177e5ec835c600bdf2d641ae3005f795b20d71802fdca5906b8c015fe6e4835c600bfd36441ae3005ff1b120d71803cfd444eeb0c01edea225558600faf4ef2aac3006f798a955618037bcbd4aab0c01eeea224458600fb74ef222c30)))) else (if i < 15 then (if i < 12 then (if i < 11 then 0xa00bfd25640a65004ff9ab14532802fec9d8a2994013fe5eeaa60600bdf2d755303004ff96baa98180277eb5d54c0c01bbe5aeaa606009ff2b755303004ff94baa9818027fc9dd54c0c013fe4aeaa606009ff21755303004ff85baa9818027fc1dd54c0c013fe0aeaa60600c7f91355303006dfaaa9dd818038fe44ceec0c01b3f29a7760600dbf1473bb03006efaaa99981803e7d3bcccc0c017be2ae66606009df957333030066fca99998180377c52cccc0c01bbe28e6660600ddf14533303006f7aaa95581803f3d334aac0c01cdf2265560600fcf14d2ab03006e7ca6955818037bc514aac0c01beeaaa4460600fb74ef22303007eba6691181803f9d2ac88c0c01eee61a4460600fd714d22303006fb8a5911818037dc51488c0c01bf6aaa3360600fbb4ef19b03007eda668cd81803fcd22466c0c01bf66923360600e7b91319b03007ed8a68cd8180376e53466c0c01bf628a3360600dfd55511303007eea6688981803fd522444c0c01ff28ce2260600f7d30d113030073ec8988981803f7453444c0c01bbb29a2260600dfd14711303005ef8b669d81802ff858b0ec0c01afeaa98660600f3f4eec3303005ef8b66958180377c5334ac0c017be2d9a460600ddf14cd2303005ff0b16118180377c532e8c0c01bee6916460600bdf16cd1b03006ef8a668d818027fc5d306c0c01bf628d8360600bfe162c1b03004ff8ab5cd8180377c532e6c0c01ebe61963606009ff156b1b03006ef8a650d81802f7c5b344c0c01bbe299a260600b7f576c1303006bfaaa60981803cfd3bb04c0c01ebe9998260600f77488c1303006bf8ba60981802dfc5d304c0c013fe2e9826060097f974c13030053fcb960981802dfc5cb04c0c01ebe2998260600f7d144c1303006fe8a260981803df858b04c0c017fc2c58260600ddf14cb9303005bf98b58981803df4c12c4c0c013fe2ad6260600f7d304a9303004ff8ab54981802efc3daa4c0c013fe2ad4260600ddf14ca1303007be9824c9818027fc55a64c0c01bbe2993260600bdf16cd0303006ef8a6681818032ff3b952c0c01b7e9dca960600ddf4cc54b0300677e552a5818037bd2a952c0c019f78cca960600dfb46654b030067ee222a5818037f511152c0c011ff5eca9606009ff2f654b03004ff96b2a5818023fead952c0c013fe56ca9606008ffa7654b03004ff93b2a5818023fe95952c0c013fe4aca9606009ff0b654b03004ff83b2a5818027fc15952c0c01bbe298a960600d7f55444b030079fa7722581803dbd2a912c0c01ef68cc8960600f7d44444b03005bf92b225818027fcd58b2c0c017fc46c5960600ddf14c2cb03004ff9ab0e581802ff88d872c0c01bbe29839606009ff35614b03005bf98b0a581802fdca5852c0c01bbe2982960600ddf55453303007cfa772998180377cd else 0x9ba5d942803ddd442e8a1401fae9997450a00fe74aaba285004ff8ba5cd428027fc5d2c6a1401f6e9dd4350a00fd74cca1a85007f3a5550d428035fc45304a140177e5ec8550a00bdf2d642a85004ff9ba21542802fdcda10aa14017f66cc8550a00bfd36442a85005ff1b1215428027fcd5902a140177e5ec8150a00bf729640a85004ff9ab14542802fdca58a2a1401b7e9deaa4ca00ddf4cd55265006f7a55aa9328037dd22554994013fe62eaa4ca009ff2f755265004ff96baa9328027fcadd54994013fe52eaa4ca009ff23755265004ff90baa9328027fc45d54994013fe16eaa4ca009ff03755265006df88a9dd328032fe54cee99401b7e286774ca00f9f4ef33265006ef85a99932803f3d334aa99401bde286554ca00fb74ef22265007eba6691132803f9d2ac8899401bee22a444ca00df70b522265006fb8a1911328027fd5db1499401bbe9998a4ca00df7488c5265004ff9b4629328023fe5cb14994013fe2e58a4ca009ff162c5265004ffabb5e93280377d332f499401bee9117a4ca009ff368bd265004ff88b5e9328023fe5caf4994013fe2e57a4ca009ff162bd265004ffabb5a9328036fd3bad499401bde9556a4ca00df7488b5265004ff98b5a9328027fcbdad4994013fe6d16a4ca008ff972b5265004ff8b95a9328027fc5aad49940177e1ed5a4ca00dbf4eea5265006efa66529328037bd2aa94994013fe22d4a4ca009ff0b6a5265004ff8b1529328027fc5d30e994013fe2e9844ca009ff174c1a65005fe8b260d32802fed5dae699401bf6aa9734ca00fdb4ccb9a65007f9a445cd32803eecc3ae699401f765d1734ca00bfd164b1a65005feabb609328037f55530499401f7a9dd824ca00fdd4ccc1265007faa44609328027fcdd30499401bfa5a9824ca00f7d30ec1265005fe9b460932803df4c1b0499401ff25cd824ca00dfd174c1265005fe8ba609328027fc5d304994013fb2e9824ca00f7d114c1265006bf88a60932803fe459b04994017f62cd824ca00bfb166b1265006feaaa50932803ef53ba8499401fba999424ca00fed4aaa1265007fc973509328035fcc511499401bde5685a4ca00dbf4ee54a650066fe662a53280377d33152994019df954a94ca00def4aa54a650047fd8b2a5328027fcc5952994013fe5eca94ca008ffad654a65004ff96b2a5328023fead952994013fe56ca94ca008ffa3654a65004ff91b2a5328027fc45952994013fe16ca94ca009ff03654a65004ff9ab22532802fdca5912994017fa4ac894ca009ff3562ca65004ff9ab06532802fec9d8329940177e5ec854ca00bdf2d642a65004ff9ba21532802bfcdc90a994017ee6d0854ca00bfb36642a65005fe9b221532802ff8d890a99401bfc684a14ca009ff35640a65005df97b20532802fdca5902994017f64ec814c) else (if i < 13 then 0xb9401f9e99a555ca00f77511222e5007eba6691172803f9d2ac88b940177eaed735ca00f9f4ccb9ae5007dba445cd728036fcd22e6b94013fe6ac895ca00bf729644ae5004ff9ab0e572802efcbd872b94013fe6ac195ca00bbf2f60cae5004ff9ab20d72802efcbd906b94017be5ac835ca00bef2b641ae5005fb94b20d72802bfcdc906b94017fa6c8835ca00bfe36241ae5004ff9ab20572802efcbd902b94017ee52c815ca009ff35618ae5005df97b0c5728036fd3bd54b14013fe62eaa58a009ff2f7552c5004ff95baa9628027fca5d54b14013fe4eeaa58a009ff237552c5004ff90baa9628023fe4dd54b14013fe16eaa58a009ff077552c50065fca99dd628036fc51ceeb1401bdeaaa5558a00faf4ef2aac5006f797a95562803f3cbb4aab14013fe2ae5558a00def1572aac5006f78a3955628037dd55488b1401f6e9de4458a00fe74ab222c5006fb98a911628037dcbd488b1401fae5da4458a00df714b222c5004ffabb629628036fd3bb14b14011ff2e58a58a009ff172c52c5004ff8b5629628027fc59b14b14013feaed7a58a009ff316bd2c50047fcb95e9628027fc5caf4b14013fe2cd7a58a009ff174c3ac5006efaaa5d962803e7cc3aecb140177e1eda558a009ff174b9ac5005efabb58d6280377d552c6b1401f3e9dd6358a00fcf4aab1ac5007eba4458d62802f7cbdac6b1401bbe6296358a00ddf348b1ac5006ef8ba58d62802f7c5d2c6b14013bf2e96358a00fdb146b1ac5006edca358d62803f74592c6b14017faaed8258a00dfd554c12c5007dea7760962803fd522304b1401efa61d8258a00fdd2ecc12c5007ee96360962802ff858b40b1401b7e9dca958a00cefcaa54ac5006f7a552a5628023fec5952b14013fe62ca958a009ff2f654ac50047fd5b2a5628027fcad952b14011ff4eca958a009ff27654ac5004ff91b2a56280337eb1952b1401bbe58ca958a009ff0b654ac5004ff83b2a5628027fcd58b2b14017be5ac5958a009ff3561cac5005ef96b0e5628037bcd294ab1401bf668ca358a009ff35629ac5005ef96b14d628035fd44554a1401b7e9deaa50a00ddf4cd55285006f7a55aa9428027fcc5d54a14013fe5eeaa50a009ff2d755285004ff95baa9428027fc8dd54a14013fe2ae8850a00d7f15744285006bf85aa21428035fc50d10a1401e7ea227750a00dbf1153ba85006df8a19dd42803d7d444cca1401f3e9de6650a00ddf0b533285007b7a8895542803ebd3bcaaa1401f9e99a5550a009ff1572aa85006f78ab955428037bc454aaa1401bde2865550a00ddf4ccc5285004ff8b1629428035fd442f4a1401bbe9997a50a00def4aabd285004ff88b5e9428027fc58af4a1401afea216a50a00dbf4eeb5285006f7a555a9428027fc5aad4a14013fe2e98750a009ff374c3285004ff else (if i < 14 then 0xff95229a430077ec2914d21803f7cb1aa4b0401fde54d5258200fdf2ca992c1006ff95a589308037fcbd302984017fe62d714c200fbf30eb8a61007fd9874c5308037fca9ad490401bfe5696348200bff2d6a9a41007fe963549208037fcc1af488401f7e61d7344200ff348919aed006fd9a48cd768027fcd5872bb401e7ea227759200f6f5112aac9007d7a7795564803eed3bc66b2401efaa222259200fbd4ef112c9007f6a5588964803fe519c44b2401bfa5ea2259200fbe4ef08ac9007fd23384564803ff111422b2401bfc5ea11592009ff356292c9005ef96b14964802fdca58a4b2401b7e9deaa58e009ff317552c7004ff97baa9638027fcadd54b1c013fe52eaa58e009ff257552c7004ff91baa9638027fc85d54b1c011ff26eaa58e009ff0b7552c7004ff82baa9638037dd55488b1c01f6e9de4458e00df72f5222c7006fb8a5911638037dc51488b1c013feaed7a58e008ff972bd2c7004ff8b95e963802dfc45b4ab1c01bbeaa96458e00f9f4eeb22c70047febb2a5638032ff3b952b1c01b7e9dca958e008ffb1654ac7004ff98b2a5638023febd952b1c013fe5eca958e008ffab654ac7004ff95b2a5638023fe95952b1c013fe4aca958e008ffa3654ac7004ff91b2a5638023fe2d952b1c013fe16ca958e008ff85654ac7004ff82b2a5638027fcd58b2b1c013fe6ac2958e00bdf2d614ac7005fb94b0a5638037bcd294ab1c01bfa688a258e009ff356292c7005ef96b14963802fdca58a4b1c01f3e9de6650e00dbf4eeb5287004ff8b55a9438027fc592d4a1c013fe6e97650e009ff35641287005fb94b209438027fcd5902a1c0177e5ec8150e00bf729640a87004ff9ab145438027fcd5842a1c016fe62c2150e00bbf2f610a87005ef96b08543802fbcad842a1c017ee52c2150e00bfb27610a87004ff96baa9828027fca5d54c14013fe4eeaa60a009ff23755305004ff90baa9828023fe4dd54c14013fe0eeaa60a009ff03755305006efaaa99982803e7d3bcccc1401bbe2966660a00ddf14733305006fbaaa91182803f5d33488c1401bee2864460a00bfb166d2305004ff8ab58d828037dcd2286c14017be2d9a160a008ffd7654b050066fe662a58280377d33152c14011ff5aca960a009ff2d654b050057bd4b2a582802fdca5952c14019ef52ca960a00df729654b050047fd3b2a5828027fc9d952c14011ff46ca960a009ff23654b050047fc3b2a5828027fc1d952c14011ff06ca960a009ff03654b05004ff9ab0e582802ff495872c14013fe6ac1960a00b7f3160cb05005ef96b28d82802fdca5946c14015fe6e4a360a00dfb34651b05005ff1b128d82802efcbd942c14017ee52ca160a00dfe34250b05004ff9ab14582802ff4958a2c14013fe6ac3160a00b7f31618b05005fe92b0c582803dbd444aa else 0x5521802bfe4dcaa90c01dfb0a655486009ff95719a430057fc9b8cd21802ffa0dc6690c013ffaed8a48600cff972c52430057fcb9629218033fe54b1490c019ff1658a48600cff872c52430077ec296292180377e5b31490c017bf2d98a486009ff96ac5243004ffcb3629218027ff5daf490c013ff62d7a486009ff916bd2430067fc895e9218033fe1caf490c013ff2cd7a486009ffd76b5243004ffd8b5a9218027febdad490c019ff1656a48600cff872b5243004ffcb55a9218027fe59ad490c013ffaed5a486009ffb16ad243004ffd7b569218027feb5ab490c013ff22d5a48600dbf8f6ad243005dfc7b569218033fe5cab490c015ff2e55a48600cff952ad2430067fc89569218033fe1cab490c01dfb0a55a486009ff966ad243004ffebb4e9218027fec5a7490c013ff5ed3a486009ffad69d243004ffd5b4e9218027fe45a7490c013ff16d3a48600cff9729d2430057fcb94e9218033fe54a7490c019ff2253a48600cff8b29d2430077ec294e9218027fe5d30e90c015ff2e58748600cff952c3a430067fca961921803bf614b0c90c013ff2e98548600efd852c2a430067fca95d5218027fe5d2ca90c015ff2e56548600cff952b2a430077ec2959521802ffcc5aa890c01fee61154486009ff974c1a430057fcb960d21803bf614b0690c013ff2e97348600aff972b9a430067fca95cd218027fe5d2c690c015ff2e56348600cff952b1a430077ec2958d218027fe5d2a690c015ff2e55348600efb872a9a430077ec2954d21802bfe5cb0490c019ff2a58248600dfdb14b1243007eed7658921803f76b2ac490c01fbb58d6248600efd8b2b12430077ec3958921802bfe5caa490c019ff2a55248600aff972992430067fca94c9218027fedd30290c015ff2e58148600cff952c0a430073fc8960521803bf614b0290c01bfd5697148600fbeb0eb8a43007df5765c521803ff2b12e290c01dfd2257148600efe872b8a43004ffdba54521802bfe5caa290c019ff2a55148600eef8b2a8a430077ec2954521802ffabda6290c013ff6e93148600dfeb1498a43007fd5634c521803ff2b126290c01ff54c93148600dfe97498a430077f4b94c521802bfe5ca6290c01dfd2a53148600cff95298a430077f4894c521803bfa2ca6290c01df70e53148600efd85298a430067fe882a5218033ff2a95290c019ff614a948600cffb0654a430067fd532a5218033fe4295290c0177f5ec8548600bdfad642a43004ffdba21521802fdeda10a90c017f76cc8548600bfdb6442a43005ff5b121521802ffcd810a90c01dfb0a48548600bbfaf641a43005efd6b20d21802fbead90690c017ef52c83486009ffb7441a43005fedb220d21802ffad890690c017fe6c08348600cff95241a430077ec2920d218027fedd0a690c017fd6c45348600c))) else (if i < 18 then (if i < 16 then 0x13ff5ad5a4c600cff972ad2630057fcb956931803bee1cab498c019ff0a55a4c6009ff964ad263004ffcba61d31802bfe5cb0e98c01df70e5874c600efb872c32630077dc395d931803bee1caea98c013ff2e9654c600aff972b2a630077dc39595318027fe5d30698c015ff2e5834c600aff972b9a63006fdd8a58d31803f6ec32c698c01df72e5634c600aff972b1a630077dca958d318033fe54ac698c01df7165634c600efb852b1a63004ffcba54d31802bfe5cb4498c019ff2a5a24c600efb872d1263006bfd8a609318027fe5d30498c015ff2e5824c600efb872c1263006dfd7a5c931803bee1cae498c01bbf5a9624c600fdbac6b1263004ffcba58931802bfe5cac498c01df70e5624c600bbf8f6a9263004ffcba54931802bfe5caa498c01df70e5524c600efd852a9263006feca254931802feeb5a6498c01bf75e9324c600ff9b0499263006fdcba4c931802fee5d26498c013ff2e9324c600efb972992630057fcb94c931803bee54a6498c019ff2a5324c600efb912992630077dc594c9318027fedd30298c01bfd5a9814c600dfeab4c0a63007bf58660531803feab1b0298c01efd609814c600ffaa64c0a63006ff4ba60531802ffa5d30298c013ff2e9814c600efe972c0a630057fcb9605318039fe44b0298c01dfd165814c600efb872c0a630077f42960531803f7a5b30298c015ff2e5714c600efb872b8a63004ffdba54531802bfe5caa298c01ddf165514c600efb872a8a63005dfd7b22931802fdea591498c019ff2a48a4c600efb872452630067fca916931803bee1c8b498c019ffa20a94c600cffcaa54a630057fd8b2a5318033fec595298c015ff5eca94c600cffaf654a630057fd5b2a5318033fead95298c019ff628a94c600cffaf454a630067fd5a2a5318033fec395298c019ff618a94c600cffaec54a630067fd752a5318033feb295298c019ff60ca94c600cffae654a630067fd532a5318033fec115298c019ff5c8a94c600cffac454a630067fd522a531803bfac095298c019ff604a94c600cffae254a630067fd512a5318033fe4295298c0177f5ec854c600bdfad642a63004ffdba21531802fdeda10a98c017f76cc854c600bfdb6442a63005ff5b121531802ffcd810a98c01df70e4854c600b7fb1651263005dfd7b28931802f7eb594498c017df56ca24c600bf7a9651263005ff9b0289318033fe5494498c01df70e4a24c6009ffb5641263005fdd3b20931802ffad890498c019ff2a4824c600efb87241263004ffdab14931802f7eb58a498c017ef52c524c600bfba7629263005ff5b1149318033fe548a498c01df70e4524c6009ff91755243004ffc5baa9218027fe1dd5490c019ff226aa48600cff8b3552430067fc39aa9218027fe55d1090c015ff26e8848600efd85344243004ffcab9 else (if i < 17 then 0x319aa3004ffebb5a9518027febdad4a8c019ff2e56a54600aff972b52a300777c595a9518033fe1cad4a8c019ff0a56a546009ff966b52a3004ffcb25a951802bfe5cb46a8c01df70e5a354600efe832d1aa3004ffcba58d51802bfe5cac6a8c01ddf1656354600bbf8f6d12a30057fcb968951803bbe2cb44a8c01dfb0a5a254600efe832d12a3004ffcba60951802bfe5cb04a8c01dfd0658254600efe832b92a3006efd6a589518027fe5d2c4a8c015ff2e56254600eef8b2b12a3005ff98b509518027fe55a64a8c015ff2e53254600eef8b2992a30077f4194c9518037fab5302a8c01efd6198154600f7eb04c0aa3007f755260551803ff8a1302a8c01bfd2e98154600efe972c0aa30057fcb9605518039fe44b02a8c01ddf1658154600efe872c0aa30077f42960551803f7a5b302a8c017fd62d7154600fbeb0eb8aa3007df5765c551803fbab2ae2a8c01f7d5c97154600feeaa4b8aa30077f4b95c551802bfe5cae2a8c01dfd2257154600efe872b8aa30067fe332a551802bfeb5952a8c019ff5aca954600affa7654aa30067fd3b2a551802bfe95952a8c019ff4aca954600cffad454aa30067fd762a5518033fed1952a8c019ff58ca954600cffb4454aa30067fd822a5518033feb9152a8c019ff588a954600cffa6454aa30077f5812a5518033fec0952a8c01dfd5c4a954600cffae254aa30067fc822a5518033fe19152a8c013ff6ac8254600bfeb62412a30077f419209518027fed5864a8c016ff62c3254600bbfaf6192a3005efd6b0c951802fbead864a8c017ef52c3254600bfeb62192a3005ff9b00c951803bbe2c864a8c01dfd0643254600dff2b4c1283005ff98b549418037fcc52a4a0c01fee6115250600ffd304a9283004ffd8baa9318027febdd5498c013ff5aeaa4c6009ffab755263004ffd2baa931802bfe4dd5498c019ff26eaa4c6009ff91755263004ffc5baa9318027fe15d5498c019ff2a6aa4c600cff913552630067fc59aa931803bee1cd5498c019ff0a6aa4c600aff93744263005ff41ba21318027fe55caa98c015ff26e554c600efb8732aa63004ffcab88931802bfe4dc4498c017f70ee224c600bfe837112630067fca988931803bee1cc4498c013ffaed8a4c600cff972c52630057fcb9629318033fe2cb1498c01df70e58a4c600cff852c5263006efcb662931802f7e5b31498c013ff2d58a4c6009ff964c5263004ffebb5e9318027fec5af498c01b7f61d7a4c6009ff916bd2630067fcb95e931802bfe5caf498c019ff2257a4c600efb872bd263006fecb25e931802ff6592f498c013ffaed6a4c6009ffb16b5263004ffd7b5a9318033fe5cad498c015ff2e56a4c600cff952b52630067fc595a931803bee1cad498c019ff0a56a4c6009ff96ab5263004ffcb25a9318027ff5dab498c0 else 0x8039fe448a6c0c01bbf2985360600ddf94c51303004ffdab14981802dfec58a4c0c017bf5ac5260600bf7a9629303005ff5b1149818039fe448a4c0c01bbf29852606009ffb5619303005bfd8b0c981802efebd864c0c017bf5ac3260600befab619303005fbd4b0c981802ffad8864c0c017fe6c03260600e7f91219303006efca60c9818027fec5d54b8c013ff5aeaa5c6009ffab7552e3004ffd3baa9718027fe95d54b8c013ff22eaa5c6009ff877552e30067fc89aa9718033fe1cd54b8c013ff2ae885c600aff937442e3004ffcab8cd71802bfe4dc66b8c013ffaed8a5c600cff972c52e30057fcb9629718033fe54b14b8c019ff0e58a5c600ddf96cc52e3005efcb6629718027fe59b14b8c0177faed875c600dbfd54c3ae30079fe8861d718036fe5d30eb8c0177f2e9875c600f3f914c3ae30075fcb961d71803afe54b0eb8c01d7f0e5875c600fbe962c3ae30067fca9619718036ff552ecb8c0177f62d765c600dbfb14bb2e30075fc395d971802bfe5cb4ab8c019ff2a5a55c600f9faecb2ae3004ffcab59571802bfe5cacab8c015ff2e5a35c600cff952d1ae3005fecb268d718027fe5d306b8c015ff2e5835c6009ff956b1ae30057fcb958d718033fe54ac6b8c01aff629825c600f3fb0ec12e3004ffcba60971802bfe5cb04b8c019ff2a5825c600bbfb16b92e30075fc895c971803afe1cae4b8c0177f5ed625c600f9faecb12e3004ffcab58971803ef6b92a4b8c013ff2ad525c600cff952a92e3004ffcab4c971802bfe5ca64b8c019ff2a5325c600aff972c0ae30067fca9605718039fe44b02b8c019ffa20a95c600cffc6654ae30067fd832a5718033fe41952b8c013ff6ac835c600bbfaf641ae3005efd6b20d71802fbead906b8c017ef52c835c600bfdb6441ae3005ff5b120d71802ffcd8106b8c015ff26e5558600aff93719ac30057fc9b889618027ff5db14b0c019ff1658a58600cff872c52c30067fc29629618027fe5ab14b0c013ff2cd8a586009ff964c52c3004ffebb5e9618027fec5af4b0c01b7f61d7a58600cff872bd2c3004ffcb35e961802bfe5cb0eb0c015ff2e58358600aff972b9ac30057fcb960961802f7f5dac4b0c01bbf5e96258600fddb04b12c30076fc5958961803b7e1cac4b0c0177f1ed5258600aff972a92c30077ec2954961802bfe5ca64b0c01efd6098158600fdeac4c0ac30077f45960561803bfa1cb02b0c01dfd0a581586009ffb5629ac3004ffdab14961802f7eb58a4b0c017ef52c52586009ffb56192c3005bfd8b0c961802efebd864b0c017bf5ac3258600befab6192c3005fbd4b0c961802ffad8864b0c017fe6c03258600defacb552a3006f7d52aa9518027fe1dd54a8c013ff0aeaa54600cff873552a30067fc29aa9518027fe55c66a8c015ff26e3354600efe83)) else (if i < 19 then 0x1ed5a4ca00aff972ad2650067fca9569328027fe5d30e994015ff2e5874ca00cff952c3a650067fca95d9328027fe5d306994019ff2a5834ca00fbbb0eb9a650077dc895cd32803bee0cae6994015ff2e5634ca00cff952b1a65004ffdba609328037f6b530499401efb61d824ca00f7db06c1265007fcd73609328037f65d304994017fb2e9824ca009ff974c12650077ecb960932802bfe5cb0499401dfb2a5824ca00cff952c12650077ec5960932803bf60cb04994015ff2e5624ca00cff952b1265005fdcb358932802bfe5cb42994019ff2a5a14ca00cffcaa54a650067fd862a532802efebd90a994017bf5ac854ca009ffb7442a65005fbdb421532802feed990a994017fb6c8854ca00bfeb6242a65005ff9b0215328033fe5490a994013ff6ac814ca00bbfaf640a65005fbd4b20532802fee9d902994017fb4ac814ca00cff95240a65004ffdab14532802fee9d8a2994019ff2a4514ca009ffaf755303005efd6baa9818027feb5d54c0c01bbf5aeaa606009ffab755303004ffd3baa9818027fe95d54c0c015ff26eaa60600cff93755303004ffc5baa9818027fe1dd54c0c013ff0aeaa60600cff8b3553030067fc39aa9818033fe14d54c0c015ff26e5560600bfe8372ab03006efca695581802bfe4dc66c0c017fd06e3360600ddf94d19b030057fc9b88981802dfe45c44c0c01bbf29a2260600aff972d3b030067fca969d818039fe44b4ec0c017bf2d9a760600aff972c3b030067fca961d818039fe2cb0cc0c01cff0e58660600e7f852c33030057fcb9695818033fe54b4ac0c01cff225a560600bdf96cd2b03006efca669581802bfe5cb46c0c019ff2a5a360600e7f912d1b03005efcb668d8180377e53346c0c013ff2e98360600aff972c1b030067fca960d818027fe55ae6c0c015ff2e57360600e7f912b9b03006efca65cd81803d7ec32c6c0c013ff2ad6360600aff972b1b030057fcb9689818033fe54b44c0c01cff225a260600bdf96cd1303006efca6689818035fe5d304c0c016ff2e982606009ff974c13030073fcb960981802bfe5cb04c0c01cff2a58260600cff952c13030073fc59609818039fe1cb04c0c01ebf2998260600e7f912b9303006efca65c981802dfec5ac4c0c01efb60962606009ff956b13030057fcb958981803df6c12a4c0c013ff2ad5260600bbf8f6a93030077ec2954981803df6c1264c0c013ff2ad3260600aff972993030073fc894c98180377e53264c0c019ff954a960600cffc6654b030067fe222a5818033feb9952c0c019ff5c8a960600cffaa454b030067fd322a5818033fe29952c0c019ff148a960600cff86454b03006efeaa2998180377ed394cc0c01dbf164a660600edf872533030076fc292998180377e5314ac0c01bbf298a3606009ffb5629b03005ff5b114d81 else (if i < 20 then 0x5004ffd3baa9828027fe8dd54c1401aff61eaa60a00dfdaa5553050057fc9baa9828033fe4dd54c14013ff0eeaa60a009ff837553050067fca9aa9828033fe1cd54c14019ff066aa60a00aff972d33050057fcb968d828033fe54b46c14013ff2ad6360a00aff972b1b050057fcb968582802f7e5b342c14015ff5eca960a00cffaf654b050057fd1b2a5828033fe8d952c14019ff69ca960a00cffaec54b050067fd632a5828033fed0952c14019ff144a960a00bdfad651b05005fbd4b28d82802ffad8946c14017fe6c0a360a00cff95251b05005dfd7b28582802fdea5942c14019ff2a4a160a009ffb5628b05005fed2b145828027fed5862c14016ff62c3160a00bfda5618b050067fca90c582802bfe4dd10b9401d7f225735ca00ebf832b9ae50057fcb958d728027fed5906b940177f5ec835ca00bdfad641ae5005f7d5b20d72802fdea5906b94017fb6c8835ca00bfeb6241ae5005ff9b020d728027fed5902b940177f5ec815ca00bf7a9640ae5004ffdab0c572802efebd862b94013ff62eaa58a009ffaf7552c5004ffd5baa9628027fe9dd54b14013ff46eaa58a009ff8b7552c5004ffc3baa9628033fe2cd54b14019ff0e6aa58a00defb4b2aac5007e7d65955628027fe55caab14015ff26e5558a009ffd76c52c50067fcb962962802bfe5cb14b14019ff2a58a58a00cff8b2c52c50067fc39629628027fe5ab14b14013ff2cd8a58a009ffd76bd2c5004ffd8b5e9628033fe1caf4b14013ff2cd7a58a009ff974c3ac50067fca961d6280377f552ecb1401f3f61d7658a00edf872bb2c5005dfc7b69562802bfe5cb4ab14019ff2a5a558a00aff972d1ac50067fca968d628027fe5d2e6b14015ff2e57358a00cff952b9ac5006efeaa58d62802f7ebdac6b1401bbf6296358a00ddf974b1ac5005efcba58d62803b7e5cac6b1401dbf2a56358a00edf8b2b1ac5007edca358d62803f76592c6b1401efb61d8258a00fddaecc12c5007eed6360962803bf65cb04b14015ff2e58258a00efd952c12c50067fca960962803bf62cb04b1401dfb0e58258a00cffcaa54ac50067fc532a5628037bed294ab1401bf768ca358a009ffb5629ac5005efd6b14d628027fec5d54994013ff5eeaa4ca009ffad755265004ffd5baa9328027fe8dd54994015ff26eaa4ca00cff93755265004ffc8baa9328027fe2dd54994013ff06eaa4ca00cff913552650067fc59aa9328033fe0cd54994015ff26e554ca009ffd76c52650067fcb962932802bfe5cb14994019ff2a58a4ca00cff832c5265004ffcb1629328027ff5daf4994013ff22d7a4ca00cff912bd2650067fc195e9328027fe58af4994013ffaed6a4ca009ffb16b5265004ffd7b5a9328033fe5cad4994015ff2e56a4ca00cff952b52650067fc595a9328027fe5aad49940177f else 0x5c028e013700938045c020e00d60063002d8014c00960043001d800cc005600230008000200000bffaf6b1b05006ffda558d82803f7ec32c6b9401bff60d7a58a00dffaa6bd2c5006ffd8a5cd62803f7f2aac6b1401fbf61d6358a00ffdae6c12c5006ffd6a56932803efec3aec99401ff7619734ca00ffdaecc1265005ffebb5cd818037ff552e6c0c017ff62d7360600fbfb0eb9b03005ffdb65cd81803dfec32e6c0c01fbf2997360600f7fae6c1303007dfd735c981803bfe1caa4c0c01ff75cd3260600dffb1519ae3007dfd878cd71803bfe1cacab8c017ffaed835c600dffd54c1ae3006ffdba60d718037fec5306b8c01f7f61d835c600fbfaecc1ae3006ffd8a58d71803efec3ac6b8c01fbf619635c600ffbb06b1ae3007bfd8360971803efec1ae4b8c01bff629325c600fbfb0e992e3007fed824c971803bfe1caeab0c01f7f61d7358600eff872a92c3007ff57360561803bfe1caeca8c017ff5ed6354600dffaf4b1aa30077fc3960951803f7eb1ac4a8c01dff0e56254600dffad4992a3007fed824c951803ffab9b02a8c01ffd4c98154600ffeb06b8aa3007ff5635c5518037fec3d5498c01bff61d8a4c600dffd10bd263007dfd875e9318037fec32f498c01bff5957a4c600dffb0eb5263006ffd755a9318037fec3ab498c01bff5d95a4c600bffd76c3a63007dfd875d931803efec3aea98c01fbf5d9654c600dffaf4c1a63005ffd8b5cd318037fec52e698c01f7f61d734c600ffbb0eb1a63007fdd7558d318037febd30498c01bff569824c600f7fb0ec1263005ffd8b5c931803f7eb2ac498c017ff62d524c600bffad6a9263006ffd6a54931803feeb1aa498c01ffb609524c600ffbb0e99263007fdd654c931803ffac3b0298c01ffd5d9814c600ffeaeac0a63007ff57360531803ffaa930298c01f7f61d714c600eff872c2a430077fc3959521803efec3ae690c017ff5ad5348600ffbb06a9a43007fed5358921803ffac1ae290c01ffd61d3148600ffeb0a98a43007ff5654c521802bfe4dc66bb4013ff62eaa58e009ffaf7552c7004ffd5baa9638027fe95d54b1c013ff46eaa58e009ff8b7552c7004ffc2baa9638033fe54d54b1c019ff166aa58e00cff853552c70057fcb9629638027ff5daf4b1c019ff2e57a58e00aff972bd2c7005bfc8b69563802bfe5cb4ab1c015ff2e5a258e00aff972d0ac70067fca968563802bfec5952b1c019ff62ca958e00affaf654ac70067fd7b2a563802bfead952b1c019ff56ca958e00affa5654ac70067fd2b2a5638033fec5152b1c019ff5e8a958e00edfb0c54ac70067fda52a563803beec1952b1c019ff60ca958e00cffae654ac70067fda22a5638033fe29152b1c019ff2a4a558e00cff952512c7004ffdab14963802f7eb58a4b1c017ef52c5258e009ffad7553))))) else (if i < 31 then (if i < 26 then (if i < 23 then (if i < 22 then 0x122229107c87c643a721b590cbc863e430f215e90ab4853a4277211d9085483c841a820b0904ec81fe40ef206a1028c8126408320399013480223fca1fcc8fd747e6e3efb1f5f8fa647cd03e581f1e8f8b47c243e021ef90f7887b783d751ea78f4a47a323d091e770f378799c3cbe1e570f278791c3c7e1e370f120782e3be61dda8ee6876d23b4e1d998ec3475ce3ac11d480ea00748839fd1ce08e6c4731639651c9f8e43871ba38ac1c3d8e128707438091bf18de9c6eec37451b8a0db8c6d6436811b280d9006c6036201b080d77c6b7235a91acc8d6246ab035481a9c0d4a069ee34b01a500d24068be342e19f38cf046720338019b28cd54668a333519820cb2065023245190a0c7b863a631b818d40c6606310316218930c3d46188307d18368c174609a301c17f58bee85f282f6317990bc305dcc2eb517478b9a45c702e1216fb8b7705b982da616cb0b6185aec2d50168f8b3b859902cb816540b1dc58602c0a15e70aea057302b8815bc0ad4856582ae515548a98854782a1614f80a728537429aa14cd0a5d052b22949148c0a3c8516c287a142a0a0b8501027e213e909f084f6427a213be09d2c4e3426f4136709a744cee2667131b098984c0025cf12d4895e04aa42521127d8935449482489122c0909c482e240711fb88f9c47ae23bc11c588dec46d62345119508c3c45bc22ad1149089b044a2222b10fd0877c4372219310bc0857442582106107b08398418020b0103f8816440501ff70fe887eac3ef41f3e0f8107b183cfe1e430f038772c3b341d740ea7074a03a041cdc0e5b071e838a81c2e0e0406f8837781b8b0db286cfc36321ae80d6106a7034d61a3a0d0a067b833a619a20cbe065843276192b0c8d8642c31f618eb0c6d8632c317618ab0c3206150308818290c0705f742f5817910bc085d982eac173b0b9585c6c2e1616cf0b44059b42c78162c0b0e058302bf815ec0add856282ade153e0a86853f429c414bc0a4b0521828ec14660a25850c0282a13e409d404e3426b81320097204acc251a125c091b0489823ea11e508ea847142354116e089904430218a109f083c841a420b2104908170404c1ff00fdd07e103e701eec0f45078f83bb81d900ea20743839dc1cce0e360708037501b5c0d8806b1034f01a2c0cf006650329019280c84062f0313818500c0205e882eac170a0b54059702c2015c40abc054b029c014c00a500520028c014400a100500027c013c009d004e0026c01340099004c0025941294091904798238c117a088c042d821001034080a03f201f240f5c079303c181d480e4206f0035f81a380cba062c0303017540b48057302a10144409c004ba024a0118c0864040c01f300f000734037401a180c7405ee02d1015580a1404a80244011a00890042801e300e98065c030e017700b3805 else 0x90a0e84ec4268a13050936848b423821181088a841441f1a0ef50744837c41ab20ced06408310417aa0b9505aa82c5415aa09e504bc823841142083503fa81cc40cda05d5029e81294081a0375014280864035a014100808025400aa0014ffea7fe53fea9ff14ff547f9a3fc51fde8fe927f2e3f8f1fc38fdba7ecd3f5e9fab4fd247e773f2e1f904fc4c7e0b3ef81f754fb487d7e3eb71f578fa447cfc3e6b1f268f8bc7c433e0e9efdcf7a27bb63dc81ecccf61a7afd3d6b9eb1cf5427a4f3d149e7e0f3a479c23cd91e688f32479823cb91e530f24c78f53c679e2a4f11c78733c2c1e0f4f04478073bf61df44ef6c779b3bba9dd3cee3c76ed3b589d9d4ec7276293b019d71ceb16754f3a8f1d3b4e96274803a2d1d128e874741439f19cec8e702733a39849cb60e54e726b39229c87ce3c671b238bb1c540e23e70ee38641c2e0e1247077380d1c028dff46fea37ed1bed0df1c6f7e37b71bd78de5a6f1d37869bbf4dd986eb137509ba44dd026e7137151b7e4db906da236be1b5b0dab86d4c36881b350d9466c67362b9b11cd8166bc435c99ae0cd6e66b6335991ac04d5a06a9f35371a978d41869e634da9a694d32a698534ba9a568d252690e34741a2b0d10c687634331a158d076682b340819fa8cf9e679e33b699cc4ce1666e5336a99b14cd54669a334519964cc5065f732e319654cab26528328119370c99864bc3245991ecc8d6641931f998f8cc7a663ad31be18d2cc64a6315318298b50c5466272312098840c3be61ae30c418588c2626121308898404c1a060aa304218178c0706012300117f70bf565f852fb517d68be945f3a2f8f97c3cbde85ed92f6497ae4bd3c5e832f2e978dcbc4e5e0c2efe177b0bbb85dcc2ede176b0bb385d6b2ead9752cba765d202e8817400b9ca5cca2e5d172a8b91e5c692e27170f8b81a5bfd2df696f74b7585b7b2daa96cbcb6125ae32d5e96a88b4e25a562d23168acb40a59df2ce7966fcb35e599f2cc2165d0b2c859542c9c964a4b23259092c7716320b14458872c3616118b04057fa2be495e60aefa57572b9895c00adca56b42b4c95a24acf256692b219581cabc255b02abf95590aa92552e2a89953e0a9ba54b72a4e151d8a87453fe29e114ec8a6d6532f297994adca4e0523428fc146f0a3005170289a143e0a18e508b283d941aca0b65014280213f4c9f184f3a279513c3c9dfe4eef2759939849c344dc826c0935149a6a4d25268a9341499a84c8d262312ffc97864b7c259a92c9496144afa257512b3c95684a99253f1298c944e4a0c24f89278493a249c124d89260092b4491e247c123a0918448b22451121c49096480423de91e5c8ee2475623a311cd88e4c4716238311bd88da046b5234d119fc8cc8464923171184c8bf045dd22db916448ad64545228f913608964448) else (if i < 24 then 0x6444b21e590bcc7f663e2b1ea98f1ec77463a731ca18e04c6dc635b31a998d00c65a631fb18918bfcc5e362e9b16e18b3ac58d62b9315058a4cc4f5626d31279891cc468621bb109d8818c3e661d530e3d86d2c338618930b2d8534c2696121b081d83c2c1b060bfb059182a8c144608f303b5814cc0756022300797fdabfbc5fbaafce57de4bee25f4daf9517c46bdf25ee62f66d7ad4bd4f5e9a2f46579d0bca15e382f0fd781cbbf35ddbaed9576aabb245d84aeb61754eba8c5d22ae8d57434ba0a5cfd2e7a97388b9885cb12e4f17258b9115c80ae3c571acb8bb5c502e2417100b8705c252e0bd703eb8045bfa2df656f7cb7a35bc42ddb56ea4b7375b8e2dbd96d8ab69f5b3cad9796c5ab6075af0ad6ed6b2ab56f5aa4ad48d69fab4d75a63ad28568e0b43f5a17acff9679ab39c59c62cdf166d8b33059902cc416600b2cf594f2c9b564bab22158f2ac6d162f0b16858a6ac4716218b0fc586b2c23d60d2b02257fe2bfb15fb8afab57c82be015ee0af555797abc7d5e08aee9575c2ba1d5cd8ae4657102b7e95bbeadc456da2b6915b28ad8456ba2b5915a92ad39567eab35d598eacb75648ab1d958ccac4b5612ab05557f4abea55e7aaed15732ab7e55b1aad215618aaf1554faa9e554a6aa2254f8aa7855376a96954a1aa3c55196a8bb5455aa26d5116a85a541a2a00d4f8ea7a153bda9d554e74a709536c29ac94d2ea6715325a98c14c14a5d952cea95854a4aa4de52512919948aca41a51ffa8f914792a3b951d4a8e654712a342519928c5d45f8a2cb5147a89d144c8a249511ca88a543f0a1bc50d0a85ed42d6a15b50a5a84c141fea0c35054281b14076a0154ff7a7f513f5c9f884fbc27d753e9a9f3d4f80a7b413d549e9a4f45279393c0e9de14ee8a76d93b369d804ea7a74fd3a5e9d1f4e87a73fd39de9cdf4e5ca724d38da9c474e162704538029bf14df0a6f4537829bb14dd0a6ded36aa9b3a4d8a26c1135a69aa24d4926a0934a29a204cf7a677d339e99bf4cc1a65cd325898e54c54a61b5307898004bed25ea52eda975d4b90a5bc12d1096784b34259612c9096384b14258612b8c95b64ad32557d2a9e953f4a97a53a12958947b4a2aa50bd283e940f49ffa4f39270e9356498d24c2925f492ea49572499d245691fa48d9a460922a291204877a42f9215c9088483124149206e9027480623ff11fd88fdc47d5a3dbd1e7c8f0d477ea3a811cf48e49471ca38a51c328e0946f1a369d1ac08d2f467423309194e8c974643a30d518088bd345cba2e1d16c28b1a4574a2ae115248a6c452e2285513de89df44e7a267912da893c4485a23ed115288834439a218d106487f643e2a1e7d0f1e877f43b7a1ca10e0486e7436ba1b1d0d6e86a7434ba19f10cc286514320a18c50c2c85fb42eaa16650b12857942b4a153 else (if i < 25 then 0x19fb0ced8663c32b2190d0c768622c307e17f30bbd85c0c2d16163f0b04857a42b9215a90ac4854f42a3a14d10a4d85194288a142509f784ee42732137909a184bdc24fe121d08e884614221a10ab081983f441f360f23076083a841d020e3506e9835c41a1e0cd906468310417be0b9305ae82c9c15b60a7905168272c12d209070468821bc109e082f03db81e5c0eee06ff032d818ec0bb205610269812740876041b01fd80e6406f203170144808f4043a01fd00d88048c0156008b002a800d40029ffdeffd47fd73fe4dfedaff527f9bbfc71fe18fedb7f553fa69fd14fe597f143f7ddfbcefdab7ecdbf62dfaf6fd4a7e81bf2f1f916fc657e1a3f039f7d0fbd87dd93ee31f6f8fb6c7dae3ed31f678fb2c7d72beb55f506fa737d1bbe7c1f368f9a47cca3e611f2a6f9227c78be385f160f88a7c3d3e17df030f7dc7be63def1ef58f7917bc0bdd99ee3ef6e37b4e3d9d9eca0f6407afcbd721eb70f5a87abbbd4edea2af5057a7abd395e97ef4997a44bd1e5e8bcf44e7a1f3d0b9e810f3e279e93ce85e6e0f34a7997bcc51e5c6f2c87956bca75e4eef2517920bc8c5e442f21178fb3c799e396f1bb78d5bc641e2eaf15a789fbc465e1fcf0ee7869bc2b5e0e2f04b7812bbfa5df86ef9d77c6bbd9dde14eee477543ba09dce4ee6277293b8b1dc0cede076dd3b651dadced32767b3b2e9d954ec8476243b031d7a0ebb575c23acf5d618eadb75553aa11d4a6ea2d7503ba759d334e97474a73a4f9d230e8f274663a2f1d158e89c74463a115d06ae825740ab9f91cf3ae78273a8b9d05ce62e7217388b9b55cd48e6947331b994dcc86e60772dab9611ca90e52d727e393b1c9b8e4957221b901dc796e3bb71d5b8dbdc6bee34f7189b8b89c54ce25f7122388d1c406e1f370f1b874dc386e1a870c6b85f5c298e13c7085b83edc1d6e0db7065b8269c114e07a703538111c068e0196ff437f61bf90df976fb337cd5be34def46f6737af9bd5cde9e6f47378c5bc2cddf06eeab7715bb54dd9a6ec5375bdbaa8dd186e8437389b9a4dcb76e53b725db8e2dc616e28b7081b7f4dbbe6dd1b6df5b6aedb316d8036b69b568daa46d3f36961b422d9e06cd2365cdb284d9116c80b63c5b1c2d8c66c55b6241b0ead85a6c1fb6065afe6d7c26bd935e05aeb6d74b6b92b5bfdad86d6b36b46b5919abfed5ef6aea3568dab10d5576a93353d5a9cad4ca6a4cb51a1a86ed40669dfb4e39a6fcd34d6988b4b81a55ed27e6926b48f5a418d1fc68dab463da2bcd1436899b4435a1e4d0cc685e342b1a138d076681d340a99ff2cfb267b5b3ce99e54cf1a677a33b0d9d0ece616728b39059bf4cdb366b6334c199d2ccad6649332099876cbf465d132d99963ecad8654e32a0594e2ca4b6502327d193b2c98764ab32495922ac905647ab233d9152c899 else 0x866542f2a117504fa809d400e9fe74fe3a7e9d3f0e9f674fa3a7c9d3e0e9e8f4f0ba76d53aa69cdb4e47a70b5381a9bed4de6a6eb5371a9b6d4da6a6cb5361a9a954d3aa695533ba997b4cada64ed318698a34c41a618d308698234be0a5d252dce969b4b11a575d2aea95294a63a51ed2832935f497ea4a6d244691c148afa444d2162903947f6a3e2d1e268ec74732a38651b9a8d6b4679a31ed18328bf945c0a2c25154e8a2f4507a26b5129688d34438a21450fde87cf43d7a1d350e0286b5434aa19d50c2685b142c8a151509f284d9425ca126508f28459421ca106507f283d941a5a0cad061682a94144a09a503b681bb4096a038500fe805f401fa007cfffe7f9d3fbe9fd74fe7a7ef13f479f9bcfc9e7e2f3f079f70cfac27cff3e6f9f2fcf93e7c7f3e0e9eeecf6b27af73d6b9e97cf47e79dd3cbd9e56cf276791b3c7d9e36cf09a77d53bae9db94ecda764d3b169d834ebda75cd3ad69d634eada754d3a499d1cce8a674333a099cfcce7a673b3399d9cc6ce5f672db395d9ca6ce446720338f19c70ce346718338859c3ace19670ab380e9bff4dfba6f6537a29bb8cdd026e1f36de9b674dafa6d5d369e9b474d9fa6c8536329b114d84a6c0535d19acacd5666a3b350d9a7ecd332694d34969a434d1da688b341499f1cce9e66ed3345999accc96662b3305997accb9665ab32c5995acca1264a7322d9903cc7866377317f98a1cc44a61ad309a982f4c0b65fe32fe197d2cbdd25e872f129770cbac25cff2e439719cb88e5be52dcc96de4b6b25b392d8c96be4b5b25ab92d4c969e4b4b25a392d0c967e4b3b259b92ccc9658cb28658e12c3f960ccafce57b12ba795c0cad6e56812b049574cab3a55672a779533ca8da544d29d494d74a5f65299293c9485ca396516928a4944a4a212507b27e093c749dfa4edd273d9375c9aea4d55268f933a498b64bcd259f92ac4949e4a2f24db9244c9136480d23ca91c1c8d76469b233d9196c8c7645ef22d19150489924493222390f3c86da42df21499081483ca41c520d29061482ca41452087903bc819e40af20319005c7f963f7f1faf8fc4c7d623e911f178f6dc7ad63c9b1e3d8f16c77f23b811db08ed0475be3a671d238e794730639631ca18e2d470fe381d1bfe8dec46e4636c11b198d7446ade35231a3f8d0cc682633f319e98cecc66a232ef19518c90463be317d18ae8c4f461b6306317f58bf2c5efe2f1d175d8b9645bee2d9516998b39c59622c7b16228b09457de2bcf15c18acdc55d62a9f15298a7c4531e292d14658a1a4500e27e713c289c8c4dae268b131f897cc4b4e25451287892b448c2244111fa88ea446ba233d118e88bf445ba22bd111788684425220f31053880bc401e1f810f6e878e43b821d1d0e738731c38f61bed0dc586ca436121ae90d4e869443462))) else (if i < 28 then (if i < 27 then 0x4eb9265c92ae4917246b9225c8f4e470f230f914bc887e43ff21879087c820640131fe98fb8c7be63db31e778f0ac77d63b531d478e93c7316389b1bd58db9c6bee35071a218cd4c651e324f19078c73c631e314f18878c12c60162fcb17578b9bc5c5e2ce716538b19c579e2b8f15a78ac3c538e298714a38a41c518e282f13f789ebc4ede26ab12dd895ec4a7624fb120588f2c4716234b11438865c42ae2117101387cdc3ce61daf0eb7874bc39de1c2b0df586eac36d61aa70cdb865dc326e18f70c5b8607c2fbe179f0b6d8585c2aa615130a1184e2c2696130b090d8455c20ce102707f383d3c1d6e0e1f0681831ac174e0b0f0525826cc1236085703c981d4c0e2606d303078152c090e03c301c180d0c04fe01bb007b800cbfeddfeaaff357f8abfacdfca2fdef7ec6bf4adf992fc677df7bef3df75efb637d80bea7df4a6f9f17ce8be6c5f322f9717c87be2b5f0c2f82b7bd9bdd9dee0af6e57b62bd98dec86f6237b01bd78deb86f5a37ac1bd58dea02f4e17a60bd285e902f44b79ffbce75e6faf31b797dbca65e49af1eb78c4bc5a5e292f0e77858bc195e006efe377c0bbc7ddd7aee5b771dbb765db72ed997690bb2fdd88eebcf75abbacddd57eea9f753fba97dd47eea1f74deba56dd21ee8c37425b9ffdcee2e6f97335b9775cacae5037250b9155c7e6e39171b8b8d45c662e3117178b8b45c4dee20d70d5b862dc2d6e1097069b821dc04adfef6fbbb7cadbe16deeb6f65b79fdbcbede136ed8b74e5ba32dcf96e6cb7185b7fedb876d92b6b0db4eeda156cd9b6545b1ded8776c0ab5fd5afaad7b56bcab5dd5aeaad7356b74b5b25aca2d5ef6ac6b5505aa42d5016a70b5305a942d43f6a0fb4ffda7bed37d69aeb4cf5a5e2d2d16958b4a45a4e2d2256902b4795a306d16368a1b448da206d0e3684bb41dda0aecfdf67b3b3c159d72ce99673cb39659c72ce1966fcb37659b72cd57666fb319d97decb8d6595b2b259552ca896534b292593a2c9b164b2b23b59116c81363d8b1d958daec67562e8b15bd89c2c46961f8b0d8d862ec29f6129b081d8376c159607bb02ad8116c0295feeafe457e5ebecd5f40af8d57bd2bdc95ed4af6257ad2bd495e94af42578f6bc035dc5aebf57536ba235ce0ae6857302b9615ca0ae4857202b8e15c60ae0756ffab7855b91adc0d6d42b6555b1aad8556beab5d55aa3ad3ed6906b4635a21ad08d6756b38b59b5acd2d657ab24558f1ac70d62c2b115587aac355608eafcf57a0abb255ca2ae315708ab7c55ba2adb156c8ab5c55aa2acc3561aaaf4d570eab6755a3aac9d5532aa37550baa7dd53aea9b754aaaa375517aa89d543eaa1754fcaa78353b1a9d0d4e46a7035371a9b0d4d46a6835331a990d4beea5955278a934548b2a43951eba8dd545faa2dd515ea8a754476a1d950dca else 0x8100810081008138a1008100810ec10961c340b44104168a025a99058689208eae1a184109d5c340b47012d4c82c3448096a64161a202dc3423ab8686c8c20864102dc3434340b44104168820815100909d5c347d01690eae1a3e80b487570d1f405a43aa7d01182d21d5c347d01690eae1a3e80b487570d1f405a4d047d0110fe2e823e80889f17411f40444f8ba08fa02227c51ec7d01113e2e823e80889f147b1f404443aa680168cea9a005a3391868fa00c20b9c347201690e402305a33900c8060ce40320183390680060ce41a00183172720d000c21c83400306720d000c19c83400306720d000c1ec80f008c74037a6c8046410c111c111c111c1ffdf178d0e022b608b8f8a3d0208e02ab60ab60ab60ab6088208b6088208a908b60e98babae01190410441045b044304410447045b0462844307e2fb60203104116c1df616fa737cedbe5bdf206f8977c2bbde4dee4ef6bb7b27bd6ddea3ef4b37a0dbce0de62ef2d7791fbc5ede21ef0a37831bbfdddf16ef4b7785bba7ddcbeee1f76d9bb51dd9b6ec4375ebbacfdd5a6ea6774fdba63dd246e8b7743bb9f7dcf3ee7077363b98bdcb2ee557725fb91fdc7cee3a7719db8bedc51ee1f770afb831dc05edfef6f95b7a4dbbf6dd376e65b70cdb78edb2f6d61b695db3d6d9536c73b61edb01ed7776b6fb591dabb6d56f6a81b530da8aed3bf69a9b4c4da54ed23b68e7b458da1eed05f680fb3ecd9ee6cf336763b38bd9bdecdaf66a1b335d992ecc2b6587b292d92b6c83f63a7b18cd8be6c5b362b9b14cd89e6c4036173b088d8266c0f36017afcfd7dfebebf5ee7af37d7836bb575d33ae68d7166b7c35b7fad83d6aeeb4b359e1acb4d6316b0c75817abfbd5f5eaeeb5729ab84d5a46ac5f55b7aacbd55deaa5754dfaa5fd527ea8ff545faa1fd507ea7ff53dfa9b3d4c16a5475283a931d4806a3135127a86dd41e6a0034f89a793d3b169c9b4dd5a6aed34f6998b4c4da616d2f2e96d34af1a547d28b6941b4995a4bad255692134891a40cd1ede8ed74709a353d18be8b9b4555a279d11ee885f43b7a1aad0b7684f74203a0d0d060682c34141a090d03ae8197407f9ff8cfe3e7edf3f4f9f97cfc3e7ddf3ecf9f57cf8de7bab3db59ecacf47679fb3cdd9e3dcf16e78773bef9de7ced5e766f3aa99d44ce9a6749339d19cb7ce53e725f38cd9c56ce2367057380b9bd4cdd1e6dcb36c59b52cda166ccb36459b12cd70e6aef356d9a85cd2fe68e733fb99abccbd664fb320598d1cc506624331019870cc3066143308197f9cbe465ee32f519798cbc465de32e79972ccb8e65c332df996cbcb4d6597b2c719607cafbe579f2baf95c7cad6656732a95950eca7f653bb29bd94ceca496520b28e59436ca1364fab275d9372c9a0e4c1725eb92e5c96ae4b17256b92a5c94ae4a172) else (if i < 29 then 0x4e1a1ee371d8687b8c1e0454844707e2e1a1ee308203047143f17db422c344f8afd30d0fdb3d51a0b230d15fa7c5770edb0d17db3d5c343f8bedb0d0fdb61a1b23f8b8687b8c6f845484090441070d5c501830958687500c204ac343080610250e80183c34030680c2561ab6c030812b0d00c18df087843532032901e06430d9c3430103206ce1a25a990d8686360641d5c344b5321b0d0e431d51b20c896a64361a19d5c3436463606461a3aa490d868432057e1a3aa4c343600604a20a908580858088e08120d82c3420958687b00c21b608820d82c3436478686f08208f7100c05aa1b0d102502dc34030960b0d082561a0183c34030560a4361a184a1963230d105e041158290d868760a4361a1c86c3420823dc403065e1a190490c0330d0c0484048425041018310410947d30d00c204a064030608c061d503c4c343602500c204a3400306128d000c184a1258680610169d51927d01914169d5d907d01914169d51b07d01914169d5047b20fa032302d3abb20fa032282d3aa360fa032282d3abb20fa03228d01b27d01113641f40443d907d0110f641f404431a07d0110c681f40443d907d0110fdb02d1247541114491d50443094104060c250410183094104060c2504101830946e01180c204a08203061282080c19df0820306324ef84101843e808c060cef84101833aa6e01900c21d53700c80610dc1a0018331c030208fe2c4113d5790f162093e282d8823f8b1045f140644118df08a9088e088608040a410aa90a8e0a860dd5b90f7ee2eb8c3465be151c17bf1044f162089efdd5d718688f235c1d5c344b529044010275520884104eaa4112df0a8e0a860fc5b1cf7f5c61a2bd5791639e2eb8c346b1c9045639eaeb8c344008148215be1552150c17bf7235c61a23d5d707230d12c324115867abae30d11c75c8d71868801027212088e421a0183390868060d6f8554854705e2c41138e88220191044f14168cb0824f8a0b40622208250820305f147bc3ac344f8a3da0261a3e85f6cf55e43c5c3453e9f147b04127b67ab8687f17db38ec344f6cf230d0c3b04fa7c51ec10482a42238221838686c8ae2dd5b90fd30d15fa5c5baa3782097db61a1b23b8bedaeadc871d868dedb0d0d91fb6c34364637c212c223823d62089e2c4113a9882271d1044e1a208be2e1a1ee31ea1046c8fe2fb6c340b48fd3e28411fc5f6ce3b0d13db3c8c343f8b8687b8d0d02d108e08860fc58450eb0d13e2bf4c343f6cf55e43c5c3457e9f14208fdb3d5c343f8b0e8110fdb3c8c343f8bedb0d0fdb61a1b23f8b8687b8fe2fb6c3431be1152107c8680a8c43046f61a0183f8afd30d0dea8de3918688fd06f0411fb67ab8687f17db38ec344391868060fe2fb6c343f6d8686c8fe2e1a1ee3f8bedb0d0fe2fb6c3431be1152111c1012100810081 else (if i < 30 then 0x20823dc423820e8210820e836a65b61a1ee4b538687b8e7a4b896c7570d170d4b61ee308414340f87b8c1d041d06c74b6c343dc963b0d0f71cf4b1d0ea5c4b6c3469e963a1d4b896d868d2db0d0f71a1a07c3dc78687b881d041e041d041d04e2841d047b8411b23c343dc5802208b0044116008822c0110441047b8b0d0f710411ee2c343dc42e0208f719d50443dc6754110f719c80643dc6720190f71ef401861b5b1d504663900887b8c066b63900889bd0066b6390088a720110f71ef4019ad8e40222ef4019ad8e40222ef4019ad8e40222bf4f8aee1db422288608820df47aaf22dc68e3bb868eaa42a183869db4221bf4f8aed91d0222fc5f6c8887a3ae43f4c344f6cf57471c8c3457e8ee3475c876d868dedb0d0d91bf476cee2e461a282209c84442011a38e421a22df0aa90a820fc5f6c8887f16c168e7e9868af55e468eb70f170d19fa7c5d1c1049f17db68e05b868b86ac12221fc5f6da380661a2bc57aaf22dc61a2fc5c343dc6889d4a8ec3440441370888423826e111096f85548543061d61a1ee3be8f55e45b83bb868d8687b8d91a1a07c3dc62a4221832801f0811044704110409041104db041104110400e8e434384560a4761a258284523b0d12c142291d8689238208ac142291d868923b0d087b841142291d86860f90d015183e94005460311128ec3440441018248fa1c8c345f8a0b4060e23be104c0b4061df1c4104a08c277c71041180c3aa1046a38ea841182d124720209016e8e39010480b7471c8082405ba38e4041202dd1c72020901184168923901048fd26461a1bf476d3206f61a2fb67533230d13db38e9918689eda6461a01849918687a80c27b69918680613db4c801807893206f61a01841be1152111c11041095868fa00c27c53e98686aa42a382a083755fa4c8c3445be151c15041b71b20fa61a25f47ab6e2db2c8c346552151c1b52fd36461a27b63ab8696411fa3b8b52edb6461a304a0640307ed8169d5064410c15900c84b7c2a382a083639fa6c8c344f6cf56c761a59057e8ee2c73b6d91868dedac73a9d91868a128c700c03c4f8bed8110f43022168604425be1552150417e93230d0dfa3b876d3230d17db38ec353209ed8064c8c3447e82f1db23a991868cb7c2a382a082b206f61a0184b04fd36461a23d5b718696411fa6c80823f6c0b76461a238eb71b230d116461a0183f8b6e30d0deae1a882b209f170d0f71fc5b718686031d4a86c344094104060c2080c100c082210c1590104060d6f8554854707e2fb6c343f8aee0fa61a27c5f6ce3b0d103c21a0ca311c11041baafd30d4c823f4baaedb0d2419906f6d8686c8fdb5d571d86a6415c761a1b231be111c110418758687b8fe2e1a1ee3be8f55640de3bb868d7d2dc3d5b6d868b7d3e2db871d6db0d1be2e1a1ee3c343647b8dd else 0x7f8bed98d0cfa7c5e34ae086d822d822a4223823646f0aeaf1a7e93209c006f0bdb7981b23f6d755d04c86345f6de606c8c11846f8425858d0de108e08f51bc2f8be607b8f800de15f4e34f565c12fa7c574010497d3e2f007412e0bf17cc0f718f51bc364608c20f02c686f0854844707e2fb6e35ff89f178d3f4ffc4f6c7578d2c823f4f8bc695c13e2fb6740c689f17db700741ff8bf17db7fee344f6de606c8fe2f981ee304611be1f6c7578d2c821c508c5083df8bed81704d0f4c68ff17db31a1a06088e0fc5f6d08c7ed9eaac884647e9f155c42327c5f6d08c637c22a43f17db71affc4f8bc69fa7fe27b67abc696411fa7c5e34ae09edb8d3d5ffc4f8bed8d031a27c5f6dffb8d13db7981b23f8be607b8fe2fb6ffdc68808c237c22a4215821b1a02a4f8bed98d0ee2f001bc3e003a86f0f800c21bc3e003a06f0c1907800e81bc3991c00670de25b6e003787c006f0841046f8441046f0f710de0db61ee2b6c37852e0210436d87b886f0f710bc36c3dc62f0db0f7183c0b1a1bc21041152110411041104111c110413bfc69644b8208608df088608d91bc21bc19901b8a37857146c8a640664046ccc810cb38a36463646f086f04d4f1a970b20821822a42218320ac7686ffc4b1d20bff089258ed0dff8632ec72c81d8e178ed8763b437fe1e866346806365640b802c8970680963bff0811845e3b610b9178ed86224492c8188e08860886088609a01bc211c121c140c1112b2042182378237826806f09efd1a8bc3f8afd28d0e8d0de151a1bc275346a2f0fdb3d5a34371d46a2f0fe2fb671d46880568d0730bc41bd46854686c8de1d1a1ea37860568d0720bc41bd468418c2f51a02a41bd468437c22a422383b20fa51a1e82247b22801f42fb6a34754663be2fb6a344f6da1a801a025003402a34378546a640a8d0de151a9902a3532054687b8de1d1a990211346a640f41686e347d0ea9741686e34754fa1741686e347d0ea94800499682d0c48cfa1d53682d0dc68ea9f42e821b1c68fa1d52e8605bc68fa1d528d0d05c006c9f43406d05c03641a03e85d05c03641a03e85d05c03641f43405d05c03641f434052001d05c00681f434051edc03641f43405f6dc00d01d527b6d0c0b4ea9a02aa90a8e0a860dd5b91ae2e2e1a5e8651c1d717570d2f426f4791ae0eae1a5ba65e80b46123a3aaad8191c1d04eaa41128e0a860fc5d7163b0d2f42ef47aaf235c58ec34b74fbd35c58e7abadb0d1b7a3d5791ae2c761a5ba75e8ea51d2b856d868cbd15c23a56c088a0e829042aa42a183ae2e461a5e84de8f575c1c85bb868dbd35c5867abadb0d1b7a6b871d7235b61a36f4d6dae30d0d92af47528e95c2b6c3465e8e391d2b856d868c0e82721208954854706208f713c588227531044e3a2089c344113c57aaf230d0f728411ee)))) else (if i < 36 then (if i < 33 then (if i < 32 then 0xd3e284118a908860fc5f6dc6bff11fa7c5e34ae09f17db2a06344f8be61db0f720230e8e07b7575c04d0f4c68ff17db31a1a0e08860fc5f6d6621193db3d5790f161195fa7c557108c9f17db42318df08a908860dd5d1d7235c71ab8a6e012e0610c118e81032088208df088208820cb81ee291d2e052e032e0210423dcfa08fa0f711c00463dc77d01f85707c104a10422082208361bff0aefe8effd7235c71a31c81b22b0c3dc43dc3c025c0de19c50f001b0210c1046078523b417fe1244d0561a477fe26821a072076195c0ac3682ffc3b0da098d0d5c0f710d93902ffc173008c4218220822082208219428044634054ba098d0bdb092390310c15703404208320b477fe1ee4d1d77e417fe25dfd1cf147a387b1f41ddfd1dff8777d8d2a01ddfd1dff8677fe2f005412e0a7d07b8aefffe10f63e82046176c3dc5ff83ff8237c22382238223823d8fa086f84af850707470e0e007d08a807b0847044707801d5970a80823822a42238320a118acc42315988462b3108c5662118acc42310230822b3008c5a0b4771a3e84f8a7d0118cfa04ea87e285607d4680a97e2bf4a343f8afd28d0fdb3d5790f168d17db3d5790f168d168d03e13f4f8a1047ed9ead1a1fb67ab46874680a8bdb3c8a343f8a1341f07c07a0543ed1a47c5f6d46861243eda8d0d918370fc5a343dc7f141e83e02a1343d51a3fc5f6d4687f17db51a02a4f8beda8d0c2f846f841484548403044307e29f4a343f8a7d0118c7b68ea347d083da8d1f41fb63ab4687012500a804a01500940291c1045402500a804a010f70822d054685402500a804a017b63914687ed8e40231e82125468e41044e8ea347209a0b4771a3aa7d0ba0b4771a3aa7d0ba0b4771a3aa7d0a4002754fa0231e821c5c68ea9f42e82d1dc68ea9f42e8e05bc68ea9f42fb6d40030e413db6a001872082f34771a1ee720bedb5000c3904f6c720118c8004e4078d1f43903d04248fa1c82089d1c7d0e413db1a926472082f3471a92643dce41bdb1a939008c86a44902d3904353a38169c823dfe35ffb5c6c82bd5f303786fd3cc0de1ba9e35ffb5c6c82ba0d71b218d13803a0ffdae36417cc00c1bc3f300306c8de27980183d46f13cc00c1bc30461f300306f0d8d0de104307ec686f05b48215006206f84548447050307801df1bc3f8bc68fa0d548547050306eaf1a7e93208b7c2a38212c3f178d1f49704e003784aa42a3820f028183a0b4371abaafd3ff1bdb71a3aab208fd38d5d55704e006a46f0fdb71a3aa35be151c140c1b41a0b643f4a345f6cf56d051a59057e9f16d004125a0d0dae1ead1a2adf0aa90bf4f8bc02d02b82e86e01ae2d03d5ffc6d71b20d031a20230aa90a060fc5f6dc6bff13db3d5e34b2087d3e2f1a5704f6dc69eaffe27c5f6ce818d1011842b03df8b7d026844634 else 0x671d46880dc3f168d0f7187bd700b36a84d0f3468ff17db51a1852f8bed82687a07f468ff17db51a180e088e080608860fc5f6c63a8d13db1c8a343d043628d1c826a9247ae2801c828d8a34720746a5c02d1ad5a352e0746a5c087b02d17146894685c3c51b2405b46a5c0cd002d10b93900b4648ce402d19c805a2e347d0e40c44ea93e87209edb5480c340720bedb5480c340720bedb5480c340720a2f354f001ee680e41bdb0d8018680e417db6a9018680e4148007db6a9018680e41611c411441846288308c407029042aa42a183757505c8b8afd30d196f85efc4113c58822d41755fa61a27b6d40f20eae1a2da9482203813aa9044b7c2a183f17db6988464f6cf55e42d3846548308c5f175c4231adf0aa90a860a234822d41721fa61a27b67aba80e461a2d864822f6da82c33d5c345f8bedb4c22327c5f6c88c7ed86ca231a4144627bfa09118d5c2c0446303813909044b7c2aa43ed9eabc878b08ca7d3e2ab88464f8beda118c54844306e2fb6bab7221195fa5c5bab7215c42337b61b308c637c308e208a20c23144184627e9f155c42320860823081c08230823082308230ddfd0508c67d020c231ddfd0508c76da11c411cb8846297108c40702070208c2070208c27142070361b414231e8239108c6106118ac368284630381d40754fa03226a03aa7d0191011841184741d53e80c89a80ea9f40644d40754fa03220230823082308bcd403dce403228230fc5e00f7fff6b8d4067aaf23806b8d40f14cfd3e2e8ee34ae0bc01eaffed71a80bf158d2415404f8bffb476b8e345f6cf4c6c8fe2f985703dc9f17ff68ed71c68a08c3ffbe2e8ed71c68bf17476b86344087f143da22474c682d87903e91be1152110c141c1552141c150c1bab7234168ee34fd2e29d6f850706fa3d5791c69e2cb832a90a0e0a860e82d1dc6aeabf4ffc6791a3b5c71a3aa57e9c6aeaab827b6e347547edb8d1d51adf0a0e0a860fc5a34fd25013db3d5791469e2ca033f4f8b2802093e2fb6a344ca50156f8554854307805c8ffdae350174168ee35721fa7fe33d5d1dae38d1c82bf4e357215c1347586d71c69eaffe37b66357215013db79878a3648fd38d5c85704f6dc6ae47fe27c5f6ce6111915c07db71a3903f6dc68e40c4704e42a0108209c857025be1552141c1f8bedb8d7fe27b67aaf238d3c529f4f8bc695c13e2fb6540c68808c215b4703df8b7d0268446348f8bed98d0cfa7c5e34ae086d822d822a422183717800d91dd5b91c69fa5c52bf4bab7215c71a3ba6f6de62e28d927b6baaa82e45c56346f6de606c8def8d9102308df0dc5087ed81e8d90a4c68f717db0d96344f6de62e28d927b6baba80061c828860f009703dc77d1eabc8971c68ee9afa71a7ab2e097d3e2aa00824f8be607b8fcc0f71b230461be80fc2b04d6340f8d7) else (if i < 34 then 0x4065be1e003645b141edf409a3642231a3ec5f6c3658d10fa79857036486d822d82238377e628d91e8298a364637c2208220823786c8822057991ae023df46343641a26644d5d04c688ae06c886c8de10f79ba23e92e06c8cfa4b81b231ba3dc6c8f800c21bc3e003a06f0c6407800e81bc3b6dc006f0e640d910c81b22e013206f0c6c8de14c80ab81bc299036453203a086c887bcb81bc36483dc6c8a5c4c8e0037883206c886ccc8e013546f1411866451a1bc3991c00490de20df08d91bc27bf46a2f0f62ed5d90fd28d168d0de13a9a351787edb642d5a34471d46a2f0f62fb6dabb21c751a36d5a341cc2f1362ed51bd46894687a8de1ad50574683905e2ad51bd4687b5431d1a0bc4d8bb546f51a251a1bc21be111c13e94686c8f4151a3e83649b5764500247b14fa1b6451ad8a7d09ed8c751a1b243403646f0f629f43403649a08fa1a01b24dabb23806c53407d0db23806c53407d0bb5764700d8a680fa1880076a8d0e01b14d01f436d5d91c03629a03e86e01715efeb82700b52f7f5c13801d5d7035e9c6aeaab826f4f30ae06c91efc4113c588227531044bd3e2da00824de8f15eada0790104dc02c73dfd704e01639e2eb82700b1cea75c12c724112f4f8bc02d02b82ef478af55e4700b40ae0e08c3c02c33dfd704b0c9045c02c338ed7045e9c6ae42b820b71ec29e8f55e44b8e34b74c1d82c687b085484470443047a8d91bc3b8b757cc5c81ee5f303dc6c8e5c2f41b230bc16343784238208c23787b8a5c0f714b81bc29701082197011b27207b8e5c0f7103c0b1a1bc238a1d6c3dc52e27a0a7a4b814f408229e92e052e27a087b4b812b61ee23ab4687b8fe298ea343dc94687a8de18411ea378648c6f0b5b1d53403dc86a47a8de19a91ea37866a4918de19a01ea3787c00d00de1f0034037866807a8de1f003403787c00d00de19000f003403786fd36af1a5704f8be60168f720230fc5f6de601693e2fb6f300b49f17db31a05a411c110c14041be8f238d2d59705452151c150c1b41ae36ad1a23f4f8b6802091fa7c5b401048a183c02d07fed71b54afd3e2f00b40ae0bae36a9a063447e9f17805a0570504613400b45f17db7003404404150c1e012e07b8efa2d57912e38d1dd37981ee3647f14158f50da134209afa7c5082311c110c1d71b549191a25b605a238a105a1b0c3dc52e0168de1823081e05a205a340520b54ffe1ee4bbf20bff02d25df5aa2d523d8fa0eefea96343bbfaa7ff0cfa0f710f63e82ffc1ffc11be11521152115213e80b4437c20b43684d6341d8a3dc16b1a195f0a290ea91c07d06b547b0854866a8d9102d90535473542c6a6a8a6a866a8d910d51b223ba3644378ee88e40d915c51b2201b35416b1a0bc563535440f7e287aa341362082d3bf4f8a1046fd3e28411fc5f6ce3a8d13e2fb else (if i < 35 then 0x1fc5f302dc7b13e283d09a3838d17e2f981c03f8be607b0c1187e2f981ec3f8be607b0fe2b1a1ec3152111c110c14be1bab7238d682de9714c97c2ad82a383f17cc5b61ec47aaf225c71a78b3d0dc00700be28f41c010481d82aa42a382a183c6aeae82ffdbd0bc697a5d557044be1e34bd2eaab822b60a860fc5b41a0b7a51a2bd5b40f23416f478b468ebd3e2da00824b41a0b7a3d5a3455e81044bd3e2da00824552150c1f8bc02d0682ffdbd0cf55e4682e01bd2d03c53fc5e00bd2d02b82fc5d05bd0d031a28230a5f0fc5e00bd2d02b82ab60a860f1ab91a0bff6f42ab8e357217a11d0682de97218d1741700de9721d07fe32b85e824be1571c6ae42f422b60a8e09b608820cf41ee29713d046d83f155c71a5e8436c15e9f16d004120820ab6082309b60af4f8bc695c10410447044107800f61a0356c11e83dc5c007bcf41ec456c136c1f8aae38d2f425869bfa0bff12c34dfffc3dc9a08e40ac30f65703b0da098d0c4304410441044106e468208815c32b1a07a0d11a098d0ac30e057033903d8421823d95c0841055b065c0f715b61ee2971c007bcf41bc5ffc1e003d86c0ce2840f0f612b60ffe0f001ec3406ad826d82bd3e28e0082478b46a3b0fdb3d5790f168d168d0f613a9a351d87ed9ead1a1b8ea351d87f17db38ea34470d46a3b0fdb3c8a3430921f6d4686c8e8d0b71ec3f8a0a826d1a0b61d8df17db0f7a344f8ae3828d1a0ec5f8bed87bd1a23c8a341503b13e2fb61ef46882a4223822183468700a8d0f6151a9e82a353d0546a7a0a8d4f410f6a343d07ed8ead1a182ddbf468ea915b07e2fb631d4689bd2801a01ab60fb63914687a0a8d1c81e82247bd2801c82ab60fc5f303806f55e44b8e34f167a1a7a3c57aaf238d4b8306009d51ec25e9c02ea8e021a01ec25e9c02d00e027b6e00754d01016ef43aa6808ad827207b095c7001c03789ed8d49323904d043a8c31d5270030c7547b9099682de848cd49c83089dbe6a4e4115b077a00c3906809ed87100c390680bbd0061a03904e00720d00f726f4018720d0137a00c39068084003bd0061a0390456c1d05b576471a7e9b14db57cc0de1ed5f3032c7b906c8de10230ed5f3037863646f0b6ab1a1bc309211be111c1e0077c6f0f62ed5d91c68fa154706fa6d5f303789b57644b8e347d26e98fa6c5dabb238d4b832d55907d25c102f054707806c51b23d91c69fa4d523f4d91c695c4d52ab85ba3646b7c2a383b56d06c8a35106699b6ada0d91469fa4d333f4dab683646c50826f6d6836451a5aa5d8bedb6ada0d91468cf7d6aac8d05468aae16e896f876aec8e01ae2d06c536d5d91c02d03f4d8a67e9b57642b8e016816e9fdb6c8e016816a97db6d5d90c68d02d337b6dabb23805a0d8a67beb556468258a5570b74408c3c00d00de1fb6dabb23806c53 else 0x6f2dd12dd1ee21ee11701a343784ea68d45e1ef4d70f575b51a2878a341cc2f106f2f4a343a343646f0f7a02ba341c82f175b6f41bd4689bd1c7063a34178badb7a0dea344a343784bd1c7079a34178abd1c72b8a344152111c1a347547b8f4351a3aa3dc9f14c751a1ee4d0d400d00f720f51bc23403d46f0cea9a01ee3d0c754d00f723dfd3108c6b2211896042313a9d3108c7f17db02303c4f6c08c6c8fe282303c3dc9f17db02303c4f8bed81181e21f403c2f8ba80fa61a22a90a820dd5d40fd26461a2adf0a820fc5d416e0fa61a2df47aba81645b83bb868eaa43a82eabf4c344f6da81641d5c3457e9a81dc5d576d868c7540f0bdb6a03aa0c88b7c2a083f15dc1f484641041f6d7566442323f4bab321dc1dd8466f6c366118c6f844107e28f78463be96d9eadb859108cd7d3e2db6b7108ca2a437140f08118411866442314c88462b8a366118c118d015b60460786b22118a5042314a084621be1d40754fa03226a03aa7d0191011841184741d53e80c89a80ea9f40644d40754fa032202308cbd4077c6c8412823082308230fb67abe606811fa3b8e01b23503b637b6e00ea7ff6c8d406f6db218d2a027b6f303407edbcc0d91a04f303407b8fdb7981a030461f6de60680fdb31a1a031be1152110415be10a015041be8f56dc71ab6cb20caa42fd34368e771c6aeabb63a820fb67ab469644a02bf4f8b469db1419406f8beda8d13294055be155215041f8bedb8d7fe27c5771c68fa13e2fb6540c68808c215c2231a0ca4f8bed98d0c41046c8d013f4bab321dc71a3ba6f6d755504c8634504611be10a0163434042083c007b8afa5b67ab6e38d2c835f4b71c69eadb62df4f8b6d9505b86346f8be607b8fcc0d91ee30461b6da3b640f70aec68d6dbe28f76344152138a1f6cf556442323f4f8aee1db4232fc5f6d08c637c22a422083717800d018d00463a06218221823646808680664066404681c51b231a008c6c8c4306435dfd1dff8977e437fe1244bbe341e28f471f415df5402e007d2642a021f41ee21a0f14408c2248712a018c91a0f14637c22382238223827d068086f84492a0108e088e0c868462b3108c5662118acc42310d03a608c67d0680868068d0d013b6a351406fd3e2bb876d468aea68d4501fb67ab46860542807da34194bf17db51a1d1a1b234060dc3f168d0f71865f6c1100a87aa340d02823e2fb6a3430ca1102851a02a5f8beda8d0c6f8454844107e29f4a343f8a7d0118f4751a3e83f6d468ea8fe29b8a343d0d468dc0f4368ee347d0ea974368ee34754fa174368ee347d0ea948004ea9f40463d0c38b8d1d53e85d1c3638d1f43aa5d0da3b8d1f43aa53703405f178d1df3704197a3b8d1df1b26e0df14ef9b80464d0c388c11f42089d1c77cdc138d1b83aa3f31a18ea9b827981ec3646edb800e))) else (if i < 39 then (if i < 37 then 0x7aaf235c71a5ba7e01ad87b8fcc0f75ba3648f547bf1ad6c404617903df8d6b62700d6c3dc7f175b0f7634406e1152110c1de9f17476b8a35300dbd1eaca0791ae28d3c59808de8f56503c8d70b768d1d54854307804dd1ee3649a3823cdd1ee3642231a3cdd1b23dd8d107a06118f714c08462f8a0fc2b075a340f8dbd1eabc8d70b768d1b7a3d5791ae16ed1a37c507cbd07b87ca346f8bae17a51a20490ef4d6dae28d0d92ef4f8bad81f07a0af468fadb7a6b8f8b468bae1e46b6de814a8d1b5b6f4f8bae28d177a03f0ae1301f04136f4f8a10460a422a42018221827568d0f719c8a343dc7a3a8d1c81ee4de9ae35b1c804653aa3dc5ad8e40f719a9265ad8e40f729a9d407207b937a6b8d6c6a4e402337003bba8077d1eabc8b707761198548443041184118411841184208e810230823082309c8083a806104e46a019c8083a80672020ea018230aa03901047f17cc2f41ee40461ffdbd36471a26dfffdb21dc71a2ec8de8c6860fc37fc50a41137a31a0fa0a12238220836e36471a9e847ab6e38d4f45905552151c1b41b237a51a27c5b40ee28d2f42a820ec8de9468d013e2db8e353d0808c26d83f142b878089468329a8d07817c5770bd28d101b87e2d1a1ee3f8a46434878a00194c48f646f4a0042474002b878068194df17db123a004f8beda8d06527c5f6d468615fe28780ca1302251a3fb6d9146860382238200822083f17db18ea344125b7e801a027c5a346e07a187b51a3704e01b207b9a02700d91bd0d0108004d007806c8de8680832f6ff1a1b26e0a4736fec82466e0a6e03c68ea9b81889dbe754dc13e2f003706809a18711b83404113b7cdc1a02700b52f7f6413805a976db208f7e8d6c81941d902265b204364680a6404d04c8102309f4a34364648cfa6c81d1a1b23407400d00d91d1a1b2378660a8d0de1b243407d0680d921f4340b206c90d01233e83408680919f41a0434048cfa0d0210009a02467d06810d01233e8340877c6f0d919df1bc364677c918de19a01b237866806f0d91ef47abe606f107a8de16f4f303646f137a7981bc30461de9e606f0f800f71bc3de8c686f0c1b84548447042f0547077a686d71c6aeaeb636f4591ae38d1d55ba6de9adbcc6b81b255ba3645c00d48de1eb6de9ae38d1d52a8e0ef4b41ae36451a9806de8f56d06b8a34b22601f7a7c5b41ae28d1329807f8b6835c2f4a345de9ad9eada0d70b228d1d642dd12a90f009e83dc73d1eaac8d71c696e983c8576341e09f175c4f46344152111c11ea3646f0fcc0f71b230bc163437842383c027a0de18f51bc21ba3dc6c8ce2866470019c378963a5b0f71e8696c3dc73d2c70de970b20b3d2c76869712d8b3d3434b8634680a365640f71d8e1ee2046111c110c110c13403787b8c4707cc2c81ee390d3d053d07b8a7a067a04 else (if i < 38 then 0x4790148268477aafd20ad1a403fa34fd01f102951a7ba0f88135ea852a0016ca0fc1f0410884f8a0fa8d015203ea341487f141f51a02a402a0fe80052050502a134140c2901507a0a080541fd000a40a0b4000883d1857a340f81e900885207a30220b41e8e803d57e80d09a3b411d53e84c8ba3b411d53e84c8bf147113207a404611c5a08ea9f42645d1da08ea9f42645f8a3889903d268ed04754fa1322a0e0fc5e000901e90e47000480f483dfe2f000480f4bf178002407a40461f8ac001203d20110a0e0fc5e003a01e90e40e807a33903a01e8c0a850707470de05a07c83dc6813207a404611a04c81e8c6813207a302a141c11be1152111c16be1652161c10181f8a59c2ba0c3e8c68c81820303ed9061d5264440c101810cc0bbe2fb6418488c208377e0604d07bc000f9be2b1a07a3f8ac680603d20090b290b0e0a060ddff8a8e80f90db04548447046c8de03e3e00fd06c81f20df0b5f0b0e088e08f51bc07c7c03e28f503e4be83646f01f23290b0e08a9088e084de001e80f93807c50f407c8327800de0e4416fc006f07220df0ac80f5c001801f29c50b00f8a1e80f93e2b1a0180f480242d7c2c3828182238363a0604d07bc000f9ac7700f8afd00f978058ef6c3640f978058ef8a3d40f96c77c5e000f439146f8454840a840a840485af8594850304060423a0cbaa1375c07b990c69012c20f0281820302818212c203037d3e283d082508a0f02818248c266020303f14328446005a0a81820302140212c203037d01f0576340fca0f02818203025bbe2fb64181698d18870503058d4c80f003032940487e2c411ee0f48f546f71a1ee4752378208f7238e1bc1047b91948587042c04048409040486169dff8b1041e943b040484af850307cc5c51b20f48f7ce28dee34364afd0eef981b20f4afd2eaf981bc0f4ad7c2c383c016407a03e405a0301e8c048494850305645a01b20f490b46843a03e47bff16d003d23f4f8aedb8d03d2bf4f8b6801e904971a5900f4823820542054202420242d7c2ca42438281830568d3df8bc482aea62f0342415a3517860568d45e1815a351786f7e2f0341e86d04754fa1322e86d04754fa13229dff8a4c81e93436823e87549197436823aa7d099146c6823aa7d09914effc52640f49a1b411d53e84c8a81823404a8d93e8488bf144a9f42444f8a254fa12227c512a7d09110effc52440f49f144a9f424443bff149103d202ef8a254fa12228150a060fb63aa4880f90ea9a007a302a140c1c001c001c001c341c341c341c341c001c001c001c001c001c001c001245b74408c263a8d0f71b24e01715efec023df865b007c00eaec01ec08462e01619efec02700391b007619196c01ec04462de9adb5c0d9446578b104488e2089c344113c57aaf207ba23282309c8064b007b9011877a68e else 0xa02082d083f0ae0f81a111484e2858002e07a3452120c1404105a10aec68220d01050107cc6d51ea0f480b420f028a4248c20b42110a80341a290a0208f5f8a1c8fa03d29f4f8be603d03d286df31b541e902687207a373011be10ec10ec12be1452161c160c1f31b54fa03d20d97bfe626a83d2c2d1aafd38d0d92bf4f307746c83d2bf4f307741e90e47981b20f49717cc0d907a4096109616be161c1a01f17db42d2445072105a0ec0f8c36fc5a340b41e97e287a05a07c81b7e2d1a05a0f4bf17db02d0e4405a1100f8d6abf47901e9ee84137c50f40b40f901ec2d71cbdf6a87a0827f8a1e81681f206d7e90b5e403da346791ed96ad1a09a50f4fd3e2d1a07a5f6ce3a16bc807b468d4001683d1fc55714681683d2d0005a0f46b542b83d1bc80f407c6f201e92203e4f8bc003903d21c80e40f4680821b76a92207a4daa4881e8c6c12207a31efb549103d206d1b04881e936a92207a3daa4881e8c0602e07a3452140414461d30144615301d30101a257807c57e8090c137807b61b2090bc03e28f507a090a0344afc5e001e8121be2f0007a0908c01022220480f4a8111102403e41be1152110c102216be1652141c160c1f8a59f476820ae7d18d1c41044a9d50f40b43917471d5d704c88838237b8002403e40180581e8c470441040a850706efe8e09a0f78001f37c56340f4777c177c56340f4aca428382c18377f477c547407ca6d822a4221837174770007a3640f9b8068e7e83640f97503f408e364837c2c006485203e46001481e8daf850707805c5d1ded86c81f368eb8b7578d03d2db6d1c1361d0f503e6e01a3be28f503e5e01a3afa0d903e507c107c107c1652141c160c1152110c1d1d0b426f000f407cdc01db68ebaa3d40f9be2b000f407c97558d03d1a0e0b0608860dd512b7d3805c5048609a1118d07b220e0a0e0a0e0a0e0f0018410c1212fa7c507a104a1150704410431042707e2db68823dc1e97e29f41ee10480f820f820f820f82ca42c1822082054205428383f175003d1fc5e003e01210170650f61e406b000d2741c1f6c723500d909a541c1f8ba807a83d27c5f303dc1e92fa0241bd1041e941e050704e287db7001b00909ed806b1a2b0441c120c110c1f8a9047b83d27b61a07206c81f2bdff8a0375c71a28860882088208120812081508150b5f0b290c2d3e9f151103d28f5f8ba80fa03d2fc5d1c1c81e93e29f4d400f49f15db7981ee0f4bf175003d1ddff8bc681e906f84470447043b043b04af85948507058307e2f003e9a801e9425850705477c54441e80f97e2f9805a0f484a42838211c4af003e8090a08c20442838204428383f160ad1a7e84a0010e0abd50685f8b4681f03d205607c07c652408d000a40f4a0442301f1fc5a340441e900882b03e3f8be601f03d20150a40f47f168d01107a)) else (if i < 40 then 0x18760a5f09b60af4babc681e901758ef8ac681e943b052f84db076fd8ef8bc681e94410431043b06ea8d0e343d89ed8269506341f0a97c2ad823d3e2d8e0823dcbf16c74f41ef104a0fd8d0f707c405df158d03d20760a5f09b60af4f8bc681e9043044104410406b1a0f0194815c068656341e0a1d821d82ca42c383f152083d1a5f0ab60fc58822e41e93e2f981ee0f483787bc4107a4078101a1b6eaeb8e3451b1c687b0ce284830406fc5b1dae38d17800d01ec09c81942200d634540a97c2ad82f563b0341fc58ec4886f223b01f1bd579011de2d1a8ec6a351d8268fe286da351d89f168d4761b8e7ab1d81a11e447703e37911dc0f8fe2f1a1c00f49b7deaf1a07a4652161c160c15e97552084427c55e963920937a1d524407c9b7cea9a007a44be156c1dbf7212083d26df1bc0b40f90757c52640f49f14990f707a4dbe7549183d26dff8a4c81e912f855b076ffc52440f4838be292207a4dbe7209103d27c52443dc1e936ffc52440f49b7fe292207a4dbff149103d202edbff149103d2a5f0ab608dee3415c7c005b83d0ae4197c006c85720dee3415c632c6485703e41be111c16be161c13be37b8d05726c56347d02b90910de0ae324415c577f8003d1b207ca3658d03d1b0019215c1e9025858706efa3a1b207c86d8223823242324277c237c2208211c377d208471b24096161c119210bc19ba3244f7c6cc411bdf8823641e918705800c90ae0f4812c2374208d91ee4197104220c3e94208215c8c006485207a409611901e003787405721680ae21971042b8c1f83e08215c81783e62640d907a4191ae38d0d920de991c682b903db1a99015c812c3e61fa0d908e46be161c1be837a208d907a55abe607b83d24c81971042b83d280d191ae38d0d928d9991c686f057284b08de9903438d0572850084b0876084b095f0ed5a34f7e2f136ac5e2441489b568d45e1bf42441487b14ef9221b20f4a3d8910d91e82d8bb57641f42446d05b17641f42445d05b176aec83e8488da0b62ed51a07d0911b629dfdaa4881e97629f424415c87575c1320884d70488220c066b807607c9f145b8f603e4652161c160c1152111c110c1de83646f01f23df8743640f93cc2f41b211c8c38223837167a24108842d01104c68a804418796341e022105e0b711c87aaf4c7a83d2fc51eb1046ca42c3827142c68ac04419060b1a2a01107f175b79807a41ebf17cc0f407a5652161c160c1e01ad85b84403e516e2f02201f20bc16eae02201f2f00d701100f90c70f51bc07c84886f01f1ef42443780f90c70f51bc07c9bd0910de03e4de84886f01f26f4f8a4895c01f2b00d700ec0f915c078004470443058705830416842b92208834041b6dc005b84403e5e00b547a81f230016e1100f918002e07a3452161c160c111c110c16000b81683d210e0 else (if i < 41 then 0x86508650db8d902fa7a71a2fc59e8c681f9006fc5b70c6886d8212421e28d0650ae4f8a0283c51a0ca5077468328572078a341ec61e68d3dd0f040881ec3c5000d25f8a0343c51a0ca5018f549d03420f8d903dc9113db18ef8a3e09114c77c507a3e09117db300f8a3e091143084060cb1ca364a094968e1d9048ca09430876fe863aa5049b7c449d5282425a638728d0282531c3946814127c531c394a0903284b3ed53e8c6b6415af8581058d6c807e3f307d06c8d008e53e86806cac808e5daa7d36412221f4d904887b54fa6c82444daa7d06812226c8daa7d09104d2ed53e9b209110eff981b23782394efac81b2504877f6a9231bc11ca364681411fb6340365640472f981bc3d41e91e2ef4e343641e97800de0e40f48e3b7a0dee340f4bc006f0f703e4152111c1652161c13abc0046a43c006f0721eb6d0dbd35c1d526469e9b238d0f720780878083c0b290b0e08a9088e0ef4f303646f0472af4e34364239187044706eacf41bdc681e942f0780046ef1a1b23dc8c38271437558d0f7183c0843b1df158d0f7283c0cc8de97578d0ce07a60a010bc116e159163b8d0d91ee5b1db238d0f7208e08860b1a07c3d41f901e059487cc0de1ea0f482dc2f546f71a5ba47aab778d0f727c571dc687b903c043c041e041e05948587077a1328bc110917891044183e2f981ea0f48360910f718d82443dc7c004abf41a009cbc0072bc5f6c11c6c8273f00f8a3dc1393800951a01e81397800e577034013958022204e14882491100704e41be1152110416be16521604125ba3b437b63aa4c8da3b645f4e3440ca10ca1024160411041f6de606c8d008e51be16be160411041d1db238d0f7268ed91c687b93805f4d403642397e2b1a1ee3be9f16dc31a20120b2908a909c50b1a0b420241b8b75780095be8340139ee2fb6baac683d942804280443040904e2bf41a1c686c95af858106fa7c5b6cc681f940906060e53e93211117e2e8e3e9c687b97db3d51a0f178d17e2fb61ca88897d06c8d078bc68a37c2238223821942194204820482ca42c0820f020482238205420483195d48438a00d0b469fa450192d1ca754fa132292d1ca754fa132292d1ca754fa1322823092d1ca754fa132292d1ca754fa132292d01a394ea9f4264625a394ea9f426450ca125a77fe28e52825196254ef8d928250461f8a77c7294121dff8a394a0900a844a9d52823f8a2546c94120150bd5e343d82691db7c5e343801e97e2bb6e343d41e97e2f001c007c8037807c51ec1c8a035c77c5e343d8bc03e28f603e40988107b87307a54081f07b81f20a9088e08860b290b0e0b060edf3abae0991041055b0417066dbff175c12230820ab6082e02c0336ffc5f300f4e37c2ad837558d03d18760a5f09b60e82baa1343ddc56353d0e1d82ca42c382c1837558d03d else 0x1ebc00648c3d5b6e003e01b20fa0c7af0010d9e002b8bc005c0023d07aac8e004e00b744edb800b801dd17007e971467d3803dd1847e002b8a137800c23f005e83e00bd043dc2bd3801dd184d5e97178010269c81700390261c1e00f14563b800b8005870762f0017000f0009f4e0023bfc005c016e881edb687431ee7d05c03629f41f009ba2e013205c02640806f0010c9e002e01b144c382bd023eb81b0e0cf4e00b746c383c016a8b9183de007746c383c005c03d1b0e080d76dc007c003c016a8b8007804d5170076d3546135e2f0019f4e00f146f7ee2f001f00083db8afd380101ef003ba3e007d07a8c26db6e00f549c0036881ebdde00308fc00477423c3a19d508e2e007744f17800823c8ee003e01714411e470b805b617007aa7747c00e40c9186de000347c00268b80047170007a2e001173c005c01db04d1bb64742e001391c005c015c0b801df13dd1ee2e00f545c01e2a8e184d09c5808261c161c1e003244ed85ca3a1f000c3a0f009902e00b205c003c01db0b7a6d5d91ae36e922368edbbc687b93806f4d4036423975b68ee00f575c07236b617cf207bf1a2fc5d6da3b800f703e6152110c107c1652160c10873d3e2b1a1ee5d1d3778d0f51b211cdbd18d0d908e4d1d756e431a1ee51e81d1d7558d0f72043d1d7218d0f7283e083e0fc507f4681f0f7283f1ea15a8d03e2ef4a345641f101f83ea3415c9bd3e283fa340f8a0fc2b03e0684de9f141f51a07e5de80f82b51a07e5f8b4681f0f723d57900fa8d0f72d1a1ea0f87f141f51a1ee407fada8d0f507c5f8a0fd7a51a07c5de8f55e403f5bb4681f1fe28f5a340fc9ad9e4034183e083e0eb61a04c87b90681321ee3046176c3976471a1ee571dbd36471a20e5f8bc037a01f2f000f00087d6341486c003e828188e088208610b0e0b0208780))))))
def hx11 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xe00f800002069bc33e00001020cc1dc80000a0bb4000031d0642bc80a34005a702988202000000000000000000608e4038700000000000000000000002c2ef70d4081801075f02bd20d9b41ea90002009091cb80000509b640a1000000000609b101001064882fc50d2e42f4b0b1a43049088fc18a70d700000f079c0000300b783793691fc14f00000834e0081a017aa05ad424cd06f842f27033b4075a0bb946baa0050001a40bc5413d0000141c400000418fb1837035d00001cced0001d020f705228048b0116d66f50b8741cd20b1f4178547440000e0c05831e0000301ec000000000f05ab8101c011841e000002c0c100001c1da000000000c091b014b9057800004070202cfe0b1202d1d100340ff000000000a065c0000104d84065000000000c091f061341ac48308e070a42d9f0060c17dd0a1e027dc08d14365202dd0141c00b84081000000000a35c00000000000000000000000000000000408ff403130897c31c8140cc188f0bd5038a50be100be212d400000000200c400001802a000000000704ee8114c05d2464e30c5280700374800b00055a812d406aac013e20a301e1500b1432e41ba88267000000000501bd00e4205e6025b202bbc1f7d0a640000c057e838171cb040abf0a54412600001c0ebf0acc0000000000000301b601f000001942a0000142d250a77c2dba09a000000036081db905b981e9e07b40000b03300000502f240a0000000000e11380000d081400b3f03780000803f00000402dac32730d3d425fa18c8000040308000000002405e111ec0000e0c5ec01ca055241a90000301718093980343060a835340b9ec09b70b7800005087b4093404ac4322e038bc20700002027700000000090850000000001c2a600003838900003827f00001804f000000000e0bac000060b240000f0afc000000dfb0290e446da113801fd0285a01a1406020674000010108c1d5c0441434500002020e00000000040555c07d0000003750000000001093cc0acc181740f2105b400000000200e3b00fc0000b0342c06630630c06b50cd400002815d03400452800000c03421c354000000235a45b2e50821c228800404060078100a0c40c22450813cd0401010400821451402020802003831840420c320011a34e08001200008620010038e08100000058358218806b2c40465a80844c908014a04a3c00c18511ce0006550001030021050430140810030824411420846c11400c000035c0050061c00c100f000ac12c10c108d0c70003c12400400c01840c014815e0850801c000400400354404100118f0420000420050400402830000000c10402800030461c70010400811400400803811c00021041401c504008014a7800030010012001860401000041400010061810031092c200100200304b0070400d4 else 0x3be80cdd06d4c22ea04e0c2d58052481fd0000000000000081e400002c08e000000000a01c80000907380000a0bb0c233000024316a0e14000030a97007100003026f00003819000000003230c3e41b7708800000e0c7d80b25158ac216f02a5022d509c34260508c401c780c754079f02640000a0032c2e00000000003141a8215d005c000091414c07c20dff42d60000281bd500ac8725d04d6e82b90e4104c0b1d0a8380c9c1e82890000242b700001c1d430a0d4384a0292819c207db0089e03e80000691b102c500a13000a404c3c3151059ec1e3a0bab81a240db9c1f1907248355610f78341c0317c307c0ac80000009e8000090b6881b100d7ac3360000341e5000000000e0c9880f6609d502523024b020d9049200efa0e2cc1c5f1c5a817e00001037c10420000070b4c00003006ec82e00002876700000000000001c16570a0000000054c0000007d3c3237098c0000e1b86c2a0106ba0116403840000a0b7c811ff05c8c30e2041040c300002c11700000c265a060d40d4f0a880000504de02e48050803739031a092da04340000000000000a0111c06c00001c0c80000202410000302f6a0a20032dc0e0dc00d000024119202180000e007c00000000101eb0000201d821863031901caa4249e0c8682e9b00d44386106bf84ff806af81ac003ab40a3d0373822800477c10e706618143784b1c1d3f0dd80279806c1024b31e3289a000b294019b042c859cb05fdc120c0190809c208898274809bb801251401c1f9f0de0c05790c358282c08440000d167c000070189c122469b400000000169766181046354040d8061600bc00002070f819f00003c0d1a0bef004e000000000b054602ba6167980c0103e6838cc0a2d430910174019470775c2274a743024a00a5dc2fd10348417b40b94c11bd0092028ea09860121e03d7813c0971a003b841a9c0e6a0b8a406a400954210b040b428640d4bc023e0cc3807a400e48118c0b07c2ac71acd40ee00001403370953810ca1bac46bb5074500a760c1482f000002801161c7fc354c00a00000d0a7340d6a1949020a909200000008740000000000000b08d4000040150000010e23071d8036800000000300ad907214016204720328d0748ac2ff03e2c0b1c0a7f011e50157021b4061d0203d02bfc2ae60a06c32961d2c012c0000182ff2060681ad50b76c095e0cef413e607580000000024340a001703620017c0000f0172834a0000000000000302abe03280000f037c000010208c0530000381b400000000000000000060c4e425600001c29310277465600003033a0000000000000000000000342b0103a4000020cd3c16100000000000002c00b709ac0000b01f8000070d0c000031b7e82e8a04c8000010b8c804904a8b404d7018c430b602a00000f0678c1fbc0a4582040000000) else (if i < 3 then 0x902f6435b30a8f0111502e14351f042541b3b041f02fe309644186b31ae0262d06e34359609410163202e6c0bb000008243803ec0000000038364000034030e05a18370b0b37014a408f4c21340cc78333c05a6c1ff3010d865cc0d83878e000740000d07eb837170b2102e6a0b2cc212308ebc75300002031140a3c000000000813a50cbc000000000000000002836d00000000070af8c245a06ea463390ad926a9d0c42835a00003c073c0b080000a0885815ce00814372000014357c09cdd9a0e1ac800009035601de306540000c097281153069c000000003c27baa4b40000b032501b60000000000000243251025c40ba80d5b404cc022c0000f03f400b589b6c0000302100000c07a1415000000000000003803870a7bc24d30ad7415700003808c308674026407040000e0d87818e1039400005053302c300002403600cc80000c07c8000000001c36a604b8c19a80201026a5086300dd20d08000000000000070956c1fc10614000050820000090416000e00003825810c000000b0ce40000609f881cc9033fc0dbb0468021f40664000000003824240c80c1fe70599c2cc80771c0298012d4047000014232f07bfc14dd04a0c1df00003031259be28244c09c800000000081b200583c01e90a68000000003c0521021c0000f01ed4377607280000b019e472d000000000000000000000000000000000000d09914176e0024c37a40d258027b051702ceb12fd42f75034fc2942a0a80000c0d8d40a50000002a1b054800000000102f3607d6c23e90365423850a4b646b5072e814400000000000000000000002c088000000000a0d300000d0df400000094440d7c01580000000000000000000000d0008831b8005581f8909a6c19b00000000070741861b431b18296000024112a03c741f3000024226b0ad00000004a94134f07b941b9c08f0000000002438f901a7c20b000000000f05670367505f3820150160000050870438e0000101a380abd46083039c00002032c0000002880000b0144c09660db2808f50ca8810f900dd82a430ce0000061b7542adb08010615016d083482027b405081637425e00001c71b002140000f08ad81bcb0419c14060613c0e0000016b2a404fc000020be803748681a030c108ed8113f0e358076d04e54271804c4022900000000090b5d42a700000000000000000000000000050a6200740000201581020e433c00000c2d800000000000000000061674000000002c25a0000085890000341a4000000324804a7825d0000140ed31423c257b0890000030cf400000000282f950aedc34751830c3445056d408a0000000000000000000000243589082401e210da7c28a9023442781008a80f380d7e000410caf4006d0006c1256065b40bf1a else 0x100aae08de851f144d00000106810193b049c00782166d01a8e0ae7c14600001031a000008306000000000d08ab809800001c59400002c164f05698303b073c000000000842f00002c43000001c600e05b20230c868102c000c280000303a00000d10b808c3f09f2405b000000000000000000c0dac00004085c0000709da01d9d0104000000998000000001c22c703b00000000000000f090000000053b0177d068744732003e412f605cd2c6ad04cc0000b062f43370000102aa306ec000090b500000903c3e028a07980000000008021a08d80000903d3c36fe048d00b4d00f7016fb0719007700000000000001822f2042ac15d000000000000000000000008368c05c00000f012800000000000002371bc0f7e00400000b5932428c000011ea60000000000000282b80000203825026a4302c0d180000c0b400000b0ac40000000000000000038253000000000906fc878a80aa000fe0000e829b2058a803a00d36409fe50ac814770644805911d3b02dc70cb08175b0252c37b201b8000020c6102a90000304b4b0cfd00c7b0100000000001c18d40020409100000018900000000000000000000002c21ab00f000000000381a5000000))
def nd12 (i : Nat) : Nat := (if i < 7 then (if i < 3 then (if i < 1 then 0x2ffaaa4ca00f7e9dd32803efa664ca00fde95532803fba444ca00bfe62932802ff97a4ca00bfe5a932802ff94a4ca00ff65cd32803fe9824ca00ffa50932802ff88a4ca00bfe169328027fca94ca00bfe2a532802ff8a14ca00bfeaa981803dfa7760600fbe99981803f7a5560600fee91181803fda3360600ffa88981803bf98660600efe609818027fca960600bfe2a5818033fc8960600efe22581803ef8a660600bbf29981802ff8a560600bfe28d81802ff8a260600bfeaa971803bfa885c600fbe99971803f7a555c600fee91171803fda335c600bfe62971803df9875c600f7e5d971803df9725c600bfe229718027fca95c600bfe2a571802ff8a35c600efea2161803dfa7758600fde95561803fba4458600ff68cd61803fea2258600bfe62961802ff97a58600fbe58961803ff18158600bfeaa951803efa6654600fee91151803fda3354600bfe5a951803ff18154600ffc5c5518027fca954600bfe2a5518037f41954600ffc06551802ff8a354600bfe28951802ffaaa50600efea2141803dfa7750600fbe99941803f7a5550600ff68cd41803fea2250600bfe62941802ff97a50600bfe5a941802ff95a50600fee61141803fb96450600fee50941802ff88a50600bfe16941802ff8a250600bfeaa931803bfa884c600f7e9dd31803efa664c600fde95531803fba444c600ffa88931802ff98a4c600bfe5e931802ff96a4c600bfe56931802ff94a4c600ff658d31803fd9324c600ffc60531803ff1414c600bfe22931802ff85a4c6009ff2a531802ff8a94c600df70e531803fd8394c600bfe28931802ffaaa48600efea2121803dfa7748600fbe99921803f7a5548600fee91121803fda3348600bfe62921802ff97a48600bfe5a921802ff95a48600bfe52921802ff93a48600ffa58921803ff17148600ffc4c521802ff88a48600bfe16921802ff83a486009ff2a521802ff8a948600dfb0a521803fe82948600efea2160803dfa7758200fde95560803fda3358200ffa88960803ff21158200bfe5e960803ef96558200fbe58d60803ef96158200bfe29560802ff8a358200bfe28960802ffaaa4c200fbe99930803fda334c200ffa88930803ff2114c200bfe5a930803fd9314c200bfe28930802ff8a14c200bfeaa920803bfa8848200f7e9dd20803efa6648200fde95520803fda3348200ffa88920803ff21148200bfe62920802ff97a48200bfe5a920802ff93a48200ffa54920803fe92148200bfe22920802ff85a48200bfe0e920802ff8a148200bfeaa910803bfa8844200f7e9dd10803efa6644200fde95510803fda3344200ffa88910803ff21144200bfe62910802ff97a44200bfe5a910802ff95a44200bfe4e910802ff92a44200ffc54510802ff88a44200bfe16910802ff83a44200bfe0a910802ef8a660600 else (if i < 2 then 0xbff16921803ff83a48600bff0e9218037fca948600ffe2a5218037fc8948600ffe225218037fc5948600ffe165218037fc3948600ffe0e521803ff88548600ffe20d21803ff85348600ffe95560803ffa3358200ffe88960803ff98a58200ffe5e960803ff98758200ffe69560803ff98558200ffe5d560803ff9a358200ffe60d60803ff97358200ffe54d60803ff9a258200ffe60960803ff97258200ffe54960803ff93258200ffe60560803ff97158200ffe54560803ff93158200ffe48560803ff85358200ffe14960803ff83258200ffe88930803ffa114c200ffe5a930803ff9764c200ffe58d30803ff9a24c200ffe60930803ff9724c200ffe58930803ff9324c200ffe68530803ff9814c200ffe5c530803ff9614c200ffe54530803ff9314c200ffe48530803ff8824c200ffe20530803ff8514c200ffe08530803ffaaa48200ffea2120803ffa5548200ffe8cd20803ffa1148200ffe62920803ff97a48200ffe5a920803ff95a48200ffe4e920803ff98748200ffe61920803ff97648200ffe61520803ff97548200ffe59520803ff98348200ffe5cd20803ff96348200ffe54d20803ff98248200ffe58920803ff95248200ffe4c920803ff9a148200ffe60520803ff97148200ffe58520803ff95148200ffe4c520803ff92148200ffe22920803ff85a48200ffe0e920803ff88548200ffe20d20803ff85348200ffe28520803ff88148200ffe14520803ff83148200ffea2110803ffa5544200ffe8cd10803ffa2244200ffe62910803ff97a44200ffe56910803ff93a44200ffe4a910803ff98744200ffe61910803ff97644200ffe61510803ff97544200ffe59510803ff98344200ffe5cd10803ff96344200ffe54d10803ff98244200ffe5c910803ff96244200ffe54910803ff93244200ffe60510803ff97144200ffe54510803ff93144200ffe48510803ff88544200ffe20d10803ff85344200ffe20910803ff85244200ffe0c910803fba445da00ff68cd76803bfa8859200f7e9dd64803f7a5559200ff68cd64803fea2259200ffc84564802ff97a59200bfeaa963803dfa7758e00fee91163802ff97a58e00fbe591638027fca958e00bfe2a563802ff8a558e00bfe28963803efa6650e00bfe5a943802ffaaa60a00fbe99982803fba4460a009ff2a582802ff8a960a00bfe28d82802ff8a160a00efea2172803efa665ca00fde95572803fba445ca00f7e5cd72802ffaaa58a00f7e9dd62803f7a5558a00fee91162802ff98a58a00bfe5e962803ef97658a00fbe58d62803fe98258a009ff2a562802ff8a958a00bfe29562802ff8a358a00bfeaa942803bfa8850a00f7e9dd42803efa6650a00fde95542802ff98a50a00bfe5e942802ff96a50a00fee5d142803fb94350a00bfe22942802ff85a50a00bfe2854280 else 0x3ff97558600ffe61161803ff97458600ffe60d61803ff97358600ffe50d61803ff98258600ffe5c961803efd6258600ffe54961803ff94258600ffe4c961803ff58158600dff16561803ff85958600dff0e561803ff83958600dff0a561803ff82958600ffe14d61803ff85258600ffe0c961803ffaaa54600bffaa951803efe6654600ffe8cd51803fde3354600ffe5a951802ffd6a54600ffe5d951803ff9a454600ffe59151803ff9a354600ffe58d51803ff94354600ffe68951803ff98254600ffe5c951803ff96254600ffe50951803ff93254600ffe60551803ff58154600ffe5c551803ff57154600ffe681518037fca954600ffe2a5518037fc3954600ffe0e5518037fc2954600ffe0a551803ff8a354600bff28d51803ff8a254600bff28951803ff88254600ffe0c951803ffa8850600ffe95541803ffa2250600ffe61d41803ff98650600ffe5d941803ff97550600ffe59541803ff98350600ffe5cd41803ff96350600ffe60941803ff97250600ffe58941803ff95250600ffe4c941803ff98150600ffe5c541803ff95150600ffe21541803ff88250600ffe14941803ffaaa4c600bffaa931803bfe884c600f7f9dd31803efe664c600ffe95531803f7e554c600ffe88931803fee224c600ffe62931802ffd8a4c600ffe5e931802ffd7a4c600ffe5a931802ffd6a4c600ffe56931802ffd5a4c600ffe52931803ff9874c600ffe61931803ff9764c600ffe5d531803ff9654c600ffe61131803ff9744c600ffe59131803ff9544c600ffe60d31803ff9734c600ffe58d31803fdd634c600ffe54d31803ff9a24c600ffe60931803ff9724c600ffe58931803ff9524c600ffe50931803ff9324c600ff74c931803ff9814c600ffd60531803ff9714c600ffe54531803ff9414c600ffe68131803ff88a4c600bff22931803ff85a4c600bff169318037fca94c600ffe2a5318037fc894c600ffe225318037fc594c600ffe165318037fc294c600ffe0a531803ff8854c600ffe28931802ffca24c600ffe20931803ff8524c600ffeaa921802ffeaa48600ffea2121803bfe8848600f7f9dd21803efe6648600ffe95521803f7e5548600ff78cd21803ff98a48600bff62921803ff97a48600bff5e921803ff96a48600bff5a921803ff95a48600bff56921803ff94a48600ffe4e921802ffd3a48600ffe61d21803ff98648600ffe5d921803ff98548600ffe5d521803ff96548600ffe61121803ff97448600ffe59121803ff95448600ffe60d21803ff97348600ffe58d21803ff95348600ffe50d21803ff98248600ffe58921803fed6248600ffe54921803ff94248600ffe4c921803ff98148600ffe5c521803ff57148600ffe54521803ff94148600ffe4c521803ff53148600ffe68121803ff88a48600bff22921803ff85a4860)) else (if i < 5 then (if i < 4 then 0xbffaa962803dfe7758a00ffe95562803f7e5558a00ffe62962802ffd8a58a00ffe5e962802ffd7a58a00ffe61d62803efd7658a00ffe69562803ff9a458a00ffe5d162803ff9a358a00ffe5cd62803efd6358a00ffe50d62803ff98258a00ffb60962803ff9a158a00ffe681628037fca958a00ffe2a5628037fc5958a00ffe165628037fc3958a00ffe0e562803ff8a558a00bff29562803ff8a358a00bff28d62803ff85358a00ffea2142803ffa5550a00ffe61d42803ff98650a00ffe5d942803ff97350a00ffe58d42803ff98250a00ffe58942803ff88a50a00ffe16942803ff88550a00ffe28542803ff88150a00ffe14542803ffaaa4ca00bffaa932803dfe774ca00fbf99932803f7e554ca00ffe62932802ffd8a4ca00ffe5e932802ffd7a4ca00ffe5a932802ffd6a4ca00ffe56932803ff94a4ca00ffe61d32803ff9864ca00ffe5d932803ff9844ca00ffe5d132803ff9644ca00ffe60d32803ff9734ca00ff75cd32803ff9634ca00ffe60932803fed824ca00ffe58932803ff9424ca00ffe68532803ff9a04ca00ffe22932802ffc8a4ca00ffe16932802ffc5a4ca00dff2a532803ff8a94ca00dff22532803ff8894ca00dff16532803ff8594ca00dff06532803ff8194ca00ffe21532803ff8a14ca00bff28532803ff8814ca00ffe14532803ffaaa60600bffaa981803dfe7760600fbf99981803f7e5560600ff78cd81803fee2260600ffe69d81803ff98760600ffe69981803bfd8660600ffe5d981803ff9a560600ffe69181803ff98460600ffe5d181803ff96460600ffe68d81803ff98360600ffe5cd81803ff96360600ffe50d81803ff9a260600ffe60981803bfd8260600ffe5c981803ff96260600ffe54981803ff94260600ffe4c981803ff9a060600dff2a581803ff8a960600dff16581803ff85960600dff0e581803ff83960600dff0a581803ff82960600fbf29981803ff8a560600bff29581803ff8a360600bff28d81803ff85360600ffe28981802ffca260600ffe14981803ff83260600ffeaa971802ffeaa5c600ffea2171803bfe885c600fbf99971803f7e555c600ffe8cd71803fde335c600ffe62971802ffd8a5c600f7f61d71803ff9a65c600ffe61971803dfd765c600ffe69571803ff9655c600ffe69171803ff9845c600ffe59171803ff9a35c600ffe60d71803ff9635c600ffe50d71803ff9a25c600ffe60971803dfd725c600ffe58971803ff9525c600ffe50971803ff9325c600ffe60571803ff9a05c600ffe22971802ffc8a5c600dff2a571803ff8a95c600dff22571803ff8895c600dff0e571803ff8395c600ffe28d71802ffca35c600ffe20d71803bfe8858600f7f9dd61803ffa5558600fdf95561803ffa3358600ff78cd61803fee2258600bff62961802ffd7a58600ffe61d618 else 0x803ffd6260600fff54981803ffd3260600fff29581803ffca360600fff14d81803ffca260600fff14981803ffc3260600fffaa971803ffe885c600fff8cd71803ffd8a5c600fff69971803ffd865c600fff69571803ffd655c600fff68d71803ffd835c600fff58d71803ffda25c600fff60971803ffd625c600fff54971803ffd325c600fff60571803ffc8a5c600fff28d71803ffc835c600fff95561803ffe3358600fff88961803ffd8758600fff5d561803ffd8358600fff5cd61803ffd8258600fff5c961803ffd5258600fff4c961803ffc5358600fff14961803ffc3258600fff8cd51803ffd6a54600fff5d951803ffda354600fff58d51803ffda254600fff60951803ffd7254600fff58951803ffd3254600fff60551803ffd7154600fff20951803ffc3254600fffaa931803ffe884c600fff95531803ffe224c600fff62931803ffd7a4c600fff5a931803ffd5a4c600fff61d31803ffd864c600fff5d931803ffd754c600fff59531803ffd834c600fff5cd31803ffd634c600fff54d31803ffda24c600fff60931803ffd724c600fff58931803ffd524c600fff4c931803ffd814c600fff5c531803ffd514c600fff22931803ffc5a4c600fff21531803ffca24c600fff20931803ffc524c600fffa2121803ffe5548600fff8cd21803ffd8a48600fff5e921803ffd6a48600fff56921803ffd3a48600fff61d21803ffd8648600fff5d921803ffd8548600fff5d521803ffd6548600fff60d21803ffd7348600fff58d21803ffd5348600fff60921803ffd6248600fff54921803ffd3248600fff60521803ffd7148600fff54521803ffd3148600fff21521803ffc8348600fff14d21803fde335da00dff0e576803ff8395da00ffe95564803ffa2259200ffe14964803ffaaa58e00bffaa963803dfe7758e00ffe62963803ff97a58e00bff5e963803ff9a558e00ffe69163803ff97458e00ffe5cd63803ff9a258e00ffe68563803ff9a058e00dff2a563803ff8a958e00dff16563803ff85958e00dff0a563803ff82958e00ffe29563802ffca558e00ffe28963802ffca258e00ffe14963803ff97650e00ffe20943803ff88150e00ffe14543803ff82150e00ffeaa982802ffeaa60a00fbf99982803ff9a660a00ffe5d982803ff9a460a00ffe59182803ff9a360a00ffe58d82803ff94360a00ffe68582803ff9a060a00dff2a582803ff8a960a00dff0e582803ff83960a00dff06582803ff81960a00ffe28d82802ffca360a00ffe28582802ffca160a00ffe14582803ff83160a00effa2172803efe665ca00fdf95572803ff9865ca00ffe59172803dfd735ca00ffe58d72803ff9435ca00dff22572803ff8895ca00dff0e572803ff8395ca00dff06572803ff8195ca00ffe20d72803ff8815ca00ffe0c572803ffaaa58a) else (if i < 6 then 0xac3a753a483a0739d039993980394938fe38db389a38633840381337e637b93778374b370036d336a6366f3642360b35de35b135843557352a351134e434cb34803467344e341733ea33b33372332732f032b932823255322831f131ba31793142311530de30bb308e3057303430072fe42fb72f6c2f212ee02e952e4a2e132dd22da52d502d052cba2c792c1a2bed2bac2b6b2b5c2b4d2b0c2acb2a9e2a712a442a0d29ea29db29cc299f295e293128fa28b9286e282327e227a1276a270b26ca267f2652262f25ee25df25d025a3256c252b24e0249f24722445240423d723aa239b238c237d233c22fb22ba2279224c221521ca217f215c212520ee20c120b220a3206c203f20301fe51fa41f6d1f361eff1ebe1e871e501e231e001dc91dba1d8d1d561d471d381d291d1a1ccf1c8e1c431c0c1bcb1b8a1b3f1af41ab31a861a771a541a131a0419d719961969193c190518d818971842181517de17a7177a174d171616df16b216851658162b161c15ef15e015d115ae156d151814eb14aa14871446140f13ce13a113741347131012ed12de12cf12c012891248120711d01199116c113510f410a910681031100e0fe10fb40f7d0f500f410f320efb0ece0ebf0e920e830e420e0b0dd40d9d0d660d390d020ccb0c8a0c490c120be50bae0b810b540b1d0b0e0aff0af00acd0aa00a910a6e0a2d09e209a10956091508f2089d085207fd07d007c107b207a307800735070806d1069a064f0618060905fa05cd05aa0573053c050f04e204b504880465042403e303b60389035c034d033e032f032002f302bc027b0258022b01f401c7019a016d012c010900dc00af0082004b003c002d001e000f0000fff8cd76803ffeaa58e00fff62963803ffd7a58e00fff69563803ffd7358e00fff68963803ffda158e00fff29563803ffca258e00fff14963803ffeaa60a00fff69982803ffd7660a00fff68d82803ffd6360a00fff68582803ffca360a00fff28582803ffc5160a00fff0c582803ffe885ca00fff61972803ffd635ca00fff20d72803ffc815ca00fff0c572803ffeaa58a00fff95562803ffd8a58a00fff5e962803ffd8758a00fff69562803ffda358a00fff5cd62803ffd8258a00fff68562803ffca558a00fff28d62803ffc5358a00fffaa932803ffe554ca00fff62932803ffd7a4ca00fff5a932803ffd5a4ca00fff61d32803ffd864ca00fff5d932803ffd834ca00fff5cd32803ffd634ca00fff60932803ffd624ca00fff68532803ffc8a4ca00fff16932803ffc854ca00fff28532803ffc814ca00fff14532803ffeaa60600fff95581803ffe3360600fff88981803ffda760600fff61d81803ffda660600fff5d981803ffda560600fff68d81803ffd8360600fff5cd81803ffd6360600fff68981803ffd8260600fff5c981 else 0x749f479f249ef79eca9e899e5c9e1b9de49da39d769d3f9d1c9cef9ccc9cbd9c909c819c549c279c189beb9bdc9ba59b6e9b419b009ad39ab09a8d9a4c9a0b99e899d999b699a79984997599529925990298df98b2985d981297d197909763972c970996aa964b960a95dd95b0955b953894d994989457942a93fd93da93b793a8938f93809349933a92f992d692c792a492959254921d91d29187914690f190ba9079904290018fde8fbb8f7a8f578f208ef38ebc8e858e4e8e0d8dd68d958d688d458cfa8cb98c6e8c238bf68bb58b7e8b3d8b1a8ae38aac8a6b8a3e8a0789c68999896c892188f488b3887c8859884a88278818880987f087e187b487a5876e875f873286fb86d886c98692865b862485d98598856b853e850784da848f844e842183ea83c783868345830482b982a08255821e81d381a6816f812e810180d4809d8070802f7fee7fad7f6c7f5d7f447f357f087ef97ec27eb37e867e4f7e2c7e1d7dfa7deb7db47d917d827d4b7d147ce77c927c517c107bcf7b987b577b167adf7a807a3f7a1c79db79a47977791878eb78967855782877dd777e773d771a76cf7698767f765275fd75b27567754475217512750374ea74db74a4749574547431742273e173aa735f733272fb72c47283724c720b71c0717f715c7125710c70df709e70857058703570126fdb6fa46f6d6f366f276f0e6eff6ee66ed76ebe6e916e6e6e4b6e1e6dd36da66d796d4c6d1f6cca6c896c5c6c2f6bee6bad6b806b3f6afe6ad16a866a456a0469cd69826955691468fb68c468ab689c686f68606833681a680b67f267e367ac6775673466f366b26653663a662165e0659f6568653164fa64b96478644163f663c9639c6365633862f762c062896252620761d0618f61626135610860db60ae606d60225fe15f8c5f5f5f145edd5e925e655e1a5ded5dac5d755d345cfd5cc65c995c6c5c355bea5bb35b7c5b4f5b185ad75aa05a555a1459f159ba598d5956591558ca589358705843580c57fd57d057c15794576757585721571256e556d656a956725645563655ff55c85591555a552d550054c9549c546f5442541553d4539d537a532f530c52d552945249521c51db51a45159512c510950c8509b5050500f4fce4fa14f604f1f4ed44e894e484e1b4dee4dcb4d9e4d674d304cf94cc24c9f4c684c314c044bcd4b8c4b734b504b414b1e4b0f4aec4add4ace4ab54aa64a794a6a4a3d4a2e4a0149ca4993495c491b48da4899486c483547e047bd477c473b471846cd4678462d460a45c94588453d44f244d9449844754448442543ee43b74376433542f442b34268422741fa41c3418c4141410a40dd409c405140243fe33fac3f6b3f343ee93ebc3e853e583e353dfe3dd13da43d773d543d1d3ce63caf3c6e3c413c003bd33ba63b653b383aed3a))) else (if i < 11 then (if i < 9 then (if i < 8 then 0x754be29415c2344ffaa0ae31a720bff3e95078b5c6346755c8a81c5ae31a364efa541e29707b8826ffaa0756b8c68be2d70118fc53df1a2e09ff3915c6344ffbc5a81f4c68acc78bdb046437c25487b6f143e0551a2d1de2d708d100e0a01e29402090860819ff571646346f1bfeae2c8c69f42f6ceae34641bc5f15f42e041378bff5915c634ea95a0b22b84689ff60164570d017fe7d2c8ae31a2f6cea9906ce346f19f4f14b83dc41378dff3ab645718d1598b22b808c9ff341645718d14f7c68de2e086ce346f1904ffbb6682c8c68a6f84a9091c10551a1787e2f6c8d1bc40182642346f0eb83d7c58ea1a3d0d5c5e8eab911d4346e9eb8bd2b67561a904d5c5e9e2b1d5b435209eb8bd2b67221a904d7a78a208ef4755c8ae0d93dcdd86907a1705b074ea9ef0d1cf42d8b80e98e374f78691001e9e288242a424704860f8bdb0443a39b67d3c5889b8868f0d78bdb0444a3bb6889c8868b4778b113710d15f46d9b8a39dd3de1a391de2844dc434521824107b6030c88688fa5910d0c4aed9d5868c82b6cfa371644345ed9a9b221a276cc75910d13b6030c88688dc5900643447d2c88686ea895db1b30d19067d1b86dac83de1a331ddb5910d1086ed9d586886437006434437c254848e090410b40cf14412505e2be90d4825ae1c5755c886a4133e9e28823ae1d586a412571e2b1d0d4825ae1c886a41278a168182091f4f16b88688e2baae45706cc3467d3c51046ead7016c34463bc5ae21a23915c0190d10820e9d50b61a29be12a42470486096c1d56bd534d4fdd4bcd485d430d3f9d3b8d36dd322d2cdd2a0d269d228d1f1d1b0d179d138d0edd0b6d06bd03ed007cfbccf85cf4ecf17cee0ce95ce68ce31cdd2cda5cd78cd19ccd8ccb5cc7ecc47cbfccba7cb5ccb25caeecaadca80ca3fca08c9bdc986c94fc90ec8cdc878c841c80ac7bfc77ec747c6fcc6c5c684c64dc60cc5dfc5a8c567c530c4f9c4ccc495c45ec3ffc3bec391c35ac323c2f6c2abc26ac23dc210c1cfc1a2c175c13ec0fdc0bcc071c03ac003bfb8bf81bf22beebbea0be41be0abdbfbd88bd51bcfcbcbbbc8ebc61bc16bbd5bb94bb5dbb08bac7ba86ba27b9f0b9afb964b923b8ecb8b5b87eb83db810b7c5b784b725b6eeb699b662b621b5d6b595b55eb531b4fab4b9b482b44bb41eb3e7b3b0b36fb342b2e3b2acb261b220b1cbb18ab13fb0f4b0bdb090b04fb00eafd7af96af41aeecaeb5ae74ae3dae06adc5ad98ad6bad3ead07acc6ac7bac44ac0dabe0abb3ab7cab31aafaaac3aa82aa41a9eca9aba956a901a8c0a893a866a82fa7f8a7b7a776a735a6eaa6a9a672a631a5e6a5d7a5b4a573a532a50fa4d8a48da442a415a3dea37fa352a325a2daa28fa262a235a208a1d1a19aa18ba154a145a10ea0cda0bea07da06ea02da00a9fdd9fc49fa19f else 0x40c3da00104c1681865b8a2096002082d1049e285a06400209600030411bab0d3e81693c5802827d0222baad005a37221a7d00c2434e405a3801c86800c25e96ab41645708d5ba7bd2d5b218eae31ab74fe2d415c1e90d5806bd1d5a82b8869c8b00f0d5e9e2d415c065601ef4f16b8b00232de9505710d391601af4f16a010497a3aae45706c9ee6e8468bd2b8f16a0c6ab63dcf505e8eab915c6346e9eb6bd2dd282b8468d7a3aae4571501b38d1ee6ea7c5300f708c95c56d7a5ba1f2346ada8ebd2ddae11a3152121830d36cfa78a20d4067d1b66e1dd3dc2337fd646357a11b8b231a3d08d05e9642344edac81e065468b645e88d0c8e09041b55f4c6ac8236cfa5aadc635641bb63571ab209db5aad02356415a0ed8d03671a320d7a571641ef5b6346f1eb8bd0c87571a374de3d917a570eae355b191abd1a0302c8104d5c173646347a16f4ad9d5ae0c83dcd9c68de49bcea9918d1ee6e98f42e0b6682c8c68f73f8b8d1ee7a12f44685e1f8b5c56d7a2346f18a9091c1a62c0b2023254111d90fa4345a83b6756233221a3540db3e911d90dc4347a82c8eda237561a3530fa5901193b6754c808c8fa36cdc5907b8466ed9d5320232141db5901190df095212083ff5915076d8d1a06a83b6754d0c68c833e95037164634db1bfeedaa0b231a754ddb141642344ffaa07d2c8c68aead41db1a06ce34641df46e2a06dac8c68f73f6d640463ed8d03671a320bff78b503e98d1598f17b608c86f84a908cbdb02a8d0a05f17b63411a21041ffa82bd0f7f171a3d8f7a3aae46355c38a62e0f6f14413d0bff5e95c634ea97c5682f4ae11a2ffd7a78b80570d01bfebd2b8c69c829707b78a209e85ff9c8ae31a278a8d0ec3ed8f7f14f6468a2f87c53d91a3d085c1c1e28827a14b60952123824306d5b22b83671ab14de3d716ad90fa635629ac82e1f4b5441374de3d906cd718d1aa5b55a0b22c5ae11a35ab6431d5c635629ad5b21f4b16b8c68d939aa6418afa5718d1b27378b83dc41364dd31b38d1bc6410df0daa8d0bc3edac8b16d5468de311c1f14f4c6ab8238b7a3aae46355c1af47571aae097a78ad00824bd3c563b1aae0b7a3918d57043d8b82dfc53d041338aeab917a1706c8826f20f5c68de2e085c78a7b8827a17fec6ab8b542d2be96ae345c11a0b56b84689ff6016ad70d015f42e2d53dc412ffcfa5ab8d13b6c68d935496ad7016a344b56b80b51a200410b6d52e11a211c12183e2846208ea0f15f488e41868ddb540eab910d44669c8287d3c5a8041276d50446eac35209bc5ae0231f6d50446e44830d1a987d3c5ae0232b8aeab915c1b21199f4f142310494c3ab5c0464f15f4ae023236cfa78a118825722b808c66f84a9090c1ffbc5c02b8a80bff78b505718d3e86756a07231aae1c53540fa78a5c0825ffaa0ae31a) else (if i < 10 then 0x5324cb77dd5ae31a320fe2e345c3e84777003787ff3bed4d71646346edb1a321d523e85e3527bd918d170748ddf682b8b211a376ceab408d190e999f4f15a0104891a64d0571642346ff9df63ab8b231a33aa659a06cd718d19077d0bc638f7b231a2e0fff352c7571646346ae2c8469a023e85e6346413002e0de187a7b9bc2093b6360bcc68c8283cd0570642345ed8922f31a320be29ec65e345c1700320de181a6c9bc646345f142d32f1a2e0be2b40cc0824f158e32f1a2e0bdb018c75901ee3464680c13bf801bc337c2d4e006f0ca90e00d01bc3238204851a3784af8682b211a7d08948686ae11a75488706b8b210068094150d8d3e8ea9682b23007d1a02d0d5c600eab4058eaf4ae1d5ad83234757a78b5c56c111a3abd2b8ada1a720de29e8209ee4755c8374413dca7ac74eab915c1e90d1ba8f14413dc67ac755c3ab0d1e86bd1c8ae2b6869d5378a209ee33d63a63bc5ae21a3d0f1d31d7a3aae45710d1ba88eaf463ab8756b6868fe28827b8cf58eab87221a3d0d7a3ab5c56d0d39068eaf461ab8756b6868f1d5e8c7570e456d0d1c413dc57a3aae4170e28826bd3c510477a78a5c0824bd3c510477a05b5b3aa1116f4032b6720322de8064015b39011180c88bb6a3a1a720c168191178b4708267d3c56da1a6e02233e8eab90dc51d0d3ba77d3c5869b86d822378bdb434111222a39f47221a2f6cead1d0d3905889f46e1c8a39b6868fe2f6c494341117c5eda1a08891178aefd1cdc4346889d5721b8a39c5868efa78b4708248882da39d56e21a378bdb11d0d044503222a39b87221a3019473e90d3905f142d03200a39df104e0651cea88240b600a39c8104bdb1910d0184b221a7d0616f6cead90191600edac808890078a208184031f4b221a21910d09437d1b8b21b6868ad4f6c065910d158eed80cb221a2992253aafa4346419b8b221a7d08fa3aadc1910d3ba66a5f4b221a276c64434ea91a97d1b8b21b6868cc73e96443443244aed9d53421a320ec73e8dc590db4346ed9a963ac8868a063e8644344031f42f1b63221a376c061b10d1905ed80c248c8868b0d0182031df6e2c8868a6481865baadc434641df4b2041181816b52dc5910d180c639b8b221a2c3464018312a1a7d00c240025064061200129a0030816c01433aafa0646802c87d022276c16c00eab1c6806478004a1040c2400ef882061200755b80c80c2c00dc340061204f1682869f42f6cea864169204f16b80889db434e40184f142d03041238a168182090410b45e285a060824030411408efbaae4570e2c3477d04113ba208a0477dd5ae21a2b915c434ea91f4f14b96d8412c08eff8ac75710d1a04639d5722b87161a3be9e2972db08258118e756b8868b023bee45710d15d5ae21a7208fa78a5c8824811a9722b8868b0231ce45710d17c50b else 0x171a3d2b83600ead703f1523680f4104ae98822f171a3d2b825e8eab918d38b5c19a01045e2e347a5704ae30037867a9bc208ef4619d5c6ab82de9e2a46d00825bd18e7231aae0be29ec7a09a2095290baa20890e0b1c20890608826f0b00755a0ae09803526f0f00680de1f315c5aa16904ded87af143dc682d3970fa5aa209300b56b86808c75ab5c63447d3c5c68b820885bb6cfa5aa3689a20a1f47231a354b8774cd05716aa3447d3c568041231c16ffd5c5ab8d19f4638f7b571a2e0d5c5aa8d34046182dffab8b571a37fcefb0d5c5ab8d1bb6c68d57208fa179549eee46345c1d23619a0b56b8468dff30cc75ab5c6346f142d3db1a2e0a2685afa0f56a87b8d1dc8c68b83549db1b22b87a6ae3464682d10f42687a8d05a54682d121c1ae2d5401a0220c1aa6b8469c8234016888e0b901688860d0554e34fa3905aa6b8c01a0720b11f8b504390d3e8688e1ca82b87543234470e5415c434e41a23871df756a0722b8868d34be82089dd104511f6d503910d3aa67d3c52e5b6a804131d1e2d315c0465755c8ae0d308cafa78adb046209623a821c7d1c8868d11f6cead410d39067d3c5a80b9104b11c39503535c3910d1e98722b808c9e2d414c0824756a0720d3104be2d414c082488ea0869d57d032354111b910d3e85edaa088dc80c8bff78b8057150144da3bc5ae0240f71a3f8b47504fa63457568e722b87171a351cfa78a209300a82b8754947570eae344c02a0ae1c8251d5c3918d11dfa3bfef16b8c68c26d054778afa07b8d1e8e755c8ae31a714ceab914707ae2d706ce3487d3c5c68b8216edb78b473e8268827a3bfe756b8c68a1ed1cead70268f58d1fc5ed99808c8efbaae451d5c634e29fc5c68b87d08fa3aae46345c3ba67228eae31a754afa51c7bbab8d170628282f15f408cbdb3aae43a61195f4f14231048cc570ea8464f1700ae0e2280ae43aa686015c140e29df4f1700280b82b6de287a7b8825c01d5ae0a0251dff3915c6345ff9dfa39c8ae31a33ab475718d39057d0bca38f77231a2e0fff353473915c6346ae1c808c7e2d71801a05016b87203dc6894778a7b6345c144df168e7d03dc68d47196eab918d170e29e8ef142dc68b82f8a118823a3bc5ae11a278b4151d8d3e8537c3475718d3aa42a43e287c8d02a4a3bc5ae11a22be1f1682a391a7d0a94868eae11a754883068eae11a72094151d8d3aafa168eae31a7208430682a3b1a7d1c82d1d5c634d4b905e6282a180c378be2f6c6f634061682c6ac87d0941590fa634432dd5ae0c8c68a5e3e9640824a1b1aae1d5250d5c3ab8d118eb22b8c68844bbfff571646346a09f4b203dc68ae2e006f0fb67540d320d937b1a3b6d801bc37d3c53d4de104a44b53ff5716463460f686756b81347ac68ed05716423442258effab8b231a331d5c5901ee34)) else (if i < 13 then (if i < 12 then 0xf4868c83c47e2d40dc434fa19f488dd5a81b83221a77506876cea9901194a07d1b8b20c008cc0f540fa1910d15f4a81b8868c8300cfa0460f0dd5078231c4750434eabe81919b8078231f8b50446ef8825a8223754412601db50d501a05a3ac8ed8d0c68bdb3aa681918d15f4a39b8b21b6c68ddb51d433ab8d1492a3bfe7d2c8c68d473e9646344717003406ea88fdb190681b38d1e8e7d1b8b231a6d8cfa370db51d641ef8d1c926a68effbb6b231a3f8bdb3301190c9754d07d31a320d4737164634fa15f4755b8c68c8774d643e8118fb6754c874c232be9e2b70e00465f17b6c00e2340a03600641406813b6340d93231a2be8dc60164140db19f424b1a3209e2d1cfa6344a38bc7d1b8c68c86d8fdb140640464a3892ffac86e31a351ddb590682345c01f434066f85a9c00d01952104828d1a0257c3475908d3e844a43db50d47234ea95020d1d64234dc1286a3b1a7d1d52e00dc1a032083475918d3bedc1686a3b1a755b82d05e2dbf8d1ec5f1682bd0f7134f6c68f6fbaae4570e2e3463dbc53d04125bf5c3ab8d12dff158eae31a2dbf5c3918d12823ddd5722f4c69c53d04eab918d38a7a19b6c00f73d887b78a1e9e8209700774f71d05ff3aa7bde98d1a82f14f7682f4468cd0505e29d07a2346755a072282bd11a74ce209ee263a82ffbc53def4c68fe29ec716347a158e755c8b7eb8c69c53f8b8d36c7b93c5a0af4469a02d05ff3907bde98d19c83db1a3d095c3901ee34475682bd31a720be2b6d8d1ee4ff986b7dd5ae31a3246d05bee45708d1bfe63adf722b8c68c7bd05e2de87b23461d828d1ec24a43415e88d3aa44383e2d057a200d015060d057a234e413c5380f4134412e00ea9ec32a43803407b0c8e0d057a600eab405c01c83d86430682bd31a6a5c82d057a600e43405a0ac5364de25ab6457006d8a6c9bd8d2282b56c8c6ac57d0d415ab643e962e346379f4b56c8b144131b3645706ae345c02d5b22b8b15a035ab6431d5c58b8d19dfb1798ae0d92dab6407b62be826d706ce349354c87d2b83671a336c6f1b23b56c82e31ab15f433e86e9bc6c8825edb98354d923e86c9bc7bd905c1aa209ba9682b8468d92246efdaad05915c58a8d21f4b55a0b22c5104d62b415c1b24a0ad563ac87d31ab14efa1bcc71ef6ad905c0826ea7b6b56c846ac5680c641b26f0ccb77ed5366b8c68c8381a6c9bc646345c00de176d8d58a6c92d548ccb680d9ae11a32116a996681b35c634641ccb77ed5b231a2e2c53d708d1b23c01df37866f844b0a346f095f0dab6458a8d3e854383db5ab6420162b406c01a037864706d5b2300b15a07d0de2e015c1e92096f4c01d5722b8376413de98d570ea92f4c02b8756412de9e2e015c3405bd3c5c018eae24135e980570e448252dfc53d8f413441338aeab917a1bc6c8827755c87 else 0x15701118ce239d5722b871422387adb17cfa78a4708270908e756b8088b4778b8d07a477e8e035c8ae31a351ce476ceae34269a8e7d3c5c683d2b534701ae45718d1824257002384dae0d008918005aefd1c4178a2087a8a39d57141c0f4b47105e2e341687a6f1495c01f4090bdb12b803aa121700a382d755f44c8d803901207a4389c8c683d251d8d3aa1e920ca0ac87d31a2c19436015c3aa9918958318ec02c8ae1223bbfe2e340607a5031d5c68cb0f4afa0746f03e47571a0303d231de2e340607a511c4d7d1d5378c8c68e1e979643e82095dd7d1d5c68de2c18efb53645718d1bb6134c8379d5c68c1e9722236cfa3aa6f0828831df63ac8ae31a33abdb09a6c9a06f1918d23c50f4b96d98e7d0de105106352c75915c63467d31a3200c23e86f0821e93b63631a3200c2f6c496346401850b5dff14410303d338aeae000603e6f1bc5e60820302d0f4c16b1de29058d0181e9f00a182d755f44c8d8078a4abe891142dc03b6255d5488d7a5ab64570c75bb8d1d0e0a016eb403bd2a0ae1d5b003235e9505710d580e419c8b00321f8b476355b1ee5bd2b8a3bc5ad8f7c68f475e8eab915c1bb8d1fc5e60f43dc8eaf30e41ba7b96f4755c8ae28e374f73671a4d6cead407b9198f14233dc97a3aae45715b3a6119ef4755c8ae300280dd3d6d503907b93c5e60b83dc94778a8d1ee4bd3c50fd1a0f8b7a78b5c56c8d15290de95c56c8d3aa541837a5715b234e416f42deb8c6ab6754c5486f42deb8c6ab6720c4306f4ae31a6a6b6720d803bb500f007d1c83a08209d02756a010470d540e40824ffb1ab22f425917a63436e2c83d31a278adc6347a11d56e0f4c68c8774cd05917a2344f15a06e11a3d1c0331dff5917a6345639b8b20f7c68f435917a234d012dfffac86e31a2d917a2343f14784686525917a23434383645e880340440836fd908d3704b22f4c01a0211c1b7ec8c69b821041a1adfc69d56e0b6fd9180370d016d57d2c8c688fa5aadc36d646346ed8d5b231a2600fa5903c02c8700623f6c681b26463467d2d56e31a6dac8360164340357c28d590fa0d0e0b1c8d1a034082c12346f0f00681f43409803be6f0f00680de1d0d5b1bc7b92f4ae03db22b63dcdec6915c1917a3aa6f1bb8d1e86bd2b8c6ab6754d435e95c3ab5b63463d398b20f725707a5907be345714de3dc77a56cead70641ee6c9bd8d24f5324de756b83d0c8c68dd4baa641ee6e9bd8d19a9e62c83dc8d05908d1ee4bd1d5682b8ad91a321d34341641ee3379d5bd0d0ae0d9adb1a32127a170c75907be346bd3c5ae11aad9a035718d1907a13c53dcf4c6885c1bc7b8ec8468f718781468de12521bd2b8ad91a754a8706f4f16b8402b6680d803526f0ca90e00d01bc323837a5718056cd03aa688ea0b221a7d0b11d314376d503aa191e23325d5a81) else (if i < 14 then 0x6dfb21b8c68bdb601e2b1c7c24464b700033c5608e5504f6fe00063aaa0952d03300396c8639413dab643e98d12d56e1f4b231a2b1cfa5aadc36d646347b57007d0d0488b6abbe23e346f16d5c0047488de2d0d5b6346f1ee5ada86c02f4ae1d54c8e7a5918d1ee4715d5c68de3dca7a9935c190ea9e86f1bb8d26867571a3dc8c75918d1ee4756b8adaf4364d0378c8c6921e9f15c1907a6346104de3dc77a1798d3aa1e96f4c00de6803d2e014356d7a570eaa44739495a1a8eedb0034027425b4750d8076ceaa647f14e57d0d0c68ae2f6ceae346817c56d9f4341b8c68ddb3aa686344325d5341f43231a351cdc590fa6345321f4754d0379ddc68fe29c4fa1a01117b6754c8c68d02924fa3716436c1118e5030927d0c8c68c0607afa1245e190db6348037c56e095c68a4ae00fa1a01394e5edb0025532340273a5b801caeabe89918e5c00d06e0272a5a06601e292aefa82703300255d5504be2d056fe347b07a6b7f00ae1d54c8b6fb1de2e015c2446b7dc8c683d238b6fbab8d07a5755c83d9c53d31a31efe28747b03e5755c8774413dcb6fbab8d07a4b7d8ef171a0f4be29c47b1e98d1447136df639d5722b87171a487adb31de28827b9adff171a0f48069ece41e98d15c8756f4c684d2f8a209ee1e92df6a40d1b5c8ae31a3dbec701ae45718d1b00755323d89e2e00911ec40b6dfc02b87552233918d1ec1e92dfc69d50f496fb91803401e9682b1457364cb0f4d4158b6ad918d3e86b158eb5700b22b8488f62bbf8d1b21e95b67d0d93781f287a6f5ab6458afa0827c00d5324570f4a5c87a22590db3e86f1aa20a6c5c01a03643d2bbec758b6ad915c63472e43db218e7d2d5374de1052647306c9961e96d5035f4364de3231a3be96ae346f07a5036c5ae31a364bdb5aa069b2681bc64634877f00b56c51043d33be2be346f130015d223789805056ad9162be8911f00bd2b8111d5904d805e9e2d70c74826bd00c8e8de07ca23e015c3aae41e86ec828bd300722b8756413600c778b5c1e9209847c018ebd2b8755c8376414e015c3907a4825bd300754de9044d3600d48f57a570e44827c018ebd2b872241331d5c3ab8d088561b00110de07cb7a600911bc0f962d63b00b56b8488c5c0742203e40f4b87d1c8355dd104ec70dbe2e341687a62e62d1e83d638b87d2d5105236f8b8d05a1e962d1b5dfaa40d722b8c690e476c6ae3426947a2e1f4b54410f4d16d52c701ae45718d1ddff14b8c682d0f4c411ab800ae1e946d7231a0f48e45ab803401e97c5a0a8ec00240f4d47505e2be98d168ec02b8755322d1ce46341e928e77fc5c683d2d1ce2bab8d07a56da8e7d3c50e81f351ceae341e90477144da3a82755c87d31a487b4778afa08250f68e7d1d5721dd104f4709ae4570eae3462e4446d83da39f47544140484778a7 else 0xbd2d5b22b863b00b7522478b4756d8d1ee5a3bc53d31a3dcb471baeab918d1ee6ada8e7571a3dca6711d7a3aae45706e8448ada8e7231a3dca1ed6d4778a209ee64b700bd0bead9d54c8e8607b7a17d5b3918d1e8ec003dbd2b8ad9c84c9072d917a63443e0f4b21b8c68a643aa7a1bceee34663bc5ed8e5c68adc31c7bd907a634603))))
def hx12 (i : Nat) : Nat := (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x2040a00286160400002041850600280045c20f06180062c00281000c10000040810200016000820700140262260801121ca010a0c2040a00209040c0010454247002059600102030008401000040000001830634086160c089040009706080022208185001080000082860010502025c207100c3930c00e0104240810e04005003450006004021400215081452e0404400140450a10040040a2c3020400300000458004000020808085000c004001408a0810501082818002001861c2058d042410018041010204a800004101001c20c000008f001440b000010802100810a000810014080060008004500021c0000f2a00000160400f000c18100380000c040030a70109065170f0268000040408b00002835aa0001001800104781800c0c997000058302084000000383061400a0030000240018104200001c04106080030100101840240b0002044040018283040c180100020802243800600082040098300101820034001000000b2000001102038008011000e001000c00a8106403000e0d0012424511062c102044820454141007e10790063c1031e08001340078f000c01f400028100003880404511220002d00080001404004000c08a0004183020c08e0e0c1862814c0b062c7001204409320000302000060c70294020008206080030c440802e187000004201001010000000081838018064c080001c2810a141020200782001000000142010200284040020522002051200103044c00202187015a0c68000481870620016000c10300001011408700024c582060410a0800b080068000281000000000811424080020c38104105035e1030302200940a1410108042000a00081000000600040880a041000044009121001800000010600a870600a000008f000610b810624002042800002002012208001004800422181832a5c08002180020a005800848384040028d06243020a04011242410430080854004380020800a000400c08003030618701082c18a240008200008800c006010400200000000900000040000080000c18c08007020acc1110028381040ce00062030002003820038204020c181040448126240832e141060210100001c002180000006081050218103140000002085810018402261830000104863a544800018005021020400009812c0000b0a000803e000050004083040000a16280890800080040800300100000a000070210180061c9010020004020510c0000086000038802102900e080800414180020830400086000a0428000087050e18700000408d001000306181010804400000008200000000004082364400004000000a0050500000810008900040c2003424303000c98004041800e0c00d0009903061800018000010400000180030e021c181000c380000809200040030014180000c284020c100 else 0x1a4fb80000000001c29c40000000000c30ec000000000000000000000000000000c4111ad0c581f5940fea022e100f6a81cd481f16e5eb00051540c5c413100000000000000010d5c400001285140000142176c23d8000000000040ef1814f400003c11100000100e220422c4022143278c44c4003d6853580000002f9882bd4051f0c2eac00000000039127100b1c022590061582b4181bb400003412fc000034018b41be34301641b70000000000102958000000000000001c18800000142390000000000240ce8000000000000000c0ba85ecc200b8e02b95c0cb3c10924281c00003041ef58548000000143800000000000000000003557bdc24adc0bfd82909418ae4114a4118cc2979004c2c276c000020053c00000c2a0d8119800002020548319525cdbc5b63025a1e5e9f4117c0000000f83c0105e867e40d63c17304153000000000020239400002c09500000100cec409ce42e0c00003016eb40d33013a741054c09b38150b0324d404850152580d6cd95318483000001c200269218000000000241bd0c2ca301921817b184f5c0000000000400f6015180000140a41416328710c00002412a0000000000000002c27e925106019c742ed40000180c7dc5cfc804fd82a94000000000000000000000000000001821800000380b0129542420604282e015cac0c2542e9001765828f0020f242b48c2b7f822a34232bc30b0427f00d5d0000000000201a9745464826be8088ac2e95c24f742663850ad401db426b54284182ebf0d1adc124ec0a648261c027d75c5d0000000000301be80000340685c55b1030a442f6582fa541715411ff42dc0000000000005b9581fca01b30000000000341159071730630e00510829fc005678547c000000000282e8cc2e2bc208f918a500079ac77f05d2c000000000000001c2bc000001c44410005282dc5c198000000000028410ac112b40be1053a40000000003804640000000000000000000000934815400000202ee0000000000300a7f8d21306e9f821be9d3f8809e700611041c80000000000c223440dd3c219d01b50c029a841010168c0000000003807d4020b10080bc0bf0c0929003bc00002c06a44532c80af5c323400001c100e068218328c41547c0b8580b3800001408ac00000c00cb82a1c0000000766ac480200478508101841c00500020cb0b0e203040000291001001c0a000860a2c28522ac80002000021a34186001400226340930a14018003c00302744012000004000000120008081a8c5054098907060ce01000800100001011a000890034002400050c087c485000963c12402025204080060841e0264b00000010304040800a0800b1c04013011801200c49000408202021cb16007c48200100023004000020c08026000012e005011a500801e0000d060508b0028680062) else (if i < 3 then 0x142a80000000000041dd44057340b12c07e48538b013264dd1c80d2c8117b8246a019ea426eec303cc6ed2830e368a4e01acc41209c26b246ff281e13c1fc0c2cce456e1c1f21021c441fa5822fb415ccc0faa02f2180b998c2f40000000001c12b642f25814b800000828940000082d1d8215d28c9c000010d68400001c111bc42254274bc013bc2a8c40ac185b80802db8571ac2c50000039575201e0b41c73822eb82c7f8227f40bd04184fc083380c67003e1c1b078858400003030dbc1db40000240ad98106cc05380000000002c1d7d031398577e42d3ec16aec1194406bf02943ed0b800001c002582d480000101f29002550037000000c01e800000000031010ec0d6800002d46240000000001c1fde01ffa012c94304d00e8a424a940e558171d8873d021048081f82262803a5c53f7822ca8113e00168c106a062d7c1587ec753007b90066981c6c016a101239d126c8034900bf80c8e7c678ec173a41f09810ea4252cc15c48425c000000000380d46021c140f0a419148c2eac182a82f3c00000420ef6d09602a0a01b1040efb00badc24a50c80882c086074a8070b408c80000000000856cac2fe5011bfc25e902872871870316c40fb100136c292602b61867fec5c1042b3b5e158000010115e0284c0000081ac40000282e580000000002c042202a36982020309400002005000000081b6241214000000000000002c156400000c308d101fc000000422001f3e41a280000342f566586601d7ac706cc27cb87175413a80000301a7e8281400001c0a00c039000003831dc02218000000000000002c25bc00002cd76f65100000004704dc172000002413b600ff940ca54194ac080000000c03e8010050015d041e580b67c0cb640a9c0000000000003f141ef18888442253810b2800d502296c03dc0000000001830cd41468000000000000002c1bef8097dec8ac00003c050b25c4400002428a8c0ea140f2800001105abc312d42e6bc3007c29494282228e6182885c1e240000041dbc022d480c379d8acc05e1411c9c05f0000012617901abdc12680000000003047478725c83090c085c00000000030013e42850c095b81fb340d740000240329c2faf43088411b00000380915428c1c10bdc071000003c1039c1492466f1c250ec179c82d8e8082983063c2e49026eac874545422059af8cc0d426340665542e6e03055994708267a4289a8028d02c6c4c606e8c17c1c820229e0064c000039426000000c71430c5fe01f4680788000000134201fda011a40000102df09c1bde59f6422680000200d7dc71cbc2be6463198303302a58031e800003818f540a8400003810e400000c044f45b7800000000000000302c0c0000202d94017c641a2c00000000000000141328c15540000102d5a2c78681cf980f00000000000 else 0xacc13f98c612c0a2f801d24668d0192a402832674501fcc0000341486e864416b0141eb74140f031d0a81920500400001ed09dc665f43202a9d6ec2e7c028800000000000000000000142a9c0000041dcc000004602c00000a9d5400002c024f82561c2c73818cc00000000034215b82f84000038128c02dbc4188d015a4406a0027df8002a427070273b00e530252441a10c1645409130047c04b430713b985ebc086800003d48ee408fa9125800c5404229ac796c2d47c084a8030bd93a041ea68304b41b9f81d3742b5f427da4213e4211d82bffc305d0250380068000000000102a540000000000000000000341bc00000100920000028261382db40000341f700000000002422d00000102d1800000000010826b05952401080000041a25844780000340c1b00edb8250b802cdc25b3c2f5000000c2ff982f4242676a8d21830840000001cd000001c3215cc83d4711342df80000204860000004299c0000000003c0c900000102cc682f6c00000000000000000003c3040031a4000012c6d402dcc00000000004176c000000253680b57018f80000001b200000000003c7154819cb816fc472300000000000005530592c000000000000003056cfc53fc0000000002c187400001817ff0182dc421c00001146354194506000000014017502b13502210574040fee07256800c540bb8000000000181850812ec0306ec196bc12bb8a159c0861415d102bbe82ee6ccbe0c034cd08b8c1b5ac265b8702200ff00000001594000004236d8306be90e8023340000205457c5374425b5c044342e4c0000000000000034305000001c21b40000102856d216c1a42e431cb805a4c1c26c2fbc000000000000002821d88238e805b840cd0c06d684767c195cc5fe441cb8c019c81df3c1b7a0173c4566e0874d82b75c293a0321b8295606ad0c29fb017590167385b460520a85c33c1e0d807318113681ea342a9b41c34c28b188594023dcc17c80714dc2bed822a500478c0d700057ec210000c4d40e7941903c030e018c8d82d10d04302d0f42712c02ec0000102f000000242b2a029c9021aa0220781cc4c6a732e168825220189d06333919b780f448170c40dc80000000000000000004602e3cc5369c280d0059000003c2aa800002691e0000008052c0000000000000000000246921c26c7825980000205558000004313ec12f501475c198f8146d0161dc2f4c0000202d540000146da00000000000051ee0236182b5000003463f0000038102a8167c020d501151828da8283d46fe481ca04121800003453ec95791c1280000039d9b304b35c09f30140642989024a0c44cd80c88a5f6140fbc02920000018300882d03803b98296885699cd16b868dfcc8be4317c80b5081a05453980000201a19e4c4100659c4ebd01b9800002c05c2c04fbc07f80)) else (if i < 6 then (if i < 5 then 0x19a9c30e800003d8ba701430000014120f41e3800002828ca0104800003c0e19c038a82b91421cc00003011628c186810f0c21868315fc043c000000000180ca800000000000000182188000000000000842810f60018700f5042231024f000000000000000000003c261400000000000000181890000016d0cc000000000302349811740000080c98000000000242274c5f74000038062fc31a2c01e000001813c400000000004154dc2f6840e3f008ee819528096046c52445b40ce56c2cc1c29e6c0a19816dbc1e9400001014f8402ba417a781c400000102db0000021127800002025ef430e4c2810000020277c0000281b40000000000042eca02cd4c074400001c0678000028091e013860715cc04a701cb74180702dadc270fc283982b4400d22c290f46321c070f42ac184b9e0144a81c4881d3dc1416810fe81a9d02f070319b441b141a23c0987c0b2cd846cc01c402e88025a801b47427fbc0071025ba0243d027c242052c03a040abfc166b0159340ee00000084793c027c0000001da8c295202e1400000284d80000000002c0461813b000000000020279ec2ad4809cb0e168000020313602122823a00000000002c13ac0567e01bb3c1c3fc156c0325400000000024109c0000000001c61624dcef0145dc1f778142400000000000000341c38000000000081ffc0000000003808dc0000341f840000000002050440000000003c1d51826e1804bb00f0ec1dfb45b9300f8cc1b2c00001419fa004ae829dc0000000000000010721c80938c5f53c21ad431c40000000002c249c40604007f3c13bb86a8500aaa83146c251284fdc062f242c5981ecfc2c3d4593580a8cc691940d96c0ba002c2b822f10275e054078179300042c2fc4817f7c2c798267dc052981e84c1cc005e040000342012c058800000000028009b0109a5970d807aa994588623000002024b58136cc697f42f29c1a50415680000000000c16f586aa34716d42e9c0009f4c405286e00000059726c12cf454b441f054222cdd718471a78117183143031fd4037582fe1018e9802d0581e941da0013684327ec113ac1578c53ad008eb8315782452c046d0cc9c4302cc6a9c00001831e000002555d70214d419b000002004904042941017c23384454f9d50981318000000000201b7f0210e41fb400001c2e63c19be003c7c534580a9182531c301b94bb4808d382cf482818c0583c721b811e4c2dec0000080afa42d76861a6414bec05240000200d1c00002c1ff40000000000000000000101b140000258339c02f000001016130073a019900000000000c26c80000301e7102575c0c03c08640000285587c264382094c1a3000002807ad1158d80d2800002c07e0021b0000000000000003c87500000281b250325200c4a581810320c000000000000000005d9c4b else 0x3600000000001c001bc103500b89c2517c5070000008075f01e8c82680000020326000000811040c1c2008f741fc4c0aea811a2421e70209ac0075423e00000000001c2996c03f4000030237c00000420ac00001c27780000341e3400001872940000280d7ac0a1dc08d9822edc2151c0e7592cb40000000002d8bd88297640144c293dc2a648107c00000c0ad64262a40c6000002404d40000000000000000000000003815da81f6200dce009bc185d000003030fc00002432740000000002409c0403ac000000000181497c2ce800003c666f408980000000000018400000000003c328841ed7c2aa0000024486a40b2400002010d680bce8184b9d59842cc9c2cadc476b6026c91265c1958000000000000003c187bc1236406440000000003c2cbb8255782223c2b7a429f400003027b00000000000000030192f4190400001e05780000000000428e4000004152a4017b02f90000000000000000000000000000000000015914400003c24880000246e1d41d2a825074040c000018230d0031000003c146400002413480000181d0980278000000000304504000000000142668000000000042c04000000000000000c1af2c5be40101c00000000000000105f4e02142061be431c000001018b80000041fa80000000000000000000382388000030294400001061a982c94000000000000002008440000142f800000300c1400003c0a0642bb281a784226d841cf44f59053e180e8c4269f864fb815ff8e744009d88099c42e398063e80c9d99292c2ff34104c000010238601c580000042b0c417b40000240978023c800000000000000182c4fc0880c1b3c42654000028181e013040000000000000000000000000000030143d006ff43295861b04235c444640000202ea205300c0f95016e1d8508000035d46442fec00003c220a4252800001820bb40038000030200d014708137e8160b4280acd0f84212581061c3080c24548cb4b02215c2041c856d4125741f1e8d2a0000000000300507c16495867241b3b81a5441e800000000000c722681c888d2afc2aae0183f04177011af802a640e6c00000000002d0a80000101ad40000200057c4582c12e3413e9c827800003814aa02adc8271d416d28289d4089700577412d5c48840000182991c2e854255200548000000000000a81887580000000003418fdc2d8082abcc1cf0026a341e88000000254c00002831b6c2e540000000002427a6408cd4312800000000000000000000000000000084f7781fe980b04000000000302bcc00003c0d0f42538447b4000000000000000c0cfdc1d55467964167606ec4000030048f42b3ec048a45e0a42ba68137a40e3a82372823e940fa041b00000028cd1585b5c000030011941dc0427bac158981f9c41f5680ab8407a3c0dde02a71c31d784ba6) else (if i < 7 then 0xd027280000282d528178000000102a2831f400002c24fb42eba407804039c0000000003009de8d5a500f62412894319f46dd2867ec4155f8168800000406f081e6cc24c8000000000000000000000000000001426f40000000000000000000000002585ee25b2f80798000000000141fac0000241744028fa06999c1e1d812604043a812490426041aa80000084104000020087c0000240c32c68ab0c20445397901b80000100db8000000000341954181bf82ae3c2910800fb81b4b420e7824d205079c0be9805568c2fb00d9f0083902bf044574000000000380834000020544b508b70479e82dd2c1e5f00df981caf06ff50130d82b34c488141d8c00002c042d000ab8135942f1dc5fa5c6bd980637025d08023402440028ac413380000000096c0c53808100000340adc0122702fa000001001d6c18a98265e42a2fc1fd40000000001d0e500000068fc4000000000000000420fd80296c26a4000000000000001c06400000180fd800001c18d60720480de8000034275801de4000000000000000258b40000100400c022400000000028155000000502ae413cd80a6000000c27c74224800b3e0200a812b3c0f57c2da7c175c0216b02c9942c9c4111681d040172587228404da82357c245e82bc840ab000000c0f3f02dd5024fd429d80000240b7a811094272ca5eaec0f66853f0000014193201bc80000000002c0e1f823af85409c244d8600482499c0a49828ee0234d80da84227b812e4000028329b02a2000b9c803ff423ee20887430250914445354000000000000000c239c0000000001831240000146d99cd74bc242b818e5c2413c24b800003c1a6cc270082ad28157cd4865845380000281298422100000101428c247400003c00480000180b63c2de0c03d000003024c400003808b4000000000000000c474f018348320800003006cc000000000302b1c4269800000000020c50c000038cfb800c280000000002c2a0400000406aac081700ccbc1bf0000000000082c1c000026059f0033c816c4000000000085fb3c0fe2c0f05023050127b82d29c2a19004e400000c197e420f781d22809ac00946c01958715ac1521485a140410401a200f198c6740000100230000030129c00003c0be4000004108000000000000000000003001b2e087f010d281f94000030088c41750c1534000024058482dfd00d400000000000000000000000000000004228842875c131c0150e45f9b41360c27818080d416810076d80e134633cc09fd4282ac2582c232c05ce186dbe02eb701d324068fc1f884108a41010000000000000002018221aaf94305b005f8292dfc017c0c33c0000000af0471df811aa029840000282a440000000fb9c0779821ee4092d4301c812acc02b0c54b18214bc279a41e33c54794296640cd7c15fa595a40000140 else 0x5598242000003411d800001471b000002c242c000000000000003017a8000010260882ed0019de81c2242b8d8191c000020447cd199e00cc10208340ebc00001022af82cbc00002888880000000000418d3c132000002c0c8c83120c71080000281f504057a81a480000140e44427bc0000000000000028099b40db682075c22be8c614414ffc726c02a4c80676011d7869b000b724107bc00a4c687d424e8000008598d68db0c03e4025f1c30d341d6941c1740b974569f4074c40a6c8637a42200421a202b32c00d280e000274da9d4b08ced1c8d4000020008780f1e031e685365c2ddb828bda8cc582e08c0a5d8442606a5c25a06000dec684d41c4640e7f0555d00ce7465ad806e2c06c04063b01b67ae16e02fff801c0000000539c4127400003405ec00000000020683d41ec00000380b18000008177d41027041fb81ba2047f4c07c900305c2fd0410cb404f2024725578dc20d342e7bc6ac64268b023b742f8c80b36025c00147c00000c2e458025c0000281dcbc522a8130180c0506bacc1a8781d2cc23d5031fa81d4642a13c121ec06998206e828d44194c065f5c0e5d824264635100f9e862e642bb9862854c11702934000001c8eb588050027141ab8467f46c78c000038060d022fc019f40000000000000000000000001c02e981fbc0000081ccc4c9040000280784072740000000000000000000282f974105800001003300000000001867cb0500281c6400000c1b9000003022280000000000c5238424c3806800000000000000000000398401692d3830138257cc24e346884c1244027698619cc033759468c0a962483c0dd8840afc0000000000420180000301e7582a6f02e42c25d8000024172f444d6c29a58071c110bfc2f744159d4207194230000000000000000c310000000000000573f0171000002c037e41c1d00eb400001c068800001807d000000830214445d05ba400d98000000000200b6c0000200fc80181901d6f01706c0d9206aacc0206c214740cf3c14b3017620485ec1bd4000000000282787c201400000e4f2300f10000000000381cdc000028106400c7400002c0bf7a968e8049f8411c8065202d98429bb009300000341da4c05ad0151c0000381ebe00ef4692c201740401248108d4209181bfb80a99811f682301c10ab4130980bd9431cc82d0bc1b0c25ebe40f7b0322d405e800000814ea003cc000004223c0000280f924127240628801280000000000000000000342ab242bb400001826cc00003806dc00002031dbc089c00000431a8000000000000003408074008e00fe502dde410c5472138096bc0a4f81baa4259742ac81852ec2f62a6bc0018bcc2644c14350279241e694230ba8624c187cc0383c0ff54110c0190d82edd41a9a459f1805c94717d8016fc272401a6701c11830fac601))) else (if i < 12 then (if i < 10 then (if i < 9 then 0xda8202d80aa40000340df2c55b40000282be381d3800002402fc427664292d441e0c14f000000427e000001c1c0c00000804e040b0c02fc000001c162882a900000000002c26d1c25c80000000002453d5810fbd8c564169f83249401b9c199e4314c487600000000003c08bec19c000000000018224400000419e0000000728841e3c000002a74a80dc680f4800000000000000100794000000000000003400d80000000000000001c2500000000001c13640073c81574067dec0199c0eb0c314906a5482f0e40ddbc1ad000001815ab0246d4dd3c000014254200c1d012d000001800348002c40e0945e900000000002429d0000000000181788c148c0000000002030ae81eb0c1c2c0000000000c5fc000000c1a45431b0000000000281350000000000000001c15f4c1eb800001405bc0000282c25c19b400000000000000000002c310400001814d4a5c538059eea543866cc01d5c000000000080143c679000000000000000201c09c7046467e00000000003017e80161400003402500000000b914279400000019f0000000000242b0b829300000000003c30dd4051c0000000000000038d538000000000186384000020077381c55c0f27823d1413fcc2fb400002c1c94000004dd4000000000000000059297295c1404c7c30f0807b628764000000000000000000000000000000000000000000002c0b44000030159a801fd42c9342358ac79886c46821d3405340000285be800001e57600000000000000000000000002401ae0072a018880000201866026b8681cd45b9cc23f4407f40000000000000024023a82bac41c50000028297cd1250000000000184461400b40000000000016a4000019431ec1b778d105004b2801528164241a168285d004b54243800001c15d40000000000c1b8d815b986199822c000001407df807c381c04010e0c13d082bf741fec00000c060180ad1868b28014e402a1d5783c57440000080a268264dc045041e059d46d41ed842c670079302b6d02650003d901812027b78042482b9a81020c1f9300315c26aa80d3b81cef872700000000455c289080c6b42baac2c2f008d7c0c584094004b9b80260000000000242d92c23c2005d000003c0e6000000000000000000000000008726841397826ae811c70475400001597300000182e82800e881184000000000000000015000000000001582ca802e601def655c481d4a422b8000000000341562650ff80ffd6057000000005c400001c6a374218dc0116805dc01264c0a34817f8a8cdb858e425d0a802bc0450380859019ee82a398059a0036c00000c40fe827f7801ec00002c52600000241b842057c1858c00000000028318040240000000000340fb6021de831ad0099000000430c4000004177a80a0bc53268196440c840000000000c2e2c00001c else 0xc287940fd780210c20484325cc2f880000380f2c000000000380ed400000002c8000004503c00001c01a5c1e1781a0b40092c00600192768ae7c1b6c0000000000427ae80284000034099482547c12d80000282ca7c001c00000000000000000001c1447420a5c25480000000000c2bf9801670df54c2332414a0000020876400000c2f2c0000000003c2a3c000008120302ae601e7c0000206659001dc40e2a00fac01d888876bc1e9b0111c00003023124103f011228048399719c1050c317981d140000000000000004165f8690e8018dc16784c4cc0000385d2800003c0e8000003016cc00002c122000000000018148000003c10940000281ddd0557c0000081d18000000000000002428e286801c1166819cf06d940000000002061c15430d0031f005200000080c2d02f1800000000000000386feb42ecfc5fe30163f881248278b441f400002003524714ac291d8326901a4cc2ed800002c1db84311c0000000000000000000000000000008261b00d0941fe682e300000041374c07040000040d100000180e1628846807db85cf400000c1bc40000000000000000000382cb6013c240b0ac311024ed246fbb8826fc185fc2d3400000000028273400001c29a84030301c300221c000000000000001825cd8047440da7c2b1402c47c000c00001c1334c066ec0fa7c318851248019b9c196f4158c0000081f7cc240b42e1c028648d76a8173440c3d805400000105c1dc094c00001c6ff98244a80d3404ba88283500ab6009a5441b50288bc5f888cc9000000c2b700309c00000000000000000003e9cf40000000003063b80000300ea942cd0000000000000000c2c7400000c04f781bde40f868328400000027440000101c9c02d3302aed41b35809ed8240e41d1d42a3345330008a942375c4469c07148306541e210412b8329c02350d8757815af81e580000080214c3264146480000186a4d42e3400031c1c90c20dd05d2781403c1382548c601e7b80b8000001d10b500b4d429c0000018223b110a000001c0f5c829154148883174000000000341651028bb8010fc006c40d8c000000000342fb80000042e98000020169a461b400001430c880bbdd522a83099c1ada4035b80499cd0dcc2fc80c229000200000002ef800000000000000000002021f000001014a4000004326e409c400003c07240000140ecc46e9000001040f901253467f2c5ba98d2b10155ac40f6027fec31bc0000302f4a02b64423bc000018cc9442f78c0bca8203502b0240aa0066a0816f2047b0022aac16aa8503a04a658c47105e32c17bc827338e17b446df14303415e6c0cac48892c2e734058e414e6004ee01845c29bf40758011ef42ce082c3800003c169001ea9000a00483800003c1ae04c5934303701afc80e9102cedc2f7000000000004103242a) else (if i < 11 then 0x1821fe40a7800000817dc000038138c00003c30b880fc000000c08f0c27abc1e2a0887c0000180290c266c00003825e4000038063042115800ae809e88125c0000145b8a81ef800000000000000000000000000000002fd825bc6020b4406ebc6fdf81d59067e946c1a8248cc217d0243000002995a2441d400000c0980000000000000002185dec15f2807c50199645496c311a00d0400003c207800001c0a77827ee8090cc1bac00001418000000142fd482d84000000000042d7104c4bc54a5c31f000000c22b1c321c000000000145dfe0049440180c108400003cd1da45fac00003652340000000003c21e80000000000000000000340067c2ec143150411f800002d8c669420c028fdd447ee059400002823a9811b800001426f2000100000202d8800001c718a65040000014050c0000340e0c00000000004123e00da10135c00000417e3c239b40e9800001c1658448b44225f467d481045015dc40e9d81ca441a93c187140ee8c2ec4024cf824db0069342c16447b801e51011f34256a4255fc425801f2f02bea80a8a427e4000000000000003004e8000020272000002422dc0000000002c158101f99c093e40bb380449029ebc14b400000000000000000000000000116c0000000002c2e200000000000000032516a02831c12dc00000c07cd413ec0000080cd80000000003c0c380000000001c119000002020aa01d0dc0d66c1f5d81e57c719a42ab80000342c540268400000c054cc3000000000000001ee802c110172b4141f8251b40c218123081f6c0000240e31c20cc00001818c50112cc09a800000000000000280d19c298c0000242696c1aec00003c22c4000000000000b22c24948019201393a5eb8070ff4132c000000000340c08820c40000000000000020496e00518000000000000000000000000080cb982492c3246c217b00cc602e240000280c46c0c7000002c44330232000926411c0000020085000001826d641cd90008900dc00000000000823e6d185c46dfa44bb240f41417a00000000000c48169d86242cdcc2d6000000c66280000000003004dec2ab405e9480649c0d8ac29e202715c2b2342fea428030085402d064224382256c205e41a8e041bc409b900750000000000000000c2d6c00000013440000000000c26f946623017b800000025840000000002927380000000002c16b0e058601f0d41eec000010668602290465644147a42d6b811b44591b827d2c18b4000010191082570816e444535c153800002807b28005c0000000003867cd418540000282ac54041800000c13d800f17c1bfd80988010ec80f9941769c13dc0000340dbd05450000000000000003027080000000001c09d40000082776108b000002c4c3d015100000101f8fc0cf980ee64168502ce58322802e5d828f4 else 0x466168000034007c825df41d03292cd80ca240740c2cb201a0d81ee366f3400001c0f6c00000000028298000003a5eb5824d702c8aee738c2e7400002821b800a3c00000424b24095d112608525f8022c00002803668603ac1293425c7c0409405cc0000000000c1838807740000302e01c0394910c702fccc269002dbac0eecc258800002c174dc045c00000c15b70038f005b280aaf40a6b806ad81211012c442c5c145174478acd5cc00000c098c0712dc15e18161a014d342418814200000201ff142a6800000000018023d468140000000003c224ed85e44702e4c6080000240acf41d7000000105b90452982cfbc13f4000000000381d980000000002c2d2c0000102962029ce428e8000008026801f680000201c7580344000000000000002826388139e68b700000000000ed0bc000000000000000d95ab06ef80000000001c29b4000030c2f00000000000c4474000000000200bdc00000000004208b42ea88503480f214525440a718037b81d9e44f71000c2c1b54403c2811d342ca80000202f0801e6400003c44db4318d84250d467e019d0000000000000002d126880a280000000001c684a018ed2059a0053381d87c0ae141697012a40000246e97c202000003c5bcc000008100800003423cdc2d4155560000008005800ba40000000003c18300000000000c2c4841b5c000030213a413140000042efc0000280fc4015738012c00000000020014981d6400003c18840000340d00902a800003c17d40000000003012c0000001481000003418b08216fc25f400002c1caa413a2c2b2e90482c10dc0000000000c299900bd640a58809194c9080000040e3501408000030112540edc00001020e00000340002c18d843160000000000000003414e00000200160000000000081aa203232852260203ca0562c2afec448c0000000000c0df742bd000003c06d000970000014262541356409d045c160264a810ad8238000000d8c6129f5d817ac00000418274ca8000000000004204701bbd00083416349e16400000818a48097602b5544272425f8803a80000000d5fc144c00000000000688000002020f901140000010292800001c1de140723908004479b1127400003c03b701fa0000026c78a40de40000140ead823b8c2869c424f90294000000000180c1000003c228000003408250559ac150701858000000000040bb500c9400000431ec00002441c1c118a6026b8034142cff812bd02bdc0000041bf400618000000096f82faa828cec546f0199800001419a0000039ebbc000000000000003251e4000000000001d120452c000bc4004f0307981e4c453a0013cb451e981cc8000010001740f7c00002ad0a4000000000041ae682af4008e00000202aa68327345f4a87124003ed8240183186c0267c6c16c67e70180c425d400)) else (if i < 14 then (if i < 13 then 0xa424c26c000003815b0c1c2981eac024864011cc1f03847a0026dbc010100f75c21f800001c0b31863b447178000008520ec2ba280ec582970000000000000000000000000240b17413bd8208502d1140871c28498055d0202800001c032c414500000141b4d01f780000000000018a0c0cbd41c0301332c1909c1dac00003c11dd06bde01f4f02a7cc29ac0000000000000000000000001c14dec0b768c533015ec014c1c05680000000002422700000000000428c500902c0a0e40bec142d30162242f9f08894807a654120000000000202b68456e80000000000000034263dc06b80000141a8000000000020200703115816c0817c34020c001ca82d5e40a470c60f808190720b41e60018f2806f402c63c1deb68413430a880e4c250f88549a80904c04a8421a782d65e4b4b2056cc25ae8263301971c29a1c1c4c82b19c0ea55d9c2d10c08300e29d63c0155c1e9e800f300433c17e481e4b85b6d4262e8446ccc2a10d5ba41dd841ac268cd50124001ed1c2bc7002f881a3ea92b901456c2559c71bc40470c138a8232504484000028277184c0400002d19b00000282e50810bb048ddc30f5c1ef7c05fcc07bfc142d426000000340d504076800002824edc296e4149a40ac64874998a7800000000000000000001c4254000000000000002c1f3ac1a71c229882c312551000000000000000282458000004c25442c80000025108d01b68000000000000003c1b0800000c212800001c0d2482d9d0593d4160580561400e08102c82a27c1c9a00f32421670069c869b502341c2226dc8d0c6a6186850006200d220c14ac819fcc1294d85e1802e00000000000c21300000000000000020170881aa6c1413042330077fc1fe260574027cd4453c805d4c01f0000018246400001c1c7bc0b4b023f042460a8a8a831b840dfe40e6800002016b5c19880000045e98407e800001871f0000000000000001c2c4000000001e642d16023784061c0000142eb1003b0c1cb0000028577ad02a6c2d4c000000000281f3000001c133f40544000010c2c400001c1b884191b83291012aa4720d002c142119406b38203a828dcd1254ca15681cfd01100c127f01418c065ccc2e080d5b448b0866c98032581df70079c00003c1ab1010a680219c0a200243444accd028c00000000000000000001402080000164f7c00001c0ae400001414c800000000000000141b820307ec1e2f82f39c22f6c04d00000000000000000000000000000014033a18224000000000082f12c4fc3c1cbfc1f4882afb01ee4821110149d80aec43190e074dc4723030d7413e7c2e1a00f3986dc188881412878268c00d5441b1c4139a445308122d002f7c084e817ce82170417f0c1c84c000982b84c1660000000000042de482af0000000000000000408844166f000e400368006c else 0x3813716058342e664cc8f0303b418e20251f08274000028dd44c26dc00000000030175782a5d41bd800111400b000001c01a841b2bc076000003822ce588e00000301814000028101a820d8000024258dc166481ec60025a41942023c58276140b7e41460828d385b9901f80e6ccc4302b01ab40000182316829b1d464601984427570317240e5b41acac7261908a7c278c42b04d109c0000000000000038628841fbbc22b701d40066f4015c3c16010164c406ec42a7b908c1c534b81dff94190000000000000000c29f0000000000280447821968201e028b7c0664c02af008fdc28a3c56bc0000000000c889800000408c0832380000286ec34104301b180000000000c1e414523c0000000000000000000003047004be001f6c2a1400003056ba40244e500e41f340000201cf48cadcc72140000000003c295e426e602b8a80bc40000000002c0670000000000000000000000000001c8dc1a62c19ad81146e8e2ea05a3c2a600000000000000000000301fd0000018416dc09a000002c116a830b40000194347ed0a000000408e400000e8648a9d7101c69e5b0c000000260c0000340e870100102805c01bcc1afb41bb84012000000000000000100dec0046903207997359c7578458400002a922b425a4000000000280b69013d400001c08200000010ecaad0b400002c0ccc00001901e400003823f90209c000000000241dd000001c1d4c84fc800000000000310c00002413f0800cdc11e140d1400000000038162402de80000002f3440c6cc323cc06f801c5f816b9c4763c31094714742a00006d8c087b871cdc05e48105f419e5c1f1b0294ec126f81898d928e022e68417a41b96419d45158800002821550888ec09f4000010228400dd540c42989cc0000382e11410a0c1a0000002c10c101aac0000082b580000200e05823b0000010c5e245cf30dd3800001c0e4a85328c2033c2d7c0000081071024e5817ec00003053fa8186bc46e30067c000004134e85fbf06150c0f4c000010680c00000c1c600274085222020240000000003411cdc0459817038271bc206b407ffc0132015be02cdac1a340000080ac8000000000341a8be8cb64286c00001056d2c00b880909c02de01edc0000000ec2001cc0000006dfcc1f42c02a800003e9d974074880e700000181be40000102cf00000285e86c00efc18de121694171800000820a000000000000000300200000000000342aea80f37844fc00002c236605e1180d840000382b9c00003181134024bc19a400001556c0000000000042da800002c1ce800003868240000182a7400000c0718000000000381ba480355d972e022664cb6681ecb022d8c859e40ed2c02c6c315a07115589740000142c1a182bfc5d2101d62004cb4179ac5feaac790430be00625c5378000034125a82b805) else (if i < 15 then 0xc0db3c3070d4912c3167c25ff0273e804058174881aeb8069640229c5d1f8727e81795c3133c857082b26420c381f10cd0fd010b7820bd82f464153e861adc177740b43c2d2240bc0000024699e420e80000042a8a409e00000280f7041e0012bbb41ce58075581514c0d828dd0a01adcc0e9782f7c00001824810154800002c2f5c42d3a8857f00ce00000294538000004247e00948000000000282c0000000000000000202ace424dd65ec380f8801a41c06e5c7220000010256c00000c1d240000000001825e142e0541d740000340cf40719d40172009b4510cd409540000242578810cd41784c08a40000000000000014507400003995ac0000000002008ba016c800000000020266400000000029c8dc000000000000000000000000000000416f800002059174206481d92814ec000000000142199c035d405b400003c152c000000000182c200000341dc40000041a75c0de00000142da041459808a140efe40fdf002b7005a0000000000101c7c00001c3220000000000000003c32800000310337023180000000000000000000000003461900000000003429050193e406b445e34c0b2b02f3380006c16d400003ccc9b42ea64197742a41817d080891821cb8189700fd3804a20026f1959985477426ff8078f423a7cd2d5c2a2b1024e82a51c07648316a812f2c4bb4000008233c0000000001c288f82a84000000000102d7a0262180657819600000141bcc00001c260400000000034234402134000018204c819340000380d4800000017710256602405c718c409f8c2161d82ce801f80000000003c0b5e00e26c21e00000000000000000000000002402d4c0dac00000000000000000000000000000000000000000000000003401b7c1f650d7648290000000000028875e408c6005978021d00608000000000185fdc0000000002e91b80000001eff8028800000000028724d427a1c0cde0322400002430c3c003fc231f0165401e9141a5c4186000001807ee81e44828634083d8212c41154819d800437471c7403180000140a1142c3480a384267040c0c00002c072ec186f0205a40a14004140000286e1b42c69406c902c8d8086d816dec716bc15a3c17d8c163b40320000000247902c85871a2c05f400ec942eedc03c946fd581a1c00002819780000301a3bc531800a540000369d24803848029ec2824000008259c00003412f8000000000000000000010178f014d80000042416c107400003868100000041c180000240eb8000034220e42858000000000000000000000000066d5d016ec0000000000832400000340fcf4ca4000000000000000000001c056d02ef6c162c000008607c000000000000002c08b00000301a6a28c7c000038718100d4d41e1a0d2aa8118382f17c2dc859711812049945c4119c00002d9288000 else 0x1c2b4f430a000000c19380000000003d85d8000000000282919c25920cc70000000114c000019029e829ef014c40228dc2d240000182eeac2750000000000080f580000000000805a8000038601b6d0b0000000000000000000000000000000429d40000000000000000000000003421f681d950236800002013e0811ea01a5800e6445cee82fdc0000283259804cfc0700832128210a40876c287c0207e02192c669000001410d800001412288873641d82c1af6c160c00002016be800fc0000000000000000000201809c0965412ebc241fc041e024440000340c79c2ff702ef0000000000182f5b40158815eb424bcc28a50c8fb4082ec1ce302bd941f2542df4c23fdc0e4080734000000000202fb3110b0461c400000000000000000000c0274000000000000003006600000000002072800000301db0000018113200d3e80a30000038284400002c03980000280a5000000000000000000001803f800000c716440c80000000000000000000020d760000000000368be9821d5014400000144fe44253f820c9c0b59414cc0000000e2c0000243074000030d72842a480000000003418c2))))
def nd13 (i : Nat) : Nat := 0xbd1aac85c376346000434100051cf4e2ad9711a30682000bd1911a1ed9aac88d116cf4642e23450d051db6644688000bd38ab88d11aac862ae2345802e1e9c520945ad55c46881a0a3b8ab88d1018c85c4688000800200080020008002000bd1aac85c469ba600040017a71540b80d300c0008002a07a715711a5b1b8bb60d28080008003fe7a322344db35634c823d170c88d2d8aa0db08d901a2ffb6ca064468a0008003fe7a715711a2b5590b88d314af4e2c69704ff355711a26d941c511868826ff71540b88d17fcc85c4688b87a7156c1a2098341477176c220d176cc80d0d71c50d1048000000e9fc53836f8dd5abf50e93ce792b0c60abc374ed5578a8d47687ce697b2be50c9390b1de34c5b84104a023c9776eb5b9349676cb5822db5529dd22a374527dce299c2e64e0830dd144250310420320500780a00a003ffb2d007ff5da00ffeca401ffd64803ffb27007ff58e00ffea1c01ffd92803ffb05007ff5ca00ffeb1401ffd42803ffa65007ff64600ffec0c01ffd71803ffac3007ff54600ffea0c01ffd31803ffa43007ff58200ffea0401ffd30803ffa41007ff44200bfecb401ff996803ff2ed005ff65200ffcca401ff964802ffb27007fe64e00ffcb1c01ff943802ffb25007fe64a00ffcc1401ff972803ff2c5007fe50a00ffc994017fd91803ff323007fe60600ffcb8c01ff961803ff2a3007fe50600ffc98c01ff921803ff2c1007fe50200ffc98401ff920803ff221005fe65a00bfcca4017f993802ff325005fe64600
def hx13 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x702456023ec5b58000000001c013b85c450a15833e54098ec574182218649b60e38000000000105f760e740000202c3f06640000184a800000330ec000000000000000000000002048a00000041ecc02200000288bc000016017501a22092c4018800b8e01fc28aa30135e40df801dad00b16158a000000000000000000160da000000832b00000c0468000078414211b000000000000000a006880584449f601c7b029e0000281e60000010167c017c0000201ef922b8000000000783c7214c400001c090d8a09000000000000000000000684c07e880428000050380c0c8cc524c0155401e6e0d5f8095183c361330000000000209e0b025a00002c103c881c000016084500d880000000008104841298000000001e0365c20200000c079042df0000008387c002c2239d05820824db02e20000201110000000000826800000580ac00001ea9e80000000000064322ea3418ed8997e133742c0a0143a01bef171ae0e8241f480000204542050e84cff832800000727c885b1b081a212cfc0cfc014f701f800000c0b40000058274b021cf236ac04a000000000180acf812d000003001000000000000000206cf22cd9003af039975049e0202402398375f075800003c486280a80000000002011688012d06e582a5f405280000000006033f814b608e9805c081060000010a03b079c00000000000000391f04081a414e602d1f038480a6205979094d000a8609c041d180000801c1203d0415e88216b030ee20640000301eb90617821c801202803f2034d20500c107382b760497e283dc08a78b4ae6786e031b81938831e2131a2062000000000000000401aa00d3b836c00000025240000681b530077a2e7ec1b88000000000000028128b8136301300000340cc80000000000000285259027c0000000000f18108d2011812c108414b15218214408000d0870481001450432062c02027411853000407410520080846800020931411c30051c118200000002704810e04108074301a1020410050022c004128148110028f0030460412440c079a2c20001433007820c03dc50000204000800004800a0cd80400038011814918000150a2410024c014058e0043042874cf0800051400410450040c808f0402cc0c700524210028105100770608328044004c0000801840411c30c008018058008800100e00308008324614500300004500010200a10005708830030200a6472c000a0010801010131011090090840020402040010490013ca0c00c40040001cd00d0c2081a000011040440031ce0002800030c214000300200104105414024030a2807012486c40030410411030800c01010831420450410421000430040000060000c410b0862812810440030030100010c80410c0000108040240100401003180000344000001000044101010001142 else (if i < 2 then 0x20000045fccb3a3000000000240ee00000300f7c096f019ee004ca06d280a07c18bf03c2a139be24cac037b83ad600412023400000000000000025bf4405189701147fa0c1a400ef8019a001420677046b800a42007880a43405330144501c24235980a978228713cd405b441646811530023e0d74000000000000000000000000005500000000000508a01380000000000c04cd0996000014082140a3e82e651818000000000080c5f035fa2e008539e80adc06c4c087c000060386707080000280cd80000b036e000000000000007048a000020035a811ef02dd40eef81ef281b0712b00000180548000000001e0f940000781fc407d060a5301a760a21335d480c8a4208901f6500742202cc0e5c800d51174a25678084c822f5078aa0cc0013d281ec00001e0928c02178401c0403a06b4000058097915d300224406e551b7a008c000000000000000000180b138045c813d00000cc9d9005bf81a40135200003819078023702eea289d40282021b8071600868c592981ae00001600de804f900900000000000000030183000016015c00e2e82d3606d4000000000483150000120bbc01f598bab205faae0e0c1ad603dc1028d80a2501895829df36aba004dc0d9e0184002ce8094200f36096c31116000000000702b2316d200000000040335a07c9a01980000000000000000002c0390019370392a007f40b568afbb013b680340167c039f801186244e809950236001f5a264c8075280c0e00e602448000038400f02a700f4f411f80027c074880d6f0174a80b6417f000000000000000eb3e200001c0a0f88991019800002419998ac800000c267000006019e000000000000003027e9048c0000100fde0173001420000000000000060338203eee97598a080000120b56016df8120000000000000001017cd06df80b7c40e7682f98063680355c201581d200001e08e4000020955a3042000000000502f840742006e98133c802d703a78292a4130403461051c400c2c004d821c83073c070d008e00000e05fc204008c27783834060a80a17cc6ff8acdc04b1c6271459c282616051ac24e741dcf00f241444c0ae0000000000b0370e0f9fc1616000f00000600624043000000118d024d58cf9f8b66411a9e0973c53280000507f722794000e08303702fa8001000001006d01270808e80000000000000000000258418c09f029ca21840000501e3302c02201c006b582d610373e290d80ba8000000001a0874000068151702a800003805f0000060055e0736c1d4800002148ac0191144f28295c121f22a6cc0bc7833e60681c00e704a5c01bd00000e0f67409230baa300fca0c94009f80000d05dbc291d004df8a0570440008d781011a24cc055700084c1a5e832f6070aa0d2901131010386109807544454f8969e03ce82e25880f48148 else 0x3e848801c6a00d16632c4014b0393110fba09f5c565f022c10677028280000108267061b0027901898040ca06bee022a0172e8061b07fca03f4a82880000e07e54040945cd301ee6b724a0129807100000a03e000000c20b800004017000000000050237f0700d451c000028ac4844180000301bdc0848e019d224dc85f6e83b7e02e00000000f21291fe04da00000000058179d06e7c0100000038bd4a0760a039000ac8000050675407fac5226040e00000000014092b82a0000002034601668000000000403e5cc7c00000e0344e0578000023aa90000000002009dc836600000c20aec4d0d0b9c1158e40afd017380000607560000005180000000001e0165c078b83da00000000000113801f730832000020038b8b8751278808cc00000029b406abe006c45cf6017ac01d3e0c3141f9b0126d061400000000060afa101ce0000000000000000000a2871ac3180000801ec00002c091c81d19040bc071184f70828fc02b560af000000000000001e06a7c1ffe0259d153fc00d40000000003a19ce09580132000dfb1732c0ae590f8800c2000008042e4017980d200000a035140d51041a00000e0fd80000680edf061c00001c0bf6022b301f860f4881ec401ea0000040ed000001a17500000808ec0000000000000000000000000000817b380288000018b8b411140000041b8381d7204626020480c0cd95d00000000000000000006066800000000028265d17800000141c9000000000100fc4000000000c0658000000000782c560683a0c05c04af1865602d0000000000000000000060148000000000d03e40000000006833c0000000002c13c582e400001803fc0000300c9b164200000000000000f07aee266800004001a3017a410580000282d88039f00db40000203e000000a0eb8000050a1610223a0a90c120e81b4c12696095000000000070426a085c000000000000000000385210000000000e20a40000380ec6649de0a9800001095300000200940000280d0302ae4106c0000203ca4015e000008178a0345e03b220653c5520000000000c6ec400000000080416000000000000000000182788000000000d00ee0000105f600000106f54003b409cb09dd303d340398c4d1880b4306a860890000000000306b8000028c8f58310106bc0000341a6e82e1147240000101ef80343000004278685c1a84060000000003815d580f8005f400000c607d83602052340740000030a2c0000100e9c0000383479828800000c0d000000d074b60fd000004025f81096207f400000000000000000000000200580000000003c14c800000000060732c1fae003812054e09fc000000000e082a007858184000004043d0044284a74811f000004287981e870292a206dc09b3c19480000b03fe000000000582779080a00002016600000003f)) else (if i < 4 then 0x5cf82a7007a800001c12b80000a96aa000000000481180000060fba0034980d3b069f60f46804980000f13b922897407700000501b600002c4cf7831c6172dc00af416e7007f616db6032800006838f8080e6254b44408000000000201700000000003016b22d7400000000030028000024001f0862a04e68029c80c17836e0000000855c02440096406ca0000380e0b830900001c818f808b309050000140977c51498033000006287fc17810396a06a560ab0c008603d64007c0000000005a0376056d406da8152981ab704a560a694014000605070480810c48b68326b10bd6279005530000000001a0f74000038031705a400000000068304a010e0000000000000090359227f380740d82b80562000030d280039ed03e222b980000682f7c05fea29c40000002d7504300000001b5f03b3002e4c0f34415450079902084a9494075b0a0b614e1206280000000005058000000000000000500ca00001020680000205e400001c0833818e000000000000001809cf004420420417ad013e00018e0a8e81a4e02b00034b5237f405fb0c079067140a85807f68249000b7e01f341bb800005009e00001405518092c050800824000000000b062200002016f480cb4030a327cc81c4f02bb00000000034573c805a305a800efb9846e88c9000000000299ac581620000060c678d27b82f3902b0000024022d0186711540000285de48164000012057641df9811b000000000041ce00112943e000000c0b34095b000012072000001003600000000034413c015f00000a04ac441500000b0316a20d140780000000296c2c62016ec83373025c0000240c79d20e213afb4c770157e0ace00515a04c401e5f0026d04866064400cbe001eb628b22c824605d8b322301e008f78441a82345020a0000002044827600000300780000182ec602fe0000000007828000001e0649c1b19016f00001808f901d51b11d305dc00000000000000c010400000049d9010a6069000003806d68805d04bc00000cdba1003de173120e5c000000000d12754220b814be013ab0147e0b1f819b0831ae022e54dd680de503949071180f6dc1de3816300295f6d5100a848afd604eb20f26015a4031880788e080c80d0b814d00000000000000782480000020fa8000020ae42018ee2e8800000b22e00000a100d406c202aa000000000000006086f00000000000000502e2000000000244398812c00001c0134000000000816d80000281c83818db011dc0d9000000006c00000807d500caf038c901ee00000000058b8ae0266c049fc0ec68b2d50293021edc025a89159020240f0601dea0212a113000ee9c11700000c0780000000000201db000000000144ea00000607d9404a40000602c600312c0aba809860113c05b4409a1c1608000000000000030071a3277e13bc000 else (if i < 5 then 0x21649e08640000383612423800000818b780bb105ec00003016cf824c416c28623c00005005680628000000000203a88034780af9812a800b28044a404f000000000000000003bf844bf020d614e9202ac448480000a17d22010c000000000b051180cb8000070293d078c000000000000005005ce0a0ec002f8044806fa424f40000003f0806b0e0bd0000000000200e800001c1005029fe163c000000000100c300000000000000281bb706ec0000881bfcc865b046482802819ce810c107ee2651ac17e48156d15fe00003002080000a03c400ed80000580bc00001e65dc00000000000517009b80000000000000160ff585f580000001bd266cd41fd2835000001e299c000010a699044600002c5cd8000060300209bc0000002300000000000000000000102f600000000000000000000000385367023800000c2ee6c57c8000001718000000000403fc000000000000003cbff00001e05a6014300000ba0f200003846e80214107142238800000000000000e05080000000007060422cac04142828c360402053284b5800000000080e610086c031f803be2026a45d65aa7b9026900ad704f63026b017a7e065ad807380a0612a3e0de181be00000c0485e03d400001096d000002077701e7802ca760eb40ebca8fb28353a06b2208420d8dd99b2f645fe0005c1d33800be073460002c1f30000030702e69e0c0376914400001e6e4dc05cb0a1d8152c0231d40d9083b87b1ec0000111541024f0000020a0800000027b001bbe09a7d9d81032a6081f546d980b5e0bd7200a746837411e3d252f145b20b24803e80107746a9a0c3f4106600aec15a80000000000000040648407694566000000000002693c016082ad000000000345f3b02ebe002be2918000028076000000000000000887e9160d0102fc0ae6006700000c066000004005e0026a6047580f2a81e8a04e4407b4000048bb7313c760e4584b190006000e1e0210800b8026a000000000101388000000000808a685d758b16000010099ac1a890165111d5c0b3980ba68954d0815c2574c4b90000040183c0467c087c03b2c6135601e800000000000001c0189804180000e03e6e102681740000070064a039745b2281764037e003360599b4ad820321804bd81ab688b88065be0e6dc0ea58b683060e72c6facf868a20657884018cc0943a89191424a2d9e848680000b06f240aa60488d0acf202b760d32a5c9902eab0318081d3c0a2a01ca50827d409141314019fa5024a0e57054c8816c5048e42440000078a9c212acac6c7a584800000000040938c0f04082d000000000000003283b0000060f88000000000e528f60b2f40ef783a20000000000000000000b154062f400000400ba000016281e01f1c80c85140c00002c09b90a23e048880cc580d40819a8110d4257244 else 0x384d2800000000120fe400005020f3016040f5740eb203ef200a38009000006397600001c0dd0000000000f071b60126c1d8e800700001e024541f0a01f4f0820c0829c1800000040544409e5655500000501af801e1c1f680)))
def lv : Nat → Packing
  | 9 => (34,6,7,0,0,9,0,nd9)
  | 10 => (913,5,7,0,0,15,0,nd10)
  | 11 => (3240,4,7,0,0,17,0,nd11)
  | 12 => (1052,3,7,0,0,16,0,nd12)
  | 13 => (62,2,7,0,0,11,0,nd13)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 12 60 4 14 6 4 hx10
  | 11 => lookupWord 344 1447 6 18 10 4 hx11
  | 12 => lookupWord 1386 5829 7 20 12 4 hx12
  | 13 => lookupWord 485 2042 6 19 11 4 hx13
  | _ => fun _ => none
def allColumns3640 : IndexTree ColumnInfo := .fork 126 deadcolumns (.leaf [(0,0,511,0,15)])
def candidate (cut : ExtraCut) (hc : ∀ k (ws : List Sig), ws.Nodup →
    cut k ws = true → Impossible (chartGoal 511) k ws.toFinset) : Forest :=
  ⟨511,13,fun j => deadsamples[j]?.getD (0,0),allColumns3640,deadautos,lv,ix,cut,hc⟩

def search3640 := candidate shapeCut3640 shapeCut3640_sound

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk9_0 : block search3640 9 0 29=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk9_29 : block search3640 9 29 5=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_0 : block search3640 10 0 96=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_96 : block search3640 10 96 96=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_192 : block search3640 10 192 2=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_194 : block search3640 10 194 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_290 : block search3640 10 290 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_386 : block search3640 10 386 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_482 : block search3640 10 482 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_578 : block search3640 10 578 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_674 : block search3640 10 674 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_770 : block search3640 10 770 68=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk10_838 : block search3640 10 838 75=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_0 : block search3640 11 0 31=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_31 : block search3640 11 31 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_127 : block search3640 11 127 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_223 : block search3640 11 223 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_319 : block search3640 11 319 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_415 : block search3640 11 415 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_511 : block search3640 11 511 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_607 : block search3640 11 607 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_703 : block search3640 11 703 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_799 : block search3640 11 799 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_895 : block search3640 11 895 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_991 : block search3640 11 991 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1087 : block search3640 11 1087 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1183 : block search3640 11 1183 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1279 : block search3640 11 1279 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1375 : block search3640 11 1375 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1471 : block search3640 11 1471 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1567 : block search3640 11 1567 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1663 : block search3640 11 1663 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1759 : block search3640 11 1759 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1855 : block search3640 11 1855 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_1951 : block search3640 11 1951 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2047 : block search3640 11 2047 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2143 : block search3640 11 2143 5=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2148 : block search3640 11 2148 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2244 : block search3640 11 2244 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2340 : block search3640 11 2340 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2436 : block search3640 11 2436 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2532 : block search3640 11 2532 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2628 : block search3640 11 2628 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2724 : block search3640 11 2724 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2820 : block search3640 11 2820 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_2916 : block search3640 11 2916 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_3012 : block search3640 11 3012 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_3108 : block search3640 11 3108 26=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_3134 : block search3640 11 3134 96=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk11_3230 : block search3640 11 3230 10=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_0 : block search3640 12 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_1 : block search3640 12 1 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_97 : block search3640 12 97 96=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_193 : block search3640 12 193 60=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_253 : block search3640 12 253 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_349 : block search3640 12 349 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_445 : block search3640 12 445 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_541 : block search3640 12 541 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_637 : block search3640 12 637 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_733 : block search3640 12 733 96=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_829 : block search3640 12 829 28=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_857 : block search3640 12 857 96=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_953 : block search3640 12 953 96=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk12_1049 : block search3640 12 1049 3=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk13_0 : block search3640 13 0 5=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk13_5 : block search3640 13 5 31=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem chk13_36 : block search3640 13 36 26=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all9 : block search3640 9 0 34=true := (@block_merge search3640 9 0 29 5 chk9_0 chk9_29)
theorem all10 : block search3640 10 0 913=true := (@block_merge search3640 10 0 386 527 (@block_merge search3640 10 0 192 194 (@block_merge search3640 10 0 96 96 chk10_0 chk10_96) (@block_merge search3640 10 192 2 192 chk10_192 (@block_merge search3640 10 194 96 96 chk10_194 chk10_290))) (@block_merge search3640 10 386 288 239 (@block_merge search3640 10 386 96 192 chk10_386 (@block_merge search3640 10 482 96 96 chk10_482 chk10_578)) (@block_merge search3640 10 674 96 143 chk10_674 (@block_merge search3640 10 770 68 75 chk10_770 chk10_838))))
theorem all11 : block search3640 11 0 3240=true := (@block_merge search3640 11 0 1663 1577 (@block_merge search3640 11 0 799 864 (@block_merge search3640 11 0 319 480 (@block_merge search3640 11 0 127 192 (@block_merge search3640 11 0 31 96 chk11_0 chk11_31) (@block_merge search3640 11 127 96 96 chk11_127 chk11_223)) (@block_merge search3640 11 319 192 288 (@block_merge search3640 11 319 96 96 chk11_319 chk11_415) (@block_merge search3640 11 511 96 192 chk11_511 (@block_merge search3640 11 607 96 96 chk11_607 chk11_703)))) (@block_merge search3640 11 799 384 480 (@block_merge search3640 11 799 192 192 (@block_merge search3640 11 799 96 96 chk11_799 chk11_895) (@block_merge search3640 11 991 96 96 chk11_991 chk11_1087)) (@block_merge search3640 11 1183 192 288 (@block_merge search3640 11 1183 96 96 chk11_1183 chk11_1279) (@block_merge search3640 11 1375 96 192 chk11_1375 (@block_merge search3640 11 1471 96 96 chk11_1471 chk11_1567))))) (@block_merge search3640 11 1663 773 804 (@block_merge search3640 11 1663 384 389 (@block_merge search3640 11 1663 192 192 (@block_merge search3640 11 1663 96 96 chk11_1663 chk11_1759) (@block_merge search3640 11 1855 96 96 chk11_1855 chk11_1951)) (@block_merge search3640 11 2047 101 288 (@block_merge search3640 11 2047 96 5 chk11_2047 chk11_2143) (@block_merge search3640 11 2148 96 192 chk11_2148 (@block_merge search3640 11 2244 96 96 chk11_2244 chk11_2340)))) (@block_merge search3640 11 2436 480 324 (@block_merge search3640 11 2436 192 288 (@block_merge search3640 11 2436 96 96 chk11_2436 chk11_2532) (@block_merge search3640 11 2628 96 192 chk11_2628 (@block_merge search3640 11 2724 96 96 chk11_2724 chk11_2820))) (@block_merge search3640 11 2916 192 132 (@block_merge search3640 11 2916 96 96 chk11_2916 chk11_3012) (@block_merge search3640 11 3108 26 106 chk11_3108 (@block_merge search3640 11 3134 96 10 chk11_3134 chk11_3230))))))
theorem all12 : block search3640 12 0 1052=true := (@block_merge search3640 12 0 541 511 (@block_merge search3640 12 0 193 348 (@block_merge search3640 12 0 1 192 chk12_0 (@block_merge search3640 12 1 96 96 chk12_1 chk12_97)) (@block_merge search3640 12 193 156 192 (@block_merge search3640 12 193 60 96 chk12_193 chk12_253) (@block_merge search3640 12 349 96 96 chk12_349 chk12_445))) (@block_merge search3640 12 541 288 223 (@block_merge search3640 12 541 96 192 chk12_541 (@block_merge search3640 12 637 96 96 chk12_637 chk12_733)) (@block_merge search3640 12 829 124 99 (@block_merge search3640 12 829 28 96 chk12_829 chk12_857) (@block_merge search3640 12 953 96 3 chk12_953 chk12_1049))))
theorem all13 : block search3640 13 0 62=true := (@block_merge search3640 13 0 5 57 chk13_0 (@block_merge search3640 13 5 31 26 chk13_5 chk13_36))
theorem tables3640 : checkedTables search3640 13 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact all9
  · exact all10
  · exact all11
  · exact all12
  · exact all13


def base3122 : List Sig := inputs ++ [neg (inputs.getD 0 zero)]
def codes3122 : List Nat := [1,2,3,4,5,6,7,8,12,13,14,15,16,17,18,19,23,24,25,26,27,28,29,34,35,36,37,38,39,45,46,47,48,49,56,57,58,59,67,68,69,78,79,89]
def code3122 (p : Fin 44) : Nat := codes3122.getD p.val 0
def or3122 (p : Fin 44) : Sig :=
  bin true (base3122.getD (code3122 p / 10) zero) (base3122.getD (code3122 p % 10) zero)
def bank3122 (p : Fin 44) : List Sig := base3122 ++ [or3122 p]


lemma oneGate3122 (dead : Impossible graph 14 inputs.toFinset) {x k t S}
    (gate : witness inputs x) (m : k≤13) (h : Live graph k t S)
    (sub : ∀ v∈S, v∈inputs++[x]) : False := by
  obtain ⟨k',t',S',hk,l,rs⟩ := pull_gate h (Or.inr gate) sub
  have lose : ∀ j : Fin 9,
      (bit (absentRow j) graph != bit (presentRow j) graph) &&
      (inputs.all fun w => w == (inputs.getD j.val zero) ||
         bit (absentRow j) w == bit (presentRow j) w) = true := by decide +kernel
  have all (j : Fin 9) : (inputs.getD j.val zero) ∈ S' := by
    have cut := lose j
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    exact raw_required l _ _ rs _ _ cut.1 (fun v hv ne => (cut.2 v hv).resolve_left ne)
  have eq : S'=inputs.toFinset := by
    ext v
    refine ⟨fun hv => List.mem_toFinset.mpr (rs _ hv),?_⟩
    rw [List.mem_toFinset,←input_list,List.mem_ofFn]
    rintro ⟨j,rfl⟩
    exact all j
  exact dead _ _ (by omega) (eq ▸ l)


open PEqualNP.CircuitLowerBounds

def positive3122 := inputs.getD 0 zero
def negative3122 := neg positive3122
def roots3122 (p : Fin 44) (x n : Bool) :=
  inputs.tail ++ (if x then [positive3122] else []) ++
    (if n then [negative3122] else []) ++ [or3122 p]

lemma rootMem3122 (p : Fin 44) (x n : Bool) (v : Sig) :
    v ∈ (roots3122 p x n).toFinset ↔ v∈inputs.tail ∨
      (v=positive3122 ∧ x=true) ∨ (v=negative3122 ∧ n=true) ∨ v=or3122 p := by
  cases x <;> cases n <;> simp [roots3122, or_assoc, or_left_comm, or_comm]

lemma sourceMem3122 {p : Fin 44} {v : Sig} :
    v∈bank3122 p → v∈inputs.tail ∨ v=positive3122 ∨ v=negative3122 ∨ v=or3122 p := by
  change v ∈ (inputs ++ [negative3122]) ++ [or3122 p] → _
  intro hv
  rcases List.mem_append.mp hv with hbase|ho
  · rcases List.mem_append.mp hbase with hr|hn
    · change v ∈ positive3122::inputs.tail at hr
      rcases List.mem_cons.mp hr with hx|ht
      · exact .inr (.inl hx)
      · exact .inl ht
    · exact .inr (.inr (.inl (List.mem_singleton.mp hn)))
  · exact .inr (.inr (.inr (List.mem_singleton.mp ho)))

def isolate3122 (p : Fin 44) (j : Fin 8) : Row :=
  Fin.ofNat 512 (([1, 2, 4, 1, 1, 2, 4, 8, 1, 9, 4, 1, 1, 2, 4, 8, 1, 2, 5, 1, 1, 2, 4, 8, 1, 2, 4, 1, 1, 2, 4, 8, 1, 2, 4, 1, 1, 2, 4, 8, 1, 2, 4, 1, 1, 257, 4, 8, 1, 2, 4, 1, 1, 2, 5, 8, 1, 2, 4, 1, 1, 2, 4, 9, 4, 2, 4, 1, 1, 2, 4, 8, 9, 2, 18, 1, 1, 2, 4, 8, 20, 2, 4, 10, 1, 2, 4, 8, 36, 2, 4, 1, 130, 2, 4, 8, 64, 2, 4, 1, 1, 2, 4, 8, 129, 2, 4, 1, 1, 2, 34, 8, 257, 2, 4, 1, 1, 2, 4, 10, 4, 2, 4, 1, 1, 2, 4, 8, 1, 8, 4, 1, 1, 2, 4, 8, 1, 18, 4, 5, 1, 2, 4, 8, 1, 34, 4, 1, 5, 2, 4, 8, 1, 72, 4, 1, 1, 260, 4, 8, 1, 128, 4, 1, 1, 2, 4, 8, 1, 258, 4, 1, 1, 2, 4, 36, 1, 2, 4, 1, 1, 2, 4, 8, 1, 2, 16, 8, 1, 2, 4, 8, 1, 2, 36, 1, 9, 2, 4, 8, 1, 2, 68, 1, 1, 10, 4, 8, 1, 2, 144, 1, 1, 2, 40, 8, 1, 2, 256, 1, 1, 2, 4, 8, 1, 2, 4, 1, 1, 2, 4, 8, 1, 2, 4, 40, 144, 2, 4, 8, 1, 2, 4, 65, 1, 18, 4, 8, 1, 2, 4, 129, 1, 2, 20, 8, 1, 2, 4, 257, 1, 2, 4, 48, 1, 2, 4, 8, 1, 2, 4, 8, 1, 2, 4, 1, 65, 34, 4, 8, 1, 2, 4, 1, 128, 2, 32, 8, 1, 2, 4, 1, 256, 2, 4, 32, 1, 2, 4, 1, 128, 2, 4, 8, 1, 2, 4, 1, 1, 130, 68, 8, 1, 2, 4, 1, 1, 256, 4, 64, 1, 2, 4, 1, 1, 2, 4, 8, 1, 2, 4, 1, 1, 2, 260, 136, 1, 2, 4, 1, 1, 2, 4, 8, 1, 2, 4, 1, 1, 2, 4, 8] : List Nat).getD (p.val*8+j.val) 0)
def raise3122 (p : Fin 44) (j : Fin 8) : Row :=
  Fin.ofNat 512 ((isolate3122 p j).val ||| (1 <<< (j.val+1)))

lemma tailWitness3122 : ∀ p : Fin 44, ∀ j : Fin 8,
    (bit (isolate3122 p j) graph != bit (raise3122 p j) graph) &&
    ((bank3122 p).all fun w => w == inputs.getD (j.val+1) zero ||
      bit (isolate3122 p j) w == bit (raise3122 p j) w) = true := by decide +kernel

lemma tailMust3122 {p k t S} (h : Live graph k t S) (sub : ∀ v∈S, v∈bank3122 p) :
    ∀ v∈inputs.tail, v∈S := by
  have each (j : Fin 8) : inputs.getD (j.val+1) zero ∈ S := by
    have cut := tailWitness3122 p j
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    exact raw_required h _ _ sub _ _ cut.1 (fun v hv ne => (cut.2 v hv).resolve_left ne)
  have eq : List.ofFn (fun j : Fin 8 => inputs.getD (j.val+1) zero)=inputs.tail := rfl
  intro v hv
  rw [←eq,List.mem_ofFn] at hv
  obtain ⟨j,rfl⟩ := hv
  exact each j

lemma rawOr3122 {p : Fin 44} (hs : code3122 p % 10 ≠ 9) : witness inputs (or3122 p) := by
  let left := fun p : Fin 44 => base3122.getD (code3122 p / 10) zero
  let right := fun p : Fin 44 => base3122.getD (code3122 p % 10) zero
  have info : ∀ q : Fin 44, code3122 q % 10 ≠ 9 → left q ∈ inputs ∧ right q ∈ inputs ∧
      proper (left q) ∧ proper (right q) ∧ left q ≠ right q := by
    dsimp only [proper,left,right]
    decide +kernel
  obtain ⟨hm,hn,pm,pn,ne⟩ := info p hs
  exact .inr ⟨true,_,_,hm,hn,pm,pn,ne,rfl⟩

lemma useRoots3122 (dead : Impossible graph 14 inputs.toFinset)
    (audit : ∀ (p : Fin 44) (x n : Bool), n=true ∨ code3122 p % 10=9 →
      Impossible graph 13 (roots3122 p x n).toFinset)
    (p : Fin 44) (k t : Nat) (S : Finset Sig) (small : k ≤ 13)
    (live : Live graph k t S) (sub : ∀ v∈S,v∈bank3122 p) : False := by
  have needed : or3122 p ∈ S := by
    by_contra missing
    have gate : witness inputs negative3122 := .inl ⟨_,by decide +kernel,by unfold proper; decide +kernel,rfl⟩
    apply oneGate3122 dead gate small live
    intro v hv
    have hv' := sub _ hv
    change v∈(inputs++[negative3122])++[or3122 p] at hv'
    rcases List.mem_append.mp hv' with base|added
    · exact base
    · have e : v=or3122 p := List.mem_singleton.mp added
      exact (missing (e ▸ hv)).elim
  let x := decide (positive3122∈S)
  let n := decide (negative3122∈S)
  have tail := tailMust3122 live sub
  have eq : S=(roots3122 p x n).toFinset := by
    ext v
    rw [rootMem3122]
    simp only [x,n,decide_eq_true_eq]
    constructor
    · intro hv
      rcases sourceMem3122 (sub _ hv) with base|eq|eq|extra
      · exact .inl base
      · exact .inr (.inl ⟨eq,eq ▸ hv⟩)
      · exact .inr (.inr (.inl ⟨eq,eq ▸ hv⟩))
      · exact .inr (.inr (.inr extra))
    · rintro (w|⟨rfl,w⟩|⟨rfl,w⟩|rfl)
      · exact tail _ w
      · exact w
      · exact w
      · exact needed
  by_cases hn : negative3122∈S
  · exact audit p x n (.inl (by simp [n,hn])) _ _ small (eq ▸ live)
  by_cases cross : code3122 p % 10=9
  · exact audit p x n (.inr cross) _ _ small (eq ▸ live)
  apply oneGate3122 dead (rawOr3122 cross) small live
  intro v hv
  rcases sourceMem3122 (sub _ hv) with ht|xp|en|eo
  · exact List.mem_append_left _ (by rw [show inputs=positive3122::inputs.tail from rfl]; exact List.mem_cons_of_mem _ ht)
  · exact List.mem_append_left _ (by rw [xp]; decide +kernel)
  · exact (hn (en ▸ hv)).elim
  · simp [eo]


def forest3122 := candidate shapeCut3640 shapeCut3640_sound
def linkFor3122 (p : Fin 44) (x n : Bool) : Nat × Nat :=
  ([(0,0),(5,0),(0,0),(36,0),(0,0),(6,0),(0,0),(37,0),(0,0),(7,0),(0,0),(38,0),(0,0),(8,0),(0,0),(39,0),(0,0),(5,1),(0,0),(36,1),(0,0),(9,0),(0,0),(40,0),(0,0),(9,1),(0,0),(40,1),(0,0),(6,1),(0,0),(37,1),(0,0),(10,0),(0,0),(41,0),(0,0),(11,0),(0,0),(42,0),(0,0),(12,0),(0,0),(43,0),(0,0),(13,0),(0,0),(44,0),(0,0),(14,0),(0,0),(45,0),(0,0),(15,0),(0,0),(46,0),(0,0),(16,0),(0,0),(47,0),(0,0),(17,0),(18,0),(48,0),(0,0),(19,0),(0,0),(49,0),(0,0),(20,0),(0,0),(50,0),(0,0),(16,1),(0,0),(47,1),(0,0),(21,0),(0,0),(51,0),(0,0),(22,0),(0,0),(52,0),(0,0),(23,0),(0,0),(53,0),(1,0),(24,0),(25,0),(54,0),(0,0),(26,0),(0,0),(55,0),(0,0),(11,1),(0,0),(42,1),(0,0),(27,0),(0,0),(56,0),(0,0),(27,1),(0,0),(56,1),(0,0),(19,1),(0,0),(49,1),(2,0),(28,0),(29,0),(57,0),(0,0),(12,1),(0,0),(43,1),(0,0),(30,0),(0,0),(58,0),(0,0),(30,1),(0,0),(58,1),(0,0),(20,1),(0,0),(50,1),(3,0),(31,0),(32,0),(59,0),(0,0),(15,1),(0,0),(46,1),(0,0),(14,1),(0,0),(45,1),(0,0),(10,1),(0,0),(41,1),(0,1),(17,1),(18,1),(48,1),(0,0),(33,0),(0,0),(60,0),(0,0),(22,1),(0,0),(52,1),(4,0),(34,0),(35,0),(61,0),(0,0),(21,1),(0,0),(51,1),(4,1),(34,1),(35,1),(61,1),(1,1),(24,1),(25,1),(54,1)] : List (Nat × Nat)).getD (4*p.val + 2*x.toNat + n.toNat) (0,0)

def validLink3122 (p : Fin 44) (x n : Bool) : Bool :=
  match linkedSet forest3122 13 (linkFor3122 p x n) with
  | none => false
  | some out => sameWords out (roots3122 p x n)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem links3122 : ∀ (p : Fin 44) (x n : Bool),
    n=true ∨ code3122 p % 10=9 → validLink3122 p x n=true := by decide +kernel

theorem audit3122 {prior : Nat → Nat} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid forest3122 prior = true)
    (tables : checkedTables forest3122 13) (p : Fin 44) (x n : Bool)
    (mode : n=true ∨ code3122 p % 10=9) : Impossible graph 13 (roots3122 p x n).toFinset := by
  have all := forest_all forest3122 13 prior low geom tables 13 (by decide)
  have names : ∀ z∈forest3122.autos.toList, autoOK (targetOf forest3122) (z.map swapRows)=true := by
    have hg := geom
    simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at hg
    exact hg.2
  have matchRows := links3122 p x n mode
  unfold validLink3122 at matchRows
  cases h : linkedSet forest3122 13 (linkFor3122 p x n) with
  | none => simp [h] at matchRows
  | some out =>
    simp only [h] at matchRows
    have impossible := linkedSet_sound forest3122 13 names all h
    have tgt : targetOf forest3122=graph := by decide +kernel
    rw [←sameWords_sound matchRows,←tgt]
    exact impossible

open PEqualNP.CircuitLowerBounds

private def Class3122 (v : Sig) : Prop :=
  v=zero ∨ v=one ∨ v∈base3122 ∨ ∃ p : Fin 44, v=or3122 p

theorem pairClass3122 : ∀ a b : Fin 11,
    let v := bin true (base3122.getD a.val zero) (base3122.getD b.val zero)
    v=zero ∨ v=one ∨ v∈base3122 ∨ ∃ p : Fin 44, v=or3122 p := by decide +kernel

private lemma clip3122 (i : Nat) :
    base3122.getD i zero = base3122.getD (min i 10) zero := by
  by_cases hi : i ≤ 10
  · rw [Nat.min_eq_left hi]
  · have le : 10 ≤ i := by omega
    rw [Nat.min_eq_right le]
    have len : base3122.length ≤ i := le
    rw [List.getD_eq_default _ _ len]
    rfl

theorem classify3122 (pins : List Nat) (two : pins.length ≤ 2) :
    gv base3122 ⟨.or,pins⟩ = zero ∨ gv base3122 ⟨.or,pins⟩ = one ∨
    gv base3122 ⟨.or,pins⟩ ∈ base3122 ∨ ∃ p : Fin 44, gv base3122 ⟨.or,pins⟩ = or3122 p := by
  change Class3122 _
  cases pins with
  | nil => exact .inl rfl
  | cons a as =>
    cases as with
    | nil =>
      change Class3122 (bin true (base3122.getD a zero) zero)
      rw [(bin_laws _).2.1]
      rw [clip3122 a]
      have h : Class3122 (bin true (base3122.getD (min a 10) zero) (base3122.getD 10 zero)) :=
        pairClass3122 ⟨_,by omega⟩ 10
      change Class3122 (bin true (base3122.getD (min a 10) zero) zero) at h
      rwa [(bin_laws _).2.1] at h
    | cons b bs =>
      cases bs with
      | cons c cs => simp at two
      | nil =>
        change Class3122 (bin true (base3122.getD a zero) (bin true (base3122.getD b zero) zero))
        rw [(bin_laws _).2.1,clip3122 a,clip3122 b]
        exact pairClass3122 ⟨_,by omega⟩ ⟨_,by omega⟩

lemma bits_base3122 (r : Row) : base3122.map (bit r) = List.ofFn (sample r) ++ [!(sample r 0)] := by
  simp only [base3122,List.map_append,List.map_cons,List.map_nil,bit_neg,←sampled]
  rfl

lemma arbitraryBank3122 (pins : List Nat) (C : Circuit)
    (fan : PEqualNP.MetaComplexity.FanInTwo C) (small : C.size ≤ 13)
    (correct : ∀ x : Fin 9 → Bool, let a := List.ofFn x ++ [!x 0]
      C.eval (a ++ [GateOp.or.eval (pins.map fun j => a.getD j false)]) = edge x) :
    ∃ k t S, k≤13 ∧ Live graph k t S ∧ ∀ w∈S, w∈base3122 ++ [gv base3122 ⟨.or,pins⟩] := by
  let b := base3122 ++ [gv base3122 ⟨.or,pins⟩]
  have goalEq : (execute C.gates b).getD C.output zero=graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r _=bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg => (fan g hg).1)]
    have bits : b.map (bit r) = (List.ofFn (sample r) ++ [!(sample r 0)]) ++
        [GateOp.or.eval (pins.map fun j => (List.ofFn (sample r) ++ [!(sample r 0)]).getD j false)] := by
      simp only [b,List.map_append,List.map_cons,List.map_nil]
      rw [run_bit r ⟨.or,pins⟩ _ (by simp),bits_base3122]
    rw [bits]
    exact (correct (sample r)).trans (edge_table r).symm
  have out := get_rep (execute C.gates b) C.output
  rw [goalEq] at out
  obtain ⟨k,t,S,sz,h,hs⟩ := extract C.gates b fan graph_proper (out.resolve_right (fun x => x graph_proper))
  exact ⟨k,t,S,sz.trans small,h,hs⟩

theorem exact3122 (dead : Impossible graph 14 inputs.toFinset)
    (audit : ∀ (p : Fin 44) k t S, k≤13 → Live graph k t S → (∀ w∈S, w∈bank3122 p) → False) :
∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro pins two C fan small _gate
  by_contra! comp
  obtain ⟨k,t,S,hk,run,sub⟩ := arbitraryBank3122 pins C fan small (fun x => Classical.not_not.mp (comp x))
  let z := gv base3122 ⟨.or,pins⟩
  have baseBad (extra : z=zero ∨ z=one ∨ z∈base3122) : False := by
    have ng : witness inputs (neg (inputs.getD 0 zero)) :=
      Or.inl ⟨_,by decide +kernel,by unfold proper; decide +kernel,rfl⟩
    apply oneGate3122 dead ng hk run
    intro w hw
    have wm := sub w hw
    change w∈base3122 ++ [z] at wm
    rcases List.mem_append.mp wm with base|last
    · exact base
    have eq := List.mem_singleton.mp last
    have pr := live_proper run w hw
    rcases extra with h0|h1|hm
    · exact (pr.1 (eq.trans h0)).elim
    · exact (pr.2 (eq.trans h1)).elim
    · exact eq ▸ hm
  rcases classify3122 pins two with h0|h1|hm|⟨p,hp⟩
  · exact baseBad (.inl h0)
  · exact baseBad (.inr (.inl h1))
  · exact baseBad (.inr (.inr hm))
  · apply audit p k t S hk run
    intro w hw
    simpa only [bank3122,←hp] using sub w hw


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geometry3122 : graphValid forest3122 bounds511 = true := by decide +kernel

end PEqualNP.Outside.L_meta_3122

open PEqualNP.Outside.L_meta_3122

theorem PEqualNP.Outside.L_meta_3122 : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  exact exact3122 dead_start (useRoots3122 dead_start (audit3122 bounds511_sound geometry3122 tables3640))
