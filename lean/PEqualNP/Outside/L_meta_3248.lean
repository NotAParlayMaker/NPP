import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3248_aux

namespace SignedLive

abbrev Word (n : Nat) := BitVec (n+1)

def flip {n} (b : Bool) (a : Word n) := if b then ~~~a else a
def norm {n} (a : Word n) := flip (a.getLsbD 0) a
def gate {n} (u v : Bool) (a b : Word n) :=
  norm (flip u a &&& flip v b)

theorem flip_twice {n} (b : Bool) (a : Word n) : flip b (flip b a) = a := by
  cases b <;> simp [flip,BitVec.not_not]

theorem norm_neg {n} (a : Word n) : norm (~~~a) = norm a := by
  unfold norm
  simp only [BitVec.getLsbD_not,show decide (0 < n+1) = true by simp,Bool.true_and]
  cases a.getLsbD 0 <;> simp [flip,BitVec.not_not]

theorem norm_zero {n} : norm (0 : Word n) = 0 := by simp [norm,flip]

theorem norm_idem {n} (a : Word n) : norm (norm a) = norm a := by
  change norm (flip (a.getLsbD 0) a) = _
  cases h : a.getLsbD 0 <;> simp [flip,norm_neg]

theorem unnorm {n} (a : Word n) : flip (a.getLsbD 0) (norm a) = a :=
  flip_twice _ _

theorem norm_cases {n} (a : Word n) : a = norm a ∨ a = ~~~(norm a) := by
  have h := unnorm a
  cases v : a.getLsbD 0
  · exact Or.inl (by simpa only [v,flip,Bool.false_eq_true,ite_false] using h.symm)
  · exact Or.inr (by simpa only [v,flip,ite_true] using h.symm)

theorem gate_of {n} (a b : Word n) :
    gate (a.getLsbD 0) (b.getLsbD 0) (norm a) (norm b) = norm (a &&& b) := by
  simp only [gate,unnorm]

theorem degeneracy {n} (a b : Word n)
    (h : norm a = 0 ∨ norm b = 0 ∨ norm a = norm b) :
    norm (a &&& b) = 0 ∨ norm (a &&& b) = norm a ∨ norm (a &&& b) = norm b := by
  rcases h with ha | hb | he
  · rcases norm_cases a with h | h
    · rw [ha] at h
      simp [h]
    · rw [ha] at h
      simp [h]
  · rcases norm_cases b with h | h
    · rw [hb] at h
      simp [h]
    · rw [hb] at h
      simp [h]
  · have same : a = b ∨ a = ~~~b := by
      rcases norm_cases a with ha | ha <;> rcases norm_cases b with hb | hb
      · exact Or.inl (ha.trans (he.trans hb.symm))
      · have h : ~~~b = norm b := (congrArg (fun x : Word n => ~~~x) hb).trans BitVec.not_not
        exact Or.inr (ha.trans (he.trans h.symm))
      · exact Or.inr (ha.trans (congrArg (fun x : Word n => ~~~x) (he.trans hb.symm)))
      · exact Or.inl (ha.trans ((congrArg (fun x : Word n => ~~~x) he).trans hb.symm))
    rcases same with h | h
    · rw [h,BitVec.and_self]
      exact Or.inr (Or.inl rfl)
    · rw [h,BitVec.not_and_self]
      exact Or.inl norm_zero

inductive Live {n} (tgt : Word n) : Nat → Finset (Word n) → Prop where
  | stop : tgt ≠ 0 → Live tgt 0 {tgt}
  | step {k U} {a b : Word n} {u v : Bool} :
      a ≠ 0 → b ≠ 0 → a ≠ b → gate u v a b ∉ insert a (insert b U) →
      Live tgt k (insert (gate u v a b) U) →
      Live tgt (k+1) (insert a (insert b U))

theorem nonzero {n} {T : Word n} {k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction h with
  | stop h => simpa using h
  | step ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem size {n} {T : Word n} {k S} (h : Live T k S) : S.card ≤ k+1 := by
  induction h with
  | stop => simp
  | @step k U a b u v _ _ _ fresh _ ih =>
    have hz : gate u v a b ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem hz] at ih
    have ha := Finset.card_insert_le a (insert b U)
    have hb := Finset.card_insert_le b U
    omega

def pool {n} (w : List (Word n)) := (w.map norm).toFinset
def add {n} (w : List (Word n)) (p : Nat × Nat) :=
  let z := w.getD p.1 0 &&& w.getD p.2 0
  w ++ [z,~~~z]

theorem pool_add {n} (w : List (Word n)) (i j : Nat) :
    pool (add w (i,j)) = insert (norm (w.getD i 0 &&& w.getD j 0)) (pool w) := by
  ext v
  simp [pool,add,norm_neg,or_comm]

theorem present {n} (w : List (Word n)) (i : Nat) :
    norm (w.getD i 0) = 0 ∨ norm (w.getD i 0) ∈ pool w := by
  by_cases h : i < w.length
  · right
    rw [List.getD_eq_getElem _ _ h]
    exact List.mem_toFinset.mpr (List.mem_map_of_mem (List.getElem_mem h))
  · left
    rw [List.getD_eq_default _ _ (by omega),norm_zero]

theorem pull {n k} {T : Word n} {S} (h : Live T k S) (w : List (Word n)) (i j : Nat)
    (sub : S ⊆ pool (add w (i,j))) :
    ∃ k' S', k' ≤ k+1 ∧ Live T k' S' ∧ S' ⊆ pool w := by
  rw [pool_add] at sub
  let a := w.getD i 0
  let b := w.getD j 0
  let z := norm (a &&& b)
  change S ⊆ insert z (pool w) at sub
  by_cases old : S ⊆ pool w
  · exact ⟨k,S,by omega,h,old⟩
  have needed : z ∈ S := by
    by_contra no
    exact old (fun v hv => (Finset.mem_insert.mp (sub hv)).resolve_left (fun e => no (e ▸ hv)))
  have fresh : z ∉ pool w := fun hz => old (fun v hv => (Finset.mem_insert.mp (sub hv)).elim (fun e => e ▸ hz) id)
  have nz : z ≠ 0 := nonzero h z needed
  have av := present w i
  have bv := present w j
  change norm a = 0 ∨ norm a ∈ pool w at av
  change norm b = 0 ∨ norm b ∈ pool w at bv
  have valid : ¬(norm a = 0 ∨ norm b = 0 ∨ norm a = norm b) := by
    intro bad
    obtain hz | hz | hz := degeneracy a b bad
    · exact nz hz
    · change z = norm a at hz
      exact av.elim (fun h => nz (hz.trans h)) (fun h => fresh (hz.symm ▸ h))
    · change z = norm b at hz
      exact bv.elim (fun h => nz (hz.trans h)) (fun h => fresh (hz.symm ▸ h))
  have ha : norm a ≠ 0 := fun e => valid (Or.inl e)
  have hb : norm b ≠ 0 := fun e => valid (Or.inr (Or.inl e))
  have ne : norm a ≠ norm b := fun e => valid (Or.inr (Or.inr e))
  have ra := av.resolve_left ha
  have rb := bv.resolve_left hb
  have rest : S.erase z ⊆ pool w := by
    intro v hv
    exact (Finset.mem_insert.mp (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
  have before : insert (norm a) (insert (norm b) (S.erase z)) ⊆ pool w :=
    Finset.insert_subset ra (Finset.insert_subset rb rest)
  have e : gate (a.getLsbD 0) (b.getLsbD 0) (norm a) (norm b) = z := gate_of a b
  refine ⟨k+1,_,le_rfl,Live.step (u:=a.getLsbD 0) (v:=b.getLsbD 0) ha hb ne ?_ ?_,before⟩
  · rw [e]
    exact fun h => fresh (before h)
  · rwa [e,Finset.insert_erase needed]

theorem extract {n} (p : List (Nat × Nat)) (w : List (Word n)) {T : Word n}
    (nz : T ≠ 0) (found : T ∈ pool (p.foldl add w)) :
    ∃ k S, k ≤ p.length ∧ Live T k S ∧ S ⊆ pool w := by
  induction p generalizing w with
  | nil => exact ⟨0,{T},by simp,Live.stop nz,Finset.singleton_subset_iff.mpr found⟩
  | cons ij ps ih =>
    obtain ⟨i,j⟩ := ij
    obtain ⟨k,S,le,run,sub⟩ := ih (add w (i,j)) found
    obtain ⟨k',S',bound,hr,hs⟩ := pull run w i j sub
    exact ⟨k',S',by simp; omega,hr,hs⟩

theorem flip_bits {n} (p : Bool) (a : Word n) {i j : Nat}
    (hi : i < n+1) (hj : j < n+1) (eq : a.getLsbD i = a.getLsbD j) :
    (flip p a).getLsbD i = (flip p a).getLsbD j := by
  cases p <;> simp only [flip,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_not,hi,hj,
    decide_true,Bool.true_and,eq]

theorem gate_bits {n} (p q : Bool) (a b : Word n) {i j : Nat}
    (hi : i < n+1) (hj : j < n+1)
    (ha : a.getLsbD i = a.getLsbD j) (hb : b.getLsbD i = b.getLsbD j) :
    (gate p q a b).getLsbD i = (gate p q a b).getLsbD j := by
  apply flip_bits _ _ hi hj
  simp only [BitVec.getLsbD_and,flip_bits p a hi hj ha,flip_bits q b hi hj hb]

theorem agree {n} {T : Word n} {k S} (h : Live T k S) {i j : Nat}
    (hi : i < n+1) (hj : j < n+1)
    (same : ∀ a ∈ S, a.getLsbD i = a.getLsbD j) :
    T.getLsbD i = T.getLsbD j := by
  induction h with
  | stop _ => exact same T (Finset.mem_singleton_self T)
  | @step k U a b p q _ _ _ _ tail ih =>
    simp only [Finset.forall_mem_insert] at same
    apply ih
    simp only [Finset.forall_mem_insert]
    exact ⟨gate_bits p q a b hi hj same.1 same.2.1,same.2.2⟩

def separated (m : Nat) (a : Word (m+m)) : BitVec m :=
  (a ^^^ (a >>> m)).setWidth m

def cover {m} : List (Word (m+m)) → BitVec m
  | [] => 0
  | a::xs => separated m a ||| cover xs

theorem separated_iff {m i : Nat} (a : Word (m+m)) (h : i<m) :
    (separated m a).getLsbD i = true ↔ a.getLsbD i ≠ a.getLsbD (i+m) := by
  simp only [separated,BitVec.getLsbD_setWidth,BitVec.getLsbD_xor,BitVec.getLsbD_ushiftRight,
    h,decide_true,Bool.true_and,Nat.add_comm m i]
  cases a.getLsbD i <;> cases a.getLsbD (i+m) <;> decide

theorem cover_bit {m i : Nat} (ws : List (Word (m+m))) :
    (cover ws).getLsbD i = true ↔ ∃ a ∈ ws, (separated m a).getLsbD i = true := by
  induction ws with
  | nil => simp [cover]
  | cons a ws ih => simp only [cover,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem coverage {m} {T : Word (m+m)} {k} {ws : List (Word (m+m))}
    (h : Live T k ws.toFinset) (ht : separated m T = BitVec.allOnes m) :
    cover ws = BitVec.allOnes m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_allOnes]
  simp only [hi,decide_true]
  apply (cover_bit ws).mpr
  by_contra! bad
  have ht' : (separated m T).getLsbD i = true := by rw [ht]; simp [hi]
  apply (separated_iff T hi).mp ht'
  apply agree h (by omega) (by omega)
  intro a ha
  by_contra ne
  have b := (separated_iff a hi).mpr ne
  have e := bad a (List.mem_toFinset.mp ha)
  simp [b] at e

theorem gate_comm {n} (u v : Bool) (a b : Word n) : gate u v a b = gate v u b a := by
  simp [gate,BitVec.and_comm]

def both (f : Bool → Bool) := f false && f true
theorem both_ok {f : Bool → Bool} (h : both f = true) (b : Bool) : f b = true := by
  simp only [both,Bool.and_eq_true] at h
  cases b <;> tauto

def rest {n} (ws : List (Word n)) (a b : Word n) (ka kb : Bool) :=
  ws.filter fun x => (ka || x != a) && (kb || x != b)

theorem rest_swap {n} (ws : List (Word n)) (a b : Word n) (ka kb : Bool) :
    rest ws a b ka kb = rest ws b a kb ka := by
  simp only [rest,Bool.and_comm]

def trial {n} (ws : List (Word n)) (f : List (Word n) → Bool) (a b : Word n) :=
  both fun u => both fun v =>
    let z := gate u v a b
    if z == 0 || ws.contains z then true else
      both fun ka => both fun kb => f (z :: rest ws a b ka kb)

def search (m : Nat) (T : Word (m+m)) : Nat → List (Word (m+m)) → Bool
  | 0, ws => !(ws.contains T)
  | k+1, ws =>
    if ws.length > k+2 then true else
    if cover ws != BitVec.allOnes m then true else
    !(ws.contains T) && ws.all fun a => ws.all fun b =>
      if a.toNat < b.toNat then trial ws (search m T k) a b else true

theorem trial_ok {n} {ws : List (Word n)} {f : List (Word n) → Bool} {a b}
    (h : trial ws f a b = true) (u v ka kb : Bool)
    (nz : gate u v a b ≠ 0) (fresh : gate u v a b ∉ ws) :
    f (gate u v a b :: rest ws a b ka kb) = true := by
  have e := both_ok (both_ok h u) v
  simp only [beq_eq_false_iff_ne.mpr nz,
    show ws.contains (gate u v a b) = false by simpa using fresh,
    Bool.false_or,Bool.false_eq_true,ite_false] at e
  exact both_ok (both_ok e ka) kb

theorem choose_trial {n} {ws : List (Word n)} {f : List (Word n) → Bool}
    (h : (ws.all fun a => ws.all fun b => if a.toNat < b.toNat then trial ws f a b else true) = true)
    {a b : Word n} (ha : a ∈ ws) (hb : b ∈ ws) (ab : a ≠ b) (u v ka kb : Bool)
    (nz : gate u v a b ≠ 0) (fresh : gate u v a b ∉ ws) :
    f (gate u v a b :: rest ws a b ka kb) = true := by
  have ne : a.toNat ≠ b.toNat := fun eq => ab (BitVec.eq_of_toNat_eq eq)
  rcases lt_or_gt_of_ne ne with lt | gt
  · have e := List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb
    exact trial_ok (by simpa only [lt,ite_true] using e) u v ka kb nz fresh
  · have e := List.all_eq_true.mp (List.all_eq_true.mp h b hb) a ha
    rw [gate_comm u v a b] at nz fresh ⊢
    rw [rest_swap ws a b ka kb]
    exact trial_ok (by simpa only [gt,ite_true] using e) v u kb ka nz fresh

theorem rest_set {n} {ws : List (Word n)} {a b : Word n} {U : Finset (Word n)}
    (e : ws.toFinset = insert a (insert b U)) :
    (rest ws a b (decide (a ∈ U)) (decide (b ∈ U))).toFinset = U := by
  ext x
  have member : x ∈ ws ↔ x = a ∨ x = b ∨ x ∈ U := by
    rw [←List.mem_toFinset,e]
    simp
  simp only [rest,List.mem_toFinset,List.mem_filter,Bool.and_eq_true,Bool.or_eq_true,
    decide_eq_true_eq,bne_iff_ne,member]
  by_cases aa : x = a <;> by_cases bb : x = b <;> simp_all

theorem search_sound {m} {T : Word (m+m)} (ht : separated m T = BitVec.allOnes m)
    (budget : Nat) (ws : List (Word (m+m))) (nd : ws.Nodup)
    (cert : search m T budget ws = true) {k} (le : k ≤ budget) : ¬Live T k ws.toFinset := by
  intro run
  induction budget generalizing ws k with
  | zero =>
    have eq : k=0 := by omega
    subst k
    have out : T ∉ ws := by simpa [search] using cert
    generalize he : ws.toFinset = S at run
    cases run with
    | stop => exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self T))
  | succ budget ih =>
    have sz := size run
    rw [List.toFinset_card_of_nodup nd] at sz
    have small : ¬ws.length > budget+2 := by omega
    have cv := coverage run ht
    have valid : ¬(cover ws != BitVec.allOnes m) = true := by simp [cv]
    simp only [search,small,ite_false,valid,Bool.false_eq_true,Bool.and_eq_true] at cert
    have out : T ∉ ws := by simpa using cert.1
    generalize he : ws.toFinset = S at run
    cases run with
    | stop => exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self T))
    | @step t U a b u v _ _ ab fresh tail =>
      have ha : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
      have hb : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have nx : gate u v a b ∉ ws := fun h => fresh (he ▸ List.mem_toFinset.mpr h)
      have nz := nonzero tail _ (Finset.mem_insert_self _ _)
      let ka := decide (a ∈ U)
      let kb := decide (b ∈ U)
      have child := choose_trial cert.2 ha hb ab u v ka kb nz nx
      have good : (gate u v a b :: rest ws a b ka kb).Nodup :=
        List.nodup_cons.mpr ⟨fun h => nx (List.mem_filter.mp h).1,nd.filter _⟩
      have eq : (gate u v a b :: rest ws a b ka kb).toFinset = insert (gate u v a b) U := by
        rw [List.toFinset_cons,rest_set he]
      exact ih _ good child (by omega) (eq.symm ▸ tail)

def roots {n} (raw : List (Word n)) : List (Word n) :=
  0 :: (~~~0) :: raw.flatMap fun a => [a,~~~a]

theorem root_pool {n} (raw : List (Word n)) :
    pool (roots raw) = insert 0 (raw.map norm).toFinset := by
  ext a
  simp only [pool,roots,List.map_cons,List.mem_toFinset,List.mem_cons,norm_neg,norm_zero,
    List.mem_map,List.mem_flatMap,List.mem_nil_iff,or_false,Finset.mem_insert]
  constructor
  · rintro (h | h | ⟨v,⟨w,hw,rfl | rfl⟩,rfl⟩)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr ⟨_,hw,rfl⟩
    · exact Or.inr ⟨_,hw,(norm_neg _).symm⟩
  · rintro (h | ⟨w,hw,rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨w,⟨w,hw,Or.inl rfl⟩,rfl⟩)

theorem cover_sup {m} {T : Word (m+m)} {k S} (h : Live T k S)
    (ht : separated m T = BitVec.allOnes m) (ws : List (Word (m+m))) (sub : S ⊆ ws.toFinset) :
    cover ws = BitVec.allOnes m := by
  have hl : Live T k S.toList.toFinset := by simpa using h
  have cv := coverage hl ht
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_allOnes]
  simp only [hi,decide_true]
  have full : (cover S.toList).getLsbD i = true := by rw [cv]; simp [hi]
  obtain ⟨w,hw,eq⟩ := (cover_bit _).mp full
  exact (cover_bit _).mpr ⟨w,List.mem_toFinset.mp (sub (Finset.mem_toList.mp hw)),eq⟩

def essential {m} (raw : List (Word (m+m))) :=
  raw.all fun a => cover (raw.erase a) != BitVec.allOnes m

theorem no_table {m} (T : Word (m+m)) (raw : List (Word (m+m))) (cap : Nat)
    (nz : T ≠ 0) (ht : separated m T = BitVec.allOnes m) (nd : (raw.map norm).Nodup)
    (needed : essential (raw.map norm) = true)
    (cert : search m T cap (raw.map norm) = true)
    (p : List (Nat × Nat)) (o : Nat) (short : p.length ≤ cap) :
    norm ((p.foldl add (roots raw)).getD o 0) ≠ T := by
  intro eq
  have seen := present (p.foldl add (roots raw)) o
  rw [eq] at seen
  obtain ⟨k,S,hk,run,sub⟩ := extract p (roots raw) nz (seen.resolve_left nz)
  rw [root_pool] at sub
  let ws := raw.map norm
  have within : S ⊆ ws.toFinset := fun a h => (Finset.mem_insert.mp (sub h)).resolve_left (nonzero run a h)
  have equality : S = ws.toFinset := by
    refine Finset.Subset.antisymm within ?_
    intro a ha
    by_contra absent
    have small : S ⊆ (ws.erase a).toFinset := by
      intro b hb
      have ne : b ≠ a := fun e => absent (e ▸ hb)
      exact List.mem_toFinset.mpr (nd.mem_erase_iff.mpr ⟨ne,List.mem_toFinset.mp (within hb)⟩)
    have cv := cover_sup run ht (ws.erase a) small
    have bad := List.all_eq_true.mp needed a (List.mem_toFinset.mp ha)
    change (cover (ws.erase a) != BitVec.allOnes m) = true at bad
    simp [cv] at bad
  exact search_sound ht cap ws nd cert (hk.trans short) (equality ▸ run)

def boolRoots (v : List Bool) := false :: true :: v.flatMap fun a => [a,!a]
def boolAdd (v : List Bool) (p : Nat × Nat) :=
  let z := v.getD p.1 false && v.getD p.2 false
  v ++ [z,!z]

def evalProgram (p : List (Nat × Nat)) (o : Nat) (v : List Bool) :=
  (p.foldl boolAdd (boolRoots v)).getD o false

def edgesBit {n} (raw : List (Word n)) : List (Nat × Nat) → Word n
  | [] => 0
  | (i,j)::es => (raw.getD i 0 &&& raw.getD j 0) ||| edgesBit raw es

def edgeTest (edges : List (Nat × Nat)) (raw : List Bool) :=
  edges.any fun ij => raw.getD ij.1 false && raw.getD ij.2 false

def read {n} (r : Fin (n+1)) (v : Word n) : Bool := v.getLsbD r.val

theorem read_neg {n} (r : Fin (n+1)) (a : Word n) :
    read r (~~~a) = !(read r a) := by simp [read,r.isLt]

theorem read_get {n} (r : Fin (n+1)) (ws : List (Word n)) (i : Nat) :
    read r (ws.getD i 0) = (ws.map (read r)).getD i false := by
  by_cases h : i < ws.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
    simp [read]

theorem read_roots {n} (r : Fin (n+1)) (ws : List (Word n)) :
    (roots ws).map (read r) = boolRoots (ws.map (read r)) := by
  simp only [roots,boolRoots,List.map_cons,read_neg,List.map_flatMap,List.flatMap_map,List.map_nil]
  simp [read]

theorem read_gate {n} (r : Fin (n+1)) (ws : List (Word n)) (ij : Nat × Nat) :
    (add ws ij).map (read r) = boolAdd (ws.map (read r)) ij := by
  simp only [add,boolAdd,List.map_append,List.map_cons,List.map_nil,read_neg]
  have bit (i j : Nat) := BitVec.getLsbD_and (x:=ws.getD i 0) (y:=ws.getD j 0) (i:=r.val)
  have e : read r (ws.getD ij.1 0 &&& ws.getD ij.2 0) =
      ((ws.map (read r)).getD ij.1 false && (ws.map (read r)).getD ij.2 false) :=
    (bit _ _).trans (congrArg₂ Bool.and (read_get r ws _) (read_get r ws _))
  rw [e]

theorem read_program {n} (r : Fin (n+1)) (p : List (Nat × Nat)) (ws : List (Word n)) :
    (p.foldl add ws).map (read r) = p.foldl boolAdd (ws.map (read r)) := by
  induction p generalizing ws with
  | nil => rfl
  | cons ij p ih => rw [List.foldl_cons,List.foldl_cons,ih,read_gate]

theorem edges_read {n} (r : Fin (n+1)) (raw : List (Word n)) (es : List (Nat × Nat)) :
    read r (edgesBit raw es) = edgeTest es (raw.map (read r)) := by
  induction es with
  | nil => simp [read,edgesBit,edgeTest]
  | cons ij es ih =>
    obtain ⟨i,j⟩ := ij
    change ((raw.getD i 0 &&& raw.getD j 0) ||| edgesBit raw es).getLsbD r.val = _
    simp only [BitVec.getLsbD_or,BitVec.getLsbD_and]
    change (read r (raw.getD i 0) && read r (raw.getD j 0) || read r (edgesBit raw es)) = _
    rw [read_get,read_get,ih]
    rfl

theorem counterexample {n} (raw : List (Word n)) (es : List (Nat × Nat))
    (p : List (Nat × Nat)) (o : Nat)
    (hn : norm ((p.foldl add (roots raw)).getD o 0) ≠ norm (edgesBit raw es)) :
    ∃ v : List Bool, v.length = raw.length ∧ evalProgram p o v ≠ edgeTest es v := by
  by_contra! no
  apply hn
  apply congrArg norm
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin (n+1) := ⟨i,hi⟩
  change read r ((p.foldl add (roots raw)).getD o 0) = read r (edgesBit raw es)
  rw [read_get,read_program,read_roots,edges_read]
  exact no _ (List.length_map ..)

end SignedLive

namespace SignedLive

theorem norm_flip {n} (u : Bool) (a : Word n) : norm (flip u a) = norm a := by
  cases u <;> simp [flip,norm_neg]

theorem small_gate {n} (a b : Word n) (u v : Bool) (ha : norm a = a) (hb : norm b = b)
    (small : a = 0 ∨ b = 0 ∨ a = b) :
    gate u v a b = 0 ∨ gate u v a b = a ∨ gate u v a b = b := by
  have d := degeneracy (flip u a) (flip v b)
  simpa only [gate,norm_flip,ha,hb] using d (by simpa only [norm_flip,ha,hb] using small)

theorem extend_back {n k} {T a b : Word n} {u v : Bool} {S W : Finset (Word n)}
    (h : Live T k S) (zero : 0 ∈ W) (aW : a ∈ W) (bW : b ∈ W)
    (na : norm a = a) (nb : norm b = b)
    (sub : S ⊆ insert (gate u v a b) W) :
    ∃ k' S', k' ≤ k + (if gate u v a b ∈ W then 0 else 1) ∧ Live T k' S' ∧ S' ⊆ W := by
  classical
  let z := gate u v a b
  change S ⊆ insert z W at sub
  by_cases old : S ⊆ W
  · exact ⟨k,S,Nat.le_add_right ..,h,old⟩
  have new : z ∉ W := fun hz => old (fun _ hh => (Finset.mem_insert.mp (sub hh)).elim (fun e => e ▸ hz) id)
  have used : z ∈ S := by
    by_contra absent
    exact old (fun _ hh => (Finset.mem_insert.mp (sub hh)).resolve_left (fun e => absent (e ▸ hh)))
  have big : ¬(a=0 ∨ b=0 ∨ a=b) := by
    intro small
    change gate u v a b ∉ W at new
    obtain hz | hz | hz := small_gate a b u v na nb small
    · exact new (hz.symm ▸ zero)
    · exact new (hz.symm ▸ aW)
    · exact new (hz.symm ▸ bW)
  have rem : S.erase z ⊆ W := fun _ hh =>
    (Finset.mem_insert.mp (sub (Finset.mem_erase.mp hh).2)).resolve_left (Finset.mem_erase.mp hh).1
  have before := Finset.insert_subset aW (Finset.insert_subset bW rem)
  refine ⟨k+1,_,by rw [if_neg (show gate u v a b ∉ W from new)],
    Live.step (u:=u) (v:=v) (fun eq => big (Or.inl eq)) (fun eq => big (Or.inr (Or.inl eq)))
      (fun eq => big (Or.inr (Or.inr eq))) (fun mem => new (before mem)) ?_,before⟩
  change Live T k (insert z (S.erase z))
  rwa [Finset.insert_erase used]

def zeros {n l} (P : Word n → Word l) (S : Finset (Word n)) := (S.filter fun x => P x = 0).card

theorem zeros_le {n l} (P : Word n → Word l) (a : Word n) (S : Finset (Word n)) :
    zeros P (insert a S) ≤ zeros P S + (if P a = 0 then 1 else 0) := by
  simp only [zeros,Finset.filter_insert]
  split <;> simp_all [Finset.card_insert_le]

theorem zeros_exact {n l} (P : Word n → Word l) (a : Word n) (S : Finset (Word n)) (h : a ∉ S) :
    zeros P (insert a S) = zeros P S + (if P a = 0 then 1 else 0) := by
  have hh : a ∉ S.filter (fun x => P x = 0) := fun mem => h (Finset.mem_filter.mp mem).1
  simp only [zeros,Finset.filter_insert]
  split <;> simp_all

theorem project_live {n l} (P : Word n → Word l)
    (pn : ∀ a, norm (P a) = P a)
    (pg : ∀ u v a b, ∃ r s, P (gate u v a b) = gate r s (P a) (P b))
    {T : Word n} {k S} (h : Live T k S) (nonconstant : P T ≠ 0) :
    ∃ j U, j + zeros P S ≤ k ∧ Live (P T) j U ∧ U ⊆ insert 0 (S.image P) := by
  classical
  induction h with
  | stop _ =>
    refine ⟨0,{P T},?_,Live.stop nonconstant,?_⟩
    · simpa [zeros] using nonconstant
    · simp
  | @step k U a b u v _ _ _ fresh tail ih =>
    let z := gate u v a b
    let W := insert (0 : Word l) ((insert a (insert b U)).image P)
    obtain ⟨j,V,count,run,sub⟩ := ih
    obtain ⟨r,s,eq⟩ := pg u v a b
    have aW : P a ∈ W := by simp [W]
    have bW : P b ∈ W := by simp [W]
    have zero : (0 : Word l) ∈ W := Finset.mem_insert_self _ _
    have na := pn a
    have nb := pn b
    have lifting : V ⊆ insert (gate r s (P a) (P b)) W := by
      intro x hx
      have h := sub hx
      simp only [Finset.image_insert,Finset.mem_insert] at h
      rcases h with rfl | hx | last
      · exact Finset.mem_insert_of_mem zero
      · exact Finset.mem_insert.mpr (Or.inl (hx.trans eq))
      · simp [W,Finset.mem_insert,last]
    obtain ⟨j',V',hi,hr,hV⟩ := extend_back run zero aW bW na nb lifting
    refine ⟨j',V',?_,hr,hV⟩
    have za := zeros_le P a (insert b U)
    have zb := zeros_le P b U
    have fz : z ∉ U := fun mem => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem))
    change j + zeros P (insert z U) ≤ k at count
    rw [zeros_exact P z U fz] at count
    change P z = gate r s (P a) (P b) at eq
    have known (small : P a = 0 ∨ P b = 0) : gate r s (P a) (P b) ∈ W := by
      obtain hg | hg | hg := small_gate (P a) (P b) r s na nb (small.elim Or.inl (Or.inr ∘ Or.inl))
      · exact hg.symm ▸ zero
      · exact hg.symm ▸ aW
      · exact hg.symm ▸ bW
    have bounded : (if gate r s (P a) (P b) ∈ W then 0 else 1) ≤ 1 := by split <;> decide
    by_cases aa : P a = 0 <;> by_cases bb : P b = 0
    · have z0 : P z = 0 := by
        rw [eq]
        obtain h | h | h := small_gate (P a) (P b) r s na nb (Or.inl aa)
        all_goals simp_all
      rw [if_pos aa] at za
      rw [if_pos bb] at zb
      rw [if_pos z0] at count
      rw [if_pos (known (Or.inl aa))] at hi
      omega
    · rw [if_pos aa] at za
      rw [if_neg bb] at zb
      rw [if_pos (known (Or.inl aa))] at hi
      split at count <;> omega
    · rw [if_neg aa] at za
      rw [if_pos bb] at zb
      rw [if_pos (known (Or.inr bb))] at hi
      split at count <;> omega
    · rw [if_neg aa] at za
      rw [if_neg bb] at zb
      split at count <;> omega

def crop (m s off : Nat) (a : Word (m+m)) : Word (s+s) :=
  let lo := (a >>> off).setWidth s
  let hi := (a >>> (m+off)).setWidth s
  let last := (a >>> off).setWidth 1
  (last ++ (hi ++ lo)).cast (by omega)

def source (m s off i : Nat) :=
  if i < s then off+i else if i < s+s then m+off+(i-s) else off

theorem crop_bit (m s off : Nat) (a : Word (m+m)) {i : Nat} (hi : i < s+s+1) :
    (crop m s off a).getLsbD i = a.getLsbD (source m s off i) := by
  simp only [crop,BitVec.getLsbD_cast,BitVec.getLsbD_append,BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight,source]
  by_cases small : i < s
  · have inside : i < s+s := by omega
    simp [small,inside]
  · by_cases inside : i < s+s
    · have width : i-s < s := by omega
      simp [small,inside,width]
    · have endBit : i-(s+s)=0 := by omega
      simp [small,inside,endBit]

theorem source_lt (m s off i : Nat) (good : off+s ≤ m) (hi : i < s+s+1) :
    source m s off i < m+m+1 := by unfold source; split <;> (first | omega | split <;> omega)

theorem crop_gate (m s off : Nat) (good : off+s ≤ m) (u v : Bool) (a b : Word (m+m)) :
    ∃ r t, norm (crop m s off (gate u v a b)) =
      gate r t (norm (crop m s off a)) (norm (crop m s off b)) := by
  let f := crop m s off
  have invert (w : Word (m+m)) : f (~~~w) = ~~~(f w) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    change (crop m s off (~~~w)).getLsbD i = _
    rw [crop_bit _ _ _ _ hi]
    simp only [BitVec.getLsbD_not,hi,source_lt m s off i good hi,decide_true,Bool.true_and]
    rw [show (f w).getLsbD i = w.getLsbD (source m s off i) from crop_bit _ _ _ _ hi]
  have conj (x y : Word (m+m)) : f (x &&& y) = f x &&& f y := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    change (crop m s off (x &&& y)).getLsbD i = _
    simp only [f,crop_bit _ _ _ _ hi,BitVec.getLsbD_and]
  have forget (x : Word (m+m)) : norm (f (norm x)) = norm (f x) := by
    change norm (f (flip (x.getLsbD 0) x)) = _
    cases x.getLsbD 0 <;> simp [flip,invert,norm_neg]
  have sign (x : Word (m+m)) (p : Bool) : f (flip p x) = flip p (f x) := by
    cases p <;> simp [flip,invert]
  have orient (x : Word (s+s)) (p : Bool) : ∃ r, flip r (norm x) = flip p x := by
    rcases norm_cases x with e | e
    · exact ⟨p,congrArg (flip p) e.symm⟩
    · refine ⟨!p,?_⟩
      cases p
      · simpa only [Bool.not_false,flip,ite_true,Bool.false_eq_true,ite_false] using e.symm
      · have h : ~~~x = norm x := (congrArg (fun y : Word (s+s) => ~~~y) e).trans BitVec.not_not
        simpa only [Bool.not_true,flip,ite_true,Bool.false_eq_true,ite_false] using h.symm
  obtain ⟨r,er⟩ := orient (f a) u
  obtain ⟨t,et⟩ := orient (f b) v
  refine ⟨r,t,?_⟩
  change norm (f (norm (flip u a &&& flip v b))) = norm (flip r (norm (f a)) &&& flip t (norm (f b)))
  rw [forget,conj,sign,sign,er,et]

def Lower {n} (T : Word n) (pool : List (Word n)) (limit : Nat) :=
  ∀ k S, Live T k S → S ⊆ insert 0 pool.toFinset → limit ≤ k

theorem lower_roots {m} {T : Word (m+m)} (ws : List (Word (m+m))) (bound : Nat)
    (ht : separated m T = BitVec.allOnes m) (nd : ws.Nodup) (ess : essential ws = true)
    (close : ∀ k ≤ bound, ¬Live T k ws.toFinset) : Lower T ws (bound+1) := by
  intro k S run sub
  by_contra! h
  have inside : S ⊆ ws.toFinset := fun a ha => (Finset.mem_insert.mp (sub ha)).resolve_left (nonzero run a ha)
  have eq : S = ws.toFinset := by
    apply Finset.Subset.antisymm inside
    intro a ha
    by_contra missing
    have smaller : S ⊆ (ws.erase a).toFinset := by
      intro b hb
      exact List.mem_toFinset.mpr (nd.mem_erase_iff.mpr
        ⟨fun e => missing (e ▸ hb),List.mem_toFinset.mp (inside hb)⟩)
    have full := cover_sup run ht (ws.erase a) smaller
    have bad := List.all_eq_true.mp ess a (List.mem_toFinset.mp ha)
    change (cover (ws.erase a) != BitVec.allOnes m) = true at bad
    simp [full] at bad
  exact close k (by omega) (eq ▸ run)

structure Slice (m : Nat) where
  width : Nat
  offset : Nat
  limit : Nat
  paid : Nat
  bank : List (Word (width+width))

def Slice.map {m} (c : Slice m) (a : Word (m+m)) := norm (crop m c.width c.offset a)

structure Valid {m} (T : Word (m+m)) (ws : List (Word (m+m))) (c : Slice m) : Prop where
  domain : c.offset+c.width ≤ m
  proper : c.map T ≠ 0
  holds : ∀ k S, Live (c.map T) k S → S ⊆ c.bank.toFinset → c.limit ≤ k+c.paid
  zero : 0 ∈ c.bank
  ready : ∀ a ∈ ws, c.map a ∈ c.bank

theorem start_slice {m s off lim} {T : Word (m+m)} {ws : List (Word (m+m))}
    (raw : List (Word (s+s))) (small : off+s ≤ m) (nz : norm (crop m s off T) ≠ 0)
    (low : Lower (norm (crop m s off T)) raw lim)
    (ready : ∀ a ∈ ws, norm (crop m s off a) ∈ 0::raw) :
    Valid T ws ⟨s,off,lim,0,0::raw⟩ := by
  refine ⟨small,nz,?_,by simp,ready⟩
  intro k S h sub
  exact low k S h (by simpa only [List.toFinset_cons] using sub)

def buy {m} (z : Word (m+m)) (c : Slice m) : Slice m :=
  let p := c.map z
  if c.bank.contains p then c else ⟨c.width,c.offset,c.limit,c.paid+1,p::c.bank⟩

theorem buy_valid {m} {T : Word (m+m)} {ws : List (Word (m+m))} {c : Slice m}
    (valid : Valid T ws c) {a b : Word (m+m)} (ha : a ∈ ws) (hb : b ∈ ws)
    (u v ka kb : Bool) :
    Valid T (gate u v a b :: rest ws a b ka kb) (buy (gate u v a b) c) := by
  let z := gate u v a b
  let p := c.map z
  have available : ∀ x ∈ rest ws a b ka kb, c.map x ∈ c.bank :=
    fun x hx => valid.ready x (List.mem_filter.mp hx).1
  change Valid T (z::rest ws a b ka kb) (if c.bank.contains p then c else
    ⟨c.width,c.offset,c.limit,c.paid+1,p::c.bank⟩)
  split
  next mem =>
    refine ⟨valid.domain,valid.proper,valid.holds,valid.zero,?_⟩
    exact List.forall_mem_cons.mpr ⟨by simpa using mem,available⟩
  next no =>
    refine ⟨valid.domain,valid.proper,?_,List.mem_cons_of_mem _ valid.zero,?_⟩
    · intro k S run sub
      obtain ⟨r,t,eq⟩ := crop_gate m c.width c.offset valid.domain u v a b
      change p = gate r t (c.map a) (c.map b) at eq
      change Live (c.map T) k S at run
      change S ⊆ (p::c.bank).toFinset at sub
      rw [List.toFinset_cons,eq] at sub
      obtain ⟨k',S',h,hr,hs⟩ := extend_back run (List.mem_toFinset.mpr valid.zero)
        (List.mem_toFinset.mpr (valid.ready a ha)) (List.mem_toFinset.mpr (valid.ready b hb))
        (norm_idem _) (norm_idem _) sub
      have base := valid.holds k' S' hr hs
      change c.limit ≤ k+(c.paid+1)
      split at h <;> omega
    · change ∀ x ∈ z::rest ws a b ka kb, c.map x ∈ p::c.bank
      exact List.forall_mem_cons.mpr ⟨List.mem_cons_self,fun x hx => List.mem_cons_of_mem _ (available x hx)⟩

def cut {m} (cap : Nat) (ws : List (Word (m+m))) (c : Slice m) :=
  decide (cap+c.paid < c.limit + ws.countP (fun a => c.map a == 0))

theorem cut_sound {m} {T : Word (m+m)} {ws : List (Word (m+m))} {c : Slice m}
    (valid : Valid T ws c) (nd : ws.Nodup) {k cap} (le : k ≤ cap) (hit : cut cap ws c = true) :
    ¬Live T k ws.toFinset := by
  intro run
  have pg (u v : Bool) (a b : Word (m+m)) : ∃ r s, c.map (gate u v a b) =
      gate r s (c.map a) (c.map b) := crop_gate m c.width c.offset valid.domain u v a b
  obtain ⟨j,U,size,small,sub⟩ := project_live c.map (fun _ => norm_idem _) pg run valid.proper
  have allowed : U ⊆ c.bank.toFinset := by
    intro x hx
    rcases Finset.mem_insert.mp (sub hx) with rfl | image
    · exact List.mem_toFinset.mpr valid.zero
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      exact List.mem_toFinset.mpr (valid.ready a (List.mem_toFinset.mp ha))
  have bound := valid.holds j U small allowed
  have countEq : zeros c.map ws.toFinset = ws.countP (fun a => c.map a == 0) := by
    let f := fun a : Word (m+m) => c.map a == 0
    have eq : (ws.toFinset.filter (fun a => c.map a = 0)) = (ws.filter f).toFinset := by
      ext a
      simp [f]
    rw [zeros,eq,List.toFinset_card_of_nodup (nd.filter f),List.countP_eq_length_filter]
  rw [countEq] at size
  have h := of_decide_eq_true hit
  change cap+c.paid < c.limit + ws.countP (fun a => c.map a == 0) at h
  omega

def checkWith (m : Nat) (T : Word (m+m)) : Nat → List (Word (m+m)) → List (Slice m) → Bool
  | 0,ws,_ => !(ws.contains T)
  | k+1,ws,cs =>
    if ws.length > k+2 then true else
    if cover ws != BitVec.allOnes m then true else
    if cs.any (cut (k+1) ws) then true else
    !(ws.contains T) && ws.all fun a => ws.all fun b =>
      if a.toNat < b.toNat then trial ws (fun child =>
        checkWith m T k child (cs.map (buy (child.headD 0)))) a b else true

theorem checkWith_sound {m} {T : Word (m+m)} (ht : separated m T = BitVec.allOnes m)
    (cap : Nat) (ws : List (Word (m+m))) (cs : List (Slice m))
    (nd : ws.Nodup) (ok : ∀ c ∈ cs, Valid T ws c)
    (cert : checkWith m T cap ws cs = true) {k} (le : k ≤ cap) : ¬Live T k ws.toFinset := by
  intro run
  induction cap generalizing ws k cs with
  | zero =>
    have eq : k=0 := by omega
    subst k
    have out : T ∉ ws := by simpa [checkWith] using cert
    generalize he : ws.toFinset = S at run
    cases run with
    | stop => exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self T))
  | succ cap ih =>
    by_cases hit : cs.any (cut (cap+1) ws) = true
    · obtain ⟨c,hc,p⟩ := List.any_eq_true.mp hit
      exact cut_sound (ok c hc) nd le p run
    have sz := size run
    rw [List.toFinset_card_of_nodup nd] at sz
    have small : ¬ws.length > cap+2 := by omega
    have cv := coverage run ht
    have valid : ¬(cover ws != BitVec.allOnes m) = true := by simp [cv]
    simp only [checkWith,small,ite_false,valid,hit,Bool.false_eq_true,Bool.and_eq_true] at cert
    have out : T ∉ ws := by simpa using cert.1
    generalize he : ws.toFinset = S at run
    cases run with
    | stop => exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self T))
    | @step t U a b u v _ _ ab fresh tail =>
      have ha : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
      have hb : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have nx : gate u v a b ∉ ws := fun h => fresh (he ▸ List.mem_toFinset.mpr h)
      have nz := nonzero tail _ (Finset.mem_insert_self _ _)
      let ka := decide (a ∈ U)
      let kb := decide (b ∈ U)
      have child := choose_trial cert.2 ha hb ab u v ka kb nz nx
      have good : (gate u v a b :: rest ws a b ka kb).Nodup :=
        List.nodup_cons.mpr ⟨fun h => nx (List.mem_filter.mp h).1,nd.filter _⟩
      have eq : (gate u v a b :: rest ws a b ka kb).toFinset = insert (gate u v a b) U := by
        rw [List.toFinset_cons,rest_set he]
      apply ih _ _ good _ child (by omega) (eq.symm ▸ tail)
      intro c hc
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      exact buy_valid (ok d hd) ha hb u v ka kb

def cell {m} (T : Word (m+m)) (k : Nat) (ws : List (Word (m+m))) (cs : List (Slice m))
    (i j : Nat) :=
  let a := ws.getD i 0
  let b := ws.getD j 0
  if a.toNat < b.toNat then trial ws (fun child => checkWith m T k child
    (cs.map (buy (child.headD 0)))) a b else true

theorem cells_ok {m} (T : Word (m+m)) (k : Nat) (ws : List (Word (m+m))) (cs : List (Slice m))
    (out : T ∉ ws) (h : ∀ i < ws.length, ∀ j < ws.length, cell T k ws cs i j = true) :
    checkWith m T (k+1) ws cs = true := by
  simp only [checkWith]
  split
  · rfl
  split
  · rfl
  split
  · rfl
  simp only [Bool.and_eq_true,List.all_eq_true]
  refine ⟨by simpa using out,?_⟩
  intro a ha b hb
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hb
  simpa only [cell,List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] using h i hi j hj

theorem flags_ok {m} (T : Word (m+m)) (k : Nat) (ws : List (Word (m+m))) (cs : List (Slice m))
    (i j : Nat)
    (h : ∀ u v ka kb : Bool, let a := ws.getD i 0; let b := ws.getD j 0; let z := gate u v a b
      z ≠ 0 → z ∉ ws → checkWith m T k (z :: rest ws a b ka kb) (cs.map (buy z)) = true) :
    cell T k ws cs i j = true := by
  unfold cell
  dsimp only
  split
  next less =>
    unfold trial
    have introBoth {f : Bool → Bool} (H : ∀ x, f x = true) : both f = true := by simp [both,H]
    apply introBoth
    intro u
    apply introBoth
    intro v
    dsimp only
    split
    · rfl
    next hn =>
      apply introBoth
      intro ka
      apply introBoth
      intro kb
      apply h u v ka kb
      · intro eq
        simp at hn
        exact hn.1 eq
      · intro mem
        simp at hn
        exact hn.2 mem
  · rfl

end SignedLive

namespace Graph235678
open SignedLive
def raw : List (Word (62+62)) := [0xc9f3def6bad9541e034b1a508361506,0x51e5ca3a8b607f45049425aa2c80850,0x2348210d4b6ab19000000eb12d00c04,0x4388008273514a8001c00648cd4520,0x8a9a35c771a5a3e00020e10c40960f8,0xf4040008149eca780001d000522b28a]
def tgt : Word (62+62) := 0xfffffffffffffffc000000000000000
def graphEdges : List (Nat × Nat) := [(0,1),(0,4),(1,5),(2,4),(2,5),(3,5)]
def cuts : List (Slice 62) := []
theorem geometry : ∀ c ∈ cuts, Valid tgt raw c := by
  simp [cuts]
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_5 : cell tgt 6 raw cuts 0 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch1_0 : cell tgt 6 raw cuts 1 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch1_4 : cell tgt 6 raw cuts 1 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch1_5 : cell tgt 6 raw cuts 1 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_0 : cell tgt 6 raw cuts 2 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_1 : cell tgt 6 raw cuts 2 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_4 : cell tgt 6 raw cuts 2 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_5 : cell tgt 6 raw cuts 2 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_0 : cell tgt 6 raw cuts 3 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_1 : cell tgt 6 raw cuts 3 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_2 : cell tgt 6 raw cuts 3 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_4 : cell tgt 6 raw cuts 3 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_5 : cell tgt 6 raw cuts 3 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_0 : cell tgt 6 raw cuts 4 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_5 : cell tgt 6 raw cuts 4 5 = true := by decide +kernel
set_option maxHeartbeats 3000000 in
theorem checked : checkWith 62 tgt 7 raw cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 6 at hi
  change j < 6 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch0_5
  · exact branch1_0
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch1_4
  · exact branch1_5
  · exact branch2_0
  · exact branch2_1
  · decide +kernel
  · decide +kernel
  · exact branch2_4
  · exact branch2_5
  · exact branch3_0
  · exact branch3_1
  · exact branch3_2
  · decide +kernel
  · exact branch3_4
  · exact branch3_5
  · exact branch4_0
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch4_5
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem bound : Lower tgt raw 8 := by
  have ht : separated 62 tgt = BitVec.allOnes 62 := by decide +kernel
  apply lower_roots raw 7 ht (by decide +kernel) (by decide +kernel)
  intro k hk; exact checkWith_sound ht 7 raw cuts (by decide +kernel) geometry checked hk
end Graph235678

namespace Graph125678
open SignedLive
def raw : List (Word (60+60)) := [0x36bfbb672bc7643160f19242b07202,0xa7aaac7ab1b0e9da0a0a64a90a0c8c,0x7a004080c307d6600008500e301d42,0x145513074e681f80000221344601f0,0xc18444b89c7c132000148b10c5c030,0x88680084549ba8c000250cc109a20c]
def tgt : Word (60+60) := 0xfffffffffffffff000000000000000
def graphEdges : List (Nat × Nat) := [(0,1),(0,3),(1,4),(2,4),(2,5),(3,5)]
def cuts : List (Slice 60) := []
theorem geometry : ∀ c ∈ cuts, Valid tgt raw c := by
  simp [cuts]
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_1 : cell tgt 6 raw cuts 0 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_2 : cell tgt 6 raw cuts 0 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_4 : cell tgt 6 raw cuts 0 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_5 : cell tgt 6 raw cuts 0 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch1_4 : cell tgt 6 raw cuts 1 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_1 : cell tgt 6 raw cuts 2 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_4 : cell tgt 6 raw cuts 2 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_5 : cell tgt 6 raw cuts 2 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_0 : cell tgt 6 raw cuts 3 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_1 : cell tgt 6 raw cuts 3 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_2 : cell tgt 6 raw cuts 3 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_4 : cell tgt 6 raw cuts 3 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_5 : cell tgt 6 raw cuts 3 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_1 : cell tgt 6 raw cuts 5 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_4 : cell tgt 6 raw cuts 5 4 = true := by decide +kernel
set_option maxHeartbeats 3000000 in
theorem checked : checkWith 60 tgt 7 raw cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 6 at hi
  change j < 6 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · exact branch0_1
  · exact branch0_2
  · decide +kernel
  · exact branch0_4
  · exact branch0_5
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch1_4
  · decide +kernel
  · decide +kernel
  · exact branch2_1
  · decide +kernel
  · decide +kernel
  · exact branch2_4
  · exact branch2_5
  · exact branch3_0
  · exact branch3_1
  · exact branch3_2
  · decide +kernel
  · exact branch3_4
  · exact branch3_5
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch5_1
  · decide +kernel
  · decide +kernel
  · exact branch5_4
  · decide +kernel
theorem bound : Lower tgt raw 8 := by
  have ht : separated 60 tgt = BitVec.allOnes 60 := by decide +kernel
  apply lower_roots raw 7 ht (by decide +kernel) (by decide +kernel)
  intro k hk; exact checkWith_sound ht 7 raw cuts (by decide +kernel) geometry checked hk
end Graph125678

namespace Graph135678
open SignedLive
def raw : List (Word (19+19)) := [0xe6a59c942,0x243630d6c0,0x8dec10348,0x13374a2688,0x4fd229ca4,0x3d01b00036]
def tgt : Word (19+19) := 0x3ffff80000
def graphEdges : List (Nat × Nat) := [(0,3),(1,5),(2,4),(2,5),(3,5)]
def cuts : List (Slice 19) := []
theorem geometry : ∀ c ∈ cuts, Valid tgt raw c := by
  simp [cuts]
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_1 : cell tgt 5 raw cuts 0 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_3 : cell tgt 5 raw cuts 0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_5 : cell tgt 5 raw cuts 0 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch1_5 : cell tgt 5 raw cuts 1 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_0 : cell tgt 5 raw cuts 2 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_1 : cell tgt 5 raw cuts 2 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_3 : cell tgt 5 raw cuts 2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_5 : cell tgt 5 raw cuts 2 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_1 : cell tgt 5 raw cuts 3 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_5 : cell tgt 5 raw cuts 3 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_0 : cell tgt 5 raw cuts 4 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_1 : cell tgt 5 raw cuts 4 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_2 : cell tgt 5 raw cuts 4 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_3 : cell tgt 5 raw cuts 4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_5 : cell tgt 5 raw cuts 4 5 = true := by decide +kernel
set_option maxHeartbeats 3000000 in
theorem checked : checkWith 19 tgt 6 raw cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 6 at hi
  change j < 6 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · exact branch0_1
  · decide +kernel
  · exact branch0_3
  · decide +kernel
  · exact branch0_5
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch1_5
  · exact branch2_0
  · exact branch2_1
  · decide +kernel
  · exact branch2_3
  · decide +kernel
  · exact branch2_5
  · decide +kernel
  · exact branch3_1
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch3_5
  · exact branch4_0
  · exact branch4_1
  · exact branch4_2
  · exact branch4_3
  · decide +kernel
  · exact branch4_5
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
theorem bound : Lower tgt raw 7 := by
  have ht : separated 19 tgt = BitVec.allOnes 19 := by decide +kernel
  apply lower_roots raw 6 ht (by decide +kernel) (by decide +kernel)
  intro k hk; exact checkWith_sound ht 6 raw cuts (by decide +kernel) geometry checked hk
end Graph135678

namespace Graph1234578
open SignedLive
def raw : List (Word (85+85)) := [0x109955221506513acf898a8440085880b209c654444,0x3b9b5da3f749f21f157522509ae1072a449038a9a90,0x2e14a25ca202cdc07ac2dc00051420100264035216e,0xcaa4c0401a46ca9b9c0000002d0090d03640dc80,0x1861800008bc00abb2f9bc0001800381c00455974d8,0x322488148db62644a0e5c00000628541b030240126,0x4c2061000a78995c5362000000984463c08a828a00]
def tgt : Word (85+85) := 0x3ffffffffffffffffffffe000000000000000000000
def graphEdges : List (Nat × Nat) := [(0,1),(1,2),(1,5),(2,3),(2,6),(4,5),(4,6)]
def cuts : List (Slice 85) := []
theorem geometry : ∀ c ∈ cuts, Valid tgt raw c := by
  simp [cuts]
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_1 : cell tgt 7 raw cuts 0 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_2 : cell tgt 7 raw cuts 0 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_4 : cell tgt 7 raw cuts 0 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_1 : cell tgt 7 raw cuts 2 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_0 : cell tgt 7 raw cuts 3 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_1 : cell tgt 7 raw cuts 3 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_2 : cell tgt 7 raw cuts 3 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_4 : cell tgt 7 raw cuts 3 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_5 : cell tgt 7 raw cuts 3 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_6 : cell tgt 7 raw cuts 3 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_1 : cell tgt 7 raw cuts 4 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_2 : cell tgt 7 raw cuts 4 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_0 : cell tgt 7 raw cuts 5 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_1 : cell tgt 7 raw cuts 5 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_2 : cell tgt 7 raw cuts 5 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_4 : cell tgt 7 raw cuts 5 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_6 : cell tgt 7 raw cuts 5 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_0 : cell tgt 7 raw cuts 6 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_1 : cell tgt 7 raw cuts 6 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_2 : cell tgt 7 raw cuts 6 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_4 : cell tgt 7 raw cuts 6 4 = true := by decide +kernel
set_option maxHeartbeats 3000000 in
theorem checked : checkWith 85 tgt 8 raw cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 7 at hi
  change j < 7 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · exact branch0_1
  · exact branch0_2
  · decide +kernel
  · exact branch0_4
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch2_1
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch3_0
  · exact branch3_1
  · exact branch3_2
  · decide +kernel
  · exact branch3_4
  · exact branch3_5
  · exact branch3_6
  · decide +kernel
  · exact branch4_1
  · exact branch4_2
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch5_0
  · exact branch5_1
  · exact branch5_2
  · decide +kernel
  · exact branch5_4
  · decide +kernel
  · exact branch5_6
  · exact branch6_0
  · exact branch6_1
  · exact branch6_2
  · decide +kernel
  · exact branch6_4
  · decide +kernel
  · decide +kernel
theorem bound : Lower tgt raw 9 := by
  have ht : separated 85 tgt = BitVec.allOnes 85 := by decide +kernel
  apply lower_roots raw 8 ht (by decide +kernel) (by decide +kernel)
  intro k hk; exact checkWith_sound ht 8 raw cuts (by decide +kernel) geometry checked hk
end Graph1234578

namespace Graph1235678
open SignedLive
def raw : List (Word (369+369)) := [0x8dec64f9ef7b5d6caa0e087100104e6a29528f2e51d45b03fa26d7f76ce578ec867352c000000000000000bab50a40d22034b1a5083615060007001923351481049425aa2c80850160f19242b0720239284000000000000000554a80,0x3d01b454d1ae3b8d2d1f1e8080010293d94f7a0200040a4f653d4f5558f56361d3a0000327cf7bdaeb65507d40bfe000d80020e10c40960f800007400148aca280001d000522b28aa0a0a64a90a0c8c0000101a58d2841b0a8328053e,0x2436311a41086a5b558c84690421a96d563211a41086a5b558c800000000000000121b19479728ea2d81fd125fc0035b0000000eb12d00c04000003ac4b40301000000eb12d00c040000000000000001ad80824a12d5164042812d800,0xe6a5821c4004139a8a5593e7bded75b2a838000000000000000f4008101860facc46f608d2084352daac6417985072508001c00648cd452080d2c69420d8541800000000000000000008500e301d42206900000075896806020a4c20,0x4fd228f2e51d45b03fa200000000000000064f9ef7b5d6caa0e28aa260e9cd03f099ba410e200209cd452a4d3a04a7291049425aa2c808500000000000000002034b1a5083615060000221344601f044d10000e0032466a290229500,0x133748000000000000000a3cb947516c0fe8821c4004139a8a558308897138f826427e922a68d71dc6968f86be0a089a200000000000000004125096a8b202140001c00648cd4520000148b10c5c0305394800107086204b07c15b040,0x7a0200040a4f653d15346b8ee34b47c454d1ae3b8d2d1f110d00108a937519e80dbd0100020527b29e2047fc000000001d000522b28a00083843102583e00020e10c40960f8000250cc109a20c0006c0000e80029159454022de]
def tgt : Word (369+369) := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def graphEdges : List (Nat × Nat) := [(0,1),(0,4),(1,2),(1,5),(2,6),(3,5),(3,6),(4,6)]
def slice0 : Slice 369 := ⟨62,23,8,0,0::Graph235678.raw⟩
def slice1 : Slice 369 := ⟨19,85,7,0,0::Graph135678.raw⟩
def slice2 : Slice 369 := ⟨60,104,8,0,0::Graph125678.raw⟩
def slice3 : Slice 369 := ⟨62,164,8,0,0::Graph235678.raw⟩
def slice4 : Slice 369 := ⟨62,226,8,0,0::Graph235678.raw⟩
def slice5 : Slice 369 := ⟨62,288,8,0,0::Graph235678.raw⟩
def slice6 : Slice 369 := ⟨19,350,7,0,0::Graph135678.raw⟩
def cuts : List (Slice 369) := [slice0,slice1,slice2,slice3,slice4,slice5,slice6]
theorem valid0 : Valid tgt raw slice0 := by
  have target : norm (crop 369 62 23 tgt) = Graph235678.tgt := by decide +kernel
  apply start_slice Graph235678.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph235678.bound
  · have test : (raw.all fun a => (0::Graph235678.raw).contains (norm (crop 369 62 23 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid1 : Valid tgt raw slice1 := by
  have target : norm (crop 369 19 85 tgt) = Graph135678.tgt := by decide +kernel
  apply start_slice Graph135678.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph135678.bound
  · have test : (raw.all fun a => (0::Graph135678.raw).contains (norm (crop 369 19 85 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid2 : Valid tgt raw slice2 := by
  have target : norm (crop 369 60 104 tgt) = Graph125678.tgt := by decide +kernel
  apply start_slice Graph125678.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph125678.bound
  · have test : (raw.all fun a => (0::Graph125678.raw).contains (norm (crop 369 60 104 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid3 : Valid tgt raw slice3 := by
  have target : norm (crop 369 62 164 tgt) = Graph235678.tgt := by decide +kernel
  apply start_slice Graph235678.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph235678.bound
  · have test : (raw.all fun a => (0::Graph235678.raw).contains (norm (crop 369 62 164 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid4 : Valid tgt raw slice4 := by
  have target : norm (crop 369 62 226 tgt) = Graph235678.tgt := by decide +kernel
  apply start_slice Graph235678.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph235678.bound
  · have test : (raw.all fun a => (0::Graph235678.raw).contains (norm (crop 369 62 226 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid5 : Valid tgt raw slice5 := by
  have target : norm (crop 369 62 288 tgt) = Graph235678.tgt := by decide +kernel
  apply start_slice Graph235678.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph235678.bound
  · have test : (raw.all fun a => (0::Graph235678.raw).contains (norm (crop 369 62 288 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid6 : Valid tgt raw slice6 := by
  have target : norm (crop 369 19 350 tgt) = Graph135678.tgt := by decide +kernel
  apply start_slice Graph135678.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph135678.bound
  · have test : (raw.all fun a => (0::Graph135678.raw).contains (norm (crop 369 19 350 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem geometry : ∀ c ∈ cuts, Valid tgt raw c := by
  intro c h
  simp only [cuts,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4
  · exact valid5
  · exact valid6
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_1 : cell tgt 8 raw cuts 0 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_2 : cell tgt 8 raw cuts 0 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_3 : cell tgt 8 raw cuts 0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_5 : cell tgt 8 raw cuts 0 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch2_1 : cell tgt 8 raw cuts 2 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_1 : cell tgt 8 raw cuts 3 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_2 : cell tgt 8 raw cuts 3 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_5 : cell tgt 8 raw cuts 3 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_0 : cell tgt 8 raw cuts 4 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_1 : cell tgt 8 raw cuts 4 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_2 : cell tgt 8 raw cuts 4 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_3 : cell tgt 8 raw cuts 4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_5 : cell tgt 8 raw cuts 4 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_1 : cell tgt 8 raw cuts 5 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_2 : cell tgt 8 raw cuts 5 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_0 : cell tgt 8 raw cuts 6 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_1 : cell tgt 8 raw cuts 6 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_2 : cell tgt 8 raw cuts 6 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_3 : cell tgt 8 raw cuts 6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_4 : cell tgt 8 raw cuts 6 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_5 : cell tgt 8 raw cuts 6 5 = true := by decide +kernel
set_option maxHeartbeats 3000000 in
theorem checked : checkWith 369 tgt 9 raw cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 7 at hi
  change j < 7 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · exact branch0_1
  · exact branch0_2
  · exact branch0_3
  · decide +kernel
  · exact branch0_5
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch2_1
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch3_1
  · exact branch3_2
  · decide +kernel
  · decide +kernel
  · exact branch3_5
  · decide +kernel
  · exact branch4_0
  · exact branch4_1
  · exact branch4_2
  · exact branch4_3
  · decide +kernel
  · exact branch4_5
  · decide +kernel
  · decide +kernel
  · exact branch5_1
  · exact branch5_2
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch6_0
  · exact branch6_1
  · exact branch6_2
  · exact branch6_3
  · exact branch6_4
  · exact branch6_5
  · decide +kernel
theorem bound : Lower tgt raw 10 := by
  have ht : separated 369 tgt = BitVec.allOnes 369 := by decide +kernel
  apply lower_roots raw 9 ht (by decide +kernel) (by decide +kernel)
  intro k hk; exact checkWith_sound ht 9 raw cuts (by decide +kernel) geometry checked hk
end Graph1235678

namespace Graph01234578
open SignedLive
def raw : List (Word (1897+1897)) := [0x7a0200040a4f653d15346b8ee34b47c454d1ae3b8d2d1f110d00108a937519e80dbd0100020527b29e2047fde80da2a68d71dc6968f8f4040008149eca7bd0100020527b29ea7aaac7ab1b0e9d0000193e7bded75b2a83ea05ff6186000022f002aecbe6f11bd8c9f3def6bad9541c10e200209cd452a51e5ca3a8b607f44dafeed9caf1d90ce6a58000000000000001756a17b9b5da3f749f21f157523dcdaed1fba4f90f8aba91237b193e7bded75b2a83821c4004139a8a54a3cb947516c0fe89b5fddb395e3b219cd4b0000000000000002ead4280000000000000000000023f643041648ab4539f86000000001d000522b28a00083843102583e00020e10c40960f8000250cc109a20c0006c0000e80029159454022de0006c00107086204b07c00003a000a4565140000e80029159455050532548506460000080d2c69420d854194029f00006000e070011565d36081a44069634a106c2a0c000e0032466a290209284b5459010a02c1e3248560e40472508000000000000000aa9500509ae1072a449038a9a90284d70839522481c54d481034880d2c69420d85418001c00648cd45204125096a8b202140583c6490ac1c808e4a10000000000000001552a000000000000000000000000780d000220dda298a82,0x2436311a41086a5b558c84690421a96d563211a41086a5b558c800000000000000121b19479728ea2d81fd125fc0046f6327cf7bdaeb6550704388008273514a9479728ea2d81fd136bfbb672bc764339a960000000000000005d5a850c892205236d89912839709fa451e5ca3a8b607f44000000000000000c9f3def6bad9541c51544c1d39a07e13374821c4004139a8a549a7408322488148db62644a0e5c84caa910a83289d67c4c5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002132aa442a0ca2759f1314730c049173c0c668684235b0000000eb12d00c04000003ac4b40301000000eb12d00c040000000000000001ad80824a12d5164042812d8002069101a58d2841b0a830003800c919a8a40824a12d516404280b078c9215839011c9420000000000000002aa5400000018a1506c0c09004994e52209284b5459010a00000000000000004069634a106c2a0c0000442688c03e089a20001c00648cd4520452a0000000628541b0302401264220042c405904e32a222000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001088010b10164138ca888838060248996020103420,0x3d01b454d1ae3b8d2d1f1e8080010293d94f7a0200040a4f653d4f5558f56361d3a0000327cf7bdaeb65507d40bfe27e91479728ea2d81fd1000000000000000327cf7bdaeb65507145513074e681f84cdd2087100104e6a295269d02ee6d768fdd27c87c55d4880000f4040008149eca7a2a68d71dc6968f88a9a35c771a5a3e221a00211526ea33d01b7a0200040a4f653c408ff9861800008bc00abb2f9bc00000000000000000000039a96087100104e6a29564f9ef7b5d6caa0e0000000000000003d0020406183eb311bd82348210d4b6ab1905e6147736bb47ee93e43e2aea4564b882301b12829d33bc000d80020e10c40960f800007400148aca280001d000522b28aa0a0a64a90a0c8c0000101a58d2841b0a8328053e53948824a12d51640428000000000000000101a58d2841b0a8300001109a2300f822688000700192335148114a801426b841ca91240e2a6a40000000003a000a45651400107086204b07c00041c218812c1f00004a1982134418000d80001d000522b28a8045bc0001800381c00455974d80000000000000000000001c9420007001923351482034b1a5083615060000000000000000000214038c0750881a4000001d625a01808293080a135c20e548920715352000182810049d414e8958,0x8dec64f9ef7b5d6caa0e087100104e6a29528f2e51d45b03fa26d7f76ce578ec867352c000000000000000bab50a00003d0100020527b29e8a9a35c771a5a3e22a68d71dc6968f888680084549ba8cf406de8080010293d94f1023feb8528972880b3701eb0b71cd4b04388008273514ab27cf7bdaeb655070000000000000001e80102030c1f5988dec11a41086a5b558c82f30a0000000000000000000000c30c000045e0055d97cde00001e8080010293d94f454d1ae3b8d2d1f115346b8ee34b47c443400422a4dd467a036f4040008149eca78811ff5c2944b944059b80f585b991d108860a417d22dd6840d22034b1a5083615060007001923351481049425aa2c80850160f19242b0720239284000000000000000554a80000000000e800291594500041c218812c1f000107086204b07c00012866084d1060003600007400148aca2a0116f0001450804009900d485b8e4a10003800c919a8a4101a58d2841b0a83000000000000000000010a01c603a8440d2000000eb12d00c041498400000000000000000000000000c001c0e0022acba6c0000000007400148aca280020e10c40960f800083843102583e0000943304268830001b00003a000a456515008b78000a28402004c806a42dc006504008122beb16484,0x4fd228f2e51d45b03fa200000000000000064f9ef7b5d6caa0e28aa260e9cd03f099ba410e200209cd452a4d3a0521b188d2084352daac642348210d4b6ab1908d2084352daac6400000000000000090d8ca3cb947516c0fe892fe0013081840029e265714d8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000109955221506513acf898a1912440a46db13225072e13f48a3cb947516c0fe8800000000000000193e7bded75b2a838a2a8983a7340fc266e904388008273514a934e8100195498080348d95373808c00364609ca29842250a7291049425aa2c808500000000000000002034b1a5083615060000221344601f044d10000e0032466a2902295001ad80000007589680602000001d625a018080000075896806020000000000000000d6c04125096a8b20214096c0000000261118f022a0a2800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008440085880b209c654444000003142a0d81812009329ca44125096a8b20214000000000000000080d2c69420d854180000884d11807c113440003800c919a8a408a5400000005a0121a06c81b90040000b2304c000421128,0xe6a5821c4004139a8a5593e7bded75b2a838000000000000000f4008101860facc46f608d2084352daac6417985099ba400000000000000051e5ca3a8b607f4410e200209cd452ac18444b89c7c13213f4915346b8ee34b47c35f0500000000000000000000007a0368a9a35c771a5a3e3d0100020527b29ef4040008149eca7a9eaab1eac6c3a74000064f9ef7b5d6caa0fa817fee14a25ca202cdc07ac2dd70a512e510166e03d616ef406d15346b8ee34b47c7a0200040a4f653de8080010293d94f53d5563d58d874e80000c9f3def6bad9541f502ffb0c300001178015765f37aca02450884a44aa7e0f872508001c00648cd452080d2c69420d8541800000000000000000008500e301d42206900000075896806020a4c2044d10000000000000000209284b5459010a0000e0032466a2900000a458862e01829ca400083843102583e0ad8200000000000000000000000001b00041c218812c1f00000e800291594500003a000a45651541414c95214191800002034b1a508361506500a7c00051420100264035216e00028a1008013201a90b70003600083843102583e00001d000522b28a00007400148aca2a8282992a428323000004069634a106c2a0ca014f800030007038008ab2e9b000020005485225d65074,0x133748000000000000000a3cb947516c0fe8821c4004139a8a558308897138f826427e922a68d71dc6968f86be0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000042655488541944eb3e262c86c62348210d4b6ab1908d2084352daac642348210d4b6ab190000000000000002436328f2e51d45b03fa24bf8004c2061000a78995c5362000655260200d23654dce04cdd200000000000000028f2e51d45b03fa2087100104e6a29560c2225c4e3e09909fa48a9a35c771a5a3e1af8280644910291b6c4c8941cb8003283e8061434b04c0489a200000000000000004125096a8b202140001c00648cd4520000148b10c5c0305394800107086204b07c15b0400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021100216202c82719511106b60000001d625a01808000007589680602000001d625a0180800000000000000035b01049425aa2c8085025b00000000984463c08a828a0000000168048681b206e40226880000000000000001049425aa2c808500007001923351480000522c431700c14e5200041c218812c1f056c10000000c50a83606048024c000001e003001a002602,0x7352c10e200209cd452ac9f3def6bad9541c0000000000000007a004080c307d66237b04690421a96d56320bcc280032a930100691b2a6e70266e90000000000000001479728ea2d81fd104388008273514ab061112e271f04c84fd2454d1ae3b8d2d1f0d7c14000caa4c0401a46ca9b9c026103080053c4cae29b1090d8c4690421a96d563211a41086a5b558c84690421a96d5632000000000000000486c651e5ca3a8b607f4497f0009840c20014f132b8a6c4000c14ec08c23d01406140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000039284000e0032466a2904069634a106c2a0c000000000000000000042807180ea110348000003ac4b40301052610000000b4024340d903720113440000000000000000824a12d516404280003800c919a8a400002916218b8060a72900020e10c40960f82b6080000002d0090d03640dc80000004c2231e0454145000d6c0000003ac4b40301000000eb12d00c04000003ac4b4030100000000000000006b60209284b5459010a04b6000000013088c781150514000000036006014008030a]
def tgt : Word (1897+1897) := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def graphEdges : List (Nat × Nat) := [(0,1),(0,4),(0,5),(1,2),(2,3),(2,6),(3,4),(3,7),(5,6),(5,7)]
def slice0 : Slice 1897 := ⟨85,81,9,0,0::Graph1234578.raw⟩
def slice1 : Slice 1897 := ⟨369,166,10,0,0::Graph1235678.raw⟩
def slice2 : Slice 1897 := ⟨85,535,9,0,0::Graph1234578.raw⟩
def slice3 : Slice 1897 := ⟨85,620,9,0,0::Graph1234578.raw⟩
def slice4 : Slice 1897 := ⟨369,705,10,0,0::Graph1235678.raw⟩
def slice5 : Slice 1897 := ⟨85,1074,9,0,0::Graph1234578.raw⟩
def slice6 : Slice 1897 := ⟨369,1159,10,0,0::Graph1235678.raw⟩
def slice7 : Slice 1897 := ⟨369,1528,10,0,0::Graph1235678.raw⟩
def cuts : List (Slice 1897) := [slice0,slice1,slice2,slice3,slice4,slice5,slice6,slice7]
theorem valid0 : Valid tgt raw slice0 := by
  have target : norm (crop 1897 85 81 tgt) = Graph1234578.tgt := by decide +kernel
  apply start_slice Graph1234578.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph1234578.bound
  · have test : (raw.all fun a => (0::Graph1234578.raw).contains (norm (crop 1897 85 81 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid1 : Valid tgt raw slice1 := by
  have target : norm (crop 1897 369 166 tgt) = Graph1235678.tgt := by decide +kernel
  apply start_slice Graph1235678.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph1235678.bound
  · have test : (raw.all fun a => (0::Graph1235678.raw).contains (norm (crop 1897 369 166 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid2 : Valid tgt raw slice2 := by
  have target : norm (crop 1897 85 535 tgt) = Graph1234578.tgt := by decide +kernel
  apply start_slice Graph1234578.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph1234578.bound
  · have test : (raw.all fun a => (0::Graph1234578.raw).contains (norm (crop 1897 85 535 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid3 : Valid tgt raw slice3 := by
  have target : norm (crop 1897 85 620 tgt) = Graph1234578.tgt := by decide +kernel
  apply start_slice Graph1234578.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph1234578.bound
  · have test : (raw.all fun a => (0::Graph1234578.raw).contains (norm (crop 1897 85 620 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid4 : Valid tgt raw slice4 := by
  have target : norm (crop 1897 369 705 tgt) = Graph1235678.tgt := by decide +kernel
  apply start_slice Graph1235678.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph1235678.bound
  · have test : (raw.all fun a => (0::Graph1235678.raw).contains (norm (crop 1897 369 705 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid5 : Valid tgt raw slice5 := by
  have target : norm (crop 1897 85 1074 tgt) = Graph1234578.tgt := by decide +kernel
  apply start_slice Graph1234578.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph1234578.bound
  · have test : (raw.all fun a => (0::Graph1234578.raw).contains (norm (crop 1897 85 1074 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid6 : Valid tgt raw slice6 := by
  have target : norm (crop 1897 369 1159 tgt) = Graph1235678.tgt := by decide +kernel
  apply start_slice Graph1235678.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph1235678.bound
  · have test : (raw.all fun a => (0::Graph1235678.raw).contains (norm (crop 1897 369 1159 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem valid7 : Valid tgt raw slice7 := by
  have target : norm (crop 1897 369 1528 tgt) = Graph1235678.tgt := by decide +kernel
  apply start_slice Graph1235678.raw (by decide) (by rw [target]; decide +kernel)
  · rw [target]; exact Graph1235678.bound
  · have test : (raw.all fun a => (0::Graph1235678.raw).contains (norm (crop 1897 369 1528 a))) = true := by decide +kernel
    intro a h; simpa using List.all_eq_true.mp test a h
theorem geometry : ∀ c ∈ cuts, Valid tgt raw c := by
  intro c h
  simp only [cuts,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4
  · exact valid5
  · exact valid6
  · exact valid7
def first0_2Wire := gate true true (raw.getD 0 0) (raw.getD 2 0)
def first0_2Pool := first0_2Wire :: rest raw (raw.getD 0 0) (raw.getD 2 0) true true
def first0_2Cuts := cuts.map (buy first0_2Wire)
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell1_0 : cell tgt 9 first0_2Pool first0_2Cuts 1 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell1_2 : cell tgt 9 first0_2Pool first0_2Cuts 1 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell1_3 : cell tgt 9 first0_2Pool first0_2Cuts 1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell1_4 : cell tgt 9 first0_2Pool first0_2Cuts 1 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell1_5 : cell tgt 9 first0_2Pool first0_2Cuts 1 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell1_6 : cell tgt 9 first0_2Pool first0_2Cuts 1 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell1_7 : cell tgt 9 first0_2Pool first0_2Cuts 1 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell2_0 : cell tgt 9 first0_2Pool first0_2Cuts 2 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell2_3 : cell tgt 9 first0_2Pool first0_2Cuts 2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell3_0 : cell tgt 9 first0_2Pool first0_2Cuts 3 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell4_0 : cell tgt 9 first0_2Pool first0_2Cuts 4 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell4_2 : cell tgt 9 first0_2Pool first0_2Cuts 4 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell4_3 : cell tgt 9 first0_2Pool first0_2Cuts 4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell4_6 : cell tgt 9 first0_2Pool first0_2Cuts 4 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell4_7 : cell tgt 9 first0_2Pool first0_2Cuts 4 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell5_0 : cell tgt 9 first0_2Pool first0_2Cuts 5 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell5_2 : cell tgt 9 first0_2Pool first0_2Cuts 5 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell5_3 : cell tgt 9 first0_2Pool first0_2Cuts 5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell5_4 : cell tgt 9 first0_2Pool first0_2Cuts 5 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell5_6 : cell tgt 9 first0_2Pool first0_2Cuts 5 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell5_7 : cell tgt 9 first0_2Pool first0_2Cuts 5 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell6_0 : cell tgt 9 first0_2Pool first0_2Cuts 6 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell6_2 : cell tgt 9 first0_2Pool first0_2Cuts 6 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell6_3 : cell tgt 9 first0_2Pool first0_2Cuts 6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell6_7 : cell tgt 9 first0_2Pool first0_2Cuts 6 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell7_0 : cell tgt 9 first0_2Pool first0_2Cuts 7 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell7_2 : cell tgt 9 first0_2Pool first0_2Cuts 7 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell7_3 : cell tgt 9 first0_2Pool first0_2Cuts 7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell8_0 : cell tgt 9 first0_2Pool first0_2Cuts 8 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell8_1 : cell tgt 9 first0_2Pool first0_2Cuts 8 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell8_2 : cell tgt 9 first0_2Pool first0_2Cuts 8 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell8_3 : cell tgt 9 first0_2Pool first0_2Cuts 8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell8_4 : cell tgt 9 first0_2Pool first0_2Cuts 8 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell8_5 : cell tgt 9 first0_2Pool first0_2Cuts 8 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell8_6 : cell tgt 9 first0_2Pool first0_2Cuts 8 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_2cell8_7 : cell tgt 9 first0_2Pool first0_2Cuts 8 7 = true := by decide +kernel
set_option maxHeartbeats 3500000 in
theorem first0_2checked : checkWith 1897 tgt 10 first0_2Pool first0_2Cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 9 at hi
  change j < 9 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_2cell1_0
  · decide +kernel
  · exact first0_2cell1_2
  · exact first0_2cell1_3
  · exact first0_2cell1_4
  · exact first0_2cell1_5
  · exact first0_2cell1_6
  · exact first0_2cell1_7
  · decide +kernel
  · exact first0_2cell2_0
  · decide +kernel
  · decide +kernel
  · exact first0_2cell2_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_2cell3_0
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_2cell4_0
  · decide +kernel
  · exact first0_2cell4_2
  · exact first0_2cell4_3
  · decide +kernel
  · decide +kernel
  · exact first0_2cell4_6
  · exact first0_2cell4_7
  · decide +kernel
  · exact first0_2cell5_0
  · decide +kernel
  · exact first0_2cell5_2
  · exact first0_2cell5_3
  · exact first0_2cell5_4
  · decide +kernel
  · exact first0_2cell5_6
  · exact first0_2cell5_7
  · decide +kernel
  · exact first0_2cell6_0
  · decide +kernel
  · exact first0_2cell6_2
  · exact first0_2cell6_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_2cell6_7
  · decide +kernel
  · exact first0_2cell7_0
  · decide +kernel
  · exact first0_2cell7_2
  · exact first0_2cell7_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_2cell8_0
  · exact first0_2cell8_1
  · exact first0_2cell8_2
  · exact first0_2cell8_3
  · exact first0_2cell8_4
  · exact first0_2cell8_5
  · exact first0_2cell8_6
  · exact first0_2cell8_7
  · decide +kernel
def first0_3Wire := gate true true (raw.getD 0 0) (raw.getD 3 0)
def first0_3Pool := first0_3Wire :: rest raw (raw.getD 0 0) (raw.getD 3 0) true true
def first0_3Cuts := cuts.map (buy first0_3Wire)
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell0_2 : cell tgt 9 first0_3Pool first0_3Cuts 0 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell0_3 : cell tgt 9 first0_3Pool first0_3Cuts 0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell0_6 : cell tgt 9 first0_3Pool first0_3Cuts 0 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell0_7 : cell tgt 9 first0_3Pool first0_3Cuts 0 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell1_0 : cell tgt 9 first0_3Pool first0_3Cuts 1 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell1_2 : cell tgt 9 first0_3Pool first0_3Cuts 1 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell1_3 : cell tgt 9 first0_3Pool first0_3Cuts 1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell1_4 : cell tgt 9 first0_3Pool first0_3Cuts 1 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell1_5 : cell tgt 9 first0_3Pool first0_3Cuts 1 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell1_6 : cell tgt 9 first0_3Pool first0_3Cuts 1 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell1_7 : cell tgt 9 first0_3Pool first0_3Cuts 1 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell2_3 : cell tgt 9 first0_3Pool first0_3Cuts 2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell4_0 : cell tgt 9 first0_3Pool first0_3Cuts 4 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell4_2 : cell tgt 9 first0_3Pool first0_3Cuts 4 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell4_3 : cell tgt 9 first0_3Pool first0_3Cuts 4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell4_6 : cell tgt 9 first0_3Pool first0_3Cuts 4 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell4_7 : cell tgt 9 first0_3Pool first0_3Cuts 4 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell5_0 : cell tgt 9 first0_3Pool first0_3Cuts 5 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell5_2 : cell tgt 9 first0_3Pool first0_3Cuts 5 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell5_3 : cell tgt 9 first0_3Pool first0_3Cuts 5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell5_4 : cell tgt 9 first0_3Pool first0_3Cuts 5 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell5_6 : cell tgt 9 first0_3Pool first0_3Cuts 5 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell5_7 : cell tgt 9 first0_3Pool first0_3Cuts 5 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell6_2 : cell tgt 9 first0_3Pool first0_3Cuts 6 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell6_3 : cell tgt 9 first0_3Pool first0_3Cuts 6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell6_7 : cell tgt 9 first0_3Pool first0_3Cuts 6 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell7_2 : cell tgt 9 first0_3Pool first0_3Cuts 7 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell7_3 : cell tgt 9 first0_3Pool first0_3Cuts 7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell8_0 : cell tgt 9 first0_3Pool first0_3Cuts 8 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell8_1 : cell tgt 9 first0_3Pool first0_3Cuts 8 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell8_2 : cell tgt 9 first0_3Pool first0_3Cuts 8 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell8_3 : cell tgt 9 first0_3Pool first0_3Cuts 8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell8_4 : cell tgt 9 first0_3Pool first0_3Cuts 8 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell8_5 : cell tgt 9 first0_3Pool first0_3Cuts 8 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell8_6 : cell tgt 9 first0_3Pool first0_3Cuts 8 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_3cell8_7 : cell tgt 9 first0_3Pool first0_3Cuts 8 7 = true := by decide +kernel
set_option maxHeartbeats 3500000 in
theorem first0_3checked : checkWith 1897 tgt 10 first0_3Pool first0_3Cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 9 at hi
  change j < 9 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · decide +kernel
  · exact first0_3cell0_2
  · exact first0_3cell0_3
  · decide +kernel
  · decide +kernel
  · exact first0_3cell0_6
  · exact first0_3cell0_7
  · decide +kernel
  · exact first0_3cell1_0
  · decide +kernel
  · exact first0_3cell1_2
  · exact first0_3cell1_3
  · exact first0_3cell1_4
  · exact first0_3cell1_5
  · exact first0_3cell1_6
  · exact first0_3cell1_7
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_3cell2_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_3cell4_0
  · decide +kernel
  · exact first0_3cell4_2
  · exact first0_3cell4_3
  · decide +kernel
  · decide +kernel
  · exact first0_3cell4_6
  · exact first0_3cell4_7
  · decide +kernel
  · exact first0_3cell5_0
  · decide +kernel
  · exact first0_3cell5_2
  · exact first0_3cell5_3
  · exact first0_3cell5_4
  · decide +kernel
  · exact first0_3cell5_6
  · exact first0_3cell5_7
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_3cell6_2
  · exact first0_3cell6_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_3cell6_7
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_3cell7_2
  · exact first0_3cell7_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_3cell8_0
  · exact first0_3cell8_1
  · exact first0_3cell8_2
  · exact first0_3cell8_3
  · exact first0_3cell8_4
  · exact first0_3cell8_5
  · exact first0_3cell8_6
  · exact first0_3cell8_7
  · decide +kernel
def first0_5Wire := gate true true (raw.getD 0 0) (raw.getD 5 0)
def first0_5Pool := first0_5Wire :: rest raw (raw.getD 0 0) (raw.getD 5 0) true true
def first0_5Cuts := cuts.map (buy first0_5Wire)
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell0_2 : cell tgt 9 first0_5Pool first0_5Cuts 0 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell0_3 : cell tgt 9 first0_5Pool first0_5Cuts 0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell0_7 : cell tgt 9 first0_5Pool first0_5Cuts 0 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell1_0 : cell tgt 9 first0_5Pool first0_5Cuts 1 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell1_2 : cell tgt 9 first0_5Pool first0_5Cuts 1 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell1_3 : cell tgt 9 first0_5Pool first0_5Cuts 1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell1_4 : cell tgt 9 first0_5Pool first0_5Cuts 1 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell1_5 : cell tgt 9 first0_5Pool first0_5Cuts 1 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell1_6 : cell tgt 9 first0_5Pool first0_5Cuts 1 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell1_7 : cell tgt 9 first0_5Pool first0_5Cuts 1 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell2_3 : cell tgt 9 first0_5Pool first0_5Cuts 2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell4_0 : cell tgt 9 first0_5Pool first0_5Cuts 4 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell4_2 : cell tgt 9 first0_5Pool first0_5Cuts 4 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell4_3 : cell tgt 9 first0_5Pool first0_5Cuts 4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell4_6 : cell tgt 9 first0_5Pool first0_5Cuts 4 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell4_7 : cell tgt 9 first0_5Pool first0_5Cuts 4 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell5_0 : cell tgt 9 first0_5Pool first0_5Cuts 5 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell5_2 : cell tgt 9 first0_5Pool first0_5Cuts 5 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell5_3 : cell tgt 9 first0_5Pool first0_5Cuts 5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell5_4 : cell tgt 9 first0_5Pool first0_5Cuts 5 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell5_6 : cell tgt 9 first0_5Pool first0_5Cuts 5 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell5_7 : cell tgt 9 first0_5Pool first0_5Cuts 5 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell6_0 : cell tgt 9 first0_5Pool first0_5Cuts 6 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell6_2 : cell tgt 9 first0_5Pool first0_5Cuts 6 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell6_3 : cell tgt 9 first0_5Pool first0_5Cuts 6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell6_7 : cell tgt 9 first0_5Pool first0_5Cuts 6 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell7_2 : cell tgt 9 first0_5Pool first0_5Cuts 7 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell7_3 : cell tgt 9 first0_5Pool first0_5Cuts 7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell8_0 : cell tgt 9 first0_5Pool first0_5Cuts 8 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell8_1 : cell tgt 9 first0_5Pool first0_5Cuts 8 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell8_2 : cell tgt 9 first0_5Pool first0_5Cuts 8 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell8_3 : cell tgt 9 first0_5Pool first0_5Cuts 8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell8_4 : cell tgt 9 first0_5Pool first0_5Cuts 8 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell8_5 : cell tgt 9 first0_5Pool first0_5Cuts 8 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell8_6 : cell tgt 9 first0_5Pool first0_5Cuts 8 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first0_5cell8_7 : cell tgt 9 first0_5Pool first0_5Cuts 8 7 = true := by decide +kernel
set_option maxHeartbeats 3500000 in
theorem first0_5checked : checkWith 1897 tgt 10 first0_5Pool first0_5Cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 9 at hi
  change j < 9 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · decide +kernel
  · exact first0_5cell0_2
  · exact first0_5cell0_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_5cell0_7
  · decide +kernel
  · exact first0_5cell1_0
  · decide +kernel
  · exact first0_5cell1_2
  · exact first0_5cell1_3
  · exact first0_5cell1_4
  · exact first0_5cell1_5
  · exact first0_5cell1_6
  · exact first0_5cell1_7
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_5cell2_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_5cell4_0
  · decide +kernel
  · exact first0_5cell4_2
  · exact first0_5cell4_3
  · decide +kernel
  · decide +kernel
  · exact first0_5cell4_6
  · exact first0_5cell4_7
  · decide +kernel
  · exact first0_5cell5_0
  · decide +kernel
  · exact first0_5cell5_2
  · exact first0_5cell5_3
  · exact first0_5cell5_4
  · decide +kernel
  · exact first0_5cell5_6
  · exact first0_5cell5_7
  · decide +kernel
  · exact first0_5cell6_0
  · decide +kernel
  · exact first0_5cell6_2
  · exact first0_5cell6_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_5cell6_7
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_5cell7_2
  · exact first0_5cell7_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_5cell8_0
  · exact first0_5cell8_1
  · exact first0_5cell8_2
  · exact first0_5cell8_3
  · exact first0_5cell8_4
  · exact first0_5cell8_5
  · exact first0_5cell8_6
  · exact first0_5cell8_7
  · decide +kernel
def first3_2Wire := gate true true (raw.getD 3 0) (raw.getD 2 0)
def first3_2Pool := first3_2Wire :: rest raw (raw.getD 3 0) (raw.getD 2 0) true true
def first3_2Cuts := cuts.map (buy first3_2Wire)
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell1_0 : cell tgt 9 first3_2Pool first3_2Cuts 1 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell1_2 : cell tgt 9 first3_2Pool first3_2Cuts 1 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell1_3 : cell tgt 9 first3_2Pool first3_2Cuts 1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell1_4 : cell tgt 9 first3_2Pool first3_2Cuts 1 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell1_5 : cell tgt 9 first3_2Pool first3_2Cuts 1 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell1_6 : cell tgt 9 first3_2Pool first3_2Cuts 1 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell1_7 : cell tgt 9 first3_2Pool first3_2Cuts 1 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell2_0 : cell tgt 9 first3_2Pool first3_2Cuts 2 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell2_3 : cell tgt 9 first3_2Pool first3_2Cuts 2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell3_0 : cell tgt 9 first3_2Pool first3_2Cuts 3 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell4_0 : cell tgt 9 first3_2Pool first3_2Cuts 4 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell4_2 : cell tgt 9 first3_2Pool first3_2Cuts 4 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell4_3 : cell tgt 9 first3_2Pool first3_2Cuts 4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell4_6 : cell tgt 9 first3_2Pool first3_2Cuts 4 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell4_7 : cell tgt 9 first3_2Pool first3_2Cuts 4 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell5_0 : cell tgt 9 first3_2Pool first3_2Cuts 5 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell5_2 : cell tgt 9 first3_2Pool first3_2Cuts 5 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell5_3 : cell tgt 9 first3_2Pool first3_2Cuts 5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell5_4 : cell tgt 9 first3_2Pool first3_2Cuts 5 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell5_6 : cell tgt 9 first3_2Pool first3_2Cuts 5 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell5_7 : cell tgt 9 first3_2Pool first3_2Cuts 5 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell6_0 : cell tgt 9 first3_2Pool first3_2Cuts 6 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell6_2 : cell tgt 9 first3_2Pool first3_2Cuts 6 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell6_3 : cell tgt 9 first3_2Pool first3_2Cuts 6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell6_7 : cell tgt 9 first3_2Pool first3_2Cuts 6 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell7_0 : cell tgt 9 first3_2Pool first3_2Cuts 7 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell7_2 : cell tgt 9 first3_2Pool first3_2Cuts 7 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell7_3 : cell tgt 9 first3_2Pool first3_2Cuts 7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell8_0 : cell tgt 9 first3_2Pool first3_2Cuts 8 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell8_1 : cell tgt 9 first3_2Pool first3_2Cuts 8 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell8_2 : cell tgt 9 first3_2Pool first3_2Cuts 8 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell8_3 : cell tgt 9 first3_2Pool first3_2Cuts 8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell8_4 : cell tgt 9 first3_2Pool first3_2Cuts 8 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell8_5 : cell tgt 9 first3_2Pool first3_2Cuts 8 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell8_6 : cell tgt 9 first3_2Pool first3_2Cuts 8 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_2cell8_7 : cell tgt 9 first3_2Pool first3_2Cuts 8 7 = true := by decide +kernel
set_option maxHeartbeats 3500000 in
theorem first3_2checked : checkWith 1897 tgt 10 first3_2Pool first3_2Cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 9 at hi
  change j < 9 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_2cell1_0
  · decide +kernel
  · exact first3_2cell1_2
  · exact first3_2cell1_3
  · exact first3_2cell1_4
  · exact first3_2cell1_5
  · exact first3_2cell1_6
  · exact first3_2cell1_7
  · decide +kernel
  · exact first3_2cell2_0
  · decide +kernel
  · decide +kernel
  · exact first3_2cell2_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_2cell3_0
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_2cell4_0
  · decide +kernel
  · exact first3_2cell4_2
  · exact first3_2cell4_3
  · decide +kernel
  · decide +kernel
  · exact first3_2cell4_6
  · exact first3_2cell4_7
  · decide +kernel
  · exact first3_2cell5_0
  · decide +kernel
  · exact first3_2cell5_2
  · exact first3_2cell5_3
  · exact first3_2cell5_4
  · decide +kernel
  · exact first3_2cell5_6
  · exact first3_2cell5_7
  · decide +kernel
  · exact first3_2cell6_0
  · decide +kernel
  · exact first3_2cell6_2
  · exact first3_2cell6_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_2cell6_7
  · decide +kernel
  · exact first3_2cell7_0
  · decide +kernel
  · exact first3_2cell7_2
  · exact first3_2cell7_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_2cell8_0
  · exact first3_2cell8_1
  · exact first3_2cell8_2
  · exact first3_2cell8_3
  · exact first3_2cell8_4
  · exact first3_2cell8_5
  · exact first3_2cell8_6
  · exact first3_2cell8_7
  · decide +kernel
def first3_5Wire := gate true true (raw.getD 3 0) (raw.getD 5 0)
def first3_5Pool := first3_5Wire :: rest raw (raw.getD 3 0) (raw.getD 5 0) true true
def first3_5Cuts := cuts.map (buy first3_5Wire)
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell0_2 : cell tgt 9 first3_5Pool first3_5Cuts 0 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell0_3 : cell tgt 9 first3_5Pool first3_5Cuts 0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell0_7 : cell tgt 9 first3_5Pool first3_5Cuts 0 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell1_0 : cell tgt 9 first3_5Pool first3_5Cuts 1 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell1_2 : cell tgt 9 first3_5Pool first3_5Cuts 1 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell1_3 : cell tgt 9 first3_5Pool first3_5Cuts 1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell1_4 : cell tgt 9 first3_5Pool first3_5Cuts 1 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell1_5 : cell tgt 9 first3_5Pool first3_5Cuts 1 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell1_6 : cell tgt 9 first3_5Pool first3_5Cuts 1 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell1_7 : cell tgt 9 first3_5Pool first3_5Cuts 1 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell2_3 : cell tgt 9 first3_5Pool first3_5Cuts 2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell4_0 : cell tgt 9 first3_5Pool first3_5Cuts 4 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell4_2 : cell tgt 9 first3_5Pool first3_5Cuts 4 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell4_3 : cell tgt 9 first3_5Pool first3_5Cuts 4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell4_6 : cell tgt 9 first3_5Pool first3_5Cuts 4 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell4_7 : cell tgt 9 first3_5Pool first3_5Cuts 4 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell5_0 : cell tgt 9 first3_5Pool first3_5Cuts 5 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell5_2 : cell tgt 9 first3_5Pool first3_5Cuts 5 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell5_3 : cell tgt 9 first3_5Pool first3_5Cuts 5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell5_4 : cell tgt 9 first3_5Pool first3_5Cuts 5 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell5_6 : cell tgt 9 first3_5Pool first3_5Cuts 5 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell5_7 : cell tgt 9 first3_5Pool first3_5Cuts 5 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell6_0 : cell tgt 9 first3_5Pool first3_5Cuts 6 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell6_2 : cell tgt 9 first3_5Pool first3_5Cuts 6 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell6_3 : cell tgt 9 first3_5Pool first3_5Cuts 6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell6_7 : cell tgt 9 first3_5Pool first3_5Cuts 6 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell7_2 : cell tgt 9 first3_5Pool first3_5Cuts 7 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell7_3 : cell tgt 9 first3_5Pool first3_5Cuts 7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell8_0 : cell tgt 9 first3_5Pool first3_5Cuts 8 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell8_1 : cell tgt 9 first3_5Pool first3_5Cuts 8 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell8_2 : cell tgt 9 first3_5Pool first3_5Cuts 8 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell8_3 : cell tgt 9 first3_5Pool first3_5Cuts 8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell8_4 : cell tgt 9 first3_5Pool first3_5Cuts 8 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell8_5 : cell tgt 9 first3_5Pool first3_5Cuts 8 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell8_6 : cell tgt 9 first3_5Pool first3_5Cuts 8 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first3_5cell8_7 : cell tgt 9 first3_5Pool first3_5Cuts 8 7 = true := by decide +kernel
set_option maxHeartbeats 3500000 in
theorem first3_5checked : checkWith 1897 tgt 10 first3_5Pool first3_5Cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 9 at hi
  change j < 9 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · decide +kernel
  · exact first3_5cell0_2
  · exact first3_5cell0_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_5cell0_7
  · decide +kernel
  · exact first3_5cell1_0
  · decide +kernel
  · exact first3_5cell1_2
  · exact first3_5cell1_3
  · exact first3_5cell1_4
  · exact first3_5cell1_5
  · exact first3_5cell1_6
  · exact first3_5cell1_7
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_5cell2_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_5cell4_0
  · decide +kernel
  · exact first3_5cell4_2
  · exact first3_5cell4_3
  · decide +kernel
  · decide +kernel
  · exact first3_5cell4_6
  · exact first3_5cell4_7
  · decide +kernel
  · exact first3_5cell5_0
  · decide +kernel
  · exact first3_5cell5_2
  · exact first3_5cell5_3
  · exact first3_5cell5_4
  · decide +kernel
  · exact first3_5cell5_6
  · exact first3_5cell5_7
  · decide +kernel
  · exact first3_5cell6_0
  · decide +kernel
  · exact first3_5cell6_2
  · exact first3_5cell6_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_5cell6_7
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_5cell7_2
  · exact first3_5cell7_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_5cell8_0
  · exact first3_5cell8_1
  · exact first3_5cell8_2
  · exact first3_5cell8_3
  · exact first3_5cell8_4
  · exact first3_5cell8_5
  · exact first3_5cell8_6
  · exact first3_5cell8_7
  · decide +kernel
def first5_2Wire := gate true true (raw.getD 5 0) (raw.getD 2 0)
def first5_2Pool := first5_2Wire :: rest raw (raw.getD 5 0) (raw.getD 2 0) true true
def first5_2Cuts := cuts.map (buy first5_2Wire)
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell1_0 : cell tgt 9 first5_2Pool first5_2Cuts 1 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell1_2 : cell tgt 9 first5_2Pool first5_2Cuts 1 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell1_3 : cell tgt 9 first5_2Pool first5_2Cuts 1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell1_4 : cell tgt 9 first5_2Pool first5_2Cuts 1 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell1_5 : cell tgt 9 first5_2Pool first5_2Cuts 1 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell1_6 : cell tgt 9 first5_2Pool first5_2Cuts 1 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell1_7 : cell tgt 9 first5_2Pool first5_2Cuts 1 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell2_0 : cell tgt 9 first5_2Pool first5_2Cuts 2 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell2_3 : cell tgt 9 first5_2Pool first5_2Cuts 2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell3_0 : cell tgt 9 first5_2Pool first5_2Cuts 3 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell4_0 : cell tgt 9 first5_2Pool first5_2Cuts 4 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell4_2 : cell tgt 9 first5_2Pool first5_2Cuts 4 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell4_3 : cell tgt 9 first5_2Pool first5_2Cuts 4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell4_6 : cell tgt 9 first5_2Pool first5_2Cuts 4 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell4_7 : cell tgt 9 first5_2Pool first5_2Cuts 4 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell5_0 : cell tgt 9 first5_2Pool first5_2Cuts 5 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell5_2 : cell tgt 9 first5_2Pool first5_2Cuts 5 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell5_3 : cell tgt 9 first5_2Pool first5_2Cuts 5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell5_4 : cell tgt 9 first5_2Pool first5_2Cuts 5 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell5_6 : cell tgt 9 first5_2Pool first5_2Cuts 5 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell5_7 : cell tgt 9 first5_2Pool first5_2Cuts 5 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell6_0 : cell tgt 9 first5_2Pool first5_2Cuts 6 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell6_2 : cell tgt 9 first5_2Pool first5_2Cuts 6 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell6_3 : cell tgt 9 first5_2Pool first5_2Cuts 6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell6_7 : cell tgt 9 first5_2Pool first5_2Cuts 6 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell7_0 : cell tgt 9 first5_2Pool first5_2Cuts 7 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell7_2 : cell tgt 9 first5_2Pool first5_2Cuts 7 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell7_3 : cell tgt 9 first5_2Pool first5_2Cuts 7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell8_0 : cell tgt 9 first5_2Pool first5_2Cuts 8 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell8_1 : cell tgt 9 first5_2Pool first5_2Cuts 8 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell8_2 : cell tgt 9 first5_2Pool first5_2Cuts 8 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell8_3 : cell tgt 9 first5_2Pool first5_2Cuts 8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell8_4 : cell tgt 9 first5_2Pool first5_2Cuts 8 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell8_5 : cell tgt 9 first5_2Pool first5_2Cuts 8 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell8_6 : cell tgt 9 first5_2Pool first5_2Cuts 8 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem first5_2cell8_7 : cell tgt 9 first5_2Pool first5_2Cuts 8 7 = true := by decide +kernel
set_option maxHeartbeats 3500000 in
theorem first5_2checked : checkWith 1897 tgt 10 first5_2Pool first5_2Cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 9 at hi
  change j < 9 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first5_2cell1_0
  · decide +kernel
  · exact first5_2cell1_2
  · exact first5_2cell1_3
  · exact first5_2cell1_4
  · exact first5_2cell1_5
  · exact first5_2cell1_6
  · exact first5_2cell1_7
  · decide +kernel
  · exact first5_2cell2_0
  · decide +kernel
  · decide +kernel
  · exact first5_2cell2_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first5_2cell3_0
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first5_2cell4_0
  · decide +kernel
  · exact first5_2cell4_2
  · exact first5_2cell4_3
  · decide +kernel
  · decide +kernel
  · exact first5_2cell4_6
  · exact first5_2cell4_7
  · decide +kernel
  · exact first5_2cell5_0
  · decide +kernel
  · exact first5_2cell5_2
  · exact first5_2cell5_3
  · exact first5_2cell5_4
  · decide +kernel
  · exact first5_2cell5_6
  · exact first5_2cell5_7
  · decide +kernel
  · exact first5_2cell6_0
  · decide +kernel
  · exact first5_2cell6_2
  · exact first5_2cell6_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first5_2cell6_7
  · decide +kernel
  · exact first5_2cell7_0
  · decide +kernel
  · exact first5_2cell7_2
  · exact first5_2cell7_3
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first5_2cell8_0
  · exact first5_2cell8_1
  · exact first5_2cell8_2
  · exact first5_2cell8_3
  · exact first5_2cell8_4
  · exact first5_2cell8_5
  · exact first5_2cell8_6
  · exact first5_2cell8_7
  · decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_1 : cell tgt 10 raw cuts 0 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_2 : cell tgt 10 raw cuts 0 2 = true := by
  apply flags_ok
  intro u v ka kb
  dsimp only
  intro nz fresh
  cases u <;> cases v <;> cases ka <;> cases kb
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_2checked
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_3 : cell tgt 10 raw cuts 0 3 = true := by
  apply flags_ok
  intro u v ka kb
  dsimp only
  intro nz fresh
  cases u <;> cases v <;> cases ka <;> cases kb
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_3checked
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_4 : cell tgt 10 raw cuts 0 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_5 : cell tgt 10 raw cuts 0 5 = true := by
  apply flags_ok
  intro u v ka kb
  dsimp only
  intro nz fresh
  cases u <;> cases v <;> cases ka <;> cases kb
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first0_5checked
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch0_6 : cell tgt 10 raw cuts 0 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch1_2 : cell tgt 10 raw cuts 1 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_1 : cell tgt 10 raw cuts 3 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_2 : cell tgt 10 raw cuts 3 2 = true := by
  apply flags_ok
  intro u v ka kb
  dsimp only
  intro nz fresh
  cases u <;> cases v <;> cases ka <;> cases kb
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_2checked
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_5 : cell tgt 10 raw cuts 3 5 = true := by
  apply flags_ok
  intro u v ka kb
  dsimp only
  intro nz fresh
  cases u <;> cases v <;> cases ka <;> cases kb
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first3_5checked
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch3_6 : cell tgt 10 raw cuts 3 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_1 : cell tgt 10 raw cuts 4 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_2 : cell tgt 10 raw cuts 4 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_3 : cell tgt 10 raw cuts 4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_5 : cell tgt 10 raw cuts 4 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch4_6 : cell tgt 10 raw cuts 4 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_1 : cell tgt 10 raw cuts 5 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_2 : cell tgt 10 raw cuts 5 2 = true := by
  apply flags_ok
  intro u v ka kb
  dsimp only
  intro nz fresh
  cases u <;> cases v <;> cases ka <;> cases kb
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact first5_2checked
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch5_6 : cell tgt 10 raw cuts 5 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_1 : cell tgt 10 raw cuts 6 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch6_2 : cell tgt 10 raw cuts 6 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch7_0 : cell tgt 10 raw cuts 7 0 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch7_1 : cell tgt 10 raw cuts 7 1 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch7_2 : cell tgt 10 raw cuts 7 2 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch7_3 : cell tgt 10 raw cuts 7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch7_4 : cell tgt 10 raw cuts 7 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch7_5 : cell tgt 10 raw cuts 7 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem branch7_6 : cell tgt 10 raw cuts 7 6 = true := by decide +kernel
set_option maxHeartbeats 3000000 in
theorem checked : checkWith 1897 tgt 11 raw cuts = true := by
  apply cells_ok _ _ _ _ (by decide +kernel)
  intro i hi j hj
  change i < 8 at hi
  change j < 8 at hj
  interval_cases i <;> interval_cases j
  · decide +kernel
  · exact branch0_1
  · exact branch0_2
  · exact branch0_3
  · exact branch0_4
  · exact branch0_5
  · exact branch0_6
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch1_2
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch3_1
  · exact branch3_2
  · decide +kernel
  · decide +kernel
  · exact branch3_5
  · exact branch3_6
  · decide +kernel
  · decide +kernel
  · exact branch4_1
  · exact branch4_2
  · exact branch4_3
  · decide +kernel
  · exact branch4_5
  · exact branch4_6
  · decide +kernel
  · decide +kernel
  · exact branch5_1
  · exact branch5_2
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch5_6
  · decide +kernel
  · decide +kernel
  · exact branch6_1
  · exact branch6_2
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact branch7_0
  · exact branch7_1
  · exact branch7_2
  · exact branch7_3
  · exact branch7_4
  · exact branch7_5
  · exact branch7_6
  · decide +kernel
theorem bound : Lower tgt raw 12 := by
  have ht : separated 1897 tgt = BitVec.allOnes 1897 := by decide +kernel
  apply lower_roots raw 11 ht (by decide +kernel) (by decide +kernel)
  intro k hk; exact checkWith_sound ht 11 raw cuts (by decide +kernel) geometry checked hk
end Graph01234578

namespace SignedPetersen
open SignedLive Graph01234578

def nine : List (Word (1897+1897)) :=
  [raw.getD 0 0,raw.getD 1 0,raw.getD 2 0,raw.getD 3 0,raw.getD 4 0,
   raw.getD 5 0,0,raw.getD 6 0,raw.getD 7 0]
def offered : List (Word (1897+1897)) := [0,~~~0] ++ nine ++ nine.map (fun x => ~~~x)
def edges9 : List (Nat × Nat) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(2,7),(3,8),(5,7),(8,5)]
def graph9 (x : Fin 9 → Bool) : Bool := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(2,7),(3,8),(5,7),(8,5)]
  : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2

theorem samplePins {n} (ws : List (Word n)) (r : Fin (n+1)) (len : ws.length = 9) :
    ws.map (SignedLive.read r) = List.ofFn (fun j : Fin 9 => SignedLive.read r (ws.getD j.val 0)) := by
  apply List.ext_getElem
  · simp [len]
  · intro i hi hj
    have inside : i < ws.length := by simpa using hi
    simp only [List.getElem_map,List.getElem_ofFn,List.getD_eq_getElem _ _ inside]

theorem agreeEdges (x : Fin 9 → Bool) : edgeTest edges9 (List.ofFn x) = graph9 x := rfl

set_option maxRecDepth 12000 in
theorem noEleven (p : List (Nat × Nat)) (o : Nat) (cost : p.length ≤ 11) :
    ∃ x : Fin 9 → Bool,
      (p.foldl (fun (w : List Bool) ij => let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false ≠ graph9 x := by
  by_contra! computes
  have recovers : (p.foldl add offered).getD o 0 = edgesBit nine edges9 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Fin ((1897+1897)+1) := ⟨i,hi⟩
    let x : Fin 9 → Bool := fun j => read r (nine.getD j.val 0)
    have sampleEq : nine.map (SignedLive.read r) = List.ofFn x := samplePins nine r rfl
    have inverted : (nine.map (fun a => ~~~a)).map (read r) = (nine.map (read r)).map Bool.not := by
      simp only [List.map_map,Function.comp_def,read_neg]
    have inputEq : offered.map (read r) = [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not := by
      simp only [offered,List.map_append,List.map_cons,List.map_nil,inverted,sampleEq,read_neg,
        show SignedLive.read r 0 = false by simp [SignedLive.read],Bool.not_false]
    change read r ((p.foldl add offered).getD o 0) = read r (edgesBit nine edges9)
    rw [read_get,read_program,inputEq,edges_read,sampleEq,agreeEdges]
    exact computes x
  have target : norm (edgesBit nine edges9) = tgt := by decide +kernel
  have seen := present (p.foldl add offered) o
  rw [recovers,target] at seen
  obtain ⟨k,S,hk,run,sub⟩ := extract p offered (show tgt ≠ 0 by decide +kernel)
    (seen.resolve_left (by decide +kernel))
  have inputs : pool offered ⊆ insert 0 raw.toFinset := by decide +kernel
  have impossible := bound k S run (sub.trans inputs)
  omega

end SignedPetersen
-- The signed-deletion reduction, binary budget and circuit compiler are by steveDOTdigital.
open PEqualNP.CircuitLowerBounds
namespace FinalNotWires
def WireLE (a b : List Bool) := ∀ i, a.getD i false = true → b.getD i false = true
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def fold (gs : List Gate) (w : List Bool) := gs.foldl step w
def mono (gs : List Gate) := ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or

theorem gate_mono (g : Gate) (a b : List Bool) (h : WireLE a b) (kind : g.op = GateOp.and ∨ g.op = GateOp.or) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
    g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases kind with hk|hk
  · simp only [hk,GateOp.eval,List.all_eq_true,List.mem_map,id_eq,forall_exists_index,and_imp]
    intro ha v i hi e
    subst v
    exact h i (ha _ i hi rfl)
  · simp only [hk,GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
    rintro ⟨v,⟨i,hi,rfl⟩,ok⟩
    exact ⟨_,⟨i,hi,rfl⟩,h i ok⟩

theorem append_mono (a b : List Bool) (hlen : a.length=b.length) (h : WireLE a b)
    (x y : Bool) (hxy : x=true → y=true) : WireLE (a++[x]) (b++[y]) := by
  intro i hi
  by_cases inA : i<a.length
  · rw [List.getD_append _ _ _ _ inA] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi ⊢
    rw [← hlen]
    by_cases atEnd : i=a.length
    · simpa [atEnd] using hxy (by simpa [atEnd] using hi)
    · have hbound : [x].length ≤ i-a.length := by simp; omega
      rw [List.getD_eq_default _ _ hbound] at hi
      contradiction

theorem fold_mono (gs : List Gate) (a b : List Bool) (m : mono gs)
    (hl : a.length=b.length) (h : WireLE a b) : WireLE (fold gs a) (fold gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    change WireLE (fold gs (step a g)) (fold gs (step b g))
    apply ih _ _ (fun z hz => m z (List.mem_cons_of_mem _ hz))
    · simp [step,hl]
    · exact append_mono a b hl h _ _ (gate_mono g a b h (m g (by simp)))

end FinalNotWires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenBinaryBudget

private def paid (g : Gate) : ℕ :=
  ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)

private theorem count (gs : List Gate) : (gs.map paid).sum ≤ gs.length ∧
    ((gs.map paid).sum = gs.length → ∀ g ∈ gs, g.op ≠ GateOp.not) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have cap : paid g ≤ 1 := by unfold paid; split <;> (first | decide | split <;> decide)
    obtain ⟨le,strict⟩ := ih
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    refine ⟨by omega,?_⟩
    intro eq z hz
    rcases List.mem_cons.mp hz with rfl | mem
    · intro h
      have : paid z = 0 := by simp [paid,h,GateOp.eval]
      omega
    · exact strict (by omega) z mem

theorem strict (C : Circuit) (h : FanInTwo C) (a b : List Bool)
    (lengths : a.length = b.length) (increasing : ∀ i : ℕ, a.getD i false = true → b.getD i false = true)
    (yes : C.eval a = true) (no : C.eval b = false) :
    (C.gates.map fun g => ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)).sum < C.size := by
  obtain ⟨le,allMono⟩ := count C.gates
  change (C.gates.map paid).sum < C.gates.length
  by_contra! ge
  have noNot := allMono (by omega)
  have mono : FinalNotWires.mono C.gates := by
    intro g hg
    have op : g.op = .and ∨ g.op = .or ∨ g.op = .not := (h g hg).1
    exact op.elim Or.inl (fun alt => Or.inr (alt.resolve_right (noNot g hg)))
  have bad := FinalNotWires.fold_mono C.gates a b mono lengths increasing C.output yes
  rw [← show C.eval b = (FinalNotWires.fold C.gates b).getD C.output false from rfl,no] at bad
  contradiction

end PetersenBinaryBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenSignedSlice

abbrev Signal (α : Type) := α → Bool
def inv {α} (a : Signal α) : Signal α := fun x => !(a x)
def meet {α} (a b : Signal α) : Signal α := fun x => a x && b x

-- A pool stores both polarities of every paid AND. Old wires remain available.
inductive Run {α : Type} (start : List (Signal α)) : ℕ → List (Signal α) → Prop where
  | nil : Run start 0 start
  | gate {k w} (h : Run start k w) {a b} (ha : a ∈ w) (hb : b ∈ w) :
      Run start (k+1) (w ++ [meet a b, inv (meet a b)])

theorem Run.keep {α} {s w : List (Signal α)} {k} (h : Run s k w) :
    ∀ v ∈ s, v ∈ w := by
  induction h with
  | nil => exact fun _ h => h
  | gate h _ _ ih => exact fun v hv => List.mem_append_left _ (ih v hv)

theorem Run.comp {α} {s w u : List (Signal α)} {k j} (h : Run s k w) (h' : Run w j u) :
    Run s (k+j) u := by
  induction h' with
  | nil => exact h
  | gate h' ha hb ih => exact Run.gate ih ha hb

structure Wire (α : Type) where
  f : Signal α
  lo : Bool
  hi : Bool

def K {α} (b : Bool) : Wire α := ⟨fun _ => b,b,b⟩
def neg {α} (a : Wire α) : Wire α := ⟨inv a.f,!a.lo,!a.hi⟩
def conj {α} (a b : Wire α) : Wire α := ⟨meet a.f b.f,a.lo && b.lo,a.hi && b.hi⟩
def disj {α} (a b : Wire α) : Wire α := neg (conj (neg a) (neg b))

def Good {α} (w : List (Signal α)) (a : Wire α) : Prop := a.f ∈ w ∧ inv a.f ∈ w
def Stable {α} (a : Wire α) : Prop := (∃ b, ∀ x, a.f x = b) ∨ a.lo = a.hi

theorem goodNeg {α} {w : List (Signal α)} {a} (h : Good w a) : Good w (neg a) := by
  refine ⟨h.2,?_⟩
  have eq : inv (inv a.f) = a.f := by funext x; simp [inv]
  change inv (inv a.f) ∈ w
  rw [eq]
  exact h.1

theorem stableNeg {α} {a : Wire α} (h : Stable a) : Stable (neg a) := by
  rcases h with ⟨b,hb⟩ | eq
  · exact Or.inl ⟨!b,fun x => by simp [neg,inv,hb]⟩
  · exact Or.inr (congrArg Bool.not eq)

def Eval {α} (op : GateOp) (args : List (Wire α)) : Wire α :=
  ⟨fun x => op.eval (args.map fun a => a.f x),op.eval (args.map Wire.lo),op.eval (args.map Wire.hi)⟩

def Paid (g : Gate) : ℕ :=
  if g.op.eval [false] then 0 else if g.inputs.length = 2 then 1 else 0

def Effect {α} (w : List (Signal α)) (n : ℕ) (a : Wire α) (inputs : List (Wire α)) : Prop :=
  ∃ c t, Run w c t ∧ c ≤ n ∧ Good t a ∧
    (c = n → (∀ u ∈ inputs, Stable u) → Stable a)

private theorem bin {α} (w : List (Signal α)) (base : ∀ b, Good w (K b)) (a b : Wire α)
    (ha : Good w a) (hb : Good w b) : Effect w 1 (conj a b) [a,b] := by
  classical
  by_cases ca : ∃ t, ∀ x, a.f x = t
  · obtain ⟨t,e⟩ := ca
    refine ⟨0,w,.nil,by decide,?_,by intro impossible; contradiction⟩
    cases t
    · have eq : (conj a b).f = (K (α := α) false).f := by funext x; simp [conj,meet,e,K]
      simpa only [Good,eq] using base false
    · have eq : (conj a b).f = b.f := by funext x; simp [conj,meet,e]
      simpa only [Good,eq] using hb
  by_cases cb : ∃ t, ∀ x, b.f x = t
  · obtain ⟨t,e⟩ := cb
    refine ⟨0,w,.nil,by decide,?_,by intro impossible; contradiction⟩
    cases t
    · have eq : (conj a b).f = (K (α := α) false).f := by funext x; simp [conj,meet,e,K]
      simpa only [Good,eq] using base false
    · have eq : (conj a b).f = a.f := by funext x; simp [conj,meet,e]
      simpa only [Good,eq] using ha
  · refine ⟨1,_,Run.gate Run.nil ha.1 hb.1,le_rfl,?_,?_⟩
    · exact ⟨List.mem_append_right _ (by simp [conj]),List.mem_append_right _ (by simp [conj])⟩
    · intro _ stable
      have ea := (stable a (by simp)).resolve_left ca
      have eb := (stable b (by simp)).resolve_left cb
      exact Or.inr (by simp [conj,ea,eb])

private theorem gateEffect {α} (w : List (Signal α)) (base : ∀ b, Good w (K b))
    (op : GateOp) (args : List (Wire α)) (h : ∀ a ∈ args, Good w a)
    (ok : op = .and ∨ op = .or ∨ op = .not) (sz : args.length ≤ 2) :
    Effect w (if op.eval [false] then 0 else if args.length = 2 then 1 else 0) (Eval op args) args := by
  have zero (z : Wire α) (hz : Good w z) (st : (∀ v ∈ args, Stable v) → Stable z) :
      Effect w 0 z args := ⟨0,w,.nil,le_rfl,hz,fun _ => st⟩
  rcases ok with rfl | rfl | rfl
  · cases args with
    | nil => exact zero _ (base true) (fun _ => Or.inl ⟨true,fun _ => rfl⟩)
    | cons a rest =>
      cases rest with
      | nil =>
        have eq : Eval .and [a] = a := by cases a; simp [Eval,GateOp.eval]
        rw [eq]
        exact zero a (h a (by simp)) (fun st => st a (by simp))
      | cons b rest =>
        have e : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at sz; omega)
        subst rest
        have eq : Eval .and [a,b] = conj a b := by simp [Eval,GateOp.eval,conj]; rfl
        rw [eq]
        exact bin w base a b (h a (by simp)) (h b (by simp))
  · cases args with
    | nil => exact zero _ (base false) (fun _ => Or.inl ⟨false,fun _ => rfl⟩)
    | cons a rest =>
      cases rest with
      | nil =>
        have eq : Eval .or [a] = a := by cases a; simp [Eval,GateOp.eval]
        rw [eq]
        exact zero a (h a (by simp)) (fun st => st a (by simp))
      | cons b rest =>
        have e : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at sz; omega)
        subst rest
        have eq : Eval .or [a,b] = disj a b := by simp [Eval,GateOp.eval,disj,conj,neg]; funext x; simp [inv,meet]
        rw [eq]
        obtain ⟨c,t,r,k,g,st⟩ := bin w base (neg a) (neg b) (goodNeg (h a (by simp))) (goodNeg (h b (by simp)))
        refine ⟨c,t,r,k,goodNeg g,fun equal stable => stableNeg (st equal ?_)⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | h'
        · exact stableNeg (stable _ (by simp))
        · have hv := List.mem_singleton.mp h'
          exact hv ▸ stableNeg (stable b (by simp))
  · cases args with
    | nil => exact zero _ (base true) (fun _ => Or.inl ⟨true,fun _ => rfl⟩)
    | cons a rest =>
      exact zero (neg a) (goodNeg (h a (by simp))) (fun st => stableNeg (st a (by simp)))


def step {α} (v : List (Wire α)) (g : Gate) : List (Wire α) :=
  v ++ [Eval g.op (g.inputs.map fun i => v.getD i (K false))]

theorem get_property {α} (P : α → Prop) (v : List α) (d : α) (i : ℕ)
    (hd : P d) (h : ∀ z ∈ v, P z) : P (v.getD i d) := by
  by_cases hi : i < v.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hd

theorem fold {α} (gs : List Gate) (legal : ∀ g ∈ gs,
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (w : List (Signal α)) (base : ∀ b, Good w (K b)) (v : List (Wire α))
    (old : ∀ a ∈ v, Good w a) :
    ∃ k t, Run w k t ∧ k ≤ (gs.map Paid).sum ∧
      (∀ a ∈ gs.foldl step v, Good t a) ∧
      (k = (gs.map Paid).sum → (∀ a ∈ v, Stable a) → ∀ a ∈ gs.foldl step v, Stable a) := by
  induction gs generalizing w v with
  | nil => exact ⟨0,w,.nil,le_rfl,old,fun _ st => st⟩
  | cons g gs ih =>
    let args := g.inputs.map fun i => v.getD i (K false)
    have allg : ∀ z ∈ args, Good w z := by
      intro z mem
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
      exact get_property _ _ _ _ (base false) old
    have h := gateEffect w base g.op args allg (legal g (by simp)).1 (by simpa [args] using (legal g (by simp)).2)
    obtain ⟨c,t,run,cap,gnew,snew⟩ := h
    have ec : c ≤ Paid g := by simpa only [Paid,args,List.length_map] using cap
    have goodKeep {a} (ok : Good w a) : Good t a := ⟨run.keep _ ok.1,run.keep _ ok.2⟩
    have goodNext : ∀ a ∈ step v g, Good t a := by
      intro a mem
      rcases List.mem_append.mp mem with ov | nv
      · exact goodKeep (old a ov)
      · exact (List.mem_singleton.mp nv) ▸ gnew
    obtain ⟨j,u,tail,limit,done,st⟩ := ih (fun z hz => legal z (List.mem_cons_of_mem g hz))
      t (fun b => goodKeep (base b)) (step v g) goodNext
    refine ⟨c+j,u,run.comp tail,by simpa using Nat.add_le_add ec limit,done,?_⟩
    intro equal previous
    simp only [List.map_cons,List.sum_cons] at equal
    apply st (by omega)
    intro a mem
    rcases List.mem_append.mp mem with ov | nv
    · exact previous a ov
    · apply (List.mem_singleton.mp nv) ▸ snew (by simpa only [args,List.length_map,Paid] using (show c = Paid g by omega))
      intro z hz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact get_property _ _ _ _ (Or.inl ⟨false,fun _ => rfl⟩ : Stable (K (α := α) false)) previous

def addPair (w : List Bool) (ij : ℕ × ℕ) : List Bool :=
  let z := w.getD ij.1 false && w.getD ij.2 false
  w ++ [z,!z]

theorem Run.program {α} {s w : List (Signal α)} {k} (r : Run s k w) :
    ∃ prog : List (ℕ × ℕ), prog.length = k ∧ ∀ x : α,
      prog.foldl addPair (s.map fun f => f x) = w.map fun f => f x := by
  induction r with
  | nil => exact ⟨[],rfl,fun _ => rfl⟩
  | @gate k w r a b ha hb ih =>
    obtain ⟨p,len,sim⟩ := ih
    obtain ⟨i,hi,ei⟩ := List.getElem_of_mem ha
    obtain ⟨j,hj,ej⟩ := List.getElem_of_mem hb
    refine ⟨p++[(i,j)],by simp [len],?_⟩
    intro x
    rw [List.foldl_append,sim]
    simp only [List.foldl_cons,List.foldl_nil,addPair,List.map_append,List.map_cons,List.map_nil]
    rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hj)]
    simp [List.getElem_map,ei,ej,meet,inv]

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem getMap {α β} (h : α → β) (v : List α) (i : ℕ) (d : α) :
    h (v.getD i d) = (v.map h).getD i (h d) := by
  simp [List.getD,List.getElem?_map,Option.getD_map]

theorem aligns {α} (h : Wire α → Bool) (hd : h (K false) = false)
    (he : ∀ op args, h (Eval op args) = op.eval (args.map h)) (gs : List Gate) (v : List (Wire α)) :
    (gs.foldl step v).map h = gs.foldl boolStep (v.map h) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    congr 1
    simp only [step,boolStep,List.map_append,List.map_cons,List.map_nil,he,List.map_map,
      Function.comp_def,getMap h,hd]

theorem outputMap {α} (h : Wire α → Bool) (hd : h (K false) = false)
    (he : ∀ op args, h (Eval op args) = op.eval (args.map h)) (C : Circuit) (v : List (Wire α)) :
    h ((C.gates.foldl step v).getD C.output (K false)) = C.eval (v.map h) := by
  rw [getMap h,hd,aligns h hd he]
  rfl


theorem compile (α : Type) (C : Circuit) (hc : FanInTwo C) (s : List (α → Bool))
    (v : List ((α → Bool) × Bool × Bool)) (constants : ∀ b : Bool, (fun _ : α => b) ∈ s)
    (pins : ∀ a ∈ v, a.1 ∈ s ∧ (fun x => !(a.1 x)) ∈ s ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2))
    (varies : ¬ ∃ b : Bool, ∀ x : α, C.eval (v.map fun a => a.1 x) = b)
    (sensitive : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2)) :
    ∃ (p : List (ℕ × ℕ)) (o : ℕ),
      p.length < (C.gates.map fun g => ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)).sum ∧
      ∀ x : α, (p.foldl (fun w ij =>
        let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) (s.map fun f => f x)).getD o false = C.eval (v.map fun a => a.1 x) := by
  let make := fun a : (α → Bool) × Bool × Bool => Wire.mk a.1 a.2.1 a.2.2
  let a := v.map make
  have base (b : Bool) : Good s (K b) := ⟨constants b,constants (!b)⟩
  have old : ∀ u ∈ a, Good s u ∧ Stable u := by
    intro u hu
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hu
    obtain ⟨hg,hn,hs⟩ := pins z hz
    exact ⟨⟨hg,hn⟩,hs⟩
  obtain ⟨k,t,run,limit,accepted,stable⟩ :=
    fold C.gates (fun g hg => ⟨(hc g hg).1,(hc g hg).2⟩) s base a (fun u hu => (old u hu).1)
  let out := (C.gates.foldl step a).getD C.output (K false)
  have values (x : α) : out.f x = C.eval (v.map fun u => u.1 x) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using
      outputMap (fun u : Wire α => u.f x) rfl (fun _ _ => rfl) C a
  have lo : out.lo = C.eval (v.map fun u => u.2.1) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using outputMap Wire.lo rfl (fun _ _ => rfl) C a
  have hi : out.hi = C.eval (v.map fun u => u.2.2) := by
    simpa [out,a,make,List.map_map,Function.comp_def] using outputMap Wire.hi rfl (fun _ _ => rfl) C a
  have lt : k < (C.gates.map Paid).sum := by
    by_contra! ge
    have eq := Nat.le_antisymm limit ge
    have impossible : Stable out := get_property _ _ _ _
      (Or.inl ⟨false,fun _ => rfl⟩ : Stable (K (α := α) false)) (stable eq (fun u hu => (old u hu).2))
    rcases impossible with ⟨b,h⟩ | e
    · exact varies ⟨b,fun x => (values x).symm.trans (h x)⟩
    · exact sensitive (lo.symm.trans (e.trans hi))
  have zero : Good t (K false) := ⟨run.keep _ (base false).1,run.keep _ (base false).2⟩
  have usable : Good t out := get_property _ _ _ _ zero accepted
  obtain ⟨o,ho,eo⟩ := List.getElem_of_mem usable.1
  obtain ⟨p,len,sim⟩ := run.program
  refine ⟨p,o,by rw [len]; exact lt,?_⟩
  intro x
  change (p.foldl addPair _).getD o false = _
  rw [sim,List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_map,eo]
  exact values x

end PetersenSignedSlice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem SignedPetersen.combine
    (budget : ∀ (C : Circuit) (h : FanInTwo C) (a b : List Bool)
    (lengths : a.length = b.length) (increasing : ∀ i : ℕ, a.getD i false = true → b.getD i false = true)
    (yes : C.eval a = true) (no : C.eval b = false),
    (C.gates.map fun g => ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)).sum < C.size)
    (slice : ∀ (α : Type) (C : Circuit) (hc : FanInTwo C) (s : List (α → Bool))
    (v : List ((α → Bool) × Bool × Bool)) (constants : ∀ b : Bool, (fun _ : α => b) ∈ s)
    (pins : ∀ a ∈ v, a.1 ∈ s ∧ (fun x => !(a.1 x)) ∈ s ∧
      ((∃ b, ∀ x, a.1 x = b) ∨ a.2.1 = a.2.2))
    (varies : ¬ ∃ b : Bool, ∀ x : α, C.eval (v.map fun a => a.1 x) = b)
    (sensitive : C.eval (v.map fun a => a.2.1) ≠ C.eval (v.map fun a => a.2.2)),
    ∃ (p : List (ℕ × ℕ)) (o : ℕ),
      p.length < (C.gates.map fun g => ite (g.op.eval [false] = true) 0 (ite (g.inputs.length = 2) 1 0)).sum ∧
      ∀ x : α, (p.foldl (fun w ij =>
        let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) (s.map fun f => f x)).getD o false = C.eval (v.map fun a => a.1 x))
    (lower : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 11 → ∃ x : Fin 9 → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false ≠
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(2,7),(3,8),(5,7),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval ((List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ))]).set ↑x2 !x8 x2) ≠ x1 x8 := by
  let graph := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let deleted := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(2,7),(3,8),(5,7),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let pins := fun (i : Fin 9) (x : Fin 9 → Bool) => (List.ofFn x ++ [x 0 || x 6]).set i.val (!(x i))
  intro target i C nz ns hc tiny
  change ∃ x : Fin 9 → Bool, C.eval (pins i x) ≠ graph x
  by_contra! correct
  let neighbor : Fin 9 → Fin 9 := ![1,0,1,2,0,0,1,2,3]
  let point := fun j : Fin 9 => decide (j=neighbor i)
  let edge := fun j : Fin 9 => decide (j=i ∨ j=neighbor i)
  have yes : graph edge = true := by
    fin_cases i <;> decide
  have no : graph point = false := by
    fin_cases i <;> decide
  let wire := fun (x : Fin 9 → Bool) (j : Fin 10) =>
    if h : j.val < 9 then (if j.val = i.val then !(x i) else x ⟨j.val,h⟩) else (x 0 || x 6)
  have pinList (x : Fin 9 → Bool) : List.ofFn (wire x) = pins i x := by
    fin_cases i <;> simp [pins,wire,List.set]
  have inc : ∀ j : Fin 10, wire edge j = true → wire point j = true := by
    fin_cases i <;> first | contradiction | decide
  have ordered (j : ℕ) : (pins i edge).getD j false = true → (pins i point).getD j false = true := by
    rw [← pinList edge,← pinList point]
    by_cases hj : j < 10
    · rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getD_eq_getElem _ _ (by simpa using hj)]
      simpa only [List.getElem_ofFn] using inc ⟨j,hj⟩
    · rw [List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt hj)),List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt hj))]
      exact id
  have less := budget C hc (pins i edge) (pins i point) (by simp [pins]) ordered
    ((correct edge).trans yes) ((correct point).trans no)
  let erase := fun (x : Fin 9 → Bool) (v : Fin 9) => if v=6 then false else x v
  let a := fun j : Fin 9 => decide (j=0 ∨ j=8)
  let b := fun j : Fin 9 => decide (j=0 ∨ j=6 ∨ j=8)
  let v := List.ofFn (fun j : Fin 10 => ((fun x : Fin 9 → Bool => wire (erase x) j),wire a j,wire b j))
  let raws := List.ofFn (fun j : Fin 9 => (fun x : Fin 9 → Bool => x j))
  let s := [(fun _ : Fin 9 → Bool => false),(fun _ : Fin 9 → Bool => true)] ++ raws ++ raws.map (fun f x => !(f x))
  have constants (bit : Bool) : (fun _ : Fin 9 → Bool => bit) ∈ s := by
    cases bit <;> simp [s]
  have pos (j : Fin 9) : (fun x : Fin 9 → Bool => x j) ∈ s := by
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  have neg (j : Fin 9) : (fun x : Fin 9 → Bool => !(x j)) ∈ s := by
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,rfl⟩
  have data : ∀ t ∈ v, t.1 ∈ s ∧ (fun x => !(t.1 x)) ∈ s ∧
      ((∃ bit, ∀ x, t.1 x=bit) ∨ t.2.1=t.2.2) := by
    intro t ht
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
    by_cases last : j.val < 9
    · by_cases same : j.val = i.val
      · have hi : i ≠ 6 := ns
        simp only [wire,same,i.isLt,↓reduceDIte,ite_true,erase,hi,ite_false,Bool.not_not]
        exact ⟨neg i,pos i,Or.inr (by simp [a,b,hi])⟩
      · let k : Fin 9 := ⟨j.val,last⟩
        by_cases six : k = 6
        · have j6 : (⟨j.val,last⟩ : Fin 9) = 6 := six
          simp only [wire,last,↓reduceDIte,same,ite_false,erase,j6,ite_true,Bool.not_false]
          exact ⟨constants false,constants true,Or.inl ⟨false,fun _ => rfl⟩⟩
        · change (⟨j.val,last⟩ : Fin 9) ≠ 6 at six
          simp only [wire,last,↓reduceDIte,same,ite_false,erase,six]
          exact ⟨pos k,neg k,Or.inr (by simp [a,b,six])⟩
    · simp [wire,last,erase,a,b]
      exact ⟨pos 0,neg 0⟩
  have mapped (x : Fin 9 → Bool) : v.map (fun t => t.1 x) = pins i (erase x) := by
    rw [← pinList]; simp only [v,List.map_ofFn]; rfl
  have lo : v.map (fun t => t.2.1) = pins i a := by
    rw [← pinList]; simp only [v,List.map_ofFn]; rfl
  have hi : v.map (fun t => t.2.2) = pins i b := by
    rw [← pinList]; simp only [v,List.map_ofFn]; rfl
  have varies : ¬∃ bit : Bool, ∀ x : Fin 9 → Bool, C.eval (v.map fun t => t.1 x) = bit := by
    rintro ⟨bit,values⟩
    have h0 := values (fun _ => false)
    have h1 := values (fun _ => true)
    rw [mapped,correct] at h0 h1
    change false = bit at h0
    change true = bit at h1
    exact Bool.false_ne_true (h0.trans h1.symm)
  have sens : C.eval (v.map fun t => t.2.1) ≠ C.eval (v.map fun t => t.2.2) := by
    rw [lo,hi,correct,correct]
    decide
  obtain ⟨p,o,cost,computes⟩ := slice (Fin 9 → Bool) C hc s v constants data varies sens
  obtain ⟨x,miss⟩ := lower p o (by omega)
  have pool : s.map (fun f => f x) = [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not := by
    simp only [s,raws,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  have matched := computes x
  rw [pool,mapped,correct] at matched
  apply miss
  apply matched.trans
  simp [graph,erase]

end PEqualNP.Outside.L_meta_3248_aux

open PEqualNP.Outside.L_meta_3248_aux

theorem PEqualNP.Outside.L_meta_3248 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval ((List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ))]).set ↑x2 !x8 x2) ≠ x1 x8 :=
  SignedPetersen.combine PetersenBinaryBudget.strict PetersenSignedSlice.compile SignedPetersen.noEleven
