import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12595

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def free (m : ℕ) (S : Finset ℕ) (v : ℕ) : Prop := v = 0 ∨ v = m ∨ v ∈ S

def comb (m : ℕ) (o : Fin 3) (a b : ℕ) : ℕ :=
  if o = 0 then a &&& b else if o = 1 then a ||| b else m ^^^ a

def Can (m f : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => free m S f
  | k+1, S => ∃ (o : Fin 3) (a b : ℕ), free m S a ∧ free m S b ∧ Can m f k (insert (comb m o a b) S)

theorem freeMono {m v : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hv : free m S v) : free m T v :=
  hv.imp_right (Or.imp_right (fun e => h e))

theorem monoC {m f k : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hc : Can m f k S) : Can m f k T := by
  induction k generalizing S T with
  | zero => exact freeMono h hc
  | succ k ih =>
    obtain ⟨o,a,b,ha,hb,hh⟩ := hc
    exact ⟨o,a,b,freeMono h ha,freeMono h hb,ih (Finset.insert_subset_insert _ h) hh⟩

theorem stepUp {m f k : ℕ} {S : Finset ℕ} (hc : Can m f k S) : Can m f (k+1) S :=
  ⟨0,0,0,Or.inl rfl,Or.inl rfl,monoC (Finset.subset_insert _ _) hc⟩

theorem small {m f k : ℕ} {S : Finset ℕ} (hc : Can m f k S) :
    ∃ T ⊆ S, T.card ≤ k+1 ∧ Can m f k T := by
  induction k generalizing S with
  | zero =>
    rcases hc with h | h | h
    · exact ⟨∅,by simp,by simp,Or.inl h⟩
    · exact ⟨∅,by simp,by simp,Or.inr (Or.inl h)⟩
    · exact ⟨{f},by simpa,by simp,Or.inr (Or.inr (by simp))⟩
  | succ k ih =>
    obtain ⟨o,a,b,ha,hb,hh⟩ := hc
    let v := comb m o a b
    obtain ⟨T,hT,hn,hc'⟩ := ih hh
    change T ⊆ insert v S at hT
    by_cases hv : v ∈ T
    · let U := T.erase v ∪ ({a,b} ∩ S)
      have hu : T.erase v ⊆ S := by
        intro x hx
        exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
      have hU : U ⊆ S := Finset.union_subset hu Finset.inter_subset_right
      have liftWire : ∀ w ∈ ({a,b} : Finset ℕ), free m S w → free m U w := by
        intro w hw he
        exact he.imp_right (Or.imp_right (fun h => Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hw,h⟩)))
      have hcard := Finset.card_union_le (T.erase v) ({a,b} ∩ S)
      have hpair := Finset.card_le_card (Finset.inter_subset_left : ({a,b} ∩ S) ⊆ {a,b})
      have htwo : ({a,b} : Finset ℕ).card ≤ 2 := by
        calc
          _ ≤ ({b} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
          _ = _ := by simp
      rw [Finset.card_erase_of_mem hv] at hcard
      refine ⟨U,hU,by dsimp [U]; omega,o,a,b,liftWire a (by simp) ha,liftWire b (by simp) hb,monoC ?_ hc'⟩
      intro x hx
      by_cases e : x = v
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hx⟩)))
    · refine ⟨T,?_,by omega,stepUp hc'⟩
      intro x hx
      exact (Finset.mem_insert.mp (hT hx)).resolve_left (fun e => hv (e ▸ hx))

theorem agreeC {m f k p q : ℕ} {S : Finset ℕ} (hc : Can m f k S)
    (hm : m.testBit p = m.testBit q) (hs : ∀ v ∈ S, Nat.testBit v p = Nat.testBit v q) :
    f.testBit p = f.testBit q := by
  have w {v} (hv : free m S v) : Nat.testBit v p = Nat.testBit v q := by
    rcases hv with rfl | rfl | h
    · simp
    · exact hm
    · exact hs _ h
  induction k generalizing S with
  | zero => exact w hc
  | succ k ih =>
    obtain ⟨o,a,b,ha,hb,hh⟩ := hc
    have hg : (comb m o a b).testBit p = (comb m o a b).testBit q := by
      unfold comb
      fin_cases o <;> simp [Nat.testBit_xor,w ha,w hb,hm]
    apply ih hh
    all_goals first
      | intro v hv; rcases Finset.mem_insert.mp hv with rfl | h; exact hg; exact hs _ h
      | intro v hv; rcases hv with rfl | rfl | h; simp; exact hm; rcases Finset.mem_insert.mp h with rfl | h; exact hg; exact hs _ h

def gt (M : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, [] => M
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | GateOp.not, [] => M
  | GateOp.not, a :: _ => M ^^^ a
  | _, _ => 0


def tstep (M : ℕ) (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gt M g.op (g.inputs.map fun i => T.getD i 0)]


def tabs (M : ℕ) (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (tstep M) T0


def GOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem gt_testBit (M p : ℕ) (hM : M.testBit p = true) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List ℕ)
    (hl : l.length ≤ 2) :
    (gt M op l).testBit p = op.eval (l.map fun t => t.testBit p) := by
  match l, hl with
  | [], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, hM]
  | [a], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, Nat.testBit_xor, hM]
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h <;>
      simp [gt, GateOp.eval, Nat.testBit_xor, hM]

theorem getD_map_testBit (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]


theorem wires_tabs (M p : ℕ) (hM : M.testBit p = true) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOk g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p)
        = (tabs M T0 gs).map fun t => t.testBit p := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p).getD i false)]
        = (tstep M T0 g).map fun t => t.testBit p := by
      simp only [tstep, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gt_testBit M p hM g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBit T0 p i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))


theorem getWire (T : List ℕ) (i : ℕ) (m : ℕ) : free m T.toFinset (T.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : T[i]? with
  | none => exact Or.inl rfl
  | some t => exact Or.inr (Or.inr (List.mem_toFinset.mpr (List.mem_of_getElem? h)))

theorem gateChoice (m : ℕ) (T : List ℕ) (g : Gate) (hg : GOk g) :
    ∃ (o : Fin 3) (a b : ℕ), free m T.toFinset a ∧ free m T.toFinset b ∧
      gt m g.op (g.inputs.map fun i => T.getD i 0) = comb m o a b := by
  obtain ⟨hop,hl⟩ := hg
  generalize g.inputs = ins at hl ⊢
  have z : free m T.toFinset 0 := Or.inl rfl
  have u : free m T.toFinset m := Or.inr (Or.inl rfl)
  match ins, hl with
  | [], _ =>
    rcases hop with h | h | h <;> rw [h]
    · exact ⟨1,m,0,u,z,by simp [gt,comb]⟩
    · exact ⟨1,0,0,z,z,rfl⟩
    · exact ⟨1,m,0,u,z,by simp [gt,comb]⟩
  | [i], _ =>
    rcases hop with h | h | h <;> rw [h]
    · exact ⟨1,_,0,getWire T i m,z,by simp [gt,comb]⟩
    · exact ⟨1,_,0,getWire T i m,z,by simp [gt,comb]⟩
    · exact ⟨2,_,0,getWire T i m,z,rfl⟩
  | [i,j], _ =>
    rcases hop with h | h | h <;> rw [h]
    · exact ⟨0,_,_,getWire T i m,getWire T j m,rfl⟩
    · exact ⟨1,_,_,getWire T i m,getWire T j m,rfl⟩
    · exact ⟨2,_,_,getWire T i m,getWire T j m,rfl⟩

theorem fromTabs (m f : ℕ) (gs : List Gate) (T : List ℕ) (ok : ∀ g ∈ gs, GOk g)
    (h : free m (tabs m T gs).toFinset f) : Can m f gs.length T.toFinset := by
  induction gs generalizing T with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨o,a,b,ha,hb,e⟩ := gateChoice m T g (ok g (by simp))
    have hh := ih (tstep m T g) (fun g' hg' => ok _ (by simp [hg'])) h
    refine ⟨o,a,b,ha,hb,?_⟩
    rw [← e]
    simpa [tstep] using hh

def cuts : ℕ → List ℕ → List (List ℕ)
  | _, [] => [[]]
  | k, x :: xs => if (x :: xs).length ≤ k then [x :: xs] else
      match k with
      | 0 => [[]]
      | j+1 => (cuts j xs).map (x :: ·) ++ cuts (j+1) xs
termination_by _ l => l.length

theorem cutsSpec (k : ℕ) (l : List ℕ) (T : Finset ℕ) (h : T ⊆ l.toFinset) (n : T.card ≤ k) :
    ∃ U ∈ cuts k l, T ⊆ U.toFinset := by
  induction l generalizing k T with
  | nil => exact ⟨[],by simp [cuts],h⟩
  | cons x xs ih =>
    cases k with
    | zero =>
      have he : T = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨[],by simp [cuts],by simp [he]⟩
    | succ j =>
      rw [cuts]
      split
      · exact ⟨_,by simp,h⟩
      ·
        by_cases hx : x ∈ T
        · have hs : T.erase x ⊆ xs.toFinset := by
            intro y hy
            have hh := h (Finset.mem_of_mem_erase hy)
            simpa [Finset.ne_of_mem_erase hy] using hh
          obtain ⟨U,hU,sub⟩ := ih j (T.erase x) hs (by rw [Finset.card_erase_of_mem hx]; omega)
          refine ⟨x::U,List.mem_append_left _ (List.mem_map.mpr ⟨U,hU,rfl⟩),?_⟩
          intro y hy
          by_cases e : y = x
          · simp [e]
          · simpa [e] using sub (Finset.mem_erase.mpr ⟨e,hy⟩)
        · have hs : T ⊆ xs.toFinset := by
            intro y hy
            have e : y ≠ x := fun he => hx (he ▸ hy)
            simpa [e] using h hy
          obtain ⟨U,hU,sub⟩ := ih (j+1) T hs n
          exact ⟨U,List.mem_append_right _ hU,sub⟩

def mask (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => (v ^^^ (v >>> d)) ||| mask d vs

theorem maskFalse {d i : ℕ} {l : List ℕ} (h : (mask d l).testBit i = false) :
    ∀ v ∈ l, Nat.testBit v i = Nat.testBit v (d+i) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [mask,Nat.testBit_lor,Nat.testBit_xor,Nat.testBit_shiftRight,Bool.or_eq_false_iff] at h
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · have hh := h.1
      revert hh
      cases v.testBit i <;> cases v.testBit (d+i) <;> decide
    · exact ih h.2 v hv

theorem covered {m f k d : ℕ} {l : List ℕ} (hc : Can m f k l.toFinset)
    (hp : ∀ i < d, m.testBit i = m.testBit (d+i) ∧ f.testBit i ≠ f.testBit (d+i)) :
    mask d l &&& (2^d-1) = 2^d-1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < d
  · have hh : (mask d l).testBit i = true := by
      cases e : (mask d l).testBit i with
      | true => rfl
      | false =>
        exact False.elim ((hp i h).2 (agreeC hc (hp i h).1 (fun v hv => maskFalse e v (List.mem_toFinset.mp hv))))
    simp [h,hh]
  · simp [h]

def upPairs (f : ℕ → ℕ → ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: t => (a :: t).map (f a) ++ upPairs f t

theorem mem_upPairs (f : ℕ → ℕ → ℕ) (hf : ∀ x y, f x y = f y x) :
    ∀ (l : List ℕ) (a b : ℕ), a ∈ l → b ∈ l → f a b ∈ upPairs f l
  | [], a, b, ha, _ => by simp at ha
  | x :: t, a, b, ha, hb => by
    simp only [upPairs, List.mem_append, List.mem_map]
    rcases List.mem_cons.mp ha with h | ha'
    · subst h
      exact Or.inl ⟨b, hb, rfl⟩
    · rcases List.mem_cons.mp hb with h | hb'
      · subst h
        exact Or.inl ⟨a, List.mem_cons_of_mem _ ha', hf _ _⟩
      · exact Or.inr (mem_upPairs f hf t a b ha' hb')

/-- The values one gate can add: AND and OR of two available wires (each unordered pair once), NOT of one. -/
def vals (m : ℕ) (S : List ℕ) : List ℕ :=
  let w := 0 :: m :: S
  (upPairs (fun x y => x &&& y) w ++ upPairs (fun x y => x ||| y) w ++ w.map (m ^^^ ·)).eraseDups

theorem memVals {m a b : ℕ} {S : List ℕ} (o : Fin 3) (ha : free m S.toFinset a)
    (hb : free m S.toFinset b) : comb m o a b ∈ vals m S := by
  have toMem {w} (h : free m S.toFinset w) : w ∈ 0 :: m :: S := by simpa [free] using h
  have ha' := toMem ha
  have hb' := toMem hb
  simp only [vals,List.mem_eraseDups,List.mem_append,List.mem_map]
  fin_cases o
  · exact Or.inl (Or.inl (mem_upPairs _ Nat.land_comm _ _ _ ha' hb'))
  · exact Or.inl (Or.inr (mem_upPairs _ Nat.lor_comm _ _ _ ha' hb'))
  · exact Or.inr ⟨a,ha',rfl⟩

def verify (d m k : ℕ) (S : List ℕ) (nextLevel : List (List ℕ)) : Bool :=
  (vals m S).all fun v =>
    (cuts (k+1) (if v ∈ S then S else v::S)).all fun U =>
      (mask d U &&& (2^d-1) != 2^d-1) || nextLevel.any (fun V => U.all (fun x => V.contains x))

theorem advance {d m f k : ℕ} {S : List ℕ} {N : List (List ℕ)}
    (hp : ∀ i < d, m.testBit i = m.testBit (d+i) ∧ f.testBit i ≠ f.testBit (d+i))
    (hv : verify d m k S N = true) (hc : Can m f (k+1) S.toFinset) :
    ∃ V ∈ N, Can m f k V.toFinset := by
  obtain ⟨o,a,b,ha,hb,hh⟩ := hc
  let v := comb m o a b
  have hg := List.all_eq_true.mp hv v (memVals o ha hb)
  let l := if v ∈ S then S else v::S
  have eqn : l.toFinset = insert v S.toFinset := by
    dsimp [l]
    split
    · rename_i h
      simp [Finset.insert_eq_of_mem (List.mem_toFinset.mpr h)]
    · simp
  obtain ⟨T,hT,hn,ht⟩ := small hh
  obtain ⟨U,hU,hu⟩ := cutsSpec (k+1) l T (eqn ▸ hT) hn
  have hcU := monoC hu ht
  have htest := List.all_eq_true.mp hg U hU
  have hcov := covered hcU hp
  simp only [hcov,bne_self_eq_false,Bool.false_or,List.any_eq_true] at htest
  obtain ⟨V,hV,hsub⟩ := htest
  refine ⟨V,hV,monoC ?_ hcU⟩
  intro x hx
  exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (List.all_eq_true.mp hsub _ (List.mem_toFinset.mp hx)))



/-! Symmetry: a permutation of the points that maps each separated pair onto a pair preserves `Can`. -/
def ofBitsL : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (ofBitsL l)

theorem testBit_ofBitsL : ∀ (l : List Bool) (j : ℕ), (ofBitsL l).testBit j = l.getD j false
  | [], j => by simp [ofBitsL]
  | b :: l, 0 => by simp [ofBitsL]
  | b :: l, j+1 => by simp [ofBitsL, Nat.testBit_bit_succ, testBit_ofBitsL l j]

def pb (N : ℕ) (t : List ℕ) (a : ℕ) : ℕ := ofBitsL ((List.range N).map fun j => a.testBit (t.getD j 0))

theorem testBit_pb (N : ℕ) (t : List ℕ) (a j : ℕ) :
    (pb N t a).testBit j = (decide (j < N) && a.testBit (t.getD j 0)) := by
  unfold pb
  rw [testBit_ofBitsL]
  by_cases h : j < N
  · simp [h, List.getD_eq_getElem?_getD]
  · simp [h, List.getD_eq_getElem?_getD]

def tauOK (d : ℕ) (t : List ℕ) : Bool :=
  (List.range d).all fun i =>
    (decide (t.getD i 0 < d) && t.getD (d+i) 0 == t.getD i 0 + d) ||
    (decide (t.getD (d+i) 0 < d) && t.getD i 0 == t.getD (d+i) 0 + d)

theorem tauOK_spec {d : ℕ} {t : List ℕ} (h : tauOK d t = true) (i : ℕ) (hi : i < d) :
    (t.getD i 0 < d ∧ t.getD (d+i) 0 = t.getD i 0 + d) ∨
    (t.getD (d+i) 0 < d ∧ t.getD i 0 = t.getD (d+i) 0 + d) := by
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa using this

theorem tauOK_range {d : ℕ} {t : List ℕ} (h : tauOK d t = true) (j : ℕ) (hj : j < 2*d) :
    t.getD j 0 < 2*d := by
  by_cases hjd : j < d
  · rcases tauOK_spec h j hjd with ⟨a, _⟩ | ⟨_, b⟩ <;> omega
  · have e : j = d + (j - d) := by omega
    rw [e]
    rcases tauOK_spec h (j-d) (by omega) with ⟨_, b⟩ | ⟨a, _⟩ <;> omega

section
variable {N m : ℕ} {t : List ℕ} (hm : ∀ j, m.testBit j = decide (j < N)) (ht : ∀ j < N, t.getD j 0 < N)
include hm ht

theorem pb_zero : pb N t 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; simp [testBit_pb]

theorem pb_m : pb N t m = m := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_pb, hm j]
  by_cases h : j < N
  · rw [hm (t.getD j 0)]
    have htj := ht j h
    simp only [List.getD_eq_getElem?_getD] at htj
    simp [h, htj]
  · simp [h]

theorem pb_comb (o : Fin 3) (a b : ℕ) : pb N t (comb m o a b) = comb m o (pb N t a) (pb N t b) := by
  apply Nat.eq_of_testBit_eq; intro j
  unfold comb
  by_cases h : j < N
  · have htj := ht j h
    simp only [List.getD_eq_getElem?_getD] at htj
    fin_cases o <;> simp [testBit_pb, Nat.testBit_land, Nat.testBit_lor, Nat.testBit_xor, h, hm, htj]
  · fin_cases o <;> simp [testBit_pb, Nat.testBit_land, Nat.testBit_lor, Nat.testBit_xor, h, hm]

theorem canPb : ∀ (k : ℕ) (f : ℕ) (S : Finset ℕ), Can m f k S → Can m (pb N t f) k (S.image (pb N t))
  | 0, f, S, hc => by
    rcases hc with rfl | rfl | h
    · exact Or.inl (pb_zero hm ht)
    · exact Or.inr (Or.inl (pb_m hm ht))
    · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ h))
  | k+1, f, S, hc => by
    obtain ⟨o, a, b, ha, hb, hh⟩ := hc
    have fr : ∀ v, free m S v → free m (S.image (pb N t)) (pb N t v) := by
      intro v hv
      rcases hv with rfl | rfl | h
      · exact Or.inl (pb_zero hm ht)
      · exact Or.inr (Or.inl (pb_m hm ht))
      · exact Or.inr (Or.inr (Finset.mem_image_of_mem _ h))
    refine ⟨o, pb N t a, pb N t b, fr a ha, fr b hb, ?_⟩
    have := canPb k f _ hh
    rwa [Finset.image_insert, pb_comb hm ht] at this
end

/-- Hinted check modulo symmetries: a hint `h` names the set `h / G` of the next level and the
permutation `h % G`, whose image of the cut must lie in that set. -/
def chkS (d : ℕ) (Ts : List (List ℕ)) (N : List (List ℕ)) : List (List ℕ) → List ℕ → Bool
  | [], _ => true
  | U :: Us, hs =>
    if (mask d U &&& (2^d-1) != 2^d-1) = true then chkS d Ts N Us hs
    else match hs with
      | [] => false
      | h :: hs' => (decide (h / Ts.length < N.length) &&
          (if h % Ts.length = 0 then U.all (fun x => (N.getD (h / Ts.length) []).contains x)
           else (U.map (pb (2*d) (Ts.getD (h % Ts.length) []))).all
             (fun x => (N.getD (h / Ts.length) []).contains x)))
          && chkS d Ts N Us hs'

theorem chkS_sound {d : ℕ} {Ts : List (List ℕ)} {N : List (List ℕ)} (hT : 0 < Ts.length) :
    ∀ (Us : List (List ℕ)) (hs : List ℕ), chkS d Ts N Us hs = true → ∀ U ∈ Us,
      (mask d U &&& (2^d-1) != 2^d-1) = true ∨ (∃ V ∈ N, ∀ x ∈ U, x ∈ V) ∨
      ∃ t ∈ Ts, ∃ V ∈ N, ∀ x ∈ U, pb (2*d) t x ∈ V := by
  intro Us
  induction Us with
  | nil => intro hs _ U hU; simp at hU
  | cons U0 Us ih =>
    intro hs h U hU
    unfold chkS at h
    by_cases hc : (mask d U0 &&& (2^d-1) != 2^d-1) = true
    · rw [if_pos hc] at h
      rcases List.mem_cons.mp hU with rfl | hU
      · exact Or.inl hc
      · exact ih hs h U hU
    · rw [if_neg hc] at h
      cases hs with
      | nil => simp at h
      | cons h0 hs' =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hlt, hall⟩, hrest⟩ := h
        rcases List.mem_cons.mp hU with rfl | hU
        · right
          have hV : N.getD (h0 / Ts.length) [] ∈ N := by
            rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
          split at hall
          · left
            refine ⟨_, hV, fun x hx => ?_⟩
            exact List.contains_iff_mem.mp (List.all_eq_true.mp hall x hx)
          · right
            have hs : h0 % Ts.length < Ts.length := Nat.mod_lt _ hT
            refine ⟨Ts.getD (h0 % Ts.length) [], ?_, _, hV, ?_⟩
            · rw [List.getD_eq_getElem _ _ hs]; exact List.getElem_mem hs
            · intro x hx
              exact List.contains_iff_mem.mp (List.all_eq_true.mp hall _ (List.mem_map_of_mem hx))
        · exact ih hs' hrest U hU

def verifyS (d m k : ℕ) (Ts : List (List ℕ)) (S : List ℕ) (N : List (List ℕ)) (H : List ℕ) : Bool :=
  chkS d Ts N ((vals m S).flatMap fun v => cuts (k+1) (if v ∈ S then S else v::S)) H

theorem advanceS {d m f k : ℕ} {Ts : List (List ℕ)} {S : List ℕ} {N : List (List ℕ)} {H : List ℕ}
    (hT : 0 < Ts.length) (hTs : Ts.all (tauOK d) = true)
    (hm : ∀ j, m.testBit j = decide (j < 2*d))
    (hp : ∀ i < d, m.testBit i = m.testBit (d+i) ∧ f.testBit i ≠ f.testBit (d+i))
    (hv : verifyS d m k Ts S N H = true) (hc : Can m f (k+1) S.toFinset) :
    ∃ V ∈ N, ∃ f' : ℕ, (∀ i < d, m.testBit i = m.testBit (d+i) ∧ f'.testBit i ≠ f'.testBit (d+i)) ∧
      Can m f' k V.toFinset := by
  obtain ⟨o,a,b,ha,hb,hh⟩ := hc
  let v := comb m o a b
  let l := if v ∈ S then S else v::S
  have eqn : l.toFinset = insert v S.toFinset := by
    dsimp [l]
    split
    · rename_i h
      simp [Finset.insert_eq_of_mem (List.mem_toFinset.mpr h)]
    · simp
  obtain ⟨T,hT',hn,ht⟩ := small hh
  obtain ⟨U,hU,hu⟩ := cutsSpec (k+1) l T (eqn ▸ hT') hn
  have hcU := monoC hu ht
  have hcov := covered hcU hp
  have hmemU : U ∈ (vals m S).flatMap fun v => cuts (k+1) (if v ∈ S then S else v::S) :=
    List.mem_flatMap.mpr ⟨v, memVals o ha hb, hU⟩
  rcases chkS_sound hT _ _ hv U hmemU with hc | ⟨V, hV, hsub⟩ | ⟨t, htm, V, hV, hsub⟩
  · simp [hcov] at hc
  · refine ⟨V, hV, f, hp, monoC ?_ hcU⟩
    intro x hx
    exact List.mem_toFinset.mpr (hsub x (List.mem_toFinset.mp hx))
  · have hok := List.all_eq_true.mp hTs t htm
    have hrange : ∀ j < 2*d, t.getD j 0 < 2*d := tauOK_range hok
    refine ⟨V, hV, pb (2*d) t f, ?_, ?_⟩
    · intro i hi
      refine ⟨(hp i hi).1, ?_⟩
      rw [testBit_pb, testBit_pb]
      simp only [show i < 2*d by omega, show d + i < 2*d by omega, decide_true, Bool.true_and]
      rcases tauOK_spec hok i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, Nat.add_comm]; exact (hp _ h1).2
      · rw [h2, Nat.add_comm]; exact fun e => (hp _ h1).2 e.symm
    · have := canPb hm hrange k f _ hcU
      refine monoC ?_ this
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact List.mem_toFinset.mpr (hsub y (List.mem_toFinset.mp hy))

theorem rowsS_ok {d m k : ℕ} {Ts : List (List ℕ)} {N : List (List ℕ)} : ∀ (R HS : List (List ℕ)),
    R.length = HS.length → (R.zip HS).all (fun p => verifyS d m k Ts p.1 N p.2) = true →
      ∀ S ∈ R, ∃ H, verifyS d m k Ts S N H = true
  | [], _, _, _ => by simp
  | S :: R, H :: HS, hl, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    intro S' hS'
    rcases List.mem_cons.mp hS' with rfl | hS'
    · exact ⟨H, h.1⟩
    · exact rowsS_ok R HS (by simpa using hl) h.2 S' hS'
  | _ :: _, [], hl, _ => by simp at hl

abbrev width : ℕ := 41
abbrev topMask : ℕ := 4835703278458516698824703
abbrev targetBits : ℕ := 2199023255551
def inputs : List ℕ := [157323436099379621261823,1871942268818151247236671,54310535542143998431175,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472]
def taus : List (List ℕ) := [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81], [0,1,2,3,4,5,6,7,8,9,10,11,26,27,28,29,30,31,32,33,34,35,36,37,38,39,12,13,14,15,16,17,18,19,20,21,22,23,24,25,40,41,42,43,44,45,46,47,48,49,50,51,52,67,68,69,70,71,72,73,74,75,76,77,78,79,80,53,54,55,56,57,58,59,60,61,62,63,64,65,66,81], [3,4,5,0,1,2,6,8,7,9,11,10,12,13,14,15,21,22,23,24,25,16,17,18,19,20,26,27,28,29,35,36,37,38,39,30,31,32,33,34,40,44,45,46,41,42,43,47,49,48,50,52,51,53,54,55,56,62,63,64,65,66,57,58,59,60,61,67,68,69,70,76,77,78,79,80,71,72,73,74,75,81], [3,4,5,0,1,2,6,8,7,9,11,10,26,27,28,29,35,36,37,38,39,30,31,32,33,34,12,13,14,15,21,22,23,24,25,16,17,18,19,20,40,44,45,46,41,42,43,47,49,48,50,52,51,67,68,69,70,76,77,78,79,80,71,72,73,74,75,53,54,55,56,62,63,64,65,66,57,58,59,60,61,81]]
def row1_0 : List (List ℕ) := [
]
def row1 : List (List ℕ) := [row1_0].flatten
def row2_0 : List (List ℕ) := [
[157323436099379621261823,1246780851073073236676159,1404104287170253834682431],
[157323436099379621261823,3431598991288262864142272,3588922427385443462148544],
[1246780851073073236676159,3431598991288262864142272,4678379842359137077562880],
[157323436099379621261823,1246780851073073236676159,3431598991288262864142272]]
def row2 : List (List ℕ) := [row2_0].flatten
def row3_0 : List (List ℕ) := [
[157323436099379621261823,1871942268818151247236671,4403580365855643729457208,4791723551289103727198200],
[157323436099379621261823,1246780851073073236676159,3474102888780621687029703,4791723551289103727198200],
[157323436099379621261823,1208999608861278144040504,3431598990021625468940288,4797922034980084210987064],
[54310535542143998431175,1246780852339925259124224,1737936938328207229194232,1871942268818151247236671],
[157323436099379621261823,1737936938328207229194232,1850690319936705060389368,3431598990021625468940288],
[157323436099379621261823,1871942268818151247236671,3043455805854802866401280,3431598991288262864142272],
[1749743575111355009535992,1871942268818151247236671,3474102888780621687029703,4678379842359137077562880],
[157323436099379621261823,1792247472603713832423423,2963761009640365451588032,3431598991288262864142272],
[1246780851073073236676159,2417913510948676139220928,3431537119569944585961472,4678379842359137077562880],
[157323436099379621261823,1361600389677895011795000,1749743575111355009535992,1871942268818151247236671]]
def row3_1 : List (List ℕ) := [
[157323436099379621261823,1749743575111355009535992,1871942268818151247236671,3474102888780621687029703],
[54310535542143998431175,157323436099379621261823,780123527595927826907584,1737936938328207229194232],
[157323436099379621261823,1246780851073073236676159,2417913509682038744018944,3431537120836581981163456],
[23059696729597153216,157323436099379621261823,1246780851073073236676159,3431598990021625468940288],
[157323436099379621261823,1246780851073073236676159,3431537120836581981163456,3431598991288262864142272],
[37781242211795092639239,157323436099379621261823,1208999610127915539238904,3431598990021625468940288],
[37781242211795092639239,157323436099379621261823,1208999608861278144040952,3431598990021625468940288],
[37781242211795092639239,1208999610127915539238904,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,1871942268818151247236671,3242692806312185720209912,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,2808798901055940013899839,3431598990021625468940288]]
def row3_2 : List (List ℕ) := [
[37781242211795092639239,157323436099379621261823,1208999610127915539238904,1404104288436891229884415],
[157323436099379621261823,1246780851073073236676159,1871942268818151247236671,3431598991288262864142272],
[157323436099379621261823,2417913510948676139220928,3431537119569944585961472,3588922427385443462148544],
[1180663757477091786815,54310535542143998431175,623980753989799942025216,1360124560001906079961080],
[54310535543347602259911,1737936938328207229194232,1871942268819357267131967,3588922426119798264951295],
[157323436099379621261823,1775718180540002321829887,1871942268818151247236671,3431598991288262864142272],
[37781242211795092639239,157323436099379621261823,1208999608861278144040504,3431598991288262864142272],
[157323436099379621261823,1246780851073073236676159,3431537119569944585961472,3431598991288262864142272],
[157323436099379621261823,1246780851073073236676159,1404166157621934717661247,2417913509682038744018944],
[157323436099379621261823,377812378327366366138304,1246780851073073236676159,3431598990021625468940288]]
def row3_3 : List (List ℕ) := [
[157323436099379621261823,1246780851073073236676159,2417789768776477954805759,3431537120836581981163456],
[157323436099379621261823,1737936938328207229194232,2985012958521811638435335,3431598990021625468940288],
[1266637395201984,157323436099379621261823,3431598990021625468940288,3588922427385443462148544],
[1266637395201984,157323436099379621261823,1246780851073073236676159,3431598990021625468940288],
[157323436099379621261823,1246780851073073236676159,2429719427155883538251712,3431537119569944585961472],
[157323436099379621261823,1246780851073073236676159,2417913510948676139220928,3431537120836581981163456],
[1792247472603713832423423,1871942268818151247236671,3431598991288262864142272,4678379842359137077562880],
[157323436099379621261823,1246780851073073236676159,1737936938328207229194232,3431598991288262864142272],
[202188661080329583132216,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[37781243478432487837639,157323436099379621261823,3431598990021625468940288,3626703669597238554784199]]
def row3_4 : List (List ℕ) := [
[157323436099379621261823,1749743575111355009535992,2963761009640365451588032,3474102888780621687029703],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3588922426118591439700479],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,4055579750862588871917119],
[54310535543347602259911,1737936938329310968938488,1871942268818151247236671,3588922426119798264951295],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431598991288262864142272],
[157323436099379621261823,1792247471337076437221439,1871942268818151247236671,3431598990021625468940288],
[157323436099379621261823,1246780851073073236676159,3431537120836581981163456,3431598990021625468940288],
[157323436099379621261823,1871942268818151247236671,3043455807121440261603264,3431598990021625468940288],
[157323436099379621261823,1246780851073073236676159,1792247472603713832423423,3431598991288262864142272],
[54310535542143998431175,1737936938328207229194232,2026904377402576684924864,3431598990021625468940288]]
def row3_5 : List (List ℕ) := [
[1266637395201984,157323436099379621261823,1246780851073073236676159,3431598991288262864142272],
[1266637395201984,157323436099379621261823,1246780851073073236676159,1404104288436891229884415],
[1266637395201984,1246780851073073236676159,3431598990021625468940288,4678379842359137077562880],
[157323436099379621261823,1246780851073073236676159,3431598990021625468940288,3431598991288262864142272],
[157323436099379621261823,1404104287170253834682431,1792247472603713832423423,1871942268818151247236671],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3462296251997473906687943],
[157323436099379621261823,1246780851073073236676159,3431598990021625468940288,4835703277191879303622719],
[54310535542143998431175,157323436099379621261823,421792104230141942562823,1871942268818151247236671],
[157323436099379621261823,432122912603973487689671,1871942268818151247236671,4791723551289103727198200]]
def row3 : List (List ℕ) := [row3_0, row3_1, row3_2, row3_3, row3_4, row3_5].flatten
def row4_0 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598991288262864138240],
[54310535542143998431175,1871942268818151247236671,3431598990021625468940288,4155788577558565090234360,4678379842359137077562880],
[54310535543243510058951,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250758864447,3431598990021625468940288],
[54310535542143998431175,2963761009640365451588032,3097766340130309469630471,3431598990021625468940288,4678379842359137077562880],
[157323436099379621261823,1737936938329310968680440,1871942268818151247236671,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,1404104288436891229884415,1737936938328207229194232,2963761009640365451588032,4678379842359137077562880],
[1206825250816,54310535542143998431175,781304190087972738036223,1737936938328207229194232,1871942268818151247236671],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2850122134790855033032647,3431598990021625468940288]]
def row4_1 : List (List ℕ) := [
[54310535542143998431175,1737936938328207229194232,1871942268819357260631615,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1247961514829557325106751,1737936938328207229194232,2028085042425485152014335],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2850099067354766433521607,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431560179266674183114688,4155827389580153771261944],
[157323436099379621261823,1737936938328207229194232,1792247472603713832423423,1871942268818151247236671,3431598991288262864142272],
[4722655280597018280391,206911316360926601412607,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431598990021625468940288,4155789298134505471545336],
[54310535542143998431175,623980753989799942025216,1737936938328207229194232,1871942268818151247236671,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431575202008393697980416],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4793199380966124587905080]]
def row4_2 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097789398560401671581703,3431575931591533266989056],
[43979727169412971626503,54310535542143998431175,157323436099379621261823,377812377060728970936320,1871942268818151247236671],
[157323436099379621261823,1246780851073073236676159,1737936938328207229194232,2417913510948676139220928,3431537119569944585961472],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431537841412522362474432],
[54310535542143998431175,157323436099379621261823,1737936938328207229243384,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247187519,3431598990021625468940288],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2472604923651868854271943,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2260466332679297369898496,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1246818933511522281639487,1737936938328207229194232,3431598990021625468940288],
[1266637395201984,157323436099379621261823,1246780851073073236676159,2417913509682038744018944,3431537120836581981163456]]
def row4_3 : List (List ℕ) := [
[54333593972236200382407,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431598990021625468940288,4289793908048509114777151],
[54333593972236200382407,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3041856181232290062397440],
[11805917473844794232768,157323436099379621261823,1246780851073073236676159,2417913509682038744018944,3431537119569944585961472],
[54333593972236200382407,157323436099379621261823,1404166158888572112863231,1871942268818151247236671,4155827389580153771261944],
[1266637395201984,157323436099379621261823,1246780851073073236676159,1792247472603713832423423,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1749742854535414628225016,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,2417913509682038744018944,3431537119569944585961472,3643823289034714510474808],
[54310535543347602259911,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288]]
def row4_4 : List (List ℕ) := [
[37781242211795092639239,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598991288262864142272],
[4722655280597018280391,206911316360926601412607,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[157323436099379621261823,623980753988593922129920,1737936938328207229194232,4679560504851182794047039,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328208034549752,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938329306741080056,1871942268818151247236671,3431598990021625468940288],
[4722655281800615756231,206911316360926601412607,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,1749742854535414628225016,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542140777009095,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[16529293330378972401607,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940295]]
def row4_5 : List (List ℕ) := [
[54310535543347602259911,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,1737936938329306741080056,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[206911316360926601412607,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4830980623177919680544312],
[54310535542143998431175,157323436099379621261823,1246780851073073236676159,3431598990021625468940288,4155827389580153771261944],
[37781242211795092639239,157323436099379621261823,1208999608861278144040504,2417913509682038744018944,3431537120836581981163456],
[1266637395201984,1792247472603713832423423,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,377812377060728970936320,1871942268818151247236671,4678379842359137077562880,4791723551289103727198200],
[54310535542143998431175,157323436099379621261823,679898947308455129513991,1871942268818151247236671,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,545923664835224918606272,1737936938328207229194232,3431537119569944585961472],
[157323436099379621261823,1871942268818151247236671,2472162174772501859471303,3097766340130309469630471,3431598990021625468940288]]
def row4_6 : List (List ℕ) := [
[11806636783147780341760,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3474102888780621687029703],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913510948676139220928,3431537120836581981163456],
[54310535542143998431175,157323436099379621261823,623980753989799942025216,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3821955927667249090924543],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,4211722524469922776694783,4679560504851182794047039],
[54310535542143998431175,157323436099379621261823,545466621530640595747264,1737936938328207229194232,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1360124561268440389652472,1871942268818151247236671,3431598990021625468940288],
[1180663757477091786815,54310535542143998431175,2028085041160053776711679,3097766340130309469630471,3431598990021625468940288],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431598991288262864142272],
[37781242211795092639239,157323436099379621261823,1208999610127915539238904,2417789768776477954805759,3431537119569944585961472]]
def row4_7 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431560898575977169223680,4155827389580153771261944],
[157323436099379621261823,1737936938328207229194232,3431575202008393691480064,4289817696061740885737023,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,377812377061832710680576,1871942268818151247236671,4791723551289103727198200],
[54310535542143998431175,157323436099379621261823,1737936938329306741080056,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,667960481158147696750599,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431598990021625468940288,4155788577558565090492408],
[1206825250816,54310535542143998431175,1737936938329310968938488,1871942268818151247236671,3588922426119798264951295],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431575202008393691480064,4289817696061740885737023],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431537120836581981163456,3431598991288262864142272],
[54310535542143998431175,151124951140627935920632,1871942268818151247236671,3091567855171557784289280,3431598990021625468940288]]
def row4_8 : List (List ℕ) := [
[54310535542143998431175,157323436099379623096831,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1266637395201984,157323436099379621261823,1792247472603713832423423,2963761009640365451588032,3431598990021625468940288],
[54333593972236200382407,157323436099379621261823,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944],
[42503897492392110919623,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,1586811987187579293273600,1871942268818151247236671,3431598990021625468940288,4829504793499765013483512],
[157323436099379621261823,1737937658905247122194424,1871942268818151247236671,2472223324648242361139143,3431537119569944585961472],
[42503897492392110919623,157323436099379621261823,1360124560001906079961080,1871942268818151247236671,3431598990021625468940288],
[54333593972236200382407,157323436099379621261823,1871942268818151247236671,3431560178000036787912704,4155827389580153771261944],
[42504618068332490198983,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[42503897492392110919623,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row4_9 : List (List ℕ) := [
[54333593972236200382407,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944,4678379842359137077562880],
[1180663757477091786815,54310535542143998431175,1404104288436891229884415,1737936938328207229194232,2028085041160053776711679],
[54310535542143998431175,157323436099379621261823,623980753989799942025216,1737936938328207229194232,4289817696061740885737023],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,2400879598285080332390399,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,377812377060728970936320,2963761009640365451588032,4791723551289103727198200],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1870761605060674960805439,3431598990021625468940288],
[54310535543347602259911,157323436099379621261823,1737936938329310968938488,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,4211722524468716756799487],
[54310535542143998431175,157323436099379621261823,1737936938329310968938488,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431575202008393697980416,4289817696061740885737023]]
def row4_10 : List (List ℕ) := [
[1266637395201984,37781242211795092639239,157323436099379621261823,1208999608861278144040504,3431598990021625468940288],
[54310535542143998431175,1404104288436891229884415,1871942268818151247236671,3097766340130309469630471,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1360124561268440389652472,1404104288436891229884415,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1737936938328237295800312,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431560178000036787912704,4155827389580153771261944],
[157323436099379621261823,1246780851073073236676159,2417913509682038744018944,3431537119569944585961472,4835703277191879303622719],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431598990021625468940288,3431598991288262864142272],
[54333593972236200382407,157323436099379621261823,679875888878362927562759,1871942268818151247236671,3431537119569944585961472],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2472223324648242361139143,3431537840145884973625344],
[157323436099379621261823,1792247472603713832423423,2417913510948676139220928,2963761009640365451588032,3431537119569944585961472]]
def row4_11 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268819357260631615],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[157323436099379621261823,1749743575111355009535992,1871942268818151247236671,2472223324648242361139143,3431598990021625468940288],
[157323436099379621261823,1404166157621934717661247,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157361518537828726731263,1737936938328207229194232,1871942268818151247236671,3431537119569944592510976],
[54310535543347602259911,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1360124560001906079961080,2963761009640365451588032,3431598990021625468940288],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2472162174772501859471303,3431598990021625468940288],
[11806636783147780341760,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3474102888780621687029703],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417789768776477954805759,3431537120836581981163456]]
def row4_12 : List (List ℕ) := [
[157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288,4781392742916372700393528],
[54310535543243516411847,1737936938329306741080056,1871942268818151247236671,2575236945780318847103487,3431537119569944585961472],
[42503897492392110919623,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431575202008393697980416],
[157323436099379621261823,1775718180540002321829887,1871942268818151247236671,2417913510948676139220928,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,2795702828312675513004032,2963761009640365451588032,4791684739267515046170616],
[157323436099379621261823,1792247471337076437221439,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268819250765364799,3097766340130309469630471,3431598990021625468940288],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2363098354806647844552760,3431598990021625468940288],
[157323436099379621261823,432099854172780767416263,1871942268818151247236671,3431598990021625468940288,4791684739267515046170616],
[1180663757477091786815,54310535542143998431175,1737936938328207229194232,2028085041160053776711679,3431598990021625468940288]]
def row4_13 : List (List ℕ) := [
[37781243478432487837639,157323436099379621261823,1208999608861278144040504,2417913509682038744018944,3431598990021625468940288],
[157323436099379621261823,432122912602872969367495,1737936938328207229194232,1871942268818151247236671,4791723551289103727198200],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431575202008393697980416],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,2963761009640365451588032,3097766340130309469630471],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431598990021625468940288,4835703277191879303622719],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1871942268818151247236671,4155788577558565090234360],
[54310535542143998431175,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,1737936938329306741080056,1871942268819250765364799,2575236945780318847103487,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1208999610127915539238904,2963761009640365451588032,3431598990021625468940288],
[37781242211795092639239,157323436099379621261823,1208999610127915539238904,1737936938328207229194232,3431598990021625468940288]]
def row4_14 : List (List ℕ) := [
[157323436099379621261823,1246780851073073236676159,2417913509682038744018944,3431537119569944585961472,3431537120836581981163456],
[54310535542143998431175,157323436099379621261823,662942659956873103196167,3431598990021625468940288,4306765948991587613670975],
[42503897492392110919623,157323436099379621261823,623980753989799942025216,1737936938328207229194232,1871942268818151247236671],
[1792247472603713832423423,1871942268818151247236671,2417913510948676139220928,3431537119569944585961472,4678379842359137077562880],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2850122134792057831505863,3431598990021625468940288],
[54310535542143998431175,151124951140627935920632,1744135423286958914535423,2963761009640365451588032,3431598990021625468940288],
[1180663757477091786815,54310535542143998431175,1737936938328207229194232,2028085041160053776711679,3431575202008393697980416],
[157323436099379621261823,432122912602872969367495,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[54310535543243516411847,1737936938328207229194232,1871942268818151247236671,2575236945780318847103487,3431537119569944592510976],
[37781242211795092639239,157323436099379621261823,1737936938328207229194232,1876664924098748265517055,3431598990021625468940288]]
def row4_15 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250765364799,3431598990021625468940288],
[157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3043455805854802866401280,3431537120836581981163456],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938329310968680440,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1404128076450123000844287,1737936938328207229194232,1871942268818151247236671],
[157323436099379621261823,1246780851073073236676159,1792247472603713832423423,2417913510948676139220928,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1246780851073073236676159,1737936938328207229194232,3431598990021625468940288],
[42503898758996218089415,157323436099379621261823,1415910925220039010226175,1737936938328207229194232,1871942268818151247236671],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4781392742915169096564792],
[157323436099379621261823,1246780851073073236676159,1737936938328207229194232,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250765364799,3431575202008393691480064]]
def row4_16 : List (List ℕ) := [
[1180663758683111682111,54310535542143998431175,1737936938328207229194232,2028085041160053776711679,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,3097766340130309469630471,3431598990021625468940288,4289793908048509108276799],
[54310535542144004722631,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818150441881151,3431598990021625468940288],
[37781242211795092639239,157323436099379621261823,1208999610127915539238904,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,389619013843876751278080,1871942268818151247236671,4791723551289103727198200],
[37781242211795092639239,157323436099379621261823,1208999608861278144040952,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,623980753989799942025216,1737936938328207229194232,4679560504851182794047039],
[54310535542143998431175,156142772341902529475008,1737936938328207229194232,2964941673397842543374847,3431598990021625468940288],
[157323436099379621261823,1246780851073073236676159,2417913509682038744018944,3474041738904881185361863,4791684739267515046170616]]
def row4_17 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818154468658751,3431598990021625468940288],
[37781964054372867313607,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1180663757477091786815,54310535542143998431175,623980753989799942025216,1737936938328207229194232,2028085041160053776711679],
[157323436099379621261823,1871942268818151247236671,2472162174772501859471303,3431598990021625468940288,4155788577558565090234360],
[54310535542143998431175,151124951140627935920632,1744135423286958914535423,1871942268818151247236671,3431598990021625468940288],
[157323436099379621261823,432122912602872969367495,1871942268818151247236671,3431598990021625468940288,4791723551289103727198200],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250765364799,3431575202008393697980416],
[37781242211795092639239,157323436099379621261823,1208999610127915539238904,1888471562148500153028607,3431598990021625468940288],
[1266637395201984,157323436099379621261823,1246780851073073236676159,2417913509682038744018944,3431537119569944585961472],
[157323436099379621261823,1737936938328207229194232,2850122134792057831505863,2963761009640365451588032,3431598990021625468940288]]
def row4_18 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819357267131967,3431598990021625468940288],
[432122912602872969367495,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[157323436099379621261823,1737936938328207229194232,1888471562148500153028607,3431598990021625468940288,4797922036246721606185464],
[49587880261550201573319,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130412548845575,3431598990021625468940288],
[54310534275506603233223,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009639159431692736,3431598990021625468940288],
[54310535542143998431175,1871942268818151247236671,3431560178000036787912704,4155827389580153771261944,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207231029240,1871942268818151247236671,3431598990021625468940288],
[11806636783147780341760,157323436099379621261823,1749743575111355009535992,1871942268818151247236671,3474102888780621687029703]]
def row4_19 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,679914700899951608590343,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130412555137031,3431598990021625468940288],
[157323436099379621261823,1208999610127915539238904,1871942268818151247236671,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340129209957744647,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1871942268818151247236671,3097766340130309469630471],
[54309814966203618955207,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998234567,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,635787390772914434338816,1737936938328207229194232,1871942268818151247236671],
[37781242211795092639239,157323436099379621261823,1263310144403422142468095,1737936938328207229194232,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,3431598990021625468940288,4289793908048509108276799,4678379842359137077562880]]
def row4_20 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1834161026606386221207103,3431598990021625468940288],
[1266637395201984,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431598991288262864142272],
[157323436099379621261823,432122912602872969367495,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431537120836581981163456,3431598990021625468940288],
[37781243478432487837639,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[1266637395201984,157323436099379621261823,1246780851073073236676159,1737936938328207229194232,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1360124561268543475159032,1871942268818151247236671,3431598990021625468940288],
[37781242211795092639239,157323436099379621261823,1888471562148500153028607,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268819250765364799,2575236945780318847103487,3431537119569944592510976],
[54310535542143998431175,157323436099379621261823,377812378327366366138304,1871942268818151247236671,4791723551289103727198200]]
def row4_21 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1247961514830550328462911,1737936938328207229194232,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,2028085041160053776711679,3431598990021625468940288,4834522614701039607037888],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640366256943552,3431598990021625468940288],
[1266637395201984,157323436099379621261823,1246780851073073236676159,1404166158888572112863231,2417913509682038744018944],
[54310535542143998431175,157323436098172796011007,1404104288438098055135231,1737936938328207229194232,1871942268818151247236671],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598991288262864142272,4781392742916372700393528],
[157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,4679560504851182794047039],
[157323436099379621261823,432122912602872969367495,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310534275506603229191,157323436099379621261823,1871942268818151247236671,3097766341396946864832455,3431598990021625468940288]]
def row4_22 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1871942268819357267131967,3097766340130309469630471,3431598990021625468940288],
[37781242211795092639239,54310535542143998431175,157323436099379621261823,1208999610127915539238904,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2575236945779219328926207,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,545885582396775813087680,1737936938328207229194232,3431575202008393691480064],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247237119,3431598990021625468940288],
[54333593972236200382407,157323436099379621261823,2963761009640365451588032,3431537119569944585961472,4155827389580153771261944],
[1266637395201984,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,623980753989799942025216,1737936938328207229194232,1871942268819357267131967],
[1180663758576609914943,54310535542143998431175,1737936938328207229194232,2028085041160053776711679,3431598990021625468940288],
[54310535543347602259911,157323436099379621261823,1737936938328207229194232,1871942268819357267131967,3431598990021625468940288]]
def row4_23 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431598990021625468940288,3588922427385443462148544],
[54310535542143998431175,155847606422325472522751,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3474102888780621687029703,4823896641675368918482943],
[1180663757477091786815,42503897492392110919623,1737936938328207229194232,2028085041160053776711679,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1404104287170253834686463,1737936938328207229194232,1871942268818151247236671],
[4722655280597018280391,195104678311174713901055,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1206825250816,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3588922426119798264951295],
[54310535542143998431175,157323436099379621261823,1737936938328210450616312,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,3431575202008393691480064,4289817696061740885737023,4678379842359137077562880]]
def row4_24 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,389619013844977269600256,1737936938328207229194232,1871942268818151247236671],
[11806638049785175543744,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151253528127,3431598990021625468940288],
[54333593972236200382407,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3041856181232290062397440,4678379842359137077562880],
[157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3043455807121440261603264,3431537119569944585961472],
[157323436099379621261823,1871942268818151247236671,2417913509682038744018944,2849951493403138628456391,4791684739267515046170616],
[1206825250816,1737936938328207229194232,1871942268818151247236671,3588922426119798264951295,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1013747350791267607900160,1737936938328207229194232,1871942268818151247236671],
[54310535543243516411847,157323436099379621261823,1737936938329306741080056,1871942268818151247236671,3431598990021625468940288]]
def row4_25 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,1871942270084788642435071,3431598990021625468940288],
[1266637395201984,157323436099379621261823,2417913509682038744018944,3431537119569944585961472,3588922427385443462148544],
[16529293330348905791936,157323436099379621261823,1737936938328207229194232,3001542251852160544227271,3431598990021625468940288],
[1266637395201984,157323436099379621261823,1404104288436891229884415,1792247472603713832423423,1871942268818151247236671],
[1266637395201984,1246780851073073236676159,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[157323436099379621261823,1737936938328207229194232,2472185242209793257455559,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598991288262864142272],
[157323436099379621261823,1749743575111355009535992,1871942268818151247236671,3431537119569944585961472,3474102888780621687029703],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4781392742916372700393528],
[157323436099379621261823,1208999608861278144040504,2417913509682038744018944,3431537119569944585961472,4797922034980084210987064]]
def row4_26 : List (List ℕ) := [
[157323436099379621261823,1737936938328207229194232,2472162174772501859471303,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,156142773607333904777664,157323436099379621261823,623980753988593922129920,1737936938328207229194232],
[54310535542143998431175,157323436099379621261823,1404104287170253834682431,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431537119569944585961472,4155804331150061569310712],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913510948676139220928,3431537119569944585961472],
[42503897492392110919623,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,545909370410007590547904,1737936938328207229194232,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,2026904377402576684924864,2417913509682038744018944,3431537119569944585961472],
[37781242211795092639239,157323436099379621261823,1737936938328207229194232,2947231716310016545796096,3431598990021625468940288],
[157323436099379621261823,1246780851073073236676159,1871942268818151247236671,2417913510948676139220928,3431537119569944585961472]]
def row4_27 : List (List ℕ) := [
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3474102888780621687029703,4791723551289103727198200],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990020418643689472,4678379842360343902813696],
[54310535542143998431175,157323436099379621265407,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[157323436099379621261823,1737936938328207229194232,1749743575111355009535992,1871942268818151247236671,3474102888780621687029703],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963799092078814557106624,3431560907583176363421696],
[157323436099379621261823,1246780851073073236676159,1737936938328207229194232,3431598990021625468940288,3474102888780621687029703],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431598990021625468940288,3626703668330601159585799],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940736],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,1404104288436891229884415,2400879598285080332390399],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,4289793908048509108276799]]
def row4_28 : List (List ℕ) := [
[54310535542143998431175,623980753988593922129920,1737936938328207229194232,4678379842359137077562880,4679560504851182794047039],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3053786612960896498003968,3475578717191038440566791],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598991288262864142272,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,3431598990021625468940288,4155788577558565090234360,4289793908048509108276799],
[54310535542143998431175,157323436099379621261823,1749742854536515146485752,1871942268818151247236671,3431598990021625468940288],
[1206825250816,54310535542143998431175,1737936938328207229194232,2963761009640365451588032,3588922426119798264951295],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598991288262864142272],
[54310535542143998431175,157323436099379621261823,1749743575111355009535992,1871942268818151247236671,3431598990021625468940288],
[1180663757477091786815,54310535542143998431175,1737936938328207229194232,2807618237298462922113024,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268819357267131967]]
def row4_29 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,2963761009640365451588032],
[1266637395201984,157323436099379621261823,1246780851073073236676159,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,623980753989799942025216,1871942268818151247236671,3097766340130309469630471],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009639159438193088,3431598990021625468940288],
[42503897492392110919623,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[37781243478432487837639,157323436099379621261823,2417913509682038744018944,3431537119569944585961472,3626703669597238554784199],
[202188661080329583132216,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,623980753989799942025216,1737936938328207229194232,2963761009640365451588032],
[54310535542143998431175,1737936938329310968938488,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[1266637395201984,157323436099379621261823,1871942268818151247236671,3043455805854802866401280,3431598990021625468940288]]
def row4_30 : List (List ℕ) := [
[54310535542143998431175,157323436099409687867903,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431598990021625468940288,4289793908048509108276799],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431598990021625468940288,4290236656927876103077439],
[54310535543347595907015,157323436099379621261823,1737936938328207229194232,1871942268819357260631615,3431598990021625468940288],
[4722655281800622109127,206911316360926601412607,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468943872],
[1266637395201984,157323436099379621261823,1775718180540002321829887,1871942268818151247236671,3431598990021625468940288],
[157323436099379621261823,1871942268818151247236671,3431560178000036787912704,4155827389580153771261944,4781392742916372700393528],
[37781243478432487837639,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[157323436099379621261823,1404104288436891229884415,1871942268818151247236671,3097766340130309469630471,4781392742916372700393528]]
def row4_31 : List (List ℕ) := [
[54310535542143998431175,1737936938328207229194232,2417913509682038744018944,2808798901055940013899839,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1246780851073073236676159,1404104288436891229884415,1737936938328207229194232],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431537119569944585961472,4289779613623291780218431],
[157323436099379621261823,2963761009640365451588032,3097766340130309469630471,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,152305614899207962096127,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[157323436099379621261823,432122912603973487689671,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[37781242211795092639239,157323436099379621261823,1208999610127915539238904,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404143100458479910911999,1871942268818151247236671,4155827389580153771261944],
[54310535542143998431175,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,4678379842359137077562880],
[37781242211795092639239,1737936938328207229194232,1888471562148500153028607,3431598990021625468940288,4678379842359137077562880]]
def row4_32 : List (List ℕ) := [
[1206825250816,54310535542143998431175,1737936938328207229194232,1871942268819357267131967,3588922426119798264951295],
[54310535542143998431175,1246780851073073236676159,1737936938328207229194232,3431598990021625468940288,4678379842359137077562880],
[1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4633514617378187115692487],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2807508744519883918667776],
[1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,4678379842359137077562880,4781392742916372700393528],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4403603424285735931408440],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[6198484958751685341191,54310535542143998431175,1871942268818151247236671,3248891291270937405551103,3431598990021625468940288],
[157323436099379621261823,432122912602872969367495,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194239,1871942268818151247236671,3431598990021625468940288]]
def row4_33 : List (List ℕ) := [
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3588922426119798264951295,4835703278457309873573887],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4403580365855643729457208],
[23059696729597153216,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404128076450123007344639,1737936938328207229194232,4289817696061740885737023],
[37781242211795092639687,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[37781243478432487837639,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[157323436099379621261823,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944,4781369684486280498442296],
[54310535542143998431175,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,1737936938328207229194232,1870761605060674155449856,3431598990021625468940288,4679560506116614169349695],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431575922584334077259776]]
def row4_34 : List (List ℕ) := [
[1206825250816,54310535542143998431175,1246780852338718433873408,1737936938328207229194232,1871942268818151247236671],
[1266637395201984,157323436099379621261823,1246780851073073236676159,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,679875888878362927562759,1871942268818151247236671,3431560178000036787912704],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451637184,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,1871942268819357267131967],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2807618236033031546810368,3587741763628959373717952],
[54310535542143998431175,1737936938328207229194232,1871942268819357267131967,3431598990021625468940288,4678379842359137077562880],
[37781243478432487837639,1208999608861278144040504,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1191879989423802188349895,2417913509682038744018944,3431537119569944585961472]]
def row4 : List (List ℕ) := [row4_0, row4_1, row4_2, row4_3, row4_4, row4_5, row4_6, row4_7, row4_8, row4_9, row4_10, row4_11, row4_12, row4_13, row4_14, row4_15, row4_16, row4_17, row4_18, row4_19, row4_20, row4_21, row4_22, row4_23, row4_24, row4_25, row4_26, row4_27, row4_28, row4_29, row4_30, row4_31, row4_32, row4_33, row4_34].flatten
def row5_0 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288,4679536716837951016586815],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2472604923651868854271943,3431537119569944585961472],
[54310535542143998431175,151124951140627935920632,157323436099379621261823,1208999608861278144040504,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1792247472603713832423423,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431575931591533266989056],
[54333593972236200382407,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4306765948991587613670975],
[54310535542143998431175,377812377060728970936320,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[157323436099379621261823,432122912602872969367495,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[38082439548623646720,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671]]
def row5_1 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,625123335307621103091775,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[61140868541248749568,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737937658904147610505208,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944,4835680220028424496873471],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2249754645877918086778431,3431598990021625468940288],
[37781242211795092639239,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913510948676139220928,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1208999610127915539238904,1871942268818151247236671,1888471562148500153028607,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,4791684739267515046170616],
[1099518177280,54310535542143998431175,1737936938328207229194232,1871942268819250765364799,2575236945780318847103487,3431537119569944585961472]]
def row5_2 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3436259774850538383016391],
[37781242211795092639239,54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,1871942268818151247236671,2400879598285080332390399,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1793723302281868499484671,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,152305614898105027707391,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2795702828312675513004032],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288,3588922426119798264951295],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[4722655280597018280391,54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,1404166158888572112863231,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,4678379842359137077562880]]
def row5_3 : List (List ℕ) := [
[1206825250816,54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2023067219958779183157247,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1208999610127915539238904,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[61870451680882978816,54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431537119569944585961472],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2472162174772605945319367,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1737975020766656275992568,1871942268818151247236671,3431598990021625468940288],
[54310534275506603229191,54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1749742854536515146485752,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,679875888878362927562759,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1360124560001906079961080,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288]]
def row5_4 : List (List ℕ) := [
[157323436099379621261823,377812377060728970936320,432122912602872969367495,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,377789318630636768985088,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3053786612960896498003968,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431575202008393697980416],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4167742797300369002074104],
[1266637395201984,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,4835703278458516698824703],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1415910925220039010226175,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,3474102888780621687029703],
[54310535542143998431175,157323436099379621261823,157324156675320002376191,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5_5 : List (List ℕ) := [
[54310535543243516411847,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431560908849813752119296],
[54310535542143998431175,151124951141727447806456,1744135423286958914535423,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[38082439548623646720,54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194239,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[1180663757477091786815,54310535542143998431175,1737936938328207229194232,2417913509682038744018944,2807618237298462922113024,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938329310968938488,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[38082439548623646720,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431575202008393697980416],
[1266637395201984,37781242211795092639239,157323436099379621261823,1208999608861278144040504,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417889721668806966558720,3431537119569944585961472,4289817696061740885737023]]
def row5_6 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842360236595740160],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3097766341396946864832455,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2434823680173436366434304,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,377812377060728970936320,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1013685480339586724921344,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032],
[54310535542143998431175,157323436099379621261823,2417913509682038744018944,2963761009640365451588032,3097766340130309469630471,3431537119569944585961472],
[157323436099379621261823,1246780851073073236676159,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472,4781392742916372700393528],
[11805916207207399030784,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[157323436099379621261823,1404166158888572112863231,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,4781392742916372700393528]]
def row5_7 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,3431537119569944585961472,4289817696061740885737023],
[37781242211795092639239,54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,1246780851073073236676159,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535543243516411847,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944592510976],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,4791684739267515046170616],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2039891679209805664223231,3431598990021625468940288],
[4722656547234413481927,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1099518177280,54310535543243516411847,1737936938328207229194232,1871942268818151247236671,2575236945780318847103487,3431537119569944585961472],
[157323436099379621261823,1737936938328207229194232,1871942268819250765364799,2417913509682038744018944,3431537119569944585961472,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3097789398560401671581703,3431598990021625468940288]]
def row5_8 : List (List ℕ) := [
[54310535542143998431175,1737936938328207229194232,1871942268819250765364799,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417851639230357867589632,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1246842722790399310302720,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,377812377060728970936320,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431575202008393691480064],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,4306765948991587613670975],
[54310535542143998431175,157323436099379621261823,1013685480339586724921344,1737936938328207229194232,2417789768776477954805759,2963761009640365451588032],
[1266637395201984,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913510948676139220928,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,3588922426119798264951295],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250765364799,2417913509682038744018944,3431537119569944585961472]]
def row5_9 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944592510976],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431575202008393691480064,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2807656318471480652328960,3431537119569944585961472],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431598990021625468940288,4289817696061740885737023],
[54310535542143998431175,1737936938328207229194232,2963761009640365451588032,3431537119569944585961472,3431598990021625468940288,4678379842359137077562880],
[37781964054372867313607,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472],
[37781242211795092639239,157323436099379621261823,1737936938328207229194232,1888471562148500153028607,2417789768776477954805759,3431537119569944585961472]]
def row5_10 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,528914269771161625690616,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,623942671551350830006272,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682146051092480],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,4791723551289103727198200],
[37781242211795092639239,157323436099379621261823,1888471562148500153028607,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[23058430092201951232,54333593972236200382407,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,377789318630636768985088,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,4835641408006835815845887],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3053786612960896498003968,3097766340130309469630471,3431598990021625468940288],
[720577039899291648,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2472223324648242361139143,3431537119569944585961472]]
def row5_11 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1404104288438098055135231,1737936938328207229194232,1871942268818151247236671],
[157323436099379621261823,1360124560001906079961080,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4781392742916372700393528],
[54310535542143998431175,1737936938328207229194232,1870761605060674155449856,2417913509682038744018944,3431537119569944585961472,4679560506116614169349695],
[37781242211795092639239,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4445960468402543897083903],
[1099518177280,54310535542143998431175,1737936938328207229194232,2575236945780318847103487,2963761009640365451588032,3431537119569944585961472],
[38082439548623646720,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,4781392742916372700393528],
[30066606080,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[38803015489002926080,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472]]
def row5_12 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471],
[7,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,623980753989799942025216,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1206818701312,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819357260631615,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431537119569944585961472,4835641408006835815845887],
[23059696729597153216,54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[3221225472,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2795702828312675513004032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4835665196020067593306111]]
def row5_13 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4155788577558565090234360],
[61870451680882978816,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1871942268818151247236671,3097766340130309469630471],
[157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2028046958720505153064959,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,2417913509682038744018944,3431537119569944585961472,4155788577558565090234360,4289793908048509108276799],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4167742067718332302233592],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431560178000036787912704]]
def row5_14 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3043455805854802866401280,3431598990021625468940288],
[54310535542143998431175,54333593972236200382407,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1247961514830550328462911,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,389595234838944686276608,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,1737936938328207229194232,2028085041160053776711679,2417913509682038744018944,3431537119569944585961472,4834522614701039607037888],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288,4678379842359137077562880],
[54310535543243516411847,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[157323436099379621261823,432122912602872969367495,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2400879598285080332390399,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,4678379842359137077562880]]
def row5_15 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4679560504851182794047039],
[1180663757477091786815,54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2575236945780318847103487,3431537119569944585961472,4835703278457417180647423],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431560178000036787912704,3431598990021625468940288],
[23059696729597153216,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[37781242211795092639239,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1888471562148500153028607,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3001542251852160544227271,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288,4679560504851182794047039],
[1206818701312,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3588860555668117388521983],
[1206825250816,54310535542143998431175,157323436099379621261823,1737936938329310968938488,1871942268818151247236671,3431598990021625468940288]]
def row5_16 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,545909370410007590547904,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1013685480339586724921344,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759],
[54310535542143998431175,157323436099379621261823,1737936938329306741080056,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431575202008393691480064,4289817696061740885737023],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4155788577558565090234360,4678379842359137077562880],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119568737767260160,4678379842360343896264192],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,4835703278458516698824703],
[54310535542143998431175,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431598990021625468940288,4791723551289103727198200],
[23058430092201951232,54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671]]
def row5_17 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[1180663757477091786815,54310535542143998431175,1360124560001906079961080,2028085041160053776711679,2417913509682038744018944,3431537119569944585961472],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1208999608861278144040952,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1208999610127915539238904,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,2400879598285080332390399,2417913509682038744018944,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3432779653779101755371583],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3432717783327420872441919],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250765364799,3431537119569944585961472,3431598990021625468940288],
[38082439548623646720,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431537119569944585961472]]
def row5_18 : List (List ℕ) := [
[1266637395201984,54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3588860555668117388521983],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1871942268818151247236671,3097766340130309469630471,3431537119569944585961472],
[61870451680882978816,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961479],
[54310535542143998431175,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,432122912602872969367495,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,1871942989394091626712639,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4834227448781462550085631],
[37781243478432487837639,54310535542143998431175,157323436099379621261823,1208999608861278144040504,2417913509682038744018944,3431537119569944585961472]]
def row5_19 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1404128076450123007344639,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[1206825250816,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3588860555668117388521983],
[54333593972236200382407,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4793199380966124587905080],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431537119569944585961472,3431560178000036787912704,4155827389580153771261944],
[38082439548623646720,54310535542143998431175,157323436099379621261823,623942671551350830006272,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1360124561267478258257912,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[42503897492392110919623,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,3431598990021625468940288],
[1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,4678379842359137077562880,4781392742916372700393528]]
def row5_20 : List (List ℕ) := [
[157323436099379621261823,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472,4289793908048509108276799,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417851639230357861040128,3431598990021625468940288],
[1180663758576609914943,54310535542143998431175,1737936938328207229194232,2028085041160053776711679,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,2963761009640365451588032,3097766340130309469630471,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4797883224225162992025599],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3822017798118929973903359],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1737936938329310968938488,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,623942671550144816611328,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247187519,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,377789318630636768985088,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288]]
def row5_21 : List (List ℕ) := [
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2575236945780318847103487,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768777577472983039,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,3431598990021625468940288,4678379842359137077562880],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880,4781392742916372700393528],
[11806636783147780341760,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2472223324648242361139143,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,4679536716837951016586815],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944592252928],
[54310535542143998431175,157323436099379621261823,1737936938328207222902776,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842360343902813696],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944592510976]]
def row5_22 : List (List ℕ) := [
[54310535542143998431175,151124951140627935920632,1744135423286958914535423,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[157323436099379621261823,432099854172780767416263,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268819357260631615,2417913509682038744018944],
[37781242211795092639239,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417875427243589638500352,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,3475555658760946238615559],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1737936938329306741080056,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[11805916207207399030784,54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288]]
def row5_23 : List (List ℕ) := [
[54310535542143998431175,157323436098172796011007,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436098172802560511,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,155847606421224954200575,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737913879898115027243000,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1099518177280,54310535542143998431175,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2575236945780318847103487],
[1266637395201984,157323436099379621261823,1246780851073073236676159,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472],
[1206818701312,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,1871942268818151247236671,4679560504851182794047039],
[1206818701312,54310535542143998431175,157323436099379621261823,1737936938329310968680440,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472]]
def row5_24 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3248891291270937405551103,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1247999597268006430625343,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880,4679560504851182794047039],
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417890451251946542067712,3097789398560401671581703,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,206911316360926601412607,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,535135813160005506691583,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535543243516411847,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1360124560001906079961080,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472],
[54310535542143998431175,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880]]
def row5_25 : List (List ℕ) := [
[54310535543347602259911,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,1871942268819357267131967,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913510948676139220928],
[1099518177280,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4683102497639734095843271],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1739117602085684320980991,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1586788927490952840351288,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2849951493403138628456391,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,528937329466929085153728,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,623942671551350830006272,1360124560001906079961080,1871942268818151247236671,2417913509682038744018944]]
def row5_26 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4830684727675205405429759],
[1180663757477091786815,54310535542143998431175,1404166158888572112863231,1737936938328207229194232,2028085041160053776711679,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,625161417746070208561215,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,4835641408006835815845887],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2807618237298462922113024,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537120836581981163456],
[4722655280597018280391,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288,3474041738904881185361863],
[37781243478432487837639,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4155788577558565090234360]]
def row5_27 : List (List ℕ) := [
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,151124951140627935920632,1737936938328207229194232,1744135423286958914535423,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,4679560504851182794047039],
[4722655280597018280391,206911316360926601412607,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[37781242211795092639239,157323436099379621261823,1737936938328207229194232,1871942270084788642435071,2417913509682038744018944,3431537119569944585961472],
[23058430092201951232,54333593972236200382407,157323436099379621261823,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944],
[3221422080,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4210137203279719993180159],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,1888471562148500153028607,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,1404166158888572112863231,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,4678379842359137077562880]]
def row5_28 : List (List ℕ) := [
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880,4679560506116614169349695],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1792247472603713832423423,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,661723913761909844479495,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1099518177280,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2260466332678197851721216,3431537119569944585961472],
[23058430092201951232,54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431560178000036787912704,4155827389580153771261944],
[1180663757477091786815,54310535542143998431175,1737936938328207229194232,2028085041160053776711679,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2472223324648242361139143,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,1737936938328207229194232,1744135423286958914535423,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[23058430092201951232,157323436099379621261823,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1246780851073073236676159,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472]]
def row5_29 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472,4155788577558565090234360],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4679560506116614169349695],
[54310535542143998431175,157323436099379621261823,377812377060728970936320,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961920],
[54333593972236200382407,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431560178000036787912704],
[157323436099379621261823,206911316360926601412607,1737936938328207229194232,1871942268818151247236671,2472223324648242361139143,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2028085041160053776711679,3097766340130309469630471,3431598990021625468940288],
[23059696729597153216,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431575202008393691480064,4678379842359137077562880]]
def row5_30 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472,3588922427385443462148544],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4797922036246751672795135],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2472223324648242361139143,3431537119569944585961472,4155827389580153771261944],
[1099518177280,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2575236945780318847103487,3431537119569944592510976],
[54310535542143998431175,157323436099379621261823,1415972075095779511894015,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4835703277191879303622719],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598991288262864142272],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,4679536716837951016586815],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3041856181232183560630272,3431598990021625468940288],
[54310535542143998431175,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,4678379842359137077562880]]
def row5_31 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,678291289530707853955015,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2400879598285080332390399,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4835703278457309873573887],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819357267131967,2417913509682038744018944,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,667960481158147696750599,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[1835008,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3474102888780621687029703,4791723551289103727198200],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288,4791723551289103727198200]]
def row5_32 : List (List ℕ) := [
[38961905969272184426047,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,389595234837844168015872,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,1871942268819357260631615,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,2963761009640365451588032],
[1266637395201984,54310535542143998431175,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,156142773607333904777664,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,2417789768776477954805759,2963761009640365451588032],
[157323436099379621261823,1737936938329306741080056,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4781392742916372700393528],
[805355520,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1415910925220039010226175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5_33 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,623942671550144816611328,1737936938328207229194232,2417913509682038744018944,4679536716837951016586815],
[157323436099379621261823,1737936938328207229194232,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431537120836581981163456],
[157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2472185242209793257455559,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,1586811987187579293273600,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4457913959827879929839615],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2455694751893833834823175,3431598990021625468940288],
[37781242211795092639239,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1361600389677895011795000,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,3588922426119798264951295],
[6198484958751685341191,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5_34 : List (List ℕ) := [
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2363541103686014839353400,2417913509682038744018944,3431537119569944585961472],
[42503897492392110919623,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[1266637395201984,157323436099379621261823,1246780851073073236676159,1792247472603713832423423,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913510948676139220928,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3475578717191038440566791],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417408890348791842983935,3431598990021625468940288],
[42504619334966664171463,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3041794310780609179418624],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431537119569944585961472,3431598990021625468940288,4289793908048509108276799]]
def row5_35 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,661761996200358948163079,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,662942659956873103196167,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4830685457258345039659007],
[1266637395201984,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404166157621934717661247,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54333593972236200382407,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,157361518537828726731263,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[61870451680882978816,54310535542143998431175,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1888471562148500153028607,2963761009640365451588032,3431598990021625468940288]]
def row5_36 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009639265933459904,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288,4835703278458516698824703],
[54310535542143998431175,157323436099379621261823,1246780851073073236676159,2417913509682038744018944,3431537119569944585961472,4791684739267515046170616],
[54310535542143998431175,157323436099379621261823,389619013843876751278080,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537120836581981163456,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417851639230357861040128,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,528937328201253821350392,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2963761009640365451588032,3431598990021625468940288,4678379842359137077562880],
[38082438449105518592,157323436099379621261823,1737936938328207229194232,3431537119569944585961472,4289817696061740885737023,4781392742916372700393528]]
def row5_37 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4791723551289103727198200],
[1266637395201984,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1360124560001906079961080,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,151124951140627935920632,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417874697660450062991360,3431537119569944585961472,4155827389580153771261944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913510948676139220928,3431598991288262864142272],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2963761009640365451588032,3431598990021625468940288,4781392742916372700393528],
[4722655280597018280391,206911316360926601412607,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1246780851073073236676159,1404166158888572112863231,1737936938328207229194232,2417913509682038744018944],
[54310535542143998431175,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472,4289793908048509108276799,4678379842359137077562880]]
def row5_38 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,3431598990021625468940288,4679560504851182794047039],
[4722655281800615756231,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1742659593608804247474175,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288,4155788577558565090234360],
[157323436099379621261823,1871942268818151247236671,2417789768776477954805759,3097766340130309469630471,3431537119569944585961472,4781392742916372700393528],
[37781243478432487837639,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288],
[4722655280597018280391,54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[0,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1744135423286958914535423,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,377812377060728970936320,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5_39 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,3474041738904881185361863],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1246780851073073236676159,1737936938328207229194232,2417913509682038744018944,3431598990021625468940288],
[157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151253528127,2417913509682038744018944,3431537119569944585961472],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417851639230357861040128,2472162174772501859471303,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,377789318630636768985088,1871942268818151247236671,3431598990021625468940288,4791684739267515046170616],
[54310535542143998431175,157323436099379621261823,545885582396775813087680,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,623980753989799942025216,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679]]
def row5_40 : List (List ℕ) := [
[54310535542143998431175,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[4722655280597018280391,206911316360926601412607,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,4155788577558565090234360],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4628791962097590097412096],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4797922034980084210987064],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990020418643689472,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2575236945780318847103487,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,3431598990021625468940288,4791684739267515046170616],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1870761605060674155449856,1871942268818151247236671,3431598990021625468940288],
[11805916208410996506624,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5_41 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1360147618431998216900600,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[11805916207207399030784,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3474041738904881185361863],
[1266637395201984,157323436099379621261823,1792247472603713832423423,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431537119568737767260160,3431598990021625468940288,4678379842359137077562880],
[49152,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1206825250816,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2575236945780318847103487,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2807618236033031546810368,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340129209957744647,3431537119569944585961472],
[1180663757477091786815,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4155827389580153771261944]]
def row5_42 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,623942671550144816611328,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,3431537119569944585961472,4679560504851182794047039],
[54310535542143998431175,157323436099379621261823,1737936938329306741080056,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[1180663757477091786815,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,4679560504851182794047039],
[37781243478432487837639,157323436099379621261823,1208999608861278144040504,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417851639230357861040128,3431598990021625468940288,4289793908048509108276799],
[157323436099379621261823,432099854172780767416263,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[1180663757477091786815,54310535542143998431175,2028085041160053776711679,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[37781242211795092639239,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2472223324648242361139143,3431598990021625468940288]]
def row5_43 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3431598990021625468940288,4155827389580153771261944,4791684739267515046170616],
[54310535542143998431175,157323436099379621265407,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4835703278458516698824703],
[1266637395201984,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4781392742916372700393528],
[1266637395201984,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,4781392742916372700393528],
[157323436099379621261823,206911316360926601412607,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3474102888780621687029703],
[23058430092201951232,54310535542143998431175,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944,4678379842359137077562880],
[38082438449105518592,54310535542143998431175,157323436099379621261823,545885582396775813087680,1737936938328207229194232,3431537119569944585961472],
[37781242211795092639239,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3474102888780621687029703]]
def row5_44 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3822017798118929973903359],
[4722655280597018280391,206911316360926601412607,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,4289817696061740885737023],
[1266637395201984,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,3588860555668117388521983],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880,4679536716837951016586815],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880,4835703278458516698824703],
[157323436099379621261823,432099854172780767416263,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3474102888780621687029703,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417827851214927060324351,3431598990021625468940288]]
def row5_45 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1360147619698532532883448,1404166158888572112863231,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509680939225841664,3431598990021625468940288],
[23058430092201951232,54310535542143998431175,157323436099379621261823,679875888878362927562759,1871942268818151247236671,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417851639230357861040128,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,2964941673397842543374847,3431598990021625468940288],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431560178000036787912704,4781392742916372700393528],
[54310535543243516411847,157323436099379621261823,1737936938328207229194232,1871942268819250765364799,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,2400879598285080332390399,2417913509682038744018944,3431537119569944585961472,3626703669597238554784199],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,2417851639230357861040128],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537120836581981163456,3431598990021625468940288]]
def row5_46 : List (List ℕ) := [
[0,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4781392742916372700393528],
[1099518177280,54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,528937329466929085153728,2417913509682038744018944,3431537119569944585961472,4172760618501643595628536],
[54310535542143998431175,157323436099379621261823,377812377060728970936320,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759],
[54310535542143998431175,157323436099379621261823,1404166158889671624491007,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,2400879598285080332390399,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,157323437366017016463359,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1206825250816,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3588922426119798264951295],
[37781243478432487837639,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472]]
def row5_47 : List (List ℕ) := [
[37781243478432487837639,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,156142772341902529475008,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585965056],
[54310535542143998431175,157323436098172796011007,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4835703277191879303622719],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4797922036246721606185464],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417890451251946542067712,3431598990021625468940288],
[37781242211795092639239,157323436099379621261823,1737936938328207229194232,1876664924098748265517055,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1247999597268006430625343,1737936938328207229194232,2028108830438716929474559,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2795702828312675513004032,2963761009640365451588032,3431537119569944585961472]]
def row5_48 : List (List ℕ) := [
[54333593972236200382407,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,1888471562148500153028607],
[61870452780394606592,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671],
[11806636783147780341760,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3474102888780621687029703],
[54310535542143998431175,157323436099379621261823,377812377061832710680576,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417851639228158837784575,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4835703278457417180647423],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417851639230357861040128,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1404166158888572106313727,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[0,54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671]]
def row5_49 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021518161866752],
[1206818701312,54310535542143998431175,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3588860555668117388521983],
[54310535542143998431175,157323436099379621261823,1360147619697570460209144,1781955477519208881848319,1871942268818151247236671,2417913509682038744018944],
[38082438449105518592,54310535542143998431175,1737936938328207229194232,3431537119569944585961472,4289817696061740885737023,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4289793908048509108276799],
[54310535542143998431175,157323436099379621261823,195104678311174713901055,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3431537120836581981163456],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944592510976],
[37781243478432487837639,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404104288438098055135231,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5_50 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,528937329466929085153728,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1360124560001906079961080,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021518161866752,4678379842359137077562880],
[54310535542143998431175,156142772341902529475008,1737936938328207229194232,2417913509682038744018944,2964941673397842543374847,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1792247472603713832423423,1871942268818151247236671,3431598990021625468940288],
[1099518177280,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2028085042425485152014335,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3248891291270937405551103,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288,3587741763628959373717952],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431575202008393691480064]]
def row5_51 : List (List ℕ) := [
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2363098354806647844552760,2417913509682038744018944,3431537119569944585961472],
[157323436099379621261823,377812377060728970936320,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472],
[1266637395201984,157323436099379621261823,1775718180540002321829887,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[49587880261546980150784,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4683102497639734095843271],
[1099518177280,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431575202008393691480064],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4834522614701039607037888],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417875427243589638500352,2963799092078814557106624,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451637184,3431537119569944585961472]]
def row5_52 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944592510976],
[54310535542144803737543,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679],
[54310535542143998431175,157323436099379621261823,377812377060728970936320,1737936938328207229194232,1871942268818151247236671,4791723551289103727198200],
[42503897492392110919623,157323436099379621261823,1360124560001906079961080,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2575175075328637970674175,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1586811987187579293273600,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1266637395201984,157323436099379621261823,1246780851073073236676159,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[37781243478432487837639,157323436099379621261823,1208999608861278144040504,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row5_53 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,3431575202008393691480064,4289817696061740885737023],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4781369684486280498442296],
[54310535542143998431175,157323436099379621261823,1247961514829557325106751,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[157323436099379621261823,1871942268818151247236671,2417913509682038744018944,2472162174772501859471303,3431537119569944585961472,4155788577558565090234360],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913510948676139220928,3431537120836581981163456],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2028085041160053776711679,3431598990021625468940288,4289817696061740885737023],
[23779006032583262208,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2472223324648242361139143,3431537119569944585961472],
[1180663757477091786815,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4172760618501643595628536],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row5_54 : List (List ℕ) := [
[54310535543243510058951,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250758864447,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119568845074333696],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3588922426119798264951295],
[1206825250816,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3588922426119798264951295],
[6198484958751685341191,54310535542143998431175,1871942268818151247236671,2417913509682038744018944,3248891291270937405551103,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,2028085042425485152014335],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,2417913509682038744018944,2434823680173436366434304,3431537119569944585961472],
[1266637395201984,37781242211795092639239,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1180663758576609914943,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5_55 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472,4289793908048615610043967],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4679536716837951016586815],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2028085041160053776711679,3431598990021625468940288,4679560504851182794047039],
[54310535542143998431175,151124951140627935920632,157323436099379621261823,1744135423286958914535423,1871942268818151247236671,3431598990021625468940288],
[1266637395201984,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3043455805854802866401280,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682146051092480,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3587741763628959373717952],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3474102888780621687029703,4678379842359137077562880],
[37781242211795092639239,157323436099379621261823,1263310144403422142468095,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472],
[4722655281800622109127,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5_56 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3822017798118929973903359],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1792247472603713832423423,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2575236945780318847103487,3431598990021625468940288,4678379842359137077562880],
[1206825250816,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3588922426119798264951295],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431537119569944585961472,4289817696061740885737023,4835665196020067593306111],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,1871942270084788642435071,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417789768776477954805759,3431537119569944585961472,4289793908048509108276799],
[61870451680882978816,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1404143100458479910911999,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2400879598285080332390399,3431598990021625468940288]]
def row5_57 : List (List ℕ) := [
[0,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880,4678379842360343902813696],
[42503898758996218089415,54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537841412522362474432],
[1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472,4678379842359137077562880,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130412548845575,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1013685480339586724921344,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[1206818701312,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[4722655280597018280391,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4628791962097590097412096],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2964941673397842543374847,3431598990021625468940288]]
def row5_58 : List (List ℕ) := [
[61870451680882978816,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3822017798118929973903359],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819357267131967,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,1737936938328207229194232,1870761605060674155449856,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880,4829504793499765013483512],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990020418643689472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682039549325312,3431537119569944585961472],
[720575940381310976,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2472223324648242361139143],
[1180663757477091786815,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2028085041160053776711679,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5_59 : List (List ℕ) := [
[1206825250816,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[54310535542143998431175,156142772341902529475008,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[54310535543347595907015,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,3431575202008393697980416],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2429719425889350228897792,3431537119569944585961472],
[6198484958751685341191,54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310534275506603229191,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766341396946864832455,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,635787390771711635865600,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[49587878994912806374919,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431537119569944585961472,3431575202008393691480064,4289817696061740885737023]]
def row5_60 : List (List ℕ) := [
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537120836581981163456,4678379842359137077562880],
[4722655280597018280391,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3582723941162150319354360],
[54310535542143998431175,157323436099379621261823,662942659956873103196167,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,545466621530640595747264,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2575236945780318847103487,3431537119569944592510976],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2807618236033031546810368,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1246780851073073236676159,1737936938328207229194232,1792247472603713832423423,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,4678379842359137077562880,4835641408006835815845887]]
def row5_61 : List (List ℕ) := [
[54333593972236200382407,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4155827389580153771261944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431575202008393691480064],
[23058430092201951232,54310535542143998431175,157323436099379621261823,2963761009640365451588032,3431537119569944585961472,4155827389580153771261944],
[1099518177280,54310535542143998431175,157361518537828726731263,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472],
[38082439548623646720,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250765364799,3431537119569944585961472],
[54310535542143998431175,157323436098172802560511,1404166158889778931564543,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,3431598990021625468940288,4289817696061740885737023],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431575202008393691480064,4289817696061740885737023],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3041794310780502677651456,3431598990021625468940288],
[448,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5_62 : List (List ℕ) := [
[54310535542143998431175,1737936938329306741080056,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[1180663757477091786815,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[37781243478432487837639,157323436099379621261823,1208999608861278144040504,2400879598285080332390399,2417913509682038744018944,3431537119569944585961472],
[42503897492392110919623,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3431560178000036787912704,4155827389580153771261944],
[157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472,4781392742916372700393528],
[54310535542143998431175,1208999608861278144040504,2400879598285080332390399,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682068808790016,3431537119569944585961472],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880,4678379842360236595740160],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431560898575977169223680]]
def row5_63 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247237119,2417913509682038744018944,3431537119569944585961472],
[157323436099379621261823,1871942268818151247236671,2417913509682038744018944,2472162174772501859471303,3097766340130309469630471,3431537119569944585961472],
[157323436099379621261823,2417913509682038744018944,2963761009640365451588032,3097766340130309469630471,3431537119569944585961472,4781392742916372700393528],
[1266637395201984,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,2963799092078814557106624,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[206911316360926601412607,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4830980623177919680544312],
[54310535542143998431175,623980753988593922129920,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250765364799,3431537119569944585961472],
[4722655280597018280391,195104678311174713901055,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row5_64 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1775718180540002321829887,1871942268818151247236671,3431598990021625468940288],
[11806636783147780341760,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3474102888780621687029703],
[38082439548623646720,1180663757477091786815,54310535542143998431175,1737936938328207229194232,2028085041160053776711679,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431560907583176363421696],
[1206825250816,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[157323436099379621261823,1737936938328207229194232,1744135423286958914535423,1871942268818151247236671,3431598990021625468940288,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1744135423286958914535423,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[38082439548623646720,54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431537119569944585961472,4289817696061740885737023],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1744135423286958914535423,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3587703681190510268199360]]
def row5_65 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1246780851073073236676159,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54333593972236200382407,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[1206825250816,54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671],
[0,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1099511627776,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944592510976,4678379842359137077562880],
[54310535543243516411847,157323436099379621261823,1737936938329306741080056,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542144004722631,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431560178000036787912704,4678379842359137077562880],
[1180663757477091786815,54310535542143998431175,1737936938328207229194232,2028085041160053776711679,2417913509682038744018944,3431537119569944585961472]]
def row5_66 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1870723522622225915842111,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,3431598990021625468940288],
[37781242211795092639239,54310535542143998431175,157323436099379621261823,1208999608861278144040504,1737936938328207229194232,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288,3475578717191038440566791],
[54310535542143998431175,157323436099379621261823,1360124561268543475159032,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[38082439548623646720,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310534275506603229191,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[61870452780394606592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,623980753989799942025216,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472],
[1206825250816,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819357267131967,3431598990021625468940288]]
def row5_67 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431560178000036787912704,4155827389580153771261944],
[1099518177280,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2575236945780318847103487,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,3053747800939307816976384,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250765364799,2417913509682038744018944,3431537119569944592510976],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,4835665196018968075177983],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2028085041160053776711679,2963761009640365451588032,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4684578327317888762904071],
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,2963761009640365451588032,3431598990021625468940288],
[3584,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5_68 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431575931591533266989056],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,3431598990021625468940288,4289817696061740885737023,4679536716837951016586815],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250765364799,2417913509682038744018944,3431598990021625468940288],
[1206825250816,54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,1871942268818151247236671],
[54310535542143998431175,151124951140627935920632,157323436099379621261823,1871942268818151247236671,3097766340130309469630471,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3588922426119798264951295,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4457890901397787727888383],
[54310535542143998431175,157323436099379621261823,1246780852338718433873408,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417852359806298242351104,3431598990021625468940288],
[1180663757477091786815,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4678379842359137077562880]]
def row5_69 : List (List ℕ) := [
[1180663758683111682111,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,377812378327366366138304,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1266637395201984,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[1266637395201984,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598991288262864142272],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4211722524469922776694783],
[54310535542143998431175,157323436099379621261823,1247961514829557325106751,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[1206825250816,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3469380232233390494973447],
[54310535542143998431175,157323436099379621261823,662942659956873103196167,2417913509682038744018944,3431537119569944585961472,4306765948991587613670975],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,4835703277191879303626751]]
def row5_70 : List (List ℕ) := [
[54310535542143998431175,157323436099409686032895,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328237293965304,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598260438485834711040],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472,4289793908048509108276799],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472,4290236656927876103077439],
[54310535542143998431175,54333593972236200382407,157323436099379621261823,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2807594448019799769350144,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431575202008393697980416],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268819250765364799,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288,3431598991288262864142272]]
def row5_71 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3097766341396946864832455,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,781304190087972738036223,1737936938328207229194232,1871942268818151247236671,3431598990021625468940288]]
def row5 : List (List ℕ) := [row5_0, row5_1, row5_2, row5_3, row5_4, row5_5, row5_6, row5_7, row5_8, row5_9, row5_10, row5_11, row5_12, row5_13, row5_14, row5_15, row5_16, row5_17, row5_18, row5_19, row5_20, row5_21, row5_22, row5_23, row5_24, row5_25, row5_26, row5_27, row5_28, row5_29, row5_30, row5_31, row5_32, row5_33, row5_34, row5_35, row5_36, row5_37, row5_38, row5_39, row5_40, row5_41, row5_42, row5_43, row5_44, row5_45, row5_46, row5_47, row5_48, row5_49, row5_50, row5_51, row5_52, row5_53, row5_54, row5_55, row5_56, row5_57, row5_58, row5_59, row5_60, row5_61, row5_62, row5_63, row5_64, row5_65, row5_66, row5_67, row5_68, row5_69, row5_70, row5_71].flatten
def row6_0 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2472223324648242361139143,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1744135423286958914535423,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288],
[1218746195926197256255,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[6291456,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[42504619334936599400391,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[805306368,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[448,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,2417913509682038744018944,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417851639230357861040128,2417913509682038744018944,3431537119569944585961472,4155788577558565090234360]]
def row6_1 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,1871942268818151247236671,2400879598285080332390399,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,152305614898105027707391,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3474041738904881185361863],
[157323436099379621261823,1737936938328207229194232,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,2472223324648242361139143,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2575236945780318847103487,2963761009640365451588032,3431537119569944585961472],
[0,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310534275506603229191,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row6_2 : List (List ℕ) := [
[11805916207207399030784,54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436098172802560511,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,155847606421224954200575,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,2417851639230357861040128,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4781392742916372700393528],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2400879598285080332390399,2417913509682038744018944,3431537119569944585961472,4781392742916372700393528],
[0,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[1099511627776,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4834189357335814250369023],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2400879598285080332390399,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880]]
def row6_3 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,377789318630636768985088,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288,3474102888780621687029703],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2028108830438716929474559,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,4791684739267515046170616],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,1737936938328207229194232,2400879598285080332390399,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4835680220028424496873471],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3822017798118929973903359],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472,4678379842359137077562880],
[720575940381310976,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288]]
def row6_4 : List (List ℕ) := [
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3475555658760946238615559],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288,3588922426119798264951295],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4679560506116614169349695],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880,4835703278458516698824703],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1792247472603713832423423,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[38082439548623646720,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,3431537119569944585961472],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4781392742916372700393528,4835703278458516698824703],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2028085041160053776711679,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472]]
def row6_5 : List (List ℕ) := [
[38082438449105518592,54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1775718180540002321829887,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[37781242211795092639239,54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[4723375856537399394759,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4835703278458516698824703],
[1266637395201984,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,206911316360926601412607,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,1871965327248243390467647,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,151124951140627935920632,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,662942659956873103196167,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472]]
def row6_6 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3431598990021625468940288,4678379842359137077562880],
[1099518177280,54310535542143998431175,157323436099379621261823,1737936938329306741080056,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,528937329466929085153728,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431598990021625468940288],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431575202008393691480064],
[30064771072,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2455694751893833834823175,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,4791684739267515046170616],
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288]]
def row6_7 : List (List ℕ) := [
[1099518177280,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2575236945780318847103487,3431537119569944585961472],
[16529293330348905791936,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2028085041160053776711679,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,206911316360926601412607,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,377812377060728970936320,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,1737936938328207229194232,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[23779006032583262208,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,2417913509682038744018944,3431537119569944585961472]]
def row6_8 : List (List ℕ) := [
[1206818701312,54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[1099518177280,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2575236945780318847103487,3431537119569944585961472],
[38082439548623646720,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2417913510948676139220928,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472,3474041738904881185361863],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2795640957860994630025216,3431537119569944585961472],
[54310535542143998431175,151124951140627935920632,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,1888471562148500153028607,2417913509682038744018944,3431598990021625468940288],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,4289817696061740885737023],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472]]
def row6_9 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1246780851073073236676159,1737936938328207229194232,1792247472603713832423423,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2807594448019799769350144,3431537119569944585961472],
[37781242211795092639239,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1209022667291370287271480,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417890451251946542067712,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417851639230357861040128,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2400879598285080332390399,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2434823680173436366434304,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,4835703278458516698824703],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3097766341396946864832455,3431537119569944585961472]]
def row6_10 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3588922426119798264951295],
[1206825250816,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880,4791684739267515046170616],
[1099518177280,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417408890348791842983935,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2472223324648242361139143,3431537119569944585961472,4155827389580153771261944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3431575202008393691480064],
[4722655280597018280391,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472]]
def row6_11 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1793723302281868499484671,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4834522614701039607037888],
[54310535542143998431175,157323436099379621261823,377789318630636768985088,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2575236945780318847103487,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1744135423286958914535423,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4445960468402543897083903],
[49587880261546980150784,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4306765948991587613670975],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472,4289817696061740885737023],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471]]
def row6_12 : List (List ℕ) := [
[1180663757477091786815,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4155827389580153771261944],
[54310535542143998431175,157323436099379621261823,1246780851073073236676159,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2963761009640365451588032],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880,4679536716837951016586815],
[157323436099379621261823,206911316360926601412607,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2472223324648242361139143,3431537119569944585961472],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880,4679560506116614169349695],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472,4791684739267515046170616],
[1099518177280,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944592510976],
[54310535542143998431175,1737936938328207229194232,1744135423286958914535423,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880]]
def row6_13 : List (List ℕ) := [
[1266637395201984,37781242211795092639239,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[37781242211795092639239,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,623942671550144816611328,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[1180663758576609914943,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[1266637395201984,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4289817696061740885737023],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3432717783327420872441919],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417890451251946542067712,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,156142772341902529475008,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row6_14 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472,4289817696061740885737023,4679536716837951016586815],
[23058430092201951232,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1247999597268006430625343,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[7,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4835665196020067593306111],
[1099518177280,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288,4835703278458516698824703],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,1876664924098748265517055,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3248891291270937405551103,3431537119569944585961472]]
def row6_15 : List (List ℕ) := [
[54310535542143998431175,1208999608861278144040504,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4818731967098577827659775],
[42503897492392110919623,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472,4289817696061740885737023],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472,3431598990021625468940288],
[721842577776512960,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,623942671550144816611328,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2400879598285080332390399,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288,3474041738904881185361863]]
def row6_16 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,3587703681190510268199360],
[38082438449105518592,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[1180663757477091786815,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1209037691299727190838840,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[1266637395201984,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537120836581981163456],
[0,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4797922036246721606185464],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2807618237298462922113024,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2472162174772501859471303,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2575175075328637970674175,3431537119569944585961472]]
def row6_17 : List (List ℕ) := [
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119568737767260160,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1247999597268006430625343,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3248891291270937405551103,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288,4678379842359137077562880],
[1180663757477091786815,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288],
[0,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1870761605060674155449856,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[11805916208410996506624,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2575236945780318847103487,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3436259774850538383016391]]
def row6_18 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,206911316360926601412607,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[37781242211795092639239,54310535542143998431175,157323436099379621261823,1208999608861278144040504,1737936938328207229194232,2417913509682038744018944,3431537119569944585961472],
[1266637395201984,54310535542143998431175,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417851639230357861040128,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417875427243589638500352,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472,3475555658760946238615559],
[4722655280597018280391,157323436099379621261823,206911316360926601412607,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1737936938329306741080056,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1360147619697570460209144,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row6_19 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4835703277191879303622719],
[1099518177280,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,1871942270084788642435071,2417913509682038744018944,3431537119569944585961472],
[49587880261546980150784,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,1871942268819250765364799,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,206911316360926601412607,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[1266637395201984,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288,3588860555668117388521983],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2039891679209805664223231,2417913509682038744018944,3431537119569944585961472]]
def row6_20 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2963761009640365451588032,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,377789318630636768985088,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4830980623177919680544312],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2028085041160053776711679,2417913509682038744018944,3431537119569944585961472,4289817696061740885737023],
[157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4289817696061740885737023,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288,4679536716837951016586815],
[54310535542143998431175,156142772341902529475008,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4172760618501643595628536],
[54310535542143998431175,157323436099379621261823,1360124560001906079961080,1871942268818151247236671,2028085041160053776711679,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3043455805854802866401280,3431537119569944585961472]]
def row6_21 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,377789318630636768985088,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3431560178000036787912704],
[54310535542143998431175,1737936938328207229194232,1870761605060674155449856,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4679560504851182794047039],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880,4829504793499765013483512],
[54310535542143998431175,157323436099379621261823,157323437366017016463359,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,4679536716837951016586815],
[38961905969272184426047,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[1266637395201984,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288]]
def row6_22 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3626642519722460190867455],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2575236945780318847103487,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,4155827389580153771261944],
[23058430092201951232,54333593972236200382407,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,377812377060728970936320,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417851639230357861040128,2417913509682038744018944,3431537119569944585961472],
[1180663757477091786815,54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,2417789768776477954805759,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3097766341396946864832455,3431537119569944585961472],
[54310535542143998431175,151124951140627935920632,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880]]
def row6_23 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417851639230465168113664,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,151124951140627935920632,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1781955477519208881848319,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[720575940381310976,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[6198484958751685341191,54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[1099518177280,38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472],
[23058430092201951232,54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4155827389580153771261944],
[54310535542143998431175,55491199299621090217983,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[1180663757477091786815,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2028085041160053776711679,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1737975020766656275992568,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row6_24 : List (List ℕ) := [
[54310534275506603229191,54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472,3588860555668117388521983],
[1206818701312,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,377789318630636768985088,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,4781392742916372700393528],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4628791962097590097412096],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417789768776477954805759,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[61140868541248749568,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1792247472603713832423423,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4829504793499765013483512]]
def row6_25 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,4289817696061740885737023],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288,4679560504851182794047039],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3588860555668117388521983],
[54310535542143998431175,157323436099379621261823,545885582396775813087680,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417851639230357861040128,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1208999608861278144040504,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4155827389580153771261944,4791684739267515046170616],
[1206825250816,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288]]
def row6_26 : List (List ℕ) := [
[61870451680882978816,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[1266637395201984,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1781955477519208881848319,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3474102888780621687029703],
[54310535542143998431175,157323436098172802560511,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417851639230357861040128,2417913509682038744018944,3431537119569944585961472,4289793908048509108276799],
[54310535542143998431175,151124951140627935920632,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880,4678379842360236595740160],
[1180663757477091786815,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2028108830438716929474559,2417913509682038744018944]]
def row6_27 : List (List ℕ) := [
[6198484958751685341191,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404104288436891229884415,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[1206818701312,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2964941673397842543374847,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2400879598285080332390399,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[1099518177280,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3001542251852160544227271,3431537119569944585961472],
[61870451680882978816,54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472],
[3584,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,151124952407265331122168,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row6_28 : List (List ℕ) := [
[23058430092201951232,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,4155827389580153771261944],
[54310535542143998431175,157323436099379621261823,157346494529471816921599,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,623942671550144816611328,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288],
[0,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[61870451680882978816,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417851639230357861040128,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4289793908048509108276799],
[54310535542143998431175,157323436099379621261823,195104678311174713901055,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,4678379842359137077562880]]
def row6_29 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417789768776477954805759,3431537119569944585961472,4835703278458516698824703],
[1266637395201984,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,157361518537828726731263,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[4722655280597018280391,54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,679875888878362927562759,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404166158889778931564543,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,4678379842359137077562880],
[1180663757477091786815,54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2400879598285080332390399,2417913509682038744018944,3431537119569944585961472]]
def row6_30 : List (List ℕ) := [
[0,54310535542143998431175,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[37781243478432487837639,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2400879598285080332390399,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842360343896264192],
[1206818701312,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431598990021625468940288],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3431537119569944592510976],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,3431537119569944585961472,3431598990021625468940288,4289817696061740885737023],
[54310535542143998431175,157323436099379621261823,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472,4306765948991587613670975],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3587703681190510268199360],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2260466332678197851721216,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2575236945780318847103487]]
def row6_31 : List (List ℕ) := [
[4722655280597018280391,37781242211795092639239,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[1099518177280,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268819250765364799,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,623980753988593922129920,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,54333593972236200382407,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[23058430092201951232,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431560178000036787912704],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1404166158889778931564543,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119568737767260160,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3041794310780502677651456,3431537119569944585961472],
[37781243478432487837639,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[4722655280597018280391,54310535542143998431175,206911316360926601412607,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row6_32 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,2417913509682038744018944,2963761009640365451588032,2964941673397842543374847,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3822017798118929973903359],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1742659593608804247474175,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417851639228158837784575,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4835703278457417180647423],
[54310535542143998431175,157323436099379621261823,662942659956873103196167,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3431598990021625468940288],
[1180663757477091786815,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,151124951141727447806456,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row6 : List (List ℕ) := [row6_0, row6_1, row6_2, row6_3, row6_4, row6_5, row6_6, row6_7, row6_8, row6_9, row6_10, row6_11, row6_12, row6_13, row6_14, row6_15, row6_16, row6_17, row6_18, row6_19, row6_20, row6_21, row6_22, row6_23, row6_24, row6_25, row6_26, row6_27, row6_28, row6_29, row6_30, row6_31, row6_32].flatten
def row7_0 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417851639230357861040128,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1792247472603713832423423,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[38082438449105518592,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[1099518177280,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1404166158888572112863231,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[4722655280597018280391,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4678379842359137077562880],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2028085041160053776711679,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4155827389580153771261944],
[37781242211795092639239,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row7_1 : List (List ℕ) := [
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4835703278458516698824703],
[23058430092201951232,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,206911316360926601412607,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2400879598285080332390399,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3097766340130309469630471,3431537119569944585961472],
[1266637395201984,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,4289817696061740885737023],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2963761009640365451588032,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,2575236945780318847103487,3431537119569944585961472],
[54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472,3431598990021625468940288]]
def row7_2 : List (List ℕ) := [
[0,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472],
[1180663757477091786815,54310535542143998431175,157323436099379621261823,1737936938328207229194232,1871942268818151247236671,2417913509682038744018944,3431537119569944585961472]]
def row7 : List (List ℕ) := [row7_0, row7_1, row7_2].flatten
def row8_0 : List (List ℕ) := [inputs]
def row8 : List (List ℕ) := [row8_0].flatten

def hint2_0 : List (List ℕ) := [
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk2_0 : (row2_0.zip hint2_0).all (fun p => verifyS width topMask 1 taus p.1 row1 p.2) = true := by
  decide +kernel

theorem chk2 : ∀ S ∈ row2, ∃ H, verifyS width topMask 1 taus S row1 H = true := by
  intro S hS
  obtain ⟨r, hr, hS⟩ := List.mem_flatten.mp hS
  simp only [row2, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact rowsS_ok _ _ (by decide) chk2_0 S hS

def hint3_0 : List (List ℕ) := [
[],
[12],
[],
[],
[],
[],
[],
[],
[8],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk3_0 : (row3_0.zip hint3_0).all (fun p => verifyS width topMask 2 taus p.1 row2 p.2) = true := by
  decide +kernel

def hint3_1 : List (List ℕ) := [
[],
[],
[12],
[12],
[12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,8,12,4,12,12,0,12],
[],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk3_1 : (row3_1.zip hint3_1).all (fun p => verifyS width topMask 2 taus p.1 row2 p.2) = true := by
  decide +kernel

def hint3_2 : List (List ℕ) := [
[],
[12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,8,12,4,12,12,0,12],
[4],
[],
[],
[12],
[12],
[12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,8,12,4,12,12,0,12],
[],
[12]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk3_2 : (row3_2.zip hint3_2).all (fun p => verifyS width topMask 2 taus p.1 row2 p.2) = true := by
  decide +kernel

def hint3_3 : List (List ℕ) := [
[],
[],
[4],
[12],
[12],
[12],
[8],
[12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,8,12,4,12,12,0,12],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk3_3 : (row3_3.zip hint3_3).all (fun p => verifyS width topMask 2 taus p.1 row2 p.2) = true := by
  decide +kernel

def hint3_4 : List (List ℕ) := [
[],
[],
[],
[],
[12],
[],
[12],
[],
[12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,8,12,4,12,12,0,12],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk3_4 : (row3_4.zip hint3_4).all (fun p => verifyS width topMask 2 taus p.1 row2 p.2) = true := by
  decide +kernel

def hint3_5 : List (List ℕ) := [
[12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,8,12,4,12,0,12],
[],
[8],
[12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,8,12,4,12,12,0,12],
[0],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk3_5 : (row3_5.zip hint3_5).all (fun p => verifyS width topMask 2 taus p.1 row2 p.2) = true := by
  decide +kernel

theorem chk3 : ∀ S ∈ row3, ∃ H, verifyS width topMask 2 taus S row2 H = true := by
  intro S hS
  obtain ⟨r, hr, hS⟩ := List.mem_flatten.mp hS
  simp only [row3, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowsS_ok _ _ (by decide) chk3_0 S hS
  · exact rowsS_ok _ _ (by decide) chk3_1 S hS
  · exact rowsS_ok _ _ (by decide) chk3_2 S hS
  · exact rowsS_ok _ _ (by decide) chk3_3 S hS
  · exact rowsS_ok _ _ (by decide) chk3_4 S hS
  · exact rowsS_ok _ _ (by decide) chk3_5 S hS

def hint4_0 : List (List ℕ) := [
[],
[],
[],
[],
[],
[],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_0 : (row4_0.zip hint4_0).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_1 : List (List ℕ) := [
[],
[],
[],
[],
[176,176,176,176,176,176,176,176,176,176,176,176,176,148,192,84,176,176,176,176,176,176,176,176,176,176,176,176,144,176,176,20,176,28,176,216,176],
[],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_1 : (row4_1.zip hint4_1).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_2 : List (List ℕ) := [
[],
[228,38],
[49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,148,57,108,49,32,49,88,49,49,113,49,121,49],
[137,176],
[],
[],
[],
[],
[],
[48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,140,48,48,48,48,48,48,200,109,56,48,48,33,48,89,48,120,48,112,48]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_2 : (row4_2.zip hint4_2).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_3 : List (List ℕ) := [
[],
[],
[],
[],
[136,48,55],
[],
[132,132,132,132,132,132,132,132,132,132,132,132,132,132,132,132,200,192,212,132,132,132,132,132,132,224,132,208,132,128,132,132,204,132],
[],
[126],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_3 : (row4_3.zip hint4_3).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_4 : List (List ℕ) := [
[104,100],
[],
[],
[],
[],
[],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_4 : (row4_4.zip hint4_4).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_5 : List (List ℕ) := [
[],
[],
[152],
[54],
[48,104],
[208,144],
[26],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_5 : (row4_5.zip hint4_5).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_6 : List (List ℕ) := [
[40],
[140,176],
[],
[],
[168],
[],
[],
[],
[176,176,176,176,176,176,176,176,176,176,176,192,84,109,176,176,176,176,176,176,176,176,176,176,176,176,176,176,144,176,20,176,28,176,176,216,176],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_6 : (row4_6.zip hint4_6).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_7 : List (List ℕ) := [
[],
[],
[232],
[],
[],
[],
[172,98],
[],
[176,176,176,176,176,176,176,176,176,176,176,192,84,56,176,176,176,176,176,176,176,176,176,176,176,176,176,176,144,176,20,176,28,176,176,216,176],
[72]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_7 : (row4_7.zip hint4_7).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_8 : List (List ℕ) := [
[],
[28],
[],
[],
[],
[],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_8 : (row4_8.zip hint4_8).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_9 : List (List ℕ) := [
[],
[],
[],
[62],
[162],
[],
[172],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_9 : (row4_9.zip hint4_9).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_10 : List (List ℕ) := [
[62,60,104,132],
[],
[],
[],
[],
[224],
[176,176,176,176,176,176,176,176,176,176,176,192,84,212,176,176,176,176,176,176,176,176,176,176,176,176,176,144,176,20,176,28,176,176,216,176],
[],
[],
[28]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_10 : (row4_10.zip hint4_10).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_11 : List (List ℕ) := [
[],
[],
[40],
[112],
[],
[],
[],
[],
[],
[120]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_11 : (row4_11.zip hint4_11).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_12 : List (List ℕ) := [
[],
[],
[],
[49,100],
[],
[180],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_12 : (row4_12.zip hint4_12).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_13 : List (List ℕ) := [
[62,62,62,62,62,62,62,62,62,62,62,62,62,62,62,62,62,62,62,62,62,62,62,62,62,8,62,70,62,156,62,62,82,62],
[42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,26,42,0,42,42,162,42,38,42],
[],
[],
[224,180],
[],
[],
[],
[],
[60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,158,60,68,60,10,60,60,80,60]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_13 : (row4_13.zip hint4_13).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_14 : List (List ℕ) := [
[48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,48,184,48,109,108,56,48,33,48,89,48,120,48,48,112,48],
[],
[94],
[32,144],
[],
[],
[],
[162],
[],
[64]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_14 : (row4_14.zip hint4_14).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_15 : List (List ℕ) := [
[],
[20],
[],
[],
[49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,192,57,108,49,32,49,88,49,49,113,49,121,49],
[132],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_15 : (row4_15.zip hint4_15).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_16 : List (List ℕ) := [
[],
[],
[],
[],
[60],
[42],
[64],
[],
[],
[48]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_16 : (row4_16.zip hint4_16).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_17 : List (List ℕ) := [
[],
[],
[94,92],
[],
[],
[42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,26,42,0,42,162,42,42,38,42],
[],
[60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,158,60,68,60,10,60,60,80,60],
[49,48,132],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_17 : (row4_17.zip hint4_17).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_18 : List (List ℕ) := [
[],
[26],
[158,16],
[],
[],
[],
[],
[],
[],
[40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,24,40,2,40,160,40,36,40]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_18 : (row4_18.zip hint4_18).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_19 : List (List ℕ) := [
[],
[],
[],
[],
[],
[],
[],
[],
[60],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_19 : (row4_19.zip hint4_19).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_20 : List (List ℕ) := [
[],
[176,176,176,176,176,176,176,176,176,176,176,176,200,192,84,176,176,176,176,176,176,176,176,176,176,176,176,144,176,20,176,28,176,216,176],
[42],
[184,176],
[82],
[132,132,132,132,132,132,132,132,132,132,132,132,132,132,132,132,132,200,148,212,132,132,132,132,132,132,132,224,132,208,132,128,132,132,204,132],
[],
[],
[],
[42]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_20 : (row4_20.zip hint4_20).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_21 : List (List ℕ) := [
[],
[196],
[],
[121],
[],
[],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_21 : (row4_21.zip hint4_21).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_22 : List (List ℕ) := [
[],
[60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,158,60,60,68,60,10,60,80,60],
[],
[],
[],
[],
[132,176],
[],
[],
[96]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_22 : (row4_22.zip hint4_22).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_23 : List (List ℕ) := [
[128],
[],
[220],
[94],
[],
[],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_23 : (row4_23.zip hint4_23).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_24 : List (List ℕ) := [
[],
[118,176],
[],
[],
[],
[188],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_24 : (row4_24.zip hint4_24).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_25 : List (List ℕ) := [
[62],
[88,89,128],
[],
[204],
[32,33,208],
[],
[28],
[40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,24,40,2,40,160,40,40,36,40],
[],
[8]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_25 : (row4_25.zip hint4_25).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_26 : List (List ℕ) := [
[],
[44],
[216],
[],
[49,176],
[],
[],
[196],
[124],
[49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,49,84,57,108,49,32,49,88,49,49,113,49,121,49]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_26 : (row4_26.zip hint4_26).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_27 : List (List ℕ) := [
[4,42,40,176],
[],
[],
[40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,40,24,40,40,2,40,160,40,36,40],
[],
[116,4],
[10],
[],
[82],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_27 : (row4_27.zip hint4_27).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_28 : List (List ℕ) := [
[],
[],
[144],
[],
[],
[],
[176],
[40],
[76],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_28 : (row4_28.zip hint4_28).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_29 : List (List ℕ) := [
[],
[132,132,132,132,132,132,132,132,132,132,132,132,132,132,132,132,184,132,200,108,212,132,132,132,132,132,132,224,132,208,132,128,132,132,204,132],
[],
[],
[],
[156],
[152],
[],
[],
[188,20]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_29 : (row4_29.zip hint4_29).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_30 : List (List ℕ) := [
[],
[],
[],
[],
[],
[],
[132,100],
[],
[70],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_30 : (row4_30.zip hint4_30).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_31 : List (List ℕ) := [
[76],
[204],
[],
[],
[],
[232],
[60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,60,158,60,68,60,10,60,60,80,60],
[],
[],
[68]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_31 : (row4_31.zip hint4_31).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_32 : List (List ℕ) := [
[96,98],
[208],
[74],
[],
[],
[],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_32 : (row4_32.zip hint4_32).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_33 : List (List ℕ) := [
[164],
[0],
[52,176],
[],
[66],
[62],
[],
[],
[],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_33 : (row4_33.zip hint4_33).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_34 : List (List ℕ) := [
[12],
[132,132,132,132,132,132,132,132,132,132,132,132,132,132,132,132,132,200,84,212,132,132,132,132,132,132,224,132,208,132,128,132,132,204,132],
[],
[],
[],
[],
[],
[70],
[18]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_34 : (row4_34.zip hint4_34).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

theorem chk4 : ∀ S ∈ row4, ∃ H, verifyS width topMask 3 taus S row3 H = true := by
  intro S hS
  obtain ⟨r, hr, hS⟩ := List.mem_flatten.mp hS
  simp only [row4, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowsS_ok _ _ (by decide) chk4_0 S hS
  · exact rowsS_ok _ _ (by decide) chk4_1 S hS
  · exact rowsS_ok _ _ (by decide) chk4_2 S hS
  · exact rowsS_ok _ _ (by decide) chk4_3 S hS
  · exact rowsS_ok _ _ (by decide) chk4_4 S hS
  · exact rowsS_ok _ _ (by decide) chk4_5 S hS
  · exact rowsS_ok _ _ (by decide) chk4_6 S hS
  · exact rowsS_ok _ _ (by decide) chk4_7 S hS
  · exact rowsS_ok _ _ (by decide) chk4_8 S hS
  · exact rowsS_ok _ _ (by decide) chk4_9 S hS
  · exact rowsS_ok _ _ (by decide) chk4_10 S hS
  · exact rowsS_ok _ _ (by decide) chk4_11 S hS
  · exact rowsS_ok _ _ (by decide) chk4_12 S hS
  · exact rowsS_ok _ _ (by decide) chk4_13 S hS
  · exact rowsS_ok _ _ (by decide) chk4_14 S hS
  · exact rowsS_ok _ _ (by decide) chk4_15 S hS
  · exact rowsS_ok _ _ (by decide) chk4_16 S hS
  · exact rowsS_ok _ _ (by decide) chk4_17 S hS
  · exact rowsS_ok _ _ (by decide) chk4_18 S hS
  · exact rowsS_ok _ _ (by decide) chk4_19 S hS
  · exact rowsS_ok _ _ (by decide) chk4_20 S hS
  · exact rowsS_ok _ _ (by decide) chk4_21 S hS
  · exact rowsS_ok _ _ (by decide) chk4_22 S hS
  · exact rowsS_ok _ _ (by decide) chk4_23 S hS
  · exact rowsS_ok _ _ (by decide) chk4_24 S hS
  · exact rowsS_ok _ _ (by decide) chk4_25 S hS
  · exact rowsS_ok _ _ (by decide) chk4_26 S hS
  · exact rowsS_ok _ _ (by decide) chk4_27 S hS
  · exact rowsS_ok _ _ (by decide) chk4_28 S hS
  · exact rowsS_ok _ _ (by decide) chk4_29 S hS
  · exact rowsS_ok _ _ (by decide) chk4_30 S hS
  · exact rowsS_ok _ _ (by decide) chk4_31 S hS
  · exact rowsS_ok _ _ (by decide) chk4_32 S hS
  · exact rowsS_ok _ _ (by decide) chk4_33 S hS
  · exact rowsS_ok _ _ (by decide) chk4_34 S hS

def hint5_0 : List (List ℕ) := [
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444,444],
[104],
[358,598,946],
[1304,1304,1304,1304,1304,1304,1304,1304,220,1304,1304,1304,1304,1304,1304,1304,1284,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1304,1348,1304,1272,1304,0,1304],
[0],
[900,972],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,724,1304,1304,1304,1304,1304,1304,1304,1304,224,1304,1304,1304,1304,1304,546,1304,1304,544,1304,1348,1304,1272,1304,0,1304],
[1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,451,1150,524,1030,700,1150,1150,1150,724,1150,1324,1150,1312,1150,588,1150,1150,872,1150],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_0 : (row5_0.zip hint5_0).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_1 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[330,149],
[1052],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[217,492,160],
[1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,884,1264,708,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,1342,768,1342,1234,1342,1104,1342,552,1342,1342,818,1342],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,634,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,1034,482,1034,0,1034,776,1034],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[550,548,832]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_1 : (row5_1.zip hint5_1).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_2 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,1114,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936],
[372,372,372,372,372,372,372,372,372,372,372,558,1266,710,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,830,372,1278,372,730,372,372,1074,372,1112,372],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,840,0,960,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,0,1304,0,1034,0,444,0,936,0],
[],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,1140,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444,444],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,60,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_2 : (row5_2.zip hint5_2).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_3 : List (List ℕ) := [
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,460,1034,880,1034,764,1034,1034,1034,1034,1034,1034,1034,990,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034],
[0,0,0,0,0,0,0,0,0,0,0,1336,0,0,0,0,0,0,598,0,358,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,884,556,1264,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,1342,0,768,1032,1342,0,1234,1304,1342,0,1104,1342,0,1034,1342,0,552,444,1342,0,818,936,1342,0],
[1034],
[303],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,0,444,0,936,0],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,876,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034],
[341,1136],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,358,1062,358,334,358,78,358,464,358,358,1178,358]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_3 : (row5_3.zip hint5_3).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_4 : List (List ℕ) := [
[1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,1150,758,524,700,1150,1150,724,1150,1150,1324,1150,1312,1150,588,1150,872,1150],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,150,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,396,133,133,0,133,74,133,977,133,72,133,528,133,133,612,133],
[38],
[904,904,904,904,904,904,904,904,904,904,904,904,904,904,144,1364,1165,904,904,904,904,904,904,904,813,904,804,272,424,904,904,904,904,904,904,904,904,904,904,536,904,220,904,1196,904,324,904,904,1012,904],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034],
[936,936,936,936,936,936,936,936,936,624,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,936,776,936,1160,936],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,472,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034,1034],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_4 : (row5_4.zip hint5_4).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_5 : List (List ℕ) := [
[294],
[4],
[183],
[72],
[1316],
[1240,1152],
[392],
[133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,704,133,133,133,133,133,133,133,133,133,133,133,133,74,133,977,133,72,133,528,133,612,133],
[658,656,217,216,712,400],
[308]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_5 : (row5_5.zip hint5_5).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_6 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,876,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,1034,776,1034],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1074,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[808,416,242],
[1304],
[444],
[482],
[632],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,184,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_6 : (row5_6.zip hint5_6).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_7 : List (List ℕ) := [
[308,868],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,828,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034],
[1016,1284],
[592,178],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034,1034],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,824,0,0,0,788,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[484,550,592],
[506],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_7 : (row5_7.zip hint5_7).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_8 : List (List ℕ) := [
[41],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,302,0,0,0,0,0,0,0,300,0,0,124,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,872,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,936,0,936,776,936,1160,936],
[308,0],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,564,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034,1034],
[],
[1056,1056,1056,1056,1056,1056,1056,1056,1056,1056,1056,1056,1056,1056,117,616,1076,1056,1056,1056,1056,1056,1056,1056,1056,244,1056,1056,1056,1056,1056,1056,1056,1056,1056,1056,804,313,273,1056,1056,572,1056,605,1056,436,1056,453,1056,477,1056],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,990,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034,1034],
[600]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_8 : (row5_8.zip hint5_8).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_9 : List (List ℕ) := [
[1034],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034],
[284,1032],
[0],
[],
[1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,1348,22,1348,20,1348,1304,1348,1348,28,1348,444,1348],
[684],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,1034,776,1034],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[276]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_9 : (row5_9.zip hint5_9).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_10 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[976],
[],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[828],
[151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,1301,151,187,151,128,151,972,151,120,151],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,129,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,1034,482,1034,0,1034,776,1034],
[],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1124,1034,864,1034,544,1034,482,1034,1034,0,1034,776,1034],
[340,432]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_10 : (row5_10.zip hint5_10).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_11 : List (List ℕ) := [
[936,936,936,936,936,936,936,936,936,936,936,936,936,856,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,936,776,936,1160,936],
[1062],
[1352],
[1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,546,1032,864,1032,480,1032,778,1032,0,1032],
[0,0,0,0,0,0,0,0,0,0,0,0,352,0,0,0,0,0,0,354,0,0,132,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[],
[133],
[936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,936,778,1272,406,936,778,0,1032,936,778,776,1236,936,778,1160,534,936,778],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1200,0,412,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[1356]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_11 : (row5_11.zip hint5_11).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_12 : List (List ℕ) := [
[],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1316,0,196,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,248,0,908,720,248,0,248,0,248,0,668,248,0,1170,1032,248,0,68,1304,248,0,388,248,0,1168,1034,248,0,1188,444,248,0,936,248,0],
[601,601,601,601,601,601,601,601,601,601,601,601,601,601,601,601,601,601,601,601,1212,601,1214,601,601,601,601,601,601,601,601,601,601,601,601,507,601,40,601,505,601,1172,601,440,601],
[],
[328,52],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,651,0,971,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[417,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_12 : (row5_12.zip hint5_12).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_13 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[544],
[0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,0,470,1032,238,0,470,1304,8,0,470,1034,0,470,444,1042,0,470,936,540,0,470,760,0,470],
[],
[778],
[444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,444,482,480,1252,444,482,1348,20,444,482,0,1034,444,482,1160,532,444,482],
[],
[1132],
[50],
[1034]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_13 : (row5_13.zip hint5_13).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_14 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,1196,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1208,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,0,151,1032,0,151,1301,0,151,1304,187,0,151,1034,128,0,151,444,972,0,151,936,120,0,151],
[840],
[1292],
[1068,844],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1304,1272,1304,0,1304],
[],
[808,809,1150],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,770,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,1034,0,1034,776,1034],
[936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,936,1272,778,406,936,1272,0,1304,936,1272,776,404,936,1272,1160,28,936,1272]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_14 : (row5_14.zip hint5_14).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_15 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,868,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,364,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936],
[888],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[139,1056,94,1328],
[374,374,374,374,374,374,374,374,374,374,374,374,374,374,374,374,374,884,556,708,374,374,374,374,374,374,374,374,374,374,374,374,374,374,374,728,374,374,1276,374,828,374,1072,374,1114,374],
[444,444,444,444,444,444,444,444,444,444,1008,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,444,1160,444],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444,444],
[],
[392,392,392,392,392,392,392,392,392,392,392,392,392,392,392,392,392,392,392,384,392,918,392,392,392,392,392,392,392,304,392,392,392,392,392,462,392,1192,392,630,392,158,392,202,392]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_15 : (row5_15.zip hint5_15).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_16 : List (List ℕ) := [
[1064],
[],
[176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,25,176,204,176,772,176,292,176,176,609,176],
[308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,284,308,956,308,286,308,308,1332,308,892,308],
[0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,0,1034,1032,864,0,1034,1304,544,0,1034,444,482,0,1034,936,776,0,1034],
[8],
[],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936],
[964,1102,660,1148,1080],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,120,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_16 : (row5_16.zip hint5_16).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_17 : List (List ℕ) := [
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,444,482,444,0,444,1160,444],
[934],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[664,1338],
[656,1342],
[372,372,372,372,372,372,372,372,372,372,558,710,520,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,372,830,372,1278,372,730,372,1074,372,372,1112,372],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,506,600,41,600,504,600,1173,600,600,441,600],
[528]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_17 : (row5_17.zip hint5_17).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_18 : List (List ℕ) := [
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,1012,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,776,1236,776,404,776,1034,776,532,776,936,776,776],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[196],
[1348],
[0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,0,1150,1094,524,700,0,1150,0,1150,1032,0,1150,1304,724,0,1150,1324,0,1150,1034,1312,0,1150,444,588,0,1150,936,872,0,1150],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,924,0,0,0,0,380,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,558,520,521,658,1036,658,658,1388,658,1180,658,278,658,279,658]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_18 : (row5_18.zip hint5_18).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_19 : List (List ℕ) := [
[1332],
[948],
[140],
[76],
[416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,1228,416,748,416,497,416,416,1268,416,1368,416],
[248],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[444],
[356,356,356,356,356,356,356,356,356,356,356,356,356,932,356,356,356,344,356,356,356,568,356,356,356,356,356,356,356,356,356,356,356,356,76,356,332,356,1060,356,466,356,356,1176,356],
[22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_19 : (row5_19.zip hint5_19).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_20 : List (List ℕ) := [
[646],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,468,0,0,0,0,0,0,0,470,0,0,1204,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[912],
[482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,482,1252,482,20,482,1034,482,444,482,482,532,482],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[936],
[0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,0,392,1032,462,0,392,1304,1192,0,392,1034,0,392,630,0,392,444,158,0,392,936,202,0,392],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,1304,544,1304,1348,1304,1272,1304,0,1304],
[100],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,973,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,444,482,444,0,444,1160,444]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_20 : (row5_20.zip hint5_20).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_21 : List (List ℕ) := [
[1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,546,1032,864,1032,480,1032,1032,778,1032,0,1032],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,332,1304,1304,1304,1304,334,1304,1304,1304,1304,1304,68,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1304,1272,1304,0,1304],
[1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,1032,546,864,1296,1032,546,480,22,1032,546,778,406,1032,546,0,1304,1032,546],
[448,240],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[0],
[786],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_21 : (row5_21.zip hint5_21).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_22 : List (List ℕ) := [
[696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,62,696,210,696,316,696,580,696,696,166,696],
[129],
[],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1276,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,1020,444,444,444,444,444,444,444,1022,444,444,444,444,480,444,1348,444,482,444,444,0,444,1160,444],
[0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,0,1304,1032,546,0,1304,1034,544,0,1304,444,1348,0,1304,936,1272,0,1304],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034,1034],
[0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,0,176,1032,25,0,176,1304,204,0,176,1034,0,176,772,0,176,444,292,0,176,936,609,0,176],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,372,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_22 : (row5_22.zip hint5_22).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_23 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[],
[712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,117,88,561,712,116,89,560,712,712,712,712,712,712,712,712,712,712,820,1165,1164,712,420,712,1016,712,1004,712,712,853,712,852,712],
[1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,24,1032,507,1032,738,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,546,1032,864,1032,480,1032,778,1032,0,1032],
[868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,168,868,1120,868,256,868,170,868,868,1044,868],
[177,177,177,177,177,177,177,177,177,177,177,177,177,177,177,177,177,177,177,177,997,177,1214,177,177,177,177,177,177,177,177,177,177,177,177,24,177,205,177,773,177,293,177,608,177],
[1034]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_23 : (row5_23.zip hint5_23).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_24 : List (List ℕ) := [
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1308,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,1034,776,1034],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1120,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304,1304],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,936,0,936,776,936,1160,936],
[80],
[936,936,936,936,936,936,936,936,164,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,936,0,936,776,936,1160,936],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[178],
[],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,1304,544,1304,1348,1304,1272,1304,0,1304]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_24 : (row5_24.zip hint5_24).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_25 : List (List ℕ) := [
[394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,394,628,394,1194,394,460,394,156,394,394,200,394],
[0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,1376,0,720,248,908,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,0,720,1032,882,0,720,1304,1384,0,720,1034,880,0,720,444,0,720,744,0,720,936,1156,0,720],
[477],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,178,0,176,0,600,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[984,67],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,1010,444,444,444,480,444,1348,444,444,482,444,0,444,1160,444],
[491]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_25 : (row5_25.zip hint5_25).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_26 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,685,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1152,0,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,38,0,0,0,0,4,0,1032,0,1304,0,1034,0,444,0,936,0],
[437,1024],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444,444],
[1388,1232],
[470]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_26 : (row5_26.zip hint5_26).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_27 : List (List ℕ) := [
[1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,1304,544,546,1296,1304,544,1348,20,1304,544,1272,404,1304,544,0,1034,1304,544],
[696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,62,696,210,696,696,316,696,580,696,166,696],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,170,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034,1034],
[698],
[656,1002],
[328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,348,328,328,328,328,328,328,328,328,328,328,328,328,1344,328,360,328,900,328,140,328,428,328],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,952,0,680,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,112,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1276,1304,1304,1304,1304,1234,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1304,1272,1304,0,1304],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_27 : (row5_27.zip hint5_27).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_28 : List (List ℕ) := [
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1352,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304,1304],
[936,936,936,936,936,936,936,936,936,936,1012,936,936,936,936,936,936,936,936,936,936,1244,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,936,1160,936],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[108],
[416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,348,416,416,416,416,416,416,416,416,416,416,416,416,416,416,1228,416,748,416,497,416,1268,416,1368,416],
[516,516,516,516,516,516,516,516,516,516,516,516,516,932,516,516,516,934,516,516,516,516,688,516,516,516,516,516,516,516,516,516,516,516,516,516,516,844,516,270,516,268,516,1152,516,516,364,516],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1304,1272,1304,0,1304],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1304,1348,1304,1272,1304,0,1304],
[1228],
[712,620]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_28 : (row5_28.zip hint5_28).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_29 : List (List ℕ) := [
[],
[],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,588,444,444,444,444,444,444,444,444,444,444,376,444,444,480,444,1348,444,444,482,444,0,444,1160,444],
[1108],
[348,151],
[181,178],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1060,1034,1034,1034,268,1034,1034,1034,1034,1034,296,1034,1168,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,1034,0,1034,776,1034],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,151,0,0,0,1144,0,0,1328,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[956,1304]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_29 : (row5_29.zip hint5_29).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_30 : List (List ℕ) := [
[1004,920],
[0,0,0,0,0,0,0,0,0,0,0,0,192,0,0,0,0,0,0,0,800,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[677,328,330,1056],
[592,594,832],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,536,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,160,1144,1144,1144,1144,1144,1144,1144,162,1144,1144,1144,1144,1144,1144,58,56,273,1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,860,1144,1128,1144,862,1144,1024,1144,1144,1048,1144],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034,1034],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,1272,406,1272,1304,1272,404,1272,28,1272,1272,936,1272]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_30 : (row5_30.zip hint5_30).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_31 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,830,1032,1032,1032,1032,1032,1032,508,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,546,1032,864,1032,480,1032,1032,778,1032,0,1032],
[544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,544,1296,544,20,544,544,1304,544,404,544,1034,544],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,444,0,444,1160,444],
[0,0,0,0,0,0,0,0,0,0,0,0,188,0,0,0,0,0,0,0,190,0,0,652,0,0,0,0,0,0,0,0,0,1320,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,908,720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,882,720,1384,720,880,720,744,720,720,1156,720],
[296],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,320,0,752,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[838,836,1144,1080],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,376,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444,444]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_31 : (row5_31.zip hint5_31).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_32 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,150,0,0,0,0,0,0,0,0,148,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,0,601,1032,507,0,601,1304,40,0,601,1034,505,0,601,444,0,601,1172,0,601,936,440,0,601],
[936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,936,1160,778,534,936,1160,1272,28,936,1160,0,444,936,1160,776,532,936,1160],
[904,904,904,904,904,904,904,904,904,904,904,904,904,904,904,904,822,144,1364,904,904,904,904,904,804,58,424,904,904,904,904,904,904,904,904,904,904,536,904,904,220,904,1196,904,324,904,1012,904],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1044,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[1160],
[25],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,174,0,172,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_32 : (row5_32.zip hint5_32).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_33 : List (List ℕ) := [
[309],
[1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,89,617,1077,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,56,272,312,1057,573,1057,1057,604,1057,437,1057,476,1057,452,1057],
[1020],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,336,1304,1304,1304,1304,546,1304,1304,544,1304,1348,1304,1272,1304,0,1304],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444],
[0,0,0,0,0,0,0,0,0,0,0,86,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_33 : (row5_33.zip hint5_33).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_34 : List (List ℕ) := [
[762],
[332],
[712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,117,616,561,712,116,617,560,712,712,712,712,712,712,712,712,712,144,1165,1164,712,420,712,1016,712,1004,712,712,853,712,852,712],
[1056,1144],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[781],
[132],
[1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,646,1204,796,1204,644,1204,1204,1116,1204,1064,1204]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_34 : (row5_34.zip hint5_34).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_35 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,564,1034,1034,1034,864,1034,544,1034,1034,482,1034,0,1034,776,1034],
[0,0,0,0,0,0,0,0,0,0,0,0,732,0,0,0,0,1256,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,1024,444,444,324,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444],
[452],
[151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,151,1301,151,187,151,128,151,972,151,151,120,151],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,1160,444,534,480,1160,444,28,1348,1160,444,532,482,1160,444,936,0,1160,444],
[],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,552,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,444,0,444,1160,444]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_35 : (row5_35.zip hint5_35).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_36 : List (List ℕ) := [
[1173],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444],
[136,676,213],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1150,0,0,0,662,0,0,0,0,0,1148,0,0,0,660,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[860],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,170,1034,1034,864,1034,544,1034,1034,482,1034,0,1034,776,1034],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,10,1304,1304,1304,1304,8,1304,1304,1304,796,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1304,1272,1304,0,1304],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,1304,1348,546,22,1304,1348,544,20,1304,1348,1272,28,1304,1348,0,444,1304,1348],
[284]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_36 : (row5_36.zip hint5_36).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_37 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,242,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[853,476],
[464],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,696,0,0,0,0,0,0,1032,0,0,1304,0,1034,0,444,0,936,0],
[985,416],
[1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,160,1144,1144,1144,1144,1144,1144,1144,162,1144,1144,1144,1144,1144,1144,58,56,313,1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,860,1144,1128,1144,862,1144,1024,1144,1144,1048,1144],
[1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,1032,480,546,22,1032,480,864,1252,1032,480,778,534,1032,480,0,444,1032,480],
[60],
[852],
[796]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_37 : (row5_37.zip hint5_37).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_38 : List (List ℕ) := [
[868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,168,868,1120,868,256,868,170,868,868,1044,868],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,179,0,0,0,0,180,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,0,444,0,936,0],
[470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,470,238,470,8,470,1042,470,470,540,470,760,470],
[],
[1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,886,1266,520,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1340,1106,1340,1232,1340,770,1340,554,1340,1340,816,1340],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,164,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444],
[444,444,444,444,444,444,444,444,444,444,444,444,444,580,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,444,0,444,1160,444],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1150,0,0,0,0,0,0,0,0,0,0,242,0,0,1032,0,1304,0,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_38 : (row5_38.zip hint5_38).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_39 : List (List ℕ) := [
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034,1034],
[1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,546,1032,864,1032,480,1032,1032,778,1032,0,1032],
[620,620,620,620,620,620,620,620,620,620,822,820,1165,620,620,620,620,620,620,620,620,620,620,620,620,620,620,620,214,620,1100,620,620,620,620,620,620,620,620,212,620,1102,620,632,620,1284,620,920,620,634,620,620,1244,620],
[864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,864,1296,864,1252,864,864,1032,864,1236,864,1034,864],
[968],
[468,468,468,468,468,468,468,468,468,468,468,468,468,468,468,468,468,468,468,468,468,468,468,468,468,692,468,468,468,1134,468,468,468,468,10,468,236,468,1040,468,468,762,468,542,468],
[512],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[],
[248,248,248,248,248,248,248,248,248,248,248,248,568,248,248,248,688,248,248,248,248,570,248,248,248,248,248,248,248,248,248,908,248,248,248,1170,248,68,248,388,248,1168,248,1188,248,248]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_39 : (row5_39.zip hint5_39).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_40 : List (List ℕ) := [
[1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,1272,1304,406,546,1272,1304,404,544,1272,1304,28,1348,1272,1304,936,0,1272,1304],
[582],
[1042],
[0,0,0,0,0,0,0,0,318,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[1036,1106],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1084,1304,546,1304,544,1304,1348,1304,1304,1272,1304,0,1304],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,444,0,444,1160,444],
[1331,213,148],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,179,0,0,1136,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_40 : (row5_40.zip hint5_40).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_41 : List (List ℕ) := [
[354],
[331,419],
[436,437,324],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1304,1272,1304,0,1304],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,98,0,96,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[948],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,576,0,0,0,0,0,0,0,578,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[772],
[1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,270,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,546,1032,864,1032,480,1032,778,1032,0,1032],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_41 : (row5_41.zip hint5_41).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_42 : List (List ℕ) := [
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,936,0,936,776,936,1160,936],
[868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,868,168,868,1120,868,256,868,170,868,868,1044,868],
[176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,176,25,176,204,176,772,176,292,176,176,609,176],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,516,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,886,520,521,658,1036,658,1388,658,1180,658,658,278,658,279,658],
[1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1204,1134,1204,1204,1204,1204,1204,1204,1204,1132,1204,1204,1204,1204,646,1204,796,1204,644,1204,1204,1116,1204,1064,1204],
[150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,150,512,150,150,150,150,186,150,1300,150,129,150,973,150,150,121,150],
[268],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_42 : (row5_42.zip hint5_42).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_43 : List (List ℕ) := [
[417,416,470],
[1088],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,860,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,546,1032,864,1032,480,1032,778,1032,0,1032],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1128,1304,1304,220,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304],
[1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,1034,864,544,1296,1034,864,482,1252,1034,864,0,1032,1034,864,776,1236,1034,864],
[1216,290,394],
[360,748],
[232,892],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_43 : (row5_43.zip hint5_43).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_44 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[],
[],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1144,0,0,904,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304,1304],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304],
[],
[1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,546,1032,864,1032,480,1032,778,1032,1032,0,1032],
[0,0,0,0,0,0,0,0,0,0,0,780,0,0,0,0,0,0,0,782,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_44 : (row5_44.zip hint5_44).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_45 : List (List ℕ) := [
[],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[428,228,1368],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,1040,444,444,444,444,444,444,444,1042,444,444,444,444,480,444,1348,444,482,444,444,0,444,1160,444],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,672,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,444,1160,444],
[1228,1032],
[550,1213],
[1180,1392,730],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,542,936,936,936,936,936,936,936,252,936,936,540,936,1116,936,778,936,1272,936,0,936,776,936,1160,936,936],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,812,0,0,0,0,0,0,0,0,0,0,0,0,0,1144,0,1032,0,1304,0,1034,0,444,0,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_45 : (row5_45.zip hint5_45).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_46 : List (List ℕ) := [
[1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,546,1032,864,1032,480,1032,778,1032,0,1032],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,611,936,936,609,936,441,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936],
[1010],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1312,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,1034,482,1034,0,1034,776,1034],
[936],
[],
[658,372],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,306,948,304,948,1280,948,948,948,948,948,948,948,948,948,948,948,1320,948,988,948,990,948,1140,948,948,1360,948],
[278]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_46 : (row5_46.zip hint5_46).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_47 : List (List ℕ) := [
[770],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,0,1304,0,1034,0,444,0,936,0],
[1220],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,856,936,936,936,936,936,936,778,936,936,1272,936,0,936,776,936,1160,936],
[420,500,536],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,728,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[664,596],
[],
[496,444]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_47 : (row5_47.zip hint5_47).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_48 : List (List ℕ) := [
[328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,1344,328,360,328,328,900,328,140,328,428,328],
[936,936,936,936,936,936,936,936,936,936,936,1114,936,936,936,936,936,936,936,936,936,818,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[],
[240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,756,1092,702,240,240,240,240,240,240,240,240,240,240,240,928,240,226,240,472,240,378,240,240,86,240],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1260,0,0,0,0,0,0,0,0,392,0,0,0,288,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,992,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,784,0,0,0,0,0,0,0,786,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,238,1032,1032,1032,646,1032,1032,1032,1032,546,1032,864,1032,480,1032,1032,778,1032,0,1032],
[],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_48 : (row5_48.zip hint5_48).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_49 : List (List ℕ) := [
[0],
[],
[],
[956],
[0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,0,1204,1032,646,0,1204,1304,796,0,1204,1034,644,0,1204,444,0,1204,936,1116,0,1204,1064,0,1204],
[0,0,0,0,0,0,0,0,944,0,356,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,617,1077,560,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,1057,812,1057,272,273,312,1057,573,1057,604,1057,437,1057,476,1057,1057,452,1057],
[456,133],
[554],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_49 : (row5_49.zip hint5_49).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_50 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,358,0,1062,1032,358,0,334,1304,358,0,78,358,0,1034,358,0,464,444,358,0,1178,936,358,0],
[1304],
[672],
[0,0,0,0,0,0,0,0,0,904,0,0,0,0,0,0,0,0,0,620,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,0,444,0,936,0],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,294,444,292,444,1372,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444],
[0,0,0,0,0,0,0,0,0,0,0,266,0,0,0,0,0,0,0,264,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,1380,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444,444],
[444]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_50 : (row5_50.zip hint5_50).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_51 : List (List ℕ) := [
[508],
[1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,474,1032,1032,1032,1032,1032,546,1032,1032,864,1032,480,1032,778,1032,0,1032],
[],
[712,492,493,1224],
[338],
[636,133],
[444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,444,1348,480,22,444,1348,482,20,444,1348,0,1304,444,1348,1160,28,444,1348],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,844,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[1096],
[1372]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_51 : (row5_51.zip hint5_51).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_52 : List (List ℕ) := [
[444],
[99],
[1272],
[936,936,936,936,936,936,936,936,936,936,936,936,1176,936,936,936,364,936,936,936,940,936,936,1178,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[242,242,242,242,242,242,242,242,242,242,242,242,242,242,242,242,242,242,242,242,1094,758,524,242,242,242,242,242,242,242,242,242,242,242,474,242,224,242,930,242,242,376,242,84,242],
[344],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,712,117,1076,561,712,116,1077,560,712,712,712,712,712,712,712,712,712,1364,1165,1164,712,420,712,1016,712,1004,712,712,853,712,852,712],
[658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,1266,520,521,658,1036,658,1388,658,1180,658,658,278,658,279,658]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_52 : (row5_52.zip hint5_52).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_53 : List (List ℕ) := [
[308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,284,308,956,308,286,308,308,1332,308,892,308],
[1344,1301],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,44,936,936,778,936,1272,936,936,0,936,776,936,1160,936],
[692],
[244,1144],
[912,368,600],
[330,282],
[516,516,516,516,516,516,516,516,516,516,516,516,516,932,516,516,516,934,516,516,516,688,516,516,516,516,516,516,516,516,516,516,516,516,516,844,516,270,516,268,516,516,1152,516,364,516],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_53 : (row5_53.zip hint5_53).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_54 : List (List ℕ) := [
[12],
[16],
[0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,948,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,306,948,304,948,1280,948,948,948,948,948,948,948,948,948,948,1320,948,988,948,948,990,948,1140,948,1360,948],
[1308],
[936,936,936,936,936,936,936,936,936,936,936,936,410,936,936,936,936,936,936,44,936,936,408,936,936,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936,936],
[152,1074],
[400,1340,1002,160,1224],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,600,0,0,0,0,0,0,0,912,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_54 : (row5_54.zip hint5_54).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_55 : List (List ℕ) := [
[125],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[640,668,720],
[696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,696,62,696,210,696,696,316,696,580,696,166,696],
[605,980,604,1196],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,226,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,1304,0,1304],
[656,792],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,394,0,0,0,0,1216,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_55 : (row5_55.zip hint5_55).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_56 : List (List ℕ) := [
[],
[444,444,444,444,444,444,444,444,444,324,444,444,444,444,444,444,444,444,444,260,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,444,0,444,1160,444],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1304,1272,1304,0,1304],
[948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,948,306,948,304,948,1280,948,948,948,948,948,948,948,948,948,948,1320,948,988,948,990,948,1140,948,948,1360,948],
[1248],
[0,0,0,0,0,0,0,0,0,0,1002,0,1340,0,0,0,0,0,0,1000,0,1342,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[],
[1304],
[1268],
[0,0,0,0,0,0,0,0,0,0,0,1340,0,0,0,0,0,0,372,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_56 : (row5_56.zip hint5_56).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_57 : List (List ℕ) := [
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1084,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304,1304],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,624,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936],
[92,54,1144],
[1296],
[736],
[0],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,207,1304,205,1304,40,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304],
[1288,318],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_57 : (row5_57.zip hint5_57).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_58 : List (List ℕ) := [
[],
[720],
[1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,1160,534,1160,28,1160,444,1160,532,1160,936,1160,1160],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1352,1304,1304,546,1304,544,1304,1304,1348,1304,1272,1304,0,1304],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,336,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304,1304],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[0],
[142],
[516,516,516,516,516,516,516,516,516,516,516,516,516,932,516,516,516,516,934,516,516,688,516,516,516,516,516,516,516,516,516,516,516,516,516,844,516,270,516,516,268,516,1152,516,364,516],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,868,0,1032,0,1304,0,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_58 : (row5_58.zip hint5_58).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_59 : List (List ℕ) := [
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1194,1304,1192,1304,1384,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,672,444,444,444,444,444,480,444,444,1348,444,482,444,0,444,1160,444],
[],
[133,133,133,133,133,133,133,133,133,133,133,488,133,133,133,584,133,133,133,490,133,133,133,248,133,133,133,133,133,133,133,133,133,133,133,133,133,74,133,977,133,72,133,528,133,133,612,133],
[433,0],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1308,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034],
[876],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,284,308,956,308,286,308,308,1332,308,892,308]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_59 : (row5_59.zip hint5_59).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_60 : List (List ℕ) := [
[573,1128],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,582,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[260],
[],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,716,444,444,444,444,444,444,444,718,444,444,444,1380,444,480,444,1348,444,482,444,444,0,444,1160,444],
[0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,0,444,1032,480,0,444,1304,1348,0,444,1034,482,0,444,936,1160,0,444],
[620,620,620,620,620,620,620,620,620,620,822,820,144,620,620,620,620,620,620,620,620,620,620,620,620,1100,620,620,620,620,620,620,620,1102,620,620,632,620,1284,620,920,620,634,620,620,1244,620],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_60 : (row5_60.zip hint5_60).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_61 : List (List ℕ) := [
[328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,513,328,328,1344,328,360,328,900,328,328,140,328,428,328],
[],
[900,497],
[456],
[704],
[],
[868],
[308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,308,284,308,956,308,286,308,1332,308,892,308],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1204,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,896,0,1108,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_61 : (row5_61.zip hint5_61).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_62 : List (List ℕ) := [
[204],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444],
[658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,658,710,520,521,658,1036,658,1388,658,1180,658,658,278,658,279,658],
[356],
[416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,1228,416,748,416,497,416,416,1268,416,1368,416],
[864],
[1388,1278],
[0],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304,1304],
[282,280,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_62 : (row5_62.zip hint5_62).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_63 : List (List ℕ) := [
[896],
[236],
[1252],
[712,1056,1057,904],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,0,444,444,1160,444],
[776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,776,1034,1236,864,776,1034,404,544,776,1034,532,482,776,1034,936,0,776,1034],
[1184,208],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1120,1304,1304,1304,546,1304,1304,544,1304,1348,1304,1272,1304,0,1304],
[636],
[944]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_63 : (row5_63.zip hint5_63).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_64 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,1224,0,1340,0,0,0,0,0,0,0,794,0,0,620,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,0,444,0,936,0],
[240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,240,756,1092,1028,240,240,240,240,240,240,240,240,240,240,240,240,928,240,226,240,472,240,378,240,240,86,240],
[584],
[1096,444],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,156,444,158,444,848,444,444,444,444,444,444,444,1140,444,444,444,444,444,480,444,1348,444,482,444,0,444,1160,444],
[1032,1032,1032,1032,1032,1032,1032,1032,62,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,1032,546,1032,864,1032,1032,480,1032,778,1032,0,1032],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,1034,482,1034,0,1034,776,1034],
[396],
[0,0,0,0,0,0,0,0,0,0,0,0,0,696,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_64 : (row5_64.zip hint5_64).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_65 : List (List ℕ) := [
[620,0,620,0,620,0,620,0,620,0,620,0,620,0,620,0,620,0,620,0,822,820,1364,620,0,620,0,620,0,620,0,620,0,620,0,620,0,620,0,620,0,620,0,620,0,620,0,620,0,620,0,1100,620,0,620,0,620,0,620,0,620,0,620,0,620,0,620,0,1102,620,0,620,0,632,1032,620,0,1284,1304,620,0,920,620,0,634,1034,620,0,444,620,0,1244,936,620,0],
[360,187],
[936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,936,200,936,936,202,936,1156,936,936,936,936,936,936,936,936,936,936,936,778,936,1272,936,0,936,776,936,1160,936],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,0,14,0,16,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[1304],
[484,996],
[648],
[748,1304],
[516]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_65 : (row5_65.zip hint5_65).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_66 : List (List ℕ) := [
[113],
[0,0,0,0,0,0,0,0,0,0,0,356,0,0,0,516,0,0,0,358,0,0,0,248,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[400,620,794,792],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1124,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,0,1034,776,1034,1034],
[824],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,600,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0],
[248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,248,908,248,133,248,248,248,369,248,1170,248,68,248,388,248,1168,248,1188,248,248],
[720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,720,908,720,916,720,918,720,720,720,720,720,720,720,1280,720,720,720,720,720,882,720,1384,720,880,720,744,720,1156,720]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_66 : (row5_66.zip hint5_66).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_67 : List (List ℕ) := [
[416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,416,1228,416,748,416,416,497,416,1268,416,1368,416],
[],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,544,1034,482,1034,1034,0,1034,776,1034],
[832,600],
[],
[444,444,444,444,444,444,444,444,444,444,466,444,444,444,444,444,444,464,444,444,444,1188,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,482,444,444,0,444,1160,444],
[936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,936,0,778,1032,936,0,1272,1304,936,0,776,1034,936,0,1160,444,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,210,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,444,480,444,1348,444,444,482,444,0,444,1160,444],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1088,0,1220,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_67 : (row5_67.zip hint5_67).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_68 : List (List ℕ) := [
[80,1034],
[309,308,1204],
[600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,600,506,600,41,600,504,600,1173,600,600,441,600],
[248,1376,32],
[1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,1034,864,1034,1034,544,1034,482,1034,0,1034,776,1034],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,1304,0,1304],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,930,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1360,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,468,0,0,0,0,0,0,0,64,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,1304,546,1304,544,1304,1348,1304,1272,1304,0,1304]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_68 : (row5_68.zip hint5_68).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_69 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,720,0,0,0,0,0,0,0,640,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1150,0,966,0,0,0,0,0,0,0,0,1144,0,0,836,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[1016,572,573,220],
[1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,160,1144,1144,1144,1144,1144,162,1144,1144,1144,1144,1144,1144,804,58,56,1144,1144,1144,1144,1144,1144,1144,1144,1144,1144,860,1144,1128,1144,862,1144,1024,1144,1048,1144],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,256,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,394,0,392,0,720,0,0,0,0,0,0,0,948,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0],
[564],
[0,0,0,0,0,0,0,0,0,0,0,0,740,0,0,0,0,0,0,742,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,936,0,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_69 : (row5_69.zip hint5_69).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_70 : List (List ℕ) := [
[321],
[753],
[0],
[1204],
[1208],
[328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,328,1344,328,360,328,900,328,140,328,428,328],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,0,0,0,0,0,0,0,50,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,133,74,133,977,133,72,133,528,133,133,612,133],
[],
[0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,160,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,162,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,58,56,424,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,0,1144,1032,860,0,1144,1304,1128,0,1144,1034,862,0,1144,444,1024,0,1144,936,0,1144,1048,0,1144]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_70 : (row5_70.zip hint5_70).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_71 : List (List ℕ) := [
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,1034,0,444,0,0,936,0],
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,248,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1032,0,1304,0,0,1034,0,444,0,936,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_71 : (row5_71.zip hint5_71).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

theorem chk5 : ∀ S ∈ row5, ∃ H, verifyS width topMask 4 taus S row4 H = true := by
  intro S hS
  obtain ⟨r, hr, hS⟩ := List.mem_flatten.mp hS
  simp only [row5, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowsS_ok _ _ (by decide) chk5_0 S hS
  · exact rowsS_ok _ _ (by decide) chk5_1 S hS
  · exact rowsS_ok _ _ (by decide) chk5_2 S hS
  · exact rowsS_ok _ _ (by decide) chk5_3 S hS
  · exact rowsS_ok _ _ (by decide) chk5_4 S hS
  · exact rowsS_ok _ _ (by decide) chk5_5 S hS
  · exact rowsS_ok _ _ (by decide) chk5_6 S hS
  · exact rowsS_ok _ _ (by decide) chk5_7 S hS
  · exact rowsS_ok _ _ (by decide) chk5_8 S hS
  · exact rowsS_ok _ _ (by decide) chk5_9 S hS
  · exact rowsS_ok _ _ (by decide) chk5_10 S hS
  · exact rowsS_ok _ _ (by decide) chk5_11 S hS
  · exact rowsS_ok _ _ (by decide) chk5_12 S hS
  · exact rowsS_ok _ _ (by decide) chk5_13 S hS
  · exact rowsS_ok _ _ (by decide) chk5_14 S hS
  · exact rowsS_ok _ _ (by decide) chk5_15 S hS
  · exact rowsS_ok _ _ (by decide) chk5_16 S hS
  · exact rowsS_ok _ _ (by decide) chk5_17 S hS
  · exact rowsS_ok _ _ (by decide) chk5_18 S hS
  · exact rowsS_ok _ _ (by decide) chk5_19 S hS
  · exact rowsS_ok _ _ (by decide) chk5_20 S hS
  · exact rowsS_ok _ _ (by decide) chk5_21 S hS
  · exact rowsS_ok _ _ (by decide) chk5_22 S hS
  · exact rowsS_ok _ _ (by decide) chk5_23 S hS
  · exact rowsS_ok _ _ (by decide) chk5_24 S hS
  · exact rowsS_ok _ _ (by decide) chk5_25 S hS
  · exact rowsS_ok _ _ (by decide) chk5_26 S hS
  · exact rowsS_ok _ _ (by decide) chk5_27 S hS
  · exact rowsS_ok _ _ (by decide) chk5_28 S hS
  · exact rowsS_ok _ _ (by decide) chk5_29 S hS
  · exact rowsS_ok _ _ (by decide) chk5_30 S hS
  · exact rowsS_ok _ _ (by decide) chk5_31 S hS
  · exact rowsS_ok _ _ (by decide) chk5_32 S hS
  · exact rowsS_ok _ _ (by decide) chk5_33 S hS
  · exact rowsS_ok _ _ (by decide) chk5_34 S hS
  · exact rowsS_ok _ _ (by decide) chk5_35 S hS
  · exact rowsS_ok _ _ (by decide) chk5_36 S hS
  · exact rowsS_ok _ _ (by decide) chk5_37 S hS
  · exact rowsS_ok _ _ (by decide) chk5_38 S hS
  · exact rowsS_ok _ _ (by decide) chk5_39 S hS
  · exact rowsS_ok _ _ (by decide) chk5_40 S hS
  · exact rowsS_ok _ _ (by decide) chk5_41 S hS
  · exact rowsS_ok _ _ (by decide) chk5_42 S hS
  · exact rowsS_ok _ _ (by decide) chk5_43 S hS
  · exact rowsS_ok _ _ (by decide) chk5_44 S hS
  · exact rowsS_ok _ _ (by decide) chk5_45 S hS
  · exact rowsS_ok _ _ (by decide) chk5_46 S hS
  · exact rowsS_ok _ _ (by decide) chk5_47 S hS
  · exact rowsS_ok _ _ (by decide) chk5_48 S hS
  · exact rowsS_ok _ _ (by decide) chk5_49 S hS
  · exact rowsS_ok _ _ (by decide) chk5_50 S hS
  · exact rowsS_ok _ _ (by decide) chk5_51 S hS
  · exact rowsS_ok _ _ (by decide) chk5_52 S hS
  · exact rowsS_ok _ _ (by decide) chk5_53 S hS
  · exact rowsS_ok _ _ (by decide) chk5_54 S hS
  · exact rowsS_ok _ _ (by decide) chk5_55 S hS
  · exact rowsS_ok _ _ (by decide) chk5_56 S hS
  · exact rowsS_ok _ _ (by decide) chk5_57 S hS
  · exact rowsS_ok _ _ (by decide) chk5_58 S hS
  · exact rowsS_ok _ _ (by decide) chk5_59 S hS
  · exact rowsS_ok _ _ (by decide) chk5_60 S hS
  · exact rowsS_ok _ _ (by decide) chk5_61 S hS
  · exact rowsS_ok _ _ (by decide) chk5_62 S hS
  · exact rowsS_ok _ _ (by decide) chk5_63 S hS
  · exact rowsS_ok _ _ (by decide) chk5_64 S hS
  · exact rowsS_ok _ _ (by decide) chk5_65 S hS
  · exact rowsS_ok _ _ (by decide) chk5_66 S hS
  · exact rowsS_ok _ _ (by decide) chk5_67 S hS
  · exact rowsS_ok _ _ (by decide) chk5_68 S hS
  · exact rowsS_ok _ _ (by decide) chk5_69 S hS
  · exact rowsS_ok _ _ (by decide) chk5_70 S hS
  · exact rowsS_ok _ _ (by decide) chk5_71 S hS

def hint6_0 : List (List ℕ) := [
[2612,109,1678,1728,109,1678,109,1678,109,1678,109,1678,109,1678,109,1678,109,1678,109,1678,1494,109,1678,1772,109,1678,914,1716,109,1678,167,1587,109,1678,1558,856,109,1678,1492,109,1678,1692,109,1678,1012,109,1678,1525,109,1678,2784,109,1678,912,109,1678,165,109,1678,1192,109,1678,1556,109,1678,688,109,1678,1129,109,1678,2356,109,1678,615,109,1678,2594,1184,109,1678,2016,1631,109,1678,2278,109,1678,1482,109,1678,2592,109,1678,2644,109,1678,725,109,1678,819,109,1678,2172,109,1678,2276,109,1678,1676,109,1678,1108,109,1678,1480,109,1678,2205,109,1678,1043,109,1678,600,109,1678,658,391,299,109,1678,900,581,1144,109,1678,656,389,1561,109,1678,2428,1252,1069,109,1678,521,109,1678,154,109,1678,393,75,2704,109,1678],
[2612,2592,109,1728,2592,109,2592,109,2592,109,2592,109,2592,109,2592,109,2592,109,2592,109,1494,2592,109,1772,2592,109,304,2592,109,914,2592,109,167,2592,109,1558,2592,109,1492,2212,1084,881,2592,109,1692,2592,109,1012,2592,109,2784,2592,109,912,2592,109,165,2592,109,1556,2592,109,1282,2592,109,1639,2592,109,1936,2592,109,688,2592,109,2356,2592,109,2594,2592,109,2016,2592,109,92,2592,109,2278,2592,109,1678,2592,109,1482,2592,109,2644,2592,109,725,2592,109,2172,2592,109,2276,2592,109,1676,1186,2592,109,1480,1746,2592,109,302,2592,109,817,2592,109,1204,2592,109,2205,2592,109,600,2592,109,658,2580,391,2592,109,900,1148,581,2592,109,656,2584,389,2592,109,1614,2592,109,1552,2428,1252,2592,109,521,2592,109,982,393,2704,2592,109],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,41,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2628,2156,1576,2156,864,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,511,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,2049,2049,2049,2049,1970,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2084,2156,2086,2156,2344,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1657,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1432,2268,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,2437,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,1592,256,996,581,580,1592,256,1592,256,1592,256,118,526,1592,256,116,524,1592,256,1116,740,1592,256,2088,1593,1592,256,2049,2156,1592,256],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2520,2156,1177,2156,1176,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2476,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2612,521,109,1728,521,109,521,109,521,109,521,109,521,109,521,109,521,109,521,109,1494,521,109,1772,521,109,914,521,109,934,521,109,167,521,109,1558,521,109,1492,521,109,1692,521,109,925,521,109,1012,521,109,2784,521,109,912,521,109,932,521,109,165,521,109,1556,521,109,965,521,109,688,521,109,2356,521,109,644,2304,733,521,109,2594,521,109,2016,521,109,2278,521,109,1217,521,109,1678,521,109,1482,521,109,2592,521,109,2644,521,109,844,521,109,725,521,109,2172,521,109,2276,521,109,1219,521,109,1676,521,109,1480,521,109,1796,521,109,2205,521,109,600,521,109,658,1564,391,521,109,900,997,581,521,109,656,1566,389,521,109,2428,681,1252,521,109,1380,393,2704,521,109],
[1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,1076,2132,1076,1076,1076,1076,1076,1076,1076,1076,1076,548,1076,1076,1076,1076,1582,1533,1532,1076,1076,1076,2526,1076,660,1076,1608,1076,1076,1164,1076,1165,1076,1362,1076]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_0 : (row6_0.zip hint6_0).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_1 : List (List ℕ) := [
[1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,756,2116,2488,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,88,700,701,1864,418,1864,2504,1864,1828,1864,1864,2188,1864,398,1864,399,1864],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,96,109,108,2156,958,2156,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1644,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,1679,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[616,1451,2144,50,1208,1631],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,460,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1252,1624,1253,788,788,788,788,266,788,740,788,264,788,1161,788,788,2156,788,1160,788],
[958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,1840,391,390,958,958,958,526,958,2500,958,266,958,483,958,482,958,2156,958],
[1956,2612,392,2704,108,668,1728,392,2704,108,392,2704,108,392,2704,108,392,2704,108,392,2704,108,392,2704,108,392,2704,108,392,2704,108,1544,1494,392,2704,108,2288,786,392,2704,108,720,1772,392,2704,108,84,914,392,2704,108,679,166,392,2704,108,334,1558,392,2704,108,1892,920,392,2704,108,1546,1492,392,2704,108,604,1692,392,2704,108,1845,1013,392,2704,108,2608,2784,392,2704,108,2290,784,392,2704,108,2128,2780,392,2704,108,86,912,392,2704,108,677,164,392,2704,108,332,1556,392,2704,108,1680,689,392,2704,108,972,2356,392,2704,108,980,2594,392,2704,108,188,1316,392,2704,108,1124,2016,392,2704,108,1924,2278,392,2704,108,74,1679,392,2704,108,414,1482,392,2704,108,440,1996,392,2704,108,982,2592,392,2704,108,2092,2644,392,2704,108,1776,724,392,2704,108,1352,2172,392,2704,108,190,1318,392,2704,108,2184,2024,392,2704,108,1052,428,1761,392,2704,108,1926,2276,392,2704,108,72,1677,392,2704,108,412,1480,392,2704,108,860,2204,392,2704,108,1696,600,392,2704,108,468,658,730,2542,390,392,2704,108,596,900,1237,1600,580,392,2704,108,470,728,2540,656,388,392,2704,108,1292,2328,1428,2428,1253,392,2704,108,1381,520,392,2704,108],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,1768,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2664,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1864,2156,2156,2156,2156,2156,912,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_1 : (row6_1.zip hint6_1).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_2 : List (List ℕ) := [
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,1823,956,956,956,956,956,1155,956,956,956,956,956,956,956,956,956,916,389,388,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,924,109,108,2156,958,2156,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,928,109,108,2156,958,2156,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,644,2048,2048,2048,2048,2048,1166,2048,2048,2048,2048,2048,2048,2048,2048,2048,1164,2048,2048,2048,2264,2048,2048,428,2048,483,2048,1593,2048,481,2048,1161,2048,2156,2048,2048,1856,2048],
[2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,2156,958,109,108,658,391,390,2156,958,2156,958,2156,958,256,526,2156,958,956,2500,2156,958,788,266,2156,958,2048,483,2156,958,2049,482,2156,958],
[958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,418,958,958,958,958,958,958,958,958,958,2040,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,1244,391,390,958,958,958,526,958,2500,958,266,958,958,483,958,482,958,2156,958],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2612,109,108,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2160,2156,2162,2156,2164,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2616,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2640,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,1109,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[256,256,256,256,256,256,256,256,256,256,256,1072,256,256,256,256,2504,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,1114,581,580,256,256,256,526,256,524,256,740,256,256,1593,256,1592,256,2156,256]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_2 : (row6_2.zip hint6_2).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_3 : List (List ℕ) := [
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,21,788,788,788,788,788,788,788,788,788,788,1916,788,788,788,788,2449,788,788,836,1252,1253,788,788,266,788,740,788,788,264,788,1161,788,2156,788,1160,788],
[2612,108,1482,1728,108,1482,108,1482,108,1482,108,1482,108,1482,108,1482,108,1482,108,1482,1494,108,1482,1772,108,1482,914,1756,108,1482,166,108,1482,1558,2098,2564,1932,108,1482,1492,108,1482,1692,108,1482,1013,108,1482,2784,108,1482,2236,108,1482,912,108,1482,164,108,1482,1556,108,1482,2764,108,1482,689,108,1482,2356,108,1482,1400,108,1482,2594,1744,108,1482,2016,674,108,1482,2278,108,1482,1679,108,1482,2592,108,1482,2644,108,1482,724,108,1482,2172,108,1482,1206,108,1482,2276,108,1482,1677,108,1482,1480,1272,108,1482,752,108,1482,2204,108,1482,600,108,1482,1410,108,1482,658,390,1792,108,1482,900,580,2228,108,1482,656,388,192,108,1482,2428,1253,1278,108,1482,520,108,1482,392,2704,414,108,1482,1348,108,1482],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1388,2156,2156,2156,2156,2156,2156,2156,2156,2156,1390,2156,2156,2156,2156,2156,2305,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1797,109,108,2156,958,2156,256,2156,956,2156,788,2156,2156,2048,2156,2049,2156],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049,2049],
[958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,958,526,391,390,852,1250,1251,958,526,958,526,958,526,958,526,958,526,958,526,2500,2296,958,526,266,796,958,526,483,119,958,526,482,118,958,526,2156,256,958,526],
[1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,756,1700,2488,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,1864,622,700,701,1864,418,1864,2504,1864,1828,1864,1864,2188,1864,398,1864,399,1864],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,52,2156,2156,2156,2156,2156,109,108,1337,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,2156,429,109,108,1760,2156,429,958,2242,2156,429,256,2437,2156,429,956,2240,2156,429,788,497,2156,429,2048,820,2156,429,2049,2156,429,2304,2156,429],
[2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,644,1433,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,2048,1593,428,2436,2048,1593,2048,1593,2048,1593,483,119,2048,1593,481,117,2048,1593,1161,1117,2048,1593,2156,256,2048,1593,1856,2088,2048,1593],
[2612,167,108,1728,167,108,167,108,167,108,167,108,167,108,167,108,167,108,167,108,509,167,108,1268,167,108,1494,167,108,1772,167,108,914,167,108,166,167,108,1558,167,108,1492,167,108,1692,167,108,1013,167,108,2784,167,108,912,167,108,164,167,108,1556,167,108,689,167,108,2356,167,108,196,167,108,422,566,1422,167,108,748,167,108,614,167,108,2594,167,108,2016,167,108,2278,167,108,1679,167,108,1482,167,108,2592,167,108,2644,167,108,724,167,108,2172,167,108,2276,167,108,1677,167,108,1480,167,108,2204,167,108,600,167,108,1339,167,108,427,658,390,167,108,273,900,580,167,108,917,656,388,167,108,839,2428,1253,167,108,520,167,108,678,392,2704,167,108]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_3 : (row6_3.zip hint6_3).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_4 : List (List ℕ) := [
[2612,688,108,1728,688,108,688,108,688,108,688,108,688,108,688,108,688,108,688,108,1268,688,108,1656,688,108,1270,688,108,1494,688,108,1772,688,108,914,688,108,166,688,108,1558,688,108,1492,688,108,1692,688,108,1013,688,108,2784,688,108,912,688,108,164,688,108,1556,688,108,689,688,108,2356,688,108,142,688,108,1424,688,108,140,688,108,1233,688,108,2594,688,108,2016,688,108,2278,688,108,1679,688,108,1482,688,108,2592,688,108,2644,688,108,724,688,108,2172,688,108,2276,688,108,1677,688,108,1480,688,108,2204,688,108,600,688,108,516,688,108,366,658,390,688,108,829,900,580,688,108,364,656,388,688,108,504,2428,1253,688,108,520,688,108,1681,392,2704,688,108],
[2612,2644,108,1728,2644,108,2644,108,2644,108,2644,108,2644,108,2644,108,2644,108,2644,108,1494,2644,108,1772,2644,108,914,2644,108,2006,792,158,2644,108,166,2644,108,1558,2644,108,1492,2644,108,1692,2352,2148,1140,2644,108,1013,2644,108,2784,2644,108,912,2644,108,2004,794,156,2644,108,164,2644,108,1556,2644,108,689,2644,108,2356,2644,108,2661,2644,108,1596,2672,488,2644,108,2594,2644,108,2016,2644,108,2278,2644,108,300,2644,108,1679,2644,108,1482,2644,108,2592,2644,108,724,2644,108,2172,2644,108,2276,2644,108,302,2644,108,1677,2644,108,1480,2644,108,2204,2141,2644,108,600,2208,2644,108,457,2644,108,2796,2644,108,658,1190,390,2644,108,900,848,580,2644,108,656,1188,388,2644,108,2428,2700,1253,2644,108,1056,2644,108,520,2644,108,2092,392,2704,2644,108],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,317,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[2612,108,2172,1728,108,2172,108,2172,108,2172,108,2172,108,2172,108,2172,108,2172,108,2172,1494,108,2172,1772,108,2172,914,108,2172,166,108,2172,1558,108,2172,1470,108,2172,1492,108,2172,1692,108,2172,1013,108,2172,2784,2176,1873,2252,108,2172,912,108,2172,164,108,2172,1556,108,2172,1468,108,2172,689,108,2172,2356,108,2172,1048,108,2172,2594,108,2172,2016,108,2172,2278,108,2172,1679,108,2172,1482,108,2172,1206,108,2172,2592,108,2172,2644,108,2172,724,108,2172,2276,108,2172,1677,108,2172,1480,108,2172,1204,108,2172,2204,108,2172,600,108,2172,2796,108,2172,658,390,354,108,2172,900,580,2740,108,2172,656,388,352,108,2172,2428,1253,104,108,2172,520,108,2172,392,2704,1352,108,2172,2748,108,2172],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,1168,2156,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,581,580,1784,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256],
[788,788,788,788,788,788,788,788,788,788,1648,788,788,788,788,788,788,788,788,788,788,788,788,788,2416,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,2244,1252,1253,788,788,266,788,740,788,264,788,788,1161,788,2156,788,1160,788],
[464,464,464,464,464,464,464,464,464,464,464,464,464,464,464,464,464,1039,464,464,464,2568,464,464,464,1037,464,464,464,780,464,464,464,464,2456,464,228,2372,2828,464,464,464,464,464,464,464,464,464,464,464,464,464,2696,464,214,464,405,464,212,464,716,464,464,36,464],
[958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,391,390,186,958,958,958,526,958,2500,958,266,958,483,958,482,958,2156,958],
[956,956,956,956,956,956,956,956,956,956,956,446,956,956,956,956,1712,956,956,956,956,956,956,956,212,956,1264,956,213,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,1188,389,388,956,956,2500,956,524,956,264,956,956,481,956,2156,956,480,956]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_4 : (row6_4.zip hint6_4).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_5 : List (List ℕ) := [
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,370,956,956,956,956,956,956,956,956,956,956,1478,956,956,956,956,364,389,388,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2052,2156,698,2156,2156,2156,2156,2156,2156,2156,2156,2156,2234,2156,2156,2156,1156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2560,109,108,2156,958,2156,256,2156,956,2156,2156,788,2156,2048,2156,2049,2156],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,416,956,956,956,956,956,956,956,956,956,956,956,956,284,389,388,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,403,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,1728,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,1457,958,1456,958,958,958,958,958,958,958,958,958,958,958,958,958,1732,391,390,958,958,958,958,526,958,2500,958,266,958,483,958,482,958,2156,958],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,1092,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2594,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,750,109,108,2156,958,2156,256,2156,956,2156,788,2156,2156,2048,2156,2049,2156],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1606,788,788,788,788,788,788,788,788,2406,1252,1253,788,788,266,788,788,740,788,264,788,1161,788,2156,788,1160,788],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,2792,956,956,956,1404,389,388,956,956,2500,956,524,956,956,264,956,481,956,2156,956,480,956]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_5 : (row6_5.zip hint6_5).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_6 : List (List ℕ) := [
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,1485,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,1512,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,2049,1160,2049,1856,2049],
[2280,256,581,580,1784,256,581,580,256,581,580,256,581,580,256,581,580,256,581,580,256,581,580,256,581,580,256,581,580,1736,256,581,580,892,256,581,580,273,256,581,580,272,256,581,580,30,256,581,580,1334,256,581,580,894,256,581,580,275,256,581,580,274,256,581,580,28,256,581,580,1332,256,581,580,829,256,581,580,828,256,581,580,2548,256,581,580,2332,256,581,580,1464,256,581,580,1653,256,581,580,1652,256,581,580,1620,256,581,580,12,256,581,580,1112,256,581,580,1144,256,581,580,1145,256,581,580,2228,256,581,580,2338,256,581,580,1114,256,581,580,1146,256,581,580,1147,256,581,580,2230,256,581,580,2336,256,581,580,1781,256,581,580,1780,256,581,580,968,256,581,580,1120,256,581,580,2512,256,581,580,2513,256,581,580,2284,256,581,580,1082,526,1250,1251,256,581,580,1080,524,1248,1249,256,581,580,1472,740,381,380,256,581,580,1593,997,256,581,580,1592,996,256,581,580,1236,1237,1600,256,581,580,2156,109,108,900,256,581,580],
[990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,990,2624,990,1826,990,294,990,990,990,990,990,990,990,990,310,990,990,990,990,990,990,990,953,648,1688,990,990,1308,990,2480,990,1668,990,202,990,2371,990,586,990],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1848,788,788,788,1032,1252,1253,788,788,266,788,740,788,788,264,788,1161,788,2156,788,1160,788],
[2612,1842,109,656,389,1728,184,109,656,389,109,656,389,109,656,389,109,656,389,109,656,389,109,656,389,109,656,389,109,656,389,1494,112,109,656,389,1772,1734,109,656,389,914,284,109,656,389,167,917,109,656,389,2664,144,109,656,389,1558,2046,109,656,389,1492,2736,109,656,389,1692,1674,109,656,389,1012,947,109,656,389,1356,2380,109,656,389,2784,120,109,656,389,912,454,109,656,389,165,425,109,656,389,1556,1852,109,656,389,688,364,109,656,389,2412,1404,109,656,389,2356,1460,109,656,389,1904,2689,109,656,389,168,432,109,656,389,2594,2582,109,656,389,2016,68,109,656,389,2278,1246,109,656,389,1678,1561,109,656,389,2840,244,109,656,389,1482,192,109,656,389,2592,2584,109,656,389,2644,1188,109,656,389,725,842,109,656,389,2028,960,109,656,389,2172,352,109,656,389,2276,592,109,656,389,1676,297,109,656,389,1480,1794,109,656,389,2205,1229,109,656,389,24,340,109,656,389,600,1088,109,656,389,316,905,109,656,389,1376,2652,109,656,389,658,1740,391,1742,1572,109,656,389,900,854,581,1080,1248,109,656,389,2428,1252,540,1506,813,109,656,389,521,1566,109,656,389,393,470,2704,729,2540,109,656,389],
[336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,2060,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,336,2468,652,2120,336,336,688,109,1233,336,336,368,336,1196,336,370,336,2036,336,2444,336,760,336],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2800,2156,2804,2156,2508,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1269,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,1340,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2156,2049,2156],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,2449,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1252,1253,1070,788,788,788,788,266,788,740,788,264,788,1161,788,2156,788,1160,788,788],
[2612,2356,109,1728,2356,109,2356,109,2356,109,2356,109,2356,109,2356,109,2356,109,2356,109,1494,2356,109,472,2356,109,1772,2356,109,914,2356,109,167,2356,109,1558,2356,109,1312,2356,109,1492,2356,109,1692,2356,109,1012,2356,109,2732,2784,2356,109,474,2356,109,688,2356,109,912,2356,109,165,2356,109,1556,2356,109,2594,2356,109,1240,2356,109,2016,2356,109,2278,2356,109,1678,2356,109,1482,2356,109,2844,2356,109,2592,2356,109,2644,2356,109,725,2356,109,2172,2356,109,1242,2356,109,1232,2356,109,2276,2356,109,1676,2356,109,1480,2356,109,2464,2205,2356,109,948,1685,1520,600,2356,109,658,1462,391,2356,109,900,2548,581,2356,109,2776,2356,109,1460,656,389,2356,109,2712,2428,1252,2356,109,521,2356,109,972,393,2704,2356,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_6 : (row6_6.zip hint6_6).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_7 : List (List ℕ) := [
[633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,308,633,310,633,76,633,1212,633,633,633,633,633,633,633,633,633,633,633,633,633,2684,633,633,608,633,1967,633,1965,633,460,633,633,1132,633,936,633],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2002,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,2036,788,788,788,788,788,788,788,788,788,788,788,788,788,504,1252,1253,788,788,788,266,788,740,788,264,788,1161,788,2156,788,1160,788],
[788,788,788,788,788,788,788,788,788,788,788,1490,788,788,788,788,788,788,788,788,1488,788,788,788,788,716,788,717,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,2700,1252,1253,788,788,266,788,740,788,264,788,788,1161,788,2156,788,1160,788],
[2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,645,2305,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,429,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,2049,2156,520,109,108,2049,2156,482,958,2049,2156,1592,256,2049,2156,480,956,2049,2156,1160,788,2049,2156,1856,2048,2049,2156],
[788,788,788,788,788,788,788,788,788,1604,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1554,1252,1253,788,788,266,788,740,788,788,264,788,1161,788,2156,788,1160,788],
[2612,1556,108,1728,1556,108,1556,108,1556,108,1556,108,1556,108,1556,108,1556,108,1556,108,1494,1556,108,1772,1556,108,914,1556,108,166,1556,108,1558,1556,108,1106,1556,108,1492,1556,108,1692,1556,108,1013,1556,108,2784,1556,108,474,1556,108,164,1556,108,912,1556,108,689,1556,108,2356,1556,108,2594,1556,108,744,160,32,1556,108,2016,1556,108,2278,1556,108,1679,1556,108,1482,1556,108,984,1556,108,2592,1556,108,2644,1556,108,724,1556,108,2172,1556,108,56,1556,108,612,1556,108,2276,1556,108,859,1677,1556,108,2096,2566,1934,1480,1556,108,2204,1556,108,600,1556,108,658,2044,390,1556,108,900,28,580,1556,108,2744,1556,108,1852,656,388,1556,108,1172,2428,1253,1556,108,520,1556,108,332,392,2704,1556,108],
[256,256,256,256,256,256,256,256,256,2768,256,256,256,256,256,256,256,256,256,288,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,12,581,580,256,256,256,526,256,524,256,256,740,256,1593,256,1592,256,2156,256],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,50,2156,2156,48,2156,2156,2516,2156,2156,2156,2156,2144,2156,2156,2156,2156,2156,2156,2156,2146,2156,2156,2156,2156,1285,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2492,2156,2156,2156,2156,2636,2156,2156,2156,2156,2494,2156,2156,2156,2156,2156,464,2156,465,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2644,109,108,2156,958,2156,256,2156,956,2156,788,2156,2156,2048,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_7 : (row6_7.zip hint6_7).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_8 : List (List ℕ) := [
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,1311,956,315,956,361,956,2300,956,956,956,956,956,956,956,956,956,1964,956,956,956,956,956,946,389,388,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956],
[633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,308,633,310,633,76,633,1212,2420,633,633,633,633,633,633,633,633,633,633,633,633,633,633,633,608,633,1967,633,633,1965,633,460,633,1132,633,936,633],
[464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,2456,356,464,2156,228,172,2828,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,464,2156,2588,464,2156,464,2156,2660,109,108,464,2156,2696,464,2156,214,958,464,2156,405,256,464,2156,212,956,464,2156,716,788,464,2156,2048,464,2156,36,2049,464,2156],
[2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,60,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,62,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,1327,1325,1985,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,2156,1372,109,1837,108,2156,1372,1225,1500,1224,2156,1372,958,1457,2156,1372,256,2401,2156,1372,956,1459,2156,1372,788,1061,2156,1372,2048,2156,1372,1417,2156,1372,2049,1008,2156,1372],
[956,956,956,956,956,956,956,956,956,956,956,956,956,1155,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,389,388,1560,956,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956,956],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1028,2156,2156,2156,2156,2156,2156,2156,2156,2156,1076,2156,1497,2156,2156,2156,2156,512,2156,109,2755,108,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2156,2049,2156],
[2612,1492,108,1728,1492,108,1492,108,1492,108,1492,108,1492,108,1492,108,1492,108,1492,108,2476,1492,108,1494,1492,108,1772,1492,108,914,1492,108,166,1492,108,1558,1492,108,486,1492,108,510,1492,108,1106,1492,108,1692,1492,108,1013,1492,108,2784,1492,108,8,912,1492,108,164,1492,108,1556,1492,108,689,1492,108,2356,1492,108,1530,1492,108,2594,1492,108,2016,1492,108,2278,1492,108,1679,1492,108,1482,1492,108,124,1492,108,82,1492,108,2408,1492,108,2212,1084,880,2592,1492,108,2644,1492,108,724,1492,108,2172,1492,108,2276,1492,108,1677,1492,108,1480,1492,108,2204,1492,108,600,1492,108,658,114,390,1492,108,2708,1492,108,1066,900,580,1492,108,2736,656,388,1492,108,2406,2428,1253,1492,108,520,1492,108,1546,392,2704,1492,108],
[2612,2278,109,1728,2278,109,2278,109,2278,109,2278,109,2278,109,2278,109,2278,109,2278,109,1494,2278,109,1772,2278,109,914,620,90,702,2278,109,167,2278,109,1558,2278,109,1492,2278,109,1692,2278,109,98,2278,109,1012,2278,109,2784,2278,109,912,2278,109,128,64,1542,2278,109,165,2278,109,1556,2278,109,688,2278,109,2356,2278,109,46,2278,109,2388,2278,109,2594,2278,109,2016,2278,109,1678,2278,109,1482,2278,109,2592,2278,109,2644,2278,109,300,2278,109,725,2278,109,2172,2278,109,2276,2278,109,1384,2278,109,1676,2278,109,1480,2278,109,2205,2278,109,600,2278,109,1043,2278,109,1410,2278,109,658,594,391,2278,109,900,1112,581,2278,109,656,1246,389,2278,109,2428,1436,1252,2278,109,250,2278,109,521,2278,109,1924,393,2704,2278,109],
[1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,2468,652,2396,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,2256,1321,1476,1321,1972,1321,1478,1321,1321,1768,1321,1752,1321],
[2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,2156,788,109,2428,108,1252,1253,2156,788,2156,788,958,266,2156,788,256,740,2156,788,956,264,2156,788,2048,1161,2156,788,2049,1160,2156,788]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_8 : (row6_8.zip hint6_8).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_9 : List (List ℕ) := [
[1156,1156,1156,1156,1156,1156,1156,1156,1156,1156,1156,942,940,1368,1156,1156,1156,1156,1156,1156,1156,1156,1156,1156,1156,1156,1156,1156,1156,1156,1156,1156,1451,1156,1450,1156,1156,1156,1156,1156,1156,1156,1156,1156,1449,1156,1448,1156,1156,1156,2432,1568,1569,1156,268,1156,288,1156,1200,1156,270,1156,1156,1513,1156,1512,1156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,554,2156,2156,2156,2156,2156,2156,2156,2156,2156,552,2156,2156,2156,2156,372,2156,109,2824,108,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2156,2049,2156],
[2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,644,2048,2048,2048,2048,2048,2048,2048,396,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,428,2048,2048,483,2048,1593,2048,481,2048,1161,2048,2156,2048,1856,2048],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1025,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,2720,956,976,956,2689,389,388,956,956,2500,956,524,956,264,956,956,481,956,2156,956,480,956],
[2612,804,108,1728,804,108,804,108,804,108,804,108,804,108,804,108,804,108,804,108,1494,804,108,1772,804,108,914,804,108,166,804,108,1558,804,108,1492,804,108,1692,804,108,2616,804,108,1013,804,108,2784,804,108,912,804,108,164,804,108,1556,804,108,689,804,108,2356,804,108,2594,804,108,2016,804,108,2278,804,108,530,1580,1534,804,108,1679,804,108,1482,804,108,2592,804,108,2644,804,108,2104,804,108,724,804,108,2172,804,108,2276,804,108,528,1582,1532,804,108,1677,804,108,1480,804,108,1976,1704,1396,804,108,2204,804,108,600,804,108,658,1948,390,804,108,900,1464,580,804,108,656,1950,388,804,108,2428,1812,1253,804,108,1940,804,108,520,804,108,1832,392,2704,804,108],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,1877,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,399,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,2049,1856,2049],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2188,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,4,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,248,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1252,1253,1444,788,788,266,788,740,788,264,788,1161,788,2156,788,1160,788],
[956,956,956,956,956,956,956,956,956,956,956,956,2384,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,389,244,388,956,956,956,2500,956,524,956,264,956,481,956,2156,956,956,480,956]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_9 : (row6_9.zip hint6_9).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_10 : List (List ℕ) := [
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,2172,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,226,2156,224,2156,2324,2156,877,2156,876,2156,2156,2156,2156,2156,2156,2156,2156,765,2156,764,2156,2156,2156,2156,2156,2156,2784,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,1749,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,581,580,1147,256,256,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256,256],
[2612,1012,109,1728,1012,109,1012,109,1012,109,1012,109,1012,109,1012,109,1012,109,1012,109,509,1012,109,511,1012,109,1656,1012,109,1494,1012,109,1772,1012,109,914,1012,109,167,1012,109,1558,1012,109,1492,1012,109,1692,1012,109,2784,1012,109,912,1012,109,165,1012,109,1556,1012,109,688,1012,109,2356,1012,109,955,910,650,1012,109,953,908,648,1012,109,493,1289,2728,1012,109,2594,1012,109,2016,1012,109,2278,1012,109,1678,1012,109,1482,1012,109,2592,1012,109,2644,1012,109,2684,725,1012,109,2172,1012,109,2276,1012,109,1676,1012,109,1480,1012,109,2205,1012,109,600,1012,109,1944,1012,109,945,658,391,1012,109,2309,900,581,1012,109,947,656,389,1012,109,2020,2428,1252,1012,109,521,1012,109,1844,393,2704,1012,109],
[480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,532,132,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,480,956,2240,480,956,480,956,480,956,480,956,480,956,480,956,1567,389,388,480,956,480,956,1537,2500,480,956,116,524,480,956,278,264,480,956,538,481,480,956,2049,2156,480,956],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1384,109,108,2156,958,2156,256,2156,956,2156,788,2156,2156,2048,2156,2049,2156],
[502,500,1372,1208],
[2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2060,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,2156,336,652,2120,2396,2156,336,2156,336,109,108,1233,2156,336,958,368,2156,336,256,1196,2156,336,956,370,2156,336,788,2036,2156,336,2048,2444,2156,336,2049,2156,336,760,2156,336],
[2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,644,2048,2048,2048,2048,2048,1764,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,428,2048,2048,483,2048,1593,2048,481,2048,1161,2048,2156,2048,1856,2048],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1346,1252,1253,788,788,266,788,740,788,788,264,788,1161,788,2156,788,1160,788]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_10 : (row6_10.zip hint6_10).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_11 : List (List ℕ) := [
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,568,2156,573,2156,572,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,92,109,108,2156,958,2156,256,2156,956,2156,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,576,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,2068,2156,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,884,956,956,956,956,956,956,956,956,956,956,956,557,956,956,956,956,956,956,424,389,388,956,2500,956,524,956,956,264,956,481,956,2156,956,480,956],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,633,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,725,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2156,2049,2156],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,2584,389,388,956,956,2500,956,524,956,956,264,956,481,956,2156,956,480,956],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1642,2156,2156,2156,2156,2156,2156,2156,2156,1640,2156,2156,2156,2156,1392,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,456,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,2056,256,256,256,256,256,256,256,256,1334,581,580,256,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,24,2156,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,2468,2120,2396,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,1321,376,1321,1321,2256,1321,1476,1321,1972,1321,1478,1321,1321,1768,1321,1752,1321],
[2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,645,532,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,429,2240,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,2049,480,482,1537,2049,480,1592,116,2049,480,2156,956,2049,480,1160,278,2049,480,1856,538,2049,480]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_11 : (row6_11.zip hint6_11).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_12 : List (List ℕ) := [
[2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,644,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,1045,2048,2048,2048,2048,2048,2048,2048,2048,428,2048,2048,483,2048,1593,2048,481,2048,1161,2048,2156,2048,1856,2048],
[1718],
[1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,942,940,2112,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1451,1156,2156,1450,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1156,2156,1449,1156,2156,1448,1156,2156,1156,2156,1156,2156,2600,1568,1569,109,108,1156,2156,268,958,1156,2156,288,256,1156,2156,1200,1156,2156,270,956,1156,2156,788,1156,2156,1513,2048,1156,2156,1512,2049,1156,2156],
[2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,645,345,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,429,497,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,2049,1160,482,276,2049,1160,1592,1116,2049,1160,2156,788,2049,1160,480,278,2049,1160,1856,1304,2049,1160],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,1973,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,581,580,1780,256,256,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256,256],
[210,436,988,1184],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,448,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,581,580,1120,256,256,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256,256],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,389,388,296,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956,956],
[876,876,876,876,876,876,876,876,876,876,876,876,876,876,876,876,876,876,876,876,876,876,876,1988,876,876,876,292,876,294,876,2692,876,876,876,876,876,876,876,876,1212,2420,876,876,876,876,876,876,876,1012,109,2221,876,876,362,876,2620,876,360,876,2080,876,409,876,1952,876],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,1148,581,580,256,256,256,526,256,524,256,256,740,256,1593,256,1592,256,2156,256]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_12 : (row6_12.zip hint6_12).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_13 : List (List ℕ) := [
[232,698,1096,60,61,2052,2192],
[2612,914,108,1728,914,108,914,108,914,108,914,108,914,108,914,108,914,108,914,108,484,914,108,2716,914,108,1269,914,108,472,914,108,10,1494,914,108,2192,1772,914,108,166,914,108,1558,914,108,1492,914,108,1692,914,108,1013,914,108,2784,914,108,2648,912,914,108,164,914,108,1556,914,108,689,914,108,2356,914,108,1980,914,108,2560,914,108,1341,914,108,2788,914,108,2594,914,108,2016,914,108,620,90,703,2278,914,108,1717,1679,914,108,1756,1482,914,108,2592,914,108,2644,914,108,724,914,108,2172,914,108,2276,914,108,1677,914,108,1480,914,108,2204,914,108,600,914,108,1900,914,108,452,658,390,914,108,892,900,580,914,108,284,656,388,914,108,1344,2428,1253,914,108,520,914,108,84,392,2704,914,108],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2445,2049,2049,429,2049,2049,2049,2049,482,2049,1592,2049,2049,2156,2049,480,2049,1160,2049,1856,2049],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,356,2156,2156,2156,2156,2156,2156,2156,2156,2156,808,2156,2156,2156,2156,2156,2156,2156,2156,2196,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,644,2048,2048,2048,1009,2048,2048,1484,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,428,2048,2048,483,2048,1593,2048,481,2048,1161,2048,2156,2048,1856,2048],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1321,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,2205,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,708,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1381,1380,393,1856,2049,645,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,820,429,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,1856,2049,536,482,1856,2049,2088,1592,1856,2049,2048,2156,1856,2049,538,480,1856,2049,1304,1160,1856,2049],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,16,2156,1904,109,108,2156,958,2156,256,2156,956,2156,788,2156,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1884,109,108,2156,958,2156,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_13 : (row6_13.zip hint6_13).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_14 : List (List ℕ) := [
[236,237,2812,2724],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,2604,256,256,2632,256,256,256,256,256,256,256,256,1748,256,256,256,256,256,256,275,581,580,256,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,1912,2049,429,2049,2049,2049,2049,482,2049,1592,2049,2049,2156,2049,480,2049,1160,2049,1856,2049],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,216,2156,737,2156,736,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,484,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2256,2156,2156,109,108,516,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,2482,256,2480,256,320,256,2620,256,256,256,256,256,256,256,256,256,256,256,256,256,256,2309,581,580,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256],
[2612,2049,520,109,1728,2049,520,109,2049,520,109,2049,520,109,2049,520,109,2049,520,109,2049,520,109,2049,520,109,2049,520,109,1494,2049,520,109,935,2049,520,109,1772,2049,520,109,914,2049,520,109,167,2049,520,109,1558,2049,520,109,924,2049,520,109,1492,2049,520,109,1692,2049,520,109,1012,2049,520,109,2784,2049,520,109,933,2049,520,109,964,2049,520,109,645,732,2049,520,109,912,2049,520,109,165,2049,520,109,1556,2049,520,109,688,2049,520,109,2356,2049,520,109,2594,2049,520,109,1216,2049,520,109,2016,2049,520,109,2278,2049,520,109,1678,2049,520,109,1482,2049,520,109,845,2049,520,109,2592,2049,520,109,2644,2049,520,109,725,2049,520,109,2172,2049,520,109,1218,2049,520,109,1797,2049,520,109,429,1760,2049,520,109,2276,2049,520,109,1676,2049,520,109,1480,2049,520,109,2205,2049,520,109,600,2049,520,109,658,482,1565,391,2049,520,109,900,1592,996,581,2049,520,109,2156,108,2049,520,109,480,1567,656,389,2049,520,109,1160,680,2428,1252,2049,520,109,1856,521,2049,520,109,1381,393,2704,2049,520,109],
[2612,109,1728,109,1728,109,1728,109,1728,109,1728,109,1728,109,1728,109,1728,1494,109,1728,1772,109,1728,914,109,1728,167,109,1728,1558,109,1728,1492,109,1728,1692,109,1728,1012,109,1728,2784,109,1728,912,109,1728,165,109,1728,1556,109,1728,688,109,1728,2356,109,1728,2594,109,1728,2016,109,1728,2278,109,1728,1678,109,1728,1482,109,1728,2592,109,1728,2644,109,1728,725,109,1728,2172,109,1728,2276,109,1728,1676,109,1728,1480,109,1728,2205,109,1728,600,109,1728,658,391,186,109,1728,900,581,1784,109,1728,656,389,184,109,1728,2428,1252,1444,109,1728,521,109,1728,393,2704,668,109,1728],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1908,2156,2492,2156,2156,2156,2156,2156,2156,2156,2156,2156,692,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,126,109,108,2156,958,2156,256,2156,956,2156,788,2156,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,2028,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_14 : (row6_14.zip hint6_14).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_15 : List (List ℕ) := [
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,2504,256,256,256,256,256,256,256,894,581,580,256,256,256,526,256,256,524,256,740,256,1593,256,1592,256,2156,256],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,384,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,1041,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2492,2156,2006,159,158,109,108,2492,2156,772,2492,2156,958,2492,2156,1364,256,2492,2156,446,956,2492,2156,1490,788,2492,2156,994,2048,2492,2156,995,2049,2492,2156],
[2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,644,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,428,2048,2048,483,2048,1593,2048,481,2048,1161,2048,2156,2048,1856,2048,2048],
[1842,956,389,388,184,956,389,388,956,389,388,956,389,388,956,389,388,956,389,388,956,389,388,956,389,388,956,389,388,112,956,389,388,284,956,389,388,917,956,389,388,144,956,389,388,916,956,389,388,2046,956,389,388,1674,956,389,388,947,956,389,388,2380,956,389,388,946,956,389,388,120,956,389,388,364,956,389,388,1404,956,389,388,365,956,389,388,1460,956,389,388,2689,956,389,388,1950,956,389,388,2688,956,389,388,432,956,389,388,2582,956,389,388,1246,956,389,388,1561,956,389,388,244,956,389,388,1560,956,389,388,192,956,389,388,1188,956,389,388,842,956,389,388,960,956,389,388,843,956,389,388,352,956,389,388,1229,956,389,388,340,956,389,388,1228,956,389,388,1088,956,389,388,905,956,389,388,904,956,389,388,2652,956,389,388,1740,2500,1572,1573,956,389,388,854,524,1248,1249,956,389,388,1506,264,813,812,956,389,388,481,1566,956,389,388,2156,109,656,108,956,389,388,480,1567,956,389,388,729,728,2540,956,389,388],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,48,2156,2156,1372,2156,2292,2156,2156,618,2156,2156,502,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1194,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,958,266,391,1504,390,815,814,958,266,958,266,958,266,958,266,958,266,526,796,958,266,2500,2528,958,266,483,277,958,266,482,276,958,266,2156,788,958,266],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,337,2156,2156,2156,2156,2156,1320,2156,689,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[788,788,788,788,788,788,788,788,788,788,788,1992,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1438,1252,1253,788,788,266,788,740,788,264,788,788,1161,788,2156,788,1160,788],
[2612,109,1679,1728,109,1679,109,1679,109,1679,109,1679,109,1679,109,1679,109,1679,109,1679,1494,109,1679,1772,109,1679,914,1717,109,1679,167,109,1679,1558,255,857,109,1679,1492,109,1679,1692,109,1679,1012,109,1679,2784,109,1679,1524,109,1679,912,109,1679,165,109,1679,1556,109,1679,1193,109,1679,688,109,1679,2356,109,1679,1128,109,1679,2752,109,1679,515,614,109,1679,2594,1185,109,1679,2016,1630,109,1679,2278,109,1679,1678,1722,109,1679,1482,109,1679,2592,109,1679,2644,109,1679,725,109,1679,2172,109,1679,818,109,1679,2276,109,1679,1676,109,1679,1480,109,1679,1109,109,1679,2205,109,1679,600,109,1679,1042,109,1679,658,391,298,109,1679,900,581,1145,109,1679,656,389,1560,109,1679,2428,1252,1068,109,1679,521,109,1679,393,2704,74,109,1679,155,109,1679]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_15 : (row6_15.zip hint6_15).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_16 : List (List ℕ) := [
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,2073,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1252,1253,2537,788,788,266,788,740,788,264,788,1161,788,2156,788,1160,788,788],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,1196,256,256,256,256,256,256,256,256,256,256,256,1972,256,256,256,829,581,580,256,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256],
[2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,686,2636,2636,2636,2636,684,2636,2636,2636,2636,2636,2568,2636,2569,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2148,1141,1140,2636,576,2636,1714,2636,1712,2636,2636,220,2636,1045,2636,1044,2636],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1131,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[1373,1373,1373,1373,1373,1373,1373,1373,1373,1373,1373,1373,61,1373,1373,1373,1373,1373,1373,1373,63,1373,1373,1373,1373,1373,1373,1373,1373,2136,1373,1373,349,1326,1324,1373,1373,1373,1373,1373,1373,1373,1373,1373,1373,1373,1373,1373,2772,1225,1501,1373,1373,1456,1373,2400,1373,1458,1373,1060,1373,1009,1373,1416,1373],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1830,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,1900,2156,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,220,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,178,2156,2156,2156,2156,2156,2156,2156,2156,2156,176,2156,2156,2156,2156,2156,205,2156,109,1056,108,2156,204,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,2156,1078,109,530,108,1535,1534,2156,1078,958,2156,1078,256,662,2156,1078,956,2524,2156,1078,788,1610,2156,1078,2048,1166,2156,1078,1360,2156,1078,2049,1167,2156,1078],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,2104,108,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_16 : (row6_16.zip hint6_16).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_17 : List (List ℕ) := [
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,2008,256,581,1652,580,256,256,664,256,526,256,524,256,740,256,1593,256,256,1592,256,2156,256],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,964,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,2180,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,389,960,388,956,956,956,2500,956,524,956,264,956,481,956,2156,956,956,480,956],
[2612,2280,109,900,581,1728,1784,109,900,581,109,900,581,109,900,581,109,900,581,109,900,581,109,900,581,109,900,581,109,900,581,1494,1064,109,900,581,1772,1736,109,900,581,914,892,109,900,581,167,273,109,900,581,1558,30,109,900,581,2110,1334,109,900,581,1492,1066,109,900,581,1692,2756,109,900,581,1012,2309,109,900,581,2784,2360,109,900,581,912,894,109,900,581,165,275,109,900,581,1556,28,109,900,581,2108,1332,109,900,581,688,829,109,900,581,2356,2548,109,900,581,1632,2332,109,900,581,1804,1653,109,900,581,2340,1620,109,900,581,2594,1150,109,900,581,2016,12,109,900,581,2278,1112,109,900,581,1678,1144,109,900,581,1482,2228,109,900,581,1016,2338,109,900,581,2592,1148,109,900,581,2644,848,109,900,581,725,2248,109,900,581,2172,2740,109,900,581,2276,1114,109,900,581,1676,1146,109,900,581,1480,2230,109,900,581,1018,2336,109,900,581,2205,1781,109,900,581,600,968,109,900,581,1168,1120,109,900,581,240,2512,109,900,581,872,2284,109,900,581,658,1082,391,852,1250,109,900,581,656,389,854,1080,1248,109,900,581,2428,1252,2064,1472,381,109,900,581,521,997,109,900,581,393,2704,596,1236,1600,109,900,581],
[2612,1692,109,1728,1692,109,1692,109,1692,109,1692,109,1692,109,1692,109,1692,109,1692,109,484,1692,109,486,1692,109,1656,1692,109,1312,1692,109,1494,1692,109,1772,1692,109,914,1692,109,167,1692,109,1558,1692,109,1492,1692,109,1012,1692,109,2784,1692,109,912,1692,109,165,1692,109,1556,1692,109,688,1692,109,2356,1692,109,1022,1692,109,1020,1692,109,709,1692,109,704,1692,109,2594,1692,109,2016,1692,109,2278,1692,109,1678,1692,109,1482,1692,109,2592,1692,109,2352,2148,1141,2644,1692,109,725,1692,109,2172,1692,109,2276,1692,109,1676,1692,109,1480,1692,109,2205,1692,109,600,1692,109,2068,1692,109,1672,658,391,1692,109,2756,900,581,1692,109,1674,656,389,1692,109,2484,2428,1252,1692,109,521,1692,109,604,393,2704,1692,109],
[2612,108,1728,2612,108,2612,108,2612,108,2612,108,2612,108,2612,108,2612,108,1494,2612,108,1772,2612,108,914,2612,108,166,2612,108,1558,2612,108,1492,2612,108,1692,2612,108,1013,2612,108,2784,2612,108,912,2612,108,164,2612,108,1556,2612,108,689,2612,108,2356,2612,108,2594,2612,108,2016,2612,108,2278,2612,108,1679,2612,108,1482,2612,108,2592,2612,108,2644,2612,108,724,2612,108,2172,2612,108,2276,2612,108,1677,2612,108,1480,2612,108,2204,2612,108,600,2612,108,1840,658,390,2612,108,2280,900,580,2612,108,1842,656,388,2612,108,1548,2428,1253,2612,108,520,2612,108,1956,392,2704,2612,108],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1632,109,108,2156,958,2156,256,2156,956,2156,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,989,2156,2156,148,2156,2156,2376,2156,2156,2156,2156,2156,437,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1636,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2612,109,725,1728,109,725,109,725,109,725,109,725,109,725,109,725,109,725,109,725,1494,109,725,1772,109,725,914,109,725,167,109,725,403,109,725,1558,109,725,1492,109,725,1692,109,725,1012,2684,109,725,2784,1660,109,725,912,109,725,165,109,725,401,109,725,1556,109,725,688,109,725,41,109,725,2356,109,725,2220,109,725,2594,109,725,2016,109,725,2278,109,725,1678,109,725,819,109,725,1482,109,725,2592,109,725,2644,109,725,2172,109,725,2276,109,725,1676,109,725,817,109,725,1480,109,725,2205,109,725,456,109,725,600,109,725,658,391,840,109,725,900,581,2248,109,725,656,389,842,109,725,2428,1252,1624,109,725,521,109,725,329,109,725,393,1777,2704,109,725],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,80,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_17 : (row6_17.zip hint6_17).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_18 : List (List ℕ) := [
[2049,2049,2049,2049,2049,2049,2049,2049,2049,1765,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,482,2049,1592,2049,2049,2156,2049,480,2049,1160,2049,1856,2049],
[232,1156,2234,2232,2648],
[2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,942,1368,2112,2532,2532,2532,2532,2532,2532,2532,2532,348,1327,1985,2532,349,1326,1984,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,2532,1296,180,181,2532,1896,2532,2532,2768,2532,2216,2532,1648,2532,1484,2532,1485,2532],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,2524,956,956,956,956,956,956,956,956,956,802,956,956,956,956,956,1950,389,388,956,956,2500,956,524,956,264,956,956,481,956,2156,956,480,956],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1328,788,788,788,788,788,788,788,788,788,1330,788,788,788,788,2572,788,2072,788,896,1252,1253,788,788,266,788,740,788,264,788,788,1161,788,2156,788,1160,788],
[2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,2156,256,109,108,900,581,580,2156,256,2156,256,2156,256,958,526,2156,256,956,524,2156,256,788,740,2156,256,2048,1593,2156,256,2049,1592,2156,256],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,977,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,389,388,904,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956,956],
[1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,2214,883,882,1092,2544,1092,1092,2312,1092,1508,1092,1604,1092,1764,1092,1765,1092],
[2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,2156,990,908,109,108,648,1688,2156,990,958,1308,2156,990,256,2480,2156,990,956,2156,990,1668,2156,990,788,202,2156,990,2048,2371,2156,990,2049,586,2156,990],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,933,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_18 : (row6_18.zip hint6_18).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_19 : List (List ℕ) := [
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1896,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,1220,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,200,788,202,788,2076,788,2080,788,788,788,788,788,788,788,460,788,788,788,788,788,788,788,2020,1252,1253,788,788,788,266,788,740,788,264,788,1161,788,2156,788,1160,788],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1096,2156,698,2156,2156,2156,2156,2156,2156,2156,2156,1098,2156,696,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2260,109,108,2156,958,2156,256,2156,956,2156,788,2156,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2110,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2552,2156,356,2156,356,464,2456,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,2156,356,1289,109,108,2728,712,2156,356,958,312,2156,356,256,320,2156,356,956,314,2156,356,788,2156,356,1440,2156,356,2048,889,2156,356,2049,2832,2156,356],
[956,956,956,956,956,956,956,956,956,1508,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,2582,389,388,956,956,2500,956,524,956,956,264,956,481,956,2156,956,480,956],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1372,2156,1373,2156,2156,2532,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1772,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2612,109,724,1728,109,724,109,724,109,724,109,724,109,724,109,724,109,724,109,724,1494,109,724,1772,109,724,914,109,724,167,109,724,1558,109,724,402,109,724,1492,109,724,1692,109,724,1012,109,724,2784,764,1661,109,724,912,109,724,165,109,724,1556,109,724,400,109,724,688,109,724,2356,109,724,40,109,724,324,109,724,876,2221,109,724,2594,109,724,2016,109,724,2278,109,724,1678,109,724,1482,109,724,818,109,724,2592,109,724,2644,109,724,725,109,724,2172,109,724,2276,109,724,1676,109,724,1480,109,724,816,109,724,2205,109,724,600,109,724,457,109,724,658,391,841,109,724,900,581,2249,109,724,656,389,843,109,724,2428,1252,1625,109,724,521,109,724,393,2704,1776,109,724,328,109,724],
[956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,956,2500,389,388,1740,1572,1573,956,2500,956,2500,956,2500,956,2500,956,2500,524,2296,956,2500,264,2528,956,2500,481,1536,956,2500,2156,958,956,2500,480,1537,956,2500],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2656,2156,2156,2156,2156,2156,476,2156,477,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,300,109,108,2156,958,2156,256,2156,956,2156,788,2156,2156,2048,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_19 : (row6_19.zip hint6_19).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_20 : List (List ℕ) := [
[2612,1548,2428,108,1253,1728,1444,2428,108,1253,2428,108,1253,2428,108,1253,2428,108,1253,2428,108,1253,2428,108,1253,2428,108,1253,2428,108,1253,1494,2404,2428,108,1253,1772,1412,2428,108,1253,914,1344,2428,108,1253,2002,1034,2428,108,1253,166,838,2428,108,1253,1558,1174,2428,108,1253,1492,2406,2428,108,1253,1692,2484,2428,108,1253,1884,2364,2428,108,1253,1013,2021,2428,108,1253,2784,2576,2428,108,1253,912,1346,2428,108,1253,2000,1032,2428,108,1253,164,836,2428,108,1253,1556,1172,2428,108,1253,689,505,2428,108,1253,2356,2712,2428,108,1253,2824,897,2428,108,1253,1664,2424,2428,108,1253,2594,1554,2428,108,1253,2016,2244,2428,108,1253,2278,1436,2428,108,1253,2154,624,2428,108,1253,1679,1068,2428,108,1253,1482,1278,2428,108,1253,2592,1552,2428,108,1253,2644,2700,2428,108,1253,2316,1816,2428,108,1253,724,1625,2428,108,1253,2172,104,2428,108,1253,2276,1438,2428,108,1253,2152,626,2428,108,1253,1677,1070,2428,108,1253,1480,1276,2428,108,1253,2204,0,2428,108,1253,600,628,2428,108,1253,2596,2537,2428,108,1253,2224,2032,2428,108,1253,658,542,1504,390,814,2428,108,1253,900,2064,1472,580,380,2428,108,1253,656,540,1506,388,812,2428,108,1253,520,680,2428,108,1253,1292,392,2704,2328,1428,2428,108,1253],
[2612,164,108,1728,164,108,164,108,164,108,164,108,164,108,164,108,164,108,164,108,1494,164,108,1772,164,108,914,164,108,166,164,108,1558,164,108,510,164,108,1492,164,108,1692,164,108,1013,164,108,2784,164,108,1271,164,108,912,164,108,1556,164,108,689,164,108,2356,164,108,2594,164,108,565,421,1708,164,108,2016,164,108,2278,164,108,1679,164,108,1482,164,108,199,164,108,2592,164,108,2644,164,108,724,164,108,2172,164,108,751,164,108,2276,164,108,1584,1677,164,108,1480,164,108,2204,164,108,600,164,108,658,918,390,164,108,900,274,580,164,108,1336,164,108,424,656,388,164,108,836,2428,1253,164,108,520,164,108,677,392,2704,164,108],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2544,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,2710,2156,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[808,2588,356,2140],
[958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,1476,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,958,391,390,1231,958,958,958,958,958,526,958,2500,958,266,958,483,958,482,958,958,2156,958],
[2612,108,2204,1728,108,2204,108,2204,108,2204,108,2204,108,2204,108,2204,108,2204,108,2204,1494,108,2204,1772,108,2204,914,108,2204,166,108,2204,1558,108,2204,1026,108,2204,1492,108,2204,1692,108,2204,1013,108,2204,2784,108,2204,2197,108,2204,912,108,2204,164,108,2204,1556,108,2204,1024,108,2204,689,377,108,2204,2356,2465,108,2204,1233,108,2204,2594,108,2204,2016,108,2204,2278,108,2204,1679,108,2204,1482,108,2204,1042,108,2204,2592,108,2204,2644,2141,108,2204,724,108,2204,2172,108,2204,457,108,2204,2276,108,2204,1677,108,2204,1480,108,2204,1040,108,2204,600,108,2204,658,390,1230,108,2204,900,580,1780,108,2204,656,388,1228,108,2204,2428,1253,0,108,2204,520,108,2204,392,2704,860,108,2204,1589,108,2204],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,2012,788,788,788,788,788,788,2364,1252,1253,788,788,266,788,788,740,788,264,788,1161,788,2156,788,1160,788],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,2152,2156,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,2100,2494,2494,2494,2494,684,2494,2494,2494,2494,2494,2494,2494,2494,1037,2494,1036,2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,2494,794,157,156,2494,444,2494,1366,2494,774,2494,1488,2494,2494,992,2494,993,2494],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2216,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2816,2156,2156,2156,109,560,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_20 : (row6_20.zip hint6_20).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_21 : List (List ℕ) := [
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,1788,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,100,2049,2049,429,2049,2049,2049,2049,482,2049,1592,2049,2049,2156,2049,480,2049,1160,2049,1856,2049],
[2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2156,513,2680,2496,776,2156,513,2156,513,2156,513,2156,513,2156,513,109,108,612,2156,513,958,1820,2156,513,256,2632,2156,513,956,556,2156,513,788,1917,2156,513,2048,101,2156,513,2049,2156,513,2272,2156,513],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,448,256,2332,581,580,256,256,256,526,256,524,256,256,740,256,1593,256,1592,256,2156,256],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,600,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,2058,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,581,580,2336,256,256,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256,256],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1868,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,256,526,581,580,1082,1250,1251,256,526,256,526,256,526,256,526,256,526,256,526,524,2296,256,526,740,796,256,526,1593,119,256,526,1592,118,256,526,2156,958,256,526],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1252,1253,0,788,788,788,266,788,740,788,264,788,1161,788,2156,788,1160,788,788],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1280,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2612,1772,108,1728,1772,108,1772,108,1772,108,1772,108,1772,108,1772,108,1772,108,1772,108,2476,1772,108,2716,1772,108,1494,1772,108,2192,914,1772,108,166,1772,108,1558,1772,108,1492,1772,108,1692,1772,108,1013,1772,108,2784,1772,108,2194,912,1772,108,164,1772,108,1556,1772,108,689,1772,108,2356,1772,108,1868,1772,108,2260,1772,108,1836,1772,108,2772,1224,2836,1772,108,2594,1772,108,1296,1298,181,2016,1772,108,2278,1772,108,1679,1772,108,1482,1772,108,2592,1772,108,2644,1772,108,724,1772,108,2172,1772,108,2276,1772,108,1677,1772,108,1480,1772,108,2204,1772,108,600,1772,108,1220,1772,108,1732,658,390,1772,108,1736,900,580,1772,108,1734,656,388,1772,108,1412,2428,1253,1772,108,520,1772,108,720,392,2704,1772,108]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_21 : (row6_21.zip hint6_21).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_22 : List (List ℕ) := [
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,818,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,581,2248,580,256,256,256,256,526,256,524,256,740,256,1593,256,256,1592,256,2156,256],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2350,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049,2049],
[50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,50,1180,50,50,50,50,50,50,50,50,50,50,50,1100,1920,2440,50,50,50,50,420,1709,1420,50,50,2124,50,2604,50,885,50,20,50,1789,50,768,50],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,588,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,512,2156,513,2156,2156,252,2156,253,2156,2156,2156,1556,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1078,2156,2156,2156,2156,2156,2156,2156,2156,2156,1076,2156,2156,2156,2812,2156,2156,2156,804,109,108,2156,958,2156,256,2156,956,2156,788,2156,2156,2048,2156,2049,2156],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,1712,956,956,956,956,956,956,956,956,1674,389,388,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956],
[2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,994,2048,2048,2048,2048,1045,2048,2048,2048,2048,992,2048,2048,2048,2048,2048,544,2048,37,2048,644,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,428,2048,483,2048,1593,2048,481,2048,1161,2048,2048,2156,2048,1856,2048],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,2840,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2156,2049,2156],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,1066,581,580,256,256,256,526,256,256,524,256,740,256,1593,256,1592,256,2156,256]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_22 : (row6_22.zip hint6_22).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_23 : List (List ℕ) := [
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,136,2156,2156,2156,2156,2156,2156,2156,2156,2156,138,2156,2156,2156,2200,2156,2156,2156,877,2156,325,109,108,2156,958,2156,256,2156,956,2156,788,2156,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1094,2156,2156,2156,2156,2156,2156,2156,2156,2156,1492,109,108,2156,958,2156,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2305,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1218,109,108,2156,958,2156,256,2156,956,2156,2156,788,2156,2048,2156,2049,2156],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,770,2049,2049,2049,2049,2049,2049,2348,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,2180,956,956,956,956,956,956,2380,389,388,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956],
[464,2552,1988,2452,2060],
[1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1100,2820,2440,1647,1647,1647,1136,2496,776,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1585,1647,1647,52,1647,1152,1647,1748,1647,2448,1647,1647,2350,1647,1808,1647],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1022,109,108,2156,958,2156,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,686,2636,2636,2636,2636,2636,2636,684,2636,2636,2636,2568,2636,2569,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2636,2352,1141,1140,2636,576,2636,1714,2636,2636,1712,2636,220,2636,1045,2636,1044,2636],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,140,109,108,2156,958,2156,256,2156,956,2156,2156,788,2156,2048,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_23 : (row6_23.zip hint6_23).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_24 : List (List ℕ) := [
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,2384,956,956,956,956,956,956,956,956,956,956,144,389,388,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,1964,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,389,388,843,956,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956,956],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,989,2156,991,2156,357,2156,877,2156,2156,2156,2156,2156,2156,2156,2156,2156,632,2156,2156,2156,2156,2156,2156,1013,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,51,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,512,2156,2156,2156,1646,2156,2156,2156,164,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,788,266,1252,1253,542,815,814,788,266,788,266,788,266,788,266,788,266,740,796,788,266,264,2528,788,266,1161,277,788,266,2156,958,788,266,1160,276,788,266],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2312,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,1612,2156,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,344,260,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,1161,788,496,1161,788,1161,788,681,1252,1253,1161,788,1161,788,277,266,1161,788,1117,740,1161,788,279,264,1161,788,2048,2156,1161,788,1304,1160,1161,788],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2808,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,44,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2612,2016,108,1728,2016,108,2016,108,2016,108,2016,108,2016,108,2016,108,2016,108,2016,108,1494,2016,108,1772,1296,1298,181,2016,108,914,2016,108,166,2016,108,1558,2016,108,1492,2016,108,928,2016,108,1692,2016,108,1013,2016,108,2784,2016,108,912,2016,108,164,2016,108,1556,2016,108,2432,2600,1569,2016,108,1284,2016,108,1452,2016,108,689,2016,108,2356,2016,108,2594,2016,108,2278,2016,108,1679,1630,2016,108,1482,674,2016,108,2592,2016,108,92,2016,108,2644,2016,108,724,2016,108,2172,2016,108,2276,2016,108,1677,1628,2016,108,1480,672,2016,108,1384,2016,108,1109,2016,108,752,2016,108,2204,2016,108,600,2016,108,658,70,390,2016,108,900,12,580,2016,108,656,68,388,2016,108,560,2016,108,2244,2428,1253,2016,108,520,2016,108,1124,392,2704,2016,108],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,1018,2156,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_24 : (row6_24.zip hint6_24).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_25 : List (List ℕ) := [
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,270,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,68,389,388,956,956,2500,956,524,956,956,264,956,481,956,2156,956,480,956],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,1768,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049,2049],
[2612,108,600,1728,108,600,108,600,108,600,108,600,108,600,108,600,108,600,108,600,1494,108,600,1772,108,600,914,108,600,166,108,600,1558,108,600,2392,108,600,1492,108,600,1692,108,600,1013,108,600,2784,108,600,2760,108,600,912,108,600,164,108,600,1556,108,600,2394,108,600,689,108,600,2356,948,1684,1520,108,600,2594,108,600,2016,108,600,2278,108,600,1679,108,600,1482,108,600,1410,108,600,2592,108,600,2644,2208,108,600,724,108,600,2172,108,600,2796,108,600,2276,108,600,1677,108,600,1480,108,600,1408,108,600,2204,108,600,658,390,1090,108,600,900,580,968,108,600,656,388,1088,108,600,2428,1253,628,108,600,520,108,600,392,2704,1696,108,600,1300,108,600],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049,2049],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1752,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1588,109,108,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[256,256,256,256,256,256,256,256,256,256,256,1364,256,256,256,256,256,1366,256,256,256,256,256,256,256,405,256,404,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,848,581,580,256,256,256,526,256,524,256,740,256,256,1593,256,1592,256,2156,256],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1610,788,788,788,788,788,788,788,788,788,1608,788,788,788,788,788,1812,1252,1253,788,788,266,788,740,788,264,788,788,1161,788,2156,788,1160,788],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,454,389,388,956,956,2500,956,524,956,956,264,956,481,956,2156,956,480,956],
[1496,1497,1076,1720],
[2612,2784,109,1728,2784,109,2784,109,2784,109,2784,109,2784,109,2784,109,2784,109,2784,109,1104,2784,109,1106,2784,109,1312,2784,109,1012,2784,109,1494,2784,109,1772,2784,109,914,2784,109,167,2784,109,1558,2784,109,1492,2784,109,1692,2784,109,912,2784,109,165,2784,109,1556,2784,109,688,2784,109,2732,2356,2784,109,638,826,1000,2784,109,636,824,1002,2784,109,2676,1004,1260,2784,109,2220,2784,109,2594,2784,109,2016,2784,109,2278,2784,109,1678,2784,109,1482,2784,109,2592,2784,109,2644,2784,109,1660,725,2784,109,2176,1872,2252,2172,2784,109,2276,2784,109,1676,2784,109,1480,2784,109,2205,2784,109,600,2784,109,1256,2784,109,122,658,391,2784,109,2360,900,581,2784,109,120,656,389,2784,109,2576,2428,1252,2784,109,521,2784,109,2608,393,2704,2784,109]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_25 : (row6_25.zip hint6_25).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_26 : List (List ℕ) := [
[645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,645,2049,2320,429,645,2049,645,2049,645,2049,645,2049,821,645,2049,534,482,645,2049,1432,1592,645,2049,2305,2156,645,2049,532,480,645,2049,345,1160,645,2049,1856,645,2049],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,2401,256,2400,256,256,2768,256,256,256,256,256,256,256,256,256,256,256,256,1736,581,580,256,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,1968,2049,2049,645,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,2049,1160,2049,1856,2049],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,1482,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2460,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,482,2049,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049],
[2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,2812,550,2812,2812,2812,2812,2812,2812,2812,2812,2812,548,2812,2812,2812,2812,1704,1397,1396,2812,2812,2812,800,2812,1516,2812,802,2812,2812,2264,2812,2265,2812,640,2812],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,2736,389,388,956,956,2500,956,956,524,956,264,956,481,956,2156,956,480,956],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,665,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,581,580,2512,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256,256],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,2756,581,580,256,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,1802,2049,2049,2049,2049,2049,2049,2049,2049,1912,2049,645,2049,2049,1800,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,2049,1856,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_26 : (row6_26.zip hint6_26).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_27 : List (List ℕ) := [
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1356,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[1956,393,392,2156,668,393,392,2156,393,392,2156,393,392,2156,393,392,2156,393,392,2156,393,392,2156,393,392,2156,393,392,2156,1544,393,392,2156,2288,393,392,2156,720,393,392,2156,84,393,392,2156,678,393,392,2156,679,393,392,2156,1892,393,392,2156,1546,393,392,2156,604,393,392,2156,1844,393,392,2156,1845,393,392,2156,2290,393,392,2156,2128,393,392,2156,86,393,392,2156,676,393,392,2156,677,393,392,2156,1681,393,392,2156,1680,393,392,2156,1832,393,392,2156,980,393,392,2156,188,393,392,2156,1124,393,392,2156,1924,393,392,2156,75,393,392,2156,74,393,392,2156,440,393,392,2156,982,393,392,2156,2092,393,392,2156,1777,393,392,2156,1776,393,392,2156,190,393,392,2156,2184,393,392,2156,1053,429,393,392,2156,1052,428,393,392,2156,1926,393,392,2156,73,393,392,2156,72,393,392,2156,861,393,392,2156,860,393,392,2156,2704,109,108,393,392,2156,468,731,730,958,393,392,2156,596,1236,1237,256,393,392,2156,470,729,728,956,393,392,2156,1292,2329,2328,788,393,392,2156,1380,2048,393,392,2156,1381,2049,393,392,2156],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,2368,2049,2049,2370,2049,888,2049,408,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,2316,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2156,2049,2156],
[956,956,956,956,956,956,956,956,956,956,956,1880,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,592,389,388,956,956,2500,956,524,956,264,956,956,481,956,2156,956,480,956],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,2049,584,2049,1860,2049,586,2049,2832,2049,2049,2049,2049,2049,2049,2049,2049,2049,936,2049,2049,2049,429,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049],
[788,788,788,788,788,788,788,788,788,788,788,788,1850,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1252,624,1253,788,788,788,266,788,740,788,264,788,1161,788,2156,788,788,1160,788],
[645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,732,520,108,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,645,2305,821,428,645,2305,534,134,645,2305,1432,2268,645,2305,532,132,645,2305,345,261,645,2305],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1724,2156,1889,2156,1888,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2716,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,306,109,108,2156,958,2156,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_27 : (row6_27.zip hint6_27).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_28 : List (List ℕ) := [
[1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1100,2820,1920,1647,1647,1647,1136,2680,776,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,1647,52,1647,1152,1647,1748,1647,1647,2448,1647,2350,1647,1808,1647],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,198,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2532,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2016,109,108,2156,958,2156,256,2156,956,2156,2156,788,2156,2048,2156,2049,2156],
[2612,689,108,1728,689,108,689,108,689,108,689,108,689,108,689,108,689,108,689,108,1494,689,108,1269,689,108,1772,689,108,914,689,108,166,689,108,1558,689,108,1657,689,108,1492,689,108,1692,689,108,1013,689,108,2784,689,108,1271,689,108,912,689,108,164,689,108,1556,689,108,2356,689,108,2594,689,108,143,689,108,2016,689,108,2278,689,108,1679,689,108,1482,689,108,1425,689,108,2592,689,108,2644,689,108,724,689,108,2172,689,108,141,689,108,2276,689,108,1677,689,108,1480,689,108,377,2204,689,108,600,689,108,658,367,390,689,108,900,828,580,689,108,517,689,108,365,656,388,689,108,505,2428,1253,689,108,520,689,108,1680,392,2704,689,108],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1548,1252,1253,788,788,266,788,740,788,264,788,1161,788,2156,788,1160,788],
[2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,732,109,108,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,2305,2156,428,2305,2156,134,958,2305,2156,2268,256,2305,2156,132,956,2305,2156,261,788,2305,2156,2048,2305,2156,645,2049,2305,2156],
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,662,256,256,256,256,256,660,256,256,256,256,1516,256,256,256,256,256,1464,581,580,256,256,256,526,256,524,256,740,256,256,1593,256,1592,256,2156,256],
[2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,2156,2812,109,108,1976,1397,1396,2156,2812,958,800,2156,2812,256,1516,2156,2812,956,802,2156,2812,788,2156,2812,2048,2264,2156,2812,2049,2265,2156,2812,640,2156,2812],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2556,2156,2492,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1980,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,256,740,581,1472,580,381,380,256,740,256,740,256,740,256,740,256,740,526,796,256,740,524,798,256,740,1593,1117,256,740,1592,1116,256,740,2156,788,256,740]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_28 : (row6_28.zip hint6_28).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_29 : List (List ℕ) := [
[2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,644,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,2048,428,2048,483,2048,1593,2048,481,2048,1161,2048,2156,2048,1856,2048],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1061,788,788,1060,788,788,1648,788,788,788,788,788,788,788,788,788,788,788,788,1412,1252,1253,788,788,788,266,788,740,788,264,788,1161,788,2156,788,1160,788],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2452,2156,2156,2156,2156,464,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1424,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,1508,956,956,956,956,956,956,956,956,956,956,956,956,956,112,389,388,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1808,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,152,109,108,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2668,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,845,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,788,740,1252,1253,2064,381,380,788,740,788,740,788,740,788,740,788,740,266,796,788,740,264,798,788,740,1161,1117,788,740,2156,256,788,740,1160,1116,788,740],
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,2484,1252,1253,788,788,788,266,788,740,788,264,788,1161,788,2156,788,1160,788],
[1548,788,1252,1253,1444,788,1252,1253,788,1252,1253,788,1252,1253,788,1252,1253,788,1252,1253,788,1252,1253,788,1252,1253,788,1252,1253,2404,788,1252,1253,1412,788,1252,1253,839,788,1252,1253,1034,788,1252,1253,838,788,1252,1253,1174,788,1252,1253,2406,788,1252,1253,2020,788,1252,1253,2364,788,1252,1253,2021,788,1252,1253,2576,788,1252,1253,837,788,1252,1253,1032,788,1252,1253,836,788,1252,1253,1172,788,1252,1253,896,788,1252,1253,1812,788,1252,1253,897,788,1252,1253,2424,788,1252,1253,1554,788,1252,1253,2244,788,1252,1253,1069,788,1252,1253,624,788,1252,1253,1068,788,1252,1253,1278,788,1252,1253,1552,788,1252,1253,1624,788,1252,1253,1816,788,1252,1253,1625,788,1252,1253,104,788,1252,1253,1071,788,1252,1253,626,788,1252,1253,1070,788,1252,1253,1276,788,1252,1253,2536,788,1252,1253,2537,788,1252,1253,2032,788,1252,1253,542,266,815,814,788,1252,1253,2064,740,381,380,788,1252,1253,540,264,813,812,788,1252,1253,1161,681,788,1252,1253,2156,109,2428,108,788,1252,1253,1160,680,788,1252,1253,2329,2328,1428,788,1252,1253],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,698,2156,2156,2156,2156,2156,2156,2156,2156,1864,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2276,109,108,2156,958,2156,256,2156,956,2156,788,2156,2156,2048,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_29 : (row6_29.zip hint6_29).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_30 : List (List ℕ) := [
[256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,2280,581,580,256,256,256,526,256,524,256,740,256,1593,256,1592,256,2156,256],
[698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,1700,2116,2488,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,698,66,1540,1541,698,1616,698,1072,698,1880,698,1992,698,698,1876,698,1877,698],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,241,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[2612,1013,109,1728,1013,109,1013,109,1013,109,1013,109,1013,109,1013,109,1013,109,1013,109,508,1013,109,510,1013,109,1657,1013,109,2616,1013,109,1494,1013,109,1772,1013,109,914,1013,109,167,1013,109,1558,1013,109,1492,1013,109,1692,1013,109,1012,1013,109,2784,1013,109,912,1013,109,165,1013,109,1556,1013,109,688,1013,109,2356,1013,109,954,911,1691,1013,109,952,909,1689,1013,109,492,1288,713,1013,109,2220,1013,109,2594,1013,109,2016,1013,109,2278,1013,109,1678,1013,109,1482,1013,109,2592,1013,109,2644,1013,109,725,1013,109,2172,1013,109,2276,1013,109,1676,1013,109,1480,1013,109,2205,1013,109,600,1013,109,1945,1013,109,944,658,391,1013,109,2308,900,581,1013,109,946,656,389,1013,109,2021,2428,1252,1013,109,521,1013,109,1845,393,2704,1013,109],
[2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,1988,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2420,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,2156,876,109,108,2221,2156,876,958,362,2156,876,256,2620,2156,876,956,360,2156,876,788,2080,2156,876,2048,409,2156,876,2049,2156,876,1952,2156,876],
[2612,108,2205,1728,108,2205,108,2205,108,2205,108,2205,108,2205,108,2205,108,2205,108,2205,1494,108,2205,1772,108,2205,914,108,2205,166,108,2205,1558,108,2205,1027,108,2205,1492,108,2205,1692,108,2205,1013,108,2205,2784,108,2205,2196,108,2205,912,108,2205,164,108,2205,1556,108,2205,1025,108,2205,689,108,2205,2356,280,2464,108,2205,2472,108,2205,337,1232,108,2205,2594,108,2205,2016,108,2205,2278,108,2205,1679,108,2205,1482,108,2205,1043,108,2205,2592,108,2205,2644,2140,108,2205,724,108,2205,2172,108,2205,456,108,2205,2276,108,2205,1677,108,2205,1480,108,2205,1041,108,2205,2204,2724,108,2205,600,108,2205,658,390,1231,108,2205,900,580,1781,108,2205,656,388,1229,108,2205,2428,1253,1,108,2205,520,108,2205,392,2704,861,108,2205,1588,108,2205],
[956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,2792,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,956,389,388,340,956,956,956,956,2500,956,524,956,264,956,481,956,2156,956,480,956,956],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,2596,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1132,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,329,109,108,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,936,2049,2049,2049,645,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,480,2049,1160,2049,1856,2049,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_30 : (row6_30.zip hint6_30).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_31 : List (List ℕ) := [
[2492,1908,2556,10],
[356,356,356,356,356,356,356,356,356,356,356,356,356,356,356,356,356,356,356,356,356,356,356,2456,356,356,356,1824,356,1826,356,2692,356,356,356,356,356,356,356,356,76,356,356,356,356,356,356,356,493,2728,712,356,356,312,356,320,356,314,356,1440,356,889,356,2832,356],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,337,2156,336,2156,2156,2156,2156,280,2156,281,2156,2356,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2156,50,2820,1920,2440,2156,50,2156,50,2156,50,2156,50,564,109,108,1709,1420,2156,50,958,2156,50,2124,2156,50,256,2604,2156,50,956,885,2156,50,788,20,2156,50,2048,1789,2156,50,2049,768,2156,50],
[513,513,513,513,513,513,513,513,513,513,513,513,513,513,513,513,513,513,513,513,513,513,513,513,513,1180,513,513,513,513,513,513,513,513,513,513,513,513,513,1136,2680,2496,513,513,513,513,165,109,612,513,513,1820,513,2632,513,556,513,1917,513,101,513,2272,513],
[2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2460,2049,2049,2049,2049,2049,2049,645,2049,2049,2049,1928,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,2049,429,2049,2049,2049,2049,2049,2049,2049,482,2049,1592,2049,2156,2049,2049,480,2049,1160,2049,1856,2049],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1960,2156,109,1805,108,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2812,2156,237,2156,337,2156,109,2472,108,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2156,2049,2156],
[698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,756,1700,2116,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,698,2156,130,1540,1541,109,108,698,2156,1616,698,2156,958,698,2156,1072,256,698,2156,1880,956,698,2156,1992,788,698,2156,1876,2048,698,2156,1877,2049,698,2156],
[1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1092,1086,883,882,1092,2544,1092,1092,2312,1092,1508,1092,1604,1092,1764,1092,1765,1092]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_31 : (row6_31.zip hint6_31).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_32 : List (List ℕ) := [
[788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,2012,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,788,1252,1816,1253,788,788,788,266,788,740,788,264,788,1161,788,2156,788,788,1160,788],
[2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,645,2320,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,2049,429,482,2242,2049,429,1592,2437,2049,429,2156,2049,429,480,2240,2049,429,1160,497,2049,429,1856,820,2049,429,2304,2049,429],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1528,109,108,2156,958,2156,256,2156,956,2156,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2305,2156,2304,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,1940,109,108,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,870,2156,2156,2156,2156,2156,2156,2156,2156,2156,868,2156,2156,2156,832,2156,2156,2156,2168,2156,2156,2156,2156,2156,2156,2156,2156,2156,608,2156,2156,2156,2156,2156,2156,2156,2156,2156,109,108,1944,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2412,109,108,2156,958,2156,256,2156,2156,956,2156,788,2156,2048,2156,2049,2156],
[2612,2156,109,108,1728,2156,109,108,2156,109,108,2156,109,108,2156,109,108,2156,109,108,2156,109,108,2156,109,108,2156,109,108,1494,2156,109,108,1772,2156,109,108,914,2156,109,108,167,2156,109,108,166,2156,109,108,1558,2156,109,108,1492,2156,109,108,1692,2156,109,108,1012,2156,109,108,1013,2156,109,108,2784,2156,109,108,912,2156,109,108,165,2156,109,108,164,2156,109,108,1556,2156,109,108,688,2156,109,108,689,2156,109,108,2356,2156,109,108,804,2156,109,108,2594,2156,109,108,2016,2156,109,108,2278,2156,109,108,1678,2156,109,108,1679,2156,109,108,1482,2156,109,108,2592,2156,109,108,2644,2156,109,108,725,2156,109,108,724,2156,109,108,2172,2156,109,108,2276,2156,109,108,1676,2156,109,108,1677,2156,109,108,1480,2156,109,108,2205,2156,109,108,2204,2156,109,108,600,2156,109,108,658,958,391,390,2156,109,108,900,256,581,580,2156,109,108,656,956,389,388,2156,109,108,2428,788,1252,1253,2156,109,108,2048,521,2156,109,108,2049,520,2156,109,108,393,392,2704,2156,109,108],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2636,2156,2156,2156,2156,2156,2156,2156,2156,1692,109,108,2156,2156,958,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156],
[2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,2156,990,2156,2156,2156,2156,208,2156,2156,2156,2156,2156,2156,2156,2156,2156,1527,109,108,2156,958,2156,2156,256,2156,956,2156,788,2156,2048,2156,2049,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_32 : (row6_32.zip hint6_32).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

theorem chk6 : ∀ S ∈ row6, ∃ H, verifyS width topMask 5 taus S row5 H = true := by
  intro S hS
  obtain ⟨r, hr, hS⟩ := List.mem_flatten.mp hS
  simp only [row6, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowsS_ok _ _ (by decide) chk6_0 S hS
  · exact rowsS_ok _ _ (by decide) chk6_1 S hS
  · exact rowsS_ok _ _ (by decide) chk6_2 S hS
  · exact rowsS_ok _ _ (by decide) chk6_3 S hS
  · exact rowsS_ok _ _ (by decide) chk6_4 S hS
  · exact rowsS_ok _ _ (by decide) chk6_5 S hS
  · exact rowsS_ok _ _ (by decide) chk6_6 S hS
  · exact rowsS_ok _ _ (by decide) chk6_7 S hS
  · exact rowsS_ok _ _ (by decide) chk6_8 S hS
  · exact rowsS_ok _ _ (by decide) chk6_9 S hS
  · exact rowsS_ok _ _ (by decide) chk6_10 S hS
  · exact rowsS_ok _ _ (by decide) chk6_11 S hS
  · exact rowsS_ok _ _ (by decide) chk6_12 S hS
  · exact rowsS_ok _ _ (by decide) chk6_13 S hS
  · exact rowsS_ok _ _ (by decide) chk6_14 S hS
  · exact rowsS_ok _ _ (by decide) chk6_15 S hS
  · exact rowsS_ok _ _ (by decide) chk6_16 S hS
  · exact rowsS_ok _ _ (by decide) chk6_17 S hS
  · exact rowsS_ok _ _ (by decide) chk6_18 S hS
  · exact rowsS_ok _ _ (by decide) chk6_19 S hS
  · exact rowsS_ok _ _ (by decide) chk6_20 S hS
  · exact rowsS_ok _ _ (by decide) chk6_21 S hS
  · exact rowsS_ok _ _ (by decide) chk6_22 S hS
  · exact rowsS_ok _ _ (by decide) chk6_23 S hS
  · exact rowsS_ok _ _ (by decide) chk6_24 S hS
  · exact rowsS_ok _ _ (by decide) chk6_25 S hS
  · exact rowsS_ok _ _ (by decide) chk6_26 S hS
  · exact rowsS_ok _ _ (by decide) chk6_27 S hS
  · exact rowsS_ok _ _ (by decide) chk6_28 S hS
  · exact rowsS_ok _ _ (by decide) chk6_29 S hS
  · exact rowsS_ok _ _ (by decide) chk6_30 S hS
  · exact rowsS_ok _ _ (by decide) chk6_31 S hS
  · exact rowsS_ok _ _ (by decide) chk6_32 S hS

def hint7_0 : List (List ℕ) := [
[104,900,216,900,900,900,900,900,900,900,900,926,900,784,900,78,900,975,900,974,900,924,900,1308,900,108,900,969,900,968,900,76,900,973,900,972,900,629,900,628,900,224,900,1128,900,1198,900,672,38,900,49,900,48,900,226,900,316,900,676,900,452,900,453,900,1196,900,674,36,900,51,900,50,900,1148,1060,900,540,900,541,900,381,380,1304,900,96,734,900,740,1144,900,98,732,900,356,1024,900,1292,900,92,297,900,93,296,900],
[104,1128,216,1128,1128,1128,1128,1128,1128,1128,1128,926,1128,784,728,730,1128,78,1128,975,1128,974,1128,924,1128,88,1128,1308,1128,969,1128,968,1128,76,1128,973,1128,972,1128,360,488,1128,312,1128,313,1128,629,1128,628,1128,900,1128,224,1128,1198,1128,49,52,1128,48,53,1128,226,1128,440,1128,316,1128,452,1128,453,1128,1196,1128,51,54,1128,50,55,1128,420,1128,113,1128,112,1128,540,1128,541,1128,993,992,1304,1128,96,1002,1128,740,308,1128,98,1000,1128,836,1128,184,356,1128,241,297,1128,240,296,1128],
[104,629,216,629,629,629,629,629,629,629,629,265,629,21,629,267,629,926,629,784,629,78,629,975,629,974,629,924,629,1308,629,940,969,629,968,629,76,629,973,629,972,629,628,629,900,629,958,629,1168,629,956,629,260,428,629,224,629,1128,629,1198,629,49,629,48,629,226,629,316,629,452,629,453,629,1196,629,51,629,50,629,352,472,540,629,541,629,1133,160,1304,629,576,629,202,96,629,644,740,629,200,98,629,288,356,629,529,297,629,68,296,629],
[104,969,216,969,969,969,969,969,969,969,969,14,969,12,969,21,969,108,969,926,969,784,969,78,969,975,969,974,969,924,969,1308,969,968,969,76,969,973,969,972,969,940,629,969,628,969,900,969,250,754,969,248,752,969,1244,776,969,512,1216,969,224,969,1128,969,1198,969,49,969,48,969,226,969,316,969,324,280,452,969,453,969,1196,969,51,969,50,969,540,969,541,969,412,1213,1304,969,1296,969,323,96,969,580,740,969,321,98,969,764,356,969,1089,297,969,1100,296,969],
[660,104,296,1161,216,296,296,296,296,296,296,296,296,433,926,296,16,758,296,537,784,296,369,78,296,932,975,296,842,974,296,1056,84,296,435,924,296,481,1308,296,1100,969,296,1088,968,296,18,756,296,568,684,296,1040,1108,1140,296,371,76,296,934,973,296,840,972,296,68,629,296,528,628,296,93,900,296,720,224,296,1050,930,296,240,1128,296,386,1198,296,890,49,296,134,48,296,1260,1180,296,722,226,296,909,316,296,1236,452,296,1012,453,296,1048,928,296,1076,128,296,1284,148,296,384,1196,296,888,51,296,132,50,296,1004,540,296,613,541,296,584,33,1304,296,478,96,418,296,153,740,24,296,476,416,98,296,492,985,356,296,548,549,297,296],
[104,926,216,926,926,926,926,926,926,926,926,28,926,572,926,14,926,15,926,784,926,1240,78,926,975,926,974,926,924,926,1308,926,969,926,968,926,76,926,973,926,972,926,629,926,628,926,900,926,1288,926,592,926,717,926,716,926,1276,748,224,926,1128,926,1198,926,49,926,48,926,226,926,316,926,452,926,453,926,1196,926,51,926,50,926,540,926,541,926,347,346,1304,926,808,926,1066,96,926,918,740,926,1172,98,926,234,356,926,432,297,926,433,296,926],
[104,1200,740,216,180,740,740,740,740,740,740,740,740,926,918,740,784,1044,740,78,602,740,975,566,740,974,567,740,772,464,740,924,916,740,1308,1072,740,969,580,740,968,581,740,76,600,740,973,564,740,972,565,740,774,466,740,629,644,740,628,645,740,704,848,740,900,1144,740,1265,681,740,1264,680,740,224,518,740,1128,308,740,1198,118,740,49,411,740,48,410,740,998,858,740,226,516,740,316,1020,740,452,884,740,453,885,740,1196,116,740,51,409,740,50,408,740,996,856,740,540,497,740,541,496,740,176,504,740,1304,692,693,244,740,1209,1068,740,1208,1069,740,96,864,136,740,98,138,866,740,356,1184,1156,740,297,152,25,740,296,153,24,740],
[104,316,216,316,316,316,316,316,316,316,316,926,316,784,316,78,316,608,834,316,975,316,974,316,924,316,1308,952,648,316,969,316,968,316,76,316,610,832,316,973,316,972,316,629,316,628,316,188,328,316,189,329,316,900,316,224,316,1128,316,1198,316,796,316,49,316,48,316,226,316,452,316,453,316,1196,316,798,316,51,316,50,316,540,812,316,541,813,316,460,316,461,316,165,164,1304,316,96,198,316,740,1020,316,98,196,316,356,292,316,668,316,908,297,316,909,296,316],
[104,51,216,51,51,51,51,51,51,51,51,926,51,784,51,78,51,975,51,974,51,620,51,924,51,1308,51,969,51,968,51,1312,51,76,484,51,973,1120,944,51,972,51,629,51,628,51,652,51,900,51,340,51,224,51,1128,54,51,1198,51,49,424,51,48,51,113,51,226,502,51,316,51,452,51,453,51,883,51,1196,51,50,1032,51,540,51,541,51,604,51,1304,2,639,51,1054,51,96,339,51,740,409,51,98,509,51,356,273,51,297,133,51,296,888,51,1176,51],
[104,78,216,78,78,78,78,78,78,78,78,572,78,1112,78,265,78,264,78,1240,926,78,520,784,78,975,78,974,78,924,78,1308,78,969,78,968,78,724,76,78,973,78,972,78,629,78,628,78,900,78,1152,78,204,78,268,78,269,78,224,78,1128,78,142,42,1198,78,486,49,78,487,48,78,226,78,316,78,452,78,453,78,1196,78,51,78,50,78,540,78,541,78,525,524,1304,78,664,78,1030,96,78,602,740,78,208,98,78,438,356,78,368,297,78,369,296,78]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk7_0 : (row7_0.zip hint7_0).all (fun p => verifyS width topMask 6 taus p.1 row6 p.2) = true := by
  decide +kernel

def hint7_1 : List (List ℕ) := [
[104,216,216,216,216,216,216,216,216,926,216,784,216,78,216,975,216,974,216,924,216,1308,216,969,216,968,216,76,216,973,216,972,216,629,216,628,216,900,216,224,216,1128,216,1198,216,49,216,48,216,226,216,316,216,452,216,453,216,1196,216,51,216,50,216,540,216,541,216,1304,588,589,216,96,192,216,740,180,216,98,194,216,356,392,216,297,1160,216,296,1161,216],
[104,973,216,973,973,973,973,973,973,973,973,12,973,267,973,926,973,784,973,78,973,975,973,974,973,924,973,1308,973,969,973,968,973,76,973,972,973,629,973,628,973,900,973,892,1252,973,1124,973,228,973,1256,844,973,224,973,1128,973,1198,973,49,973,48,973,226,973,316,973,452,973,453,973,1196,973,1120,944,51,973,50,973,540,973,541,973,805,158,1304,973,144,973,83,96,973,564,740,973,449,98,973,121,356,973,841,297,973,934,296,973],
[104,224,216,224,224,224,224,224,224,224,224,926,1276,748,224,784,224,78,224,975,224,974,224,924,224,1308,224,969,224,968,224,1116,224,872,224,709,224,708,224,76,224,973,224,972,224,629,224,628,224,900,224,1128,224,1198,224,49,500,224,48,501,224,226,224,316,224,452,224,453,224,440,224,796,224,881,224,880,224,1196,224,51,224,50,224,540,224,541,224,6,7,1304,224,96,458,224,740,518,224,980,224,780,98,224,300,356,224,721,297,224,720,296,224],
[104,1196,216,1196,1196,1196,1196,1196,1196,1196,1196,926,1196,784,1196,78,1196,1272,1204,1196,975,1196,974,1196,924,1196,1308,1196,44,1196,969,1196,968,1196,76,140,40,1196,973,1196,972,1196,629,1196,628,1196,988,1196,989,1196,900,1196,224,1196,1128,1196,1198,1196,420,1196,49,1196,48,1196,226,1196,316,1196,798,1196,452,1196,453,1196,51,1196,50,1196,540,1196,541,1196,604,1196,605,1196,350,351,1304,1196,96,100,1196,740,116,1196,98,1096,1196,356,632,1196,388,1196,385,297,1196,384,296,1196],
[104,62,98,216,194,98,98,98,98,98,98,98,98,926,1172,98,784,222,98,78,208,98,975,81,98,72,960,98,974,80,98,924,1064,98,1308,904,98,969,321,98,1080,936,98,968,320,98,76,1028,98,973,449,98,972,448,98,629,200,98,1300,236,98,628,201,98,552,376,98,900,732,98,553,377,98,224,780,98,1128,1000,98,1198,102,98,49,337,98,912,396,98,48,336,98,226,456,98,316,196,98,452,965,98,596,688,98,453,964,98,1196,1096,98,51,509,98,50,508,98,540,818,98,468,1224,98,541,819,98,169,745,98,256,1304,257,616,98,168,744,98,96,792,794,98,740,138,866,98,356,978,626,98,297,477,417,98,476,296,416,98],
[104,784,216,784,784,784,784,784,784,784,784,28,784,1112,784,926,784,520,78,784,975,784,974,784,924,784,1308,784,969,784,968,784,522,76,784,973,784,972,784,629,784,628,784,900,784,860,784,768,784,657,332,784,656,333,784,224,784,728,730,1128,784,1198,784,49,784,48,784,226,784,316,784,452,784,453,784,1196,784,51,784,50,784,540,784,541,784,877,876,1304,784,760,784,220,96,784,1044,740,784,222,98,784,1164,356,784,536,297,784,537,296,784],
[104,540,216,540,540,540,540,540,540,540,540,926,540,784,540,78,540,975,540,974,540,374,540,924,540,1308,540,969,540,968,540,532,540,76,540,973,540,972,540,372,540,629,352,472,540,628,540,900,540,1268,540,224,540,1128,540,1198,540,49,540,48,540,606,540,226,540,316,812,540,452,540,453,540,460,540,1196,540,51,540,50,540,604,540,541,560,540,1304,821,1220,540,852,540,96,816,540,740,497,540,98,818,540,356,869,540,297,612,540,296,1004,540,1016,540],
[104,1136,356,216,392,356,356,356,356,356,356,356,356,926,234,356,784,1164,356,78,438,356,975,123,356,284,254,356,974,122,356,924,232,356,1308,1188,356,969,764,356,556,824,356,968,765,356,76,436,356,973,121,356,286,252,356,972,120,356,629,288,356,628,289,356,365,736,356,900,1024,356,364,737,356,224,300,356,1128,184,356,1198,634,356,49,275,356,830,1104,356,48,274,356,226,302,356,316,292,356,452,56,356,1092,1280,356,453,57,356,1196,632,356,51,273,356,828,1106,356,50,272,356,540,869,356,541,868,356,1229,641,356,801,1304,800,1192,356,1228,640,356,96,976,624,356,740,1184,1156,356,98,978,626,356,297,493,984,356,492,296,985,356],
[104,452,216,452,452,452,452,452,452,452,452,926,452,784,452,78,452,975,452,212,452,974,452,924,452,1308,452,969,324,280,452,968,452,76,452,973,452,214,452,972,452,629,452,8,452,628,452,900,452,920,452,224,452,1128,452,1198,452,49,452,881,452,48,452,226,452,316,452,453,452,1196,452,51,452,883,452,50,452,540,452,460,452,541,452,712,1304,789,452,400,452,96,967,452,740,884,452,98,965,452,356,56,452,297,1013,452,1232,452,1236,296,452],
[104,701,700,1304,216,588,589,1304,1304,1304,1304,1304,1304,1304,1304,926,347,346,1304,784,877,876,1304,78,525,524,1304,975,807,156,1304,974,157,806,1304,898,307,306,1304,924,345,344,1304,1308,696,697,1304,969,412,1213,1304,968,1212,413,1304,404,1036,1037,1304,76,527,526,1304,973,805,158,1304,972,159,804,1304,896,305,304,1304,629,1133,160,1304,628,161,1132,1304,1248,276,277,1304,900,381,380,1304,224,6,7,1304,1128,993,992,1304,1198,348,349,1304,49,0,637,1304,48,636,1,1304,1052,125,124,1304,226,4,5,1304,316,165,164,1304,452,712,789,1304,453,788,713,1304,400,173,172,1304,1196,350,351,1304,51,2,639,1304,50,638,3,1304,1054,127,126,1304,540,821,1220,1304,541,1221,820,1304,852,1009,1008,1304,96,258,259,618,1304,740,692,693,244,1304,98,256,257,616,1304,356,801,800,1192,1304,297,32,585,1304,296,584,33,1304,1084,65,64,1304]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk7_1 : (row7_1.zip hint7_1).all (fun p => verifyS width topMask 6 taus p.1 row6 p.2) = true := by
  decide +kernel

def hint7_2 : List (List ℕ) := [
[104,216,104,104,104,104,104,104,104,926,104,784,104,78,104,975,104,974,104,924,104,1308,104,969,104,968,104,76,104,973,104,972,104,629,104,628,104,900,104,224,104,1128,104,1198,104,49,104,48,104,226,104,316,104,452,104,453,104,1196,104,51,104,50,104,540,104,541,104,701,700,1304,104,60,96,104,1200,740,104,62,98,104,1136,356,104,661,297,104,660,296,104],
[104,1308,216,1308,1308,1308,1308,1308,1308,1308,1308,572,1308,574,1308,21,1308,20,1308,926,1308,784,1308,78,1308,975,1308,974,1308,924,1308,969,1308,968,1308,76,1308,973,1308,972,1308,629,1308,628,1308,900,1308,948,1308,950,1308,545,1308,544,1308,224,1308,1128,1308,1198,1308,49,1308,48,1308,226,1308,952,648,316,1308,452,1308,453,1308,1196,1308,51,1308,50,1308,540,1308,541,1308,696,697,1304,1308,444,1308,906,96,1308,1072,740,1308,904,98,1308,1188,356,1308,480,297,1308,481,296,1308]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk7_2 : (row7_2.zip hint7_2).all (fun p => verifyS width topMask 6 taus p.1 row6 p.2) = true := by
  decide +kernel

theorem chk7 : ∀ S ∈ row7, ∃ H, verifyS width topMask 6 taus S row6 H = true := by
  intro S hS
  obtain ⟨r, hr, hS⟩ := List.mem_flatten.mp hS
  simp only [row7, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact rowsS_ok _ _ (by decide) chk7_0 S hS
  · exact rowsS_ok _ _ (by decide) chk7_1 S hS
  · exact rowsS_ok _ _ (by decide) chk7_2 S hS

def hint8_0 : List (List ℕ) := [
[80,40,0,0,0,0,0,0,84,20,22,12,13,36,38,8,9,60,46,47,44,45,0,28,48,50,72,73,54,52,64,65,4,34,35,32,33,76,24,68,58,56,17,16]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk8_0 : (row8_0.zip hint8_0).all (fun p => verifyS width topMask 7 taus p.1 row7 p.2) = true := by
  decide +kernel

theorem chk8 : ∀ S ∈ row8, ∃ H, verifyS width topMask 7 taus S row7 H = true := by
  intro S hS
  obtain ⟨r, hr, hS⟩ := List.mem_flatten.mp hS
  simp only [row8, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact rowsS_ok _ _ (by decide) chk8_0 S hS

theorem excluded (f : ℕ)
    (hp : ∀ i < width, topMask.testBit i = topMask.testBit (width+i) ∧ f.testBit i ≠ f.testBit (width+i))
    (hc : Can topMask f 8 inputs.toFinset) : False := by
  have hT : 0 < taus.length := by decide
  have hTs : taus.all (tauOK width) = true := by decide +kernel
  have hm : ∀ j, topMask.testBit j = decide (j < 2*width) := by
    intro j
    rw [show topMask = 2^(2*width) - 1 by norm_num [topMask, width]]
    exact Nat.testBit_two_pow_sub_one _ _
  obtain ⟨H8, hH8⟩ := chk8 inputs (by simp [row8, row8_0])
  obtain ⟨S7, hS7, f7, hp7, c7⟩ := advanceS hT hTs hm hp hH8 hc
  obtain ⟨H7, hH7⟩ := chk7 S7 hS7
  obtain ⟨S6, hS6, f6, hp6, c6⟩ := advanceS hT hTs hm hp7 hH7 c7
  obtain ⟨H6, hH6⟩ := chk6 S6 hS6
  obtain ⟨S5, hS5, f5, hp5, c5⟩ := advanceS hT hTs hm hp6 hH6 c6
  obtain ⟨H5, hH5⟩ := chk5 S5 hS5
  obtain ⟨S4, hS4, f4, hp4, c4⟩ := advanceS hT hTs hm hp5 hH5 c5
  obtain ⟨H4, hH4⟩ := chk4 S4 hS4
  obtain ⟨S3, hS3, f3, hp3, c3⟩ := advanceS hT hTs hm hp4 hH4 c4
  obtain ⟨H3, hH3⟩ := chk3 S3 hS3
  obtain ⟨S2, hS2, f2, hp2, c2⟩ := advanceS hT hTs hm hp3 hH3 c3
  obtain ⟨H2, hH2⟩ := chk2 S2 hS2
  obtain ⟨S1, hS1, f1, hp1, c1⟩ := advanceS hT hTs hm hp2 hH2 c2
  simp [row1, row1_0] at hS1

def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373994 * 2 ^ 32 + 4008372352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def assignment (p : ℕ) (i : Fin 6) : Bool := (inputs.getD i.val 0).testBit p

theorem inputMap (p : ℕ) : List.ofFn (assignment p) = inputs.map (fun t => t.testBit p) := by
  simp [inputs,assignment,List.ofFn_succ]

theorem values : ∀ p : Fin (2*width), target (assignment p.val) = targetBits.testBit p.val ∧
    topMask.testBit p.val = true := by decide +kernel

theorem paired : ∀ i : Fin width, targetBits.testBit i.val ≠ targetBits.testBit (width+i.val) := by
  decide +kernel

theorem lower (t : ℕ) (h : HasCircuitSize 6 target t) : 9 ≤ t := by
  by_contra! ht
  obtain ⟨C,ok,sz,ev⟩ := h
  have hok : ∀ g ∈ C.gates, GOk g := ok
  let out := (tabs topMask inputs C.gates).getD C.output 0
  have obs (p : Fin (2*width)) : out.testBit p.val = targetBits.testBit p.val := by
    have hval := ev (assignment p.val)
    unfold Circuit.eval Circuit.wires at hval
    rw [inputMap,wires_tabs topMask p.val (values p).2 _ _ hok,getD_map_testBit] at hval
    exact hval.trans (values p).1
  have hw : ∀ i < width, topMask.testBit i = topMask.testBit (width+i) ∧ out.testBit i ≠ out.testBit (width+i) := by
    intro i hi
    let p : Fin (2*width) := ⟨i,by omega⟩
    let q : Fin (2*width) := ⟨width+i,by omega⟩
    exact ⟨(values p).2.trans (values q).2.symm,fun e => paired ⟨i,hi⟩ ((obs p).symm.trans (e.trans (obs q)))⟩
  have hc := fromTabs topMask out C.gates inputs hok (getWire _ C.output topMask)
  have pad {k j : ℕ} (hj : k ≤ j) (ha : Can topMask out k inputs.toFinset) : Can topMask out j inputs.toFinset := by
    induction hj with
    | refl => exact ha
    | step _ ih => exact stepUp ih
  change C.gates.length ≤ t at sz
  exact excluded out hw (pad (by omega) hc)

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem witMono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem witEval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witSize : witness.size = 9 := rfl

end PEqualNP.Outside.L_meta_12595

theorem PEqualNP.Outside.L_meta_12595 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373994 * 2 ^ 32 + 4008372352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373994 * 2 ^ 32 + 4008372352) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  fun s hs => ⟨PEqualNP.Outside.L_meta_12595.witness, PEqualNP.Outside.L_meta_12595.witMono, PEqualNP.Outside.L_meta_12595.witSize ▸ PEqualNP.Outside.L_meta_12595.lower s hs, PEqualNP.Outside.L_meta_12595.witEval⟩
