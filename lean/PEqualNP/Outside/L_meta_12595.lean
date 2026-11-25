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

/-- The cuts of `S` with one new value: those inside `S` once, then for each new value `v` those through `v`. -/
def cutsV (k : ℕ) (S vs : List ℕ) : List (List ℕ) :=
  cuts (k+1) S ++ vs.flatMap fun v => if v ∈ S then [] else (cuts k S).map (v :: ·)

theorem cutsV_spec {k v : ℕ} {S vs : List ℕ} (hv : v ∈ vs) (T : Finset ℕ)
    (h : T ⊆ insert v S.toFinset) (n : T.card ≤ k+1) : ∃ U ∈ cutsV k S vs, T ⊆ U.toFinset := by
  by_cases hvS : v ∈ S ∨ v ∉ T
  · have hT : T ⊆ S.toFinset := by
      intro y hy
      rcases Finset.mem_insert.mp (h hy) with rfl | h'
      · rcases hvS with h1 | h1
        · exact List.mem_toFinset.mpr h1
        · exact absurd hy h1
      · exact h'
    obtain ⟨U, hU, sub⟩ := cutsSpec (k+1) S T hT n
    exact ⟨U, List.mem_append_left _ hU, sub⟩
  · push_neg at hvS
    obtain ⟨hvS, hvT⟩ := hvS
    have hs : T.erase v ⊆ S.toFinset := by
      intro y hy
      rcases Finset.mem_insert.mp (h (Finset.mem_of_mem_erase hy)) with e | h'
      · exact absurd e (Finset.ne_of_mem_erase hy)
      · exact h'
    obtain ⟨U, hU, sub⟩ := cutsSpec k S (T.erase v) hs (by rw [Finset.card_erase_of_mem hvT]; omega)
    refine ⟨v :: U, List.mem_append_right _ (List.mem_flatMap.mpr ⟨v, hv, ?_⟩), ?_⟩
    · rw [if_neg hvS]; exact List.mem_map.mpr ⟨U, hU, rfl⟩
    · intro y hy
      by_cases e : y = v
      · simp [e]
      · simpa [e] using sub (Finset.mem_erase.mpr ⟨e, hy⟩)

def verifyS (d m k : ℕ) (Ts : List (List ℕ)) (S : List ℕ) (N : List (List ℕ)) (H : List ℕ) : Bool :=
  chkS d Ts N (cutsV k S (vals m S)) H

theorem advanceS {d m f k : ℕ} {Ts : List (List ℕ)} {S : List ℕ} {N : List (List ℕ)} {H : List ℕ}
    (hT : 0 < Ts.length) (hTs : Ts.all (tauOK d) = true)
    (hm : ∀ j, m.testBit j = decide (j < 2*d))
    (hp : ∀ i < d, m.testBit i = m.testBit (d+i) ∧ f.testBit i ≠ f.testBit (d+i))
    (hv : verifyS d m k Ts S N H = true) (hc : Can m f (k+1) S.toFinset) :
    ∃ V ∈ N, ∃ f' : ℕ, (∀ i < d, m.testBit i = m.testBit (d+i) ∧ f'.testBit i ≠ f'.testBit (d+i)) ∧
      Can m f' k V.toFinset := by
  obtain ⟨o,a,b,ha,hb,hh⟩ := hc
  let v := comb m o a b
  obtain ⟨T,hT',hn,ht⟩ := small hh
  obtain ⟨U,hmemU,hu⟩ := cutsV_spec (memVals o ha hb) T hT' hn
  have hcU := monoC hu ht
  have hcov := covered hcU hp
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
[12,8,4,0],
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
[12,8,4,0],
[4],
[],
[],
[12],
[12],
[12,8,4,0],
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
[12,8,4,0],
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
[12,8,4,0],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk3_4 : (row3_4.zip hint3_4).all (fun p => verifyS width topMask 2 taus p.1 row2 p.2) = true := by
  decide +kernel

def hint3_5 : List (List ℕ) := [
[12,8,4,0],
[],
[8],
[12,8,4,0],
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
[176,148,192,84,144,20,28,216],
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
[49,148,57,108,32,88,113,121],
[137,176],
[],
[],
[],
[],
[],
[48,140,200,109,56,33,89,120,112]]
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
[132,200,192,212,224,208,128,204],
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
[176,192,84,109,144,20,28,216],
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
[176,192,84,56,144,20,28,216],
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
[176,192,84,212,144,20,28,216],
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
[62,8,70,156,82],
[42,26,0,162,38],
[],
[],
[224,180],
[],
[],
[],
[],
[60,158,68,10,80]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_13 : (row4_13.zip hint4_13).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_14 : List (List ℕ) := [
[48,184,109,108,56,33,89,120,112],
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
[49,192,57,108,32,88,113,121],
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
[42,26,0,162,38],
[],
[60,158,68,10,80],
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
[40,24,2,160,36]]
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
[176,200,192,84,144,20,28,216],
[42],
[184,176],
[82],
[132,200,148,212,224,208,128,204],
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
[60,158,68,10,80],
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
[40,24,2,160,36],
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
[49,84,57,108,32,88,113,121]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk4_26 : (row4_26.zip hint4_26).all (fun p => verifyS width topMask 3 taus p.1 row3 p.2) = true := by
  decide +kernel

def hint4_27 : List (List ℕ) := [
[4,42,40,176],
[],
[],
[40,24,2,160,36],
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
[132,184,200,108,212,224,208,128,204],
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
[60,158,68,10,80],
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
[132,200,84,212,224,208,128,204],
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
[444,480,1348,482,0,1160],
[104],
[358,598,946],
[1304,220,1284,546,544,1348,1272,0],
[0],
[900,972],
[0,1032,1304,1034,444,936],
[1304,724,224,546,544,1348,1272,0],
[1150,451,524,1030,700,724,1324,1312,588,872],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_0 : (row5_0.zip hint5_0).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_1 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[330,149],
[1052],
[0,1032,1304,1034,444,936],
[217,492,160],
[1342,884,1264,708,768,1234,1104,552,818],
[1034,634,864,544,482,0,776],
[936,778,1272,0,776,1160],
[550,548,832]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_1 : (row5_1.zip hint5_1).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_2 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[936,1114,778,1272,0,776,1160],
[372,558,1266,710,830,1278,730,1074,1112],
[0,840,960,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[],
[444,1140,480,1348,482,0,1160],
[0,1032,1304,1034,444,936],
[1034,60,864,544,482,0,776],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_2 : (row5_2.zip hint5_2).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_3 : List (List ℕ) := [
[1034,460,880,764,990,864,544,482,0,776],
[0,1336,598,358,1032,1304,1034,444,936],
[1342,0,884,556,1264,768,1032,1234,1304,1104,1034,552,444,818,936],
[1034],
[303],
[0,1032,1304,1034,444,936],
[1034,876,864,544,482,0,776],
[341,1136],
[0,1032,1304,1034,444,936],
[358,1062,334,78,464,1178]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_3 : (row5_3.zip hint5_3).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_4 : List (List ℕ) := [
[1150,758,524,700,724,1324,1312,588,872],
[0,150,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[133,396,0,74,977,72,528,612],
[38],
[904,144,1364,1165,813,804,272,424,536,220,1196,324,1012],
[1034,864,544,482,0,776],
[936,624,778,1272,0,776,1160],
[1034,472,864,544,482,0,776],
[0,1032,1304,1034,444,936]]
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
[133,704,74,977,72,528,612],
[658,656,217,216,712,400],
[308]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_5 : (row5_5.zip hint5_5).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_6 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[1034,876,864,544,482,0,776],
[0,1074,104,1032,1304,1034,444,936],
[808,416,242],
[1304],
[444],
[482],
[632],
[1304,184,546,544,1348,1272,0],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_6 : (row5_6.zip hint5_6).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_7 : List (List ℕ) := [
[308,868],
[1034,828,864,544,482,0,776],
[1016,1284],
[592,178],
[1034,864,544,482,0,776],
[0,824,788,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[484,550,592],
[506],
[0,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_7 : (row5_7.zip hint5_7).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_8 : List (List ℕ) := [
[41],
[0,302,300,124,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[936,872,778,1272,0,776,1160],
[308,0],
[1034,564,864,544,482,0,776],
[],
[1056,117,616,1076,244,804,313,273,572,605,436,453,477],
[1034,990,864,544,482,0,776],
[600]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_8 : (row5_8.zip hint5_8).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_9 : List (List ℕ) := [
[1034],
[1034,864,544,482,0,776],
[284,1032],
[0],
[],
[1348,22,20,1304,28,444],
[684],
[1034,864,544,482,0,776],
[936,778,1272,0,776,1160],
[276]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_9 : (row5_9.zip hint5_9).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_10 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[976],
[],
[936,778,1272,0,776,1160],
[828],
[151,1301,187,128,972,120],
[1034,129,864,544,482,0,776],
[],
[1034,1124,864,544,482,0,776],
[340,432]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_10 : (row5_10.zip hint5_10).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_11 : List (List ℕ) := [
[936,856,778,1272,0,776,1160],
[1062],
[1352],
[1032,546,864,480,778,0],
[0,352,354,132,1032,1304,1034,444,936],
[],
[133],
[936,778,1272,406,0,1032,776,1236,1160,534],
[0,1200,412,1032,1304,1034,444,936],
[1356]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_11 : (row5_11.zip hint5_11).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_12 : List (List ℕ) := [
[],
[0,1316,196,1032,1304,1034,444,936],
[248,0,908,720,668,1170,1032,68,1304,388,1168,1034,1188,444,936],
[601,1212,1214,507,40,505,1172,440],
[],
[328,52],
[444,480,1348,482,0,1160],
[0,651,971,1032,1304,1034,444,936],
[417,0],
[0,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_12 : (row5_12.zip hint5_12).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_13 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[544],
[0,470,1032,238,1304,8,1034,444,1042,936,540,760],
[],
[778],
[444,482,480,1252,1348,20,0,1034,1160,532],
[],
[1132],
[50],
[1034]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_13 : (row5_13.zip hint5_13).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_14 : List (List ℕ) := [
[0,1196,1208,1032,1304,1034,444,936],
[0,151,1032,1301,1304,187,1034,128,444,972,936,120],
[840],
[1292],
[1068,844],
[1304,546,544,1348,1272,0],
[],
[808,809,1150],
[1034,770,864,544,482,0,776],
[936,1272,778,406,0,1304,776,404,1160,28]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_14 : (row5_14.zip hint5_14).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_15 : List (List ℕ) := [
[0,868,1032,1304,1034,444,936],
[936,364,778,1272,0,776,1160],
[888],
[0,1032,1304,1034,444,936],
[139,1056,94,1328],
[374,884,556,708,728,1276,828,1072,1114],
[444,1008,480,1348,482,0,1160],
[444,480,1348,482,0,1160],
[],
[392,384,918,304,462,1192,630,158,202]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_15 : (row5_15.zip hint5_15).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_16 : List (List ℕ) := [
[1064],
[],
[176,25,204,772,292,609],
[308,284,956,286,1332,892],
[0,1034,1032,864,1304,544,444,482,936,776],
[8],
[],
[936,778,1272,0,776,1160],
[964,1102,660,1148,1080],
[936,120,778,1272,0,776,1160]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_16 : (row5_16.zip hint5_16).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_17 : List (List ℕ) := [
[444,480,1348,482,0,1160],
[934],
[0,1032,1304,1034,444,936],
[664,1338],
[656,1342],
[372,558,710,520,830,1278,730,1074,1112],
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[600,506,41,504,1173,441],
[528]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_17 : (row5_17.zip hint5_17).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_18 : List (List ℕ) := [
[936,1012,778,1272,0,776,1160],
[0,1032,1304,1034,444,936],
[776,1236,404,1034,532,936],
[0,1032,1304,1034,444,936],
[196],
[1348],
[0,1150,1094,524,700,1032,1304,724,1324,1034,1312,444,588,936,872],
[0,1032,1304,1034,444,936],
[0,924,380,1032,1304,1034,444,936],
[658,558,520,521,1036,1388,1180,278,279]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_18 : (row5_18.zip hint5_18).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_19 : List (List ℕ) := [
[1332],
[948],
[140],
[76],
[416,1228,748,497,1268,1368],
[248],
[0,1032,1304,1034,444,936],
[444],
[356,932,344,568,76,332,1060,466,1176],
[22]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_19 : (row5_19.zip hint5_19).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_20 : List (List ℕ) := [
[646],
[0,468,470,1204,1032,1304,1034,444,936],
[912],
[482,1252,20,1034,444,532],
[0,1032,1304,1034,444,936],
[936],
[0,392,1032,462,1304,1192,1034,630,444,158,936,202],
[1304,546,544,1348,1272,0],
[100],
[444,973,480,1348,482,0,1160]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_20 : (row5_20.zip hint5_20).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_21 : List (List ℕ) := [
[1032,546,864,480,778,0],
[0,1032,1304,1034,444,936],
[1304,332,334,68,546,544,1348,1272,0],
[1032,546,864,1296,480,22,778,406,0,1304],
[448,240],
[936,778,1272,0,776,1160],
[0],
[786],
[0,1032,1304,1034,444,936],
[0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_21 : (row5_21.zip hint5_21).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_22 : List (List ℕ) := [
[696,62,210,316,580,166],
[129],
[],
[1304,1276,546,544,1348,1272,0],
[444,1020,1022,480,1348,482,0,1160],
[0,1304,1032,546,1034,544,444,1348,936,1272],
[1034,864,544,482,0,776],
[0,176,1032,25,1304,204,1034,772,444,292,936,609],
[0,372,1032,1304,1034,444,936],
[1034,864,544,482,0,776]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_22 : (row5_22.zip hint5_22).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_23 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[],
[712,117,88,561,116,89,560,820,1165,1164,420,1016,1004,853,852],
[1032,24,507,738,546,864,480,778,0],
[868,168,1120,256,170,1044],
[177,997,1214,24,205,773,293,608],
[1034]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_23 : (row5_23.zip hint5_23).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_24 : List (List ℕ) := [
[1034,1308,864,544,482,0,776],
[0,1032,1304,1034,444,936],
[1304,1120,546,544,1348,1272,0],
[936,778,1272,0,776,1160],
[80],
[936,164,778,1272,0,776,1160],
[0,1032,1304,1034,444,936],
[178],
[],
[1304,546,544,1348,1272,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_24 : (row5_24.zip hint5_24).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_25 : List (List ℕ) := [
[394,628,1194,460,156,200],
[0,720,1376,248,908,1032,882,1304,1384,1034,880,444,744,936,1156],
[477],
[0,178,176,600,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[984,67],
[444,1010,480,1348,482,0,1160],
[491]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_25 : (row5_25.zip hint5_25).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_26 : List (List ℕ) := [
[0,685,1032,1304,1034,444,936],
[],
[0,1032,1304,1034,444,936],
[936,778,1272,0,776,1160],
[0,1152,36,38,4,1032,1304,1034,444,936],
[437,1024],
[1304,546,544,1348,1272,0],
[444,480,1348,482,0,1160],
[1388,1232],
[470]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_26 : (row5_26.zip hint5_26).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_27 : List (List ℕ) := [
[1304,544,546,1296,1348,20,1272,404,0,1034],
[696,62,210,316,580,166],
[1034,170,864,544,482,0,776],
[698],
[656,1002],
[328,348,1344,360,900,140,428],
[0,952,680,1032,1304,1034,444,936],
[0,112,1032,1304,1034,444,936],
[1304,1276,1234,546,544,1348,1272,0],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_27 : (row5_27.zip hint5_27).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_28 : List (List ℕ) := [
[1304,1352,546,544,1348,1272,0],
[936,1012,1244,778,1272,0,776,1160],
[0,1032,1304,1034,444,936],
[108],
[416,348,1228,748,497,1268,1368],
[516,932,934,688,844,270,268,1152,364],
[1304,546,544,1348,1272,0],
[1304,546,544,1348,1272,0],
[1228],
[712,620]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_28 : (row5_28.zip hint5_28).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_29 : List (List ℕ) := [
[],
[],
[0,1032,1304,1034,444,936],
[444,588,376,480,1348,482,0,1160],
[1108],
[348,151],
[181,178],
[1034,1060,268,296,1168,864,544,482,0,776],
[0,151,1144,1328,1032,1304,1034,444,936],
[956,1304]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_29 : (row5_29.zip hint5_29).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_30 : List (List ℕ) := [
[1004,920],
[0,192,800,1032,1304,1034,444,936],
[677,328,330,1056],
[592,594,832],
[0,1032,1304,1034,444,936],
[0,536,1032,1304,1034,444,936],
[1144,160,162,58,56,273,860,1128,862,1024,1048],
[1034,864,544,482,0,776],
[0,1032,1304,1034,444,936],
[1272,406,1304,404,28,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_30 : (row5_30.zip hint5_30).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_31 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[1032,830,508,546,864,480,778,0],
[544,1296,20,1304,404,1034],
[444,480,1348,482,0,1160],
[0,188,190,652,1320,1032,1304,1034,444,936],
[720,908,882,1384,880,744,1156],
[296],
[0,320,752,1032,1304,1034,444,936],
[838,836,1144,1080],
[444,376,480,1348,482,0,1160]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_31 : (row5_31.zip hint5_31).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_32 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[0,150,148,1032,1304,1034,444,936],
[0,601,1032,507,1304,40,1034,505,444,1172,936,440],
[936,1160,778,534,1272,28,0,444,776,532],
[904,822,144,1364,804,58,424,536,220,1196,324,1012],
[0,1044,1032,1304,1034,444,936],
[1160],
[25],
[0,174,172,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_32 : (row5_32.zip hint5_32).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_33 : List (List ℕ) := [
[309],
[1057,89,617,1077,56,272,312,573,604,437,476,452],
[1020],
[1304,336,546,544,1348,1272,0],
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[444,480,1348,482,0,1160],
[0,86,1032,1304,1034,444,936],
[936,778,1272,0,776,1160],
[0,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_33 : (row5_33.zip hint5_33).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_34 : List (List ℕ) := [
[762],
[332],
[712,117,616,561,116,617,560,144,1165,1164,420,1016,1004,853,852],
[1056,1144],
[0,1032,1304,1034,444,936],
[936,778,1272,0,776,1160],
[0,1032,1304,1034,444,936],
[781],
[132],
[1204,646,796,644,1116,1064]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_34 : (row5_34.zip hint5_34).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_35 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[1034,564,864,544,482,0,776],
[0,732,1256,1032,1304,1034,444,936],
[444,1024,324,480,1348,482,0,1160],
[452],
[151,1301,187,128,972,120],
[0,1032,1304,1034,444,936],
[1160,444,534,480,28,1348,532,482,936,0],
[],
[444,552,480,1348,482,0,1160]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_35 : (row5_35.zip hint5_35).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_36 : List (List ℕ) := [
[1173],
[444,480,1348,482,0,1160],
[136,676,213],
[0,1150,662,1148,660,1032,1304,1034,444,936],
[860],
[1034,170,864,544,482,0,776],
[1304,10,8,796,546,544,1348,1272,0],
[0,1032,1304,1034,444,936],
[1304,1348,546,22,544,20,1272,28,0,444],
[284]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_36 : (row5_36.zip hint5_36).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_37 : List (List ℕ) := [
[0,242,1032,1304,1034,444,936],
[853,476],
[464],
[0,696,1032,1304,1034,444,936],
[985,416],
[1144,160,162,58,56,313,860,1128,862,1024,1048],
[1032,480,546,22,864,1252,778,534,0,444],
[60],
[852],
[796]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_37 : (row5_37.zip hint5_37).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_38 : List (List ℕ) := [
[868,168,1120,256,170,1044],
[0,179,180,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[470,238,8,1042,540,760],
[],
[1340,886,1266,520,1106,1232,770,554,816],
[936,164,778,1272,0,776,1160],
[444,480,1348,482,0,1160],
[444,580,480,1348,482,0,1160],
[0,1150,242,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_38 : (row5_38.zip hint5_38).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_39 : List (List ℕ) := [
[1034,864,544,482,0,776],
[1032,546,864,480,778,0],
[620,822,820,1165,214,1100,212,1102,632,1284,920,634,1244],
[864,1296,1252,1032,1236,1034],
[968],
[468,692,1134,10,236,1040,762,542],
[512],
[0,1032,1304,1034,444,936],
[],
[248,568,688,570,908,1170,68,388,1168,1188]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_39 : (row5_39.zip hint5_39).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_40 : List (List ℕ) := [
[1272,1304,406,546,404,544,28,1348,936,0],
[582],
[1042],
[0,318,1032,1304,1034,444,936],
[1036,1106],
[1304,1084,546,544,1348,1272,0],
[444,480,1348,482,0,1160],
[1331,213,148],
[0,1032,1304,1034,444,936],
[0,179,1136,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_40 : (row5_40.zip hint5_40).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_41 : List (List ℕ) := [
[354],
[331,419],
[436,437,324],
[1304,546,544,1348,1272,0],
[0,98,96,1032,1304,1034,444,936],
[948],
[0,576,578,1032,1304,1034,444,936],
[772],
[1032,270,546,864,480,778,0],
[0,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_41 : (row5_41.zip hint5_41).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_42 : List (List ℕ) := [
[936,778,1272,0,776,1160],
[868,168,1120,256,170,1044],
[176,25,204,772,292,609],
[0,516,1032,1304,1034,444,936],
[936,778,1272,0,776,1160],
[658,886,520,521,1036,1388,1180,278,279],
[1204,1134,1132,646,796,644,1116,1064],
[150,512,186,1300,129,973,121],
[268],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_42 : (row5_42.zip hint5_42).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_43 : List (List ℕ) := [
[417,416,470],
[1088],
[0,1032,1304,1034,444,936],
[1032,860,546,864,480,778,0],
[1304,1128,220,546,544,1348,1272,0],
[1034,864,544,1296,482,1252,0,1032,776,1236],
[1216,290,394],
[360,748],
[232,892],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_43 : (row5_43.zip hint5_43).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_44 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[],
[],
[0,1144,904,1032,1304,1034,444,936],
[936,778,1272,0,776,1160],
[1304,546,544,1348,1272,0],
[1304,546,544,1348,1272,0],
[],
[1032,546,864,480,778,0],
[0,780,782,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_44 : (row5_44.zip hint5_44).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_45 : List (List ℕ) := [
[],
[0,1032,1304,1034,444,936],
[428,228,1368],
[444,1040,1042,480,1348,482,0,1160],
[444,672,480,1348,482,0,1160],
[1228,1032],
[550,1213],
[1180,1392,730],
[936,542,252,540,1116,778,1272,0,776,1160],
[0,812,1144,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_45 : (row5_45.zip hint5_45).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_46 : List (List ℕ) := [
[1032,546,864,480,778,0],
[936,611,609,441,778,1272,0,776,1160],
[1010],
[1034,1312,864,544,482,0,776],
[936],
[],
[658,372],
[0,1032,1304,1034,444,936],
[948,306,304,1280,1320,988,990,1140,1360],
[278]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_46 : (row5_46.zip hint5_46).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_47 : List (List ℕ) := [
[770],
[0,1032,1304,1034,444,936],
[1220],
[936,856,778,1272,0,776,1160],
[420,500,536],
[0,728,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[664,596],
[],
[496,444]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_47 : (row5_47.zip hint5_47).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_48 : List (List ℕ) := [
[328,1344,360,900,140,428],
[936,1114,818,778,1272,0,776,1160],
[],
[240,756,1092,702,928,226,472,378,86],
[0,1260,392,288,1032,1304,1034,444,936],
[0,992,1032,1304,1034,444,936],
[0,784,786,100,1032,1304,1034,444,936],
[1032,238,646,546,864,480,778,0],
[],
[936,778,1272,0,776,1160]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_48 : (row5_48.zip hint5_48).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_49 : List (List ℕ) := [
[0],
[],
[],
[956],
[0,1204,1032,646,1304,796,1034,644,444,936,1116,1064],
[0,944,356,1032,1304,1034,444,936],
[1057,617,1077,560,812,272,273,312,573,604,437,476,452],
[456,133],
[554],
[0,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_49 : (row5_49.zip hint5_49).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_50 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[358,0,1062,1032,334,1304,78,1034,464,444,1178,936],
[1304],
[672],
[0,904,620,1032,1304,1034,444,936],
[444,294,292,1372,480,1348,482,0,1160],
[0,266,264,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[444,1380,480,1348,482,0,1160],
[444]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_50 : (row5_50.zip hint5_50).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_51 : List (List ℕ) := [
[508],
[1032,474,546,864,480,778,0],
[],
[712,492,493,1224],
[338],
[636,133],
[444,1348,480,22,482,20,0,1304,1160,28],
[0,844,1032,1304,1034,444,936],
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
[936,1176,364,940,1178,778,1272,0,776,1160],
[242,1094,758,524,474,224,930,376,84],
[344],
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[712,117,1076,561,116,1077,560,1364,1165,1164,420,1016,1004,853,852],
[658,1266,520,521,1036,1388,1180,278,279]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_52 : (row5_52.zip hint5_52).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_53 : List (List ℕ) := [
[308,284,956,286,1332,892],
[1344,1301],
[936,44,778,1272,0,776,1160],
[692],
[244,1144],
[912,368,600],
[330,282],
[516,932,934,688,844,270,268,1152,364],
[0,1032,1304,1034,444,936],
[0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_53 : (row5_53.zip hint5_53).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_54 : List (List ℕ) := [
[12],
[16],
[0],
[0,948,1032,1304,1034,444,936],
[948,306,304,1280,1320,988,990,1140,1360],
[1308],
[936,410,44,408,778,1272,0,776,1160],
[152,1074],
[400,1340,1002,160,1224],
[0,600,912,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_54 : (row5_54.zip hint5_54).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_55 : List (List ℕ) := [
[125],
[0,1032,1304,1034,444,936],
[640,668,720],
[696,62,210,316,580,166],
[605,980,604,1196],
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[1304,226,546,544,1348,1272,0],
[656,792],
[0,394,1216,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_55 : (row5_55.zip hint5_55).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_56 : List (List ℕ) := [
[],
[444,324,260,480,1348,482,0,1160],
[1304,546,544,1348,1272,0],
[948,306,304,1280,1320,988,990,1140,1360],
[1248],
[0,1002,1340,1000,1342,1032,1304,1034,444,936],
[],
[1304],
[1268],
[0,1340,372,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_56 : (row5_56.zip hint5_56).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_57 : List (List ℕ) := [
[1304,546,544,1348,1272,0],
[1304,1084,546,544,1348,1272,0],
[936,624,778,1272,0,776,1160],
[92,54,1144],
[1296],
[736],
[0],
[1304,207,205,40,546,544,1348,1272,0],
[1288,318],
[0,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_57 : (row5_57.zip hint5_57).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_58 : List (List ℕ) := [
[],
[720],
[1160,534,28,444,532,936],
[1304,1352,546,544,1348,1272,0],
[1304,336,546,544,1348,1272,0],
[0,1032,1304,1034,444,936],
[0],
[142],
[516,932,934,688,844,270,268,1152,364],
[0,868,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_58 : (row5_58.zip hint5_58).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_59 : List (List ℕ) := [
[1304,1194,1192,1384,546,544,1348,1272,0],
[444,672,480,1348,482,0,1160],
[],
[133,488,584,490,248,74,977,72,528,612],
[433,0],
[1034,1308,864,544,482,0,776],
[876],
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[308,284,956,286,1332,892]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_59 : (row5_59.zip hint5_59).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_60 : List (List ℕ) := [
[573,1128],
[444,582,480,1348,482,0,1160],
[0,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[260],
[],
[444,716,718,1380,480,1348,482,0,1160],
[0,444,1032,480,1304,1348,1034,482,936,1160],
[620,822,820,144,1100,1102,632,1284,920,634,1244],
[]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_60 : (row5_60.zip hint5_60).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_61 : List (List ℕ) := [
[328,513,1344,360,900,140,428],
[],
[900,497],
[456],
[704],
[],
[868],
[308,284,956,286,1332,892],
[0,1204,1032,1304,1034,444,936],
[0,896,1108,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_61 : (row5_61.zip hint5_61).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_62 : List (List ℕ) := [
[204],
[444,480,1348,482,0,1160],
[658,710,520,521,1036,1388,1180,278,279],
[356],
[416,1228,748,497,1268,1368],
[864],
[1388,1278],
[0],
[1304,546,544,1348,1272,0],
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
[444,480,1348,482,0,1160],
[776,1034,1236,864,404,544,532,482,936,0],
[1184,208],
[1304,1120,546,544,1348,1272,0],
[636],
[944]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_63 : (row5_63.zip hint5_63).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_64 : List (List ℕ) := [
[0,1224,1340,794,620,1032,1304,1034,444,936],
[240,756,1092,1028,928,226,472,378,86],
[584],
[1096,444],
[444,156,158,848,1140,480,1348,482,0,1160],
[1032,62,546,864,480,778,0],
[1034,864,544,482,0,776],
[396],
[0,696,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_64 : (row5_64.zip hint5_64).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_65 : List (List ℕ) := [
[620,0,822,820,1364,1100,1102,632,1032,1284,1304,920,634,1034,444,1244,936],
[360,187],
[936,200,202,1156,778,1272,0,776,1160],
[0,1032,1304,1034,444,936],
[0,12,14,16,1032,1304,1034,444,936],
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
[0,356,516,358,248,1032,1304,1034,444,936],
[400,620,794,792],
[1034,1124,864,544,482,0,776],
[824],
[0,600,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[0],
[248,908,133,369,1170,68,388,1168,1188],
[720,908,916,918,1280,882,1384,880,744,1156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_66 : (row5_66.zip hint5_66).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_67 : List (List ℕ) := [
[416,1228,748,497,1268,1368],
[],
[1034,864,544,482,0,776],
[832,600],
[],
[444,466,464,1188,480,1348,482,0,1160],
[936,0,778,1032,1272,1304,776,1034,1160,444],
[0,210,1032,1304,1034,444,936],
[444,480,1348,482,0,1160],
[0,1088,1220,1032,1304,1034,444,936]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_67 : (row5_67.zip hint5_67).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_68 : List (List ℕ) := [
[80,1034],
[309,308,1204],
[600,506,41,504,1173,441],
[248,1376,32],
[1034,864,544,482,0,776],
[1304,546,544,1348,1272,0],
[0,930,1032,1304,1034,444,936],
[0,1360,1032,1304,1034,444,936],
[0,468,64,1032,1304,1034,444,936],
[1304,546,544,1348,1272,0]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_68 : (row5_68.zip hint5_68).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_69 : List (List ℕ) := [
[0,720,640,1032,1304,1034,444,936],
[0,1150,966,1144,836,1032,1304,1034,444,936],
[1016,572,573,220],
[1144,160,162,804,58,56,860,1128,862,1024,1048],
[0,256,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[0,394,392,720,948,1032,1304,1034,444,936],
[0,1032,1304,1034,444,936],
[564],
[0,740,742,1032,1304,1034,444,936]]
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
[328,1344,360,900,140,428],
[0,48,50,1032,1304,1034,444,936],
[133,74,977,72,528,612],
[],
[0,1144,160,162,58,56,424,1032,860,1304,1128,1034,862,444,1024,936,1048]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk5_70 : (row5_70.zip hint5_70).all (fun p => verifyS width topMask 4 taus p.1 row4 p.2) = true := by
  decide +kernel

def hint5_71 : List (List ℕ) := [
[0,1032,1304,1034,444,936],
[0,32,248,1032,1304,1034,444,936]]
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
[109,1678,2612,1728,1494,1772,914,1716,167,1587,1558,856,1492,1692,1012,1525,2784,912,165,1192,1556,688,1129,2356,615,2594,1184,2016,1631,2278,1482,2592,2644,725,819,2172,2276,1676,1108,1480,2205,1043,600,658,391,299,900,581,1144,656,389,1561,2428,1252,1069,521,154,393,75,2704],
[2592,109,2612,1728,1494,1772,304,914,167,1558,1492,2212,1084,881,1692,1012,2784,912,165,1556,1282,1639,1936,688,2356,2594,2016,92,2278,1678,1482,2644,725,2172,2276,1676,1186,1480,1746,302,817,1204,2205,600,658,2580,391,900,1148,581,656,2584,389,1614,1552,2428,1252,521,982,393,2704],
[2156,41,109,108,958,256,956,788,2048,2049],
[2156,2628,1576,864,511,109,108,958,256,956,788,2048,2049],
[2049,645,1970,429,482,1592,2156,480,1160,1856],
[2156,2084,2086,2344,1657,109,108,958,256,956,788,2048,2049],
[1592,256,1432,2268,2437,996,581,580,118,526,116,524,1116,740,2088,1593,2049,2156],
[2156,2520,1177,1176,2476,109,108,958,256,956,788,2048,2049],
[521,109,2612,1728,1494,1772,914,934,167,1558,1492,1692,925,1012,2784,912,932,165,1556,965,688,2356,644,2304,733,2594,2016,2278,1217,1678,1482,2592,2644,844,725,2172,2276,1219,1676,1480,1796,2205,600,658,1564,391,900,997,581,656,1566,389,2428,681,1252,1380,393,2704],
[1076,2132,548,1582,1533,1532,2526,660,1608,1164,1165,1362]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_0 : (row6_0.zip hint6_0).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_1 : List (List ℕ) := [
[1864,756,2116,2488,88,700,701,418,2504,1828,2188,398,399],
[2156,96,109,108,958,256,956,788,2048,2049],
[2156,1644,109,108,1679,958,256,956,788,2048,2049],
[616,1451,2144,50,1208,1631],
[788,460,1252,1624,1253,266,740,264,1161,2156,1160],
[958,1840,391,390,526,2500,266,483,482,2156],
[392,2704,108,1956,2612,668,1728,1544,1494,2288,786,720,1772,84,914,679,166,334,1558,1892,920,1546,1492,604,1692,1845,1013,2608,2784,2290,784,2128,2780,86,912,677,164,332,1556,1680,689,972,2356,980,2594,188,1316,1124,2016,1924,2278,74,1679,414,1482,440,1996,982,2592,2092,2644,1776,724,1352,2172,190,1318,2184,2024,1052,428,1761,1926,2276,72,1677,412,1480,860,2204,1696,600,468,658,730,2542,390,596,900,1237,1600,580,470,728,2540,656,388,1292,2328,1428,2428,1253,1381,520],
[2049,645,429,1768,482,1592,2156,480,1160,1856],
[2156,2664,109,108,958,256,956,788,2048,2049],
[2156,1864,912,109,108,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_1 : (row6_1.zip hint6_1).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_2 : List (List ℕ) := [
[956,1823,1155,916,389,388,2500,524,264,481,2156,480],
[2156,924,109,108,958,256,956,788,2048,2049],
[2156,928,109,108,958,256,956,788,2048,2049],
[2048,644,1166,1164,2264,428,483,1593,481,1161,2156,1856],
[2156,958,109,108,658,391,390,256,526,956,2500,788,266,2048,483,2049,482],
[958,418,2040,1244,391,390,526,2500,266,483,482,2156],
[2156,2612,109,108,958,256,956,788,2048,2049],
[2156,2160,2162,2164,2616,109,108,958,256,956,788,2048,2049],
[2156,2640,109,108,1109,958,256,956,788,2048,2049],
[256,1072,2504,1114,581,580,526,524,740,1593,1592,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_2 : (row6_2.zip hint6_2).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_3 : List (List ℕ) := [
[788,21,1916,2449,836,1252,1253,266,740,264,1161,2156,1160],
[108,1482,2612,1728,1494,1772,914,1756,166,1558,2098,2564,1932,1492,1692,1013,2784,2236,912,164,1556,2764,689,2356,1400,2594,1744,2016,674,2278,1679,2592,2644,724,2172,1206,2276,1677,1480,1272,752,2204,600,1410,658,390,1792,900,580,2228,656,388,192,2428,1253,1278,520,392,2704,414,1348],
[2156,1388,1390,2305,1797,109,108,958,256,956,788,2048,2049],
[2049,645,429,482,1592,2156,480,1160,1856],
[958,526,391,390,852,1250,1251,2500,2296,266,796,483,119,482,118,2156,256],
[1864,756,1700,2488,622,700,701,418,2504,1828,2188,398,399],
[2156,52,109,108,1337,958,256,956,788,2048,2049],
[2156,429,109,108,1760,958,2242,256,2437,956,2240,788,497,2048,820,2049,2304],
[2048,1593,644,1433,428,2436,483,119,481,117,1161,1117,2156,256,1856,2088],
[167,108,2612,1728,509,1268,1494,1772,914,166,1558,1492,1692,1013,2784,912,164,1556,689,2356,196,422,566,1422,748,614,2594,2016,2278,1679,1482,2592,2644,724,2172,2276,1677,1480,2204,600,1339,427,658,390,273,900,580,917,656,388,839,2428,1253,520,678,392,2704]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_3 : (row6_3.zip hint6_3).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_4 : List (List ℕ) := [
[688,108,2612,1728,1268,1656,1270,1494,1772,914,166,1558,1492,1692,1013,2784,912,164,1556,689,2356,142,1424,140,1233,2594,2016,2278,1679,1482,2592,2644,724,2172,2276,1677,1480,2204,600,516,366,658,390,829,900,580,364,656,388,504,2428,1253,520,1681,392,2704],
[2644,108,2612,1728,1494,1772,914,2006,792,158,166,1558,1492,1692,2352,2148,1140,1013,2784,912,2004,794,156,164,1556,689,2356,2661,1596,2672,488,2594,2016,2278,300,1679,1482,2592,724,2172,2276,302,1677,1480,2204,2141,600,2208,457,2796,658,1190,390,900,848,580,656,1188,388,2428,2700,1253,1056,520,2092,392,2704],
[2156,109,108,317,958,256,956,788,2048,2049],
[108,2172,2612,1728,1494,1772,914,166,1558,1470,1492,1692,1013,2784,2176,1873,2252,912,164,1556,1468,689,2356,1048,2594,2016,2278,1679,1482,1206,2592,2644,724,2276,1677,1480,1204,2204,600,2796,658,390,354,900,580,2740,656,388,352,2428,1253,104,520,392,2704,1352,2748],
[2156,109,108,1168,958,256,956,788,2048,2049],
[256,581,580,1784,526,524,740,1593,1592,2156],
[788,1648,2416,2244,1252,1253,266,740,264,1161,2156,1160],
[464,1039,2568,1037,780,2456,228,2372,2828,2696,214,405,212,716,36],
[958,391,390,186,526,2500,266,483,482,2156],
[956,446,1712,212,1264,213,1188,389,388,2500,524,264,481,2156,480]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_4 : (row6_4.zip hint6_4).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_5 : List (List ℕ) := [
[956,370,1478,364,389,388,2500,524,264,481,2156,480],
[2156,2052,698,2234,1156,2560,109,108,958,256,956,788,2048,2049],
[956,416,284,389,388,2500,524,264,481,2156,480],
[2156,403,109,108,958,256,956,788,2048,2049],
[2156,109,108,1728,958,256,956,788,2048,2049],
[958,1457,1456,1732,391,390,526,2500,266,483,482,2156],
[2156,1092,2594,109,108,958,256,956,788,2048,2049],
[2156,750,109,108,958,256,956,788,2048,2049],
[788,1606,2406,1252,1253,266,740,264,1161,2156,1160],
[956,2792,1404,389,388,2500,524,264,481,2156,480]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_5 : (row6_5.zip hint6_5).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_6 : List (List ℕ) := [
[2049,1485,645,1512,429,482,1592,2156,480,1160,1856],
[256,581,580,2280,1784,1736,892,273,272,30,1334,894,275,274,28,1332,829,828,2548,2332,1464,1653,1652,1620,12,1112,1144,1145,2228,2338,1114,1146,1147,2230,2336,1781,1780,968,1120,2512,2513,2284,1082,526,1250,1251,1080,524,1248,1249,1472,740,381,380,1593,997,1592,996,1236,1237,1600,2156,109,108,900],
[990,2624,1826,294,310,953,648,1688,1308,2480,1668,202,2371,586],
[788,1848,1032,1252,1253,266,740,264,1161,2156,1160],
[109,656,389,2612,1842,1728,184,1494,112,1772,1734,914,284,167,917,2664,144,1558,2046,1492,2736,1692,1674,1012,947,1356,2380,2784,120,912,454,165,425,1556,1852,688,364,2412,1404,2356,1460,1904,2689,168,432,2594,2582,2016,68,2278,1246,1678,1561,2840,244,1482,192,2592,2584,2644,1188,725,842,2028,960,2172,352,2276,592,1676,297,1480,1794,2205,1229,24,340,600,1088,316,905,1376,2652,658,1740,391,1742,1572,900,854,581,1080,1248,2428,1252,540,1506,813,521,1566,393,470,2704,729,2540],
[336,2060,2468,652,2120,688,109,1233,368,1196,370,2036,2444,760],
[2156,2800,2804,2508,1269,109,108,958,256,956,788,2048,2049],
[2156,109,1340,108,958,256,956,788,2048,2049],
[788,2449,1252,1253,1070,266,740,264,1161,2156,1160],
[2356,109,2612,1728,1494,472,1772,914,167,1558,1312,1492,1692,1012,2732,2784,474,688,912,165,1556,2594,1240,2016,2278,1678,1482,2844,2592,2644,725,2172,1242,1232,2276,1676,1480,2464,2205,948,1685,1520,600,658,1462,391,900,2548,581,2776,1460,656,389,2712,2428,1252,521,972,393,2704]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_6 : (row6_6.zip hint6_6).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_7 : List (List ℕ) := [
[633,308,310,76,1212,2684,608,1967,1965,460,1132,936],
[2156,2002,109,108,958,256,956,788,2048,2049],
[788,2036,504,1252,1253,266,740,264,1161,2156,1160],
[788,1490,1488,716,717,2700,1252,1253,266,740,264,1161,2156,1160],
[2049,2156,645,2305,429,520,109,108,482,958,1592,256,480,956,1160,788,1856,2048],
[788,1604,1554,1252,1253,266,740,264,1161,2156,1160],
[1556,108,2612,1728,1494,1772,914,166,1558,1106,1492,1692,1013,2784,474,164,912,689,2356,2594,744,160,32,2016,2278,1679,1482,984,2592,2644,724,2172,56,612,2276,859,1677,2096,2566,1934,1480,2204,600,658,2044,390,900,28,580,2744,1852,656,388,1172,2428,1253,520,332,392,2704],
[256,2768,288,12,581,580,526,524,740,1593,1592,2156],
[2156,50,48,2516,2144,2146,1285,109,108,958,256,956,788,2048,2049],
[2156,2492,2636,2494,464,465,2644,109,108,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_7 : (row6_7.zip hint6_7).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_8 : List (List ℕ) := [
[956,1311,315,361,2300,1964,946,389,388,2500,524,264,481,2156,480],
[633,308,310,76,1212,2420,608,1967,1965,460,1132,936],
[464,2156,2456,356,228,172,2828,2588,2660,109,108,2696,214,958,405,256,212,956,716,788,2048,36,2049],
[2156,1372,60,62,1327,1325,1985,109,1837,108,1225,1500,1224,958,1457,256,2401,956,1459,788,1061,2048,1417,2049,1008],
[956,1155,389,388,1560,2500,524,264,481,2156,480],
[2156,1028,1076,1497,512,109,2755,108,958,256,956,788,2048,2049],
[1492,108,2612,1728,2476,1494,1772,914,166,1558,486,510,1106,1692,1013,2784,8,912,164,1556,689,2356,1530,2594,2016,2278,1679,1482,124,82,2408,2212,1084,880,2592,2644,724,2172,2276,1677,1480,2204,600,658,114,390,2708,1066,900,580,2736,656,388,2406,2428,1253,520,1546,392,2704],
[2278,109,2612,1728,1494,1772,914,620,90,702,167,1558,1492,1692,98,1012,2784,912,128,64,1542,165,1556,688,2356,46,2388,2594,2016,1678,1482,2592,2644,300,725,2172,2276,1384,1676,1480,2205,600,1043,1410,658,594,391,900,1112,581,656,1246,389,2428,1436,1252,250,521,1924,393,2704],
[1321,2468,652,2396,2256,1476,1972,1478,1768,1752],
[2156,788,109,2428,108,1252,1253,958,266,256,740,956,264,2048,1161,2049,1160]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_8 : (row6_8.zip hint6_8).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_9 : List (List ℕ) := [
[1156,942,940,1368,1451,1450,1449,1448,2432,1568,1569,268,288,1200,270,1513,1512],
[2156,554,552,372,109,2824,108,958,256,956,788,2048,2049],
[2048,644,396,428,483,1593,481,1161,2156,1856],
[2156,1025,109,108,958,256,956,788,2048,2049],
[956,2720,976,2689,389,388,2500,524,264,481,2156,480],
[804,108,2612,1728,1494,1772,914,166,1558,1492,1692,2616,1013,2784,912,164,1556,689,2356,2594,2016,2278,530,1580,1534,1679,1482,2592,2644,2104,724,2172,2276,528,1582,1532,1677,1480,1976,1704,1396,2204,600,658,1948,390,900,1464,580,656,1950,388,2428,1812,1253,1940,520,1832,392,2704],
[2049,1877,645,399,429,482,1592,2156,480,1160,1856],
[2156,2188,4,109,248,108,958,256,956,788,2048,2049],
[788,1252,1253,1444,266,740,264,1161,2156,1160],
[956,2384,389,244,388,2500,524,264,481,2156,480]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_9 : (row6_9.zip hint6_9).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_10 : List (List ℕ) := [
[2156,109,108,2172,958,256,956,788,2048,2049],
[2156,226,224,2324,877,876,765,764,2784,109,108,958,256,956,788,2048,2049],
[256,1749,581,580,1147,526,524,740,1593,1592,2156],
[1012,109,2612,1728,509,511,1656,1494,1772,914,167,1558,1492,1692,2784,912,165,1556,688,2356,955,910,650,953,908,648,493,1289,2728,2594,2016,2278,1678,1482,2592,2644,2684,725,2172,2276,1676,1480,2205,600,1944,945,658,391,2309,900,581,947,656,389,2020,2428,1252,521,1844,393,2704],
[480,956,532,132,2240,1567,389,388,1537,2500,116,524,278,264,538,481,2049,2156],
[2156,1384,109,108,958,256,956,788,2048,2049],
[502,500,1372,1208],
[2156,336,2060,652,2120,2396,109,108,1233,958,368,256,1196,956,370,788,2036,2048,2444,2049,760],
[2048,644,1764,428,483,1593,481,1161,2156,1856],
[788,1346,1252,1253,266,740,264,1161,2156,1160]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_10 : (row6_10.zip hint6_10).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_11 : List (List ℕ) := [
[2156,568,573,572,92,109,108,958,256,956,788,2048,2049],
[2156,576,109,108,2068,958,256,956,788,2048,2049],
[956,884,557,424,389,388,2500,524,264,481,2156,480],
[2156,633,109,725,108,958,256,956,788,2048,2049],
[956,2584,389,388,2500,524,264,481,2156,480],
[2156,1642,1640,1392,109,108,456,958,256,956,788,2048,2049],
[256,2056,1334,581,580,526,524,740,1593,1592,2156],
[2156,109,108,24,958,256,956,788,2048,2049],
[1321,2468,2120,2396,376,2256,1476,1972,1478,1768,1752],
[2049,480,645,532,429,2240,482,1537,1592,116,2156,956,1160,278,1856,538]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_11 : (row6_11.zip hint6_11).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_12 : List (List ℕ) := [
[2048,644,1045,428,483,1593,481,1161,2156,1856],
[1718],
[1156,2156,942,940,2112,1451,1450,1449,1448,2600,1568,1569,109,108,268,958,288,256,1200,270,956,788,1513,2048,1512,2049],
[2049,1160,645,345,429,497,482,276,1592,1116,2156,788,480,278,1856,1304],
[256,1973,581,580,1780,526,524,740,1593,1592,2156],
[210,436,988,1184],
[256,448,581,580,1120,526,524,740,1593,1592,2156],
[956,389,388,296,2500,524,264,481,2156,480],
[876,1988,292,294,2692,1212,2420,1012,109,2221,362,2620,360,2080,409,1952],
[256,1148,581,580,526,524,740,1593,1592,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_12 : (row6_12.zip hint6_12).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_13 : List (List ℕ) := [
[232,698,1096,60,61,2052,2192],
[914,108,2612,1728,484,2716,1269,472,10,1494,2192,1772,166,1558,1492,1692,1013,2784,2648,912,164,1556,689,2356,1980,2560,1341,2788,2594,2016,620,90,703,2278,1717,1679,1756,1482,2592,2644,724,2172,2276,1677,1480,2204,600,1900,452,658,390,892,900,580,284,656,388,1344,2428,1253,520,84,392,2704],
[2049,645,2445,429,482,1592,2156,480,1160,1856],
[2156,356,808,2196,109,108,958,256,956,788,2048,2049],
[2048,644,1009,1484,428,483,1593,481,1161,2156,1856],
[2156,1321,109,108,2205,958,256,956,788,2048,2049],
[2156,109,108,708,958,256,956,788,2048,2049],
[1856,2049,1381,1380,393,645,820,429,536,482,2088,1592,2048,2156,538,480,1304,1160],
[2156,16,1904,109,108,958,256,956,788,2048,2049],
[2156,1884,109,108,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_13 : (row6_13.zip hint6_13).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_14 : List (List ℕ) := [
[236,237,2812,2724],
[256,2604,2632,1748,275,581,580,526,524,740,1593,1592,2156],
[2049,645,1912,429,482,1592,2156,480,1160,1856],
[2156,216,737,736,484,109,108,958,256,956,788,2048,2049],
[2156,2256,109,108,516,958,256,956,788,2048,2049],
[256,2482,2480,320,2620,2309,581,580,526,524,740,1593,1592,2156],
[2049,520,109,2612,1728,1494,935,1772,914,167,1558,924,1492,1692,1012,2784,933,964,645,732,912,165,1556,688,2356,2594,1216,2016,2278,1678,1482,845,2592,2644,725,2172,1218,1797,429,1760,2276,1676,1480,2205,600,658,482,1565,391,900,1592,996,581,2156,108,480,1567,656,389,1160,680,2428,1252,1856,521,1381,393,2704],
[109,1728,2612,1494,1772,914,167,1558,1492,1692,1012,2784,912,165,1556,688,2356,2594,2016,2278,1678,1482,2592,2644,725,2172,2276,1676,1480,2205,600,658,391,186,900,581,1784,656,389,184,2428,1252,1444,521,393,2704,668],
[2156,1908,2492,692,126,109,108,958,256,956,788,2048,2049],
[2156,109,2028,108,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_14 : (row6_14.zip hint6_14).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_15 : List (List ℕ) := [
[256,2504,894,581,580,526,524,740,1593,1592,2156],
[2156,384,109,108,1041,958,256,956,788,2048,2049],
[2492,2156,2006,159,158,109,108,772,958,1364,256,446,956,1490,788,994,2048,995,2049],
[2048,644,428,483,1593,481,1161,2156,1856],
[956,389,388,1842,184,112,284,917,144,916,2046,1674,947,2380,946,120,364,1404,365,1460,2689,1950,2688,432,2582,1246,1561,244,1560,192,1188,842,960,843,352,1229,340,1228,1088,905,904,2652,1740,2500,1572,1573,854,524,1248,1249,1506,264,813,812,481,1566,2156,109,656,108,480,1567,729,728,2540],
[2156,48,1372,2292,618,502,1194,109,108,958,256,956,788,2048,2049],
[958,266,391,1504,390,815,814,526,796,2500,2528,483,277,482,276,2156,788],
[2156,337,1320,689,109,108,958,256,956,788,2048,2049],
[788,1992,1438,1252,1253,266,740,264,1161,2156,1160],
[109,1679,2612,1728,1494,1772,914,1717,167,1558,255,857,1492,1692,1012,2784,1524,912,165,1556,1193,688,2356,1128,2752,515,614,2594,1185,2016,1630,2278,1678,1722,1482,2592,2644,725,2172,818,2276,1676,1480,1109,2205,600,1042,658,391,298,900,581,1145,656,389,1560,2428,1252,1068,521,393,2704,74,155]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_15 : (row6_15.zip hint6_15).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_16 : List (List ℕ) := [
[788,2073,1252,1253,2537,266,740,264,1161,2156,1160],
[256,1196,1972,829,581,580,526,524,740,1593,1592,2156],
[2636,686,684,2568,2569,2148,1141,1140,576,1714,1712,220,1045,1044],
[2156,1131,109,108,958,256,956,788,2048,2049],
[1373,61,63,2136,349,1326,1324,2772,1225,1501,1456,2400,1458,1060,1009,1416],
[2049,645,429,482,1592,2156,480,1160,1856],
[2156,1830,109,108,1900,958,256,956,788,2048,2049],
[2156,220,178,176,205,109,1056,108,204,958,256,956,788,2048,2049],
[2156,1078,109,530,108,1535,1534,958,256,662,956,2524,788,1610,2048,1166,1360,2049,1167],
[2156,109,2104,108,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_16 : (row6_16.zip hint6_16).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_17 : List (List ℕ) := [
[256,2008,581,1652,580,664,526,524,740,1593,1592,2156],
[2156,964,109,108,958,256,956,788,2048,2049],
[956,2180,389,960,388,2500,524,264,481,2156,480],
[109,900,581,2612,2280,1728,1784,1494,1064,1772,1736,914,892,167,273,1558,30,2110,1334,1492,1066,1692,2756,1012,2309,2784,2360,912,894,165,275,1556,28,2108,1332,688,829,2356,2548,1632,2332,1804,1653,2340,1620,2594,1150,2016,12,2278,1112,1678,1144,1482,2228,1016,2338,2592,1148,2644,848,725,2248,2172,2740,2276,1114,1676,1146,1480,2230,1018,2336,2205,1781,600,968,1168,1120,240,2512,872,2284,658,1082,391,852,1250,656,389,854,1080,1248,2428,1252,2064,1472,381,521,997,393,2704,596,1236,1600],
[1692,109,2612,1728,484,486,1656,1312,1494,1772,914,167,1558,1492,1012,2784,912,165,1556,688,2356,1022,1020,709,704,2594,2016,2278,1678,1482,2592,2352,2148,1141,2644,725,2172,2276,1676,1480,2205,600,2068,1672,658,391,2756,900,581,1674,656,389,2484,2428,1252,521,604,393,2704],
[2612,108,1728,1494,1772,914,166,1558,1492,1692,1013,2784,912,164,1556,689,2356,2594,2016,2278,1679,1482,2592,2644,724,2172,2276,1677,1480,2204,600,1840,658,390,2280,900,580,1842,656,388,1548,2428,1253,520,1956,392,2704],
[2156,1632,109,108,958,256,956,788,2048,2049],
[2156,989,148,2376,437,1636,109,108,958,256,956,788,2048,2049],
[109,725,2612,1728,1494,1772,914,167,403,1558,1492,1692,1012,2684,2784,1660,912,165,401,1556,688,41,2356,2220,2594,2016,2278,1678,819,1482,2592,2644,2172,2276,1676,817,1480,2205,456,600,658,391,840,900,581,2248,656,389,842,2428,1252,1624,521,329,393,1777,2704],
[2156,109,108,80,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_17 : (row6_17.zip hint6_17).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_18 : List (List ℕ) := [
[2049,1765,645,429,482,1592,2156,480,1160,1856],
[232,1156,2234,2232,2648],
[2532,942,1368,2112,348,1327,1985,349,1326,1984,1296,180,181,1896,2768,2216,1648,1484,1485],
[956,2524,802,1950,389,388,2500,524,264,481,2156,480],
[788,1328,1330,2572,2072,896,1252,1253,266,740,264,1161,2156,1160],
[2156,256,109,108,900,581,580,958,526,956,524,788,740,2048,1593,2049,1592],
[956,977,389,388,904,2500,524,264,481,2156,480],
[1092,2214,883,882,2544,2312,1508,1604,1764,1765],
[2156,990,908,109,108,648,1688,958,1308,256,2480,956,1668,788,202,2048,2371,2049,586],
[2156,933,109,108,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_18 : (row6_18.zip hint6_18).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_19 : List (List ℕ) := [
[2156,1896,109,108,1220,958,256,956,788,2048,2049],
[788,200,202,2076,2080,460,2020,1252,1253,266,740,264,1161,2156,1160],
[2156,1096,698,1098,696,2260,109,108,958,256,956,788,2048,2049],
[2156,2110,109,108,958,256,956,788,2048,2049],
[2156,356,2552,464,2456,1289,109,108,2728,712,958,312,256,320,956,314,788,1440,2048,889,2049,2832],
[956,1508,2582,389,388,2500,524,264,481,2156,480],
[2156,1372,1373,2532,1772,109,108,958,256,956,788,2048,2049],
[109,724,2612,1728,1494,1772,914,167,1558,402,1492,1692,1012,2784,764,1661,912,165,1556,400,688,2356,40,324,876,2221,2594,2016,2278,1678,1482,818,2592,2644,725,2172,2276,1676,1480,816,2205,600,457,658,391,841,900,581,2249,656,389,843,2428,1252,1625,521,393,2704,1776,328],
[956,2500,389,388,1740,1572,1573,524,2296,264,2528,481,1536,2156,958,480,1537],
[2156,2656,476,477,300,109,108,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_19 : (row6_19.zip hint6_19).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_20 : List (List ℕ) := [
[2428,108,1253,2612,1548,1728,1444,1494,2404,1772,1412,914,1344,2002,1034,166,838,1558,1174,1492,2406,1692,2484,1884,2364,1013,2021,2784,2576,912,1346,2000,1032,164,836,1556,1172,689,505,2356,2712,2824,897,1664,2424,2594,1554,2016,2244,2278,1436,2154,624,1679,1068,1482,1278,2592,1552,2644,2700,2316,1816,724,1625,2172,104,2276,1438,2152,626,1677,1070,1480,1276,2204,0,600,628,2596,2537,2224,2032,658,542,1504,390,814,900,2064,1472,580,380,656,540,1506,388,812,520,680,1292,392,2704,2328,1428],
[164,108,2612,1728,1494,1772,914,166,1558,510,1492,1692,1013,2784,1271,912,1556,689,2356,2594,565,421,1708,2016,2278,1679,1482,199,2592,2644,724,2172,751,2276,1584,1677,1480,2204,600,658,918,390,900,274,580,1336,424,656,388,836,2428,1253,520,677,392,2704],
[2156,2544,109,108,2710,958,256,956,788,2048,2049],
[808,2588,356,2140],
[958,1476,391,390,1231,526,2500,266,483,482,2156],
[108,2204,2612,1728,1494,1772,914,166,1558,1026,1492,1692,1013,2784,2197,912,164,1556,1024,689,377,2356,2465,1233,2594,2016,2278,1679,1482,1042,2592,2644,2141,724,2172,457,2276,1677,1480,1040,600,658,390,1230,900,580,1780,656,388,1228,2428,1253,0,520,392,2704,860,1589],
[788,2012,2364,1252,1253,266,740,264,1161,2156,1160],
[2156,109,108,2152,958,256,956,788,2048,2049],
[2494,2100,684,1037,1036,794,157,156,444,1366,774,1488,992,993],
[2156,2216,2816,109,560,108,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_20 : (row6_20.zip hint6_20).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_21 : List (List ℕ) := [
[2049,645,1788,100,429,482,1592,2156,480,1160,1856],
[2156,513,2680,2496,776,109,108,612,958,1820,256,2632,956,556,788,1917,2048,101,2049,2272],
[256,448,2332,581,580,526,524,740,1593,1592,2156],
[2156,109,108,600,958,256,956,788,2048,2049],
[256,2058,581,580,2336,526,524,740,1593,1592,2156],
[2156,1868,109,108,958,256,956,788,2048,2049],
[256,526,581,580,1082,1250,1251,524,2296,740,796,1593,119,1592,118,2156,958],
[788,1252,1253,0,266,740,264,1161,2156,1160],
[2156,1280,109,108,958,256,956,788,2048,2049],
[1772,108,2612,1728,2476,2716,1494,2192,914,166,1558,1492,1692,1013,2784,2194,912,164,1556,689,2356,1868,2260,1836,2772,1224,2836,2594,1296,1298,181,2016,2278,1679,1482,2592,2644,724,2172,2276,1677,1480,2204,600,1220,1732,658,390,1736,900,580,1734,656,388,1412,2428,1253,520,720,392,2704]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_21 : (row6_21.zip hint6_21).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_22 : List (List ℕ) := [
[2156,109,108,818,958,256,956,788,2048,2049],
[256,581,2248,580,526,524,740,1593,1592,2156],
[2049,645,2350,429,482,1592,2156,480,1160,1856],
[50,1180,1100,1920,2440,420,1709,1420,2124,2604,885,20,1789,768],
[2156,588,512,513,252,253,1556,109,108,958,256,956,788,2048,2049],
[2156,1078,1076,2812,804,109,108,958,256,956,788,2048,2049],
[956,1712,1674,389,388,2500,524,264,481,2156,480],
[2048,994,1045,992,544,37,644,428,483,1593,481,1161,2156,1856],
[2156,109,2840,108,958,256,956,788,2048,2049],
[256,1066,581,580,526,524,740,1593,1592,2156]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_22 : (row6_22.zip hint6_22).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_23 : List (List ℕ) := [
[2156,136,138,2200,877,325,109,108,958,256,956,788,2048,2049],
[2156,1094,1492,109,108,958,256,956,788,2048,2049],
[2156,2305,1218,109,108,958,256,956,788,2048,2049],
[2049,645,770,2348,429,482,1592,2156,480,1160,1856],
[956,2180,2380,389,388,2500,524,264,481,2156,480],
[464,2552,1988,2452,2060],
[1647,1100,2820,2440,1136,2496,776,1585,52,1152,1748,2448,2350,1808],
[2156,1022,109,108,958,256,956,788,2048,2049],
[2636,686,684,2568,2569,2352,1141,1140,576,1714,1712,220,1045,1044],
[2156,140,109,108,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_23 : (row6_23.zip hint6_23).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_24 : List (List ℕ) := [
[956,2384,144,389,388,2500,524,264,481,2156,480],
[956,1964,389,388,843,2500,524,264,481,2156,480],
[2156,989,991,357,877,632,1013,109,108,958,256,956,788,2048,2049],
[2156,51,512,1646,164,109,108,958,256,956,788,2048,2049],
[788,266,1252,1253,542,815,814,740,796,264,2528,1161,277,2156,958,1160,276],
[2156,2312,109,108,1612,958,256,956,788,2048,2049],
[1161,788,344,260,496,681,1252,1253,277,266,1117,740,279,264,2048,2156,1304,1160],
[2156,2808,44,109,108,958,256,956,788,2048,2049],
[2016,108,2612,1728,1494,1772,1296,1298,181,914,166,1558,1492,928,1692,1013,2784,912,164,1556,2432,2600,1569,1284,1452,689,2356,2594,2278,1679,1630,1482,674,2592,92,2644,724,2172,2276,1677,1628,1480,672,1384,1109,752,2204,600,658,70,390,900,12,580,656,68,388,560,2244,2428,1253,520,1124,392,2704],
[2156,109,108,1018,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_24 : (row6_24.zip hint6_24).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_25 : List (List ℕ) := [
[956,270,68,389,388,2500,524,264,481,2156,480],
[2049,645,1768,429,482,1592,2156,480,1160,1856],
[108,600,2612,1728,1494,1772,914,166,1558,2392,1492,1692,1013,2784,2760,912,164,1556,2394,689,2356,948,1684,1520,2594,2016,2278,1679,1482,1410,2592,2644,2208,724,2172,2796,2276,1677,1480,1408,2204,658,390,1090,900,580,968,656,388,1088,2428,1253,628,520,392,2704,1696,1300],
[2049,645,429,482,1592,2156,480,1160,1856],
[2156,1752,1588,109,108,958,256,956,788,2048,2049],
[256,1364,1366,405,404,848,581,580,526,524,740,1593,1592,2156],
[788,1610,1608,1812,1252,1253,266,740,264,1161,2156,1160],
[956,454,389,388,2500,524,264,481,2156,480],
[1496,1497,1076,1720],
[2784,109,2612,1728,1104,1106,1312,1012,1494,1772,914,167,1558,1492,1692,912,165,1556,688,2732,2356,638,826,1000,636,824,1002,2676,1004,1260,2220,2594,2016,2278,1678,1482,2592,2644,1660,725,2176,1872,2252,2172,2276,1676,1480,2205,600,1256,122,658,391,2360,900,581,120,656,389,2576,2428,1252,521,2608,393,2704]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_25 : (row6_25.zip hint6_25).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_26 : List (List ℕ) := [
[645,2049,2320,429,821,534,482,1432,1592,2305,2156,532,480,345,1160,1856],
[256,2401,2400,2768,1736,581,580,526,524,740,1593,1592,2156],
[2049,1968,645,429,482,1592,2156,480,1160,1856],
[2156,109,108,1482,958,256,956,788,2048,2049],
[2049,645,2460,429,482,1592,2156,480,1160,1856],
[2812,550,548,1704,1397,1396,800,1516,802,2264,2265,640],
[956,2736,389,388,2500,524,264,481,2156,480],
[256,665,581,580,2512,526,524,740,1593,1592,2156],
[256,2756,581,580,526,524,740,1593,1592,2156],
[2049,1802,1912,645,1800,429,482,1592,2156,480,1160,1856]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_26 : (row6_26.zip hint6_26).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_27 : List (List ℕ) := [
[2156,1356,109,108,958,256,956,788,2048,2049],
[393,392,2156,1956,668,1544,2288,720,84,678,679,1892,1546,604,1844,1845,2290,2128,86,676,677,1681,1680,1832,980,188,1124,1924,75,74,440,982,2092,1777,1776,190,2184,1053,429,1052,428,1926,73,72,861,860,2704,109,108,468,731,730,958,596,1236,1237,256,470,729,728,956,1292,2329,2328,788,1380,2048,1381,2049],
[2049,645,2368,2370,888,408,429,482,1592,2156,480,1160,1856],
[2156,109,2316,108,958,256,956,788,2048,2049],
[956,1880,592,389,388,2500,524,264,481,2156,480],
[2049,645,584,1860,586,2832,936,429,482,1592,2156,480,1160,1856],
[788,1850,1252,624,1253,266,740,264,1161,2156,1160],
[645,2305,732,520,108,821,428,534,134,1432,2268,532,132,345,261],
[2156,1724,1889,1888,2716,109,108,958,256,956,788,2048,2049],
[2156,306,109,108,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_27 : (row6_27.zip hint6_27).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_28 : List (List ℕ) := [
[1647,1100,2820,1920,1136,2680,776,52,1152,1748,2448,2350,1808],
[2156,198,109,108,958,256,956,788,2048,2049],
[2156,2532,1156,2016,109,108,958,256,956,788,2048,2049],
[689,108,2612,1728,1494,1269,1772,914,166,1558,1657,1492,1692,1013,2784,1271,912,164,1556,2356,2594,143,2016,2278,1679,1482,1425,2592,2644,724,2172,141,2276,1677,1480,377,2204,600,658,367,390,900,828,580,517,365,656,388,505,2428,1253,520,1680,392,2704],
[788,1548,1252,1253,266,740,264,1161,2156,1160],
[2305,2156,732,109,108,428,134,958,2268,256,132,956,261,788,2048,645,2049],
[256,662,660,1516,1464,581,580,526,524,740,1593,1592,2156],
[2156,2812,109,108,1976,1397,1396,958,800,256,1516,956,802,788,2048,2264,2049,2265,640],
[2156,2556,2492,1980,109,108,958,256,956,788,2048,2049],
[256,740,581,1472,580,381,380,526,796,524,798,1593,1117,1592,1116,2156,788]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_28 : (row6_28.zip hint6_28).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_29 : List (List ℕ) := [
[2048,644,428,483,1593,481,1161,2156,1856],
[788,1061,1060,1648,1412,1252,1253,266,740,264,1161,2156,1160],
[2156,2452,464,1424,109,108,958,256,956,788,2048,2049],
[956,1508,112,389,388,2500,524,264,481,2156,480],
[2156,1808,152,109,108,958,256,956,788,2048,2049],
[2156,2668,845,109,108,958,256,956,788,2048,2049],
[788,740,1252,1253,2064,381,380,266,796,264,798,1161,1117,2156,256,1160,1116],
[788,2484,1252,1253,266,740,264,1161,2156,1160],
[788,1252,1253,1548,1444,2404,1412,839,1034,838,1174,2406,2020,2364,2021,2576,837,1032,836,1172,896,1812,897,2424,1554,2244,1069,624,1068,1278,1552,1624,1816,1625,104,1071,626,1070,1276,2536,2537,2032,542,266,815,814,2064,740,381,380,540,264,813,812,1161,681,2156,109,2428,108,1160,680,2329,2328,1428],
[2156,698,1864,2276,109,108,958,256,956,788,2048,2049]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_29 : (row6_29.zip hint6_29).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_30 : List (List ℕ) := [
[256,2280,581,580,526,524,740,1593,1592,2156],
[698,1700,2116,2488,66,1540,1541,1616,1072,1880,1992,1876,1877],
[2156,109,108,241,958,256,956,788,2048,2049],
[1013,109,2612,1728,508,510,1657,2616,1494,1772,914,167,1558,1492,1692,1012,2784,912,165,1556,688,2356,954,911,1691,952,909,1689,492,1288,713,2220,2594,2016,2278,1678,1482,2592,2644,725,2172,2276,1676,1480,2205,600,1945,944,658,391,2308,900,581,946,656,389,2021,2428,1252,521,1845,393,2704],
[2156,876,1988,2420,109,108,2221,958,362,256,2620,956,360,788,2080,2048,409,2049,1952],
[108,2205,2612,1728,1494,1772,914,166,1558,1027,1492,1692,1013,2784,2196,912,164,1556,1025,689,2356,280,2464,2472,337,1232,2594,2016,2278,1679,1482,1043,2592,2644,2140,724,2172,456,2276,1677,1480,1041,2204,2724,600,658,390,1231,900,580,1781,656,388,1229,2428,1253,1,520,392,2704,861,1588],
[956,2792,389,388,340,2500,524,264,481,2156,480],
[2156,109,108,2596,958,256,956,788,2048,2049],
[2156,1132,329,109,108,958,256,956,788,2048,2049],
[2049,936,645,429,482,1592,2156,480,1160,1856]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_30 : (row6_30.zip hint6_30).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_31 : List (List ℕ) := [
[2492,1908,2556,10],
[356,2456,1824,1826,2692,76,493,2728,712,312,320,314,1440,889,2832],
[2156,337,336,280,281,2356,109,108,958,256,956,788,2048,2049],
[2156,50,2820,1920,2440,564,109,108,1709,1420,958,2124,256,2604,956,885,788,20,2048,1789,2049,768],
[513,1180,1136,2680,2496,165,109,612,1820,2632,556,1917,101,2272],
[2049,2460,645,1928,429,482,1592,2156,480,1160,1856],
[2156,1960,109,1805,108,958,256,956,788,2048,2049],
[2156,2812,237,337,109,2472,108,958,256,956,788,2048,2049],
[698,2156,756,1700,2116,130,1540,1541,109,108,1616,958,1072,256,1880,956,1992,788,1876,2048,1877,2049],
[1092,1086,883,882,2544,2312,1508,1604,1764,1765]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk6_31 : (row6_31.zip hint6_31).all (fun p => verifyS width topMask 5 taus p.1 row5 p.2) = true := by
  decide +kernel

def hint6_32 : List (List ℕ) := [
[788,2012,1252,1816,1253,266,740,264,1161,2156,1160],
[2049,429,645,2320,482,2242,1592,2437,2156,480,2240,1160,497,1856,820,2304],
[2156,1528,109,108,958,256,956,788,2048,2049],
[2156,2305,2304,1940,109,108,958,256,956,788,2048,2049],
[2156,870,868,832,2168,608,109,108,1944,958,256,956,788,2048,2049],
[2156,2412,109,108,958,256,956,788,2048,2049],
[2156,109,108,2612,1728,1494,1772,914,167,166,1558,1492,1692,1012,1013,2784,912,165,164,1556,688,689,2356,804,2594,2016,2278,1678,1679,1482,2592,2644,725,724,2172,2276,1676,1677,1480,2205,2204,600,658,958,391,390,900,256,581,580,656,956,389,388,2428,788,1252,1253,2048,521,2049,520,393,392,2704],
[2156,2636,1692,109,108,958,256,956,788,2048,2049],
[2156,990,208,1527,109,108,958,256,956,788,2048,2049]]
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
[900,104,216,926,784,78,975,974,924,1308,108,969,968,76,973,972,629,628,224,1128,1198,672,38,49,48,226,316,676,452,453,1196,674,36,51,50,1148,1060,540,541,381,380,1304,96,734,740,1144,98,732,356,1024,1292,92,297,93,296],
[1128,104,216,926,784,728,730,78,975,974,924,88,1308,969,968,76,973,972,360,488,312,313,629,628,900,224,1198,49,52,48,53,226,440,316,452,453,1196,51,54,50,55,420,113,112,540,541,993,992,1304,96,1002,740,308,98,1000,836,184,356,241,297,240,296],
[629,104,216,265,21,267,926,784,78,975,974,924,1308,940,969,968,76,973,972,628,900,958,1168,956,260,428,224,1128,1198,49,48,226,316,452,453,1196,51,50,352,472,540,541,1133,160,1304,576,202,96,644,740,200,98,288,356,529,297,68,296],
[969,104,216,14,12,21,108,926,784,78,975,974,924,1308,968,76,973,972,940,629,628,900,250,754,248,752,1244,776,512,1216,224,1128,1198,49,48,226,316,324,280,452,453,1196,51,50,540,541,412,1213,1304,1296,323,96,580,740,321,98,764,356,1089,297,1100,296],
[296,660,104,1161,216,433,926,16,758,537,784,369,78,932,975,842,974,1056,84,435,924,481,1308,1100,969,1088,968,18,756,568,684,1040,1108,1140,371,76,934,973,840,972,68,629,528,628,93,900,720,224,1050,930,240,1128,386,1198,890,49,134,48,1260,1180,722,226,909,316,1236,452,1012,453,1048,928,1076,128,1284,148,384,1196,888,51,132,50,1004,540,613,541,584,33,1304,478,96,418,153,740,24,476,416,98,492,985,356,548,549,297],
[926,104,216,28,572,14,15,784,1240,78,975,974,924,1308,969,968,76,973,972,629,628,900,1288,592,717,716,1276,748,224,1128,1198,49,48,226,316,452,453,1196,51,50,540,541,347,346,1304,808,1066,96,918,740,1172,98,234,356,432,297,433,296],
[740,104,1200,216,180,926,918,784,1044,78,602,975,566,974,567,772,464,924,916,1308,1072,969,580,968,581,76,600,973,564,972,565,774,466,629,644,628,645,704,848,900,1144,1265,681,1264,680,224,518,1128,308,1198,118,49,411,48,410,998,858,226,516,316,1020,452,884,453,885,1196,116,51,409,50,408,996,856,540,497,541,496,176,504,1304,692,693,244,1209,1068,1208,1069,96,864,136,98,138,866,356,1184,1156,297,152,25,296,153,24],
[316,104,216,926,784,78,608,834,975,974,924,1308,952,648,969,968,76,610,832,973,972,629,628,188,328,189,329,900,224,1128,1198,796,49,48,226,452,453,1196,798,51,50,540,812,541,813,460,461,165,164,1304,96,198,740,1020,98,196,356,292,668,908,297,909,296],
[51,104,216,926,784,78,975,974,620,924,1308,969,968,1312,76,484,973,1120,944,972,629,628,652,900,340,224,1128,54,1198,49,424,48,113,226,502,316,452,453,883,1196,50,1032,540,541,604,1304,2,639,1054,96,339,740,409,98,509,356,273,297,133,296,888,1176],
[78,104,216,572,1112,265,264,1240,926,520,784,975,974,924,1308,969,968,724,76,973,972,629,628,900,1152,204,268,269,224,1128,142,42,1198,486,49,487,48,226,316,452,453,1196,51,50,540,541,525,524,1304,664,1030,96,602,740,208,98,438,356,368,297,369,296]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk7_0 : (row7_0.zip hint7_0).all (fun p => verifyS width topMask 6 taus p.1 row6 p.2) = true := by
  decide +kernel

def hint7_1 : List (List ℕ) := [
[216,104,926,784,78,975,974,924,1308,969,968,76,973,972,629,628,900,224,1128,1198,49,48,226,316,452,453,1196,51,50,540,541,1304,588,589,96,192,740,180,98,194,356,392,297,1160,296,1161],
[973,104,216,12,267,926,784,78,975,974,924,1308,969,968,76,972,629,628,900,892,1252,1124,228,1256,844,224,1128,1198,49,48,226,316,452,453,1196,1120,944,51,50,540,541,805,158,1304,144,83,96,564,740,449,98,121,356,841,297,934,296],
[224,104,216,926,1276,748,784,78,975,974,924,1308,969,968,1116,872,709,708,76,973,972,629,628,900,1128,1198,49,500,48,501,226,316,452,453,440,796,881,880,1196,51,50,540,541,6,7,1304,96,458,740,518,980,780,98,300,356,721,297,720,296],
[1196,104,216,926,784,78,1272,1204,975,974,924,1308,44,969,968,76,140,40,973,972,629,628,988,989,900,224,1128,1198,420,49,48,226,316,798,452,453,51,50,540,541,604,605,350,351,1304,96,100,740,116,98,1096,356,632,388,385,297,384,296],
[98,104,62,216,194,926,1172,784,222,78,208,975,81,72,960,974,80,924,1064,1308,904,969,321,1080,936,968,320,76,1028,973,449,972,448,629,200,1300,236,628,201,552,376,900,732,553,377,224,780,1128,1000,1198,102,49,337,912,396,48,336,226,456,316,196,452,965,596,688,453,964,1196,1096,51,509,50,508,540,818,468,1224,541,819,169,745,256,1304,257,616,168,744,96,792,794,740,138,866,356,978,626,297,477,417,476,296,416],
[784,104,216,28,1112,926,520,78,975,974,924,1308,969,968,522,76,973,972,629,628,900,860,768,657,332,656,333,224,728,730,1128,1198,49,48,226,316,452,453,1196,51,50,540,541,877,876,1304,760,220,96,1044,740,222,98,1164,356,536,297,537,296],
[540,104,216,926,784,78,975,974,374,924,1308,969,968,532,76,973,972,372,629,352,472,628,900,1268,224,1128,1198,49,48,606,226,316,812,452,453,460,1196,51,50,604,541,560,1304,821,1220,852,96,816,740,497,98,818,356,869,297,612,296,1004,1016],
[356,104,1136,216,392,926,234,784,1164,78,438,975,123,284,254,974,122,924,232,1308,1188,969,764,556,824,968,765,76,436,973,121,286,252,972,120,629,288,628,289,365,736,900,1024,364,737,224,300,1128,184,1198,634,49,275,830,1104,48,274,226,302,316,292,452,56,1092,1280,453,57,1196,632,51,273,828,1106,50,272,540,869,541,868,1229,641,801,1304,800,1192,1228,640,96,976,624,740,1184,1156,98,978,626,297,493,984,492,296,985],
[452,104,216,926,784,78,975,212,974,924,1308,969,324,280,968,76,973,214,972,629,8,628,900,920,224,1128,1198,49,881,48,226,316,453,1196,51,883,50,540,460,541,712,1304,789,400,96,967,740,884,98,965,356,56,297,1013,1232,1236,296],
[1304,104,701,700,216,588,589,926,347,346,784,877,876,78,525,524,975,807,156,974,157,806,898,307,306,924,345,344,1308,696,697,969,412,1213,968,1212,413,404,1036,1037,76,527,526,973,805,158,972,159,804,896,305,304,629,1133,160,628,161,1132,1248,276,277,900,381,380,224,6,7,1128,993,992,1198,348,349,49,0,637,48,636,1,1052,125,124,226,4,5,316,165,164,452,712,789,453,788,713,400,173,172,1196,350,351,51,2,639,50,638,3,1054,127,126,540,821,1220,541,1221,820,852,1009,1008,96,258,259,618,740,692,693,244,98,256,257,616,356,801,800,1192,297,32,585,296,584,33,1084,65,64]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chk7_1 : (row7_1.zip hint7_1).all (fun p => verifyS width topMask 6 taus p.1 row6 p.2) = true := by
  decide +kernel

def hint7_2 : List (List ℕ) := [
[104,216,926,784,78,975,974,924,1308,969,968,76,973,972,629,628,900,224,1128,1198,49,48,226,316,452,453,1196,51,50,540,541,701,700,1304,60,96,1200,740,62,98,1136,356,661,297,660,296],
[1308,104,216,572,574,21,20,926,784,78,975,974,924,969,968,76,973,972,629,628,900,948,950,545,544,224,1128,1198,49,48,226,952,648,316,452,453,1196,51,50,540,541,696,697,1304,444,906,96,1072,740,904,98,1188,356,480,297,481,296]]
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
[0,80,40,84,20,22,12,13,36,38,8,9,60,46,47,44,45,0,28,48,50,72,73,54,52,64,65,4,34,35,32,33,76,24,68,58,56,17,16]]
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
