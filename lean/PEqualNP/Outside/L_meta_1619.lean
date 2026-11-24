import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1619_aux

abbrev X := Fin 13
def Linear (L : X → Finset X) := ∀ p q a b, p ≠ q →
  p ∈ L a → q ∈ L a → p ∈ L b → q ∈ L b → a=b
def Joined (L : X → Finset X) := ∀ p q, p≠q → ∃ a, p∈L a ∧ q∈L a
def contained (L : X → Finset X) (S : Finset X) := Finset.univ.filter fun l => L l ⊆ S

lemma le_pencil (L : X → Finset X) (sizes : ∀ l, (L l).card=4) (lin : Linear L) (p : X) :
    (Finset.univ.filter fun a => p∈L a).card ≤ 4 := by
  let A := Finset.univ.filter fun a => p∈L a
  let T := fun a => (L a).erase p
  have dis : (A : Set X).PairwiseDisjoint T := by
    intro a ha b hb ab
    apply Finset.disjoint_left.mpr
    intro q qa qb
    have ap := (Finset.mem_filter.mp ha).2
    have bp := (Finset.mem_filter.mp hb).2
    have u := Finset.mem_erase.mp qa
    have v := Finset.mem_erase.mp qb
    exact ab (lin q p a b u.1 u.2 ap v.2 bp)
  have sub : A.biUnion T ⊆ Finset.univ.erase p := by
    intro q h
    obtain ⟨a,_,qa⟩ := Finset.mem_biUnion.mp h
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp qa).1,Finset.mem_univ _⟩
  have h := Finset.card_le_card sub
  rw [Finset.card_biUnion dis] at h
  have t : ∀ a ∈ A, (T a).card=3 := by
    intro a ha
    change ((L a).erase p).card=3
    rw [Finset.card_erase_of_mem ((Finset.mem_filter.mp ha).2),sizes]
  rw [Finset.sum_congr rfl t] at h
  change A.card ≤ 4
  simp [Finset.card_erase_of_mem] at h
  omega

lemma meets (L : X → Finset X) (sizes : ∀ l, (L l).card=4) (lin : Linear L) (jn : Joined L)
    (a b : X) : ∃ p, p∈L a ∧ p∈L b := by
  classical
  by_contra! no
  let A := {p // p ∈ L a}
  let B := {q // q ∈ L b}
  have ne (x : A × B) : x.1.val ≠ x.2.val := fun h => no _ x.1.property (h ▸ x.2.property)
  let f (x : A × B) : X := (jn _ _ (ne x)).choose
  have fp (x : A × B) : x.1.val∈L (f x) ∧ x.2.val∈L (f x) := (jn _ _ (ne x)).choose_spec
  have inj : Function.Injective f := by
    intro x y eq
    have yy : y.1.val∈L (f x) ∧ y.2.val∈L (f x) := eq ▸ fp y
    apply Prod.ext <;> apply Subtype.ext
    · by_contra h
      have same := lin _ _ a (f x) h x.1.property y.1.property (fp x).1 yy.1
      exact no _ (same ▸ (fp x).2) x.2.property
    · by_contra h
      have same := lin _ _ b (f x) h x.2.property y.2.property (fp x).2 yy.2
      exact no _ x.1.property (same ▸ (fp x).1)
  have h := Fintype.card_le_of_injective f inj
  simp [A,B,sizes] at h

lemma line_eq (L : X → Finset X) (_sizes : ∀ l, (L l).card=4) (lin : Linear L)
    {s : Finset X} {l m : X} (two : 2 ≤ s.card) (a : s⊆L l) (b : s⊆L m) : l=m := by
  obtain ⟨p,hp,q,hq,pq⟩ := Finset.one_lt_card.mp (by omega : 1<s.card)
  exact lin p q l m pq (a hp) (a hq) (b hp) (b hq)

lemma sparse_parent (L : X → Finset X) (sizes : ∀ l, (L l).card=4) (lin : Linear L) (jn : Joined L)
    (a b : Finset X) (l : X) (inter : a∩b=L l) :
    (contained L a).card≤2 ∨ (contained L b).card≤2 := by
  classical
  let A := contained L a
  let B := contained L b
  have la : l∈A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => (Finset.mem_inter.mp (inter ▸ hp)).1⟩
  have lb : l∈B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => (Finset.mem_inter.mp (inter ▸ hp)).2⟩
  have common {i} (ia : i∈A) (ib : i∈B) : i=l := by
    apply line_eq L sizes lin (s := L i) (by rw [sizes]; decide) (fun _ h => h)
    intro p hp
    rw [←inter]
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp ia).2 hp,(Finset.mem_filter.mp ib).2 hp⟩
  by_contra! large
  change 2<A.card ∧ 2<B.card at large
  obtain ⟨i,ia,il⟩ := Finset.exists_mem_ne (s := A) (a := l) (by omega)
  obtain ⟨j,jb,jl⟩ := Finset.exists_mem_ne (s := B) (a := l) (by omega)
  have cross {v w} (va : v∈A) (wb : w∈B) : ∃ p, p∈L v ∧ p∈L w ∧ p∈L l := by
    obtain ⟨p,hv,hw⟩ := meets L sizes lin jn v w
    exact ⟨p,hv,hw,inter ▸ Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp va).2 hv,(Finset.mem_filter.mp wb).2 hw⟩⟩
  obtain ⟨p,pii,pj,pl⟩ := cross ia jb
  have into : A ∪ B ⊆ Finset.univ.filter fun m => p∈L m := by
    intro m mem
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp mem with ma|mb
    · obtain ⟨q,qm,qj,ql⟩ := cross ma jb
      have e : q=p := by by_contra ne; exact jl (lin q p j l ne qj pj ql pl)
      exact e ▸ qm
    · obtain ⟨q,qi,qm,ql⟩ := cross ia mb
      have e : q=p := by by_contra ne; exact il (lin q p i l ne qi pii ql pl)
      exact e ▸ qm
  have cap := (Finset.card_le_card into).trans (le_pencil L sizes lin p)
  have eq : A∩B={l} := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_singleton]
    exact ⟨fun h => common h.1 h.2,fun e => e ▸ ⟨la,lb⟩⟩
  have h := Finset.card_union_add_card_inter A B
  rw [eq,Finset.card_singleton] at h
  omega

open PEqualNP.CircuitLowerBounds
-- The wire evaluation identities specialize the public bowtie proof to thirteen inputs.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht]; simp [hl]

theorem getD_ext (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val (C : Circuit) (x : Fin 13 → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_output (C : Circuit) (x : Fin 13 → Bool) :
    val C x C.output = C.eval (List.ofFn x) := rfl

theorem val_input (C : Circuit) (x : Fin 13 → Bool) (i : Fin 13) :
    val C x i.val = x i := by
  rw [val, getD_ext _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  fin_cases i <;> rfl

theorem val_beyond (C : Circuit) (x : Fin 13 → Bool) {i : ℕ}
    (hi : 13 + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand (C : Circuit) (x : Fin 13 → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate (C : Circuit) (x : Fin 13 → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (13 + p) = g.op.eval (g.inputs.map (operand C x (13 + p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p + 1) := by
    conv_lhs => rw [← List.take_append_drop (p + 1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = 13 + p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (13 + p) i := by
    by_cases hi : i < 13 + p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact getD_ext _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (13 + p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p + 1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (13 + p) false = _
  rw [getD_ext _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

theorem val_and {C : Circuit} (x : Fin 13 → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) (hop : g.op = GateOp.and) :
    val C x (13 + p) = true ↔ ∀ i ∈ g.inputs, i < 13 + p ∧ val C x i = true := by
  rw [val_gate C x hp, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id, operand]
  constructor
  · intro h i hi
    have := h i hi
    split_ifs at this with hlt
    exact ⟨hlt, this⟩
  · intro h i hi
    obtain ⟨hlt, hv⟩ := h i hi
    simp [hlt, hv]

theorem val_or {C : Circuit} (x : Fin 13 → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) (hop : g.op = GateOp.or) :
    val C x (13 + p) = true ↔ ∃ i ∈ g.inputs, i < 13 + p ∧ val C x i = true := by
  rw [val_gate C x hp, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id, operand]
  constructor
  · rintro ⟨i, hi, hv⟩
    split_ifs at hv with hlt
    exact ⟨i, hi, hlt, hv⟩
  · rintro ⟨i, hi, hlt, hv⟩
    exact ⟨i, hi, by simp [hlt, hv]⟩

def singletonRow (u p : Fin 13) := decide (p=u)
def part (C : Circuit) (w : Nat) := Finset.univ.filter fun u : Fin 13 => val C (singletonRow u) w=true
def arg (C : Circuit) (w i : Nat) : Finset (Fin 13) := if i<w then part C i else ∅

theorem part_raw (C : Circuit) {w : Nat} (h : w<13) : part C w = {⟨w,h⟩} := by
  ext u
  have eq := val_input C (singletonRow u) ⟨w,h⟩
  simp only [part,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  rw [eq]; simp only [singletonRow,decide_eq_true_eq]; exact eq_comm

theorem part_beyond (C : Circuit) {w : Nat} (h : 13+C.gates.length≤w) : part C w=∅ := by
  ext u; simp [part,val_beyond C _ h]

theorem part_arg (C : Circuit) (w i : Nat) (u : Fin 13) :
    u∈arg C w i ↔ i<w ∧ val C (singletonRow u) i=true := by
  by_cases h : i<w <;> simp [arg,h,part]

theorem binary_shape (C : Circuit) (basis : ∀ g∈C.gates,
    (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (k : Fin C.gates.length) :
    let w := 13+k.val
    (part C w=∅ ∨ part C w=Finset.univ) ∨
    (∃ a, part C w=arg C w a) ∨
    (∃ a b, part C w=arg C w a ∪ arg C w b ∨ part C w=arg C w a ∩ arg C w b) := by
  classical
  let g := C.gates.get k
  have someg : C.gates[k.val]?=some g := by simp [g]
  obtain ⟨op,size⟩ := basis g (List.get_mem _ _)
  let w := 13+k.val
  change (part C w=∅ ∨ part C w=Finset.univ) ∨ _ ∨ _
  have leaves : g.inputs=[] ∨ (∃ a, g.inputs=[a]) ∨ ∃ a b, g.inputs=[a,b] := by
    cases e : g.inputs with
    | nil => exact Or.inl rfl
    | cons a tl => cases tl with
      | nil => exact Or.inr (Or.inl ⟨_,rfl⟩)
      | cons b tt => cases tt with
        | nil => exact Or.inr (Or.inr ⟨_,_,rfl⟩)
        | cons c rr => simp [e] at size
  have andv (ha : g.op=GateOp.and) (u : Fin 13) :
      u ∈ part C w ↔ ∀ i∈g.inputs, u∈arg C w i := by
    simpa only [part,Finset.mem_filter,Finset.mem_univ,true_and,part_arg,w] using val_and (singletonRow u) someg ha
  have orv (ho : g.op=GateOp.or) (u : Fin 13) :
      u ∈ part C w ↔ ∃ i∈g.inputs, u∈arg C w i := by
    simpa only [part,Finset.mem_filter,Finset.mem_univ,true_and,part_arg,w] using val_or (singletonRow u) someg ho
  rcases leaves with e|⟨a,e⟩|⟨a,b,e⟩
  · rcases op with ha|ho
    · left; right; ext u; rw [andv ha]; simp [e,w]
    · left; left; ext u; rw [orv ho]; simp [e,w]
  · right; left; refine ⟨a,?_⟩; ext u
    rcases op with ha|ho
    · rw [andv ha]; simp [e,w]
    · rw [orv ho]; simp [e,w]
  · right; right; refine ⟨a,b,?_⟩
    rcases op with ha|ho
    · right; ext u; rw [andv ha]; simp [e,w]
    · left; ext u; rw [orv ho]; simp [e,w]

open PEqualNP.CircuitLowerBounds

def tags (L : X → Finset X) (S : Finset X) : Finset X :=
  if 2 ≤ S.card ∧ S.card < 4 then Finset.univ.filter fun l => S ⊆ L l
  else if 4 < S.card ∧ (contained L S).card ≤ 2 then contained L S else ∅

lemma tag_bound (L : X → Finset X) (sizes : ∀ l, (L l).card=4) (lin : Linear L) (S : Finset X) :
    (tags L S).card ≤ 2 := by
  unfold tags
  split_ifs with a b
  · have one : (Finset.univ.filter fun l => S ⊆ L l).card ≤ 1 :=
      Finset.card_le_one_iff.mpr fun hi hj =>
        line_eq L sizes lin a.1 (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    omega
  · exact b.2
  · simp

lemma tag_not_four (L : X → Finset X) {S : Finset X} {l} (h : l∈tags L S) : S.card≠4 := by
  unfold tags at h; split_ifs at h with a b
  · omega
  · omega
  · simp at h

lemma tag_not_held (L : X → Finset X) (sizes : ∀ l, (L l).card=4) (lin : Linear L)
    {S : Finset X} {l m} (tag : l∈tags L S) (sub : S⊆L m) : l=m := by
  unfold tags at tag; split_ifs at tag with small large
  · exact line_eq L sizes lin small.1 (Finset.mem_filter.mp tag).2 sub
  · have le := Finset.card_le_card sub; rw [sizes] at le; omega
  · simp at tag

lemma union_tag (L : X → Finset X) (sizes : ∀ l, (L l).card=4)
    {a b : Finset X} {l} (eq : a∪b=L l) (neA : a≠L l) (neB : b≠L l) :
    l∈tags L a ∨ l∈tags L b := by
  have sa : a ⊆ L l := eq ▸ Finset.subset_union_left
  have sb : b ⊆ L l := eq ▸ Finset.subset_union_right
  have small (s : Finset X) (sub : s⊆L l) (ne : s≠L l) (two : 2≤ s.card) : l∈tags L s := by
    have lt := Finset.card_lt_card (show s ⊂ L l from Finset.ssubset_iff_subset_ne.mpr ⟨sub,ne⟩)
    rw [sizes] at lt; simp [tags,two,lt,sub]
  by_cases h : 2 ≤ a.card
  · exact Or.inl (small a sa neA h)
  · apply Or.inr; apply small b sb neB
    have le := Finset.card_union_le a b; rw [eq,sizes] at le; omega

lemma inter_tag (L : X → Finset X) (sizes : ∀ l, (L l).card=4) (lin : Linear L) (jn : Joined L)
    {a b : Finset X} {l} (eq : a∩b=L l) (neA : a≠L l) (neB : b≠L l) :
    l∈tags L a ∨ l∈tags L b := by
  have sa : L l ⊆ a := eq ▸ Finset.inter_subset_left
  have sb : L l ⊆ b := eq ▸ Finset.inter_subset_right
  have large (s : Finset X) (sub : L l⊆s) (ne : s≠L l) (few : (contained L s).card ≤ 2) :
      l ∈ tags L s := by
    have lt := Finset.card_lt_card (show L l ⊂ s from Finset.ssubset_iff_subset_ne.mpr ⟨sub,Ne.symm ne⟩)
    rw [sizes] at lt
    have no : ¬s.card<4 := by omega
    have yes : l ∈ contained L s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub⟩
    simpa [tags,no,lt,few] using yes
  exact (sparse_parent L sizes lin jn a b l eq).imp (large a sa neA) (large b sb neB)

lemma gate_for (C : Circuit) {w : Nat} (two : 2 ≤ (part C w).card) :
    ∃ j : Fin C.gates.length, 13+j.val=w := by
  by_cases raw : w<13
  · rw [part_raw C raw,Finset.card_singleton] at two; omega
  by_cases beyond : 13+C.gates.length≤w
  · rw [part_beyond C beyond,Finset.card_empty] at two; omega
  exact ⟨⟨w-13,by omega⟩,by change 13+(w-13)=w; omega⟩

lemma root_and_tag (C : Circuit) (L : X → Finset X) (sizes : ∀ l, (L l).card=4)
    (lin : Linear L) (jn : Joined L) (basis : ∀ g∈C.gates,
    (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (l : X) (found : ∃ u, part C u = L l) :
    (∃ j : Fin C.gates.length, part C (13+j.val)=L l) ∧
    ∃ j : Fin C.gates.length, l ∈ tags L (part C (13+j.val)) := by
  classical
  let w := Nat.find found
  have eq : part C w=L l := Nat.find_spec found
  have four : (part C w).card=4 := eq ▸ sizes l
  obtain ⟨j,hj⟩ := gate_for C (w := w) (by omega)
  refine ⟨⟨j,hj ▸ eq⟩,?_⟩
  have nonempty : L l ≠ ∅ := by intro h; have s := sizes l; simp [h] at s
  have ne (i : Nat) : arg C w i ≠ L l := by
    intro e
    by_cases hi : i<w
    · rw [arg,ite_eq_left hi] at e
      exact (Nat.find_min found hi) e
    · rw [arg,ite_eq_right hi] at e
      exact nonempty e.symm
  have convert (i : Nat) (tag : l∈tags L (arg C w i)) : ∃ k : Fin C.gates.length, l∈tags L (part C (13+k.val)) := by
    by_cases hi : i<w
    · rw [arg,ite_eq_left hi] at tag
      have two : 2≤(part C i).card := by
        by_contra! low
        have notbig : ¬4<(part C i).card := by omega
        have nottwo : ¬2≤(part C i).card := by omega
        simp [tags,nottwo,notbig] at tag
      obtain ⟨k,ee⟩ := gate_for C two
      exact ⟨k,ee ▸ tag⟩
    · simp [arg,hi,tags] at tag
  have shape := binary_shape C basis j
  dsimp only at shape
  rw [hj,eq] at shape
  rcases shape with (zero|one)|⟨i,e⟩|⟨i,i',e|e⟩
  · exact False.elim (nonempty zero)
  · have h := sizes l; simp [one] at h
  · exact False.elim (ne i e.symm)
  · rcases union_tag L sizes e.symm (ne i) (ne i') with h|h
    · exact convert i h
    · exact convert i' h
  · rcases inter_tag L sizes lin jn e.symm (ne i) (ne i') with h|h
    · exact convert i h
    · exact convert i' h

open PEqualNP.CircuitLowerBounds

lemma count_final (C : Circuit) (L : X → Finset X) (sizes : ∀ l, (L l).card=4)
    (lin : Linear L) (jn : Joined L) (basis : ∀ g∈C.gates,
    (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (found : ∀ l, ∃ w, part C w=L l)
    (B : Finset X) (H : Finset (Fin C.gates.length))
    (held : ∀ k∈H, ∃ m∉B, part C (13+k.val)⊆L m) :
    3 * B.card + 2 * H.card ≤ 2*C.gates.length := by
  classical
  let S (k : Fin C.gates.length) := part C (13+k.val)
  let R := Finset.univ.filter fun k => ∃ l∈B, S k=L l
  let T := Finset.univ.filter fun k => ∃ l∈B, l∈tags L (S k)
  have cert (l : X) := root_and_tag C L sizes lin jn basis l (found l)
  let f (l : {a // a∈B}) : {k // k∈R} :=
    ⟨(cert l).1.choose,Finset.mem_filter.mpr ⟨Finset.mem_univ _,l,l.property,(cert l).1.choose_spec⟩⟩
  have key (l : {a // a∈B}) : S (f l).val=L l := (cert l).1.choose_spec
  have inject : Function.Injective f := by
    intro i j eq
    have line : L i=L j := (key i).symm.trans (eq ▸ key j)
    apply Subtype.ext
    exact line_eq L sizes lin (s := L i) (by rw [sizes]; decide) (fun _ h => h) (fun _ h => line ▸ h)
  have rb : B.card≤R.card := by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inject
  have sub : B ⊆ T.biUnion (fun k => tags L (S k)) := by
    intro l lb
    obtain ⟨k,tag⟩ := (cert l).2
    exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,l,lb,tag⟩,tag⟩
  have tb : B.card≤T.card*2 := by
    have h := (Finset.card_le_card sub).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum (s := T) (g := fun _ => 2) (fun k _ => tag_bound L sizes lin (S k))))
    simpa using h
  have rt : Disjoint R T := by
    apply Finset.disjoint_left.mpr
    intro k kr kt
    obtain ⟨l,_,e⟩ := (Finset.mem_filter.mp kr).2
    obtain ⟨m,_,t⟩ := (Finset.mem_filter.mp kt).2
    exact tag_not_four L t (e ▸ sizes l)
  have rh : Disjoint R H := by
    apply Finset.disjoint_left.mpr
    intro k kr kh
    obtain ⟨l,lb,e⟩ := (Finset.mem_filter.mp kr).2
    obtain ⟨m,nm,sm⟩ := held k kh
    have lm := line_eq L sizes lin (s := S k) (by rw [e,sizes]; decide) (fun p hp => e ▸ hp) sm
    exact nm (lm ▸ lb)
  have th : Disjoint T H := by
    apply Finset.disjoint_left.mpr
    intro k kt kh
    obtain ⟨l,lb,t⟩ := (Finset.mem_filter.mp kt).2
    obtain ⟨m,nm,sm⟩ := held k kh
    exact nm ((tag_not_held L sizes lin t sm) ▸ lb)
  have cap := Finset.card_le_univ (R ∪ T ∪ H)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨rh,th⟩),Finset.card_union_of_disjoint rt] at cap
  simp only [Fintype.card_fin] at cap
  omega

end PEqualNP.Outside.L_meta_1619_aux


open PEqualNP.Outside.L_meta_1619_aux PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1619 : ∀ (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ l0 : Fin 13, (Finset.univ.filter (fun p0 : Fin 13 => I p0 l0)).card = 4) → (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (l2 u2 : Fin 13), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin 13 => decide (u2k = u2)))).getD (out l2) false = true ↔ I u2 l2) → ∀ (B : Finset (Fin 13)) (H : Finset (Fin gates.length)), (∀ k5 ∈ H, 2 ≤ (Finset.univ.filter (fun u5 : Fin 13 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u5k : Fin 13 => decide (u5k = u5)))).getD (13 + k5.val) false = true)).card ∧ ∃ l4 : Fin 13, l4 ∉ B ∧ ∀ u6 : Fin 13, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u6k : Fin 13 => decide (u6k = u6)))).getD (13 + k5.val) false = true → I u6 l4) → 3 * B.card + 2 * H.card ≤ 2 * gates.length := by
  intro I inst gates out sizes unique basis outputs B H held
  let L (l : Fin 13) := Finset.univ.filter fun p => I p l
  let C : Circuit := ⟨gates,0⟩
  have mem (p l : Fin 13) : p ∈ L l ↔ I p l := by simp [L]
  have lin : Linear L := by
    intro p q a b ne pa qa pb qb
    exact (unique p q ne).unique ⟨(mem _ _).mp pa,(mem _ _).mp qa⟩ ⟨(mem _ _).mp pb,(mem _ _).mp qb⟩
  have jn : Joined L := by
    intro p q ne
    obtain ⟨a,ha,_⟩ := unique p q ne
    exact ⟨a,(mem _ _).mpr ha.1,(mem _ _).mpr ha.2⟩
  apply count_final C L sizes lin jn basis _ B H
  · intro k kh
    obtain ⟨_,m,mb,h⟩ := held k kh
    refine ⟨m,mb,?_⟩
    intro u hu
    exact (mem _ _).mpr (h u ((Finset.mem_filter.mp hu).2))
  · intro l
    refine ⟨out l,?_⟩
    ext u
    constructor
    · intro hu
      apply (mem _ _).mpr
      apply (outputs l u).mp
      exact (Finset.mem_filter.mp hu).2
    · intro hu
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      exact (outputs l u).mpr ((mem _ _).mp hu)
