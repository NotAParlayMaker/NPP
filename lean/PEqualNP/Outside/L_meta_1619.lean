import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds Finset
namespace PEqualNP.Outside.L_meta_1619_aux

-- Wire evaluation identities from the project proof of L-meta-1558.
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

abbrev P := Fin 13
abbrev G (gs : List Gate) := Fin gs.length
def W (gs : List Gate) (w : ℕ) : Finset P :=
  univ.filter fun p => value (⟨gs,0⟩ : Circuit) (fun v : P => decide (v = p)) w = true
def node {gs : List Gate} (k : G gs) := 13 + k.val
def part (gs : List Gate) (k : G gs) := W gs (node k)
lemma in_W {gs : List Gate} {w : ℕ} {p : P} :
    p ∈ W gs w ↔ value (⟨gs,0⟩ : Circuit) (fun v : P => decide (v=p)) w = true := by simp [W]
lemma raw (gs : List Gate) (p : P) : W gs p = {p} := by
  ext v
  rw [in_W,input_value]
  simp [eq_comm]
lemma beyond (gs : List Gate) (w : ℕ) (bad : 13+gs.length ≤ w) : W gs w = ∅ := by
  ext v
  rw [in_W,missing_value]
  · simp
  · exact bad

abbrev Law (gs : List Gate) := ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
def operand (gs : List Gate) (k : G gs) (w : ℕ) := if w < node k then W gs w else ∅

lemma large_operand {gs : List Gate} {k : G gs} {w : ℕ} (h : 2 ≤ (operand gs k w).card) :
    ∃ j : G gs, j < k ∧ part gs j = operand gs k w := by
  unfold operand at *
  split at h <;> rename_i hw
  · rw [ite_eq_left hw]
    by_cases rawwire : w < 13
    · have hraw := raw gs ⟨w,rawwire⟩
      change W gs w = _ at hraw
      rw [hraw,card_singleton] at h
      omega
    · have hk := k.isLt
      unfold node at hw
      let j : G gs := ⟨w-13,by omega⟩
      refine ⟨j,?_,?_⟩
      · change w-13 < k.val
        omega
      · unfold part node
        congr 1
        change 13+(w-13) = w
        omega
  · simp at h

lemma eval_args (gs : List Gate) (k : G gs) (v : P) :
    (v ∈ part gs k) ↔ (gs.get k).op.eval ((gs.get k).inputs.map (fun a => decide (v ∈ operand gs k a))) = true := by
  unfold part
  rw [in_W,gate_value]
  · simp only [node,Nat.add_sub_cancel_left]
    have ff : (fun r : ℕ => if r < 13 + (k : ℕ) then value (⟨gs,0⟩ : Circuit) (fun q : P => decide (q = v)) r else false) =
        (fun r => decide (v ∈ operand gs k r)) := by
      funext r
      by_cases hr : r < 13 + (k : ℕ)
      · simp [operand,node,hr,in_W]
      · simp [operand,node,hr]
    exact iff_of_eq (congrArg (fun f : ℕ → Bool => (gs.get k).op.eval ((gs.get k).inputs.map f) = true) ff)
  · unfold node
    omega
  · unfold Circuit.size node
    have := k.isLt
    simpa using k.isLt

lemma shape {gs : List Gate} (law : Law gs) (k : G gs) :
    part gs k = ∅ ∨ part gs k = univ ∨ (∃ a, part gs k = operand gs k a) ∨
    ∃ a b, part gs k = operand gs k a ∪ operand gs k b ∨
           part gs k = operand gs k a ∩ operand gs k b := by
  obtain ⟨op,arity⟩ := law (gs.get k) (List.get_mem gs k)
  generalize he : (gs.get k).inputs = xs at arity
  cases xs with
  | nil =>
    rcases op with h | h
    · right; left; ext v; rw [eval_args,he,h]; simp [GateOp.eval]
    · left; ext v; rw [eval_args,he,h]; simp [GateOp.eval]
  | cons a tail =>
    cases tail with
    | nil =>
      right; right; left; refine ⟨a,?_⟩
      ext v; rcases op with h|h <;> rw [eval_args,he,h] <;> simp [GateOp.eval]
    | cons b more =>
      cases more with
      | nil =>
        right; right; right; refine ⟨a,b,?_⟩
        rcases op with h|h
        · right; ext v; rw [eval_args,he,h]; simp [GateOp.eval]
        · left; ext v; rw [eval_args,he,h]; simp [GateOp.eval]
      | cons c tail => simp at arity

lemma output_gate {gs : List Gate} {w : ℕ} (h : 2 ≤ (W gs w).card) :
    ∃ k : G gs, part gs k = W gs w := by
  by_cases hr : w < 13
  · have eq := raw gs ⟨w,hr⟩
    change W gs w = _ at eq
    rw [eq,card_singleton] at h
    omega
  by_cases hb : 13+gs.length ≤ w
  · rw [beyond gs w hb] at h
    simp at h
  refine ⟨⟨w-13,by omega⟩,?_⟩
  unfold part node
  congr 1
  change 13+(w-13)=w
  omega

def Big (gs : List Gate) : Finset (G gs) := univ.filter fun j => 4 < (part gs j).card ∧ part gs j ≠ univ

lemma explain {gs : List Gate} (law : Law gs) {T : Finset P} (size : T.card = 4)
    (k : G gs) (same : part gs k = T) (earliest : ∀ j < k, part gs j ≠ T) :
    (∃ j : G gs, 2 ≤ (part gs j).card ∧ part gs j ⊂ T) ∨
    ∃ j ∈ Big gs, ∃ h ∈ Big gs, j ≠ h ∧ part gs j ∩ part gs h = T := by
  have diff (a : ℕ) : operand gs k a ≠ T := by
    intro eq
    obtain ⟨j,lt,hj⟩ := large_operand (k:=k) (w:=a) (by rw [eq,size]; decide)
    exact earliest j lt (hj.trans eq)
  rw [← same] at size
  rcases shape law k with emp|full|⟨a,unary⟩|⟨a,b,hu|hi⟩
  · simp [emp] at size
  · simp [full] at size
  · exact (diff a (unary.symm.trans same)).elim
  · left
    have sc := card_union_le (operand gs k a) (operand gs k b)
    rw [← hu,size] at sc
    have source (x : ℕ) (large : 2 ≤ (operand gs k x).card) (sub : operand gs k x ⊆ T) :
        ∃ j : G gs, 2 ≤ (part gs j).card ∧ part gs j ⊂ T := by
      obtain ⟨j,_,eq⟩ := large_operand large
      exact ⟨j,eq ▸ large,eq ▸ (lt_of_le_of_ne sub (diff x))⟩
    by_cases enough : 2 ≤ (operand gs k a).card
    · exact source a enough (same ▸ hu ▸ subset_union_left)
    · apply source b (by omega)
      rw [← same,hu]
      exact subset_union_right
  · right
    have eq : operand gs k a ∩ operand gs k b = T := hi.symm.trans same
    have ta : T ⊆ operand gs k a := eq ▸ inter_subset_left
    have tb : T ⊆ operand gs k b := eq ▸ inter_subset_right
    have sz : T.card = 4 := same ▸ size
    have get (a : ℕ) (sub : T ⊆ operand gs k a) (proper : operand gs k a ≠ univ) :
        ∃ j ∈ Big gs, part gs j = operand gs k a := by
      have bigger := card_lt_card (lt_of_le_of_ne sub (Ne.symm (diff a)))
      rw [sz] at bigger
      obtain ⟨j,_,e⟩ := large_operand (k:=k) (w:=a) (by omega)
      exact ⟨j,mem_filter.mpr ⟨mem_univ _, e ▸ bigger, e ▸ proper⟩,e⟩
    obtain ⟨j,hj,ej⟩ := get a ta (by intro e; rw [e,univ_inter] at eq; exact diff b eq)
    obtain ⟨h,hh,eh⟩ := get b tb (by intro e; rw [e,inter_univ] at eq; exact diff a eq)
    refine ⟨j,hj,h,hh,?_,by rwa [ej,eh]⟩
    rintro rfl
    rw [← ej,← eh,inter_self] at eq
    exact diff a (ej.symm.trans eq)

lemma first_unused {gs : List Gate} (law : Law gs) (pos : 0 < gs.length) :
    (part gs ⟨0,pos⟩).card ≤ 2 ∨ part gs ⟨0,pos⟩ = univ := by
  let k : G gs := ⟨0,pos⟩
  have small (w : ℕ) : (operand gs k w).card ≤ 1 := by
    by_contra! large
    obtain ⟨j,lt,_⟩ := large_operand (show 2 ≤ (operand gs k w).card by omega)
    exact (Nat.not_lt_zero j.val) lt
  rcases shape law k with h|h|⟨w,h⟩|⟨a,b,h|h⟩
  · left; change (part gs k).card ≤ 2; simp [h]
  · exact Or.inr h
  · left; change (part gs k).card ≤ 2; rw [h]; exact (small w).trans (by decide)
  · left; change (part gs k).card ≤ 2; rw [h]
    have := card_union_le (operand gs k a) (operand gs k b)
    have := small a
    have := small b
    omega
  · left; change (part gs k).card ≤ 2; rw [h]
    exact (card_le_card inter_subset_left).trans ((small a).trans (by decide))

def common (gs : List Gate) (Z : Finset (G gs)) : Finset P :=
  univ.filter fun p => ∀ k ∈ Z, p ∈ part gs k

lemma common_pair (gs : List Gate) (j k : G gs) : common gs {j,k} = part gs j ∩ part gs k := by
  ext; simp [common]

lemma unique_owner (T : P → Finset P)
    (linear : ∀ p q : P, p ≠ q → ∃! l, p ∈ T l ∧ q ∈ T l)
    {U : Finset P} (hu : 2 ≤ U.card) {l m : P} (a : U ⊆ T l) (b : U ⊆ T m) : l = m := by
  obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp (by omega : 1 < U.card)
  exact (linear p q ne).unique ⟨a hp,a hq⟩ ⟨b hp,b hq⟩

noncomputable def owner (T : P → Finset P) (U : Finset P) : P :=
  if h : ∃ l, U ⊆ T l then h.choose else 0
lemma owner_eq (T : P → Finset P)
    (linear : ∀ p q : P, p ≠ q → ∃! l, p ∈ T l ∧ q ∈ T l)
    {U : Finset P} (hu : 2 ≤ U.card) {l : P} (sub : U ⊆ T l) : owner T U = l := by
  have h : ∃ l, U ⊆ T l := ⟨l,sub⟩
  rw [owner,dite_eq_left h]
  exact unique_owner T linear hu h.choose_spec sub

def exacts (gs : List Gate) (T : P → Finset P) (B : Finset P) : Finset (G gs) :=
  univ.filter fun k => ∃ l ∈ B, part gs k = T l
def smalls (gs : List Gate) (T : P → Finset P) (B : Finset P) : Finset (G gs) :=
  univ.filter fun k => 2 ≤ (part gs k).card ∧ ∃ l ∈ B, part gs k ⊂ T l

lemma earliest {gs : List Gate} {T : Finset P} (hx : ∃ k : G gs, part gs k = T) :
    ∃ k : G gs, part gs k = T ∧ ∀ j < k, part gs j ≠ T := by
  let A := univ.filter fun k : G gs => part gs k = T
  obtain ⟨v,hv⟩ := hx
  have nonempty : A.Nonempty := ⟨v,mem_filter.mpr ⟨mem_univ _,hv⟩⟩
  let k := A.min' nonempty
  have hk := A.min'_mem nonempty
  refine ⟨k,(mem_filter.mp hk).2,?_⟩
  intro j lt eq
  exact (not_le_of_gt lt) (A.min'_le j (mem_filter.mpr ⟨mem_univ _,eq⟩))

lemma sources (gs : List Gate) (T : P → Finset P) (B : Finset P)
    (law : Law gs) (size : ∀ l, (T l).card = 4)
    (linear : ∀ p q : P, p ≠ q → ∃! l, p ∈ T l ∧ q ∈ T l)
    (exists_gate : ∀ l, ∃ k : G gs, part gs k = T l) :
    B.card ≤ (exacts gs T B).card ∧ B.card ≤ (smalls gs T B).card + (Big gs).card.choose 2 := by
  classical
  let E := exacts gs T B
  let S := smalls gs T B
  let D := Big gs
  let name := fun k : G gs => owner T (part gs k)
  let pairName := fun X : Finset (G gs) => owner T (common gs X)
  have lineName (l : P) : owner T (T l) = l :=
    owner_eq T linear (by rw [size]; decide) (Subset.rfl)
  have e : B ⊆ E.image name := by
    intro l hl
    obtain ⟨k,hk⟩ := exists_gate l
    exact mem_image.mpr ⟨k,mem_filter.mpr ⟨mem_univ _,l,hl,hk⟩,by simpa [name,hk] using lineName l⟩
  refine ⟨(card_le_card e).trans card_image_le,?_⟩
  have cover : B ⊆ S.image name ∪ (D.powersetCard 2).image pairName := by
    intro l hl
    obtain ⟨k,hk,first⟩ := earliest (exists_gate l)
    rcases explain law (size l) k hk first with ⟨j,sz,sub⟩ | ⟨j,hj,h,hh,ne,eq⟩
    · exact mem_union_left _ (mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,sz,l,hl,sub⟩,
        owner_eq T linear sz sub.le⟩)
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨{j,h},mem_powersetCard.mpr ⟨?_,card_pair ne⟩,?_⟩
      · intro v hv
        simp only [mem_insert,mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hj
        · exact hh
      · simpa [pairName,common_pair,eq] using lineName l
  have b1 := card_le_card cover
  have b2 := card_union_le (S.image name) ((D.powersetCard 2).image pairName)
  have b3 := card_image_le (s:=S) (f:=name)
  have b4 := card_image_le (s:=D.powersetCard 2) (f:=pairName)
  rw [card_powersetCard] at b4
  change B.card ≤ S.card + D.card.choose 2
  omega

lemma budget (gs : List Gate) (T : P → Finset P) (B : Finset P) (H : Finset (G gs))
    (law : Law gs) (size : ∀ l, (T l).card = 4)
    (linear : ∀ p q : P, p ≠ q → ∃! l, p ∈ T l ∧ q ∈ T l)
    (exists_gate : ∀ l, ∃ k : G gs, part gs k = T l)
    (foreign : ∀ k ∈ H, 2 ≤ (part gs k).card ∧ ∃ l ∉ B, part gs k ⊆ T l) :
    3 * B.card + 2 * H.card ≤ 2 * gs.length := by
  classical
  let E := exacts gs T B
  let S := smalls gs T B
  let D := Big gs
  obtain ⟨he,hs⟩ := sources gs T B law size linear exists_gate
  change B.card ≤ E.card at he
  change B.card ≤ S.card + D.card.choose 2 at hs
  have ex {k} (hk : k ∈ E) : ∃ l ∈ B, part gs k = T l := (mem_filter.mp hk).2
  have sm {k} (hk : k ∈ S) : 2 ≤ (part gs k).card ∧ ∃ l ∈ B, part gs k ⊂ T l :=
    (mem_filter.mp hk).2
  have big {k} (hk : k ∈ D) : 4 < (part gs k).card ∧ part gs k ≠ univ :=
    (mem_filter.mp hk).2
  have ec {k} (hk : k ∈ E) : (part gs k).card = 4 := by
    obtain ⟨l,_,r⟩ := ex hk
    rw [r,size]
  have sc {k} (hk : k ∈ S) : (part gs k).card < 4 := by
    obtain ⟨_,l,_,lt⟩ := sm hk
    simpa [size] using card_lt_card lt
  have heH : Disjoint H E := disjoint_left.mpr (by
    intro k fh fe
    obtain ⟨large,l,hl,sub⟩ := foreign k fh
    obtain ⟨m,hm,e⟩ := ex fe
    exact hl ((unique_owner T linear large sub e.le).symm ▸ hm))
  have hsH : Disjoint H S := disjoint_left.mpr (by
    intro k fh fs
    obtain ⟨large,l,hl,sub⟩ := foreign k fh
    obtain ⟨_,m,hm,e⟩ := sm fs
    exact hl ((unique_owner T linear large sub e.le).symm ▸ hm))
  have hdH : Disjoint H D := disjoint_left.mpr (by
    intro k fh fd
    obtain ⟨_,l,_,sub⟩ := foreign k fh
    have := card_le_card sub
    have := size l
    have := (big fd).1
    omega)
  have es : Disjoint E S := disjoint_left.mpr (fun _ e s => (sc s).ne (ec e))
  have ed : Disjoint E D := disjoint_left.mpr (fun _ e d => (big d).1.ne (ec e).symm)
  have sd : Disjoint S D := disjoint_left.mpr (fun _ s d => (sc s).asymm (big d).1)
  have total := card_le_univ (((H ∪ E) ∪ S) ∪ D)
  rw [card_union_of_disjoint ((hdH.sup_left ed).sup_left sd),
      card_union_of_disjoint (hsH.sup_left es),card_union_of_disjoint heH,Fintype.card_fin] at total
  have limit := card_le_univ B
  rw [Fintype.card_fin] at limit
  by_cases low : D.card ≤ 5
  · have arith : ∀ n : Fin 6, n.val.choose 2 ≤ 2 * n.val := by decide
    have := arith ⟨D.card,by omega⟩
    change D.card.choose 2 ≤ 2*D.card at this
    omega
  by_cases middle : B.card = 13 ∧ D.card = 6
  · obtain ⟨all,six⟩ := middle
    have allB : B = univ := B.eq_univ_of_card all
    have emptyH : H = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro k h
      obtain ⟨_,l,hl,_⟩ := foreign k h
      exact hl (allB ▸ mem_univ l)
    have pos : 0 < gs.length := by omega
    let zero : G gs := ⟨0,pos⟩
    have spare := first_unused law pos
    change (part gs zero).card ≤ 2 ∨ part gs zero = univ at spare
    have ze : zero ∉ E := by
      intro h
      have q := ec h
      rcases spare with a | a
      · omega
      · simp [a] at q
    have zd : zero ∉ D := by
      intro h
      obtain ⟨l,n⟩ := big h
      rcases spare with a | a
      · omega
      · exact n a
    have extra := card_le_univ (insert zero (E ∪ D))
    rw [card_insert_of_notMem (by simp [ze,zd]),card_union_of_disjoint ed,Fintype.card_fin] at extra
    simp only [emptyH,card_empty,mul_zero,add_zero]
    omega
  · omega

end PEqualNP.Outside.L_meta_1619_aux

open PEqualNP.Outside.L_meta_1619_aux

theorem PEqualNP.Outside.L_meta_1619 : ∀ (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ l0 : Fin 13, (Finset.univ.filter (fun p0 : Fin 13 => I p0 l0)).card = 4) → (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (l2 u2 : Fin 13), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin 13 => decide (u2k = u2)))).getD (out l2) false = true ↔ I u2 l2) → ∀ (B : Finset (Fin 13)) (H : Finset (Fin gates.length)), (∀ k5 ∈ H, 2 ≤ (Finset.univ.filter (fun u5 : Fin 13 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u5k : Fin 13 => decide (u5k = u5)))).getD (13 + k5.val) false = true)).card ∧ ∃ l4 : Fin 13, l4 ∉ B ∧ ∀ u6 : Fin 13, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u6k : Fin 13 => decide (u6k = u6)))).getD (13 + k5.val) false = true → I u6 l4) → 3 * B.card + 2 * H.card ≤ 2 * gates.length := by
  intro I _ gs out size linear law outputs B H foreign
  let T := fun l : Fin 13 => univ.filter fun p => I p l
  have unique (p q : Fin 13) (ne : p ≠ q) : ∃! l, p ∈ T l ∧ q ∈ T l := by
    simpa [T] using linear p q ne
  have out_eq (l : Fin 13) : W gs (out l) = T l := by
    ext p
    rw [in_W]
    simpa only [value,T,mem_filter,mem_univ,true_and] using outputs l p
  apply budget gs T B H law size unique
  · intro l
    have sz : (W gs (out l)).card = 4 := (congrArg card (out_eq l)).trans (size l)
    obtain ⟨k,h⟩ := output_gate (w:=out l) (gs:=gs) (by omega)
    exact ⟨k,h.trans (out_eq l)⟩
  · intro k hk
    obtain ⟨large,l,hl,in_line⟩ := foreign k hk
    refine ⟨large,l,hl,?_⟩
    intro p hp
    exact mem_filter.mpr ⟨mem_univ p,in_line p (in_W.mp hp)⟩
