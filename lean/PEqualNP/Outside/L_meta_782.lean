import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]; simp [hl]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def rd (C : Circuit) (x : List Bool) (g i : ℕ) : Bool :=
  if i < g then (C.wires x).getD i false else false

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false := fold_getD_lt _ _ _ h

theorem wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  set A := (C.gates.take j).foldl step x with hA
  have hAl : A.length = x.length + j := by
    rw [hA, fold_length]; simp; omega
  have hw : C.wires x = (C.gates.drop (j + 1)).foldl step (step A C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hreadA : ∀ i, A.getD i false = rd C x (x.length + j) i := by
    intro i
    unfold rd
    by_cases hi : i < x.length + j
    · rw [ite_eq_left hi, hw, fold_getD_lt _ (step A C.gates[j]) i (by simp [step]; omega), step,
        List.getD_append _ _ _ _ (by omega)]
    · rw [ite_eq_right hi, List.getD_eq_default]; omega
  rw [hw, fold_getD_lt _ _ _ (by simp [step]; omega), step,
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hAl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  exact List.map_congr_left (fun i _ => hreadA i)


def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi

theorem wires_mono (C : Circuit) (hC : IsMonotoneCircuit C) (a b : List Bool)
    (hl : a.length = b.length) (h : LeL a b) : LeL (C.wires a) (C.wires b) :=
  fold_mono C.gates hC a b hl h

def oneInput {n : ℕ} (a : Fin n) (b : Fin n) : Bool := decide (b = a)

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (g : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD g false

def support (n : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => value C (oneInput a) g = true)

theorem mem_support {n : ℕ} (C : Circuit) (g : ℕ) (a : Fin n) :
    a ∈ support n C g ↔ value C (oneInput a) g = true := by
  simp [support]

def gateAt (C : Circuit) (n g : ℕ) : Gate :=
  C.gates.getD (g - n) ⟨GateOp.or, []⟩

def child (C : Circuit) (n g : ℕ) (slot : Fin 2) : ℕ :=
  (gateAt C n g).inputs.getD slot.val g

theorem difference_child {n : ℕ} (C : Circuit)
    (basis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (g : ℕ) (lo : n ≤ g) (hi : g < n + C.gates.length)
    (x y : Fin n → Bool) (hx : value C x g = true) (hy : value C y g = false) :
    ∃ slot : Fin 2, child C n g slot < g ∧
      value C x (child C n g slot) = true ∧ value C y (child C n g slot) = false := by
  let t := g - n
  have ht : t < C.gates.length := by dsimp [t]; omega
  have hg : g = n + t := by dsimp [t]; omega
  have ha : gateAt C n g = C.gates[t] := by
    simp [gateAt, t, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  have hb := basis C.gates[t] (List.getElem_mem ht)
  have form : ∃ a b, C.gates[t].inputs = [a,b] := by
    generalize C.gates[t].inputs = l at hb ⊢
    rcases l with _ | ⟨a, _ | ⟨b, tail⟩⟩
    · simp at hb
    · simp at hb
    · have hempty : tail = [] := by
        apply List.length_eq_zero_iff.mp
        simpa using hb.2
      subst tail
      exact ⟨a,b,rfl⟩
  obtain ⟨a,b,hab⟩ := form
  have ch0 : child C n g (0 : Fin 2) = a := by simp [child, ha, hab]
  have ch1 : child C n g (1 : Fin 2) = b := by simp [child, ha, hab]
  have hgEval (z : Fin n → Bool) :
      value C z g = C.gates[t].op.eval [rd C (List.ofFn z) g a, rd C (List.ofFn z) g b] := by
    unfold value
    have h := wires_gate C (List.ofFn z) t ht
    simpa [List.length_ofFn, ← hg, hab] using h
  have diff (w : ℕ) (h : rd C (List.ofFn x) g w = true)
      (h' : rd C (List.ofFn y) g w = false) :
      w < g ∧ value C x w = true ∧ value C y w = false := by
    unfold rd at h h'
    by_cases hw : w < g
    · simp only [ite_eq_left hw] at h h'
      exact ⟨hw,h,h'⟩
    · simp [hw] at h
  rw [hgEval] at hx hy
  rcases hb.1 with hop | hop
  · simp [hop, GateOp.eval, Bool.and_eq_true] at hx hy
    by_cases hya : rd C (List.ofFn y) g a = true
    · exact ⟨1, by simpa only [ch1] using diff b hx.2 (hy hya)⟩
    · have haf : rd C (List.ofFn y) g a = false := by
        cases he : rd C (List.ofFn y) g a <;> simp_all
      exact ⟨0, by simpa only [ch0] using diff a hx.1 haf⟩
  · simp [hop, GateOp.eval, Bool.or_eq_true, Bool.or_eq_false_iff] at hx hy
    rcases hx with hx | hx
    · exact ⟨0, by simpa only [ch0] using diff a hx hy.1⟩
    · exact ⟨1, by simpa only [ch1] using diff b hx hy.2⟩

theorem support_card_of_input {n : ℕ} (C : Circuit) (g : ℕ) (h : g < n) :
    (support n C g).card ≤ 1 := by
  have sub : support n C g ⊆ {⟨g,h⟩} := by
    intro a ha
    rw [mem_support] at ha
    unfold value at ha
    rw [wires_input _ _ _ (by simpa using h)] at ha
    simpa [oneInput, List.getD_eq_getElem?_getD, h, eq_comm] using ha
  simpa using Finset.card_le_card sub

theorem support_empty_above {n : ℕ} (C : Circuit) (g : ℕ)
    (h : n + C.gates.length ≤ g) : support n C g = ∅ := by
  ext a
  have hv : value C (oneInput a) g = false := by
    unfold value
    rw [List.getD_eq_default]
    simpa [wires_length] using h
  simp [mem_support, hv]

theorem value_mono {n : ℕ} (C : Circuit) (mono : IsMonotoneCircuit C)
    (x y : Fin n → Bool) (h : ∀ a, x a = true → y a = true)
    (g : ℕ) (hx : value C x g = true) : value C y g = true := by
  apply wires_mono C mono (List.ofFn x) (List.ofFn y) (by simp) _ g hx
  intro i hi
  by_cases hlt : i < n
  · have hv (z : Fin n → Bool) : (List.ofFn z).getD i false = z ⟨i,hlt⟩ := by
      simp [List.getD_eq_getElem?_getD, hlt]
    rw [hv] at hi ⊢
    exact h _ hi
  · simp [List.getD_eq_getElem?_getD, hlt] at hi

abbrev IsPrivate {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (g : ℕ) : Prop :=
  support n C g ⊆ S ∧ 2 ≤ (support n C g).card

def goes {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (u v : ℕ) : Prop :=
  IsPrivate C S u ∧ v < u ∧ ∃ s : Fin 2, child C n u s = v

noncomputable def reachable {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (root : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (root+1)).filter (Relation.ReflTransGen (goes C S) root)

theorem root_reachable {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (root : ℕ) :
    root ∈ reachable C S root := by
  classical
  simp [reachable, Relation.ReflTransGen.refl]

theorem earlier_reachable {n : ℕ} (C : Circuit) (S : Finset (Fin n)) {root u v : ℕ}
    (hu : u ∈ reachable C S root) (hv : goes C S u v) : v ∈ reachable C S root := by
  classical
  simp only [reachable, Finset.mem_filter, Finset.mem_range] at hu ⊢
  exact ⟨by have := hv.2.1; omega, hu.2.tail hv⟩

-- Each reached wire except the root occupies a distinct parent slot.
theorem reachable_exit_bound {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (root : ℕ) :
    let R := reachable C S root
    let P := R.filter (IsPrivate C S)
    let E := R.filter (fun g => ¬ IsPrivate C S g)
    E.card ≤ P.card + 1 := by
  classical
  dsimp only
  set R := reachable C S root
  set P := R.filter (IsPrivate C S)
  have hsub : R.erase root ⊆ (P ×ˢ (Finset.univ : Finset (Fin 2))).image
      (fun z => child C n z.1 z.2) := by
    intro v hv
    obtain ⟨hne,hR⟩ := Finset.mem_erase.mp hv
    have hh := (Finset.mem_filter.mp hR).2
    cases hh with
    | refl => exact (hne rfl).elim
    | tail hp he =>
      obtain ⟨priv, lt, slot, hs⟩ := he
      obtain ⟨bound,_⟩ := Finset.mem_filter.mp hR
      refine Finset.mem_image.mpr ⟨(_,slot), ?_, hs⟩
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, hp⟩,priv⟩, Finset.mem_univ _⟩
      have rle : ∀ a b, Relation.ReflTransGen (goes C S) a b → b ≤ a := by
        intro a b hab
        induction hab with
        | refl => rfl
        | tail _ h ih => exact h.2.1.le.trans ih
      have := rle _ _ hp
      exact Finset.mem_range.mpr (by omega)
  have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
  have hr := root_reachable C S root
  rw [Finset.card_erase_of_mem hr, Finset.card_product] at hcard
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hsplit := Finset.card_filter_add_card_filter_not (s := R) (IsPrivate C S)
  change P.card + _ = R.card at hsplit
  change R.card - 1 ≤ P.card * 2 at hcard
  have hpos := Finset.card_pos.mpr ⟨root,hr⟩
  change 0 < R.card at hpos
  omega


theorem private_is_gate {n : ℕ} (C : Circuit) (S : Finset (Fin n)) {g : ℕ}
    (h : IsPrivate C S g) : n ≤ g ∧ g < n + C.gates.length := by
  constructor
  · by_contra! hlt
    have := support_card_of_input C g hlt
    have := h.2
    omega
  · by_contra! hge
    have hc := h.2
    rw [support_empty_above C g hge, Finset.card_empty] at hc
    omega

theorem output_bound {n k c root : ℕ} (C : Circuit) (S : Finset (Fin n))
    (basis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (_hr : IsPrivate C S root)
    (promise : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → value C x root = false)
    (ck : c ≤ k) (cs : c+1 ≤ (support n C root).card) :
    c ≤ ((reachable C S root).filter (IsPrivate C S)).card := by
  classical
  set R := reachable C S root
  set P := R.filter (IsPrivate C S)
  set E := R.filter (fun g => ¬ IsPrivate C S g)
  set B := E.filter (fun g => ¬ support n C g ⊆ S)
  have exitBound : E.card ≤ P.card + 1 := reachable_exit_bound C S root
  by_contra! tooFew
  -- Choose one point outside the set for each exit with such a witness.
  have witnesses : ∀ g : B, ∃ a ∈ support n C g.val, a ∉ S :=
    fun g => Finset.not_subset.mp (Finset.mem_filter.mp g.property).2
  choose choosePoint hp hnot using witnesses
  set T := B.attach.image choosePoint
  have tcard : T.card ≤ k := by
    have h1 : T.card ≤ B.attach.card := Finset.card_image_le
    rw [Finset.card_attach] at h1
    have h2 : B.card ≤ E.card := Finset.card_filter_le _ _
    omega
  let test : Fin n → Bool := fun a => decide (a ∈ T)
  have testFalse : value C test root = false := by
    apply promise test
    · simpa [test, Finset.filter_mem_eq_inter] using tcard
    · intro a ha
      simp only [test, decide_eq_false_iff_not]
      intro aT
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp aT
      exact hnot g ha
  have mono : IsMonotoneCircuit C := fun g hg => (basis g hg).1
  have trueOutside (g : ℕ) (hg : g ∈ B) : value C test g = true := by
    let w : B := ⟨g,hg⟩
    refine value_mono C mono (oneInput (choosePoint w)) test ?_ g ?_
    · intro a ha
      have he : a = choosePoint w := by simpa [oneInput] using ha
      subst a
      simp only [test, decide_eq_true_eq]
      exact Finset.mem_image.mpr ⟨w,Finset.mem_attach _ _,rfl⟩
    · exact (mem_support C g _).mp (hp w)
  -- Follow a difference between the singleton and the test down to an exit.
  have trace (a : Fin n) (g : ℕ) : g ∈ R →
      value C (oneInput a) g = true → value C test g = false →
      ∃ e ∈ E, a ∈ support n C e ∧ value C test e = false := by
    induction g using Nat.strong_induction_on with
    | ind g ih =>
      intro hg hon hoff
      by_cases priv : IsPrivate C S g
      · obtain ⟨lo,hi⟩ := private_is_gate C S priv
        obtain ⟨slot,hs,hon',hoff'⟩ := difference_child C basis g lo hi _ _ hon hoff
        exact ih _ hs (earlier_reachable C S hg ⟨priv,hs,slot,rfl⟩) hon' hoff'
      · exact ⟨g,Finset.mem_filter.mpr ⟨hg,priv⟩,(mem_support C g a).mpr hon,hoff⟩
  have exitFor : ∀ a : (support n C root), ∃ e ∈ E,
      a.val ∈ support n C e ∧ value C test e = false := by
    intro a
    exact trace a.val root (root_reachable C S root) ((mem_support C root a.val).mp a.property) testFalse
  choose exit eh ealive eoff using exitFor
  have exSmall (a : (support n C root)) : (support n C (exit a)).card ≤ 1 := by
    have hnp := (Finset.mem_filter.mp (eh a)).2
    have hsub : support n C (exit a) ⊆ S := by
      by_contra hbad
      have hm : exit a ∈ B := Finset.mem_filter.mpr ⟨eh a,hbad⟩
      exact (by decide : true ≠ false) ((trueOutside _ hm).symm.trans (eoff a))
    by_contra! hc
    exact hnp ⟨hsub,by omega⟩
  let mapExit (a : (support n C root)) : E := ⟨exit a,eh a⟩
  have inj : Function.Injective mapExit := by
    intro a b eq
    have he : exit a = exit b := congrArg Subtype.val eq
    apply Subtype.ext
    exact Finset.card_le_one.mp (exSmall a) _ (ealive a) _ (he.symm ▸ ealive b)
  have count := Fintype.card_le_of_injective mapExit inj
  simp only [Fintype.card_coe] at count
  omega

end PEqualNP.Outside.L_meta_782_aux

open PEqualNP.Outside.L_meta_782_aux in
theorem PEqualNP.Outside.L_meta_782 :
    ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c intersection enough basis accepted promise cap budget
  classical
  let P (i : Fin m) := (reachable C (S i) (o i)).filter (IsPrivate C (S i))
  have bound (i : Fin m) : c i ≤ (P i).card := by
    apply output_bound C (S i) basis
    · exact ⟨fun a ha => accepted i a ((mem_support C (o i) a).mp ha),enough i⟩
    · exact promise i
    · exact cap i
    · exact budget i
  -- Two outputs cannot both charge a gate that accepts two distinct singletons.
  have apart : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ different
    apply Finset.disjoint_left.mpr
    intro g gi gj
    have hi := (Finset.mem_filter.mp gi).2
    have hj := (Finset.mem_filter.mp gj).2
    have h := Finset.card_le_card (s := support n C g) (t := S i ∩ S j)
      (fun a ha => Finset.mem_inter.mpr ⟨hi.1 ha,hj.1 ha⟩)
    have h' := intersection i j different
    have := hi.2
    omega
  have unionBound : (Finset.univ.biUnion P).card ≤ C.size := by
    have sub : Finset.univ.biUnion P ⊆ (Finset.range C.gates.length).image (fun j => n+j) := by
      intro g hg
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hg
      have h := private_is_gate C (S i) ((Finset.mem_filter.mp hi).2)
      exact Finset.mem_image.mpr ⟨g-n,Finset.mem_range.mpr (by omega),by omega⟩
    have h := (Finset.card_le_card sub).trans Finset.card_image_le
    simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using h
  rw [Finset.card_biUnion apart] at unionBound
  exact (Finset.sum_le_sum (fun i _ => bound i)).trans unionBound
