import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_270_aux

open PEqualNP.CircuitLowerBounds
abbrev Input (n : Nat) := Fin n → Bool
abbrev Sig (n : Nat) := Input n → Bool
-- Each wire stores its Boolean function and its value under an auxiliary evaluation.
abbrev W (n : Nat) := Sig n × Bool
def blank {n : Nat} : W n := (fun _ => false,false)
def supp {n : Nat} (f : Sig n) : Finset (Fin n) :=
  Finset.univ.filter (fun p => f (fun q => decide (q=p)))
-- A gate can be private to at most one output because output sets meet in at most one point.
abbrev privateFor {n : Nat} (S : Finset (Fin n)) (f : Sig n) : Prop :=
  supp f ⊆ S ∧ 2 ≤ (supp f).card
def Mono {n : Nat} (f : Sig n) : Prop :=
  ∀ x y : Input n, (∀ p, x p = true → y p = true) → f x = true → f y = true
def escapes {n : Nat} (S : Finset (Fin n)) (f : Sig n) : Bool := decide (¬ supp f ⊆ S)
def leafOK {n : Nat} (S : Finset (Fin n)) (b : Bool) (f : Sig n) : Prop :=
  Mono f ∧ ¬ privateFor S f ∧ escapes S f = b
-- A common wire value can be forced by fixing a finite set of nonprivate leaves.
def cert {n : Nat} (S : Finset (Fin n)) (L : List (W n)) (k : Nat) : Prop :=
  ∀ (b : Bool) (Q : Finset Nat), (∀ i ∈ Q, (L.getD i blank).2 = b) →
    ∃ U : Finset (Sig n), U.card ≤ Q.card + k ∧ (∀ f ∈ U, leafOK S b f) ∧
      ∀ x, (∀ f ∈ U, f x = b) → ∀ i ∈ Q, (L.getD i blank).1 x = b
def raw {n : Nat} (L : List (W n)) (g : Gate) : Sig n :=
  fun x => g.op.eval (g.inputs.map (fun i => (L.getD i blank).1 x))
def tag {n : Nat} (L : List (W n)) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => (L.getD i blank).2))
def appendGate {n : Nat} (S : Finset (Fin n)) (L : List (W n)) (g : Gate) : List (W n) :=
  let f := raw L g
  L ++ [(f,if privateFor S f then tag L g else escapes S f)]
def primary {n : Nat} (S : Finset (Fin n)) : List (W n) :=
  List.ofFn (fun i : Fin n => ((fun x : Input n => x i),escapes S (fun x => x i)))
def run {n : Nat} (S : Finset (Fin n)) (gs : List Gate) : List (W n) :=
  gs.foldl (appendGate S) (primary S)
def flags {n : Nat} (S : Finset (Fin n)) (gs : List Gate) : Finset Nat :=
  (Finset.range gs.length).filter (fun j => privateFor S (((run S gs).getD (n+j) blank).1))

private theorem proj_supp {n : Nat} (i : Fin n) :
    supp (fun x : Input n => x i) = {i} := by
  ext p
  simp [supp, eq_comm]

private theorem primary_leaf {n : Nat} (S : Finset (Fin n)) (i : Nat) :
    leafOK S ((primary S).getD i blank).2 ((primary S).getD i blank).1 := by
  by_cases hi : i < n
  · have he : (primary S).getD i blank =
        ((fun x : Input n => x ⟨i,hi⟩),escapes S (fun x => x ⟨i,hi⟩)) := by
      simp [primary, List.getD_eq_getElem?_getD, hi]
    rw [he]
    refine ⟨?_, ?_, rfl⟩
    · intro x y h; exact h ⟨i,hi⟩
    · simp [privateFor, proj_supp]
  · have he : (primary S).getD i blank = blank := by
      simp [primary, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi : (List.ofFn (fun j : Fin n => ((fun x : Input n => x j), escapes S (fun x => x j)))).length ≤ i)]
    rw [he]
    simp [blank, leafOK, Mono, privateFor, escapes, supp]

theorem certInit {n : Nat} (S : Finset (Fin n)) : cert S (primary S) 0 := by
  classical
  intro b Q hQ
  refine ⟨Q.image (fun i => ((primary S).getD i blank).1), ?_, ?_, ?_⟩
  · simpa using Finset.card_image_le (s := Q) (f := fun i => ((primary S).getD i blank).1)
  · intro f hf
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
    exact hQ i hi ▸ primary_leaf S i
  · intro x hx i hi
    exact hx _ (Finset.mem_image_of_mem _ hi)

private theorem semSnoc {n : Nat} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    run S (gs ++ [g]) = appendGate S (run S gs) g := by
  simp [run, List.foldl_append]

theorem runLength {n : Nat} (S : Finset (Fin n)) (gs : List Gate) :
    (run S gs).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run, primary]
  | append_singleton gs g ih =>
    simp [semSnoc, appendGate, ih, Nat.add_assoc]

private theorem semMap {n : Nat} (S : Finset (Fin n)) (gs : List Gate) (x : Input n) :
    (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)) =
    (run S gs).map (fun w => w.1 x) := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires, run, primary, List.map_ofFn, Function.comp_def]
  | append_singleton gs g ih =>
    have hv (i : Nat) : ((run S gs).map (fun w => w.1 x)).getD i false =
        ((run S gs).getD i blank).1 x := List.getD_map _ blank (fun w => w.1 x)
    have hs : Circuit.wires ⟨gs ++ [g], 0⟩ (List.ofFn x) =
        (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)) ++
          [g.op.eval (g.inputs.map (fun i => (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false))] := by
      simp [Circuit.wires, List.foldl_append]
    simp only [hs, ih, hv, semSnoc, appendGate, List.map_append, List.map_cons, List.map_nil, raw]

theorem runRead {n : Nat} (S : Finset (Fin n)) (gs : List Gate) (x : Input n) (i : Nat) :
    ((Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false) = ((run S gs).getD i blank).1 x := by
  rw [semMap S gs x]
  exact List.getD_map _ blank (fun w => w.1 x)

private theorem semGetMono {n : Nat} {L : List (W n)} (h : ∀ t ∈ L, Mono t.1) (i : Nat) :
    Mono (L.getD i blank).1 := by
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro x y hxy hx
    exact hx

private theorem semGateMono {n : Nat} {L : List (W n)} {g : Gate}
    (h : ∀ t ∈ L, Mono t.1) (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    Mono (raw L g) := by
  obtain ⟨i, j, hij⟩ := List.length_eq_two.mp hg.2
  intro x y hxy hgate
  rcases hg.1 with ha | ho
  · simp [raw, ha, hij, GateOp.eval] at hgate ⊢
    exact ⟨semGetMono h i x y hxy hgate.1, semGetMono h j x y hxy hgate.2⟩
  · simp [raw, ho, hij, GateOp.eval] at hgate ⊢
    exact hgate.imp (semGetMono h i x y hxy) (semGetMono h j x y hxy)

private theorem semAllMono {n : Nat} (S : Finset (Fin n)) (gs : List Gate)
    (hgs : ∀ a ∈ gs, (a.op = .and ∨ a.op = .or) ∧ a.inputs.length = 2) :
    ∀ t ∈ run S gs, Mono t.1 := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro t ht
    change t ∈ List.ofFn _ at ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact fun x y hxy hx => hxy i hx
  | append_singleton gs g ih =>
    have hs := ih (fun a ha => hgs a (List.mem_append_left _ ha))
    have hg := hgs g (by simp)
    intro t ht
    rw [semSnoc] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hs _ ht
    · obtain rfl := List.mem_singleton.mp ht
      exact semGateMono hs hg

theorem rawMono {n : Nat} (S : Finset (Fin n)) (gs : List Gate) (g : Gate)
    (hgs : ∀ a ∈ gs, (a.op = .and ∨ a.op = .or) ∧ a.inputs.length = 2)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    Mono (raw (run S gs) g) := semGateMono (semAllMono S gs hgs) hg

theorem flagsSnoc {n : Nat} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    (flags S (gs ++ [g])).card = (flags S gs).card +
      (if privateFor S (raw (run S gs) g) then 1 else 0) := by
  let w : W n := (raw (run S gs) g, if privateFor S (raw (run S gs) g)
    then tag (run S gs) g else escapes S (raw (run S gs) g))
  have hs : run S (gs ++ [g]) = run S gs ++ [w] := semSnoc _ _ _
  have hf : (Finset.range gs.length).filter (fun j =>
      privateFor S (((run S gs ++ [w]).getD (n+j) blank).1)) = flags S gs := by
    apply Finset.filter_congr
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [List.getD_append _ _ _ _ (by rw [runLength]; omega)]
  have hl : ((run S gs ++ [w]).getD (n+gs.length) blank).1 = raw (run S gs) g := by
    rw [← runLength S gs, List.getD_eq_getElem _ _ (by simp)]
    simp [w]
  have hn : gs.length ∉ flags S gs := by simp [flags]
  simp only [flags, List.length_append, List.length_singleton, Finset.range_add_one,
    Finset.filter_insert, hs, hf, hl]
  change (if privateFor S (raw (run S gs) g) then insert gs.length (flags S gs)
    else flags S gs).card = (flags S gs).card +
      (if privateFor S (raw (run S gs) g) then 1 else 0)
  split
  · exact Finset.card_insert_of_notMem hn
  · rfl

private theorem frontierReadOld {α : Type} (L : List α) (v d : α) {i : Nat}
    (hi : i ≠ L.length) : (L ++ [v]).getD i d = L.getD i d := by
  by_cases h : i < L.length
  · exact List.getD_append L [v] d i h
  · have ha : (L ++ [v]).length ≤ i := by simp; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none ha,
      List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem frontierReadLast {α : Type} (L : List α) (v d : α) :
    (L ++ [v]).getD L.length d = v := by
  simp [List.getD_eq_getElem?_getD]

private theorem frontierBool (a b c d t : Bool) (ha : a = t → c = t) (hb : b = t → d = t) :
    ((a && b) = t → (c && d) = t) ∧ ((a || b) = t → (c || d) = t) := by
  revert a b c d t
  decide

private theorem frontierPred {n : Nat} (L : List (W n)) (g : Gate)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (b : Bool) (ht : tag L g = b) :
    ∃ P : Finset Nat, P.card ≤ 2 ∧ (∀ i ∈ P, (L.getD i blank).2 = b) ∧
      ∀ x, (∀ i ∈ P, (L.getD i blank).1 x = b) → raw L g x = b := by
  obtain ⟨i, j, heq⟩ := List.length_eq_two.mp hg.2
  let P := ({i,j} : Finset Nat).filter (fun q => (L.getD q blank).2 = b)
  refine ⟨P, (Finset.card_filter_le ..).trans Finset.card_le_two,
    fun q hq => (Finset.mem_filter.mp hq).2, ?_⟩
  intro x hx
  have hi : (L.getD i blank).2 = b → (L.getD i blank).1 x = b :=
    fun hi => hx i (Finset.mem_filter.mpr ⟨by simp, hi⟩)
  have hj : (L.getD j blank).2 = b → (L.getD j blank).1 x = b :=
    fun hj => hx j (Finset.mem_filter.mpr ⟨by simp, hj⟩)
  have hh := frontierBool _ _ _ _ _ hi hj
  rcases hg.1 with ha | ho
  · simp [tag, raw, ha, heq, GateOp.eval] at ht ⊢
    exact hh.1 ht
  · simp [tag, raw, ho, heq, GateOp.eval] at ht ⊢
    exact hh.2 ht

-- Expanding a private binary gate adds at most one extra leaf to the frontier.
theorem certStep {n k : Nat} (S : Finset (Fin n)) (L : List (W n)) (g : Gate)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (hr : Mono (raw L g))
    (h : cert S L k) :
    cert S (appendGate S L g) (k + if privateFor S (raw L g) then 1 else 0) := by
  classical
  intro b Q htag
  have prev {i : Nat} (hi : i ≠ L.length) : (appendGate S L g).getD i blank = L.getD i blank :=
    frontierReadOld L _ blank hi
  have last : (appendGate S L g).getD L.length blank =
      (raw L g, if privateFor S (raw L g) then tag L g else escapes S (raw L g)) :=
    frontierReadLast L _ blank
  by_cases hn : L.length ∉ Q
  · have hne : ∀ i ∈ Q, i ≠ L.length := fun _ hi hlen => hn (hlen ▸ hi)
    obtain ⟨U, hu, hf, hx⟩ := h b Q (fun i hi => (prev (hne i hi)) ▸ htag i hi)
    refine ⟨U, by omega, hf, ?_⟩
    intro x he i hi
    rw [prev (hne i hi)]
    exact hx x he i hi
  have hin : L.length ∈ Q := by simpa using hn
  let R := Q.erase L.length
  have hcard : R.card + 1 = Q.card := Finset.card_erase_add_one hin
  have hrt : ∀ i ∈ R, (L.getD i blank).2 = b := by
    intro i hi
    obtain ⟨hne, hq⟩ := Finset.mem_erase.mp hi
    rw [← prev hne]
    exact htag i hq
  have hlast := htag L.length hin
  rw [last] at hlast
  by_cases hp : privateFor S (raw L g)
  · simp only [ite_eq_left hp] at hlast ⊢
    obtain ⟨P, hpc, hpt, hpf⟩ := frontierPred L g hg b hlast
    obtain ⟨U, hu, hf, hx⟩ := h b (R ∪ P) (by
      intro i hi
      rcases Finset.mem_union.mp hi with hr | hp
      · exact hrt i hr
      · exact hpt i hp)
    have hbound := Finset.card_union_le R P
    refine ⟨U, by omega, hf, ?_⟩
    intro x he i hi
    by_cases hi' : i = L.length
    · subst i
      rw [last]
      exact hpf x (fun q hq => hx x he q (Finset.mem_union_right R hq))
    · rw [prev hi']
      exact hx x he i (Finset.mem_union_left P (Finset.mem_erase.mpr ⟨hi', hi⟩))
  · simp only [ite_eq_right hp, Nat.add_zero] at hlast ⊢
    obtain ⟨U, hu, hf, hx⟩ := h b R hrt
    have hbound := Finset.card_insert_le (raw L g) U
    refine ⟨insert (raw L g) U, by omega, ?_, ?_⟩
    · intro f hmem
      rcases Finset.mem_insert.mp hmem with rfl | hmem
      · exact ⟨hr, hp, hlast⟩
      · exact hf f hmem
    · intro x he i hi
      by_cases hi' : i = L.length
      · subst i
        rw [last]
        exact he _ (Finset.mem_insert_self ..)
      · rw [prev hi']
        exact hx x (fun f hmem => he f (Finset.mem_insert_of_mem hmem)) i
          (Finset.mem_erase.mpr ⟨hi', hi⟩)

-- A false frontier covers the desired singleton inputs. A true frontier supplies an outside test.
theorem singleCost {n k cost ci : Nat} (S : Finset (Fin n)) (L : List (W n))
    (out : Nat) (hc : cert S L cost) (hs : supp (L.getD out blank).1 = S)
    (hz : ∀ x : Input n, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → (L.getD out blank).1 x = false)
    (hk : ci ≤ k) (hcard : ci+1 ≤ S.card) : ci ≤ cost := by
  classical
  by_contra! hcost
  cases ht : (L.getD out blank).2 with
  | false =>
    obtain ⟨U, hU, hleaf, hforces⟩ := hc false {out} (by simpa using ht)
    simp only [Finset.card_singleton] at hU
    have hsmall : ∀ f ∈ U, (supp f).card ≤ 1 := by
      intro f hf
      have hsub : supp f ⊆ S := by simpa [escapes] using (hleaf f hf).2.2
      have hnot := (hleaf f hf).2.1
      by_contra! hsize
      exact hnot ⟨hsub, by omega⟩
    have hcover : S ⊆ U.biUnion supp := by
      intro q hq
      by_contra hmiss
      have hall : ∀ f ∈ U, f (fun p => decide (p = q)) = false := by
        intro f hf
        cases he : f (fun p => decide (p = q)) with
        | false => rfl
        | true =>
          exact False.elim (hmiss (Finset.mem_biUnion.mpr ⟨f, hf, by simpa [supp] using he⟩))
      have hf := hforces _ hall out (by simp)
      have hout : q ∈ supp (L.getD out blank).1 := hs.symm ▸ hq
      have htrue : (L.getD out blank).1 (fun p => decide (p = q)) = true := by
        simpa [supp] using hout
      exact Bool.noConfusion (htrue.symm.trans hf)
    have hsize : S.card ≤ U.card := calc
      S.card ≤ (U.biUnion supp).card := Finset.card_le_card hcover
      _ ≤ ∑ f ∈ U, (supp f).card := Finset.card_biUnion_le
      _ ≤ ∑ _f ∈ U, 1 := Finset.sum_le_sum hsmall
      _ = U.card := by simp
    omega
  | true =>
    obtain ⟨U, hU, hleaf, hforces⟩ := hc true {out} (by simpa using ht)
    simp only [Finset.card_singleton] at hU
    have hwit (f) (hf : f ∈ U) : ∃ q, q ∈ supp f ∧ q ∉ S := by
      have hsub : ¬ supp f ⊆ S := by simpa [escapes] using (hleaf f hf).2.2
      exact Finset.not_subset.mp hsub
    choose w hmem hout using hwit
    let T := U.attach.image (fun f => w f.1 f.2)
    let x : Input n := fun q => decide (q ∈ T)
    have hT : T.card ≤ U.card := by
      simpa [T] using (Finset.card_image_le (s := U.attach) (f := fun f => w f.1 f.2))
    have hweight : (Finset.univ.filter (fun q => x q = true)).card ≤ k := by
      have heq : (Finset.univ.filter (fun q => x q = true)) = T := by ext q; simp [x]
      rw [heq]
      omega
    have hzero : ∀ q ∈ S, x q = false := by
      intro q hq
      simp only [x, decide_eq_false_iff_not]
      intro hinc
      obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hinc
      exact hout f.1 f.2 hq
    have hone : ∀ f ∈ U, f x = true := by
      intro f hf
      have hsing : f (fun q => decide (q = w f hf)) = true := by
        simpa [supp] using hmem f hf
      apply (hleaf f hf).1 _ x ?_ hsing
      intro q hq
      have heq : q = w f hf := of_decide_eq_true hq
      subst q
      apply decide_eq_true
      exact Finset.mem_image.mpr ⟨⟨f, hf⟩, by simp, rfl⟩
    have hpos := hforces x hone out (by simp)
    have hneg := hz x hweight hzero
    exact Bool.noConfusion (hpos.symm.trans hneg)

private theorem runCert {n : Nat} (S : Finset (Fin n)) (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    cert S (run S gs) (flags S gs).card := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run, flags] using certInit S
  | append_singleton gs g ih =>
    have hprefix : ∀ a ∈ gs, (a.op = .and ∨ a.op = .or) ∧ a.inputs.length = 2 :=
      fun a ha => hgs a (List.mem_append_left _ ha)
    have hg := hgs g (by simp)
    rw [flagsSnoc]
    simpa [run, List.foldl_append] using
      certStep S (run S gs) g hg (rawMono S gs g hprefix hg) (ih hprefix)

-- Each charged gate belongs to a disjoint collection of indices.
private theorem sumFlags {n m : Nat} (S : Fin m → Finset (Fin n)) (gs : List Gate)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (∑ i, (flags (S i) gs).card) ≤ gs.length := by
  classical
  have hd : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => flags (S i) gs) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro t hi hj
    have h₁ := (Finset.mem_filter.mp hi).2
    have h₂ := (Finset.mem_filter.mp hj).2
    have he : ((run (S i) gs).getD (n+t) blank).1 =
        ((run (S j) gs).getD (n+t) blank).1 := by
      funext x
      exact (runRead (S i) gs x _).symm.trans (runRead (S j) gs x _)
    rw [← he] at h₂
    have ht := Finset.card_le_card (Finset.subset_inter h₁.1 h₂.1)
    have hm := h₁.2
    have hu := h i j hij
    omega
  rw [← Finset.card_biUnion hd]
  calc
    _ ≤ (Finset.range gs.length).card := by
      apply Finset.card_le_card
      intro t ht
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ht
      exact (Finset.mem_filter.mp hi).1
    _ = _ := Finset.card_range _

end PEqualNP.Outside.L_meta_270_aux

open PEqualNP.Outside.L_meta_270_aux

theorem PEqualNP.Outside.L_meta_270 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c hinter _ hg hs hz hk hcard
  calc
    (∑ i, c i) ≤ ∑ i, (flags (S i) C.gates).card := by
      apply Finset.sum_le_sum
      intro i _
      apply singleCost (S i) (run (S i) C.gates) (o i) (runCert (S i) C.gates hg)
      · ext p
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← runRead]
        exact hs i p
      · intro x hx hy
        rw [← runRead]
        exact hz i x hx hy
      · exact hk i
      · exact hcard i
    _ ≤ C.size := sumFlags S C.gates hinter
