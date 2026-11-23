import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_986_aux

open PEqualNP.CircuitLowerBounds
open Finset

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

def value {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wiresFrom gates (List.ofFn x)).getD w false

lemma value_input {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (u : Fin n) :
    value gates x u.val = x u := by
  change (wiresFrom gates (List.ofFn x)).getD u.val false = x u
  rw [getD_wiresFrom_lt]
  · simp [List.getD_eq_getElem?_getD]
  · simp

lemma value_past {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ)
    (h : n + gates.length ≤ w) : value gates x w = false := by
  unfold value
  apply List.getD_eq_default
  simpa [length_wiresFrom] using h

lemma value_gate {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (q : Fin gates.length) :
    value gates x (n + q.val) =
      (gates.get q).op.eval ((gates.get q).inputs.map fun u =>
        if u < n + q.val then value gates x u else false) := by
  simpa [value] using getD_wiresFrom_gate gates (List.ofFn x) q.val q.isLt

lemma and_true (ins : List ℕ) (v : ℕ → Bool) :
    GateOp.and.eval (ins.map v) = true ↔ ∀ u ∈ ins, v u = true := by
  simp [GateOp.eval, List.all_eq_true]

lemma or_true (ins : List ℕ) (v : ℕ → Bool) :
    GateOp.or.eval (ins.map v) = true ↔ ∃ u ∈ ins, v u = true := by
  simp [GateOp.eval, List.any_eq_true]

lemma and_false_child (ins : List ℕ) (v : ℕ → Bool)
    (h : GateOp.and.eval (ins.map v) = false) :
    ∃ u ∈ ins, v u = false := by
  by_contra! no
  have htrue := (and_true ins v).2 fun u hu => Bool.eq_true_of_not_eq_false (no u hu)
  rw [h] at htrue
  contradiction

lemma eval_mono_of_gate {op : GateOp} (h : op = .and ∨ op = .or) (ins : List ℕ)
    (v w : ℕ → Bool) (hv : ∀ u ∈ ins, v u = true → w u = true) :
    op.eval (ins.map v) = true → op.eval (ins.map w) = true := by
  rcases h with rfl | rfl
  · intro ht
    exact (and_true ins w).2 fun u hu => hv u hu ((and_true ins v).1 ht u hu)
  · intro ht
    obtain ⟨u, hu, hval⟩ := (or_true ins v).1 ht
    exact (or_true ins w).2 ⟨u, hu, hv u hu hval⟩

lemma not_eval_head {ins : List ℕ} {u : ℕ} (h : ins.head? = some u) (v : ℕ → Bool) :
    GateOp.not.eval (ins.map v) = !(v u) := by
  cases ins with
  | nil => simp at h
  | cons a ins =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst a
    rfl

def relaxGate (g : Gate) : Gate :=
  match g.op with
  | .not => ⟨.and, []⟩
  | _ => g

lemma relax_and {g : Gate} (h : g.op = .and) : relaxGate g = g := by simp [relaxGate, h]
lemma relax_or {g : Gate} (h : g.op = .or) : relaxGate g = g := by simp [relaxGate, h]
lemma relax_not {g : Gate} (h : g.op = .not) : relaxGate g = ⟨.and, []⟩ := by
  simp [relaxGate, h]

abbrev relaxed (gates : List Gate) : List Gate := gates.map relaxGate

lemma relaxed_get (gates : List Gate) (q : Fin gates.length) :
    (relaxed gates).get ⟨q.val, by simp⟩ = relaxGate (gates.get q) := by simp

lemma relaxed_spec (gates : List Gate)
    (valid : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (g : Gate) (hg : g ∈ relaxed gates) :
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨h, size⟩ := valid a ha
  rcases h with h | h | h
  · simpa [relax_and h, h] using size
  · simpa [relax_or h, h] using size
  · simp [relax_not h]

lemma value_mono {n : ℕ} (gates : List Gate)
    (mono : ∀ g ∈ gates, g.op = .and ∨ g.op = .or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    value gates x w = true → value gates y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · let i : Fin n := ⟨w, hin⟩
      rw [show w = i.val from rfl, value_input, value_input]
      exact hxy i
    by_cases hw : w < n + gates.length
    · let q : Fin gates.length := ⟨w - n, by omega⟩
      have eq : w = n + q.val := by dsimp [q]; omega
      rw [eq, value_gate, value_gate]
      apply eval_mono_of_gate (mono _ (List.get_mem _ _))
      intro u _ hu
      by_cases h : u < n + q.val
      · simp only [h, ite_true] at hu ⊢
        exact ih u (eq ▸ h) hu
      · simp [h] at hu
    · rw [value_past gates x w (by omega)]; simp

lemma relaxed_compare {n : ℕ} (gates : List Gate)
    (valid : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (i0 : Fin gates.length) (hw : ℕ)
    (unique : ∀ q : Fin gates.length, (gates.get q).op = .not → q = i0)
    (head : (gates.get i0).inputs.head? = some hw) (early : hw < n + i0.val)
    (x : Fin n → Bool) (w : ℕ) :
    (value gates x w = true → value (relaxed gates) x w = true) ∧
    (value gates x hw = false → value gates x w = value (relaxed gates) x w) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · let j : Fin n := ⟨w, hin⟩
      rw [show w = j.val from rfl, value_input, value_input]
      simp
    by_cases hw' : w < n + gates.length
    · let q : Fin gates.length := ⟨w - n, by omega⟩
      let q' : Fin (relaxed gates).length := ⟨q.val, by simp⟩
      have eq : w = n + q.val := by dsimp [q]; omega
      have e₁ := value_gate gates x q
      have e₂ := value_gate (relaxed gates) x q'
      change value (relaxed gates) x (n+q.val) =
        ((relaxed gates).get q').op.eval (((relaxed gates).get q').inputs.map fun u =>
          if u < n + q.val then value (relaxed gates) x u else false) at e₂
      rw [show (relaxed gates).get q' = relaxGate (gates.get q) from relaxed_get gates q] at e₂
      rw [eq, e₁, e₂]
      obtain ⟨op, _⟩ := valid _ (List.get_mem _ _ : gates.get q ∈ gates)
      by_cases h : (gates.get q).op = .not
      · have hq : q = i0 := unique q h
        have hh : (gates.get q).inputs.head? = some hw := hq.symm ▸ head
        have ee : hw < n + q.val := hq.symm ▸ early
        rw [relax_not h, h, not_eval_head hh, ite_eq_left ee]
        change ((!value gates x hw) = true → true = true) ∧
          (value gates x hw = false → (!value gates x hw) = true)
        constructor
        · intro _
          rfl
        · intro H
          rw [H]
          rfl
      · have hm : (gates.get q).op = .and ∨ (gates.get q).op = .or :=
          op.elim Or.inl fun z => Or.inr (z.resolve_right h)
        have hr : relaxGate (gates.get q) = gates.get q :=
          hm.elim relax_and relax_or
        rw [hr]
        constructor
        · apply eval_mono_of_gate hm
          intro u _ hu
          split_ifs at hu ⊢ with he
          · exact (ih u (eq ▸ he)).1 hu
        · intro H
          congr 1
          apply List.map_congr_left
          intro u _
          split_ifs with he
          · exact (ih u (eq ▸ he)).2 H
          · rfl
    · have a := value_past gates x w (by omega)
      have b := value_past (relaxed gates) x w (by simpa using (show n+gates.length≤w by omega))
      rw [a,b]
      simp

-- In the directed graph obtained by following chosen gate inputs, every reachable
-- vertex other than the root consumes one of the at most two edges per gate.
lemma charge_count {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (labels : α → Finset β) (large : Finset α) (children : α → Finset α)
    (rank : α → ℕ) (good : α → Prop) (root : α)
    (rootGood : good root)
    (small : ∀ v, good v → v ∉ large → (labels v).card ≤ 1)
    (childCard : ∀ v, v ∈ large → (children v).card ≤ 2)
    (childGood : ∀ v, v ∈ large → ∀ u ∈ children v, good u ∧ rank u < rank v)
    (cover : ∀ v, v ∈ large → labels v ⊆ (children v).biUnion labels) :
    (labels root).card - 1 ≤ large.card := by
  classical
  let step : α → α → Prop := fun v u => v ∈ large ∧ u ∈ children v
  let D : Finset α := univ.filter fun v => Relation.ReflTransGen step root v
  have rootD : root ∈ D := mem_filter.mpr ⟨mem_univ _, Relation.ReflTransGen.refl⟩
  have goodD {u : α} (hu : u ∈ D) : good u := by
    have r := (mem_filter.mp hu).2
    cases r with
    | refl => exact rootGood
    | tail _ h => exact (childGood _ h.1 _ h.2).1
  have exits (v : α) (x : β) (hv : x ∈ labels v) :
      ∃ u, Relation.ReflTransGen step v u ∧ u ∉ large ∧ x ∈ labels u := by
    generalize e : rank v = k
    induction k using Nat.strong_induction_on generalizing v with
    | ind k ih =>
      by_cases h : v ∈ large
      · obtain ⟨u, hu, hx⟩ := mem_biUnion.mp (cover v h hv)
        obtain ⟨y, path, smallY, labelY⟩ :=
          ih (rank u) (e ▸ (childGood v h u hu).2) u hx rfl
        exact ⟨y, (Relation.ReflTransGen.single (show step v u from ⟨h,hu⟩)).trans path,
          smallY, labelY⟩
      · exact ⟨v, Relation.ReflTransGen.refl, h, hv⟩
  have labelBound : (labels root).card ≤ (D \ large).card := by
    apply (card_le_card ?_).trans
      (card_biUnion_le_card_mul (D \ large) labels 1 ?_ |>.trans (by simp))
    · intro x hx
      obtain ⟨u, r, h, hxu⟩ := exits root x hx
      exact mem_biUnion.mpr ⟨u,
        mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, r⟩, h⟩, hxu⟩
    · intro v hv
      exact small v (goodD (mem_sdiff.mp hv).1) (mem_sdiff.mp hv).2
  have edgeBound : (D.erase root).card ≤ (D ∩ large).card * 2 := by
    apply (card_le_card ?_).trans (card_biUnion_le_card_mul (D ∩ large) children 2 ?_)
    · intro w hw
      have rr := (mem_filter.mp (mem_of_mem_erase hw)).2
      cases rr with
      | refl => exact ((mem_erase.mp hw).1 rfl).elim
      | tail rr e =>
        exact mem_biUnion.mpr ⟨_, mem_inter.mpr
          ⟨mem_filter.mpr ⟨mem_univ _, rr⟩, e.1⟩, e.2⟩
    · intro v hv
      exact childCard v (mem_inter.mp hv).2
  have split := card_sdiff_add_card_inter D large
  have erased := card_erase_of_mem rootD
  have largeBound : (D ∩ large).card ≤ large.card := card_le_card inter_subset_right
  omega

abbrev Wire (n : ℕ) (gates : List Gate) := Fin (n + gates.length)

def gateWire {n : ℕ} {gates : List Gate} (q : Fin gates.length) : Wire n gates :=
  ⟨n + q.val, by omega⟩

def singletonInput {n : ℕ} (x : Fin n) : Fin n → Bool :=
  fun z => decide (z = x)

def zeroTest {n : ℕ} (S T : Finset (Fin n)) : Fin n → Bool :=
  fun x => decide (x ∉ S ∧ x ∉ T)

def track {n : ℕ} (S U : Finset (Fin n)) (a x : Fin n) : Prop :=
  x ∉ U ∧ (x ≠ a ∨ a ∈ S)

noncomputable def labels {n : ℕ} (gates : List Gate) (S U : Finset (Fin n))
    (a : Fin n) (w : Wire n gates) : Finset (Fin n) := by
  classical
  exact univ.filter fun x => track S U a x ∧ value gates (singletonInput x) w.val = true

lemma mem_labels {n : ℕ} (gates : List Gate) (S U : Finset (Fin n)) (a x : Fin n)
    (w : Wire n gates) :
    x ∈ labels gates S U a w ↔
      track S U a x ∧ value gates (singletonInput x) w.val = true := by
  classical
  simp [labels]

def goodWire {n : ℕ} (gates : List Gate) (S T : Finset (Fin n))
    (w : Wire n gates) : Prop :=
  value gates (zeroTest S T) w.val = false

noncomputable def bigWires {n : ℕ} (gates : List Gate) (S T : Finset (Fin n))
    (a : Fin n) : Finset (Wire n gates) := by
  classical
  exact univ.filter fun w =>
    goodWire gates S T w ∧ 2 ≤ (labels gates S (T.erase a) a w).card

lemma mem_big {n : ℕ} (gates : List Gate) (S T : Finset (Fin n))
    (a : Fin n) (w : Wire n gates) :
    w ∈ bigWires gates S T a ↔
      goodWire gates S T w ∧ 2 ≤ (labels gates S (T.erase a) a w).card := by
  classical
  simp [bigWires]

lemma labels_subset {n : ℕ} (gates : List Gate)
    (mono : ∀ g ∈ gates, g.op = .and ∨ g.op = .or)
    (S T : Finset (Fin n)) (a : Fin n) (w : Wire n gates)
    (good : goodWire gates S T w) : labels gates S (T.erase a) a w ⊆ S := by
  classical
  intro x hx
  obtain ⟨⟨hxU, relevant⟩, hxw⟩ := (mem_labels gates S (T.erase a) a x w).mp hx
  by_contra hxS
  have hne : x ≠ a := by
    intro e
    subst x
    exact hxS (relevant.resolve_left (fun h => h rfl))
  have hxT : x ∉ T := fun hT => hxU (mem_erase.mpr ⟨hne, hT⟩)
  have hmono : ∀ i, singletonInput x i = true → zeroTest S T i = true := by
    intro i hi
    obtain rfl : i = x := by simpa [singletonInput] using hi
    simp [zeroTest, hxS, hxT]
  have ht := value_mono gates mono _ _ hmono w.val hxw
  exact Bool.noConfusion (good.symm.trans ht)

lemma big_not_input {n : ℕ} (gates : List Gate) (S T : Finset (Fin n))
    (a : Fin n) (w : Wire n gates) (h : w ∈ bigWires gates S T a) : n ≤ w.val := by
  classical
  by_contra! hn
  let x : Fin n := ⟨w.val, hn⟩
  have sub : labels gates S (T.erase a) a w ⊆ {x} := by
    intro i hi
    have e := ((mem_labels gates S (T.erase a) a i w).mp hi).2
    change value gates (singletonInput i) x.val = true at e
    rw [value_input] at e
    have ee : x = i := by simpa [singletonInput] using e
    simpa using ee.symm
  have bound := card_le_card sub
  simpa using (show (2 : ℕ) ≤ ({x} : Finset (Fin n)).card from
    ((mem_big gates S T a w).mp h).2.trans bound)

lemma choose_children {n : ℕ} (gates : List Gate)
    (valid : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (S T : Finset (Fin n)) (a : Fin n) (w : Wire n gates)
    (big : w ∈ bigWires gates S T a) :
    ∃ children : Finset (Wire n gates), children.card ≤ 2 ∧
      (∀ u ∈ children, goodWire gates S T u ∧ u.val < w.val) ∧
      labels gates S (T.erase a) a w ⊆ children.biUnion (labels gates S (T.erase a) a) := by
  classical
  have hn := big_not_input gates S T a w big
  let q : Fin gates.length := ⟨w.val-n, by have := w.isLt; omega⟩
  have eq : w.val = n+q.val := by dsimp [q]; omega
  have gateEq (x : Fin n → Bool) :
      value gates x w.val = (gates.get q).op.eval ((gates.get q).inputs.map
        fun j => if j < w.val then value gates x j else false) := by
    conv_lhs => rw [eq, value_gate]
    rw [← eq]
  obtain ⟨good, many⟩ := (mem_big gates S T a w).mp big
  have hfalse : value gates (zeroTest S T) w.val = false := good
  obtain ⟨op, fan⟩ := valid _ (List.get_mem _ _ : gates.get q ∈ gates)
  rcases op with h | h
  · rw [gateEq, h] at hfalse
    obtain ⟨u, hu, uf⟩ := and_false_child _ _ hfalse
    have pass (x : Fin n) (hx : x ∈ labels gates S (T.erase a) a w) :
        (if u < w.val then value gates (singletonInput x) u else false) = true := by
      have hxv := ((mem_labels gates S (T.erase a) a x w).mp hx).2
      rw [gateEq, h] at hxv
      exact (and_true _ _).mp hxv u hu
    obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < (labels gates S (T.erase a) a w).card)
    have huLt : u < w.val := by
      by_contra H
      simpa [H] using pass x hx
    let v : Wire n gates := ⟨u, huLt.trans w.isLt⟩
    refine ⟨{v}, by simp, ?_, ?_⟩
    · intro i hi
      obtain rfl : i = v := by simpa using hi
      exact ⟨by simpa [goodWire, v, huLt] using uf, huLt⟩
    · intro i hi
      refine mem_biUnion.mpr ⟨v, mem_singleton_self _, (mem_labels gates S (T.erase a) a i v).mpr ⟨?_, ?_⟩⟩
      · exact ((mem_labels gates S (T.erase a) a i w).mp hi).1
      · simpa [v, huLt] using pass i hi
  · let children : Finset (Wire n gates) :=
      univ.filter fun u => u.val ∈ (gates.get q).inputs ∧ u.val < w.val
    have small : children.card ≤ (gates.get q).inputs.toFinset.card := by
      apply card_le_card_of_injOn (fun x : Wire n gates => x.val)
      · intro u hu
        exact List.mem_toFinset.mpr (mem_filter.mp hu).2.1
      · intro u _ v _ eq
        exact Fin.ext eq
    refine ⟨children, small.trans (Nat.le_trans (List.toFinset_card_le _) fan), ?_, ?_⟩
    · intro u hu
      obtain ⟨hm, hl⟩ := (mem_filter.mp hu).2
      refine ⟨?_, hl⟩
      by_contra he
      have hv : value gates (zeroTest S T) u.val = true := Bool.eq_true_of_not_eq_false he
      have hh := (or_true (gates.get q).inputs
        (fun j => if j < w.val then value gates (zeroTest S T) j else false)).mpr
          ⟨u.val, hm, by rw [ite_eq_left hl]; exact hv⟩
      rw [gateEq, h, hh] at hfalse
      contradiction
    · intro x hx
      obtain ⟨relevant, ht⟩ := (mem_labels gates S (T.erase a) a x w).mp hx
      rw [gateEq, h] at ht
      obtain ⟨u, hu, uv⟩ := (or_true _ _).mp ht
      have ul : u < w.val := by
        by_contra H
        simp [H] at uv
      let v : Wire n gates := ⟨u, ul.trans w.isLt⟩
      refine mem_biUnion.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hu, ul⟩, ?_⟩
      exact (mem_labels gates S (T.erase a) a x v).mpr ⟨relevant, by simpa [v, ul] using uv⟩

lemma output_charge {n : ℕ} (gates : List Gate)
    (valid : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (S T : Finset (Fin n)) (a : Fin n) (w : Wire n gates) (good : goodWire gates S T w) :
    (labels gates S (T.erase a) a w).card - 1 ≤ (bigWires gates S T a).card := by
  classical
  let large := bigWires gates S T a
  let lbs := labels gates S (T.erase a) a
  let children (v : Wire n gates) : Finset (Wire n gates) :=
    if hv : v ∈ large then (choose_children gates valid S T a v hv).choose else ∅
  have spec (v : Wire n gates) (hv : v ∈ large) :
      (children v).card ≤ 2 ∧
      (∀ u ∈ children v, goodWire gates S T u ∧ u.val < v.val) ∧
      lbs v ⊆ (children v).biUnion lbs := by
    simpa [children, hv, lbs] using (choose_children gates valid S T a v hv).choose_spec
  apply charge_count lbs large children (fun v => v.val) (goodWire gates S T) w good
  · intro v gv hv
    have notbig : ¬ 2 ≤ (lbs v).card := fun h => hv ((mem_big gates S T a v).mpr ⟨gv,h⟩)
    omega
  · exact fun v hv => (spec v hv).1
  · exact fun v hv => (spec v hv).2.1
  · exact fun v hv => (spec v hv).2.2

lemma labels_rel {n : ℕ} (gates : List Gate) (S R U : Finset (Fin n))
    (a : Fin n) (w : Wire n gates) (h : a ∈ S → a ∈ R) :
    labels gates S U a w ⊆ labels gates R U a w := by
  intro x hx
  obtain ⟨⟨hu, hx⟩, hv⟩ := (mem_labels gates S U a x w).mp hx
  exact (mem_labels gates R U a x w).mpr ⟨⟨hu, hx.imp_right h⟩,hv⟩

lemma gateWire_excluded {n : ℕ} (gates : List Gate) (i0 : Fin gates.length)
    (hNot : (gates.get i0).op = .not) (S T : Finset (Fin n)) (a : Fin n) :
    gateWire (n := n) (gates := relaxed gates) ⟨i0.val, by simp⟩ ∉
      bigWires (relaxed gates) S T a := by
  intro h
  have e := (mem_big _ _ _ _ _).mp h
  have v := value_gate (relaxed gates) (zeroTest S T) ⟨i0.val, by simp⟩
  rw [relaxed_get gates i0, relax_not hNot] at v
  change value (relaxed gates) (zeroTest S T) (n+i0.val) = true at v
  exact Bool.noConfusion (e.1.symm.trans v)

lemma incidence {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin n)) :
    (∑ o, (S o ∩ U).card) =
      ∑ u ∈ U, (univ.filter fun o : Fin m => u ∈ S o).card := by
  classical
  calc
    _ = ∑ o, ∑ u ∈ U, if u ∈ S o then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro o _
      rw [sum_boole]
      congr 1
      ext u
      simp [and_comm]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro u _
      rw [sum_boole]
      rfl

end PEqualNP.Outside.L_meta_986_aux

open PEqualNP.Outside.L_meta_986_aux Finset in
theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  intro n m S gates out i0 hw T a _ linear valid unique hNot head early output clause _ _
  change (∀ o x, value gates x (out o) = _) at output
  change (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → value gates y hw = false) at clause
  let U := T.erase a
  let r := relaxed gates
  let B := fun o : Fin m => bigWires r (S o) T a
  have vR (g) (hg : g ∈ r) := relaxed_spec gates valid g hg
  have mono (g) (hg : g ∈ r) := (vR g hg).1
  have size_charge (o : Fin m) : (S o \ U).card - 1 ≤ (B o).card := by
    by_cases hsize : 2 ≤ (S o \ U).card
    · obtain ⟨b, hb⟩ := card_pos.mp (by omega : 0 < (S o \ U).card)
      have unit_true {x : Fin n} (hx : x ∈ S o) :
          value r (singletonInput x) (out o) = true := by
        have h := output o (singletonInput x)
        have hxTrue : ∃ v ∈ S o, singletonInput x v = true := ⟨x,hx,by simp [singletonInput]⟩
        have hEval : value gates (singletonInput x) (out o) = true := by rw [h, decide_eq_true hxTrue]
        exact (relaxed_compare gates valid i0 hw unique head early _ _).1 hEval
      have wireBound : out o < n + r.length := by
        by_contra! h
        have e := unit_true (mem_sdiff.mp hb).1
        rw [show value r (singletonInput b) (out o) = false from value_past _ _ _ h] at e
        contradiction
      let w : Wire n r := ⟨out o, wireBound⟩
      have hcl := clause (zeroTest (S o) T) (by intro t ht; simp [zeroTest, ht])
      have hOrig : value gates (zeroTest (S o) T) (out o) = false := by
        rw [output]
        apply decide_eq_false
        rintro ⟨t, ht, hv⟩
        simp [zeroTest, ht] at hv
      have good : goodWire r (S o) T w := by
        change value r (zeroTest (S o) T) (out o) = false
        rw [← (relaxed_compare gates valid i0 hw unique head early _ _).2 hcl]
        exact hOrig
      have labelEq : labels r (S o) U a w = S o \ U := by
        ext x
        constructor
        · intro hh
          exact mem_sdiff.mpr ⟨labels_subset r mono (S o) T a w good hh,
            ((mem_labels r (S o) U a x w).mp hh).1.1⟩
        · intro hh
          obtain ⟨hx, hU⟩ := mem_sdiff.mp hh
          apply (mem_labels r (S o) U a x w).mpr
          refine ⟨⟨hU, ?_⟩, unit_true hx⟩
          by_cases he : x = a
          · exact Or.inr (he ▸ hx)
          · exact Or.inl he
      simpa [U, B, labelEq] using output_charge r vR (S o) T a w good
    · have e : (S o \ U).card - 1 = 0 := by omega
      rw [e]
      exact Nat.zero_le _
  have disjoint : ((univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint B := by
    intro o ho p hp ne
    apply disjoint_left.mpr
    intro w wo wp
    have eo := (mem_big r (S o) T a w).mp wo
    have ep := (mem_big r (S p) T a w).mp wp
    have lo := labels_subset r mono (S o) T a w eo.1
    have lp := labels_subset r mono (S p) T a w ep.1
    by_cases h : a ∈ S o → a ∈ S p
    · have sub : labels r (S o) U a w ⊆ S o ∩ S p :=
        subset_inter lo ((labels_rel r (S o) (S p) U a w h).trans lp)
      exact (by decide : ¬ 2 ≤ (1 : ℕ)) (eo.2.trans ((card_le_card sub).trans (linear o p ne)))
    · have h' : a ∈ S p → a ∈ S o := by
        intro hp
        exact False.elim (h fun _ => hp)
      have sub : labels r (S p) U a w ⊆ S o ∩ S p :=
        subset_inter ((labels_rel r (S p) (S o) U a w h').trans lo) lp
      exact (by decide : ¬ 2 ≤ (1 : ℕ)) (ep.2.trans ((card_le_card sub).trans (linear o p ne)))
  have cap : (univ.biUnion B).card ≤ gates.length - 1 := by
    let j0 : Fin r.length := ⟨i0.val, by simp [r]⟩
    have bound : univ.biUnion B ⊆ (univ.erase j0).image (gateWire (n := n) (gates := r)) := by
      intro w hw
      obtain ⟨o, _, hwo⟩ := mem_biUnion.mp hw
      have hn := big_not_input r (S o) T a w hwo
      let j : Fin r.length := ⟨w.val-n, by have := w.isLt; omega⟩
      have e : gateWire (n := n) (gates := r) j = w := by
        apply Fin.ext
        change n+(w.val-n)=w.val
        omega
      have ne : j ≠ j0 := by
        intro he
        have hh := gateWire_excluded gates i0 hNot (S o) T a
        apply hh
        change gateWire (n := n) (gates := r) j0 ∈ B o
        simpa only [←he, e] using hwo
      exact mem_image.mpr ⟨j, mem_erase.mpr ⟨ne, mem_univ _⟩, e⟩
    have h := (card_le_card bound).trans card_image_le
    simpa [r, card_erase_of_mem (mem_univ j0)] using h
  have d : (∑ o, ((S o \ U).card - 1)) ≤ gates.length - 1 := by
    calc
      _ ≤ ∑ o, (B o).card := sum_le_sum fun o _ => size_charge o
      _ = (univ.biUnion B).card := (card_biUnion disjoint).symm
      _ ≤ _ := cap
  have pointwise (o : Fin m) :
      (S o).card - 1 ≤ ((S o \ U).card - 1) + (S o ∩ U).card := by
    have e := card_sdiff_add_card_inter (S o) U
    omega
  have sum := sum_le_sum (fun o (_ : o ∈ (univ : Finset (Fin m))) => pointwise o)
  rw [sum_add_distrib, incidence S U] at sum
  have nonempty := i0.isLt
  change _ ≤ gates.length + ∑ u ∈ U, _
  omega
