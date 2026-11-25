import Mathlib
import PEqualNP.Defs

-- The lemmas from run to build are copied from the merged file L_meta_4342 of this project.

namespace PEqualNP.Outside.L_meta_6734

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def AO (n : ℕ) (ds : List Gate) : Prop :=
  (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < n + j

def Rep (n : ℕ) (ds : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c, ∀ y, f y = c) ∨
    ∃ k < n + ds.length, ∀ y, f y = (run ds (List.ofFn y)).getD k false

theorem rep_app (n : ℕ) (ds : List Gate) (g : Gate) (f : (Fin n → Bool) → Bool)
    (h : Rep n ds f) : Rep n (ds ++ [g]) f := by
  rcases h with h | ⟨k, hk, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
    rw [h y, run_prefix _ _ _ _ (by simpa using hk)]

theorem rep_two (n : ℕ) (ds : List Gate) (hds : AO n ds) (o : GateOp)
    (ho : o = GateOp.and ∨ o = GateOp.or) (u v : (Fin n → Bool) → Bool)
    (hu : Rep n ds u) (hv : Rep n ds v) :
    ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧
      Rep n (ds ++ hs) fun y => o.eval [u y, v y] := by
  have triv : ∀ w : (Fin n → Bool) → Bool, Rep n ds w → (∀ y, o.eval [u y, v y] = w y) →
      ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧
      Rep n (ds ++ hs) fun y => o.eval [u y, v y] := by
    intro w hw e
    refine ⟨[], by simp, by simpa using hds, ?_⟩
    rw [List.append_nil, show (fun y => o.eval [u y, v y]) = w from funext e]
    exact hw
  have cst : ∀ c : Bool, Rep n ds fun _ => c := fun c => Or.inl ⟨c, fun _ => rfl⟩
  rcases hu with ⟨c, hc⟩ | ⟨a, ha, hua⟩
  · rcases ho with rfl | rfl <;> cases c
    · exact triv _ (cst false) fun y => by simp [GateOp.eval, hc]
    · exact triv v hv fun y => by simp [GateOp.eval, hc]
    · exact triv v hv fun y => by simp [GateOp.eval, hc]
    · exact triv _ (cst true) fun y => by simp [GateOp.eval, hc]
  · rcases hv with ⟨c, hc⟩ | ⟨b, hb, hvb⟩
    · have hu : Rep n ds u := Or.inr ⟨a, ha, hua⟩
      rcases ho with rfl | rfl <;> cases c
      · exact triv _ (cst false) fun y => by simp [GateOp.eval, hc]
      · exact triv u hu fun y => by simp [GateOp.eval, hc]
      · exact triv u hu fun y => by simp [GateOp.eval, hc]
      · exact triv _ (cst true) fun y => by simp [GateOp.eval, hc]
    · refine ⟨[⟨o, [a, b]⟩], by simp, ⟨?_, ?_⟩, Or.inr ⟨n + ds.length, by simp, fun y => ?_⟩⟩
      · intro g hg
        rcases List.mem_append.1 hg with h | h
        · exact hds.1 g h
        · rw [List.mem_singleton.1 h]; exact ⟨ho, rfl⟩
      · intro j hj i hi
        by_cases h : j < ds.length
        · rw [List.getElem_append_left h] at hi
          exact hds.2 j h i hi
        · have hj' : j = ds.length := by simp at hj; omega
          subst hj'
          simp at hi
          rcases hi with rfl | rfl <;> assumption
      · rw [run_snoc, show n + ds.length = (run ds (List.ofFn y)).length by
          rw [run_length, List.length_ofFn], getD_at]
        simp [hua, hvb]

theorem build (n : ℕ) (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ ds : List Gate, AO n ds ∧ ds.length ≤ gs.length ∧
      ∀ w, Rep n ds fun y => (run gs (List.ofFn y)).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], ⟨by simp, by simp⟩, le_rfl, fun w => ?_⟩
    by_cases hw : w < n
    · exact Or.inr ⟨w, by simpa using hw, fun y => rfl⟩
    · exact Or.inl ⟨false, fun y => List.getD_eq_default _ _ (by simp [run]; omega)⟩
  | append_singleton gs g ih =>
    obtain ⟨ds, h1, h2, h3⟩ := ih fun g' h => hops g' (by simp [h])
    obtain ⟨hop, hlen⟩ := hops g (by simp)
    have main : ∃ hs : List Gate, hs.length ≤ 1 ∧ AO n (ds ++ hs) ∧ Rep n (ds ++ hs)
        fun y => g.op.eval (g.inputs.map fun i => (run gs (List.ofFn y)).getD i false) := by
      match hI : g.inputs, hlen with
      | [], _ =>
        exact ⟨[], by simp, by simpa using h1, Or.inl ⟨g.op.eval [], fun y => rfl⟩⟩
      | [a], _ =>
        refine ⟨[], by simp, by simpa using h1, ?_⟩
        rw [List.append_nil]
        have e : (fun y : Fin n → Bool => g.op.eval ([a].map fun i =>
            (run gs (List.ofFn y)).getD i false)) =
            fun y => (run gs (List.ofFn y)).getD a false := by
          funext y
          rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
        rw [e]
        exact h3 a
      | [a, b], _ => exact rep_two n ds h1 g.op hop _ _ (h3 a) (h3 b)
    obtain ⟨hs, k1, k2, k3⟩ := main
    have k4 : ∀ f : (Fin n → Bool) → Bool, Rep n ds f → Rep n (ds ++ hs) f := by
      intro f hf
      match hs, k1 with
      | [], _ => simpa using hf
      | [g'], _ => exact rep_app n ds g' f hf
    refine ⟨ds ++ hs, k2, by simp; omega, fun w => ?_⟩
    by_cases hw : w = n + gs.length
    · have e : (fun y : Fin n → Bool => (run (gs ++ [g]) (List.ofFn y)).getD w false) =
          fun y => g.op.eval (g.inputs.map fun i => (run gs (List.ofFn y)).getD i false) := by
        funext y
        rw [run_snoc, hw, show n + gs.length = (run gs (List.ofFn y)).length by
          rw [run_length, List.length_ofFn], getD_at]
      rw [e]
      exact k3
    · by_cases hw' : w < n + gs.length
      · have e : (fun y : Fin n → Bool => (run (gs ++ [g]) (List.ofFn y)).getD w false) =
            fun y => (run gs (List.ofFn y)).getD w false := by
          funext y
          exact run_prefix _ _ _ _ (by simpa using hw')
        rw [e]
        exact k4 _ (h3 w)
      · exact Or.inl ⟨false, fun y => List.getD_eq_default _ _ (by
          rw [run_length]; simp; omega)⟩

noncomputable section BS

open Finset Classical

variable {V ι : Type}

abbrev Opd (V ι : Type) : Type := (V ⊕ ι) ⊕ Bool

def ev (f : ι → (V → Bool) → Bool) (x : V → Bool) : Opd V ι → Bool
  | Sum.inl (Sum.inl v) => x v
  | Sum.inl (Sum.inr i) => f i x
  | Sum.inr b => b

def NetOk (p : (ι → Bool) × (ι → Opd V ι) × (ι → Opd V ι) × (ι → ℕ) × (ι → (V → Bool) → Bool)) :
    Prop :=
  (∀ i j, p.2.1 i = Sum.inl (Sum.inr j) → p.2.2.2.1 j < p.2.2.2.1 i) ∧
  (∀ i j, p.2.2.1 i = Sum.inl (Sum.inr j) → p.2.2.2.1 j < p.2.2.2.1 i) ∧
  ∀ i x, p.2.2.2.2 i x = if p.1 i then (ev p.2.2.2.2 x (p.2.1 i) && ev p.2.2.2.2 x (p.2.2.1 i))
    else (ev p.2.2.2.2 x (p.2.1 i) || ev p.2.2.2.2 x (p.2.2.1 i))

def Net (V ι : Type) : Type :=
  {p : (ι → Bool) × (ι → Opd V ι) × (ι → Opd V ι) × (ι → ℕ) × (ι → (V → Bool) → Bool) // NetOk p}

def Net.isAnd (N : Net V ι) : ι → Bool := (Subtype.val N).1
def Net.left (N : Net V ι) : ι → Opd V ι := (Subtype.val N).2.1
def Net.right (N : Net V ι) : ι → Opd V ι := (Subtype.val N).2.2.1
def Net.rank (N : Net V ι) : ι → ℕ := (Subtype.val N).2.2.2.1
def Net.f (N : Net V ι) : ι → (V → Bool) → Bool := (Subtype.val N).2.2.2.2

lemma Net.hl (N : Net V ι) : ∀ i j, N.left i = Sum.inl (Sum.inr j) → N.rank j < N.rank i :=
  (Subtype.property N).1

lemma Net.hr (N : Net V ι) : ∀ i j, N.right i = Sum.inl (Sum.inr j) → N.rank j < N.rank i :=
  (Subtype.property N).2.1

lemma Net.hf (N : Net V ι) : ∀ i x, N.f i x = if N.isAnd i then
    (ev N.f x (N.left i) && ev N.f x (N.right i)) else (ev N.f x (N.left i) || ev N.f x (N.right i)) :=
  (Subtype.property N).2.2

def Le (x y : V → Bool) : Prop := ∀ v, x v = true → y v = true

def Mono (g : (V → Bool) → Bool) : Prop := ∀ x y, Le x y → g x = true → g y = true

def Clean (S : Finset V) (g : (V → Bool) → Bool) : Prop := ∀ x, g x = true → ∃ a ∈ S, x a = true

def single (a : V) : V → Bool := fun v => decide (v = a)

variable [Fintype V]

def Tset (g : (V → Bool) → Bool) : Finset V := univ.filter fun a => g (single a) = true

lemma mem_Tset {g : (V → Bool) → Bool} {a : V} : a ∈ Tset g ↔ g (single a) = true := by
  simp [Tset]

lemma Clean.Tset_subset {S : Finset V} {g : (V → Bool) → Bool} (h : Clean S g) : Tset g ⊆ S := by
  intro a ha
  obtain ⟨b, hb, hx⟩ := h _ (mem_Tset.mp ha)
  have : b = a := by simpa [single] using hx
  exact this ▸ hb

namespace Net

variable (N : Net V ι)

def opf (o : Opd V ι) : (V → Bool) → Bool := fun x => ev N.f x o

lemma mono_wire : ∀ i, Mono (N.f i) := by
  intro i
  induction' h : N.rank i using Nat.strong_induction_on with r ih generalizing i
  have hop : ∀ o : Opd V ι, (∀ j, o = Sum.inl (Sum.inr j) → N.rank j < r) → Mono (N.opf o) := by
    intro o ho x y hxy hx
    rcases o with (v | j) | b
    · exact hxy v hx
    · exact ih _ (ho j rfl) j rfl x y hxy hx
    · cases b
      · simp [opf, ev] at hx
      · rfl
  have hL := hop (N.left i) (fun j hj => h ▸ N.hl i j hj)
  have hR := hop (N.right i) (fun j hj => h ▸ N.hr i j hj)
  intro x y hxy hx
  rw [N.hf] at hx ⊢
  by_cases ha : N.isAnd i = true
  · simp only [ha, if_true, Bool.and_eq_true] at hx ⊢
    exact ⟨hL x y hxy hx.1, hR x y hxy hx.2⟩
  · simp only [ha, Bool.false_eq_true, if_false, Bool.or_eq_true] at hx ⊢
    exact hx.imp (hL x y hxy) (hR x y hxy)

lemma mono_opf (o : Opd V ι) : Mono (N.opf o) := by
  intro x y hxy hx
  rcases o with (v | j) | b
  · exact hxy v hx
  · exact N.mono_wire j x y hxy hx
  · cases b
    · simp [opf, ev] at hx
    · rfl

lemma f_and {i : ι} (h : N.isAnd i = true) (x : V → Bool) :
    N.f i x = true ↔ N.opf (N.left i) x = true ∧ N.opf (N.right i) x = true := by
  rw [N.hf]; simp [h, opf]

lemma f_or {i : ι} (h : N.isAnd i = false) (x : V → Bool) :
    N.f i x = true ↔ N.opf (N.left i) x = true ∨ N.opf (N.right i) x = true := by
  rw [N.hf]; simp [h, opf]

lemma or_clean {S : Finset V} {i : ι} (h : N.isAnd i = false) (hc : Clean S (N.f i)) :
    Clean S (N.opf (N.left i)) ∧ Clean S (N.opf (N.right i)) :=
  ⟨fun x hx => hc x ((N.f_or h x).mpr (Or.inl hx)), fun x hx => hc x ((N.f_or h x).mpr (Or.inr hx))⟩

lemma and_clean {S : Finset V} {i : ι} (h : N.isAnd i = true) (hc : Clean S (N.f i)) :
    Clean S (N.opf (N.left i)) ∨ Clean S (N.opf (N.right i)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [Clean, not_forall] at h1 h2
  obtain ⟨x1, hx1, n1⟩ := h1
  obtain ⟨x2, hx2, n2⟩ := h2
  let x : V → Bool := fun v => x1 v || x2 v
  have l1 : Le x1 x := fun v hv => by simp [x, hv]
  have l2 : Le x2 x := fun v hv => by simp [x, hv]
  obtain ⟨a, ha, hxa⟩ := hc x ((N.f_and h x).mpr
    ⟨N.mono_opf _ x1 x l1 hx1, N.mono_opf _ x2 x l2 hx2⟩)
  simp only [x, Bool.or_eq_true] at hxa
  rcases hxa with h' | h'
  · exact n1 ⟨a, ha, h'⟩
  · exact n2 ⟨a, ha, h'⟩

lemma T_or {i : ι} (h : N.isAnd i = false) :
    Tset (N.f i) ⊆ Tset (N.opf (N.left i)) ∪ Tset (N.opf (N.right i)) := by
  intro a ha
  rw [mem_union, mem_Tset, mem_Tset]
  exact (N.f_or h _).mp (mem_Tset.mp ha)

lemma T_and_left {i : ι} (h : N.isAnd i = true) : Tset (N.f i) ⊆ Tset (N.opf (N.left i)) :=
  fun _ ha => mem_Tset.mpr ((N.f_and h _).mp (mem_Tset.mp ha)).1

lemma T_and_right {i : ι} (h : N.isAnd i = true) : Tset (N.f i) ⊆ Tset (N.opf (N.right i)) :=
  fun _ ha => mem_Tset.mpr ((N.f_and h _).mp (mem_Tset.mp ha)).2

lemma clean_two_is_wire {S : Finset V} {o : Opd V ι} (hc : Clean S (N.opf o))
    (h2 : 2 ≤ (Tset (N.opf o)).card) : ∃ j, o = Sum.inl (Sum.inr j) := by
  rcases o with (v | j) | b
  · exfalso
    have : Tset (N.opf (Sum.inl (Sum.inl v) : Opd V ι)) ⊆ {v} := by
      intro a ha
      have := mem_Tset.mp ha
      simp only [opf, ev, single, decide_eq_true_eq] at this
      simp [this]
    have := card_le_card this
    simp at this
    omega
  · exact ⟨j, rfl⟩
  · exfalso
    cases b
    · have : Tset (N.opf (Sum.inr false : Opd V ι)) = ∅ := by
        ext a; simp [mem_Tset, opf, ev]
      rw [this] at h2; simp at h2
    · obtain ⟨a, _, ha⟩ := hc (fun _ => false) rfl
      simp at ha

variable [Fintype ι]

def good (S : Finset V) : Finset ι :=
  (univ : Finset ι).filter fun i => Clean S (N.f i) ∧ 2 ≤ (Tset (N.f i)).card

lemma mem_good {S : Finset V} {i : ι} :
    i ∈ N.good S ↔ Clean S (N.f i) ∧ 2 ≤ (Tset (N.f i)).card := by
  simp [good]

def small (o : Opd V ι) : Finset V := if (Tset (N.opf o)).card ≤ 1 then Tset (N.opf o) else ∅

lemma small_card (o : Opd V ι) : (N.small o).card ≤ 1 := by
  unfold small; split_ifs with h
  · exact h
  · simp

lemma card_cover_le (S : Finset V) (A : Finset V)
    (hA : ∀ a ∈ A, ∃ i ∈ N.good S, a ∈ Tset (N.f i)) : A.card ≤ 2 * (N.good S).card := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a0, ha0⟩
  · simp
  obtain ⟨i0, hi0, _⟩ := hA a0 ha0
  have hex : ∀ a, a ∈ A →
      ∃ w ∈ N.good S, a ∈ Tset (N.f w) ∧ ∀ j ∈ N.good S, a ∈ Tset (N.f j) → N.rank w ≤ N.rank j := by
    intro a ha
    have hne : ((N.good S).filter fun j => a ∈ Tset (N.f j)).Nonempty := by
      obtain ⟨i1, hi1, ha1⟩ := hA a ha
      exact ⟨i1, mem_filter.mpr ⟨hi1, ha1⟩⟩
    obtain ⟨w, hw, hmin⟩ := exists_min_image _ N.rank hne
    rw [mem_filter] at hw
    exact ⟨w, hw.1, hw.2, fun j hj haj => hmin j (mem_filter.mpr ⟨hj, haj⟩)⟩
  let first : V → ι := fun a => if ha : a ∈ A then Classical.choose (hex a ha) else i0
  have hfirst : ∀ a (ha : a ∈ A), first a ∈ N.good S ∧ a ∈ Tset (N.f (first a)) ∧
      ∀ j ∈ N.good S, a ∈ Tset (N.f j) → N.rank (first a) ≤ N.rank j := by
    intro a ha
    have := Classical.choose_spec (hex a ha)
    simp only [first, ha, dif_pos]
    exact ⟨this.1, this.2.1, this.2.2⟩
  have himg : (A).image first ⊆ N.good S := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hw
    exact (hfirst a ha).1
  have hfib : ∀ w ∈ (A).image first,
      ((A).filter fun a => first a = w).card ≤ 2 := by
    intro w hw
    have hwg := himg hw
    obtain ⟨hwc, hw2⟩ := N.mem_good.mp hwg
    have hsub : ((A).filter fun a => first a = w) ⊆
        N.small (N.left w) ∪ N.small (N.right w) := by
      intro a ha
      rw [mem_filter] at ha
      obtain ⟨ha0, rfl⟩ := ha
      obtain ⟨_, haw, hmin⟩ := hfirst a ha0
      have key : ∀ o : Opd V ι, (∀ j, o = Sum.inl (Sum.inr j) → N.rank j < N.rank (first a)) →
          Clean S (N.opf o) → a ∈ Tset (N.opf o) → (Tset (N.opf o)).card ≤ 1 := by
        intro o hlt hoc hao
        by_contra hgt
        rw [not_le] at hgt
        obtain ⟨j, rfl⟩ := N.clean_two_is_wire hoc hgt
        have hj : j ∈ N.good S := N.mem_good.mpr ⟨hoc, hgt⟩
        have := hmin j hj hao
        have := hlt j rfl
        omega
      by_cases hand : N.isAnd (first a) = true
      · exfalso
        rcases N.and_clean hand hwc with hcl | hcl
        · have h1 := key _ (N.hl _) hcl (N.T_and_left hand haw)
          have := card_le_card (N.T_and_left hand)
          omega
        · have h1 := key _ (N.hr _) hcl (N.T_and_right hand haw)
          have := card_le_card (N.T_and_right hand)
          omega
      · have hor : N.isAnd (first a) = false := by simpa using hand
        obtain ⟨cl, cr⟩ := N.or_clean hor hwc
        rcases mem_union.mp (N.T_or hor haw) with hal | har
        · have h1 := key _ (N.hl _) cl hal
          exact mem_union_left _ (by simp [small, h1, hal])
        · have h1 := key _ (N.hr _) cr har
          exact mem_union_right _ (by simp [small, h1, har])
    calc _ ≤ (N.small (N.left w) ∪ N.small (N.right w)).card := card_le_card hsub
      _ ≤ (N.small (N.left w)).card + (N.small (N.right w)).card := card_union_le _ _
      _ ≤ 2 := by have := N.small_card (N.left w); have := N.small_card (N.right w); omega
  calc (A).card ≤ 2 * ((A).image first).card :=
        card_le_mul_card_image _ 2 hfib
    _ ≤ 2 * (N.good S).card := Nat.mul_le_mul_left 2 (card_le_card himg)

lemma card_T_le (S : Finset V) {i0 : ι} (hi0 : i0 ∈ N.good S) :
    (Tset (N.f i0)).card ≤ 2 * (N.good S).card :=
  N.card_cover_le S _ fun _ ha => ⟨i0, hi0, ha⟩

theorem sum_cover_le {κ : Type} [Fintype κ] (Nb : κ → Finset V)
    (hdisj : ∀ c c', c ≠ c' → (Nb c ∩ Nb c').card ≤ 1) :
    ∑ c, ((N.good (Nb c)).biUnion fun i => Tset (N.f i)).card ≤ 2 * Fintype.card ι := by
  have hpair : ∀ c ∈ (univ : Finset κ), ∀ c' ∈ (univ : Finset κ), c ≠ c' →
      Disjoint (N.good (Nb c)) (N.good (Nb c')) := by
    intro c _ c' _ hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨hc1, h2⟩ := N.mem_good.mp hi
    obtain ⟨hc2, _⟩ := N.mem_good.mp hi'
    have hsub : Tset (N.f i) ⊆ Nb c ∩ Nb c' :=
      fun a ha => mem_inter.mpr ⟨hc1.Tset_subset ha, hc2.Tset_subset ha⟩
    have := card_le_card hsub
    have := hdisj c c' hne
    omega
  have hsum : ∑ c, (N.good (Nb c)).card ≤ Fintype.card ι := by
    rw [← card_biUnion hpair]
    exact card_le_univ _
  calc ∑ c, ((N.good (Nb c)).biUnion fun i => Tset (N.f i)).card
      ≤ ∑ c, 2 * (N.good (Nb c)).card := sum_le_sum fun c _ =>
        N.card_cover_le (Nb c) _ fun a ha => by
          obtain ⟨i, hi, hai⟩ := mem_biUnion.mp ha
          exact ⟨i, hi, hai⟩
    _ = 2 * ∑ c, (N.good (Nb c)).card := by rw [mul_sum]
    _ ≤ 2 * Fintype.card ι := by omega

theorem sum_T_le {κ : Type} [Fintype κ] (Nb : κ → Finset V)
    (hdisj : ∀ c c', c ≠ c' → (Nb c ∩ Nb c').card ≤ 1)
    (h : κ → Opd V ι) (hclean : ∀ c, Clean (Nb c) (N.opf (h c))) :
    ∑ c, (Tset (N.opf (h c))).card ≤ 2 * Fintype.card ι + Fintype.card κ := by
  have hterm : ∀ c, (Tset (N.opf (h c))).card ≤ 2 * (N.good (Nb c)).card + 1 := by
    intro c
    by_cases h2 : 2 ≤ (Tset (N.opf (h c))).card
    · obtain ⟨j, hj⟩ := N.clean_two_is_wire (hclean c) h2
      have hc' := hclean c
      rw [hj] at hc' h2 ⊢
      have := N.card_T_le (Nb c) (N.mem_good.mpr ⟨hc', h2⟩)
      exact le_trans this (Nat.le_succ _)
    · omega
  have hpair : ∀ c ∈ (univ : Finset κ), ∀ c' ∈ (univ : Finset κ), c ≠ c' →
      Disjoint (N.good (Nb c)) (N.good (Nb c')) := by
    intro c _ c' _ hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨hc1, h2⟩ := N.mem_good.mp hi
    obtain ⟨hc2, _⟩ := N.mem_good.mp hi'
    have hsub : Tset (N.f i) ⊆ Nb c ∩ Nb c' :=
      fun a ha => mem_inter.mpr ⟨hc1.Tset_subset ha, hc2.Tset_subset ha⟩
    have := card_le_card hsub
    have := hdisj c c' hne
    omega
  have hsum : ∑ c, (N.good (Nb c)).card ≤ Fintype.card ι := by
    rw [← card_biUnion hpair]
    exact card_le_univ _
  calc ∑ c, (Tset (N.opf (h c))).card ≤ ∑ c, (2 * (N.good (Nb c)).card + 1) :=
        sum_le_sum fun c _ => hterm c
    _ = 2 * ∑ c, (N.good (Nb c)).card + Fintype.card κ := by
        rw [sum_add_distrib, ← mul_sum]; simp
    _ ≤ 2 * Fintype.card ι + Fintype.card κ := by omega
end Net

end BS

def toOpd (n L w : ℕ) : Opd (Fin n) (Fin L) :=
  if h : w < n then Sum.inl (Sum.inl ⟨w, h⟩)
  else if h3 : w - n < L then Sum.inl (Sum.inr ⟨w - n, h3⟩)
  else Sum.inr false

def bf (n : ℕ) (ds : List Gate) (i : Fin ds.length) (y : Fin n → Bool) : Bool :=
  (run ds (List.ofFn y)).getD (n + i.val) false

lemma toOpd_ev (n : ℕ) (ds : List Gate) (w : ℕ) (y : Fin n → Bool) :
    ev (bf n ds) y (toOpd n ds.length w) = (run ds (List.ofFn y)).getD w false := by
  unfold toOpd
  split_ifs with h h3
  · rw [run_input _ _ _ (by simpa using h)]
    simp [ev, List.getD_eq_getElem?_getD, h]
  · have hw : w = n + (w - n) := by omega
    conv_rhs => rw [hw]
    rfl
  · exact (List.getD_eq_default _ _ (by rw [run_length]; simp; omega)).symm

lemma toOpd_wire {n L w : ℕ} {j : Fin L} (h : toOpd n L w = Sum.inl (Sum.inr j)) :
    w = n + j.val := by
  by_cases h1 : w < n
  · simp [toOpd, h1] at h
  · by_cases h3 : w - n < L
    · simp [toOpd, h1, h3] at h
      have hv : w - n = j.val := by first | exact h | exact congrArg Fin.val h
      omega
    · simp [toOpd, h1, h3] at h

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

def inp (g : Gate) (k : ℕ) : ℕ := g.inputs.getD k 0

lemma ao_gate {n : ℕ} {ds : List Gate} (hds : AO n ds) (j : ℕ) (hj : j < ds.length) :
    ∃ a b, ds[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      (ds[j].op = GateOp.and ∨ ds[j].op = GateOp.or) := by
  obtain ⟨hop, hlen⟩ := hds.1 ds[j] (List.getElem_mem hj)
  have hin := hds.2 j hj
  obtain ⟨a, b, hI⟩ := List.length_eq_two.mp hlen
  rw [hI] at hin
  exact ⟨a, b, hI, hin a (by simp), hin b (by simp), hop⟩

lemma gate_val {n : ℕ} (ds : List Gate) (y : Fin n → Bool) (j : ℕ) (hj : j < ds.length)
    (a b : ℕ) (hI : ds[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j) :
    (run ds (List.ofFn y)).getD (n + j) false =
      ds[j].op.eval [(run ds (List.ofFn y)).getD a false, (run ds (List.ofFn y)).getD b false] := by
  have h := run_gate ds (List.ofFn y) j hj
  rw [List.length_ofFn] at h
  rw [h, hI]
  simp [ha, hb]

def bdata (n : ℕ) (ds : List Gate) :
    (Fin ds.length → Bool) × (Fin ds.length → Opd (Fin n) (Fin ds.length)) ×
      (Fin ds.length → Opd (Fin n) (Fin ds.length)) × (Fin ds.length → ℕ) ×
      (Fin ds.length → (Fin n → Bool) → Bool) :=
  (fun i => isAndOp (ds[i.val]'i.isLt).op, fun i => toOpd n ds.length (inp (ds[i.val]'i.isLt) 0),
    fun i => toOpd n ds.length (inp (ds[i.val]'i.isLt) 1), fun i => i.val, bf n ds)

lemma bdata_ok (n : ℕ) (ds : List Gate) (hds : AO n ds) : NetOk (bdata n ds) := by
  unfold NetOk
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    obtain ⟨a, b, hI, ha, hb, hop⟩ := ao_gate hds i.val i.isLt
    have e0 : inp (ds[i.val]'i.isLt) 0 = a := by simp [inp, hI]
    dsimp only [bdata] at h ⊢
    rw [e0] at h
    have := toOpd_wire h
    omega
  · intro i j h
    obtain ⟨a, b, hI, ha, hb, hop⟩ := ao_gate hds i.val i.isLt
    have e1 : inp (ds[i.val]'i.isLt) 1 = b := by simp [inp, hI]
    dsimp only [bdata] at h ⊢
    rw [e1] at h
    have := toOpd_wire h
    omega
  · intro i y
    obtain ⟨a, b, hI, ha, hb, hop⟩ := ao_gate hds i.val i.isLt
    have e0 : inp (ds[i.val]'i.isLt) 0 = a := by simp [inp, hI]
    have e1 : inp (ds[i.val]'i.isLt) 1 = b := by simp [inp, hI]
    dsimp only [bdata]
    rw [toOpd_ev, toOpd_ev, e0, e1]
    unfold bf
    rw [gate_val ds y i.val i.isLt a b hI ha hb]
    rcases hop with hop | hop <;> simp [hop, isAndOp, GateOp.eval]

noncomputable def bnet (n : ℕ) (ds : List Gate) (hds : AO n ds) : Net (Fin n) (Fin ds.length) :=
  Subtype.mk (bdata n ds) (bdata_ok n ds hds)

lemma bnet_opf (n : ℕ) (ds : List Gate) (hds : AO n ds) (o : Opd (Fin n) (Fin ds.length))
    (y : Fin n → Bool) : (bnet n ds hds).opf o y = ev (bf n ds) y o := rfl

abbrev Row {m n : ℕ} (R : Fin m → Fin n → Prop) [∀ i j, Decidable (R i j)] : Type :=
  {i : Fin m // 0 < (Finset.filter (R i) Finset.univ).card}

theorem core {m n : ℕ} (R : Fin m → Fin n → Prop) [dR : ∀ i j, Decidable (R i j)]
    (h4 : ∀ (a b : Fin m) (c d : Fin n), R a c → R b c → R a d → R b d → a = b ∨ c = d)
    (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ)
    (hout : ∀ (i : Fin m) (y : Fin n → Bool), (run gs (List.ofFn y)).getD (out i) false =
      decide (∃ j, R i j ∧ y j = true)) :
    ∑ i, (Finset.filter (R i) Finset.univ).card ≤ 2 * gs.length +
      (Finset.univ.filter fun i : Fin m => 0 < (Finset.filter (R i) Finset.univ).card).card := by
  classical
  obtain ⟨ds, h1, h2, h3⟩ := build n gs hops
  have hex : ∀ c : Row R, ∃ o : Opd (Fin n) (Fin ds.length),
      ∀ y, (bnet n ds h1).opf o y = decide (∃ j, R c.1 j ∧ y j = true) := by
    intro c
    obtain ⟨a, ha⟩ := Finset.card_pos.mp c.2
    have hRa : R c.1 a := (Finset.mem_filter.mp ha).2
    rcases h3 (out c.1) with ⟨b, hb⟩ | ⟨k, hk, hk'⟩
    · exfalso
      have e1 : decide (∃ j, R c.1 j ∧ (fun _ : Fin n => false) j = true) = b :=
        (hout c.1 _).symm.trans (hb _)
      have e2 : decide (∃ j, R c.1 j ∧ (fun j : Fin n => decide (j = a)) j = true) = b :=
        (hout c.1 _).symm.trans (hb _)
      have f1 : decide (∃ j, R c.1 j ∧ (fun _ : Fin n => false) j = true) = false := by simp
      have f2 : decide (∃ j, R c.1 j ∧ (fun j : Fin n => decide (j = a)) j = true) = true :=
        decide_eq_true ⟨a, hRa, by simp⟩
      exact Bool.false_ne_true ((f1.symm.trans e1).trans (f2.symm.trans e2).symm)
    · refine ⟨toOpd n ds.length k, fun y => ?_⟩
      rw [bnet_opf, toOpd_ev, ← hout]
      exact (hk' y).symm
  choose h hh using hex
  have hclean : ∀ c : Row R, Clean (Finset.filter (R c.1) Finset.univ) ((bnet n ds h1).opf (h c)) := by
    intro c y hy
    rw [hh c y] at hy
    obtain ⟨j, hj, hyj⟩ := of_decide_eq_true hy
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hyj⟩
  have hT : ∀ c : Row R, Tset ((bnet n ds h1).opf (h c)) = Finset.filter (R c.1) Finset.univ := by
    intro c
    ext a
    rw [mem_Tset, hh c]
    simp [single]
  have hdisj : ∀ c c' : Row R, c ≠ c' →
      (Finset.filter (R c.1) Finset.univ ∩ Finset.filter (R c'.1) Finset.univ).card ≤ 1 := by
    intro c c' hne
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases h4 c.1 c'.1 a b ha.1 ha.2 hb.1 hb.2 with e | e
    · exact absurd (Subtype.ext e) hne
    · exact e
  have key := (bnet n ds h1).sum_T_le (fun c : Row R => Finset.filter (R c.1) Finset.univ)
    (by intro c c' hne; convert hdisj c c' hne) h hclean
  simp only [hT] at key
  rw [Fintype.card_fin, Fintype.card_subtype] at key
  have e : ∑ i ∈ Finset.univ.filter fun i : Fin m => 0 < (Finset.filter (R i) Finset.univ).card,
      (Finset.filter (R i) Finset.univ).card =
      ∑ c : Row R, (Finset.filter (R c.1) Finset.univ).card :=
    Finset.sum_subtype _ (by simp) _
  have e' : ∑ i, (Finset.filter (R i) Finset.univ).card =
      ∑ i ∈ Finset.univ.filter fun i : Fin m => 0 < (Finset.filter (R i) Finset.univ).card,
        (Finset.filter (R i) Finset.univ).card := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simpa using hi
  rw [e', e]
  exact le_trans key (by omega)

theorem main {m n : ℕ} (R : Fin m → Fin n → Prop) [dR : ∀ i j, Decidable (R i j)]
    (h3 : ∀ i : Fin m, (Finset.filter (R i) Finset.univ).card = 0 ∨
      3 ≤ (Finset.filter (R i) Finset.univ).card)
    (h4 : ∀ (a b : Fin m) (c d : Fin n), R a c → R b c → R a d → R b d → a = b ∨ c = d)
    (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ)
    (hout : ∀ (i : Fin m) (y : Fin n → Bool), (run gs (List.ofFn y)).getD (out i) false =
      decide (∃ j, R i j ∧ y j = true)) :
    ∑ i, (Finset.filter (R i) Finset.univ).card ≤ 3 * gs.length := by
  have hc := core R h4 gs hops out hout
  have hs : (Finset.univ.filter fun i : Fin m =>
      0 < (Finset.filter (R i) Finset.univ).card).card * 3 ≤
      ∑ i, (Finset.filter (R i) Finset.univ).card := by
    calc _ = (Finset.univ.filter fun i : Fin m =>
          0 < (Finset.filter (R i) Finset.univ).card).card • 3 := by simp
      _ ≤ ∑ i ∈ Finset.univ.filter fun i : Fin m => 0 < (Finset.filter (R i) Finset.univ).card,
          (Finset.filter (R i) Finset.univ).card :=
        Finset.card_nsmul_le_sum _ _ _ (fun i hi => by
          rcases h3 i with h | h
          · have := (Finset.mem_filter.mp hi).2
            omega
          · exact h)
      _ ≤ ∑ i, (Finset.filter (R i) Finset.univ).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

def orBuild {m n : ℕ} : List (Sigma fun _ : Fin m => Fin n) → List Gate × (Fin m → ℕ)
  | [] => ([⟨GateOp.or, []⟩], fun _ => n)
  | p :: P => ((orBuild P).1 ++ [⟨GateOp.or, [p.2.val, (orBuild P).2 p.1]⟩],
      fun i => if i = p.1 then n + (orBuild P).1.length else (orBuild P).2 i)

lemma orBuild_ops {m n : ℕ} (P : List (Sigma fun _ : Fin m => Fin n)) :
    ∀ g ∈ (orBuild P).1, g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  induction P with
  | nil =>
    intro g hg
    have hg' : g = ⟨GateOp.or, []⟩ := List.mem_singleton.mp hg
    subst hg'
    simp
  | cons p P ih =>
    intro g hg
    have hg' : g ∈ (orBuild P).1 ++ [⟨GateOp.or, [p.2.val, (orBuild P).2 p.1]⟩] := hg
    rcases List.mem_append.mp hg' with h | h
    · exact ih g h
    · rw [List.mem_singleton.mp h]
      simp

lemma orBuild_len {m n : ℕ} (P : List (Sigma fun _ : Fin m => Fin n)) :
    (orBuild P).1.length = P.length + 1 := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [orBuild, ih]

lemma or_eval2 (f : ℕ → Bool) (a b : ℕ) : GateOp.or.eval ([a, b].map f) = (f a || f b) := by
  simp [GateOp.eval]

lemma orBuild_spec {m n : ℕ} (P : List (Sigma fun _ : Fin m => Fin n)) (y : Fin n → Bool) :
    ∀ i : Fin m, (orBuild P).2 i < n + (orBuild P).1.length ∧
      ((run (orBuild P).1 (List.ofFn y)).getD ((orBuild P).2 i) false = true ↔
        ∃ p ∈ P, p.1 = i ∧ y p.2 = true) := by
  induction P with
  | nil =>
    intro i
    refine ⟨by simp [orBuild], ?_⟩
    have h0 : (run [⟨GateOp.or, []⟩] (List.ofFn y)).getD (List.ofFn y).length false = false :=
      getD_at (List.ofFn y) _
    rw [List.length_ofFn] at h0
    constructor
    · intro h
      exact absurd (h0.symm.trans h) (by simp)
    · rintro ⟨q, hq, _⟩
      simp at hq
  | cons p P ih =>
    intro i
    have hlen : (run (orBuild P).1 (List.ofFn y)).length = n + (orBuild P).1.length := by
      rw [run_length, List.length_ofFn]
    have e2 : (orBuild (p :: P)).1 =
        (orBuild P).1 ++ [⟨GateOp.or, [p.2.val, (orBuild P).2 p.1]⟩] := rfl
    by_cases hi : i = p.1
    · subst hi
      refine ⟨by simp [orBuild], ?_⟩
      have e : (orBuild (p :: P)).2 p.1 = (run (orBuild P).1 (List.ofFn y)).length := by
        rw [hlen]
        simp [orBuild]
      have hj : (run (orBuild P).1 (List.ofFn y)).getD p.2.val false = y p.2 := by
        rw [run_input _ _ _ (by simp)]
        simp [List.getD_eq_getElem?_getD]
      rw [e, e2, run_snoc, getD_at, or_eval2, hj, Bool.or_eq_true, (ih p.1).2]
      constructor
      · rintro (h | ⟨q, hq, h1, h2⟩)
        · exact ⟨p, by simp, rfl, h⟩
        · exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩
      · rintro ⟨q, hq, h1, h2⟩
        rcases List.mem_cons.mp hq with hq | hq
        · rw [hq] at h2
          exact Or.inl h2
        · exact Or.inr ⟨q, hq, h1, h2⟩
    · have e : (orBuild (p :: P)).2 i = (orBuild P).2 i := by simp [orBuild, hi]
      obtain ⟨hlt, hiff⟩ := ih i
      refine ⟨by rw [e, e2]; simp; omega, ?_⟩
      rw [e, e2, run_snoc, getD_lt _ _ _ (by rw [hlen]; exact hlt), hiff]
      constructor
      · rintro ⟨q, hq, h1, h2⟩
        exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩
      · rintro ⟨q, hq, h1, h2⟩
        rcases List.mem_cons.mp hq with hq | hq
        · rw [hq] at h1
          exact absurd h1.symm hi
        · exact ⟨q, hq, h1, h2⟩

theorem main2 {m n : ℕ} (R : Fin m → Fin n → Prop) [dR : ∀ i j, Decidable (R i j)]
    (h3 : ∀ i : Fin m, (Finset.filter (R i) Finset.univ).card = 0 ∨
      3 ≤ (Finset.filter (R i) Finset.univ).card)
    (h4 : ∀ (a b : Fin m) (c d : Fin n), R a c → R b c → R a d → R b d → a = b ∨ c = d)
    (s : ℕ)
    (hJ : JointSizeAtMost Set.univ (fun (i : Fin m) (y : Fin n → Bool) =>
      decide (∃ j, R i j ∧ y j = true)) Finset.univ s) :
    ∃ (C : Circuit) (out : Fin m → ℕ),
      (∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size ≤ 3 * (s + 1) ∧
      JointComputes Set.univ (fun (i : Fin m) (y : Fin n → Bool) =>
        decide (∃ j, R i j ∧ y j = true)) Finset.univ C out := by
  obtain ⟨C0, out0, ⟨hmono, hfan⟩, hsize, hcomp⟩ := hJ
  have hsum := main R h3 h4 C0.gates (fun g hg => ⟨hmono g hg, hfan g hg⟩) out0
    (fun i y => hcomp i (Finset.mem_univ _) y (Set.mem_univ _))
  obtain ⟨P, hPdef⟩ : ∃ P : List (Sigma fun _ : Fin m => Fin n),
      P = (Finset.univ.sigma fun i : Fin m => Finset.filter (R i) Finset.univ).toList := ⟨_, rfl⟩
  have hP : P.length = ∑ i, (Finset.filter (R i) Finset.univ).card := by
    rw [hPdef, Finset.length_toList, Finset.card_sigma]
  refine ⟨⟨(orBuild P).1, 0⟩, (orBuild P).2, orBuild_ops P, ?_, ?_⟩
  · show (orBuild P).1.length ≤ 3 * (s + 1)
    rw [orBuild_len, hP]
    have hs : C0.gates.length ≤ s := hsize
    omega
  · intro i _ y _
    show (run (orBuild P).1 (List.ofFn y)).getD ((orBuild P).2 i) false =
      decide (∃ j, R i j ∧ y j = true)
    rw [Bool.eq_iff_iff, (orBuild_spec P y i).2, decide_eq_true_iff]
    constructor
    · rintro ⟨q, hq, h1, h2⟩
      rw [hPdef, Finset.mem_toList, Finset.mem_sigma] at hq
      exact ⟨q.2, by rw [← h1]; exact (Finset.mem_filter.mp hq.2).2, h2⟩
    · rintro ⟨j, hj, hy⟩
      refine ⟨⟨i, j⟩, ?_, rfl, hy⟩
      rw [hPdef, Finset.mem_toList, Finset.mem_sigma]
      exact ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

end PEqualNP.Outside.L_meta_6734

theorem PEqualNP.Outside.L_meta_6734 : ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : ℕ), PEqualNP.CircuitLowerBounds.JointSizeAtMost Set.univ (fun (x10 : Fin x2) (x11 : Fin x3 → Bool) => Decidable.decide (∃ (x12 : Fin x3), x4 x10 x12 ∧ x11 x12 = Bool.true)) Finset.univ x9 → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit) (x12 : Fin x2 → ℕ), (∀ x13 ∈ x11.gates, x13.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x13.inputs.length ≤ (2 : ℕ)) ∧ x11.size ≤ x1 * (x9 + (1 : ℕ)) ∧ PEqualNP.CircuitLowerBounds.JointComputes Set.univ (fun (x13 : Fin x2) (x14 : Fin x3 → Bool) => Decidable.decide (∃ (x15 : Fin x3), x4 x13 x15 ∧ x14 x15 = Bool.true)) Finset.univ x11 x12 := by
  refine ⟨3, ?_⟩
  intro m n R dR h3 _ h4 s hJ
  exact PEqualNP.Outside.L_meta_6734.main2 R h3 h4 s hJ
