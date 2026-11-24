import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5148_aux

open PEqualNP.CircuitLowerBounds

def val (W : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr w => W.getD w false

def toW : Bool ⊕ ℕ → ℕ
  | Sum.inl _ => 0
  | Sum.inr w => w

def simpG : GateOp → List (Bool ⊕ ℕ) → Option (Bool ⊕ ℕ)
  | GateOp.and, [Sum.inl a] => some (Sum.inl a)
  | GateOp.and, [Sum.inl a, d] => some (if a then d else Sum.inl false)
  | GateOp.and, [d, Sum.inl a] => some (if a then d else Sum.inl false)
  | GateOp.or, [Sum.inl a] => some (Sum.inl a)
  | GateOp.or, [Sum.inl a, d] => some (if a then Sum.inl true else d)
  | GateOp.or, [d, Sum.inl a] => some (if a then Sum.inl true else d)
  | GateOp.not, Sum.inl a :: _ => some (Sum.inl (!a))
  | _, _ => none

def OkOp (op : GateOp) : Prop :=
  op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)

theorem simp_some (W : List Bool) (op : GateOp) (ds : List (Bool ⊕ ℕ)) (d : Bool ⊕ ℕ)
    (hop : OkOp op) (hl : ds.length ≤ 2) (h : simpG op ds = some d) :
    val W d = op.eval (ds.map (val W)) := by
  simp only [OkOp, Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [simpG] at h
  · rcases hop with rfl | rfl | rfl <;> rcases a with a | a <;>
      simp [simpG] at h <;> subst h <;> simp [val, GateOp.eval]
  · rcases hop with rfl | rfl | rfl <;> rcases a with a | a <;> rcases b with b | b <;>
      cases a <;> cases b <;>
      simp [simpG] at h <;> subst h <;> simp [val, GateOp.eval]
  · simp at hl

theorem simp_none (W : List Bool) (op : GateOp) (ds : List (Bool ⊕ ℕ))
    (hop : OkOp op) (hl : ds.length ≤ 2) (h : simpG op ds = none) :
    op.eval ((ds.map toW).map (fun i => W.getD i false)) = op.eval (ds.map (val W)) := by
  simp only [OkOp, Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp
  · rcases hop with rfl | rfl | rfl <;> rcases a with a | a <;>
      simp [simpG] at h ⊢ <;> simp [val, toW, GateOp.eval]
  · rcases hop with rfl | rfl | rfl <;> rcases a with a | a <;> rcases b with b | b <;>
      cases a <;> cases b <;>
      simp [simpG] at h ⊢ <;> simp [val, toW, GateOp.eval]
  · simp at hl

theorem simp_S (op : GateOp) (ds : List (Bool ⊕ ℕ))
    (hop : OkOp op) (hl : ds.length ≤ 2) (hm : Sum.inl false ∈ ds)
    (hn : op = GateOp.not → ds.head? = some (Sum.inl false)) : simpG op ds ≠ none := by
  simp only [OkOp, Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at hm
  · rcases hop with rfl | rfl | rfl <;> rcases a with a | a <;>
      simp_all [simpG]
  · rcases hop with rfl | rfl | rfl <;> rcases a with a | a <;> rcases b with b | b <;>
      cases a <;> cases b <;>
      simp_all [simpG]
  · simp at hl

theorem simp_mem (op : GateOp) (ds : List (Bool ⊕ ℕ)) (w : ℕ)
    (h : simpG op ds = some (Sum.inr w)) : Sum.inr w ∈ ds := by
  unfold simpG at h
  split at h <;> simp_all <;> split_ifs at h <;> simp_all

def stepS (n : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  match simpG g.op (g.inputs.map (fun i => st.1.getD i (Sum.inl false))) with
  | some d => (st.1 ++ [d], st.2)
  | none => (st.1 ++ [Sum.inr (n + st.2.length)],
      st.2 ++ [⟨g.op, (g.inputs.map (fun i => st.1.getD i (Sum.inl false))).map toW⟩])

def init (n v : ℕ) : List (Bool ⊕ ℕ) :=
  (List.range n).map (fun i => if i = v then Sum.inl false else Sum.inr i)

def run (n v : ℕ) (L : List Gate) : List (Bool ⊕ ℕ) × List Gate :=
  L.foldl (stepS n) (init n v, [])

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  ({ gates := gs, output := 0 } : Circuit).wires x

theorem wiresOf_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresOf (gs ++ [g]) x =
      wiresOf gs x ++ [g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false)] := by
  simp [wiresOf, Circuit.wires, List.foldl_append]

theorem wiresOf_length (gs : List Gate) :
    ∀ x : List Bool, (wiresOf gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => intro x; simp [wiresOf, Circuit.wires]
  | append_singleton gs g ih => intro x; rw [wiresOf_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

theorem val_snoc (W : List Bool) (b : Bool) (e : Bool ⊕ ℕ)
    (h : ∀ w, e = Sum.inr w → w < W.length) : val (W ++ [b]) e = val W e := by
  rcases e with c | w
  · rfl
  · simp only [val]; exact List.getD_append _ _ _ _ (h w rfl)

theorem getD_mem {α : Type} (l : List α) (d : α) (i : ℕ) : l.getD i d ∈ l ∨ l.getD i d = d := by
  by_cases h : i < l.length
  · left; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · right; exact List.getD_eq_default _ _ (by omega)

def Inv (n v : ℕ) (L : List Gate) (ds : List (Bool ⊕ ℕ)) (gs : List Gate) : Prop :=
  ds.length = n + L.length ∧
  (∀ x : List Bool, x.length = n → x.getD v false = false →
    ∀ i, val (wiresOf gs x) (ds.getD i (Sum.inl false)) = (wiresOf L x).getD i false) ∧
  (∀ w, Sum.inr w ∈ ds → w < n + gs.length) ∧
  ds.getD v (Sum.inl false) = Sum.inl false ∧
  (∀ g ∈ gs, OkOp g.op ∧ g.inputs.length ≤ 2) ∧
  (∀ T : Finset ℕ, (∀ j ∈ T, ∃ g : Gate, L[j]? = some g ∧ v ∈ g.inputs ∧
      (g.op = GateOp.not → g.inputs.head? = some v)) → gs.length + T.card ≤ L.length)

theorem inv_init (n v : ℕ) (hv : v < n) : Inv n v [] (init n v) [] := by
  refine ⟨by simp [init], ?_, ?_, ?_, by simp, ?_⟩
  · intro x hx hxv i
    simp only [wiresOf, Circuit.wires, List.foldl_nil]
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [init]; exact hi)]
      simp only [init, List.getElem_map, List.getElem_range]
      split_ifs with h
      · subst h; simpa [val] using hxv
      · rfl
    · rw [List.getD_eq_default _ _ (by simp [init]; omega), List.getD_eq_default _ _ (by omega)]
      rfl
  · intro w hw
    obtain ⟨a, ha, he⟩ := List.mem_map.1 hw
    simp only [List.mem_range] at ha
    split_ifs at he
    injection he with he
    simp; omega
  · rw [List.getD_eq_getElem _ _ (by simp [init]; exact hv)]; simp [init]
  · intro T hT
    have hT0 : T = ∅ := by
      ext j; constructor
      · intro hj; obtain ⟨g, hg, -⟩ := hT j hj; simp at hg
      · intro hj; simp at hj
    simp [hT0]

theorem inv_step (n v : ℕ) (hv : v < n) (L : List Gate) (g : Gate) (st : List (Bool ⊕ ℕ) × List Gate)
    (hI : Inv n v L st.1 st.2) (hg : OkOp g.op ∧ g.inputs.length ≤ 2) :
    Inv n v (L ++ [g]) (stepS n st g).1 (stepS n st g).2 := by
  obtain ⟨ds, gs⟩ := st
  obtain ⟨hlen, hval, hbd, hvv, hfan, hcnt⟩ := hI
  simp only at hlen hval hbd hvv hfan hcnt
  set dg := g.inputs.map (fun i => ds.getD i (Sum.inl false)) with hdg
  have hdgl : dg.length ≤ 2 := by simp [hdg, hg.2]
  have hdgb : ∀ w, Sum.inr w ∈ dg → w < n + gs.length := by
    intro w hw
    obtain ⟨i, -, hi⟩ := List.mem_map.1 hw
    rcases getD_mem ds (Sum.inl false) i with h | h
    · rw [hi] at h; exact hbd w h
    · rw [hi] at h; cases h
  have hgate : ∀ x : List Bool, x.length = n → x.getD v false = false →
      g.op.eval (g.inputs.map fun i => (wiresOf L x).getD i false) =
        g.op.eval (dg.map (val (wiresOf gs x))) := by
    intro x hx hxv
    rw [hdg, List.map_map]; congr 1; apply List.map_congr_left; intro i _
    exact (hval x hx hxv i).symm
  have hS : (v ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = some v)) →
      simpG g.op dg ≠ none := by
    rintro ⟨hm, hn⟩
    apply simp_S _ _ hg.1 hdgl
    · rw [← hvv]; exact List.mem_map_of_mem hm
    · intro h; rw [hdg, List.head?_map, hn h]; exact congrArg some hvv
  have hcount : ∀ T : Finset ℕ, (∀ j ∈ T, ∃ g' : Gate, (L ++ [g])[j]? = some g' ∧
      v ∈ g'.inputs ∧ (g'.op = GateOp.not → g'.inputs.head? = some v)) →
      gs.length + (T.erase L.length).card ≤ L.length ∧
        (L.length ∈ T → v ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = some v)) := by
    intro T hT
    constructor
    · apply hcnt
      intro j hj
      obtain ⟨hne, hjT⟩ := Finset.mem_erase.1 hj
      obtain ⟨g', hg', h2⟩ := hT j hjT
      have hjl : j < L.length := by
        have := (List.getElem?_eq_some_iff.1 hg').1; simp at this; omega
      refine ⟨g', ?_, h2⟩
      rwa [List.getElem?_append_left hjl] at hg'
    · intro hm
      obtain ⟨g', hg', h2⟩ := hT _ hm
      simp at hg'; subst hg'; exact h2
  have hW : ∀ x : List Bool, x.length = n → (wiresOf L x).length = n + L.length := by
    intro x hx; rw [wiresOf_length, hx]
  have hWg : ∀ x : List Bool, x.length = n → (wiresOf gs x).length = n + gs.length := by
    intro x hx; rw [wiresOf_length, hx]
  have hdsv : v < ds.length := by omega
  unfold stepS
  simp only
  rcases hs : simpG g.op dg with _ | d
  · refine ⟨by simp [hlen]; omega, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx hxv i
      rw [wiresOf_snoc, wiresOf_snoc, getD_snoc, getD_snoc, hW x hx, hlen]
      split_ifs with h1 h2
      · rw [val_snoc]
        · exact hval x hx hxv i
        · intro w hw; rw [hWg x hx]
          rcases getD_mem ds (Sum.inl false) i with h | h <;> rw [hw] at h
          · exact hbd w h
          · cases h
      · simp only [val]; rw [getD_snoc, hWg x hx]; simp only [lt_irrefl, ite_false, ite_true]
        rw [simp_none _ _ _ hg.1 hdgl hs, hgate x hx hxv]
      · rfl
    · intro w hw; simp only [List.mem_append, List.mem_singleton, Sum.inr.injEq] at hw
      simp only [List.length_append, List.length_singleton]
      rcases hw with hw | hw
      · have := hbd w hw; omega
      · omega
    · rw [List.getD_append _ _ _ _ hdsv]; exact hvv
    · intro g' hg'; simp only [List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | hg'
      · exact hfan g' hg'
      · subst hg'; exact ⟨hg.1, by simp [hg.2]⟩
    · intro T hT
      obtain ⟨h1, h2⟩ := hcount T hT
      have hnm : L.length ∉ T := fun hm => hS (h2 hm) hs
      rw [Finset.erase_eq_of_notMem hnm] at h1
      simp only [List.length_append, List.length_singleton]; omega
  · refine ⟨by simp [hlen]; omega, ?_, ?_, ?_, hfan, ?_⟩
    · intro x hx hxv i
      rw [wiresOf_snoc, getD_snoc, getD_snoc, hW x hx, hlen]
      split_ifs with h1 h2
      · exact hval x hx hxv i
      · rw [simp_some _ _ _ _ hg.1 hdgl hs, hgate x hx hxv]
      · rfl
    · intro w hw; simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw
      · exact hbd w hw
      · subst hw; exact hdgb w (simp_mem _ _ _ hs)
    · rw [List.getD_append _ _ _ _ hdsv]; exact hvv
    · intro T hT
      obtain ⟨h1, -⟩ := hcount T hT
      have := Finset.pred_card_le_card_erase (s := T) (a := L.length)
      simp only [List.length_append, List.length_singleton]; omega

theorem inv_run (n v : ℕ) (hv : v < n) : ∀ L : List Gate,
    (∀ g ∈ L, OkOp g.op ∧ g.inputs.length ≤ 2) → Inv n v L (run n v L).1 (run n v L).2 := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; exact inv_init n v hv
  | append_singleton L g ih =>
    intro hL
    have h := inv_step n v hv L g (run n v L) (ih (fun g' hg' => hL g' (by simp [hg'])))
      (hL g (by simp))
    have hr : run n v (L ++ [g]) = stepS n (run n v L) g := by simp [run, List.foldl_append]
    rw [hr]; exact h

theorem main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : Finset ℕ),
    PEqualNP.MetaComplexity.FanInTwo x2 →
    (∀ x6 ∈ x4, ∃ (x8 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x8 ∧
      ↑x3 ∈ x8.inputs ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.not →
        x8.inputs.head? = Option.some ↑x3)) →
    (∃ (x7 : Bool), ∀ (x8 : Fin x1 → Bool), x8 x3 = Bool.false → x2.eval (List.ofFn x8) = x7) ∨
    ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧
      x7.size + x4.card ≤ x2.size ∧ ∀ (x8 : Fin x1 → Bool), x8 x3 = Bool.false →
        x7.eval (List.ofFn x8) = x2.eval (List.ofFn x8) := by
  intro n C v S hC hS
  obtain ⟨-, hval, -, -, hfan, hcnt⟩ := inv_run n v v.2 C.gates (fun g hg => hC g hg)
  have hx : ∀ x : Fin n → Bool, x v = false →
      val (wiresOf (run n v C.gates).2 (List.ofFn x))
        ((run n v C.gates).1.getD C.output (Sum.inl false)) = C.eval (List.ofFn x) := by
    intro x hxv
    rw [hval (List.ofFn x) (by simp) (by simp [List.getD_eq_getElem?_getD, hxv]) C.output]
    rfl
  rcases hd : (run n v C.gates).1.getD C.output (Sum.inl false) with c | w
  · left
    refine ⟨c, fun x hxv => ?_⟩
    rw [← hx x hxv, hd]; rfl
  · right
    refine ⟨⟨(run n v C.gates).2, w⟩, fun g hg => hfan g hg, hcnt S hS, ?_⟩
    intro x hxv
    rw [← hx x hxv, hd]; rfl

end PEqualNP.Outside.L_meta_5148_aux

theorem PEqualNP.Outside.L_meta_5148 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : Finset ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ x6 ∈ x4, ∃ (x8 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x8 ∧ ↑x3 ∈ x8.inputs ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.not → x8.inputs.head? = Option.some ↑x3)) → (∃ (x7 : Bool), ∀ (x8 : Fin x1 → Bool), x8 x3 = Bool.false → x2.eval (List.ofFn x8) = x7) ∨ ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size + x4.card ≤ x2.size ∧ ∀ (x8 : Fin x1 → Bool), x8 x3 = Bool.false → x7.eval (List.ofFn x8) = x2.eval (List.ofFn x8) :=
  PEqualNP.Outside.L_meta_5148_aux.main
