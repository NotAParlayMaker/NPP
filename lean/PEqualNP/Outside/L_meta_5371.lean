import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5371

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

def AO (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem ofFn_update {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    List.ofFn (Function.update x v false) = (List.ofFn x).set v false := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply]
  by_cases hi : (v : ℕ) = i
  · simp [hi, Fin.ext_iff]
  · have : ¬ (⟨i, by simpa using h1⟩ : Fin n) = v := by
      intro h; apply hi; rw [← h]
    simp [hi, this]

def Inv (n v : ℕ) (L : List Gate) (ds : List (Bool ⊕ ℕ)) (gs : List Gate) : Prop :=
  ds.length = n + L.length ∧
  (∀ x : List Bool, x.length = n →
    ∀ i, val (wiresOf gs x) (ds.getD i (Sum.inl false)) = (wiresOf L (x.set v false)).getD i false) ∧
  (∀ w, Sum.inr w ∈ ds → w < n + gs.length) ∧
  ds.getD v (Sum.inl false) = Sum.inl false ∧
  (∀ g ∈ gs, AO g) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) ∧
  gs.length ≤ L.length ∧
  (gs.length = L.length → ∀ x : List Bool, x.length = n → ∀ i, i ≠ v →
    val (wiresOf gs x) (ds.getD i (Sum.inl false)) = (wiresOf L x).getD i false)

theorem inv_init (n v : ℕ) (hv : v < n) : Inv n v [] (init n v) [] := by
  refine ⟨by simp [init], ?_, ?_, ?_, by simp, by simp, by simp, ?_⟩
  · intro x hx i
    simp only [wiresOf, Circuit.wires, List.foldl_nil]
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [init]; exact hi)]
      simp only [init, List.getElem_map, List.getElem_range]
      split_ifs with h
      · subst h; simp [val, List.getD_eq_getElem?_getD, List.getElem?_set, hx, hv]
      · simp [val, List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega), List.getD_eq_default _ _ (by simp; omega)]
      rfl
  · intro w hw
    obtain ⟨a, ha, he⟩ := List.mem_map.1 hw
    simp only [List.mem_range] at ha
    split_ifs at he
    injection he with he
    simp; omega
  · rw [List.getD_eq_getElem _ _ (by simp [init]; exact hv)]; simp [init]
  · intro _ x hx i hiv
    simp only [wiresOf, Circuit.wires, List.foldl_nil]
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [init]; exact hi)]
      simp [init, hiv, val]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega), List.getD_eq_default _ _ (by omega)]
      rfl

theorem inv_step (n v : ℕ) (hv : v < n) (L : List Gate) (g : Gate) (st : List (Bool ⊕ ℕ) × List Gate)
    (hI : Inv n v L st.1 st.2) (hg : AO g) :
    Inv n v (L ++ [g]) (stepS n st g).1 (stepS n st g).2 := by
  obtain ⟨ds, gs⟩ := st
  obtain ⟨hlen, hval, hbd, hvv, hfan, hrb, hle, h7⟩ := hI
  simp only at hlen hval hbd hvv hfan hrb hle h7
  have hok : OkOp g.op := by
    rcases hg.1 with h | h <;> simp [OkOp, h]
  have hnot : g.op ≠ GateOp.not := by
    intro h'; rcases hg.1 with h | h <;> rw [h] at h' <;> cases h'
  set dg := g.inputs.map (fun i => ds.getD i (Sum.inl false)) with hdg
  have hdgl : dg.length ≤ 2 := by simp [hdg, hg.2]
  have hdgb : ∀ w, Sum.inr w ∈ dg → w < n + gs.length := by
    intro w hw
    obtain ⟨i, -, hi⟩ := List.mem_map.1 hw
    rcases getD_mem ds (Sum.inl false) i with h | h
    · rw [hi] at h; exact hbd w h
    · rw [hi] at h; cases h
  have hgate : ∀ x : List Bool, x.length = n →
      g.op.eval (g.inputs.map fun i => (wiresOf L (x.set v false)).getD i false) =
        g.op.eval (dg.map (val (wiresOf gs x))) := by
    intro x hx
    rw [hdg, List.map_map]; congr 1; apply List.map_congr_left; intro i _
    exact (hval x hx i).symm
  have hS : v ∈ g.inputs → simpG g.op dg ≠ none := by
    intro hm
    apply simp_S _ _ hok hdgl
    · rw [← hvv]; exact List.mem_map_of_mem hm
    · intro h; exact absurd h hnot
  have hW : ∀ x : List Bool, x.length = n → (wiresOf L x).length = n + L.length := by
    intro x hx; rw [wiresOf_length, hx]
  have hWg : ∀ x : List Bool, x.length = n → (wiresOf gs x).length = n + gs.length := by
    intro x hx; rw [wiresOf_length, hx]
  have hdsv : v < ds.length := by omega
  have hsl : ∀ x : List Bool, x.length = n → (x.set v false).length = n := by
    intro x hx; simp [hx]
  have hvs : ∀ x : List Bool, x.length = n → ∀ i,
      val (wiresOf gs x ++ [g.op.eval (List.map (fun i => (wiresOf gs x).getD i false)
        (dg.map toW))]) (ds.getD i (Sum.inl false)) = val (wiresOf gs x) (ds.getD i (Sum.inl false)) := by
    intro x hx i
    rw [val_snoc]
    intro w hw; rw [hWg x hx]
    rcases getD_mem ds (Sum.inl false) i with h | h <;> rw [hw] at h
    · exact hbd w h
    · cases h
  unfold stepS
  simp only
  rcases hs : simpG g.op dg with _ | d
  · have hgate7 : gs.length = L.length → ∀ x : List Bool, x.length = n →
        g.op.eval (g.inputs.map fun i => (wiresOf L x).getD i false) =
          g.op.eval (dg.map (val (wiresOf gs x))) := by
      intro he x hx
      rw [hdg, List.map_map]; congr 1; apply List.map_congr_left; intro i hi
      have hne : i ≠ v := by rintro rfl; exact hS hi hs
      exact (h7 he x hx i hne).symm
    refine ⟨by simp [hlen]; omega, ?_, ?_, ?_, ?_, ?_, by simp; omega, ?_⟩
    · intro x hx i
      rw [wiresOf_snoc, wiresOf_snoc, getD_snoc, getD_snoc, hW _ (hsl x hx), hlen]
      split_ifs with h1 h2
      · exact (hvs x hx i).trans (hval x hx i)
      · simp only [val]; rw [getD_snoc, hWg x hx]; simp only [lt_irrefl, ite_false, ite_true]
        rw [simp_none _ _ _ hok hdgl hs, hgate x hx]
      · first | rfl | (rw [List.getD_eq_default _ _ (by simp; omega)]; rfl)
    · intro w hw; simp only [List.mem_append, List.mem_singleton, Sum.inr.injEq] at hw
      simp only [List.length_append, List.length_singleton]
      rcases hw with hw | hw
      · have := hbd w hw; omega
      · omega
    · rw [List.getD_append _ _ _ _ hdsv]; exact hvv
    · intro g' hg'; simp only [List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | hg'
      · exact hfan g' hg'
      · subst hg'; exact ⟨hg.1, by simp [hdg, hg.2]⟩
    · intro j hj i hi
      simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_or_ge j gs.length with hj' | hj'
      · rw [List.getD_append _ _ _ _ hj'] at hi; exact hrb j hj' i hi
      · have hje : j = gs.length := by omega
        subst hje
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hi
        rcases e with c | w
        · simp [toW]; omega
        · exact hdgb w he
    · intro he x hx i hiv
      simp only [List.length_append, List.length_singleton] at he
      have he' : gs.length = L.length := by omega
      rw [wiresOf_snoc, wiresOf_snoc, getD_snoc, getD_snoc, hW x hx, hlen]
      split_ifs with h1 h2
      · exact (hvs x hx i).trans (h7 he' x hx i hiv)
      · simp only [val]; rw [getD_snoc, hWg x hx]; simp only [lt_irrefl, ite_false, ite_true]
        rw [simp_none _ _ _ hok hdgl hs, hgate7 he' x hx]
      · first | rfl | (rw [List.getD_eq_default _ _ (by simp; omega)]; rfl)
  · refine ⟨by simp [hlen]; omega, ?_, ?_, ?_, hfan, hrb, by simp; omega, ?_⟩
    · intro x hx i
      rw [wiresOf_snoc, getD_snoc, getD_snoc, hW _ (hsl x hx), hlen]
      split_ifs with h1 h2
      · exact hval x hx i
      · rw [simp_some _ _ _ _ hok hdgl hs, hgate x hx]
      · rfl
    · intro w hw; simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw
      · exact hbd w hw
      · subst hw; exact hdgb w (simp_mem _ _ _ hs)
    · rw [List.getD_append _ _ _ _ hdsv]; exact hvv
    · intro he; simp at he; omega

theorem inv_run (n v : ℕ) (hv : v < n) : ∀ L : List Gate,
    (∀ g ∈ L, AO g) → Inv n v L (run n v L).1 (run n v L).2 := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; exact inv_init n v hv
  | append_singleton L g ih =>
    intro hL
    have h := inv_step n v hv L g (run n v L) (ih (fun g' hg' => hL g' (by simp [hg'])))
      (hL g (by simp))
    have hr : run n v (L ++ [g]) = stepS n (run n v L) g := by simp [run, List.foldl_append]
    rw [hr]; exact h

theorem main : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size = x3 → PEqualNP.TopForm.IsAO2 x1 x4 → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x4.eval (List.ofFn (Function.update x7 x2 Bool.false)) ≠ x4.eval (List.ofFn (Function.update x8 x2 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size ≤ x4.size ∧ ((∃ (x9 : Fin x1 → Bool), x4.eval (List.ofFn x9) ≠ x4.eval (List.ofFn (Function.update x9 x2 Bool.false))) → x8.size < x4.size) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval (List.ofFn (Function.update x9 x2 Bool.false)) := by
  intro n v s C _ hC hnc
  obtain ⟨hAO, -, h2⟩ := hC
  obtain ⟨-, hval, -, hvv, hfan, hrb, hle, h7⟩ :=
    inv_run n v v.2 C.gates (fun g hg => ⟨hAO g hg, h2 g hg⟩)
  have hx : ∀ x : Fin n → Bool,
      val (wiresOf (run n v C.gates).2 (List.ofFn x))
        ((run n v C.gates).1.getD C.output (Sum.inl false)) =
        C.eval (List.ofFn (Function.update x v false)) := by
    intro x
    rw [ofFn_update, hval (List.ofFn x) (by simp) C.output]
    rfl
  rcases hd : (run n v C.gates).1.getD C.output (Sum.inl false) with c | w
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    rw [← hx a, ← hx b, hd]; rfl
  · refine ⟨⟨(run n v C.gates).2, w⟩, ⟨fun g hg => (hfan g hg).1, ?_, fun g hg => (hfan g hg).2⟩,
      hle, ?_, ?_⟩
    · intro j hj i hi; exact hrb j hj i hi
    · rintro ⟨x, hxd⟩
      show (run n v C.gates).2.length < C.gates.length
      by_contra hcon
      have heq : (run n v C.gates).2.length = C.gates.length := by
        have : (run n v C.gates).2.length ≤ C.gates.length := hle
        omega
      by_cases ho : C.output = (v : ℕ)
      · rw [ho, hvv] at hd; cases hd
      · have h1 := h7 heq (List.ofFn x) (by simp) C.output ho
        have h2 := hx x
        rw [hd] at h1 h2
        exact hxd (h1.symm.trans h2)
    · intro x
      have := hx x
      rw [hd] at this
      exact this

end PEqualNP.Outside.L_meta_5371

theorem PEqualNP.Outside.L_meta_5371 : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size = x3 → PEqualNP.TopForm.IsAO2 x1 x4 → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x4.eval (List.ofFn (Function.update x7 x2 Bool.false)) ≠ x4.eval (List.ofFn (Function.update x8 x2 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size ≤ x4.size ∧ ((∃ (x9 : Fin x1 → Bool), x4.eval (List.ofFn x9) ≠ x4.eval (List.ofFn (Function.update x9 x2 Bool.false))) → x8.size < x4.size) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval (List.ofFn (Function.update x9 x2 Bool.false)) :=
  PEqualNP.Outside.L_meta_5371.main
