import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5252

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


theorem simp_true (op : GateOp) (ds : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : ds.length ≤ 2) (hm : Sum.inl true ∉ ds)
    (h : simpG op ds = some (Sum.inl true)) : False := by
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl <;> simp [simpG] at h
  · rcases hop with rfl | rfl <;> rcases a with a | a <;> cases a <;> simp_all [simpG]
  · rcases hop with rfl | rfl <;> rcases a with a | a <;> rcases b with b | b <;>
      cases a <;> cases b <;> simp_all [simpG] <;> split_ifs at h <;> simp_all
  · simp at hl

theorem wiresOf_prefix (L R : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + L.length) :
    (wiresOf (L ++ R) x).getD i false = (wiresOf L x).getD i false := by
  induction R using List.reverseRecOn with
  | nil => simp
  | append_singleton R g ih =>
    rw [← List.append_assoc, wiresOf_snoc,
      List.getD_append _ _ _ _ (by rw [wiresOf_length]; simp; omega), ih]

def tgt (n gi w : ℕ) (ds : List (Bool ⊕ ℕ)) : Bool ⊕ ℕ :=
  if w = n + gi then Sum.inl false else ds.getD w (Sum.inl false)

def stepT (n gi w : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  if st.1.length = n + gi then (st.1 ++ [tgt n gi w st.1], st.2) else stepS n st g

def initW (n : ℕ) : List (Bool ⊕ ℕ) := (List.range n).map Sum.inr

def run (n gi w : ℕ) (L : List Gate) : List (Bool ⊕ ℕ) × List Gate :=
  L.foldl (stepT n gi w) (initW n, [])

def TVal (n gi w : ℕ) (W : List Bool) : Bool := if w = n + gi then false else W.getD w false

def P (n gi w : ℕ) (Cg : List Gate) (s : Bool) (x : List Bool) : Prop :=
  x.length = n ∧ ((wiresOf Cg x).getD (n + gi) false = s → TVal n gi w (wiresOf Cg x) ≠ !s)

def Mono (s a b : Bool) : Prop := if s = true then (a = true → b = true) else (b = true → a = true)

theorem mono_refl (s a : Bool) : Mono s a a := by cases s <;> simp [Mono]

theorem mono_eval (s : Bool) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (f f' : ℕ → Bool) (h : ∀ i, Mono s (f i) (f' i)) :
    Mono s (op.eval (l.map f)) (op.eval (l.map f')) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl <;> cases s <;> simp [Mono, GateOp.eval]
  · have ha := h a
    clear h
    rcases hop with rfl | rfl <;> cases s <;> cases hfa : f a <;> cases hfa' : f' a <;>
      simp_all [Mono, GateOp.eval]
  · have ha := h a
    have hb := h b
    clear h
    rcases hop with rfl | rfl <;> cases s <;> cases hfa : f a <;> cases hfa' : f' a <;>
      cases hfb : f b <;> cases hfb' : f' b <;> simp_all [Mono, GateOp.eval]
  · simp at hl

def GOk (n : ℕ) (gs : List Gate) : Prop :=
  ∀ k (hk : k < gs.length), (gs[k].op = GateOp.and ∨ gs[k].op = GateOp.or) ∧
    gs[k].inputs.length ≤ 2 ∧ ∀ i ∈ gs[k].inputs, i < n + k

def Inv (n gi w : ℕ) (Cg L : List Gate) (ds : List (Bool ⊕ ℕ)) (gs : List Gate) : Prop :=
  ds.length = n + L.length ∧
  (∀ s x, P n gi w Cg s x → ∀ i,
    Mono s ((wiresOf L x).getD i false) (val (wiresOf gs x) (ds.getD i (Sum.inl false)))) ∧
  (∀ v, Sum.inr v ∈ ds → v < n + gs.length) ∧
  Sum.inl true ∉ ds ∧ GOk n gs ∧
  gs.length ≤ L.length ∧ (gi < L.length → gs.length < L.length)

theorem inv_init (n gi w : ℕ) (Cg : List Gate) : Inv n gi w Cg [] (initW n) [] := by
  refine ⟨by simp [initW], ?_, ?_, ?_, ?_, by simp, by simp⟩
  · intro s x hx i
    have hxl := hx.1
    simp only [wiresOf, Circuit.wires, List.foldl_nil]
    by_cases hi : i < n
    · have hi' : i < (initW n).length := by simp [initW]; exact hi
      rw [List.getD_eq_getElem _ _ hi']
      simp [initW, val]
      exact mono_refl _ _
    · have hi' : (initW n).length ≤ i := by simp [initW]; omega
      have hi2 : x.length ≤ i := by omega
      rw [List.getD_eq_default _ _ hi', List.getD_eq_default _ _ hi2]
      exact mono_refl _ _
  · intro v hv; simp [initW] at hv; simp; exact hv
  · simp [initW]
  · intro k hk; simp at hk

theorem okop_of (op : GateOp) (h : op = GateOp.and ∨ op = GateOp.or) : OkOp op := by
  rcases h with rfl | rfl <;> simp [OkOp]

theorem inv_step (n gi w : ℕ) (hn : 0 < n) (hw : w ≤ n + gi) (Cg L : List Gate) (g : Gate)
    (hpre : L ++ [g] <+: Cg) (st : List (Bool ⊕ ℕ) × List Gate)
    (hI : Inv n gi w Cg L st.1 st.2)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv n gi w Cg (L ++ [g]) (stepT n gi w st g).1 (stepT n gi w st g).2 := by
  obtain ⟨ds, gs⟩ := st
  obtain ⟨hlen, hval, hbd, htr, hok, hle, hlt⟩ := hI
  simp only at hlen hval hbd htr hok hle hlt
  obtain ⟨R, hR⟩ := hpre
  have hW : ∀ x : List Bool, x.length = n → (wiresOf L x).length = n + L.length := by
    intro x hx; rw [wiresOf_length, hx]
  have hWg : ∀ x : List Bool, x.length = n → (wiresOf gs x).length = n + gs.length := by
    intro x hx; rw [wiresOf_length, hx]
  unfold stepT
  simp only
  by_cases hc : ds.length = n + gi
  · rw [if_pos hc]
    dsimp only
    have hLg : L.length = gi := by omega
    have htm : ∀ e, e = tgt n gi w ds → e ∈ ds ∨ e = Sum.inl false := by
      intro e he; subst he; unfold tgt; split_ifs
      · right; rfl
      · exact getD_mem ds _ w
    refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_, ?_, hok, by simp; omega, by simp; omega⟩
    · intro s x hx i
      have hxl := hx.1
      rcases lt_trichotomy i ds.length with h1 | h1 | h1
      · rw [List.getD_append _ _ _ _ h1, wiresOf_prefix L [g] x i (by omega)]; exact hval s x hx i
      · subst h1
        rw [getD_snoc, if_neg (lt_irrefl _), if_pos rfl]
        have e1 : (wiresOf (L ++ [g]) x).getD ds.length false =
            (wiresOf Cg x).getD (n + gi) false := by
          rw [← hR, wiresOf_prefix _ R x _ (by simp; omega), hc]
        rw [e1]
        have hq := hx.2
        have hv := hval s x hx w
        have hwl : w ≠ n + gi → (wiresOf Cg x).getD w false = (wiresOf L x).getD w false := by
          intro hwe
          rw [← hR, wiresOf_prefix (L ++ [g]) R x w (by simp; omega),
            wiresOf_prefix L [g] x w (by omega)]
        unfold TVal at hq
        unfold tgt
        revert hq hv hwl
        generalize (wiresOf Cg x).getD (n + gi) false = a
        generalize (wiresOf Cg x).getD w false = b
        generalize (wiresOf L x).getD w false = c
        intro hq hv hwl
        split_ifs at hq ⊢ with hwe
        · cases s <;> cases a <;> simp [Mono, val] at hq ⊢
        · rw [hwl hwe] at hq
          revert hv hq
          generalize val (wiresOf gs x) (ds.getD w (Sum.inl false)) = d
          cases s <;> cases a <;> cases c <;> cases d <;> simp [Mono]
      · have e1 : (ds ++ [tgt n gi w ds]).getD i (Sum.inl false) = Sum.inl false :=
          List.getD_eq_default _ _ (by simp; omega)
        have e2 : (wiresOf (L ++ [g]) x).getD i false = false :=
          List.getD_eq_default _ _ (by rw [wiresOf_length]; simp; omega)
        rw [e1, e2]
        exact mono_refl _ _
    · intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hbd v hv
      · rcases htm _ (List.mem_singleton.1 hv) with h | h
        · exact hbd v h
        · cases h
    · intro hv
      rcases List.mem_append.1 hv with hv | hv
      · exact htr hv
      · rcases htm _ (List.mem_singleton.1 hv) with h | h
        · exact htr h
        · cases h
  · rw [if_neg hc]
    have hLg : L.length ≠ gi := by omega
    set dg := g.inputs.map (fun i => ds.getD i (Sum.inl false)) with hdg
    have hdgl : dg.length ≤ 2 := by simp [hdg, hg.2]
    have hdgm : ∀ e ∈ dg, e ∈ ds ∨ e = Sum.inl false := by
      intro e he
      obtain ⟨i, -, hi⟩ := List.mem_map.1 he
      rw [← hi]; exact getD_mem ds _ i
    have hdgb : ∀ v, Sum.inr v ∈ dg → v < n + gs.length := by
      intro v hv
      rcases hdgm _ hv with h | h
      · exact hbd v h
      · cases h
    have hdgt : Sum.inl true ∉ dg := by
      intro hv
      rcases hdgm _ hv with h | h
      · exact htr h
      · cases h
    have hgate : ∀ s x, P n gi w Cg s x →
        Mono s (g.op.eval (g.inputs.map fun i => (wiresOf L x).getD i false))
          (g.op.eval (dg.map (val (wiresOf gs x)))) := by
      intro s x hx
      rw [hdg, List.map_map]
      exact mono_eval s g.op hg.1 _ hg.2 _ _ (fun i => hval s x hx i)
    unfold stepS
    simp only
    rcases hs : simpG g.op dg with _ | d
    · refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_, ?_, ?_, by simp; omega, ?_⟩
      · intro s x hx i
        have hxl := hx.1
        rw [wiresOf_snoc, wiresOf_snoc, getD_snoc, getD_snoc, hW x hxl, hlen]
        split_ifs with h1 h2
        · rw [val_snoc]
          · exact hval s x hx i
          · intro v hv; rw [hWg x hxl]
            rcases getD_mem ds (Sum.inl false) i with h | h <;> rw [hv] at h
            · exact hbd v h
            · cases h
        · simp only [val]; rw [getD_snoc, hWg x hxl]
          simp only [lt_irrefl, ite_false, ite_true]
          rw [simp_none _ _ _ (okop_of _ hg.1) hdgl hs]; exact hgate s x hx
        · exact mono_refl _ _
      · intro v hv
        simp only [List.mem_append, List.mem_singleton, Sum.inr.injEq] at hv
        simp only [List.length_append, List.length_singleton]
        rcases hv with hv | hv
        · have := hbd v hv; omega
        · omega
      · intro hv
        simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | hv
        · exact htr hv
        · cases hv
      · intro k hk
        simp only [List.length_append, List.length_singleton] at hk
        by_cases hk2 : k < gs.length
        · rw [List.getElem_append_left hk2]; exact hok k hk2
        · have hk3 : k = gs.length := by omega
          subst hk3
          rw [List.getElem_append_right (by simp)]
          simp only [Nat.sub_self, List.getElem_singleton]
          refine ⟨hg.1, by simp [hdg, hg.2], ?_⟩
          intro i hi
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hi
          rcases e with c | v
          · simp [toW]; exact Or.inl hn
          · simp [toW]; exact hdgb v he
      · intro hgi
        simp only [List.length_append, List.length_singleton] at hgi ⊢
        have : gi < L.length := by omega
        have := hlt this; omega
    · refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_, ?_, hok, by simp; omega, ?_⟩
      · intro s x hx i
        have hxl := hx.1
        rw [wiresOf_snoc, getD_snoc, getD_snoc, hW x hxl, hlen]
        split_ifs with h1 h2
        · exact hval s x hx i
        · rw [simp_some _ _ _ _ (okop_of _ hg.1) hdgl hs]; exact hgate s x hx
        · exact mono_refl _ _
      · intro v hv; simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | hv
        · exact hbd v hv
        · subst hv; exact hdgb v (simp_mem _ _ _ hs)
      · intro hv; simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | hv
        · exact htr hv
        · exact simp_true _ _ hg.1 hdgl hdgt (hv ▸ hs)
      · intro hgi
        simp only [List.length_append, List.length_singleton] at hgi ⊢
        have : gi < L.length := by omega
        have := hlt this; omega

theorem inv_run (n gi w : ℕ) (hn : 0 < n) (hw : w ≤ n + gi) (Cg : List Gate)
    (hC : ∀ g ∈ Cg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ L : List Gate, L <+: Cg → Inv n gi w Cg L (run n gi w L).1 (run n gi w L).2 := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _; exact inv_init n gi w Cg
  | append_singleton L g ih =>
    intro hL
    have hL' : L <+: Cg := (List.prefix_append L [g]).trans hL
    have h := inv_step n gi w hn hw Cg L g hL (run n gi w L) (ih hL')
      (hC g (hL.subset (by simp)))
    have hr : run n gi w (L ++ [g]) = stepT n gi w (run n gi w L) g := by
      simp [run, List.foldl_append]
    rw [hr]; exact h

end PEqualNP.Outside.L_meta_5252

open PEqualNP.Outside.L_meta_5252 in
theorem PEqualNP.Outside.L_meta_5252 : ∀ (x1 : Bool → List Bool → Prop) (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Bool) (x4 : List Bool), x1 x3 x4 → x4.length = (26 : ℕ)) → PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 → (∀ (x6 : Bool) (x7 : List Bool), x1 x6 x7 → x2.eval x7 = x6) → (¬∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), (PEqualNP.MetaComplexity.Monotone2 x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 ∧ ∀ (x8 : Bool) (x9 : List Bool), x1 x8 x9 → x7.eval x9 = x8) ∧ x7.size < x2.size) → ∀ x8 < x2.size, ∀ x10 ≤ (26 : ℕ) + x8, ∃ (x12 : Bool) (x13 : List Bool), x1 x12 x13 ∧ (x2.wires x13).getD ((26 : ℕ) + x8) Bool.false = x12 ∧ (if x10 = (26 : ℕ) + x8 then Bool.false else (x2.wires x13).getD x10 Bool.false) = !x12 := by
  intro T C hlen hmono _ hev hmin gi hgi w hw
  by_contra hcon
  have hwC : ∀ l, wiresOf C.gates l = C.wires l := fun _ => rfl
  have hC : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have := hmono g hg
    simpa using this
  have hP : ∀ b l, T b l → P 26 gi w C.gates b l := by
    intro b l hl
    refine ⟨hlen b l hl, ?_⟩
    intro hga hne
    exact hcon ⟨b, l, hl, hga, hne⟩
  obtain ⟨-, hval, hbd, htr, hok, -, hlt⟩ :=
    inv_run 26 gi w (by omega) hw C.gates hC C.gates (List.prefix_refl _)
  set ds := (run 26 gi w C.gates).1
  set gs := (run 26 gi w C.gates).2
  have hsz : gs.length < C.gates.length := hlt hgi
  let out : ℕ := match ds.getD C.output (Sum.inl false) with
    | Sum.inr v => v
    | Sum.inl _ => 26 + gs.length
  apply hmin
  refine ⟨⟨gs, out⟩, ⟨?_, ?_, ?_⟩, hsz⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
    obtain ⟨h1, h2, -⟩ := hok k hk
    refine ⟨?_, h2⟩
    rcases h1 with h | h <;> simp [h]
  · intro j hj i hi
    have hj' : j < gs.length := hj
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hj'] at hi
    exact (hok j hj').2.2 i hi
  · intro b l hl
    have hx := hP b l hl
    have hxl := hx.1
    have hm := hval b l hx C.output
    have e2 : (wiresOf C.gates l).getD C.output false = b := hev b l hl
    rw [e2] at hm
    have e3 : (wiresOf gs l).getD out false = val (wiresOf gs l) (ds.getD C.output (Sum.inl false)) := by
      simp only [out]
      rcases hd : ds.getD C.output (Sum.inl false) with c | v
      · have hc : c = false := by
          cases c
          · rfl
          · exfalso
            rcases getD_mem ds (Sum.inl false) C.output with h | h
            · rw [hd] at h; exact htr h
            · rw [hd] at h; cases h
        subst hc
        simp only [val]
        exact List.getD_eq_default _ _ (by rw [wiresOf_length]; omega)
      · rfl
    show (wiresOf gs l).getD out false = b
    rw [e3]
    revert hm
    generalize val (wiresOf gs l) (ds.getD C.output (Sum.inl false)) = d
    cases b <;> cases d <;> simp [Mono]
