import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_986

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem fold_getD_prefix (suf : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (suf.foldl step w).getD i false = w.getD i false := by
  induction suf with
  | nil => intro w i _; rfl
  | cons g suf ih =>
    intro w i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [step, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi]

theorem val_prefix {n : ℕ} (pre suf : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + pre.length) : val (pre ++ suf) x i = val pre x i := by
  unfold val
  rw [List.foldl_append, fold_getD_prefix]
  rw [fold_length]
  simp only [List.length_ofFn]
  exact hi

theorem val_split {n : ℕ} (gs pre suf : List Gate) (g : Gate) (x : Fin n → Bool)
    (hdec : gs = pre ++ g :: suf) :
    val gs x (n + pre.length) = g.op.eval (g.inputs.map fun j => val pre x j) := by
  subst hdec
  have h : pre ++ g :: suf = (pre ++ [g]) ++ suf := by simp
  rw [h, val_prefix _ _ _ _ (by simp), val_snoc, if_pos rfl]

theorem not_true {n : ℕ} (gs pre suf : List Gate) (g : Gate) (x : Fin n → Bool) (hw : ℕ)
    (hdec : gs = pre ++ g :: suf) (hop : g.op = GateOp.not) (hhead : g.inputs.head? = some hw)
    (hlt : hw < n + pre.length) (hfalse : val gs x hw = false) :
    g.op.eval (g.inputs.map fun j => val pre x j) = true := by
  subst hdec
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp hhead
  have hpre : val pre x hw = false := by
    have h := hfalse
    rw [val_prefix _ _ _ _ hlt] at h
    exact h
  rw [hop, hrest]
  simp [GateOp.eval, hpre]

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (W : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ W)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (W R : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, u ∈ R → v ∈ R → val gs (Zof W) i = false → val gs (eof u) i = true →
    val gs (eof v) i = true → u ∈ W ∧ l u = l v

def Cnt {n : ℕ} (W R : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof W) i = false ∧
    ∃ u v : Fin n, u ∈ R ∧ v ∈ R ∧ u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (W R : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt W R gs i

def Good {n : ℕ} (W : Finset (Fin n)) (pre : List Gate) (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    g.op.eval (g.inputs.map fun j => val pre (Zof W) j) = true

theorem D_mono {n : ℕ} (W R : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D W R gs ⊆ D W R (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huR, hvR, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huR, hvR, huv, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

theorem main_inv {n : ℕ} (W R : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ pre g, pre ++ [g] <+: gs → Good W pre g) :
    ∃ l : Fin n → Fin n, Inv W R gs l ∧
      (W ∩ R).card ≤ ((W ∩ R).image l).card + (D W R gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v _ _ hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ :=
      ih (fun pre g' h => hg pre g' (h.trans (List.prefix_append gs [g])))
    have hgood := hg gs g (List.prefix_refl _)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    have key : P (Zof W) = false → ∀ u ∈ R, P (eof u) = true →
        u ∈ W ∧ ∃ A B : Fin n → Prop, (∀ w ∈ R, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', w ∈ R → w' ∈ R → A w → A w' → l w = l w') ∧
          (∀ w w', w ∈ R → w' ∈ R → B w → B w' → l w = l w') := by
      intro hz u huR hu
      rcases hgood with ⟨hop, hlen⟩ | htrue
      · rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof W) with hall | ⟨a, b, hab⟩
        · have := hall (eof u)
          simp only [hP] at hu
          rw [this] at hu
          exact absurd hu (by simp)
        · obtain ⟨ha, hb, hy⟩ := hab hz
          refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
            fun w _ hw => hy (eof w) hw,
            fun w w' hwR hw'R hw hw' => (hinv a w w' hwR hw'R ha hw hw').2,
            fun w w' hwR hw'R hw hw' => (hinv b w w' hwR hw'R hb hw hw').2⟩
          rcases hy (eof u) hu with h | h
          · exact (hinv a u u huR huR ha h h).1
          · exact (hinv b u u huR huR hb h h).1
      · have h' : P (Zof W) = true := htrue
        rw [hz] at h'
        exact absurd h' (by decide)
    by_cases hm : P (Zof W) = false ∧
        ∃ u v, u ∈ R ∧ v ∈ R ∧ P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0R, hv0R, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v huR hvR hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u huR hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w ∈ R, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hwR hw
            rcases hAB w hwR hw with h | h <;> rcases hAB u0 hu0R hu0 with h0 | h0 <;>
              rcases hAB v0 hv0R hv0 with h1 | h1
            · exact Or.inl (hA w u0 hwR hu0R h h0)
            · exact Or.inl (hA w u0 hwR hu0R h h0)
            · exact Or.inr (hA w v0 hwR hv0R h h1)
            · exact absurd (hB u0 v0 hu0R hv0R h0 h1) hne
            · exact absurd (hA u0 v0 hu0R hv0R h0 h1) hne
            · exact Or.inr (hB w v0 hwR hv0R h h1)
            · exact Or.inl (hB w u0 hwR hu0R h h0)
            · exact Or.inl (hB w u0 hwR hu0R h h0)
          have red : ∀ w ∈ R, P (eof w) = true →
              (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hwR hw
            rcases two w hwR hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [if_pos h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u huR hiu, red v hvR hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v huR hvR hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : (W ∩ R).image l ⊆
            insert (l v0) ((W ∩ R).image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [if_neg h]
        have h1 : ((W ∩ R).image l).card ≤
            ((W ∩ R).image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D W R (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, hu0R, hv0R, ?_, ?_, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D W R gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D W R gs).card + 1 ≤ (D W R (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono W R gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v huR hvR hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u huR hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, huR, hvR, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v huR hvR hiz hiu hiv
      · have := Finset.card_le_card (D_mono W R gs g)
        omega

def Wset {n : ℕ} (S T : Finset (Fin n)) : Finset (Fin n) := S ∪ T

open Classical in
noncomputable def Rset {n : ℕ} (S T : Finset (Fin n)) (t0 : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun c => c ∉ T ∨ (c = t0 ∧ t0 ∈ S)

theorem mem_Rset {n : ℕ} (S T : Finset (Fin n)) (t0 c : Fin n) :
    c ∈ Rset S T t0 ↔ (c ∉ T ∨ (c = t0 ∧ t0 ∈ S)) := by
  classical
  simp [Rset]

theorem RW_sub {n : ℕ} (S T : Finset (Fin n)) (t0 c : Fin n) (hR : c ∈ Rset S T t0)
    (hW : c ∈ Wset S T) : c ∈ S := by
  rw [mem_Rset] at hR
  have hW' : c ∈ S ∨ c ∈ T := Finset.mem_union.mp hW
  rcases hR with h | ⟨rfl, h⟩
  · exact hW'.resolve_right h
  · exact h

theorem R_mono {n : ℕ} (S S' T : Finset (Fin n)) (t0 : Fin n) (h : t0 ∈ S → t0 ∈ S') :
    ∀ c ∈ Rset S T t0, c ∈ Rset S' T t0 := by
  intro c hc
  rw [mem_Rset] at hc ⊢
  rcases hc with hc | ⟨hc, hs⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hc, h hs⟩

theorem WR_eq {n : ℕ} (S T : Finset (Fin n)) (t0 : Fin n) :
    Wset S T ∩ Rset S T t0 = S \ T.erase t0 := by
  ext c
  rw [Finset.mem_inter, mem_Rset, Finset.mem_sdiff, Finset.mem_erase]
  have hW : c ∈ Wset S T ↔ c ∈ S ∨ c ∈ T := Finset.mem_union
  rw [hW]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h2 with h2 | ⟨rfl, h3⟩
    · exact ⟨h1.resolve_right h2, fun h => h2 h.2⟩
    · exact ⟨h3, fun h => h.1 rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨Or.inl h1, ?_⟩
    by_cases hc : c ∈ T
    · right
      have hct : c = t0 := by
        by_contra hne
        exact h2 ⟨hne, hc⟩
      subst hct
      exact ⟨rfl, h1⟩
    · exact Or.inl hc

theorem Zof_T {n : ℕ} (S T : Finset (Fin n)) (t : Fin n) (ht : t ∈ T) :
    Zof (Wset S T) t = false := by
  have : t ∈ Wset S T := Finset.mem_union_right _ ht
  simp [Zof, this]

end PEqualNP.Outside.L_meta_986

open PEqualNP.Outside.L_meta_986 in
theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  intro n m S gates out i0 hw T t0 _hsz hS hops hnot hi0 hhw hhwlt hev hT _ht0 _hmax
  have hval : ∀ (o : Fin m) (x : Fin n → Bool),
      val gates x (out o) = decide (∃ v ∈ S o, x v = true) := fun o x => hev o x
  have hvanish : ∀ o, val gates (Zof (Wset (S o) T)) hw = false :=
    fun o => hT _ (fun t ht => Zof_T (S o) T t ht)
  have hgood : ∀ o pre g, pre ++ [g] <+: gates → Good (Wset (S o) T) pre g := by
    intro o pre g hpre
    obtain ⟨t, ht⟩ := hpre
    have hdec : gates = pre ++ g :: t := by rw [← ht]; simp
    have hgmem : g ∈ gates := by rw [hdec]; simp
    obtain ⟨hop, hlen⟩ := hops g hgmem
    rcases hop with h | h | h
    · exact Or.inl ⟨Or.inl h, hlen⟩
    · exact Or.inl ⟨Or.inr h, hlen⟩
    · right
      have hidx : pre.length < gates.length := by rw [hdec]; simp
      have h1 : gates[pre.length]? = some g := by rw [hdec]; simp
      have hget : gates[pre.length] = g := by
        rw [List.getElem?_eq_getElem hidx] at h1
        exact Option.some.inj h1
      have hq := hnot ⟨pre.length, hidx⟩ (by rw [List.get_eq_getElem]; simp only [hget]; exact h)
      have hlen0 : i0.val = pre.length := by rw [← hq]
      have hgi0 : gates.get i0 = g := by rw [← hq, List.get_eq_getElem]; exact hget
      have hhw' : g.inputs.head? = some hw := by rw [← hgi0]; exact hhw
      exact not_true gates pre t g _ hw hdec h hhw' (by omega) (hvanish o)
  have hNtrue : ∀ o, val gates (Zof (Wset (S o) T)) (n + i0.val) = true := by
    intro o
    have hdec : gates = gates.take i0.val ++ gates.get i0 :: gates.drop (i0.val + 1) := by
      rw [List.get_eq_getElem, ← List.drop_eq_getElem_cons i0.isLt, List.take_append_drop]
    have hlen : (gates.take i0.val).length = i0.val := by
      rw [List.length_take]
      exact Nat.min_eq_left i0.isLt.le
    have hs := val_split gates (gates.take i0.val) (gates.drop (i0.val + 1)) (gates.get i0)
      (Zof (Wset (S o) T)) hdec
    rw [hlen] at hs
    rw [hs]
    exact not_true gates _ _ _ _ hw hdec hi0 hhw (by omega) (hvanish o)
  choose l hinv hcard using fun o => main_inv (Wset (S o) T) (Rset (S o) T t0) gates (hgood o)
  have hZ : ∀ o, val gates (Zof (Wset (S o) T)) (out o) = false := by
    intro o
    rw [hval]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv
    simp [Zof, Wset, hv]
  have hE : ∀ o, ∀ u ∈ S o, val gates (eof u) (out o) = true := by
    intro o u hu
    rw [hval]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  have hbound : ∀ o, (S o \ T.erase t0).card - 1 ≤
      (D (Wset (S o) T) (Rset (S o) T t0) gates).card := by
    intro o
    have h1 : ((Wset (S o) T ∩ Rset (S o) T t0).image (l o)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      have hu' := Finset.mem_inter.mp hu
      have hv' := Finset.mem_inter.mp hv
      have huS := RW_sub (S o) T t0 u hu'.2 hu'.1
      have hvS := RW_sub (S o) T t0 v hv'.2 hv'.1
      exact (hinv o (out o) u v hu'.2 hv'.2 (hZ o) (hE o u huS) (hE o v hvS)).2
    have h2 := hcard o
    rw [WR_eq] at h1 h2
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (Wset (S a) T) (Rset (S a) T t0) gates)
        (D (Wset (S b) T) (Rset (S b) T t0) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, hza, u, v, huRa, hvRa, huv, hu, hv⟩ := hia
    obtain ⟨-, hzb, u', v', huRb, hvRb, huv', hu', hv'⟩ := hib
    have pair : ∃ x y : Fin n, x ≠ y ∧ x ∈ Rset (S a) T t0 ∧ x ∈ Rset (S b) T t0 ∧
        y ∈ Rset (S a) T t0 ∧ y ∈ Rset (S b) T t0 ∧
        val gates (eof x) i = true ∧ val gates (eof y) i = true := by
      by_cases h : t0 ∈ S a → t0 ∈ S b
      · exact ⟨u, v, huv, huRa, R_mono _ _ T t0 h u huRa, hvRa, R_mono _ _ T t0 h v hvRa,
          hu, hv⟩
      · have h' : t0 ∈ S b → t0 ∈ S a := fun _ => (not_imp.mp h).1
        exact ⟨u', v', huv', R_mono _ _ T t0 h' u' huRb, huRb, R_mono _ _ T t0 h' v' hvRb,
          hvRb, hu', hv'⟩
    obtain ⟨x, y, hxy, hxa, hxb, hya, hyb, hx, hy⟩ := pair
    have hxSa := RW_sub (S a) T t0 x hxa (hinv a i x x hxa hxa hza hx hx).1
    have hySa := RW_sub (S a) T t0 y hya (hinv a i y y hya hya hza hy hy).1
    have hxSb := RW_sub (S b) T t0 x hxb (hinv b i x x hxb hxb hzb hx hx).1
    have hySb := RW_sub (S b) T t0 y hyb (hinv b i y y hyb hyb hzb hy hy).1
    have hsub : ({x, y} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hxSa, hxSb⟩
      · exact Finset.mem_inter.mpr ⟨hySa, hySb⟩
    have h2 : ({x, y} : Finset (Fin n)).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub
    have := hS a b hab
    omega
  have hsub : (Finset.univ.biUnion fun o => D (Wset (S o) T) (Rset (S o) T t0) gates) ⊆
      (Finset.Ico n (n + gates.length)).erase (n + i0.val) := by
    intro i hi
    obtain ⟨o, -, ho⟩ := Finset.mem_biUnion.mp hi
    simp only [D, Finset.mem_filter] at ho
    refine Finset.mem_erase.mpr ⟨?_, ho.1⟩
    intro hi0'
    have hz := ho.2.1
    rw [hi0', hNtrue o] at hz
    exact absurd hz (by decide)
  have hsum1 : ∑ o, ((S o \ T.erase t0).card - 1) ≤ gates.length - 1 := by
    calc ∑ o, ((S o \ T.erase t0).card - 1)
        ≤ ∑ o, (D (Wset (S o) T) (Rset (S o) T t0) gates).card :=
          Finset.sum_le_sum fun o _ => hbound o
      _ = (Finset.univ.biUnion fun o => D (Wset (S o) T) (Rset (S o) T t0) gates).card :=
          (Finset.card_biUnion hdisj).symm
      _ ≤ ((Finset.Ico n (n + gates.length)).erase (n + i0.val)).card :=
          Finset.card_le_card hsub
      _ = gates.length - 1 := by
          rw [Finset.card_erase_of_mem (by simp only [Finset.mem_Ico]; omega)]
          simp
  have hsum2 : ∀ o, (S o).card - 1 ≤
      ((S o \ T.erase t0).card - 1) + (S o ∩ T.erase t0).card := by
    intro o
    have := Finset.card_sdiff_add_card_inter (S o) (T.erase t0)
    omega
  have hsum3 : ∑ o, (S o ∩ T.erase t0).card =
      ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro o _
    rw [← Finset.card_filter]
    congr 1
    ext u
    simp [and_comm]
  have h1 := Finset.sum_le_sum fun o (_ : o ∈ (Finset.univ : Finset (Fin m))) => hsum2 o
  rw [Finset.sum_add_distrib, hsum3] at h1
  have hlen1 : 1 ≤ gates.length := by have := i0.isLt; omega
  omega
