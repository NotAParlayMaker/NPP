import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_986_aux

open PEqualNP.CircuitLowerBounds

-- Wire values, computed gate by gate, exactly as Circuit.wires does.
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

theorem fold_prefix (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl step w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem val_prefix {n : ℕ} (gs rest : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + gs.length) : val (gs ++ rest) x i = val gs x i := by
  unfold val
  rw [List.foldl_append]
  obtain ⟨t, ht⟩ := fold_prefix rest (gs.foldl step (List.ofFn x))
  rw [ht]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

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

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

-- The invariant, for a base point Z and a set V of allowed unit points.
def Inv {n : ℕ} (Z : Fin n → Bool) (V : Finset (Fin n)) (gs : List Gate)
    (l : Fin n → Fin n) : Prop :=
  ∀ i, ∀ u ∈ V, ∀ v ∈ V, val gs Z i = false → val gs (eof u) i = true →
    val gs (eof v) i = true → Z u = false ∧ l u = l v

def Cnt {n : ℕ} (Z : Fin n → Bool) (V : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs Z i = false ∧
    ∃ u ∈ V, ∃ v ∈ V, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (Z : Fin n → Bool) (V : Finset (Fin n)) (gs : List Gate) :
    Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt Z V gs i

theorem D_mono {n : ℕ} (Z : Fin n → Bool) (V : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D Z V gs ⊆ D Z V (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, hu, v, hv, huv, hu1, hv1⟩ := hi.2
  refine ⟨?_, u, hu, v, hv, huv, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu1
  · rw [val_snoc, if_neg hne]; exact hv1

-- Every gate is a fan-in two AND or OR gate, or is true at the base point Z.
def Good {n : ℕ} (Z : Fin n → Bool) (gs : List Gate) : Prop :=
  ∀ (gs1 gs2 : List Gate) (g : Gate), gs = gs1 ++ g :: gs2 →
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
      g.op.eval (g.inputs.map fun j => val gs1 Z j) = true

theorem good_init {n : ℕ} (Z : Fin n → Bool) (gs : List Gate) (g : Gate)
    (h : Good Z (gs ++ [g])) : Good Z gs := by
  intro gs1 gs2 g' he
  exact h gs1 (gs2 ++ [g]) g' (by rw [he]; simp)

theorem main_inv {n : ℕ} (Z : Fin n → Bool) (V : Finset (Fin n)) (gs : List Gate)
    (hg : Good Z gs) :
    ∃ l : Fin n → Fin n, Inv Z V gs l ∧
      ∀ Q : Finset (Fin n), Q.card ≤ (Q.image l).card + (D Z V gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, fun Q => by simp⟩
    intro i u _ v _ hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, eof, decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (good_init Z gs g hg)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    have hDmono := Finset.card_le_card (D_mono Z V gs g)
    rcases hg gs [] g (by simp) with ⟨hop, hlen⟩ | htrue
    · have key : P Z = false → ∀ u ∈ V, P (eof u) = true →
          Z u = false ∧ ∃ A B : Fin n → Prop, (∀ w ∈ V, P (eof w) = true → A w ∨ B w) ∧
            (∀ w ∈ V, ∀ w' ∈ V, A w → A w' → l w = l w') ∧
            (∀ w ∈ V, ∀ w' ∈ V, B w → B w' → l w = l w') := by
        intro hz u huV hu
        rcases gate_cases g hop hlen (fun x j => val gs x j) Z with hall | ⟨a, b, hab⟩
        · have := hall (eof u)
          simp only [hP] at hu
          rw [this] at hu
          exact absurd hu (by simp)
        · obtain ⟨ha, hb, hy⟩ := hab hz
          refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
            fun w _ hw => hy (eof w) hw,
            fun w hw w' hw' h1 h2 => (hinv a w hw w' hw' ha h1 h2).2,
            fun w hw w' hw' h1 h2 => (hinv b w hw w' hw' hb h1 h2).2⟩
          rcases hy (eof u) hu with h | h
          · exact (hinv a u huV u huV ha h h).1
          · exact (hinv b u huV u huV hb h h).1
      by_cases hm : P Z = false ∧
          ∃ u ∈ V, ∃ v ∈ V, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
      · obtain ⟨hz, u0, hu0V, v0, hv0V, hu0, hv0, hne⟩ := hm
        refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
        · intro i u huV v hvV hiz hiu hiv
          by_cases hi : i = N
          · subst hi
            rw [hnew] at hiz hiu hiv
            obtain ⟨huZ, A, B, hAB, hA, hB⟩ := key hiz u huV hiu
            refine ⟨huZ, ?_⟩
            have two : ∀ w ∈ V, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
              intro w hwV hw
              rcases hAB w hwV hw with h | h <;> rcases hAB u0 hu0V hu0 with h0 | h0 <;>
                rcases hAB v0 hv0V hv0 with h1 | h1
              · exact Or.inl (hA w hwV u0 hu0V h h0)
              · exact Or.inl (hA w hwV u0 hu0V h h0)
              · exact Or.inr (hA w hwV v0 hv0V h h1)
              · exact absurd (hB u0 hu0V v0 hv0V h0 h1) hne
              · exact absurd (hA u0 hu0V v0 hv0V h0 h1) hne
              · exact Or.inr (hB w hwV v0 hv0V h h1)
              · exact Or.inl (hB w hwV u0 hu0V h h0)
              · exact Or.inl (hB w hwV u0 hu0V h h0)
            have red : ∀ w ∈ V, P (eof w) = true →
                (if l w = l v0 then l u0 else l w) = l u0 := by
              intro w hwV hw
              rcases two w hwV hw with h | h
              · rw [h]; split_ifs <;> rfl
              · rw [if_pos h]
            show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
            rw [red u huV hiu, red v hvV hiv]
          · rw [hold _ _ hi] at hiz hiu hiv
            obtain ⟨huZ, hl⟩ := hinv i u huV v hvV hiz hiu hiv
            refine ⟨huZ, ?_⟩
            show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
            rw [hl]
        · intro Q
          have himg : Q.image l ⊆
              insert (l v0) (Q.image fun w => if l w = l v0 then l u0 else l w) := by
            intro y hy
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
            by_cases h : l w = l v0
            · rw [h]; exact Finset.mem_insert_self _ _
            · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
              rw [if_neg h]
          have h1 : (Q.image l).card ≤
              (Q.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
            (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
          have hNin : N ∈ D Z V (gs ++ [g]) := by
            simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
              List.length_cons, List.length_nil]
            refine ⟨⟨by omega, by omega⟩, ?_, u0, hu0V, v0, hv0V, ?_, ?_, ?_⟩
            · rw [hnew]; exact hz
            · intro h; exact hne (by rw [h])
            · rw [hnew]; exact hu0
            · rw [hnew]; exact hv0
          have hNnot : N ∉ D Z V gs := by
            simp only [D, Finset.mem_filter, Finset.mem_Ico]
            intro h
            omega
          have h2 : (D Z V gs).card + 1 ≤ (D Z V (gs ++ [g])).card := by
            rw [← Finset.card_insert_of_notMem hNnot]
            apply Finset.card_le_card
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact hNin
            · exact D_mono Z V gs g hi
          have := hcard Q
          omega
      · refine ⟨l, ?_, fun Q => (hcard Q).trans (by omega)⟩
        intro i u huV v hvV hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huZ, -⟩ := key hiz u huV hiu
          refine ⟨huZ, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, huV, v, hvV, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u huV v hvV hiz hiu hiv
    · refine ⟨l, ?_, fun Q => (hcard Q).trans (by omega)⟩
      intro i u huV v hvV hiz hiu hiv
      by_cases hi : i = N
      · subst hi
        rw [hnew] at hiz
        exact absurd htrue (by simp only [hP] at hiz; rw [hiz]; simp)
      · rw [hold _ _ hi] at hiz hiu hiv
        exact hinv i u huV v hvV hiz hiu hiv

theorem get_split (L a b : List Gate) (g : Gate) (hL : L = a ++ g :: b)
    (hq : a.length < L.length) : L.get ⟨a.length, hq⟩ = g := by
  subst hL
  simp

end PEqualNP.Outside.L_meta_986_aux

open PEqualNP.Outside.L_meta_986_aux in
theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  intro n m S gates out i0 hw T t0 _hS2 hS hops huniq hnot hhead hhw hev hT _ht0 _hmax
  -- base point for output s: zero on S s and on all of T, one elsewhere
  let Z : Fin m → Fin n → Bool := fun s c => decide (c ∉ S s ∧ c ∉ T)
  -- unit points allowed for output s: off T, plus t0 when t0 lies in S s
  let V : Fin m → Finset (Fin n) :=
    fun s => Finset.univ.filter (fun c => c ∉ T ∨ (c = t0 ∧ c ∈ S s))
  have hval : ∀ (s : Fin m) (x : Fin n → Bool),
      val gates x (out s) = decide (∃ v ∈ S s, x v = true) := fun s x => hev s x
  have hZT : ∀ s, val gates (Z s) hw = false := by
    intro s
    exact hT (Z s) (fun t ht => by simp [Z, ht])
  -- the NOT gate reads a wire that is false at every base point
  have hNOT : ∀ (a b : List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate), gates = a ++ g :: b →
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not →
      a.length = i0.val ∧ ∀ s, g.op.eval (g.inputs.map fun j => val a (Z s) j) = true := by
    intro a b g he hg
    have hq : a.length < gates.length := by rw [he]; simp
    have hget := get_split gates a b g he hq
    have hqi := huniq ⟨a.length, hq⟩ (by rw [hget]; exact hg)
    have hlen : a.length = i0.val := by rw [← hqi]
    have hgi : gates.get i0 = g := by rw [← hqi]; exact hget
    refine ⟨hlen, fun s => ?_⟩
    rw [hgi] at hhead
    have hpre : val a (Z s) hw = false := by
      rw [← val_prefix a (g :: b) (Z s) hw (by omega), ← he]
      exact hZT s
    cases hin : g.inputs with
    | nil => rw [hin] at hhead; simp at hhead
    | cons c rest =>
      rw [hin] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      rw [hg]
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval, hpre]
  have hgood : ∀ s, Good (Z s) gates := by
    intro s a b g he
    have hmem : g ∈ gates := by rw [he]; simp
    obtain ⟨hop3, hlen⟩ := hops g hmem
    rcases hop3 with h | h | h
    · exact Or.inl ⟨Or.inl h, hlen⟩
    · exact Or.inl ⟨Or.inr h, hlen⟩
    · exact Or.inr ((hNOT a b g he h).2 s)
  -- the NOT gate's own wire is true at every base point
  have hdec : gates = gates.take i0.val ++ gates.get i0 :: gates.drop (i0.val + 1) := by
    conv_lhs => rw [← List.take_append_drop i0.val gates]
    rw [List.drop_eq_getElem_cons i0.isLt]
    rfl
  have hNwire : ∀ s, val gates (Z s) (n + i0.val) = true := by
    intro s
    obtain ⟨hl1, hev1⟩ := hNOT _ _ _ hdec hnot
    have key : ∀ (k : ℕ) (L a b : List PEqualNP.CircuitLowerBounds.Gate)
        (g : PEqualNP.CircuitLowerBounds.Gate), L = (a ++ [g]) ++ b → a.length = k →
        g.op.eval (g.inputs.map fun j => val a (Z s) j) = true → val L (Z s) (n + k) = true := by
      intro k L a b g hL hk he
      subst hL
      rw [val_prefix _ _ _ _ (by simp; omega), val_snoc, if_pos (by omega)]
      exact he
    exact key i0.val gates (gates.take i0.val) (gates.drop (i0.val + 1)) (gates.get i0)
      (by rw [List.append_assoc, List.singleton_append]; exact hdec) hl1 (hev1 s)
  choose l hinv hcard using fun s => main_inv (Z s) (V s) gates (hgood s)
  set T' := T.erase t0 with hT'
  have memS : ∀ s, ∀ c ∈ V s, Z s c = false → c ∈ S s := by
    intro s c hc hz
    simp only [V, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [Z, decide_eq_false_iff_not, not_and, not_not] at hz
    by_contra hcs
    rcases hc with hc | hc
    · exact hc (hz hcs)
    · exact hcs hc.2
  have hbound : ∀ s, (S s \ T').card - 1 ≤ (D (Z s) (V s) gates).card := by
    intro s
    have hZ : val gates (Z s) (out s) = false := by
      rw [hval, decide_eq_false_iff_not]
      rintro ⟨v, hv, h⟩
      simp only [Z, decide_eq_true_eq] at h
      exact h.1 hv
    have hE : ∀ u ∈ S s, val gates (eof u) (out s) = true := by
      intro u hu
      rw [hval]
      simp only [decide_eq_true_eq]
      exact ⟨u, hu, by simp [eof]⟩
    have hV : ∀ u ∈ S s \ T', u ∈ V s := by
      intro u hu
      rw [Finset.mem_sdiff] at hu
      simp only [V, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : u = t0
      · exact Or.inr ⟨h, hu.1⟩
      · left
        intro huT
        exact hu.2 (by rw [hT']; exact Finset.mem_erase.mpr ⟨h, huT⟩)
    have h1 : ((S s \ T').image (l s)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv s (out s) u (hV u hu) v (hV v hv) hZ
        (hE u (Finset.mem_sdiff.mp hu).1) (hE v (Finset.mem_sdiff.mp hv).1)).2
    have := hcard s (S s \ T')
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (Z a) (V a) gates) (D (Z b) (V b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, hza, u, hua, v, hva, huv, hu, hv⟩ := hia
    obtain ⟨-, hzb, u', hub', v', hvb', huv', hu', hv'⟩ := hib
    have inS : ∀ s, val gates (Z s) i = false → ∀ c ∈ V s,
        val gates (eof c) i = true → c ∈ S s :=
      fun s hz c hc h => memS s c hc (hinv s i c hc c hc hz h h).1
    have swap : ∀ s s', ∀ c ∈ V s, c ≠ t0 → c ∈ V s' := by
      intro s s' c hc hct
      simp only [V, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact absurd hc.1 hct
    have pair : ∀ x y : Fin n, x ≠ y → x ∈ S a → x ∈ S b → y ∈ S a → y ∈ S b → False := by
      intro x y hxy hxa hxb hya hyb
      have hsub : ({x, y} : Finset (Fin n)) ⊆ S a ∩ S b := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hxa, hxb⟩
        · exact Finset.mem_inter.mpr ⟨hya, hyb⟩
      have h2 : ({x, y} : Finset (Fin n)).card = 2 := Finset.card_pair hxy
      have := Finset.card_le_card hsub
      have := hS a b hab
      omega
    by_cases ht : t0 ∈ V b
    · have sub : ∀ c ∈ V a, c ∈ V b := by
        intro c hc
        by_cases hct : c = t0
        · rw [hct]; exact ht
        · exact swap a b c hc hct
      exact pair u v huv (inS a hza u hua hu) (inS b hzb u (sub u hua) hu)
        (inS a hza v hva hv) (inS b hzb v (sub v hva) hv)
    · have sub : ∀ c ∈ V b, c ∈ V a := by
        intro c hc
        have hct : c ≠ t0 := by
          rintro rfl
          exact ht hc
        exact swap b a c hc hct
      exact pair u' v' huv' (inS a hza u' (sub u' hub') hu') (inS b hzb u' hub' hu')
        (inS a hza v' (sub v' hvb') hv') (inS b hzb v' hvb' hv')
  have hunion : (Finset.univ.biUnion fun s => D (Z s) (V s) gates) ⊆
      (Finset.Ico n (n + gates.length)).erase (n + i0.val) := by
    intro i hi
    obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.mp hi
    simp only [D, Finset.mem_filter] at hs
    refine Finset.mem_erase.mpr ⟨?_, hs.1⟩
    rintro rfl
    have := hs.2.1
    rw [hNwire s] at this
    exact absurd this (by simp)
  have hmain : ∑ s, ((S s \ T').card - 1) + 1 ≤ gates.length := by
    have hc1 : ∑ s, ((S s \ T').card - 1) ≤ ∑ s, (D (Z s) (V s) gates).card :=
      Finset.sum_le_sum fun s _ => hbound s
    have hc2 : ∑ s, (D (Z s) (V s) gates).card =
        (Finset.univ.biUnion fun s => D (Z s) (V s) gates).card :=
      (Finset.card_biUnion hdisj).symm
    have hc3 := Finset.card_le_card hunion
    have hmemI : n + i0.val ∈ Finset.Ico n (n + gates.length) := by
      simp only [Finset.mem_Ico]
      have := i0.isLt
      omega
    rw [Finset.card_erase_of_mem hmemI] at hc3
    simp only [Nat.card_Ico] at hc3
    have := i0.isLt
    omega
  have hsplit : ∑ s, ((S s).card - 1) ≤
      ∑ s, ((S s \ T').card - 1) + ∑ s, (S s ∩ T').card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    have := Finset.card_sdiff_add_card_inter (S s) T'
    omega
  have hcount : ∑ s, (S s ∩ T').card =
      ∑ u ∈ T', (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
    calc ∑ s, (S s ∩ T').card
        = ∑ s, ∑ u ∈ T', (if u ∈ S s then 1 else 0) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
      _ = ∑ u ∈ T', ∑ s, (if u ∈ S s then 1 else 0) := Finset.sum_comm
      _ = ∑ u ∈ T', (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.card_filter]
  omega
