import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_986_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
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

lemma gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
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

lemma not_gate_val (g : Gate) (f : ℕ → Bool) (h : ℕ) (hop : g.op = GateOp.not)
    (hhd : g.inputs.head? = some h) (hv : f h = false) :
    g.op.eval (g.inputs.map f) = true := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hhd ⊢
  subst hop
  cases ins with
  | nil => simp at hhd
  | cons a tl =>
    simp only [List.head?_cons, Option.some.injEq] at hhd
    subst hhd
    simp [GateOp.eval, hv]

def Zof {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ A)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (A B : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, u ∉ B → v ∉ B → val gs (Zof A) i = false → val gs (eof u) i = true →
    val gs (eof v) i = true → u ∈ A ∧ l u = l v

def Cnt {n : ℕ} (A B : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof A) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ u ∉ B ∧ v ∉ B ∧
      val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (A B : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt A B gs i

def Ok {n : ℕ} (A : Finset (Fin n)) (gs : List Gate) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length),
    ((gs[k].op = GateOp.and ∨ gs[k].op = GateOp.or) ∧ gs[k].inputs.length ≤ 2) ∨
    (gs[k].op = GateOp.not ∧ ∃ h : ℕ, gs[k].inputs.head? = some h ∧ h < n + k ∧
      val gs (Zof A) h = false)

lemma Ok_prefix {n : ℕ} (A : Finset (Fin n)) (gs : List Gate) (g : Gate)
    (h : Ok A (gs ++ [g])) : Ok A gs := by
  intro k hk
  have hk' : k < (gs ++ [g]).length := by simp; omega
  have hget : (gs ++ [g])[k]'hk' = gs[k] := List.getElem_append_left hk
  rcases h k hk' with h1 | ⟨hop, hh, hhd, hlt, hv⟩
  · left
    rw [hget] at h1
    exact h1
  · right
    rw [hget] at hop hhd
    refine ⟨hop, hh, hhd, hlt, ?_⟩
    rw [val_snoc, if_neg (by omega)] at hv
    exact hv

lemma D_mono {n : ℕ} (A B : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D A B gs ⊆ D A B (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, huB, hvB, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, huB, hvB, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

lemma not_true {n : ℕ} (A : Finset (Fin n)) (gs : List Gate) (hg : Ok A gs) :
    ∀ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.not →
      val gs (Zof A) (n + k) = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk hop
    have hk' : k < gs.length + 1 := by simpa using hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl] at hop
      have hlast := hg gs.length hk
      rw [hgl] at hlast
      rw [val_snoc, if_pos rfl]
      rcases hlast with ⟨hmono, -⟩ | ⟨-, h, hhd, hlt, hv⟩
      · rcases hmono with h | h <;> rw [hop] at h <;> cases h
      · rw [val_snoc, if_neg (by omega)] at hv
        exact not_gate_val g (fun j => val gs (Zof A) j) h hop hhd hv
    · have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget] at hop
      rw [val_snoc, if_neg (by omega)]
      exact ih (Ok_prefix A gs g hg) k hk2 hop

lemma main_inv {n : ℕ} (A B : Finset (Fin n)) (gs : List Gate) (hg : Ok A gs) :
    ∃ l : Fin n → Fin n, Inv A B gs l ∧
      (A \ B).card ≤ ((A \ B).image l).card + (D A B gs).card := by
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
    obtain ⟨l, hinv, hcard⟩ := ih (Ok_prefix A gs g hg)
    have hlen0 : gs.length < (gs ++ [g]).length := by simp
    have hgl : (gs ++ [g])[gs.length]'hlen0 = g := by simp
    have hlast := hg gs.length hlen0
    rw [hgl] at hlast
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    rcases hlast with ⟨hop, hlen⟩ | ⟨hop, h, hhd, hlt, hv⟩
    · have key : P (Zof A) = false → ∀ u, u ∉ B → P (eof u) = true →
          u ∈ A ∧ ∃ X Y : Fin n → Prop, (∀ w, w ∉ B → P (eof w) = true → X w ∨ Y w) ∧
            (∀ w w', X w → X w' → l w = l w') ∧ (∀ w w', Y w → Y w' → l w = l w') := by
        intro hz u huB hu
        rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof A) with hall | ⟨a, b, hab⟩
        · have := hall (eof u)
          simp only [hP] at hu
          rw [this] at hu
          exact absurd hu (by simp)
        · obtain ⟨ha, hb, hy⟩ := hab hz
          refine ⟨?_, fun w => w ∉ B ∧ val gs (eof w) a = true,
            fun w => w ∉ B ∧ val gs (eof w) b = true, fun w hwB hw => ?_,
            fun w w' hw hw' => (hinv a w w' hw.1 hw'.1 ha hw.2 hw'.2).2,
            fun w w' hw hw' => (hinv b w w' hw.1 hw'.1 hb hw.2 hw'.2).2⟩
          · rcases hy (eof u) hu with h | h
            · exact (hinv a u u huB huB ha h h).1
            · exact (hinv b u u huB huB hb h h).1
          · rcases hy (eof w) hw with h | h
            · exact Or.inl ⟨hwB, h⟩
            · exact Or.inr ⟨hwB, h⟩
      by_cases hm : P (Zof A) = false ∧ ∃ u v, u ∉ B ∧ v ∉ B ∧ P (eof u) = true ∧
          P (eof v) = true ∧ l u ≠ l v
      · obtain ⟨hz, u0, v0, hu0B, hv0B, hu0, hv0, hne⟩ := hm
        refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
        · intro i u v huB hvB hiz hiu hiv
          by_cases hi : i = N
          · subst hi
            rw [hnew] at hiz hiu hiv
            obtain ⟨huA, X, Y, hXY, hX, hY⟩ := key hiz u huB hiu
            refine ⟨huA, ?_⟩
            have two : ∀ w, w ∉ B → P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
              intro w hwB hw
              rcases hXY w hwB hw with h | h <;> rcases hXY u0 hu0B hu0 with h0 | h0 <;>
                rcases hXY v0 hv0B hv0 with h1 | h1
              · exact Or.inl (hX w u0 h h0)
              · exact Or.inl (hX w u0 h h0)
              · exact Or.inr (hX w v0 h h1)
              · exact absurd (hY u0 v0 h0 h1) hne
              · exact absurd (hX u0 v0 h0 h1) hne
              · exact Or.inr (hY w v0 h h1)
              · exact Or.inl (hY w u0 h h0)
              · exact Or.inl (hY w u0 h h0)
            have red : ∀ w, w ∉ B → P (eof w) = true →
                (if l w = l v0 then l u0 else l w) = l u0 := by
              intro w hwB hw
              rcases two w hwB hw with h | h
              · rw [h]; split_ifs <;> rfl
              · rw [if_pos h]
            show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
            rw [red u huB hiu, red v hvB hiv]
          · rw [hold _ _ hi] at hiz hiu hiv
            obtain ⟨huA, hl⟩ := hinv i u v huB hvB hiz hiu hiv
            refine ⟨huA, ?_⟩
            show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
            rw [hl]
        · have himg : (A \ B).image l ⊆
              insert (l v0) ((A \ B).image fun w => if l w = l v0 then l u0 else l w) := by
            intro y hy
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
            by_cases h : l w = l v0
            · rw [h]; exact Finset.mem_insert_self _ _
            · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
              rw [if_neg h]
          have h1 : ((A \ B).image l).card ≤
              ((A \ B).image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
            (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
          have hNin : N ∈ D A B (gs ++ [g]) := by
            simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
              List.length_cons, List.length_nil]
            refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, hu0B, hv0B, ?_, ?_⟩
            · rw [hnew]; exact hz
            · intro h; exact hne (by rw [h])
            · rw [hnew]; exact hu0
            · rw [hnew]; exact hv0
          have hNnot : N ∉ D A B gs := by
            simp only [D, Finset.mem_filter, Finset.mem_Ico]
            intro h
            omega
          have h2 : (D A B gs).card + 1 ≤ (D A B (gs ++ [g])).card := by
            rw [← Finset.card_insert_of_notMem hNnot]
            apply Finset.card_le_card
            intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact hNin
            · exact D_mono A B gs g hi
          omega
      · refine ⟨l, ?_, ?_⟩
        · intro i u v huB hvB hiz hiu hiv
          by_cases hi : i = N
          · subst hi
            rw [hnew] at hiz hiu hiv
            obtain ⟨huA, -⟩ := key hiz u huB hiu
            refine ⟨huA, ?_⟩
            by_contra hne
            exact hm ⟨hiz, u, v, huB, hvB, hiu, hiv, hne⟩
          · rw [hold _ _ hi] at hiz hiu hiv
            exact hinv i u v huB hvB hiz hiu hiv
        · have := Finset.card_le_card (D_mono A B gs g)
          omega
    · have hPz : P (Zof A) = true := by
        rw [val_snoc, if_neg (by omega)] at hv
        exact not_gate_val g (fun j => val gs (Zof A) j) h hop hhd hv
      refine ⟨l, ?_, ?_⟩
      · intro i u v huB hvB hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew, hPz] at hiz
          exact absurd hiz (by simp)
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v huB hvB hiz hiu hiv
      · have := Finset.card_le_card (D_mono A B gs g)
        omega

def Bof {n m : ℕ} (S : Fin m → Finset (Fin n)) (T : Finset (Fin n)) (t0 : Fin n)
    (o : Fin m) : Finset (Fin n) :=
  if t0 ∈ S o then T.erase t0 else T

lemma sdiff_Bof {n m : ℕ} (S : Fin m → Finset (Fin n)) (T : Finset (Fin n)) (t0 : Fin n)
    (o : Fin m) : (S o ∪ T) \ Bof S T t0 o = S o \ T.erase t0 := by
  ext x
  unfold Bof
  by_cases h : t0 ∈ S o
  · by_cases hx : x = t0
    · subst hx
      simp [h]
    · simp [h, hx]
      tauto
  · by_cases hx : x = t0
    · subst hx
      simp [h]
    · simp [h, hx]

lemma Bof_sub {n m : ℕ} (S : Fin m → Finset (Fin n)) (T : Finset (Fin n)) (t0 : Fin n)
    (a b : Fin m) : Bof S T t0 a ⊆ Bof S T t0 b ∨ Bof S T t0 b ⊆ Bof S T t0 a := by
  unfold Bof
  split_ifs
  · exact Or.inl (Finset.Subset.refl _)
  · exact Or.inl (Finset.erase_subset _ _)
  · exact Or.inr (Finset.erase_subset _ _)
  · exact Or.inl (Finset.Subset.refl _)

lemma main (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
    (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (hi0 : (gates.get i0).op = GateOp.not)
    (hhd : (gates.get i0).inputs.head? = some hw)
    (hlt : hw < n + i0.val)
    (hev : ∀ (o : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true))
    (hT : ∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) →
      Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) :
    1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length +
      ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  have hval : ∀ (o : Fin m) (x : Fin n → Bool),
      val gates x (out o) = decide (∃ v ∈ S o, x v = true) := fun o x => hev o x
  have hvalT : ∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → val gates y hw = false :=
    fun y hy => hT y hy
  have hOk : ∀ o : Fin m, Ok (S o ∪ T) gates := by
    intro o k hk
    by_cases hk0 : k = i0.val
    · right
      subst hk0
      refine ⟨hi0, hw, hhd, hlt, hvalT _ ?_⟩
      intro t ht
      simp [Zof, ht]
    · left
      obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (congrArg Fin.val (hnot ⟨k, hk⟩ h)) hk0
  choose l hinv hcard using fun o : Fin m => main_inv (S o ∪ T) (Bof S T t0 o) gates (hOk o)
  have hZ : ∀ o, val gates (Zof (S o ∪ T)) (out o) = false := by
    intro o
    rw [hval, decide_eq_false_iff_not]
    rintro ⟨v, hv, hzv⟩
    simp [Zof, hv] at hzv
  have hE : ∀ o, ∀ u ∈ S o, val gates (eof u) (out o) = true := by
    intro o u hu
    rw [hval]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  have hmemS : ∀ (o : Fin m) (x : Fin n), x ∈ S o ∪ T → x ∉ Bof S T t0 o → x ∈ S o := by
    intro o x hx hnx
    have hx2 : x ∈ (S o ∪ T) \ Bof S T t0 o := Finset.mem_sdiff.mpr ⟨hx, hnx⟩
    rw [sdiff_Bof] at hx2
    exact (Finset.mem_sdiff.mp hx2).1
  have hbound : ∀ o, (S o \ T.erase t0).card - 1 ≤ (D (S o ∪ T) (Bof S T t0 o) gates).card := by
    intro o
    have h1 : (((S o ∪ T) \ Bof S T t0 o).image (l o)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨hu1, hu2⟩ := Finset.mem_sdiff.mp hu
      obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.mp hv
      exact (hinv o (out o) u v hu2 hv2 (hZ o) (hE o u (hmemS o u hu1 hu2))
        (hE o v (hmemS o v hv1 hv2))).2
    have h2 := hcard o
    have h3 : ((S o ∪ T) \ Bof S T t0 o).card = (S o \ T.erase t0).card := by
      rw [sdiff_Bof]
    omega
  have hdisj1 : ∀ a b : Fin m, a ≠ b → Bof S T t0 a ⊆ Bof S T t0 b →
      Disjoint (D (S a ∪ T) (Bof S T t0 a) gates) (D (S b ∪ T) (Bof S T t0 b) gates) := by
    intro a b hab hsubab
    rw [Finset.disjoint_left]
    intro i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, hza, -⟩ := hia
    obtain ⟨-, hzb, u, v, huv, huB, hvB, hu, hv⟩ := hib
    have huBa : u ∉ Bof S T t0 a := fun h => huB (hsubab h)
    have hvBa : v ∉ Bof S T t0 a := fun h => hvB (hsubab h)
    have hua := hmemS a u (hinv a i u u huBa huBa hza hu hu).1 huBa
    have hva := hmemS a v (hinv a i v v hvBa hvBa hza hv hv).1 hvBa
    have hub := hmemS b u (hinv b i u u huB huB hzb hu hu).1 huB
    have hvb := hmemS b v (hinv b i v v hvB hvB hzb hv hv).1 hvB
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, hub⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
    have h2 : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have h3 := Finset.card_le_card hsub
    have h4 := hS a b hab
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (S a ∪ T) (Bof S T t0 a) gates) (D (S b ∪ T) (Bof S T t0 b) gates) := by
    intro a _ b _ hab
    rcases Bof_sub S T t0 a b with h | h
    · exact hdisj1 a b hab h
    · exact (hdisj1 b a (Ne.symm hab) h).symm
  have hnotD : ∀ o : Fin m, n + i0.val ∉ D (S o ∪ T) (Bof S T t0 o) gates := by
    intro o hmem
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hmem
    obtain ⟨-, hz, -⟩ := hmem
    have htrue := not_true (S o ∪ T) gates (hOk o) i0.val i0.isLt hi0
    rw [htrue] at hz
    exact absurd hz (by simp)
  have hcount : ∑ o : Fin m, (D (S o ∪ T) (Bof S T t0 o) gates).card + 1 ≤ gates.length := by
    have hsubset : (Finset.univ.biUnion fun o : Fin m => D (S o ∪ T) (Bof S T t0 o) gates) ⊆
        (Finset.Ico n (n + gates.length)).erase (n + i0.val) := by
      intro i hi
      obtain ⟨o, -, ho⟩ := Finset.mem_biUnion.mp hi
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · rintro rfl
        exact hnotD o ho
      · simp only [D, Finset.mem_filter] at ho
        exact ho.1
    have hc1 := Finset.card_le_card hsubset
    rw [Finset.card_biUnion hdisj] at hc1
    have hmemI : n + i0.val ∈ Finset.Ico n (n + gates.length) := by
      simp [i0.isLt]
    rw [Finset.card_erase_of_mem hmemI, Nat.card_Ico] at hc1
    have := i0.isLt
    omega
  have hpt : ∀ s : Fin m, (S s).card - 1 ≤
      ((S s \ T.erase t0).card - 1) + (S s ∩ T.erase t0).card := by
    intro s
    have := Finset.card_sdiff_add_card_inter (S s) (T.erase t0)
    omega
  have hdc : ∑ s : Fin m, (S s ∩ T.erase t0).card =
      ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
    have h1 : ∀ s : Fin m, (S s ∩ T.erase t0).card =
        ∑ u ∈ T.erase t0, if u ∈ S s then 1 else 0 := by
      intro s
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.card_filter]
  have hsum1 : ∑ s : Fin m, ((S s).card - 1) ≤
      ∑ s : Fin m, ((S s \ T.erase t0).card - 1) + ∑ s : Fin m, (S s ∩ T.erase t0).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun s _ => hpt s
  have hsum2 : ∑ s : Fin m, ((S s \ T.erase t0).card - 1) ≤
      ∑ o : Fin m, (D (S o ∪ T) (Bof S T t0 o) gates).card :=
    Finset.sum_le_sum fun s _ => hbound s
  rw [hdc] at hsum1
  omega

end PEqualNP.Outside.L_meta_986_aux

theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  intro n m S gates out i0 hw T t0 _ hS hg hnot hi0 hhd hlt hev hT _ _
  exact PEqualNP.Outside.L_meta_986_aux.main n m S gates out i0 hw T t0 hS hg hnot hi0 hhd hlt
    hev hT
