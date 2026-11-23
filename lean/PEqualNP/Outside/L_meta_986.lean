import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
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

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (S : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, u ∈ S → v ∈ S → val gs z i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate) (i : ℕ) : Prop :=
  val gs z i = false ∧
    ∃ u v : Fin n, u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt S z gs i

theorem D_mono {n : ℕ} (S : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate) (g : Gate) :
    D S z gs ⊆ D S z (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huS, hvS, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huS, hvS, huv, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

theorem main_inv {n : ℕ} (S : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnt : ∀ j : Fin gs.length, (gs.get j).op = GateOp.not → val gs z (n + j.val) = true) :
    ∃ l : Fin n → Fin n, Inv S z gs l ∧ S.card ≤ (S.image l).card + (D S z gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v huS hvS hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      rfl
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg'])) (by
      intro j hj
      have h : val (gs ++ [g]) z (n + j.val) = true :=
        hnt ⟨j.val, by simp only [List.length_append, List.length_singleton]; omega⟩ (by simpa using hj)
      have hn : n + j.val ≠ n + gs.length := by have := j.isLt; omega
      simpa only [val_snoc, if_neg hn] using h)
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    -- facts about the new wire from the old invariant
    have key : P z = false → ∀ u, u ∈ S → P (eof u) = true →
        ∃ A B : Fin n → Prop, (∀ w, w ∈ S → P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', w ∈ S → w' ∈ S → A w → A w' → l w = l w') ∧ (∀ w w', w ∈ S → w' ∈ S → B w → B w' → l w = l w') := by
      intro hz u huS hu
      have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have h1 := hnt ⟨gs.length, by simp⟩ (by simpa using h)
          rw [hnew] at h1
          exact False.elim (by rw [hz] at h1; contradiction)
      rcases gate_cases g hop' hlen (fun x j => val gs x j) z with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        exact ⟨fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w _ hw => hy (eof w) hw,
          fun w w' hwS hwS' hw hw' => hinv a w w' hwS hwS' ha hw hw',
          fun w w' hwS hwS' hw hw' => hinv b w w' hwS hwS' hb hw hw'⟩
    by_cases hm : P z = false ∧ ∃ u v, u ∈ S ∧ v ∈ S ∧ P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, huS0, hvS0, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v huS hvS hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨A, B, hAB, hA, hB⟩ := key hiz u huS hiu
          have two : ∀ w, w ∈ S → P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hwS hw
            rcases hAB w hwS hw with h | h <;> rcases hAB u0 huS0 hu0 with h0 | h0 <;>
              rcases hAB v0 hvS0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 hwS huS0 h h0)
            · exact Or.inl (hA w u0 hwS huS0 h h0)
            · exact Or.inr (hA w v0 hwS hvS0 h h1)
            · exact absurd (hB u0 v0 huS0 hvS0 h0 h1) hne
            · exact absurd (hA u0 v0 huS0 hvS0 h0 h1) hne
            · exact Or.inr (hB w v0 hwS hvS0 h h1)
            · exact Or.inl (hB w u0 hwS huS0 h h0)
            · exact Or.inl (hB w u0 hwS huS0 h h0)
          have red : ∀ w, w ∈ S → P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hwS hw
            rcases two w hwS hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [if_pos h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u huS hiu, red v hvS hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          have hl := hinv i u v huS hvS hiz hiu hiv
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [if_neg h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S z (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, huS0, hvS0, ?_, ?_, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D S z gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S z gs).card + 1 ≤ (D S z (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S z gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v huS hvS hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          by_contra hne
          exact hm ⟨hiz, u, v, huS, hvS, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v huS hvS hiz hiu hiv
      · have := Finset.card_le_card (D_mono S z gs g)
        omega


theorem val_append_old {n : ℕ} (gs rest : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + gs.length) : val (gs ++ rest) x i = val gs x i := by
  induction rest using List.reverseRecOn with
  | nil => simp
  | append_singleton rest g ih =>
    rw [← List.append_assoc, val_snoc, if_neg (by simp only [List.length_append]; omega), ih]

theorem val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : Fin gs.length) :
    val gs x (n + j.val) = (gs.get j).op.eval
      ((gs.get j).inputs.map fun i => val (gs.take j.val) x i) := by
  have hs : gs = (gs.take j.val ++ [gs.get j]) ++ gs.drop (j.val + 1) := by
    simpa [List.append_assoc] using (List.take_append_getElem_drop gs j.val j.isLt).symm
  calc val gs x (n + j.val) =
      val ((gs.take j.val ++ [gs.get j]) ++ gs.drop (j.val + 1)) x (n + j.val) :=
        congrArg (fun l : List Gate => val l x (n + j.val)) hs
    _ = _ := by
      rw [val_append_old _ _ _ _ (by simp [List.length_take, Nat.min_eq_left j.isLt.le]),
        val_snoc]
      simp [List.length_take, Nat.min_eq_left j.isLt.le]

theorem support {n : ℕ} (A : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnt : ∀ j : Fin gs.length, (gs.get j).op = GateOp.not → val gs (Zof A) (n + j.val) = true) :
    ∀ i u, val gs (Zof A) i = false → val gs (eof u) i = true → u ∈ A := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i u hz hu
    rw [val_nil] at hz hu
    by_cases hi : i < n
    · simp only [hi, dite_true, eof, decide_eq_true_eq] at hu
      subst u
      simpa [val_nil, hi, Zof] using hz
    · simp [hi] at hu
  | append_singleton gs g ih =>
    have oldnt : ∀ j : Fin gs.length, (gs.get j).op = GateOp.not →
        val gs (Zof A) (n + j.val) = true := by
      intro j hj
      have h : val (gs ++ [g]) (Zof A) (n + j.val) = true :=
        hnt ⟨j.val, by simp only [List.length_append, List.length_singleton]; omega⟩
          (by simpa using hj)
      have hn : n + j.val ≠ n + gs.length := by have := j.isLt; omega
      simpa only [val_snoc, if_neg hn] using h
    have ih' := ih (fun g' hg' => hg g' (by simp [hg'])) oldnt
    intro i u hz hu
    by_cases hi : i = n + gs.length
    · subst i
      rw [val_snoc, if_pos rfl] at hz hu
      obtain ⟨hop, hlen⟩ := hg g (by simp)
      have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have hn := hnt ⟨gs.length, by simp⟩ (by simpa using h)
          rw [val_snoc, if_pos rfl, hz] at hn
          contradiction
      rcases gate_cases g hop' hlen (fun x j => val gs x j) (Zof A) with hf | ⟨a,b,hab⟩
      · have := hf (eof u)
        rw [this] at hu
        contradiction
      · obtain ⟨ha,hb,hh⟩ := hab hz
        rcases hh (eof u) hu with h | h
        · exact ih' a u ha h
        · exact ih' b u hb h
    · rw [val_snoc, if_neg hi] at hz hu
      exact ih' i u hz hu

end PEqualNP.Outside.L_meta_986

open PEqualNP.CircuitLowerBounds

open PEqualNP.Outside.L_meta_986 in
theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  intro n m S gates out i0 hw T t0 hsize hinter hg huniq hnot hhead hhw heval hclause ht0 hmax
  have not_true : ∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) →
      ∀ j : Fin gates.length, (gates.get j).op = GateOp.not →
        val gates y (n + j.val) = true := by
    intro y hy j hj
    have hj0 := huniq j hj
    subst j
    have hv : val (gates.take i0.val) y hw = false := by
      have ho := val_append_old (gates.take i0.val) (gates.drop i0.val) y hw
        (by simpa [List.length_take, Nat.min_eq_left i0.isLt.le] using hhw)
      rw [List.take_append_drop] at ho
      rw [← ho]
      exact hclause y hy
    rw [val_gate, hnot]
    cases hins : (gates.get i0).inputs with
    | nil => rw [hins] at hhead; simp at hhead
    | cons a tail =>
      have ha : a = hw := by rw [hins] at hhead; exact Option.some.inj hhead
      simp [GateOp.eval, hins, ha, hv]
  let E := T.erase t0
  let R := fun s => S s \ E
  let z := fun s => Zof (S s ∪ T)
  have hnt : ∀ s, ∀ j : Fin gates.length, (gates.get j).op = GateOp.not →
      val gates (z s) (n + j.val) = true := by
    intro s
    apply not_true
    intro t ht
    simp [z, Zof, ht]
  have hZ : ∀ s, val gates (z s) (out s) = false := by
    intro s
    change Circuit.eval ⟨gates, out s⟩ (List.ofFn (z s)) = false
    rw [heval]
    simp only [decide_eq_false_iff_not]
    rintro ⟨v, hv, hh⟩
    have hz : z s v = false := by simp [z, Zof, hv]
    rw [hz] at hh
    contradiction
  have hE : ∀ s, ∀ u ∈ R s, val gates (eof u) (out s) = true := by
    intro s u hu
    change Circuit.eval ⟨gates, out s⟩ (List.ofFn (eof u)) = true
    rw [heval]
    simp only [decide_eq_true_eq]
    exact ⟨u, (Finset.mem_sdiff.mp hu).1, by simp [eof]⟩
  choose l hinv hcard using fun s => main_inv (R s) (z s) gates hg (hnt s)
  have hbound : ∀ s, (R s).card - 1 ≤ (D (R s) (z s) gates).card := by
    intro s
    have hi : ((R s).image (l s)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact hinv s (out s) u v hu hv (hZ s) (hE s u hu) (hE s v hv)
    have := hcard s
    omega
  have hsupp : ∀ s i u, val gates (z s) i = false → val gates (eof u) i = true →
      u ∉ T → u ∈ S s := by
    intro s i u hz hu hut
    have hh := support (S s ∪ T) gates hg (hnt s) i u hz hu
    exact (Finset.mem_union.mp hh).resolve_right hut
  have hret : ∀ s u, u ∈ R s → u ∈ T → u = t0 := by
    intro s u hu hut
    have hne := (Finset.mem_sdiff.mp hu).2
    by_contra h
    exact hne (Finset.mem_erase.mpr ⟨h, hut⟩)
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (R a) (z a) gates) (D (R b) (z b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    obtain ⟨-, hza, u, v, huR, hvR, huv, hu, hv⟩ := Finset.mem_filter.mp hia
    obtain ⟨-, hzb, u', v', huR', hvR', huv', hu', hv'⟩ := Finset.mem_filter.mp hib
    have contradiction_pair : ∀ p q : Fin n, p ≠ q → p ∈ S a → q ∈ S a →
        p ∈ S b → q ∈ S b → False := by
      intro p q hpq hpa hqa hpb hqb
      have hsub : ({p,q} : Finset (Fin n)) ⊆ S a ∩ S b := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hpa,hpb⟩
        · exact Finset.mem_inter.mpr ⟨hqa,hqb⟩
      have := Finset.card_le_card hsub
      have := hinter a b hab
      rw [Finset.card_pair hpq] at *
      omega
    by_cases htb : t0 ∈ S b
    · have ub : u ∈ S b := by
        by_cases ht : u ∈ T
        · rw [hret a u huR ht]; exact htb
        · exact hsupp b i u hzb hu ht
      have vb : v ∈ S b := by
        by_cases ht : v ∈ T
        · rw [hret a v hvR ht]; exact htb
        · exact hsupp b i v hzb hv ht
      exact contradiction_pair u v huv (Finset.mem_sdiff.mp huR).1
        (Finset.mem_sdiff.mp hvR).1 ub vb
    · have ut : u' ∉ T := by
        intro ht
        exact htb (hret b u' huR' ht ▸ (Finset.mem_sdiff.mp huR').1)
      have vt : v' ∉ T := by
        intro ht
        exact htb (hret b v' hvR' ht ▸ (Finset.mem_sdiff.mp hvR').1)
      exact contradiction_pair u' v' huv' (hsupp a i u' hza hu' ut)
        (hsupp a i v' hza hv' vt) (Finset.mem_sdiff.mp huR').1 (Finset.mem_sdiff.mp hvR').1
  have htotal : ∑ s, ((R s).card - 1) ≤ gates.length - 1 := by
    calc ∑ s, ((R s).card - 1) ≤ ∑ s, (D (R s) (z s) gates).card :=
          Finset.sum_le_sum fun s _ => hbound s
      _ = (Finset.univ.biUnion fun s => D (R s) (z s) gates).card :=
          (Finset.card_biUnion hdisj).symm
      _ ≤ ((Finset.Ico n (n + gates.length)).erase (n + i0.val)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨s, -, hs⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨hI, hz, -⟩ := Finset.mem_filter.mp hs
        apply Finset.mem_erase.mpr
        refine ⟨?_, hI⟩
        intro heq
        subst i
        have hn := hnt s i0 hnot
        rw [hz] at hn
        contradiction
      _ = gates.length - 1 := by
        rw [Finset.card_erase_of_mem (by simp only [Finset.mem_Ico]; omega)]
        simp
  have hcount : ∑ s, (S s ∩ E).card =
      ∑ u ∈ E, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
    have hc : ∀ s, (S s ∩ E).card = ∑ u ∈ E, if u ∈ S s then 1 else 0 := by
      intro s
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      ext u
      simp [and_comm]
    simp_rw [hc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    rw [← Finset.sum_filter]
    simp
  have hcost : ∑ s, ((S s).card - 1) ≤
      (∑ s, ((R s).card - 1)) + ∑ u ∈ E, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
    rw [← hcount, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s hs
    have hh := Finset.card_sdiff_add_card_inter (S s) E
    change (S s).card - 1 ≤ (S s \ E).card - 1 + (S s ∩ E).card
    omega
  have hlen : 1 ≤ gates.length := by have := i0.isLt; omega
  change 1 + ∑ s, ((S s).card - 1) ≤ gates.length +
    ∑ u ∈ E, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card
  omega
