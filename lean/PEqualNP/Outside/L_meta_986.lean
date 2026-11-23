import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_986_aux

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
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
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


def oneHot {n : ℕ} (u : Fin n) : Fin n → Bool := fun x => decide (x = u)

def complement {n : ℕ} (T S : Finset (Fin n)) : Fin n → Bool :=
  fun x => decide (x ∉ T ∧ x ∉ S)

def Fixed {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : Prop :=
  ∀ pre g post, gs = pre ++ g :: post → g.op = GateOp.not →
    g.op.eval (g.inputs.map fun j => val pre x j) = true

theorem fixed_prefix {n : ℕ} {gs : List Gate} {x : Fin n → Bool} (g : Gate)
    (h : Fixed (gs ++ [g]) x) : Fixed gs x := by
  intro pre q post eq hq
  apply h pre q (post ++ [g]) _ hq
  rw [eq, List.append_assoc]
  rfl

theorem val_prefix {n : ℕ} (pre post : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + pre.length) : val (pre ++ post) x i = val pre x i := by
  induction post using List.reverseRecOn with
  | nil => simp
  | append_singleton rest g ih =>
    rw [← List.append_assoc, val_snoc, ite_eq_right, ih]
    simp only [List.length_append]
    omega

theorem eval_mono (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : ℕ → Bool) (hxy : ∀ i, x i = true → y i = true) :
    g.op.eval (g.inputs.map x) = true → g.op.eval (g.inputs.map y) = true := by
  rcases h with h | h
  · simp only [h, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hx b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact hxy i (hx _ ⟨i, hi, rfl⟩)
  · simp only [h, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨y i, ⟨i, hi, rfl⟩, hxy i hx⟩

theorem val_mono_fixed {n : ℕ} {gs : List Gate} {x y : Fin n → Bool}
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hx : Fixed gs x) (hy : Fixed gs y)
    (hxy : ∀ u, x u = true → y u = true) :
    ∀ i, val gs x i = true → val gs y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    rw [val_nil] at hi ⊢
    by_cases h : i < n
    · simp only [h, dite_true] at hi ⊢
      exact hxy _ hi
    · simp [h] at hi
  | append_singleton pre g ih =>
    intro i hi
    rw [val_snoc] at hi ⊢
    split_ifs at hi ⊢ with e
    · rcases hg g (by simp) with e | e | e
      · exact eval_mono g (Or.inl e) _ _
          (ih (fun p hp => hg p (by simp [hp])) (fixed_prefix g hx) (fixed_prefix g hy)) hi
      · exact eval_mono g (Or.inr e) _ _
          (ih (fun p hp => hg p (by simp [hp])) (fixed_prefix g hx) (fixed_prefix g hy)) hi
      · exact hy pre g [] rfl e
    · exact ih (fun p hp => hg p (by simp [hp])) (fixed_prefix g hx) (fixed_prefix g hy) i hi

def Inv {n : ℕ} (R : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate)
    (label : Fin n → Fin n) : Prop :=
  ∀ i u v, u ∈ R → v ∈ R → val gs z i = false →
    val gs (oneHot u) i = true → val gs (oneHot v) i = true → label u = label v

def Counts {n : ℕ} (R : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate) (i : ℕ) : Prop :=
  val gs z i = false ∧ ∃ u ∈ R, ∃ v ∈ R,
    u ≠ v ∧ val gs (oneHot u) i = true ∧ val gs (oneHot v) i = true

open Classical in
noncomputable def Charged {n : ℕ} (R : Finset (Fin n)) (z : Fin n → Bool)
    (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter (Counts R z gs)

theorem charged_iff {n : ℕ} (R : Finset (Fin n)) (z : Fin n → Bool)
    (gs : List Gate) (i : ℕ) :
    i ∈ Charged R z gs ↔ n ≤ i ∧ i < n + gs.length ∧ Counts R z gs i := by
  simp [Charged, and_assoc]

theorem charged_mono {n : ℕ} (R : Finset (Fin n)) (z : Fin n → Bool)
    (gs : List Gate) (g : Gate) : Charged R z gs ⊆ Charged R z (gs ++ [g]) := by
  intro i hi
  rw [charged_iff] at hi ⊢
  simp only [List.length_append, List.length_cons, List.length_nil]
  refine ⟨hi.1, by omega, ?_⟩
  rcases hi.2.2 with ⟨hz, u, hu, v, hv, huv, hwu, hwv⟩
  have e : i ≠ n + gs.length := by omega
  refine ⟨?_, u, hu, v, hv, huv, ?_, ?_⟩ <;> rw [val_snoc, ite_eq_right e] <;> assumption

-- Each charged wire can merge at most two existing classes of input witnesses.
theorem main_inv {n : ℕ} (R : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (fixed : Fixed gs z) :
    ∃ l : Fin n → Fin n, Inv R z gs l ∧ R.card ≤ (R.image l).card + (Charged R z gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v _ _ hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, oneHot,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      rfl
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg'])) (fixed_prefix g fixed)
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, ite_eq_left hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, ite_eq_right hi]
    have key : P z = false →
        ∃ A B : Fin n → Prop,
          (∀ w ∈ R, P (oneHot w) = true → A w ∨ B w) ∧
          (∀ w ∈ R, ∀ w' ∈ R, A w → A w' → l w = l w') ∧
          (∀ w ∈ R, ∀ w' ∈ R, B w → B w' → l w = l w') := by
      intro hz
      have hmono : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hop with ha | ho | hn
        · exact Or.inl ha
        · exact Or.inr ho
        · have ht : P z = true := fixed gs g [] rfl hn
          rw [hz] at ht
          contradiction
      rcases gate_cases g hmono hlen (fun x j => val gs x j) z with hall | ⟨a, b, hab⟩
      · refine ⟨fun _ => False, fun _ => False, ?_, ?_, ?_⟩
        · intro w _ hw
          have hf : P (oneHot w) = false := hall _
          rw [hf] at hw
          contradiction
        · simp
        · simp
      · obtain ⟨ha, hb, hy⟩ := hab hz
        exact ⟨fun w => val gs (oneHot w) a = true, fun w => val gs (oneHot w) b = true,
          fun w _ hw => hy _ hw,
          fun w hw w' hw' h h' => hinv a w w' hw hw' ha h h',
          fun w hw w' hw' h h' => hinv b w w' hw hw' hb h h'⟩
    by_cases hm : P z = false ∧ ∃ u ∈ R, ∃ v ∈ R, P (oneHot u) = true ∧ P (oneHot v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, huR, v0, hvR, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hu hv hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨A, B, hAB, hA, hB⟩ := key hiz
          have two : ∀ w ∈ R, P (oneHot w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hwR hw
            rcases hAB w hwR hw with h | h <;> rcases hAB u0 huR hu0 with h0 | h0 <;>
              rcases hAB v0 hvR hv0 with h1 | h1
            · exact Or.inl (hA w hwR u0 huR h h0)
            · exact Or.inl (hA w hwR u0 huR h h0)
            · exact Or.inr (hA w hwR v0 hvR h h1)
            · exact absurd (hB u0 huR v0 hvR h0 h1) hne
            · exact absurd (hA u0 huR v0 hvR h0 h1) hne
            · exact Or.inr (hB w hwR v0 hvR h h1)
            · exact Or.inl (hB w hwR u0 huR h h0)
            · exact Or.inl (hB w hwR u0 huR h h0)
          have red : ∀ w ∈ R, P (oneHot w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hwR hw
            rcases two w hwR hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [ite_eq_left h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hu hiu, red v hv hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          have hl := hinv i u v hu hv hiz hiu hiv
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : R.image l ⊆
            insert (l v0) (R.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [ite_eq_right h]
        have h1 : (R.image l).card ≤
            (R.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ Charged R z (gs ++ [g]) := by
          rw [charged_iff]
          refine ⟨by omega, by simp [N], ?_, u0, huR, v0, hvR, ?_, ?_, ?_⟩
          · exact (hnew z).trans hz
          · intro h
            exact hne (by rw [h])
          · exact (hnew _).trans hu0
          · exact (hnew _).trans hv0
        have hNnot : N ∉ Charged R z gs := by
          rw [charged_iff]
          intro h
          omega
        have h2 : (Charged R z gs).card + 1 ≤ (Charged R z (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact charged_mono R z gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hu hv hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          by_contra hne
          exact hm ⟨hiz, u, hu, v, hv, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hu hv hiz hiu hiv
      · have := Finset.card_le_card (charged_mono R z gs g)
        omega

theorem fixed_of_kill {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (hw : ℕ)
    (unique : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (head : (gates.get i0).inputs.head? = some hw)
    (wire : hw < n + i0.val) (x : Fin n → Bool)
    (killed : val gates x hw = false) : Fixed gates x := by
  intro pre g post eq hg
  have bound : pre.length < gates.length := by simp [eq]
  let j : Fin gates.length := ⟨pre.length, bound⟩
  have hget : gates.get j = g := by
    have hopt : gates[pre.length]? = some g := by
      rw [eq, List.getElem?_append_right (by omega)]
      simp
    rw [List.getElem?_eq_getElem bound] at hopt
    exact Option.some.inj hopt
  have hj := unique j (hget ▸ hg)
  have e : i0.val = pre.length := (congrArg Fin.val hj).symm
  have hhw : hw < n + pre.length := by rw [e] at wire; exact wire
  have hk : val pre x hw = false := by
    rw [← val_prefix pre (g :: post) x hw hhw, ← eq]
    exact killed
  have hh : g.inputs.head? = some hw := by rwa [← hget, hj]
  rw [hg, GateOp.eval]
  cases hinputs : g.inputs with
  | nil => simp [hinputs] at hh
  | cons a as =>
    simp [hinputs] at hh
    simp [hh, hk]

theorem not_wire_true {n : ℕ} (gates : List Gate) (pre : List Gate) (g : Gate)
    (post : List Gate) (eq : gates = pre ++ g :: post) (x : Fin n → Bool)
    (fixed : Fixed gates x) (hg : g.op = GateOp.not) :
    val gates x (n + pre.length) = true := by
  have hlt : n + pre.length < n + (pre ++ [g]).length := by simp
  rw [eq, show pre ++ g :: post = (pre ++ [g]) ++ post by simp, val_prefix _ _ _ _ hlt]
  rw [val_snoc, ite_eq_left rfl]
  exact fixed pre g post eq hg

theorem lost_sum {n m : ℕ} (S : Fin m → Finset (Fin n)) (E : Finset (Fin n)) :
    ∑ i : Fin m, ((S i).card - 1) ≤
      (∑ i : Fin m, ((S i \ E).card - 1)) +
      ∑ u ∈ E, (Finset.univ.filter (fun i : Fin m => u ∈ S i)).card := by
  classical
  have card_left (i : Fin m) : ((S i) ∩ E).card = ∑ u ∈ E, if u ∈ S i then 1 else 0 := by
    have h : (S i) ∩ E = E.filter (· ∈ S i) := by
      ext u
      simp [and_comm]
    rw [h, ← Finset.sum_filter]
    simp
  have card_right (u : Fin n) :
      (Finset.univ.filter (fun i : Fin m => u ∈ S i)).card =
      ∑ i : Fin m, if u ∈ S i then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp
  have double : ∑ i : Fin m, ((S i) ∩ E).card =
      ∑ u ∈ E, (Finset.univ.filter (fun i : Fin m => u ∈ S i)).card := by
    simp only [card_left, card_right]
    exact Finset.sum_comm
  rw [← double, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have := Finset.card_sdiff_add_card_inter (S i) E
  omega

end PEqualNP.Outside.L_meta_986_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_986_aux in
theorem PEqualNP.Outside.L_meta_986 :
    ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  intro n m S gates out i0 hw T t0 _ sparse allowed unique neg head wire output kill _ _
  let E := T.erase t0
  let R := fun a => S a \ E
  let z := fun a => complement T (S a)
  have mono := fun g hg => (allowed g hg).1
  have fixed (x : Fin n → Bool) (hx : ∀ t ∈ T, x t = false) : Fixed gates x :=
    fixed_of_kill gates i0 hw unique head wire x (kill x hx)
  have fixed_z (a : Fin m) : Fixed gates (z a) := fixed _ (by
    intro t ht
    simp [z, complement, ht])
  have zero (a : Fin m) : val gates (z a) (out a) = false := by
    change Circuit.eval ⟨gates, out a⟩ (List.ofFn (z a)) = false
    rw [output]
    apply decide_eq_false
    rintro ⟨u, hu, hv⟩
    simp [z, complement, hu] at hv
  have one (a : Fin m) (u : Fin n) (hu : u ∈ R a) :
      val gates (oneHot u) (out a) = true := by
    change Circuit.eval ⟨gates, out a⟩ (List.ofFn (oneHot u)) = true
    rw [output, decide_eq_true_eq]
    exact ⟨u, (Finset.mem_sdiff.mp hu).1, by simp [oneHot]⟩
  choose label inv card using fun a => main_inv (R a) (z a) gates allowed (fixed_z a)
  have lower (a : Fin m) : (R a).card - 1 ≤ (Charged (R a) (z a) gates).card := by
    have hcard : ((R a).image (label a)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro u hu v hv
      obtain ⟨u, huR, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨v, hvR, rfl⟩ := Finset.mem_image.mp hv
      exact inv a (out a) u v huR hvR (zero a) (one a u huR) (one a v hvR)
    have := card a
    omega
  -- A witness outside T can only reach a charged wire for an output that uses it.
  have belongs (a : Fin m) (i : ℕ) (u : Fin n) (hu : u ∉ T)
      (hfalse : val gates (z a) i = false) (htrue : val gates (oneHot u) i = true) :
      u ∈ S a := by
    by_contra h
    have hx : Fixed gates (oneHot u) := fixed _ (by
      intro v hv
      simp [oneHot, ne_of_mem_of_not_mem hv hu])
    have hxy : ∀ v, oneHot u v = true → z a v = true := by
      intro v hv
      have e : v = u := by simpa [oneHot] using hv
      subst v
      simp [z, complement, hu, h]
    have := val_mono_fixed mono hx (fixed_z a) hxy i htrue
    rw [hfalse] at this
    contradiction
  -- If exactly one output contains t0, use the other output to choose the witnesses.
  have overlap (a b : Fin m) (hab : a ≠ b) (together : t0 ∈ S a → t0 ∈ S b)
      (i : ℕ) (ha : i ∈ Charged (R a) (z a) gates)
      (hb : i ∈ Charged (R b) (z b) gates) : False := by
    obtain ⟨_, _, _, u, hu, v, hv, huv, hu', hv'⟩ := (charged_iff _ _ _ _).mp ha
    have hb' := ((charged_iff _ _ _ _).mp hb).2.2.1
    have share (w : Fin n) (hw₁ : w ∈ R a) (hw₂ : val gates (oneHot w) i = true) :
        w ∈ S a ∩ S b := by
      have hwS := (Finset.mem_sdiff.mp hw₁).1
      refine Finset.mem_inter.mpr ⟨hwS, ?_⟩
      by_cases eq : w = t0
      · subst w
        exact together hwS
      · apply belongs b i w _ hb' hw₂
        intro h
        exact (Finset.mem_sdiff.mp hw₁).2 (Finset.mem_erase.mpr ⟨eq, h⟩)
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact share _ hu hu'
      · exact share _ hv hv'
    have hsize := Finset.card_le_card hsub
    have htwo := Finset.card_pair huv
    have hone := sparse a b hab
    omega
  have disjoint : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (Charged (R a) (z a) gates) (Charged (R b) (z b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i ha hb
    by_cases h : t0 ∈ S b
    · exact overlap a b hab (fun _ => h) i ha hb
    · exact overlap b a hab.symm (fun hb' => (h hb').elim) i hb ha
  let wi := n + i0.val
  have not_true (x : Fin n → Bool) (fixedx : Fixed gates x) : val gates x wi = true := by
    obtain ⟨pre, g, post, eq, hp, hg⟩ :
        ∃ pre g post, gates = pre ++ g :: post ∧ pre.length = i0.val ∧ g = gates.get i0 := by
      let pre := gates.take i0.val
      let post := gates.drop (i0.val + 1)
      refine ⟨pre, gates.get i0, post, ?_, ?_, rfl⟩
      · simp [pre, post]
      · simp [pre]
    have hw' : wi = n + pre.length := by rw [hp]
    rw [hw']
    exact not_wire_true _ pre g post eq x fixedx (hg ▸ neg)
  have hi : wi ∈ Finset.Ico n (n + gates.length) := by
    exact Finset.mem_Ico.mpr ⟨by omega, by dsimp [wi]; omega⟩
  have sub : (Finset.univ.biUnion fun a => Charged (R a) (z a) gates) ⊆
      (Finset.Ico n (n + gates.length)).erase wi := by
    intro i h
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp h
    obtain ⟨ha0, ha1, hz, _⟩ := (charged_iff _ _ _ _).mp ha
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_Ico.mpr ⟨ha0, ha1⟩⟩
    intro e
    rw [e, not_true _ (fixed_z a)] at hz
    contradiction
  have cost : 1 + ∑ a : Fin m, ((R a).card - 1) ≤ gates.length := by
    have hs : ∑ a : Fin m, ((R a).card - 1) ≤ ∑ a : Fin m, (Charged (R a) (z a) gates).card :=
      Finset.sum_le_sum fun a _ => lower a
    have hc := Finset.card_le_card sub
    rw [Finset.card_biUnion disjoint, Finset.card_erase_of_mem hi] at hc
    simp only [Nat.card_Ico, Nat.add_sub_cancel_left] at hc
    have := i0.isLt
    omega
  have total := lost_sum S E
  change ∑ i : Fin m, ((S i).card - 1) ≤
      (∑ a : Fin m, ((R a).card - 1)) +
      ∑ u ∈ E, (Finset.univ.filter (fun i : Fin m => u ∈ S i)).card at total
  change 1 + ∑ i : Fin m, ((S i).card - 1) ≤ gates.length +
      ∑ u ∈ E, (Finset.univ.filter (fun i : Fin m => u ∈ S i)).card
  omega
