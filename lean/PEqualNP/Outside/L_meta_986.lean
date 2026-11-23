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

theorem fold_prefix (gs : List Gate) (w : List Bool) :
    ∃ r, gs.foldl step w = w ++ r := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ r, ?_⟩
    rw [List.foldl_cons, hr]
    simp [step]

theorem val_append {n : ℕ} (A B : List Gate) (x : Fin n → Bool) (j : ℕ)
    (hj : j < n + A.length) : val (A ++ B) x j = val A x j := by
  unfold val
  rw [List.foldl_append]
  obtain ⟨r, hr⟩ := fold_prefix B (A.foldl step (List.ofFn x))
  rw [hr]
  have hl : (A.foldl step (List.ofFn x)).length = n + A.length := by
    rw [fold_length]; simp
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

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

def Zof {n : ℕ} (Q : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ Q)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Good {n : ℕ} (Q : Finset (Fin n)) (gs : List Gate) : Prop :=
  ∀ (pre : List Gate) (g : Gate) (rest : List Gate), gs = pre ++ g :: rest →
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
      g.op.eval (g.inputs.map fun j => val pre (Zof Q) j) = true

def Inv {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof Q) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ Q ∧ (u ∈ R → v ∈ R → l u = l v)

def Cnt {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof Q) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ u ∈ R ∧ v ∈ R ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt Q R gs i

theorem D_mono {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D Q R gs ⊆ D Q R (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, huR, hvR, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, huR, hvR, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

theorem main_inv {n : ℕ} (Q R : Finset (Fin n)) (gs : List Gate) (hgood : Good Q gs) :
    ∃ l : Fin n → Fin n, Inv Q R gs l ∧ R.card ≤ (R.image l).card + (D Q R gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, fun _ _ => rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    have hgood' : Good Q gs := by
      intro pre g' rest h
      exact hgood pre g' (rest ++ [g]) (by rw [h]; simp)
    obtain ⟨l, hinv, hcard⟩ := ih hgood'
    have hg := hgood gs g [] (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    by_cases hPz : P (Zof Q) = true
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz
          rw [hPz] at hiz
          exact absurd hiz (by simp)
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono Q R gs g)
        omega
    have hPz' : P (Zof Q) = false := by simpa using hPz
    have hopl : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      rcases hg with h | h
      · exact h
      · exact absurd h hPz
    obtain ⟨hop, hlen⟩ := hopl
    have key : ∀ u, P (eof u) = true →
        u ∈ Q ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → w ∈ R → w' ∈ R → l w = l w') ∧
          (∀ w w', B w → B w' → w ∈ R → w' ∈ R → l w = l w') := by
      intro u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof Q) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hPz'
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : ∃ u v, u ∈ R ∧ v ∈ R ∧ P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨u0, v0, hu0R, hv0R, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiu hiv
          obtain ⟨huQ, A, B, hAB, hA, hB⟩ := key u hiu
          refine ⟨huQ, fun huR hvR => ?_⟩
          have two : ∀ w, w ∈ R → P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hwR hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0 hwR hu0R)
            · exact Or.inl (hA w u0 h h0 hwR hu0R)
            · exact Or.inr (hA w v0 h h1 hwR hv0R)
            · exact absurd (hB u0 v0 h0 h1 hu0R hv0R) hne
            · exact absurd (hA u0 v0 h0 h1 hu0R hv0R) hne
            · exact Or.inr (hB w v0 h h1 hwR hv0R)
            · exact Or.inl (hB w u0 h h0 hwR hu0R)
            · exact Or.inl (hB w u0 h h0 hwR hu0R)
          have red : ∀ w, w ∈ R → P (eof w) = true →
              (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hwR hw
            rcases two w hwR hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [if_pos h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u huR hiu, red v hvR hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huQ, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huQ, fun huR hvR => ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl huR hvR]
      · have himg : R.image l ⊆
            insert (l v0) (R.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [if_neg h]
        have h1 : (R.image l).card ≤
            (R.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D Q R (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, hu0R, hv0R, ?_, ?_⟩
          · rw [hnew]; exact hPz'
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D Q R gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D Q R gs).card + 1 ≤ (D Q R (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono Q R gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huQ, -⟩ := key u hiu
          refine ⟨huQ, fun huR hvR => ?_⟩
          by_contra hne
          exact hm ⟨u, v, huR, hvR, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono Q R gs g)
        omega

end PEqualNP.Outside.L_meta_986_aux

open PEqualNP.Outside.L_meta_986_aux in
theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  intro n m S gates out i0 hw T t0 _h2 hS hg hnot hi0 hhead hhw hev hT _ht0 _hmax
  set T' := T.erase t0 with hT'
  set Q : Fin m → Finset (Fin n) := fun o => S o ∪ T with hQ
  set R : Fin m → Finset (Fin n) := fun o => S o \ T' with hR
  have hval : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true) := fun w x => hev w x
  have hTz : ∀ o, val gates (Zof (Q o)) hw = false := by
    intro o
    apply hT
    intro t ht
    simp [Zof, hQ, ht]
  -- the one gate that negates: its value at every zero point is true
  have hgood : ∀ o, Good (Q o) gates := by
    intro o pre g rest hsplit
    have hlenpre : pre.length < gates.length := by rw [hsplit]; simp
    have hget : gates[pre.length] = g := by
      simp only [hsplit, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero]
    have hmem : g ∈ gates := by rw [hsplit]; simp
    rcases (hg g hmem).1 with h | h | h
    · exact Or.inl ⟨Or.inl h, (hg g hmem).2⟩
    · exact Or.inl ⟨Or.inr h, (hg g hmem).2⟩
    · right
      have hq : (⟨pre.length, hlenpre⟩ : Fin gates.length) = i0 := by
        apply hnot
        simp [List.get_eq_getElem, hget, h]
      have hpi : pre.length = i0.val := by rw [← hq]
      have hgi : gates.get i0 = g := by
        rw [← hq]; simp [List.get_eq_getElem, hget]
      rw [hgi] at hhead
      obtain ⟨rest', hins⟩ : ∃ r, g.inputs = hw :: r := by
        cases hgi' : g.inputs with
        | nil => rw [hgi'] at hhead; simp at hhead
        | cons a r => rw [hgi'] at hhead; simp at hhead; exact ⟨r, by rw [hhead]⟩
      rw [h, hins]
      have hpre : val pre (Zof (Q o)) hw = false := by
        rw [← val_append pre (g :: rest) _ hw (by omega), ← hsplit]
        exact hTz o
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval, hpre]
  choose l hinv hcard using fun o => main_inv (Q o) (R o) gates (hgood o)
  have hZ : ∀ w, val gates (Zof (Q w)) (out w) = false := by
    intro w
    rw [hval]
    simp only [Zof, hQ, decide_eq_false_iff_not, not_exists, not_and]
    intro x hx
    simp [hx]
  have hE : ∀ w, ∀ u ∈ R w, val gates (eof u) (out w) = true := by
    intro w u hu
    rw [hval]
    simp only [decide_eq_true_eq]
    exact ⟨u, (Finset.mem_sdiff.mp hu).1, by simp [eof]⟩
  have hbound : ∀ w, (R w).card - 1 ≤ (D (Q w) (R w) gates).card := by
    intro w
    have h1 : ((R w).image (l w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv w (out w) u v (hZ w) (hE w u hu) (hE w v hv)).2 hu hv
    have := hcard w
    omega
  have side : ∀ a b : Fin m, a ≠ b → ∀ i, i ∈ D (Q a) (R a) gates →
      i ∈ D (Q b) (R b) gates → t0 ∈ S a ∧ t0 ∉ S b := by
    intro a b hab i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, hza, u, v, huv, huR, hvR, hu, hv⟩ := hia
    obtain ⟨-, hzb, -⟩ := hib
    have hub := (hinv b i u u hzb hu hu).1
    have hvb := (hinv b i v v hzb hv hv).1
    simp only [hR, hT', Finset.mem_sdiff, Finset.mem_erase, not_and, not_not] at huR hvR
    simp only [hQ, Finset.mem_union] at hub hvb
    have hu' : u ∈ S b ∨ u = t0 := by
      rcases hub with h | h
      · exact Or.inl h
      · exact Or.inr (by by_contra hne; exact absurd (huR.2 hne) (by simpa using h))
    have hv' : v ∈ S b ∨ v = t0 := by
      rcases hvb with h | h
      · exact Or.inl h
      · exact Or.inr (by by_contra hne; exact absurd (hvR.2 hne) (by simpa using h))
    have hcap := hS a b hab
    have pair : ∀ x y, x ≠ y → x ∈ S a → y ∈ S a → x ∈ S b → y ∈ S b → False := by
      intro x y hxy hxa hya hxb hyb
      have hsub : ({x, y} : Finset (Fin n)) ⊆ S a ∩ S b := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hxa, hxb⟩
        · exact Finset.mem_inter.mpr ⟨hya, hyb⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hxy] at this
      omega
    rcases hu' with hu' | rfl <;> rcases hv' with hv' | rfl
    · exact (pair u v huv huR.1 hvR.1 hu' hv').elim
    · exact ⟨hvR.1, fun h => pair u v huv huR.1 hvR.1 hu' h⟩
    · exact ⟨huR.1, fun h => pair u v huv huR.1 hvR.1 h hv'⟩
    · exact (huv rfl).elim
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (Q a) (R a) gates) (D (Q b) (R b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    exact (side a b hab i hia hib).2 (side b a (Ne.symm hab) i hib hia).1
  -- the negating wire lies in no counted set
  have hNOTval : ∀ o, val gates (Zof (Q o)) (n + i0.val) = true := by
    intro o
    obtain ⟨pre, rest, hsplit, hplen⟩ : ∃ pre rest, gates = pre ++ gates.get i0 :: rest ∧
        pre.length = i0.val := by
      refine ⟨gates.take i0.val, gates.drop (i0.val + 1), ?_, by simp⟩
      simp [List.get_eq_getElem]
    have hnotop : (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not := hi0
    have hg0 := hgood o pre (gates.get i0) rest hsplit
    generalize gates.get i0 = g0 at hsplit hnotop hg0
    have hidx : n + i0.val = n + pre.length := by omega
    rw [hidx]
    have hre : gates = (pre ++ [g0]) ++ rest := by rw [hsplit]; simp
    rw [hre, val_append _ _ _ _ (by simp), val_snoc, if_pos rfl]
    rcases hg0 with h | h
    · rw [hnotop] at h; rcases h.1 with h | h <;> cases h
    · exact h
  have hNnot : ∀ o, n + i0.val ∉ D (Q o) (R o) gates := by
    intro o h
    simp only [D, Finset.mem_filter] at h
    obtain ⟨-, hz, -⟩ := h
    rw [hNOTval o] at hz
    exact absurd hz (by simp)
  have hcount : 1 + ∑ w, ((R w).card - 1) ≤ gates.length := by
    calc 1 + ∑ w, ((R w).card - 1) ≤ 1 + ∑ w, (D (Q w) (R w) gates).card := by
          have := Finset.sum_le_sum fun w (_ : w ∈ (Finset.univ : Finset (Fin m))) => hbound w
          omega
      _ = 1 + (Finset.univ.biUnion fun w => D (Q w) (R w) gates).card := by
          rw [Finset.card_biUnion hdisj]
      _ = (insert (n + i0.val) (Finset.univ.biUnion fun w => D (Q w) (R w) gates)).card := by
          rw [Finset.card_insert_of_notMem]
          · omega
          · intro h
            obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp h
            exact hNnot w hw
      _ ≤ (Finset.Ico n (n + gates.length)).card := by
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · simp
          · obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
            simp only [D, Finset.mem_filter] at hw
            exact hw.1
      _ = gates.length := by simp
  have hper : ∀ w, (S w).card - 1 ≤ ((R w).card - 1) + (S w ∩ T').card := by
    intro w
    have := Finset.card_sdiff_add_card_inter (S w) T'
    simp only [hR] at this ⊢
    omega
  have hswap : ∑ w, (S w ∩ T').card =
      ∑ u ∈ T', (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
    have h1 : ∀ w, (S w ∩ T').card = ∑ u ∈ T', if u ∈ S w then 1 else 0 := by
      intro w
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1
      ext u
      simp [Finset.mem_inter, and_comm]
    have h2 : ∀ u, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card =
        ∑ w, if u ∈ S w then 1 else 0 := by
      intro u
      rw [Finset.sum_boole, Nat.cast_id]
    simp only [h1, h2]
    exact Finset.sum_comm
  have hsum : ∑ s, ((S s).card - 1) ≤ ∑ w, ((R w).card - 1) + ∑ w, (S w ∩ T').card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun w _ => hper w
  rw [hswap] at hsum
  omega
