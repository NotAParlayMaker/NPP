import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_986

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def valW {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl stepW (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [stepW, List.length_append, List.length_cons, List.length_nil]
    omega

lemma valW_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    valW [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold valW
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma valW_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    valW (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => valW gs x j)
      else valW gs x i := by
  unfold valW
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, stepW]
  have hl : (gs.foldl stepW (List.ofFn x)).length = n + gs.length := by
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

lemma valW_append {n : ℕ} (gs1 gs2 : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + gs1.length) : valW (gs1 ++ gs2) x i = valW gs1 x i := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [← List.append_assoc, valW_snoc, if_neg (by rw [List.length_append]; omega), ih]

lemma valW_mid {n : ℕ} (gs1 gs2 : List Gate) (g : Gate) (x : Fin n → Bool) :
    valW (gs1 ++ g :: gs2) x (n + gs1.length) = g.op.eval (g.inputs.map fun j => valW gs1 x j) := by
  have h : gs1 ++ g :: gs2 = (gs1 ++ [g]) ++ gs2 := by simp
  rw [h, valW_append _ _ _ _ (by simp), valW_snoc, if_pos rfl]

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

def eofW {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def InvW {n : ℕ} (z : Fin n → Bool) (U : Fin n → Prop) (R : Finset (Fin n)) (gs : List Gate)
    (l : Fin n → Fin n) : Prop :=
  ∀ i u v, U u → U v → valW gs z i = false → valW gs (eofW u) i = true →
    valW gs (eofW v) i = true → u ∈ R ∧ l u = l v

def CntW {n : ℕ} (z : Fin n → Bool) (U : Fin n → Prop) (gs : List Gate) (i : ℕ) : Prop :=
  valW gs z i = false ∧
    ∃ u v : Fin n, U u ∧ U v ∧ u ≠ v ∧ valW gs (eofW u) i = true ∧ valW gs (eofW v) i = true

open Classical in
noncomputable def DW {n : ℕ} (z : Fin n → Bool) (U : Fin n → Prop) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => CntW z U gs i

def OkW {n : ℕ} (z : Fin n → Bool) (gs : List Gate) (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    g.op.eval (g.inputs.map fun j => valW gs z j) = true

lemma DW_mono {n : ℕ} (z : Fin n → Bool) (U : Fin n → Prop) (gs : List Gate) (g : Gate) :
    DW z U gs ⊆ DW z U (gs ++ [g]) := by
  classical
  intro i hi
  simp only [DW, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, hU, hV, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, hU, hV, huv, ?_, ?_⟩
  · rw [valW_snoc, if_neg hne]; exact hz
  · rw [valW_snoc, if_neg hne]; exact hu
  · rw [valW_snoc, if_neg hne]; exact hv

lemma main_inv {n : ℕ} (z : Fin n → Bool) (U : Fin n → Prop) (R : Finset (Fin n))
    (hR : ∀ u, U u → z u = false → u ∈ R) (gs : List Gate)
    (hg : ∀ gs1 g gs2, gs = gs1 ++ g :: gs2 → OkW z gs1 g) :
    ∃ l : Fin n → Fin n, InvW z U R gs l ∧ R.card ≤ (R.image l).card + (DW z U gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hUu hUv hz hu hv
    rw [valW_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, eofW, decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hR _ hUu hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun gs1 g' gs2 h => hg gs1 g' (gs2 ++ [g]) (by rw [h]; simp))
    have hok : OkW z gs g := hg gs g [] rfl
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => valW gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, valW (gs ++ [g]) x N = P x := by
      intro x
      rw [valW_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → valW (gs ++ [g]) x i = valW gs x i := by
      intro x i hi
      rw [valW_snoc, if_neg hi]
    have key : P z = false → ∀ u, U u → P (eofW u) = true →
        u ∈ R ∧ ∃ A B : Fin n → Prop, (∀ w, U w → P (eofW w) = true → A w ∨ B w) ∧
          (∀ w w', U w → U w' → A w → A w' → l w = l w') ∧
          (∀ w w', U w → U w' → B w → B w' → l w = l w') := by
      intro hz u hUu hu
      rcases hok with ⟨hop, hlen⟩ | htrue
      · rcases gate_cases g hop hlen (fun x j => valW gs x j) z with hall | ⟨a, b, hab⟩
        · have := hall (eofW u)
          simp only [hP] at hu
          rw [this] at hu
          exact absurd hu (by simp)
        · obtain ⟨ha, hb, hy⟩ := hab hz
          refine ⟨?_, fun w => valW gs (eofW w) a = true, fun w => valW gs (eofW w) b = true,
            fun w _ hw => hy (eofW w) hw,
            fun w w' hUw hUw' hw hw' => (hinv a w w' hUw hUw' ha hw hw').2,
            fun w w' hUw hUw' hw hw' => (hinv b w w' hUw hUw' hb hw hw').2⟩
          rcases hy (eofW u) hu with h | h
          · exact (hinv a u u hUu hUu ha h h).1
          · exact (hinv b u u hUu hUu hb h h).1
      · exact absurd (hz.symm.trans htrue) (by simp)
    by_cases hm : P z = false ∧ ∃ u v, U u ∧ U v ∧ P (eofW u) = true ∧ P (eofW v) = true ∧
        l u ≠ l v
    · obtain ⟨hz, u0, v0, hU0, hV0, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hUu hUv hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hUu hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, U w → P (eofW w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hUw hw
            rcases hAB w hUw hw with h | h <;> rcases hAB u0 hU0 hu0 with h0 | h0 <;>
              rcases hAB v0 hV0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 hUw hU0 h h0)
            · exact Or.inl (hA w u0 hUw hU0 h h0)
            · exact Or.inr (hA w v0 hUw hV0 h h1)
            · exact absurd (hB u0 v0 hU0 hV0 h0 h1) hne
            · exact absurd (hA u0 v0 hU0 hV0 h0 h1) hne
            · exact Or.inr (hB w v0 hUw hV0 h h1)
            · exact Or.inl (hB w u0 hUw hU0 h h0)
            · exact Or.inl (hB w u0 hUw hU0 h h0)
          have red : ∀ w, U w → P (eofW w) = true →
              (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hUw hw
            rcases two w hUw hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [if_pos h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hUu hiu, red v hUv hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hUu hUv hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
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
        have hNin : N ∈ DW z U (gs ++ [g]) := by
          simp only [DW, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, hU0, hV0, ?_, ?_, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ DW z U gs := by
          simp only [DW, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (DW z U gs).card + 1 ≤ (DW z U (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact DW_mono z U gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hUu hUv hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hUu hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hUu, hUv, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hUu hUv hiz hiu hiv
      · have := Finset.card_le_card (DW_mono z U gs g)
        omega

def zoW {n m : ℕ} (S : Fin m → Finset (Fin n)) (T : Finset (Fin n)) (o : Fin m) :
    Fin n → Bool := fun c => decide (c ∉ S o ∧ c ∉ T)

def UoW {n m : ℕ} (S : Fin m → Finset (Fin n)) (T : Finset (Fin n)) (t0 : Fin n) (o : Fin m) :
    Fin n → Prop := fun u => u ∉ T ∨ (u = t0 ∧ t0 ∈ S o)

def RoW {n m : ℕ} (S : Fin m → Finset (Fin n)) (T : Finset (Fin n)) (t0 : Fin n) (o : Fin m) :
    Finset (Fin n) := (S o).filter (fun u => u ∉ T ∨ u = t0)

lemma get_mid (L gs1 gs2 : List Gate) (g : Gate) (h : L = gs1 ++ g :: gs2)
    (hl : gs1.length < L.length) : L.get ⟨gs1.length, hl⟩ = g := by
  subst h
  simp

end PEqualNP.Outside.L_meta_986

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_986 in
theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  intro n m S gates out i0 hw T t0 _hS2 hS hg hnot hop0 hhead hwlt hev hT _ht0 _hmax
  have hval : ∀ (o : Fin m) (x : Fin n → Bool),
      valW gates x (out o) = decide (∃ v ∈ S o, x v = true) := fun o x => hev o x
  have hRU : ∀ o u, u ∈ RoW S T t0 o → UoW S T t0 o u ∧ u ∈ S o := by
    intro o u hu
    simp only [RoW, Finset.mem_filter] at hu
    refine ⟨?_, hu.1⟩
    show u ∉ T ∨ (u = t0 ∧ t0 ∈ S o)
    rcases hu.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, h ▸ hu.1⟩
  have hR : ∀ o u, UoW S T t0 o u → zoW S T o u = false → u ∈ RoW S T t0 o := by
    intro o u hU hz
    have hz' : u ∈ S o ∨ u ∈ T := by
      by_contra hc
      push_neg at hc
      simp [zoW, hc.1, hc.2] at hz
    simp only [RoW, Finset.mem_filter]
    rcases hU with hU | ⟨h1, h2⟩
    · exact ⟨hz'.resolve_right hU, Or.inl hU⟩
    · exact ⟨h1 ▸ h2, Or.inr h1⟩
  have hok : ∀ o gs1 g gs2, gates = gs1 ++ g :: gs2 → OkW (zoW S T o) gs1 g := by
    intro o gs1 g gs2 hgs
    have hmem : g ∈ gates := by rw [hgs]; simp
    obtain ⟨hop, hlen⟩ := hg g hmem
    rcases hop with h | h | h
    · exact Or.inl ⟨Or.inl h, hlen⟩
    · exact Or.inl ⟨Or.inr h, hlen⟩
    · right
      have hlt : gs1.length < gates.length := by rw [hgs]; simp
      have hget : gates.get ⟨gs1.length, hlt⟩ = g := get_mid gates gs1 gs2 g hgs hlt
      have hq := hnot ⟨gs1.length, hlt⟩ (by rw [hget]; exact h)
      have hi0 : i0.val = gs1.length := by rw [← hq]
      have hg0 : gates.get i0 = g := by rw [← hq]; exact hget
      rw [hg0] at hhead
      rw [hi0] at hwlt
      obtain ⟨rest, hrest⟩ : ∃ rest, g.inputs = hw :: rest := by
        cases hin : g.inputs with
        | nil => rw [hin] at hhead; simp at hhead
        | cons a rest =>
          rw [hin] at hhead
          simp at hhead
          exact ⟨rest, by rw [hhead]⟩
      have h1 : valW gs1 (zoW S T o) hw = valW gates (zoW S T o) hw := by
        rw [hgs, valW_append gs1 (g :: gs2) _ hw hwlt]
      have h2 : valW gates (zoW S T o) hw = false :=
        hT (zoW S T o) (by intro t ht; simp [zoW, ht])
      rw [h, hrest]
      simp only [GateOp.eval, List.map_cons, List.headD_cons, h1, h2, Bool.not_false]
  choose l hinv hcard using fun o => main_inv (zoW S T o) (UoW S T t0 o) (RoW S T t0 o)
    (hR o) gates (hok o)
  have hZ : ∀ o, valW gates (zoW S T o) (out o) = false := by
    intro o
    rw [hval]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv
    simp [zoW, hv]
  have hE : ∀ o, ∀ u ∈ S o, valW gates (eofW u) (out o) = true := by
    intro o u hu
    rw [hval]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eofW]⟩
  have hbound : ∀ o, (RoW S T t0 o).card - 1 ≤ (DW (zoW S T o) (UoW S T t0 o) gates).card := by
    intro o
    have h1 : ((RoW S T t0 o).image (l o)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      have hu' := hRU o u hu
      have hv' := hRU o v hv
      exact (hinv o (out o) u v hu'.1 hv'.1 (hZ o) (hE o u hu'.2) (hE o v hv'.2)).2
    have := hcard o
    omega
  have hcross : ∀ a b : Fin m, a ≠ b → (∀ u, UoW S T t0 a u → UoW S T t0 b u) →
      ∀ i, i ∈ DW (zoW S T a) (UoW S T t0 a) gates →
        i ∈ DW (zoW S T b) (UoW S T t0 b) gates → False := by
    intro a b hab hUab i hia hib
    simp only [DW, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, hza, u, v, hUu, hUv, huv, hu, hv⟩ := hia
    obtain ⟨-, hzb, -⟩ := hib
    have hua := (hinv a i u u hUu hUu hza hu hu).1
    have hva := (hinv a i v v hUv hUv hza hv hv).1
    have hub := (hinv b i u u (hUab u hUu) (hUab u hUu) hzb hu hu).1
    have hvb := (hinv b i v v (hUab v hUv) (hUab v hUv) hzb hv hv).1
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(hRU a _ hua).2, (hRU b _ hub).2⟩
      · exact Finset.mem_inter.mpr ⟨(hRU a _ hva).2, (hRU b _ hvb).2⟩
    have h2 : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := hS a b hab
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (DW (zoW S T a) (UoW S T t0 a) gates)
        (DW (zoW S T b) (UoW S T t0 b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    by_cases hc : t0 ∉ S a ∨ t0 ∈ S b
    · refine hcross a b hab ?_ i hia hib
      intro u hu
      show u ∉ T ∨ (u = t0 ∧ t0 ∈ S b)
      rcases hu with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, hc.resolve_left (not_not.mpr h2)⟩
    · push_neg at hc
      refine hcross b a (Ne.symm hab) ?_ i hib hia
      intro u hu
      show u ∉ T ∨ (u = t0 ∧ t0 ∈ S a)
      rcases hu with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact absurd h2 hc.2
  have hdec : gates = gates.take i0.val ++ gates.get i0 :: gates.drop (i0.val + 1) := by
    rw [List.get_eq_getElem, List.getElem_cons_drop, List.take_append_drop]
  have hlen0 : (gates.take i0.val).length = i0.val := by
    rw [List.length_take]
    exact min_eq_left (le_of_lt i0.isLt)
  have hNot : ∀ o, n + i0.val ∉ DW (zoW S T o) (UoW S T t0 o) gates := by
    intro o hmem
    simp only [DW, Finset.mem_filter] at hmem
    obtain ⟨-, hz, -⟩ := hmem
    have hv := valW_mid (gates.take i0.val) (gates.drop (i0.val + 1)) (gates.get i0) (zoW S T o)
    rw [← hdec, hlen0] at hv
    rcases hok o _ _ _ hdec with ⟨hop, -⟩ | htrue
    · rw [hop0] at hop
      rcases hop with h | h <;> cases h
    · rw [hv] at hz
      exact Bool.false_ne_true (hz.symm.trans htrue)
  have hUn : (Finset.univ.biUnion fun o => DW (zoW S T o) (UoW S T t0 o) gates) ⊆
      (Finset.Ico n (n + gates.length)).erase (n + i0.val) := by
    intro i hi
    obtain ⟨o, -, ho⟩ := Finset.mem_biUnion.mp hi
    refine Finset.mem_erase.mpr ⟨fun h => hNot o (h ▸ ho), ?_⟩
    simp only [DW, Finset.mem_filter] at ho
    exact ho.1
  have hcardU : ((Finset.Ico n (n + gates.length)).erase (n + i0.val)).card =
      gates.length - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_Ico.mpr ⟨by omega, by have := i0.isLt; omega⟩)]
    simp
  have hD : ∑ o, (DW (zoW S T o) (UoW S T t0 o) gates).card ≤ gates.length - 1 := by
    rw [← Finset.card_biUnion hdisj]
    exact (Finset.card_le_card hUn).trans hcardU.le
  have hpos : 1 ≤ gates.length := by have := i0.isLt; omega
  have hsplit : ∀ o, (S o).card - 1 ≤ ((RoW S T t0 o).card - 1) + (S o ∩ T.erase t0).card := by
    intro o
    have hsub : S o ⊆ RoW S T t0 o ∪ (S o ∩ T.erase t0) := by
      intro u hu
      by_cases h : u ∉ T ∨ u = t0
      · apply Finset.mem_union_left
        simp only [RoW, Finset.mem_filter]
        exact ⟨hu, h⟩
      · push_neg at h
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hu, Finset.mem_erase.mpr ⟨h.2, h.1⟩⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  have hdouble : ∑ o : Fin m, (S o ∩ T.erase t0).card =
      ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
    have h1 : ∀ o, (S o ∩ T.erase t0).card = ∑ u ∈ T.erase t0, if u ∈ S o then 1 else 0 := by
      intro o
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    have h2 : ∀ u, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card =
        ∑ c : Fin m, if u ∈ S c then 1 else 0 := by
      intro u
      rw [Finset.card_filter]
    simp_rw [h1, h2]
    exact Finset.sum_comm
  have hA : ∑ s, ((S s).card - 1) ≤
      ∑ s, ((RoW S T t0 s).card - 1) + ∑ s, (S s ∩ T.erase t0).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun s _ => hsplit s
  have hB : ∑ s, ((RoW S T t0 s).card - 1) ≤
      ∑ s, (DW (zoW S T s) (UoW S T t0 s) gates).card :=
    Finset.sum_le_sum fun s _ => hbound s
  rw [← hdouble]
  omega
