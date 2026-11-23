import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def bits {n : ℕ} (X : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ X)

def val {n : ℕ} (gs : List Gate) (x : Finset (Fin n)) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn (bits x))).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Finset (Fin n)) (i : ℕ) :
    val [] x i = if h : i < n then bits x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Finset (Fin n)) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn (bits x))).length = n + gs.length := by
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

def basis (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem gate_transfer (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f f' : ℕ → Bool) (h : ∀ i ∈ g.inputs, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with ha | ho
  · simp only [ha, GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun hf i hi => h i hi (hf i hi)
  · simp only [ho, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨true, ⟨i, hi, h i hi hb⟩, rfl⟩

theorem val_mono {n : ℕ} (gs : List Gate) (hg : basis gs)
    {X Y : Finset (Fin n)} (hXY : X ⊆ Y) (i : ℕ) :
    val gs X i = true → val gs Y i = true := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    rw [val_nil, val_nil]
    split
    · simpa [bits] using @hXY ⟨i, by assumption⟩
    · exact id
  | append_singleton gs g ih =>
    have hb : basis gs := fun a ha => hg a (by simp [ha])
    rw [val_snoc, val_snoc]
    split
    · exact gate_transfer g (hg g (by simp)).1 _ _ (fun j _ => ih hb j)
    · exact ih hb i

def specific {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m)
    (gs : List Gate) (i : ℕ) : Prop :=
  val gs (S w) i = true ∧ ∀ v, v ≠ w → val gs (S v) i ≠ true

open Classical in
noncomputable def charged {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m)
    (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter (specific S w gs)

theorem charged_mono {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m)
    (gs : List Gate) (g : Gate) : charged S w gs ⊆ charged S w (gs ++ [g]) := by
  classical
  intro i hi
  obtain ⟨hr, ht, hu⟩ := Finset.mem_filter.mp hi
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hr
  have hne : i ≠ n + gs.length := Nat.ne_of_lt hhi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ico.mpr ⟨hlo, by simp; omega⟩, ?_⟩
  simpa only [specific, val_snoc, ite_eq_right hne] using And.intro ht hu

theorem charged_incr {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m)
    (gs : List Gate) (g : Gate) (h : specific S w (gs ++ [g]) (n + gs.length)) :
    (charged S w gs).card + 1 ≤ (charged S w (gs ++ [g])).card := by
  classical
  let N := n + gs.length
  have hnew : N ∈ charged S w (gs ++ [g]) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by dsimp [N]; omega, by simp [N]⟩, h⟩
  have hold : N ∉ charged S w gs := by
    intro hmem
    exact (Nat.lt_irrefl N) (Finset.mem_Ico.mp (Finset.mem_filter.mp hmem).1).2
  rw [← Finset.card_insert_of_notMem hold]
  exact Finset.card_le_card (Finset.insert_subset hnew (charged_mono S w gs g))

def forces {n m : ℕ} (S : Fin m → Finset (Fin n)) (gs : List Gate)
    (F : Finset ℕ) (A : Finset (Fin n)) (B : Finset (Fin m)) : Prop :=
  ∀ X : Finset (Fin n), A ⊆ X → (∀ v ∈ B, S v ⊆ X) → ∀ i ∈ F, val gs X i = true

theorem certificate {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m)
    (gs : List Gate) (hg : basis gs) (F : Finset ℕ)
    (hF : ∀ i ∈ F, val gs (S w) i = true) :
    ∃ A B, w ∉ B ∧ A.card + B.card ≤ F.card + (charged S w gs).card ∧
      forces S gs F A B := by
  classical
  induction gs using List.reverseRecOn generalizing F with
  | nil =>
    let A := Finset.univ.filter (fun i : Fin n => i.val ∈ F)
    have hA : A.card ≤ F.card := Finset.card_le_card_of_injOn Fin.val
      (fun _ hi => (Finset.mem_filter.mp hi).2) Fin.val_injective.injOn
    refine ⟨A, ∅, by simp, by simp; omega, ?_⟩
    intro X hX _ i hi
    have h := hF i hi
    rw [val_nil] at h ⊢
    split at h
    · rename_i hl
      rw [dite_eq_left hl]
      exact decide_eq_true (hX (show (⟨i, hl⟩ : Fin n) ∈ A from
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
    · contradiction
  | append_singleton gs g ih =>
    let N := n + gs.length
    have hb : basis gs := fun a ha => hg a (by simp [ha])
    have old (X : Finset (Fin n)) (i : ℕ) (h : i ≠ N) :
        val (gs ++ [g]) X i = val gs X i := by rw [val_snoc, ite_eq_right h]
    have fresh (X : Finset (Fin n)) :
        val (gs ++ [g]) X N = g.op.eval (g.inputs.map (val gs X)) := by
      rw [val_snoc, ite_eq_left rfl]
    have count := Finset.card_le_card (charged_mono S w gs g)
    by_cases hN : N ∈ F
    · let R := F.erase N
      have hr : R.card + 1 = F.card := Finset.card_erase_add_one hN
      have hrtrue : ∀ i ∈ R, val gs (S w) i = true := by
        intro i hi
        obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hi
        rw [← old _ _ hne]
        exact hF i hin
      by_cases hother : ∃ v, v ≠ w ∧ val (gs ++ [g]) (S v) N = true
      · obtain ⟨v, hvw, hv⟩ := hother
        obtain ⟨A, B, hw, hsize, hforce⟩ := ih hb R hrtrue
        refine ⟨A, insert v B, by simp [Ne.symm hvw, hw], ?_, ?_⟩
        · have := Finset.card_insert_le v B
          omega
        · intro X hX hlines i hi
          by_cases heq : i = N
          · subst i
            exact val_mono _ hg (hlines v (Finset.mem_insert_self _ _)) _ hv
          · rw [old _ _ heq]
            exact hforce X hX (fun u hu => hlines u (Finset.mem_insert_of_mem hu)) i
              (Finset.mem_erase.mpr ⟨heq, hi⟩)
      · have hspec : specific S w (gs ++ [g]) N :=
          ⟨hF N hN, fun v hne hv => hother ⟨v, hne, hv⟩⟩
        have hinc := charged_incr S w gs g hspec
        let T := g.inputs.toFinset.filter (fun i => val gs (S w) i = true)
        obtain ⟨hop, hlen⟩ := hg g (by simp)
        have ht : T.card ≤ 2 := (Finset.card_filter_le ..).trans
          ((List.toFinset_card_le _).trans hlen)
        have hall : ∀ i ∈ R ∪ T, val gs (S w) i = true := by
          intro i hi
          rcases Finset.mem_union.mp hi with hr' | ht'
          · exact hrtrue i hr'
          · exact (Finset.mem_filter.mp ht').2
        obtain ⟨A, B, hw, hsize, hforce⟩ := ih hb (R ∪ T) hall
        refine ⟨A, B, hw, ?_, ?_⟩
        · have := Finset.card_union_le R T
          omega
        · intro X hX hlines i hi
          have hval := hforce X hX hlines
          by_cases heq : i = N
          · subst i
            rw [fresh]
            apply gate_transfer g hop (val gs (S w)) (val gs X)
            · intro j hj hjt
              exact hval j (Finset.mem_union_right _ (Finset.mem_filter.mpr
                ⟨List.mem_toFinset.mpr hj, hjt⟩))
            · rw [← fresh]
              exact hF N hN
          · rw [old _ _ heq]
            exact hval i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hi⟩))
    · have hne (i : ℕ) (hi : i ∈ F) : i ≠ N := fun e => hN (e ▸ hi)
      obtain ⟨A, B, hw, hsize, hforce⟩ := ih hb F (fun i hi => by
        rw [← old _ _ (hne i hi)]
        exact hF i hi)
      refine ⟨A, B, hw, by omega, ?_⟩
      intro X hX hlines i hi
      rw [old _ _ (hne i hi)]
      exact hforce X hX hlines i hi

theorem union_size {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ v, (S v).card = q + 1)
    (hi : ∀ u v, u ≠ v → (S u ∩ S v).card = 1) (B : Finset (Fin m)) :
    (B.biUnion S).card ≤ B.card * q + 1 := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert u B hu ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hu, Nat.add_mul, one_mul]
    rcases B.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp [hs]
    · have huv : u ≠ v := fun e => hu (e ▸ hv)
      have hsub : S u ∩ S v ⊆ S u ∩ B.biUnion S := by
        intro a ha
        obtain ⟨hau, hav⟩ := Finset.mem_inter.mp ha
        exact Finset.mem_inter.mpr ⟨hau, Finset.mem_biUnion.mpr ⟨v, hv, hav⟩⟩
      have hl := Finset.card_le_card hsub
      rw [hi u v huv] at hl
      have he := Finset.card_union_add_card_inter (S u) (B.biUnion S)
      rw [hs] at he
      omega

theorem cover_size {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m)
    (hi : ∀ u v, u ≠ v → (S u ∩ S v).card = 1) (A : Finset (Fin n)) (B : Finset (Fin m))
    (hw : w ∉ B) (hcover : S w ⊆ A ∪ B.biUnion S) : (S w).card ≤ A.card + B.card := by
  classical
  have hsub : S w ⊆ A ∪ (S w ∩ B.biUnion S) := by
    intro a ha
    rcases Finset.mem_union.mp (hcover ha) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ha, h⟩)
  have hbound := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.inter_biUnion] at hbound
  have hone := Finset.card_biUnion_le_card_mul B (fun v => S w ∩ S v) 1 (by
    intro v hv
    rw [hi w v (fun e => hw (e ▸ hv))])
  simpa using hbound.trans (Nat.add_le_add_left hone A.card)

theorem count_all {n m : ℕ} (S : Fin m → Finset (Fin n)) (gs : List Gate)
    (c : ℕ) (hc : ∀ w, c ≤ (charged S w gs).card) : m * c ≤ gs.length := by
  classical
  have hd : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (charged S a gs) (charged S b gs) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    exact (Finset.mem_filter.mp hia).2.2 b hab.symm (Finset.mem_filter.mp hib).2.1
  calc
    m * c = ∑ _w : Fin m, c := by simp
    _ ≤ ∑ w, (charged S w gs).card := Finset.sum_le_sum fun w _ => hc w
    _ = (Finset.univ.biUnion fun w => charged S w gs).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n + gs.length)).card := by
      apply Finset.card_le_card
      intro i hi
      obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_filter.mp hw).1
    _ = gs.length := by simp

end PEqualNP.Outside.L_meta_925

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hs hi gs out hg hev c hc hK
  by_cases hz : c = 0
  · simp [hz]
  have hqK : q + 1 ≤ K := by
    have h := Nat.mul_le_mul_right q (show 1 ≤ c by omega)
    simp only [one_mul] at h
    omega
  have he (w : Fin m) (X : Finset (Fin n)) (hX : X.card ≤ K) :
      L_meta_925.val gs X (out w) = true ↔ S w ⊆ X := by
    have hweight : Finset.univ.filter (fun i => L_meta_925.bits X i = true) = X := by
      ext i
      simp [L_meta_925.bits]
    have h := hev w (L_meta_925.bits X) (by rwa [hweight])
    change L_meta_925.val gs X (out w) = _ at h
    rw [h]
    simp [L_meta_925.bits, Finset.subset_iff]
  apply L_meta_925.count_all S gs c
  intro w
  by_contra! hsmall
  have hout := (he w (S w) (by simpa [hs] using hqK)).2 (Finset.Subset.rfl)
  obtain ⟨A, B, hw, hsize, hf⟩ := L_meta_925.certificate S w gs hg {out w}
    (by simpa using hout)
  simp only [Finset.card_singleton] at hsize
  have hbudget : A.card + B.card ≤ c := by omega
  let X := A ∪ B.biUnion S
  have hX : X.card ≤ K := by
    have hU := L_meta_925.union_size S hs hi B
    have hA : A.card * 1 ≤ A.card * q := Nat.mul_le_mul_left _ (by omega)
    have hprod := Nat.mul_le_mul_right q hbudget
    rw [Nat.add_mul] at hprod
    have hsum := Finset.card_union_le A (B.biUnion S)
    dsimp [X]
    simp only [Nat.mul_one] at hA
    omega
  have hval := hf X Finset.subset_union_left (fun v hv a ha =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hv, ha⟩)) (out w) (by simp)
  have hcover := (he w X hX).1 hval
  have hsw := L_meta_925.cover_size S w hi A B hw hcover
  rw [hs] at hsw
  omega
