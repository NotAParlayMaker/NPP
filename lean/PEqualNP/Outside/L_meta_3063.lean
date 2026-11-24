import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3063

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem read_pair {n m : ℕ} (f : Fin n → Bool) (g : Fin m → Bool) (w : ℕ) :
    (List.ofFn f ++ List.ofFn g).getD w false =
      if h : w < n then f ⟨w, h⟩ else if h : w - n < m then g ⟨w - n, h⟩ else false := by
  by_cases h : w < n
  · rw [dif_pos h, List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [dif_neg h, List.getD_append_right _ _ _ _ (by simpa using h)]
    by_cases h' : w - n < m
    · rw [dif_pos h']
      simp [List.getD_eq_getElem?_getD, h']
    · rw [dif_neg h']
      simp [List.getD_eq_getElem?_getD, h']

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ h

theorem wire_gate {N : ℕ} {C : Circuit} (rb : ReadsBack N C) (x : List Bool) (hx : x.length = N)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hg : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have split : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by simp
  have whole : C.wires x = (C.gates.drop (j + 1)).foldl step
      (step ((C.gates.take j).foldl step x) C.gates[j]) := by
    change C.gates.foldl step x = _
    have h := congrArg (fun l => List.foldl step x l) split
    simp only [List.foldl_append, List.foldl_cons] at h
    exact h
  have len : ((C.gates.take j).foldl step x).length = N + j := by
    rw [run_length, hx, List.length_take]
    omega
  have low (i : ℕ) (hi : i < N + j) :
      (C.wires x).getD i false = ((C.gates.take j).foldl step x).getD i false := by
    rw [whole, run_keep _ _ _ (by simp [step, len]; omega)]
    exact List.getD_append _ _ _ _ (by omega)
  have args : (C.gates[j].inputs.map fun i => ((C.gates.take j).foldl step x).getD i false) =
      (C.gates[j].inputs.map fun i => (C.wires x).getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact (low i (rb j hj i (hg ▸ hi))).symm
  have top : (C.wires x).getD (N + j) false =
      (step ((C.gates.take j).foldl step x) C.gates[j]).getD (N + j) false := by
    rw [whole, run_keep _ _ _ (by simp [step, len])]
  rw [top, hg, step, List.getD_append_right _ _ _ _ (by omega), len, args]
  simp

theorem merge_count {V ι : Type} [DecidableEq V] [DecidableEq ι] (N s : ℕ) (S : ℕ → Finset V)
    (leaf : ∀ w < N, (S w).card ≤ 1)
    (node : ∀ j < s, ∃ x y, x < N + j ∧ y < N + j ∧ S (N + j) = S x ∪ S y)
    (Z : Finset V) (F : Finset ι) (r : ι → ℕ) (hr : ∀ t ∈ F, r t < N + s)
    (cover : ∀ z ∈ Z, ∃ t ∈ F, z ∈ S (r t)) :
    Z.card ≤ ((Finset.range s).filter fun j =>
      (∃ t ∈ F, S (N + j) ⊆ S (r t)) ∧ 2 ≤ (S (N + j) ∩ Z).card).card + F.card := by
  classical
  choose! x y hx hy hS using node
  let J := (Finset.range s).filter fun j =>
      (∃ t ∈ F, S (N + j) ⊆ S (r t)) ∧ 2 ≤ (S (N + j) ∩ Z).card
  let val (w : ℕ) : (Z → ℚ) →ₗ[ℚ] ℚ :=
    if h : (S w ∩ Z).Nonempty then
      LinearMap.proj (R := ℚ) (φ := fun _ : Z => ℚ) ⟨h.choose, (Finset.mem_inter.mp h.choose_spec).2⟩
    else 0
  have val_eq (w : ℕ) (f : Z → ℚ)
      (same : ∀ u v : Z, u.val ∈ S w → v.val ∈ S w → f u = f v) (u : Z) (hu : u.val ∈ S w) :
      val w f = f u := by
    have h : (S w ∩ Z).Nonempty := ⟨u.val, Finset.mem_inter.mpr ⟨hu, u.2⟩⟩
    simp only [val, dif_pos h, LinearMap.proj_apply]
    exact same _ _ (Finset.mem_inter.mp h.choose_spec).1 hu
  let φ : (Z → ℚ) →ₗ[ℚ] ((J → ℚ) × (F → ℚ)) :=
    LinearMap.prod (LinearMap.pi fun j => val (x j.val) - val (y j.val))
      (LinearMap.pi fun t => val (r t.val))
  have inj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have hJ (j : ℕ) (hj : j ∈ J) : val (x j) f = val (y j) f := by
      have h := congrFun (congrArg Prod.fst hf) ⟨j, hj⟩
      exact sub_eq_zero.mp h
    have hF (t : ι) (ht : t ∈ F) : val (r t) f = 0 := congrFun (congrArg Prod.snd hf) ⟨t, ht⟩
    have same : ∀ w, w < N + s → (∃ t ∈ F, S w ⊆ S (r t)) →
        ∀ u v : Z, u.val ∈ S w → v.val ∈ S w → f u = f v := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw ht u v hu hv
        by_cases huv : u = v
        · rw [huv]
        have hne : u.val ≠ v.val := fun h => huv (Subtype.ext h)
        by_cases hN : w < N
        · exact absurd (Finset.card_le_one.mp (leaf w hN) _ hu _ hv) hne
        obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j < s := by omega
        obtain ⟨t, htF, hts⟩ := ht
        have eq := hS j hj
        have subx : S (x j) ⊆ S (N + j) := by rw [eq]; exact Finset.subset_union_left
        have suby : S (y j) ⊆ S (N + j) := by rw [eq]; exact Finset.subset_union_right
        have ihx := ih (x j) (hx j hj) (by have := hx j hj; omega) ⟨t, htF, subx.trans hts⟩
        have ihy := ih (y j) (hy j hj) (by have := hy j hj; omega) ⟨t, htF, suby.trans hts⟩
        have two : 2 ≤ (S (N + j) ∩ Z).card :=
          Finset.one_lt_card.mpr ⟨u.val, Finset.mem_inter.mpr ⟨hu, u.2⟩, v.val,
            Finset.mem_inter.mpr ⟨hv, v.2⟩, hne⟩
        have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ⟨t, htF, hts⟩, two⟩
        have link := hJ j hjJ
        rw [eq] at hu hv
        rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
        · exact ihx u v hu hv
        · rw [← val_eq _ f ihx u hu, ← val_eq _ f ihy v hv, link]
        · rw [← val_eq _ f ihy u hu, ← val_eq _ f ihx v hv, link]
        · exact ihy u v hu hv
    funext z
    obtain ⟨t, ht, hz⟩ := cover z.val z.2
    have := val_eq (r t) f (same (r t) (hr t ht) ⟨t, ht, fun _ h => h⟩) z hz
    rw [← this, hF t ht]
    rfl
  have dim := LinearMap.finrank_le_finrank_of_injective inj
  simpa [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] using dim

set_option maxHeartbeats 2000000 in
theorem core {n m s k : ℕ} (inc : Fin n → Fin m → Bool)
    (a b : Fin k → ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m))
    (free : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
      inc p l' = true → inc p' l' = true → False)
    (ha : ∀ i, a i < n + m + s) (hb : ∀ i, b i < n + m + s)
    (S : ℕ → Finset (Fin n ⊕ Fin m))
    (leaf : ∀ w < n + m, (S w).card ≤ 1)
    (node : ∀ j < s, ∃ x y, x < n + m + j ∧ y < n + m + j ∧ S (n + m + j) = S x ∪ S y)
    (sa : ∀ i, S (a i) = (A i).image Sum.inl) (sb : ∀ i, S (b i) = (B i).image Sum.inr)
    (meetP : ∀ i j p, i ≠ j → p ∈ A i → p ∈ A j →
      (∀ e ∈ B i, inc p e = true) ∨ (∀ e ∈ B j, inc p e = true))
    (meetL : ∀ i j l, i ≠ j → l ∈ B i → l ∈ B j →
      (∀ g ∈ A i, inc g l = true) ∨ (∀ g ∈ A j, inc g l = true))
    (E : Finset (Fin n × Fin m))
    (hE : ∀ q ∈ E, inc q.1 q.2 = true ∧ ∃ i j : Fin k, i ≠ j ∧ q.1 ∈ A i ∧ q.2 ∈ B i ∧ q.1 ∈ A j ∧ q.2 ∈ B j) :
    E.card ≤ s + k + ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card := by
  classical
  let Fp (p : Fin n) : Finset (Fin k) :=
    Finset.univ.filter fun t => p ∈ A t ∧ 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc p e = true
  let Fl (l : Fin m) : Finset (Fin k) :=
    Finset.univ.filter fun t => l ∈ B t ∧ 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g l = true
  let Fr (l : Fin m) : Finset (Fin k) :=
    Finset.univ.filter fun t => B t = {l} ∧ 2 ≤ (A t).card ∧ ¬ ∀ g ∈ A t, inc g l = true
  let Fx : Finset (Fin k) := Finset.univ.filter fun t => (A t).card = 1 ∧ (B t).card = 1
  let Zp (p : Fin n) : Finset (Fin m) := (Fp p).biUnion B
  let Zl (l : Fin m) : Finset (Fin n) := (Fl l).biUnion A
  let Zr (l : Fin m) : Finset (Fin n) := Finset.univ.filter fun p =>
    (p, l) ∈ E ∧ l ∉ Zp p ∧ p ∉ Zl l ∧ ¬ ∃ t, A t = {p} ∧ B t = {l}
  let X : Finset (Fin n × Fin m) := E.filter fun q => ∃ t, A t = {q.1} ∧ B t = {q.2}
  have mFp (p t) : t ∈ Fp p ↔ p ∈ A t ∧ 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc p e = true := by simp [Fp]
  have mFl (l t) : t ∈ Fl l ↔ l ∈ B t ∧ 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g l = true := by simp [Fl]
  have mFr (l t) : t ∈ Fr l ↔ B t = {l} ∧ 2 ≤ (A t).card ∧ ¬ ∀ g ∈ A t, inc g l = true := by
    simp only [Fr, Finset.mem_filter, Finset.mem_univ, true_and]
  have mZp (p e) : e ∈ Zp p ↔ ∃ t ∈ Fp p, e ∈ B t := by simp only [Zp, Finset.mem_biUnion]
  have mZl (l g) : g ∈ Zl l ↔ ∃ t ∈ Fl l, g ∈ A t := by simp only [Zl, Finset.mem_biUnion]
  have mZr (l p) : p ∈ Zr l ↔ (p, l) ∈ E ∧ l ∉ Zp p ∧ p ∉ Zl l ∧ ¬ ∃ t, A t = {p} ∧ B t = {l} := by
    simp only [Zr, Finset.mem_filter, Finset.mem_univ, true_and]
  have oneSet {α : Type} [DecidableEq α] {T : Finset α} {u : α} (hu : u ∈ T) (h : ¬ 2 ≤ T.card) : T = {u} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hu, fun v hv => ?_⟩
    exact Finset.card_le_one.mp (by omega) v hv u hu
  have residue (l p) (h : p ∈ Zr l) : (∃ t ∈ Fr l, p ∈ A t) ∧
      (∃ t, A t = {p} ∧ ¬ ∀ e ∈ B t, inc p e = true) := by
    obtain ⟨hq, hp, hl, hc⟩ := (mZr l p).mp h
    have main : ∀ i j : Fin k, i ≠ j → p ∈ A i → l ∈ B i → p ∈ A j → l ∈ B j →
        (∀ e ∈ B i, inc p e = true) → (∃ t ∈ Fr l, p ∈ A t) ∧
        (∃ t, A t = {p} ∧ ¬ ∀ e ∈ B t, inc p e = true) := by
      intro i j hij pi li pj lj hin
      have hBi : B i = {l} := by
        apply oneSet li
        intro h2
        exact hp ((mZp p l).mpr ⟨i, (mFp p i).mpr ⟨pi, h2, hin⟩, li⟩)
      have hAi : 2 ≤ (A i).card := by
        by_contra h2
        exact hc ⟨i, oneSet pi h2, hBi⟩
      have notA : ∀ t, p ∈ A t → l ∈ B t → 2 ≤ (A t).card → ¬ ∀ g ∈ A t, inc g l = true := by
        intro t pt lt h2 hall
        exact hl ((mZl l p).mpr ⟨t, (mFl l t).mpr ⟨lt, h2, hall⟩, pt⟩)
      have hni := notA i pi li hAi
      have hAj : ∀ g ∈ A j, inc g l = true := (meetL i j l hij li lj).resolve_left hni
      have hAj1 : A j = {p} := by
        apply oneSet pj
        intro h2
        exact notA j pj lj h2 hAj
      have hBj : 2 ≤ (B j).card := by
        by_contra h2
        exact hc ⟨j, hAj1, oneSet lj h2⟩
      refine ⟨⟨i, (mFr l i).mpr ⟨hBi, hAi, hni⟩, pi⟩, j, hAj1, ?_⟩
      intro hall
      exact hp ((mZp p l).mpr ⟨j, (mFp p j).mpr ⟨pj, hBj, hall⟩, lj⟩)
    obtain ⟨_, i, j, hij, pi, li, pj, lj⟩ := hE _ hq
    rcases meetP i j p hij pi pj with h | h
    · exact main i j hij pi li pj lj h
    · exact main j i hij.symm pj lj pi li h
  have onLine (l f p t) (h : p ∈ Zr l) (ht : t ∈ Fr f) (hp : p ∈ A t) : inc p f = true := by
    obtain ⟨_, j, hj, hn⟩ := residue l p h
    obtain ⟨hB, h2, _⟩ := (mFr f t).mp ht
    have hne : t ≠ j := by
      rintro rfl
      rw [hj] at h2
      simp at h2
    rcases meetP t j p hne hp (by rw [hj]; simp) with h | h
    · exact h f (by rw [hB]; simp)
    · exact absurd h hn
  have incZr (l p) (h : p ∈ Zr l) : inc p l = true := (hE _ ((mZr l p).mp h).1).1
  let Z : Fin n ⊕ Fin m ⊕ Fin m → Finset (Fin n ⊕ Fin m)
    | .inl p => (Zp p).image Sum.inr
    | .inr (.inl l) => (Zl l).image Sum.inl
    | .inr (.inr l) => (Zr l).image Sum.inl
  let F : Fin n ⊕ Fin m ⊕ Fin m → Finset (Fin k)
    | .inl p => Fp p
    | .inr (.inl l) => Fl l
    | .inr (.inr l) => Fr l
  let r : Fin n ⊕ Fin m ⊕ Fin m → Fin k → ℕ
    | .inl _ => b
    | .inr _ => a
  let J (c : Fin n ⊕ Fin m ⊕ Fin m) := (Finset.range s).filter fun j =>
      (∃ t ∈ F c, S (n + m + j) ⊆ S (r c t)) ∧ 2 ≤ (S (n + m + j) ∩ Z c).card
  have bound (c) : (Z c).card ≤ (J c).card + (F c).card := by
    have h := merge_count (n + m) s S leaf node (Z c) (F c) (r c) ?_ ?_
    · convert h
    · intro t _
      rcases c with p | l | l
      · exact hb t
      · exact ha t
      · exact ha t
    · intro z hz
      rcases c with p | l | l
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨t, ht, h⟩ := (mZp p e).mp he
        exact ⟨t, ht, (sb t).symm ▸ Finset.mem_image_of_mem _ h⟩
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨t, ht, h⟩ := (mZl l e).mp he
        exact ⟨t, ht, (sa t).symm ▸ Finset.mem_image_of_mem _ h⟩
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨t, ht, h⟩ := (residue l e he).1
        exact ⟨t, ht, (sa t).symm ▸ Finset.mem_image_of_mem _ h⟩
  have pointCase (p j) (h : j ∈ J (.inl p)) : ∃ e e', e ≠ e' ∧ Sum.inr e ∈ S (n + m + j) ∧
      Sum.inr e' ∈ S (n + m + j) ∧ ∀ u ∈ S (n + m + j), ∃ v, u = Sum.inr v ∧ inc p v = true := by
    obtain ⟨_, ⟨t, ht, hsub⟩, h2⟩ := Finset.mem_filter.mp h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
    obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
    obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hu2
    obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp hv2
    refine ⟨e, e', fun h => huv (by rw [h]), hu1, hv1, fun u hu => ?_⟩
    have := hsub hu
    change u ∈ S (b t) at this
    rw [sb] at this
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp this
    exact ⟨v, rfl, ((mFp p t).mp ht).2.2 v hv⟩
  have lineCase (l j) (h : j ∈ J (.inr (.inl l))) : ∃ t ∈ Fl l, ∃ e e', e ≠ e' ∧ Sum.inl e ∈ S (n + m + j) ∧
      Sum.inl e' ∈ S (n + m + j) ∧ ∀ u ∈ S (n + m + j), ∃ v, u = Sum.inl v ∧ v ∈ A t := by
    obtain ⟨_, ⟨t, ht, hsub⟩, h2⟩ := Finset.mem_filter.mp h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
    obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
    obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hu2
    obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp hv2
    refine ⟨t, ht, e, e', fun h => huv (by rw [h]), hu1, hv1, fun u hu => ?_⟩
    have := hsub hu
    change u ∈ S (a t) at this
    rw [sa] at this
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp this
    exact ⟨v, rfl, hv⟩
  have resCase (l j) (h : j ∈ J (.inr (.inr l))) : ∃ t ∈ Fr l, ∃ e e', e ≠ e' ∧ e ∈ Zr l ∧ e' ∈ Zr l ∧
      Sum.inl e ∈ S (n + m + j) ∧
      Sum.inl e' ∈ S (n + m + j) ∧ ∀ u ∈ S (n + m + j), ∃ v, u = Sum.inl v ∧ v ∈ A t := by
    obtain ⟨_, ⟨t, ht, hsub⟩, h2⟩ := Finset.mem_filter.mp h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
    obtain ⟨hu1, hu2⟩ := Finset.mem_inter.mp hu
    obtain ⟨hv1, hv2⟩ := Finset.mem_inter.mp hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu2
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hv2
    refine ⟨t, ht, e, e', fun h => huv (by rw [h]), he, he', hu1, hv1, fun u hu => ?_⟩
    have := hsub hu
    change u ∈ S (a t) at this
    rw [sa] at this
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp this
    exact ⟨v, rfl, hv⟩
  have sameLine {p p' : Fin n} {l l' : Fin m} (hp : p ≠ p') (h1 : inc p l = true) (h2 : inc p' l = true)
      (h3 : inc p l' = true) (h4 : inc p' l' = true) : l = l' := by
    by_contra h
    exact free p p' l l' hp h h1 h2 h3 h4
  have samePoint {p p' : Fin n} {l l' : Fin m} (hl : l ≠ l') (h1 : inc p l = true) (h2 : inc p' l = true)
      (h3 : inc p l' = true) (h4 : inc p' l' = true) : p = p' := by
    by_contra h
    exact free p p' l l' h hl h1 h2 h3 h4
  have inlOf {T : Finset (Fin n ⊕ Fin m)} {U : Finset (Fin n)} (hT : ∀ u ∈ T, ∃ v, u = Sum.inl v ∧ v ∈ U)
      {e : Fin n} (he : Sum.inl e ∈ T) : e ∈ U := by
    obtain ⟨v, hv, hU⟩ := hT _ he
    cases hv
    exact hU
  have inrOf {T : Finset (Fin n ⊕ Fin m)} {p : Fin n}
      (hT : ∀ u ∈ T, ∃ v, u = Sum.inr v ∧ inc p v = true)
      {e : Fin m} (he : Sum.inr e ∈ T) : inc p e = true := by
    obtain ⟨v, hv, hU⟩ := hT _ he
    cases hv
    exact hU
  have mixed (p : Fin n) (l j) (h : j ∈ J (.inl p)) (h' : j ∈ J (.inr l)) : False := by
    obtain ⟨e, _, _, he, _⟩ := pointCase p j h
    rcases l with l | l
    · obtain ⟨_, _, _, _, _, _, _, hT⟩ := lineCase l j h'
      obtain ⟨v, hv, _⟩ := hT _ he
      cases hv
    · obtain ⟨_, _, _, _, _, _, _, _, _, hT⟩ := resCase l j h'
      obtain ⟨v, hv, _⟩ := hT _ he
      cases hv
  have lineRes (f l j) (h : j ∈ J (.inr (.inl f))) (h' : j ∈ J (.inr (.inr l))) : False := by
    obtain ⟨t, ht, _, _, _, _, _, hT⟩ := lineCase f j h
    obtain ⟨_, _, e, e', hne, he, he', hs, hs', _⟩ := resCase l j h'
    obtain ⟨_, _, hall⟩ := (mFl f t).mp ht
    have e1 := inlOf hT hs
    have e2 := inlOf hT hs'
    have : f = l := sameLine hne (hall _ e1) (hall _ e2) (incZr l e he) (incZr l e' he')
    subst this
    exact ((mZr f e).mp he).2.2.1 ((mZl f e).mpr ⟨t, ht, e1⟩)
  have disj : ∀ c c', c ≠ c' → Disjoint (J c) (J c') := by
    intro c c' hcc
    refine Finset.disjoint_left.mpr ?_
    intro j h h'
    rcases c with p | l | l <;> rcases c' with p' | l' | l'
    · obtain ⟨e, e', hne, he, he', hT⟩ := pointCase p j h
      obtain ⟨_, _, _, _, _, hT'⟩ := pointCase p' j h'
      have : p = p' := samePoint hne (inrOf hT he) (inrOf hT' he) (inrOf hT he') (inrOf hT' he')
      exact hcc (by rw [this])
    · exact mixed p (.inl l') j h h'
    · exact mixed p (.inr l') j h h'
    · exact mixed p' (.inl l) j h' h
    · obtain ⟨t, ht, e, e', hne, he, he', hT⟩ := lineCase l j h
      obtain ⟨t', ht', _, _, _, _, _, hT'⟩ := lineCase l' j h'
      have q := ((mFl l t).mp ht).2.2
      have q' := ((mFl l' t').mp ht').2.2
      have : l = l' := sameLine hne (q _ (inlOf hT he)) (q _ (inlOf hT he')) (q' _ (inlOf hT' he))
        (q' _ (inlOf hT' he'))
      exact hcc (by rw [this])
    · exact lineRes l l' j h h'
    · exact mixed p' (.inr l) j h' h
    · exact lineRes l' l j h' h
    · obtain ⟨t, ht, e, e', hne, he, he', hs, hs', hT⟩ := resCase l j h
      obtain ⟨t', ht', _, _, _, _, _, _, _, hT'⟩ := resCase l' j h'
      have : l = l' := sameLine hne (incZr l e he) (incZr l e' he')
        (onLine l l' e t' he ht' (inlOf hT' hs)) (onLine l l' e' t' he' ht' (inlOf hT' hs'))
      exact hcc (by rw [this])
  have gates : ∑ c, (J c).card ≤ s := by
    rw [← Finset.card_biUnion (fun c _ c' _ h => disj c c' h)]
    calc _ ≤ (Finset.range s).card := by
          apply Finset.card_le_card
          intro j hj
          obtain ⟨c, _, h⟩ := Finset.mem_biUnion.mp hj
          exact (Finset.mem_filter.mp h).1
      _ = s := Finset.card_range s
  let P := (Finset.univ : Finset (Fin n)).biUnion Fp
  let Q := (Finset.univ : Finset (Fin m)).biUnion Fl
  let R := (Finset.univ : Finset (Fin m)).biUnion Fr
  have cP : ∑ p, (Fp p).card = P.card := by
    refine (Finset.card_biUnion fun p _ p' _ hne => ?_).symm
    refine Finset.disjoint_left.mpr ?_
    intro t h h'
    obtain ⟨_, h2, hall⟩ := (mFp p t).mp h
    obtain ⟨_, _, hall'⟩ := (mFp p' t).mp h'
    obtain ⟨e, he, e', he', hee⟩ := Finset.one_lt_card.mp h2
    exact hne (samePoint hee (hall e he) (hall' e he) (hall e' he') (hall' e' he'))
  have cQ : ∑ l, (Fl l).card = Q.card := by
    refine (Finset.card_biUnion fun p _ p' _ hne => ?_).symm
    refine Finset.disjoint_left.mpr ?_
    intro t h h'
    obtain ⟨_, h2, hall⟩ := (mFl p t).mp h
    obtain ⟨_, _, hall'⟩ := (mFl p' t).mp h'
    obtain ⟨e, he, e', he', hee⟩ := Finset.one_lt_card.mp h2
    exact hne (sameLine hee (hall e he) (hall e' he') (hall' e he) (hall' e' he'))
  have cR : ∑ l, (Fr l).card = R.card := by
    refine (Finset.card_biUnion fun p _ p' _ hne => ?_).symm
    refine Finset.disjoint_left.mpr ?_
    intro t h h'
    have h1 := ((mFr p t).mp h).1
    have h2 := ((mFr p' t).mp h').1
    rw [h1] at h2
    exact hne (Finset.singleton_injective h2)
  have mP (t) (h : t ∈ P) : ∃ p, t ∈ Fp p := by
    obtain ⟨p, _, h⟩ := Finset.mem_biUnion.mp h
    exact ⟨p, h⟩
  have mQ (t) (h : t ∈ Q) : ∃ p, t ∈ Fl p := by
    obtain ⟨p, _, h⟩ := Finset.mem_biUnion.mp h
    exact ⟨p, h⟩
  have mR (t) (h : t ∈ R) : ∃ p, t ∈ Fr p := by
    obtain ⟨p, _, h⟩ := Finset.mem_biUnion.mp h
    exact ⟨p, h⟩
  let D := (Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))
  have both : (P ∩ Q).card ≤ D.card := by
    apply Finset.card_le_card
    intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp ht
    obtain ⟨p, hp⟩ := mP t h1
    obtain ⟨l, hl⟩ := mQ t h2
    obtain ⟨_, u, v⟩ := (mFp p t).mp hp
    obtain ⟨x, y, z⟩ := (mFl l t).mp hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, u, v⟩, l, x, y, z⟩
  have dR : Disjoint (P ∪ Q) R := by
    refine Finset.disjoint_left.mpr ?_
    intro t h h'
    obtain ⟨l, hl⟩ := mR t h'
    obtain ⟨hB, _, hno⟩ := (mFr l t).mp hl
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨p, hp⟩ := mP t h
      have := ((mFp p t).mp hp).2.1
      rw [hB] at this
      simp at this
    · obtain ⟨f, hf⟩ := mQ t h
      obtain ⟨h1, _, h3⟩ := (mFl f t).mp hf
      rw [hB, Finset.mem_singleton] at h1
      subst h1
      exact hno h3
  have dX : Disjoint (P ∪ Q ∪ R) Fx := by
    refine Finset.disjoint_left.mpr ?_
    intro t h h'
    obtain ⟨_, hA, hB⟩ := Finset.mem_filter.mp h'
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨p, hp⟩ := mP t h
        have := ((mFp p t).mp hp).2.1
        omega
      · obtain ⟨f, hf⟩ := mQ t h
        have := ((mFl f t).mp hf).2.1
        omega
    · obtain ⟨f, hf⟩ := mR t h
      have := ((mFr f t).mp hf).2.1
      omega
  have rects : P.card + Q.card + R.card + Fx.card ≤ k + D.card := by
    have h1 := Finset.card_union_add_card_inter P Q
    have h2 := Finset.card_union_of_disjoint dR
    have h3 := Finset.card_union_of_disjoint dX
    have h4 := Finset.card_le_univ (P ∪ Q ∪ R ∪ Fx)
    rw [Fintype.card_fin] at h4
    omega
  have cells : X.card ≤ Fx.card := by
    have pick : ∀ q ∈ X, ∃ t, A t = {q.1} ∧ B t = {q.2} := fun q hq => (Finset.mem_filter.mp hq).2
    rcases X.eq_empty_or_nonempty with h0 | ⟨q0, hq0⟩
    · rw [h0]; simp
    have : Nonempty (Fin k) := ⟨(pick q0 hq0).choose⟩
    choose! g hg using pick
    apply Finset.card_le_card_of_injOn g
    · intro q hq
      obtain ⟨h1, h2⟩ := hg q hq
      simp [Fx, h1, h2]
    · intro q hq q' hq' h
      obtain ⟨h1, h2⟩ := hg q hq
      obtain ⟨h3, h4⟩ := hg q' hq'
      rw [h] at h1 h2
      exact Prod.ext (Finset.singleton_injective (h1.symm.trans h3))
        (Finset.singleton_injective (h2.symm.trans h4))
  let E1 := ((Finset.univ : Finset (Fin n)).sigma fun p => Zp p).image (fun z => ((z.1, z.2) : Fin n × Fin m))
  let E2 := ((Finset.univ : Finset (Fin m)).sigma fun l => Zl l).image (fun z => ((z.2, z.1) : Fin n × Fin m))
  let E3 := ((Finset.univ : Finset (Fin m)).sigma fun l => Zr l).image (fun z => ((z.2, z.1) : Fin n × Fin m))
  have split : E ⊆ E1 ∪ E2 ∪ E3 ∪ X := by
    rintro ⟨p, l⟩ hq
    by_cases h1 : l ∈ Zp p
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨⟨p, l⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, h1⟩, rfl⟩)))
    by_cases h2 : p ∈ Zl l
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨⟨l, p⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, h2⟩, rfl⟩)))
    by_cases h3 : ∃ t, A t = {p} ∧ B t = {l}
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq, h3⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨⟨l, p⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
          (mZr l p).mpr ⟨hq, h1, h2, h3⟩⟩, rfl⟩))
  have c1 := Finset.card_le_card split
  have u1 := Finset.card_union_le (E1 ∪ E2 ∪ E3) X
  have u2 := Finset.card_union_le (E1 ∪ E2) E3
  have u3 := Finset.card_union_le E1 E2
  have s1 : E1.card ≤ ∑ p, (Zp p).card := Finset.card_image_le.trans (Finset.card_sigma _ _).le
  have s2 : E2.card ≤ ∑ l, (Zl l).card := Finset.card_image_le.trans (Finset.card_sigma _ _).le
  have s3 : E3.card ≤ ∑ l, (Zr l).card := Finset.card_image_le.trans (Finset.card_sigma _ _).le
  have total := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => bound c
  rw [Finset.sum_add_distrib] at total
  rw [Fintype.sum_sum_type (fun c => (Z c).card), Fintype.sum_sum_type (fun c => (Z (.inr c)).card),
    Fintype.sum_sum_type (fun c => (F c).card), Fintype.sum_sum_type (fun c => (F (.inr c)).card)] at total
  have z1 (p) : (Z (.inl p)).card = (Zp p).card := Finset.card_image_of_injective _ Sum.inr_injective
  have z2 (l) : (Z (.inr (.inl l))).card = (Zl l).card := Finset.card_image_of_injective _ Sum.inl_injective
  have z3 (l) : (Z (.inr (.inr l))).card = (Zr l).card := Finset.card_image_of_injective _ Sum.inl_injective
  rw [Finset.sum_congr rfl fun p _ => z1 p, Finset.sum_congr rfl fun p _ => z2 p,
    Finset.sum_congr rfl fun p _ => z3 p] at total
  have f1 : ∑ p, (F (.inl p)).card = P.card := cP
  have f2 : ∑ l, (F (.inr (.inl l))).card = Q.card := cQ
  have f3 : ∑ l, (F (.inr (.inr l))).card = R.card := cR
  rw [f1, f2, f3] at total
  change E.card ≤ s + k + D.card
  omega

theorem main : ∀ (n m : ℕ) (inc : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (s k T : ℕ)
  (a b : Fin k → ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)),
  (∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
    inc p l' = true → inc p' l' = true → False) →
  PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  C.size = s + k + T → 1 ≤ k →
  (∀ j < s, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) →
  (∀ i : Fin k, (A i).Nonempty ∧ (B i).Nonempty ∧ a i < n + m + s ∧ b i < n + m + s ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).inputs = [a i, b i] ∧
    ∀ x : List Bool, x.length = n + m →
      ((C.wires x).getD (a i) false = decide (∃ pa ∈ A i, x.getD pa.val false = true) ∧
       (C.wires x).getD (b i) false = decide (∃ lb ∈ B i, x.getD (n + lb.val) false = true))) →
  (∀ x : List Bool, x.length = n + m →
    C.eval x = decide (∃ i1 j1 : Fin k, i1 < j1 ∧ (C.wires x).getD (n + m + s + i1.val) false = true ∧
      (C.wires x).getD (n + m + s + j1.val) false = true)) →
  (∀ (P : Finset (Fin n)) (L : Finset (Fin m)),
    ((P.card = 1 ∧ L.card ≤ 2) ∨ (P.card ≤ 2 ∧ L.card = 1)) →
    (∀ p ∈ P, ∀ l ∈ L, inc p l = false) →
    C.eval (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))) = false) →
  ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++ List.ofFn (fun v : Fin m => decide (v = q.2))) = true)).card
    ≤ s + k + ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card ∧
  (k ≤ T + 1 →
    ((Finset.univ : Finset (Fin n × Fin m)).filter (fun r => inc r.1 r.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = r.1)) ++ List.ofFn (fun v : Fin m => decide (v = r.2))) = true)).card
    ≤ C.size + 1) := by
  intro n m inc C s k T a b A B free mono rb size hk ors ands out sound
  classical
  have len : C.gates.length = s + k + T := size
  let e : Fin n ⊕ Fin m → List Bool := fun u =>
    List.ofFn (fun i : Fin n => decide (Sum.inl i = u)) ++ List.ofFn (fun i : Fin m => decide (Sum.inr i = u))
  have elen (u) : (e u).length = n + m := by simp [e]
  let S (w : ℕ) : Finset (Fin n ⊕ Fin m) := Finset.univ.filter fun u => (C.wires (e u)).getD w false = true
  have mS (w u) : u ∈ S w ↔ (C.wires (e u)).getD w false = true := by simp [S]
  have input (x : List Bool) (hx : x.length = n + m) (w : ℕ) (hw : w < n + m) :
      (C.wires x).getD w false = x.getD w false :=
    run_keep C.gates x w (by omega)
  have leaf : ∀ w < n + m, (S w).card ≤ 1 := by
    intro w hw
    rw [Finset.card_le_one]
    intro u hu v hv
    have key (u) (hu : u ∈ S w) : (∀ h : w < n, Sum.inl ⟨w, h⟩ = u) ∧
        (¬ w < n → ∃ h' : w - n < m, Sum.inr ⟨w - n, h'⟩ = u) := by
      rw [mS, input _ (elen u) w hw, read_pair] at hu
      constructor
      · intro h
        rw [dif_pos h] at hu
        exact of_decide_eq_true hu
      · intro h
        rw [dif_neg h] at hu
        have h' : w - n < m := by omega
        rw [dif_pos h'] at hu
        exact ⟨h', of_decide_eq_true hu⟩
    by_cases h : w < n
    · exact ((key u hu).1 h).symm.trans ((key v hv).1 h)
    · obtain ⟨_, h1⟩ := (key u hu).2 h
      obtain ⟨_, h2⟩ := (key v hv).2 h
      exact h1.symm.trans h2
  have node : ∀ j < s, ∃ x y, x < n + m + j ∧ y < n + m + j ∧ S (n + m + j) = S x ∪ S y := by
    intro j hj
    obtain ⟨hop, hin⟩ := ors j hj
    obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hin
    have hjl : j < C.gates.length := by omega
    refine ⟨x, y, rb j hjl x (by rw [hxy]; simp), rb j hjl y (by rw [hxy]; simp), ?_⟩
    ext u
    rw [Finset.mem_union, mS, mS, mS, wire_gate rb _ (elen u) j hjl, hop, hxy]
    simp [GateOp.eval]
  have fin2 (l : Fin m) (h : n + l.val - n < m) : (⟨n + l.val - n, h⟩ : Fin m) = l :=
    Fin.ext (Nat.add_sub_cancel_left n l.val)
  have rd1 (f : Fin n → Bool) (g : Fin m → Bool) (p : Fin n) :
      (List.ofFn f ++ List.ofFn g).getD p.val false = f p := by
    rw [read_pair, dif_pos p.2]
  have rd2 (f : Fin n → Bool) (g : Fin m → Bool) (l : Fin m) :
      (List.ofFn f ++ List.ofFn g).getD (n + l.val) false = g l := by
    rw [read_pair, dif_neg (by omega), dif_pos (by omega), fin2]
  have evA (u) (p : Fin n) : (e u).getD p.val false = decide (Sum.inl p = u) := rd1 _ _ p
  have evB (u) (l : Fin m) : (e u).getD (n + l.val) false = decide (Sum.inr l = u) := rd2 _ _ l
  have sa (i) : S (a i) = (A i).image Sum.inl := by
    ext u
    rw [mS, ((ands i).2.2.2.2.2.2 _ (elen u)).1, decide_eq_true_iff, Finset.mem_image]
    simp only [evA, decide_eq_true_iff]
  have sb (i) : S (b i) = (B i).image Sum.inr := by
    ext u
    rw [mS, ((ands i).2.2.2.2.2.2 _ (elen u)).2, decide_eq_true_iff, Finset.mem_image]
    simp only [evB, decide_eq_true_iff]
  have rect (x : List Bool) (hx : x.length = n + m) (i : Fin k) :
      (C.wires x).getD (n + m + s + i.val) false = true ↔
        (∃ p ∈ A i, x.getD p.val false = true) ∧ ∃ l ∈ B i, x.getD (n + l.val) false = true := by
    obtain ⟨_, _, _, _, hop, hin, hv⟩ := ands i
    have hi : s + i.val < C.gates.length := by have := i.2; omega
    rw [Nat.add_assoc (n + m), wire_gate rb x hx _ hi, hop, hin]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true,
      Bool.and_eq_true, (hv x hx).1, (hv x hx).2, decide_eq_true_iff]
  have accept (P : Finset (Fin n)) (L : Finset (Fin m)) (i j : Fin k) (hij : i ≠ j)
      (h1 : ∃ p ∈ A i, p ∈ P) (h2 : ∃ l ∈ B i, l ∈ L) (h3 : ∃ p ∈ A j, p ∈ P) (h4 : ∃ l ∈ B j, l ∈ L) :
      C.eval (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))) = true := by
    rw [out _ (by simp), decide_eq_true_iff]
    have ri := (rect (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++
      List.ofFn (fun v : Fin m => decide (v ∈ L))) (by simp) i).mpr
      ⟨by simpa only [rd1, decide_eq_true_iff] using h1, by simpa only [rd2, decide_eq_true_iff] using h2⟩
    have rj := (rect (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++
      List.ofFn (fun v : Fin m => decide (v ∈ L))) (by simp) j).mpr
      ⟨by simpa only [rd1, decide_eq_true_iff] using h3, by simpa only [rd2, decide_eq_true_iff] using h4⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, ri, rj⟩
    · exact ⟨j, i, h, rj, ri⟩
  have meetP : ∀ i j p, i ≠ j → p ∈ A i → p ∈ A j →
      (∀ e ∈ B i, inc p e = true) ∨ (∀ e ∈ B j, inc p e = true) := by
    intro i j p hij pi pj
    by_contra h
    push Not at h
    obtain ⟨⟨l, hl, nl⟩, l', hl', nl'⟩ := h
    have acc := accept {p} {l, l'} i j hij ⟨p, pi, by simp⟩ ⟨l, hl, by simp⟩ ⟨p, pj, by simp⟩ ⟨l', hl', by simp⟩
    have rej := sound {p} {l, l'} (Or.inl ⟨by simp, Finset.card_le_two⟩) (by
      intro q hq f hf
      rw [Finset.mem_singleton] at hq
      subst hq
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact Bool.eq_false_of_not_eq_true nl
      · rw [Finset.mem_singleton] at hf
        subst hf
        exact Bool.eq_false_of_not_eq_true nl')
    rw [acc] at rej
    exact Bool.noConfusion rej
  have meetL : ∀ i j l, i ≠ j → l ∈ B i → l ∈ B j →
      (∀ g ∈ A i, inc g l = true) ∨ (∀ g ∈ A j, inc g l = true) := by
    intro i j l hij li lj
    by_contra h
    push Not at h
    obtain ⟨⟨p, hp, np⟩, p', hp', np'⟩ := h
    have acc := accept {p, p'} {l} i j hij ⟨p, hp, by simp⟩ ⟨l, li, by simp⟩ ⟨p', hp', by simp⟩ ⟨l, lj, by simp⟩
    have rej := sound {p, p'} {l} (Or.inr ⟨Finset.card_le_two, by simp⟩) (by
      intro q hq f hf
      rw [Finset.mem_singleton] at hf
      subst hf
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact Bool.eq_false_of_not_eq_true np
      · rw [Finset.mem_singleton] at hq
        subst hq
        exact Bool.eq_false_of_not_eq_true np')
    rw [acc] at rej
    exact Bool.noConfusion rej
  have first := core inc a b A B free
    (fun i => (ands i).2.2.1) (fun i => (ands i).2.2.2.1) S leaf node sa sb meetP meetL
    ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++ List.ofFn (fun v : Fin m => decide (v = q.2))) = true))
    (by
      rintro ⟨p, l⟩ hq
      obtain ⟨_, hinc, hev⟩ := Finset.mem_filter.mp hq
      refine ⟨hinc, ?_⟩
      rw [out _ (by simp), decide_eq_true_iff] at hev
      obtain ⟨i, j, hij, hi, hj⟩ := hev
      rw [rect _ (by simp)] at hi hj
      simp only [rd1, rd2, decide_eq_true_iff, exists_eq_right] at hi hj
      exact ⟨i, j, hij.ne, hi.1, hi.2, hj.1, hj.2⟩)
  refine ⟨by convert first, fun hkT => ?_⟩
  have hd := Finset.card_le_univ ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true)))
  rw [Fintype.card_fin] at hd
  have bound2 := first.trans (show _ ≤ C.size + 1 by omega)
  convert bound2

end PEqualNP.Outside.L_meta_3063

theorem PEqualNP.Outside.L_meta_3063 : ∀ (n m : ℕ) (inc : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (s k T : ℕ)
  (a b : Fin k → ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)),
  (∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
    inc p l' = true → inc p' l' = true → False) →
  PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  C.size = s + k + T → 1 ≤ k →
  (∀ j < s, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) →
  (∀ i : Fin k, (A i).Nonempty ∧ (B i).Nonempty ∧ a i < n + m + s ∧ b i < n + m + s ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).inputs = [a i, b i] ∧
    ∀ x : List Bool, x.length = n + m →
      ((C.wires x).getD (a i) false = decide (∃ pa ∈ A i, x.getD pa.val false = true) ∧
       (C.wires x).getD (b i) false = decide (∃ lb ∈ B i, x.getD (n + lb.val) false = true))) →
  (∀ x : List Bool, x.length = n + m →
    C.eval x = decide (∃ i1 j1 : Fin k, i1 < j1 ∧ (C.wires x).getD (n + m + s + i1.val) false = true ∧
      (C.wires x).getD (n + m + s + j1.val) false = true)) →
  (∀ (P : Finset (Fin n)) (L : Finset (Fin m)),
    ((P.card = 1 ∧ L.card ≤ 2) ∨ (P.card ≤ 2 ∧ L.card = 1)) →
    (∀ p ∈ P, ∀ l ∈ L, inc p l = false) →
    C.eval (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))) = false) →
  ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++ List.ofFn (fun v : Fin m => decide (v = q.2))) = true)).card
    ≤ s + k + ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card ∧
  (k ≤ T + 1 →
    ((Finset.univ : Finset (Fin n × Fin m)).filter (fun r => inc r.1 r.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = r.1)) ++ List.ofFn (fun v : Fin m => decide (v = r.2))) = true)).card
    ≤ C.size + 1) :=
  PEqualNP.Outside.L_meta_3063.main
