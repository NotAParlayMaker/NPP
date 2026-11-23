import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_925

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma foldl_prefix (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl step w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (step w g)
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,
      by rw [List.foldl_cons, ht]; simp [step]⟩

lemma getD_prefix (a t : List Bool) (i : ℕ) (h : i < a.length) :
    (a ++ t).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_ge (a : List Bool) (i : ℕ) (h : a.length ≤ i) : a.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma getD_mid (a t : List Bool) (b : Bool) : (a ++ b :: t).getD a.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma gate_val (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (gs.foldl step w).getD (w.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i =>
        if i < w.length + k then (gs.foldl step w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ (gs[k] :: gs.drop (k + 1)) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hAlen : ((gs.take k).foldl step w).length = w.length + k := by
    rw [foldl_len]; simp; omega
  have hfull : gs.foldl step w =
      (gs.drop (k + 1)).foldl step (step ((gs.take k).foldl step w) gs[k]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  obtain ⟨t, ht⟩ := foldl_prefix (gs.drop (k + 1)) (step ((gs.take k).foldl step w) gs[k])
  have key : (fun i => if i < w.length + k then (gs.foldl step w).getD i false else false) =
      fun i => ((gs.take k).foldl step w).getD i false := by
    funext i
    split_ifs with hi
    · rw [hfull, ht, step, List.append_assoc, getD_prefix _ _ _ (by omega)]
    · rw [getD_ge _ _ (by omega)]
  rw [key, hfull, ht, step, List.append_assoc, List.singleton_append, ← hAlen, getD_mid]

def val (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (j : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD j false

lemma val_lt (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (h : j < n) :
    val gs x j = x ⟨j, h⟩ := by
  obtain ⟨t, ht⟩ := foldl_prefix gs (List.ofFn x)
  unfold val
  rw [ht, getD_prefix _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_ge (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (h : n + gs.length ≤ j) :
    val gs x j = false := by
  unfold val
  exact getD_ge _ _ (by rw [foldl_len]; simpa using h)

lemma val_gate (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    val gs x (n + k) = gs[k].op.eval (gs[k].inputs.map fun i =>
        if i < n + k then val gs x i else false) := by
  have h := gate_val gs (List.ofFn x) k hk
  simp only [List.length_ofFn] at h
  exact h

lemma eval_eq (gs : List Gate) (o : ℕ) {n : ℕ} (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = val gs x o := rfl

lemma and_true_iff (l : List ℕ) (r : ℕ → Bool) :
    GateOp.eval GateOp.and (l.map r) = true ↔ ∀ i ∈ l, r i = true := by
  simp [GateOp.eval]

lemma or_true_iff (l : List ℕ) (r : ℕ → Bool) :
    GateOp.eval GateOp.or (l.map r) = true ↔ ∃ i ∈ l, r i = true := by
  simp [GateOp.eval]

lemma val_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {n : ℕ} (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val gs x j = true → val gs y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  rcases lt_or_ge j n with h | h
  · rw [val_lt _ _ _ h] at hj ⊢
    exact hxy _ hj
  · rcases lt_or_ge (j - n) gs.length with hk | hk
    · obtain ⟨k, rfl⟩ : ∃ k, j = n + k := ⟨j - n, by omega⟩
      have hk' : k < gs.length := by omega
      rw [val_gate _ _ _ hk'] at hj ⊢
      have hread : ∀ i, (if i < n + k then val gs x i else false) = true →
          (if i < n + k then val gs y i else false) = true := by
        intro i hi
        split_ifs at hi ⊢ with h1
        exact ih i h1 hi
      rcases hg _ (List.getElem_mem hk') with hop | hop
      · rw [hop, and_true_iff] at hj ⊢
        exact fun i hi => hread i (hj i hi)
      · rw [hop, or_true_iff] at hj ⊢
        obtain ⟨i, hi, hb⟩ := hj
        exact ⟨i, hi, hread i hb⟩
    · rw [val_ge _ _ _ (by omega)] at hj
      exact absurd hj (by simp)

def ind {n : ℕ} (T : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ T)

lemma wt_ind {n : ℕ} (T : Finset (Fin n)) :
    (Finset.univ.filter (fun i : Fin n => ind T i = true)).card = T.card := by
  congr 1
  ext i
  simp [ind]

def spec (gs : List Gate) {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m) (j : ℕ) : Prop :=
  n ≤ j ∧ val gs (ind (S w)) j = true ∧ ∀ v, v ≠ w → val gs (ind (S v)) j = false

noncomputable def specSet (gs : List Gate) {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m) (N : ℕ) :
    Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun j => spec gs S w j)

lemma specSet_mono (gs : List Gate) {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m)
    (N : ℕ) : (specSet gs S w N).card ≤ (specSet gs S w (N + 1)).card := by
  classical
  apply Finset.card_le_card
  intro j hj
  simp only [specSet, Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨by omega, hj.2⟩

lemma specSet_succ (gs : List Gate) {n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m)
    (N : ℕ) (h : spec gs S w N) :
    (specSet gs S w (N + 1)).card = (specSet gs S w N).card + 1 := by
  classical
  have : specSet gs S w (N + 1) = insert N (specSet gs S w N) := by
    ext j
    simp only [specSet, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hj : j = N
      · exact Or.inl hj
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨by omega, h⟩
      · exact ⟨by omega, h2⟩
  rw [this, Finset.card_insert_of_notMem]
  simp [specSet]

def Inv (gs : List Gate) {n m : ℕ} (S : Fin m → Finset (Fin n)) (K : ℕ) (w : Fin m)
    (F : Finset ℕ) (E P : Finset (Fin n)) : Prop :=
  ∀ x : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
    (∀ p ∈ P, x p = true) → ¬ (∀ p ∈ S w, x p = true) →
    (∃ j ∈ F, val gs x j = false) ∨ (∃ p ∈ E, x p = false)

lemma claim (q n m K c : ℕ) (S : Fin m → Finset (Fin n)) (hq : 2 ≤ q)
    (hcard : ∀ i : Fin m, (S i).card = q + 1)
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hc : c ≤ q) (hK : c * q < K) (w : Fin m) :
    ∀ N : ℕ, ∀ (F : Finset ℕ) (E P : Finset (Fin n)) (d : ℕ),
      (∀ j ∈ F, j < N) → (∀ j ∈ F, val gs (ind (S w)) j = true) →
      Inv gs S K w F E P → P.card ≤ q * d + 1 → (P ∩ S w).card ≤ d →
      (P = ∅ ∨ ∃ u, u ≠ w ∧ S u ⊆ P) →
      c + 1 ≤ d + E.card + F.card + (specSet gs S w N).card := by
  classical
  have hmono := @val_mono gs (fun g hgm => (hg g hgm).1) n
  intro N
  induction N with
  | zero =>
    intro F E P d hF _ hInv hP hPw _
    have hF0 : F = ∅ := by
      ext j
      simp only [Finset.notMem_empty, iff_false]
      intro hj
      exact absurd (hF j hj) (by omega)
    subst hF0
    by_contra hlt
    have hdE : d + E.card ≤ c := by simp at hlt; omega
    have hlight : (Finset.univ.filter (fun i : Fin n => ind (P ∪ E) i = true)).card ≤ K := by
      rw [wt_ind]
      have h1 := Finset.card_union_le P E
      have h2 : q * d + E.card ≤ q * c := by nlinarith
      nlinarith
    have hnot : ¬ (∀ p ∈ S w, ind (P ∪ E) p = true) := by
      intro hall
      have hsub : S w ⊆ (P ∩ S w) ∪ E := by
        intro p hp
        have := hall p hp
        simp only [ind, decide_eq_true_eq, Finset.mem_union] at this
        simp only [Finset.mem_union, Finset.mem_inter]
        rcases this with h | h
        · exact Or.inl ⟨h, hp⟩
        · exact Or.inr h
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (P ∩ S w) E
      rw [hcard] at h1
      omega
    have hPin : ∀ p ∈ P, ind (P ∪ E) p = true := by
      intro p hp
      simp [ind, hp]
    rcases hInv _ hlight hPin hnot with ⟨j, hj, _⟩ | ⟨p, hp, hpx⟩
    · simp at hj
    · simp [ind, hp] at hpx
  | succ N ih =>
    intro F E P d hF hT hInv hP hPw hPu
    by_cases hN : N ∈ F
    swap
    · have hF' : ∀ j ∈ F, j < N := by
        intro j hj
        have := hF j hj
        have : j ≠ N := fun h => hN (h ▸ hj)
        omega
      have := ih F E P d hF' hT hInv hP hPw hPu
      have := specSet_mono gs S w N
      omega
    have hF0lt : ∀ j ∈ F.erase N, j < N := by
      intro j hj
      rw [Finset.mem_erase] at hj
      have := hF j hj.2
      omega
    have hF0T : ∀ j ∈ F.erase N, val gs (ind (S w)) j = true :=
      fun j hj => hT j (Finset.mem_of_mem_erase hj)
    have hF0card : (F.erase N).card + 1 = F.card := Finset.card_erase_add_one hN
    have hsm := specSet_mono gs S w N
    rcases lt_or_ge N n with hNn | hNn
    · -- an input wire: its point joins E
      have hInv' : Inv gs S K w (F.erase N) (insert ⟨N, hNn⟩ E) P := by
        intro x hx hxP hxS
        rcases hInv x hx hxP hxS with ⟨j, hj, hjx⟩ | ⟨p, hp, hpx⟩
        · by_cases hjN : j = N
          · subst hjN
            right
            refine ⟨⟨j, hNn⟩, Finset.mem_insert_self _ _, ?_⟩
            rw [val_lt _ _ _ hNn] at hjx
            exact hjx
          · exact Or.inl ⟨j, Finset.mem_erase.mpr ⟨hjN, hj⟩, hjx⟩
        · exact Or.inr ⟨p, Finset.mem_insert_of_mem hp, hpx⟩
      have := ih (F.erase N) (insert ⟨N, hNn⟩ E) P d hF0lt hF0T hInv' hP hPw hPu
      have := Finset.card_insert_le (⟨N, hNn⟩ : Fin n) E
      omega
    rcases lt_or_ge (N - n) gs.length with hk | hk
    swap
    · have := hT N hN
      rw [val_ge _ _ _ (by omega)] at this
      exact absurd this (by simp)
    obtain ⟨k, hkN⟩ : ∃ k, N = n + k := ⟨N - n, by omega⟩
    have hk' : k < gs.length := by omega
    by_cases hsp : ∃ v, v ≠ w ∧ val gs (ind (S v)) N = true
    · -- the gate is true on another set: drop it, that set joins P
      obtain ⟨v, hvw, hvN⟩ := hsp
      have hInv' : Inv gs S K w (F.erase N) E (P ∪ S v) := by
        intro x hx hxP hxS
        have hxP0 : ∀ p ∈ P, x p = true := fun p hp => hxP p (Finset.mem_union_left _ hp)
        rcases hInv x hx hxP0 hxS with ⟨j, hj, hjx⟩ | h
        · by_cases hjN : j = N
          · subst hjN
            have hxv : ∀ i, ind (S v) i = true → x i = true := by
              intro i hi
              simp only [ind, decide_eq_true_eq] at hi
              exact hxP i (Finset.mem_union_right _ hi)
            have := hmono _ _ hxv j hvN
            rw [hjx] at this
            exact absurd this (by simp)
          · exact Or.inl ⟨j, Finset.mem_erase.mpr ⟨hjN, hj⟩, hjx⟩
        · exact Or.inr h
      have hP' : (P ∪ S v).card ≤ q * (d + 1) + 1 := by
        have hu := Finset.card_union_add_card_inter P (S v)
        rw [hcard] at hu
        rcases hPu with hP0 | ⟨u, _, hu'⟩
        · subst hP0
          simp [hcard]
          nlinarith
        · have hi : 1 ≤ (P ∩ S v).card := by
            by_cases huv : u = v
            · subst huv
              rw [Finset.inter_eq_right.mpr hu', hcard]
              omega
            · have h1 := hmeet u v huv
              have h2 : S u ∩ S v ⊆ P ∩ S v := Finset.inter_subset_inter_right hu'
              have := Finset.card_le_card h2
              omega
          nlinarith
      have hPw' : ((P ∪ S v) ∩ S w).card ≤ d + 1 := by
        rw [Finset.union_inter_distrib_right]
        have h1 := Finset.card_union_le (P ∩ S w) (S v ∩ S w)
        have h2 := hmeet v w hvw
        omega
      have hPu' : (P ∪ S v = ∅ ∨ ∃ u, u ≠ w ∧ S u ⊆ P ∪ S v) :=
        Or.inr ⟨v, hvw, Finset.subset_union_right⟩
      have := ih (F.erase N) E (P ∪ S v) (d + 1) hF0lt hF0T hInv' hP' hPw' hPu'
      omega
    · -- the gate is specific to w
      push Not at hsp
      have hspec : spec gs S w N := by
        refine ⟨by omega, hT N hN, fun v hv => ?_⟩
        have := hsp v hv
        simpa using this
      have hsucc := specSet_succ gs S w N hspec
      have hTN := hT N hN
      have hval : ∀ x : Fin n → Bool, val gs x N = gs[k].op.eval (gs[k].inputs.map fun i =>
          if i < N then val gs x i else false) := by
        intro x
        rw [hkN]
        exact val_gate gs x k hk'
      have hlen := (hg _ (List.getElem_mem hk')).2
      rcases (hg _ (List.getElem_mem hk')).1 with hop | hop
      · -- AND: both inputs replace it
        rw [hval, hop, and_true_iff] at hTN
        have hch : ∀ i ∈ gs[k].inputs, i < N ∧ val gs (ind (S w)) i = true := by
          intro i hi
          have := hTN i hi
          split_ifs at this with h1
          exact ⟨h1, this⟩
        let F' := F.erase N ∪ gs[k].inputs.toFinset
        have hF'lt : ∀ j ∈ F', j < N := by
          intro j hj
          rcases Finset.mem_union.mp hj with h | h
          · exact hF0lt j h
          · exact (hch j (List.mem_toFinset.mp h)).1
        have hF'T : ∀ j ∈ F', val gs (ind (S w)) j = true := by
          intro j hj
          rcases Finset.mem_union.mp hj with h | h
          · exact hF0T j h
          · exact (hch j (List.mem_toFinset.mp h)).2
        have hInv' : Inv gs S K w F' E P := by
          intro x hx hxP hxS
          rcases hInv x hx hxP hxS with ⟨j, hj, hjx⟩ | h
          · by_cases hjN : j = N
            · subst hjN
              have hne : ¬ (gs[k].op.eval (gs[k].inputs.map fun i =>
                  if i < j then val gs x i else false) = true) := by
                rw [← hval]; simp [hjx]
              rw [hop, and_true_iff] at hne
              push Not at hne
              obtain ⟨i, hi, hix⟩ := hne
              have hiN := (hch i hi).1
              rw [if_pos hiN] at hix
              left
              exact ⟨i, Finset.mem_union_right _ (List.mem_toFinset.mpr hi), by simpa using hix⟩
            · exact Or.inl ⟨j, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hjN, hj⟩), hjx⟩
          · exact Or.inr h
        have := ih F' E P d hF'lt hF'T hInv' hP hPw hPu
        have h1 : F'.card ≤ (F.erase N).card + gs[k].inputs.toFinset.card :=
          Finset.card_union_le _ _
        have h2 := List.toFinset_card_le gs[k].inputs
        omega
      · -- OR: one input true on S w replaces it
        rw [hval, hop, or_true_iff] at hTN
        obtain ⟨i, hi, hiv⟩ := hTN
        have hiN : i < N := by
          by_contra h
          rw [if_neg h] at hiv
          exact absurd hiv (by simp)
        rw [if_pos hiN] at hiv
        let F' := insert i (F.erase N)
        have hF'lt : ∀ j ∈ F', j < N := by
          intro j hj
          rcases Finset.mem_insert.mp hj with h | h
          · exact h ▸ hiN
          · exact hF0lt j h
        have hF'T : ∀ j ∈ F', val gs (ind (S w)) j = true := by
          intro j hj
          rcases Finset.mem_insert.mp hj with h | h
          · exact h ▸ hiv
          · exact hF0T j h
        have hInv' : Inv gs S K w F' E P := by
          intro x hx hxP hxS
          rcases hInv x hx hxP hxS with ⟨j, hj, hjx⟩ | h
          · by_cases hjN : j = N
            · subst hjN
              have hne : ¬ (gs[k].op.eval (gs[k].inputs.map fun i =>
                  if i < j then val gs x i else false) = true) := by
                rw [← hval]; simp [hjx]
              rw [hop, or_true_iff] at hne
              push Not at hne
              have := hne i hi
              rw [if_pos hiN] at this
              left
              exact ⟨i, Finset.mem_insert_self _ _, by simpa using this⟩
            · exact Or.inl ⟨j, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hjN, hj⟩), hjx⟩
          · exact Or.inr h
        have := ih F' E P d hF'lt hF'T hInv' hP hPw hPu
        have h1 : F'.card ≤ (F.erase N).card + 1 := Finset.card_insert_le _ _
        omega

end PEqualNP.Outside.L_meta_925

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hcard hmeet gates out hg heval c hc hK
  rcases Nat.eq_zero_or_pos c with hc0 | hc0
  · subst hc0
    simp
  have hlightS : ∀ w : Fin m,
      (Finset.univ.filter (fun i : Fin n => PEqualNP.Outside.L_meta_925.ind (S w) i = true)).card
        ≤ K := by
    intro w
    rw [PEqualNP.Outside.L_meta_925.wt_ind, hcard]
    nlinarith
  have hcount : ∀ w : Fin m,
      c ≤ (PEqualNP.Outside.L_meta_925.specSet gates S w (n + gates.length)).card := by
    intro w
    have hout : PEqualNP.Outside.L_meta_925.val gates
        (PEqualNP.Outside.L_meta_925.ind (S w)) (out w) = true := by
      rw [← PEqualNP.Outside.L_meta_925.eval_eq, heval w _ (hlightS w)]
      simp [PEqualNP.Outside.L_meta_925.ind]
    have houtlt : out w < n + gates.length := by
      by_contra h
      rw [PEqualNP.Outside.L_meta_925.val_ge _ _ _ (by omega)] at hout
      exact absurd hout (by simp)
    have hInv0 : PEqualNP.Outside.L_meta_925.Inv gates S K w {out w} ∅ ∅ := by
      intro x hx _ hxS
      left
      refine ⟨out w, Finset.mem_singleton_self _, ?_⟩
      rw [← PEqualNP.Outside.L_meta_925.eval_eq, heval w x hx]
      simpa using hxS
    have := PEqualNP.Outside.L_meta_925.claim q n m K c S hq hcard hmeet gates hg hc hK w
      (n + gates.length) {out w} ∅ ∅ 0
      (by simpa using houtlt) (by simpa using hout) hInv0 (by simp) (by simp) (Or.inl rfl)
    simp at this
    omega
  have hdisj : ∀ v ∈ (Finset.univ : Finset (Fin m)), ∀ w ∈ (Finset.univ : Finset (Fin m)),
      v ≠ w → Disjoint (PEqualNP.Outside.L_meta_925.specSet gates S v (n + gates.length))
        (PEqualNP.Outside.L_meta_925.specSet gates S w (n + gates.length)) := by
    intro v _ w _ hvw
    rw [Finset.disjoint_left]
    intro j hjv hjw
    simp only [PEqualNP.Outside.L_meta_925.specSet, Finset.mem_filter] at hjv hjw
    have h1 := hjv.2.2.1
    have h2 := hjw.2.2.2 v hvw
    rw [h1] at h2
    exact absurd h2 (by simp)
  have hsub : (Finset.univ.biUnion fun w =>
      PEqualNP.Outside.L_meta_925.specSet gates S w (n + gates.length)) ⊆
        Finset.Ico n (n + gates.length) := by
    intro j hj
    simp only [Finset.mem_biUnion, PEqualNP.Outside.L_meta_925.specSet, Finset.mem_filter,
      Finset.mem_range] at hj
    obtain ⟨_, _, hj1, hj2⟩ := hj
    simp only [Finset.mem_Ico]
    exact ⟨hj2.1, hj1⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Nat.card_Ico] at hle
  have hsum : ∑ _w : Fin m, c ≤ ∑ w : Fin m,
      (PEqualNP.Outside.L_meta_925.specSet gates S w (n + gates.length)).card :=
    Finset.sum_le_sum fun w _ => hcount w
  simp at hsum
  omega
