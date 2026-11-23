import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925
open PEqualNP.CircuitLowerBounds

-- A wire is a predicate on the set of true input positions.
abbrev V (n : ℕ) := Finset (Fin n) → Prop

def joinV {n : ℕ} (a b : V n) : V n := fun X => a X ∨ b X
def meetV {n : ℕ} (a b : V n) : V n := fun X => a X ∧ b X

def Parents {n : ℕ} (F : ℕ → V n) (k : ℕ) := ∃ a < k, ∃ b < k,
  F k = joinV (F a) (F b) ∨ F k = meetV (F a) (F b)

-- Every wire is monotone once index 0 is false, index 1 is true, the next
-- n indices are the input positions and every later index is a join or meet.
lemma mono_of {n : ℕ} {F : ℕ → V n} {N : ℕ} (h0 : ∀ X, ¬ F 0 X) (h1 : ∀ X, F 1 X)
    (hin : ∀ (p : Fin n) (X : Finset (Fin n)), F ((p : ℕ) + 2) X ↔ p ∈ X)
    (hpar : ∀ k, n + 2 ≤ k → k < N → Parents F k) :
    ∀ i < N, ∀ X Y : Finset (Fin n), X ⊆ Y → F i X → F i Y := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi X Y hXY hX
    by_cases hb : i < n + 2
    · by_cases hi0 : i = 0
      · rw [hi0] at hX
        exact (h0 X hX).elim
      by_cases hi1 : i = 1
      · rw [hi1]
        exact h1 Y
      have hp : i - 2 < n := by omega
      have e : ((⟨i - 2, hp⟩ : Fin n) : ℕ) + 2 = i := by
        show i - 2 + 2 = i
        omega
      have hx := hin ⟨i - 2, hp⟩ X
      have hy := hin ⟨i - 2, hp⟩ Y
      rw [e] at hx hy
      exact hy.mpr (hXY (hx.mp hX))
    · obtain ⟨a, ha, b, hb', hj | hm⟩ := hpar i (by omega) hi
      · rw [hj] at hX ⊢
        rcases hX with h | h
        · exact Or.inl (ih a ha (by omega) X Y hXY h)
        · exact Or.inr (ih b hb' (by omega) X Y hXY h)
      · rw [hm] at hX ⊢
        exact ⟨ih a ha (by omega) X Y hXY hX.1, ih b hb' (by omega) X Y hXY hX.2⟩

-- A wire is specific to w: true on the set of w, false on every other set.
def Spec {n m : ℕ} (F : ℕ → V n) (S : Fin m → Finset (Fin n)) (w : Fin m) (g : ℕ) : Prop :=
  F g (S w) ∧ ∀ v, v ≠ w → ¬ F g (S v)

-- The state of the descent when all indices from k upward have been handled.
def Inv {n m : ℕ} (F : ℕ → V n) (S : Fin m → Finset (Fin n)) (K N : ℕ) (w : Fin m)
    (k : ℕ) : Prop :=
  ∃ (Fs : Finset ℕ) (T : Finset (Fin m)) (A : Finset ℕ),
    (∀ i ∈ Fs, F i (S w) ∧ i < k) ∧
    (∀ X : Finset (Fin n), X.card ≤ K → T.biUnion S ⊆ X → ¬ S w ⊆ X → ∃ i ∈ Fs, ¬ F i X) ∧
    w ∉ T ∧
    Fs.card + T.card ≤ 1 + A.card ∧
    (∀ g ∈ A, Spec F S w g ∧ k ≤ g ∧ g < N)

lemma inv_step {n m : ℕ} {F : ℕ → V n} {S : Fin m → Finset (Fin n)} {K N : ℕ} {w : Fin m}
    {k : ℕ} (hmono : ∀ i < N, ∀ X Y : Finset (Fin n), X ⊆ Y → F i X → F i Y)
    (hpar : Parents F k) (hkN : k < N) (h : Inv F S K N w (k + 1)) : Inv F S K N w k := by
  classical
  obtain ⟨Fs, T, A, h1, h2, h3, h4, h5⟩ := h
  have hA' : ∀ g ∈ A, Spec F S w g ∧ k ≤ g ∧ g < N := by
    intro g hg
    have hh := h5 g hg
    exact ⟨hh.1, by omega, hh.2.2⟩
  by_cases hk : k ∈ Fs
  swap
  · refine ⟨Fs, T, A, ?_, h2, h3, h4, hA'⟩
    intro i hi
    have hh := h1 i hi
    have hne : i ≠ k := fun e => hk (e ▸ hi)
    exact ⟨hh.1, by omega⟩
  have hkw : F k (S w) := (h1 k hk).1
  have hkA : k ∉ A := fun hA => by
    have hh := (h5 k hA).2.1
    omega
  have hlt : ∀ i ∈ Fs.erase k, F i (S w) ∧ i < k := by
    intro i hi
    obtain ⟨hne, hi⟩ := Finset.mem_erase.mp hi
    have hh := h1 i hi
    exact ⟨hh.1, by omega⟩
  have hcard : (Fs.erase k).card + 1 = Fs.card := Finset.card_erase_add_one hk
  by_cases hs : ∀ v, v ≠ w → ¬ F k (S v)
  · have hspec : Spec F S w k := ⟨hkw, hs⟩
    have hA : ∀ g ∈ insert k A, Spec F S w g ∧ k ≤ g ∧ g < N := by
      intro g hg
      rcases Finset.mem_insert.mp hg with e | hg
      · rw [e]
        exact ⟨hspec, le_refl _, hkN⟩
      · exact hA' g hg
    have hAc : (insert k A).card = A.card + 1 := Finset.card_insert_of_notMem hkA
    obtain ⟨a, ha, b, hb, hj | hm⟩ := hpar
    · have hor : F a (S w) ∨ F b (S w) := by
        rw [hj] at hkw
        exact hkw
      have key : ∀ a', a' < k → F a' (S w) → (∀ X, ¬ F k X → ¬ F a' X) →
          Inv F S K N w k := by
        intro a' ha' haw himp
        refine ⟨insert a' (Fs.erase k), T, insert k A, ?_, ?_, h3, ?_, hA⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with e | hi
          · rw [e]
            exact ⟨haw, ha'⟩
          · exact hlt i hi
        · intro X hX hT hw
          obtain ⟨i, hi, hiX⟩ := h2 X hX hT hw
          by_cases hik : i = k
          · rw [hik] at hiX
            exact ⟨a', Finset.mem_insert_self _ _, himp X hiX⟩
          · exact ⟨i, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hik, hi⟩), hiX⟩
        · have hh := Finset.card_insert_le a' (Fs.erase k)
          omega
      rcases hor with h | h
      · exact key a ha h (fun X hX hx => hX (by rw [hj]; exact Or.inl hx))
      · exact key b hb h (fun X hX hx => hX (by rw [hj]; exact Or.inr hx))
    · have hand : F a (S w) ∧ F b (S w) := by
        rw [hm] at hkw
        exact hkw
      refine ⟨insert a (insert b (Fs.erase k)), T, insert k A, ?_, ?_, h3, ?_, hA⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with e | hi
        · rw [e]
          exact ⟨hand.1, ha⟩
        rcases Finset.mem_insert.mp hi with e | hi
        · rw [e]
          exact ⟨hand.2, hb⟩
        · exact hlt i hi
      · intro X hX hT hw
        obtain ⟨i, hi, hiX⟩ := h2 X hX hT hw
        by_cases hik : i = k
        · rw [hik] at hiX
          by_cases hax : F a X
          · refine ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun hbx => hiX ?_⟩
            rw [hm]
            exact ⟨hax, hbx⟩
          · exact ⟨a, Finset.mem_insert_self _ _, hax⟩
        · exact ⟨i, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hik, hi⟩)), hiX⟩
      · have hh1 := Finset.card_insert_le a (insert b (Fs.erase k))
        have hh2 := Finset.card_insert_le b (Fs.erase k)
        omega
  · have hex : ∃ v, v ≠ w ∧ F k (S v) := by
      by_contra hno
      exact hs (fun v hv hF => hno ⟨v, hv, hF⟩)
    obtain ⟨v, hvw, hv⟩ := hex
    refine ⟨Fs.erase k, insert v T, A, hlt, ?_, ?_, ?_, hA'⟩
    · intro X hX hT hw
      rw [Finset.biUnion_insert] at hT
      have hT' : T.biUnion S ⊆ X := fun p hp => hT (Finset.mem_union_right _ hp)
      have hv' : S v ⊆ X := fun p hp => hT (Finset.mem_union_left _ hp)
      obtain ⟨i, hi, hiX⟩ := h2 X hX hT' hw
      refine ⟨i, Finset.mem_erase.mpr ⟨?_, hi⟩, hiX⟩
      intro e
      rw [e] at hiX
      exact hiX (hmono k hkN _ _ hv' hv)
    · intro hw
      rcases Finset.mem_insert.mp hw with e | hw
      · exact hvw e.symm
      · exact h3 hw
    · have hh := Finset.card_insert_le v T
      omega

-- The union of d of the sets has at most d * q + 1 points.
lemma union_card {n m : ℕ} (S : Fin m → Finset (Fin n)) (q : ℕ)
    (hcard : ∀ i, (S i).card = q + 1) (hint : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (T : Finset (Fin m)) : T.Nonempty → (T.biUnion S).card ≤ T.card * q + 1 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro h
    exact absurd h (by simp)
  | insert v T hv ih =>
    intro _
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hv]
    rcases T.eq_empty_or_nonempty with hT | hT
    · rw [hT]
      simp [hcard]
    · obtain ⟨u, hu⟩ := hT
      have hne : v ≠ u := fun e => hv (e ▸ hu)
      have h1 : S v ∩ S u ⊆ S v ∩ T.biUnion S :=
        Finset.inter_subset_inter (Finset.Subset.refl _) (Finset.subset_biUnion_of_mem S hu)
      have h2 := Finset.card_le_card h1
      rw [hint v u hne] at h2
      have h3 := Finset.card_union_add_card_inter (S v) (T.biUnion S)
      have h4 := ih ⟨u, hu⟩
      have h5 := hcard v
      have h6 : (T.card + 1) * q = T.card * q + q := by ring
      omega

lemma inter_card {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hint : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) (w : Fin m)
    (T : Finset (Fin m)) (hw : w ∉ T) : (T.biUnion S ∩ S w).card ≤ T.card := by
  classical
  rw [Finset.biUnion_inter]
  refine le_trans Finset.card_biUnion_le ?_
  have h : ∀ v ∈ T, (S v ∩ S w).card = 1 := fun v hv => hint v w (fun e => hw (e ▸ hv))
  rw [Finset.sum_congr rfl h]
  simp

-- The end of the descent: only constants and input positions are left.
lemma final {n m : ℕ} {F : ℕ → V n} {S : Fin m → Finset (Fin n)} {q K N c : ℕ} {w : Fin m}
    (h0 : ∀ X, ¬ F 0 X) (h1' : ∀ X, F 1 X)
    (hin : ∀ (p : Fin n) (X : Finset (Fin n)), F ((p : ℕ) + 2) X ↔ p ∈ X)
    (hq : 1 ≤ q) (hcard : ∀ i, (S i).card = q + 1)
    (hint : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hc : c ≤ q) (hcK : c * q < K)
    (h : Inv F S K N w (n + 2)) :
    ∃ A : Finset ℕ, c ≤ A.card ∧ ∀ g ∈ A, Spec F S w g ∧ n + 2 ≤ g ∧ g < N := by
  classical
  obtain ⟨Fs, T, A, h1, h2, h3, h4, h5⟩ := h
  refine ⟨A, ?_, h5⟩
  by_contra hge
  have hlt : A.card < c := Nat.lt_of_not_le hge
  obtain ⟨T', hT'⟩ : ∃ T' : Finset (Fin n), ∀ p, p ∈ T' ↔ (p : ℕ) + 2 ∈ Fs :=
    ⟨Finset.univ.filter (fun p : Fin n => (p : ℕ) + 2 ∈ Fs), by simp⟩
  have hT'card : T'.card ≤ Fs.card := by
    apply Finset.card_le_card_of_injOn (fun p : Fin n => (p : ℕ) + 2)
    · intro p hp
      exact (hT' p).mp (Finset.mem_coe.mp hp)
    · intro p _ p' _ hpp
      have hpp' : (p : ℕ) + 2 = (p' : ℕ) + 2 := hpp
      exact Fin.ext (by omega)
  have hall : ∀ i ∈ Fs, F i (T.biUnion S ∪ T') := by
    intro i hi
    obtain ⟨hiw, hlt'⟩ := h1 i hi
    by_cases hi0 : i = 0
    · rw [hi0] at hiw
      exact (h0 _ hiw).elim
    by_cases hi1 : i = 1
    · rw [hi1]
      exact h1' _
    have hp : i - 2 < n := by omega
    have e : ((⟨i - 2, hp⟩ : Fin n) : ℕ) + 2 = i := by
      show i - 2 + 2 = i
      omega
    have hx := hin ⟨i - 2, hp⟩ (T.biUnion S ∪ T')
    rw [e] at hx
    apply hx.mpr
    apply Finset.mem_union_right
    rw [hT', e]
    exact hi
  have hPw := inter_card S hint w T h3
  have hnsub : ¬ S w ⊆ T.biUnion S ∪ T' := by
    intro hsub
    have h' : S w ⊆ (T.biUnion S ∩ S w) ∪ T' := by
      intro p hp
      rcases Finset.mem_union.mp (hsub hp) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h, hp⟩)
      · exact Finset.mem_union_right _ h
    have h6 := Finset.card_le_card h'
    have h7 := Finset.card_union_le (T.biUnion S ∩ S w) T'
    rw [hcard w] at h6
    omega
  have hXK : (T.biUnion S ∪ T').card ≤ K := by
    have h7 := Finset.card_union_le (T.biUnion S) T'
    rcases T.eq_empty_or_nonempty with hT | hT
    · rw [hT] at h7 h4 ⊢
      simp only [Finset.biUnion_empty, Finset.card_empty] at h7 h4 ⊢
      have h8 : c ≤ c * q := Nat.le_mul_of_pos_right c hq
      omega
    · have h8 := union_card S q hcard hint T hT
      have h9 : (T.card + Fs.card) * q ≤ c * q := Nat.mul_le_mul_right q (by omega)
      have h10 : Fs.card ≤ Fs.card * q := Nat.le_mul_of_pos_right _ hq
      rw [Nat.add_mul] at h9
      omega
  obtain ⟨i, hi, hiX⟩ := h2 _ hXK Finset.subset_union_left hnsub
  exact hiX (hall i hi)

-- The circuit model.
def setInput {n : ℕ} (X : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∈ X)

def raw {n : ℕ} (gs : List Gate) (X : Finset (Fin n)) : List Bool :=
  (Circuit.mk gs 0).wires (List.ofFn (setInput X))

lemma raw_step {n : ℕ} (gs : List Gate) (g : Gate) (X : Finset (Fin n)) :
    raw (gs ++ [g]) X = raw gs X ++
      [g.op.eval (g.inputs.map fun i => (raw gs X).getD i false)] := by
  simp [raw, Circuit.wires, List.foldl_append]

lemma raw_length {n : ℕ} (gs : List Gate) (X : Finset (Fin n)) :
    (raw gs X).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [raw, Circuit.wires]
  | append_singleton gs g ih =>
    rw [raw_step, List.length_append, ih, List.length_append]
    simp
    omega

def size (n : ℕ) (gs : List Gate) := n + 2 + gs.length

-- Indices zero and one are the constants. Every original wire is shifted
-- by two. A missing operand is redirected to zero.
def model {n : ℕ} (gs : List Gate) (i : ℕ) : V n :=
  fun X => if i = 1 then True else if i < 2 then False
    else (raw gs X).getD (i - 2) false = true

def addr (n : ℕ) (gs : List Gate) (i : ℕ) := if i < n + gs.length then i + 2 else 0

lemma addr_lt (n : ℕ) (gs : List Gate) (i : ℕ) : addr n gs i < size n gs := by
  unfold addr size
  split <;> omega

lemma read_addr {n : ℕ} (gs : List Gate) (i : ℕ) (X : Finset (Fin n)) :
    model gs (addr n gs i) X ↔ (raw gs X).getD i false = true := by
  by_cases h : i < n + gs.length
  · simp [model, addr, h, show i + 2 ≠ 1 by omega]
  · rw [List.getD_eq_default _ _ (by rw [raw_length]; omega)]
    simp [model, addr, h]

lemma model_old {n : ℕ} (gs : List Gate) (g : Gate) (i : ℕ) (hi : i < size n gs) :
    (model (gs ++ [g]) i : V n) = model gs i := by
  funext X
  by_cases h : i < 2
  · simp [model, h]
  · have hs : i - 2 < (raw gs X).length := by
      rw [raw_length]
      unfold size at hi
      omega
    simp only [model, raw_step, List.getD_append _ _ _ _ hs]

lemma model_last {n : ℕ} (gs : List Gate) (g : Gate) (X : Finset (Fin n)) :
    model (gs ++ [g]) (size n gs) X ↔
      g.op.eval (g.inputs.map fun i => (raw gs X).getD i false) = true := by
  have hs : size n gs - 2 = (raw gs X).length := by
    rw [raw_length]
    unfold size
    omega
  simp [model, show size n gs ≠ 1 by unfold size; omega,
    show ¬ size n gs < 2 by unfold size; omega, raw_step, hs]

def Legal (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

-- Every allowed gate is a binary join or meet of earlier indices.
lemma last_parents {n : ℕ} (gs : List Gate) (g : Gate) (hg : Legal g) :
    Parents (model (gs ++ [g]) : ℕ → V n) (size n gs) := by
  obtain ⟨hop, hlen⟩ := hg
  have hn : 1 < size n gs := by unfold size; omega
  rcases hin : g.inputs with _ | ⟨i, t⟩
  · rcases hop with ha | ho
    · refine ⟨1, hn, 1, hn, Or.inl ?_⟩
      funext X
      apply propext
      rw [model_last]
      simp [ha, hin, GateOp.eval, joinV, model]
    · refine ⟨0, by omega, 0, by omega, Or.inl ?_⟩
      funext X
      apply propext
      rw [model_last]
      simp [ho, hin, GateOp.eval, joinV, model]
  · cases t with
    | nil =>
      refine ⟨addr n gs i, addr_lt _ _ _, addr n gs i, addr_lt _ _ _, Or.inl ?_⟩
      funext X
      apply propext
      rcases hop with h | h <;>
        simp [model_last, h, hin, GateOp.eval, joinV, model_old _ _ _ (addr_lt n gs i),
          read_addr]
    | cons j t =>
      have ht : t = [] := by
        rw [hin] at hlen
        simpa using hlen
      subst t
      refine ⟨addr n gs i, addr_lt _ _ _, addr n gs j, addr_lt _ _ _, ?_⟩
      rcases hop with h | h
      · right
        funext X
        apply propext
        simp [model_last, h, hin, GateOp.eval, meetV, model_old _ _ _ (addr_lt n gs i),
          model_old _ _ _ (addr_lt n gs j), read_addr]
      · left
        funext X
        apply propext
        simp [model_last, h, hin, GateOp.eval, joinV, model_old _ _ _ (addr_lt n gs i),
          model_old _ _ _ (addr_lt n gs j), read_addr]

lemma model_parents {n : ℕ} (gs : List Gate) (hleg : ∀ g ∈ gs, Legal g) :
    ∀ k, n + 2 ≤ k → k < size n gs → Parents (model gs : ℕ → V n) k := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k h1 h2
    unfold size at h2
    simp at h2
    omega
  | append_singleton gs g ih =>
    intro k h1 h2
    have hh : size n (gs ++ [g]) = size n gs + 1 := by
      simp [size]
      omega
    rw [hh] at h2
    rcases Nat.lt_or_eq_of_le (show k ≤ size n gs by omega) with h | h
    · obtain ⟨a, ha, b, hb, hp⟩ := ih (fun e he => hleg e (by simp [he])) k h1 h
      refine ⟨a, ha, b, hb, ?_⟩
      rwa [model_old _ _ _ h, model_old _ _ _ (ha.trans h), model_old _ _ _ (hb.trans h)]
    · rw [h]
      exact last_parents gs g (hleg g (by simp))

lemma base_read {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n + 2) :
    (model gs i : V n) = model [] i := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [model_old, ih]
    unfold size
    omega

lemma model_zero {n : ℕ} (gs : List Gate) (X : Finset (Fin n)) : ¬ model gs 0 X := by
  simp [model]

lemma model_one {n : ℕ} (gs : List Gate) (X : Finset (Fin n)) : model gs 1 X := by
  simp [model]

lemma model_input {n : ℕ} (gs : List Gate) (p : Fin n) (X : Finset (Fin n)) :
    model gs ((p : ℕ) + 2) X ↔ p ∈ X := by
  have hp := p.isLt
  rw [base_read gs _ (by omega)]
  unfold model
  have hp1 : ¬ ((p : ℕ) + 2 = 1) := by omega
  have hp2 : ¬ ((p : ℕ) + 2 < 2) := by omega
  simp only [hp1, hp2, ↓reduceIte]
  show (List.ofFn (setInput X)).getD ((p : ℕ) + 2 - 2) false = true ↔ _
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega), List.getElem_ofFn]
  simp [setInput]

lemma bound {n m : ℕ} (q K : ℕ) (S : Fin m → Finset (Fin n)) (hq : 2 ≤ q)
    (hcard : ∀ i, (S i).card = q + 1) (hint : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (gs : List Gate) (out : Fin m → ℕ) (hleg : ∀ g ∈ gs, Legal g)
    (hcorr : ∀ (w : Fin m) (X : Finset (Fin n)), X.card ≤ K →
      ((raw gs X).getD (out w) false = true ↔ S w ⊆ X))
    (c : ℕ) (hc : c ≤ q) (hcK : c * q < K) : m * c ≤ gs.length := by
  classical
  rcases Nat.eq_zero_or_pos c with hc0 | hc0
  · rw [hc0]
    simp
  have hKq : q + 1 ≤ K := by
    have hh : q ≤ c * q := Nat.le_mul_of_pos_left q hc0
    omega
  have hpar := model_parents (n := n) gs hleg
  have hmono := mono_of (F := (model gs : ℕ → V n)) (N := size n gs) (model_zero gs)
    (model_one gs) (model_input gs) hpar
  have per_w : ∀ w : Fin m, ∃ A : Finset ℕ, c ≤ A.card ∧
      ∀ g ∈ A, Spec (model gs) S w g ∧ n + 2 ≤ g ∧ g < size n gs := by
    intro w
    apply final (model_zero gs) (model_one gs) (model_input gs) (by omega) hcard hint hc hcK
    have hstart : Inv (model gs) S K (size n gs) w (size n gs) := by
      refine ⟨{addr n gs (out w)}, ∅, ∅, ?_, ?_, by simp, by simp, by simp⟩
      · intro i hi
        rw [Finset.mem_singleton.mp hi]
        refine ⟨?_, addr_lt n gs _⟩
        rw [read_addr]
        exact (hcorr w (S w) (by rw [hcard]; exact hKq)).mpr (Finset.Subset.refl _)
      · intro X hX _ hw
        refine ⟨_, Finset.mem_singleton_self _, ?_⟩
        rw [read_addr]
        exact fun h => hw ((hcorr w X hX).mp h)
    have hdown : ∀ j, j ≤ gs.length → Inv (model gs) S K (size n gs) w (size n gs - j) := by
      intro j
      induction j with
      | zero =>
        intro _
        exact hstart
      | succ j ih =>
        intro hj
        have hk : size n gs - j = (size n gs - (j + 1)) + 1 := by
          unfold size
          omega
        have hprev := ih (by omega)
        rw [hk] at hprev
        exact inv_step hmono (hpar _ (by unfold size; omega) (by unfold size; omega))
          (by unfold size; omega) hprev
    have hend := hdown gs.length (le_refl _)
    have e : size n gs - gs.length = n + 2 := by
      unfold size
      omega
    rwa [e] at hend
  choose A hA using per_w
  have hdisj : ∀ w ∈ (Finset.univ : Finset (Fin m)), ∀ w' ∈ (Finset.univ : Finset (Fin m)),
      w ≠ w' → Disjoint (A w) (A w') := by
    intro w _ w' _ hne
    rw [Finset.disjoint_left]
    intro g hg hg'
    exact ((hA w').2 g hg').1.2 w hne ((hA w).2 g hg).1.1
  have hsub : (Finset.univ : Finset (Fin m)).biUnion A ⊆ Finset.Ico (n + 2) (size n gs) := by
    intro g hg
    obtain ⟨w, _, hg⟩ := Finset.mem_biUnion.mp hg
    have hh := (hA w).2 g hg
    exact Finset.mem_Ico.mpr ⟨hh.2.1, hh.2.2⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Nat.card_Ico] at h1
  have h2 : ∑ _w : Fin m, c ≤ ∑ w : Fin m, (A w).card :=
    Finset.sum_le_sum (fun w _ => (hA w).1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  unfold size at h1
  omega

end PEqualNP.Outside.L_meta_925

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  intro q n m K S hq hcard hint gates out hg hcorrect c hc hcK
  apply PEqualNP.Outside.L_meta_925.bound q K S hq hcard hint gates out hg _ c hc hcK
  intro w X hX
  have hfilter : (Finset.univ.filter
      (fun i : Fin n => PEqualNP.Outside.L_meta_925.setInput X i = true)) = X := by
    ext i
    simp [PEqualNP.Outside.L_meta_925.setInput]
  have hh := hcorrect w (PEqualNP.Outside.L_meta_925.setInput X) (by rw [hfilter]; exact hX)
  have hraw : (PEqualNP.Outside.L_meta_925.raw gates X).getD (out w) false =
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩
        (List.ofFn (PEqualNP.Outside.L_meta_925.setInput X)) := rfl
  rw [hraw, hh]
  simp [PEqualNP.Outside.L_meta_925.setInput, Finset.subset_iff]
