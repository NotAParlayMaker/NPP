import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1595

lemma ifp {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

lemma ifn {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ifp hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ifn hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def gA (gs : List Gate) (j : ℕ) : Gate := gs.getD j ⟨GateOp.or, []⟩

lemma gA_eq {gs : List Gate} {j : ℕ} (hj : j < gs.length) : gA gs j = gs[j] := by
  simp [gA, List.getD_eq_getElem?_getD, hj]

lemma gA_mem {gs : List Gate} {j : ℕ} (hj : j < gs.length) : gA gs j ∈ gs := by
  rw [gA_eq hj]; exact List.getElem_mem hj

def V {N : ℕ} (gs : List Gate) (z : Fin N → Bool) (u : ℕ) : Bool :=
  (gs.foldl stepWire (List.ofFn z)).getD u false

lemma V_input {N : ℕ} (gs : List Gate) (z : Fin N → Bool) {u : ℕ} (hu : u < N) :
    V gs z u = z ⟨u, hu⟩ := by
  unfold V
  rw [foldl_getD_lt _ _ _ (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma V_ge {N : ℕ} (gs : List Gate) (z : Fin N → Bool) {u : ℕ} (hu : N + gs.length ≤ u) :
    V gs z u = false := by
  unfold V
  apply getD_ge
  rw [foldl_length]
  simpa using hu

lemma V_gate {N : ℕ} (gs : List Gate) (z : Fin N → Bool) {j : ℕ} (hj : j < gs.length) :
    V gs z (N + j) = (gA gs j).op.eval ((gA gs j).inputs.map fun i =>
      if i < N + j then V gs z i else false) := by
  rw [gA_eq hj]
  have key := foldl_getD_gate gs (List.ofFn z) j hj
  rw [List.length_ofFn] at key
  exact key

lemma and_eval {α : Type} (l : List α) (f : α → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

lemma or_eval {α : Type} (l : List α) (f : α → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

lemma notzero_of {N : ℕ} (gs : List Gate) (Y : Finset (Fin N)) (t : ℕ)
    (ht : t < gs.length) (hnt : (gA gs t).op = GateOp.not)
    (hY : V gs (fun v => decide (v ∈ Y)) (N + t) = false)
    (ih : ∀ i < N + t, ∀ x x' : Fin N → Bool, (∀ v ∈ Y, x v = true) →
      (∀ v, x v = true → x' v = true) → V gs x i = true → V gs x' i = true)
    (x : Fin N → Bool) (hx : ∀ v ∈ Y, x v = true) : V gs x (N + t) = false := by
  rw [V_gate gs _ ht, hnt] at hY
  rw [V_gate gs _ ht, hnt]
  generalize (gA gs t).inputs = l at hY ⊢
  cases l with
  | nil => simp [GateOp.eval] at hY
  | cons i rest =>
    simp only [List.map_cons, GateOp.eval, List.headD_cons] at hY ⊢
    by_cases hlt : i < N + t
    · rw [ifp hlt] at hY ⊢
      have h1 : V gs (fun v => decide (v ∈ Y)) i = true := by simpa using hY
      have h2 := ih i hlt _ x (fun v hv => by simp [hv]) (fun v hv => hx v (by simpa using hv)) h1
      rw [h2]; rfl
    · rw [ifn hlt] at hY; exact absurd hY (by decide)

lemma mono {N : ℕ} (gs : List Gate) (Y : Finset (Fin N)) (t : ℕ)
    (hop : ∀ k < gs.length, (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or ∨
      (gA gs k).op = GateOp.not)
    (hnot : ∀ k < gs.length, (gA gs k).op = GateOp.not → k = t)
    (hY : V gs (fun v => decide (v ∈ Y)) (N + t) = false) :
    ∀ j, ∀ x x' : Fin N → Bool, (∀ v ∈ Y, x v = true) →
      (∀ v, x v = true → x' v = true) → V gs x j = true → V gs x' j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro x x' hxY hxx' h
    rcases lt_or_ge j N with hj | hj
    · rw [V_input gs _ hj] at h ⊢; exact hxx' _ h
    · obtain ⟨k, rfl⟩ : ∃ k, j = N + k := ⟨j - N, by omega⟩
      by_cases hk : k < gs.length
      · rcases hop k hk with ho | ho | ho
        · rw [V_gate gs _ hk, ho, and_eval] at h
          rw [V_gate gs _ hk, ho, and_eval]
          intro i hi
          have h1 := h i hi
          by_cases hlt : i < N + k
          · rw [ifp hlt] at h1 ⊢; exact ih i hlt x x' hxY hxx' h1
          · rw [ifn hlt] at h1; exact absurd h1 (by decide)
        · rw [V_gate gs _ hk, ho, or_eval] at h
          rw [V_gate gs _ hk, ho, or_eval]
          obtain ⟨i, hi, h1⟩ := h
          by_cases hlt : i < N + k
          · rw [ifp hlt] at h1
            exact ⟨i, hi, by rw [ifp hlt]; exact ih i hlt x x' hxY hxx' h1⟩
          · rw [ifn hlt] at h1; exact absurd h1 (by decide)
        · have hkt := hnot k hk ho
          subst hkt
          rw [notzero_of gs Y k hk ho hY (fun i hi => ih i hi) x hxY] at h
          exact absurd h (by decide)
      · rw [V_ge gs _ (by omega)] at h; exact absurd h (by decide)

def xh {N : ℕ} (S : Finset (Fin N)) : Fin N → Bool := fun v => decide (v ∉ S)

def pt {N : ℕ} (Y : Finset (Fin N)) (s : Fin N) : Fin N → Bool :=
  fun w => decide (w ∈ Y ∨ w = s)

def oneB {N : ℕ} (gs : List Gate) (S : Finset (Fin N)) (j : ℕ) : Bool := V gs (xh S) j

def Pp {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (j : ℕ) : Finset (Fin N) :=
  S.filter (fun s => V gs (pt Y s) j = true)

def keepB {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (j : ℕ) : Bool :=
  !oneB gs S j && decide (2 ≤ (Pp gs S Y j).card)

def rk {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => keepB gs S Y (N + i) = true)).card

noncomputable def phi {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (j : ℕ) : ℕ :=
  if 2 ≤ (Pp gs S Y j).card then N + rk gs S Y (j - N)
  else if h : (Pp gs S Y j).Nonempty then (h.choose : ℕ) else N + gs.length

noncomputable def mk {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (k : ℕ) : Gate :=
  ⟨(gA gs k).op, ((gA gs k).inputs.filter (fun j => !(decide (j < N + k) && oneB gs S j))).map
    (fun j => if j < N + k then phi gs S Y j else N + gs.length)⟩

noncomputable def newG {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) : ℕ → List Gate
  | 0 => []
  | k + 1 => if keepB gs S Y (N + k) = true then newG gs S Y k ++ [mk gs S Y k]
      else newG gs S Y k

noncomputable def star {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (x : Fin N → Bool)
    (j : ℕ) : Bool :=
  if oneB gs S j = true then true
  else if 2 ≤ (Pp gs S Y j).card then V (newG gs S Y gs.length) x (N + rk gs S Y (j - N))
  else if h : (Pp gs S Y j).Nonempty then x h.choose else false

lemma mem_Pp {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (j : ℕ) (s : Fin N) :
    s ∈ Pp gs S Y j ↔ s ∈ S ∧ V gs (pt Y s) j = true := by
  simp [Pp]

lemma keepB_iff {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (j : ℕ) :
    keepB gs S Y j = true ↔ oneB gs S j = false ∧ 2 ≤ (Pp gs S Y j).card := by
  simp [keepB]

lemma rk_succ {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (k : ℕ) :
    rk gs S Y (k + 1) = rk gs S Y k + (if keepB gs S Y (N + k) = true then 1 else 0) := by
  unfold rk
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

lemma rk_mono {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) {k K : ℕ} (h : k ≤ K) :
    rk gs S Y k ≤ rk gs S Y K := by
  induction K, h using Nat.le_induction with
  | base => exact le_rfl
  | succ K _ ih => rw [rk_succ]; omega

lemma rk_lt {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) {k K : ℕ} (h : k < K)
    (hk : keepB gs S Y (N + k) = true) : rk gs S Y k < rk gs S Y K := by
  have h1 := rk_mono gs S Y (show k + 1 ≤ K from h)
  rw [rk_succ, ifp hk] at h1
  omega

lemma rk_le {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (k : ℕ) : rk gs S Y k ≤ k := by
  induction k with
  | zero => simp [rk]
  | succ k ih => rw [rk_succ]; split_ifs <;> omega

lemma newG_length {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (K : ℕ) :
    (newG gs S Y K).length = rk gs S Y K := by
  induction K with
  | zero => simp [newG, rk]
  | succ K ih =>
    rw [rk_succ]
    simp only [newG]
    split_ifs with h <;> simp [ih]

lemma newG_get {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (K : ℕ) :
    ∀ k < K, keepB gs S Y (N + k) = true →
      (newG gs S Y K)[rk gs S Y k]? = some (mk gs S Y k) := by
  induction K with
  | zero => intro k hk; omega
  | succ K ih =>
    intro k hk hkeep
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · have h1 := ih k h hkeep
      have hlt : rk gs S Y k < (newG gs S Y K).length := by
        rw [newG_length]; exact rk_lt gs S Y h hkeep
      simp only [newG]
      split_ifs
      · rw [List.getElem?_append_left hlt]; exact h1
      · exact h1
    · subst h
      simp only [newG]
      rw [ifp hkeep, ← newG_length]
      simp

lemma newG_mem {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (K : ℕ) :
    ∀ g ∈ newG gs S Y K, ∃ k < K, keepB gs S Y (N + k) = true ∧ g = mk gs S Y k := by
  induction K with
  | zero => intro g hg; simp [newG] at hg
  | succ K ih =>
    intro g hg
    simp only [newG] at hg
    split_ifs at hg with h
    · rcases List.mem_append.1 hg with h1 | h1
      · obtain ⟨k, hk, h2⟩ := ih g h1
        exact ⟨k, by omega, h2⟩
      · exact ⟨K, by omega, h, by simpa using h1⟩
    · obtain ⟨k, hk, h2⟩ := ih g hg
      exact ⟨k, by omega, h2⟩

lemma Pp_input {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (hd : Disjoint S Y) {j : ℕ}
    (hj : j < N) (hone : oneB gs S j = false) : (Pp gs S Y j).card ≤ 1 := by
  have hjS : (⟨j, hj⟩ : Fin N) ∈ S := by
    have h1 := hone
    unfold oneB at h1
    rw [V_input gs _ hj] at h1
    simpa [xh] using h1
  have hsub : Pp gs S Y j ⊆ {⟨j, hj⟩} := by
    intro s hs
    have h2 := ((mem_Pp gs S Y j s).1 hs).2
    rw [V_input gs _ hj] at h2
    have h3 : (⟨j, hj⟩ : Fin N) ∈ Y ∨ (⟨j, hj⟩ : Fin N) = s := by simpa [pt] using h2
    rcases h3 with h3 | h3
    · exact absurd h3 (Finset.disjoint_left.1 hd hjS)
    · rw [Finset.mem_singleton]; exact h3.symm
  exact le_trans (Finset.card_le_card hsub) (by simp)

lemma Pp_ge {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) {j : ℕ}
    (hj : N + gs.length ≤ j) : (Pp gs S Y j).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro s hs
  have h1 := ((mem_Pp gs S Y j s).1 hs).2
  rw [V_ge gs _ hj] at h1
  exact absurd h1 (by decide)

lemma keep_shape {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (hd : Disjoint S Y) {j : ℕ}
    (h2 : 2 ≤ (Pp gs S Y j).card) (hone : oneB gs S j = false) :
    ∃ k, j = N + k ∧ k < gs.length ∧ keepB gs S Y (N + k) = true := by
  have hj : N ≤ j := by
    by_contra h
    have := Pp_input gs S Y hd (by omega : j < N) hone
    omega
  have hj2 : j < N + gs.length := by
    by_contra h
    have := Pp_ge gs S Y (by omega : N + gs.length ≤ j)
    omega
  refine ⟨j - N, by omega, by omega, ?_⟩
  have e : N + (j - N) = j := by omega
  rw [e, keepB_iff]
  exact ⟨hone, h2⟩

lemma phi_keep {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) {j : ℕ}
    (h2 : 2 ≤ (Pp gs S Y j).card) : phi gs S Y j = N + rk gs S Y (j - N) := by
  unfold phi; rw [ifp h2]

lemma phi_low {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) {j : ℕ}
    (h2 : ¬ 2 ≤ (Pp gs S Y j).card) (hne : (Pp gs S Y j).Nonempty) :
    phi gs S Y j = (hne.choose : ℕ) := by
  unfold phi; rw [ifn h2, dif_pos hne]

lemma phi_none {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) {j : ℕ}
    (h2 : ¬ 2 ≤ (Pp gs S Y j).card) (hne : ¬ (Pp gs S Y j).Nonempty) :
    phi gs S Y j = N + gs.length := by
  unfold phi; rw [ifn h2, dif_neg hne]

lemma star_one {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (x : Fin N → Bool) {j : ℕ}
    (hone : oneB gs S j = true) : star gs S Y x j = true := by
  unfold star; rw [ifp hone]

lemma star_keep {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (x : Fin N → Bool) {j : ℕ}
    (hone : ¬ oneB gs S j = true) (h2 : 2 ≤ (Pp gs S Y j).card) :
    star gs S Y x j = V (newG gs S Y gs.length) x (N + rk gs S Y (j - N)) := by
  unfold star; rw [ifn hone, ifp h2]

lemma star_low {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (x : Fin N → Bool) {j : ℕ}
    (hone : ¬ oneB gs S j = true) (h2 : ¬ 2 ≤ (Pp gs S Y j).card)
    (hne : (Pp gs S Y j).Nonempty) : star gs S Y x j = x hne.choose := by
  unfold star; rw [ifn hone, ifn h2, dif_pos hne]

lemma star_none {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (x : Fin N → Bool) {j : ℕ}
    (hone : ¬ oneB gs S j = true) (h2 : ¬ 2 ≤ (Pp gs S Y j).card)
    (hne : ¬ (Pp gs S Y j).Nonempty) : star gs S Y x j = false := by
  unfold star; rw [ifn hone, ifn h2, dif_neg hne]

lemma read_eq {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (hd : Disjoint S Y)
    (x : Fin N → Bool) {k j : ℕ} (hk : k < gs.length) (hj : j < N + k)
    (hone : oneB gs S j = false) :
    (if phi gs S Y j < N + rk gs S Y k then V (newG gs S Y gs.length) x (phi gs S Y j)
      else false) = star gs S Y x j := by
  have hone' : ¬ oneB gs S j = true := by simp [hone]
  by_cases h2 : 2 ≤ (Pp gs S Y j).card
  · rw [phi_keep gs S Y h2, star_keep gs S Y x hone' h2]
    obtain ⟨k', rfl, hk', hkeep⟩ := keep_shape gs S Y hd h2 hone
    have e : N + k' - N = k' := by omega
    rw [e]
    have hlt := rk_lt gs S Y (show k' < k by omega) hkeep
    rw [ifp (by omega)]
  · by_cases hne : (Pp gs S Y j).Nonempty
    · rw [phi_low gs S Y h2 hne, star_low gs S Y x hone' h2 hne]
      have hc := hne.choose.isLt
      rw [ifp (by omega)]
      exact V_input _ x hc
    · rw [phi_none gs S Y h2 hne, star_none gs S Y x hone' h2 hne]
      have hr := rk_le gs S Y k
      rw [ifn (by omega)]

lemma newgate_eval {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (hd : Disjoint S Y)
    (x : Fin N → Bool) {k : ℕ} (hk : k < gs.length) (hkeep : keepB gs S Y (N + k) = true) :
    V (newG gs S Y gs.length) x (N + rk gs S Y k) =
      (gA gs k).op.eval (((gA gs k).inputs.filter
        (fun j => !(decide (j < N + k) && oneB gs S j))).map
        (fun j => if j < N + k then star gs S Y x j else false)) := by
  have hget := newG_get gs S Y gs.length k hk hkeep
  have hlt : rk gs S Y k < (newG gs S Y gs.length).length := by
    rw [newG_length]; exact rk_lt gs S Y hk hkeep
  have hg : gA (newG gs S Y gs.length) (rk gs S Y k) = mk gs S Y k := by
    rw [gA_eq hlt]
    rw [List.getElem?_eq_getElem hlt] at hget
    exact Option.some.inj hget
  rw [V_gate _ x hlt, hg]
  simp only [mk, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj2 := (List.mem_filter.1 hj).2
  simp only [Function.comp_apply]
  by_cases hlt' : j < N + k
  · simp only [ifp hlt']
    have hone : oneB gs S j = false := by simpa [hlt'] using hj2
    exact read_eq gs S Y hd x hk hlt' hone
  · simp only [ifn hlt']
    have hr := rk_le gs S Y k
    rw [ifn (by omega)]

lemma keep_op {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (t : ℕ)
    (hop : ∀ k < gs.length, (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or ∨
      (gA gs k).op = GateOp.not)
    (hnot : ∀ k < gs.length, (gA gs k).op = GateOp.not → k = t)
    (hY : V gs (fun v => decide (v ∈ Y)) (N + t) = false)
    {k : ℕ} (hk : k < gs.length) (hkeep : keepB gs S Y (N + k) = true) :
    (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or := by
  rcases hop k hk with ho | ho | ho
  · exact Or.inl ho
  · exact Or.inr ho
  · exfalso
    have hkt := hnot k hk ho
    subst hkt
    have hcard : (Pp gs S Y (N + k)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro s hs
      have h1 := ((mem_Pp gs S Y _ s).1 hs).2
      rw [notzero_of gs Y k hk ho hY (fun i _ => mono gs Y k hop hnot hY i) (pt Y s)
        (fun v hv => by simp [pt, hv])] at h1
      exact absurd h1 (by decide)
    have h2 := ((keepB_iff gs S Y _).1 hkeep).2
    omega

lemma upper {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (hd : Disjoint S Y)
    (hao : ∀ k < gs.length, keepB gs S Y (N + k) = true →
      (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or)
    (x : Fin N → Bool) (hx : ∀ s ∈ S, x s = false) :
    ∀ j, star gs S Y x j = true → oneB gs S j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    by_contra hone
    have hone' : oneB gs S j = false := by simpa using hone
    by_cases h2 : 2 ≤ (Pp gs S Y j).card
    · obtain ⟨k, rfl, hk, hkeep⟩ := keep_shape gs S Y hd h2 hone'
      rw [star_keep gs S Y x hone h2] at h
      have e : N + k - N = k := by omega
      rw [e, newgate_eval gs S Y hd x hk hkeep] at h
      have horig : V gs (xh S) (N + k) = false := hone'
      rw [V_gate gs _ hk] at horig
      rcases hao k hk hkeep with ho | ho
      · rw [ho, and_eval] at h
        have hall : GateOp.and.eval ((gA gs k).inputs.map fun i =>
            if i < N + k then V gs (xh S) i else false) = true := by
          rw [and_eval]
          intro i hi
          by_cases hlt : i < N + k
          · rw [ifp hlt]
            by_contra hi1
            have hi1' : oneB gs S i = false := by simpa [oneB] using hi1
            have hmem : i ∈ (gA gs k).inputs.filter
                (fun j => !(decide (j < N + k) && oneB gs S j)) :=
              List.mem_filter.2 ⟨hi, by simp [hi1']⟩
            have h3 := h i hmem
            rw [ifp hlt] at h3
            have h4 := ih i hlt h3
            rw [hi1'] at h4
            exact absurd h4 (by decide)
          · have hmem : i ∈ (gA gs k).inputs.filter
                (fun j => !(decide (j < N + k) && oneB gs S j)) :=
              List.mem_filter.2 ⟨hi, by simp [hlt]⟩
            have h3 := h i hmem
            rw [ifn hlt] at h3
            exact absurd h3 (by decide)
        rw [ho, hall] at horig
        exact absurd horig (by decide)
      · rw [ho, or_eval] at h
        obtain ⟨i, hi, h3⟩ := h
        by_cases hlt : i < N + k
        · rw [ifp hlt] at h3
          have h4 : V gs (xh S) i = true := ih i hlt h3
          have hany : GateOp.or.eval ((gA gs k).inputs.map fun i =>
              if i < N + k then V gs (xh S) i else false) = true := by
            rw [or_eval]
            exact ⟨i, (List.mem_filter.1 hi).1, by rw [ifp hlt]; exact h4⟩
          rw [ho, hany] at horig
          exact absurd horig (by decide)
        · rw [ifn hlt] at h3; exact absurd h3 (by decide)
    · by_cases hne : (Pp gs S Y j).Nonempty
      · rw [star_low gs S Y x hone h2 hne] at h
        have h5 := hx _ ((mem_Pp gs S Y j _).1 hne.choose_spec).1
        rw [h5] at h
        exact absurd h (by decide)
      · rw [star_none gs S Y x hone h2 hne] at h
        exact absurd h (by decide)

lemma lower {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (hd : Disjoint S Y)
    (hao : ∀ k < gs.length, keepB gs S Y (N + k) = true →
      (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or)
    (x : Fin N → Bool) (s : Fin N) (hs : s ∈ S) (hxs : x s = true) :
    ∀ j, V gs (pt Y s) j = true → star gs S Y x j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    by_cases hone : oneB gs S j = true
    · exact star_one gs S Y x hone
    · have hone' : oneB gs S j = false := by simpa using hone
      have hsP : s ∈ Pp gs S Y j := (mem_Pp gs S Y j s).2 ⟨hs, h⟩
      by_cases h2 : 2 ≤ (Pp gs S Y j).card
      · obtain ⟨k, rfl, hk, hkeep⟩ := keep_shape gs S Y hd h2 hone'
        rw [star_keep gs S Y x hone h2]
        have e : N + k - N = k := by omega
        rw [e, newgate_eval gs S Y hd x hk hkeep]
        have horig : V gs (xh S) (N + k) = false := hone'
        rw [V_gate gs _ hk] at horig
        rw [V_gate gs _ hk] at h
        rcases hao k hk hkeep with ho | ho
        · rw [ho, and_eval] at h
          rw [ho, and_eval]
          intro i hi
          have h3 := h i (List.mem_filter.1 hi).1
          by_cases hlt : i < N + k
          · rw [ifp hlt] at h3 ⊢; exact ih i hlt h3
          · rw [ifn hlt] at h3; exact absurd h3 (by decide)
        · rw [ho, or_eval] at h
          rw [ho, or_eval]
          obtain ⟨i, hi, h3⟩ := h
          by_cases hlt : i < N + k
          · rw [ifp hlt] at h3
            have hi1 : oneB gs S i = false := by
              by_contra hc
              have hc' : V gs (xh S) i = true := by simpa [oneB] using hc
              have hany : GateOp.or.eval ((gA gs k).inputs.map fun i =>
                  if i < N + k then V gs (xh S) i else false) = true := by
                rw [or_eval]
                exact ⟨i, hi, by rw [ifp hlt]; exact hc'⟩
              rw [ho, hany] at horig
              exact absurd horig (by decide)
            exact ⟨i, List.mem_filter.2 ⟨hi, by simp [hi1]⟩,
              by rw [ifp hlt]; exact ih i hlt h3⟩
          · rw [ifn hlt] at h3; exact absurd h3 (by decide)
      · have hne : (Pp gs S Y j).Nonempty := ⟨s, hsP⟩
        rw [star_low gs S Y x hone h2 hne]
        have hch : hne.choose = s :=
          Finset.card_le_one.1 (by omega) _ hne.choose_spec _ hsP
        rw [hch]; exact hxs

lemma rk_le_card {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N))
    (F : Finset (Fin gs.length))
    (h : ∀ i : Fin gs.length, keepB gs S Y (N + i) = true → i ∈ F) :
    rk gs S Y gs.length ≤ F.card := by
  have hsub : (Finset.range gs.length).filter (fun i => keepB gs S Y (N + i) = true) ⊆
      F.map Fin.valEmbedding := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
    rw [Finset.mem_range] at hi1
    exact Finset.mem_map.2 ⟨⟨i, hi1⟩, h ⟨i, hi1⟩ hi2, rfl⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_map] at h1
  exact h1

lemma core {N : ℕ} (gs : List Gate) (S Y : Finset (Fin N)) (hd : Disjoint S Y) (t o : ℕ)
    (hop : ∀ k < gs.length, (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or ∨
      (gA gs k).op = GateOp.not)
    (hlen : ∀ k < gs.length, (gA gs k).inputs.length ≤ 2)
    (hnot : ∀ k < gs.length, (gA gs k).op = GateOp.not → k = t)
    (hY : V gs (fun v => decide (v ∈ Y)) (N + t) = false)
    (hval : ∀ z : Fin N → Bool, V gs z o = decide (∃ s ∈ S, z s = true))
    (hS : 2 ≤ S.card) :
    ∃ (G : List Gate) (o' : ℕ),
      (∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin N → Bool, V G x o' = decide (∃ v ∈ S, x v = true)) ∧
      G.length = rk gs S Y gs.length := by
  have hao : ∀ k < gs.length, keepB gs S Y (N + k) = true →
      (gA gs k).op = GateOp.and ∨ (gA gs k).op = GateOp.or :=
    fun k hk hkeep => keep_op gs S Y t hop hnot hY hk hkeep
  have hone : oneB gs S o = false := by
    unfold oneB
    rw [hval]
    simp [xh]
  have hpt : ∀ s ∈ S, V gs (pt Y s) o = true := by
    intro s hs
    rw [hval]
    exact decide_eq_true ⟨s, hs, by simp [pt]⟩
  have hP : Pp gs S Y o = S := by
    unfold Pp
    exact Finset.filter_true_of_mem hpt
  have h2 : 2 ≤ (Pp gs S Y o).card := by rw [hP]; exact hS
  have hone' : ¬ oneB gs S o = true := by simp [hone]
  obtain ⟨k, rfl, hk, hkeep⟩ := keep_shape gs S Y hd h2 hone
  refine ⟨newG gs S Y gs.length, N + rk gs S Y k, ?_, ?_, newG_length gs S Y gs.length⟩
  · intro g hg
    obtain ⟨k', hk', hkeep', rfl⟩ := newG_mem gs S Y gs.length g hg
    refine ⟨hao k' hk' hkeep', ?_⟩
    show (List.map _ (List.filter _ _)).length ≤ 2
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) (hlen k' hk')
  · intro x
    have hst : star gs S Y x (N + k) = V (newG gs S Y gs.length) x (N + rk gs S Y k) := by
      rw [star_keep gs S Y x hone' h2]
      have e : N + k - N = k := by omega
      rw [e]
    rw [← hst]
    by_cases hex : ∃ v ∈ S, x v = true
    · obtain ⟨s, hs, hxs⟩ := hex
      rw [lower gs S Y hd hao x s hs hxs (N + k) (hpt s hs)]
      exact (decide_eq_true ⟨s, hs, hxs⟩).symm
    · have hx : ∀ s ∈ S, x s = false := by
        intro s hs
        by_contra hc
        exact hex ⟨s, hs, by simpa using hc⟩
      have hf : star gs S Y x (N + k) = false := by
        by_contra hc
        have h3 := upper gs S Y hd hao x hx (N + k) (by simpa using hc)
        exact hone' h3
      rw [hf]
      exact (decide_eq_false hex).symm

end PEqualNP.Outside.L_meta_1595

open PEqualNP.Outside.L_meta_1595 in
theorem PEqualNP.Outside.L_meta_1595 : (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (N M : ℕ) (A : Fin M → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : Fin M → ℕ) (t : ℕ) (Y : Finset (Fin N)), (∀ ab1 ab2 : Fin M, ab1 ≠ ab2 → (A ab1 ∩ A ab2).card ≤ 1) → (∀ eb1 ∈ D.gates, (eb1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ eb1.inputs.length ≤ 2) → (∀ lb1 : Fin D.gates.length, (D.gates.get lb1).op = PEqualNP.CircuitLowerBounds.GateOp.not → (lb1 : ℕ) = t) → (∀ (ab3 : Fin M) (zb1 : Fin N → Bool), (D.wires (List.ofFn zb1)).getD (u ab3) false = decide (∃ sb1 ∈ A ab3, zb1 sb1 = true)) → (∀ zb2 : Fin N → Bool, (Finset.univ.filter (fun vb1 : Fin N => zb2 vb1 = true)).card < Y.card → (D.wires (List.ofFn zb2)).getD (N + t) false = true) → (D.wires (List.ofFn (fun vb2 : Fin N => decide (vb2 ∈ Y)))).getD (N + t) false = false → ∀ b4 : Fin M, Disjoint (A b4) Y → (A b4).card ≤ (Finset.univ.filter (fun h1 : Fin D.gates.length => (∀ s2 : Fin N, s2 ∉ Y → (D.wires (List.ofFn (fun w1 : Fin N => decide (w1 ∈ Y ∨ w1 = s2)))).getD (N + h1) false = true → s2 ∈ A b4) ∧ 2 ≤ (Finset.univ.filter (fun s3 : Fin N => s3 ∉ Y ∧ (D.wires (List.ofFn (fun w2 : Fin N => decide (w2 ∈ Y ∨ w2 = s3)))).getD (N + h1) false = true)).card)).card + 1 := by
  intro _ H2 N M A D u t Y _ hD hnot hu _ hY b4 hdisj
  have hop : ∀ k < D.gates.length, (gA D.gates k).op = GateOp.and ∨
      (gA D.gates k).op = GateOp.or ∨ (gA D.gates k).op = GateOp.not :=
    fun k hk => (hD _ (gA_mem hk)).1
  have hlen : ∀ k < D.gates.length, (gA D.gates k).inputs.length ≤ 2 :=
    fun k hk => (hD _ (gA_mem hk)).2
  have hnot' : ∀ k < D.gates.length, (gA D.gates k).op = GateOp.not → k = t := by
    intro k hk ho
    rw [gA_eq hk] at ho
    exact hnot ⟨k, hk⟩ ho
  have hY' : V D.gates (fun v => decide (v ∈ Y)) (N + t) = false := hY
  have hM := mono D.gates Y t hop hnot' hY'
  by_cases hS : (A b4).card ≤ 1
  · omega
  have hval : ∀ z : Fin N → Bool, V D.gates z (u b4) = decide (∃ s ∈ A b4, z s = true) :=
    fun z => hu b4 z
  obtain ⟨G, o', hG, hfun, hGlen⟩ := core D.gates (A b4) Y hdisj t (u b4) hop hlen hnot' hY'
    hval (by omega)
  have hH := H2 N 1 (fun _ => A b4) (fun i j hij => absurd (Subsingleton.elim i j) hij)
    G (fun _ => o') hG (fun _ x => hfun x)
  simp only [Finset.univ_unique, Finset.sum_singleton] at hH
  rw [hGlen] at hH
  refine le_trans (by omega : (A b4).card ≤ rk D.gates (A b4) Y D.gates.length + 1)
    (Nat.add_le_add_right (rk_le_card D.gates (A b4) Y _
      (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩)) 1)
  · intro s2 _ hv
    by_contra hns
    have h1 : oneB D.gates (A b4) (N + i) = true :=
      hM (N + i) (pt Y s2) (xh (A b4)) (fun v hv' => by simp [pt, hv'])
        (fun v hv' => by
          have h3 : v ∈ Y ∨ v = s2 := by simpa [pt] using hv'
          refine decide_eq_true ?_
          rcases h3 with h3 | h3
          · exact fun hc => Finset.disjoint_left.1 hdisj hc h3
          · rw [h3]; exact hns) hv
    rw [((keepB_iff D.gates (A b4) Y _).1 hi).1] at h1
    exact absurd h1 (by decide)
  · refine le_trans ((keepB_iff D.gates (A b4) Y _).1 hi).2 (Finset.card_le_card ?_)
    intro s hs
    obtain ⟨hsS, hv⟩ := (mem_Pp D.gates (A b4) Y _ s).1 hs
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      fun hc => Finset.disjoint_left.1 hdisj hsS hc, hv⟩
