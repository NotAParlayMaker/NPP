import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Choose
import PEqualNP.Defs

-- The clean-circuit ledger below is adapted from the project's L_meta_1602 by Robert Cass in PR 3328.
namespace PEqualNP.Outside.L_meta_4767.Ledger

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

def gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

def firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 0 (w-1))

def secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w-1)))

def andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  match (gateAtPos n gs w).op with
  | GateOp.and => true
  | _ => false

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
  unfold clampWire
  split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
    (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]
  split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i+1) x = x ⟨i,hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

lemma edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ¬ edgeTrue G (singletonBits u) := by
  rintro ⟨i,j,h,hi,hj⟩
  simp only [singletonBits, decide_eq_true_eq] at hi hj
  subst i
  subst j
  exact G.loopless.irrefl u h

lemma edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    edgeTrue G (pairBits u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    simp only [pairBits, decide_eq_true_eq] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (G.loopless.irrefl _ h).elim
    · exact h
    · exact h.symm
    · exact (G.loopless.irrefl _ h).elim
  · intro h
    exact ⟨u,v,h,by simp [pairBits],by simp [pairBits]⟩

lemma binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
    (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
    op.eval (l.map v) =
      (if (match op with | GateOp.and => true | _ => false) then
        v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
       else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact (nonempty rfl rfl).elim
    · simp [GateOp.eval,vd]
  | cons i t =>
    cases t with
    | nil => rcases hop with rfl | rfl <;> simp [GateOp.eval]
    | cons j t =>
      have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst t
      rcases hop with rfl | rfl <;> simp [GateOp.eval]

def supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => posRead gs w (singletonBits u) = true

lemma mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (u : Fin n) :
    u ∈ supports gs w ↔ posRead gs w (singletonBits u) = true := by simp [supports]


def cleanOn {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ (j : Fin gs.length) (x : Fin n → Bool),
    (x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) →
    (gs.get j).op = GateOp.and →
    (wiresFrom gs (List.ofFn x)).getD (n + j.val) false = true → edgeTrue G x

def binaryOps (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n+j+1) = gs[j] := by
  unfold gateAtPos
  rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs)
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
    intro ha hempty
    let z : Fin n → Bool := fun _ => false
    have eqg := getD_wiresFrom_gate gs (List.ofFn z) j hj
    simp only [List.length_ofFn, hempty, List.map_nil, ha, GateOp.eval, List.all_nil] at eqg
    obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z (Or.inl rfl) ha eqg
    contradiction
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

lemma pos_clean {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) (x : Fin n → Bool)
    (hx : x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) :
    posRead gs w x = true → edgeTrue G x := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  rw [hw] at ha ⊢
  simp only [andPos, gateAt_index gs j hj] at ha
  have hop : gs[j].op = GateOp.and := by
    cases h : gs[j].op <;> simp_all
  exact clean ⟨j,hj⟩ x hx hop

lemma support_base {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n+1) :
    (supports (n:=n) gs w).card ≤ 1 := by
  cases w with
  | zero => simp [supports,posRead]
  | succ i =>
    have hi : i < n := by omega
    have hs : supports gs (i+1) = {⟨i,hi⟩} := by
      ext u
      simp [mem_support,pos_input gs i hi,singletonBits,eq_comm]
    simp [hs]

lemma hit_base {n : ℕ} (gs : List Gate) (w : ℕ) (u v : Fin n) (hw : w < n+1) :
    posRead gs w (pairBits u v) = true → u ∈ supports gs w ∨ v ∈ supports gs w := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    have hi : i<n := by omega
    simp [mem_support,pos_input gs i hi,pairBits,singletonBits]

lemma support_and {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) : supports (n:=n) gs w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact edge_single G u (pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inl ⟨u, rfl⟩)) ((mem_support gs w u).mp hu))

lemma support_or {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
    supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
  ext u
  simp only [Finset.mem_union,mem_support,pos_gate G gs ops clean w lo hi,ha]
  simp

lemma cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
    (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
    (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
  apply (edge_pair G u v).mp
  apply pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inr ⟨u, v, rfl⟩))
  rw [pos_gate G gs ops clean w lo hi,ha]
  simp only [ite_true, Bool.and_eq_true]
  have hm := pos_mono (n:=n) gs (fun g h => (ops g h).1)
  constructor
  · apply hm (firstWire n gs w) (singletonBits u) (pairBits u v) _ ((mem_support _ _ _).mp hu)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]
  · apply hm (secondWire n gs w) (singletonBits v) (pairBits u v) _ ((mem_support _ _ _).mp hv)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]


lemma root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [pos_clamp]
  change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
  split_ifs with h
  · rfl
  · symm
    apply List.getD_eq_default
    simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

lemma root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
  unfold clampWire
  split <;> omega

lemma root_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    supports (n:=n) gs (clampWire (n+gs.length) out) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u h
  apply edge_single G u
  apply (heval _).mp
  rw [← root_read]
  exact (mem_support _ _ _).mp h

lemma root_hits {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    ∀ u v, G.Adj u v → posRead gs (clampWire (n+gs.length) out) (pairBits u v) = true := by
  intro u v h
  rw [root_read,heval]
  exact (edge_pair G u v).mpr h

theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

theorem gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2
      simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2
      exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

theorem cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
      (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
      (R.biUnion f).card ≤ R.card + B.card) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]
            tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]
            tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨
        (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
      simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using hdag f {r} B hstep

theorem edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

theorem edge_finset_gate_bound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
        have hw : w ∈ AS := by simp [AS,hN,hk,hA]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]

theorem total_from_model (n k N r L : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hr : r < N) (hrS : S r = ∅) (hrH : ∀ u v, G.Adj u v → H r u v)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hpartition :
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card ≤ L) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ L + 1 := by
  classical
  have hd (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) : Disjoint (S (a w)) (S (b w)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact G.loopless.irrefl t (hjoin w hk hN hA t ht t ht')
  have hside (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
    by_contra! hf
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hf.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hf.2
    have hJ := hjoin w hk hN hA
    exact hc4 u x v y huv hxy ⟨hJ u hu x hx, (hJ v hv x hx).symm, hJ v hv y hy, (hJ u hu y hy).symm⟩
  have births (u v) (huv : G.Adj u v) := edge_birth n k N r S H a b A u v hr
    (hrH u v huv) (by simp [hrS]) (by simp [hrS]) hinput ha hb horS horH handH hd
  have edgeCount := edge_finset_gate_bound n k N G S a b A hc4 hsmall
    (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) hzero horS hjoin hside births
  obtain ⟨T,hT,hcard⟩ := cover_half n k N r G S H a b A hr hrS hrH hinput ha hb
    horS horH hside handH (fun f R B step => dag_union_bound f R B step)
  exact ⟨T,hT,by omega⟩

theorem pairCleanBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (x = (fun _ => false) ∨ (∃ u : Fin n, x = fun z => decide (z = u)) ∨ (∃ u v : Fin n, x = fun z => decide (z = u ∨ z = v))) → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G inst hc4 gs out ops eval clean
  have he : ∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x := by
    intro x
    rw [eval]
    exact decide_eq_true_iff
  apply total_from_model n (n+1) (n+1+gs.length) (clampWire (n+gs.length) out) gs.length G
    (supports gs) (fun w u v => posRead gs w (pairBits u v) = true)
    (firstWire n gs) (secondWire n gs) (andPos n gs) hc4 (root_bound n gs.length out)
    (root_support_empty G gs out he) (root_hits G gs out he) (support_base gs) (hit_base gs)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · exact support_or G gs ops clean
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,Bool.false_eq_true,ite_false,Bool.or_eq_true]
      using h
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,ite_true,Bool.and_eq_true] using h
  · exact support_and G gs clean
  · exact cross_support G gs ops clean
  · exact gate_partition_count n gs.length (andPos n gs) (supports gs)

end PEqualNP.Outside.L_meta_4767.Ledger


namespace PEqualNP.Outside.L_meta_4767

open PEqualNP.CircuitLowerBounds

lemma andGate_on_extension {n : ℕ} (x : Fin n → Bool) (a b : Fin n)
    (tail : List Bool) :
    (⟨GateOp.and, [a.val, b.val]⟩ : Gate).op.eval
        ((⟨GateOp.and, [a.val, b.val]⟩ : Gate).inputs.map
          fun i => (List.ofFn x ++ tail).getD i false) = true ↔
      x a = true ∧ x b = true := by
  have ha : (List.ofFn x ++ tail).getD a.val false = x a := by
    rw [List.getD_append _ _ _ _ (by simp)]
    simp
  have hb : (List.ofFn x ++ tail).getD b.val false = x b := by
    rw [List.getD_append _ _ _ _ (by simp)]
    simp
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
  rw [ha, hb]
  simp

lemma andGate_on_primaryEdge {n : ℕ} (a b c d : Fin n)
    (hab : a ≠ b) (hcd : c ≠ d) :
    (⟨GateOp.and, [a.val, b.val]⟩ : Gate).op.eval
        ((⟨GateOp.and, [a.val, b.val]⟩ : Gate).inputs.map fun i =>
          (List.ofFn (fun k : Fin n => decide (k = c ∨ k = d))).getD i false) = true ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h :
      (⟨GateOp.and, [a.val, b.val]⟩ : Gate).op.eval
        ((⟨GateOp.and, [a.val, b.val]⟩ : Gate).inputs.map fun i =>
          (List.ofFn (fun k : Fin n => decide (k = c ∨ k = d))).getD i false) = true ↔
        (a = c ∨ a = d) ∧ (b = c ∨ b = d) := by
    simpa using andGate_on_extension
      (x := fun k : Fin n => decide (k = c ∨ k = d)) a b []
  constructor
  · intro hval
    rcases h.mp hval with ⟨hac | had, hbc | hbd⟩
    · exact False.elim (hab (hac.trans hbc.symm))
    · exact Or.inl ⟨hac, hbd⟩
    · exact Or.inr ⟨had, hbc⟩
    · exact False.elim (hab (had.trans hbd.symm))
  · intro hedge
    apply h.mpr
    rcases hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩

lemma emptyOrEval : GateOp.eval GateOp.or ([] : List Bool) = false := rfl

lemma andGate_on_primaryAdj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d) :
    (⟨GateOp.and, [a.val, b.val]⟩ : Gate).op.eval
        ((⟨GateOp.and, [a.val, b.val]⟩ : Gate).inputs.map fun i =>
          (List.ofFn (fun k : Fin n => decide (k = c ∨ k = d))).getD i false) = true ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  exact andGate_on_primaryEdge a b c d (G.ne_of_adj hab) (G.ne_of_adj hcd)

end PEqualNP.Outside.L_meta_4767

namespace PEqualNP.Outside.L_meta_4767

theorem chooseGateData {n m : Nat} (G : SimpleGraph (Fin n))
    (val : Nat → (Fin n → Bool) → Bool) (isAnd : Fin m → Prop)
    (casesOf : ∀ i : Fin m, isAnd i →
      (∀ x, val i x = true → ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∨
      (∀ a b c d, G.Adj a b → G.Adj c d →
        val i (fun k => decide (k = a ∨ k = b)) = true →
        val i (fun k => decide (k = c ∨ k = d)) = true →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    ∃ (safe : Nat → Bool) (pick : Nat → Option (Fin n × Fin n)),
      (∀ i : Fin m, isAnd i → safe i = true →
        ∀ x, val i x = true → ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∧
      (∀ i : Fin m, isAnd i → safe i = false →
        (∀ u v, G.Adj u v → (val i (fun k => decide (k = u ∨ k = v)) = true ↔
          pick i = some (u,v) ∨ pick i = some (v,u))) ∧
        (∀ a b, pick i = some (a,b) → G.Adj a b ∧
          val i (fun k => decide (k = a ∨ k = b)) = true)) := by
  classical
  let clean (i : Nat) := ∀ x, val i x = true → ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  let accepts (i : Nat) (p : Fin n × Fin n) :=
    G.Adj p.1 p.2 ∧ val i (fun k => decide (k = p.1 ∨ k = p.2)) = true
  let pick (i : Nat) : Option (Fin n × Fin n) :=
    if h : ∃ p, accepts i p then some (Classical.choose h) else none
  have sound (i a b) (sel : pick i = some (a,b)) : accepts i (a,b) := by
    unfold pick at sel
    split at sel
    next h =>
      have hp := Option.some.inj sel
      exact hp ▸ Classical.choose_spec h
    next => contradiction
  refine ⟨fun i => decide (clean i), pick, fun i _ h => of_decide_eq_true h, ?_⟩
  intro i hi hfalse
  have hu := (casesOf i hi).resolve_left (of_decide_eq_false hfalse)
  refine ⟨?_, fun a b sel => sound i a b sel⟩
  intro u v edge
  constructor
  · intro hv
    have h : ∃ p, accepts i p := ⟨(u,v),edge,hv⟩
    let p := Classical.choose h
    have hr : accepts i p := Classical.choose_spec h
    have sel : pick i = some p := dif_pos h
    rcases hu p.1 p.2 u v hr.1 edge hr.2 hv with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl (sel.trans (congrArg some (Prod.ext ha hb)))
    · exact Or.inr (sel.trans (congrArg some (Prod.ext ha hb)))
  · rintro (h | h)
    · exact (sound i u v h).2
    · simpa only [or_comm] using (sound i v u h).2

end PEqualNP.Outside.L_meta_4767

namespace PEqualNP.Outside.L_meta_4767

theorem recoverEdgeFunction {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f g : (Fin n → Bool) → Bool)
    (hf : ∀ x, f x = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    (dom : ∀ x, g x = true → f x = true)
    (agrees : ∀ u v, G.Adj u v →
      g (fun i => decide (i = u ∨ i = v)) = f (fun i => decide (i = u ∨ i = v)))
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true) :
    ∀ x, g x = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rw [← hf]
    exact dom x hx
  · intro hx
    obtain ⟨u,v,edge,hu,hv⟩ := of_decide_eq_true hx
    let base := fun i : Fin n => decide (i = u ∨ i = v)
    have hu' : base u = true := by simp [base]
    have hv' : base v = true := by simp [base]
    have hbase : g base = true := by
      rw [show g base = f base from agrees u v edge, hf, decide_eq_true_iff]
      exact ⟨u,v,edge,hu',hv'⟩
    exact mono base x (fun i hi => (of_decide_eq_true hi).elim
      (fun e => e ▸ hu) (fun e => e ▸ hv)) hbase

end PEqualNP.Outside.L_meta_4767

namespace PEqualNP.Outside.L_meta_4767

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Ledger

def replaceGate {n : ℕ} (safe : ℕ → Bool) (pick : ℕ → Option (Fin n × Fin n))
    (i : ℕ) (g : Gate) : Gate :=
  letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  if g.op = GateOp.and then
    if safe i then g else
      match pick i with
      | some (u, v) => ⟨GateOp.and, [u.val, v.val]⟩
      | none => ⟨GateOp.or, []⟩
  else g

def normalizeGates {n : ℕ} (gs : List Gate) (safe : ℕ → Bool)
    (pick : ℕ → Option (Fin n × Fin n)) : List Gate :=
  gs.mapIdx (fun i g => replaceGate safe pick i g)

def origWireVal {n : ℕ} (gs : List Gate) (i : Fin gs.length)
    (x : Fin n → Bool) : Bool :=
  ((Circuit.mk gs 0).wires (List.ofFn x)).getD (n + i.val) false

lemma normalizeGates_length {n : ℕ} (gs : List Gate) (safe : ℕ → Bool)
    (pick : ℕ → Option (Fin n × Fin n)) :
    (normalizeGates gs safe pick).length = gs.length := by
  simp [normalizeGates]

lemma normalizeGates_get {n : ℕ} (gs : List Gate) (safe : ℕ → Bool)
    (pick : ℕ → Option (Fin n × Fin n)) (i : ℕ) (hi : i < gs.length) :
    (normalizeGates gs safe pick)[i]'(by simpa [normalizeGates] using hi) =
      replaceGate safe pick i (gs[i]'hi) := by
  simp [normalizeGates, List.getElem?_mapIdx, hi]

lemma normalizeGates_binaryOps {n : ℕ} (gs : List Gate) (safe : ℕ → Bool)
    (pick : ℕ → Option (Fin n × Fin n)) (hops : binaryOps gs) :
    binaryOps (normalizeGates gs safe pick) := by
  letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro g hg
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hg
  subst g
  have hi' : i < gs.length := by simpa [normalizeGates_length] using hi
  have hnorm := normalizeGates_get gs safe pick i hi'
  rw [hnorm]
  have hbase := hops (gs[i]'hi') (List.getElem_mem hi')
  by_cases hop : (gs[i]'hi').op = GateOp.and
  · simp only [replaceGate, hop, if_pos]
    cases hs : safe i with
    | false =>
      cases he : pick i with
      | none => simp
      | some e => cases e with | mk u v => simp
    | true => simpa [hs] using hbase
  · have hor : (gs[i]'hi').op = GateOp.or := by
      rcases hbase.1 with ha | ho
      · exact (hop ha).elim
      · exact ho
    simpa [replaceGate, hop] using hbase

def WireLe (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

lemma mapWireLe {inputs : List ℕ} {a b : List Bool} (h : WireLe a b) :
    WireLe (inputs.map fun i => a.getD i false) (inputs.map fun i => b.getD i false) := by
  intro i hi
  by_cases hi' : i < inputs.length
  · have hiA : i < (inputs.map fun j => a.getD j false).length := by simp [hi']
    have hiB : i < (inputs.map fun j => b.getD j false).length := by simp [hi']
    rw [List.getD_eq_getElem _ _ hiA] at hi
    rw [List.getD_eq_getElem _ _ hiB]
    simp only [List.getElem_map] at hi ⊢
    exact h _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact Bool.noConfusion hi

lemma wiresFrom_gateEval_eq {n : ℕ} (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (x : Fin n → Bool) :
    (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
      (wiresFrom (gs.take k) (List.ofFn x)).getD i false) =
      (wiresFrom gs (List.ofFn x)).getD (n + k) false := by
  have hsplit : gs.take (k + 1) = gs.take k ++ [gs[k]'hk] :=
    List.take_succ_eq_append_getElem hk
  have hcut := getD_wiresFrom_take gs (List.ofFn x) (k + 1) (n + k) (by omega)
  simp only [List.length_ofFn] at hcut
  rw [if_pos (by omega)] at hcut
  have hrun : wiresFrom (gs.take (k + 1)) (List.ofFn x) =
      wiresFrom (gs.take k) (List.ofFn x) ++
        [(gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
          (wiresFrom (gs.take k) (List.ofFn x)).getD i false)] := by
    rw [hsplit, wiresFrom_append]
    rfl
  have hlen : (wiresFrom (gs.take k) (List.ofFn x)).length = n + k := by
    simp [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [hrun, ← hlen, getD_snoc_eq, hlen] at hcut
  exact hcut

lemma wiresFrom_gateValue_eq {n : ℕ} (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (x : Fin n → Bool) :
    ((Circuit.mk gs 0).wires (List.ofFn x)).getD (n + k) false =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
        (wiresFrom (gs.take k) (List.ofFn x)).getD i false) := by
  simpa [Circuit.wires, wiresFrom] using
    (wiresFrom_gateEval_eq (n:=n) gs k hk x).symm

lemma normalize_gateStep_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (safe : ℕ → Bool) (pick : ℕ → Option (Fin n × Fin n))
    (hops : binaryOps gs)
    (hPick : ∀ i : Fin gs.length, (gs.get i).op = GateOp.and → safe i.val = false →
      (∀ a b : Fin n, G.Adj a b →
        (origWireVal gs i (pairBits a b) = true ↔
          pick i.val = some (a, b) ∨ pick i.val = some (b, a))) ∧
      (∀ a b : Fin n, pick i.val = some (a, b) →
        G.Adj a b ∧ origWireVal gs i (pairBits a b) = true))
    (k : ℕ) (hk : k < gs.length) (x : Fin n → Bool)
    (newW : List Bool)
    (hprev : WireLe newW (wiresFrom (gs.take k) (List.ofFn x)))
    (hraw : ∀ p : Fin n, newW.getD p.val false = x p) :
    (replaceGate safe pick k (gs[k]'hk)).op.eval
        ((replaceGate safe pick k (gs[k]'hk)).inputs.map fun i => newW.getD i false) = true →
    (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
      (wiresFrom (gs.take k) (List.ofFn x)).getD i false) = true := by
  intro hnewVal
  let g := gs[k]'hk
  have hopsK := hops g (List.getElem_mem hk)
  by_cases hAnd : g.op = GateOp.and
  · by_cases hSafe : safe k = true
    · have hsame : replaceGate safe pick k g = g := by
        simp [replaceGate, hAnd, hSafe]
      have hnew' : g.op.eval (g.inputs.map fun i => newW.getD i false) = true := by
        simpa [g, hsame] using hnewVal
      have hmap : WireLe (g.inputs.map fun i => newW.getD i false)
          (g.inputs.map fun i => (wiresFrom (gs.take k) (List.ofFn x)).getD i false) :=
        mapWireLe (inputs:=g.inputs) hprev
      have hlen : (g.inputs.map fun i => newW.getD i false).length =
          (g.inputs.map fun i => (wiresFrom (gs.take k) (List.ofFn x)).getD i false).length := by simp
      exact gateOp_eval_mono g.op hopsK.1 _ _ hlen hmap hnew'
    · have hUnsafe : safe k = false := by cases hs : safe k <;> simp_all
      cases hChosen : pick k with
      | none =>
        have hfalse : False := by
          simpa [replaceGate, g, hAnd, hUnsafe, hChosen, GateOp.eval] using hnewVal
        exact hfalse.elim
      | some e =>
        rcases e with ⟨u, v⟩
        have hp := (hPick ⟨k, hk⟩ hAnd hUnsafe).2 u v (by simp [hChosen])
        have hpairNew : newW.getD u.val false = true ∧ newW.getD v.val false = true := by
          simpa [replaceGate, g, hAnd, hUnsafe, hChosen, GateOp.eval] using hnewVal
        have huWire := hpairNew.1
        have hvWire := hpairNew.2
        change newW.getD u.val false = true at huWire
        change newW.getD v.val false = true at hvWire
        have hu : x u = true := by
          rw [hraw u] at huWire
          exact huWire
        have hv : x v = true := by
          rw [hraw v] at hvWire
          exact hvWire
        have hsub : ∀ z : Fin n, (pairBits u v) z = true → x z = true := by
          intro z hz
          simp only [pairBits, decide_eq_true_eq] at hz
          rcases hz with rfl | rfl
          · exact hu
          · exact hv
        have hpair : (wiresFrom gs (List.ofFn (pairBits u v))).getD (n + k) false = true := by
          have hpval := hp.2
          change (wiresFrom gs (List.ofFn (pairBits u v))).getD (n + k) false = true at hpval
          exact hpval
        have hfull := wiresFrom_mono gs (fun g' hg' => (hops g' hg').1)
          (List.ofFn (pairBits u v)) (List.ofFn x) (by simp) (by
            intro z hz
            by_cases hz' : z < n
            · rw [List.getD_eq_getElem _ _ (by simpa using hz')] at hz ⊢
              simp only [List.getElem_ofFn] at hz ⊢
              exact hsub ⟨z, hz'⟩ hz
            · rw [List.getD_eq_default _ _ (by simp; omega)] at hz
              exact Bool.noConfusion hz) (n + k) hpair
        rw [← wiresFrom_gateEval_eq (n:=n) gs k hk x] at hfull
        exact hfull
  · have hsame : replaceGate safe pick k g = g := by
      simp [replaceGate, hAnd]
    have hnew' : g.op.eval (g.inputs.map fun i => newW.getD i false) = true := by
      simpa [g, hsame] using hnewVal
    have hmap : WireLe (g.inputs.map fun i => newW.getD i false)
        (g.inputs.map fun i => (wiresFrom (gs.take k) (List.ofFn x)).getD i false) :=
      mapWireLe (inputs:=g.inputs) hprev
    have hlen : (g.inputs.map fun i => newW.getD i false).length =
        (g.inputs.map fun i => (wiresFrom (gs.take k) (List.ofFn x)).getD i false).length := by simp
    exact gateOp_eval_mono g.op hopsK.1 _ _ hlen hmap hnew'

lemma wireLe_snoc {a b : List Bool} {x y : Bool}
    (hlen : a.length = b.length) (hab : WireLe a b)
    (hxy : x = true → y = true) :
    WireLe (a ++ [x]) (b ++ [y]) := by
  intro i hi
  by_cases hlt : i < a.length
  · have hltb : i < b.length := by omega
    rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ hltb]
    exact hab i hi
  · by_cases heq : i = a.length
    · subst i
      have hia : (a ++ [x]).getD a.length false = x := Ledger.getD_snoc_eq a x
      have hib : (b ++ [y]).getD a.length false = y := by
        rw [hlen]
        exact Ledger.getD_snoc_eq b y
      rw [hia] at hi
      rw [hib]
      exact hxy hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact Bool.noConfusion hi

lemma wiresFrom_singleton (g : Gate) (w : List Bool) :
    Ledger.wiresFrom [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  rfl

theorem normalize_prefix_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (safe : ℕ → Bool) (pick : ℕ → Option (Fin n × Fin n))
    (hops : binaryOps gs)
    (hPick : ∀ i : Fin gs.length, (gs.get i).op = GateOp.and → safe i.val = false →
      (∀ a b : Fin n, G.Adj a b →
        (origWireVal gs i (pairBits a b) = true ↔
          pick i.val = some (a, b) ∨ pick i.val = some (b, a))) ∧
      (∀ a b : Fin n, pick i.val = some (a, b) →
        G.Adj a b ∧ origWireVal gs i (pairBits a b) = true)) :
    ∀ k, k ≤ gs.length → ∀ x : Fin n → Bool,
      WireLe (Ledger.wiresFrom ((normalizeGates gs safe pick).take k) (List.ofFn x))
        (Ledger.wiresFrom (gs.take k) (List.ofFn x)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk x
    by_cases hk0 : k = 0
    · subst k
      intro i hi
      exact hi
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hj : j < gs.length := by omega
      have hjnorm : j < (normalizeGates gs safe pick).length := by
        simpa [normalizeGates_length] using hj
      have hprev := ih j (by omega) (by omega) x
      have htakeOrig : gs.take (j + 1) = gs.take j ++ [gs[j]'hj] :=
        List.take_succ_eq_append_getElem hj
      have htakeNorm : (normalizeGates gs safe pick).take (j + 1) =
          (normalizeGates gs safe pick).take j ++
            [(normalizeGates gs safe pick)[j]'hjnorm] :=
        List.take_succ_eq_append_getElem hjnorm
      rw [normalizeGates_get gs safe pick j hj] at htakeNorm
      let oldW := Ledger.wiresFrom (gs.take j) (List.ofFn x)
      let newW := Ledger.wiresFrom ((normalizeGates gs safe pick).take j) (List.ofFn x)
      have hprev' : WireLe newW oldW := by simpa [newW, oldW] using hprev
      have hraw : ∀ p : Fin n, newW.getD p.val false = x p := by
        intro p
        dsimp [newW]
        rw [Ledger.getD_wiresFrom_lt _ _ _ (by simp)]
        simp [List.getD_eq_getElem, List.getElem_ofFn]
      have hstep := normalize_gateStep_le G gs safe pick hops hPick j hj x newW hprev' hraw
      have hlen : newW.length = oldW.length := by
        simp [newW, oldW, Ledger.length_wiresFrom, normalizeGates_length,
          Nat.min_eq_left (Nat.le_of_lt hj), Nat.min_eq_left (Nat.le_of_lt hjnorm)]
      rw [htakeNorm, htakeOrig, Ledger.wiresFrom_append, Ledger.wiresFrom_append,
        wiresFrom_singleton, wiresFrom_singleton]
      change WireLe (newW ++ [(replaceGate safe pick j (gs[j]'hj)).op.eval
          ((replaceGate safe pick j (gs[j]'hj)).inputs.map fun i => newW.getD i false)])
        (oldW ++ [(gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => oldW.getD i false)])
      apply wireLe_snoc hlen hprev'
      intro hval
      apply hstep
      simpa [normalizeGates_get gs safe pick j hj] using hval

theorem normalize_wire_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (gs : List Gate) (safe : ℕ → Bool) (pick : ℕ → Option (Fin n × Fin n))
    (hops : binaryOps gs)
    (hPick : ∀ i : Fin gs.length, (gs.get i).op = GateOp.and → safe i.val = false →
      (∀ a b : Fin n, G.Adj a b →
        (origWireVal gs i (pairBits a b) = true ↔
          pick i.val = some (a, b) ∨ pick i.val = some (b, a))) ∧
      (∀ a b : Fin n, pick i.val = some (a, b) →
        G.Adj a b ∧ origWireVal gs i (pairBits a b) = true))
    (x : Fin n → Bool) :
      WireLe (Ledger.wiresFrom (normalizeGates gs safe pick) (List.ofFn x))
        (Ledger.wiresFrom gs (List.ofFn x)) := by
  have h := normalize_prefix_le G gs safe pick hops hPick gs.length (by rfl) x
  have ht : (normalizeGates gs safe pick).take gs.length = normalizeGates gs safe pick := by
    rw [← normalizeGates_length gs safe pick]
    exact List.take_length
  have htOrig : gs.take gs.length = gs := List.take_length
  rw [ht] at h
  rw [htOrig] at h
  exact h

end PEqualNP.Outside.L_meta_4767

namespace PEqualNP.Outside.L_meta_4767
open PEqualNP.CircuitLowerBounds Ledger
def oldWireValue {n : ℕ} (gs : List Gate) (i : ℕ) (x : Fin n → Bool) : Bool :=
  ((Circuit.mk gs 0).wires (List.ofFn x)).getD (n + i) false

lemma normalizeGates_take {n : ℕ} (gs : List Gate) (safe : ℕ → Bool)
    (pick : ℕ → Option (Fin n × Fin n)) (k : ℕ) :
    (normalizeGates gs safe pick).take k = normalizeGates (gs.take k) safe pick := by
  apply List.ext_getElem
  · simp [normalizeGates]
  · intro i h₁ h₂
    simp [normalizeGates, List.getElem_mapIdx] at h₁ h₂ ⊢

lemma normalizeGates_snoc {n : ℕ} (gs : List Gate) (g : Gate)
    (safe : ℕ → Bool) (pick : ℕ → Option (Fin n × Fin n)) :
    normalizeGates (gs ++ [g]) safe pick =
      normalizeGates gs safe pick ++ [replaceGate safe pick gs.length g] := by
  apply List.ext_getElem
  · simp [normalizeGates]
  · intro i h₁ h₂
    by_cases hi : i < gs.length
    · simp [normalizeGates, hi, List.getElem_mapIdx]
    · have hieq : i = gs.length := by simp [normalizeGates] at h₁; omega
      subst i
      simp [normalizeGates, List.getElem_mapIdx]

lemma wiresFrom_gateEval_eq_local {n : ℕ} (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (x : Fin n → Bool) :
    (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
      (wiresFrom (gs.take k) (List.ofFn x)).getD i false) =
      (wiresFrom gs (List.ofFn x)).getD (n + k) false := by
  have hsplit : gs.take (k + 1) = gs.take k ++ [gs[k]'hk] :=
    List.take_succ_eq_append_getElem hk
  have hcut := getD_wiresFrom_take gs (List.ofFn x) (k + 1) (n + k) (by omega)
  simp only [List.length_ofFn] at hcut
  rw [if_pos (by omega)] at hcut
  have hrun : wiresFrom (gs.take (k + 1)) (List.ofFn x) =
      wiresFrom (gs.take k) (List.ofFn x) ++
        [(gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
          (wiresFrom (gs.take k) (List.ofFn x)).getD i false)] := by
    rw [hsplit, wiresFrom_append]
    rfl
  have hlen : (wiresFrom (gs.take k) (List.ofFn x)).length = n + k := by
    simp [length_wiresFrom, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [hrun, ← hlen, getD_snoc_eq, hlen] at hcut
  exact hcut

lemma wiresFrom_gateValue_eq_local {n : ℕ} (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (x : Fin n → Bool) :
    (wiresFrom gs (List.ofFn x)).getD (n + k) false =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
        (wiresFrom (gs.take k) (List.ofFn x)).getD i false) := by
  exact (wiresFrom_gateEval_eq_local gs k hk x).symm

lemma wiresFrom_snoc_local (gs : List Gate) (g : Gate) (w : List Bool) :
    wiresFrom (gs ++ [g]) w = wiresFrom gs w ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs w).getD i false)] := by
  rw [wiresFrom_append]
  rfl

private lemma pairBits_gate_iff {n : ℕ} (a b u v : Fin n)
    (hab : a ≠ b) (huv : u ≠ v) :
    pairBits a b u = true ∧ pairBits a b v = true ↔
      (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  have hu : pairBits a b u = true ↔ u = a ∨ u = b := by simp [pairBits]
  have hv : pairBits a b v = true ↔ v = a ∨ v = b := by simp [pairBits]
  constructor
  · intro h
    rcases hu.mp h.1 with hua | hub <;> rcases hv.mp h.2 with hva | hvb
    · exact False.elim (huv (hua.trans hva.symm))
    · exact Or.inl ⟨hua, hvb⟩
    · exact Or.inr ⟨hub, hva⟩
    · exact False.elim (huv (hub.trans hvb.symm))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [pairBits]

private lemma replacedGate_eval_pair {n : ℕ} (G : SimpleGraph (Fin n))
    (gs : List Gate) (safe : ℕ → Bool) (pick : ℕ → Option (Fin n × Fin n))
    (k : ℕ) (hk : k < gs.length) (a b : Fin n) (hab : G.Adj a b)
    (hp : (gs[k]'hk).op = GateOp.and → safe k = false →
      (∀ u v, G.Adj u v →
        (oldWireValue gs k (pairBits u v) = true ↔
          pick k = some (u, v) ∨ pick k = some (v, u))) ∧
      (∀ u v, pick k = some (u, v) →
        G.Adj u v ∧ oldWireValue gs k (pairBits u v) = true)) :
    (replaceGate safe pick k (gs[k]'hk)).op.eval
        ((replaceGate safe pick k (gs[k]'hk)).inputs.map fun i =>
          (wiresFrom (gs.take k) (List.ofFn (pairBits a b))).getD i false) =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
        (wiresFrom (gs.take k) (List.ofFn (pairBits a b))).getD i false) := by
  let g := gs[k]'hk
  let row : Fin n → Bool := pairBits a b
  let w := wiresFrom (gs.take k) (List.ofFn row)
  have hOld : oldWireValue gs k row = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simpa [oldWireValue, Circuit.wires, wiresFrom, g, w, row] using
      (wiresFrom_gateValue_eq_local gs k hk row)
  letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  by_cases hand : g.op = GateOp.and
  · by_cases hs : safe k = true
    · simp [replaceGate, g, hand, hs]
    · have hsf : safe k = false := by cases h : safe k <;> simp_all
      have hdata := hp hand hsf
      cases hpick : pick k with
      | none =>
        have holdFalse : oldWireValue gs k row = false := by
          have hiff : oldWireValue gs k row = true ↔ False := by
            simpa [row, hpick] using hdata.1 a b hab
          cases hv : oldWireValue gs k row <;> simp_all
        have hrep : replaceGate safe pick k g = ⟨GateOp.or, []⟩ := by
          simp [replaceGate, g, hand, hsf, hpick]
        rw [hrep]
        change GateOp.or.eval ([] : List Bool) =
          (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => w.getD i false)
        simp only [GateOp.eval, List.any_nil]
        change false = g.op.eval (g.inputs.map fun i => w.getD i false)
        rw [← hOld, holdFalse]
      | some uv =>
        rcases uv with ⟨u, v⟩
        have hpick' : pick k = some (u, v) := hpick
        have hedg : G.Adj u v := (hdata.2 u v hpick').1
        have huv : u ≠ v := G.ne_of_adj hedg
        have holdTrue : oldWireValue gs k row = true ↔
            (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
          simpa [row, hpick'] using hdata.1 a b hab
        have hu : w.getD u.val false = pairBits a b u := by
          rw [getD_wiresFrom_lt _ _ _ (by simp)]
          simp [row]
        have hv : w.getD v.val false = pairBits a b v := by
          rw [getD_wiresFrom_lt _ _ _ (by simp)]
          simp [row]
        have hnewTrue :
            (replaceGate safe pick k g).op.eval ((replaceGate safe pick k g).inputs.map
              fun i => w.getD i false) = true ↔
              (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
          have hrep : replaceGate safe pick k g = ⟨GateOp.and, [u.val, v.val]⟩ := by
            simp [replaceGate, g, hand, hsf, hpick']
          rw [hrep]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
          simp only [Bool.and_eq_true, and_true]
          rw [hu, hv]
          exact pairBits_gate_iff a b u v (G.ne_of_adj hab) huv
        have holdEvalTrue : g.op.eval (g.inputs.map fun i => w.getD i false) = true ↔
            (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
          rw [← hOld]
          exact holdTrue
        have hEqTrue : (g.op.eval (g.inputs.map fun i => w.getD i false) = true) ↔
            ((replaceGate safe pick k g).op.eval ((replaceGate safe pick k g).inputs.map
              fun i => w.getD i false) = true) := by
          exact holdEvalTrue.trans hnewTrue.symm
        cases h₁ : (replaceGate safe pick k g).op.eval
            ((replaceGate safe pick k g).inputs.map fun i => w.getD i false) <;>
          cases h₂ : g.op.eval (g.inputs.map fun i => w.getD i false) <;> simp_all
  · simp [replaceGate, g, hand]

private lemma normalize_prefix_eq {n : ℕ} (G : SimpleGraph (Fin n))
    (gs : List Gate) (safe : ℕ → Bool) (pick : ℕ → Option (Fin n × Fin n))
    (hp : ∀ i : Fin gs.length, (gs.get i).op = GateOp.and → safe i.val = false →
      (∀ u v, G.Adj u v →
        (oldWireValue gs i.val (pairBits u v) = true ↔
          pick i.val = some (u, v) ∨ pick i.val = some (v, u))) ∧
      (∀ u v, pick i.val = some (u, v) →
        G.Adj u v ∧ oldWireValue gs i.val (pairBits u v) = true))
    (a b : Fin n) (hab : G.Adj a b) :
    ∀ k ≤ gs.length,
      wiresFrom (normalizeGates (gs.take k) safe pick) (List.ofFn (pairBits a b)) =
        wiresFrom (gs.take k) (List.ofFn (pairBits a b)) := by
  intro k
  induction k with
  | zero => intro hk; simp [normalizeGates, wiresFrom]
  | succ k ih =>
    intro hk
    have hk' : k < gs.length := by omega
    have hprev := ih (by omega)
    have htake : gs.take (k + 1) = gs.take k ++ [gs[k]'hk'] :=
      List.take_succ_eq_append_getElem hk'
    have hnorm : normalizeGates (gs.take (k + 1)) safe pick =
        normalizeGates (gs.take k) safe pick ++
          [replaceGate safe pick k (gs[k]'hk')] := by
      rw [htake, normalizeGates_snoc]
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk')]
    have hlocal := replacedGate_eval_pair G gs safe pick k hk' a b hab
      (fun ha hs => hp ⟨k, hk'⟩ (by simpa using ha) hs)
    rw [hnorm, wiresFrom_snoc_local, htake, wiresFrom_snoc_local, hprev]
    rw [hlocal]

theorem normalize_eq_on_edgePairs {n : ℕ} (G : SimpleGraph (Fin n))
    (gs : List Gate) (safe : ℕ → Bool) (pick : ℕ → Option (Fin n × Fin n))
    (hsafe : ∀ i : Fin gs.length, (gs.get i).op = GateOp.and → safe i.val = true →
      ∀ x, oldWireValue gs i.val x = true → edgeTrue G x)
    (hp : ∀ i : Fin gs.length, (gs.get i).op = GateOp.and → safe i.val = false →
      (∀ u v, G.Adj u v →
        (oldWireValue gs i.val (pairBits u v) = true ↔
          pick i.val = some (u, v) ∨ pick i.val = some (v, u))) ∧
      (∀ u v, pick i.val = some (u, v) →
        G.Adj u v ∧ oldWireValue gs i.val (pairBits u v) = true))
    (a b : Fin n) (hab : G.Adj a b) :
    ∀ w, ((Circuit.mk (normalizeGates gs safe pick) 0).wires
          (List.ofFn (pairBits a b))).getD w false =
        ((Circuit.mk gs 0).wires (List.ofFn (pairBits a b))).getD w false := by
  intro w
  change (wiresFrom (normalizeGates gs safe pick) (List.ofFn (pairBits a b))).getD w false =
    (wiresFrom gs (List.ofFn (pairBits a b))).getD w false
  have hprefix := normalize_prefix_eq G gs safe pick hp a b hab
  by_cases hw : w < n
  · have h1 := getD_wiresFrom_lt (normalizeGates gs safe pick)
      (List.ofFn (pairBits a b)) w (by simpa using hw)
    have h2 := getD_wiresFrom_lt gs (List.ofFn (pairBits a b)) w (by simpa using hw)
    rw [h1, h2]
  · by_cases hg : w < n + gs.length
    · let k := w - n
      have hk : k < gs.length := by dsimp [k]; omega
      have hw' : w = n + k := by dsimp [k]; omega
      rw [hw']
      have hleft := getD_wiresFrom_take (normalizeGates gs safe pick)
        (List.ofFn (pairBits a b)) (k + 1) (n + k) (by
          rw [normalizeGates_length]; omega)
      have hright := getD_wiresFrom_take gs (List.ofFn (pairBits a b))
        (k + 1) (n + k) (by omega)
      simp only [List.length_ofFn] at hleft hright
      rw [if_pos (by omega)] at hleft hright
      have hpre := hprefix (k + 1) (by omega)
      have hpre' : wiresFrom ((normalizeGates gs safe pick).take (k+1))
          (List.ofFn (pairBits a b)) = wiresFrom (gs.take (k+1))
          (List.ofFn (pairBits a b)) := by
        simpa [normalizeGates_take] using hpre
      rw [hpre'] at hleft
      calc
        (wiresFrom (normalizeGates gs safe pick) (List.ofFn (pairBits a b))).getD (n+k) false =
            (wiresFrom (gs.take (k+1)) (List.ofFn (pairBits a b))).getD (n+k) false := hleft.symm
        _ = (wiresFrom gs (List.ofFn (pairBits a b))).getD (n+k) false := hright
    · have hlen₁ : (wiresFrom (normalizeGates gs safe pick) (List.ofFn (pairBits a b))).length = n + gs.length := by
        simp [length_wiresFrom, List.length_ofFn, normalizeGates_length]
      have hlen₂ : (wiresFrom gs (List.ofFn (pairBits a b))).length = n + gs.length := by
        simp [length_wiresFrom, List.length_ofFn]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

end PEqualNP.Outside.L_meta_4767


namespace PEqualNP.Outside.L_meta_4767
open PEqualNP.CircuitLowerBounds Ledger

theorem normalize_cleanOn_from_dom {n : Nat} (G : SimpleGraph (Fin n))
    (gs : List Gate) (safe : Nat → Bool) (pick : Nat → Option (Fin n × Fin n))
    (hs : ∀ i : Fin gs.length, (gs.get i).op = .and → safe i = true →
      ∀ x, origWireVal gs i x = true → edgeTrue G x)
    (hp : ∀ i : Fin gs.length, (gs.get i).op = .and → safe i = false →
      ∀ a b, pick i = some (a,b) → G.Adj a b)
    (dom : ∀ x : Fin n → Bool, WireLe (wiresFrom (normalizeGates gs safe pick) (List.ofFn x))
        (wiresFrom gs (List.ofFn x))) : cleanOn G (normalizeGates gs safe pick) := by
  let ns := normalizeGates gs safe pick
  intro j x _ newAnd live
  have bound : j.val < gs.length := by simpa [normalizeGates] using j.isLt
  let i : Fin gs.length := ⟨j.val,bound⟩
  have gate : ns.get j = replaceGate safe pick j.val (gs.get i) :=
    normalizeGates_get gs safe pick j.val bound
  have ho : (gs.get i).op = GateOp.and := by
    by_contra h
    rw [gate] at newAnd
    simp only [replaceGate, if_neg h] at newAnd
    exact h newAnd
  cases hz : safe i.val with
  | true => exact hs i ho hz x (dom x (n + j.val) live)
  | false =>
    cases hpick : pick i.val with
    | none =>
      rw [gate] at newAnd
      change (replaceGate safe pick i.val (gs.get i)).op = GateOp.and at newAnd
      simp only [replaceGate, if_pos ho] at newAnd
      simp [hz,hpick] at newAnd
    | some e =>
      obtain ⟨a,b⟩ := e
      have actual : ns[j.val] = (⟨.and,[a.val,b.val]⟩ : Gate) := by
        change ns.get j = _
        rw [gate]
        change replaceGate safe pick i.val (gs.get i) = _
        simp only [replaceGate, if_pos ho]
        simp [hz,hpick]
      have evalAt := wiresFrom_gateValue_eq ns j.val j.isLt x
      rw [actual] at evalAt
      have eqv : (⟨.and,[a.val,b.val]⟩ : Gate).op.eval
          ((⟨.and,[a.val,b.val]⟩ : Gate).inputs.map fun w =>
            (wiresFrom (ns.take j.val) (List.ofFn x)).getD w false) = true := evalAt.symm.trans live
      obtain ⟨tail,extension,_⟩ := wiresFrom_ext (ns.take j.val) (List.ofFn x)
      rw [extension] at eqv
      obtain ⟨ta,tb⟩ := (andGate_on_extension x a b tail).mp eqv
      exact ⟨a,b,hp i ho hz a b hpick,ta,tb⟩

end PEqualNP.Outside.L_meta_4767

namespace PEqualNP.Outside.L_meta_4767

open PEqualNP.CircuitLowerBounds Ledger

theorem concludeFromNormalization (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (square : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (gs ns : List Gate) (out : Nat)
    (computes : ∀ x : Fin n → Bool, (Circuit.mk gs out).eval (List.ofFn x) =
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    (ops : binaryOps ns) (size : ns.length = gs.length)
    (dom : ∀ x : Fin n → Bool, ∀ w, (wiresFrom ns (List.ofFn x)).getD w false = true →
      (wiresFrom gs (List.ofFn x)).getD w false = true)
    (agree : ∀ u v, G.Adj u v → ∀ w,
      (wiresFrom ns (List.ofFn (pairBits u v))).getD w false =
        (wiresFrom gs (List.ofFn (pairBits u v))).getD w false)
    (clean : cleanOn G ns) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ gs.length + 1 := by
  let old := fun x : Fin n → Bool => (Circuit.mk gs out).eval (List.ofFn x)
  let new := fun x : Fin n → Bool => (Circuit.mk ns out).eval (List.ofFn x)
  have monotone (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) : new x = true → new y = true :=
    pos_mono ns (fun g hg => (ops g hg).1) (out+1) x y h
  have result := recoverEdgeFunction G old new computes (fun x => dom x out)
    (fun u v e => agree u v e out) monotone
  obtain ⟨T,cover,count⟩ := pairCleanBound n G square ns out ops result clean
  exact ⟨T,cover,size ▸ count⟩

end PEqualNP.Outside.L_meta_4767

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4767 PEqualNP.Outside.L_meta_4767.Ledger in
theorem PEqualNP.Outside.L_meta_4767 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∨ (∀ a b c d : Fin n, G.Adj a b → G.Adj c d → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = a ∨ k = b)))).getD (n + (i : ℕ)) false = true → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun k => decide (k = c ∨ k = d)))).getD (n + (i : ℕ)) false = true → (a = c ∧ b = d) ∨ (a = d ∧ b = c))) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G inst square gs out hops computes spec
  let val := fun (i : Nat) (x : Fin n → Bool) =>
    ((Circuit.mk gs 0).wires (List.ofFn x)).getD (n+i) false
  obtain ⟨safe,pick,hs,hp⟩ := chooseGateData G val (fun i : Fin gs.length =>
    (gs.get i).op = GateOp.and) spec
  have dom := normalize_wire_le G gs safe pick hops hp
  exact concludeFromNormalization n G square gs (normalizeGates gs safe pick) out computes
    (normalizeGates_binaryOps gs safe pick hops) (normalizeGates_length gs safe pick) dom
    (normalize_eq_on_edgePairs G gs safe pick hs hp)
    (normalize_cleanOn_from_dom G gs safe pick hs (fun i ha hf a b h => (hp i ha hf).2 a b h |>.1) dom)
