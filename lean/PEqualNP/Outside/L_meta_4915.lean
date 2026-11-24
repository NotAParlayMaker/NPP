import Mathlib
import PEqualNP.Defs

-- OR support and DAG counting lemmas from copsrlpond, merged PR 2889, commit 1b5cd22c667b0d9f968d94cb3ef9cfbaa366473d.
namespace PEqualNP.Outside.L_meta_4915

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
  ∀ (j : Fin gs.length) (x : Fin n → Bool), (gs.get j).op = GateOp.and →
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
    obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z ha eqg
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
    (ha : andPos n gs w = true) (x : Fin n → Bool) :
    posRead gs w x = true → edgeTrue G x := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  rw [hw] at ha ⊢
  simp only [andPos, gateAt_index gs j hj] at ha
  have hop : gs[j].op = GateOp.and := by
    cases h : gs[j].op <;> simp_all
  exact clean ⟨j,hj⟩ x hop

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
  exact edge_single G u (pos_clean G gs clean w lo hi ha _ ((mem_support gs w u).mp hu))

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
  apply pos_clean G gs clean w lo hi ha
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


open PEqualNP.SharedBlockCost

theorem leaf_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (center : ι → Fin n) (leaf : ι → Finset (Fin n))
    (neighbors : ∀ j u, u ∈ leaf j → G.Adj (center j) u)
    (C : Circuit) (hc : IsOrCircuit n C) (root : ι → ℕ)
    (hr : ∀ j, ComputesOr n C (root j) (leaf j)) :
    (∑ v : Fin n, ((Finset.univ.filter (fun i : ι => center i = v)).biUnion leaf).card) ≤
      Fintype.card ι + C.gates.length := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h => simp
  | inr hn =>
    let S : ℕ → Finset (Fin n) := supports C.gates
    let N := n + 1 + C.gates.length
    let OS := Finset.Ico (n+1) N
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else Classical.choice hn
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    let I (c : Fin n) := Finset.univ.filter (fun i : ι => center i = c)
    let R (c : Fin n) := (I c).image (fun i => root i + 1)
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      have sub : S w ⊆ (Finset.univ.filter fun x => G.Adj (oc w) x ∧ G.Adj c x) := by
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h' x hx, h x hx⟩
      exact (not_lt_of_ge ((Finset.card_le_card sub).trans (h4 _ _ hne))) hbig
    have op (j : ℕ) (hj : j < C.gates.length) : C.gates[j].op = GateOp.or := by
      have h := (hc j hj).1
      cases e : C.gates[j].op <;> simp_all [isOrOp]
    have binary : binaryOps C.gates := by
      intro g hg
      obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
      subst g
      exact ⟨Or.inr (op j hj), (hc j hj).2.1.le⟩
    have clean : cleanOn G C.gates := by
      intro j x hj
      have he := op j.val j.isLt
      change C.gates[j.val].op = GateOp.and at hj
      rw [he] at hj
      contradiction
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : n+1 ≤ i := by
          by_contra! hh
          exact (not_lt_of_ge (support_base C.gates i hh)) hi
        let j := i - (n+1)
        have hj : j < C.gates.length := by dsimp [j,N] at *; omega
        have eqi : i = n+j+1 := by dsimp [j]; omega
        have orGate : andPos n C.gates i = false := by
          rw [eqi]
          simp only [andPos, gateAt_index C.gates j hj, op j hj]
        have hu := support_or G C.gates binary clean i hk hgood.1 orGate
        change S i = S (firstWire n C.gates i) ∪ S (secondWire n C.gates i) at hu
        have ha : firstWire n C.gates i < i := clamp_lt _ _ (by omega)
        have hb : secondWire n C.gates i < i := clamp_lt _ _ (by omega)
        have hfa : F c (firstWire n C.gates i) = S (firstWire n C.gates i) :=
          ite_eq_left ⟨ha.trans hgood.1, fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (secondWire n C.gates i) = S (secondWire n C.gates i) :=
          ite_eq_left ⟨hb.trans hgood.1, fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, _, ha, _, hb, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hk,hgood.1⟩, owner_eq i c hi hgood.2⟩
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    have root_set (j : ι) : S (root j + 1) = leaf j := by
      ext u
      change u ∈ supports C.gates (root j + 1) ↔ u ∈ leaf j
      rw [mem_support]
      change PEqualNP.BlindGate.wireValue C n (singletonBits u) (root j) = true ↔ _
      rw [(hr j).2]
      simp [singletonBits]
    have bound (c : Fin n) : ((I c).biUnion leaf).card ≤ (I c).card + (B c).card := by
      have subset : (I c).biUnion leaf ⊆ (R c).biUnion (F c) := by
        intro x hx
        obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp hx
        have cen : center j = c := (Finset.mem_filter.mp hj).2
        have good : root j + 1 < N ∧ adj c (root j + 1) := by
          refine ⟨?_,?_⟩
          · have h := (hr j).1
            dsimp [N]
            omega
          · intro t ht
            rw [←cen]
            exact neighbors j t (root_set j ▸ ht)
        exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_image_of_mem _ hj, by simpa [F,good,root_set] using hx⟩
      have rsmall : (R c).card ≤ (I c).card := Finset.card_image_le
      exact (Finset.card_le_card subset).trans ((hlocal c).trans (Nat.add_le_add_right rsmall _))
    have his : (∑ c, (I c).card) = Fintype.card ι :=
      (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset ι)) (f := center) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      _ ≤ ∑ c : Fin n, ((I c).card + (B c).card) := Finset.sum_le_sum (fun c _ => bound c)
      _ = _ := by rw [Finset.sum_add_distrib,his,hbs]; simp [OS,N]

open PEqualNP PEqualNP.BicliqueBlockCost PEqualNP.SharedBlockCost PEqualNP.CircuitLowerBounds

theorem orientBlock {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : TopForm.NoFourCycle G) (p : Block n) (hp : IsBlock G p) :
    ∃ (v : Fin n) (L : Finset (Fin n)), (L = p.1 ∨ L = p.2) ∧ L.Nonempty ∧
      (∀ u ∈ L, G.Adj v u) ∧ ∀ u w, BlockCovers p u w →
        (u = v ∧ w ∈ L) ∨ (w = v ∧ u ∈ L) := by
  classical
  obtain ⟨A,B⟩ := p
  obtain ⟨_,hA,hB,join⟩ := hp
  change A.Nonempty at hA
  change B.Nonempty at hB
  change ∀ a ∈ A, ∀ b ∈ B, G.Adj a b at join
  have hs : A.card ≤ 1 ∨ B.card ≤ 1 := by
    by_cases h : A.card ≤ 1
    · exact Or.inl h
    · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
      exact Or.inr ((Finset.card_le_card (show B ⊆ Finset.univ.filter (fun u => G.Adj a u ∧ G.Adj b u) by
        intro u hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,join a ha u hu,join b hb u hu⟩)).trans (h4 a b hab))
  rcases hs with h | h
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr hA))
    refine ⟨v,B,Or.inr rfl,hB,join v (Finset.mem_singleton_self _),?_⟩
    intro u w h
    simpa only [BlockCovers, Finset.mem_singleton] using h
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr hB))
    refine ⟨v,A,Or.inl rfl,hA,fun u hu => (join u hu v (Finset.mem_singleton_self _)).symm,?_⟩
    intro u w h
    rcases h with ⟨hu,hw⟩ | ⟨hw,hu⟩
    · exact Or.inr ⟨Finset.mem_singleton.mp hw,hu⟩
    · exact Or.inl ⟨Finset.mem_singleton.mp hu,hw⟩

theorem mergeStars {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (F : Finset (Block n)) (hF : IsBlockCover G F)
    (center : F → Fin n) (leaf : F → Finset (Fin n))
    (nonempty : ∀ j, (leaf j).Nonempty)
    (neighbors : ∀ j u, u ∈ leaf j → G.Adj (center j) u)
    (splitEdge : ∀ (j : F) u w, BlockCovers j.val u w →
      (u = center j ∧ w ∈ leaf j) ∨ (w = center j ∧ u ∈ leaf j))
    (k : ℕ) (hl : (∑ v : Fin n, ((Finset.univ.filter (fun i : F => center i = v)).biUnion leaf).card)
      ≤ F.card + k) : HasBlockCost G (k + F.card + (F.card - 1)) := by
  classical
  let T := Finset.univ.image center
  let U := fun v => (Finset.univ.filter (fun i : F => center i = v)).biUnion leaf
  let star := fun v : Fin n => (({v}, U v) : Block n)
  let A := T.image star
  have leafIn (j : F) (v : Fin n) (hj : center j = v) (u : Fin n) (hu : u ∈ leaf j) : u ∈ U v :=
    Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,hu⟩
  have adjU (v u : Fin n) (hu : u ∈ U v) : G.Adj v u := by
    obtain ⟨j,hj,huj⟩ := Finset.mem_biUnion.mp hu
    rw [← (Finset.mem_filter.mp hj).2]
    exact neighbors j u huj
  have node (j : F) : center j ∈ T := Finset.mem_image_of_mem center (Finset.mem_univ j)
  have hcost (v : Fin n) : blockCost (star v) = (U v).card := by simp [star,blockCost]
  refine ⟨A, ⟨?_,?_⟩, ?_⟩
  · intro p hp
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨u,hu⟩ := nonempty j
    refine ⟨Finset.disjoint_left.mpr ?_, Finset.singleton_nonempty _, ⟨u,leafIn j _ rfl u hu⟩,
      fun a ha b hb => ?_⟩
    · intro t ht hu'
      have he : t = center j := Finset.mem_singleton.mp ht
      subst t
      exact (G.loopless.irrefl _) (adjU (center j) _ hu')
    · have he : a = center j := Finset.mem_singleton.mp ha
      simpa only [he] using adjU (center j) b hb
  · intro u v huv
    obtain ⟨p,hp,hcov⟩ := hF.2 u v huv
    let j : F := ⟨p,hp⟩
    refine ⟨star (center j),Finset.mem_image_of_mem star (node j),?_⟩
    rcases splitEdge j u v hcov with ⟨rfl,hv⟩ | ⟨rfl,hu⟩
    · exact Or.inl ⟨Finset.mem_singleton_self _,leafIn j _ rfl v hv⟩
    · exact Or.inr ⟨Finset.mem_singleton_self _,leafIn j _ rfl u hu⟩
  · have hT : T.card ≤ F.card := Finset.card_image_le.trans (by simp)
    have hA : A.card ≤ F.card := Finset.card_image_le.trans hT
    have hs : (∑ p ∈ A, blockCost p) = ∑ v ∈ T, (U v).card := by
      change (∑ p ∈ T.image star, blockCost p) = _
      rw [Finset.sum_image (by
        intro a _ b _ e
        have he := congrArg Prod.fst e
        simpa [star] using he)]
      exact Finset.sum_congr rfl (fun v _ => hcost v)
    have hU : (∑ v ∈ T, (U v).card) ≤ ∑ v : Fin n, (U v).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun _ _ _ => Nat.zero_le _)
    unfold familyCost
    rw [hs]
    change (∑ v : Fin n, (U v).card) ≤ F.card+k at hl
    omega

theorem shared_to_block {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (b : ℕ) (h4 : TopForm.NoFourCycle G) (h : HasSharedBlockCost G b) : HasBlockCost G b := by
  classical
  obtain ⟨F,hF,k,⟨C,⟨circuit,roots⟩,hc⟩,hb⟩ := h
  choose center leaf hside hnon hadj hcov using
    fun j : F => orientBlock G h4 j.val (hF.1 j.val j.property)
  have sideMem (j : F) : leaf j ∈ sides F := by
    rcases hside j with h | h
    · exact h ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst j.property)
    · exact h ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd j.property)
  choose root _ hr using fun j : F => roots (leaf j) (sideMem j)
  have count := leaf_bound G h4 center leaf hadj C circuit root hr
  have hl : (∑ v : Fin n, ((Finset.univ.filter (fun i : F => center i = v)).biUnion leaf).card) ≤ F.card + k :=
    (by simpa using count : _ ≤ F.card + C.gates.length) |>.trans (Nat.add_le_add_left hc _)
  obtain ⟨out,cover,le⟩ := mergeStars G F hF center leaf hnon hadj hcov k hl
  exact ⟨out,cover,le.trans hb⟩

end PEqualNP.Outside.L_meta_4915

theorem PEqualNP.Outside.L_meta_4915 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : ℕ), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.SharedBlockCost.HasSharedBlockCost x2 x4 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x4 := by
  intro n G _ b h4 h
  exact PEqualNP.Outside.L_meta_4915.shared_to_block G b h4 h
