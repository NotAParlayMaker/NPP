import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7626

abbrev Grid := Option ℕ × Option ℕ
abbrev Sig := Grid → Bool
abbrev Key := ℕ × Fin 3

def atom (a : Key) (p : Grid) : Bool :=
  (decide (a.2 ≠ 1) && decide (p.1 = some a.1)) ||
  (decide (a.2 ≠ 0) && decide (p.2 = some a.1))

def keys (I M : Finset ℕ) : Finset Key :=
  (I ×ˢ (Finset.univ : Finset (Fin 3))).filter fun a =>
    if a.1 ∈ M then a.2 = 2 else a.2 ≠ 2

def pool (K : Finset Key) : Set Sig := atom '' (↑K : Set Key)

def want (L R : Finset ℕ) (p : Grid) : Bool :=
  match p with
  | (some i, some j) => decide (i ∈ L ∧ j ∈ R ∧ i ≠ j)
  | _ => false

def gate (b : Bool) (u v : Sig) : Sig :=
  fun p => if b then u p || v p else u p && v p

def Free (P : Set Sig) (f : Sig) : Prop :=
  f ∈ P ∨ f = (fun _ => false) ∨ f = (fun _ => true)

def Run : ℕ → Set Sig → Sig → Prop
  | 0, P, f => Free P f
  | s+1, P, f => Run s P f ∨ ∃ u ∈ P, ∃ v ∈ P, ∃ b : Bool, Run s (insert (gate b u v) P) f

def Sep (P : Set Sig) (f : Sig) : Prop :=
  ∀ p q : Grid, (∀ u ∈ P, u p = u q) → f p = f q

def pull (ρ : Grid → Grid) (u : Sig) : Sig := u ∘ ρ

def dropKey (a : Key) (p : Grid) : Grid :=
  (if a.2 ≠ 1 ∧ p.1 = some a.1 then none else p.1,
   if a.2 ≠ 0 ∧ p.2 = some a.1 then none else p.2)

theorem run_mono {s t : ℕ} {P : Set Sig} {f : Sig} (hs : s ≤ t) : Run s P f → Run t P f := by
  induction hs with
  | refl => exact id
  | step _ ih => exact fun h => Or.inl (ih h)

private theorem l2_free_map {P Q : Set Sig} {f : Sig}
    (h : ∀ u ∈ P, Free Q u) (hf : Free P f) : Free Q f := by
  rcases hf with hf | hf | hf
  · exact h f hf
  · exact Or.inr (Or.inl hf)
  · exact Or.inr (Or.inr hf)

private theorem l2_gate_left {P : Set Sig} (b c : Bool) {v : Sig}
    (hv : Free P v) : Free P (gate b (fun _ => c) v) := by
  have hg : gate b (fun _ => c) v = (if b = c then (fun _ => c) else v) := by
    funext p
    cases b <;> cases c <;> simp [gate]
  rw [hg]
  split
  · cases c
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · exact hv

private theorem l2_gate_right {P : Set Sig} (b c : Bool) {u : Sig}
    (hu : Free P u) : Free P (gate b u (fun _ => c)) := by
  have hg : gate b u (fun _ => c) = (if b = c then (fun _ => c) else u) := by
    funext p
    cases b <;> cases c <;> simp [gate]
  rw [hg]
  split
  · cases c
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · exact hu

private theorem l2_gate_cases {Q : Set Sig} {u v : Sig} (b : Bool)
    (hu : Free Q u) (hv : Free Q v) : (u ∈ Q ∧ v ∈ Q) ∨ Free Q (gate b u v) := by
  rcases hu with hu | rfl | rfl
  · rcases hv with hv | rfl | rfl
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr (l2_gate_right b false (Or.inl hu))
    · exact Or.inr (l2_gate_right b true (Or.inl hu))
  · exact Or.inr (l2_gate_left b false hv)
  · exact Or.inr (l2_gate_left b true hv)

theorem run_weaken {s : ℕ} {P Q : Set Sig} {f : Sig} (h : ∀ u ∈ P, Free Q u) : Run s P f → Run s Q f := by
  induction s generalizing P Q with
  | zero => exact l2_free_map h
  | succ s ih =>
    intro hr
    rcases hr with hr | ⟨u, hu, v, hv, b, hr⟩
    · exact Or.inl (ih h hr)
    · rcases l2_gate_cases b (h u hu) (h v hv) with ⟨hu', hv'⟩ | hg
      · refine Or.inr ⟨u, hu', v, hv', b, ih ?_ hr⟩
        intro w hw
        rcases Set.mem_insert_iff.mp hw with rfl | hw
        · exact Or.inl (Set.mem_insert _ _)
        · exact l2_free_map (fun _ hk => Or.inl (Set.mem_insert_of_mem _ hk)) (h w hw)
      · refine Or.inl (ih ?_ hr)
        intro w hw
        rcases Set.mem_insert_iff.mp hw with rfl | hw
        · exact hg
        · exact h w hw

theorem run_sep {s : ℕ} {P : Set Sig} {f : Sig} : Run s P f → Sep P f := by
  induction s generalizing P with
  | zero =>
    intro h p q he
    rcases h with h | rfl | rfl
    · exact he f h
    · rfl
    · rfl
  | succ s ih =>
    intro hr
    rcases hr with hr | ⟨u, hu, v, hv, b, hr⟩
    · exact ih hr
    · intro p q he
      apply ih hr p q
      intro w hw
      rcases Set.mem_insert_iff.mp hw with rfl | hw
      · simp only [gate, he u hu, he v hv]
      · exact he w hw

private theorem l2_pull_gate (ρ : Grid → Grid) (b : Bool) (u v : Sig) :
    pull ρ (gate b u v) = gate b (pull ρ u) (pull ρ v) := rfl

theorem run_pull {s : ℕ} {P : Set Sig} {f : Sig} (ρ : Grid → Grid) : Run s P f → Run s (pull ρ '' P) (pull ρ f) := by
  induction s generalizing P with
  | zero =>
    intro hr
    rcases hr with h | rfl | rfl
    · exact Or.inl ⟨f, h, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  | succ s ih =>
    intro hr
    rcases hr with hr | ⟨u, hu, v, hv, b, hr⟩
    · exact Or.inl (ih hr)
    · refine Or.inr ⟨pull ρ u, ⟨u, hu, rfl⟩, pull ρ v, ⟨v, hv, rfl⟩, b, ?_⟩
      simpa only [Set.image_insert_eq, l2_pull_gate] using ih hr

private theorem l2_elide {s : ℕ} {P : Set Sig} {g f : Sig} (ρ : Grid → Grid)
    (hg : Free (pull ρ '' P) (pull ρ g)) (hr : Run s (insert g P) f) :
    Run s (pull ρ '' P) (pull ρ f) := by
  have hk := run_pull ρ hr
  rw [Set.image_insert_eq] at hk
  refine run_weaken ?_ hk
  intro w hw
  rcases Set.mem_insert_iff.mp hw with rfl | hw
  · exact hg
  · exact Or.inl hw

theorem cut_or {s : ℕ} {P H : Set Sig} {f : Sig} (h : Run s (P ∪ H) f) : Run s P f ∨ ∃ u ∈ H, ∀ ρ : Grid → Grid, pull ρ u = (fun _ => false) → pull ρ f ≠ (fun _ => false) → ∃ t, t+1 ≤ s ∧ Run t (pull ρ '' (P ∪ H)) (pull ρ f) := by
  induction s generalizing P with
  | zero =>
    rcases h with (hf | hf) | hf | hf
    · exact Or.inl (Or.inl hf)
    · exact Or.inr ⟨f, hf, fun _ he hn => (hn he).elim⟩
    · exact Or.inl (Or.inr (Or.inl hf))
    · exact Or.inl (Or.inr (Or.inr hf))
  | succ s ih =>
    rcases h with hr | ⟨u, hu, v, hv, b, hr⟩
    · rcases ih hr with hk | ⟨w, hw, hk⟩
      · exact Or.inl (Or.inl hk)
      · refine Or.inr ⟨w, hw, fun ρ he hn => ?_⟩
        obtain ⟨t, ht, hrun⟩ := hk ρ he hn
        exact ⟨t, Nat.le.step ht, hrun⟩
    · rcases hu with hu | hu
      · rcases hv with hv | hv
        · rw [← Set.insert_union] at hr
          rcases ih hr with hk | ⟨w, hw, hk⟩
          · exact Or.inl (Or.inr ⟨u, hu, v, hv, b, hk⟩)
          · refine Or.inr ⟨w, hw, fun ρ he hn => ?_⟩
            obtain ⟨t, ht, hrun⟩ := hk ρ he hn
            rw [Set.insert_union, Set.image_insert_eq, l2_pull_gate] at hrun
            refine ⟨t+1, Nat.succ_le_succ ht, Or.inr ?_⟩
            exact ⟨pull ρ u, ⟨u, Or.inl hu, rfl⟩, pull ρ v, ⟨v, Or.inl hv, rfl⟩, b, hrun⟩
        · refine Or.inr ⟨v, hv, fun ρ he _ => ⟨s, le_rfl, l2_elide ρ ?_ hr⟩⟩
          rw [l2_pull_gate, he]
          exact l2_gate_right b false (Or.inl ⟨u, Or.inl hu, rfl⟩)
      · refine Or.inr ⟨u, hu, fun ρ he _ => ⟨s, le_rfl, l2_elide ρ ?_ hr⟩⟩
        rw [l2_pull_gate, he]
        exact l2_gate_left b false (Or.inl ⟨v, hv, rfl⟩)

private theorem moSilent {I M : Finset ℕ} {a c : Key} {t : Fin 3}
    (ha : a ∈ keys I M) (hc : c ∈ keys I M) (hca : c ≠ a)
    (ht : t ≠ 2) (hat : a.2 ≠ t) : c.2 = t ∨ a.1 ≠ c.1 := by
  obtain ⟨i, s⟩ := a
  obtain ⟨j, r⟩ := c
  by_cases hij : i = j
  · subst j
    left
    have hrs : r ≠ s := fun e => hca (Prod.ext rfl e)
    change s ≠ t at hat
    change r = t
    by_cases hi : i ∈ M
    · simp [keys, hi] at ha hc
      exact False.elim (hrs (hc.2.trans ha.2.symm))
    · simp [keys, hi] at ha hc
      have hs := ha.2
      have hr := hc.2
      omega
  · exact Or.inr hij

theorem merge_only {I M : Finset ℕ} {a b : Key} (ha : a ∈ keys I M) (hb : b ∈ keys I M) (hab : a ≠ b)
    (h : Sep (insert (gate true (atom a) (atom b)) (pool (((keys I M).erase a).erase b))) (want I I)) :
    a.1 = b.1 := by
  -- Des indices distincts suffisent déjà à distinguer les deux clés.
  clear hab
  by_contra hd
  have haI := (Finset.mem_product.mp (Finset.mem_filter.mp ha).1).1
  have hbI := (Finset.mem_product.mp (Finset.mem_filter.mp hb).1).1
  have clash (p q : Grid) (hp : want I I p = true) (hq : want I I q = false)
      (hg : gate true (atom a) (atom b) p = gate true (atom a) (atom b) q)
      (hs : ∀ c ∈ keys I M, c ≠ a → c ≠ b → atom c p = atom c q) : False := by
    have he := h p q (by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | ⟨c, hc, rfl⟩
      · exact hg
      · obtain ⟨hcb, hca, hcK⟩ := (show c ≠ b ∧ c ≠ a ∧ c ∈ keys I M by
          simpa only [Finset.mem_coe, Finset.mem_erase] using hc)
        exact hs c hcK hca hcb)
    simp [hp, hq] at he
  by_cases hal : a.2 ≠ 1
  · by_cases hbl : b.2 ≠ 1
    · apply clash (some a.1, some b.1) (some b.1, some b.1)
      · simp [want, haI, hbI, hd]
      · simp [want]
      · simp [gate, atom, hal, hbl]
      · intro c hc hca hcb
        rcases moSilent ha hc hca (by decide) hal with e | e <;>
          rcases moSilent hb hc hcb (by decide) hbl with f | f <;> simp [atom, e, f]
    · have hbr : b.2 ≠ 0 := by omega
      apply clash (some a.1, some b.1) (none, some b.1)
      · simp [want, haI, hbI, hd]
      · rfl
      · simp [gate, atom, hbr]
      · intro c hc hca _
        rcases moSilent ha hc hca (by decide) hal with e | e <;> simp [atom, e]
  · have har : a.2 ≠ 0 := by omega
    by_cases hbr : b.2 ≠ 0
    · apply clash (some b.1, some a.1) (some b.1, some b.1)
      · simp [want, haI, hbI, Ne.symm hd]
      · simp [want]
      · simp [gate, atom, har, hbr]
      · intro c hc hca hcb
        rcases moSilent ha hc hca (by decide) har with e | e <;>
          rcases moSilent hb hc hcb (by decide) hbr with f | f <;> simp [atom, e, f]
    · have hbl : b.2 ≠ 1 := by omega
      apply clash (some b.1, some a.1) (none, some a.1)
      · simp [want, haI, hbI, Ne.symm hd]
      · rfl
      · simp [gate, atom, har]
      · intro c hc _ hcb
        rcases moSilent hb hc hcb (by decide) hbl with e | e <;> simp [atom, e]

private theorem keIndex {I M : Finset ℕ} {a : Key} (ha : a ∈ keys I M) : a.1 ∈ I :=
  (Finset.mem_product.mp (Finset.mem_filter.mp ha).1).1

private theorem keOpp {I M : Finset ℕ} {a b : Key} (ha : a ∈ keys I M)
    (hb : b ∈ keys I M) (hi : a.1 = b.1) (hne : a ≠ b) :
    (a.2 = 0 ∧ b.2 = 1) ∨ (a.2 = 1 ∧ b.2 = 0) := by
  obtain ⟨i, u⟩ := a
  obtain ⟨j, v⟩ := b
  change i = j at hi
  subst j
  have hu := (Finset.mem_filter.mp ha).2
  have hv := (Finset.mem_filter.mp hb).2
  by_cases h : i ∈ M
  · simp [h] at hu hv
    simp [hu, hv] at hne
  · simp [h] at hu hv
    fin_cases u <;> fin_cases v <;> simp_all

theorem pull_atom_self (a : Key) : pull (dropKey a) (atom a) = (fun _ => false) := by
  funext p
  simp only [pull, Function.comp_apply, atom, dropKey]
  split_ifs <;> simp_all

theorem pull_atom_other {I M : Finset ℕ} {a b : Key} (ha : a ∈ keys I M)
    (hb : b ∈ keys I M) (hne : a ≠ b) : pull (dropKey a) (atom b) = atom b := by
  funext p
  by_cases h : a.1 = b.1
  · rcases keOpp ha hb h hne with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;>
      simp [pull, atom, dropKey, hu, hv]
  · have hh (x : Option ℕ) (hx : x = some a.1) : x ≠ some b.1 := by simpa [hx] using h
    simp only [pull, Function.comp_apply, atom, dropKey]
    split_ifs with hl hr hr <;> simp_all

theorem pull_want (a : Key) (L R : Finset ℕ) : pull (dropKey a) (want L R) =
    want (if a.2 ≠ 1 then L.erase a.1 else L) (if a.2 ≠ 0 then R.erase a.1 else R) := by
  obtain ⟨k, s⟩ := a
  funext ⟨x, y⟩
  fin_cases s <;> cases x with
  | none => simp [pull, dropKey, want]
  | some i =>
    cases y with
    | none => by_cases hi : i = k <;> simp [pull, dropKey, want, hi]
    | some j => by_cases hi : i = k <;> by_cases hj : j = k <;> simp [pull, dropKey, want, hi, hj]

private theorem keLose {I M : Finset ℕ} {b : Key} (hb : b ∈ keys I M) {K : Finset Key}
    (hK : ∀ c ∈ K, c ∈ keys I M ∧ c ≠ b) {f : Sig} {p : Grid}
    (hp : f p = true) (hq : f (dropKey b p) = false) : ¬ Sep (pool K) f := by
  intro hs
  have he := hs p (dropKey b p) (by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hck, hcb⟩ := hK c hc
    exact (congrFun (pull_atom_other hb hck (Ne.symm hcb)) p).symm)
  simp [hp, hq] at he

private theorem keLeft {I M : Finset ℕ} {b : Key} (hb : b ∈ keys I M) {K : Finset Key}
    (hK : ∀ c ∈ K, c ∈ keys I M ∧ c ≠ b) {L R : Finset ℕ} {j : ℕ}
    (ht : b.2 ≠ 1) (hi : b.1 ∈ L) (hj : j ∈ R) (hji : j ≠ b.1) :
    ¬ Sep (pool K) (want L R) := by
  apply keLose hb hK (p := (some b.1, some j))
  · simp [want, hi, hj, Ne.symm hji]
  · simp [dropKey, want, ht, hji]

private theorem keRight {I M : Finset ℕ} {b : Key} (hb : b ∈ keys I M) {K : Finset Key}
    (hK : ∀ c ∈ K, c ∈ keys I M ∧ c ≠ b) {L R : Finset ℕ} {j : ℕ}
    (ht : b.2 ≠ 0) (hi : b.1 ∈ R) (hj : j ∈ L) (hji : j ≠ b.1) :
    ¬ Sep (pool K) (want L R) := by
  apply keLose hb hK (p := (some j, some b.1))
  · simp [want, hi, hj, hji]
  · simp [dropKey, want, ht, hji]

theorem key_essential {I M : Finset ℕ} (hn : 2 ≤ I.card) {a : Key}
    (ha : a ∈ keys I M) : ¬ Sep (pool ((keys I M).erase a)) (want I I) := by
  obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne hn a.1
  have hK : ∀ c ∈ (keys I M).erase a, c ∈ keys I M ∧ c ≠ a := by
    intro c hc
    exact (Finset.mem_erase.mp hc).symm
  by_cases h : a.2 = 1
  · exact keRight ha hK (by simp [h]) (keIndex ha) hj hji
  · exact keLeft ha hK h (keIndex ha) hj hji

theorem half_essential {I M : Finset ℕ} (hn : 2 ≤ I.card) {a b : Key}
    (ha : a ∈ keys I M) (hb : b ∈ keys I M) (hi : a.1 = b.1) (hab : a ≠ b) :
    ¬ Sep (pool (((keys I M).erase a).erase b)) (pull (dropKey a) (want I I)) := by
  rw [pull_want]
  obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne hn b.1
  have hK : ∀ c ∈ ((keys I M).erase a).erase b, c ∈ keys I M ∧ c ≠ b := by
    intro c hc
    exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc), (Finset.mem_erase.mp hc).1⟩
  rcases keOpp ha hb hi hab with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · apply keRight hb hK (by simp [hv]) _ _ hji
    · simpa [hu] using keIndex hb
    · simp [hu, hi, hji, hj]
  · apply keLeft hb hK (by simp [hv]) _ _ hji
    · simpa [hu] using keIndex hb
    · simp [hu, hi, hji, hj]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def repRead (w : List Sig) (i : ℕ) : Sig := w.getD i (fun _ => false)

private def repGate (w : List Sig) (g : Gate) : Sig :=
  fun p => g.op.eval (g.inputs.map fun i => repRead w i p)

private def repStep (w : List Sig) (g : Gate) := w ++ [repGate w g]

private theorem repMapRead (w : List Sig) (p : Grid) (i : ℕ) :
    (w.map (fun u => u p)).getD i false = repRead w i p :=
  List.getD_map w (fun _ => false) (fun u => u p)

private theorem repMapFold (gs : List Gate) (w : List Sig) (p : Grid) :
    (gs.foldl repStep w).map (fun u => u p) =
    gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
      (w.map (fun u => u p)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.foldl_cons, ih, repStep, List.map_append, List.map_cons,
      List.map_nil, repGate, repMapRead]

private theorem repReadFree {P : Set Sig} {w : List Sig} (h : ∀ u ∈ w, Free P u) (i : ℕ) :
    Free P (repRead w i) := by
  by_cases hi : i < w.length
  · rw [repRead, List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)
  · rw [repRead, List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    exact Or.inr (Or.inl rfl)

private def repNew (P : Set Sig) (z : Sig) : Prop :=
  Free P z ∨ ∃ u ∈ P, ∃ v ∈ P, ∃ b : Bool, z = gate b u v

private theorem repBinary {P : Set Sig} {u v : Sig} (b : Bool)
    (hu : Free P u) (hv : Free P v) : repNew P (gate b u v) := by
  obtain hu | hu | hu := hu
  · obtain hv | hv | hv := hv
    · exact Or.inr ⟨u, hu, v, hv, b, rfl⟩
    · subst v; left; unfold gate; cases b <;> simp [Free, hu]
    · subst v; left; unfold gate; cases b <;> simp [Free, hu]
  · subst u; left; unfold gate; cases b <;> simp_all [Free]
  · subst u; left; unfold gate; cases b <;> simp_all [Free]

private theorem repGateNew {P : Set Sig} {w : List Sig} (hw : ∀ u ∈ w, Free P u)
    (g : Gate) (hop : g.op = .and ∨ g.op = .or) (hs : g.inputs.length ≤ 2) :
    repNew P (repGate w g) := by
  obtain ⟨op, ins⟩ := g
  change op = .and ∨ op = .or at hop
  change ins.length ≤ 2 at hs
  cases ins with
  | nil => rcases hop with rfl | rfl <;> left <;> unfold repGate <;> simp [GateOp.eval, Free]
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl <;> left <;> unfold repGate <;>
        simpa [GateOp.eval] using repReadFree hw i
    | cons j tail =>
      cases tail with
      | nil =>
        rcases hop with rfl | rfl
        · convert repBinary false (repReadFree hw i) (repReadFree hw j) using 1
          funext p; simp [repGate, GateOp.eval, gate]
        · convert repBinary true (repReadFree hw i) (repReadFree hw j) using 1
          funext p; simp [repGate, GateOp.eval, gate]
      | cons _ _ => simp at hs

private theorem repBound {s t : ℕ} {P : Set Sig} {f : Sig} (h : s ≤ t) :
    Run s P f → Run t P f := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun hr => Or.inl (ih hr)

private theorem repCompile (gs : List Gate) (w : List Sig) (P : Set Sig) (i : ℕ)
    (hw : ∀ u ∈ w, Free P u)
    (hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    Run gs.length P (repRead (gs.foldl repStep w) i) := by
  induction gs generalizing w P with
  | nil => exact repReadFree hw i
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hgs g (by simp)
    have htail := fun k hk => hgs k (List.mem_cons_of_mem g hk)
    rcases repGateNew hw g hop hlen with h | ⟨u, hu, v, hv, b, he⟩
    · left
      apply ih _ _ _ htail
      intro z hz
      rcases List.mem_append.mp hz with hold | hnew
      · exact hw _ hold
      · simp only [List.mem_singleton] at hnew; exact hnew ▸ h
    · right
      refine ⟨u, hu, v, hv, b, ih _ _ ?_ htail⟩
      intro z hz
      rcases List.mem_append.mp hz with hold | hnew
      · rcases hw _ hold with hmem | hc
        · exact Or.inl (Set.mem_insert_of_mem _ hmem)
        · exact Or.inr hc
      · simp only [List.mem_singleton] at hnew
        exact Or.inl (Set.mem_insert_iff.mpr (Or.inl (hnew.trans he)))

private def repInputs (n : ℕ) : List Sig :=
  List.ofFn (fun i : Fin n => atom (i.val, 0)) ++
  List.ofFn (fun i : Fin n => atom (i.val, 1))

private theorem repInputsFree (n : ℕ) : ∀ u ∈ repInputs n,
    Free (pool (keys (Finset.range n) ∅)) u := by
  intro u hu
  left
  rcases List.mem_append.mp hu with hl | hr
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact ⟨(i.val, 0), by simp [keys, i.isLt], rfl⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact ⟨(i.val, 1), by simp [keys, i.isLt], rfl⟩

private theorem repMapPair {n : ℕ} (i j : Fin n) :
    (repInputs n).map (fun u => u (some i.val, some j.val)) = oneEach i j := by
  simp only [repInputs, List.map_append, List.map_ofFn, Function.comp_def, oneEach]
  congr 1 <;> apply congrArg List.ofFn <;> funext k <;> simp [atom, Fin.ext_iff, eq_comm]

private theorem repOrder {s : ℕ} {P : Set Sig} {f : Sig} {p q : Grid}
    (h : Run s P f) (hp : ∀ u ∈ P, u p = true → u q = true) : f p = true → f q = true := by
  induction s generalizing P with
  | zero =>
    rcases h with hmem | rfl | rfl
    · exact hp _ hmem
    · exact id
    · exact id
  | succ s ih =>
    rcases h with h | ⟨u, hu, v, hv, b, h⟩
    · exact ih h hp
    · apply ih h
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · cases b
        · simpa only [gate, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] using
            And.imp (hp u hu) (hp v hv)
        · simpa only [gate, ↓reduceIte, Bool.or_eq_true] using Or.imp (hp u hu) (hp v hv)
      · exact hp _ hz

private theorem repDominated {n : ℕ} (k : Fin n) (p : Grid)
    (hl : ∀ i : Fin n, p.1 = some i.val → i = k)
    (hr : ∀ i : Fin n, p.2 = some i.val → i = k) :
    ∀ u ∈ pool (keys (Finset.range n) ∅), u p = true → u (some k.val, some k.val) = true := by
  rintro _ ⟨⟨a, b⟩, ha, rfl⟩
  have han : a < n := by
    have h := (Finset.mem_filter.mp ha).1
    simpa using (Finset.mem_product.mp h).1
  simp only [atom, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rintro (⟨hb, he⟩ | ⟨hb, he⟩)
  · exact Or.inl ⟨hb, congrArg (fun i : Fin n => some i.val) (hl ⟨a, han⟩ he).symm⟩
  · exact Or.inr ⟨hb, congrArg (fun i : Fin n => some i.val) (hr ⟨a, han⟩ he).symm⟩

private theorem repWantValid {n : ℕ} {p : Grid}
    (h : want (Finset.range n) (Finset.range n) p = true) :
    (∃ i : Fin n, p.1 = some i.val) ∧ (∃ j : Fin n, p.2 = some j.val) := by
  obtain ⟨l, r⟩ := p
  cases l <;> cases r <;> simp_all [want]
  rename_i i j
  exact ⟨⟨⟨i, h.1⟩, rfl⟩, ⟨⟨j, h.2.1⟩, rfl⟩⟩

theorem run_of_rep {n s : ℕ}
    (h : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) :
    Run s (pool (keys (Finset.range n) ∅)) (want (Finset.range n) (Finset.range n)) := by
  cases n with
  | zero =>
    apply repBound (Nat.zero_le _)
    right; left; funext ⟨l, r⟩; cases l <;> cases r <;> simp [want]
  | succ m =>
    obtain ⟨C, hm, hs, hc⟩ := h
    let F := repRead (C.gates.foldl repStep (repInputs (m+1))) C.output
    have hF : Run C.size (pool (keys (Finset.range (m+1)) ∅)) F :=
      repCompile C.gates _ _ C.output (repInputsFree _) (fun g hg => by simpa using hm g hg)
    have hpair (i j : Fin (m+1)) : F (some i.val, some j.val) = decide (i ≠ j) := by
      unfold F
      rw [← repMapRead, repMapFold, repMapPair]
      exact hc i j
    have hdiag (k : Fin (m+1)) : F (some k.val, some k.val) = false := by simp [hpair]
    have heq : F = want (Finset.range (m+1)) (Finset.range (m+1)) := by
      funext p
      by_cases hboth : (∃ i : Fin (m+1), p.1 = some i.val) ∧ (∃ j : Fin (m+1), p.2 = some j.val)
      · obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hboth
        have hpeq : p = (some i.val, some j.val) := Prod.ext hi hj
        rw [hpeq, hpair]
        simp [want, i.isLt, j.isLt, Fin.ext_iff]
      · have hw : want (Finset.range (m+1)) (Finset.range (m+1)) p = false := by
          cases hval : want _ _ p <;> first | rfl | exact (hboth (repWantValid hval)).elim
        rw [hw]
        have hoff (k : Fin (m+1))
            (hl : ∀ i : Fin (m+1), p.1 = some i.val → i = k)
            (hr : ∀ i : Fin (m+1), p.2 = some i.val → i = k) : F p = false := by
          cases he : F p with
          | false => rfl
          | true => simpa [hdiag k] using repOrder hF (repDominated k p hl hr) he
        by_cases hl : ∃ i : Fin (m+1), p.1 = some i.val
        · obtain ⟨k, hk⟩ := hl
          exact hoff k (fun i hi => Fin.ext (Option.some.inj (hi.symm.trans hk)))
            (fun j hj => (hboth ⟨⟨k, hk⟩, ⟨j, hj⟩⟩).elim)
        · by_cases hr : ∃ j : Fin (m+1), p.2 = some j.val
          · obtain ⟨k, hk⟩ := hr
            exact hoff k (fun i hi => (hl ⟨i, hi⟩).elim)
              (fun j hj => Fin.ext (Option.some.inj (hj.symm.trans hk)))
          · exact hoff 0 (fun i hi => (hl ⟨i, hi⟩).elim) (fun j hj => (hr ⟨j, hj⟩).elim)
    exact heq ▸ repBound hs hF

theorem sep_sup {P Q : Set Sig} {f : Sig} (hPQ : P ⊆ Q) (h : Sep P f) : Sep Q f :=
  fun p q he => h p q fun u hu => he u (hPQ hu)

theorem support_bound {s : ℕ} {P : Set Sig} {f : Sig} (h : Run s P f) :
    ∃ S : Finset Sig, (↑S : Set Sig) ⊆ P ∧ S.card ≤ s+1 ∧ Sep (↑S) f := by
  classical
  induction s generalizing P with
  | zero =>
    rcases h with hf | hf | hf
    · exact ⟨{f}, by simpa using hf, by simp, fun p q H => H f (by simp)⟩
    · exact ⟨∅, by simp, by simp, by subst f; intro p q _; rfl⟩
    · exact ⟨∅, by simp, by simp, by subst f; intro p q _; rfl⟩
  | succ s ih =>
    rcases h with h | ⟨u, hu, v, hv, b, h⟩
    · obtain ⟨S, hS, hc, he⟩ := ih h
      exact ⟨S, hS, by omega, he⟩
    obtain ⟨S, hS, hc, he⟩ := ih h
    let g := gate b u v
    by_cases hg : g ∈ S
    · refine ⟨insert u (insert v (S.erase g)), ?_, ?_, ?_⟩
      · intro w hw
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hw
        rcases hw with rfl | rfl | ⟨hne, hw⟩
        · exact hu
        · exact hv
        · exact (hS hw).resolve_left hne
      · have h1 := Finset.card_insert_le u (insert v (S.erase g))
        have h2 := Finset.card_insert_le v (S.erase g)
        have h3 := Finset.card_erase_add_one hg
        omega
      · intro p q eqs
        apply he p q
        intro w hw
        by_cases hwg : w = g
        · subst w
          simp [g, gate, eqs u (by simp), eqs v (by simp)]
        · exact eqs w (by simp [Finset.mem_coe.mp hw, hwg])
    · refine ⟨S, ?_, by omega, he⟩
      intro w hw
      exact (hS hw).resolve_left fun e => hg (by simpa only [g, ← e] using Finset.mem_coe.mp hw)

theorem mem_keys {I M : Finset ℕ} {a : Key} : a ∈ keys I M ↔
    a.1 ∈ I ∧ (if a.1 ∈ M then a.2 = 2 else a.2 ≠ 2) := by simp [keys]

theorem keys_card {I M : Finset ℕ} (hM : M ⊆ I) : (keys I M).card + M.card = 2 * I.card := by
  let T : Finset (Fin 3) := {0,1}
  have hh : keys I M = (M ×ˢ ({2} : Finset (Fin 3))) ∪ ((I \ M) ×ˢ T) := by
    ext ⟨i,k⟩
    by_cases hi : i ∈ M
    · simp [mem_keys, hi, hM hi, eq_comm]
    · fin_cases k <;> simp [mem_keys, hi, T]
  rw [hh, Finset.card_union_of_disjoint (by
    apply Finset.disjoint_left.mpr
    rintro ⟨i,k⟩ ha hb
    exact (Finset.mem_sdiff.mp (Finset.mem_product.mp hb).1).2 (Finset.mem_product.mp ha).1)]
  have ht : T.card = 2 := by decide
  simp only [Finset.card_product, Finset.card_singleton, mul_one, ht]
  have := Finset.card_sdiff_add_card_eq_card hM
  omega

theorem atom_inj : Function.Injective atom := by
  intro ⟨i,k⟩ ⟨j,l⟩ he
  have e1 := congrFun he (some i,none)
  have e2 := congrFun he (none,some i)
  have e3 := congrFun he (some j,none)
  have e4 := congrFun he (none,some j)
  fin_cases k <;> fin_cases l <;> simp_all [atom]

theorem basic_bound {I M : Finset ℕ} {s : ℕ} (hn : 2 ≤ I.card) (hM : M ⊆ I)
    (h : Run s (pool (keys I M)) (want I I)) : 2 * I.card ≤ s+1+M.card := by
  classical
  obtain ⟨S,hs,hc,hsep⟩ := support_bound h
  have cover : (keys I M).image atom ⊆ S := by
    intro u hu
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    by_contra hbad
    apply key_essential hn ha
    apply sep_sup _ hsep
    intro v hv
    obtain ⟨d,hd,rfl⟩ := hs hv
    exact ⟨d, Finset.mem_erase.mpr ⟨by rintro rfl; exact hbad hv, hd⟩, rfl⟩
  have hc2 := Finset.card_le_card cover
  rw [Finset.card_image_of_injective _ atom_inj] at hc2
  have hk := keys_card hM
  omega

theorem nonzero_want {J L R : Finset ℕ} (hn : 2 ≤ J.card) (hL : J ⊆ L) (hR : J ⊆ R) :
    want L R ≠ (fun _ => false) := by
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hn
  intro h
  have := congrFun h (some i, some j)
  simp [want, hL hi, hR hj, hij] at this

theorem reduced_key {I M : Finset ℕ} {a d : Key} (hd : d ∈ keys I M) (hne : d.1 ≠ a.1) :
    d ∈ keys (I.erase a.1) (M.erase a.1) := by
  simpa [mem_keys, hne] using hd

theorem run_remove {s : ℕ} {P H : Set Sig} {f : Sig} (h : Run s P f) (sub : P ⊆ H) : Run s H f :=
  run_weaken (fun _ hu => Or.inl (sub hu)) h

theorem restrict_stock {s : ℕ} {I M : Finset ℕ} {a : Key} (ha : a ∈ keys I M) {f : Sig}
    (h : Run s (pull (dropKey a) '' (pool (keys I M))) f) : Run s (pool ((keys I M).erase a)) f := by
  apply run_weaken _ h
  rintro _ ⟨_, ⟨b,hb,rfl⟩,rfl⟩
  by_cases hba : b = a
  · subst b; exact Or.inr (Or.inl (pull_atom_self a))
  · rw [pull_atom_other ha hb (Ne.symm hba)]; exact Or.inl ⟨b, Finset.mem_erase.mpr ⟨hba,hb⟩,rfl⟩

theorem after_one {I M : Finset ℕ} (hn : 3 ≤ I.card) {a : Key} (ha : a ∈ keys I M) :
    pull (dropKey a) (want I I) ≠ (fun _ => false) := by
  rw [pull_want]
  have hcard := Finset.card_erase_add_one (mem_keys.mp ha).1
  apply nonzero_want (J := I.erase a.1) (by omega)
  all_goals split <;> first | exact Finset.Subset.refl _ | exact Finset.erase_subset _ _

theorem after_both {I M : Finset ℕ} {a b : Key} (ha : a ∈ keys I M) (hb : b ∈ keys I M)
    (hi : a.1 = b.1) (hne : a ≠ b) : pull (dropKey b) (pull (dropKey a) (want I I)) = want (I.erase a.1) (I.erase a.1) := by
  obtain ⟨i,k⟩ := a; obtain ⟨j,l⟩ := b
  change i = j at hi; subst j
  simp only [mem_keys] at ha hb
  rw [pull_want, pull_want]
  fin_cases k <;> fin_cases l <;> simp_all (config := {decide := true})
private theorem fdPair {I M : Finset ℕ} {a : Key} (ha : a ∈ keys I M) (hu : a.1 ∉ M) :
    ∃ b ∈ keys I M, a.1 = b.1 ∧ a ≠ b ∧
      ∀ d ∈ keys I M, d.1 = a.1 → d = a ∨ d = b := by
  obtain ⟨i,k⟩ := a
  change i ∉ M at hu
  let b : Key := (i, if k = 0 then 1 else 0)
  have ha' := mem_keys.mp ha
  simp [hu] at ha'
  refine ⟨b, ?_, rfl, ?_, ?_⟩
  · fin_cases k <;> simp_all [b, mem_keys]
  · fin_cases k <;> simp_all [b]
  · rintro ⟨j,l⟩ hd hij
    change j = i at hij
    subst j
    have hd' := mem_keys.mp hd
    simp [hu] at hd'
    fin_cases k <;> fin_cases l <;> simp_all [b]

private theorem fdSplitPool (K : Finset Key) (b : Key) :
    pool K ⊆ pool (K.erase b) ∪ {atom b} := by
  rintro _ ⟨d,hd,rfl⟩
  by_cases he : d = b
  · exact Or.inr (by simp [he])
  · exact Or.inl ⟨d, Finset.mem_erase.mpr ⟨he, hd⟩, rfl⟩

theorem finish_drop {s t : ℕ} {I M : Finset ℕ} (hn : 3 ≤ I.card) (hM : M ⊆ I) {a : Key} (ha : a ∈ keys I M)
    (budget : t + 2 ≤ s) (h : Run t (pool ((keys I M).erase a)) (pull (dropKey a) (want I I)))
    (ih : ∀ {v : ℕ} {J B : Finset ℕ}, v < s → B ⊆ J → Run v (pool (keys J B)) (want J J) → 3 * J.card ≤ v+3+B.card) :
    3 * I.card ≤ s+3+M.card := by
  have hc := Finset.card_erase_add_one (mem_keys.mp ha).1
  have hsub := Finset.erase_subset_erase a.1 hM
  by_cases hm : a.1 ∈ M
  · have ha2 : a.2 = 2 := by simpa [hm] using (mem_keys.mp ha).2
    have hf : pull (dropKey a) (want I I) = want (I.erase a.1) (I.erase a.1) := by
      simp [pull_want, ha2]
    rw [hf] at h
    have hsmall : Run t (pool (keys (I.erase a.1) (M.erase a.1))) (want (I.erase a.1) (I.erase a.1)) := by
      apply run_remove h
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨hne, hd⟩ := Finset.mem_erase.mp hd
      refine ⟨d, reduced_key hd ?_, rfl⟩
      intro hi
      apply hne (Prod.ext hi ?_)
      simpa [hi, hm, ha2] using (mem_keys.mp hd).2
    have := ih (by omega : t < s) hsub hsmall
    have := Finset.card_erase_add_one hm
    omega
  · obtain ⟨b, hb, hi, hab, hpair⟩ := fdPair ha hm
    rcases cut_or (run_remove h (fdSplitPool _ b)) with hbad | ⟨u, hu, hcut⟩
    · exact False.elim (half_essential (by omega) ha hb hi hab (run_sep hbad))
    · have he := Set.mem_singleton_iff.mp hu
      subst u
      have hf := after_both ha hb hi hab
      have hnz : pull (dropKey b) (pull (dropKey a) (want I I)) ≠ (fun _ => false) := by
        rw [hf]
        exact nonzero_want (J := I.erase a.1) (by omega) (Finset.Subset.refl _) (Finset.Subset.refl _)
      obtain ⟨v, hv, hrest⟩ := hcut (dropKey b) (pull_atom_self b) hnz
      rw [hf] at hrest
      have hsmall : Run v (pool (keys (I.erase a.1) (M.erase a.1))) (want (I.erase a.1) (I.erase a.1)) := by
        apply run_weaken _ hrest
        rintro _ ⟨w, hw, rfl⟩
        rcases hw with ⟨d, hd, rfl⟩ | hw
        · obtain ⟨hdb, hd⟩ := Finset.mem_erase.mp hd
          obtain ⟨hda, hd⟩ := Finset.mem_erase.mp hd
          rw [pull_atom_other hb hd (Ne.symm hdb)]
          apply Or.inl
          exact ⟨d, reduced_key hd (fun e => (hpair d hd e).elim hda hdb), rfl⟩
        · obtain rfl := Set.mem_singleton_iff.mp hw
          exact Or.inr (Or.inl (pull_atom_self b))
      have hrec := ih (by omega : v < s) hsub hsmall
      rw [Finset.erase_eq_of_notMem hm] at hrec
      omega

private theorem foMerge {I M : Finset ℕ} {a b : Key} (ha : a ∈ keys I M)
    (hb : b ∈ keys I M) (hne : a ≠ b) (hi : a.1 = b.1) :
    a.1 ∉ M ∧ insert (gate true (atom a) (atom b)) (pool (((keys I M).erase a).erase b)) ⊆
      pool (keys I (insert a.1 M)) := by
  obtain ⟨i,k⟩ := a
  obtain ⟨j,l⟩ := b
  change i = j at hi
  subst j
  have hkl : k ≠ l := by rintro rfl; exact hne rfl
  obtain ⟨hiI, hk⟩ := mem_keys.mp ha
  obtain ⟨_, hl⟩ := mem_keys.mp hb
  change (if i ∈ M then k = 2 else k ≠ 2) at hk
  change (if i ∈ M then l = 2 else l ≠ 2) at hl
  have hm : i ∉ M := by
    intro h
    simp [h] at hk hl
    exact hkl (hk.trans hl.symm)
  simp [hm] at hk hl
  have hp : (k = 0 ∧ l = 1) ∨ (k = 1 ∧ l = 0) := by omega
  have hg : gate true (atom (i,k)) (atom (i,l)) = atom (i,2) := by
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> funext p <;> simp [gate, atom, Bool.or_comm]
  refine ⟨hm, ?_⟩
  rintro w (rfl | ⟨⟨j,z⟩, hz, rfl⟩)
  · exact ⟨(i,2), mem_keys.mpr ⟨hiI, by simp⟩, hg.symm⟩
  · obtain ⟨hzl, hz'⟩ := Finset.mem_erase.mp hz
    obtain ⟨hzk, hmem⟩ := Finset.mem_erase.mp hz'
    refine ⟨(j,z), ?_, rfl⟩
    by_cases hji : j = i
    · subst j
      have hn1 : z ≠ k := by rintro rfl; exact hzk rfl
      have hn2 : z ≠ l := by rintro rfl; exact hzl rfl
      have hz2 : z = 2 := by omega
      exact mem_keys.mpr ⟨hiI, by simp [hz2]⟩
    · simpa [mem_keys, hji] using hmem

private theorem foSplit {I M : Finset ℕ} {a b : Key} (ha : a ∈ keys I M)
    (hb : b ∈ keys I M) (g : Sig) :
    insert g (pool (((keys I M).erase a).erase b)) ∪ {atom a, atom b} =
      insert g (pool (keys I M)) := by
  ext w
  constructor
  · rintro ((hw | ⟨d,hd,rfl⟩) | (rfl | hw))
    · exact Or.inl hw
    · exact Or.inr ⟨d, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd), rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
    · exact Or.inr ⟨b, hb, (Set.mem_singleton_iff.mp hw).symm⟩
  · rintro (hw | ⟨d,hd,rfl⟩)
    · exact Or.inl (Or.inl hw)
    · by_cases hda : d = a
      · subst d; exact Or.inr (Or.inl rfl)
      by_cases hdb : d = b
      · subst d; exact Or.inr (Or.inr rfl)
      · exact Or.inl (Or.inr ⟨d, Finset.mem_erase.mpr ⟨hdb, Finset.mem_erase.mpr ⟨hda,hd⟩⟩, rfl⟩)

private theorem foPullOr (ρ : Grid → Grid) (u v : Sig) :
    pull ρ (gate true u v) = (fun p => pull ρ u p || pull ρ v p) := rfl

theorem first_or {t : ℕ} {I M : Finset ℕ} (hn : 3 ≤ I.card) (hM : M ⊆ I) {a b : Key} (ha : a ∈ keys I M) (hb : b ∈ keys I M) (hne : a ≠ b)
    (h : Run t (insert (gate true (atom a) (atom b)) (pool (keys I M))) (want I I))
    (ih : ∀ {v : ℕ} {J B : Finset ℕ}, v < t+1 → B ⊆ J → Run v (pool (keys J B)) (want J J) → 3 * J.card ≤ v+3+B.card) :
    3 * I.card ≤ (t+1)+3+M.card := by
  let g := gate true (atom a) (atom b)
  have he := foSplit ha hb g
  change Run t (insert g (pool (keys I M))) (want I I) at h
  rw [← he] at h
  rcases cut_or h with hr | ⟨u,hu,hc⟩
  · have hi := merge_only ha hb hne (run_sep hr)
    obtain ⟨hm,hsub⟩ := foMerge ha hb hne hi
    have hMI : insert a.1 M ⊆ I := Finset.insert_subset (mem_keys.mp ha).1 hM
    have bound := ih (Nat.lt_succ_self t) hMI (run_remove hr hsub)
    rw [Finset.card_insert_of_notMem hm] at bound
    omega
  · have solveMarked (k : Key) (hk : k ∈ keys I M) (eqk : u = atom k)
        (hg : pull (dropKey k) g ∈ pull (dropKey k) '' pool (keys I M)) :
        3 * I.card ≤ (t+1)+3+M.card := by
      obtain ⟨v,hv,hvRun⟩ := hc (dropKey k) (eqk ▸ pull_atom_self k) (after_one hn hk)
      rw [he] at hvRun
      apply finish_drop hn hM hk (by omega : v+2 ≤ t+1) _ ih
      apply restrict_stock hk
      apply run_remove hvRun
      rintro _ ⟨w, hw, rfl⟩
      rcases Set.mem_insert_iff.mp hw with rfl | hw
      · exact hg
      · exact ⟨w, hw, rfl⟩
    rcases Set.mem_insert_iff.mp hu with e | e
    · apply solveMarked a ha e
      refine ⟨atom b, ⟨b, hb, rfl⟩, ?_⟩
      simp only [g, foPullOr, pull_atom_self, Bool.false_or]
    · apply solveMarked b hb (Set.mem_singleton_iff.mp e)
      refine ⟨atom a, ⟨a, ha, rfl⟩, ?_⟩
      simp only [g, foPullOr, pull_atom_self, Bool.or_false]

theorem first_and {t : ℕ} {I M : Finset ℕ} (hn : 3 ≤ I.card) (hM : M ⊆ I) {a b : Key} (ha : a ∈ keys I M) (hb : b ∈ keys I M) (hne : a ≠ b)
    (h : Run t (insert (gate false (atom a) (atom b)) (pool (keys I M))) (want I I))
    (ih : ∀ {v : ℕ} {J B : Finset ℕ}, v < t+1 → B ⊆ J → Run v (pool (keys J B)) (want J J) → 3 * J.card ≤ v+3+B.card) :
    3 * I.card ≤ (t+1)+3+M.card := by
  let P := pool ((keys I M).erase a)
  let H : Set Sig := {atom a, gate false (atom a) (atom b)}
  have hz : ∀ u ∈ H, pull (dropKey a) u = (fun _ => false) := by
    intro u hu
    rcases (show u = atom a ∨ u = gate false (atom a) (atom b) from hu) with rfl | rfl
    · exact pull_atom_self a
    · funext p
      have hap := congrFun (pull_atom_self a) p
      change atom a (dropKey a p) = false at hap
      change (atom a (dropKey a p) && atom b (dropKey a p)) = false
      simp [hap]
  have h' : Run t (P ∪ H) (want I I) := by
    apply run_remove h
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl | ⟨k,hk,rfl⟩
    · exact Or.inr (by simp [H])
    · by_cases hka : k = a
      · subst k; exact Or.inr (by simp [H])
      · exact Or.inl ⟨k, Finset.mem_erase.mpr ⟨hka,hk⟩, rfl⟩
  rcases cut_or h' with hskip | ⟨u, hu, hcut⟩
  · exact (key_essential (by omega) ha (run_sep hskip)).elim
  obtain ⟨v, hv, hr⟩ := hcut (dropKey a) (hz u hu) (after_one hn ha)
  apply finish_drop hn hM ha (by omega : v+2 ≤ t+1) _ ih
  apply run_weaken _ hr
  rintro _ ⟨w, hw, rfl⟩
  rcases hw with ⟨k, hk, rfl⟩ | hw
  · have hek := Finset.mem_erase.mp hk
    rw [pull_atom_other ha hek.2 (Ne.symm hek.1)]
    exact Or.inl ⟨k, hk, rfl⟩
  · exact Or.inr (Or.inl (hz w hw))

theorem invariant {s : ℕ} {I M : Finset ℕ} (hM : M ⊆ I)
    (h : Run s (pool (keys I M)) (want I I)) : 3 * I.card ≤ s + 3 + M.card := by
  induction s using Nat.strong_induction_on generalizing I M with
  | ind s ih =>
    by_cases hsmall : I.card ≤ 1
    · omega
    have htwo : 2 ≤ I.card := by omega
    by_cases hthree : 3 ≤ I.card
    · cases s with
      | zero =>
        have := basic_bound htwo hM h
        have := Finset.card_le_card hM
        omega
      | succ t =>
        have next : ∀ {v : ℕ} {J B : Finset ℕ}, v < t+1 → B ⊆ J →
            Run v (pool (keys J B)) (want J J) → 3 * J.card ≤ v+3+B.card :=
          fun {v _ _} hv hsub hr => ih v hv hsub hr
        rcases h with h | ⟨_, ⟨a,ha,rfl⟩, _, ⟨b,hb,rfl⟩, op, h⟩
        · have := next (Nat.lt_succ_self _) hM h
          omega
        by_cases e : a = b
        · subst b
          have hg : gate op (atom a) (atom a) = atom a := by
            funext p; cases op <;> simp [gate]
          rw [hg, Set.insert_eq_of_mem (show atom a ∈ pool (keys I M) from ⟨a,ha,rfl⟩)] at h
          have := next (Nat.lt_succ_self _) hM h
          omega
        cases op
        · exact first_and hthree hM ha hb e h next
        · exact first_or hthree hM ha hb e h next
    · have := basic_bound htwo hM h
      omega

end PEqualNP.Outside.L_meta_7626

theorem PEqualNP.Outside.L_meta_7626 : ∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → 3 * n ≤ s + 3 := by
  intro n s h
  have := PEqualNP.Outside.L_meta_7626.invariant (Finset.empty_subset _) (PEqualNP.Outside.L_meta_7626.run_of_rep h)
  simpa using this
