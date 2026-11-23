import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1376

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons, step, List.length_append, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]; simp
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

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]; simp
  rw [List.getD_eq_default _ _ (by omega)]

lemma prefix_keep (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def sigVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr i => w.getD i false

def sigBounded (lim : ℕ) : Bool ⊕ ℕ → Prop
  | .inl _ => True
  | .inr i => i < lim

def normBin (isAnd : Bool) (next : ℕ) : Bool ⊕ ℕ → Bool ⊕ ℕ → (Bool ⊕ ℕ) × List Gate
  | .inl a, .inl b => (.inl (if isAnd then a && b else a || b), [])
  | .inl a, .inr b => if a == isAnd then (.inr b, []) else (.inl a, [])
  | .inr a, .inl b => if b == isAnd then (.inr a, []) else (.inl b, [])
  | .inr a, .inr b => (.inr next, [⟨if isAnd then GateOp.and else GateOp.or, [a, b]⟩])

def normGate (isAnd : Bool) (next : ℕ) : List (Bool ⊕ ℕ) → (Bool ⊕ ℕ) × List Gate
  | [] => (.inl isAnd, [])
  | [a] => (a, [])
  | a :: b :: _ => normBin isAnd next a b

def monoGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma normBin_ok (isAnd : Bool) (w : List Bool) (a b : Bool ⊕ ℕ)
    (ha : sigBounded w.length a) (hb : sigBounded w.length b) :
    let r := normBin isAnd w.length a b
    let w' := r.2.foldl step w
    r.2.length ≤ (if a.isLeft ∨ b.isLeft then 0 else 1) ∧
    (∀ g ∈ r.2, monoGate g) ∧
    sigBounded w'.length r.1 ∧
    sigVal w' r.1 = if isAnd then sigVal w a && sigVal w b else sigVal w a || sigVal w b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => cases isAnd <;> simp [normBin, sigVal, sigBounded]
    | inr b => cases isAnd <;> cases a <;> simp [normBin, sigVal, sigBounded] at ha hb ⊢ <;> assumption
  | inr a =>
    cases b with
    | inl b => cases isAnd <;> cases b <;> simp [normBin, sigVal, sigBounded] at ha hb ⊢ <;> assumption
    | inr b =>
      cases isAnd <;> simp [normBin, monoGate, sigBounded, sigVal, step, GateOp.eval]

lemma normGate_ok (isAnd : Bool) (w : List Bool) (s : List (Bool ⊕ ℕ))
    (hs : s.length ≤ 2) (hb : ∀ a ∈ s, sigBounded w.length a) :
    let r := normGate isAnd w.length s
    let w' := r.2.foldl step w
    r.2.length ≤ (if ∃ a ∈ s, a.isLeft then 0 else 1) ∧
    (∀ g ∈ r.2, monoGate g) ∧
    sigBounded w'.length r.1 ∧
    sigVal w' r.1 = (if isAnd then GateOp.and else GateOp.or).eval (s.map (sigVal w)) := by
  rcases s with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · cases isAnd <;> simp [normGate, sigVal, GateOp.eval, sigBounded]
  · cases isAnd <;> simpa [normGate, GateOp.eval] using hb a (by simp)
  · have h := normBin_ok isAnd w a b (hb a (by simp)) (hb b (by simp))
    have hcond : (∃ x ∈ [a, b], x.isLeft) ↔ (a.isLeft ∨ b.isLeft) := by simp
    cases isAnd <;> simpa [normGate, GateOp.eval, hcond] using h
  · simp at hs

def elimStep (n jIdx : ℕ) (idx : ℕ) (g : Gate)
    (status : List (Bool ⊕ ℕ)) (done : List Gate) : List (Bool ⊕ ℕ) × List Gate :=
  if idx = jIdx then
    (status ++ [.inl true], done)
  else
    let sig := g.inputs.map (fun i => status.getD i (.inl false))
    let isAnd := match g.op with | .and => true | _ => false
    let r := normGate isAnd (n + done.length) sig
    (status ++ [r.1], done ++ r.2)

def elimLoop (n jIdx : ℕ) : ℕ → List Gate → List (Bool ⊕ ℕ) → List Gate →
    List (Bool ⊕ ℕ) × List Gate
  | _, [], status, done => (status, done)
  | idx, g :: gs, status, done =>
    let next := elimStep n jIdx idx g status done
    elimLoop n jIdx (idx + 1) gs next.1 next.2

lemma status_read (status : List (Bool ⊕ ℕ)) (w : List Bool) (i : ℕ) :
    (status.map (sigVal w)).getD i false = sigVal w (status.getD i (.inl false)) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases status[i]? <;> rfl

def dGate : Gate := ⟨GateOp.or, []⟩

lemma elimLoop_ok (n jIdx : ℕ) :
    ∀ (idx : ℕ) (gs : List Gate) (status : List (Bool ⊕ ℕ)) (done : List Gate)
      (hstatLen : status.length = n + idx)
      (hstatJ : jIdx < idx → status[n + jIdx]? = some (.inl true))
      (hbound : ∀ a ∈ status, sigBounded (n + done.length) a)
      (hdone : ∀ g ∈ done, monoGate g)
      (hgs : ∀ k (hk : k < gs.length),
        idx + k ≠ jIdx → monoGate gs[k]),
      let res := elimLoop n jIdx idx gs status done
      res.2.length +
        ((Finset.range gs.length).filter (fun k =>
          idx + k = jIdx ∨ (jIdx < idx + k ∧ n + jIdx ∈ (gs.getD k dGate).inputs))).card
          ≤ done.length + gs.length ∧
      (∀ g ∈ res.2, monoGate g) ∧
      ∀ (x : Fin n → Bool) (origW : List Bool),
        origW = status.map (sigVal (done.foldl step (List.ofFn x))) →
        (∀ k (hk : k < gs.length), idx + k = jIdx →
          (gs.foldl step origW).getD (n + jIdx) false = true) →
        res.1.map (sigVal (res.2.foldl step (List.ofFn x))) = gs.foldl step origW := by
  intro idx gs
  induction gs generalizing idx with
  | nil =>
    intro status done _ _ _ hdone _
    refine ⟨by simp [elimLoop], hdone, ?_⟩
    intro x origW horig _
    simpa [elimLoop] using horig.symm
  | cons g gs ih =>
    intro status done hstatLen hstatJ hbound hdone hgs
    by_cases hidx : idx = jIdx
    · subst hidx
      have hstatLen' : (status ++ [Sum.inl true]).length = n + (idx + 1) := by
        simp [hstatLen]; omega
      have hstatJ' : idx < idx + 1 → (status ++ [Sum.inl true])[n + idx]? = some (.inl true) := by
        intro _
        rw [List.getElem?_append_right (by omega)]
        simp [hstatLen]
      have hbound' : ∀ a ∈ status ++ [Sum.inl true], sigBounded (n + done.length) a := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hbound a ha
        · simp at ha; subst ha; trivial
      have hgs' : ∀ k (hk : k < gs.length), idx + 1 + k ≠ idx → monoGate gs[k] := by
        intro k hk hne
        have := hgs (k + 1) (by simp; omega) (by omega)
        simpa using this
      obtain ⟨hcard, hmono, heval⟩ := ih (idx + 1) (status ++ [.inl true]) done
        hstatLen' hstatJ' hbound' hdone hgs'
      have hstepEq : elimLoop n idx idx (g :: gs) status done =
          elimLoop n idx (idx + 1) gs (status ++ [.inl true]) done := by
        simp [elimLoop, elimStep]
      rw [hstepEq]
      refine ⟨?_, hmono, ?_⟩
      · have hfilt : ((Finset.range (g :: gs).length).filter (fun k =>
            idx + k = idx ∨ (idx < idx + k ∧ n + idx ∈ ((g :: gs).getD k dGate).inputs))).card =
            1 + ((Finset.range gs.length).filter (fun k =>
              idx + 1 + k = idx ∨ (idx < idx + 1 + k ∧ n + idx ∈ (gs.getD k dGate).inputs))).card := by
          have hbij : ((Finset.range (g :: gs).length).filter (fun k =>
              idx + k = idx ∨ (idx < idx + k ∧ n + idx ∈ ((g :: gs).getD k dGate).inputs))) =
              insert 0 (((Finset.range gs.length).filter (fun k =>
                idx + 1 + k = idx ∨ (idx < idx + 1 + k ∧ n + idx ∈ (gs.getD k dGate).inputs))).image (· + 1)) := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image,
              List.length_cons]
            constructor
            · rintro ⟨hk, hcond⟩
              cases k with
              | zero => exact Or.inl rfl
              | succ k =>
                right
                refine ⟨k, ⟨by omega, ?_⟩, rfl⟩
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcond
            · rintro (rfl | ⟨k, ⟨hk, hcond⟩, rfl⟩)
              · exact ⟨by omega, Or.inl (by omega)⟩
              · refine ⟨by omega, ?_⟩
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcond
          rw [hbij, Finset.card_insert_of_notMem (by simp),
            Finset.card_image_of_injective _ (fun a b h => by omega)]
          omega
        rw [hfilt, List.length_cons]
        omega
      · intro x origW horig hnotTrue
        have htrue : (step origW g).getD (n + idx) false = true := by
          have h1 := hnotTrue 0 (by simp) (by omega)
          simp only [List.foldl_cons] at h1
          have hlen1 : (step origW g).length = n + idx + 1 := by
            simp [step, horig, hstatLen]
          rw [prefix_keep gs (step origW g) (by omega)] at h1
          exact h1
        have hstepW : (status ++ [Sum.inl true]).map (sigVal (done.foldl step (List.ofFn x))) =
            step origW g := by
          simp only [List.map_append, List.map_cons, List.map_nil, sigVal, ← horig, step]
          congr 1
          have hlen0 : origW.length = n + idx := by simp [horig, hstatLen]
          have hget : (step origW g).getD (n + idx) false =
              g.op.eval (g.inputs.map fun i => origW.getD i false) := by
            simp [step, ← hlen0]
          rw [← hget, htrue]
        simp only [List.foldl_cons]
        exact heval x (step origW g) hstepW.symm (fun k hk h => by omega)
    · have hgMono : monoGate g := by
        have := hgs 0 (by simp) (by omega)
        simpa using this
      let sig := g.inputs.map (fun i => status.getD i (.inl false))
      let isAnd := match g.op with | .and => true | _ => false
      let r := normGate isAnd (n + done.length) sig
      have hstepEq : elimLoop n jIdx idx (g :: gs) status done =
          elimLoop n jIdx (idx + 1) gs (status ++ [r.1]) (done ++ r.2) := by
        simp [elimLoop, elimStep, hidx, sig, isAnd, r]
      rw [hstepEq]
      have hsigBound : ∀ a ∈ sig, sigBounded (n + done.length) a := by
        intro a ha
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        rw [List.getD_eq_getElem?_getD]
        cases hsi : status[i]? with
        | none => trivial
        | some u => exact hbound u (List.mem_of_getElem? hsi)
      have hsigLen : sig.length ≤ 2 := by simpa [sig] using hgMono.2
      have hng0 := normGate_ok isAnd (done.foldl step (List.ofFn (fun _ : Fin n => false)))
        sig hsigLen (by simpa [fold_length] using hsigBound)
      have hlen0 : (done.foldl step (List.ofFn (fun _ : Fin n => false))).length = n + done.length := by
        rw [fold_length]; simp
      rw [hlen0] at hng0
      obtain ⟨hrLen, hrMono, hrBound, _⟩ := hng0
      change r.2.length ≤ _ at hrLen
      have hstatLen' : (status ++ [r.1]).length = n + (idx + 1) := by
        simp [hstatLen]; omega
      have hstatJ' : jIdx < idx + 1 → (status ++ [r.1])[n + jIdx]? = some (.inl true) := by
        intro hlt
        have hlt' : jIdx < idx := by omega
        rw [List.getElem?_append_left (by omega)]
        exact hstatJ hlt'
      have hbound' : ∀ a ∈ status ++ [r.1], sigBounded (n + (done ++ r.2).length) a := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · cases a with
          | inl _ => trivial
          | inr i =>
            have hi : i < n + done.length := hbound (.inr i) ha
            simp [sigBounded]; omega
        · simp only [List.mem_singleton] at ha
          subst ha
          simpa [sigBounded, fold_length, List.length_append, Nat.add_assoc] using hrBound
      have hdone' : ∀ h ∈ done ++ r.2, monoGate h := by
        intro h hh
        exact (List.mem_append.mp hh).elim (hdone h) (hrMono h)
      have hgs' : ∀ k (hk : k < gs.length), idx + 1 + k ≠ jIdx → monoGate gs[k] := by
        intro k hk hne
        have := hgs (k + 1) (by simp; omega) (by omega)
        simpa using this
      obtain ⟨hcard, hmono, heval⟩ := ih (idx + 1) (status ++ [r.1]) (done ++ r.2)
        hstatLen' hstatJ' hbound' hdone' hgs'
      refine ⟨?_, hmono, ?_⟩
      · have hfilt0 : ((Finset.range (g :: gs).length).filter (fun k =>
            idx + k = jIdx ∨ (jIdx < idx + k ∧ n + jIdx ∈ ((g :: gs).getD k dGate).inputs))).card =
            (if jIdx < idx ∧ n + jIdx ∈ g.inputs then 1 else 0) +
            ((Finset.range gs.length).filter (fun k =>
              idx + 1 + k = jIdx ∨ (jIdx < idx + 1 + k ∧ n + jIdx ∈ (gs.getD k dGate).inputs))).card := by
          by_cases h0 : jIdx < idx ∧ n + jIdx ∈ g.inputs
          · rw [if_pos h0]
            have hbij : ((Finset.range (g :: gs).length).filter (fun k =>
                idx + k = jIdx ∨ (jIdx < idx + k ∧ n + jIdx ∈ ((g :: gs).getD k dGate).inputs))) =
                insert 0 (((Finset.range gs.length).filter (fun k =>
                  idx + 1 + k = jIdx ∨ (jIdx < idx + 1 + k ∧ n + jIdx ∈ (gs.getD k dGate).inputs))).image (· + 1)) := by
              ext k
              simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image,
                List.length_cons]
              constructor
              · rintro ⟨hk, hcond⟩
                cases k with
                | zero => exact Or.inl rfl
                | succ k =>
                  right
                  refine ⟨k, ⟨by omega, ?_⟩, rfl⟩
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcond
              · rintro (rfl | ⟨k, ⟨hk, hcond⟩, rfl⟩)
                · exact ⟨by omega, Or.inr (by simpa using h0)⟩
                · refine ⟨by omega, ?_⟩
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcond
            rw [hbij, Finset.card_insert_of_notMem (by simp),
              Finset.card_image_of_injective _ (fun a b h => by omega)]
            omega
          · rw [if_neg h0, Nat.zero_add]
            have hbij : ((Finset.range (g :: gs).length).filter (fun k =>
                idx + k = jIdx ∨ (jIdx < idx + k ∧ n + jIdx ∈ ((g :: gs).getD k dGate).inputs))) =
                ((Finset.range gs.length).filter (fun k =>
                  idx + 1 + k = jIdx ∨ (jIdx < idx + 1 + k ∧ n + jIdx ∈ (gs.getD k dGate).inputs))).image (· + 1) := by
              ext k
              simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, List.length_cons]
              constructor
              · rintro ⟨hk, hcond⟩
                cases k with
                | zero =>
                  rcases hcond with heq | hmem
                  · exact absurd (by omega) hidx
                  · exact absurd (by simpa using hmem) h0
                | succ k =>
                  refine ⟨k, ⟨by omega, ?_⟩, rfl⟩
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcond
              · rintro ⟨k, ⟨hk, hcond⟩, rfl⟩
                refine ⟨by omega, ?_⟩
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcond
            rw [hbij, Finset.card_image_of_injective _ (fun a b h => by omega)]
        have hr0 : (jIdx < idx ∧ n + jIdx ∈ g.inputs) → r.2.length = 0 := by
          intro h0
          have hmem : status.getD (n + jIdx) (.inl false) ∈ sig :=
            List.mem_map.mpr ⟨n + jIdx, h0.2, rfl⟩
          have hleft : (status.getD (n + jIdx) (.inl false)).isLeft := by
            rw [List.getD_eq_getElem?_getD, hstatJ h0.1]
            rfl
          have hex : ∃ a ∈ sig, a.isLeft := ⟨_, hmem, hleft⟩
          rw [if_pos hex] at hrLen
          omega
        rw [hfilt0, List.length_cons]
        rw [List.length_append] at hcard
        by_cases h0 : jIdx < idx ∧ n + jIdx ∈ g.inputs
        · have hr0' : r.2.length = 0 := hr0 h0
          rw [if_pos h0] at *
          omega
        · rw [if_neg h0]
          have : r.2.length ≤ 1 := by split_ifs at hrLen <;> omega
          omega
      · intro x origW horig hnotTrue
        let wx := done.foldl step (List.ofFn x)
        have hwxLen : wx.length = n + done.length := by rw [fold_length]; simp
        have hngx := normGate_ok isAnd wx sig hsigLen (by simpa [hwxLen] using hsigBound)
        rw [hwxLen] at hngx
        obtain ⟨_, _, _, hrVal⟩ := hngx
        have hop : (if isAnd then GateOp.and else GateOp.or) = g.op := by
          rcases hgMono.1 with h | h <;> simp [isAnd, h]
        have hmapKeep : status.map (sigVal (r.2.foldl step wx)) = status.map (sigVal wx) := by
          apply List.map_congr_left
          intro a ha
          cases a with
          | inl _ => rfl
          | inr i => exact prefix_keep r.2 wx (hwxLen ▸ hbound (.inr i) ha)
        have hreads : sig.map (sigVal wx) = g.inputs.map (fun i => origW.getD i false) := by
          simp only [sig, List.map_map, Function.comp_def, horig, ← status_read]
          rfl
        have hstepW : (status ++ [r.1]).map (sigVal ((done ++ r.2).foldl step (List.ofFn x))) =
            step origW g := by
          simp only [List.foldl_append, List.map_append, List.map_cons, List.map_nil]
          change status.map (sigVal (r.2.foldl step wx)) ++ [sigVal (r.2.foldl step wx) r.1] = _
          rw [hmapKeep, ← horig, hrVal, hop, hreads]
          rfl
        simp only [List.foldl_cons]
        exact heval x (step origW g) hstepW.symm (fun k hk heq => by
          have := hnotTrue (k + 1) (by simp; omega) (by omega)
          simpa only [List.foldl_cons] using this)

lemma elim_not_gate {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j) :
    ∃ (gs' : List Gate) (σ : ℕ → Bool ⊕ ℕ),
      gs'.length + (Finset.univ.filter (fun i : Fin gates.length =>
          j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length ∧
      (∀ g ∈ gs', monoGate g) ∧
      ∀ (x : Fin n → Bool), val gates x (n + j.val) = true →
        ∀ a : ℕ, sigVal (gs'.foldl step (List.ofFn x)) (σ a) = val gates x a := by
  let initStatus : List (Bool ⊕ ℕ) := (List.range n).map Sum.inr
  have hgs : ∀ k (hk : k < gates.length), 0 + k ≠ j.val → monoGate gates[k] := by
    intro k hk hne
    have h1 := hG gates[k] (List.getElem_mem hk)
    refine ⟨?_, h1.2⟩
    rcases h1.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have heq : k = j.val := congrArg Fin.val (huniq ⟨k, hk⟩ (by simpa using h))
      omega
  have hbound : ∀ a ∈ initStatus, sigBounded (n + ([] : List Gate).length) a := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    simpa [sigBounded] using List.mem_range.mp hi
  obtain ⟨hcard, hmono, heval⟩ := elimLoop_ok n j.val 0 gates initStatus []
    (by simp [initStatus]) (fun h => by omega) hbound (by simp) hgs
  let res := elimLoop n j.val 0 gates initStatus []
  refine ⟨res.2, fun a => res.1.getD a (.inl false), ?_, hmono, ?_⟩
  · have hfiltEq : ((Finset.range gates.length).filter (fun k =>
        0 + k = j.val ∨ (j.val < 0 + k ∧ n + j.val ∈ (gates.getD k dGate).inputs))).card =
        (Finset.univ.filter (fun i : Fin gates.length =>
          j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 1 := by
      have hbij : ((Finset.range gates.length).filter (fun k =>
          0 + k = j.val ∨ (j.val < 0 + k ∧ n + j.val ∈ (gates.getD k dGate).inputs))) =
          insert j.val ((Finset.univ.filter (fun i : Fin gates.length =>
            j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).image Fin.val) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image,
          Finset.mem_univ, true_and, Nat.zero_add]
        constructor
        · rintro ⟨hk, rfl | ⟨hlt, hmem⟩⟩
          · exact Or.inl rfl
          · right
            refine ⟨⟨k, hk⟩, ⟨hlt, ?_⟩, rfl⟩
            have : gates.getD k dGate = gates.get ⟨k, hk⟩ := by
              simp [hk]
            rwa [← this]
        · rintro (rfl | ⟨i, ⟨hlt, hmem⟩, rfl⟩)
          · exact ⟨j.isLt, Or.inl rfl⟩
          · refine ⟨i.isLt, Or.inr ⟨hlt, ?_⟩⟩
            have : gates.getD i.val dGate = gates.get i := by
              simp [i.isLt]
            rwa [this]
      rw [hbij, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
          not_and]
        intro i hi heq
        have : j.val < i.val := hi.1
        omega), Finset.card_image_of_injective _ Fin.val_injective]
    rw [hfiltEq] at hcard
    simp only [List.length_nil, Nat.zero_add] at hcard
    omega
  · intro x htrue a
    have hinit : List.ofFn x = initStatus.map (sigVal (([] : List Gate).foldl step (List.ofFn x))) := by
      apply List.ext_getElem
      · simp [initStatus]
      · intro i hi1 hi2
        simp only [List.length_ofFn] at hi1
        simp [initStatus, sigVal, List.getD_eq_getElem?_getD, hi1]
    have hres := heval x (List.ofFn x) hinit (fun k hk heq => by simpa [val] using htrue)
    rw [← status_read, hres]
    rfl

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

lemma gate_cases {X : Type} (g : Gate) (hg : monoGate g) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right; exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left; simp [GateOp.eval]
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

def Inv {n : ℕ} (Z T : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i, val gs (Zof Z) i = false →
    ∀ u ∈ T, ∀ v ∈ T, val gs (eof u) i = true → val gs (eof v) i = true → l u = l v

lemma val_mono_eof {n : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs, monoGate g)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (i : ℕ) :
    val gs x i = true → val gs y i = true := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    rw [val_nil, val_nil]
    split_ifs with h
    · exact hxy ⟨i, h⟩
    · simp
  | append_singleton gs g ih =>
    rw [val_snoc, val_snoc]
    have hg0 := hg g (by simp)
    have hgs : ∀ g' ∈ gs, monoGate g' := fun g' h' => hg g' (by simp [h'])
    split_ifs with h
    · rcases hg0.1 with hop | hop
      · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
        intro hx b hb
        obtain ⟨k, hk, rfl⟩ := hb
        exact ih hgs k (hx _ ⟨k, hk, rfl⟩)
      · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        rintro ⟨b, ⟨k, hk, rfl⟩, hv⟩
        exact ⟨_, ⟨k, hk, rfl⟩, ih hgs k hv⟩
    · exact ih hgs i

lemma mem_of_zof_false {n : ℕ} (Z : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, monoGate g) (i : ℕ) (hz : val gs (Zof Z) i = false)
    (u : Fin n) (hu : val gs (eof u) i = true) : u ∈ Z := by
  by_contra hnot
  have h1 := val_mono_eof gs hg (eof u) (Zof Z) (fun p hp => by
    have : p = u := of_decide_eq_true hp
    subst this
    simp [Zof, hnot]) i hu
  rw [hz] at h1
  cases h1

def supp {n : ℕ} (gs : List Gate) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => val gs (eof p) i = true)

lemma mem_supp {n : ℕ} (gs : List Gate) (i : ℕ) (p : Fin n) :
    p ∈ supp gs i ↔ val gs (eof p) i = true := by
  simp [supp]

def IsBridge {n : ℕ} (S R : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof (S ∪ R)) i = false ∧
  supp gs i ⊆ S ∧
  (supp gs i ∩ (S ∩ R)).Nonempty ∧
  (supp gs i ∩ (S \ R)).Nonempty

lemma bridge_gate {n : ℕ} (S R : Finset (Fin n)) (gs : List Gate) (i : ℕ)
    (hb : IsBridge S R gs i) : n ≤ i ∧ i < n + gs.length := by
  obtain ⟨_, _, ⟨p, hp⟩, ⟨u, hu⟩⟩ := hb
  have hpu : p ≠ u := by
    intro h; subst h
    have h1 := (Finset.mem_inter.mp hp).2
    have h2 := (Finset.mem_inter.mp hu).2
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
  have hvp : val gs (eof p) i = true := (mem_supp gs i p).mp (Finset.mem_inter.mp hp).1
  have hvu : val gs (eof u) i = true := (mem_supp gs i u).mp (Finset.mem_inter.mp hu).1
  constructor
  · by_contra hlt
    have hi : i < n := by omega
    have hge : ∀ x : Fin n → Bool, val gs x i = x ⟨i, hi⟩ := by
      intro x
      unfold val
      rw [prefix_keep gs (List.ofFn x) (by simp [hi]),
        List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
    rw [hge] at hvp hvu
    simp only [eof, decide_eq_true_eq] at hvp hvu
    exact hpu (hvp.symm.trans hvu)
  · by_contra hge
    rw [val_ge gs (eof p) i (by omega)] at hvp
    cases hvp

lemma main_inv {n : ℕ} (S R : Finset (Fin n)) (Z T : Finset (Fin n))
    (gs : List Gate) (hg : ∀ g ∈ gs, monoGate g) :
    ∃ (l : Fin n → Fin n) (M : Finset ℕ),
      Inv Z T gs l ∧
      T.card ≤ (T.image l).card + M.card ∧
      (∀ i ∈ M, n ≤ i ∧ i < n + gs.length ∧ val gs (Zof Z) i = false ∧
        ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true) ∧
      (Z = S ∪ R → T = S \ R →
        ∀ g0, IsBridge S R gs g0 → (∀ i < g0, ¬ IsBridge S R gs i) → g0 ∉ M) := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ∅, ?_, by simp, by simp, by simp⟩
    intro i hz u _ v _ hu hv
    rw [val_nil] at hu hv
    by_cases h : i < n
    · simp only [dif_pos h, eof, decide_eq_true_eq] at hu hv
      exact hu.symm.trans hv
    · simp [dif_neg h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, M, hinv, hcard, hM, hnoB⟩ := ih (fun g' h' => hg g' (by simp [h']))
    obtain hg0 := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun k => val gs x k) with hP
    have hnew : ∀ x, val (gs ++ [g]) x N = P x := fun x => by rw [val_snoc, if_pos hN]
    have hold : ∀ x i, i ≠ N → val (gs ++ [g]) x i = val gs x i := fun x i hi => by
      rw [val_snoc, if_neg hi]
    have hsupp_old : ∀ i, i ≠ N → @supp n (gs ++ [g]) i = @supp n gs i := by
      intro i hi; ext p; simp [supp, hold _ i hi]
    have hbridge_old : ∀ i, i ≠ N → (IsBridge S R (gs ++ [g]) i ↔ IsBridge S R gs i) := by
      intro i hi
      simp only [IsBridge, hold _ i hi, hsupp_old i hi]
    have key : P (Zof Z) = false →
        (∀ u ∈ T, P (eof u) = false) ∨
        ∃ A B : Fin n → Prop, (∀ w ∈ T, P (eof w) = true → A w ∨ B w) ∧
          (∀ w ∈ T, ∀ w' ∈ T, A w → A w' → l w = l w') ∧
          (∀ w ∈ T, ∀ w' ∈ T, B w → B w' → l w = l w') := by
      intro hz
      rcases gate_cases g hg0 (fun x k => val gs x k) (Zof Z) with hall | ⟨a, b, hab⟩
      · exact Or.inl (fun u _ => hall (eof u))
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine Or.inr ⟨fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w _ hw => hy (eof w) hw,
          fun w hw w' hw' ha1 ha2 => hinv a ha w hw w' hw' ha1 ha2,
          fun w hw w' hw' hb1 hb2 => hinv b hb w hw w' hw' hb1 hb2⟩
    have hbridge_not_merge : Z = S ∪ R → T = S \ R →
        IsBridge S R (gs ++ [g]) N → (∀ i < N, ¬ IsBridge S R (gs ++ [g]) i) →
        ¬ (P (Zof Z) = false ∧ ∃ u ∈ T, ∃ v ∈ T, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v) := by
      intro hZ hT hBN hmin ⟨hz, u, hu, v, hv, hPu, hPv, hne⟩
      subst hZ; subst hT
      have hmin' : ∀ i < N, ¬ IsBridge S R gs i := fun i hi => by
        rw [← hbridge_old i (by omega)]; exact hmin i hi
      obtain ⟨hBz, hBsub, ⟨p0, hp0⟩, _⟩ := hBN
      have hp0_mem : p0 ∈ S ∩ R := (Finset.mem_inter.mp hp0).2
      have hp0_val : P (eof p0) = true := by
        rw [← hnew]; exact (mem_supp _ _ _).mp (Finset.mem_inter.mp hp0).1
      rcases hg0 with ⟨hop, hlen⟩
      obtain ⟨op, ins⟩ := g
      simp only at hop hlen hP
      have hsingle : ∀ a, val gs (Zof (S ∪ R)) a = false →
          (∀ w, P (eof w) = true → val gs (eof w) a = true) → False := by
        intro a ha hcov
        exact hne (hinv a ha u hu v hv (hcov u hPu) (hcov v hPv))
      match ins, hlen with
      | [], _ =>
        rcases hop with rfl | rfl
        · simp [hP, GateOp.eval] at hz
        · simp [hP, GateOp.eval] at hPu
      | [a], _ =>
        rcases hop with rfl | rfl
        · exact hsingle a (by simpa [hP, GateOp.eval] using hz) (fun w hw => by simpa [hP, GateOp.eval] using hw)
        · exact hsingle a (by simpa [hP, GateOp.eval] using hz) (fun w hw => by simpa [hP, GateOp.eval] using hw)
      | [a, b], _ =>
        rcases hop with rfl | rfl
        · simp only [hP, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, Bool.and_eq_false_iff, Bool.and_eq_true] at hz hPu hPv
          rcases hz with ha | hb
          · exact hsingle a ha (fun w hw => by
              simp only [hP, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, Bool.and_eq_true] at hw
              exact hw.1)
          · exact hsingle b hb (fun w hw => by
              simp only [hP, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, Bool.and_eq_true] at hw
              exact hw.2)
        · simp only [hP, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, Bool.or_eq_false_iff, Bool.or_eq_true] at hz hPu hPv hp0_val
          have hsub_a : supp gs a ⊆ S := by
            intro q hq
            apply hBsub
            rw [mem_supp, hnew]
            simp only [hP, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.or_eq_true]
            exact Or.inl ((mem_supp gs a q).mp hq)
          have hsub_b : supp gs b ⊆ S := by
            intro q hq
            apply hBsub
            rw [mem_supp, hnew]
            simp only [hP, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, Bool.or_eq_true]
            exact Or.inr ((mem_supp gs b q).mp hq)
          have hno_both : ∀ c, val gs (Zof (S ∪ R)) c = false → supp gs c ⊆ S →
              (supp gs c ∩ (S ∩ R)).Nonempty → ¬ (supp gs c ∩ (S \ R)).Nonempty := by
            intro c hcz hcsub hcR hcOut
            have hB : IsBridge S R gs c := ⟨hcz, hcsub, hcR, hcOut⟩
            have hlt := (bridge_gate S R gs c hB).2
            exact hmin' c (by omega) hB
          rcases hp0_val with ha0 | hb0
          · have hnoA := hno_both a hz.1 hsub_a ⟨p0, Finset.mem_inter.mpr ⟨(mem_supp gs a p0).mpr ha0, hp0_mem⟩⟩
            have hbu : val gs (eof u) b = true := by
              rcases hPu with hua | hub
              · exact absurd ⟨u, Finset.mem_inter.mpr ⟨(mem_supp gs a u).mpr hua, hu⟩⟩ hnoA
              · exact hub
            have hbv : val gs (eof v) b = true := by
              rcases hPv with hva | hvb
              · exact absurd ⟨v, Finset.mem_inter.mpr ⟨(mem_supp gs a v).mpr hva, hv⟩⟩ hnoA
              · exact hvb
            exact hne (hinv b hz.2 u hu v hv hbu hbv)
          · have hnoB := hno_both b hz.2 hsub_b ⟨p0, Finset.mem_inter.mpr ⟨(mem_supp gs b p0).mpr hb0, hp0_mem⟩⟩
            have hau : val gs (eof u) a = true := by
              rcases hPu with hua | hub
              · exact hua
              · exact absurd ⟨u, Finset.mem_inter.mpr ⟨(mem_supp gs b u).mpr hub, hu⟩⟩ hnoB
            have hav : val gs (eof v) a = true := by
              rcases hPv with hva | hvb
              · exact hva
              · exact absurd ⟨v, Finset.mem_inter.mpr ⟨(mem_supp gs b v).mpr hvb, hv⟩⟩ hnoB
            exact hne (hinv a hz.1 u hu v hv hau hav)
      | _ :: _ :: _ :: _, h => simp at h
    by_cases hm : P (Zof Z) = false ∧ ∃ u ∈ T, ∃ v ∈ T, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, hu0, v0, hv0, hPu0, hPv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, insert N M, ?_, ?_, ?_, ?_⟩
      · intro i hiz u hu v hv hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          rcases key hiz with hall | ⟨A, B, hAB, hA, hB⟩
          · rw [hall u hu] at hiu; cases hiu
          · have two : ∀ w ∈ T, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
              intro w hw hPw
              rcases hAB w hw hPw with h | h <;> rcases hAB u0 hu0 hPu0 with h0 | h0 <;>
                rcases hAB v0 hv0 hPv0 with h1 | h1
              · exact Or.inl (hA w hw u0 hu0 h h0)
              · exact Or.inl (hA w hw u0 hu0 h h0)
              · exact Or.inr (hA w hw v0 hv0 h h1)
              · exact absurd (hB u0 hu0 v0 hv0 h0 h1) hne
              · exact absurd (hA u0 hu0 v0 hv0 h0 h1) hne
              · exact Or.inr (hB w hw v0 hv0 h h1)
              · exact Or.inl (hB w hw u0 hu0 h h0)
              · exact Or.inl (hB w hw u0 hu0 h h0)
            have red : ∀ w ∈ T, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
              intro w hw hPw
              rcases two w hw hPw with h | h
              · rw [h]; split_ifs <;> rfl
              · rw [if_pos h]
            show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
            rw [red u hu hiu, red v hv hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          have hl := hinv i hiz u hu v hv hiu hiv
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : T.image l ⊆ insert (l v0) (T.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [if_neg h]
        have h1 : (T.image l).card ≤ (T.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNnot : N ∉ M := fun h => by have := (hM N h).2.1; omega
        rw [Finset.card_insert_of_notMem hNnot]
        omega
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · refine ⟨by omega, by simp [hN], by rw [hnew]; exact hz,
            u0, hu0, v0, hv0, fun h => hne (by rw [h]), by rw [hnew]; exact hPu0, by rw [hnew]; exact hPv0⟩
        · obtain ⟨h1, h2, h3, u, hu, v, hv, huv, h4, h5⟩ := hM i hi
          have hneN : i ≠ N := by omega
          exact ⟨h1, by simp; omega, by rw [hold _ _ hneN]; exact h3,
            u, hu, v, hv, huv, by rw [hold _ _ hneN]; exact h4, by rw [hold _ _ hneN]; exact h5⟩
      · intro hZ hT g0 hBg0 hmin hmem
        rcases Finset.mem_insert.mp hmem with rfl | hmem
        · exact hbridge_not_merge hZ hT hBg0 hmin ⟨hz, u0, hu0, v0, hv0, hPu0, hPv0, hne⟩
        · have hlt : g0 < N := (hM g0 hmem).2.1
          have hBg0' : IsBridge S R gs g0 := (hbridge_old g0 (by omega)).mp hBg0
          have hmin' : ∀ i < g0, ¬ IsBridge S R gs i := fun i hi => by
            rw [← hbridge_old i (by omega)]; exact hmin i hi
          exact hnoB hZ hT g0 hBg0' hmin' hmem
    · refine ⟨l, M, ?_, hcard, ?_, ?_⟩
      · intro i hiz u hu v hv hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          by_contra hne
          exact hm ⟨hiz, u, hu, v, hv, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i hiz u hu v hv hiu hiv
      · intro i hi
        obtain ⟨h1, h2, h3, u, hu, v, hv, huv, h4, h5⟩ := hM i hi
        have hneN : i ≠ N := by omega
        exact ⟨h1, by simp; omega, by rw [hold _ _ hneN]; exact h3,
          u, hu, v, hv, huv, by rw [hold _ _ hneN]; exact h4, by rw [hold _ _ hneN]; exact h5⟩
      · intro hZ hT g0 hBg0 hmin hmem
        have hlt : g0 < N := (hM g0 hmem).2.1
        have hBg0' : IsBridge S R gs g0 := (hbridge_old g0 (by omega)).mp hBg0
        have hmin' : ∀ i < g0, ¬ IsBridge S R gs i := fun i hi => by
          rw [← hbridge_old i (by omega)]; exact hmin i hi
        exact hnoB hZ hT g0 hBg0' hmin' hmem

end PEqualNP.Outside.L_meta_1376

open PEqualNP.Outside.L_meta_1376 in
theorem PEqualNP.Outside.L_meta_1376 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (R : Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool,
      ((∀ v ∈ R, x v = false) ∨ (∃ p ∈ R, ∀ v : Fin n, x v = decide (v = p))) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = true) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 1 ≤
      gates.length + (if ∃ i0 : Fin m, R = S i0 then 0 else ∑ i : Fin m, ((S i ∩ R).card - 1)) := by
  classical
  intro q n m S R hq hScard hSinter gates out j hG hjop hjuniq heval hnot
  obtain ⟨gs', σ, hgsLen, hgsMono, hgsEval⟩ := elim_not_gate gates j hG hjuniq
  have hzero : val gates (fun _ => false) (n + j.val) = true :=
    hnot (fun _ => false) (Or.inl (fun _ _ => rfl))
  have heof_not : ∀ p : Fin n, val gates (eof p) (n + j.val) = true := by
    intro p
    by_cases hp : p ∈ R
    · exact hnot (eof p) (Or.inr ⟨p, hp, fun _ => rfl⟩)
    · exact hnot (eof p) (Or.inl (fun v hv => by
        simp only [eof, decide_eq_false_iff_not]
        rintro rfl
        exact hp hv))
  have hzof_not : ∀ w : Fin m, val gates (Zof (S w ∪ R)) (n + j.val) = true := by
    intro w
    exact hnot (Zof (S w ∪ R)) (Or.inl (fun v hv => by
      simp [Zof, hv]))
  have hout_inr : ∀ w : Fin m, ∃ ow : ℕ, σ (out w) = Sum.inr ow := by
    intro w
    cases hσ : σ (out w) with
    | inr ow => exact ⟨ow, rfl⟩
    | inl b =>
      obtain ⟨p, hp⟩ : (S w).Nonempty := Finset.card_pos.mp (by rw [hScard w]; omega)
      have h0 : sigVal (gs'.foldl step (List.ofFn (fun _ : Fin n => false))) (σ (out w)) = false := by
        rw [hgsEval _ hzero (out w)]
        have h2 := heval w (fun _ => false)
        change val gates (fun _ => false) (out w) = _ at h2
        rw [h2]
        simp
      have h1 : sigVal (gs'.foldl step (List.ofFn (eof p))) (σ (out w)) = true := by
        rw [hgsEval _ (heof_not p) (out w)]
        have h2 := heval w (eof p)
        change val gates (eof p) (out w) = _ at h2
        rw [h2]
        simp [eof, hp]
      rw [hσ] at h0 h1
      simp only [sigVal] at h0 h1
      rw [h0] at h1
      cases h1
  choose o ho using hout_inr
  have ho_eof : ∀ (w : Fin m) (p : Fin n), val gs' (eof p) (o w) = decide (p ∈ S w) := by
    intro w p
    have h1 := hgsEval (eof p) (heof_not p) (out w)
    rw [ho w] at h1
    change val gs' (eof p) (o w) = val gates (eof p) (out w) at h1
    rw [h1]
    have h2 := heval w (eof p)
    change val gates (eof p) (out w) = _ at h2
    rw [h2]
    simp [eof]
  have ho_zof : ∀ w : Fin m, val gs' (Zof (S w ∪ R)) (o w) = false := by
    intro w
    have h1 := hgsEval (Zof (S w ∪ R)) (hzof_not w) (out w)
    rw [ho w] at h1
    change val gs' (Zof (S w ∪ R)) (o w) = val gates (Zof (S w ∪ R)) (out w) at h1
    rw [h1]
    have h2 := heval w (Zof (S w ∪ R))
    change val gates (Zof (S w ∪ R)) (out w) = _ at h2
    rw [h2]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv
    simp [Zof, hv]
  have ho_supp : ∀ w : Fin m, supp gs' (o w) = S w := by
    intro w
    ext p
    simp [mem_supp, ho_eof w p]
  have hpiece : ∀ w : Fin m, ∃ E : Finset ℕ,
      E ⊆ Finset.Ico n (n + gs'.length) ∧
      (∀ i ∈ E, (val gs' (Zof (S w ∪ R)) i = false ∧
          ∃ u ∈ S w \ R, ∃ v ∈ S w \ R, u ≠ v ∧ val gs' (eof u) i = true ∧ val gs' (eof v) i = true) ∨
        (supp gs' i ⊆ S w ∧ 2 ≤ (@supp n gs' i).card)) ∧
      ((R = S w → q ≤ E.card) ∧
        (R ≠ S w → q ≤ E.card + ((S w ∩ R).card - 1))) := by
    intro w
    by_cases hReq : R = S w
    · obtain ⟨l, M, hinv, hcard, hM, _⟩ := main_inv (S w) R (S w) (S w) gs' hgsMono
      have himg : ((S w).image l).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
        have hz : val gs' (Zof (S w)) (o w) = false := by
          have := ho_zof w
          rwa [hReq, Finset.union_idempotent] at this
        exact hinv (o w) hz u hu v hv (by simp [ho_eof w u, hu]) (by simp [ho_eof w v, hv])
      refine ⟨M, fun i hi => Finset.mem_Ico.mpr ⟨(hM i hi).1, (hM i hi).2.1⟩, ?_, ?_, ?_⟩
      · intro i hi
        right
        obtain ⟨_, _, hz, u, hu, v, hv, huv, hiu, hiv⟩ := hM i hi
        refine ⟨fun p hp => mem_of_zof_false (S w) gs' hgsMono i hz p ((mem_supp gs' i p).mp hp), ?_⟩
        have hsub : ({u, v} : Finset (Fin n)) ⊆ supp gs' i := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> exact (mem_supp gs' i _).mpr (by assumption)
        have := Finset.card_le_card hsub
        rw [Finset.card_pair huv] at this
        exact this
      · intro _
        have := hScard w
        omega
      · intro hne; exact absurd hReq hne
    · obtain ⟨l, M, hinv, hcard, hM, hnoB⟩ := main_inv (S w) R (S w ∪ R) (S w \ R) gs' hgsMono
      have himg : ((S w \ R).image l).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
        have huS : u ∈ S w := (Finset.mem_sdiff.mp hu).1
        have hvS : v ∈ S w := (Finset.mem_sdiff.mp hv).1
        exact hinv (o w) (ho_zof w) u hu v hv (by simp [ho_eof w u, huS]) (by simp [ho_eof w v, hvS])
      by_cases hboth : (S w ∩ R).Nonempty ∧ (S w \ R).Nonempty
      · have hoB : IsBridge (S w) R gs' (o w) := by
          refine ⟨ho_zof w, by rw [ho_supp w], ?_, ?_⟩
          · rw [ho_supp w, ← Finset.inter_assoc, Finset.inter_self]; exact hboth.1
          · rw [ho_supp w, Finset.inter_eq_right.mpr Finset.sdiff_subset]; exact hboth.2
        let g0 := Nat.find (⟨o w, hoB⟩ : ∃ i, IsBridge (S w) R gs' i)
        have hg0 : IsBridge (S w) R gs' g0 := Nat.find_spec (⟨o w, hoB⟩ : ∃ i, IsBridge (S w) R gs' i)
        have hmin : ∀ i < g0, ¬ IsBridge (S w) R gs' i := fun i hi => Nat.find_min _ hi
        have hg0_notM : g0 ∉ M := hnoB rfl rfl g0 hg0 hmin
        have hg0_gate := bridge_gate (S w) R gs' g0 hg0
        refine ⟨insert g0 M, ?_, ?_, fun h => absurd h hReq, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Finset.mem_Ico.mpr hg0_gate
          · exact Finset.mem_Ico.mpr ⟨(hM i hi).1, (hM i hi).2.1⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · right
            refine ⟨hg0.2.1, ?_⟩
            obtain ⟨p, hp⟩ := hg0.2.2.1
            obtain ⟨u, hu⟩ := hg0.2.2.2
            have hpu : p ≠ u := by
              intro he; subst he
              exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu).2).2
                (Finset.mem_inter.mp (Finset.mem_inter.mp hp).2).2
            have hsub : ({p, u} : Finset (Fin n)) ⊆ supp gs' g0 := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact (Finset.mem_inter.mp hp).1
              · exact (Finset.mem_inter.mp hu).1
            have := Finset.card_le_card hsub
            rw [Finset.card_pair hpu] at this
            exact this
          · left
            obtain ⟨_, _, h1, h2⟩ := hM i hi
            exact ⟨h1, h2⟩
        · intro _
          rw [Finset.card_insert_of_notMem hg0_notM]
          have hadd := Finset.card_sdiff_add_card_inter (S w) R
          have hpos1 : 1 ≤ (S w ∩ R).card := Finset.card_pos.mpr hboth.1
          have hpos2 : 1 ≤ (S w \ R).card := Finset.card_pos.mpr hboth.2
          have := hScard w
          omega
      · refine ⟨M, fun i hi => Finset.mem_Ico.mpr ⟨(hM i hi).1, (hM i hi).2.1⟩, ?_,
            fun h => absurd h hReq, ?_⟩
        · intro i hi
          left
          obtain ⟨_, _, h1, h2⟩ := hM i hi
          exact ⟨h1, h2⟩
        · intro _
          have hadd := Finset.card_sdiff_add_card_inter (S w) R
          have := hScard w
          by_cases h1 : (S w ∩ R).Nonempty
          · have h2 : S w \ R = ∅ := by
              by_contra hne
              exact hboth ⟨h1, Finset.nonempty_iff_ne_empty.mpr hne⟩
            rw [h2, Finset.card_empty] at hadd
            omega
          · have h1' : S w ∩ R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h1
            rw [h1', Finset.card_empty] at hadd ⊢
            omega
  choose E hEsub hEprop hEcard using hpiece
  have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint E := by
    intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left]
    intro i hia hib
    have hpa := hEprop a i hia
    have hpb := hEprop b i hib
    rcases hpa with ⟨hza, u, hu, v, hv, huv, hiu, hiv⟩ | ⟨hsubA, hcardA⟩
    · rcases hpb with ⟨hzb, _⟩ | ⟨hsubB, _⟩
      · have huB : u ∈ S b := by
          have := mem_of_zof_false (S b ∪ R) gs' hgsMono i hzb u hiu
          rcases Finset.mem_union.mp this with h | h
          · exact h
          · exact absurd h (Finset.mem_sdiff.mp hu).2
        have hvB : v ∈ S b := by
          have := mem_of_zof_false (S b ∪ R) gs' hgsMono i hzb v hiv
          rcases Finset.mem_union.mp this with h | h
          · exact h
          · exact absurd h (Finset.mem_sdiff.mp hv).2
        have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hu).1, huB⟩
          · exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hv).1, hvB⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_pair huv] at this
        have := hSinter a b hab
        omega
      · have huB : u ∈ S b := hsubB ((mem_supp gs' i u).mpr hiu)
        have hvB : v ∈ S b := hsubB ((mem_supp gs' i v).mpr hiv)
        have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hu).1, huB⟩
          · exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hv).1, hvB⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_pair huv] at this
        have := hSinter a b hab
        omega
    · rcases hpb with ⟨_, u, hu, v, hv, huv, hiu, hiv⟩ | ⟨hsubB, _⟩
      · have huA : u ∈ S a := hsubA ((mem_supp gs' i u).mpr hiu)
        have hvA : v ∈ S a := hsubA ((mem_supp gs' i v).mpr hiv)
        have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
          intro p hp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨huA, (Finset.mem_sdiff.mp hu).1⟩
          · exact Finset.mem_inter.mpr ⟨hvA, (Finset.mem_sdiff.mp hv).1⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_pair huv] at this
        have := hSinter a b hab
        omega
      · have hsub : supp gs' i ⊆ S a ∩ S b := fun p hp => Finset.mem_inter.mpr ⟨hsubA hp, hsubB hp⟩
        have := Finset.card_le_card hsub
        have := hSinter a b hab
        omega
  have hsumE : ∑ w : Fin m, (E w).card ≤ gs'.length := by
    calc ∑ w : Fin m, (E w).card = (Finset.univ.biUnion E).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (Finset.Ico n (n + gs'.length)).card := Finset.card_le_card (fun i hi => by
          obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hi
          exact hEsub w hw)
      _ = gs'.length := by simp
  by_cases hex : ∃ i0 : Fin m, R = S i0
  · rw [if_pos hex, Nat.add_zero]
    obtain ⟨i0, hi0⟩ := hex
    have hmq : m * q ≤ ∑ w : Fin m, (E w).card := by
      have : m * q = ∑ _w : Fin m, q := by simp
      rw [this]
      refine Finset.sum_le_sum (fun w _ => ?_)
      by_cases hw : w = i0
      · subst hw; exact (hEcard w).1 hi0
      · have hne : R ≠ S w := by
          intro heq
          have h1 := hi0.symm.trans heq
          have hsub : S i0 ⊆ S i0 ∩ S w := by rw [← h1]; simp
          have := Finset.card_le_card hsub
          have := hSinter i0 w (Ne.symm hw)
          have := hScard i0
          omega
        have h2 := (hEcard w).2 hne
        have h3 : (S w ∩ R).card ≤ 1 := by rw [hi0]; exact hSinter w i0 hw
        omega
    omega
  · rw [if_neg hex]
    have hmq : m * q ≤ (∑ w : Fin m, (E w).card) + ∑ w : Fin m, ((S w ∩ R).card - 1) := by
      rw [← Finset.sum_add_distrib]
      have : m * q = ∑ _w : Fin m, q := by simp
      rw [this]
      refine Finset.sum_le_sum (fun w _ => (hEcard w).2 (fun h => hex ⟨w, h⟩))
    omega
