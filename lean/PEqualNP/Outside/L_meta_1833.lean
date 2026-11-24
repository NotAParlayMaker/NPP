import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1833

-- Wire evaluation and dependency lemmas are adapted from L-meta-1713.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem difp {α : Type} {c : Prop} [Decidable c] (h : c) {a : c → α} {b : ¬ c → α} :
    dite c a b = a h := by simp [h]

theorem difn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a : c → α} {b : ¬ c → α} :
    dite c a b = b h := by simp [h]

def fd {α : Type} (F : Gate → List α → α) (X : List α) (gs : List Gate) : List α :=
  gs.foldl (fun w g => w ++ [F g w]) X

theorem fd_len {α : Type} (F : Gate → List α → α) :
    ∀ (gs : List Gate) (X : List α), (fd F X gs).length = X.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro X; simp [fd]
  | cons g gs ih =>
    intro X
    have := ih (X ++ [F g X])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp
    omega

theorem fd_pre {α : Type} (F : Gate → List α → α) :
    ∀ (gs : List Gate) (X : List α) (i : ℕ), i < X.length → (fd F X gs)[i]? = X[i]? := by
  intro gs
  induction gs with
  | nil => intro X i _; simp [fd]
  | cons g gs ih =>
    intro X i hi
    have := ih (X ++ [F g X]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this, List.getElem?_append_left hi]

theorem fd_app {α : Type} (F : Gate → List α → α) (X : List α) (gs hs : List Gate) :
    fd F X (gs ++ hs) = fd F (fd F X gs) hs := by
  simp [fd, List.foldl_append]

theorem fd_gate' {α : Type} (F : Gate → List α → α) (dflt : α)
    (hF : ∀ (g : Gate) (w w' : List α),
      (∀ i ∈ g.inputs, w.getD i dflt = w'.getD i dflt) → F g w = F g w')
    (as : List Gate) (g : Gate) (bs : List Gate) (X : List α)
    (hrb : ∀ i ∈ g.inputs, i < X.length + as.length) :
    (fd F X (as ++ g :: bs)).getD (X.length + as.length) dflt = F g (fd F X (as ++ g :: bs)) := by
  have e1 : fd F X (as ++ g :: bs) = fd F (fd F X as ++ [F g (fd F X as)]) bs := by
    simp [fd, List.foldl_append]
  have hWl : (fd F X as).length = X.length + as.length := fd_len F as X
  have key : ∀ i, i < (fd F X as).length + 1 →
      (fd F X (as ++ g :: bs))[i]? = (fd F X as ++ [F g (fd F X as)])[i]? := by
    intro i hi
    rw [e1]
    exact fd_pre F bs _ i (by simp; omega)
  rw [List.getD_eq_getElem?_getD, key _ (by omega), ← hWl,
    List.getElem?_append_right (le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  apply hF
  intro i hi
  have hi' := hrb i hi
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, key i (by omega),
    List.getElem?_append_left (by omega)]

theorem fd_gate {α : Type} (F : Gate → List α → α) (dflt : α)
    (hF : ∀ (g : Gate) (w w' : List α),
      (∀ i ∈ g.inputs, w.getD i dflt = w'.getD i dflt) → F g w = F g w')
    (gs : List Gate) (X : List α) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < X.length + j) :
    (fd F X gs).getD (X.length + j) dflt = F (gs.getD j ⟨GateOp.or, []⟩) (fd F X gs) := by
  have h1 : gs.take j ++ gs[j] :: gs.drop (j + 1) = gs := by
    rw [← List.drop_eq_getElem_cons hj]
    exact List.take_append_drop j gs
  have h2 : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := by
    simp [List.getD_eq_getElem?_getD, hj]
  have h3 := fd_gate' F dflt hF (gs.take j) gs[j] (gs.drop (j + 1)) X (by
    rw [List.length_take, min_eq_left hj.le, ← h2]
    exact hrb)
  rw [h1, List.length_take, min_eq_left hj.le] at h3
  rw [h2]
  exact h3

def stpF : Gate → List Bool → Bool :=
  fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)

theorem stpF_congr (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : stpF g w = stpF g w' := by
  unfold stpF
  rw [List.map_congr_left h]

theorem ld_congr (g : Gate) (w w' : List ℕ)
    (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) : g.lineDegree w = g.lineDegree w' := by
  unfold Gate.lineDegree
  rw [List.map_congr_left h]

theorem getD_snoc {α : Type} (W : List α) (v d : α) (i : ℕ) :
    (W ++ [v]).getD i d = if i = W.length then v else W.getD i d := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ifn (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ifn (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (fd stpF W1 gs).getD i false = true → (fd stpF W2 gs).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa [fd] using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    have := ih (W1 ++ [stpF g W1]) (W2 ++ [stpF g W2]) (by simp [hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) (by
        intro i
        simp only [getD_snoc, hl]
        split_ifs
        · unfold stpF
          rcases hop g List.mem_cons_self with ha | ho
          · rw [ev_and g _ ha, ev_and g _ ha]
            intro h k hk
            exact H k (h k hk)
          · rw [ev_or g _ ho, ev_or g _ ho]
            rintro ⟨k, hk, h⟩
            exact ⟨k, hk, H k h⟩
        · exact H i)
    simpa only [fd, List.foldl_cons] using this

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem app_getD {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (i : ℕ) :
    (List.ofFn (Fin.append x y)).getD i false =
      if h : i < n then x ⟨i, h⟩ else if h2 : i - n < m then y ⟨i - n, h2⟩ else false := by
  rw [ofFn_getD]
  by_cases h : i < n
  · rw [difp (by omega), difp h]
    exact Fin.append_left x y ⟨i, h⟩
  · rw [difn h]
    by_cases h2 : i - n < m
    · rw [difp (by omega), difp h2]
      have hh : (⟨i, by omega⟩ : Fin (n + m)) = Fin.natAdd n ⟨i - n, h2⟩ := by
        apply Fin.ext
        show i = n + (i - n)
        omega
      rw [hh, Fin.append_right]
    · rw [difn (by omega), difn h2]


def V (C : Circuit) (X : List Bool) (w : ℕ) : Bool := (C.wires X).getD w false

def D (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) : ℕ := (C.lineDegrees K M).getD w 0

theorem wires_fd (C : Circuit) (X : List Bool) : C.wires X = fd stpF X C.gates := rfl

theorem V_in (C : Circuit) (X : List Bool) (w : ℕ) (hw : w < X.length) :
    V C X w = X.getD w false := by
  unfold V
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, fd_pre _ _ _ _ hw]

theorem V_out (C : Circuit) (X : List Bool) (w : ℕ) (hw : X.length + C.gates.length ≤ w) :
    V C X w = false := by
  unfold V
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
    rw [fd_len]; exact hw)]
  rfl

theorem V_gate (K : ℕ) (C : Circuit) (hrb : ReadsBack K C) (X : List Bool) (hX : X.length = K)
    (j : ℕ) (hj : j < C.gates.length) :
    V C X (K + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C X)) := by
  have h := fd_gate stpF false stpF_congr C.gates X j hj (by
    intro i hi
    have := hrb j hj i hi
    rw [hX]
    exact this)
  rw [hX] at h
  exact h

theorem D_len (K : ℕ) (M : Finset ℕ) (C : Circuit) :
    (C.lineDegrees K M).length = K + C.gates.length := by
  have := fd_len Gate.lineDegree C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0)
  simpa [fd, Circuit.lineDegrees] using this

theorem D_in (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) (hw : w < K) :
    D K M C w = if w ∈ M then 1 else 0 := by
  unfold D Circuit.lineDegrees
  have := fd_pre Gate.lineDegree C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0) w
    (by simpa using hw)
  unfold fd at this
  rw [List.getD_eq_getElem?_getD, this]
  simp [hw]

theorem D_out (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) (hw : K + C.gates.length ≤ w) :
    D K M C w = 0 := by
  unfold D
  have hl := D_len K M C
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem foldr_max_zero : ∀ (l : List ℕ), l.foldr max 0 = 0 ↔ ∀ a ∈ l, a = 0 := by
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    omega

theorem D_zero_iff (K : ℕ) (M : Finset ℕ) (C : Circuit) (hrb : ReadsBack K C) (j : ℕ)
    (hj : j < C.gates.length) :
    D K M C (K + j) = 0 ↔ ∀ i ∈ (gateAt C j).inputs, D K M C i = 0 := by
  have h := fd_gate Gate.lineDegree 0 ld_congr C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0) j hj (by
    intro i hi
    have := hrb j hj i hi
    simpa using this)
  simp only [List.length_map, List.length_range] at h
  have h' : D K M C (K + j) = (gateAt C j).lineDegree (C.lineDegrees K M) := h
  rw [h']
  unfold Gate.lineDegree
  split_ifs
  · rw [List.sum_eq_zero_iff]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl
  · rw [foldr_max_zero]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl

theorem V_mono (C : Circuit) (hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (X X' : List Bool) (hl : X.length = X'.length)
    (h : ∀ i, X.getD i false = true → X'.getD i false = true) (w : ℕ)
    (hw : V C X w = true) : V C X' w = true := by
  unfold V at hw ⊢
  rw [wires_fd] at hw ⊢
  exact mono C.gates _ _ hl hm h w hw

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _


def Binary (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem two_inputs (g : Gate) (h : Binary g) : ∃ a b, g.inputs = [a,b] := by
  have := h.2
  match eq : g.inputs with
  | [a,b] => exact ⟨a,b,rfl⟩
  | [] | [_] | _ :: _ :: _ :: _ => simp_all

def replaceAt (C : Circuit) (f : Nat → Gate) : Circuit :=
  ⟨List.ofFn (fun j : Fin C.gates.length => f j.val),C.output⟩

theorem rep_length (C : Circuit) (f) : (replaceAt C f).gates.length = C.gates.length := by
  simp [replaceAt]

theorem rep_at (C : Circuit) (f) (j) (hj : j < C.gates.length) :
    gateAt (replaceAt C f) j = f j := by
  simp [replaceAt, gateAt, List.getD_eq_getElem?_getD,hj]

theorem rep_back (K : Nat) (C : Circuit) (f) (h : ∀ j < C.gates.length, ∀ i ∈ (f j).inputs, i < K+j) :
    ReadsBack K (replaceAt C f) := by
  intro j hj
  rw [rep_length] at hj
  rw [rep_at _ _ _ hj]
  exact h j hj

theorem rep_binary (C : Circuit) (f) (h : ∀ j < C.gates.length, Binary (f j)) :
    ∀ g ∈ (replaceAt C f).gates, Binary g := by
  intro g hg
  rcases List.mem_ofFn.mp hg with ⟨j,rfl⟩
  exact h j j.isLt

def copyWire (i : Nat) : Gate := ⟨GateOp.or,[i,i]⟩

-- Keep each wire index. A free dummy input stands in for constant wires.
-- A varying gate with just one varying operand copies that operand.
noncomputable def shrink (A : Nat → Prop) (d : Nat) (g : Gate) : Gate := by
  classical
  exact if A (g.inputs.getD 0 0) then
    if A (g.inputs.getD 1 0) then g else copyWire (g.inputs.getD 0 0)
    else if A (g.inputs.getD 1 0) then copyWire (g.inputs.getD 1 0) else copyWire d

theorem shrink_binary (A) (d) (g) (hb : Binary g) : Binary (shrink A d g) := by
  unfold shrink
  split_ifs <;> first | exact hb | exact ⟨Or.inr rfl,rfl⟩

theorem shrink_reads (A) (d) (g) (hb : Binary g) (i : Nat) (hi : i ∈ (shrink A d g).inputs) :
    (i ∈ g.inputs ∧ A i) ∨ (i = d ∧ ∀ t ∈ g.inputs, ¬ A t) := by
  obtain ⟨a,b,e⟩ := two_inputs g hb
  by_cases ha : A a <;> by_cases hh : A b <;>
    simp [shrink,e,ha,hh,copyWire] at hi ⊢ <;> grind

theorem shrink_and (A) (d) (g) (hb : Binary g) (h : (shrink A d g).op = GateOp.and) :
    shrink A d g = g ∧ ∀ t ∈ g.inputs, A t := by
  obtain ⟨a,b,e⟩ := two_inputs g hb
  by_cases ha : A a <;> by_cases hh : A b <;>
    simp_all [shrink,copyWire]

def evalAt (g : Gate) (v : Nat → Bool) := g.op.eval (g.inputs.map v)

theorem nonconstant_has_input {A : Nat → Prop} (g : Gate) (v w : Nat → Bool)
    (hc : ∀ i, ¬ A i → w i = v i) (h : evalAt g w ≠ evalAt g v) :
    ∃ i ∈ g.inputs, A i := by
  by_contra! no
  apply h
  unfold evalAt
  rw [List.map_congr_left (fun i hi => hc i (no i hi))]

theorem shrink_eval {A : Nat → Prop} (d : Nat) (g : Gate) (hb : Binary g)
    (old now alt : Nat → Bool) (hc : ∀ i, ¬ A i → alt i = old i)
    (changeVal : evalAt g alt ≠ evalAt g old)
    (same : ∀ i ∈ g.inputs, A i → now i = old i) :
    evalAt (shrink A d g) now = evalAt g old := by
  obtain ⟨a,b,e⟩ := two_inputs g hb
  have hop := hb.1
  by_cases ha : A a <;> by_cases hh : A b
  · have ea := same a (by simp [e]) ha
    have eb := same b (by simp [e]) hh
    simp [shrink,e,ha,hh,evalAt,ea,eb]
  · have ea := same a (by simp [e]) ha
    have eb := hc b hh
    rcases hop with h | h <;> cases ex : old b <;>
      simp_all [shrink,copyWire,evalAt,GateOp.eval]
  · have eb := same b (by simp [e]) hh
    have ea := hc a ha
    rcases hop with h | h <;> cases ex : old a <;>
      simp_all [shrink,copyWire,evalAt,GateOp.eval]
  · obtain ⟨t,ht,hA⟩ := nonconstant_has_input g old alt hc changeVal
    simp only [e,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl <;> contradiction

def Cross (N : Nat) (C : Circuit) (j : Nat) := j < C.gates.length ∧
  (gateAt C j).op = GateOp.and ∧ ¬ ((∃ i ∈ (gateAt C j).inputs,
    D (N+N) (Finset.Ico N (N+N)) C i = 0) ∨ (∀ i ∈ (gateAt C j).inputs,
    D (N+N) (Finset.range N) C i = 0))

noncomputable def viewGate (N : Nat) (C : Circuit) (sel : Nat → Fin 2) (j : Nat) : Gate := by
  classical
  exact if Cross N C j then copyWire ((gateAt C j).inputs.getD (sel j).val 0) else gateAt C j

theorem selected_mem (g : Gate) (hb : Binary g) (s : Fin 2) :
    g.inputs.getD s.val 0 ∈ g.inputs := by
  have hi : s.val < g.inputs.length := by rw [hb.2]; exact s.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

theorem view_reads (N) (C : Circuit) (sel) (j) (hb : Binary (gateAt C j)) :
    ∀ i ∈ (viewGate N C sel j).inputs, i ∈ (gateAt C j).inputs := by
  classical
  unfold viewGate
  split_ifs
  · intro i h
    have eq : i = (gateAt C j).inputs.getD (sel j).val 0 := by simpa [copyWire] using h
    rw [eq]
    exact selected_mem _ hb _
  · exact fun _ h => h

-- If every crossed gate reads only varying wires, both operands are false
-- on the minimal assignment. Copying either operand preserves that value.
theorem find_fixed_cross (N : Nat) (C : Circuit) (X : List Bool) (len : X.length = N+N)
    (sel : Nat → Fin 2) (A : Nat → Prop) (bottom : ∀ i, A i → V C X i = false)
    (basis : ∀ g ∈ C.gates, Binary g) (rb : ReadsBack (N+N) C)
    (diff : V (replaceAt C (viewGate N C sel)) X C.output ≠ V C X C.output) :
    ∃ j, Cross N C j ∧ ∃ i ∈ (gateAt C j).inputs, ¬ A i := by
  classical
  by_contra! no
  let E := replaceAt C (viewGate N C sel)
  have hlen : E.gates.length = C.gates.length := rep_length _ _
  have gate (j) (hj : j < C.gates.length) := basis _ (gateAt_mem C j hj)
  have er : ReadsBack (N+N) E := rep_back _ _ _ (fun j hj i hi =>
    rb _ hj i (view_reads N C sel j (gate _ hj) i hi))
  apply diff
  change V E X C.output = _
  suffices allW : ∀ w, V E X w = V C X w from allW _
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < N+N
    · rw [V_in _ _ _ (by omega), V_in _ _ _ (by omega)]
    by_cases inside : w < N+N+C.gates.length
    · let j := w-(N+N)
      have hj : j < C.gates.length := by dsimp [j]; omega
      have ej : w = N+N+j := by dsimp [j]; omega
      rw [ej, V_gate _ E er X len j (by omega), V_gate _ C rb X len j hj]
      change (gateAt (replaceAt C _) j).op.eval _ = _
      rw [rep_at _ _ j hj]
      have gr (i) (hi : i ∈ (gateAt C j).inputs) : V E X i = V C X i :=
        ih i (by have := rb j hj i hi; omega)
      by_cases c : Cross N C j
      · obtain ⟨a,b,e⟩ := two_inputs _ (gate j hj)
        have op := c.2.1
        have ha : a ∈ (gateAt C j).inputs := by simp [e]
        have hb : b ∈ (gateAt C j).inputs := by simp [e]
        let u := (gateAt C j).inputs.getD (sel j).val 0
        have hu : u ∈ (gateAt C j).inputs := selected_mem _ (gate _ hj) _
        have vu : V E X u = false := (gr u hu).trans (bottom u (no j c u hu))
        have va := bottom a (no j c a ha)
        have vb := bottom b (no j c b hb)
        rw [show viewGate N C sel j = copyWire u by simp [viewGate,c,u]]
        change GateOp.or.eval ([u,u].map (V E X)) = _
        simp [GateOp.eval,op,e,vu,va,vb]
      · rw [show viewGate N C sel j = gateAt C j by simp [viewGate,c]]
        congr 1
        exact List.map_congr_left gr
    · rw [V_out _ _ _ (by omega), V_out _ _ _ (by omega)]

def Alive {ι : Type} (C : Circuit) (X : ι → List Bool) (base : ι) (w : Nat) :=
  ∃ t, V C (X t) w ≠ V C (X base) w

theorem stable {ι : Type} (C : Circuit) (X : ι → List Bool) (base : ι) (i : Nat)
    (h : ¬ Alive C X base i) (t t' : ι) : V C (X t) i = V C (X t') i := by
  have eq (k : ι) : V C (X k) i = V C (X base) i := by
    by_contra neq
    exact h ⟨k,neq⟩
  exact (eq t).trans (eq t').symm

theorem variable_gate {ι : Type} (K : Nat) (C : Circuit) (X : ι → List Bool) (base : ι)
    (lengthX : ∀ t, (X t).length = K) (rb : ReadsBack K C) (j : Nat) (hj : j < C.gates.length)
    (active : Alive C X base (K+j)) (t : ι) :
    ∃ t', evalAt (gateAt C j) (V C (X t')) ≠ evalAt (gateAt C j) (V C (X t)) := by
  by_contra! no
  obtain ⟨k,hk⟩ := active
  apply hk
  rw [V_gate K C rb _ (lengthX _) j hj,V_gate K C rb _ (lengthX _) j hj]
  exact (no k).trans (no base).symm

theorem active_input {ι : Type} (K : Nat) (C : Circuit) (X : ι → List Bool) (base : ι)
    (lengthX : ∀ t, (X t).length = K) (rb : ReadsBack K C) (j : Nat) (hj : j < C.gates.length)
    (active : Alive C X base (K+j)) : ∃ i ∈ (gateAt C j).inputs, Alive C X base i := by
  obtain ⟨t,hd⟩ := variable_gate K C X base lengthX rb j hj active base
  exact nonconstant_has_input _ _ _ (fun i hi => stable C X base i hi t base) hd

noncomputable def shrunk (C : Circuit) (A : Nat → Prop) (d : Nat) :=
  replaceAt C (fun j => shrink A d (gateAt C j))

theorem shrunk_rules (K : Nat) (C : Circuit) (A : Nat → Prop) (d : Nat) (hd : d < K)
    (basis : ∀ g ∈ C.gates, Binary g) (rb : ReadsBack K C) :
    (∀ g ∈ (shrunk C A d).gates, Binary g) ∧ ReadsBack K (shrunk C A d) := by
  have hb (j) (hj : j < C.gates.length) := basis _ (gateAt_mem C j hj)
  refine ⟨rep_binary C _ (fun j hj => shrink_binary _ _ _ (hb _ hj)), rep_back K C _ ?_⟩
  intro j hj i hi
  rcases shrink_reads _ _ _ (hb j hj) i hi with h | ⟨rfl,_⟩
  · exact rb j hj i h.1
  · omega

theorem shrunk_values {ι : Type} (K : Nat) (C : Circuit) (X R : ι → List Bool) (base : ι)
    (lengthX : ∀ t, (X t).length = K) (lengthR : ∀ t, (R t).length = K)
    (basis : ∀ g ∈ C.gates, Binary g) (rb : ReadsBack K C) (d : Nat) (hd : d < K)
    (inputs : ∀ i < K, Alive C X base i → ∀ t, (R t).getD i false = (X t).getD i false)
    (t : ι) (w : Nat) (active : Alive C X base w) :
    V (shrunk C (Alive C X base) d) (R t) w = V C (X t) w := by
  let A := Alive C X base
  let E := shrunk C A d
  have hlen : E.gates.length = C.gates.length := rep_length _ _
  have er := (shrunk_rules K C A d hd basis rb).2
  change V E (R t) w = _
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases inpt : w < K
    · rw [V_in _ _ _ (by rw [lengthR]; exact inpt), V_in _ _ _ (by rw [lengthX]; exact inpt)]
      exact inputs w inpt active t
    by_cases inside : w < K+C.gates.length
    · let j := w-K
      have hj : j < C.gates.length := by dsimp [j]; omega
      have ej : w = K+j := by dsimp [j]; omega
      rw [ej] at active ⊢
      obtain ⟨t',diff⟩ := variable_gate K C X base lengthX rb j hj active t
      rw [V_gate K E er _ (lengthR _) j (by omega), V_gate K C rb _ (lengthX _) j hj]
      rw [show gateAt E j = shrink A d (gateAt C j) from rep_at _ _ _ hj]
      apply shrink_eval d _ (basis _ (gateAt_mem C j hj)) _ _ _ (fun i hi => stable C X base i hi t' t) diff
      intro i hi ha
      exact ih i (by have := rb j hj i hi; omega) ha
    · rw [V_out _ _ _ (by rw [lengthR]; omega), V_out _ _ _ (by rw [lengthX]; omega)]

theorem deg_transfer {ι : Type} (K : Nat) (C : Circuit) (X : ι → List Bool) (base : ι)
    (lengthX : ∀ t, (X t).length = K) (basis : ∀ g ∈ C.gates, Binary g) (rb : ReadsBack K C)
    (d : Nat) (hd : d < K) (M : Finset Nat) (w : Nat) (active : Alive C X base w)
    (zero : D K M C w = 0) : D K M (shrunk C (Alive C X base) d) w = 0 := by
  let A := Alive C X base
  let E := shrunk C A d
  have len : E.gates.length = C.gates.length := rep_length _ _
  have er := (shrunk_rules K C A d hd basis rb).2
  change D K M E w = 0
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases inpt : w < K
    · rwa [D_in _ _ E w inpt, ← D_in _ _ C w inpt]
    by_cases inside : w < K+C.gates.length
    · let j := w-K
      have hj : j < C.gates.length := by dsimp [j]; omega
      have ej : w = K+j := by dsimp [j]; omega
      rw [ej] at active zero ⊢
      obtain ⟨a,ha,act⟩ := active_input K C X base lengthX rb j hj active
      apply (D_zero_iff K M E er j (by omega)).2
      intro i hi
      change i ∈ (gateAt (replaceAt C _) j).inputs at hi
      rw [rep_at _ _ _ hj] at hi
      rcases shrink_reads A d _ (basis _ (gateAt_mem C j hj)) i hi with h | h
      · exact ih i (by have := rb j hj i h.1; omega) h.2 ((D_zero_iff K M C rb j hj).1 zero i h.1)
      · exact (h.2 a ha act).elim
    · exact D_out _ _ _ _ (by omega)

theorem clean_wires (K : Nat) (C : Circuit) (A : Nat → Prop) (d : Nat) (hd : d < K)
    (basis : ∀ g ∈ C.gates, Binary g) (rb : ReadsBack K C) (M : Finset Nat)
    (dFree : d ∉ M) (free : ∀ i < K, A i → i ∉ M) :
    (∀ w, (K ≤ w ∨ A w ∨ w=d) → D K M (shrunk C A d) w = 0) ∧
    (∀ j < (shrunk C A d).gates.length, ∀ i ∈ (gateAt (shrunk C A d) j).inputs,
      D K M (shrunk C A d) i = 0) := by
  let E := shrunk C A d
  have len : E.gates.length = C.gates.length := rep_length _ _
  have er := (shrunk_rules K C A d hd basis rb).2
  have reads (j) (hj : j < E.gates.length) (i) (hi : i ∈ (gateAt E j).inputs) : A i ∨ i = d := by
    change i ∈ (gateAt (replaceAt C _) j).inputs at hi
    rw [rep_at _ _ _ (by omega)] at hi
    rcases shrink_reads A d _ (basis _ (gateAt_mem C j (by omega))) i hi with h | h
    · exact Or.inl h.2
    · exact Or.inr h.1
  have allok (w) (h : K ≤ w ∨ A w ∨ w=d) : D K M E w = 0 := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases inpt : w < K
      · rw [D_in _ _ _ _ inpt]
        rcases h with bad | active | rfl
        · omega
        · simp [free w inpt active]
        · simp [dFree]
      by_cases inside : w < K+E.gates.length
      · let j := w-K
        have hj : j < E.gates.length := by dsimp [j]; omega
        have ej : w = K+j := by dsimp [j]; omega
        rw [ej]
        apply (D_zero_iff K M E er _ hj).2
        intro i hi
        exact ih i (by have := er j hj i hi; omega) (Or.inr (reads j hj i hi))
      · exact D_out _ _ _ _ (by omega)
  exact ⟨allok,fun j hj i hi => allok i (Or.inr (reads j hj i hi))⟩

theorem cross_subset {ι : Type} (N : Nat) (C : Circuit) (X : ι → List Bool) (base : ι)
    (lengthX : ∀ t, (X t).length = N+N) (basis : ∀ g ∈ C.gates, Binary g)
    (rb : ReadsBack (N+N) C) (d : Nat) (hd : d < N+N) (j : Nat)
    (hc : Cross N (shrunk C (Alive C X base) d) j) :
    Cross N C j ∧ ∀ i ∈ (gateAt C j).inputs, Alive C X base i := by
  let A := Alive C X base
  let E := shrunk C A d
  rcases hc with ⟨hj,hAnd,hCross⟩
  have hj' : j < C.gates.length := by simpa [shrunk,rep_length] using hj
  have rep : gateAt E j = shrink A d (gateAt C j) := rep_at _ _ j hj'
  change (gateAt E j).op = GateOp.and at hAnd
  obtain ⟨eg,act⟩ := shrink_and A d _ (basis _ (gateAt_mem C j hj')) (rep ▸ hAnd)
  have gateEq := rep.trans eg
  change ¬ ((∃ i ∈ (gateAt E j).inputs, D _ _ E i = 0) ∨ (∀ i ∈ (gateAt E j).inputs, D _ _ E i = 0)) at hCross
  rw [gateEq] at hAnd hCross
  refine ⟨⟨hj',hAnd,fun bad => hCross ?_⟩,act⟩
  rcases bad with ⟨i,hi,h⟩ | allI
  · exact Or.inl ⟨i,hi,deg_transfer _ C X base lengthX basis rb d hd _ i (act i hi) h⟩
  · exact Or.inr (fun i hi => deg_transfer _ C X base lengthX basis rb d hd _ i (act i hi) (allI i hi))

abbrev Config (N : Nat) := (Fin N → Bool) × (Fin N → Bool)

def initial (N : Nat) : Config N := (fun _ => false,fun _ => false)

def raw {N : Nat} (t : Config N) : List Bool := List.ofFn (Fin.append t.1 t.2)

def assigned {N : Nat} (S W : Finset (Fin N)) (pi nu : Fin N → Bool) (t : Config N) : List Bool :=
  List.ofFn (Fin.append (fun p => if p ∈ S then t.1 p else pi p)
    (fun l => if l ∈ W then t.2 l else nu l))

def frozen {N : Nat} (S W : Finset (Fin N)) : Finset Nat :=
  Sᶜ.image (fun p => p.val) ∪ Wᶜ.image (fun l => N+l.val)

theorem bottom_inputs {N : Nat} (S W : Finset (Fin N)) (pi nu : Fin N → Bool)
    (t : Config N) (i : Nat) :
    (assigned S W pi nu (initial N)).getD i false = true → (assigned S W pi nu t).getD i false = true := by
  unfold assigned
  rw [app_getD,app_getD]
  split_ifs <;> simp_all [initial]

theorem free_info {N : Nat} (C : Circuit) (S W : Finset (Fin N)) (pi nu : Fin N → Bool)
    (i : Nat) (hi : i < N+N) (ha : Alive C (assigned S W pi nu) (initial N) i) :
    i ∉ frozen S W ∧ ∀ t, (raw t).getD i false = (assigned S W pi nu t).getD i false := by
  obtain ⟨k,diff⟩ := ha
  rw [V_in _ _ _ (by simpa [assigned] using hi), V_in _ _ _ (by simpa [assigned] using hi)] at diff
  unfold assigned at diff
  rw [app_getD,app_getD] at diff
  by_cases left : i < N
  · let u : Fin N := ⟨i,left⟩
    have hu : u ∈ S := by
      by_contra out
      simp [left,show (⟨i,left⟩ : Fin N) ∉ S from out] at diff
    refine ⟨?_, ?_⟩
    · intro hf
      rcases Finset.mem_union.mp hf with hf | hf
      · obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp hf
        have vu : v = u := Fin.ext ev
        exact (Finset.mem_compl.mp hv) (vu ▸ hu)
      · obtain ⟨v,_,ev⟩ := Finset.mem_image.mp hf
        omega
    · intro t
      unfold raw assigned
      rw [app_getD,app_getD]
      simp [left,show (⟨i,left⟩ : Fin N) ∈ S from hu]
  · have hri : i-N < N := by omega
    let u : Fin N := ⟨i-N,hri⟩
    have hu : u ∈ W := by
      by_contra out
      simp [left,hri,show (⟨i-N,hri⟩ : Fin N) ∉ W from out] at diff
    refine ⟨?_, ?_⟩
    · intro hf
      rcases Finset.mem_union.mp hf with hf | hf
      · obtain ⟨v,_,ev⟩ := Finset.mem_image.mp hf
        have := v.isLt
        omega
      · obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp hf
        have vu : v = u := Fin.ext (by change v.val=i-N; omega)
        exact (Finset.mem_compl.mp hv) (vu ▸ hu)
    · intro t
      unfold raw assigned
      rw [app_getD,app_getD]
      simp [left,hri,show (⟨i-N,hri⟩ : Fin N) ∈ W from hu]

theorem some_variable_input {ι : Type} (K : Nat) (C : Circuit) (X : ι → List Bool) (base : ι)
    (lengthX : ∀ t, (X t).length = K) (w : Nat) (hw : Alive C X base w) :
    ∃ i < K, Alive C X base i := by
  by_contra! no
  obtain ⟨t,diff⟩ := hw
  have eq : X t = X base := by
    apply List.ext_getElem (by simp [lengthX])
    intro i ht hb
    have h := stable C X base i (no i (by rw [← lengthX t]; exact ht)) t base
    rwa [V_in _ _ _ ht,V_in _ _ _ hb,List.getD_eq_getElem _ _ ht,List.getD_eq_getElem _ _ hb] at h
  exact diff (congrArg (fun x => V C x w) eq)

theorem main (N m : Nat) (C : Circuit) (S W : Finset (Fin N)) (pi nu : Fin N → Bool)
    (sel : Nat → Fin 2) (basis : ∀ g ∈ C.gates, Binary g) (rb : ReadsBack (N+N) C)
    (count : Set.ncard {j | Cross N C j} ≤ m+1)
    (viewOn : V (replaceAt C (viewGate N C sel)) (assigned S W pi nu (initial N)) C.output = true)
    (off : V C (assigned S W pi nu (initial N)) C.output = false)
    (on : ∃ t, V C (assigned S W pi nu t) C.output = true) :
    ∃ E : Circuit, ((∀ g ∈ E.gates, Binary g) ∧ ReadsBack (N+N) E) ∧
      Set.ncard {j | Cross N E j} ≤ m ∧ E.size ≤ C.size ∧
      (0 < E.gates.length ∧ (∀ j < E.gates.length, ∀ i ∈ (gateAt E j).inputs, D (N+N) (frozen S W) E i = 0) ∧
        D (N+N) (frozen S W) E E.output = 0) ∧
      ∀ t, V E (raw t) E.output = V C (assigned S W pi nu t) C.output := by
  classical
  let X := assigned S W pi nu
  let base := initial N
  let A := Alive C X base
  have lx (t) : (X t).length = N+N := by simp [X,assigned]
  have actout : A C.output := by
    obtain ⟨t,ht⟩ := on
    exact ⟨t,by rw [ht,off]; decide⟩
  obtain ⟨d,hd,actd⟩ := some_variable_input (N+N) C X base lx C.output actout
  let E := shrunk C A d
  have len : E.gates.length = C.gates.length := rep_length _ _
  have headEq : E.output = C.output := rfl
  have atBottom (i) (a : A i) : V C (X base) i = false := by
    cases e : V C (X base) i with
    | false => rfl
    | true =>
      obtain ⟨t,ht⟩ := a
      have on := V_mono C (fun g hg => (basis g hg).1) (X base) (X t) (by simp [lx])
        (bottom_inputs S W pi nu t) i e
      exact (ht (on.trans e.symm)).elim
  obtain ⟨j,hj,i,hij,fixed⟩ := find_fixed_cross N C (X base) (lx base) sel A atBottom basis rb
    (by change V _ (assigned _ _ _ _ _) _ ≠ V C (assigned _ _ _ _ _) _; rw [viewOn,off]; decide)
  have sub (k) (h : Cross N E k) := cross_subset N C X base lx basis rb d hd k h
  have strict : {k | Cross N E k} ⊂ {k | Cross N C k} := by
    refine ⟨fun k hk => (sub k hk).1, fun h => fixed ((sub j (h hj)).2 i hij)⟩
  have fin : {k | Cross N C k}.Finite := (Set.finite_lt_nat C.gates.length).subset (fun k hk => hk.1)
  have less := Set.ncard_lt_ncard strict fin
  have info := free_info C S W pi nu
  have clean := clean_wires (N+N) C A d hd basis rb (frozen S W) (info d hd actd).1
    (fun i hi hai => (info i hi hai).1)
  refine ⟨E,shrunk_rules _ _ _ _ hd basis rb,by omega,?_,⟨?_,clean.2,?_,⟩,?_⟩
  · exact le_of_eq len
  · have := hj.1
    omega
  · exact clean.1 _ (Or.inr (Or.inl actout))
  · intro t
    exact shrunk_values (N+N) C X raw base lx (fun _ => by simp [raw]) basis rb d hd
      (fun i hi a => (info i hi a).2) t C.output actout

noncomputable def postedView (N : Nat) (C : Circuit) (sel : Nat → Fin 2) : Circuit :=
  ⟨List.ofFn (fun j : Fin C.gates.length => @ite Gate
    ((gateAt C j.val).op = GateOp.and ∧ ¬ ((∃ i ∈ (gateAt C j.val).inputs,
      D (N+N) (Finset.Ico N (N+N)) C i = 0) ∨ (∀ i ∈ (gateAt C j.val).inputs,
      D (N+N) (Finset.range N) C i = 0))) (Classical.propDecidable _)
    (copyWire ((gateAt C j.val).inputs.getD (sel j.val).val 0)) (gateAt C j.val)), C.output⟩

theorem posted_eq (N) (C : Circuit) (sel) : replaceAt C (viewGate N C sel) = postedView N C sel := by
  classical
  unfold replaceAt postedView
  congr 1
  apply congrArg List.ofFn
  funext j
  simp [viewGate,Cross,j.isLt]

end PEqualNP.Outside.L_meta_1833

open PEqualNP.Outside.L_meta_1833

theorem PEqualNP.Outside.L_meta_1833 : ∀ (Nlv15 mlv15 : ℕ) (Clv15 : PEqualNP.CircuitLowerBounds.Circuit) (Slv15 Wlv15 : Finset (Fin Nlv15)) (pilv15 nulv15 : Fin Nlv15 → Bool) (sglv15 : ℕ → Fin 2), ((∀ glv15 ∈ Clv15.gates, (glv15.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Clv15) → Set.ncard {jlv15 : ℕ | jlv15 < Clv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15 0 = 0) ∨ (∀ hlv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15 0 = 0))} ≤ mlv15 + 1 → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv15x1 : Fin Clv15.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x1 0 = 0) ∨ (∀ hlv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val))) Clv15.output) (Fin.append (fun plv15 : Fin Nlv15 => if plv15 ∈ Slv15 then (fun ulv15 : Fin Nlv15 => false) plv15 else pilv15 plv15) (fun llv15 : Fin Nlv15 => if llv15 ∈ Wlv15 then (fun ulv15x1 : Fin Nlv15 => false) llv15 else nulv15 llv15)) = true → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x1 : Fin Nlv15 => if plv15x1 ∈ Slv15 then (fun ulv15x2 : Fin Nlv15 => false) plv15x1 else pilv15 plv15x1) (fun llv15x1 : Fin Nlv15 => if llv15x1 ∈ Wlv15 then (fun ulv15x3 : Fin Nlv15 => false) llv15x1 else nulv15 llv15x1)) = false → (∃ xlv15 ylv15 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x2 : Fin Nlv15 => if plv15x2 ∈ Slv15 then xlv15 plv15x2 else pilv15 plv15x2) (fun llv15x2 : Fin Nlv15 => if llv15x2 ∈ Wlv15 then ylv15 llv15x2 else nulv15 llv15x2)) = true) → ∃ Dlv15 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ glv15x1 ∈ Dlv15.gates, (glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15x1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Dlv15) ∧ Set.ncard {jlv15x2 : ℕ | jlv15x2 < Dlv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x2 0 = 0) ∨ (∀ hlv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x2 0 = 0))} ≤ mlv15 ∧ Dlv15.size ≤ Clv15.size ∧ (0 < Dlv15.gates.length ∧ (∀ jlv15x3 < Dlv15.gates.length, ∀ ilv15x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x3).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x3 : Fin Nlv15 => (plv15x3 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x3 : Fin Nlv15 => Nlv15 + (llv15x3 : ℕ)) (Wlv15)ᶜ)).getD ilv15x3 0 = 0) ∧ (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x4 : Fin Nlv15 => (plv15x4 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x4 : Fin Nlv15 => Nlv15 + (llv15x4 : ℕ)) (Wlv15)ᶜ)).getD Dlv15.output 0 = 0) ∧ ∀ xlv15x1 ylv15x1 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Dlv15 (Fin.append xlv15x1 ylv15x1) = PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x5 : Fin Nlv15 => if plv15x5 ∈ Slv15 then xlv15x1 plv15x5 else pilv15 plv15x5) (fun llv15x5 : Fin Nlv15 => if llv15x5 ∈ Wlv15 then ylv15x1 llv15x5 else nulv15 llv15x5)) := by
  intro N m C S W pi nu sel rules bound v off on
  change V (postedView N C sel) (assigned S W pi nu (initial N)) C.output = true at v
  rw [← posted_eq] at v
  obtain ⟨x,y,hxy⟩ := on
  obtain ⟨E,binary,hcount,hsize,clean,evalEq⟩ := main N m C S W pi nu sel rules.1 rules.2
    bound v off ⟨(x,y),hxy⟩
  exact ⟨E,binary,hcount,hsize,clean,fun u v => evalEq (u,v)⟩
