import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1346_aux

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_snoc (l : List Gate) (g : Gate) (w : List Bool) :
    run (l ++ [g]) w = run l w ++ [g.op.eval (g.inputs.map fun i => (run l w).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (l : List Gate) (w : List Bool) : (run l w).length = w.length + l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton l g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then v else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split
  · rfl
  · split
    · rename_i h; subst h; simp
    · rename_i h1 h2
      have : 1 ≤ i - w.length := by omega
      rw [List.getElem?_eq_none (by simpa using this)]
      rfl

theorem getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ h

theorem run_append_getD (l s : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length + l.length) :
    (run (l ++ s) w).getD i false = (run l w).getD i false := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s g ih =>
    rw [← List.append_assoc, run_snoc, getD_snoc, run_length]
    simp only [List.length_append]
    rw [if_pos (by omega)]
    exact ih

/-- The gate equation. -/
theorem geq (gl : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hg : gl[j]? = some g) :
    (run gl w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < w.length + j then (run gl w).getD i false else false) := by
  induction gl using List.reverseRecOn with
  | nil => simp at hg
  | append_singleton l h ih =>
    rw [run_snoc, getD_snoc, run_length]
    by_cases hj : j < l.length
    · rw [if_pos (by omega)]
      rw [List.getElem?_append_left hj] at hg
      rw [ih hg]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length + j
      · rw [if_pos hi, if_pos hi, getD_snoc, run_length, if_pos (by omega)]
      · rw [if_neg hi, if_neg hi]
    · have hjl : j = l.length := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hg
        simp at hg
      subst hjl
      rw [if_neg (by omega), if_pos rfl]
      simp at hg
      subst hg
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length + l.length
      · rw [if_pos hi, getD_snoc, run_length, if_pos hi]
      · rw [if_neg hi]
        exact getD_big _ _ (by rw [run_length]; omega)

/-- The index map of a removal: wire `B` is redirected to `a`, later wires move down. -/
def phi (B a i : ℕ) : ℕ := if i < B then i else if i = B then a else i - 1

def mg (B a : ℕ) (h : Gate) : Gate := ⟨h.op, h.inputs.map (phi B a)⟩

def OkOp (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not

def noRead (B : ℕ) (h : Gate) : Prop :=
  (h.op = GateOp.not → h.inputs.head? ≠ some B) ∧
    (h.op = GateOp.and ∨ h.op = GateOp.or → B ∉ h.inputs)

theorem gate_step (B a : ℕ) (wo wn : List Bool) (E : Prop) (h : Gate) (hok : OkOp h)
    (hinv : ∀ i, (i ≠ B ∨ E) → wo.getD i false = wn.getD (phi B a i) false)
    (hE : E ∨ noRead B h) :
    h.op.eval (h.inputs.map fun i => wo.getD i false) =
      (mg B a h).op.eval ((mg B a h).inputs.map fun i => wn.getD i false) := by
  obtain ⟨op, ins⟩ := h
  simp only [mg, List.map_map]
  rcases hE with hE | ⟨hn1, hn2⟩
  · congr 1
    apply List.map_congr_left
    intro i _
    exact hinv i (Or.inr hE)
  · rcases hok with h1 | h1 | h1 <;> simp only at h1 <;> subst h1
    · congr 1
      apply List.map_congr_left
      intro i hi
      exact hinv i (Or.inl fun e => hn2 (Or.inl rfl) (e ▸ hi))
    · congr 1
      apply List.map_congr_left
      intro i hi
      exact hinv i (Or.inl fun e => hn2 (Or.inr rfl) (e ▸ hi))
    · cases ins with
      | nil => rfl
      | cons i t =>
        have hi : i ≠ B := fun e => hn1 rfl (by simp [e])
        simp only [GateOp.eval, List.map_cons, List.headD_cons, Function.comp]
        rw [hinv i (Or.inl hi)]

theorem sim (pre : List Gate) (g : Gate) (a : ℕ) (x : List Bool) (suf : List Gate)
    (hok : ∀ h ∈ suf, OkOp h)
    (ha : a < x.length + pre.length ∨ x.length + pre.length + 1 + suf.length ≤ a)
    (E : Prop)
    (hEdef : E → (run (pre ++ [g]) x).getD (x.length + pre.length) false =
      (run (pre ++ [g]) x).getD a false)
    (hE : E ∨ ∀ h ∈ suf, noRead (x.length + pre.length) h) :
    ∀ i, (i ≠ x.length + pre.length ∨ E) →
      (run (pre ++ g :: suf) x).getD i false =
        (run (pre ++ suf.map (mg (x.length + pre.length) a)) x).getD
          (phi (x.length + pre.length) a i) false := by
  induction suf using List.reverseRecOn with
  | nil =>
    intro i hi
    simp only [List.map_nil, List.append_nil, List.length_nil, Nat.add_zero] at ha ⊢
    by_cases h1 : i < x.length + pre.length
    · simp only [phi, if_pos h1]
      exact run_append_getD pre [g] x i h1
    · by_cases h2 : i = x.length + pre.length
      · subst h2
        have hE' : E := by
          rcases hi with hi | hi
          · exact absurd rfl hi
          · exact hi
        simp only [phi, lt_irrefl, if_false, if_true]
        rw [hEdef hE']
        rcases ha with ha | ha
        · exact run_append_getD pre [g] x a ha
        · rw [getD_big _ _ (by rw [run_length]; simp; omega),
            getD_big _ _ (by rw [run_length]; omega)]
      · simp only [phi, if_neg h1, if_neg h2]
        rw [getD_big _ _ (by rw [run_length]; simp; omega),
          getD_big _ _ (by rw [run_length]; omega)]
  | append_singleton s h ih =>
    have ih' := ih (fun h' hh => hok h' (by simp [hh]))
      (by rcases ha with ha | ha
          · exact Or.inl ha
          · right; simp at ha; omega)
      (by rcases hE with hE | hE
          · exact Or.inl hE
          · exact Or.inr fun h' hh => hE h' (by simp [hh]))
    have e1 : pre ++ g :: (s ++ [h]) = (pre ++ g :: s) ++ [h] := by simp
    have e2 : pre ++ (s ++ [h]).map (mg (x.length + pre.length) a) =
        (pre ++ s.map (mg (x.length + pre.length) a)) ++ [mg (x.length + pre.length) a h] := by
      simp
    have hstep := gate_step (x.length + pre.length) a (run (pre ++ g :: s) x)
      (run (pre ++ s.map (mg (x.length + pre.length) a)) x) E h (hok h (by simp)) ih'
      (by rcases hE with hE | hE
          · exact Or.inl hE
          · exact Or.inr (hE h (by simp)))
    intro i hi
    rw [e1, e2, run_snoc, run_snoc, getD_snoc, getD_snoc, run_length, run_length, ← hstep]
    simp only [List.length_append, List.length_cons, List.length_map]
    simp only [List.length_append, List.length_singleton] at ha
    have ihi := ih' i hi
    have hbig : x.length + (pre.length + s.length) ≤ phi (x.length + pre.length) a i →
        (run (pre ++ s.map (mg (x.length + pre.length) a)) x).getD
          (phi (x.length + pre.length) a i) false = false := fun hh =>
      getD_big _ _ (by rw [run_length]; simp; omega)
    have hp : phi (x.length + pre.length) a i =
        if i < x.length + pre.length then i else if i = x.length + pre.length then a
          else i - 1 := rfl
    split_ifs at hp with c1 c2 <;> split_ifs <;>
      first
        | exact ihi
        | rfl
        | omega
        | (exfalso; omega)
        | (rw [ihi]; exact hbig (by omega))

def isNot (g : Gate) : Bool := match g.op with
  | GateOp.not => true
  | _ => false

def isTW (g : Gate) : Bool := match g.op with
  | GateOp.and => decide (g.inputs.length = 2)
  | GateOp.or => decide (g.inputs.length = 2)
  | _ => false

theorem isNot_iff (g : Gate) : isNot g = true ↔ g.op = GateOp.not := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [isNot]

theorem isTW_iff (g : Gate) :
    isTW g = true ↔ ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [isTW]

theorem isNot_mg (B a : ℕ) : (isNot ∘ mg B a) = isNot := by
  funext h
  rfl

theorem isTW_mg (B a : ℕ) : (isTW ∘ mg B a) = isTW := by
  funext h
  obtain ⟨op, ins⟩ := h
  cases op <;> simp [isTW, mg]

theorem cnt_bridge (l : List Gate) (p : Gate → Bool) :
    (Finset.univ.filter (fun q : Fin l.length => p (l.get q) = true)).card = l.countP p := by
  conv_rhs => rw [← List.ofFn_get l]
  rw [List.countP_ofFn]

def Val (gl : List Gate) : Prop :=
  ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def W {n : ℕ} (gl : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (run gl (List.ofFn x)).getD i false

def rd {n : ℕ} (gl : List Gate) (x : Fin n → Bool) (b i : ℕ) : Bool :=
  if i < b then W gl x i else false

def Comp {n m : ℕ} (S : Fin m → Finset (Fin n)) (gl : List Gate) (ol : Fin m → ℕ) : Prop :=
  ∀ (o : Fin m) (x : Fin n → Bool), W gl x (ol o) = decide (∃ v ∈ S o, x v = true)

theorem W_big {n : ℕ} (gl : List Gate) (x : Fin n → Bool) (i : ℕ) (h : n + gl.length ≤ i) :
    W gl x i = false :=
  getD_big _ _ (by rw [run_length]; simpa using h)

theorem W_geq {n : ℕ} (gl : List Gate) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : gl[j]? = some g) :
    W gl x (n + j) = g.op.eval (g.inputs.map (rd gl x (n + j))) := by
  have := geq gl (List.ofFn x) j g hg
  simp only [List.length_ofFn] at this
  exact this

theorem remove {n m : ℕ} (S : Fin m → Finset (Fin n)) (gl : List Gate) (ol : Fin m → ℕ) (c : ℕ)
    (hV : Val gl) (hN : gl.countP isNot ≤ 1) (hT : gl.countP isTW ≤ c) (hC : Comp S gl ol)
    (k a : ℕ) (hk : k < gl.length) (ha : a < n + k ∨ n + gl.length ≤ a)
    (hyp : (∀ x : Fin n → Bool, W gl x (n + k) = W gl x a) ∨
      ((∀ o, ol o ≠ n + k) ∧ ∀ (kr : ℕ) (h : Gate), k < kr → gl[kr]? = some h → noRead (n + k) h)) :
    ∃ (gl' : List Gate) (ol' : Fin m → ℕ), gl'.length < gl.length ∧ Val gl' ∧
      gl'.countP isNot ≤ 1 ∧ gl'.countP isTW ≤ c ∧ Comp S gl' ol' := by
  obtain ⟨pre, g, suf, hsplit, hpl⟩ : ∃ pre g suf, gl = pre ++ g :: suf ∧ pre.length = k :=
    ⟨gl.take k, gl[k], gl.drop (k + 1), by
      rw [← List.drop_eq_getElem_cons hk]; exact (List.take_append_drop k gl).symm,
      by rw [List.length_take]; omega⟩
  subst hsplit
  subst hpl
  refine ⟨pre ++ suf.map (mg (n + pre.length) a), fun o => phi (n + pre.length) a (ol o),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro h hh
    rw [List.mem_append, List.mem_map] at hh
    rcases hh with hh | ⟨h0, hh0, rfl⟩
    · exact hV h (by simp [hh])
    · have := hV h0 (by simp [hh0])
      simpa [mg] using this
  · refine le_trans ?_ hN
    rw [List.countP_append, List.countP_append, List.countP_cons, List.countP_map, isNot_mg]
    omega
  · refine le_trans ?_ hT
    rw [List.countP_append, List.countP_append, List.countP_cons, List.countP_map, isTW_mg]
    omega
  · intro o x
    rw [← hC o x]
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    have hpref : ∀ i, i < n + pre.length + 1 →
        W (pre ++ g :: suf) x i = (run (pre ++ [g]) (List.ofFn x)).getD i false := by
      intro i hi
      have e : pre ++ g :: suf = (pre ++ [g]) ++ suf := by simp
      unfold W
      rw [e]
      exact run_append_getD _ _ _ _ (by simp; omega)
    have hs := sim pre g a (List.ofFn x) suf
      (fun h hh => (hV h (by simp [hh])).1)
      (by rw [hlen]; simp at ha; omega)
      (W (pre ++ g :: suf) x (n + pre.length) = W (pre ++ g :: suf) x a)
      (by
        intro hE
        rw [hlen, ← hpref _ (by omega), hE]
        rcases ha with ha | ha
        · exact hpref _ (by omega)
        · rw [W_big _ _ _ ha]
          exact (getD_big _ _ (by rw [run_length]; simp at ha ⊢; omega)).symm)
      (by
        rcases hyp with hyp | ⟨-, hr⟩
        · exact Or.inl (hyp x)
        · right
          intro h hh
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hh
          rw [hlen]
          refine hr (pre.length + 1 + i) h (by omega) ?_
          rw [List.getElem?_append_right (by omega)]
          have e : pre.length + 1 + i - pre.length = i + 1 := by omega
          rw [e, List.getElem?_cons_succ]
          exact hi)
      (ol o)
      (by
        rcases hyp with hyp | ⟨ho, -⟩
        · exact Or.inr (hyp x)
        · left; rw [hlen]; exact ho o)
    rw [hlen] at hs
    exact hs.symm

def Red {m : ℕ} (n : ℕ) (gl : List Gate) (ol : Fin m → ℕ) : Prop :=
  (∀ k, k < gl.length →
    (∃ x : Fin n → Bool, W gl x (n + k) = true) ∧ (∃ x : Fin n → Bool, W gl x (n + k) = false)) ∧
  (∀ k, k < gl.length → ∀ a, a < n + k → ∃ x : Fin n → Bool, W gl x (n + k) ≠ W gl x a) ∧
  (∀ k, k < gl.length → (∃ o, ol o = n + k) ∨
    ∃ (kr : ℕ) (h : Gate), k < kr ∧ gl[kr]? = some h ∧ ¬ noRead (n + k) h) ∧
  (∀ (k : ℕ) (g : Gate), gl[k]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∃ a b : ℕ, a ≠ b ∧ g.inputs = [a, b])

theorem reduce {n m : ℕ} (S : Fin m → Finset (Fin n)) (c : ℕ) :
    ∀ (N : ℕ) (gl : List Gate) (ol : Fin m → ℕ), gl.length = N → Val gl →
      gl.countP isNot ≤ 1 → gl.countP isTW ≤ c → Comp S gl ol →
      ∃ (gl' : List Gate) (ol' : Fin m → ℕ), Val gl' ∧ gl'.countP isNot ≤ 1 ∧
        gl'.countP isTW ≤ c ∧ Comp S gl' ol' ∧ Red n gl' ol' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro gl ol hlen hV hN hT hC
  by_cases h1 : ∃ k a, k < gl.length ∧ (a < n + k ∨ n + gl.length ≤ a) ∧
      ((∀ x : Fin n → Bool, W gl x (n + k) = W gl x a) ∨
        ((∀ o, ol o ≠ n + k) ∧ ∀ (kr : ℕ) (h : Gate), k < kr → gl[kr]? = some h → noRead (n + k) h))
  · obtain ⟨k, a, hk, ha, hyp⟩ := h1
    obtain ⟨gl', ol', hlt, hV', hN', hT', hC'⟩ := remove S gl ol c hV hN hT hC k a hk ha hyp
    exact ih gl'.length (by omega) gl' ol' rfl hV' hN' hT' hC'
  · refine ⟨gl, ol, hV, hN, hT, hC, ?_⟩
    have F1 : ∀ k, k < gl.length → ∀ a, a < n + k →
        ∃ x : Fin n → Bool, W gl x (n + k) ≠ W gl x a := by
      intro k hk a ha
      by_contra hc
      push Not at hc
      exact h1 ⟨k, a, hk, Or.inl ha, Or.inl hc⟩
    have F2 : ∀ k, k < gl.length → ∃ x : Fin n → Bool, W gl x (n + k) = true := by
      intro k hk
      by_contra hc
      push Not at hc
      exact h1 ⟨k, n + gl.length, hk, Or.inr le_rfl, Or.inl fun x => by
        rw [W_big gl x _ le_rfl]
        exact Bool.eq_false_iff.2 (hc x)⟩
    have F3 : ∀ k, k < gl.length → (∃ o, ol o = n + k) ∨
        ∃ (kr : ℕ) (h : Gate), k < kr ∧ gl[kr]? = some h ∧ ¬ noRead (n + k) h := by
      intro k hk
      by_contra hc
      rw [not_or] at hc
      obtain ⟨ho, hr⟩ := hc
      push Not at ho hr
      exact h1 ⟨k, n + gl.length, hk, Or.inr le_rfl, Or.inr ⟨ho, hr⟩⟩
    have aux : ∀ k, k < gl.length → ∀ j,
        (∀ x : Fin n → Bool, W gl x (n + k) = rd gl x (n + k) j) → False := by
      intro k hk j hj
      by_cases hj' : j < n + k
      · obtain ⟨x, hx⟩ := F1 k hk j hj'
        exact hx (by rw [hj x, rd, if_pos hj'])
      · obtain ⟨x, hx⟩ := F2 k hk
        rw [hj x, rd, if_neg hj'] at hx
        exact Bool.false_ne_true hx
    have F4 : ∀ d k, k < gl.length → gl.length - k = d →
        ∃ x : Fin n → Bool, W gl x (n + k) = false := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ihd =>
      intro k hk hd
      by_contra hc
      push Not at hc
      have hTr : ∀ x : Fin n → Bool, W gl x (n + k) = true := fun x => by simpa using hc x
      rcases F3 k hk with ⟨o, ho⟩ | ⟨kr, h, hkr, hh, hnr⟩
      · have := hC o (fun _ => false)
        rw [ho, hTr] at this
        simp at this
      · have hkrlt : kr < gl.length := (List.getElem?_eq_some_iff.1 hh).1
        have hok := hV h (List.mem_of_getElem? hh)
        have hge := fun x : Fin n → Bool => W_geq gl x kr h hh
        obtain ⟨x0, hx0⟩ := ihd (gl.length - kr) (by omega) kr hkrlt rfl
        have hrd : ∀ x : Fin n → Bool, rd gl x (n + kr) (n + k) = true := fun x => by
          rw [rd, if_pos (by omega)]; exact hTr x
        obtain ⟨op, ins⟩ := h
        unfold noRead at hnr
        simp only at hok hnr hge
        obtain ⟨hop, hl⟩ := hok
        rcases hop with hop | hop | hop <;> subst hop
        · have hmem : n + k ∈ ins := by
            by_contra hm
            exact hnr ⟨fun e => (by cases e), fun _ => hm⟩
          rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, t⟩⟩⟩
          · simp at hmem
          · simp only [List.mem_singleton] at hmem
            subst hmem
            have := hge x0
            rw [hx0] at this
            simp [GateOp.eval, hrd x0] at this
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with hmem | hmem <;> subst hmem
            · exact aux kr hkrlt j fun x => by
                have := hge x
                simpa [GateOp.eval, hrd x] using this
            · exact aux kr hkrlt i fun x => by
                have := hge x
                simpa [GateOp.eval, hrd x] using this
          · simp at hl
        · have hmem : n + k ∈ ins := by
            by_contra hm
            exact hnr ⟨fun e => (by cases e), fun _ => hm⟩
          have := hge x0
          rw [hx0] at this
          have h2 : (List.map (rd gl x0 (n + kr)) ins).any id = true :=
            List.any_eq_true.2 ⟨true, List.mem_map.2 ⟨n + k, hmem, hrd x0⟩, rfl⟩
          simp only [GateOp.eval] at this
          rw [h2] at this
          exact Bool.false_ne_true this
        · have hhead : ins.head? = some (n + k) := by
            by_contra hm
            exact hnr ⟨fun _ => hm, by rintro (e | e) <;> cases e⟩
          rcases ins with _ | ⟨i, t⟩
          · simp at hhead
          · simp only [List.head?_cons, Option.some.injEq] at hhead
            subst hhead
            obtain ⟨x, hx⟩ := F2 kr hkrlt
            have := hge x
            rw [hx] at this
            simp [GateOp.eval, hrd x] at this
    refine ⟨fun k hk => ⟨F2 k hk, F4 _ k hk rfl⟩, F1, F3, ?_⟩
    intro k g hg hop
    have hk : k < gl.length := (List.getElem?_eq_some_iff.1 hg).1
    have hok := hV g (List.mem_of_getElem? hg)
    have hge := fun x : Fin n → Bool => W_geq gl x k g hg
    obtain ⟨op, ins⟩ := g
    simp only at hok hop hge
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, t⟩⟩⟩
    · exfalso
      rcases hop with hop | hop <;> subst hop
      · obtain ⟨x, hx⟩ := F4 _ k hk rfl
        have := hge x
        rw [hx] at this
        simp [GateOp.eval] at this
      · obtain ⟨x, hx⟩ := F2 k hk
        have := hge x
        rw [hx] at this
        simp [GateOp.eval] at this
    · exfalso
      apply aux k hk i
      intro x
      have := hge x
      rcases hop with hop | hop <;> subst hop <;> simpa [GateOp.eval] using this
    · refine ⟨i, j, ?_, rfl⟩
      rintro rfl
      apply aux k hk i
      intro x
      have := hge x
      rcases hop with hop | hop <;> subst hop <;> simpa [GateOp.eval] using this
    · have := hok.2
      simp at this

theorem ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (i : ℕ)
    (h : (List.ofFn x).getD i false = true) : ∃ hi : i < n, x ⟨i, hi⟩ = true := by
  by_cases hi : i < n
  · refine ⟨hi, ?_⟩
    simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi] using h
  · rw [getD_big _ _ (by simp; omega)] at h
    exact absurd h (by simp)

end PEqualNP.Outside.L_meta_1346_aux

open PEqualNP.Outside.L_meta_1346_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1346 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ ic : Fin m, 2 ≤ (S ic).card) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → (∃ c : PEqualNP.CircuitLowerBounds.GateOp, (c = PEqualNP.CircuitLowerBounds.GateOp.and ∨ c = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (o1 : Fin m) (x1 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set (ι 0).val ⟨c, []⟩, out o1⟩ (List.ofFn x1) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o1⟩ (List.ofFn x1)) ∨ ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin 1 → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin 1, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card ≤ I.card ∧ (∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, x2 v2 = true)) ∧ (∀ jr : Fin gl.length, ∃ xr yr : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn xr) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn yr)) ∧ (∀ jr2 : Fin gl.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr2.val⟩ (List.ofFn xr2) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, wr⟩ (List.ofFn xr2)) ∧ (∀ jr3 : Fin gl.length, (∃ oq : Fin m, ol oq = n + jr3.val) ∨ ∃ kr : Fin gl.length, ((gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gl.get kr).inputs.head? = some (n + jr3.val)) ∨ (((gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n + jr3.val ∈ (gl.get kr).inputs)) ∧ (∀ jr4 : Fin gl.length, ((gl.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ ar br : ℕ, ar ≠ br ∧ (gl.get jr4).inputs = [ar, br]) := by
  intro n m S hS gates out hgates hcomp ι hι I hI
  by_cases hm : m = 0
  · subst hm
    exact Or.inl ⟨GateOp.and, Or.inl rfl, fun o1 => o1.elim0⟩
  right
  have hV : Val gates := hgates
  have hN : gates.countP isNot ≤ 1 := by
    rw [← cnt_bridge]
    apply Finset.card_le_one.2
    intro q hq q' hq'
    rw [Finset.mem_filter] at hq hq'
    obtain ⟨r, hr⟩ := hι q ((isNot_iff _).1 hq.2)
    obtain ⟨r', hr'⟩ := hι q' ((isNot_iff _).1 hq'.2)
    rw [← hr, ← hr', Subsingleton.elim r r']
  have hT : gates.countP isTW ≤ I.card := by
    rw [← cnt_bridge]
    apply Finset.card_le_card
    intro q hq
    rw [Finset.mem_filter] at hq
    exact hI q ((isTW_iff _).1 hq.2)
  have hC : Comp S gates out := fun o x => hcomp o x
  obtain ⟨gl, ol, hV', hN', hT', hC', hR1, hR2, hR3, hR4⟩ :=
    reduce S I.card gates.length gates out rfl hV hN hT hC
  have hne : 0 < gl.length := by
    by_contra hz
    have hnil : gl = [] := List.length_eq_zero_iff.1 (by omega)
    subst hnil
    obtain ⟨v1, hv1, v2, hv2, hne⟩ := Finset.one_lt_card.1 (hS ⟨0, by omega⟩)
    have e1 := hC' ⟨0, by omega⟩ (fun u => decide (u = v1))
    have e2 := hC' ⟨0, by omega⟩ (fun u => decide (u = v2))
    rw [decide_eq_true ⟨v1, hv1, by simp⟩] at e1
    rw [decide_eq_true ⟨v2, hv2, by simp⟩] at e2
    obtain ⟨h1, hx1⟩ := ofFn_getD_true _ _ e1
    obtain ⟨h2, hx2⟩ := ofFn_getD_true _ _ e2
    simp only [decide_eq_true_eq] at hx1 hx2
    exact hne (hx1.symm.trans hx2)
  obtain ⟨q0, hq0⟩ : ∃ q0 : Fin gl.length,
      ∀ q3 : Fin gl.length, (gl.get q3).op = GateOp.not → q0 = q3 := by
    by_cases hex : ∃ q : Fin gl.length, (gl.get q).op = GateOp.not
    · obtain ⟨q, hq⟩ := hex
      refine ⟨q, fun q3 h3 => ?_⟩
      have hc1 : (Finset.univ.filter (fun q : Fin gl.length => isNot (gl.get q) = true)).card ≤ 1 := by
        rw [cnt_bridge]; exact hN'
      exact Finset.card_le_one.1 hc1 q
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, (isNot_iff _).2 hq⟩) q3
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, (isNot_iff _).2 h3⟩)
    · exact ⟨⟨0, hne⟩, fun q3 h3 => absurd ⟨q3, h3⟩ hex⟩
  refine ⟨gl, ol, fun _ => q0,
    Finset.univ.filter (fun q : Fin gl.length => isTW (gl.get q) = true),
    hV', fun q3 h3 => ⟨0, hq0 q3 h3⟩, ?_, ?_, fun o x => hC' o x, ?_, ?_, ?_, ?_⟩
  · intro q4 h4
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (isTW_iff _).2 h4⟩
  · rw [cnt_bridge]; exact hT'
  · intro jr
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hR1 jr.val jr.2
    refine ⟨x, y, ?_⟩
    show W gl x (n + jr.val) ≠ W gl y (n + jr.val)
    rw [hx, hy]
    simp
  · intro jr wr hwr
    exact hR2 jr.val jr.2 wr hwr
  · intro jr
    rcases hR3 jr.val jr.2 with ⟨o, ho⟩ | ⟨kr, h, hkr, hh, hnr⟩
    · exact Or.inl ⟨o, ho⟩
    · right
      obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 hh
      refine ⟨⟨kr, hlt⟩, ?_⟩
      have hget : gl.get ⟨kr, hlt⟩ = h := he
      rw [hget]
      by_contra hcon
      rw [not_or] at hcon
      exact hnr ⟨fun hop hhead => hcon.1 ⟨hop, hhead⟩, fun hop hmem => hcon.2 ⟨hop, hmem⟩⟩
  · intro jr4 hop
    exact hR4 jr4.val (gl.get jr4) (List.getElem?_eq_getElem jr4.2) hop
